//! Network emulator for samod: a relay between two real `Repo`s that can drop,
//! delay (reorder) or hold individual sync frames. Handshake frames always pass.
#![allow(dead_code)]
use std::{
    collections::HashMap,
    convert::Infallible,
    pin::Pin,
    sync::{Arc, Mutex},
    time::Duration,
};

use automerge::{Automerge, ChangeHash, ROOT, transaction::Transactable};
use futures::{FutureExt, Sink, SinkExt, Stream, StreamExt, select};
use rand::Rng;
use samod::{AcceptorEvent, BackoffConfig, DialerHandle, DocHandle, Repo, Transport};
use tokio_stream::wrappers::{ReceiverStream, UnboundedReceiverStream};
use tokio_util::sync::PollSender;
use url::Url;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Dir {
    /// dialer (repo A) to acceptor (repo B)
    AtoB,
    BtoA,
}

#[derive(Clone, Copy, Debug)]
pub enum Action {
    Deliver,
    Drop,
    /// deliver later (reorders relative to frames sent after it)
    Delay(Duration),
    /// keep until `LinkCtl::release(dir, idx)`
    Hold,
}

/// Called for each sync/request frame. `idx` counts such frames per direction from 0.
pub type Policy = Box<dyn FnMut(Dir, usize) -> Action + Send>;

enum Ctl {
    Release(Dir, usize),
    Inject(Dir, Vec<u8>),
}

#[derive(Clone)]
pub struct LinkCtl {
    tx: tokio::sync::mpsc::UnboundedSender<Ctl>,
    pub log: Arc<Mutex<Vec<String>>>,
}
impl LinkCtl {
    pub fn release(&self, d: Dir, idx: usize) {
        let _ = self.tx.send(Ctl::Release(d, idx));
    }
}

struct TinCanError(String);
impl std::fmt::Display for TinCanError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl std::fmt::Debug for TinCanError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl std::error::Error for TinCanError {}

type Tx = Box<dyn Send + Unpin + Sink<Vec<u8>, Error = TinCanError>>;
type Rx = Box<dyn Send + Unpin + Stream<Item = Result<Vec<u8>, TinCanError>>>;
struct Side {
    send: Tx,
    recv: Rx,
}

fn kind(b: &[u8]) -> Option<&'static str> {
    let has = |p: &[u8]| b.windows(p.len()).any(|w| w == p);
    if has(b"\x64type\x64sync") {
        Some("sync")
    } else if has(b"\x64type\x67request") {
        Some("request")
    } else {
        None
    }
}

fn pair(mut policy: Policy) -> (Side, Side, LinkCtl) {
    let (l_tx, ml_rx) = tokio::sync::mpsc::channel::<Vec<u8>>(256);
    let (ml_tx, l_rx) = tokio::sync::mpsc::channel::<Vec<u8>>(256);
    let (r_tx, mr_rx) = tokio::sync::mpsc::channel::<Vec<u8>>(256);
    let (mr_tx, r_rx) = tokio::sync::mpsc::channel::<Vec<u8>>(256);
    let (ctl_tx, ctl_rx) = tokio::sync::mpsc::unbounded_channel::<Ctl>();
    let log = Arc::new(Mutex::new(Vec::new()));
    let ctl = LinkCtl { tx: ctl_tx.clone(), log: log.clone() };
    let mut from_l = ReceiverStream::new(ml_rx);
    let mut from_r = ReceiverStream::new(mr_rx);
    let mut to_l = PollSender::new(ml_tx).sink_map_err(|e| TinCanError(format!("{e:?}")));
    let mut to_r = PollSender::new(mr_tx).sink_map_err(|e| TinCanError(format!("{e:?}")));
    let mut ctl_rx = UnboundedReceiverStream::new(ctl_rx);
    tokio::spawn(async move {
        let mut counts: HashMap<Dir, usize> = HashMap::new();
        let mut held: HashMap<(Dir, usize), Vec<u8>> = HashMap::new();
        loop {
            // (dir, bytes, from_peer)
            let (dir, msg, fresh) = select! {
                m = from_l.next().fuse() => match m { Some(m) => (Dir::AtoB, m, true), None => break },
                m = from_r.next().fuse() => match m { Some(m) => (Dir::BtoA, m, true), None => break },
                c = ctl_rx.next().fuse() => match c {
                    Some(Ctl::Inject(d, b)) => (d, b, false),
                    Some(Ctl::Release(d, i)) => match held.remove(&(d, i)) { Some(b) => (d, b, false), None => continue },
                    None => break,
                },
            };
            if fresh {
                if let Some(k) = kind(&msg) {
                    let idx = *counts.entry(dir).and_modify(|c| *c += 1).or_insert(0);
                    let act = policy(dir, idx);
                    log.lock().unwrap().push(format!("{dir:?} #{idx} {k} {}B -> {act:?}", msg.len()));
                    match act {
                        Action::Deliver => {}
                        Action::Drop => continue,
                        Action::Delay(d) => {
                            let tx = ctl_tx.clone();
                            tokio::spawn(async move {
                                tokio::time::sleep(d).await;
                                let _ = tx.send(Ctl::Inject(dir, msg));
                            });
                            continue;
                        }
                        Action::Hold => {
                            held.insert((dir, idx), msg);
                            continue;
                        }
                    }
                }
            }
            let r = match dir {
                Dir::AtoB => to_r.send(msg).await,
                Dir::BtoA => to_l.send(msg).await,
            };
            if r.is_err() {
                break;
            }
        }
    });
    let left = Side {
        send: Box::new(PollSender::new(l_tx).sink_map_err(|e| TinCanError(format!("{e:?}")))),
        recv: Box::new(ReceiverStream::new(l_rx).map(Ok)),
    };
    let right = Side {
        send: Box::new(PollSender::new(r_tx).sink_map_err(|e| TinCanError(format!("{e:?}")))),
        recv: Box::new(ReceiverStream::new(r_rx).map(Ok)),
    };
    (left, right, ctl)
}

struct EmuDialer {
    url: Url,
    acceptor: samod::AcceptorHandle,
    policy: Mutex<Option<Policy>>,
    ctl: Mutex<Option<LinkCtl>>,
}
impl samod::Dialer for EmuDialer {
    type Error = Infallible;
    fn url(&self) -> Url {
        self.url.clone()
    }
    fn connect(
        &self,
    ) -> Pin<Box<dyn std::future::Future<Output = Result<Transport, samod::DialError<Infallible>>> + Send>>
    {
        // one connection only: a reconnect would get a pass-through link
        let policy = self.policy.lock().unwrap().take().unwrap_or_else(|| Box::new(|_, _| Action::Deliver));
        let (l, r, ctl) = pair(policy);
        *self.ctl.lock().unwrap() = Some(ctl);
        let acceptor = self.acceptor.clone();
        Box::pin(async move {
            acceptor
                .accept(Transport::new(r.recv, r.send))
                .map_err(samod::DialError::transient)?;
            Ok(Transport::new(l.recv, l.send))
        })
    }
}

/// Connect `a` (dialer) to `b` through a link with `policy`. Returns the dialer
/// handle (close it to disconnect) and the link control.
pub async fn connect(a: &Repo, b: &Repo, policy: Policy) -> (DialerHandle, LinkCtl) {
    let id: u64 = rand::rng().random();
    let url = Url::parse(&format!("ws://netem-{id}:0")).unwrap();
    let acceptor = b.make_acceptor(url.clone()).unwrap();
    let mut events = acceptor.events();
    let d = Arc::new(EmuDialer {
        url,
        acceptor: acceptor.clone(),
        policy: Mutex::new(Some(policy)),
        ctl: Mutex::new(None),
    });
    let h = a.dial(BackoffConfig::default(), d.clone()).unwrap();
    tokio::time::timeout(Duration::from_secs(5), h.established()).await.unwrap().unwrap();
    tokio::time::timeout(Duration::from_secs(5), async {
        while let Some(e) = events.next().await {
            if matches!(e, AcceptorEvent::ClientConnected { .. }) {
                return;
            }
        }
    })
    .await
    .unwrap();
    let ctl = d.ctl.lock().unwrap().clone().unwrap();
    (h, ctl)
}

pub fn heads(h: &DocHandle) -> Vec<ChangeHash> {
    let mut v = h.with_document(|am| am.get_heads());
    v.sort();
    v
}

pub fn put(h: &DocHandle, k: &str, v: i64) {
    h.with_document(|am| {
        am.transact::<_, _, automerge::AutomergeError>(|tx| {
            tx.put(ROOT, k, v)?;
            Ok(())
        })
        .unwrap();
    });
}

/// Two repos that share a document, currently disconnected, with equal heads.
pub struct Pair {
    pub a: Repo,
    pub b: Repo,
    pub ha: DocHandle,
    pub hb: DocHandle,
}

pub async fn shared_pair(sync_timeout: Option<Duration>) -> Pair {
    let mk = |t: Option<Duration>| async move {
        let mut bld = Repo::build_tokio();
        if let Some(t) = t {
            bld = bld.with_sync_timeout(t);
        }
        bld.load().await
    };
    let a = mk(sync_timeout).await;
    let b = mk(sync_timeout).await;
    let ha = a.create(Automerge::new()).await.unwrap();
    put(&ha, "init", 0);
    let (dh, _ctl) = connect(&a, &b, Box::new(|_, _| Action::Deliver)).await;
    let hb = tokio::time::timeout(Duration::from_secs(5), b.find(ha.document_id().clone()))
        .await
        .unwrap()
        .unwrap()
        .expect("b finds doc");
    for _ in 0..100 {
        if heads(&ha) == heads(&hb) {
            break;
        }
        tokio::time::sleep(Duration::from_millis(20)).await;
    }
    assert_eq!(heads(&ha), heads(&hb));
    tokio::time::sleep(Duration::from_millis(100)).await;
    dh.close();
    tokio::time::sleep(Duration::from_millis(200)).await;
    Pair { a, b, ha, hb }
}

/// Wait up to `deadline` for both docs to have identical heads and contain every change in `want`.
pub async fn wait_converged(p: &Pair, want: &[ChangeHash], deadline: Duration) -> bool {
    let t0 = tokio::time::Instant::now();
    loop {
        let (x, y) = (heads(&p.ha), heads(&p.hb));
        let has = |h: &DocHandle| h.with_document(|am| want.iter().all(|w| am.get_changes(&[]).iter().any(|c| c.hash() == *w)));
        if x == y && has(&p.ha) && has(&p.hb) {
            return true;
        }
        if t0.elapsed() > deadline {
            return false;
        }
        tokio::time::sleep(Duration::from_millis(10)).await;
    }
}
