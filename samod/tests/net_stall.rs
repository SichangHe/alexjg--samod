#![cfg(feature = "tokio")]
mod netem;
use netem::*;
use std::time::Duration;

fn init_logging() {
    let _ = tracing_subscriber::fmt().with_env_filter(tracing_subscriber::EnvFilter::from_default_env()).try_init();
}

/// Concurrent edits on both sides while disconnected, then reconnect through a link
/// with `policy`. Returns (converged, link log).
async fn run(policy: Policy, timeout: Option<Duration>, deadline: Duration) -> (bool, Vec<String>) {
    let p = shared_pair(timeout).await;
    put(&p.ha, "a", 1);
    put(&p.hb, "b", 2);
    let mut want = heads(&p.ha);
    want.extend(heads(&p.hb));
    let (_dh, ctl) = connect(&p.a, &p.b, policy).await;
    let ok = wait_converged(&p, &want, deadline).await;
    let log = ctl.log.lock().unwrap().clone();
    (ok, log)
}

#[tokio::test]
async fn explore_single_drop() {
    init_logging();
    let (ok, log) = run(Box::new(|_, _| Action::Deliver), None, Duration::from_secs(2)).await;
    println!("baseline ok={ok}\n{}", log.join("\n"));
    for dir in [Dir::AtoB, Dir::BtoA] {
        for k in 0..4 {
            let (ok, _) = run(Box::new(move |d, i| if d == dir && i == k { Action::Drop } else { Action::Deliver }), None, Duration::from_secs(2)).await;
            println!("drop {dir:?} #{k}: converged={ok}");
        }
    }
}

const FIX: Option<Duration> = Some(Duration::from_millis(100));
const WAIT: Duration = Duration::from_secs(3);

fn drop_set(set: &'static [(Dir, usize)]) -> Policy {
    Box::new(move |d, i| if set.contains(&(d, i)) { Action::Drop } else { Action::Deliver })
}

/// #772: the sync message that carries changes is lost (selective drop of the
/// 2nd A->B frame, 301 B). Without the fix both peers go silent forever.
#[tokio::test]
async fn lost_change_message_stalls_without_fix_and_recovers_with_fix() {
    init_logging();
    let (ok, log) = run(drop_set(&[(Dir::AtoB, 1)]), None, WAIT).await;
    println!("no fix: {} frames, first 8:\n{}", log.len(), log[..log.len().min(8)].join("\n"));
    assert!(!ok, "expected a stall without the timeout fix");
    let (ok, log) = run(drop_set(&[(Dir::AtoB, 1)]), FIX, WAIT).await;
    println!("fix: {} frames, first 10:\n{}", log.len(), log[..log.len().min(10)].join("\n"));
    assert!(ok, "timeout fix should recover");
}

/// #772: both first sync messages are lost; both sides keep `in_flight` set.
#[tokio::test]
async fn both_first_messages_lost() {
    init_logging();
    let set: &'static [(Dir, usize)] = &[(Dir::AtoB, 0), (Dir::BtoA, 0)];
    let (ok, _) = run(drop_set(set), None, WAIT).await;
    assert!(!ok, "expected a stall without the timeout fix");
    let (ok, _) = run(drop_set(set), FIX, WAIT).await;
    assert!(ok, "timeout fix should recover");
}

/// Edit `a` so that its next two changes are c1 = false positive of `bloom`, c2 = miss.
/// Returns the number of candidate edits tried.
fn edit_fp_then_miss(h: &samod::DocHandle, bloom: &automerge::sync::BloomFilter) -> u64 {
    use automerge::{ROOT, transaction::Transactable};
    h.with_document(|am| {
        let mut tries = 0u64;
        loop {
            tries += 1;
            let mut t = am.clone();
            t.transact::<_, _, automerge::AutomergeError>(|tx| { tx.put(ROOT, "k1", tries as i64)?; Ok(()) }).unwrap();
            if !bloom.contains_hash(&t.get_heads()[0]) { continue; }
            t.transact::<_, _, automerge::AutomergeError>(|tx| { tx.put(ROOT, "k2", 2)?; Ok(()) }).unwrap();
            if bloom.contains_hash(&t.get_heads()[0]) { continue; }
            *am = t;
            return tries;
        }
    })
}

/// No message is lost. Two reorderings (B->A #0 delivered after #1; A->B #1 after
/// the next one) plus one Bloom false positive: both peers go silent with different docs.
/// Returns (converged, tries, link log).
async fn bloom_run(timeout: Option<Duration>, deadline: Duration) -> (bool, u64, Vec<String>) {
    let sleep = |ms| tokio::time::sleep(Duration::from_millis(ms));
    let p = shared_pair(timeout).await;
    put(&p.hb, "c0", 1); // only B has a new change
    let bloom = {
        let hs: Vec<_> = p.hb.with_document(|am| am.get_changes(&[]).iter().map(|c| c.hash()).collect());
        automerge::sync::BloomFilter::from_hashes(hs.iter())
    };
    let policy: Policy = Box::new(|d, i| match (d, i) {
        (Dir::BtoA, 0) | (Dir::AtoB, 1) => Action::Hold,
        _ => Action::Deliver,
    });
    let (_dh, ctl) = connect(&p.a, &p.b, policy).await;
    sleep(300).await; // A->B #0 delivered, B->A #0 held, B->A #1 (c0) delivered, A->B #1 (ack) held
    ctl.release(Dir::BtoA, 0); // old Bloom{...,c0} reaches A after the newer message
    sleep(100).await;
    let tries = edit_fp_then_miss(&p.ha, &bloom); // c1 (false positive), c2 (miss) -> A->B #2 carries c2 only
    sleep(300).await;
    ctl.release(Dir::AtoB, 1); // old ack (heads=[c0]) arrives after the newer message
    let mut want = heads(&p.ha);
    want.extend(heads(&p.hb));
    let ok = wait_converged(&p, &want, deadline).await;
    (ok, tries, ctl.log.lock().unwrap().clone())
}

/// Finding: samod regenerates after EVERY received message, so after the late-ordered
/// c2 message B immediately sends `need=[c1]` and A answers: the bare-crate stuck state
/// (B silent after two receives with no generate in between) is not reached.
/// This test pins that: with the exact schedule that sticks the bare crate, samod converges
/// even without the fix.
#[tokio::test]
async fn bloom_false_positive_with_reordering_no_loss_is_masked_by_eager_generation() {
    init_logging();
    let (ok, tries, log) = bloom_run(None, WAIT).await;
    println!("no fix: converged={ok} tries={tries} frames={}\n{}", log.len(), log.join("\n"));
    assert!(ok, "samod is expected to recover here without the fix");
}

// ---------------------------------------------------------------- random sweeps

use rand::Rng;

fn random_policy(loss: f64, reorder: f64) -> Policy {
    Box::new(move |_, _| {
        let mut r = rand::rng();
        if r.random_bool(loss) {
            Action::Drop
        } else if r.random_bool(reorder) {
            Action::Delay(Duration::from_millis(r.random_range(5..60)))
        } else {
            Action::Deliver
        }
    })
}

async fn random_plain(loss: f64, reorder: f64, timeout: Option<Duration>) -> (bool, u128) {
    let p = shared_pair(timeout).await;
    put(&p.ha, "a", 1);
    put(&p.hb, "b", 2);
    let mut want = heads(&p.ha);
    want.extend(heads(&p.hb));
    let (_dh, _ctl) = connect(&p.a, &p.b, random_policy(loss, reorder)).await;
    let t0 = std::time::Instant::now();
    let ok = wait_converged(&p, &want, Duration::from_secs(4)).await;
    (ok, t0.elapsed().as_millis())
}

/// B has a new change c0; A edits (c1 FP, c2 miss) at a random time after connecting.
async fn random_bloom(loss: f64, reorder: f64, timeout: Option<Duration>) -> (bool, u64) {
    let p = shared_pair(timeout).await;
    put(&p.hb, "c0", 1);
    let bloom = {
        let hs: Vec<_> = p.hb.with_document(|am| am.get_changes(&[]).iter().map(|c| c.hash()).collect());
        automerge::sync::BloomFilter::from_hashes(hs.iter())
    };
    let (_dh, _ctl) = connect(&p.a, &p.b, random_policy(loss, reorder)).await;
    tokio::time::sleep(Duration::from_millis(rand::rng().random_range(0..80))).await;
    let tries = edit_fp_then_miss(&p.ha, &bloom);
    let mut want = heads(&p.ha);
    want.extend(heads(&p.hb));
    let ok = wait_converged(&p, &want, Duration::from_secs(4)).await;
    (ok, tries)
}

/// `SWEEP_N` runs per config (default 40), `SWEEP_PAR` concurrent runs (default 20).
/// Run: cargo test -p samod --features tokio --test net_stall --release sweep -- --ignored --nocapture
#[tokio::test]
#[ignore]
async fn sweep() {
    let n: usize = std::env::var("SWEEP_N").ok().and_then(|s| s.parse().ok()).unwrap_or(40);
    let par: usize = std::env::var("SWEEP_PAR").ok().and_then(|s| s.parse().ok()).unwrap_or(20);
    let scen = std::env::var("SWEEP_SCEN").unwrap_or("plain".into());
    let configs: Vec<(f64, f64)> = std::env::var("SWEEP_CFG")
        .unwrap_or("0,0;0,0.3;0.05,0;0.1,0;0.2,0;0.1,0.3".into())
        .split(';')
        .map(|c| { let (a, b) = c.split_once(',').unwrap(); (a.parse().unwrap(), b.parse().unwrap()) })
        .collect();
    use futures::StreamExt;
    for (loss, reorder) in configs {
        for fix in [None, FIX] {
            let t0 = std::time::Instant::now();
            let scen2 = scen.clone();
            let res: Vec<(bool, u64)> = futures::stream::iter(0..n)
                .map(|_| {
                    let scen = scen2.clone();
                    async move {
                        if scen == "plain" {
                            let (ok, ms) = random_plain(loss, reorder, fix).await;
                            (ok, ms as u64)
                        } else {
                            random_bloom(loss, reorder, fix).await
                        }
                    }
                })
                .buffer_unordered(par)
                .collect()
                .await;
            let stalled = res.iter().filter(|r| !r.0).count();
            let mut v: Vec<u64> = res.iter().filter(|r| r.0).map(|r| r.1).collect();
            v.sort();
            let med = v.get(v.len() / 2).copied().unwrap_or(0);
            println!(
                "RESULT scen={scen} loss={loss} reorder={reorder} fix={} runs={n} stalled={stalled} converged={} median_{}={med} wall={:?}",
                fix.is_some(), n - stalled, if scen == "plain" { "ms_to_converge" } else { "tries" }, t0.elapsed()
            );
        }
    }
}

/// How often does a new change hash hit a Bloom filter of n entries (false positive)?
#[test]
#[ignore]
fn bloom_false_positive_rate() {
    use automerge::{ChangeHash, sync::BloomFilter};
    let mut r = rand::rng();
    let trials = 2_000_000u64;
    for n in [1usize, 2, 3, 4, 6, 8, 16] {
        let mut hit = 0u64;
        for _ in 0..trials / 100 {
            let hs: Vec<ChangeHash> = (0..n).map(|_| ChangeHash(r.random())).collect();
            let b = BloomFilter::from_hashes(hs.iter());
            for _ in 0..100 {
                if b.contains_hash(&ChangeHash(r.random())) {
                    hit += 1;
                }
            }
        }
        println!("RESULT bloom entries={n} trials={trials} false_positives={hit} rate={:.5}", hit as f64 / trials as f64);
    }
}
