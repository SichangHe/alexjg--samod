
// =====================================================================================
// Part 11 (vlm47_amcode/net): the samod session layer, composed with the model above.
// samod drives one automerge sync::State per (document, ConnectionId). Network assumption:
// the transport is a reliable in-order stream, so each direction is a FIFO queue. State is
// created fresh when the connection is added, and thrown away with the connection. Mid-connection,
// samod re-creates the state of ONE side in reset_sync_state / prepare_request / set_share_config
// (Fresh), and it may silently drop a received message (DropRecv: decode/apply error, policy denial).
// =====================================================================================
verus! {

pub struct FW { pub peers: Seq<Peer>, pub q: Seq<Seq<Msg>> }
pub open spec fn qset(s: Seq<Msg>) -> ISet<Msg> { ISet::new(|m: Msg| s.contains(m)) }
pub open spec fn abs_w(fw: FW) -> World { World { peers: fw.peers, net: Seq::new(fw.q.len(), |i: int| qset(fw.q[i])) } }
// sync::State::new() / new_read_only() / set_read_only(true);set_read_only(false) (nr = needs_reset)
pub open spec fn fresh(p: Peer, nr: bool) -> Peer {
    Peer { shared_heads: ISet::empty(), last_sent_heads: ISet::empty(), their_heads: None,
           their_have: Some(Seq::empty()), their_need: None, sent_hashes: ISet::empty(),
           in_flight: false, have_responded: false, needs_reset: nr, ..p }
}
pub enum SStep {
    Edit { who: int, c: int },
    Gen { who: int, bloom: ISet<int>, fake: bool },
    Patch { who: int, h: ISet<int> },      // samod: self.sync_state.last_sent_heads.clone_from(&msg.heads)
    Recv { who: int, s2: ISet<int> },      // oldest message of the other direction
    DropRecv { who: int, touch: bool, clear: bool }, // oldest message discarded; touch: automerge returned Err, which sets in_flight=false (and maybe clears sent_hashes)
    Fresh { who: int, nr: bool },          // one side re-creates its State
    Reconnect,                             // both Sync states re-created, both directions emptied
}
pub open spec fn sguard(d: Deps, n: int, fw: FW, st: SStep) -> bool {
    match st {
        SStep::Edit { who, c } => guard(d, n, abs_w(fw), Step::Edit { who, c }),
        SStep::Gen { who, bloom, fake } => guard(d, n, abs_w(fw), Step::Gen { who, bloom, fake }),
        SStep::Patch { who, h } => who == 0 || who == 1,
        SStep::Recv { who, s2 } => (who == 0 || who == 1) && fw.q.len() == 2 && fw.q[1 - who].len() > 0
            && guard(d, n, abs_w(fw), Step::Recv { who, m: fw.q[1 - who][0], s2, keep: true }),
        SStep::DropRecv { who, touch, clear } => (who == 0 || who == 1) && fw.q.len() == 2 && fw.q[1 - who].len() > 0,
        SStep::Fresh { who, nr } => who == 0 || who == 1,
        SStep::Reconnect => true,
    }
}
pub open spec fn sapply(d: Deps, n: int, fw: FW, st: SStep) -> FW {
    match st {
        SStep::Edit { who, c } => { let p = fw.peers[who]; FW { peers: fw.peers.update(who, Peer { doc: p.doc.insert(c), ..p }), q: fw.q } }
        SStep::Gen { who, bloom, fake } => {
            let r = gen(d, n, fw.peers[who], bloom, fake);
            FW { peers: fw.peers.update(who, r.0),
                 q: match r.1 { Some(m) => fw.q.update(who, fw.q[who].push(m)), None => fw.q } }
        }
        SStep::Patch { who, h } => { let p = fw.peers[who]; FW { peers: fw.peers.update(who, Peer { last_sent_heads: h, ..p }), q: fw.q } }
        SStep::Recv { who, s2 } => {
            let m = fw.q[1 - who][0];
            FW { peers: fw.peers.update(who, recv(d, n, fw.peers[who], m, s2)),
                 q: fw.q.update(1 - who, fw.q[1 - who].subrange(1, fw.q[1 - who].len() as int)) }
        }
        SStep::DropRecv { who, touch, clear } => FW { peers: if touch { let p = fw.peers[who];
                fw.peers.update(who, Peer { in_flight: false, sent_hashes: if clear { ISet::empty() } else { p.sent_hashes }, ..p }) } else { fw.peers }, q: fw.q.update(1 - who, fw.q[1 - who].subrange(1, fw.q[1 - who].len() as int)) },
        SStep::Fresh { who, nr } => FW { peers: fw.peers.update(who, fresh(fw.peers[who], nr)), q: fw.q },
        SStep::Reconnect => FW { peers: seq![fresh(fw.peers[0], false), fresh(fw.peers[1], false)], q: seq![Seq::<Msg>::empty(), Seq::<Msg>::empty()] },
    }
}
pub open spec fn snext(d: Deps, n: int, fw: FW, st: SStep, fw2: FW) -> bool { sguard(d, n, fw, st) && fw2 == sapply(d, n, fw, st) }

proof fn lemma_qset_push(s: Seq<Msg>, m: Msg)
    ensures qset(s.push(m)) =~= qset(s).insert(m),
{
    assert forall|x: Msg| qset(s.push(m)).contains(x) == qset(s).insert(m).contains(x) by {
        if x == m { assert(s.push(m)[s.len() as int] == m); }
        else if s.push(m).contains(x) { let k = choose|k: int| 0 <= k < s.push(m).len() && s.push(m)[k] == x; assert(k < s.len()); assert(s[k] == x); }
        if s.contains(x) { let k = choose|k: int| 0 <= k < s.len() && s[k] == x; assert(s.push(m)[k] == x); }
    }
}

proof fn lemma_qset_pop(s: Seq<Msg>)
    requires s.len() > 0,
    ensures
        s.subrange(1, s.len() as int).contains(s[0]) ==> qset(s.subrange(1, s.len() as int)) =~= qset(s),
        !s.subrange(1, s.len() as int).contains(s[0]) ==> qset(s.subrange(1, s.len() as int)) =~= qset(s).remove(s[0]),
{
    let t = s.subrange(1, s.len() as int);
    assert forall|x: Msg| t.contains(x) implies s.contains(x) by {
        let k = choose|k: int| 0 <= k < t.len() && t[k] == x; assert(s[k + 1] == x);
    }
    assert forall|x: Msg| s.contains(x) && x != s[0] implies t.contains(x) by {
        let k = choose|k: int| 0 <= k < s.len() && s[k] == x; assert(k >= 1); assert(t[k - 1] == x);
    }
    assert(s.contains(s[0]));
    if t.contains(s[0]) {
        assert forall|x: Msg| qset(t).contains(x) == qset(s).contains(x) by {}
    } else {
        assert forall|x: Msg| qset(t).contains(x) == qset(s).remove(s[0]).contains(x) by {}
    }
}

// steps that keep docs/queues and only reset or shrink sync bookkeeping and messages
proof fn lemma_core(d: Deps, n: int, w: World, w2: World)
    requires wf(d, n), sinv(d, n, w), w2.peers.len() == 2, w2.net.len() == 2,
        forall|i: int| 0 <= i < 2 ==> (
            #[trigger] w2.peers[i].doc == w.peers[i].doc && w2.peers[i].queue == w.peers[i].queue
            && (w2.peers[i].their_heads == w.peers[i].their_heads || w2.peers[i].their_heads == None::<ISet<int>>)
            && (w2.peers[i].shared_heads == w.peers[i].shared_heads || w2.peers[i].shared_heads == ISet::<int>::empty())
            && (w2.peers[i].their_have == w.peers[i].their_have || w2.peers[i].their_have == Some(Seq::<Have>::empty()))
            && (forall|m: Msg| w2.net[i].contains(m) ==> w.net[i].contains(m))),
    ensures sinv(d, n, w2), rel(w, w2),
{
    assert(w.peers.len() == 2 && w.net.len() == 2);
    assert forall|i: int| 0 <= i < 2 implies peer_inv(d, n, w2, i) && xinv_p(d, n, w2, i) by {
        assert(peer_inv(d, n, w, i) && xinv_p(d, n, w, i));
        assert(w2.peers[i].doc == w.peers[i].doc && w2.peers[1 - i].doc == w.peers[1 - i].doc);
        let p = w.peers[i]; let p2 = w2.peers[i];
        if p2.their_heads != None::<ISet<int>> { assert(p2.their_heads == p.their_heads); }
        assert(p2.shared_heads.subset_of(w2.peers[1 - i].doc));
        match p2.their_have {
            Some(h) => {
                if p2.their_have != Some(Seq::<Have>::empty()) { assert(p2.their_have == p.their_have); }
            }
            None => { assert(p2.their_have == p.their_have); }
        }
    }
    assert(peer_inv(d, n, w2, 0) && peer_inv(d, n, w2, 1) && xinv_p(d, n, w2, 0) && xinv_p(d, n, w2, 1));
    assert(rel_i(w, w2, 0) && rel_i(w, w2, 1)) by {
        assert(w2.peers[0].doc == w.peers[0].doc && w2.peers[1].doc == w.peers[1].doc);
        assert(w2.peers[0].queue == w.peers[0].queue && w2.peers[1].queue == w.peers[1].queue);
    }
}
// lift: a FIFO step that is a model step maps onto it
proof fn lemma_lift(d: Deps, n: int, fw: FW, ms: Step, fw2: FW)
    requires wf(d, n), sinv(d, n, abs_w(fw)), next(d, n, abs_w(fw), ms, abs_w(fw2)), ensures sinv(d, n, abs_w(fw2)),
{
    lemma_step(d, n, abs_w(fw), ms, abs_w(fw2));
    lemma_xstep(d, n, abs_w(fw), ms, abs_w(fw2));
}

pub proof fn lemma_sstep(d: Deps, n: int, fw: FW, st: SStep, fw2: FW)
    requires wf(d, n), sinv(d, n, abs_w(fw)), snext(d, n, fw, st, fw2),
    ensures sinv(d, n, abs_w(fw2)), !(st is Edit) ==> rel(abs_w(fw), abs_w(fw2)),
{
    let w = abs_w(fw);
    assert(fw.peers.len() == 2 && fw.q.len() == 2);
    match st {
        SStep::Edit { who, c } => {
            let ms = Step::Edit { who, c };
            let w2 = apply(d, n, w, ms);
            assert(abs_w(fw2).peers =~= w2.peers);
            assert(abs_w(fw2).net =~~= w2.net);
            assert(abs_w(fw2) == w2);
            lemma_lift(d, n, fw, ms, fw2);
        }
        SStep::Gen { who, bloom, fake } => {
            let ms = Step::Gen { who, bloom, fake };
            let w2 = apply(d, n, w, ms);
            assert(abs_w(fw2).peers =~= w2.peers);
            assert(abs_w(fw2).net.len() == w2.net.len());
            assert forall|i: int| 0 <= i < 2 implies abs_w(fw2).net[i] =~= w2.net[i] by {
                if let Some(m) = gen(d, n, fw.peers[who], bloom, fake).1 {
                    if i == who {
                        lemma_qset_push(fw.q[who], m);
                        assert(fw2.q[i] == fw.q[who].push(m));
                    }
                }
            }
            assert(abs_w(fw2).net =~= w2.net);
            assert(abs_w(fw2) == w2);
            lemma_lift(d, n, fw, ms, fw2);
            lemma_rel_step(d, n, w, ms, w2);
        }
        SStep::Recv { who, s2 } => {
            let m = fw.q[1 - who][0];
            let tl = fw.q[1 - who].subrange(1, fw.q[1 - who].len() as int);
            let keep = tl.contains(m);
            let ms = Step::Recv { who, m, s2, keep };
            let w2 = apply(d, n, w, ms);
            lemma_qset_pop(fw.q[1 - who]);
            assert(abs_w(fw2).peers =~= w2.peers);
            assert(abs_w(fw2).net.len() == w2.net.len());
            assert(qset(fw.q[1 - who]).contains(m)) by { assert(fw.q[1 - who].contains(m)); }
            assert forall|i: int| 0 <= i < 2 implies abs_w(fw2).net[i] =~= w2.net[i] by {
                if i == 1 - who { assert(fw2.q[i] == tl); } else { assert(fw2.q[i] == fw.q[i]); }
            }
            assert(abs_w(fw2).net =~= w2.net);
            assert(abs_w(fw2) == w2);
            lemma_lift(d, n, fw, ms, fw2);
            lemma_rel_step(d, n, w, ms, w2);
        }
        SStep::DropRecv { who, touch, clear } => {
            let m = fw.q[1 - who][0];
            let tl = fw.q[1 - who].subrange(1, fw.q[1 - who].len() as int);
            lemma_qset_pop(fw.q[1 - who]);
            assert(fw.q[1 - who].contains(m));
            assert forall|i: int| 0 <= i < 2 implies (
                #[trigger] abs_w(fw2).peers[i].doc == w.peers[i].doc && abs_w(fw2).peers[i].queue == w.peers[i].queue) by {}
            assert forall|i: int, mm: Msg| 0 <= i < 2 && #[trigger] abs_w(fw2).net[i].contains(mm) implies w.net[i].contains(mm) by {
                if i == 1 - who { assert(fw2.q[i] == tl); assert(tl.contains(mm)); let k = choose|k: int| 0 <= k < tl.len() && tl[k] == mm; assert(fw.q[i][k + 1] == mm); }
                else { assert(fw2.q[i] == fw.q[i]); }
            }
            lemma_core(d, n, w, abs_w(fw2));
        }
        SStep::Patch { who, h } => {
            assert forall|i: int| 0 <= i < 2 implies (
                #[trigger] abs_w(fw2).peers[i].doc == w.peers[i].doc && abs_w(fw2).peers[i].queue == w.peers[i].queue) by {}
            assert forall|i: int, m: Msg| 0 <= i < 2 && #[trigger] abs_w(fw2).net[i].contains(m) implies w.net[i].contains(m) by {}
            assert(abs_w(fw2).peers[who].their_heads == w.peers[who].their_heads);
            lemma_core(d, n, w, abs_w(fw2));
        }
        SStep::Fresh { who, nr } => {
            lemma_core(d, n, w, abs_w(fw2));
        }
        SStep::Reconnect => {
            assert(abs_w(fw2).net.len() == 2);
            lemma_core(d, n, w, abs_w(fw2));
        }
    }
}
}
