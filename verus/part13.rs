
// =====================================================================================
// Part 13: link and safety theorem.
// =====================================================================================
verus! {
pub open spec fn sfold(d: Deps, n: int, fw: FW, steps: Seq<SStep>) -> FW decreases steps.len() {
    if steps.len() == 0 { fw } else { sapply(d, n, sfold(d, n, fw, steps.drop_last()), steps.last()) }
}
pub open spec fn sok(d: Deps, n: int, fw: FW, steps: Seq<SStep>) -> bool decreases steps.len() {
    if steps.len() == 0 { true } else { sok(d, n, fw, steps.drop_last()) && sguard(d, n, sfold(d, n, fw, steps.drop_last()), steps.last()) }
}
pub open spec fn to_s(who: int, b: BStep) -> SStep {
    match b { BStep::Gen { bloom, fake } => SStep::Gen { who, bloom, fake }, BStep::Patch { h } => SStep::Patch { who, h } }
}
pub open spec fn pre(fw: FW, who: int, p: Peer) -> bool { (who == 0 || who == 1) && fw.peers.len() == 2 && fw.q.len() == 2 && fw.peers[who] == p }

// a generate batch (as proved for PDC::generate_sync_messages) is a sequence of FIFO session steps
pub proof fn lemma_batch_is_session(d: Deps, n: int, who: int, fw: FW, p0: Peer, steps: Seq<BStep>)
    requires pre(fw, who, p0), bok(d, n, p0, steps),
    ensures ({ let ss = Seq::new(steps.len(), |i: int| to_s(who, steps[i]));
        sok(d, n, fw, ss) && sfold(d, n, fw, ss).peers == fw.peers.update(who, brun(d, n, p0, steps).0)
        && sfold(d, n, fw, ss).q == fw.q.update(who, fw.q[who] + brun(d, n, p0, steps).1) }),
    decreases steps.len(),
{
    let ss = Seq::new(steps.len(), |i: int| to_s(who, steps[i]));
    if steps.len() > 0 {
        let sh = steps.drop_last();
        lemma_batch_is_session(d, n, who, fw, p0, sh);
        let ssh = Seq::new(sh.len(), |i: int| to_s(who, sh[i]));
        assert(ss.drop_last() =~= ssh);
        assert(ss.last() == to_s(who, steps.last()));
        let f = sfold(d, n, fw, ssh);
        let pm = brun(d, n, p0, sh);
        assert(f.peers[who] == pm.0);
        assert(sfold(d, n, fw, ss) == sapply(d, n, f, ss.last()));
        match steps.last() {
            BStep::Gen { bloom, fake } => {
                let r = gen(d, n, pm.0, bloom, fake);
                assert(sapply(d, n, f, ss.last()).peers =~= fw.peers.update(who, r.0));
                match r.1 {
                    Some(m) => { assert(sapply(d, n, f, ss.last()).q =~= fw.q.update(who, fw.q[who] + pm.1.push(m)));
                                 assert((fw.q[who] + pm.1).push(m) =~= fw.q[who] + pm.1.push(m)); }
                    None => { assert(sapply(d, n, f, ss.last()).q =~= fw.q.update(who, fw.q[who] + pm.1)); }
                }
            }
            BStep::Patch { h } => {
                assert(sapply(d, n, f, ss.last()).peers =~= fw.peers.update(who, Peer { last_sent_heads: h, ..pm.0 }));
            }
        }
    } else {
        assert(ss =~= Seq::<SStep>::empty());
        assert(fw.peers.update(who, p0) =~= fw.peers);
        assert(fw.q.update(who, fw.q[who] + Seq::<Msg>::empty()) =~= fw.q);
    }
}

pub open spec fn sreach(d: Deps, n: int, fw: FW, k: nat) -> bool decreases k {
    if k == 0 { s_init(fw, d, n) } else { exists|fw0: FW, st: SStep| sreach(d, n, fw0, (k - 1) as nat) && snext(d, n, fw0, st, fw) }
}
// connection start: both sides have a fresh State, queues empty, documents arbitrary closed and bounded
pub open spec fn s_init(fw: FW, d: Deps, n: int) -> bool {
    fw.peers.len() == 2 && fw.q.len() == 2 && fw.q[0].len() == 0 && fw.q[1].len() == 0
    && (forall|i: int| 0 <= i < 2 ==> (#[trigger] fw.peers[i] == fresh(fw.peers[i], false) && fw.peers[i].queue == ISet::<int>::empty()
         && closed(d, fw.peers[i].doc) && bounded(fw.peers[i].doc, n)))
}
proof fn lemma_sinit(d: Deps, n: int, fw: FW)
    requires s_init(fw, d, n), wf(d, n), ensures sinv(d, n, abs_w(fw)),
{
    let w = abs_w(fw);
    assert(w.net.len() == 2);
    assert forall|i: int| 0 <= i < 2 implies w.net[i] == ISet::<Msg>::empty() by {
        assert(fw.q[i] =~= Seq::<Msg>::empty()); assert(w.net[i] =~= ISet::<Msg>::empty());
    }
    assert forall|i: int| 0 <= i < 2 implies peer_inv(d, n, w, i) && xinv_p(d, n, w, i) by {
        let p = w.peers[i];
        assert(p.their_heads == None::<ISet<int>>);
        assert(p.queue.subset_of(w.peers[1 - i].doc)); assert(bounded(p.queue, n));
        assert(p.shared_heads.subset_of(w.peers[1 - i].doc));
    }
}
pub proof fn lemma_sreach_sinv(d: Deps, n: int, fw: FW, k: nat)
    requires wf(d, n), sreach(d, n, fw, k), ensures sinv(d, n, abs_w(fw)), decreases k,
{
    if k == 0 { lemma_sinit(d, n, fw); } else {
        reveal_with_fuel(sreach, 2);
        let (fw0, st) = choose|fw0: FW, st: SStep| sreach(d, n, fw0, (k - 1) as nat) && snext(d, n, fw0, st, fw);
        lemma_sreach_sinv(d, n, fw0, (k - 1) as nat);
        lemma_sstep(d, n, fw0, st, fw);
    }
}
// SAFETY of the samod session: whatever the interleaving of FIFO deliveries, Gen/Patch batches, dropped/errored
// messages, one-sided resets (reset_sync_state / prepare_request / share-policy re-grant) and reconnects,
// if both peers' generate_sync_message would return None via heads_equal, the documents are equal.
pub proof fn theorem_samod_safety(d: Deps, n: int, fw: FW, k: nat)
    requires wf(d, n), sreach(d, n, fw, k),
        report_in_sync(d, n, fw.peers[0]), report_in_sync(d, n, fw.peers[1]),
    ensures fw.peers[0].doc == fw.peers[1].doc,
{
    lemma_sreach_sinv(d, n, fw, k);
    let w = abs_w(fw);
    let a = w.peers[0]; let b = w.peers[1];
    let ta = choose|t: ISet<int>| closed(d, t) && bounded(t, n) && t.subset_of(b.doc) && heads(d, t) == heads(d, a.doc);
    let tb = choose|t: ISet<int>| closed(d, t) && bounded(t, n) && t.subset_of(a.doc) && heads(d, t) == heads(d, b.doc);
    lemma_heads_determine(d, n, a.doc, ta);
    lemma_heads_determine(d, n, b.doc, tb);
    assert(a.doc =~= b.doc);
}
}
