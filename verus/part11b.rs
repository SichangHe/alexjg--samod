
verus! {
pub enum BStep { Gen { bloom: ISet<int>, fake: bool }, Patch { h: ISet<int> } }
pub open spec fn bstep(d: Deps, n: int, pm: (Peer, Seq<Msg>), s: BStep) -> (Peer, Seq<Msg>) {
    match s {
        BStep::Gen { bloom, fake } => { let r = gen(d, n, pm.0, bloom, fake);
            (r.0, match r.1 { Some(m) => pm.1.push(m), None => pm.1 }) }
        BStep::Patch { h } => (Peer { last_sent_heads: h, ..pm.0 }, pm.1),
    }
}
pub open spec fn bguard(d: Deps, n: int, p: Peer, s: BStep) -> bool {
    match s { BStep::Gen { bloom, fake } => p.doc.difference(closure(d, n, p.shared_heads)).subset_of(bloom), BStep::Patch { h } => true }
}
pub open spec fn brun(d: Deps, n: int, p0: Peer, steps: Seq<BStep>) -> (Peer, Seq<Msg>) decreases steps.len() {
    if steps.len() == 0 { (p0, Seq::empty()) } else { bstep(d, n, brun(d, n, p0, steps.drop_last()), steps.last()) }
}
pub open spec fn bok(d: Deps, n: int, p0: Peer, steps: Seq<BStep>) -> bool decreases steps.len() {
    if steps.len() == 0 { true } else { bok(d, n, p0, steps.drop_last()) && bguard(d, n, brun(d, n, p0, steps.drop_last()).0, steps.last()) }
}
pub open spec fn batch_conf(d: Deps, n: int, p0: Peer, p1: Peer, msgs: Seq<Msg>) -> bool {
    exists|steps: Seq<BStep>| bok(d, n, p0, steps) && brun(d, n, p0, steps) == (p1, msgs)
}
pub proof fn lemma_bstep(d: Deps, n: int, p0: Peer, steps: Seq<BStep>, s: BStep)
    requires bok(d, n, p0, steps), bguard(d, n, brun(d, n, p0, steps).0, s),
    ensures bok(d, n, p0, steps.push(s)), brun(d, n, p0, steps.push(s)) == bstep(d, n, brun(d, n, p0, steps), s),
{ assert(steps.push(s).drop_last() =~= steps); assert(steps.push(s).last() == s); }
pub open spec fn recv_conf(d: Deps, n: int, p0: Peer, doc0: ADoc, m: Msg, p1: Peer, doc1: ADoc, ok: bool) -> bool {
    if ok { exists|s2: ISet<int>| doc1.dset() == s2 && drain_ok(d, doc0.dset(), doc0.queue().union(m.changes), s2)
                && bounded(doc0.queue().union(m.changes), n) && (m.changes == ISet::<int>::empty() ==> s2 == doc0.dset())
                && p1 == recv(d, n, p0, m, s2) }
    else { doc1.dset() == doc0.dset() && doc1.queue() == doc0.queue()
                && (p1 == Peer { in_flight: false, sent_hashes: ISet::empty(), ..p0 } || p1 == Peer { in_flight: false, ..p0 }) }
}
}
