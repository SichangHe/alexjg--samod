
verus! {
// CONDITIONAL liveness (samod does NOT implement the Timeout step, so this is about a samod + timeout-fix driver):
// from ANY session world satisfying the invariants (including worlds that are stuck forever under plain automerge sync),
// a Reconnect followed by a run of the fixed protocol with infinitely-often 4 loss-free rounds ends with equal documents.
pub proof fn theorem_reconnect_then_fixed_live(d: Deps, n: int, fw: FW,
    ws: spec_fn(nat) -> World, isr: spec_fn(nat) -> bool, rps: spec_fn(nat) -> RP, sts: spec_fn(nat) -> Step)
    requires wf(d, n), sinv(d, n, abs_w(fw)), ws(0) == abs_w(sapply(d, n, fw, SStep::Reconnect)),
        grun_ok(d, n, ws, isr, rps, sts), gfair(isr, rps),
    ensures exists|K: nat| #![trigger ws(K)] ws(K).peers[0].doc == ws(K).peers[1].doc,
{
    lemma_sstep(d, n, fw, SStep::Reconnect, sapply(d, n, fw, SStep::Reconnect));
    lemma_glive_from(d, n, ws, isr, rps, sts, phi(n, ws(0)), 0);
}
}
