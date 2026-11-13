
// =====================================================================================
// Part 12 (vlm47_amcode/net): the samod code, conformance to the session model.
// Copy of samod-core/src/actors/document/peer_doc_connection.rs functions, minimal labelled changes
// (CHANGE tags; see ../verus/diff_orig.sh).  automerge itself is trusted through external_body specs
// (a sibling agent proves those against the same model).
// =====================================================================================
verus! {
pub struct ES { pub e: EState, pub read_only: bool }       // CHANGE C1: automerge sync::State = model fields + read_only
#[verifier::external_body] pub struct ADoc;                // CHANGE C2: automerge::Automerge, opaque
#[verifier::external_body] pub struct EMsg;                // CHANGE C3: sync::Message, opaque
impl EMsg { pub uninterp spec fn view(&self) -> Msg; }
impl ADoc { pub uninterp spec fn dset(&self) -> ISet<int>; pub uninterp spec fn queue(&self) -> ISet<int>; }
pub uninterp spec fn the_d() -> Deps;
pub uninterp spec fn the_n() -> int;
pub open spec fn aps(s: ES, doc: ADoc) -> Peer { abs(s.e, doc.dset(), doc.queue()) }
pub open spec fn old_shared(p: Peer) -> ISet<int> { p.shared_heads }
pub open spec fn oview(r: Option<EMsg>) -> Option<Msg> { match r { Some(m) => Some(m.view()), None => None } }

// ---- trusted automerge specs ----
#[verifier::external_body]
fn vec_copy(v: &Vec<u64>) -> (r: Vec<u64>) ensures r@ == v@ { v.clone() }
#[verifier::external_body]
fn am_heads(doc: &ADoc) -> (h: Vec<u64>) ensures vset(h@) == heads(the_d(), doc.dset()) { unimplemented!() }
#[verifier::external_body]
fn emsg_heads(m: &EMsg) -> (h: Vec<u64>) ensures vset(h@) == m.view().heads { unimplemented!() }
// TRUSTED: change-hash lists are sorted and unique, so Vec inequality = set inequality
#[verifier::external_body]
fn heads_ne(a: &Vec<u64>, b: &Vec<u64>) -> (r: bool) ensures r == (vset(a@) != vset(b@)) { unimplemented!() }
// doc.generate_sync_message(&mut state) (read-write state only; read_only branches are not modelled)
#[verifier::external_body]
fn am_generate(doc: &ADoc, st: &mut ES) -> (r: Option<EMsg>)
    requires !old(st).read_only,
    ensures !final(st).read_only,
        exists|bloom: ISet<int>, fake: bool|
            doc.dset().difference(closure(the_d(), the_n(), aps(*old(st), *doc).shared_heads)).subset_of(bloom)
            && (aps(*final(st), *doc), oview(r)) == gen(the_d(), the_n(), aps(*old(st), *doc), bloom, fake),
{ unimplemented!() }
// doc.receive_sync_message(&mut state, msg): Ok = model recv; Err = message dropped, in_flight cleared,
// sent_hashes possibly cleared (receive_sync_message_inner sets in_flight=false first; see sync.rs).
#[verifier::external_body]
fn am_receive(doc: &mut ADoc, st: &mut ES, msg: EMsg) -> (ok: bool)
    requires !old(st).read_only,
    ensures !final(st).read_only,
        recv_conf(the_d(), the_n(), aps(*old(st), *old(doc)), *old(doc), msg.view(), aps(*final(st), *final(doc)), *final(doc), ok),
{ unimplemented!() }

// ---- sync::State constructors and set_read_only (copied from automerge state.rs; their_capabilities dropped) ----
impl ES {
    pub fn new() -> (r: ES) ensures forall|doc: ISet<int>, queue: ISet<int>, p0: Peer| p0.doc == doc && p0.queue == queue ==>
        abs(r.e, doc, queue) == fresh(p0, false) { 
        let r = ES { e: EState { shared_heads: Vec::new(), last_sent_heads: Vec::new(), their_heads: None, their_need: None,
            their_have: Some(Vec::new()), sent_hashes: Vec::new(), in_flight: false, have_responded: false, needs_reset: false }, read_only: false };
        proof { assert forall|doc: ISet<int>, queue: ISet<int>, p0: Peer| p0.doc == doc && p0.queue == queue implies abs(r.e, doc, queue) == fresh(p0, false) by {
            assert(vset(r.e.shared_heads@) =~= ISet::<int>::empty()); assert(vset(r.e.last_sent_heads@) =~= ISet::<int>::empty());
            assert(vset(r.e.sent_hashes@) =~= ISet::<int>::empty());
            assert(abs(r.e, doc, queue).their_have == Some(Seq::<Have>::empty())) by { assert(Seq::new(0nat as nat, |i: int| abs_have(r.e.their_have.unwrap()@[i])) =~= Seq::<Have>::empty()); }
        } }
        r }
    pub fn new_read_only() -> (r: ES) ensures forall|doc: ISet<int>, queue: ISet<int>, p0: Peer| p0.doc == doc && p0.queue == queue ==>
        abs(r.e, doc, queue) == fresh(p0, false) {
        let mut r = ES::new(); r.read_only = true; r }
    // automerge State::set_read_only
    pub fn set_read_only(&mut self, read_only: bool) ensures
        forall|doc: ISet<int>, queue: ISet<int>, p0: Peer| p0.doc == doc && p0.queue == queue ==>
            (abs(final(self).e, doc, queue) == abs(old(self).e, doc, queue)
             || abs(final(self).e, doc, queue) == fresh(p0, true)
             || abs(final(self).e, doc, queue) == Peer { in_flight: false, have_responded: false, ..abs(old(self).e, doc, queue) }),
        old(self).read_only && !read_only ==> forall|doc: ISet<int>, queue: ISet<int>, p0: Peer| p0.doc == doc && p0.queue == queue ==>
            abs(final(self).e, doc, queue) == fresh(p0, true),
        final(self).read_only == read_only,
    {
        if self.read_only == read_only { return; }
        if self.read_only && !read_only {
            let r = ES::new();
            *self = ES { e: EState { needs_reset: true, ..r.e }, read_only: false };
            proof { assert forall|doc: ISet<int>, queue: ISet<int>, p0: Peer| p0.doc == doc && p0.queue == queue implies
                abs(self.e, doc, queue) == fresh(p0, true) by {
                    assert(abs(r.e, doc, queue) == fresh(p0, false));
                    assert(abs(self.e, doc, queue) == Peer { needs_reset: true, ..abs(r.e, doc, queue) });
            } }
        } else {
            self.read_only = true; self.e.in_flight = false; self.e.have_responded = false;
        }
    }
}

// ---- PeerDocConnection (samod) ----
pub struct PDC {
    pub sync_state: ES,
    pub can_write: bool,          // CHANGE C4: stands for self.can_write() (share_policy lookup)
    pub exchanged: bool,          // CHANGE C5: stands for state.last_sent.is_some() || state.last_received.is_some()
}
impl PDC {
    // original: peer_doc_connection.rs:53 reset_sync_state
    pub fn reset_sync_state(&mut self)
        ensures forall|doc: ISet<int>, queue: ISet<int>|
            abs(final(self).sync_state.e, doc, queue) == fresh(abs(old(self).sync_state.e, doc, queue), false),
    {
        self.sync_state = if self.can_write { ES::new() } else { ES::new_read_only() };
        proof { assert forall|doc: ISet<int>, queue: ISet<int>| abs(self.sync_state.e, doc, queue) == fresh(abs(old(self).sync_state.e, doc, queue), false) by {
            let p0 = abs(old(self).sync_state.e, doc, queue); assert(p0.doc == doc && p0.queue == queue); } }
    }
    // original: peer_doc_connection.rs:61 prepare_request
    pub fn prepare_request(&mut self)
        ensures
            old(self).exchanged ==> forall|doc: ISet<int>, queue: ISet<int>|
                abs(final(self).sync_state.e, doc, queue) == fresh(abs(old(self).sync_state.e, doc, queue), true),
            !old(self).exchanged ==> final(self).sync_state == old(self).sync_state,
    {
        if self.exchanged {                       // CHANGE C5
            self.sync_state.set_read_only(true);
            self.sync_state.set_read_only(false);
            // CHANGE C6: PeerDocState mirror updates (self.state.*, self.dirty) removed; they never write sync_state
            proof { assert forall|doc: ISet<int>, queue: ISet<int>| abs(self.sync_state.e, doc, queue) == fresh(abs(old(self).sync_state.e, doc, queue), true) by {
                let p0 = abs(old(self).sync_state.e, doc, queue); assert(p0.doc == doc && p0.queue == queue); } }
        }
    }
    // original: peer_doc_connection.rs:83 receive_sync_message
    // CHANGE C7: now/Duration/Instant and the PeerDocState mirror updates removed; result = Ok?
    pub fn receive_sync_message(&mut self, doc: &mut ADoc, msg: EMsg) -> (ok: bool)
        requires !old(self).sync_state.read_only,
        ensures !final(self).sync_state.read_only, final(self).can_write == old(self).can_write,
            recv_conf(the_d(), the_n(), aps(old(self).sync_state, *old(doc)), *old(doc), msg.view(), aps(final(self).sync_state, *final(doc)), *final(doc), ok),
    {
        let ok = am_receive(doc, &mut self.sync_state, msg);
        ok
    }

    // original: peer_doc_connection.rs:102 generate_sync_messages
    // CHANGE C8: PeerDocState mirror updates, timing, `dirty`, `now` removed; messages is Vec<EMsg>
    // CHANGE C9: `msg.heads != heads` is heads_ne on Vec<u64>
    #[verifier::exec_allows_no_decreases_clause] // GAP: termination of the loop is not proved
    pub fn generate_sync_messages(&mut self, doc: &ADoc) -> (messages: Vec<EMsg>)
        requires !old(self).sync_state.read_only,
        ensures !final(self).sync_state.read_only,
            batch_conf(the_d(), the_n(), aps(old(self).sync_state, *doc), aps(final(self).sync_state, *doc),
                       Seq::new(messages@.len(), |i: int| messages@[i].view())),
    {
        let heads = am_heads(doc);
        let mut messages: Vec<EMsg> = Vec::new();
        let ghost p0 = aps(self.sync_state, *doc);
        let ghost mut steps: Seq<BStep> = Seq::empty();
        loop
            invariant
                !self.sync_state.read_only,
                bok(the_d(), the_n(), p0, steps),
                brun(the_d(), the_n(), p0, steps) == (aps(self.sync_state, *doc), Seq::new(messages@.len(), |i: int| messages@[i].view())),
        {
            let ghost before = aps(self.sync_state, *doc);
            let r = am_generate(doc, &mut self.sync_state);
            proof {
                let (bloom, fake) = choose|bloom: ISet<int>, fake: bool|
                    doc.dset().difference(closure(the_d(), the_n(), old_shared(before))).subset_of(bloom)
                    && (aps(self.sync_state, *doc), oview(r)) == gen(the_d(), the_n(), before, bloom, fake);
                lemma_bstep(the_d(), the_n(), p0, steps, BStep::Gen { bloom, fake });
                steps = steps.push(BStep::Gen { bloom, fake });
            }
            match r {
                None => { break; }
                Some(msg) => {
                    let mh = emsg_heads(&msg);
                    let follow_up = heads_ne(&mh, &heads);
                    let ghost msgs_before = Seq::new(messages@.len(), |i: int| messages@[i].view());
                    let ghost pm = aps(self.sync_state, *doc);
                    let ghost mv = msg.view();
                    messages.push(msg);
                    proof { assert(Seq::new(messages@.len(), |i: int| messages@[i].view()) =~= msgs_before.push(mv)); }
                    if follow_up {
                        let mh2 = vec_copy(&mh);
                        self.sync_state.e.last_sent_heads = mh2;
                        proof {
                            lemma_bstep(the_d(), the_n(), p0, steps, BStep::Patch { h: vset(mh@) });
                            steps = steps.push(BStep::Patch { h: vset(mh@) });
                            assert(aps(self.sync_state, *doc) == Peer { last_sent_heads: vset(mh@), ..pm });
                        }
                    }
                    if !follow_up { break; }
                }
            }
        }
        proof { assert(batch_conf(the_d(), the_n(), p0, aps(self.sync_state, *doc), Seq::new(messages@.len(), |i: int| messages@[i].view()))); }
        messages
    }
}
}
