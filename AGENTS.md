# PICO Rocq proof notes

## Viewpoint adaptation invariant

For field mutability adaptation, keep this equation fixed:

```text
RO |> RDM_f = Lost
```

It is **not** `RO`. A readonly receiver does not retain the authority carried
by a receiver-dependent-mutable field.

Before reasoning about an `RDM_f` read through an `RO` receiver, use the
authoritative regression lemma:

```coq
vpa_mutability_field_readonly_state_ro_rdm_is_lost
```

in `ViewpointAdaptation.v`. Do not construct a counterexample or proof step
that assumes such a read has type `RO`.

The corresponding `Mut_f` case in ReadonlyState is also `Lost`:

```coq
vpa_mutability_field_readonly_state_ro_mut_is_lost
```

In particular, explicit `Assignable` controls whether a field slot may be
updated, but does not change the adapted type of the slot.  A `Mut` value
therefore cannot be published through a `Mut_f` field of an `RO` receiver.

This applies to examples, informal explanations, and Rocq proofs alike:
an expression such as `p.next`, where `p : RO` and `next : RDM_f`, has
qualifier `Lost`.  It therefore cannot be used as an `RO`, `RDM`, or `Mut`
reference, and an assignment justified by treating it as one is not a valid
counterexample.

## Flexible-call color staging

Do not put prospective joins from different call phases into one transitive
graph. In particular, a pending return edge must not let a suspended caller
color enter a fresh callee allocation and then traverse that allocation's
`Mut_f` fields: the return occurs only after the callee body has finished.

The authority-sensitive design is temporally stratified:

1. Maintain a prospective closure separately for each live frame. It contains
   actual forward retained edges and the RDM-root joins possible in that
   frame.
2. Do not include a call-return edge while the callee body is executing.
3. Treat call pop as the transition that constructs and verifies the resumed
   caller's closure.

Do not reconstruct a suspended caller's earlier phase by closing its roots
over the callee's current heap.  In particular, a definition of the form

```text
close(final_heap, suspended_caller, ...)
```

is temporally invalid: field edges created by the callee would become visible
retroactively in the caller phase.  Carry the caller's completed color set as
a frozen proof-only snapshot at call entry instead.  Nested execution may
transform that snapshot forward through each newly entered frame, but may not
recompute an earlier frame closure against a later heap.

Index frozen snapshots with one proof-only slot per operational call
boundary. Use `Some colors` for a tracked exceptional boundary and `None`
for a pre-existing or untracked boundary. Exact slot/stack alignment is
required so that pop always removes the head slot. At the start of a public
preservation invocation, every existing boundary receives `None`; therefore
this indexing creates no public premise.

For nested tracked calls, the new head must summarize the dangerous current
colors of every older tracked slot as well as the immediate caller's colors.
Maintain the private pairwise invariant that each tracked head covers every
older tracked slot beneath it.  It is vacuous for the public theorem's
initial `None` slots, is preserved when all slots advance through the same
phase closure, and survives pop by dropping the head.  Without this summary,
the head return classifier cannot justify an older frozen color that reaches
the nested call's fresh return location.  Never repair that gap with a new
public premise or by reconstructing an older caller phase on the final heap.

Set inclusion is not the whole nested invariant.  A newer frozen color may
arrive at an older snapshot's captured resume root, thereby activating the
older caller's prospective RDM-join exposure.  Maintain a second private
pairwise certificate: for every newer/older tracked pair, such a source is
either an older entry color or the older exposure avoids the protected zone.
At nested return, distinguish historical activation using this certificate
from genuinely callee-created mutable components using the tracked
boundary's allocation cutoff.  The latter cannot reach an older resume root.
Do not weaken this conditional certificate to mere per-location
non-membership, and do not expose it as a public theorem premise.
Set inclusion alone is not caller-origin evidence.  When an older color is
imported into the nested head, retain a proof-local derivation that identifies
it as an older frozen base.  If a caller-frame join first moves that color
into the fresh return root, classify the return as join-introduced and peel
that predecessor when the return later becomes a join source.  Do not treat
the imported color as immediate caller incoming, and do not manufacture a
current-heap origin path for historical authority whose path may have been
severed by a legal overwrite.

The immediate caller's completed color set is a third nested-entry case; it
is not interchangeable with the active frame's independent colors.  It may
contain authority inherited through the phase incoming set.  When proving a
new tracked head safe against older snapshots, classify its frozen-snapshot
seeds with the pairwise certificate, and classify its immediate-caller seeds
with a separate private completion/resume certificate.  Never discharge the
latter by simply calling all completed caller colors independently active.
That shortcut loses inherited provenance and would amount to hiding a missing
premise.

The policy-only witness stack participates in this nesting recursively.
A newly pushed policy witness must summarize both the ordinary frozen
snapshot tail and every older policy witness beneath it.  An older policy
witness can contain inherited caller authority even when the corresponding
ordinary slot is `None`; therefore summarizing only the ordinary snapshots
loses provenance at the next pop.  Maintain pairwise coverage and
resume-safety among policy witnesses themselves, advance the retained policy
witness tail through the resumed frame exactly when the ordinary snapshot
tail is advanced, and use the popped head as the proof-local mediator for
that transition.  Do not leave the policy tail in the completed-callee phase
and do not repair the gap with a public premise.

Each tracked slot stores both immutable entry colors and phase-current
colors. Freeze only dangerous caller authority (`FlowPowered` or
`FlowProspective`); do not freeze neutral bookkeeping colors. `FlowNeutral`
means authority was forgotten, and later promotion at a callee-owned
location is independent callee authority, not retroactive caller authority.

Do not require global disjointness between a frozen caller color and the
active frame's independent color set.  That property is not inductive under
allocation.  A readonly callee may first allocate a fresh `Mut` object `b`
and then allocate a runtime-mutable `RDM` object with an `RDM_f` constructor
argument from the caller and a `Mut_f` constructor argument `b`.  The frozen
caller color legitimately reaches `b` through the fresh object while `b`
also carries independent callee authority.  This overlap is harmless because
it was created after the protected history cutoff.

The replacement invariant must express the theorem's actual obligation:
frozen dangerous colors avoid the protected zone.  Preserve it with an
origin-coverage disjunction: a newly observed frozen color is justified
either by the preceding frozen snapshot or by independently active authority.
The main phase invariant already proves that the latter avoids the protected
zone.  This permits harmless multi-origin overlap without adding a premise to
dispatch or to the public preservation theorem.  At channel-free entry the
independent set is empty, so the initial coverage fact remains derived.

Protected-zone avoidance is sufficient for atomic statements but is not by
itself a complete pop invariant.  When the caller resumes, its RDM-root frame
joins become active again.  A callee-origin color at one unchanged caller RDM
root could then join another caller RDM root only at pop.  Therefore retain a
proof-only snapshot of the suspended caller's RDM roots (or an equivalent
root-scoped provenance relation).  The precise condition is pairwise: if
independent callee provenance reaches one resume root, no protected resume
root may be available as its caller-frame join target.  Do not forbid active
provenance at every resume root unconditionally; that would reject harmless
executions when the caller has no protected RDM join target.  Scope the
condition to resume roots, not to every heap location, so fresh caller/callee
overlap remains legitimate.  Capture and maintain this relation internally;
it must not become a dispatch or public-theorem premise.

An RDM-only graph is insufficient because, once an RDM join becomes actual,
authority may continue forward through the joined root's `Mut_f` descendants.
A single cross-frame graph with `Mut_f` is also insufficient because it loses
the temporal order above.

Consequently, "the join target root is outside the protected zone" is not a
strong enough pop condition.  A non-protected target root may already have a
retained `Mut_f` path into the protected zone.  The captured resume summary
must instead classify the target root's caller-phase prospective closure (or
an equivalent frozen exposure set), and reject active callee provenance at a
join source whenever any compatible target closure reaches the protected
zone.  This summary is private ghost state established at call entry; never
turn it into a method, dispatch, or public preservation-theorem premise.

The target exposure summary alone does not identify why authority reached a
resume source.  Preserve a second private, root-scoped provenance fact: a
dangerous frozen color at a resume source is either already represented at
the snapshot's caller entry or is justified by independently active callee
authority.  The entry-derived case was already closed under the caller's
frame joins before suspension; the active-derived case is checked against
the frozen exposure summary.  Do not collapse these two cases into one
unconditional exposure restriction, which would reject harmless suspended
callers whose RDM components touch the protected zone but never receive new
callee authority.

For the entry-derived source case, preserve the lockstep relation between the
two frozen images: if a dangerous caller-entry color reaches a captured
resume root, then the snapshot's current resume-exposure colors are included
in its current caller colors.  This holds initially because the caller phase
had already performed every RDM-root join, and it remains true because both
sets are advanced by the same phase closure.  At pop, protected-zone
avoidance for current caller colors then discharges the whole exposure path.
Do not replace this relational invariant with unconditional exposure
avoidance; the latter is unnecessarily strong.

At pop, distinguish captured caller RDM roots from the return location newly
installed into an RDM destination.  The latter did not exist as a caller root
at call entry and therefore cannot be assumed to belong to the captured root
set.  Do not forbid a covariant `Mut` overriding return merely to avoid this
case, and do not add a public preservation premise.  Preserve the completed
caller color set as immutable snapshot metadata.  For joins among captured
roots, use the frozen resume-exposure certificate.  For a new return root,
derive the required non-overlap directionally from the body-local confinement
and provenance argument: independent callee authority is demoted at return,
and frozen caller authority cannot acquire a fresh return origin by reversing
an unavailable path.  In particular, do not use `potential_connected_sym`.

Keep the caller-origin evidence used for this argument private.  A callee
color is not, by itself, evidence that the resumed caller may exercise that
authority: independently owned callee authority is demoted at return.  Thread
an existential caller-origin witness through the internal frozen-suffix and
join lemmas, construct it from the existing typing and history hypotheses,
and eliminate it before restating the public preservation theorem.  The
public theorem's premises and conclusion are a fixed interface; do not add a
dispatch condition, a return restriction, or any ghost-invariant premise to
that interface.

A bare existential caller-origin path is not sufficient as the sole tracked
classification.  A dangerous snapshot color may first cross the newly live
caller RDM join into the return root; the resulting return color is also a
callee color, but the snapshot stores membership rather than the historical
seed/path needed to reconstruct the bare existential.  Preserve the internal
derivation instead: distinguish snapshot, completed-callee, and safe-exposure
bases, and record each frozen non-join and caller-frame join.  Prove return
safety by induction on this derivation, so a return-root source created by an
earlier join can be reduced to its strictly smaller predecessor derivation.
This derivation is proof-local and must be eliminated before the public
theorem.

Retain a stack-aligned age certificate for each tracked snapshot: every
captured resume root and every state in the completed caller colors existed
strictly before that boundary's entry cutoff.  The fact follows from runtime
mutability/well-formedness at call entry, is unchanged by snapshot advance,
and is discarded with the boundary at pop.  Keep it in the strengthened
internal induction package, not in the public theorem.

Split return-pop classification by caller authority.  Under `Mut_r`, every
post-call RDM root is caller-owned, and call-return reflection makes it
powered in the completed callee; all RDM joins then classify directly.  The
directional fresh-component argument is needed only under `Imm_r`, where a
fresh RDM result is not independently owned by the resumed caller.

Do not implement that split by globally requiring `frame_authority = Mut_r`
on dangerous RDM frame-join constructors.  That gate is too coarse:
readonly-state execution may still update `Assignable` fields, and the
pre-update RDM join is what prevents an already-colored endpoint from being
merged silently with a protected RDM endpoint.  Authority sensitivity must
therefore be localized to call return.  When the new return root already has
a dangerous completed-callee color, classify the caller join using that
color plus the smaller derivation's caller-origin witness.  The remaining
fresh-return direction must peel the derivation back across the join that
introduced the new root; do not replace it with current-heap reachability to
an entry root, because a legal overwrite can sever such a path while frozen
color provenance remains valid.

Nested pop must advance both an older snapshot's current colors and its
current resume-exposure colors through the resumed caller.  A certificate
that the pre-pop exposure avoids the protected zone is not, by itself,
closed under this second transition: the resumed caller can add a new RDM
join involving the return root.  Preserve a proof-local derivation/classifier
for exposure advancement as well as for ordinary snapshot colors.  Its bases
are the old exposure, completed-callee colors, and already-certified safe
exposure; its join case must reuse the same strictly-smaller predecessor
argument.  Do not pretend that `advance_frozen_caller_snapshot` leaves the
current exposure unchanged, and do not strengthen the public theorem to
paper over this nested-return obligation.

The second-order exposure obligation is discharged by the stack-aligned
callee-side freshness partition, not by making every latent exposure an
actual frozen color.  A tracked channel-free entry has neither a capability
root nor an RDM root, so its mutable-authority components are initially
vacuous.  Safe nested calls reflect every callee mutable-authority root to a
caller mutable-authority root, preserving each enclosing boundary cutoff.
Thread this private partition through the statement induction and use it at
pop when a newly installed return root meets a suspended caller root.  This
avoids both unconditional exposure safety and any new public premise.

## Approved call-pop target policy

The later design decision is to make caller-frame RDM joining directional at
resume.  Under `Mut_r`, the resumed frame has its ordinary RDM join behavior.
Under `Imm_r`, the target of a resumed-frame join must be a location in the
saved pre-call caller RDM-root set.  A fresh RDM return may carry neutral
component identity toward an old captured root, but old caller authority must
not be projected into that fresh return root.  Persist the saved target policy
as private per-frame ghost state for the remainder of the resumed frame; do
not apply it only at the instant of pop and then restore unrestricted joining.

This decision supersedes the earlier instruction above to discharge the
old-to-fresh return direction with a recursive fresh-return classifier.  The
classifier remains useful for paths whose target is captured and for nested
snapshot transport, but it is not a license to reintroduce an immutable
old-authority-to-fresh-return join.  The public theorem statement remains
unchanged and receives no policy, dispatch, or provenance premise.

## Immutable RDM return: no heap-wide fresh-source rule

Do not discharge the final immutable-authority call-pop branch by
postulating a heap-wide rule saying that every non-join step into the fresh
suffix has a fresh source.  **Legal allocation can create an edge between a
fresh object and an old reference**, so that rule is not a semantic
invariant of the language.  Concretely, do not instantiate
`untracked_immutable_resumed_call_pop_safe_from_witness` that way.

The required proof is target-directed instead.  Under immutable authority
every frame-join target is one of the captured pre-call RDM roots.  The
evolved policy witness classifies authority arriving at such a root by its
current resume exposure, while its prospective-component partition prevents
a callee-side fresh component from reaching an older protected resume root.
That classification is proof-local and must be eliminated before the public
preservation theorem.

The surviving machinery for this lives in `PotentialCapabilityRDMPop.v`
(salvaged from the retired `PotentialCapabilityRDMCall.v`).  Its combinator
`classified_rdm_call_pop_merge_safe` reduces the whole RDM-destination pop
obligation to exactly one residual case: `caller_authority = Imm_r` with a
covariant `Mut` body return.  The other shapes are proved directionally --
`mutable_rdm_call_pop_merge_safe` notes explicitly that no symmetry of
`potential_connected` is used.  That residual case is the open obligation
behind `PotentialCapability.v`'s call branch; it exists because flexible
overriding admits covariant `Mut` returns, and per the note above it must
not be dodged by forbidding them.

## Closing the Imm_r / covariant-Mut call-pop residual

`call_pop_bridge` has two orientations.  The one whose protected endpoint
hangs off the return dies immediately: a covariant `Mut` body return is a
`Mut` root of the completed callee, hence one of its live capabilities
(`typed_mut_root_is_active_live_capability`), and `potential_colors_separated`
finishes it.  That orientation is proved.

The other orientation -- `capability ->* return` together with
`receiver ->* protected` -- is the real obligation.  Two routes are dead ends
and must not be retried:

1. `potential_connected_sym`.  The relation is not symmetric: `potential_adjacent`
   follows retained mut edges forward but only current mutable edges backward,
   and a legal overwrite severs the latter.
2. "Nothing entry-reachable can reach the fresh return."  This is **false**.
   `potential_frame_edge` joins *any two* RDM roots of a live frame with no
   authority condition, so an old RDM root and a freshly allocated RDM local
   of the callee are adjacent, and the fresh region is reachable.

The correct argument is a collapse into the receiver case, forward-only.
Under `Imm_r` with `signature_has_no_mutable_roots` the callee can never
obtain `Mut` authority on an old object: both `RDM |> Mut_f` and
`RO |> Mut_f` are `Lost`.  Hence it creates no old-to-fresh retained mut
edge, and *every* crossing into the fresh region is a frame edge at an RDM
root.  Every such root is frame-joined to the receiver:

  - callee RDM roots, when the callee receiver is RDM-typed: the receiver is
    then itself a callee RDM root, so the frame edge exists in the callee
    frame;
  - an RDM parameter: `ST_Call_readonly_state`'s `Harg_sub` forces the
    argument type below `vpa_mutability_tt_readonly_state Ty T`, which for an
    RDM receiver and RDM parameter is `RDM`.  So the argument object is a
    *caller* RDM root and is frame-joined to the receiver in the caller
    frame, which is a live frame member across the boundary;
  - an `RO` receiver derives no RDM roots at all, since `RO |> RDM_f = Lost`
    and `Lost` is unusable.

So `capability ->* return` forces `capability ->* receiver`, which is the
third `Hpropagate` case and is discharged against the callee's own
separation invariant.  The counterexample refutes itself: the very frame
edge that reaches the fresh return also reaches the receiver.

Do not close this by gating `potential_frame_edge` under `Imm_r`.  That would
leave the public theorem's text unchanged while shrinking
`potential_connected`, and therefore weaken what
`successful_stmt_preserves_potential_history` asserts.  The statement is a
fixed interface.

### Correction: old-to-fresh heap crossings do exist

Do not try to prove that a readonly-state callee creates no old-to-fresh
retained mut edge.  That is false.  `retained_mut_edge` has two
constructors, and `retained_edge_rdm` goes through `mutable_edge` on an
`RDM_f` field.  Since `RDM |> RDM_f = RDM`, the callee may legitimately store
a fresh RDM object into an `RDM_f` field of an old runtime-mutable object.

Only the `Mut_f` route is blocked, and only because `Mut |> Mut_f = Mut` is
the single non-`Lost` entry, so a `Mut_f` write needs a `Mut`-typed receiver
variable -- and every `Mut`-typed variable of this callee holds a fresh
location.

Derive that freshness from the local induction instance, not from the phased
formalism.  `principled_phased_local_mut_root_is_fresh` needs
`principled_phased_authority_live_history_state`, and no bridge to it exists
in the kept files.  Instead instantiate the statement IH a second time with
`P = Z = body_initial_reachable` and `cutoff = dom h`; then `env_is_confined`
puts every value of the callee env in `body_initial_reachable` or above the
cutoff, and applying the local separation reflexively to a `Mut` root
excludes the first.

The uniform statement to prove is therefore not "no old-to-fresh edge" but:

  every old-to-fresh crossing, whether a frame edge or an `RDM_f` heap edge,
  occurs at an RDM root,

which `boundary_caller_rdm_roots_are_connected` then joins to the receiver,
collapsing into the already-discharged receiver case.

### Why the graph formalism cannot close the Imm_r residual

Four strategies have been tried and all four fail at the same constructor:

1. `potential_connected_sym` -- false: `potential_adjacent` follows retained
   mut edges forward but only current mutable edges backward.
2. "nothing entry-reachable reaches the fresh return" -- false:
   `potential_frame_edge` joins any two RDM roots with no authority
   condition.
3. "a readonly-state callee creates no old-to-fresh retained mut edge" --
   false: `retained_edge_rdm` goes through `mutable_edge` on an `RDM_f`
   field and `RDM |> RDM_f = RDM`.
4. "every old-to-fresh crossing occurs at an RDM root" -- true for
   `potential_frame_edge` and `potential_return_edge`, false for the heap
   constructors.

The frame and return constructors are fine every time; the `RDM_f` heap
crossing kills every attempt.  The obstruction is structural rather than
tactical: `retained_mut_edge` and `mutable_edge` are relations on the final
heap and record no provenance.  They do not say which variable or viewpoint
performed the write, and that variable may be dead by the end of the body,
so no property of the *final* frame can be recovered from the edge.

The collapse argument therefore cannot be completed in the potential-graph
formalism.  Provenance is what `executing_authority_color_set` and the
frozen-snapshot machinery exist to track, which is why the immutable branch
is stated against `executing_resumed_authority_color_set` and the saved
target policy.  Closing this residual requires either a color-to-graph
bridge or reinstating enough policy infrastructure to apply
`immutable_rdm_evolved_policy_head_pop_safe`; both are recoverable from tag
`wip-snapshot-2026-08-03`.

The two lemmas salvaged from these attempts --
`boundary_caller_rdm_roots_are_connected` and
`potential_local_mut_root_is_fresh` -- are sound and reusable in either
route.

### Route C: the colour-to-graph bridge

The per-case machinery for both private layers survives in the kept files and
is axiom-free: `private_fresh_frozen_statement_after_{assignment,local,new,
field_write}`, `..._enter_call_channel_free`, `..._after_{nonnull,null}_
return_parts`, and on the policy side `initial_/enter_/leave_private_frame_
join_policies_valid` plus `private_policy_statement_after_{tracked,untracked}_
pop_from_parts`.  What the retired chain contributed was the induction that
threaded them, not the mathematics.  Rebuilding that thread needs no admit.

The one genuinely new obligation is the bridge

  executing_resumed_authority_call_pop_safe  ->  call_pop_merge_safe

Sketch, refuting the hard orientation `capability ->* return` with
`receiver ->* protected`:

1. `capability` is a capability root of the post frame, hence
   `frame_owned_location`, hence `FlowPowered` in the resumed caller colour
   set -- this is the `Howned` premise of
   `immutable_rdm_evolved_policy_head_pop_safe`.
2. propagate that colour along `capability ->* return_location`;
3. cross the pop join `return_location -- receiver`, whose target lies in the
   saved pre-call RDM roots (`eligible`);
4. propagate along `receiver ->* protected`;
5. pop safety then forces reflection into the callee colour set, and the
   callee's own `executing_authority_colors_separated` contradicts
   `protected` being in Z.

Steps 2 and 4 need the converse of
`authority_color_connected_is_potential_connected`.  That converse's only gap
is `potential_return_edge`: the colour relation has heap and frame steps and
no return step.  `potential_return_edge` requires
`boundary_callee_return_qualifier = RDM`, and in this branch
`sqtype body_return_type = Mut` with `body_return_type <= mret runtime_sig`
forces `sqtype (mret runtime_sig)` into `{Mut, RO}`.  So the head boundary
contributes no return edge precisely in the case that needs the bridge.
Return edges at deeper pre-existing boundaries are the remaining open part.

### The real shape of the colour/graph gap

Return edges are not the crux of the bridge.  The prior obstacle is join
scoping:

  * `potential_connected CT h active stack` closes frame joins over *every*
    live frame, via `potential_frame_edge active stack`;
  * `phased_authority_frame_step CT h frame` -- and hence
    `executing_authority_color_set` -- is parameterised by a *single* frame.
    Its heap steps are stack-independent, but its joins are frame-local.

So a stack-wide potential path may traverse a caller-frame join that has no
counterpart in the callee's colour closure.  Such colours can only enter the
callee's set through `callee_incoming`.

That is precisely what the frozen-snapshot/incoming discipline constructs,
and what the retired statement-level chain existed to thread through the
body.  Any bridge from `executing_resumed_authority_call_pop_safe` to
`call_pop_merge_safe` therefore has to reconstruct that discipline; it is not
a single lemma about return edges.

Reusable results proved while establishing this:

  boundary_caller_rdm_roots_are_connected
  potential_local_mut_root_is_fresh
  potential_connected_is_authority_color_connected_without_return
  no_return_edge_when_callee_return_not_rdm

All four are axiom-free and independent of which route is finally taken.

### Route C1: the combined threading induction

Every invariant route C needs is constructible from `potential_live_history_state`;
the entry bridges all survive in `PotentialCapabilityCore.v`:

  potential_live_history_starts_principled_phased_authority     :6372
  potential_live_history_starts_principled_frozen_authority     :6406
  potential_live_history_starts_private_fresh_frozen_statement  :6549

The remaining work is one induction over `eval_stmt` threading four
invariants *simultaneously*:

  potential_live_history_state                     (already the main theorem)
  principled_phased_authority_live_history_state
  private_fresh_frozen_statement_state
  private_frame_join_policies_valid

They must be threaded together, not in sequence: the return case of the
frozen layer (`private_fresh_frozen_statement_after_nonnull_return_parts`)
requires `principled_phased_authority_live_history_state` for the *caller
post* frame, which is itself a post-call fact.  This mutual dependency at the
call case is why the retired `Statement.v` threaded them jointly.

Per-case pieces, all surviving and axiom-free:

  atomic   private_fresh_frozen_statement_after_{local,assignment,new,field_write}
  entry    private_fresh_frozen_statement_enter_call_{channel_free,untracked}
           principled_phased_authority_history_enter_call
  return   private_fresh_frozen_statement_after_{nonnull,null}_return_parts
           private_policy_statement_after_{tracked,untracked}_pop_from_parts
  policy   initial_/enter_/leave_private_frame_join_policies_valid

The covariant `Mut` return branch takes the *channel-free* entry: by
`refined_mut_return_call_has_channel_free_entry_shape` the callee receiver
qualifier is forced to `RO` and the callee entry frame has no RDM roots, so
`private_fresh_frozen_statement_enter_call_channel_free` applies and yields
the `Some`-headed snapshot list that
`immutable_rdm_evolved_policy_head_pop_safe` requires.

No step of this needs an admit: every piece it builds on is `Qed`.

### The origins-alignment obstacle, and why the retired entry was not axiom-free

`private_statement_enter_call_channel_free` (Private.v:7714) depends on
`Classical_Prop.classic`.  So does the retired chain's channel-free entry,
which contained the line

  assert (witness_origins = origins) by apply proof_irrelevance.

The cause is structural.  Each layer's call-entry lemma builds its boundary
with `Build_call_boundary_origins ... Hwf ...`, extracting `Hwf` from *its
own* invariant.  `watched_boundary` is a `Type` record whose last field is
`boundary_origins : call_boundary_origins ... : Prop`, so two boundaries that
differ only in that proof term are propositionally distinct.  Combining the
layers into one state over one boundary therefore requires identifying two
proofs of the same `Prop`, which needs proof irrelevance.

This matters because `scripts/check-public-assumptions.py` fails on any
global axiom, and commit 71815d0 removed classical assumptions on purpose.
An axiom-free route C cannot use `private_statement_enter_call_channel_free`
or reproduce its `proof_irrelevance` step.  Note the *single-layer* lemmas
are clean: `private_fresh_frozen_statement_enter_call_channel_free` is
`Closed under the global context`.

Three ways out, in increasing order of blast radius:

1. Prove `_with_origins` variants of the per-layer entry lemmas that take the
   boundary (hence the origins proof) as input rather than existentially
   producing it, so all layers share one term by construction.
2. Prove one combined entry lemma directly, extracting `wf_r_config` once and
   building the origins once, at the cost of redoing the entry proofs.
3. Move `call_boundary_origins` from `Prop` to `SProp`, making the two proofs
   definitionally equal so alignment is `reflexivity`.  This changes no
   statement's meaning -- the record is proof-carrying only -- but it is a
   core definition change in `WatchedFrames.v`.

Option 1 is the smallest and keeps every existing proof intact.

### C1 must be parameterised by the call rule, not sequenced with it

The threading induction's call case cannot be completed before the pop-safety
results.  Every layer's leave lemma consumes a pop-safety certificate:
`principled_phased_authority_history_leave_call_null` and `..._nonnull`
require `executing_authority_call_pop_safe`, and the frozen return-parts
lemmas require `private_frozen_snapshot_return_safety` together with the
phased state for the caller-post frame.

So C1 and the bridge are mutually dependent, and neither "C4 first" nor "C1
first" is right.  This is exactly why the retired development stated

  private_advancing_policy_eval_preserves_from_call_rule :
    private_advancing_policy_successful_call_rule ->
    private_advancing_policy_eval_preserves

taking the call rule as a *hypothesis*, with `CallRule.v` discharging it from
the null and non-null cases separately.  Any reconstruction must adopt the
same shape: state the induction parameterised by the call rule, prove it, and
discharge the call rule independently.

Progress so far on the induction (scratch, not committed because the call
case is incomplete): skip, local, var-assign, field-write, new and sequencing
are proved; the call case has its untracked frozen entry, its policy entry
onto the *same* boundary, and the inductive hypothesis on the body all
working.  What remains inside it is exactly the return step, which is where
the call-rule hypothesis has to enter.

### C3: the induction must also carry the reflection summary

Discharging `private_call_pop_call_rule` needs call-pop safety, and the only
route to it is

  executing_authority_call_pop_safe_from_old_colors_reflected_or_outside
    (Private.v:14269)

whose second premise is

  executing_authority_old_colors_reflected_or_outside CT Z
    caller_h caller caller_incoming callee_h caller_post caller_incoming

This cannot be obtained from the post-state's own separation: that is exactly
what the pop is trying to establish, so
`executing_authority_colors_separated_implies_old_colors_reflected_or_outside`
(Core.v:1066) is circular here.  The summary has to be *produced by the
induction*, which is why the retired statement result was a conjunction --
the private state together with the reflection summary -- rather than the
state alone.

So `private_call_pop_state_preserved_from_call_rule` needs its conclusion
strengthened to also yield

  executing_authority_old_colors_reflected_or_outside CT Z h
    (mk_watched_frame authority sGamma  rGamma ) incoming
    h' (mk_watched_frame authority sGamma' rGamma') incoming

Support that survives:
  - structural: `..._refl` (Core.v:1034), `..._trans` (Core.v:1044),
    `executing_authority_old_colors_reflected_implies_or_outside`
    (Core.v:1022);
  - the sequencing case is exactly `..._trans`;
  - the per-statement colour machinery is in `PotentialCapabilityAtomic.v`
    (`phased_authority_colors_after_null_field_update`,
    `..._after_non_rdm_field_update`, `phased_colors_after_*`,
    `pending_call_colors_after_heap_change`, and neighbours).

The per-case reflection lemmas themselves did not survive and must be
re-proved from that machinery.  None of it needs an admit.

### C4: neither colour closure covers the potential graph's frame joins

Sharper statement of the join-scoping gap.  Three relations, three different
join scopes:

  * `phased_authority_frame_step CT h frame` -- joins among the RDM roots of
    that single frame;
  * `resumed_authority_frame_step CT h eligible caller` -- joins among the
    RDM roots of the *caller* frame, gated by `resumed_frame_join_target`;
  * `potential_frame_edge active stack` -- joins among the RDM roots of
    *every* live frame, i.e. the active frame and every suspended caller
    reachable through the boundaries.

`call_pop_merge_safe` is stated over
`potential_connected callee (boundary :: stack)`, so its paths may use both
callee-frame and caller-frame joins.  The phased closure sees only the
former, the resumed closure only the latter.  There is therefore no single
colour closure for a `potential_connected` path to be replayed in, and the
bridge cannot be obtained by choosing a different target relation.

Closing C4 needs a genuinely new construction: either a combined closure that
admits joins from every live frame, or a segment-wise argument that splits a
potential path at frame boundaries and applies the phased and resumed
closures to alternating segments.  Neither exists in the development.  This
is the one remaining piece of the residual with no located strategy.

### The Imm_r residual: the RS publication argument

The strategy that works is not to replay a potential path in the colour
formalism (see the join-scoping note above -- that cannot work).  It is to
characterise what a readonly-state body can publish.

`mut_into_readonly_state_field_is_ro_or_mut_receiver` (proved): if a `Mut`
value fits a field under readonly-state adaptation then either the field is
`RO_f` or the receiver variable is `Mut`.  Those are the two disjuncts:

  * `RO_f` -- the slot adapts to `RO`, so the value fits, but the stored
    reference is readonly and `retained_mut_edge` follows only `RDM_f` and
    `Mut_f`.  The write adds no mutable connectivity at all.
  * otherwise -- the receiver is `Mut`-typed, and
    `potential_local_mut_root_is_fresh` shows every `Mut`-typed variable of
    this callee denotes a freshly allocated object.

So every mutable *predecessor* of the `Mut` return is fresh.  Note this does
not say the callee creates no old-to-fresh edges: it does, via ordinary
`RDM_f` writes, and that is legal and harmless.  What it cannot do is put a
`Mut`-authority value anywhere an old object can mutably reach.

The remaining formal step is the induction that lifts the single-edge fact to
a path:

  forall CT sGamma rGamma h stmt rGamma' h' return_location source,
    eval_stmt CT rGamma h stmt OK rGamma' h' ->
    <return_location is a Mut root of the final frame> ->
    dom h <= return_location ->
    mutable_connected CT h' source return_location ->
    dom h <= source.

Backward along the path, each edge into a `Mut`-authority-carrying location
was written through a `Mut` receiver, hence from a fresh source.  With it, the
first conjunct of `call_pop_bridge` dies: `capability` is old and cannot
mutably reach the return.  The existing component lemmas run forward
(`principled_local_mut_result_component_is_fresh`) and do not give this;
`potential_connected_to_fresh_is_fresh` is about `dom h` exactly, not about
freshness across a call.

### The Imm_r residual: the complete argument

Orientation A of `call_pop_bridge` (`capability ->* receiver` with
`return ->* protected`) is proved: the covariant `Mut` return is a `Mut` root
of the completed callee, hence a live capability, and
`potential_colors_separated` finishes it.

Orientation B (`capability ->* return` with `receiver ->* protected`) dies on
its first conjunct.  Only three kinds of step can arrive at the return:

1. a heap edge into it -- some `RDM_f`/`Mut_f` field holds the return.  By
   `mut_into_readonly_state_field_is_ro_or_mut_receiver` a `Mut` value fits
   such a slot only through a `Mut` receiver (the `RO_f` escape is excluded
   because `retained_mut_edge` does not follow `RO_f`), and by
   `potential_local_mut_root_is_fresh` every `Mut`-typed variable of this
   callee is fresh.  So the source is fresh.
2. a backward step inside its own component -- `mutable_connected` is the
   closure of a symmetric adjacency, and
   `principled_local_mut_result_component_source_is_fresh` bounds that whole
   component to fresh locations.
3. a frame join.  This is the case that defeated every earlier attempt, and
   it closes on channel-freeness.
   `refined_mut_return_call_has_channel_free_entry_shape` proves the callee
   entry frame has *no* RDM roots, and the body cannot create an old one: its
   receiver is `RO` and `RO |> RDM_f = Lost`, so it can never hold an old
   object at RDM type.  Every RDM root of the callee frame is therefore
   fresh, and callee-frame joins connect only fresh locations.  Caller-frame
   joins connect only old caller roots, which can enter the return's
   component only through case 1.

So nothing old reaches the return.  Note what this does *not* claim: the body
does create old-to-fresh edges, by ordinary `RDM_f` writes, and that is legal
and harmless.  What it cannot do is put `Mut` authority anywhere an old
object reaches.

## The restored RO/RDM call rule: repair map

The published artifact (de48a09) has, in both `SCall` rules:

    Hrcv_sub : Ty <= vpa(Ty, mreceiver)
               \/ (sqtype Ty = RO /\ sq mreceiver = RDM /\
                   base_subtype CT (sctype Ty) (sctype mreceiver))

The disjunct was silently dropped during the pre-snapshot proof effort,
narrowing `stmt_typing` under every theorem.  It is now restored (f020677).
Nobody has ever proved the combination special-rule x flexible-overriding:
master's special-branch proofs used signature EQUALITY at dispatch
(`runtime_call_signature_agrees`), which flexible overriding replaced with
refinement.  Known repair obligations, in dependency order:

1. `callee_frame_wf_abs` / `callee_frame_wf_rs_ts` (Preservation.v) must take
   the disjunctive premise again.  In the special branch the dynamic receiver
   qualifier is only refinement-bounded: static RDM gives
   `qc2q qc <= sq dyn-receiver`, so dyn is `qc2q qc` or `RO`.  Receiver-var
   typability for dyn = Mut or Imm is NOT automatic -- it follows from bound
   agreement: `wf_rtypeuse` forces every instance of a Mut_c-bounded class to
   be `Mut_r` (and Imm_c / Imm_r), and flexible subclassing makes bounds
   hereditary except under RDM_c, so the dynamic class's bound matches the
   declaring class's.  This bound-agreement step is the genuinely new lemma.

2. `safe_typed_call_static_result` and everything downstream that inverts
   `Hrcv_sub` as a plain subtype.  In the covariant-Mut-return residual the
   special branch is REFUTABLE at the top call: the RDM destination forces
   `sqtype receiver_type = RDM` (refined_call_rdm_result_classifies_body_
   return), contradicting `sqtype Ty = RO`.  So the residual's top-level
   analysis survives; only its lemma statements need the disjunction threaded
   or refuted.

3. `rs_mutable_freshness_preserved`'s call case: the special rule lets a
   nested frame hold an OLD object at declared-RDM receiver type, so J as
   stated fails at such entries.  What survives, by the channel analysis:
   an RO view adapts every argument channel to RO/Imm and every return
   channel to RO/Imm, so special-rule frames can never receive or return
   outer Mut values at write-capable types.  Writes through old-RDM `this`:
   the value channel is `RDM |> RDM_f = RDM`, but assignability gates it --
   `vpa_assignability(RDM, RDA)` is not `Assignable`, so Final/RDA fields of
   old objects remain unwritable (readonly_state_preservation is therefore
   semantically unaffected).  Explicitly-`Assignable` `RDM_f` fields CAN be
   stitched: an old `Mut_r` object may acquire an edge to a fresh `Mut_r`
   object created inside a special-rule frame.  Hence:
     - L weakens to Final/RDA-assignability fields only;
     - the old-stays-old walk gains a crossing case: an
       explicitly-Assignable RDM_f edge into special-frame-created fresh
       structure.  The repair is an ownership argument: members of the outer
       frame's Mut components are never named at Mut/RDM by any other frame
       (they can only travel through RO/Imm channels), so the stitched
       structure cannot contain the covariant Mut return, and the walk can
       conclude "old or stitched-but-return-free" instead of "old".

4. J itself weakens: RDM-typed variables may hold old objects exactly when
   the value shares the frame receiver's runtime context (already a wf fact);
   the Mut half of J is unchanged -- no channel ever passes an old object at
   Mut type.

Do NOT re-narrow the typing rule to make proofs pass; that repeats the
original silent weakening.

### Restored-rule triage, session end state

Repaired and committed: callee_frame_wf_rs_ts / callee_frame_wf_abs
(Preservation.v) -- disjunctive premise, special branch closed by RDM's
universal runtime-typability.  Preservation.v compiles.

Next casualty, and it is semantic: safe_call_callee_rdm_root_origin
(ForwardCapabilityHistory.v:191).  Its conclusion

    sqtype Ty = Mut \/ sqtype Ty = Imm \/ sqtype Ty = RDM

is FALSE under the special rule: the callee's receiver-derived RDM root
reflects to the caller's y at sqtype Ty = RO.  The conclusion must gain the
RO case, which flows into rdm_roots_reflect_through_view and the boundary
origins record -- i.e. the callee's RDM roots are no longer guaranteed to
reflect to non-readonly caller roots.  This is where the ownership rework of
items 3-4 begins, not a mechanical thread-the-disjunction site.

Everything after ForwardCapabilityHistory.v in the build order is untested
against the restored rule.

### Restored-rule triage: FCH origin lemma reshaped

safe_call_callee_rdm_root_origin now concludes

  ((sqtype Ty = Mut \/ Imm \/ RDM) /\ typed_root (sqtype Ty) caller root)
  \/ (sqtype Ty = RO /\ root = ly /\ typed_root RO caller root)

matching the RO branch that rdm_roots_reflect_through_view always had: under
the special call the receiver is the callee's ONLY RDM root (RO-view
parameter channels adapt RDM to Lost, so params hold no locations at RDM),
and it reflects to the caller at RO.  The lemma and its special branch are
proved; the plain-branch sites just gained `left`.

REMAINING: its five consumers must handle the new RO case --
  ForwardCapabilityHistory.v:~470 (two uses, in one separation lemma; in the
    RO case both roots coincide with ly),
  AuthorityHistory.v:856, LiveCapabilityStack.v:642,
  PotentialCapabilityPrivate.v:5449.
Then continue make -k.  After FCH, the same reshaping will be needed wherever
the origins record is CONSTRUCTED for a special call (the RO branch of
rdm_roots_reflect_through_view finally becomes reachable), and then items 3-4
of the repair map (the freshness invariant under the restored rule).
