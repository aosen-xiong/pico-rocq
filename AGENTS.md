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
