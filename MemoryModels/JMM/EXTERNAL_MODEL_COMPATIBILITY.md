# External Java Memory-Model Compatibility

This note evaluates existing Rocq/Coq Java memory-model developments against
the obligation stated by `JmmCacheProjectionAdequate` in
`JmmCacheAdequacyInterface.v`. It is an import decision record, not an
adequacy claim.

## Decision

Do not import either candidate as a complete JMM instance.

- **JAM** is the closest reusable model for cache-access histories. Its event,
  reads-from, trace-order, and coherence definitions can inform a correspondence
  proof for the local plain-JAM layer. It has no constructor/final-field
  semantics, however, and its published Coq development uses assumptions that
  are incompatible with this artifact's no-axiom policy.
- **Plan B** models a broader Java execution language, but deliberately defines
  BMM, a restriction of the JMM, and forbids unsafe publication instead of
  formalizing the JLS final-field rules. It therefore cannot instantiate a
  theorem quantified over all relevant JMM-legal executions. The paper's
  official artifact URL is no longer reachable, so its Coq sources could not be
  audited.
- **JLS Chapter 17** remains the authoritative target for final-field and JMM
  behavior, but it is a prose specification rather than reusable Rocq code.

The next justified integration is a small, axiom-free correspondence theorem
from the plain subset of upstream JAM histories to the local `jam_plain_legal`
judgment. Final-field publication remains a separate projection obligation.

## Candidate Sources

| Candidate | Audited material | Semantic status |
|---|---|---|
| Bender--Palsberg JAM | Coq repository commit `9d70010634b5494e0e4203f2ccb1d69308e2a3f8`; `coq/Syntax.v`, `coq/Dynamic.v`, `coq/Hwf.v`, `coq/History.v` | Formal model of Java access modes, not the complete JLS/JMM |
| Demange et al. Plan B | POPL 2013 paper; artifact URL printed as `http://r.cs.purdue.edu/bmm` | Alternative Buffered Memory Model; BMM executions are claimed to be a subset of JMM executions |
| JLS 17 | Java Language Specification, Chapter 17, especially Sections 17.4--17.5 | Normative prose target, not a proof-assistant development |

Primary sources:

- JAM project and paper: <https://www.johnbender.us/research/oopsla-2019/>
- JAM source: <https://bitbucket.org/ucla-pls/jam>
- Plan B paper: <https://janvitek.org/pubs/popl13.pdf>
- JLS Chapter 17: <https://docs.oracle.com/javase/specs/jls/se26/html/jls-17.html>

## Obligation Matrix

Legend: **yes** means directly represented; **adapter** means a proof-preserving
encoding is plausible; **missing** means the candidate has no corresponding
semantics; **blocking** means the candidate cannot establish the stated
obligation without a new theorem or a change of claim.

| `JmmCacheProjectionAdequate` obligation | Upstream JAM Coq | Plan B / BMM | Current artifact |
|---|---|---|---|
| External execution and legality judgment | **yes**: event histories, `trco`, and `hok` | **yes** in the paper: axiomatic BMM and operational BMMo | **yes** for the scoped JLS cache fragment only |
| Plain cache reads and writes | **yes**: `plain`, `ac_read`, `ac_write` | **yes**: non-volatile read/write actions | **yes**: `JamPlain` events |
| Explicit reads-from source | **yes**: `ev_rf` and `rf` | **yes**: execution write-observation function `W` | **yes**: `jam_reads_from` |
| Same-location read source | **yes**: `trco_rf` requires source and read at one location | **yes** at the axiomatic execution level | **yes**: `jam_rf_shapes` |
| Read value equals complete source-write value | **adapter**: reads execute through an `ev_rf`; value transport must be extracted from the term semantics | **adapter**: `W` supplies the observed write, but whole-value admissibility depends on Java type/access width | **yes**: explicit `jam_same_value` premise |
| Whole-value atomicity classification | **missing**: locations carry natural values and no Java field-type classification | **partial**: the paper explicitly models potentially non-atomic `long`/`double` | **yes** as a scoped admissibility premise |
| Object-and-field address identity | **adapter**: JAM locations are abstract naturals | **adapter**: abstract addresses can encode object-field pairs | **yes**: `FieldAddr` |
| Default initialization write | **adapter**: initialization events exist, but not Java object allocation/default-field initialization | **partial**: well-typed initial values and per-thread allocation pools | **yes** in the scoped fragment and JAM projection |
| Program/trace order and causality | **yes**: `po`, `to`, visibility, coherence, and acyclicity | **yes**: program order, synchronization order, happens-before, and BMM reorderings | **partial**: enough for the scoped combined trace, not complete JMM causality |
| Out-of-thin-air exclusion | **partial**: history execution and acyclicity constrain reads, but this is JAM legality, not JLS causality | **yes for BMM**, not a proof about every JMM-legal execution | **yes within the scoped fragment** through grounded reads-from |
| Constructor completion and final-field freeze | **missing** | **blocking**: unsafe publication is forbidden rather than modeled with JLS final-field semantics | **yes** in `FinalFieldPublication.v` and `JlsCacheFragment.v` |
| Publication and dereference-chain rule | **missing** | **blocking** for JLS 17.5: safe publication is a model restriction | **partial**: explicit publication/dereference events, but no full JLS derivation |
| Source Java/PICO action projection | **missing** | **missing** for PICO and unavailable for source audit | **partial**: PICO construction and cache accesses reach the scoped fragment |
| Proves every relevant JMM-legal execution projects | **blocking** | **blocking**: BMM is intentionally stricter than JMM | **open**: exactly `JmmCacheProjectionAdequate` |
| Compatible with the no-axiom policy | **no**: the source contains several declared axioms, including `spo_before`, finite/infinite carrier assumptions, and substitution interface assumptions | **unknown**: source unavailable for audit | **yes**: checked by the artifact audit |
| Current Rocq toolchain compatibility | **no direct import**: project specifies Coq 8.6.1 | **unknown** | **yes** |

## JAM Source Audit

The useful upstream definitions are structurally close to the local model:

- `coq/Syntax.v` defines `plain`, `opaque`, `relacq`, and `vol` modes and
  read/write actions over locations.
- `coq/Dynamic.v` defines `reads`, `writes`, program order `po`, trace order
  `to`, reads-from `rf`, visibility, and coherence.
- `coq/Hwf.v` defines trace coherence `trco` and history well-formedness `hok`.
- `coq/History.v` proves properties such as `rf_wf_prop`, which recovers one
  location containing both the source write and target read.

A direct import is unsuitable. Besides abstract carrier assumptions in
`coq/PreSyntax.v` and substitution-interface assumptions, `coq/Dynamic.v`
declares `spo_before` as an axiom. Those assumptions may be reasonable model
parameters, but importing them would make this artifact's no-axiom theorem
audit fail and would not add final-field publication.

The local `MemoryModels/JAM` development should therefore remain the canonical
plain-cache model. A later correspondence proof may translate the upstream
plain event subset into local events and prove that upstream trace coherence
implies local history well-formedness. It must re-prove every imported fact
needed by the cache endpoint in current Rocq.

## Plan B Source Audit

The Plan B paper is broader operationally than JAM: it discusses Java values,
references, allocation pools, default initialization, locks, thread lifecycle,
volatile accesses, and potentially split `long`/`double` accesses. This makes it
useful design evidence for event generation and atomicity classification.

It is not the missing JLS adequacy model. The paper explicitly defines BMM as a
more restrictive alternative whose legal executions are included in the JMM.
For final fields it forbids unsafe publication, rather than reproducing the JLS
freeze and dereference-chain semantics. Consequently, a BMM adapter could prove
the cache theorem for BMM executions, but it could not prove
`JmmCacheProjectionAdequate` for all in-scope JMM executions.

The paper points to an online Coq development at
`http://r.cs.purdue.edu/bmm`. That host is currently unresolved, and no
author-maintained source mirror was found. Claims about the Coq artifact's
assumptions or exact theorem statements must therefore remain unknown.

## Import Gate

External code should be imported only if all of the following hold:

1. Its source is available at a fixed revision and builds on a supportable Rocq
   version.
2. The exact theorem used by the bridge has no axioms or admissions, including
   transitive dependencies.
3. Its legality judgment entails grounded, same-field, whole-value reads for
   the admitted cache-field classes.
4. It formalizes, or is paired with a proved projection for, constructor
   completion, final-field freeze, publication, and dereference chains.
5. A source/action translation connects PICO or the Java fragment to that
   legality judgment.

Neither audited candidate currently passes this gate. The scientific claim
should remain conditional on `JmmCacheProjectionAdequate` rather than calling
the current fragment a full JMM instantiation.
