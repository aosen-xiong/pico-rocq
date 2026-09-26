# Semantic Immutability and Derived Caches

This document describes the semantic-immutability development built on top of
the PICO formalization (see [README.md](README.md) for the PICO claims). It
was developed on the `semantics-immutability` branch and ported onto the
flexible-overriding calculus of #21.

This repository mechanizes PICO and a semantic account of immutable objects
with racy derived caches.  The cache theorem is parametric in a weak
field-history memory interface.  A mechanized plain-access history fragment,
adapted from the Java Access Modes (JAM) model, now discharges the
same-field/read-from-history obligation for labeled PICO executions. One
ordered execution now combines construction, freeze/publish/acquire, and cache
accesses; its projections establish final-field snapshot observation and
plain-JAM legality. This is an explicit adequacy interface, not a full Java
Memory Model theorem. A narrow Java-facing action fragment now models
constructor-return freeze, reference publication/dereference, and plain cache
accesses and is proved to simulate the combined execution.

## Proof Story

```text
PICO typing and TS cache-initializer effects
  + Iris method pre/postconditions
  -> typed PICO core execution
  -> protocol-valid weak cache observations
  -> ghost-backed SemImmI preservation
  -> Iris NotStuck WP and adequacy
  -> safe execution and client-selected pure result refinement
```

A cache method is semantically invisible when it is correct for every
cache-read trace admitted by its cache protocol.  The proof separates:

- `StableAbs o a`: the provider says the object represents abstract value `a`;
- `CacheProtocol`: each cache field has a value protocol;
- whole-value per-field histories and read-from-history weak reads;
- `CacheSafeMethod`: method correctness for every valid observation trace;
- `SemImmI`: stable abstract state plus exclusive cache-history snapshot
  ownership, updated in place at the same ghost name.

## Typing, Concurrency, and Memory Models

The source TS judgment in `PICOBridge/PicoCacheTyping.v` checks that a cache
initializer reads only locals, arguments, and stable abstract fields and has
no direct shared writes.  A separate semantic computation obligation proves
that the initializer returns the deterministic derived value.  The cache write
itself remains racy, but is accepted only when the value satisfies the cache
protocol.

TS method summaries do not add an `ensures` construct to PICO. The installed
`PicoSemanticMethodContract` is the Iris pre/postcondition for the method.
`pico_ts_semantic_method_wfI` combines that contract with a checked `ts_stmt`
body, and `pico_ts_call_summary` permits TS calls only to methods listed in
the supplied summary. For inline cache computation,
`pico_ts_derived_computationI` combines the TS effect with the continuation-
aware Iris proof of the derived result, and
`pico_ts_derived_computation_direct_write_freeI` exports only the absence of a
direct shared field write. Functional correctness remains a separate Iris
premise.

The cache API uses `pico_callable_methodI`, whose postcondition is established
at the actual `KCall` return boundary before the caller continuation resumes;
`pico_exported_methodI` is this same callable contract. Typed PICO calls are
handled only by the resource LR, which consumes explicit runtime resolution
and derives callee-frame typing, heap extension, and qualifier-sensitive return
transfer. The closed
`pico_semantic_methodI` is used only by whole-execution adequacy examples. The
hash example proves its callable/exported contract from one TS/Iris computation package in
`pico_hash_callable_and_exported_with_computationI`.

PICO source syntax remains sequential. Semantic concurrency is supplied by
`PICOBridge/PicoSemanticConcurrency.v`: an external invocation pool installs
ordinary `SCall` controls and schedules their CESK steps over one shared heap
and weak field-history state. This layer records successful read/write access
events, defines conflicting-access races, and separates race reachability from
benignity (state-invariant preservation plus terminal result contracts). It
does not add `spawn`, `join`, or parallel composition to `stmt`.

`PICOBridge/PicoLabeledExecution.v` records every successful pool read/write
in execution order and erases back to the scheduler semantics.
`MemoryModels/JAM/` reconstructs the axiom-free plain JAM history semantics,
including explicit reads-from edges, transitive visibility, four derived
non-atomic coherence generators, and causality/coherence acyclicity. The bridge theorem
`jam_read_from_same_field_history` derives the whole-value field-history fact
used by the cache theory. `PICOBridge/PicoJamSimulation.v` relates labeled PICO
accesses to such JAM histories without guessing a reads-from source when
duplicate writes carry the same value.

`Examples/PicoSemanticConcurrencyExamples.v` closes the existential side for
two concrete source hash calls: both calls dynamically resolve the verified
method, both read the default before either write, and both append `Int 7` to
the same cache-field history. `Examples/PicoSemanticConcurrencySafety.v`
closes the universal side with a finite CESK phase invariant. Every scheduler
interleaving preserves the concrete `PicoCoreSemImmInstantiation` state
invariant, and every completed call returns `Int 7`. The combined endpoint is
`pico_two_hash_invocations_semimm_benign_race`.
`Examples/PicoJamHashAdequacy.v` strengthens that endpoint with one explicit
four-access scheduler execution, a legal plain-JAM realization in which both
default reads read from initialization, and the universal result theorem
`pico_hash_jam_admissible_results_correct`.  The combined endpoint is
`pico_hash_plain_jam_benign_race`.

`MemoryModels/JMM/FinalFieldPublication.v` models the publication obligation
independently: a location is frozen once, publication requires that frozen
snapshot, and an observer may acquire only a published frozen snapshot.
`PICOBridge/PicoFinalFieldPublication.v` connects an acquired snapshot to an
observer-indexed PICO stable abstraction.  The concrete endpoint
`pico_hash_published_plain_jam_benign_race` combines the receiver's
freeze/publish/acquire execution with the legal plain-JAM cache race.

`MemoryModels/JMM/JamPublicationExecution.v` places construction, freeze,
publish, acquire, and JAM access events in one ordered trace. Its legality
judgment requires every freeze to follow construction, every non-initial
access to follow a same-thread acquisition, a legal publication replay, and a
legal plain-JAM access projection. The remaining Java boundary is a simulation
from the complete JLS/JMM execution relation into the scoped fragment.

`MemoryModels/JMM/JlsCacheFragment.v` defines that scoped boundary.
Constructor return performs the final-snapshot freeze, publication must follow
freeze, each caller dereferences the published receiver before its accesses,
and the access projection must be plain-JAM legal. The theorem
`jls_cache_execution_simulates_combined` translates every legal fragment
execution into the combined model. Here “dereference” denotes the JLS
final-field observation boundary, not a Java acquire access mode.

`MemoryModels/JMM/EXTERNAL_MODEL_COMPATIBILITY.md` audits candidate external
Java memory-model developments obligation by obligation. The audit concludes
that upstream JAM can inform an axiom-free plain-history correspondence proof,
while Plan B is a stricter alternative memory model; neither currently
instantiates the complete-JMM projection interface.

`PICOBridge/PicoConstructionPublication.v` derives the freeze action from the
actual PICO construction boundary. A synchronized `SNew` step initializes the
ordinary heap and weak histories exactly as `PCS_New`, selects only declared
final fields from the constructor values, and freezes that post-allocation
snapshot. Its erasure theorem is the original CESK step. The concrete typed
hash allocation in `Examples/PicoConstructionPublicationExamples.v`
establishes the fresh receiver's cache-provider invariant and observer-visible
stable payload without a hand-built freeze premise.  The scheduler and JAM
fixtures use that same fresh receiver and post-allocation state.  The closed
endpoint `pico_hash_source_constructed_combined_benign_race` therefore runs
from typed `SNew` through one ordered publication/access execution to the legal
two-call benign race. `pico_hash_source_constructed_jls_fragment_benign_race`
adds the Java-facing fragment execution and its generic simulation proof.

## Main Files

Pure cache theory:

- `Core/GenericCacheProtocol.v`: protocols, histories, traces,
  `CacheSafeMethod`, semantic immutability, and pure refinement.
- `Core/CacheLRVerticalSlice.v`: source cache-method rule, local-copy proof,
  and rejected bad double-read shape.
- `Core/GenericDerivedCache.v`: the unknown-or-derived cache instance.

PICO core language and typing:

- `PICOBridge/PicoIrisCoreLanguage.v`: continuation machine with ordinary heap
  and weak field histories.
- `PICOBridge/PicoSemanticConcurrency.v`: source-independent invocation pool,
  shared-state scheduler, access/race semantics, and invariant composition.
- `PICOBridge/PicoLabeledExecution.v`: exact read/write access traces and
  erasure to pool execution.
- `MemoryModels/JAM/`: modern axiom-free plain JAM event/history, visibility,
  coherence legality, and the same-field history bridge. Visibility beyond the
  plain fragment remains separate.
- `MemoryModels/JMM/FinalFieldPublication.v`: axiom-free freeze, publication,
  and observer-acquisition machine for final snapshots.
- `MemoryModels/JMM/JamPublicationExecution.v`: one ordered lifecycle/access
  trace with final-publication and plain-JAM projections.
- `MemoryModels/JMM/JlsCacheFragment.v`: scoped constructor-return,
  publication/dereference, and plain-cache-access semantics with a generic
  simulation into the combined execution.
- `MemoryModels/JMM/JmmCacheAdequacyInterface.v`: the formal obligation for an
  external complete-JMM model: project every legal in-scope execution to a
  legal cache-fragment execution. Its proved corollaries recover combined
  legality and same-field history membership for every projected read.
- `MemoryModels/JMM/EXTERNAL_MODEL_COMPATIBILITY.md`: source-level audit and
  import gate for JAM, Plan B, and the normative JLS target.
- `PICOBridge/PicoFinalFieldPublication.v`: PICO final-field snapshots and the
  observer-indexed stable-abstraction bridge.
- `PICOBridge/PicoConstructionPublication.v`: synchronized `SNew`/freeze
  semantics and erasure back to the existing CESK allocation rule.
- `PICOBridge/PicoJamSimulation.v`: relational realization of PICO access
  traces by JAM executions with explicit reads-from choices.
- `Examples/PicoSemanticConcurrencyExamples.v`: closed two-call hash fixture
  and explicit default-read/double-write race execution.
- `Examples/PicoSemanticConcurrencySafety.v`: universal pool invariant,
  deterministic completed-call results, and the closed benign-race theorem.
- `Examples/PicoJamHashAdequacy.v`: concrete legal plain-JAM realization of
  the two-default-read/two-write race and the JAM-admissible result corollary.
- `Examples/PicoFinalFieldPublicationExamples.v`: concrete final-payload
  publication trace composed with the legal plain-JAM benign-race endpoint.
- `Examples/PicoConstructionPublicationExamples.v`: typed source allocation
  that initializes the concrete hash provider and freezes its final payload.
- `Examples/PicoCombinedMemoryExecution.v`: source-linked construction,
  two-observer acquisition, and the legal cache race in one event execution.
- `Examples/PicoJlsCacheFragmentAdequacy.v`: legal Java-facing fragment
  execution for the concrete hash race and its source-linked endpoint.
- `PICOBridge/PicoIrisCoreInvariant.v`: typed runtime environments, state
  well-formedness, progress, and one-step preservation.
- `PICOBridge/PicoIrisCoreWP.v`: primitive Iris WP lifting rules.
- `PICOBridge/PicoIrisTypingFundamental.v`: structural typing-directed WP
  rules for the complete statement grammar, parameterized by effectful
  primitive handlers.

Ghost-backed logical relation:

- `Iris/IrisSemanticBridge.v`: `SemImmI` and abstract cache read/write/method
  rules.
- `PICOBridge/PicoIrisSemImmOperations.v`: concrete PICO weak reads and writes
  connected to `SemImmI`.
- `PICOBridge/PicoIrisResourceLogicalRelation.v`: one linear, state-indexed
  semantic resource threaded through statement outcomes; includes the
  guarded-recursive call handler.
- `PICOBridge/PicoIrisSemanticAPI.v`: Iris method contracts, TS-checked
  semantic method environments, and TS derived-computation specifications.
- `PICOBridge/PicoIrisSemImmLogicalRelation.v`: the concrete SemImm world,
  history-read bridge, allocation rule, and protocol-admissible write rule.
  It deliberately does not turn ordinary PICO field-write typing into a
  SemImm-preserving statement rule.
- `PICOBridge/PicoIrisSemImmAdequacy.v`: safety adequacy and lifting of
  client-proved terminal postconditions.
- `Examples/PicoSemanticCacheAPIExamples.v`: the hash-cache API contract and
  concrete CESK/Iris proof of the local-copy implementation.  The closed
  `pico_hash_literal_model_api_wfI` theorem is only the literal test model; it combines ordinary method typing with
  the body WP without assuming a semantic-method premise.  The separate
  `pico_double_read_hash_trace_contract_refuted` theorem rejects the
  double-read trace contract.
  `pico_hash_read_then_finish_wpI` is the generic cache-control theorem: its
  miss path consumes any verified read-only derived computation.  The current
  concrete method supplies `pico_hash_literal_ts_computationI` as one instance.
  `pico_hash_method_semantic_with_computationI` lifts this abstraction through
  the complete local-declaration and method-contract boundary, while
  `pico_hash_verified_computation_api_wfI` combines it with ordinary
  `wf_method` obligations.
- `Examples/PicoHashExecutionTrace.v`: a cache-read-labeled CESK closure, the
  concrete double-read execution realizing `[Int H; Int 0]`, and an Iris
  adequacy proof that this execution cannot satisfy the deterministic method
  contract when `H <> 0`. `pico_double_read_callable_method_uninhabited` is the
  continuation-aware endpoint, and
  `pico_hash_witness_double_read_callable_uninhabited` instantiates it with a
  typed provider state whose cache history is `[Int 0; Int 7]`. The fresh
  `ownPGS` belongs to Iris physical-state adequacy and is distinct from the
  cache-history ghost name, which writes update in place.

`PICOBridge/PicoIrisTypingSupport.v` contains only the typed runtime-value and
environment lemmas reused by the split proof files. The canonical LR is the
resource/SemImm pipeline above. Its structural statement theorem is
parameterized by semantic handlers for reads, writes, allocation, and calls.
The guarded call handler closes recursive method reasoning, while cache APIs
must discharge the protocol-valid write handler; ordinary PICO typing alone
is intentionally insufficient. The retired pure-wrapper and pre-CESK Iris
facade files are not part of the source tree or project manifests.

## Public Endpoints

- `pico_core_resource_guarded_call_handlerI`: closes recursive calls with an
  Iris Löb argument over resolved typed method bodies.
- `pico_core_semimm_cache_read_from_history`: a mapped weak cache read yields
  a snapshot-backed cache observation.
- `pico_core_semimm_admissible_write_ruleI`: an unrelated-field write or a
  protocol-valid cache write preserves the semantic object; abstract-field
  writes are rejected.
- `pico_core_ownP_adequacy`: the generic `ownP` transport used after a
  method-specific SemImm-preserving WP has been proved; it does not establish
  SemImm preservation by itself.
- `pico_hash_method_semantic_with_computationI`: the concrete local-copy hash
  body satisfies its semantic method contract.
- `pico_hash_method_callable_with_computationI`: the same body satisfies the
  continuation-aware source-call contract.
- `pico_semantic_typed_call_wpI`: combines an advertised functional contract
  with qualifier-sensitive typed return transfer.
- `pico_heap_hash_callable_api_wfI`: packages the verified body as
  callable/exported contracts, conditional on source typing, override
  coherence, runtime cache assignability, and the verified computation API.
- `pico_heap_hash_api_call_wpI`: invokes that installed API from a typed caller
  under explicit class-table lookup and closed-dispatch premises.
- `pico_two_hash_invocations_semimm_benign_race`: two concrete calls exhibit
  a cache race while every interleaving preserves the concrete SemImm provider
  invariant and every completed call returns the derived hash.
- `pico_hash_plain_jam_benign_race`: the same race has one explicit legal
  plain-JAM realization whose reads-from edges target initialization.
- `pico_hash_jam_admissible_results_correct`: every terminating labeled PICO
  execution admitted by a legal plain-JAM realization satisfies the existing
  deterministic result contract.
- `pico_publication_execution_establishes_observer_stable_abs`: acquiring a
  published PICO final snapshot establishes observer-indexed stable state.
- `pico_hash_published_plain_jam_benign_race`: the concrete receiver is
  published with its final payload before the legal plain-JAM cache race.
- `pico_new_freeze_step_erases_to_core`: synchronized construction has exactly
  the existing `PCS_New` behavior after erasing publication state.
- `pico_hash_source_construction_publication_ready`: a typed concrete `SNew`
  establishes the fresh hash provider and observer-visible stable payload.
- `pico_hash_source_constructed_plain_jam_benign_race`: the source-allocated
  receiver is exactly the receiver used by the universal scheduler and legal
  plain-JAM race proofs.
- `pico_hash_source_constructed_combined_benign_race`: construction,
  freeze/publication, both caller acquisitions, and all JAM cache accesses form
  one legal ordered execution whose projections recover those proofs.
- `pico_hash_source_constructed_jls_fragment_benign_race`: constructor return,
  publication, both reference dereferences, and the plain cache race satisfy
  the scoped Java-facing fragment and simulate the combined endpoint.

The guarded call theorem derives resolved body typing, return-slot typing,
callee-frame typing, and qualifier-sensitive return transfer from source call
typing, dynamic lookup, `wf_method`, heap-type extension, and preserved callee
receiver identity. No caller-supplied call model remains.

The semantic object rules are parameterized by `PicoCoreSemImmInstantiation`. This is the
explicit proof that a particular PICO object representation, cache-field
adapter, and cache snapshot implement `StableAbs` and the cache protocol.
Publication is derived uniformly from protocol validity through
`cache_valid_published`. `pico_concrete_hash_semimm` derives the represented hash from the
tail of the tracked receiver's physical field list; field zero is the cache.
`pico_concrete_hash_provider_represents_heap` exposes that connection, while
`pico_concrete_hash_initial_state` constructs satisfying one-object states and
`pico_concrete_hash_provider_inhabited` gives a closed class-table, object, and
initial-history witness. Concretely, it uses a two-class table, object
`[Int 0; Int 7]`, and a nonconstant heap-derived hash. The witness table proves
provider satisfiability and contains no hash method; API installation is the
separate conditional theorem. Its write policy separates protected
abstract fields, protocol-checked cache fields, and unrelated framed fields.
This is intentionally a one-cache representation instance, not a general
layout for objects with multiple caches or ordinary non-abstract fields.
Ordinary PICO typing alone does not justify mapped-field writes, so the
artifact deliberately exposes no ordinary-typing-to-`SemImmI` theorem.

`pico_heap_hash_callable_api_wfI` connects this provider to the verified
computation API at the callable/exported boundary. Its object-indexed contract
requires this invocation's receiver to equal the tracked receiver; it makes no
global uniqueness assumption about typed environments.

Pure-result determinism is proved by the cache-aware trace judgment
(`CacheSafeMethod`) and directly by the local-copy WP. For the negative
example, `pico_double_read_cesk_matches_bad_trace` supplies a concrete
read-labeled CESK-to-trace witness and
`pico_double_read_cesk_refutes_contract_adequacy` transports the resulting
counterexecution through Iris adequacy. A language-wide trace extraction
theorem for arbitrary methods remains outside this example-specific bridge.
For the accepted path, `pico_local_copy_cesk_refines_trace_on_hit` and
`pico_local_copy_cesk_refines_trace_on_miss` connect both hit and
literal-recompute/write executions to valid traces and pure results. The
general verified-computation theorem is an Iris callable-method result, not a
generic CESK-to-trace extraction theorem.

Following the logical approach to type soundness, concrete source behavior is
proved at an API boundary rather than by an ordinary PICO typing rule:
`pico_callable_method_wfI` states that a method body inhabits its
continuation-aware advertised Iris contract, and
`pico_semantic_method_env_wfI` packages such proofs for clients.
`pico_semantic_typed_call_wpI` handles an already resolved successful branch:
typing derives its callee frame and override-coherent contract, the rule
performs `PCS_Call`, and the callable implementation returns normalized callee
typing, heap-extension, receiver, and state-validity evidence. The rule then
applies `pico_core_typed_resolved_method_return` before resuming the caller.
Runtime resolution and the contract precondition remain branch premises.
`pico_ts_call_summary` requires the same contract for every dispatchable
override. Ordinary unadvertised calls remain under the guarded resource LR.
`CacheSafeMethod` conservatively quantifies over every pointwise
protocol-valid trace, including traces a stricter coherent memory model may
exclude. It remains a separate generic trace theorem; the
artifact relates it to concrete execution only where an explicit labeled CESK
proof has been supplied.

`pico_heap_hash_api_call_wpI` is the concrete installation-to-client slice: it
assumes method lookup and closed dynamic dispatch, constructs the singleton
semantic environment from the proved callable body, invokes the combined call
rule, and returns both the hash postcondition and the typed caller environment.

## Memory Boundary

The memory model assumes:

The exhibited `history_cache_memory_model` is deliberately adversarial: a read
may return any complete value in the same field history. It is neither SC nor
a standard weak-memory model; it is the arbitrary-stale whole-value model used
by the conservative trace theorem.

- reads select one complete value from the same field's history;
- writes append one complete value;
- allocation initializes heap and weak-history state consistently, including
  the default value as the first complete history message;
- every nonempty field history admits a read (`CacheMemoryModelProgress`).

Initial/default values are observable only when allocation inserted them as an
initial history message. Empty histories admit no read.

This admits Java `int`, `boolean`, and reference cache fields at the atomicity
boundary.  Plain non-volatile `long` and `double` caches are excluded unless a
stronger atomic or synchronization mechanism supplies whole-value reads and
writes.  Object-valued caches additionally require a stable or safely
published referent protocol.
