# Derived Cache Proof Map

## Claim

A racy derived cache is semantically invisible when every method result is
correct for every cache-read trace admitted by the cache protocol.

```text
StableAbs(o,a)
  + CacheHistOK(P,o,a)
  + whole-value read-from-history execution
  + CacheSafeMethod(m,P,F)
  -> result = F(a,args)
  + cache validity is preserved
```

## Pure Core

| Paper role | Rocq definition or theorem | File |
|---|---|---|
| Stable provider state | `StableAbs` | `Core/GenericCacheProtocol.v` |
| Cache value protocol | `CacheProtocol` | `Core/GenericCacheProtocol.v` |
| Valid cache histories | `CacheHistOK`, `CacheHistSnapshotOK` | `Core/GenericCacheProtocol.v` |
| Valid observations | `ValidTrace` | `Core/GenericCacheProtocol.v` |
| Trace-robust method | `CacheSafeMethod` | `Core/GenericCacheProtocol.v` |
| Read validity | `cache_read_valid` | `Core/GenericCacheProtocol.v` |
| Semantic refinement | `cache_safe_method_sound` and related refinement theorems | `Core/GenericCacheProtocol.v` |
| Accepted source shape | local-copy cache rule | `Core/CacheLRVerticalSlice.v` |
| Rejected source shape | bad double-read counterexample | `Core/CacheLRVerticalSlice.v` |
| Plain JAM read source | `jam_read_from_same_field_history` | `MemoryModels/JAM/JamFieldHistoryBridge.v` |
| PICO/JAM access correspondence | `pico_read_realized_by_jam_history` | `PICOBridge/PicoJamSimulation.v` |
| Concrete JAM benign race | `pico_hash_plain_jam_benign_race` | `Examples/PicoJamHashAdequacy.v` |
| Final snapshot publication | `acquired_final_snapshot_is_frozen` | `MemoryModels/JMM/FinalFieldPublication.v` |
| Published PICO stable state | `pico_publication_execution_establishes_observer_stable_abs` | `PICOBridge/PicoFinalFieldPublication.v` |
| Published concrete JAM race | `pico_hash_published_plain_jam_benign_race` | `Examples/PicoFinalFieldPublicationExamples.v` |
| PICO construction/freeze simulation | `pico_new_freeze_step_erases_to_core` | `PICOBridge/PicoConstructionPublication.v` |
| Typed constructed hash provider | `pico_hash_source_construction_publication_ready` | `Examples/PicoConstructionPublicationExamples.v` |
| Source construction to legal benign race | `pico_hash_source_constructed_plain_jam_benign_race` | `Examples/PicoConstructionPublicationExamples.v` |
| Combined publication/JAM execution | `combined_memory_execution_legal` | `MemoryModels/JMM/JamPublicationExecution.v` |
| Source construction to one combined execution | `pico_hash_source_constructed_combined_benign_race` | `Examples/PicoCombinedMemoryExecution.v` |
| JLS cache-fragment simulation | `jls_cache_execution_simulates_combined` | `MemoryModels/JMM/JlsCacheFragment.v` |
| Source construction to scoped JLS fragment | `pico_hash_source_constructed_jls_fragment_benign_race` | `Examples/PicoJlsCacheFragmentAdequacy.v` |

The unknown-or-derived integer cache is an instance in
`Core/GenericDerivedCache.v`; it is not baked into the generic theorem.

## Source Obligations

`PICOBridge/PicoCacheTyping.v` defines the TS source effect judgment used for
cache initializers.  A TS initializer:

- reads only locals, arguments, and stable abstract fields;
- uses calls only through explicit TS summaries;
- performs no direct shared field writes;
- computes independently of racy cache values.

The key bridge is `ts_verified_cache_compute_write_safe`: a TS miss
computation followed by one protocol-valid cache write supplies the pure cache
method premise.

TS proves direct shared-write freedom for the abstract computation. It does
not inspect conflicts, publication, or callees, and does not claim
that the surrounding cache method is race-free; races on declared cache fields
are justified by the cache protocol.

Functional results are not PICO annotations. `PicoSemanticMethodContract`
provides the Iris pre/postcondition, while `pico_ts_semantic_method_wfI`
packages that contract with the checked TS body. `pico_ts_call_summary`
restricts TS calls to methods listed in the supplied effect summary.
`pico_ts_derived_computationI` is the corresponding inline-computation rule,
with `pico_ts_derived_computation_direct_write_freeI` exposing the checked effect.
Callable cache contracts are interpreted at the CESK `KCall` boundary and the
exported contract is the same continuation-aware proposition. Ordinary typed
calls are proved by the resource LR. Advertised calls use
`pico_semantic_typed_call_wpI`, which combines dynamic lookup, callee-frame
typing, the functional contract, heap extension, return typing, and caller
resumption. The local-copy hash proof exports its callable contract from the
same TS/Iris computation evidence, and `pico_heap_hash_api_call_wpI`
demonstrates a concrete typed client call.

## Iris Layer

`Iris/IrisSemanticBridge.v` defines:

```text
SemImmI(P,o,a,snapshot)
  = StableAbsI(o,a) * exclusive valid snapshot ownership
```

Its read and write rules expose protocol validity and preserve `SemImmI`; a
write updates the snapshot at the same ghost name.
`PICOBridge/PicoIrisSemImmOperations.v` connects those abstract rules to
concrete PICO weak-history reads and writes.

The full statement-grammar LR, parameterized by semantic primitive handlers,
is split as follows:

| Layer | Responsibility |
|---|---|
| `PicoIrisCoreLanguage.v` | PICO continuation machine and weak-history state |
| `PicoIrisCoreInvariant.v` | typed environments, state invariant, progress/preservation |
| `PicoIrisTypingFundamental.v` | structural typing-directed WP rules |
| `PicoIrisResourceLogicalRelation.v` | linear resource outcomes and recursive calls |
| `PicoIrisSemImmLogicalRelation.v` | Concrete SemImm world, history-read bridge, allocation, and admissible-write rules |
| `PicoIrisSemImmAdequacy.v` | Generic own-state Iris adequacy bridge |
| `PicoIrisSemanticAPI.v` | Bespoke semantic method and class API boundary |
| `PicoSemanticCacheAPIExamples.v` | Concrete local-copy CESK/WP installation, ordinarily typed double-read source, and trace-level rejection |
| `PicoHashExecutionTrace.v` | Read-labeled concrete double-read execution and Iris adequacy refutation |

The canonical endpoints are:

- `cache_read_valid`
- `cache_safe_method_refines_pure`
- `pico_core_resource_stmt_fundamentalI`
- `pico_core_typed_resolved_method_return`
- `pico_semantic_typed_call_wpI`
- `pico_core_semimm_read_ruleI`
- `pico_core_semimm_admissible_write_ruleI`
- `pico_core_ownP_adequacy`
- `pico_heap_hash_callable_api_wfI`
- `pico_heap_hash_api_call_wpI`
- `pico_local_copy_cesk_refines_trace_on_hit`
- `pico_local_copy_cesk_refines_trace_on_miss`
- `pico_double_read_callable_method_uninhabited`
- `pico_hash_witness_double_read_callable_uninhabited`
- `pico_concrete_hash_provider_inhabited`

Recursive calls are not supplied as a WP assumption.  The theorem
`pico_core_resource_guarded_call_handlerI` uses Iris Löb induction: after the
concrete call step, it verifies the resolved body with the recursive LR,
extracts the typed return value, and executes the return continuation.

## Trusted Boundary

There are no added Rocq axioms or admitted proofs.  The theorem signatures
make these model interfaces explicit:

- `CacheMemoryModel`: per-field whole-value histories and append writes;
- `jam_plain_legal`: an axiom-free reconstruction of plain JAM histories,
  reads-from visibility, derived non-atomic coherence, and both acyclicity
  obligations discharges same-field reads-from for realized PICO traces;
- `final_publication_steps`: an axiom-free freeze/publish/acquire interface;
  consistency proves that every observer acquisition returns the location's
  frozen snapshot. It is the target of, not a replacement for, a JLS
  constructor/final-field adequacy proof;
- `combined_memory_execution_legal`: a single ordered construction,
  freeze/publish/acquire, and cache-access trace whose projections satisfy the
  final-publication interface and plain-JAM legality; non-initial accesses must
  follow acquisition by their executing thread;
- `jls_cache_execution_legal`: the scoped Java-facing constructor-return,
  reference publication/dereference, and plain-access fragment. Its generic
  simulation theorem derives `combined_memory_execution_legal`; it is not the
  complete JLS/JMM execution relation;
- `JmmCacheProjectionAdequate`: the remaining external-model obligation. A
  complete JMM instantiation must project every legal execution satisfying its
  explicit cache-admissibility scope to `jls_cache_execution_legal`;
- `CacheMemoryModelProgress`: reads exist for nonempty histories;
- `PicoCoreSemImmInstantiation`: provider, cache-adapter, and
  weak-history-to-snapshot interface on a reachable-state invariant;
- `pico_concrete_hash_semimm`: concrete integer hash-cache provider, with
  heap-derived abstract state, `pico_concrete_hash_initial_state` constructing
  valid initial states, and `pico_concrete_hash_provider_inhabited` exhibiting
  a closed two-class/object/history witness with object `[Int 0; Int 7]` and a
  nonconstant heap-derived hash. The witness table contains no hash method;
- `pico_heap_hash_callable_api_wfI`: conditionally packages the provider and
  verified body as callable/exported contracts under source typing, override,
  assignability, and verified-computation premises;
- `history_cache_memory_model` and
  `history_cache_memory_model_progress`: canonical whole-value history reads
  and a concrete nonempty-history progress instance;
- Calls: resolved bodies, callee frames, and qualifier-sensitive return
  transfer are derived from typing, lookup, `wf_method`, heap-type extension,
  and CESK receiver continuity;
- Iris and Rocq kernels and libraries.

The publication bridge strengthens physical `pico_stable_abs` with an
observer-indexed observation fact. Its core-StableAbs corollary is only a
projection; the operational content is the stronger theorem
`pico_publication_execution_establishes_observer_stable_abs`.

PICO construction is connected by `pico_new_freeze_step`. Its source side is
the existing `SNew` transition: constructor arguments become the complete
field vector, heap allocation and weak-history initialization happen together,
and selected fields must satisfy `final_fields`. The erasure theorem returns
exactly `PCS_New`; publication and observer acquisition remain later actions.
The concrete hash witness additionally proves ordinary source typing and the
fresh receiver's `pico_hash_provider_inv`.  The concurrent scheduler, final
publication witness, and JAM events are all indexed by that same receiver.
`pico_hash_source_constructed_combined_benign_race` strengthens the previous
composition by placing lifecycle and access events in one ordered execution;
its projections recover final publication and the existing legal JAM race.

The concrete hash provider's abstract hash is defined by a PICO derivation
method, not a Rocq function on field values. `pico_hash_provider_inv` fixes a
reference heap in which the method returns the hash on the receiver. It then
requires every later heap to agree with that reference heap on the receiver's
abstract footprint (`abs_agree` over `reachable_abs`). Unrelated writes, cache
writes and allocation preserve this agreement.
`pico_concrete_hash_provider_represents_heap` shows that the method still
returns exactly the hash in every provider state.
`pico_concrete_hash_cache_valid_is_derivation_value` shows that the Iris hash
protocol's valid values are exactly the derivation-defined ones
(`derivation_cache_value`). The witness method `pico_hash_derive_method_def`
reads the final payload field.

The concurrent example's cached hash method computes its value the same way,
with `pico_hash_read_compute_stmt` (`cache_tmp = this.payload`), not a literal.
The provider invariant also records that every weak history in the footprint
is nonempty and holds only the reference value, so every weak read of the
payload returns the hash. `pico_derived_computation_atI` is a derived-computation
judgment for frames whose receiver satisfies a predicate; the hash API now
takes it. `pico_hash_read_computationI` proves the payload read is such a
computation, and `pico_hash_concurrent_method_api_wfI` installs the
concurrent method through the Iris API with no computation premise. The
concurrent safety, JAM, JLS and publication examples run the same method.
Their access lists include each thread's payload read. The race schedule,
the JAM execution, the combined trace and the JLS fragment all record six
accesses in the same order: two cache reads, two payload reads, two cache
writes. The constructor initializes both the cache and the payload.
`combined_final_field_read_sees_snapshot` is the general final-field
guarantee for combined executions. Its extra condition,
`combined_final_fields_initialized`, says each final field of a frozen
location has exactly one write: the constructor's initialization, before the
freeze, with the snapshot's value. So no final field is written after its
freeze. Under that condition, every plain read of a final field follows its
thread's acquire of the location, reads from that initialization, and returns
the field's value in the acquired snapshot, which is the frozen snapshot.
`pico_hash_combined_payload_reads_observe_snapshot` is its instance for the
hash receiver, whose only final field is the payload. The condition is checked
on the concrete trace; it is not yet derived from PICO typing, and the JLS
fragment's legality does not include it. The race
schedule is still existential: the scheduler steps between listed accesses
are not proved to be free of other accesses. `pico_pool_access_trace` is the
relation that would make the list complete.
`PicoHashExecutionTrace` still uses the literal compute, since it is about the
double-read bug for an arbitrary hash.

`pico_heap_hash_api_call_wpI` additionally assumes source call typing, method
lookup, closed dispatch, a typed caller/state, and the verified computation
contract before constructing the singleton semantic environment.

The CESK receiver invariant and heap-type extension prevent the call proof
from transferring a return value across an unrelated frame or arbitrary
post-heap. Return transfer is now a derived PICO theorem, not a public model
assumption.

## Atomicity

The field-history theorem assumes one read observes one complete message in
the same field history. Allocation records the initial/default value as the
first message; an empty history is unreadable. It therefore rejects torn plain
non-volatile Java `long` and `double` caches by default.  Atomic primitive
fields, references, volatile accesses, atomics, synchronization, or a
separately verified multi-field protocol can satisfy the boundary.  An atomic
reference still requires the referenced cached object to be stably initialized
or safely published.

## Non-Claims

- No full Java/JMM-to-core adequacy theorem. The scoped JLS cache-fragment
  simulation does not formalize the complete JLS causality, happens-before,
  synchronization-order, or dereference-chain rules.
- No claim that arbitrary PICO field writes are protocol-valid cache writes.
- No whole-class contextual equivalence theorem.
- The source grammar and CESK machine include `SIfZero`, and the local-copy and
  rejected double-read shapes are represented in `PicoIfZeroCacheExamples.v`.
  The double-read counterexample is connected to a concrete labeled CESK
  execution and Iris adequacy in `PicoHashExecutionTrace.v`; a language-wide
  trace extraction theorem remains out of scope.
- `pico_local_copy_cesk_refines_trace_on_hit` and
  `pico_local_copy_cesk_refines_trace_on_miss` supply positive bridges for the
  hit and literal-recompute/write paths. The general computation contract is
  proved through the Iris callable API rather than these trace lemmas.
- No deterministic final cache contents; only deterministic specified method
  results and semantic invisibility of cache state.

## Verification

```sh
dune build @default
make check
python3 scripts/check-no-axioms-admits.py .
git diff --check
```
