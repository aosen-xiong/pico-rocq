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
| `PicoIrisSemImmLogicalRelation.v` | Pointwise SemImm read, allocation, and admissible-write rules |
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

- No Java/JMM-to-core adequacy theorem.
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
