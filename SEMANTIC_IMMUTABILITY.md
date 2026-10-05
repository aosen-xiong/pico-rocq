# Semantic Immutability

This document describes the semantic-immutability development built on top of
the PICO formalization (see [README.md](README.md) for the PICO claims).

An immutable object may contain lazily initialized cache fields that are
written after construction, read and written without synchronization, and
read under weak memory. The development states what such an object must
satisfy and proves it for PICO. Everything is plain Rocq: there is no program
logic framework, and every public theorem is closed under the global context.

## Proof story

```text
PICO type system (big-step, sequential)            Generic cache theory
  typing, preservation, abstract-state               protocols, traces, histories,
  preservation, no mutation exception                trace-robust methods, refinement
            |                                                   |
            v                                                   v
Small-step core machine with weak field histories   Rely-guarantee specification
  CESK controls, call frames, run-time               one interference relation is both
  assignability check                                rely and guarantee
            |                                                   |
            +---------------------+-----------------------------+
                                  v
                Invocation pool: any number of threads,
                any interleaving; the parallel rule
                                  |
        +-------------------------+--------------------------+
        v                         v                          v
Type safety under          Derivation methods         Concurrent hash calls
interleaving               stable under every         preserve the invariant and
                           interleaving               return the hash
```

## Two correctness conditions

1. *Cache-independent results.* A method returns the same result whether or
   not a cache is filled, for every combination of values its reads may
   return (trace robustness).
2. *Derived values.* Every value written to a cache field is computed from
   the abstract state by a derivation method, so all threads that find a
   cached value find the same one.

## File map

Generic theory (`Core/`), independent of PICO:

- `GenericCacheProtocol.v`: cache protocols, histories, valid traces,
  trace-robust methods (`CacheSafeMethod`), refinement to pure recomputation.
- `RelyGuarantee.v`: the interference relation, stability of semantic
  immutability, derived protocols and agreement of cached values.
- `SequentialModel.v`: the sequential specialization; the double-read method
  is correct sequentially although it is not trace robust.
- `CacheLRVerticalSlice.v`, `GenericDerivedCache.v`: the local-copy rule, the
  source cache-method judgment and its fundamental theorem, the double-read
  counterexample.

PICO instance (`PICOBridge/`):

- `PicoCoreLanguage.v`: the small-step CESK machine over a heap and weak
  field histories.
- `PicoCoreInvariant.v`, `PicoCoreTypingSupport.v`, `PicoCoreTyping.v`: typed
  environments, the state invariant, and typing lemmas for each statement
  form, including call entry and return.
- `PicoSemanticConcurrency.v`: the invocation pool, labeled events, races,
  and the parallel rule `pool_rely_guarantee`.
- `PicoCoreTypeSafety.v`: type safety under interleaving. A typed pool stays
  typed (`typed_pool_preservation`), every field history stays typed
  (`typed_pool_histories_typed`), no thread raises the mutation exception
  (`typed_pool_no_mutation_exception`), and every unfinished thread can take
  a step (`typed_pool_progress`).
- `PicoCoreTraceRobust.v`: trace robustness stated for controls of the
  machine, for an arbitrary protocol and provider. From a pool of trace
  robust controls, every execution preserves semantic immutability
  (`machine_trace_robust_semimm`), every weak read of a cache field is valid
  (`machine_cache_read_valid`), and every finished control meets its
  contract (`machine_trace_robust_results`).
- `PicoStableAbsPreservation.v`: abstract-state preservation on the machine
  and on every scheduler execution.
- `PicoDerivationNoninterference.v`, `PicoDerivationCache.v`,
  `PicoDerivationSmallStep.v`: derivation methods, their noninterference in
  the big-step and small-step semantics, and stability under every
  interleaving.
- `PicoDerivationPrefix.v`: derivation code under interference
  (`deriv_prefix`). A run whose steps start from different states that agree
  with the reference heap on the footprint is still running without having
  written a field, has finished with the environment of its sequential
  evaluation in the reference heap, or has ended with an exception.
- `PicoCoreSemImm.v`: providers that connect an object's representation to a
  cache protocol.
- `PicoCacheTyping.v`, `PicoLabeledExecution.v`, `ConcurrentPico.v`,
  `WeakPico.v`: cache typing and the earlier event-level models.

Memory models (`MemoryModels/`, `PICOBridge/PicoJamSimulation.v`,
`PICOBridge/Pico*Publication.v`): a plain-access fragment of Java Access
Modes, final-field publication, the combined execution, a Java-facing
fragment with its simulation, and the interface for an external JMM
projection. This is an adequacy interface, not a Java Memory Model theorem.

Examples (`Examples/`):

- `PicoHashMethod.v`, `PicoConcreteHashProvider.v`: the hash method and its
  derivation-defined provider.
- `PicoSemanticConcurrencyExamples.v`, `PicoSemanticConcurrencySafety.v`: two
  calls race on the cache field; any number of calls preserve the invariant
  and return the hash (`pico_hash_n_calls_results_correct`).
- `PicoHashTypeSafety.v`: the pool of hash calls is a typed pool
  (`pico_hash_n_calls_type_safe`).
- `PicoCacheMethodJudgment.v`: the cache-method judgment over PICO
  statements. A call to a method of the local-copy shape whose initializer is
  derivation code is trace robust on the machine
  (`cache_method_call_trace_robust`), with no semantic premise when the
  initializer calls the derivation method itself
  (`derivation_call_cache_method_trace_robust`).
- `PicoHashCacheMethod.v`: the hash method satisfies the judgment
  (`pico_hash_n_calls_by_judgment`).
- `PicoCacheClients.v`: a thread can break the provider's invariant only by
  writing the cache field itself (`noncache_step_preserves_inv`), so any
  control that never writes it directly may run alongside cache-method calls
  (`no_direct_cache_write_client`); hash calls with direct readers as an
  instance (`pico_hash_calls_and_readers_semimm`).
- `PicoCacheClientCalls.v`, `PicoHashClients.v`: client code that
  interleaves its own steps with calls to the cache method is trace robust
  (`client_code_trace_robust`); it rests on `step_under_cont` in
  `PICOBridge/PicoCoreFrame.v`, which says a step never inspects the rest
  of the continuation.
- `PicoHashTraceRobust.v`: the hash call is trace robust on the machine, and
  the n-call theorem as an instance (`pico_hash_n_calls_trace_robust`).
- `PicoHashExecution.v`: read-labeled executions of the local-copy and
  double-read methods.
- `CacheProtocolDiversity.v`, `PicoProtocolDiversityExecution.v`,
  `PicoOffsetCacheExecution.v`: offset-encoded, two-field and
  reference-valued protocols.
- `PicoJamHashAdequacy.v`, `PicoCombinedMemoryExecution.v`,
  `PicoJlsCacheFragmentAdequacy.v` and the publication examples: the race as
  a legal plain-JAM execution and the construction-to-access composition.

## Building and checking

```bash
make
```

```bash
make check
```

`make check` scans for `Axiom`, `Admitted` and `admit`, checks that
`scripts/public-theorems.txt` lists every `Theorem`, and runs
`Print Assumptions` on each entry. No axiom is accepted.

## What is not proved

- No soundness claim for the full Java Memory Model.
- No thread creation, synchronization or blocking in the source language; the
  invocation pool schedules a fixed set of calls.
- No checker for trace robustness of arbitrary Java methods; the JDK case
  studies are analyzed on paper except for the protocol instances above.
