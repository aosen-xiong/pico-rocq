# PICO Iris Pipeline

## Current Result

```text
PICO typing
  -> typing-directed core WP
  -> guarded-recursive method calls
  -> SemImmI-preserving weak cache operations
  -> statement fundamental theorem and method-specific callable proofs
  -> generic ownP adequacy transport for a proved WP
```

The operational target is the continuation-based language in
`PICOBridge/PicoIrisCoreLanguage.v`.  Its state contains both the PICO heap and
the weak field-history state.  Field reads use `wm_read`; writes update the heap
and append a whole value to the corresponding history; calls enter resolved
method bodies and return through `KCall` frames.

## Logical Relation

The LR is split by proof responsibility:

1. `PicoIrisTypingFundamental.v` proves the structural statement theorem over
   typed runtime environments and the core state invariant.
2. `PicoIrisResourceLogicalRelation.v` threads one state-indexed linear
   resource through the selected success or exception branch.
3. `PicoIrisSemImmOperations.v` proves that concrete weak cache reads and
   writes preserve the ghost-backed `SemImmI` protocol; writes update the
   existing cache ghost name.
4. `PicoIrisSemImmLogicalRelation.v` instantiates the resource with `SemImmI`
   and closes recursive calls with Iris Löb induction.
5. Method-specific proofs allocate the initial SemImm ghost history;
   `PicoIrisSemImmAdequacy.v` then supplies the generic Iris `ownP` adequacy
   transport for their terminal postconditions.
6. `PicoIrisSemanticAPI.v` provides the open semantic method/class boundary for
   manually verified APIs whose guarantees are stronger than ordinary typing.

The central interpretations are:

```text
V[[T]]        = typed runtime value
G[[Gamma]]    = typed runtime environment
E[[e : T]]    = WP in every typed assignment context
S[[s]]        = resource-aware WP for a typed statement
M[[method]]   = resource-aware WP for a well-formed method body
```

The expression interpretation uses assignment contexts because PICO source
expressions are not standalone controls in the core machine.

## Main Theorems

- `pico_core_resource_guarded_call_handlerI`
- `pico_core_semimm_read_ruleI`
- `pico_core_semimm_admissible_write_ruleI`
- `pico_core_ownP_adequacy`
- `pico_hash_method_semantic_with_computationI`

The first theorem is the recursive method environment.  A concrete call step
enters the resolved body, making the Löb hypothesis available; the body LR
then runs to `SSkip`, reads the typed return slot, and takes `PCS_SkipCall` back
to the suspended caller.

Method-specific semantic API proofs are the refinement endpoint. A cache API
proves its body WP, including protocol validity of each concrete cache write,
and the generic own-state adequacy bridge exports its terminal postcondition.
There is no ordinary-typing-to-`SemImmI` theorem because PICO field typing does
not imply cache-protocol validity.

TS methods use `ts_stmt` only for their source effect. Their functional result
is specified by an Iris `PicoSemanticMethodContract`, not by a new PICO
`ensures` form. `pico_ts_semantic_method_wfI` checks the source effect and the
callable Iris contract. `pico_ts_call_summary` is only the source-effect
summary; typed dynamic dispatch remains the responsibility of the resource LR.

The callable and exported endpoint is `pico_callable_methodI`. It is continuation-aware:
the callee establishes its semantic postcondition before `PCS_SkipCall`
restores the caller frame. The resource LR handles ordinary unadvertised
calls, composing call entry, dynamic lookup, typed body execution, heap
extension, qualifier-sensitive return transfer, and caller resumption.
`pico_semantic_methodI` remains only for closed-execution adequacy tests.
Advertised successful branches use `pico_semantic_typed_call_wpI`. Given
runtime resolution, it derives the callee frame and override-coherent contract
from typing, takes `PCS_Call`, applies the callable contract, consumes the
callee's typed return evidence with `pico_core_typed_resolved_method_return`,
and resumes with both the functional postcondition and a typed caller frame.
`pico_ts_call_summary` requires contract coherence for every subclass override
that dynamic dispatch may select.

## Explicit Assumptions

- `CacheMemoryModel`: whole-value field histories, read-from-history reads, and
  append-style writes. `history_cache_memory_model` is the canonical exhibited
  instance; stricter models may refine its read choices.
- `CacheMemoryModelProgress`: every nonempty field history admits a read.
- Initial/default values are observable only when allocation inserted them as
  an initial history message; empty histories admit no read.
- `PicoCoreSemImmInstantiation`: proves that a chosen PICO representation and
  cache-field adapter implement `StableAbs` and the tracked cache snapshot on
  an explicit reachable-state invariant. It maps concrete cache histories into
  the protocol snapshot; publication follows from the protocol's
  `cache_valid_published` law. The provider proves that
  classified writes and allocations preserve the invariant and `SemImmI`.
  `pico_concrete_hash_semimm` and `pico_concrete_hash_initial_state` discharge
  this boundary for the integer hash example. The represented value is the
  supplied pure hash of the receiver's non-cache field tail, not an external
  constant. `pico_concrete_hash_provider_inhabited` gives an explicit closed
  two-class table, concrete object `[Int 0; Int 7]`, and nonconstant
  heap-derived hash witness. The witness table contains no hash method; it
  proves provider satisfiability, while installation remains conditional.
  `pico_heap_hash_callable_api_wfI` connects the provider to the
  callable/exported method API.
- Calls: resolved method bodies, callee frames, and qualifier-sensitive return
  transfer are derived from source typing, dynamic lookup, `wf_method`,
  heap-type extension, and CESK receiver continuity.
- Initial typed runtime environment, well-formed core state, and valid cache
  snapshot.

These assumptions define the source/runtime and memory-model boundary.  In
particular, the instantiation is a concrete provider proof obligation; source
typing alone does not invent an abstract-state function or cache protocol.
They are intentionally visible in theorem signatures.

## Cache Result

The pure cache theory remains the source of semantic refinement:

```text
StableAbs
  + CacheHistOK
  + valid read traces
  + CacheSafeMethod
  -> result = pure recomputation
  + cache-history validity is preserved
```

`StableAbs` is a provider predicate, not temporal preservation by itself. The
provider must prove that its reachable-state invariant re-establishes the same
abstract value after every admitted transition.

The TS source effect judgment discharges the important initializer premise:
the miss computation reads only stable abstract state, locals, and arguments.
It therefore has no direct shared writes and computes independently of racy
cache observations.  The accepted local-copy method reads the cache once; the
bad double-read trace remains rejected.

## Scope

Proved:

- method-specific safety and result-postcondition adequacy for executions whose
  SemImm-preserving WP has been proved;
- recursive method execution in Iris;
- ghost-backed preservation of valid cache histories;
- source-level TS direct shared-write freedom for the abstract cache initializer;
- pure trace-robust cache refinement.

Not claimed:

- adequacy from Java/JMM executions to the field-history core;
- contextual equivalence of an entire class with a pure implementation;
- a language-wide execution-to-trace theorem connecting arbitrary source
  methods to generic trace runners; the double-read counterexample has a
  dedicated labeled CESK bridge in `PicoHashExecutionTrace.v`;
- acceptance of torn plain non-volatile Java `long` or `double` caches.
A class-level observational-purity theorem would require an explicit
observation boundary and a binary LR or separate contextual simulation.  That
is a separate contribution, not another wrapper around the current unary LR.

## Verification

```sh
dune build @default
make check
python3 scripts/check-no-axioms-admits.py .
git diff --check
```
