# Pico Semantic Immutability Artifact

This repository mechanizes PICO and a semantic account of immutable objects
with racy derived caches.  The cache theorem is parametric in a weak
field-history memory interface; it is not a Java Memory Model adequacy theorem.

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
- `PICOBridge/PicoIrisSemImmLogicalRelation.v`: closed SemImm expression,
  statement, and method interpretations.
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
resource/SemImm pipeline above. The retired pure-wrapper and pre-CESK Iris
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

## Other PICO Results

- `Preservation.v`: PICO preservation.
- `DeepImmutability.v`: shallow and deep immutability.
- `ReadonlySafety.v`: readonly write/call safety.
- `ConcreteImmutability.v`: concrete immutability.
- `WFNOMutationEXP.v`: no-mutation result for well-typed expressions.

## Build

```sh
dune build @default
make check
python3 scripts/check-no-axioms-admits.py .
```

The final scanner must report no `Axiom`, `Admitted`, or `admit`.
