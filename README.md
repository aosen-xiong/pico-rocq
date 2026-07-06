# Pico Rocq Artifact

This repository contains the Rocq/Coq mechanization for the Pico language.  The
core artifact claims are organized around type soundness, immutability, and
readonly guarantees.

Top-level theorem entry points:

- `Preservation.v`: `preservation_pico`
- `DeepImmutability.v`: `shallow_immutability_pico`, `deep_immutability_pico`
- `ReadonlySafety.v`: `readonly_pico_field_write`,
  `readonly_method_call_preserves_arguments`
- `ConcreteImmutability.v`: `ConcreteImmutability`
- `WFNOMutationEXP.v`: `well_typed_no_mutation_exp`

Derived-cache and concurrency entry points:

- `DerivedCache.v`: sequential derived-cache soundness for `Final` abstract
  fields and `Assignable` integer cache fields.
- `ConcurrentPico.v`: sequentially consistent interleaving model for PICO
  thread pools sharing one heap.
- `WeakPico.v`: weak-observation model for cache writes, with explicit
  observed final-field snapshots.
- `StringCacheIris.v`: Iris/heap_lang comparison model for a String-like hash
  cache under SC interleaving concurrency.
- `PicoIrisCacheBridge.v`: bridge/summary theorems collecting the sequential
  PICO, SC PICO, weak-observation PICO, and Iris-facing results.

## Claims and proofs

| Paper reference | Paper-level claim / premise | Mechanized premise in Rocq | Proved guarantee | Rocq theorem / file |
|---|---|---|---|---|
| Syntax figures | Pico syntax: qualifiers, expressions, statements, fields, classes, methods, runtime values, heaps | Inductive datatypes and records encode the paper grammar | Source language and runtime configurations used by all later judgments | `q`, `q_f`, `q_c`, `a`, `expr`, `stmt`, `field_type`, `method_sig`, `class_def`, `runtime_type`, `r_env`, `Obj` in [Syntax.v](Syntax.v) |
| Viewpoint adaptation rules | Mutability, assignability, field, constructor, and runtime viewpoint adaptation | Scope-specific functions encode AS, RS, and TS adaptation cases | Adapted qualifiers used by typing, field access/write, constructors, and runtime typability | `vpa_mutability_qq_abs_imm`, `vpa_mutability_tt_abs_imm`, `vpa_mutability_qq_safe_ro`, `vpa_mutability_tt_safe_ro`, `vpa_assignability`, `vpa_assignability_concret_imm` in [ViewpointAdaptation.v](ViewpointAdaptation.v) |
| Subtyping rules | Qualifier, class/base, method-scope, and qualified-type subtyping | Inductive relations encode the subtype premises consumed by typing | Subtyping derivations used by statement typing and well-formedness | `q_subtype`, `base_subtype`, `method_subtype`, `qualified_type_subtype` in [Subtyping.v](Subtyping.v) |
| Static typing | Statement typing and well-formed class/method/table conditions | Static environments, method scopes, receiver/argument adaptation, and class-table checks are explicit premises | Well-typed statements and well-formed programs used by preservation and immutability proofs | `stmt_typing`, `wf_stypeuse`, `wf_method`, `wf_class`, `wf_class_table` in [Typing.v](Typing.v) |
| Dynamic semantics | Big-step expression and statement evaluation with success and mutation-exception results | Evaluation carries the heap, runtime environment, and protected-location set | Operational semantics used by preservation and no-mutation proofs | `eval_expr`, `eval_stmt` in [Bigstep.v](Bigstep.v) |
| Runtime well-formedness | Runtime configuration consistency between static environments, runtime environments, heaps, and class tables | Runtime typability and heap/object well-formedness are bundled in `wf_r_config` | Starting assumption and final guarantee for preservation | `wf_rtypeuse`, `wf_obj`, `wf_heap`, `wf_r_env`, `wf_r_config` in [Bigstep.v](Bigstep.v) |
| Reachability definitions | Ordinary reachability and abstract-state reachability | Heap reachability is encoded as inductive graph reachability; abstract reachability restricts steps to abstract-state fields | Reachability sets used by shallow/deep immutability, safe readonly, and concrete immutability | `reachable`, `reachable_abs`, `protected_locset`, `reachable_locations_from_initial_env` in [Reachability.v](Reachability.v) and [Bigstep.v](Bigstep.v) |
| Theorem 1 | Preservation | Initial runtime config is well-formed; statement is well-typed; statement evaluates successfully with result `OK` | Final runtime config is well-formed | `preservation_pico` in [Preservation.v](Preservation.v) |
| Theorem 1 safety support | Mutation exception cannot arise for well-typed field writes | Runtime config is well-formed; field write is well-typed; assume it evaluates to `MUTATIONEXP` | Contradiction: a well-typed field write cannot produce the mutation exception | `well_typed_no_mutation_exp` in [WFNOMutationEXP.v](WFNOMutationEXP.v) |
| Theorem 1 support | Big-step evaluation determinism | The same expression or statement evaluates twice from the same initial configuration | The two evaluations produce the same result/configuration | `eval_expr_deterministic` and `eval_stmt_deterministic` in [Bigstep.v](Bigstep.v) |
| Theorem 1 support | Local variable declaration preserves well-formedness | `SLocal T x` is well-typed and evaluates by `eval_stmt` | Extending runtime/static environments with the local binding preserves `wf_r_config` | `preservation_local_ok` in [Properties.v](Properties.v) |
| Theorem 1 support | Variable assignment preserves well-formedness | `SVarAss x e` is well-typed and evaluates by `eval_stmt` | Updating `x` with the evaluated value preserves `wf_r_config` | `preservation_varass_ok` in [Properties.v](Properties.v) |
| Theorem 1 support | Field write preserves well-formedness under permitted writes | `SFldWrite x f y` is well-typed and evaluates successfully by `eval_stmt` | Heap update preserves `wf_r_config` | `preservation_fldwrite_ok` plus scope-specific lemmas in [Properties.v](Properties.v) |
| Theorem 1 support | Object creation preserves well-formedness | `SNew x q_c c ys` is well-typed and evaluates by `eval_stmt` | Extending the heap and assigning the fresh object preserves `wf_r_config` | `preservation_new_ok` in [Properties.v](Properties.v) |
| Theorem 2 | Shallow abstract immutability | Immutable object exists before and after evaluation; field is `Final` or `RDA`; statement is well-typed and evaluates successfully | Protected field value is unchanged | `shallow_immutability_pico` in [DeepImmutability.v](DeepImmutability.v) |
| Lemma 1 | Reachable-abstract-state reachability from an immutable root preserves immutability | Object is reachable from an immutable root through abstract-state fields | The reachable object is also immutable | `reachable_abs_from_imm_points_to_imm` in [DeepImmutability.v](DeepImmutability.v) |
| Theorem 3 | Transitive abstract immutability | Object is reachable from an immutable root; statement is well-typed and evaluates successfully | Reachable abstract-state objects remain protected | `deep_immutability_pico` in [DeepImmutability.v](DeepImmutability.v) |
| Theorem 4 | Safe readonly method call | Method call through readonly receiver; arguments are protected/readable; method body evaluates successfully | Readonly-reachable arguments remain protected across the call | `readonly_method_call_preserves_arguments` in [ReadonlySafety.v](ReadonlySafety.v) |
| Theorem 4 support | Readonly field-write safety | Receiver expression has static type `RO`; field-write statement evaluates successfully; method scope is not `AbstractImm` | Protected field of the readonly-referenced object is unchanged | `readonly_pico_field_write` in [ReadonlySafety.v](ReadonlySafety.v) |
| Theorem 5 | Concrete immutability | Method call occurs in `ConcreteImm` scope; receiver and all parameters are safe | Entire reachable receiver/argument object graph remains unchanged for all fields | `ConcreteImmutability` in [ConcreteImmutability.v](ConcreteImmutability.v) |
| Derived cache, sequential | Writing an `Assignable` integer cache field derived from `Final` abstract fields is semantically sound | Abstract fields are `Final`; cache field is `Assignable`; the computed integer equals the derived function over the abstract-field reads | Final-field reads are preserved and the derived-cache protocol holds after the cache update | `derived_cache_update_sequence_sound` in [DerivedCache.v](DerivedCache.v) |
| Derived cache, SC concurrency | Thread-pool execution uses one shared heap and interleaves one thread step at a time | Every heap transition is cache-safe for the target derived cache | The shared derived-cache invariant is preserved across all interleavings | `concurrent_steps_preserve_cache_state` in [ConcurrentPico.v](ConcurrentPico.v) |
| Derived cache, SC accepted/rejected examples | SC cache writes may update only the assignable derived cache slot, not final abstract fields | Accepted transitions are stutters or derived-cache writes; rejected transitions change final-field reads | Accepted examples preserve the cache protocol; final-field changes are rejected | `simple_sc_accepts_cache_write`, `simple_sc_rejects_final_field_change` in [ConcurrentPicoExamples.v](ConcurrentPicoExamples.v) |
| Derived cache, weak observations | Weak executions expose the abstract-field values observed by a cache computation | A weak cache-write event is accepted only when its observed final-field snapshot is coherent with the heap at commit time | Coherent weak cache writes preserve the derived-cache protocol | `weak_accepts_preserves_protocol`, `weak_execution_preserves_cache_state_for_target` in [WeakPico.v](WeakPico.v) |
| Derived cache, weak rejected examples | Mixed or stale observations can compute a cache value that does not match the actual final fields | Candidate weak event observes values inconsistent with the heap snapshot at commit time | The candidate event/execution is rejected | `simple_weak_rejects_incoherent_cache_write`, `pair_weak_rejects_mixed_snapshot_execution` in [WeakPicoExamples.v](WeakPicoExamples.v) |
| Iris comparison model | A String-like derived hash cache is modeled in Iris heap_lang with atomic heap operations and fork/join | `ImmString` invariant protects immutable payload and mutable cache fields; concurrency is heap_lang SC interleaving, not Java weak memory | Two joined concurrent `hashCode` calls both return the deterministic hash and preserve the invariant | `hashCode_spawn2_join_spec` in [StringCacheIris.v](StringCacheIris.v) |
| Bridge summary | The artifact separates sequential PICO, SC PICO concurrency, weak-observation PICO, and Iris comparison results | Each model has an explicit theorem boundary and does not silently imply a stronger memory model | Main result shapes are re-exported as compact entry points | `pico_sequential_cache_result_from_eval`, `pico_concurrent_cache_result_from_steps`, `pico_weak_cache_result_from_coherent_execution`, `iris_sc_concurrent_hash_result_from_spawn` in [PicoIrisCacheBridge.v](PicoIrisCacheBridge.v) |
| Proof integrity | No axioms/admitted proof gaps in submitted sources | Artifact sources exclude forbidden `Axiom`, `Admitted`, and `admit`, except bundled `LibTactics.v` support library | Mechanical checker passes | [scripts/check-no-axioms-admits.py](scripts/check-no-axioms-admits.py) via `make check` |

## Paper/Formalization Notes

- The paper's full method-overriding rule uses viewpoint-adapted variance. The
  Rocq development intentionally mechanizes invariant overriding: if a subclass
  method overrides a parent method, the signatures must be syntactically equal.
- The paper treats `Lost` as a helper qualifier rather than a programmer-written
  type qualifier. Rocq represents it in the common qualifier datatype, but
  `wf_stypeuse` and non-reflexive `Lost` subtyping prevent direct `Lost` type
  uses in well-formed static environments.
- The method-call immutability theorems package receiver and parameter
  non-mutable premises through `all_params_safe`.
- The derived-cache concurrency development is intentionally versioned.  The
  SC PICO model is an interleaving semantics with one shared heap.  The weak
  PICO model is not a full Java memory model; it is an explicit-observation
  layer that accepts cache writes only when the observed final-field snapshot
  is coherent.  `StringCacheIris.v` is an Iris/heap_lang comparison model, not
  a replacement for the PICO semantics.

## Toolchain

- Rocq/Coq: `9.1.0`
- OCaml: `5.2.1`

## Artifact verification

The recommended reviewer command is:

```sh
make check
```

This builds all Rocq sources and checks that the submitted proof files do not
use forbidden `Axiom`, `Admitted`, or `admit` declarations outside the bundled
`LibTactics.v` support library.

The same checks can be run separately:

```sh
JOBS="$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || printf 1)"
dune build @default -j"$JOBS"
python3 scripts/check-no-axioms-admits.py .
```

## Rendered proof documentation

This artifact can also render browsable Alectryon proof pages:

```sh
make alectryon-doc
```

The generated index is `alectryon/index.html`. The rendered documentation is a
generated artifact and is intentionally ignored by git.

## Local project page preview

The repository includes a static landing page prototype in `site/`. To render
the proof documentation under that page and preview the future GitHub Pages
layout, run:

```sh
make site
open site/index.html
```

The generated proof pages live under `site/proofs/` and are ignored by git.

## Build (current Make-based workflow)

1. Generate the Makefile:
   ```sh
   coq_makefile -f _RocqProject -o Makefile
   ```
2. Build:
   ```sh
   JOBS="$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || printf 1)"
   make -j"$JOBS"
   ```

## Build with dune (recommended command)

```sh
JOBS="$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || printf 1)"
dune build @default -j"$JOBS"
```

This repository currently uses dune as a frontend wrapper over the existing
`_RocqProject` + `coq_makefile` build, so `dune build` and CI stay reliable.
Generated files such as `CoqMakefile*`, `.vo`, `.vos`, `.vok`, `.glob`, and
`_build/` are ignored and are not part of the source artifact.

## Reproducible setup with opam

This repository includes `pico-coq.opam` so dependencies can be installed in an
isolated switch.

```sh
# From the repo root
opam switch create . 5.2.1
eval "$(opam env)"

# Pin this package and install only its dependencies
opam pin add . -n
opam install . --deps-only

# Build (dune wrapper)
JOBS="$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || printf 1)"
dune build @default -j"$JOBS"
```

## Notes

- `dune` and `_RocqProject` builds are both available during transition.
- The opam package build uses `dune build`.
- `WFNOMutationEXP.v` proves a preservation-style mutation-safety claim:
  well-typed field writes do not produce a mutation exception.
