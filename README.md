# PICO Rocq Formalization

This directory contains the Rocq/Coq mechanization for the paper
**Transitive, Abstract, and Class Polymorphic Immutability**. The core artifact
claims are organized around type soundness, immutability, and readonly
guarantees.

Top-level theorem entry points:

- `Preservation.v`: `preservation_pico`
- `AbstractStatePreservation.v`: `shallow_abstract_immutability`, `abstract_state_preservation`
- `ConcreteStatePreservation.v`: `concrete_state_preservation`
- `ReadonlyStatePreservation.v`: `readonly_field_write_preservation`,
  `readonly_state_preservation`
- `TransitiveStatePreservation.v`: `transitive_state_preservation`
- `WFNOMutationEXP.v`: `well_typed_no_mutation_exp`

## Claims and proofs

| Paper reference | Paper-level claim / premise | Mechanized premise in Rocq | Proved guarantee | Rocq theorem / file |
|---|---|---|---|---|
| Syntax figures | Pico syntax: qualifiers, expressions, statements, fields, classes, methods, runtime values, heaps | Inductive datatypes and records encode the paper grammar | Source language and runtime configurations used by all later judgments | `q`, `q_f`, `q_c`, `a`, `expr`, `stmt`, `field_type`, `method_sig`, `class_def`, `runtime_type`, `r_env`, `Obj` in [Syntax.v](Syntax.v) |
| Viewpoint adaptation rules | Mutability, assignability, field, constructor, and runtime viewpoint adaptation | Scope-specific functions encode AS, CS, RS, and TS as independent mutability/assignability choices | Adapted qualifiers used by typing, field access/write, constructors, and runtime typability | `vpa_mutability_qq_abstract_state`, `vpa_mutability_tt_abstract_state`, `vpa_mutability_qq_readonly_state`, `vpa_mutability_tt_readonly_state`, `vpa_assignability`, `vpa_assignability_cs_ts` in [ViewpointAdaptation.v](ViewpointAdaptation.v) |
| Subtyping rules | Qualifier, class/base, method-scope, and qualified-type subtyping | Inductive relations encode the subtype premises consumed by typing | Subtyping derivations used by statement typing and well-formedness | `q_subtype`, `base_subtype`, `method_scope_subtype`, `qualified_type_subtype` in [Subtyping.v](Subtyping.v) |
| Static typing | Statement typing and well-formed field, constructor, class, method, and table conditions | Static environments, method scopes, receiver/argument adaptation, and class-table checks are explicit premises | Well-typed statements and well-formed declarations used by preservation and immutability proofs | `stmt_typing`, `wf_stypeuse`, `wf_field`, `wf_constructor`, `wf_method`, `wf_class`, `wf_class_table` in [Typing.v](Typing.v) |
| Dynamic semantics | Big-step expression and statement evaluation with success, null-pointer, and mutation-exception outcomes | Evaluation relates expressions and statements in an initial runtime configuration to an outcome and final configuration | Operational behavior used by preservation, mutation safety, and the immutability proofs | `eval_expr`, `eval_stmt` and their determinism theorems in [Bigstep.v](Bigstep.v) |
| Runtime well-formedness | Runtime configuration consistency between static environments, runtime environments, heaps, and class tables | Runtime typability and heap/object well-formedness are bundled in `wf_r_config` | Starting assumption and final guarantee for preservation | `wf_rtypeuse`, `wf_obj`, `wf_heap`, `wf_renv`, `wf_r_config` in [Bigstep.v](Bigstep.v) |
| Reachability definitions | Ordinary reachability and abstract-state reachability | `reachable` follows arbitrary heap edges; `reachable_abs` and `protected_locset` encode RAS protection; `reachable_locations_from_initial_env` collects the objects reachable from call roots | Reachability sets used by shallow abstract immutability and the four state-preservation guarantees | `reachable`, `reachable_abs`, `protected_locset` in [Reachability.v](Reachability.v); `reachable_locations_from_initial_env` in [Bigstep.v](Bigstep.v) |
| Theorem 1 | Preservation and mutation safety | The initial runtime configuration is well-formed and the statement is well-typed; preservation additionally assumes a successful `OK` evaluation, while safety considers an evaluation producing `MUTATIONEXP` | Successful evaluation preserves runtime well-formedness, and no well-typed statement can produce the mutation exception | `preservation_pico` in [Preservation.v](Preservation.v) and `well_typed_no_mutation_exp` in [WFNOMutationEXP.v](WFNOMutationEXP.v) |
| Theorem 1 support | Big-step evaluation determinism | The same expression or statement evaluates twice from the same initial configuration | The two evaluations produce the same result/configuration | `eval_expr_deterministic` and `eval_stmt_deterministic` in [Bigstep.v](Bigstep.v) |
| Theorem 1 support | Local variable declaration preserves well-formedness | `SLocal T x` is well-typed and evaluates by `eval_stmt` | Extending runtime/static environments with the local binding preserves `wf_r_config` | `preservation_local_ok` in [Properties.v](Properties.v) |
| Theorem 1 support | Variable assignment preserves well-formedness | `SVarAss x e` is well-typed and evaluates by `eval_stmt` | Updating `x` with the evaluated value preserves `wf_r_config` | `preservation_varass_ok` in [Properties.v](Properties.v) |
| Theorem 1 support | Field write preserves well-formedness under permitted writes | `SFldWrite x f y` is well-typed and evaluates successfully by `eval_stmt` | Heap update preserves `wf_r_config` | `preservation_fldwrite_ok` plus scope-specific lemmas in [Properties.v](Properties.v) |
| Theorem 1 support | Object creation preserves well-formedness | `SNew x q_c c ys` is well-typed and evaluates by `eval_stmt` | Extending the heap and assigning the fresh object preserves `wf_r_config` | `preservation_new_ok` in [Properties.v](Properties.v) |
| Theorem 2 | Shallow abstract immutability | Immutable object exists at entry; field is `Final` or `RDA`; statement is well-typed and evaluates successfully | The object still exists with the same runtime type, and the protected field value is unchanged | `shallow_abstract_immutability` in [AbstractStatePreservation.v](AbstractStatePreservation.v) |
| Lemma 1 | Reachable-abstract-state reachability from an immutable root preserves immutability | Object is reachable from an immutable root through abstract-state fields | The reachable object is also immutable | `reachable_abs_from_imm_points_to_imm` in [AbstractStatePreservation.v](AbstractStatePreservation.v) |
| Theorem 3, AS clause | Abstract-state preservation | Object is reachable from an immutable root through abstract state; statement is well-typed and evaluates successfully | The reachable object still exists with the same runtime type, and every non-`Assignable` field retains its entry value | `abstract_state_preservation` in [AbstractStatePreservation.v](AbstractStatePreservation.v) |
| Theorem 3, CS clause | Concrete-state preservation | Object is reachable through abstract state from an immutable root; statement is well-typed in `ConcreteState` scope | The reachable object still exists with the same runtime type, and every field retains its entry value, including fields declared `Assignable` | `concrete_state_preservation` in [ConcreteStatePreservation.v](ConcreteStatePreservation.v), supported by [ConcreteState.v](ConcreteState.v) |
| Theorem 4, RS clause | Readonly-state preservation | Method call occurs in `ReadonlyState` scope through protected receiver/arguments and evaluates successfully | Each protected object still exists with the same runtime type, and its non-`Assignable` fields retain their entry values | `readonly_state_preservation` in [ReadonlyStatePreservation.v](ReadonlyStatePreservation.v) |
| Theorem 4 support | Readonly field-write safety | Receiver expression has static type `RO`; field-write statement evaluates successfully in `ReadonlyState` or `TransitiveState` scope | Protected field of the readonly-referenced object is unchanged | `readonly_field_write_preservation` in [ReadonlyStatePreservation.v](ReadonlyStatePreservation.v) |
| Theorem 4, TS clause | Transitive-state preservation | Method call occurs in `TransitiveState` scope; receiver and all parameters are safe | Each protected object still exists with the same runtime type, and every field retains its entry value | `transitive_state_preservation` in [TransitiveStatePreservation.v](TransitiveStatePreservation.v) |
| Proof-hygiene scan | Submitted proof sources do not use the forbidden commands scanned by the artifact | Every submitted `.v` file excludes literal `Axiom`, `Admitted`, and `admit` | Mechanical forbidden-command scan passes | [scripts/check-no-axioms-admits.py](scripts/check-no-axioms-admits.py) via `make check` |
| Kernel-assumption audit | Public results do not depend on global axioms | The explicit [public-theorems.txt](scripts/public-theorems.txt) manifest is checked against every source `Theorem`, then each fully qualified theorem, lemma, or corollary entry is inspected with `Print Assumptions` | The manifest and sources agree, and every listed public result is closed under the global context | [scripts/check-public-assumptions.py](scripts/check-public-assumptions.py) via `make check` |

## Paper/Formalization Notes

- Variable index `0` is reserved for `this`. Following Java, `this` is not a
  reassignable variable, so variable assignment, object creation, and
  method-call typing require their destination variable to differ from `0`.
- The constructor model omits executable constructor bodies and explicit
  superclass-constructor calls. Consequently, the paper's `checkSuperCall`
  premise has no separate Rocq judgment; this is part of the declared
  constructor-body simplification.
- The development proves declaration-, statement-, and configuration-level
  results rather than a separate `WF-Prog`/`OS-P-Prog` wrapper judgment.
- `wf_field` and `wf_constructor` implement the paper's viewpoint-adapted
  well-formedness checks, and `wf_method` checks its declared return type with
  `wf_stypeuse`. [WellformednessRegression.v](WellformednessRegression.v)
  exercises both formerly divergent field/constructor cases and supplies
  a positive runtime-configuration witness.
- The paper's full method-overriding rule uses viewpoint-adapted variance. The
  Rocq development intentionally mechanizes invariant overriding: if a subclass
  method overrides a parent method, the signatures must be syntactically equal.
- The paper treats `Lost` as a helper qualifier rather than a programmer-written
  type qualifier. Rocq represents it in the common qualifier datatype, but
  `wf_stypeuse` and non-reflexive `Lost` subtyping prevent direct `Lost` type
  uses in well-formed static environments.
- The method-call preservation theorems package the non-mutable declared
  receiver and formal-parameter premises through
  `signature_has_no_mutable_roots`.

## Toolchain

- Rocq/Coq: `9.1.1`
- OCaml: `5.2.1`

## Artifact verification

The recommended reviewer command is:

```sh
make check
```

This builds all Rocq sources, checks that every submitted `.v` file avoids the
forbidden `Axiom`, `Admitted`, and `admit` commands, verifies that the explicit
public-theorem manifest matches the source declarations, and checks that every
manifest entry is closed under the global context.

The same checks can be run separately:

```sh
JOBS="$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || printf 1)"
dune build @default -j"$JOBS"
python3 scripts/check-no-axioms-admits.py .
python3 scripts/check-public-assumptions.py .
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
  no well-typed statement, including nested method calls and sequences,
  produces a mutation exception.
