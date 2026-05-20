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

## Claims and proofs

| Paper-level claim / premise | Mechanized premise in Rocq | Proved guarantee | Rocq theorem / file |
|---|---|---|---|
| Type soundness / preservation | Initial runtime config is well-formed; statement is well-typed; statement evaluates successfully | Final runtime config is well-formed | `preservation_pico` in `Preservation.v` |
| Local variable declaration preserves well-formedness | `SLocal T x` is well-typed and evaluates by `eval_stmt` | Extending runtime/static environments with the local binding preserves `wf_r_config` | `preservation_local_ok` in `Properties.v` |
| Variable assignment preserves well-formedness | `SVarAss x e` is well-typed and evaluates by `eval_stmt` | Updating `x` with the evaluated value preserves `wf_r_config` | `preservation_varass_ok` in `Properties.v` |
| Field write preserves well-formedness under permitted writes | `SFldWrite x f y` is well-typed and evaluates successfully by `eval_stmt` | Heap update preserves `wf_r_config` | `preservation_fldwrite_ok` plus scope-specific lemmas in `Properties.v` |
| Object creation preserves well-formedness | `SNew x q_c c ys` is well-typed and evaluates by `eval_stmt` | Extending the heap and assigning the fresh object preserves `wf_r_config` | `preservation_new_ok` in `Properties.v` |
| Abstract immutability / shallow field protection | Immutable object exists before and after evaluation; field is `Final` or `RDA`; statement is well-typed and evaluates successfully | Protected field value is unchanged | `shallow_immutability_pico` in `DeepImmutability.v` |
| Transitive / deep immutability | Object is reachable from an immutable root; statement is well-typed and evaluates successfully | Reachable abstract-state objects remain immutable / protected | `deep_immutability_pico` in `DeepImmutability.v` |
| Readonly field-write safety | Receiver expression has static type `RO`; field-write statement evaluates successfully; method scope is not `AbstractImm` | Protected field of the readonly-referenced object is unchanged | `readonly_pico_field_write` in `ReadonlySafety.v` |
| Readonly method-call safety | Method call through readonly receiver; arguments are protected/readable; method body evaluates successfully | Readonly-reachable arguments remain protected across the call | `readonly_method_call_preserves_arguments` in `ReadonlySafety.v` |
| Concrete immutability | Method call occurs in `ConcreteImm` scope; receiver has static `RO` type; all parameters are safe | Entire reachable argument/object graph remains unchanged for protected fields | `ConcreteImmutability` in `ConcreteImmutability.v` |
| No successful mutation through forbidden field write | Well-typed field write evaluates to `MUTATIONEXP` | Contradiction: such a well-typed mutation exception cannot occur | `well_typed_no_mutation_exp` in `WFNOMutationEXP.v` |
| No axioms/admitted proof gaps in submitted sources | Artifact sources exclude forbidden `Axiom`, `Admitted`, and `admit`, except bundled `LibTactics.v` support library | Mechanical checker passes | `scripts/check-no-axioms-admits.py` via `make check` |

## Toolchain

- Rocq/Coq: `9.1.0`
- OCaml: `5.2.1`
- `coq-record-update`: `0.3.4`

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
