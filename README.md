# GAIT: Rocq mechanization

This repository holds the Rocq mechanization of the paper **Generic Abstract
Immutability Types** (GAIT). GAIT extends PICO's abstract immutability with
class and method type parameters, qualifier parameters, qualified type-variable
uses, and a qualifier downcast. The development has 64 files and about 47,000
lines, not counting the third-party tactic library `LibTactics.v`. About 15,900
of the lines are examples and regression programs. No file uses `Axiom`,
`Admitted` or `admit`.

The earlier mechanization without generics, from the PICO paper, is kept in
[PICO/](PICO/README.md) and builds on its own.

## Build and check

Requirements: Rocq 9.1 (the CI uses 9.1.1, OCaml 5.2.1 and the opam file
`pico-coq.opam`) and Python 3.

```sh
make          # build every file, serially (about 5 minutes)
make check    # build, then run the two checks below
```

`make check` runs two scripts:

- [scripts/check-no-axioms-admits.py](scripts/check-no-axioms-admits.py) scans
  every `.v` file for `Axiom`, `Admitted` and `admit`.
- [scripts/check-public-assumptions.py](scripts/check-public-assumptions.py)
  checks that [scripts/public-theorems.txt](scripts/public-theorems.txt) lists
  every `Theorem` of the sources, then runs `Print Assumptions` on each listed
  result and fails unless every one is closed under the global context. The
  list has 189 entries, including every result in the table below.

`make check-pico` does the same for the PICO folder. `dune build @default` is a
wrapper over the same build and is what the CI runs. `make alectryon-doc`
renders the sources as web pages in `alectryon/`.

## The paper's results

| Paper | Rocq name | File |
| --- | --- | --- |
| Theorem (Preservation) | `preservation_pico` | [Preservation.v](Preservation.v) |
| Theorem (Mutation-exception freedom) | `well_typed_no_mutation_exp` | [MutationSafety.v](MutationSafety.v) |
| Theorem (Progress), for the fuel-based interpreter | `run_progress` | [Interp.v](Interp.v) |
| The interpreter agrees with the big-step semantics | `run_sound`, `run_complete`, `run_agrees` | [Interp.v](Interp.v) |
| The same, between the budgeted evaluation and the big-step one | `eval_fuel_erase`, `eval_stmt_has_fuel` | [Progress.v](Progress.v) |
| Lemma (abstract-state reachability preserves immutability) | `reachable_abs_from_imm_points_to_imm` | [Immutability.v](Immutability.v) |
| Theorem (Abstract-state and concrete-state preservation) | `abstract_state_preservation`, `concrete_state_preservation` | [Immutability.v](Immutability.v) |
| Theorem (Readonly-state and transitive-state preservation) | `rs_ts_preservation_all_calls` | [ArgTheorems.v](ArgTheorems.v) |
| A type that contradicts its class's declared mutability has only null values | `pinned_class_uninhabited` | [Inhabitants.v](Inhabitants.v) |
| A value has a type that contains `@Lost` exactly when it has some reading of that type without `@Lost` | `lost_is_some_reading` | [LostReading.v](LostReading.v) |

The qualifier downcast needs no theorem of its own. Preservation covers it,
because the downcast has no runtime test.

### The readonly-state and transitive-state theorem

`rs_ts_preservation_all_calls` starts from a *start state*: a well-formed
configuration with no type parameter in scope whose objects all belong to
classes without type parameters. The first state of a program, which holds only
the main object, is one. From a start state, run any well-typed statement. Every
call made during that run, at any depth, that selects a readonly-state or
transitive-state method leaves unchanged the protected fields of every object
that existed when the call started, however the call ends. Readonly state
protects the fields that are not assignable, and transitive state protects all
fields.

The statement uses only the language's own definitions: typing, big-step
evaluation and the heap. The general form of the theorem,
`rs_ts_call_preservation_final_any` in [ArgTheorems.v](ArgTheorems.v), starts at
the call instead. It assumes a well-formed configuration whose stored type
arguments, in the heap and in the current frame, satisfy their bounds when read
in readonly state, and that the bounds in scope of readonly-state and
transitive-state methods contain no `@Mut`, which well-formedness requires.
`RSFp_start_plain` shows that a start state meets the first assumption, and
`rsfp_preservation` shows that every well-typed statement that finishes
normally keeps it.

## Files

The files build in the order of [_RocqProject](_RocqProject).

| Part | Files |
| --- | --- |
| Language: syntax, adaptation, subtyping, typing, big-step semantics | `Syntax.v`, `Notations.v`, `Helpers.v`, `ViewpointAdaptation.v`, `Subtyping.v`, `Typing.v`, `NoMutEquiv.v`, `Bigstep.v` |
| Type safety | `DynLemmas.v`, `RuntimeTyping.v`, `ConfigLemmas.v`, `PreservationCases.v`, `PreservationCall.v`, `LostReading.v`, `Inhabitants.v`, `Preservation.v`, `MutationSafety.v`, `Progress.v`, `Interp.v` |
| Abstract-state and concrete-state preservation | `Immutability.v` |
| Readonly-state and transitive-state preservation, first without type parameters, then with them | `ReadonlyWrite.v`, `ReadonlyFlat.v`, `ReadonlyWorlds.v`, `ReadonlyGeneric.v` |
| Readonly-state and transitive-state preservation, general case | `GhostLabels.v`, `ArgViews.v`, `GhostTyping.v`, `GhostForget.v`, `GhostFit.v`, `GhostShadow.v`, `ArgTyping.v`, `GhostInvariant.v`, `ArgFit.v`, `ArgInvariant.v`, `ArgStatements.v`, `ArgOverriding.v`, `OverrideCheck.v`, `ArgCalls.v`, `ArgEntry.v`, `ArgTheorems.v` |
| Examples | `Examples*.v` |
| Regression programs | `SuperArgsRegression.v`, `OverrideReturnProbe.v`, `DeepBoundProbe.v`, `DeepBoundProbe2.v` |

Each file opens with a comment that gives its role. The example files write out
concrete class tables and programs, derive their typing and evaluation, and
apply the theorems to them. [ExamplesInterp.v](ExamplesInterp.v) runs the
example programs with the interpreter. Each regression program records a rule
variant that the proof effort found unsound, and proves that the current rules
reject it.
