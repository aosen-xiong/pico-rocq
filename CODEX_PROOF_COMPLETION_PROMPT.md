# Prompt: Complete and Audit the PICO Semantic-Immutability Proof

## Current task statement

You are working in the Rocq/Iris repository:

```text
/Users/aosenxiong/semantic-immutability
```

Complete and adversarially audit the formal proof that a PICO object with
stable abstract state and racy derived-cache fields remains semantically
immutable under the repository's whole-value, read-from-history weak-memory
interface.

The intended proof pipeline is:

```text
PICO typing and TS effect checking
  -> CESK operational safety and typed call/return
  -> semantic cache API implemented by the concrete method body
  -> SemImmI preservation under history-backed reads and valid writes
  -> trace-robust deterministic result
  -> refinement to pure recomputation
```

The proof must cover the actual local-copy hash-cache method, not merely an
abstract method relation. It must also retain the ordinarily typed double-read
implementation as a negative example and prove that, for a nonzero hash, this
implementation cannot inhabit the stronger semantic API contract.

Assume the repository's field-history memory interface is the intended memory
model. Do not attempt to replace this task with Java Memory Model adequacy.

## Exact completion criteria

A complete result must establish all of the following in compiling Rocq:

1. **Generic cache theory.** `CacheHistOK` and read-from-history imply that
   every observed cache value satisfies the protocol; `CacheSafeMethod`
   implies the specified pure result and preserves cache-history validity.

2. **Whole-value memory boundary.** Cache reads observe one complete value
   previously written to the same field, or its initial/default value. Writes
   append complete values to that field's history. The documentation must
   explicitly exclude torn plain Java `long`/`double` reads and distinguish
   atomic reference transfer from safe publication of the referenced object.

3. **Real PICO execution.** The CESK semantics covers the source constructs
   used by typed PICO methods, including locals, assignments, field reads and
   writes, allocation, sequencing, conditionals, calls, continuations, and
   method return. Heap state and weak histories remain related by the stated
   agreement invariant.

4. **Primitive/reference typing.** Source types use `TInt` and `TRef C`.
   Integers inhabit only `Imm TInt`; null and locations inhabit reference
   types; class lookup and dispatch operate only on `TRef C`. There must be no
   fake integer class, `int_class_name`, or compatibility projection.

5. **Logical relation and adequacy.** Typed expressions, statements, and
   methods satisfy the canonical PICO Iris interpretation. The proof must use
   operational WP/state ownership and typed CESK preservation, not redefine
   semantic typing as ordinary typing paired with a manually supplied safety
   proposition.

6. **Ghost-backed semantic object protocol.** `SemImmI` owns or preserves the
   stable abstract-state fact and cache-history protocol. Cache reads expose a
   protocol-valid value. Cache writes preserve `SemImmI` only when an explicit
   protocol-valid write obligation is proved.

7. **Concrete semantic API proof.** The real local-copy hash method body must
   inhabit its continuation-aware callable contract. Its immutable-state
   recomputation may be supplied by a separately verified TS/Iris computation
   API, but the cache control flow itself must be proved by symbolic CESK/WP
   execution. No theorem called "concrete" may take the desired semantic
   method proposition as a premise.

8. **Typed semantic calls.** The callable return boundary must provide final
   callee typing, receiver identity, heap-extension evidence, core-state
   validity, and the actual return-slot value. The advertised-call handler
   must consume that evidence through
   `pico_core_typed_resolved_method_return` and resume with a typed caller
   frame and the advertised functional postcondition.

9. **Installed client call.** At least one theorem must install the concrete
   hash implementation in a sound semantic method environment and invoke it
   from a typed PICO caller. Merely proving a lookup lemma or assuming a
   pre-installed semantic environment is insufficient.

10. **Positive and negative trace connection.** Concrete hit and miss CESK
    executions of the local-copy method refine valid cache traces and return
    the pure hash. A labeled CESK execution of the double-read method must
    realize the bad trace `[H; 0]`, and for `H <> 0` this must refute the
    callable semantic contract through adequacy.

11. **Non-vacuity.** Exhibit a concrete cache adapter/provider whose abstract
    value is computed from immutable heap fields and whose invariant is
    satisfiable by an explicit initial state. Do not discharge the central
    theorem using an empty predicate, a constant abstract-state function, an
    impossible precondition, or a provider law that already assumes the
    desired result.

12. **Canonical artifact.** Remove obsolete facades, duplicate theorem
    families, compatibility aliases, and manually supplied call models. Paper
    and repository documentation must identify the actual public endpoints
    and accurately state all remaining assumptions and non-claims.

The intended public endpoints include, or should be replaced by demonstrably
stronger canonical theorems:

```text
cache_read_valid
cache_safe_method_refines_pure
pico_core_resource_stmt_fundamentalI
pico_core_typed_resolved_method_return
pico_semantic_typed_call_wpI
pico_heap_hash_callable_api_wfI
pico_heap_hash_api_call_wpI
pico_local_copy_cesk_refines_trace_on_hit
pico_local_copy_cesk_refines_trace_on_miss
pico_double_read_callable_method_uninhabited
```

## Insufficient substitutes

Do not claim completion if the artifact only provides any of the following:

- a pure theorem wrapped in an Iris pure proposition without a
  WP/state-ownership proof;
- a "logical relation" that assumes `cache_safe_stmt` or the desired semantic
  method contract;
- a trace theorem disconnected from actual CESK executions;
- a method theorem that models recomputation as an unexplained literal while
  claiming to verify computation from immutable fields;
- a call rule that proves entry typing but forwards untyped return evidence;
- a semantic environment whose method implementations are assumed rather than
  installed from proved method bodies;
- a positive local-copy example without a concrete negative double-read
  execution;
- a provider whose invariant is inconsistent, empty, or definitionally equal
  to the theorem being proved;
- ordinary PICO typing presented as sufficient to validate arbitrary cache
  writes;
- special-case results for SC heap loads presented as weak-history results;
- compilation of selected files while the full project fails;
- a reduction to Java/JMM soundness, contextual refinement, or another
  unproved theorem;
- documentation that overstates Java, JMM, termination, race freedom, or
  whole-program contextual refinement.

## Working method

Use multiple independent agents or workstreams aggressively when available.
Manage them dynamically rather than assigning a fixed number of agents to
fixed tasks.

- Begin with independent audits of: pure cache theory, CESK semantics,
  typing/preservation, Iris ownership/WP, concrete provider non-vacuity,
  positive method execution, negative execution, call/return integration, and
  paper-to-code consistency.

- Maintain an explicit registry of proof obligations and approach families.
  Group work by the actual invariant or proof mechanism, not by filenames.

- Do not tell every auditor the currently favored diagnosis. Preserve
  independent scrutiny long enough to reveal different failure modes.

- Require concrete output: theorem statements, proof terms, failing commands,
  exact file/line references, countermodels to overly weak lemmas, or patches.
  Reject vague status reports and claims that a return-transfer, adequacy, or
  invariant-preservation step is "routine."

- Mark a route blocked only when the same precise obstacle survives several
  materially different attempts. A large or difficult proof is not itself a
  blocker.

- Keep the pure trace proof, operational proof, and Iris proof distinct enough
  to expose circularity. Connect them only through named bridge theorems with
  explicit premises.

- Prefer deleting obsolete wrappers over preserving backward compatibility.
  Do not add aliases merely to keep old theorem names alive.

- Read the existing definitions and proof style before editing. Use named
  premises for substantial hypotheses. Keep theorem families small and avoid
  incremental wrappers used only once.

- Work in compiling slices, but do not stop at a compiling intermediate
  scaffold. Continue through implementation, downstream migration,
  documentation, and full verification.

## Adversarial audit checklist

Every candidate completion must be challenged for:

- a cache read not tied to the same object's same field history;
- torn or synthesized values that were never complete writes;
- writes to non-cache fields accidentally admitted by the cache protocol;
- a protocol write rule that accepts an arbitrary value;
- unstable abstract state or mutable cache fields leaking into abstract state;
- object-valued caches whose references are atomic but whose referents are not
  safely initialized or semantically stable;
- cache histories or adapters that map the wrong receiver or field;
- hash collision being confused with nondeterminism (equal hashes are allowed;
  the result must equal the deterministic hash function's value);
- hit/miss reasoning that silently assumes coherent repeated reads;
- the bad trace `[H; 0]` being excluded by definition rather than rejected by
  the method contract;
- a "local copy" proof that performs a second shared read;
- a final return value not tied to the method's actual return slot;
- a callee final environment not typed in the final heap;
- missing heap-extension evidence across allocation or calls;
- loss of receiver identity across the callee body;
- static contract lookup not covering dynamically dispatched overrides;
- recursive calls using an unguarded or circular method assumption;
- `NotStuck` being mistaken for termination;
- an Iris postcondition mentioning a final state different from the owned
  `ownP` state;
- a pure premise that is impossible to instantiate in the concrete model;
- use of `Axiom`, `Parameter` as an undocumented proof shortcut, `Admitted`,
  `admit`, `exfalso` from an inconsistent model, or hidden generated
  assumptions;
- stale project manifests, stale `.vo` files, or IDE success that differs from
  a clean command-line build;
- paper claims that do not map to a named compiled theorem.

For every proposed fix, test whether weakening or removing one premise would
make the theorem false. If a premise already states essentially the desired
conclusion, either derive it from a lower-level judgment or identify it
honestly as the semantic API boundary and prove that a concrete implementation
inhabits it.

## Repository discipline

- The worktree may already contain intentional changes. Never revert changes
  you did not make.
- Use the repository's existing architecture and proof conventions unless a
  demonstrated design defect requires a refactor.
- No backward-compatibility facade is required.
- Keep the field-history interface generic. Do not claim Java/JMM adequacy.
- Update Rocqdoc comments for every new public definition and theorem.
- Update `_RocqProject`, `_CoqProject`, and `dune` when adding or removing
  source files.

## Verification gates

Run focused compilation while developing. Before returning, run all of:

```sh
dune build @default
make check
python3 scripts/check-no-axioms-admits.py .
git diff --check
```

Also search for retired names, compatibility facades, undocumented axioms,
and paper claims with no theorem endpoint. A successful cached build is not
enough when dependency assumptions changed; force or clean the relevant build
when necessary.

## Return condition

Do not return merely because the current files compile, because one positive
example works, or because a remaining proof obligation is large. Repeatedly
synthesize findings, challenge the strongest candidate proof, repair concrete
gaps, and rerun the full gates.

Return only when either:

1. every completion criterion above is implemented and survives adversarial
   audit; or
2. a genuine external or logical blocker remains after materially different
   attempts, in which case report the strongest compiled theorem, the exact
   missing statement, why existing premises cannot derive it, and the smallest
   language/model extension required.

The final report must distinguish:

- mechanized theorems;
- semantic API assumptions discharged by concrete proofs;
- memory-interface assumptions;
- explicitly unmechanized claims;
- verification commands and their results.

Do not describe partial scaffolds, wrappers, or theorem-shaped assumptions as
the completed semantic-immutability proof.
