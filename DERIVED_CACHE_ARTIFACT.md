# Derived Cache Artifact Status

This note summarizes the derived-cache extension and its relationship to Iris.
It is intended as a reviewer-facing map of what is proved now and what remains
future work.

## Current Status

We are at Level 1 as a first working artifact:

- Iris owns a small concurrent mutable-cache proof in `heap_lang`.
- PICO owns the pure abstract-immutability and derived-cache facts.
- The bridge imports PICO theorems into Iris as pure propositions.

We also added preliminary Rocq-side SC and weak-observation PICO models.  These
are stepping stones toward richer concurrency work, not a full Iris
instantiation for PICO and not a Java weak-memory model.

## Level 1: Iris Wrapper Using heap_lang

Main file:

- [StringCacheIris.v](StringCacheIris.v)

What it contains:

- an ordinary Iris/`heap_lang` model of a String-like object;
- `ImmString`, an Iris invariant for immutable payload fields plus mutable
  cache fields;
- `hashCode_local_copy_spec`, the unified sequential hash-cache spec;
- `hashCode_spawn2_join_spec`, a fork/join theorem showing that two concurrent
  calls both return the deterministic hash and preserve the invariant.

This is a comparison model.  It uses Iris's built-in `heap_lang` semantics,
with sequentially consistent interleaving and atomic heap operations.  It is not
PICO's operational semantics.

## PICO Pure Theorem Side

Main file:

- [DerivedCache.v](DerivedCache.v)

What it contains:

- a reduced derived-cache protocol for `Final` abstract fields and an
  `Assignable` integer cache field;
- preservation lemmas showing that cache writes preserve final-field reads;
- sequential soundness theorems, including
  `derived_cache_update_sequence_sound`.

The PICO theorem is sequential: it is stated over PICO's existing statement
semantics and does not itself model threads or weak memory.

## Bridge Layer

Main files:

- [DerivedCacheIris.v](DerivedCacheIris.v)
- [PicoIrisCacheBridge.v](PicoIrisCacheBridge.v)

What they contain:

- pure Iris wrappers such as `field_readsI` and
  `derived_int_cache_protocolI`;
- bridge theorem entry points collecting the sequential PICO, SC PICO,
  weak-observation PICO, and Iris/`heap_lang` results.

This follows the intended Level 1 architecture: do not rewrite PICO in Iris;
instead, import PICO facts as pure facts `⌜ ... ⌝` where useful.

## Beyond Level 1: PICO-Side Concurrency Models

Main files:

- [ConcurrentPico.v](ConcurrentPico.v)
- [ConcurrentPicoExamples.v](ConcurrentPicoExamples.v)
- [WeakPico.v](WeakPico.v)
- [WeakPicoExamples.v](WeakPicoExamples.v)

What they contain:

- an SC interleaving PICO thread-pool model with one shared heap;
- accepted/rejected SC cache-transition examples;
- a weak-observation model where cache writes carry explicit observed
  final-field snapshots;
- acceptance/rejection theorems based on snapshot coherence;
- examples rejecting stale or mixed snapshots;
- `weak_rejects_execution_with_rejected_event`, which rejects a whole
  candidate execution if any event in the trace is rejected.

These files are Rocq-side stepping stones toward stronger concurrency models.
They are not yet Iris Level 2.

## Not Claimed

The current artifact does not claim:

- an Iris instantiation for PICO's operational semantics;
- a full Iris semantic interpretation of PICO types;
- a Java weak-memory or iRC11 model;
- that `WeakPico.v` is a complete weak-memory semantics.

`WeakPico.v` is an explicit observation/coherence model: a weak cache write is
accepted only when the observed final-field snapshot is coherent with the heap
at commit time.

## Future Levels

Level 2 would instantiate Iris for PICO's operational semantics.  That would
require a genuine PICO language instance, program steps, weakest preconditions,
and adequacy lemmas for PICO programs.

Level 3 would add a full Iris semantic interpretation of PICO types and prove
semantic type soundness inside Iris.

Those are future work.  The current branch completes a Level 1 bridge and adds
Rocq-side SC/weak-observation models to clarify the accepted/rejected cache
story.
