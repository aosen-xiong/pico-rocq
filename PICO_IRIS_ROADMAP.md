# PICO Iris Pipeline Roadmap

This document is the short roadmap for the PICO/Iris direction.  It records
the intended proof story and the current implementation boundary.  Detailed
theorem inventories belong in [DERIVED_CACHE_ARTIFACT.md](DERIVED_CACHE_ARTIFACT.md).

## Final Story

The central claim is generic:

```text
A racy derived cache is semantically invisible when the method is correct for
every cache-read trace allowed by the cache protocol.
```

The proof is organized around this pipeline:

```text
PICO typing / cache-safe method rule
  -> generic trace-robust method semantics
  -> weak execution produces valid reads and append-only cache histories
  -> semantic immutability / refinement to pure recomputation
  -> Iris wrapper and, later, a real logical relation
```

The generic theorem is not PICO-specific.  PICO is one provider of the stable
abstract state; the generic cache theory then handles cache histories,
trace-robust method correctness, and weak-memory-parametric reads from those
histories.

## Core Concepts

- `StableAbs o a`: object `o` represents a stable abstract value `a`.
- `CacheProtocol`: describes which cache values are valid for an abstract
  value.
- `CacheHistOK`: every value in a cache-field history satisfies the protocol.
- `ValidTrace`: every cache read in a method trace observes a protocol-valid
  value.
- `CacheSafeMethod`: for every valid cache-read trace, the method returns the
  pure recomputation result and records only protocol-valid cache writes.

Important separation:

- `CacheSafeMethod` does not by itself prove abstract-field immutability,
  cache encapsulation, or post-state `StableAbs`.
- PICO/provider layers prove those obligations, either from write-avoidance or
  from final-field facts.
- The weak-memory layer only needs a field-history contract: reads come from
  histories, writes extend histories, recorded cache writes are appended, and
  each admissible cache field has whole-value reads/writes.  In the paper this
  is the `AtomicCacheField(k)` side condition.  It admits Java `int`,
  `boolean`, and reference cache values, but excludes plain non-volatile
  `long`/`double` cache fields unless a stronger atomic/synchronization
  mechanism or verified representation protocol is supplied.

## Main Theorem Shape

The pure theorem has this shape:

```text
StableAbs o a
  + CacheHistOK P o a
  + CacheSafeMethod m P F
  + final cache histories = old histories ++ method-recorded valid writes
  -> result = F a args
  -> post-state semantic immutability
```

Equivalently, the cached method refines pure recomputation:

```text
m_cached(o, args) refines F a args
```

The JDK-style `hashCode` race is the guiding example.  A method that reads the
cache twice can fail because the valid trace `read hash = H; read hash = 0`
may return the wrong result.  The local-copy implementation is accepted because
it is correct for every valid cache-read trace.

## Current Status

The generic pure theory is implemented in
[Core/GenericCacheProtocol.v](Core/GenericCacheProtocol.v).  It contains the protocol,
trace, history, method-safety, and refinement definitions, plus the central
trace-robust semantic immutability theorem.

The current derived-cache instance is implemented in
[Core/GenericDerivedCache.v](Core/GenericDerivedCache.v).  It instantiates the generic
theory with the unknown-or-derived cache protocol, weak-memory read bridge,
bad-hash counterexample, local-copy accepted proof shape, and PICO stable
abstraction hooks.

The weak-memory shell is implemented in
[PICOBridge/PicoMemoryModel.v](PICOBridge/PicoMemoryModel.v).  It provides field-addressed histories,
`wm_thread_step`, `wm_step`, `wm_steps`, path-local allowed-config conditions,
and cache-history preservation/read-validity lemmas.

The PICO typing-shaped bridge is implemented in
[PICOBridge/PicoCacheTyping.v](PICOBridge/PicoCacheTyping.v).  It connects verified cache-compute
programs and compute-then-write programs to the generic cache-safe method
boundary.

The Iris-facing generic layer is split across:

- [Iris/GenericCacheGhostState.v](Iris/GenericCacheGhostState.v): first generic
  ghost-backed cache-history snapshot ownership.
- [Iris/IrisSemanticBridge.v](Iris/IrisSemanticBridge.v): the compact public Iris
  surface, centered on `StableAbsI`, `CacheHistI`, `SemImmI`,
  `cache_read_validI`, valid-extension preservation, and
  `cache_safe_method_wpI`.
- [Examples/LocalCopyCacheRule.v](Examples/LocalCopyCacheRule.v): one representative
  Iris-facing rule for the accepted local-copy hash-cache idiom.
- [Iris/GenericCacheIris.v](Iris/GenericCacheIris.v): older pure-Iris theorem wrappers,
  kept as detail/proof-engineering surface.
- [Iris/GenericDerivedCacheIris.v](Iris/GenericDerivedCacheIris.v): derived-cache
  instantiation of the generic Iris layer.

The PICO/Iris facade layer is split across:

- [PICOBridge/PicoIrisLanguage.v](PICOBridge/PicoIrisLanguage.v): minimal Iris language instance
  whose expressions are weak-memory threads.
- [PICOBridge/PicoIrisCacheInvariant.v](PICOBridge/PicoIrisCacheInvariant.v): cache-history
  invariant boundary.
- [PICOBridge/PicoIrisStateInterp.v](PICOBridge/PicoIrisStateInterp.v) and
  [PICOBridge/PicoIrisStateBridge.v](PICOBridge/PicoIrisStateBridge.v): ghost-backed weak-state and
  WP-state bridge facades.
- [PICOBridge/PicoIrisWP.v](PICOBridge/PicoIrisWP.v) and
  [PICOBridge/PicoIrisThreadSafety.v](PICOBridge/PicoIrisThreadSafety.v): primitive-step WP and
  thread-safety wrappers.
- [PICOBridge/PicoIrisSemanticTyping.v](PICOBridge/PicoIrisSemanticTyping.v): current semantic
  typing facade.
- [PICOBridge/PicoIrisLogicalRelation.v](PICOBridge/PicoIrisLogicalRelation.v): LR-facing facade
  over the current semantic typing layer.

## What The Current Pipeline Proves

The implemented path is:

```text
generic protocol facts
  -> derived-cache instance
  -> weak read/write history facts
  -> pure semantic immutability
  -> compact SemImmI / ghost-backed Iris bridge
  -> PICO state, WP, semantic typing, and LR-facing facades
```

This is enough to state the final story through the current facade:

```text
PICO supplies stable abstract-state facts.
The generic cache theorem proves trace-robust cache correctness.
The weak-memory shell connects concrete executions to cache-history facts.
The Iris layer packages those facts as propositions/resources.
```

## Deliberate Non-Claims

- This is not yet a full Java Memory Model proof.
- This is not yet a full type-indexed Iris logical relation for all PICO types.
- The current Iris LR file is still a facade over semantic typing, not the
  final logical relation.
- The weak-memory theorem is field-history parametric: it assumes the memory
  model provides read-from-history and append-style write-history behavior.

## Next Milestones

1. Keep simplifying theorem surfaces around the generic names.
2. Reduce specialized unknown-or-derived wrappers when callers can use
   `cache_valid` directly.
3. Replace facade-style semantic typing with a real type-indexed Iris logical
   relation.
4. Move stable-abstraction preservation into the LR rule structure instead of
   passing it as external side conditions.
5. Only after that, consider a stronger memory-model instantiation beyond the
   current field-history shell.

## Verification Gate

Before treating a milestone as complete:

```sh
make check
```

Required outcome:

- Rocq build passes.
- `scripts/check-no-axioms-admits.py` passes.
- No new `Axiom`, `Admitted`, or `admit`.
