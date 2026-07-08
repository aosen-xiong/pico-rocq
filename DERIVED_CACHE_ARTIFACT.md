# Derived Cache Artifact Status

This note summarizes the derived-cache extension and its relationship to Iris.
It is intended as a reviewer-facing map of the proved trace-robust cache story
and the separate non-claims around full Java/JMM and full type-indexed Iris
soundness.

## Current Status

The artifact now centers on the generic trace-robust derived-cache theorem:

- `Core/GenericCacheProtocol.v` owns the PICO-independent theorem.
- `Core/GenericDerivedCache.v` instantiates it for the current derived-cache model
  and PICO stable-abstraction provider.
- `Iris/IrisSemanticBridge.v` is the compact public Iris surface:
  `StableAbsI`, `CacheHistI`, `SemImmI`, read validity, valid-extension
  preservation, and the method-style `cache_safe_method_wpI` rule.
- `Examples/LocalCopyCacheRule.v` gives one representative Iris-facing local-copy
  cache rule, avoiding a full PICO logical relation in this submission.
- The remaining Iris-facing files expose ghost-backed, state/WP, semantic
  typing, and LR facade entrypoints for that theorem.

We also added preliminary Rocq-side SC and weak-observation PICO models.  These
are stepping stones toward richer concurrency work, not a full Iris
instantiation for PICO and not a Java weak-memory model.

The generic cache theory has now been factored out in
[Core/GenericCacheProtocol.v](Core/GenericCacheProtocol.v).  It defines stable
abstraction providers, cache protocols, cache-history validity, valid
cache-read traces, trace-robust cache-safe methods, valid post-history
extensions, append-preserving trace-write extension relations,
read-from-history soundness, and method soundness without
depending on PICO, including post-execution trace reads through
`valid_trace_from_post_history_with_valid_extension`,
`valid_trace_from_post_snapshot_with_valid_extension`,
`cache_safe_method_sound_from_post_history_with_valid_extension` and
`cache_safe_method_refines_pure_from_post_history_with_valid_extension`, and
valid-write preservation through
`cache_safe_method_writes_history_valid_extension` and
`cache_safe_method_writes_snapshot_valid_extension`.  The central pure
end-to-end statements are `trace_robust_semantic_immutability` and
`trace_robust_semantic_immutability_after_history_extension`: they package
valid history reads, trace-robust method correctness, and writes recorded in
`CacheHistExtendsByTrace` into the post-state semantic-immutability result.
Here `CacheHistExtendsByTrace` is an append relation: each final cache-field
history is the initial history followed by added writes, and every added write
is covered by the method trace.  The generic method predicate itself proves the
result and protocol validity of recorded cache writes; PICO/provider layers
separately supply stable-abstraction preservation and write-avoidance or
final-field obligations.  The theorem result is
`r = F a args /\ SemImm P Hist' Stable o' a`.  The current
derived-cache protocol instance, weak-memory read bridge, motivating bad
hash/local-copy trace examples, and PICO stable-abstraction providers live in
[Core/GenericDerivedCache.v](Core/GenericDerivedCache.v): `pico_stable_abs` for the
sequential heap view and `pico_wm_stable_abs` for the weak-state view where
abstract-field histories are stable at the abstract values, with
`pico_wm_stable_cache_safe_method_sound_after_steps_post_history` and
`pico_wm_stable_cache_safe_method_sound_from_closed_steps_post_history`
connecting PICO final-field stability, weak post histories, and the generic
cache-safe method theorem.  Its method-write/cache-only endpoints
`pico_wm_stable_cache_safe_method_sound_after_steps_write_extension`,
`pico_wm_stable_cache_safe_method_sound_after_steps_cache_only_write_extension`,
and
`pico_wm_stable_cache_safe_method_sound_from_closed_steps_cache_only_write_extension`
instantiate the same theorem for the PICO weak-history provider after a
cache-update execution.  [Iris/GenericCacheIris.v](Iris/GenericCacheIris.v)
exports the generic boundary as pure Iris propositions, including
`valid_trace_from_post_history_with_valid_extensionI`,
`valid_trace_from_post_snapshot_with_valid_extensionI`,
`cache_safe_method_sound_from_post_history_with_valid_extensionI` and
`cache_safe_method_refines_pure_from_post_history_with_valid_extensionI` for
post-execution trace reads, plus
`trace_robust_semantic_immutabilityI` and
`trace_robust_semantic_immutability_after_history_extensionI` for the
end-to-end pure theorem boundary.
[Iris/GenericCacheGhostState.v](Iris/GenericCacheGhostState.v) adds a PICO-independent
auth/agreement resource for one `CacheHistorySnapshot`, with ghost-backed
allocation, read-validity, trace-validity, semantic-immutability, and
post-snapshot allocation from valid history extensions, plus pure-refinement
and post-extension trace/refinement endpoints such as
`generic_cache_history_interp_valid_trace_post_extension` and
`generic_cache_history_interp_refines_pure_post_extension`.  Its public
ghost-backed final-story endpoint is
`generic_trace_robust_semantic_immutability_interp_alloc_post`.
[Iris/IrisSemanticBridge.v](Iris/IrisSemanticBridge.v) provides the reader-facing
interface over that ghost layer, so clients can use `SemImmI` and
`cache_safe_method_wpI` instead of navigating the lower-level theorem wrappers.
[Examples/LocalCopyCacheRule.v](Examples/LocalCopyCacheRule.v) proves the accepted local-copy
hash-cache idiom through that interface.
[Iris/GenericDerivedCacheIris.v](Iris/GenericDerivedCacheIris.v)
instantiates both views for the current derived-cache weak-history bridge,
including `wm_derived_cache_history_interp_valid_trace_post_extension` and
`wm_derived_cache_history_interp_refines_pure_post_extension`, plus
`wm_derived_cache_history_interp_writes_valid_extension`,
`wm_derived_cache_history_interp_writes_valid_extension_alloc`, and the
public theorem
`wm_derived_cache_trace_robust_semantic_immutability_alloc_post` for deriving
post-state semantic immutability directly from a cache-safe method's recorded
writes.
The PICO state and WP-state bridge layers expose the same route through
`pico_cache_state_interp_generic_history_refines_pure_post_extension`,
`pico_cache_state_interp_after_steps_generic_history_refines_pure_post_extension`,
`pico_wp_state_cfg_bridge_generic_history_refines_pure_post_extension`, and
`pico_wp_state_cfg_bridge_after_steps_generic_history_refines_pure_post_extension`.
They now also expose the method-write semantic route through
`pico_cache_state_interp_after_steps_semantic_immutability_method_write_extension_post`
and
`pico_wp_state_cfg_bridge_after_steps_semantic_immutability_method_write_extension_post`,
with PICO-provider conveniences
`pico_cache_state_interp_after_steps_pico_wm_stable_preserved_method_write_extension_post`,
`pico_cache_state_interp_after_steps_pico_wm_stable_final_fields_method_write_extension_post`,
`pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_preserved_method_write_extension_post`,
and
`pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_final_fields_method_write_extension_post`.
The cache-only postcondition `wm_histories_only_extend_field`, combined with
`wm_write_avoids_fields`, now derives abstract-field preservation through
`wm_histories_only_extend_field_preserves_fields`; state and WP bridge expose
that shorter route through the final-story theorems
`pico_cache_state_interp_after_steps_pico_wm_stable_trace_robust_cache_only_post`
and
`pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_trace_robust_cache_only_post`.
The pure weak-history layer derives the cache-only postcondition
from concrete writes and selected field-write steps through
`wm_write_histories_only_extend_field`,
`wm_thread_step_fldwrite_histories_only_extend_field`, and
`wm_step_selected_fldwrite_histories_only_extend_field`.
The semantic typing and LR facades forward these routes through
`sem_typed_state_after_steps_generic_history_refines_pure_post_extensionI`,
`sem_typed_wp_bridge_after_steps_generic_history_refines_pure_post_extensionI`,
`pico_lr_config_state_steps_generic_history_refines_pure_post_extension`, and
`pico_lr_wp_state_bridge_after_steps_generic_history_refines_pure_post_extension`,
plus
`sem_typed_state_after_steps_semantic_immutability_method_write_extension_postI`,
`sem_typed_wp_bridge_after_steps_semantic_immutability_method_write_extension_postI`,
`pico_lr_config_state_steps_semantic_immutability_method_write_extension_post`,
and
`pico_lr_wp_state_bridge_after_steps_semantic_immutability_method_write_extension_post`,
plus preserved/final-field PICO-provider variants
`sem_typed_state_after_steps_pico_wm_stable_preserved_method_write_extension_postI`,
`sem_typed_wp_bridge_after_steps_pico_wm_stable_preserved_method_write_extension_postI`,
`sem_typed_state_after_steps_pico_wm_stable_final_fields_method_write_extension_postI`,
`sem_typed_wp_bridge_after_steps_pico_wm_stable_final_fields_method_write_extension_postI`,
`pico_lr_config_state_steps_pico_wm_stable_preserved_method_write_extension_post`,
`pico_lr_wp_state_bridge_after_steps_pico_wm_stable_preserved_method_write_extension_post`,
`pico_lr_config_state_steps_pico_wm_stable_final_fields_method_write_extension_post`,
and
`pico_lr_wp_state_bridge_after_steps_pico_wm_stable_final_fields_method_write_extension_post`.
They also expose public LR-facing final-story theorems so callers can state
that only the cache field changed, rather than providing
`wm_histories_preserve_fields` directly:
`pico_lr_config_state_steps_pico_wm_stable_trace_robust_cache_only_post` and
`pico_lr_wp_state_bridge_after_steps_pico_wm_stable_trace_robust_cache_only_post`.

The next layer has started in [PICOBridge/PicoMemoryModel.v](PICOBridge/PicoMemoryModel.v): field
addresses, field histories, cache-history validity, a parameterized weak read
interface, and a small-step thread-pool shell over weak-memory state.  This
follows the design principle that weak-memory reasoning should be layered over
histories of field writes rather than by changing PICO's deterministic big-step
semantics.  The weak-memory shell now also exposes allowed-write preservation
and final-read validity endpoints, including direct one-allowed-write/read
validity and multi-step executions whose transitions or pre-state thread pools
satisfy the cache-allowed write contract.
Those preservation results are also exposed as generic
`CacheHistValidExtension` facts between initial and final weak states.

## Intended Final Story

The final paper theorem should be a generic derived-cache theorem, not a
String-specific or PICO-specific theorem:

```text
A racy derived cache is semantically invisible when the method is correct for
every cache-read trace allowed by the cache protocol.
```

The final architecture should have three independent layers.

1. A stable abstraction provider supplies `StableAbs o a`, meaning object `o`
   represents a fixed abstract value `a`.  PICO is one provider of this layer:
   `pico_stable_abs` states the sequential heap view, while
   `pico_wm_stable_abs` states the weak-memory provider as abstract-field
   histories stable at the abstract values.  Other providers could be
   final-field invariants, module abstraction, ownership, or hand-written Iris
   invariants.
2. A cache protocol over histories supplies `valid a k v` for each cache field
   `k`.  `CacheHistOK P o a` means every value ever written to every cache
   field of `o` is valid for the fixed abstract value `a`.
3. A cache-safe method judgment proves trace robustness: for every valid
   cache-read trace, the method returns the pure recomputation result `F a args`,
   writes only valid cache values, and records those writes in the method
   trace.  Provider obligations outside the generic method judgment prove
   abstract-state write avoidance, cache encapsulation, and post-state
   `StableAbs` preservation.

The weak-memory assumption needed by the generic theorem is intentionally
small: cache reads come from field histories, cache writes extend field
histories, and reads observe whole written values.  In paper terms this should
be stated as a memory-model side condition `AtomicCacheField(k)`: reads and
writes of cache field `k` observe complete values, not torn halves.  This is
weak-memory-parametric field-history soundness, not a full Java Memory Model
claim.  For Java, plain `int`, `boolean`, and reference cache fields satisfy
the value-atomicity part of this condition, while plain non-volatile `long` and
`double` cache fields are rejected unless accessed through `volatile`,
synchronization, atomic wrappers, or a verified representation-specific
protocol.  Object-valued caches additionally need a safe-publication or stable
representation premise for the object behind the reference.

The intended main theorem is:

```text
StableAbs o a
  and CacheHistOK P o a
  and CacheSafe m P F
  and a post history that appends the method's protocol-valid cache writes
  imply the method result is F a args and the post history remains
  semantically immutable for the same stable abstraction provider.
```

The generic core now names this as `CacheRefinesPure`, with executions returning
the `PureRecomputeResult` `F a args`:

```text
m_cached(o, args) refines m_pure(o, args) = F a args.
```

This story also captures the JDK-style hash-cache bug precisely.  For a hash
cache with valid values `0` or the correct hash `H`, the implementation

```java
if (hash == 0) {
    hash = computeHash();
}
return hash;
```

is not cache-safe because a valid trace can read `hash = H` at the branch and
then `hash = 0` at the return.  The local-copy version is the proof shape the
generic trace theorem should accept.

The current artifact now implements the first generic version of this story.
`Core/GenericCacheProtocol.v` is the PICO-independent central theory, while
`Core/GenericDerivedCache.v` and the PICO files are provider and execution-layer
bridges around it.  The local-copy hash example proves
`good_hash_refines_pure_recompute`, while the bad hash example remains rejected
by `bad_hash_not_cache_safe`.  The Iris semantic-cache, invariant, state-interpretation,
WP-state bridge, semantic typing, and LR facade layers now expose generic
`CacheHistOK` and `cache_valid` endpoints alongside the older
unknown-or-derived wrappers.  The first generic ghost-backed interpretation is
now present in `Iris/GenericCacheGhostState.v` and instantiated for derived-cache
weak histories in `Iris/GenericDerivedCacheIris.v`.  `PICOBridge/PicoIrisStateInterp.v` and
`PICOBridge/PicoIrisStateBridge.v` now thread that generic ownership through
`pico_cache_state_interp` and `pico_wp_state_cfg_bridge`, exposing generic
history allocation, read-validity, and pure-refinement endpoints for both the
current weak state and post-`wm_steps` weak states.  The semantic-typing and LR
facades now expose direct generic-ghost consumers under
`sem_typed_*_generic_history_*` and `pico_lr_*_generic_history_*` names,
including after-step wrappers.  The LR facade also has generic
allocation-to-final-read wrappers for state and WP-bridge execution-prefix,
closed-step, closure-step, and direct `wm_steps` paths, so new clients can end
at `cache_valid` instead of re-entering `derived_cache_msg_ok`.  Cache-update
tail read specs, compute/write tail read specs, and selected-first execution
wrappers now also have generic final-read variants, with generic
allocation/read-spec endpoints for invariant, state, and WP-bridge tail
resources.  The selected-first and post-first-step tail-pool LR wrappers also
carry generic `cache_valid` conclusions through existing-resource,
allocation-to-read, semantic, and combined `pico_lr_configI` facade paths.  The
bundled `pico_lr_cache_update_execution_specI` layer now has generic
final-read, existing-resource read, allocation-to-read, final-resource/read,
and from-safe closure/thread-post/covered-step variants as well, so the
single-spec execution path no longer has to collapse back to
`derived_cache_msg_ok`.  The direct `closedI`, `coveredI`, and `thread_postI`
execution facades now expose the same generic `cache_valid` read-validity
boundary for final reads, existing invariant/state/WP resources, and
allocation-to-read paths.  The semantic selected-first LR wrappers now expose
matching generic closure/configI read-validity endpoints.  The weak-memory
allowed-write/config-allowed read boundaries now also have generic
`cache_valid` variants through the pure, semantic-cache, state/WP bridge, and
LR facade layers, including direct one-allowed-write/read endpoints.
The same weak-memory preservation results also expose generic
`CacheHistValidExtension` facts, which are the post-history premise consumed by
the generic method soundness theorem.  These facts are now available through
the cache invariant, state-interpretation facade, WP-state bridge, and LR
facade layers.
The state, WP-bridge, semantic-typing, and LR layers now also package the full
generic method-post result: pure recomputation plus post-state
`generic_semantic_immutability_interp`.  They also expose PICO-provider
specializations fixed to `pico_wm_stable_abs`, so the public story is
PICO supplies the stable abstraction and the generic cache theory supplies the
trace-robust semantic-immutability theorem.  For the state, WP-bridge,
semantic-typing, and LR entry points, the post PICO stable abstraction can now
be derived from pre stability plus a path-local `wm_steps_writes_avoid_fields`
proof that each write in the actual `wm_steps` execution avoids the abstract
fields.  The stronger PICO-provider path derives the same post stability
directly from the receiver runtime type and
`final_fields CT C abs_fields`, via
`wm_steps_preserve_pico_wm_stable_abs_from_final_fields`, so clients no longer
need to manufacture write-avoidance separately when PICO final-field typing is
available.  The pure PICO-provider layer now also packages this route with the
generic post-history method theorem in
`pico_wm_stable_cache_safe_method_sound_after_steps_post_history` and
`pico_wm_stable_cache_safe_method_sound_from_closed_steps_post_history`.
The older specialized consumers remain as compatibility/proof-engineering
surface, but the public theorem path now points at the generic
trace-robust names.

## Level 1: Iris Wrapper Using heap_lang

Main file:

- [Examples/StringCacheIris.v](Examples/StringCacheIris.v)

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

- [PICO_IRIS_ROADMAP.md](PICO_IRIS_ROADMAP.md)
- [Iris/DerivedCacheIris.v](Iris/DerivedCacheIris.v)
- [Core/GenericCacheProtocol.v](Core/GenericCacheProtocol.v)
- [Iris/GenericCacheIris.v](Iris/GenericCacheIris.v)
- [Iris/GenericCacheGhostState.v](Iris/GenericCacheGhostState.v)
- [Core/GenericDerivedCache.v](Core/GenericDerivedCache.v)
- [Iris/GenericDerivedCacheIris.v](Iris/GenericDerivedCacheIris.v)
- [PICOBridge/PicoIrisLanguage.v](PICOBridge/PicoIrisLanguage.v)
- [PICOBridge/PicoIrisSemanticCache.v](PICOBridge/PicoIrisSemanticCache.v)
- [PICOBridge/PicoIrisCacheInvariant.v](PICOBridge/PicoIrisCacheInvariant.v)
- [PICOBridge/PicoIrisStateInterp.v](PICOBridge/PicoIrisStateInterp.v)
- [PICOBridge/PicoIrisWP.v](PICOBridge/PicoIrisWP.v)
- [PICOBridge/PicoIrisThreadSafety.v](PICOBridge/PicoIrisThreadSafety.v)
- [PICOBridge/PicoIrisSemanticTyping.v](PICOBridge/PicoIrisSemanticTyping.v)
- [PICOBridge/PicoIrisLogicalRelation.v](PICOBridge/PicoIrisLogicalRelation.v)
- [PICOBridge/PicoIrisCacheBridge.v](PICOBridge/PicoIrisCacheBridge.v)

What they contain:

- a staged roadmap for the PICO Iris pipeline, including current verified
  theorem boundaries and explicit non-claims before the full ghost-backed
  logical relation;
- pure Iris wrappers such as `field_readsI` and
  `derived_int_cache_protocolI`;
- a minimal Iris `language` instance whose expressions are `wm_thread`, whose
  state is `wm_state`, and whose primitive step is `wm_thread_step`;
- named value/non-value facts for PICO statements in that language, including
  `pico_to_val_inv`, `pico_to_val_some_inv`,
  `pico_language_to_val_inv`, `pico_language_to_val_some_inv`,
  `pico_language_to_val_var_assign`, `pico_language_to_val_fld_write`, and
  `pico_language_to_val_seq`, so WP rules can cite the language boundary
  instead of reducing the statement syntax ad hoc;
- reducibility and not-stuck bridge lemmas,
  `pico_reducible_iff_thread_step` and
  `pico_not_stuck_iff_value_or_thread_step`, exposing the Iris operational
  boundary directly in terms of `wm_thread_step`;
- primitive statement progress wrappers for assignment, field read, field
  write, sequence-skip, and sequence-step shapes, including
  `pico_assign_int_thread_step_exists`,
  `pico_field_read_thread_step_exists`,
  `pico_fldwrite_thread_step_exists`,
  `pico_seqskip_thread_step_exists`, and
  `pico_seqstep_thread_step_exists`, with matching `not_stuck` lemmas under
  the explicit operational premises of each weak step rule;
- a WP state-bridge contract, `pico_wp_state_bridge_lift_premise` and
  `pico_wp_state_bridge_step_contract`, naming the future obligation that will
  connect Iris's abstract `state_interp` to `pico_wp_state_cfg_bridge` during
  primitive-step updates, plus
  `pico_wp_state_bridge_step_contract_lift_premise`, proving that this
  stronger bridge-aware contract entails the ordinary PICO WP lift premise,
  general cache-safe views
  `pico_wp_state_bridge_step_contract_cache_safe_contract` and
  `pico_wp_state_bridge_step_contract_cache_safe_lift_premise`,
  reverse conversions
  `pico_wp_state_bridge_cache_safe_lift_premise_lift_premise` and
  `pico_wp_state_bridge_cache_safe_contract_step_contract` under explicit
  thread cache safety,
  with cache-safe variants
  `pico_wp_state_bridge_cache_safe_lift_premise`,
  `pico_wp_state_bridge_cache_safe_step_contract`,
  `pico_wp_state_bridge_cache_safe_step_contract_lift_premise`, and
  `pico_wp_state_bridge_cache_safe_contract_from_step_contract` for
  thread-safety and semantic-typing continuations, plus
  `pico_sem_typed_thread_cacheI_bridge_cache_safe_contract` and
  `pico_lr_threadI_bridge_cache_safe_contract`, which connect semantic typed
  threads and LR threads to the cache-safe bridge boundary, together with
  `pico_sem_typed_thread_cacheI_bridge_cache_safe_lift_premise` and
  `pico_lr_threadI_bridge_cache_safe_lift_premise` for clients that need the
  cache-safe WP lifting premise directly, direct ordinary lift adapters
  `pico_sem_typed_thread_cacheI_bridge_lift_premise` and
  `pico_lr_threadI_bridge_lift_premise`, and reverse semantic/LR adapters
  `pico_sem_typed_thread_cacheI_bridge_lift_premise_from_cache_safe`,
  `pico_sem_typed_thread_cacheI_bridge_contract_from_cache_safe`,
  `pico_lr_threadI_bridge_lift_premise_from_cache_safe`, and
  `pico_lr_threadI_bridge_contract_from_cache_safe`, plus selected-thread
  config adapters `pico_sem_typed_config_cacheI_nth_thread_cache_safeI`,
  `pico_sem_typed_config_cacheI_nth_bridge_cache_safe_contract`,
  `pico_sem_typed_config_cacheI_nth_thread_entryI`,
  `pico_sem_typed_config_cacheI_nth_threadI`,
  `pico_sem_typed_config_cacheI_nth_threadI_elim`,
  `pico_sem_typed_config_cacheI_nth_thread_bridge_lift_premise`,
  `pico_sem_typed_config_cacheI_nth_thread_bridge_cache_safe_lift_premise`,
  `pico_sem_typed_config_cacheI_nth_thread_bridge_cache_safe_contract`,
  `pico_sem_typed_config_cacheI_nth_bridge_cache_safe_lift_premise`,
  `pico_sem_typed_config_cacheI_nth_bridge_lift_premise`,
  `pico_lr_configI_nth_thread_cache_safeI`,
  `pico_lr_configI_nth_thread_entryI`,
  `pico_lr_configI_nth_threadI`,
  `pico_lr_configI_nth_threadI_elim`,
  `pico_lr_configI_nth_thread_bridge_lift_premise`,
  `pico_lr_configI_nth_thread_bridge_cache_safe_lift_premise`,
  `pico_lr_configI_nth_thread_bridge_cache_safe_contract`,
  `pico_lr_configI_nth_bridge_cache_safe_contract`, and
  `pico_lr_configI_nth_bridge_cache_safe_lift_premise`, and
  `pico_lr_configI_nth_bridge_lift_premise`, with reverse
  selected-thread adapters
  `pico_sem_typed_config_cacheI_nth_bridge_lift_premise_from_cache_safe`,
  `pico_sem_typed_config_cacheI_nth_bridge_contract_from_cache_safe`,
  `pico_lr_configI_nth_bridge_lift_premise_from_cache_safe`, and
  `pico_lr_configI_nth_bridge_contract_from_cache_safe`;
- LR-facing operation-level progress wrappers,
  `pico_lr_assign_int_not_stuckI`, `pico_lr_field_read_not_stuckI`,
  `pico_lr_fldwrite_not_stuckI`, `pico_lr_seqskip_not_stuckI`, and
  `pico_lr_seqstep_not_stuckI`, which pair the LR thread-step environment
  adapters with the corresponding PICO Iris language `not_stuck` facts;
- LR WP wrappers for state-independent progress cases,
  `wp_pico_lr_assign_int_step_progress` and
  `wp_pico_lr_seqskip_step_progress`, which discharge the generic
  `NotStuck` existential-step premise before handing control to the WP
  continuation;
- LR WP wrappers for state-dependent read/write progress,
  `wp_pico_lr_field_read_step_progress` and
  `wp_pico_lr_fldwrite_step_progress`, which obtain read/write witnesses after
  `state_interp` exposes the current weak state and then discharge the generic
  existential-step premise;
- an LR WP wrapper for compositional sequence-step progress,
  `wp_pico_lr_seqstep_step_progress`, which discharges the same generic
  progress premise from a first-component `wm_thread_step` witness;
- a literal cache-update tail-write specialization,
  `wp_pico_lr_cache_update_tail_fldwrite_step_progress`, routing the
  post-assignment cache write through the generic LR field-write WP progress
  wrapper while deriving the tail receiver/tmp runtime facts from the
  cache-update safety record;
- semantic-layer literal cache-update WP progress endpoints,
  `wp_pico_sem_cache_update_tail_fldwrite_step_progress` and
  `wp_pico_lift_sem_cache_update_sequence_full_progress`, exposing the same
  tail-write and selected-assignment-plus-tail path before the LR facade;
- a composed full literal cache-update WP rule,
  `wp_pico_lr_sem_cache_update_sequence_full_progress`, sequencing the
  selected assignment step with the state-dependent tail-write progress
  wrapper under the LR cache-update interpretation by delegating to the
  semantic full-cache-update WP boundary;
- pure Iris wrappers for field-addressed cache-history validity and semantic
  cache safety, including allowed-write one-step read validity and multi-step
  final-read validity;
- an invariant-backed cache-history interpretation,
  `pico_cache_history_inv`, which protects
  `wm_config_cache_history_stateI` behind an Iris namespace;
- invariant operations,
  `pico_cache_history_inv_read_valid`,
  `pico_cache_history_inv_read_unknown_or_derived`,
  `pico_cache_history_inv_after_execution_alloc`,
  `pico_cache_history_inv_after_execution_read_valid`, and
  `pico_cache_history_inv_after_execution_read_unknown_or_derived`, giving the
  first real Iris boundary that can later be refined with ghost state;
- invariant-backed generic valid-extension endpoints,
  `pico_cache_history_inv_valid_extension_generic`,
  `pico_cache_history_inv_after_execution_valid_extension_generic`, and
  `pico_cache_history_inv_after_steps_valid_extension_generic`, exposing the
  post-history premise consumed by the generic method theorem;
- a one-step invariant transport operation,
  `pico_cache_history_inv_after_thread_step_alloc`, which reallocates the
  cache-history invariant for the post-state of a cache-safe PICO thread step;
- a config-step invariant transport operation,
  `pico_cache_history_inv_after_config_step_alloc`, lifting the same idea to
  an interleaving-style `wm_step` when the pre-configuration is cache-safe;
- a multi-step invariant transport operation,
  `pico_cache_history_inv_after_steps_alloc`, matching the pure
  `cache_safe_config_semantic_cache_safe` boundary for `wm_steps`;
- an invariant-backed multi-step read endpoint,
  `pico_cache_history_inv_after_steps_read_valid`, plus
  `pico_cache_history_inv_after_steps_read_unknown_or_derived`, composing
  invariant transport with weak-read validity and explicit read classification
  at the final configuration;
- a first ghost cache-state layer,
  `PICOBridge/PicoIrisGhostState.v`, defining `picoCacheG`,
  `pico_cache_weak_state_auth`, `pico_cache_weak_state_own`,
  `pico_cache_field_history_auth`, `pico_cache_field_history_own`,
  `pico_cache_history_auth`, and `pico_cache_history_own` as minimal Iris
  authoritative agreement resources for the weak-memory state, an
  address-indexed field-history map, and the concrete target field history;
- a ghost-backed state-interpretation facade,
  `pico_cache_state_interp`, with allocation, one-thread-step transport,
  target/non-target/allowed write transport, concrete field-write step
  transport, direct allowed-write/read generic validity, multi-step transport,
  generic valid-extension transport, generic and PICO-provider method-post
  transport,
  preservation-function transport, and final-read wrappers, including direct and allocation-to-read
  unknown-or-derived read-shape variants, currently
  packaging hidden authoritative weak-state, per-field target-history, and
  target-history ownership together with `pico_cache_history_inv` as the API
  to preserve when refining ownership to broader per-field memory cells;
- a first WP-facing lifting lemma, `wp_pico_lift_thread_step`, which
  specializes Iris's generic lifting rule to PICO's `wm_thread_step` while
  leaving `state_interp` abstract;
- WP-facing thread-safety adapters,
  `pico_thread_cache_safeI_step_preserves_cacheI` and
  `wp_pico_lift_cache_safe_thread_stepI`, plus the existential-step variants
  `wp_pico_lift_cache_safe_thread_step_exists` and
  `wp_pico_lift_cache_safe_thread_step_existsI`, allowing clients to consume
  the named `pico_thread_cache_safeI` proposition rather than raw
  `cache_safe_thread` at the WP boundary and to supply only a concrete
  `wm_thread_step` witness in `NotStuck` mode;
- a WP-state bridge,
  `PICOBridge/PicoIrisStateBridge.v`, defining `pico_wp_state_cfg_bridge` as the explicit
  contract that the WP-visible weak state is the `wc_state` protected by
  `pico_cache_state_interp`, with allocation, equality-extraction,
  target-history validity, read-validity, primitive-step transport,
  allowed-write transport, direct allowed-write/read generic validity,
  generic valid-extension transport, generic and PICO-provider method-post
  transport,
  concrete field-write step transport,
  multi-step transport, multi-step final-read validity, explicit unknown-or-derived
  read-shape variants, and allocation-to-final-read endpoints for both
  derived-cache validity and the explicit read shape, including the generic
  preservation-function endpoint
  `pico_wp_state_cfg_bridge_alloc_after_steps_preserved_read_valid_generic`;
- a WP-facing cache-safety lifting lemma,
  `wp_pico_lift_cache_safe_thread_step`, which passes a pure
  cache-history-preservation fact to the continuation of a cache-safe thread;
- first semantic typing wrappers, including `pico_sem_typed_thread_cacheI` and
  `pico_sem_typed_config_cacheI`, the reusable config entry predicate
  `sem_typed_thread_entry`, rule-shaped constructors such as `sem_cache_seqI`,
  the adapters `pico_sem_typed_thread_cacheI_cache_safe` and
  `pico_sem_typed_thread_cacheI_entry`, the config interpretation bridge
  `pico_sem_typed_config_cacheI_interp`, and the WP rule
  `wp_pico_lift_sem_typed_thread_step`, and the existential-step wrapper
  `wp_pico_lift_sem_typed_thread_step_exists`, which let WP and config-level
  proofs consume named PICO typing-plus-cache-safety facts instead of raw
  syntactic premises;
- semantic-typing method-post wrappers,
  `sem_typed_state_after_steps_semantic_immutability_method_postI`,
  `sem_typed_wp_bridge_after_steps_semantic_immutability_method_postI`,
  `sem_typed_state_after_steps_pico_wm_stable_method_postI`, and
  `sem_typed_wp_bridge_after_steps_pico_wm_stable_method_postI`, which route
  typed config-entry preservation into the generic post-state semantic
  immutability theorem;
- preservation-based semantic-typing method-post wrappers,
  `sem_typed_state_after_steps_pico_wm_stable_preserved_method_postI` and
  `sem_typed_wp_bridge_after_steps_pico_wm_stable_preserved_method_postI`,
  which derive the post PICO stable abstraction from abstract-field
  write-avoidance instead of requiring it as a separate premise;
- final-field semantic-typing method-post wrappers,
  `sem_typed_state_after_steps_pico_wm_stable_final_fields_method_postI` and
  `sem_typed_wp_bridge_after_steps_pico_wm_stable_final_fields_method_postI`,
  which derive post PICO stability from the initial receiver type and
  `final_fields CT C abs_fields`;
- matching preservation-based and final-field state/WP/LR method-post wrappers,
  `pico_cache_state_interp_after_steps_pico_wm_stable_preserved_method_post`,
  `pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_preserved_method_post`,
  `pico_lr_wp_state_bridge_after_steps_pico_wm_stable_preserved_method_post`,
  `pico_lr_config_state_steps_pico_wm_stable_preserved_method_post`,
  `pico_cache_state_interp_after_steps_pico_wm_stable_final_fields_method_post`,
  `pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_final_fields_method_post`,
  `pico_lr_wp_state_bridge_after_steps_pico_wm_stable_final_fields_method_post`,
  and `pico_lr_config_state_steps_pico_wm_stable_final_fields_method_post`;
- a semantic-typed invariant updater,
  `pico_sem_typed_thread_cacheI_inv_step_update`, deriving the one-step
  invariant transport from the semantic thread interpretation and a concrete
  `wm_thread_step` through the named thread-safety adapter;
- a semantic-config invariant updater,
  `pico_sem_typed_config_cacheI_inv_step_update`, deriving config-step
  invariant transport from `pico_sem_typed_config_cacheI` and a concrete
  `wm_step`;
- a semantic multi-step invariant updater,
  `sem_typed_config_entry_interpretation_inv_steps_update`, deriving
  multi-step invariant transport from the config-level semantic typing
  interpretation supplied at every stepped pre-state;
- a semantic invariant-backed final-read endpoint,
  `sem_typed_config_entry_interpretation_inv_steps_read_valid`, deriving
  final weak-read validity from the same semantic config interpretation and
  initial cache-history invariant;
- semantic config-interpretation closure endpoints,
  `sem_typed_config_entry_interpretation_step_update` and
  `sem_typed_config_entry_interpretation_seqstep_update`, plus
  `sem_typed_config_entry_interpretation_closed_final_read_validI`, packaging
  config-list replacement for one stepped thread and deriving final weak-read
  validity from an initial semantic config interpretation plus a step
  preservation closure;
- post-thread-entry preservation for covered weak steps,
  `sem_typed_thread_entry_assign_int_post`,
  `sem_typed_thread_entry_field_read_post`,
  `sem_typed_thread_entry_fldwrite_post`, and
  `sem_typed_thread_entry_seqskip_post`;
- a post-environment-aware sequence residual entry rule,
  `sem_typed_thread_entry_seqstep_residual_post`, which reassembles the
  residual sequence from first-step post typing/cache safety and second-phase
  cache safety under the post runtime environment;
- concrete first-component sequence residual endpoints,
  `sem_typed_thread_entry_seqstep_assign_int_post`,
  `sem_typed_thread_entry_seqstep_field_read_post`, and
  `sem_typed_thread_entry_seqstep_fldwrite_post`, reducing assignment/read/write
  sequence steps to explicit post-tail cache-safety obligations;
- a first logical-relation facade,
  `PICOBridge/PicoIrisLogicalRelation.v`, naming `pico_lr_stmtI`,
  `pico_lr_method_bodyI`, `pico_lr_threadI`, `pico_lr_thread_entry`,
  `pico_lr_configI`, and
  `pico_lr_config_interp` as the stable LR-facing API over the current pure
  semantic typing layer;
- first value/environment logical-relation predicates,
  `pico_lr_valueI` and `pico_lr_envI`, relating weak-memory object values to
  `wm_get_type`, static qualified types, base subtyping, and runtime qualifier
  typability, with lookup, local-null extension, assignment-style update, and
  weak-write preservation lemmas;
- a typed-thread LR package, `pico_lr_typed_threadI`, pairing
  `pico_lr_threadI` with the runtime environment interpretation
  `pico_lr_envI`, with intro/elimination projections and
  `pico_lr_typed_thread_state_env_step_update` and
  `pico_lr_typed_thread_wp_state_bridge_env_step_update` for carrying the
  bundled type/cache/env boundary through one weak-memory step at both the
  ghost-backed state facade and the WP-state bridge;
- selected-config typed-thread package wrappers,
  `pico_lr_typed_thread_step_envI`,
  `pico_lr_typed_thread_step_envI_intro`,
  `pico_lr_typed_thread_step_envI_elim`,
  `pico_lr_typed_thread_step_envI_from_interp`,
  `pico_lr_typed_thread_step_resultI`,
  `pico_lr_typed_thread_step_resultI_intro`,
  `pico_lr_typed_thread_step_resultI_elim`,
  `pico_lr_typed_thread_step_resultI_thread`,
  `pico_lr_typed_thread_step_resultI_env`,
  `pico_lr_typed_thread_step_env_state_update`,
  `pico_lr_typed_thread_step_env_state_update_result`,
  `pico_lr_typed_thread_step_env_wp_state_bridge_update`,
  `pico_lr_typed_thread_step_env_wp_state_bridge_update_result`,
  `pico_lr_typed_thread_step_env_package_from_interp`,
  `pico_lr_config_nth_typed_thread_step_envI`,
  `pico_lr_config_nth_typed_thread_step_envI_intro`,
  `pico_lr_config_nth_typed_thread_step_envI_from_interp`,
  `pico_lr_config_nth_typed_thread_step_envI_from_step_env`,
  `pico_lr_config_nth_typed_thread_step_envI_from_thread_env_interp`,
  `pico_lr_config_nth_typed_thread_step_envI_from_thread_step_env_package`,
  `pico_lr_config_nth_typed_thread_step_envI_from_interp_package`,
  `pico_lr_config_nth_typed_thread_step_envI_elim`,
  `pico_lr_config_nth_typed_thread_step_envI_configI`,
  `pico_lr_config_nth_typed_thread_step_envI_nth`,
  `pico_lr_config_nth_typed_thread_step_envI_typed_step_envI`,
  `pico_lr_config_nth_typed_thread_step_envI_raw_step_envI`,
  `pico_lr_config_nth_typed_thread_step_resultI`,
  `pico_lr_config_nth_typed_thread_step_resultI_intro`,
  `pico_lr_config_nth_typed_thread_step_resultI_elim`,
  `pico_lr_config_nth_typed_thread_step_resultI_nth`,
  `pico_lr_config_nth_typed_thread_step_resultI_typed_resultI`,
  `pico_lr_config_nth_typed_thread_step_resultI_raw`,
  `pico_lr_config_nth_typed_thread_step_envI_thread_entryI`,
  `pico_lr_config_nth_typed_thread_step_envI_thread_cache_safeI`,
  `pico_lr_config_nth_typed_thread_step_envI_state_update_result`,
  `pico_lr_config_nth_typed_thread_step_envI_state_update_result_package`,
  `pico_lr_config_nth_typed_thread_step_resultI_state_update_raw`,
  `pico_lr_config_nth_typed_thread_step_resultI_state_read_valid`,
  `pico_lr_config_nth_typed_thread_step_resultI_state_read_valid_generic`,
  `pico_lr_config_nth_typed_thread_step_resultI_state_read_unknown_or_derived`,
  `pico_lr_config_nth_typed_thread_step_envI_state_update_raw`,
  `pico_lr_config_nth_typed_thread_step_envI_wp_state_bridge_update_result`,
  `pico_lr_config_nth_typed_thread_step_envI_wp_state_bridge_update_result_package`,
  `pico_lr_config_nth_typed_thread_step_resultI_wp_state_bridge_update_raw`,
  `pico_lr_config_nth_typed_thread_step_resultI_wp_state_bridge_read_valid`,
  `pico_lr_config_nth_typed_thread_step_resultI_wp_state_bridge_read_valid_generic`,
  `pico_lr_config_nth_typed_thread_step_resultI_wp_state_bridge_read_unknown_or_derived`,
  `pico_lr_config_nth_typed_thread_step_envI_wp_state_bridge_update_raw`,
  `pico_lr_configI_nth_typed_state_env_step_update_package`,
  `pico_lr_configI_nth_typed_state_env_step_update_package_result`,
  `pico_lr_configI_nth_typed_state_env_step_update_from_interp_package`,
  `pico_lr_configI_nth_typed_state_env_step_update_from_interp_package_result`,
  `pico_lr_configI_nth_typed_state_env_step_update_result_raw`,
  `pico_lr_configI_nth_typed_wp_state_bridge_env_step_update_package`, and
  `pico_lr_configI_nth_typed_wp_state_bridge_env_step_update_package_result`,
  `pico_lr_configI_nth_typed_wp_state_bridge_env_step_update_from_interp_package`,
  `pico_lr_configI_nth_typed_wp_state_bridge_env_step_update_from_interp_package_result`,
  `pico_lr_configI_nth_typed_wp_state_bridge_env_step_update_result_raw`,
  allowing scheduled-thread proofs to pass the bundled typed-thread resource
  instead of separate thread and environment resources, and optionally receive
  the named typed-thread step result or project it back to the raw
  thread/env/resource shape;
- first expression logical-relation predicate,
  `pico_lr_exprI`, with null, integer literal, and variable constructors plus
  `pico_lr_assign_int_env_update`, connecting typed integer expressions to the
  runtime environment update used by assignment steps;
- expression-to-environment LR transport,
  `pico_lr_valueI_subtype`, `pico_lr_envI_update_subtype`,
  `pico_lr_assign_expr_env_update`, and
  `pico_lr_field_read_assign_env_update`, allowing typed expression results
  to update target variables through qualified subtyping, including the
  field-read assignment shape used by `WMTS_FieldRead`;
- concrete weak-step environment endpoints,
  `pico_lr_assign_int_step_env_update` and
  `pico_lr_field_read_step_env_update`, exposing LR post-environment facts for
  the assignment-producing `WMTS_AssignInt` and `WMTS_FieldRead` step shapes;
- sequence-step LR environment endpoints,
  `pico_lr_seqskip_step_env_preserved`, `pico_lr_seqstep_env_lift`, and
  `pico_lr_seqstep_env_update`, giving compositional hooks for
  `WMTS_SeqSkip` and `WMTS_SeqStep` residual threads;
- a named thread-step environment predicate,
  `pico_lr_thread_step_envI`, plus the pure interpretation
  `pico_lr_thread_step_env_interp`, with constructors for assignment-int,
  field-read, field-write, sequence-skip, and sequence-step cases, providing
  a stable target for later induction over `wm_thread_step`;
- a generic combined thread-step transport theorem,
  `pico_lr_thread_state_env_step_update`, plus the pure-interpretation
  wrapper `pico_lr_thread_state_env_step_update_from_interp`, which compose
  the thread-step environment interpretation with `pico_lr_threadI` and
  `pico_cache_state_interp` to update both the LR environment and the
  ghost-backed cache-state facade for one weak thread step;
- case-specific combined state/env thread-step wrappers,
  `pico_lr_assign_int_state_env_step_update`,
  `pico_lr_field_read_state_env_step_update`,
  `pico_lr_fldwrite_generic_state_env_step_update`, and
  `pico_lr_seqskip_state_env_step_update`, plus
  `pico_lr_seqstep_state_env_step_update` for compositional residual sequence
  steps, exposing the same combined update directly for covered operational
  step shapes;
- WP-state bridge/env transport,
  `pico_lr_thread_wp_state_bridge_env_step_update`, plus the
  pure-interpretation wrapper
  `pico_lr_thread_wp_state_bridge_env_step_update_from_interp`, with
  case-specific wrappers for assignment-int, field-read, field-write,
  sequence-skip, and sequence-step weak thread steps, carrying the LR
  environment alongside `pico_wp_state_cfg_bridge`;
- LR-facing WP-state bridge execution transport,
  `pico_lr_wp_state_bridge_after_steps` and
  `pico_lr_wp_state_bridge_after_steps_read_valid`, deriving multi-step bridge
  preservation and final weak-read validity from `pico_lr_config_interp`;
- LR-facing allocation-to-execution endpoint,
  `pico_lr_wp_state_bridge_alloc_steps_read_valid`, allocating the
  WP-state bridge from the initial pure cache-history state and deriving final
  weak-read validity from `pico_lr_config_interp`;
- LR-facing config interpretation closure endpoints,
  `pico_lr_config_step_update`,
  `pico_lr_config_step_closure`,
  `pico_lr_config_step_closure_from_thread_post`,
  `pico_lr_config_step_closure_from_covered`,
  `pico_lr_config_closed_steps_read_validI`, and
  `pico_lr_config_closed_steps_preserve_cache_history`, replacing the global
  prefix-interpretation assumption with an initial config interpretation plus
  a per-step preservation closure;
- LR-facing named closure endpoints,
  `pico_lr_config_closure_steps_read_validI`,
  `pico_lr_config_closure_steps_preserve_cache_history`,
  `pico_lr_config_state_closure_steps_update`,
  `pico_lr_config_state_closure_steps_read_valid`,
  `pico_lr_config_state_alloc_closure_steps_read_valid`,
  `pico_lr_wp_state_bridge_after_closure_steps`,
  `pico_lr_wp_state_bridge_after_closure_steps_read_valid`, and
  `pico_lr_wp_state_bridge_alloc_closure_steps_read_valid`, allowing later
  callers to pass a stable closure object instead of restating the full
  per-step function type at each state or WP bridge boundary;
- LR-facing closed-execution state and WP-bridge endpoints,
  `pico_lr_config_state_closed_steps_update`,
  `pico_lr_config_state_closed_steps_read_valid`,
  `pico_lr_config_state_alloc_closed_steps_read_valid`,
  `pico_lr_wp_state_bridge_after_closed_steps`,
  `pico_lr_wp_state_bridge_after_closed_steps_read_valid`, and
  `pico_lr_wp_state_bridge_alloc_closed_steps_read_valid`, connecting the
  same closed config interpretation closure to the ghost-backed state facade
  and WP-state bridge;
- LR-facing post-entry and config-update endpoints for covered weak steps,
  including `pico_lr_thread_entry_assign_int_post`,
  `pico_lr_thread_entry_field_read_post`,
  `pico_lr_thread_entry_fldwrite_post`,
  `pico_lr_thread_entry_seqskip_post`,
  `pico_lr_config_assign_int_step_update`,
  `pico_lr_config_field_read_step_update`,
  `pico_lr_config_fldwrite_step_update`,
  `pico_lr_config_seqskip_step_update`, and
  `pico_lr_config_seqstep_step_update`, where the sequence-step wrapper makes
  the residual thread-entry proof the explicit remaining preservation
  obligation;
- LR-facing sequence residual wrappers,
  `pico_lr_thread_entry_seqstep_residual_post` and
  `pico_lr_config_seqstep_residual_step_update`, which discharge that residual
  entry once post-step typing/cache safety for the first component and
  post-environment cache safety for the second component are available;
- LR-facing concrete sequence first-step wrappers,
  `pico_lr_thread_entry_seqstep_assign_int_post`,
  `pico_lr_thread_entry_seqstep_field_read_post`,
  `pico_lr_thread_entry_seqstep_fldwrite_post`,
  `pico_lr_config_seqstep_assign_int_step_update`,
  `pico_lr_config_seqstep_field_read_step_update`, and
  `pico_lr_config_seqstep_fldwrite_step_update`;
- a unified covered-step closure interface,
  `pico_lr_covered_thread_step_post`,
  `pico_lr_covered_thread_step_post_entry`, and
  `pico_lr_config_covered_step_update`, packaging the supported assignment,
  field-read, field-write, sequence-skip, and sequence-step update cases
  behind one config-preservation premise;
- covered-step final-read endpoints,
  `pico_lr_config_covered_steps_read_validI` and
  `pico_lr_covered_steps_read_valid_fupd`, deriving final weak-read validity
  from an initial LR config interpretation plus covered-step evidence along
  the execution;
- post-entry closure final-read and preservation endpoints,
  `pico_lr_config_thread_post_steps_read_validI` and
  `pico_lr_config_thread_post_steps_preserve_cache_history`, deriving the same
  multi-step cache-history/read facts from per-step post-thread LR entries
  without constructing covered-step evidence;
- covered-step state and WP-bridge transport endpoints,
  `pico_lr_config_covered_steps_preserve_cache_history`,
  `pico_lr_config_state_covered_steps_update`,
  `pico_lr_config_state_covered_steps_read_valid`,
  `pico_lr_config_state_alloc_covered_steps_read_valid`,
  `pico_lr_wp_state_bridge_after_covered_steps`, and
  `pico_lr_wp_state_bridge_after_covered_steps_read_valid`, plus the
  allocation-to-final-read endpoint
  `pico_lr_wp_state_bridge_alloc_covered_steps_read_valid`, connecting the
  unified closure interface to the ghost-backed state facade and WP-state
  bridge;
- post-entry state and WP-bridge final-read endpoints,
  `pico_lr_config_state_thread_post_steps_read_valid`,
  `pico_lr_config_state_alloc_thread_post_steps_read_valid`,
  `pico_lr_wp_state_bridge_after_thread_post_steps_read_valid`, and
  `pico_lr_wp_state_bridge_alloc_thread_post_steps_read_valid`, connecting the
  simpler post-thread-entry closure interface to the same ghost-backed state
  facade and WP-state bridge;
- field-write LR transport,
  `pico_lr_fldwrite_step_env_preserved` and
  `pico_lr_fldwrite_state_env_step_update`, combining weak-write environment
  preservation with the ghost-backed cache-state transport for the concrete
  `SFldWrite` step shape;
- LR-facing rule constructors,
  `pico_lr_skipI`, `pico_lr_localI`, `pico_lr_varassI`,
  `pico_lr_fldwrite_otherI`, `pico_lr_fldwrite_target_knownI`,
  `pico_lr_newI`, `pico_lr_callI`, and `pico_lr_seqI`, plus
  `pico_lr_thread_intro` and `pico_lr_config_intro`, so clients can build the
  current logical relation without depending on temporary semantic-typing
  constructor names;
- explicit LR interpretation predicates,
  `pico_lr_expr_interp`, `pico_lr_thread_step_env_interp`,
  `pico_lr_stmt_interp`, `pico_lr_thread_interp`,
  `pico_lr_method_body_interp`, and `pico_lr_config_entries`, with bridge
  lemmas to and from the existing expression, thread-step, statement, thread,
  method, and config Iris propositions where sound, value/environment
  elimination lemmas, and explicit config-entry/config-interpretation
  equivalence lemmas, giving later type-indexed/ghost-backed refinements a
  named replacement point;
- LR-named config safety endpoints,
  `pico_lr_config_entries_cache_safe_config`,
  `pico_lr_config_interp_cache_safe_config`,
  `pico_lr_configI_cache_safe_config`,
  `pico_lr_config_interp_semantic_cache_safe`,
  `pico_lr_config_interp_semantic_cache_safeI`, and
  `pico_lr_config_interp_semantic_executionI`, plus final-read wrappers
  `pico_lr_config_interp_final_read_valid`,
  `pico_lr_config_interp_final_read_validI`, and
  `pico_lr_config_interp_semantic_execution_read_validI`, routing config
  interpretation through weak-memory cache-history preservation and read
  validity without exposing the temporary semantic-typing predicate names;
- a named prefix-interpretation proposition,
  `pico_lr_config_prefix_interpI`, with intro/elim, semantic-preservation,
  semantic-execution, and final-read wrappers, so global execution assumptions
  can be passed at an LR-facing Iris boundary instead of as raw higher-order
  `Prop` arguments;
- an execution-scoped prefix-interpretation proposition,
  `pico_lr_config_execution_prefix_interpI`, with preservation and final-read
  wrappers proved by induction over a concrete `wm_steps` derivation, avoiding
  a global all-configurations assumption when an execution-local prefix is
  enough; adapters derive this scoped evidence from either the global
  `pico_lr_config_prefix_interpI` proposition or from an initial
  `pico_lr_configI` plus `pico_lr_config_step_closureI`;
- execution-prefix resource endpoints for `pico_cache_state_interp` and
  `pico_wp_state_cfg_bridge`, transporting those resources and deriving final
  read validity from `pico_lr_config_execution_prefix_interpI`, plus
  allocation-to-final-read variants for callers that start from a pure initial
  cache-history fact;
- execution-prefix cache-history invariant endpoints,
  `pico_lr_config_inv_execution_prefix_steps_update` and
  `pico_lr_config_inv_execution_prefix_steps_read_valid`, transporting the raw
  invariant and deriving final read validity from the same per-run prefix
  proposition, plus an allocation-to-final-read variant from a pure initial
  cache-history fact;
- a bundled execution-prefix read spec,
  `pico_lr_config_execution_prefix_read_specI`, packaging the concrete
  execution, initial cache-history fact, final weak read, and per-run prefix
  interpretation, with final-read and invariant/state/WP allocation endpoints
  that consume the bundle directly; constructors build the bundle either from
  global prefix evidence, from initial `pico_lr_configI` plus closure evidence,
  from covered-step evidence, or from post-thread-entry evidence; direct
  invariant/state/WP allocation-to-read endpoints also consume the covered-step
  and post-thread-entry evidence forms;
- LR-facing method constructors,
  `pico_lr_method_body_intro`, `pico_lr_method_thread_intro`, and
  `pico_lr_method_thread_entry`, connecting method-body typing plus
  `cache_safe_method_body` to the LR thread/config-entry layer;
- LR-facing derived-cache update bridges,
  `pico_lr_cache_update_sequenceI`,
  `pico_lr_cache_update_sequence_intro`,
  `pico_lr_cache_update_sequence_tail_threadI`,
  `pico_lr_cache_update_tail_threadI`,
  `pico_lr_cache_update_tail_thread_entry`,
  `pico_lr_cache_update_step_to_tailI`,
  `pico_lr_cache_update_config_step_to_tailI`, and
  `pico_lr_sem_cache_update_step_to_tailI`,
  `pico_lr_sem_cache_update_config_step_to_tailI`,
  `wp_pico_lr_cache_update_sequence_with_tail`, plus
  `wp_pico_lr_sem_cache_update_sequence_with_tail`, exposing the literal
  `tmp = EInt n; receiver.cache = tmp` update sequence through the
  logical-relation facade either from the pure safety record or from its named
  semantic/LR interpretation;
- an embedded thread-pool first-step bridge,
  `pico_lr_cache_update_embedded_config_step_to_tailI`,
  `pico_lr_cache_update_embedded_config_state_step_to_tail`,
  `pico_lr_cache_update_embedded_config_wp_bridge_step_to_tail`,
  `pico_lr_cache_update_embedded_config_inv_step_to_tail`,
  `pico_lr_cache_update_embedded_config_state_step_to_tailI`, and
  `pico_lr_cache_update_embedded_config_wp_bridge_step_to_tailI`, plus the
  invariant existential package
  `pico_lr_cache_update_embedded_config_inv_step_to_tailI`, which package the
  first cache-update step, cache-history preservation, the LR interpretation
  of the updated tail configuration, and invariant/state/WP bridge transport
  for arbitrary thread pools;
- semantic/LR embedded first-step bridge variants,
  `pico_lr_sem_cache_update_embedded_config_step_to_tailI`,
  `pico_lr_sem_cache_update_embedded_config_state_step_to_tail`,
  `pico_lr_sem_cache_update_embedded_config_wp_bridge_step_to_tail`,
  `pico_lr_sem_cache_update_embedded_config_inv_step_to_tail`,
  `pico_lr_sem_cache_update_embedded_config_state_step_to_tailI`, and
  `pico_lr_sem_cache_update_embedded_config_wp_bridge_step_to_tailI`, plus
  `pico_lr_sem_cache_update_embedded_config_inv_step_to_tailI`, which consume
  `pico_lr_cache_update_sequenceI` at the arbitrary thread-pool
  first-step boundary;
- LR-facing selected-first execution/read endpoints,
  `pico_lr_cache_update_selected_first_steps`,
  `pico_lr_cache_update_selected_first_execution_safeI`, and
  `pico_lr_cache_update_selected_first_final_read_validI`, exposing the
  selected-first derived-cache execution path through the logical-relation
  facade;
- closure-based selected-first execution/read endpoints,
  `pico_lr_cache_update_selected_first_closure_execution_safeI`,
  `pico_lr_cache_update_selected_first_closure_final_read_validI`,
  `pico_lr_cache_update_selected_first_state_closure_read_valid`,
  `pico_lr_cache_update_selected_first_wp_bridge_closure_read_valid`,
  `pico_lr_cache_update_selected_first_inv_closure_read_valid`,
  `pico_lr_cache_update_selected_first_inv_closure_update`,
  `pico_lr_cache_update_selected_first_inv_alloc_closure_read_valid`,
  `pico_lr_cache_update_selected_first_inv_alloc_closure_update`,
  `pico_lr_cache_update_selected_first_state_alloc_closure_read_valid`, and
  `pico_lr_cache_update_selected_first_wp_bridge_alloc_closure_read_valid`,
  routing the literal cache-update execution through the named closure
  contract and then into existing or freshly allocated invariant/state facade
  / WP-state bridge resources, including final-invariant transport;
- semantic/LR selected-first closure endpoints,
  `pico_lr_sem_cache_update_selected_first_closure_execution_safeI`,
  `pico_lr_sem_cache_update_selected_first_closure_final_read_validI`,
  `pico_lr_sem_cache_update_selected_first_state_closure_read_valid`, and
  `pico_lr_sem_cache_update_selected_first_wp_bridge_closure_read_valid`,
  plus `pico_lr_sem_cache_update_selected_first_inv_closure_read_valid` and
  `pico_lr_sem_cache_update_selected_first_inv_closure_update`,
  which consume `pico_lr_cache_update_sequenceI` instead of exposing the raw
  literal-update safety record at the selected-first execution boundary;
- short execution-facade invariant endpoints,
  `pico_lr_cache_update_execution_inv_read_valid`,
  `pico_lr_cache_update_execution_inv_after_execution`,
  `pico_lr_cache_update_execution_inv_alloc_read_valid`, and
  `pico_lr_cache_update_execution_inv_alloc_after_execution`, plus closedI,
  coveredI, thread_postI, selectedI, and evidenceI variants, so callers can
  transport/read from cache-history invariants without depending on internal
  selected-first names; the `pico_lr_cache_update_execution_specI_*` and
  `pico_lr_cache_update_execution_from_safe_*` layers also expose direct
  existing-invariant read endpoints and existing-invariant transport/read
  endpoints alongside allocation-based final-resource and final-resource/read
  endpoints;
- direct generic compute/write tail closure endpoints,
  `pico_lr_cache_compute_then_write_phases_tail_inv_closure_read_valid_generic`,
  `pico_lr_cache_compute_then_write_phases_tail_state_closure_read_valid_generic`,
  and
  `pico_lr_cache_compute_then_write_phases_tail_wp_bridge_closure_read_valid_generic`,
  so clients can stay at `cache_valid` without waiting for allocation/read-spec
  wrappers;
- closure-based tail-pool endpoints,
  `pico_lr_cache_update_tail_pool_interp`,
  `pico_lr_cache_update_tail_pool_closure_final_read_validI`,
  `pico_lr_cache_update_tail_pool_inv_closure_read_valid`,
  `pico_lr_cache_update_tail_pool_inv_closure_update`,
  `pico_lr_cache_update_tail_pool_state_closure_read_valid`,
  `pico_lr_cache_update_tail_pool_wp_bridge_closure_read_valid`,
  `pico_lr_cache_update_tail_pool_inv_alloc_closure_read_valid`,
  `pico_lr_cache_update_tail_pool_inv_alloc_closure_update`,
  `pico_lr_cache_update_tail_pool_state_alloc_closure_read_valid`, and
  `pico_lr_cache_update_tail_pool_wp_bridge_alloc_closure_read_valid`,
  exposing the reusable post-first-step tail execution through the same named
  closure and into existing or freshly allocated invariant/state facade /
  WP-state bridge resources, including final-invariant transport, with
  `..._generic` read-validity variants for the generic cache protocol;
- semantic/LR tail-pool endpoints,
  `pico_lr_sem_cache_update_tail_pool_closure_final_read_validI`,
  `pico_lr_sem_cache_update_tail_pool_inv_closure_read_valid`,
  `pico_lr_sem_cache_update_tail_pool_inv_closure_update`,
  `pico_lr_sem_cache_update_tail_pool_state_closure_read_valid`,
  `pico_lr_sem_cache_update_tail_pool_wp_bridge_closure_read_valid`,
  `pico_lr_sem_cache_update_tail_pool_inv_alloc_closure_read_valid`,
  `pico_lr_sem_cache_update_tail_pool_inv_alloc_closure_update`,
  `pico_lr_sem_cache_update_tail_pool_state_alloc_closure_read_valid`, and
  `pico_lr_sem_cache_update_tail_pool_wp_bridge_alloc_closure_read_valid`,
  which carry the named cache-update interpretation through the reusable
  post-first-step tail execution phase, with matching generic variants,
  including combined `pico_lr_configI` wrappers, that conclude `cache_valid`;
- an invariant-backed selected-first LR read endpoint,
  `pico_lr_cache_update_selected_first_inv_final_read_validI`, deriving final
  weak-read validity from a starting `pico_cache_history_inv` rather than a
  raw pure cache-history premise, plus
  `pico_lr_sem_cache_update_selected_first_inv_final_read_validI`, which
  consumes the named cache-update interpretation;
- LR-facing endpoint wrappers,
  `pico_lr_thread_cache_safeI`, `pico_lr_threadI_entry`,
  `pico_lr_configI_interp`,
  `pico_lr_configI_closure_steps_read_validI`,
  `pico_lr_configI_state_closure_steps_update`,
  `pico_lr_configI_state_closure_steps_read_valid`,
  `pico_lr_configI_wp_state_bridge_after_closure_steps`,
  `pico_lr_configI_wp_state_bridge_after_closure_steps_read_valid`,
  `pico_lr_configI_wp_state_bridge_alloc_closure_steps_read_valid`,
  generic/closed/closure allocation-to-unknown-or-derived wrappers for the
  state facade and WP-state bridge, plus configI-consuming closure variants
  `pico_lr_configI_state_alloc_closure_steps_read_unknown_or_derived` and
  `pico_lr_configI_wp_state_bridge_alloc_closure_steps_read_unknown_or_derived`,
  literal cache-update selected-first and execution-level state/WP allocation
  read-shape wrappers
  `pico_lr_cache_update_selected_first_configI_state_alloc_closure_read_unknown_or_derived`,
  `pico_lr_cache_update_selected_first_configI_wp_bridge_alloc_closure_read_unknown_or_derived`,
  `pico_lr_cache_update_execution_state_alloc_read_unknown_or_derived`, and
  `pico_lr_cache_update_execution_wp_bridge_alloc_read_unknown_or_derived`,
  with matching `closedI`, `evidenceI`, and `specI` state/WP allocation
  package wrappers, plus `specI` after-execution variants that return the
  transported final state/WP bridge resource with the unknown-or-derived read
  fact and `from_safe` closure/thread-post/covered-step forwards,
  `pico_lr_thread_wp_step`,
  `pico_lr_thread_wp_step_exists`,
  `wp_pico_lr_cache_update_sequence_with_tail_exists`,
  `wp_pico_lr_sem_cache_update_sequence_with_tail_exists`,
  `wp_pico_lr_cache_compute_then_write_tail_step_exists`,
  `pico_lr_config_semantic_executionI`,
  `pico_lr_config_allowed_steps_read_validI`,
  `pico_lr_config_inv_steps_update`, and
  `pico_lr_config_inv_steps_read_valid`, which are intended to keep their shape
  when the implementation behind the facade moves from pure facts to ghost
  state; the LR thread-step state and WP-state bridge updates now route through
  `pico_lr_thread_cache_safeI` rather than unfolding `pico_lr_threadI`
  directly;
- LR-facing state-interpretation wrappers,
  `pico_lr_thread_state_step_update`,
  `pico_lr_thread_wp_state_bridge_step_update`,
  `pico_lr_configI_nth_state_step_update`,
  `pico_lr_configI_nth_wp_state_bridge_step_update`,
  `pico_lr_configI_nth_state_env_step_update_package`,
  `pico_lr_configI_nth_wp_state_bridge_env_step_update_package`,
  `pico_lr_configI_nth_state_env_step_update_from_interp_package`,
  `pico_lr_configI_nth_wp_state_bridge_env_step_update_from_interp_package`,
  `pico_lr_thread_step_env_package_from_interp`,
  `pico_lr_configI_nth_state_env_step_update_from_interp_package_via_step_env`,
  `pico_lr_configI_nth_wp_state_bridge_env_step_update_from_interp_package_via_step_env`,
  `pico_lr_wp_state_bridge_after_allowed_write_threads`,
  `pico_lr_wp_state_bridge_after_allowed_write`,
  `pico_lr_wp_state_bridge_after_allowed_write_threads_read_valid_generic`,
  `pico_lr_wp_state_bridge_after_allowed_write_read_valid_generic`,
  `pico_lr_fldwrite_wp_state_bridge_step_update`,
  `pico_lr_wp_state_bridge_target_history_valid`,
  `pico_lr_wp_state_bridge_read_valid`,
  `pico_lr_config_state_steps_update`,
  `pico_lr_config_state_after_target_write`,
  `pico_lr_config_state_after_other_write`,
  `pico_lr_config_state_after_allowed_write_threads`,
  `pico_lr_config_state_after_allowed_write`,
  `pico_lr_config_state_after_allowed_write_threads_read_valid_generic`,
  `pico_lr_config_state_after_allowed_write_read_valid_generic`,
  `pico_lr_fldwrite_state_step_update`,
  `pico_lr_config_state_weak_state_snapshot`,
  `pico_lr_config_state_field_history_snapshot`,
  `pico_lr_config_state_field_history_snapshot_valid`,
  `pico_lr_config_state_field_history_read_valid`,
  `pico_lr_config_state_target_history_valid`, and
  `pico_lr_config_state_steps_read_valid`, lifting primitive thread-step
  transport, WP-state bridge transport/read validity, config execution
  transport, target/non-target/allowed write transport, concrete field-write
  step transport, weak-state snapshot extraction, field-history validity/read
  extraction, target-history validity extraction, and final weak-read validity
  to the ghost-backed `pico_cache_state_interp` facade;
- a direct semantic-config weak-memory interpretation theorem,
  `sem_typed_config_entry_interpretation_semantic_cache_safe`, showing that
  configs whose threads satisfy `sem_typed_thread_entry` are an allowed
  path-local interpretation for `wm_semantic_cache_safe_under`;
- an adequacy-shaped pure endpoint,
  `sem_typed_config_entry_interpretation_cache_safe_execution`, packaging that
  interpretation as `wm_semantic_cache_safe_execution` while still avoiding any
  claim of full Iris adequacy;
- a read-side endpoint,
  `sem_typed_config_entry_interpretation_final_read_valid`, composing semantic
  config execution preservation with cache read-validity so final weak reads
  from the cache field observe only derived-cache-valid values;
- a named Iris execution boundary,
  `wm_semantic_cache_safe_executionI`, with
  `wm_config_cache_history_state_read_unknown_or_derivedI`,
  `wm_semantic_cache_safe_execution_read_validI`,
  `wm_semantic_cache_safe_execution_read_unknown_or_derivedI`,
  `wm_steps_read_unknown_or_derived_from_allowed_writesI`,
  `wm_steps_read_unknown_or_derived_from_config_allowedI`, and
  `cache_safe_config_semantic_cache_safe_executionI`, so later ghost-state
  work can refine a stable Iris proposition instead of changing the pure
  theorem boundary;
- a typed semantic execution wrapper,
  `sem_typed_config_entry_interpretation_semantic_executionI`, plus
  `sem_typed_config_entry_interpretation_semantic_execution_read_validI`,
  deriving the named Iris execution/read-validity endpoint from the
  config-level semantic typing interpretation;
- a literal-update tail-pool endpoint,
  `cache_update_sequence_safe_tail_pool_cache_safe_execution`, specializing the
  adequacy-shaped semantic-config endpoint to the pool obtained after replacing
  the selected full update thread with its semantically typed cache-write tail;
- a phased residual bridge,
  `cache_update_sequence_safe_step_to_sem_typed_tailI`, showing that the
  literal `tmp = EInt n; receiver.cache = tmp` update sequence takes one
  weak-memory thread step to the semantically typed cache-write tail;
- a specialized WP bridge,
  `wp_pico_lift_cache_update_sequence_to_sem_typed_tail`, proving WP for that
  whole literal cache-update sequence by reducing to WP of the semantically
  typed tail;
- a packaged semantic WP bridge,
  `wp_pico_lift_cache_update_sequence_with_sem_typed_tail`, which passes the
  semantically typed tail proposition directly to the client continuation;
- a named semantic cache-update interpretation,
  `pico_sem_cache_update_sequenceI`, with constructor
  `pico_sem_cache_update_sequence_intro`, tail interpretation
  `pico_sem_cache_update_sequence_tail_threadI`, and WP endpoint
  `wp_pico_lift_sem_cache_update_sequence_with_tail`, so callers can consume a
  stable Iris proposition rather than the raw literal-update safety record;
- existential-step WP wrappers for the literal update first-step boundary,
  `wp_pico_lift_cache_update_sequence_to_sem_typed_tail_exists`,
  `wp_pico_lift_cache_update_sequence_with_sem_typed_tail_exists`, and
  `wp_pico_lift_sem_cache_update_sequence_with_tail_exists`, routing the
  selected assignment step through a concrete `wm_thread_step` witness instead
  of constructing Iris `reducible` evidence directly;
- semantic full-cache-update progress wrappers,
  `wp_pico_sem_cache_update_tail_fldwrite_step_progress` and
  `wp_pico_lift_sem_cache_update_sequence_full_progress`, which combine the
  selected-assignment first step with the state-dependent tail field-write
  witness while staying at the semantic interpretation layer;
- concrete progress facts for that first-step boundary,
  `cache_update_sequence_safe_first_step_exists`,
  `cache_update_sequence_safe_first_step_not_stuck`,
  `pico_sem_cache_update_sequence_first_step_existsI`, and
  `pico_sem_cache_update_sequence_not_stuckI`, plus LR-facing wrappers
  `pico_lr_cache_update_sequence_first_step_existsI` and
  `pico_lr_cache_update_sequence_not_stuckI`;
- named semantic cache-update execution/read wrappers,
  `pico_sem_cache_update_sequence_tail_pool_cache_safe_executionI`,
  `pico_sem_cache_update_sequence_selected_first_execution_safeI`, and
  `pico_sem_cache_update_sequence_selected_first_final_read_validI`, carrying
  that stable proposition through the semantic tail-pool and selected-first
  execution boundaries;
- selected-first LR cache-update wrappers consuming `pico_lr_configI`,
  including `pico_lr_cache_update_selected_first_configI_closure_execution_safeI`,
  `pico_lr_cache_update_selected_first_configI_closure_final_read_validI`,
  `pico_lr_cache_update_selected_first_configI_state_closure_read_valid`,
  `pico_lr_cache_update_selected_first_configI_wp_bridge_closure_read_valid`,
  `pico_lr_cache_update_selected_first_configI_state_alloc_closure_read_valid`,
  and
  `pico_lr_cache_update_selected_first_configI_wp_bridge_alloc_closure_read_valid`,
  so the selected-first path no longer has to expose the pure
  `pico_lr_config_interp` premise at the caller boundary;
- combined selected-first semantic/LR wrappers,
  `pico_lr_sem_cache_update_selected_first_configI_closure_execution_safeI`,
  `pico_lr_sem_cache_update_selected_first_configI_closure_final_read_validI`,
  `pico_lr_sem_cache_update_selected_first_configI_state_closure_read_valid`,
  `pico_lr_sem_cache_update_selected_first_configI_wp_bridge_closure_read_valid`,
  `pico_lr_sem_cache_update_selected_first_configI_state_alloc_closure_read_valid`,
  and
  `pico_lr_sem_cache_update_selected_first_configI_wp_bridge_alloc_closure_read_valid`,
  consuming both `pico_lr_cache_update_sequenceI` and `pico_lr_configI`;
- stable end-to-end cache-update facade names,
  `pico_lr_cache_update_execution_safeI`,
  `pico_lr_cache_update_execution_final_read_validI`,
  `pico_lr_cache_update_execution_state_read_valid`,
  `pico_lr_cache_update_execution_wp_bridge_read_valid`,
  `pico_lr_cache_update_execution_state_alloc_read_valid`, and
  `pico_lr_cache_update_execution_wp_bridge_alloc_read_valid`, delegating to
  the selected-first combined wrappers while exposing a single execution-level
  API;
- a named selected-first execution proposition,
  `pico_lr_cache_update_selected_first_executionI`, with intro/extraction
  lemmas and `pico_lr_cache_update_execution_selectedI_*` facade variants, so
  the execution evidence itself can be passed as an Iris proposition;
- a named closure proposition, `pico_lr_config_step_closureI`, with
  introduction/extraction lemmas and `pico_lr_cache_update_execution_closedI_*`
  facade variants, so the execution API can consume closure evidence as an
  Iris proposition rather than a raw function premise;
- a named covered-step evidence proposition, `pico_lr_covered_stepsI`, with
  intro/extraction lemmas, a bridge
  `pico_lr_config_step_closureI_from_coveredI`, and
  `pico_lr_cache_update_execution_coveredI_*` facade variants, so supported
  weak-step preservation evidence also stays in the named Iris layer;
- a named post-thread-entry evidence proposition,
  `pico_lr_thread_post_stepsI`, with intro/extraction lemmas, a bridge
  `pico_lr_config_step_closureI_from_thread_postI`, and
  `pico_lr_cache_update_execution_thread_postI_*` facade variants, giving the
  alternate closure-construction path the same named-Iris boundary;
- a bundled selected-execution plus closure evidence proposition,
  `pico_lr_cache_update_execution_evidenceI`, with constructors from selected
  execution plus closure, covered-step evidence, and post-thread-entry
  evidence, and `pico_lr_cache_update_execution_evidenceI_*` facade variants
  for safe execution, final-read validity, state-facade transport, WP-state
  bridge transport, and invariant/state/WP allocation-to-read endpoints;
- a caller-facing cache-update execution spec proposition,
  `pico_lr_cache_update_execution_specI`, bundling the LR cache-update
  interpretation, initial config interpretation, initial cache-history state,
  selected thread-slot fact, and execution evidence, with
  constructors from explicit closure, covered-step evidence, and
  post-thread-entry evidence, plus
  `pico_lr_cache_update_execution_specI_from_safe_*` constructors that build
  the spec from the raw cache-update safety record, selected-first execution
  fact, initial history state, and the chosen closure-evidence path, and
  invariant allocation-to-read, spec-preserving invariant transport, and
  spec-preserving allocation lemmas for the ghost-backed state facade and
  WP-state bridge, plus spec-preserving transport lemmas that move those
  resources to the final configuration, with generic `cache_valid` variants
  for final reads, existing-resource reads, allocation-to-read paths,
  final-resource/read endpoints, and from-safe closure/thread-post/covered-step
  constructors;
  resources to the selected execution's final configuration, including
  direct allocation-to-final-resource endpoints and combined
  final-resource/read-validity endpoints for the invariant, state facade, and
  WP-state bridge, with `from_safe_*` variants for explicit closure,
  covered-step evidence, and post-thread-entry evidence,
  `pico_lr_cache_update_execution_specI_*` facade variants for the same
  safe-execution and final-read endpoints, and generic read-validity variants
  for the direct `closedI`, `coveredI`, and `thread_postI` facade paths;
- semantic selected-first generic wrappers covering closure/configI final-read,
  existing invariant/state/WP-resource reads, and allocation-to-read paths;
- combined tail-pool semantic/LR wrappers,
  `pico_lr_sem_cache_update_tail_pool_configI_closure_final_read_validI`,
  `pico_lr_sem_cache_update_tail_pool_configI_inv_closure_read_valid`,
  `pico_lr_sem_cache_update_tail_pool_configI_inv_closure_update`,
  `pico_lr_sem_cache_update_tail_pool_configI_state_closure_read_valid`,
  `pico_lr_sem_cache_update_tail_pool_configI_wp_bridge_closure_read_valid`,
  `pico_lr_sem_cache_update_tail_pool_configI_inv_alloc_closure_read_valid`,
  `pico_lr_sem_cache_update_tail_pool_configI_inv_alloc_closure_update`,
  `pico_lr_sem_cache_update_tail_pool_configI_state_alloc_closure_read_valid`,
  and
  `pico_lr_sem_cache_update_tail_pool_configI_wp_bridge_alloc_closure_read_valid`,
  carrying the same named cache-update/config interpretation boundary through
  the post-first-step tail execution phase;
- combined selected-first semantic/LR invariant wrappers,
  `pico_lr_sem_cache_update_selected_first_configI_inv_closure_read_valid`,
  `pico_lr_sem_cache_update_selected_first_configI_inv_closure_update`,
  `pico_lr_sem_cache_update_selected_first_configI_inv_alloc_closure_read_valid`,
  and `pico_lr_sem_cache_update_selected_first_configI_inv_alloc_closure_update`,
  carrying the named cache-update/config interpretation boundary through the
  selected-first execution phase for existing and freshly allocated
  cache-history invariants;
- a singleton-configuration weak-memory bridge,
  `cache_update_sequence_safe_config_step_to_sem_typed_tailI`, showing that a
  configuration containing the literal update sequence steps to a configuration
  whose cache-write tail satisfies `pico_sem_typed_config_cacheI`, while the
  cache-history state is unchanged by that first assignment step;
- an embedded-thread config bridge,
  `cache_update_sequence_safe_embedded_config_step_to_sem_typed_tailI`, lifting
  the same result to an interleaving-style thread pool where the selected slot
  contains the full literal cache-update sequence and the updated tail pool
  satisfies the semantic config interpretation;
- combined embedded first-step LR wrappers,
  `pico_lr_sem_cache_update_embedded_config_configI_step_to_tailI`,
  `pico_lr_sem_cache_update_embedded_config_configI_inv_step_to_tail`,
  `pico_lr_sem_cache_update_embedded_config_configI_state_step_to_tail`,
  `pico_lr_sem_cache_update_embedded_config_configI_wp_bridge_step_to_tail`,
  `pico_lr_sem_cache_update_embedded_config_configI_inv_step_to_tailI`,
  `pico_lr_sem_cache_update_embedded_config_configI_state_step_to_tailI`, and
  `pico_lr_sem_cache_update_embedded_config_configI_wp_bridge_step_to_tailI`,
  consuming both `pico_lr_cache_update_sequenceI` and `pico_lr_configI` while
  packaging the transition from the full literal update thread to the typed
  cache-write tail pool;
- a composed post-first-step execution theorem,
  `cache_update_sequence_safe_embedded_config_tail_execution_safeI`, which uses
  semantic config typing after the selected assignment step to preserve the
  cache-history invariant for later weak-memory executions;
- a full embedded execution theorem,
  `cache_update_sequence_safe_embedded_config_execution_safeI`, which packages
  the selected first assignment step with the later tail execution and returns
  both the composed `wm_steps` evidence from the original thread pool and the
  final cache-history invariant;
- a named selected-first execution shape,
  `cache_update_sequence_selected_first_execution`, and wrapper theorem
  `cache_update_sequence_safe_selected_first_execution_safeI`, making explicit
  that this phased bridge covers executions whose first step is the selected
  literal update thread;
- a selected-first read-safety theorem,
  `cache_update_sequence_safe_selected_first_final_read_validI`, showing that
  final weak reads from the cache field are derived-cache-valid after such
  selected-first executions;
- bridge theorem entry points collecting the sequential PICO, SC PICO,
  weak-observation PICO, and Iris/`heap_lang` results.

This follows the intended Level 1 architecture: do not rewrite PICO in Iris;
instead, import PICO facts as pure facts `⌜ ... ⌝` where useful.
The new PICO Iris language shell and semantic typing wrapper are still staging
layers: they support WP-facing cache-safety reasoning, including
`wp_pico_lift_thread_step_exists` for lifting existential weak-step witnesses
into Iris WP, but they are not yet a full weakest-precondition development or
logical relation for all PICO types.

## Beyond Level 1: PICO-Side Concurrency Models

Main files:

- [PICOBridge/PicoMemoryModel.v](PICOBridge/PicoMemoryModel.v)
- [PICOBridge/PicoCacheTyping.v](PICOBridge/PicoCacheTyping.v)
- [PICOBridge/ConcurrentPico.v](PICOBridge/ConcurrentPico.v)
- [Examples/ConcurrentPicoExamples.v](Examples/ConcurrentPicoExamples.v)
- [PICOBridge/WeakPico.v](PICOBridge/WeakPico.v)
- [Examples/WeakPicoExamples.v](Examples/WeakPicoExamples.v)

What they contain:

- a field-addressed memory/history interface and small-step shell for future
  weak-memory semantics;
- read-validity lemmas such as `wm_config_cache_history_state_read_valid`,
  `wm_cache_history_state_read_unknown_or_derived`, and
  `wm_config_cache_history_state_read_unknown_or_derived`, proving that reads
  from a valid cache history observe only unknown or derived cache values;
- a first typing-shaped bridge from the concrete derived-cache update sequence
  to the semantic cache-safety layer;
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

- a full Iris weakest-precondition or adequacy development for PICO;
- a full Iris semantic interpretation of PICO types;
- a Java weak-memory or iRC11 model;
- that `PICOBridge/WeakPico.v` is a complete weak-memory semantics.

`PICOBridge/WeakPico.v` is an explicit observation/coherence model: a weak cache write is
accepted only when the observed final-field snapshot is coherent with the heap
at commit time.

## Claim Boundary and JMM Examples

The current weak-memory claim should be stated as memory-model-parametric, not
as full Java Memory Model soundness.  A defensible paper-level claim is:

```text
We model semantic immutability for derived caches using a field-history
weak-memory abstraction.  The model is parameterized by a memory-model
interface requiring reads to come from field histories.  Under cache-safe
typing/semantic conditions, every weak read from the cache field observes
either unknown/uninitialized cache state or a valid derived cache value.
```

The artifact should not yet claim:

```text
This proves semantic immutability under the Java Memory Model.
```

or:

```text
This models all JMM executions of Java programs.
```

The current `CacheMemoryModel` interface assumes the reads-from-history fact
needed by the cache-history proof, but it does not model the full set of Java
memory-model machinery:

- happens-before;
- synchronization order;
- volatile access semantics;
- final-field initialization/freeze semantics;
- general data-race behavior;
- causality and out-of-thin-air restrictions;
- initialization safety for escaping objects;
- compiler and hardware reorderings allowed for ordinary Java fields.

For paper wording, use "JMM-inspired" or "weak-memory-parametric" semantic
immutability unless a later artifact actually instantiates the interface with a
full JMM model:

```text
Our weak-memory layer is parametric in a memory model.  The current artifact
assumes a reads-from-history interface sufficient to state and prove
cache-history safety.  Instantiating this interface with the full Java Memory
Model, including final-field and synchronization semantics, is future work.
```

The intended benign-race example is a String-like derived cache:

```java
int h = hash;
if (h == 0) {
  h = computeFromFinalFields();
  hash = h;
}
return h;
```

The cache field `hash` may be plain and racy.  The race is benign only because
every permitted nonzero write to `hash` stores the same deterministic value
derived from stable abstract state.  A weak read may see the default/unknown
cache value or the derived value, but not an arbitrary value:

```text
Thread 1: hash = H
Thread 2: hash = H
Thread 3: read hash observes 0 or H
```

The theorem shape should therefore be "racy cache reads are semantically
valid," not "there is no data race."  The history model abstracts compiler and
hardware reordering through the set of writes that reads may observe.  This is
enough for the current benign-race proof once all writes to the cache field are
classified as valid.

Examples that should be rejected or left outside the current claim include:

```java
hash = partialResult;
hash = finalResult;
```

because a racy reader may observe `partialResult`, and:

```java
hash = h;
h = computeFromFinalFields();
```

because the cache write is not justified by a completed derived computation in
the source-level proof shape.  More generally, arbitrary races on abstract
state fields or writes of non-derived values to the cache field are not benign
under the current semantic invariant.

If reviewers expect a Java-level theorem, the next modular target is:

```text
Any memory model satisfying CacheMemoryModel plus the cache-write coherence
obligations enjoys semantic cache safety.
```

That statement makes the current proof reusable while isolating exactly what a
future JMM instantiation must provide.

## Future Levels

Stage 1 is to grow [PICOBridge/PicoMemoryModel.v](PICOBridge/PicoMemoryModel.v) into a small-step
field-addressed semantics while keeping the existing big-step PICO semantics
unchanged.  The first semantic target is a history invariant: every value a
weak read may observe from a cache field is either the unknown value or a value
derived from the fixed abstract state.  The current preservation theorem is
already phrased in terms of classified writes: a step preserves the target cache
history when each actual write is either to another field or appends a valid
derived cache value.  The newest layer derives that classified-write premise
from a statement/thread/configuration write discipline, moving the proof
boundary closer to a future typing rule for cache-safe methods.

The intended Iris-style structure is:

```text
typing / cache-safe method rule
  -> semantic interpretation of well-behaved cache code
  -> preservation of field-addressed cache histories
  -> safe weak-memory execution
```

The current branch has a pure Rocq version of the middle of that stack:
`cache_safe_method_body`, `cache_safe_stmt`, `cache_safe_config`,
`cache_safe_config_semantic_cache_safe`, and
`wm_semantic_cache_safe_execution`.  What remains is the true Iris/logical
relation layer: interpreting PICO typing judgments as Iris propositions and
showing the typing rules imply `cache_safe_method_body` or its eventual Iris
counterpart.  Helper lemmas such as `cache_safe_fldwrite_other` and
`cache_safe_fldwrite_target_known` make the two intended write cases explicit:
writes to non-cache fields are harmless, and writes to the target cache field
must store the nonzero derived value.  The helper
`cache_safe_fldwrite_target_after_assign_int` handles the common sequential
shape where a temporary is first assigned the derived integer and then written
to the cache field under the updated runtime environment.
[PICOBridge/PicoCacheTyping.v](PICOBridge/PicoCacheTyping.v) packages that shape in two layers:
`verified_cache_compute` covers any typed computation that leaves the nonzero
derived value in a temporary, while `cache_compute_write_safe` adds the typed
cache-field write.  The phased `cache_compute_then_write_safe` judgment records
the compute statement under the pre-compute environment and the cache write
under the post-compute environment.  The theorem
`cache_compute_then_write_safe_implies_cache_safe_phases` exposes those two
safe phases explicitly, while
`cache_compute_then_write_safe_implies_cache_safe_stmt_same_env` gives the
ordinary `SSeq` statement theorem only in the honest same-runtime-environment
case.  The same bridge now also connects to the generic trace theorem:
`pico_cache_compute_refines_pure` proves the derived-cache recomputation runner
refines pure recomputation, `verified_cache_compute_refines_pure_via_generic`
uses typed compute evidence to recover `PureRecomputeResult`, and
`cache_compute_write_safe_refines_pure_via_generic` lifts that fact through the
typed cache-write package.  `cache_compute_write_safe_tail_threads_imply_cache_safe_config`
lifts lists of post-compute cache-write threads to `cache_safe_config`.  The
older literal `tmp = EInt n` shape is captured by `cache_update_sequence_safe`
and proved to be an instance of both the general compute-then-write bridge and
generic pure-refinement bridge, including
`cache_update_sequence_safe_implies_cache_safe_phases` and
`cache_update_sequence_safe_refines_pure_via_generic`.  `PICOBridge/PicoIrisSemanticTyping.v`
also exposes matching pure-Iris endpoints, including
`pico_sem_cache_compute_refines_pure_introI`,
`verified_cache_compute_refines_pure_via_genericI`,
`cache_compute_write_safe_refines_pure_via_genericI`, and
`cache_update_sequence_safe_refines_pure_via_genericI`.
`PICOBridge/PicoIrisSemanticTyping.v` names the corresponding Iris phase package as
`pico_sem_cache_compute_then_write_phasesI`, with constructors from both the
general `cache_compute_then_write_safe` judgment and the literal
`cache_update_sequence_safe` proposition.
`PICOBridge/PicoIrisLogicalRelation.v` re-exports the same boundary under LR-facing names,
including `pico_lr_cache_compute_then_write_phasesI` and
`pico_lr_cache_compute_then_write_phases_elim`.  The semantic and LR layers now
also project the post-compute cache-write phase into tail thread/config
interpretations, so clients can continue from the general compute/write package
without reopening the literal update proof.  The same phase package now has a
WP-facing tail-step rule, which is deliberately scoped to the post-compute
cache write and does not claim that an arbitrary compute statement executes in
one step.  Under a closed config-interpretation assumption, the phase package
also derives final weak-read validity for executions starting from that
post-compute tail config.  The semantic layer also packages the literal
post-compute tail read boundary as
`pico_sem_cache_update_sequence_tail_read_specI`, with named semantic closure
thread-post, and covered-step evidence propositions for constructing it.
The execution-only spec
`pico_sem_cache_update_sequence_tail_execution_specI` derives final
cache-history preservation and semantic cache-safe execution for the tail
configuration; the read spec layers final weak-read validity on top.
LR-facing variants carry the same endpoint through
the invariant, state-interpretation, and WP-state bridge resource layers, with
allocation-to-read variants for callers that start from a pure tail
cache-history fact.  Matching transport/allocation lemmas return the final
resource itself for callers that need to continue reasoning after the tail
execution.  Combined allocation/update-read variants return both the final
resource and the read-validity fact at this same boundary.  Literal
cache-update sequence wrappers expose the same combined endpoint directly from
`pico_lr_cache_update_sequenceI`, with thread-post and covered-step variants
that derive the closure from the named LR execution-evidence propositions.
The general compute/write phase tail also has named execution and read specs
in both layers:
`pico_sem_cache_compute_then_write_phases_tail_execution_specI`,
`pico_sem_cache_compute_then_write_phases_tail_read_specI`,
`pico_lr_cache_compute_then_write_phases_tail_execution_specI`, and
`pico_lr_cache_compute_then_write_phases_tail_read_specI`.  These specs expose
the post-compute cache-write boundary before the proof specializes to the
literal cache-update sequence.  The LR resource endpoints
`pico_lr_cache_compute_then_write_phases_tail_inv_alloc_execution_specI`,
`pico_lr_cache_compute_then_write_phases_tail_state_alloc_execution_specI`,
`pico_lr_cache_compute_then_write_phases_tail_wp_bridge_alloc_execution_specI`,
`pico_lr_cache_compute_then_write_phases_tail_inv_alloc_read_specI`,
`pico_lr_cache_compute_then_write_phases_tail_state_alloc_read_specI`, and
`pico_lr_cache_compute_then_write_phases_tail_wp_bridge_alloc_read_specI`
consume those named specs directly.  Matching `from_semI` variants consume the
semantic phase specs and allocate the same LR resources through the
semantic-to-LR bridge.
The LR layer mirrors the semantic execution/read split at the same boundary:
`pico_lr_cache_update_sequence_tail_execution_specI` carries the tail
execution, initial cache-history fact, literal update interpretation, and
closure evidence as one execution-only Iris proposition, with constructors from
named LR evidence and semantic-to-LR constructors from the semantic execution
spec, semantic thread-post evidence, and semantic covered-step evidence.
The bundled spec `pico_lr_cache_update_sequence_tail_read_specI` layers the
final weak read on top, with constructors and direct resource/read endpoints
from named thread-post or covered-step evidence, plus a bridge and direct
resource/read endpoints from the semantic read spec, semantic thread-post
evidence, and semantic covered-step evidence.  The LR tail read spec also
mirrors the semantic final-history and semantic-execution endpoints, with
direct LR wrappers from the semantic execution spec.  The literal update tail
specs now explicitly specialize the general phase specs through
`pico_sem_cache_update_sequence_tail_execution_specI_phaseI`,
`pico_sem_cache_update_sequence_tail_read_specI_phaseI`,
`pico_lr_cache_update_sequence_tail_execution_specI_phaseI`, and
`pico_lr_cache_update_sequence_tail_read_specI_phaseI`.  The literal LR layer
also exposes final-resource endpoints from the execution spec:
`pico_lr_cache_update_sequence_tail_inv_alloc_execution_specI`,
`pico_lr_cache_update_sequence_tail_state_alloc_execution_specI`, and
`pico_lr_cache_update_sequence_tail_wp_bridge_alloc_execution_specI`, plus
matching variants from the semantic execution spec, semantic thread-post
evidence, and semantic covered-step evidence.  The read-spec resource endpoints
delegate through the general phase read-spec resource API.

The remaining Level 2 work is to connect the minimal PICO Iris language shell
to a full weakest-precondition and adequacy development for PICO programs.

Level 3 would add a full Iris semantic interpretation of PICO types and prove
semantic type soundness inside Iris.

Those deeper Iris results are future work.  The current branch completes the
generic trace-robust cache core, keeps the Level 1 pure-Iris bridge, and adds
Rocq-side SC/weak-observation models to clarify the accepted/rejected cache
story.
