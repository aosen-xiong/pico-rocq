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

- `PICO_IRIS_ROADMAP.md`: staged status for the PICO Iris pipeline, including
  current theorem boundaries and remaining non-claims before a full
  ghost-backed logical relation.
- `DerivedCache.v`: sequential derived-cache soundness for `Final` abstract
  fields and `Assignable` integer cache fields.
- `PICOBridge/PicoMemoryModel.v`: field-addressed memory/history interface for the next
  weak-memory layer.
- `Core/GenericCacheProtocol.v`: generic trace-robust derived-cache theory:
  stable abstraction providers, cache protocols, valid traces, cache-safe
  methods, and weak read-from-history soundness.
- `Iris/GenericCacheIris.v`: pure Iris-facing wrapper for the generic cache
  theorem boundary.
- `Iris/GenericCacheGhostState.v`: PICO-independent auth/agreement ownership for a
  single generic `CacheHistorySnapshot`, plus ghost-backed read, trace, and
  refinement endpoints.
- `Core/GenericDerivedCache.v`: current derived-cache instance of the generic
  protocol, weak-memory read bridge, hash-cache trace examples, and PICO
  stable-abstraction provider hook.
- `Iris/GenericDerivedCacheIris.v`: pure and ghost-backed Iris bridge for the
  derived-cache instance and PICO weak-memory cache history.
- `PICOBridge/PicoCacheTyping.v`: first typing-shaped bridge from a derived-cache update
  sequence to the semantic cache-safety layer.
- `PICOBridge/PicoIrisLanguage.v`: minimal Iris `language` wrapper for the
  field-addressed PICO weak-memory thread step.
- `PICOBridge/PicoIrisSemanticCache.v`: first Iris-facing pure wrapper for semantic
  cache-history safety, now exposing both specialized unknown-or-derived facts
  and generic `CacheHistOK` endpoints.
- `PICOBridge/PicoIrisCacheInvariant.v`: first invariant-backed PICO Iris interpretation
  of cache-history validity.
- `PICOBridge/PicoIrisGhostState.v`, `PICOBridge/PicoIrisStateInterp.v`, and
  `PICOBridge/PicoIrisStateBridge.v`: ghost-backed facade over the weak-memory state,
  target history, cache-history validity, and the WP-visible state component.
- `PICOBridge/PicoIrisWP.v`: first WP-facing lifting lemma specialized to PICO
  `wm_thread_step`.
- `PICOBridge/PicoIrisThreadSafety.v`: WP-facing cache-safety lifting for
  `cache_safe_thread`.
- `PICOBridge/PicoIrisSemanticTyping.v`: first pure semantic typing interpretation that
  packages PICO typing with cache safety for WP rules.
- `PICOBridge/PicoIrisLogicalRelation.v`: logical-relation-facing facade over the current
  semantic typing and invariant endpoints.
- `PICOBridge/ConcurrentPico.v`: sequentially consistent interleaving model for PICO
  thread pools sharing one heap.
- `PICOBridge/WeakPico.v`: weak-observation model for cache writes, with explicit
  observed final-field snapshots.
- `Examples/StringCacheIris.v`: Iris/heap_lang comparison model for a String-like hash
  cache under SC interleaving concurrency.
- `PICOBridge/PicoIrisCacheBridge.v`: bridge/summary theorems collecting the sequential
  PICO, SC PICO, weak-observation PICO, and Iris-facing results.

## Final derived-cache story

The final derived-cache theorem is generic:

```text
A racy derived cache is semantically invisible when the method is correct for
every cache-read trace allowed by the cache protocol.
```

The architecture separates the stable abstraction provider from
the cache protocol.  PICO proves that immutable objects provide a stable
abstract value, while the generic cache theory defines cache-field
protocols over histories, valid cache-read traces, trace-robust cache-safe
methods, and refinement to pure recomputation.  In that final story,
`String.hashCode`, URI caches, and BigInteger caches are examples of the same
theorem, not separate special-purpose soundness results.

The current repository now starts from that generic story.  It mechanizes
`StableAbs`, `CacheProtocol`, `CacheHistOK`, `CacheHistValidExtension`,
`ValidTrace`, trace-robust `CacheSafeMethod`, `CacheRefinesPure`,
`PureRecomputeResult`, trace-write extension relations
`CacheHistExtendsByTrace` and `CacheHistSnapshotExtendsByTrace`, and the
read-from-history/post-history/refinement soundness lemmas.  The memory-model
side condition for the paper is `AtomicCacheField(k)`: reads and writes of
cache field `k` observe complete values from that field's history, or its
default initial value.  This admits Java `int`, `boolean`, and reference cache
values, but rejects plain non-volatile `long`/`double` caches unless
`volatile`, synchronization, an atomic wrapper, or a verified representation
protocol supplies whole-value behavior.  Reference-valued caches also need a
separate safe-publication or stable-representation premise for the referenced
object.  The trace-write extension relations are append preserving: each final
cache-field history is
the initial history followed by added writes, and every added write is covered
by the method trace.  The central pure
endpoints are now `trace_robust_semantic_immutability` and
`trace_robust_semantic_immutability_after_history_extension`, which combine
valid reads, cache-safe method results, and append-only method-write history
extension into post-state semantic immutability, in
[Core/GenericCacheProtocol.v](Core/GenericCacheProtocol.v).  The current
unknown-or-derived cache, bad/local-copy hash-cache trace examples, and PICO
stable-abstraction providers are instances in
[Core/GenericDerivedCache.v](Core/GenericDerivedCache.v), including
`pico_stable_abs` for the sequential heap view, `pico_wm_stable_abs` for the
field-history weak-state view whose abstract field histories are stable at the
abstract values, `pico_wm_stable_cache_safe_method_sound_after_steps_post_history`
and `pico_wm_stable_cache_safe_method_sound_from_closed_steps_post_history`
for the pure PICO-provider/post-execution trace bridge,
`pico_wm_stable_cache_safe_method_sound_after_steps_write_extension`,
`pico_wm_stable_cache_safe_method_sound_after_steps_cache_only_write_extension`,
and
`pico_wm_stable_cache_safe_method_sound_from_closed_steps_cache_only_write_extension`
for the method-write/cache-only end-to-end bridge, and
`good_hash_refines_pure_recompute` for the accepted local-copy pattern.  The
generic Iris side now has a first PICO-independent ownership layer in
[Iris/GenericCacheGhostState.v](Iris/GenericCacheGhostState.v), where an auth/agreement
resource owns one `CacheHistorySnapshot` and exposes ghost-backed read, trace,
semantic-immutability, pure-refinement, and post-extension trace/refinement
endpoints such as `generic_cache_history_interp_valid_trace_post_extension`
and `generic_cache_history_interp_refines_pure_post_extension`, with
`generic_trace_robust_semantic_immutability_interp_alloc_post` as the
ghost-backed final-story endpoint.  [Iris/IrisSemanticBridge.v](Iris/IrisSemanticBridge.v)
is now the compact public Iris surface over that layer: it exposes
`StableAbsI`, `CacheHistI`, `SemImmI`, a read-validity rule, a valid-extension
preservation rule, and `cache_safe_method_wpI`.  [Examples/LocalCopyCacheRule.v](Examples/LocalCopyCacheRule.v)
uses that surface for the representative local-copy hash-cache rule, while the
older pure-Iris wrappers remain as proof-engineering detail.  The
derived-cache weak history bridge instantiates that layer in
[Iris/GenericDerivedCacheIris.v](Iris/GenericDerivedCacheIris.v), including
`wm_derived_cache_history_interp_valid_trace_post_extension` and
`wm_derived_cache_history_interp_refines_pure_post_extension`, plus the
method-write extension endpoints
`wm_derived_cache_history_interp_writes_valid_extension`,
`wm_derived_cache_history_interp_writes_valid_extension_alloc`, and the
public trace-robust theorem
`wm_derived_cache_trace_robust_semantic_immutability_alloc_post`, which turns
a cache-safe method's recorded writes into the post-state semantic
immutability interpretation.  The PICO
state/WP bridge layers now allocate and return that generic history
interpretation through `pico_cache_state_interp_generic_history_interp_alloc`
and `pico_wp_state_cfg_bridge_generic_history_interp_alloc`, and now expose
post-extension refinement wrappers
`pico_cache_state_interp_generic_history_refines_pure_post_extension`,
`pico_cache_state_interp_after_steps_generic_history_refines_pure_post_extension`,
`pico_wp_state_cfg_bridge_generic_history_refines_pure_post_extension`, and
`pico_wp_state_cfg_bridge_after_steps_generic_history_refines_pure_post_extension`;
the method-write semantic route is exposed through
`pico_cache_state_interp_after_steps_semantic_immutability_method_write_extension_post`
and
`pico_wp_state_cfg_bridge_after_steps_semantic_immutability_method_write_extension_post`,
with PICO-provider conveniences
`pico_cache_state_interp_after_steps_pico_wm_stable_preserved_method_write_extension_post`,
`pico_cache_state_interp_after_steps_pico_wm_stable_final_fields_method_write_extension_post`,
`pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_preserved_method_write_extension_post`,
and
`pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_final_fields_method_write_extension_post`.
The weaker cache-only postcondition
`wm_histories_only_extend_field`, together with `wm_write_avoids_fields`,
derives the abstract-field preservation fact via
`wm_histories_only_extend_field_preserves_fields`; state and WP bridge expose
this under the public final-story theorems
`pico_cache_state_interp_after_steps_pico_wm_stable_trace_robust_cache_only_post`
and
`pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_trace_robust_cache_only_post`.
The pure
weak-history layer derives that postcondition from concrete writes and selected
field-write steps through `wm_write_histories_only_extend_field`,
`wm_thread_step_fldwrite_histories_only_extend_field`, and
`wm_step_selected_fldwrite_histories_only_extend_field`.
Semantic typing and LR expose the same route via
`sem_typed_state_after_steps_generic_history_refines_pure_post_extensionI`,
`sem_typed_wp_bridge_after_steps_generic_history_refines_pure_post_extensionI`,
`pico_lr_config_state_steps_generic_history_refines_pure_post_extension`, and
`pico_lr_wp_state_bridge_after_steps_generic_history_refines_pure_post_extension`,
and now expose the method-write route via
`sem_typed_state_after_steps_semantic_immutability_method_write_extension_postI`,
`sem_typed_wp_bridge_after_steps_semantic_immutability_method_write_extension_postI`,
`pico_lr_config_state_steps_semantic_immutability_method_write_extension_post`,
and
`pico_lr_wp_state_bridge_after_steps_semantic_immutability_method_write_extension_post`,
with preserved/final-field PICO-provider variants
`sem_typed_state_after_steps_pico_wm_stable_preserved_method_write_extension_postI`,
`sem_typed_wp_bridge_after_steps_pico_wm_stable_preserved_method_write_extension_postI`,
`sem_typed_state_after_steps_pico_wm_stable_final_fields_method_write_extension_postI`,
`sem_typed_wp_bridge_after_steps_pico_wm_stable_final_fields_method_write_extension_postI`,
`pico_lr_config_state_steps_pico_wm_stable_preserved_method_write_extension_post`,
`pico_lr_wp_state_bridge_after_steps_pico_wm_stable_preserved_method_write_extension_post`,
`pico_lr_config_state_steps_pico_wm_stable_final_fields_method_write_extension_post`,
and
`pico_lr_wp_state_bridge_after_steps_pico_wm_stable_final_fields_method_write_extension_post`;
the public LR cache-only theorems use the cache-only postcondition instead of
requiring callers to pass `wm_histories_preserve_fields` directly:
`pico_lr_config_state_steps_pico_wm_stable_trace_robust_cache_only_post` and
`pico_lr_wp_state_bridge_after_steps_pico_wm_stable_trace_robust_cache_only_post`;
after-step variants can also allocate the same generic snapshot for the
post-execution weak state.  The generic ghost layer can now allocate a fresh post-snapshot
interpretation from a valid history extension, matching the final
semantic-immutability story over the execution result; state, WP bridge,
semantic-typing, and LR endpoints now package this as method-post theorems
returning the pure result and post-state semantic immutability, with
the pure-Iris facade exposing the same post-history shape through
`valid_trace_from_post_history_with_valid_extensionI`,
`valid_trace_from_post_snapshot_with_valid_extensionI`,
`cache_safe_method_sound_from_post_history_with_valid_extensionI` and
`cache_safe_method_refines_pure_from_post_history_with_valid_extensionI`, and with
PICO-provider-specialized wrappers
such as `pico_cache_state_interp_after_steps_pico_wm_stable_method_post`,
`pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_method_post`,
`pico_cache_state_interp_after_steps_pico_wm_stable_preserved_method_post`,
`pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_preserved_method_post`,
`pico_cache_state_interp_after_steps_pico_wm_stable_final_fields_method_post`,
`pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_final_fields_method_post`,
`sem_typed_state_after_steps_pico_wm_stable_method_postI`,
`sem_typed_wp_bridge_after_steps_pico_wm_stable_method_postI`,
`sem_typed_state_after_steps_pico_wm_stable_preserved_method_postI`,
`sem_typed_wp_bridge_after_steps_pico_wm_stable_preserved_method_postI`,
`sem_typed_state_after_steps_pico_wm_stable_final_fields_method_postI`,
`sem_typed_wp_bridge_after_steps_pico_wm_stable_final_fields_method_postI`,
`pico_lr_wp_state_bridge_after_steps_pico_wm_stable_preserved_method_post`,
`pico_lr_config_state_steps_pico_wm_stable_preserved_method_post`,
`pico_lr_wp_state_bridge_after_steps_pico_wm_stable_final_fields_method_post`,
`pico_lr_config_state_steps_pico_wm_stable_final_fields_method_post`,
`pico_lr_wp_state_bridge_after_steps_pico_wm_stable_method_post`, and
`pico_lr_config_state_steps_pico_wm_stable_method_post`.  The PICO cache-typing
bridge also exposes the generic refinement boundary
through `pico_cache_compute_refines_pure`,
`verified_cache_compute_refines_pure_via_generic`,
`cache_compute_write_safe_refines_pure_via_generic`, and
`cache_update_sequence_safe_refines_pure_via_generic`; `PICOBridge/PicoIrisSemanticTyping.v`
mirrors these as pure Iris propositions with the corresponding `...I` lemmas.
The existing Iris/PICO files remain staged wrappers around the field-history
theorem boundaries.

The generic view is now threaded through the semantic-cache, invariant,
state-interpretation, WP-state bridge, semantic typing, and LR facade layers:
callers can use `CacheHistOK`/`cache_valid` endpoints instead of only the older
`derived_cache_msg_ok` and unknown-or-derived wrappers.
The semantic-typing and LR facades also expose direct generic-ghost consumers:
`sem_typed_state_generic_history_*`,
`sem_typed_wp_bridge_generic_history_*`,
`sem_typed_state_after_steps_semantic_immutability_method_postI`,
`sem_typed_wp_bridge_after_steps_semantic_immutability_method_postI`,
`sem_typed_state_after_steps_pico_wm_stable_preserved_method_postI`,
`sem_typed_wp_bridge_after_steps_pico_wm_stable_preserved_method_postI`,
`sem_typed_state_after_steps_pico_wm_stable_final_fields_method_postI`,
`sem_typed_wp_bridge_after_steps_pico_wm_stable_final_fields_method_postI`,
`pico_lr_config_state_generic_history_*`, and
`pico_lr_wp_state_bridge_generic_history_*`, including `after_steps`
variants for post-execution state/WP bridge configurations.  LR allocation
wrappers also now expose generic final-read validity for execution-prefix,
closed-step, closure-step, direct `wm_steps`, and direct preservation-function
paths, including `pico_lr_wp_state_bridge_alloc_after_steps_preserved_read_valid_generic`.
Cache-update tail
read specs and selected-first execution wrappers likewise expose
`...final_read_valid_genericI` and generic allocation/read-spec variants.
The selected-first and post-first-step tail-pool LR wrappers now also carry
generic `cache_valid` conclusions through existing invariant/state/WP bridge
resources, freshly allocated resource paths, and semantic/configI facade
variants.  The semantic selected-first LR wrappers now expose matching generic
closure/configI read-validity endpoints.
The weak-memory allowed-write/config-allowed read boundaries now also expose
generic `cache_valid` variants through the pure, semantic-cache, state/WP
bridge, and LR facade layers, including direct one-allowed-write/read
endpoints.
They also produce generic valid-history extension facts for post-execution
weak states through invariant, state/WP bridge, and LR-facing endpoints, giving
the generic method theorem a direct post-history premise.
The bundled `pico_lr_cache_update_execution_specI` path now exposes the same
generic result at the evidence/spec layer, including final-read, existing
resource read, allocation-to-read, final-resource/read, and from-safe closure
constructor variants.  The from-safe thread-post and covered-step constructors
now forward to the same generic `cache_valid` read/resource endpoints.

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
| Field-addressed memory interface | Weak-memory reasoning should be layered over field histories, not by mutating PICO's deterministic big-step semantics | Field addresses are `(Loc, field)` pairs; cache histories contain only unknown or derived values; weak reads must return a value from the field history | Generic cache-history read/write lemmas, read-validity lemmas for cache fields, cache-safe method/statement/config judgments, allowed-write preservation/final-read endpoints, environment-sensitive cache-write helpers, and semantic cache-safety theorem shapes are available for later weak-memory semantics | `FieldAddr`, `write_msg`, `wm_state`, `CacheMemoryModel`, `wm_cache_history_state_read_unknown_or_derived`, `wm_config_cache_history_state_read_valid`, `wm_config_cache_history_state_read_unknown_or_derived`, `wm_write_allowed_preserves_cache_history`, `wm_write_allowed_read_valid`, `wm_steps_read_valid_from_allowed_writes`, `wm_steps_read_valid_from_config_allowed`, `cache_safe_config_semantic_cache_safe` in [PICOBridge/PicoMemoryModel.v](PICOBridge/PicoMemoryModel.v); `wm_write_allowed_read_valid_generic`, `wm_steps_read_valid_from_allowed_writes_generic`, `wm_steps_read_valid_from_config_allowed_generic`, `pico_wm_stable_cache_safe_method_sound_after_steps_post_history`, `pico_wm_stable_cache_safe_method_sound_from_closed_steps_post_history` in [Core/GenericDerivedCache.v](Core/GenericDerivedCache.v) |
| Cache typing bridge | A typed derived-cache computation produces a nonzero derived integer in a temporary and writes it to the target cache field | Statement typing for the compute and write statements plus runtime receiver/tmp facts, a phased compute/write safety judgment, the derived-value equation, and the generic trace protocol | The post-compute cache write is a `cache_safe_stmt`; the whole compute/write shape is exposed as pre-env/post-env safe phases; lists of such tail threads imply `cache_safe_config`; the same typed compute/write facts refine pure recomputation through `CacheRefinesPure`; the literal `tmp = EInt n` case is an instance | `verified_cache_compute`, `pico_cache_compute_refines_pure`, `verified_cache_compute_refines_pure_via_generic`, `cache_compute_write_safe`, `cache_compute_write_safe_refines_pure_via_generic`, `cache_compute_then_write_safe`, `cache_compute_then_write_safe_implies_cache_safe_phases`, `cache_compute_then_write_safe_implies_cache_safe_stmt_same_env`, `cache_compute_write_safe_tail_threads_imply_cache_safe_config`, `cache_update_sequence_safe_implies_cache_compute_write_safe`, `cache_update_sequence_safe_refines_pure_via_generic`, `cache_update_sequence_safe_implies_cache_safe_phases` in [PICOBridge/PicoCacheTyping.v](PICOBridge/PicoCacheTyping.v) |
| PICO Iris language shell | Iris integration should start from the field-addressed PICO small-step shell, not heap_lang | Iris expressions are `wm_thread`; values are finished `SSkip` threads; state is `wm_state`; primitive steps are `wm_thread_step` with no observations or forks yet | The minimal Iris `language` instance compiles and exposes value/non-value, value-shape inversion, step, reducibility, not-stuck, and primitive statement progress bridge lemmas | `pico_language`, `pico_to_val_inv`, `pico_to_val_some_inv`, `pico_language_to_val_inv`, `pico_language_to_val_some_inv`, `pico_language_to_val_var_assign`, `pico_language_to_val_fld_write`, `pico_language_to_val_seq`, `pico_thread_step_is_prim_step`, `pico_reducible_iff_thread_step`, `pico_not_stuck_iff_value_or_thread_step`, `pico_assign_int_thread_step_exists`, `pico_field_read_thread_step_exists`, `pico_fldwrite_thread_step_exists`, `pico_seqskip_thread_step_exists`, `pico_seqstep_thread_step_exists` in [PICOBridge/PicoIrisLanguage.v](PICOBridge/PicoIrisLanguage.v) |
| PICO Iris semantic cache wrapper | The first Iris-facing semantic interpretation should mirror the pure cache-history theorem before adding ghost state or a full logical relation | Cache-history state, generic `CacheHistOK`, cache-read validity, cache-safe configs, semantic cache-safe execution, and allowed-write final-read validity are wrapped as pure Iris propositions | Cache-safe and allowed-write executions yield named Iris execution predicates, final cache-history validity, generic cache-history validity, and read-validity facts for weak cache reads | `wm_config_cache_history_stateI`, `wm_config_cache_hist_ok_genericI`, `wm_config_cache_history_state_genericI`, `wm_config_cache_history_state_read_valid_genericI`, `wm_write_allowed_read_valid_genericI`, `wm_semantic_cache_safe_execution_genericI`, `wm_semantic_cache_safe_execution_read_valid_genericI`, `wm_semantic_cache_safe_executionI`, `wm_config_cache_history_state_read_unknown_or_derivedI`, `wm_semantic_cache_safe_execution_read_validI`, `wm_semantic_cache_safe_execution_read_unknown_or_derivedI`, `wm_steps_read_valid_from_allowed_writesI`, `wm_steps_read_unknown_or_derived_from_allowed_writesI`, `wm_steps_read_valid_from_config_allowedI`, `wm_steps_read_unknown_or_derived_from_config_allowedI`, `cache_safe_config_semantic_cache_safe_executionI` in [PICOBridge/PicoIrisSemanticCache.v](PICOBridge/PicoIrisSemanticCache.v) |
| PICO Iris cache invariant | The pure semantic cache wrapper needs a real Iris interpretation boundary before ghost-state refinement | A namespace protects `wm_config_cache_history_stateI` as an Iris invariant for a fixed weak-memory config | The invariant can be allocated, opened for weak-read validity, generic `CacheHistOK`, generic `cache_valid`, generic valid-history extension, and explicit unknown-or-derived read classification, transported across semantic cache-safe executions, reallocated for cache-safe PICO thread/config/multi-step executions, and used to validate final weak reads | `pico_cache_history_inv`, `pico_cache_history_inv_read_valid`, `pico_cache_history_inv_cache_hist_ok_generic`, `pico_cache_history_inv_valid_extension_generic`, `pico_cache_history_inv_read_valid_generic`, `pico_cache_history_inv_read_unknown_or_derived`, `pico_cache_history_inv_after_execution_alloc`, `pico_cache_history_inv_after_execution_cache_hist_ok_generic`, `pico_cache_history_inv_after_execution_valid_extension_generic`, `pico_cache_history_inv_after_execution_read_valid_generic`, `pico_cache_history_inv_after_execution_read_valid`, `pico_cache_history_inv_after_execution_read_unknown_or_derived`, `pico_cache_history_inv_after_steps_alloc`, `pico_cache_history_inv_after_steps_valid_extension_generic`, `pico_cache_history_inv_after_steps_read_valid_generic`, `pico_cache_history_inv_after_steps_read_valid`, `pico_cache_history_inv_after_steps_read_unknown_or_derived` in [PICOBridge/PicoIrisCacheInvariant.v](PICOBridge/PicoIrisCacheInvariant.v) |
| PICO Iris ghost cache state | The state interpretation needs real Iris ownership before it can connect to WP `state_interp` | The whole weak-memory state, an address-indexed field-history map, and the concrete target field history are recorded in authoritative agreement resources hidden behind a `picoCacheG` class | Authoritative and fragment ownership can be allocated for the weak-memory state, target field-history map cell, and target history, giving later WP work both whole-state and per-field ownership hooks | `picoCacheG`, `pico_cache_weak_state_auth`, `pico_cache_field_history_auth`, `pico_cache_field_history_own`, `pico_cache_history_auth`, `pico_cache_weak_state_own_alloc`, `pico_cache_field_history_own_alloc`, `pico_cache_history_own_alloc` in [PICOBridge/PicoIrisGhostState.v](PICOBridge/PicoIrisGhostState.v) |
| PICO Iris state interpretation facade | The invariant boundary should be replaceable by ghost ownership without changing callers | `pico_cache_state_interp` packages hidden authoritative weak-state, per-field target-history, target-history ownership together with `pico_cache_history_inv` | Allocation, weak-state snapshot extraction, field-history snapshot/read validity, generic `CacheHistOK`/`cache_valid`, generic valid-history extension, target-history validity extraction, generic cache-history snapshot ownership allocation, generic ghost-backed read/refinement/method-post endpoints, target/non-target/allowed write transport, concrete field-write step transport, one-thread-step transport, preservation-function transport, and final weak-read validity are exposed under state-interpretation names for later connection to Iris `state_interp` | `pico_cache_state_interp`, `pico_cache_state_interp_alloc`, `pico_cache_state_interp_weak_state_snapshot`, `pico_cache_state_interp_field_history_snapshot`, `pico_cache_state_interp_field_history_snapshot_valid`, `pico_cache_state_interp_field_history_read_valid`, `pico_cache_state_interp_read_valid_generic`, `pico_cache_state_interp_target_history_valid_generic`, `pico_cache_state_interp_valid_extension_generic`, `pico_cache_state_interp_generic_history_interp_alloc`, `pico_cache_state_interp_generic_history_read_valid`, `pico_cache_state_interp_generic_history_refines_pure`, `pico_cache_state_interp_after_steps_semantic_immutability_method_post`, `pico_cache_state_interp_after_steps_pico_wm_stable_method_post`, `pico_cache_state_interp_after_steps_pico_wm_stable_preserved_method_post`, `pico_cache_state_interp_field_history_read_valid_generic`, `pico_cache_state_interp_after_target_write`, `pico_cache_state_interp_after_other_write`, `pico_cache_state_interp_after_allowed_write_threads`, `pico_cache_state_interp_after_allowed_write`, `pico_cache_state_interp_after_allowed_write_threads_read_valid_generic`, `pico_cache_state_interp_after_allowed_write_read_valid_generic`, `pico_cache_state_interp_after_fldwrite_step`, `pico_cache_state_interp_target_history_valid`, `pico_cache_state_interp_after_thread_step`, `pico_cache_state_interp_after_steps`, `pico_cache_state_interp_after_steps_valid_extension_generic`, `pico_cache_state_interp_after_steps_preserved`, `pico_cache_state_interp_after_steps_preserved_valid_extension_generic`, `pico_cache_state_interp_after_steps_read_valid_generic`, `pico_cache_state_interp_after_steps_read_valid`, `pico_cache_state_interp_read_unknown_or_derived`, `pico_cache_state_interp_after_steps_read_unknown_or_derived`, `pico_cache_state_interp_after_steps_preserved_read_valid_generic`, `pico_cache_state_interp_after_steps_preserved_read_unknown_or_derived`, `pico_cache_state_interp_alloc_after_steps_read_unknown_or_derived`, `pico_cache_state_interp_alloc_after_steps_preserved_read_unknown_or_derived`, `pico_cache_state_interp_after_steps_preserved_read_valid` in [PICOBridge/PicoIrisStateInterp.v](PICOBridge/PicoIrisStateInterp.v) |
| PICO Iris WP state bridge | Iris WP exposes an abstract `state_interp` state component before the PICO facade is installed as the real instance | The bridge records that the WP-visible `sigma` is the `wc_state` inside a `pico_cache_state_interp` configuration | The bridge can be allocated, inspected for state equality, used for target-history/read validity and generic `CacheHistOK`/`cache_valid`/valid-extension facts, allocate generic cache-history snapshot ownership, derive generic ghost-backed read/refinement/method-post facts, transported across one primitive thread step, allowed writes, concrete field-write steps, multi-step executions, preservation-function executions, and allocated directly into a final-read endpoint | `pico_wp_state_cfg_bridge`, `pico_wp_state_cfg_bridge_alloc`, `pico_wp_state_cfg_bridge_target_history_valid`, `pico_wp_state_cfg_bridge_target_history_valid_generic`, `pico_wp_state_cfg_bridge_valid_extension_generic`, `pico_wp_state_cfg_bridge_generic_history_interp_alloc`, `pico_wp_state_cfg_bridge_generic_history_read_valid`, `pico_wp_state_cfg_bridge_generic_history_refines_pure`, `pico_wp_state_cfg_bridge_after_steps_semantic_immutability_method_post`, `pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_method_post`, `pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_preserved_method_post`, `pico_wp_state_cfg_bridge_read_valid_generic`, `pico_wp_state_cfg_bridge_read_valid`, `pico_wp_state_cfg_bridge_read_unknown_or_derived`, `pico_wp_state_cfg_bridge_after_thread_step`, `pico_wp_state_cfg_bridge_after_allowed_write_threads`, `pico_wp_state_cfg_bridge_after_allowed_write`, `pico_wp_state_cfg_bridge_after_allowed_write_threads_read_valid_generic`, `pico_wp_state_cfg_bridge_after_allowed_write_read_valid_generic`, `pico_wp_state_cfg_bridge_after_fldwrite_step`, `pico_wp_state_cfg_bridge_after_steps`, `pico_wp_state_cfg_bridge_after_steps_valid_extension_generic`, `pico_wp_state_cfg_bridge_after_steps_preserved`, `pico_wp_state_cfg_bridge_after_steps_preserved_valid_extension_generic`, `pico_wp_state_cfg_bridge_after_steps_read_valid_generic`, `pico_wp_state_cfg_bridge_after_steps_read_valid`, `pico_wp_state_cfg_bridge_after_steps_read_unknown_or_derived`, `pico_wp_state_cfg_bridge_after_steps_preserved_read_valid_generic`, `pico_wp_state_cfg_bridge_after_steps_preserved_read_valid`, `pico_wp_state_cfg_bridge_after_steps_preserved_read_unknown_or_derived`, `pico_wp_state_cfg_bridge_alloc_after_steps_read_valid_generic`, `pico_wp_state_cfg_bridge_alloc_after_steps_read_valid`, `pico_wp_state_cfg_bridge_alloc_after_steps_read_unknown_or_derived` in [PICOBridge/PicoIrisStateBridge.v](PICOBridge/PicoIrisStateBridge.v) |
| PICO Iris WP state-bridge contract | The abstract `state_interp` needs an explicit target contract before it is replaced by the PICO ghost-backed facade | The contract names the ordinary WP lift premise, a cache-safe lift premise, and stronger bridge-aware step obligations that reveal `pico_wp_state_cfg_bridge` for the current thread | Future concrete `irisGS` work has a stable obligation boundary for connecting primitive WP state updates to the field-addressed cache-state facade; bridge-aware contracts entail the ordinary/cache-safe WP lift premises, with semantic/LR adapters deriving and forgetting cache-safe bridge views from typed threads and selected config entries | `pico_wp_state_bridge_lift_premise`, `pico_wp_state_bridge_step_contract`, `pico_wp_state_bridge_step_contract_lift_premise`, `pico_wp_state_bridge_cache_safe_lift_premise`, `pico_wp_state_bridge_cache_safe_step_contract`, `pico_wp_state_bridge_cache_safe_step_contract_lift_premise`, `pico_wp_state_bridge_step_contract_cache_safe_contract`, `pico_wp_state_bridge_step_contract_cache_safe_lift_premise`, `pico_wp_state_bridge_cache_safe_lift_premise_lift_premise`, `pico_wp_state_bridge_cache_safe_contract_step_contract`, `pico_wp_state_bridge_cache_safe_contract_from_step_contract` in [PICOBridge/PicoIrisWPStateBridge.v](PICOBridge/PicoIrisWPStateBridge.v); `pico_sem_typed_thread_cacheI_bridge_cache_safe_contract`, `pico_sem_typed_thread_cacheI_bridge_cache_safe_lift_premise`, `pico_sem_typed_thread_cacheI_bridge_lift_premise`, `pico_sem_typed_thread_cacheI_bridge_lift_premise_from_cache_safe`, `pico_sem_typed_thread_cacheI_bridge_contract_from_cache_safe`, `pico_sem_typed_config_cacheI_nth_thread_entryI`, `pico_sem_typed_config_cacheI_nth_threadI`, `pico_sem_typed_config_cacheI_nth_threadI_elim`, `pico_sem_typed_config_cacheI_nth_thread_bridge_lift_premise`, `pico_sem_typed_config_cacheI_nth_thread_bridge_cache_safe_lift_premise`, `pico_sem_typed_config_cacheI_nth_thread_bridge_cache_safe_contract`, `pico_sem_typed_config_cacheI_nth_thread_cache_safeI`, `pico_sem_typed_config_cacheI_nth_bridge_cache_safe_contract`, `pico_sem_typed_config_cacheI_nth_bridge_cache_safe_lift_premise`, `pico_sem_typed_config_cacheI_nth_bridge_lift_premise`, `pico_sem_typed_config_cacheI_nth_bridge_lift_premise_from_cache_safe`, `pico_sem_typed_config_cacheI_nth_bridge_contract_from_cache_safe` in [PICOBridge/PicoIrisSemanticTyping.v](PICOBridge/PicoIrisSemanticTyping.v); `pico_lr_threadI_bridge_cache_safe_contract`, `pico_lr_threadI_bridge_cache_safe_lift_premise`, `pico_lr_threadI_bridge_lift_premise`, `pico_lr_threadI_bridge_lift_premise_from_cache_safe`, `pico_lr_threadI_bridge_contract_from_cache_safe`, `pico_lr_configI_nth_thread_entryI`, `pico_lr_configI_nth_threadI`, `pico_lr_configI_nth_threadI_elim`, `pico_lr_configI_nth_thread_bridge_lift_premise`, `pico_lr_configI_nth_thread_bridge_cache_safe_lift_premise`, `pico_lr_configI_nth_thread_bridge_cache_safe_contract`, `pico_lr_configI_nth_thread_cache_safeI`, `pico_lr_configI_nth_bridge_cache_safe_contract`, `pico_lr_configI_nth_bridge_cache_safe_lift_premise`, `pico_lr_configI_nth_bridge_lift_premise`, `pico_lr_configI_nth_bridge_lift_premise_from_cache_safe`, `pico_lr_configI_nth_bridge_contract_from_cache_safe` in [PICOBridge/PicoIrisLogicalRelation.v](PICOBridge/PicoIrisLogicalRelation.v) |
| PICO Iris WP lifting | A first WP-facing theorem should connect Iris weakest preconditions to PICO's `wm_thread_step` | Iris `state_interp` remains abstract through `irisGS`; the lemma specializes generic Iris lifting to PICO primitive steps with no observations or forks | A `wm_thread_step`-based premise, or an existential step witness for NotStuck mode, is sufficient to prove `WP` for `pico_language` expressions | `wp_pico_lift_thread_step`, `wp_pico_lift_thread_step_exists` in [PICOBridge/PicoIrisWP.v](PICOBridge/PicoIrisWP.v) |
| PICO Iris thread safety | Cache-safe PICO threads should expose their one-step cache-history preservation fact to Iris WP continuations | `cache_safe_thread` is wrapped as a pure Iris proposition; `state_interp` is still abstract | The PICO WP lifting rule can pass a pure cache-history preservation implication for every `wm_thread_step` of a cache-safe thread, either from the raw proof or from the named Iris proposition, and can use an existential weak-step witness in `NotStuck` mode | `pico_thread_cache_safeI`, `pico_thread_step_preserves_cacheI`, `pico_thread_cache_safeI_step_preserves_cacheI`, `wp_pico_lift_cache_safe_thread_step`, `wp_pico_lift_cache_safe_thread_stepI`, `wp_pico_lift_cache_safe_thread_step_exists`, `wp_pico_lift_cache_safe_thread_step_existsI` in [PICOBridge/PicoIrisThreadSafety.v](PICOBridge/PicoIrisThreadSafety.v) |
| PICO Iris semantic typing | The logical relation should eventually interpret PICO typing judgments semantically, not only reuse syntactic premises | First-stage semantic typing is a pure Iris proposition combining `stmt_typing` with `cache_safe_stmt` / `cache_safe_thread`, plus rule-shaped introduction lemmas, named literal cache-update and compute/write phase interpretations, and a config-level typed-cache interpretation over `sem_typed_thread_entry` | WP rules can consume a named semantic typing interpretation and obtain cache-history preservation for each PICO step; semantic typed threads/configs transport the cache-history invariant across concrete PICO steps/executions, package config-step interpretation updates, expose post-thread-entry preservation for covered weak steps, provide post-environment-aware sequence residual rules, route literal cache updates through named semantic propositions, expose the config-level iProp as the reusable Prop interpretation, derive post-compute tail thread/config interpretations, a WP tail-step rule, a closed-execution final-read endpoint from compute/write phases, and after-step method-post semantic immutability endpoints that can derive post PICO stability from abstract-field write avoidance, and validate final weak cache reads under either global or closed preservation assumptions, including generic `cache_valid` variants | `pico_sem_typed_stmt_cacheI`, `pico_sem_typed_thread_cacheI_cache_safe`, `pico_sem_typed_thread_cacheI_entry`, `pico_sem_typed_config_cacheI_interp`, `pico_sem_cache_update_sequenceI`, `pico_sem_cache_update_sequence_intro`, `pico_sem_cache_update_sequence_tail_threadI`, `pico_sem_cache_compute_then_write_phasesI`, `cache_compute_then_write_safe_sem_typed_phases_namedI`, `cache_update_sequence_safe_sem_typed_phasesI`, `pico_sem_cache_update_sequence_phasesI`, `pico_sem_cache_compute_then_write_phases_tail_threadI`, `pico_sem_cache_compute_then_write_phases_tail_configI`, `pico_sem_cache_compute_then_write_phases_tail_closed_final_read_validI`, `sem_typed_config_entry_interpretation_final_read_valid_genericI`, `sem_typed_config_entry_interpretation_closed_final_read_valid_genericI`, `sem_typed_config_entry_interpretation_semantic_execution_read_valid_genericI`, `sem_typed_config_entry_interpretation_inv_steps_read_valid_generic`, `sem_typed_state_after_steps_semantic_immutability_method_postI`, `sem_typed_wp_bridge_after_steps_semantic_immutability_method_postI`, `sem_typed_state_after_steps_pico_wm_stable_method_postI`, `sem_typed_wp_bridge_after_steps_pico_wm_stable_method_postI`, `sem_typed_state_after_steps_pico_wm_stable_preserved_method_postI`, `sem_typed_wp_bridge_after_steps_pico_wm_stable_preserved_method_postI`, `wp_pico_lift_cache_update_sequence_to_sem_typed_tail_exists`, `wp_pico_lift_cache_update_sequence_with_sem_typed_tail_exists`, `wp_pico_lift_sem_cache_update_sequence_with_tail_exists`, `wp_pico_sem_cache_update_tail_fldwrite_step_progress`, `wp_pico_lift_sem_cache_update_sequence_full_progress`, `wp_pico_lift_sem_typed_thread_step_exists`, `wp_pico_lift_sem_cache_compute_then_write_tail_step`, `wp_pico_lift_sem_cache_compute_then_write_tail_step_exists`, `wp_pico_lift_sem_cache_update_sequence_with_tail`, `sem_typed_thread_entry`, `sem_typed_thread_entry_assign_int_post`, `sem_typed_thread_entry_field_read_post`, `sem_typed_thread_entry_fldwrite_post`, `sem_typed_thread_entry_seqskip_post`, `sem_typed_thread_entry_seqstep_residual_post`, `sem_typed_thread_entry_seqstep_assign_int_post`, `sem_typed_thread_entry_seqstep_field_read_post`, `sem_typed_thread_entry_seqstep_fldwrite_post`, `sem_typed_config_entry_interpretation_step_update`, `sem_typed_config_entry_interpretation_seqstep_update`, `sem_typed_config_entry_interpretation_closed_final_read_validI`, `pico_sem_typed_config_cacheI_inv_step_update`, `sem_typed_config_entry_interpretation_inv_steps_update`, `sem_typed_config_entry_interpretation_inv_steps_read_valid`, `sem_typed_config_entry_interpretation_semantic_executionI` in [PICOBridge/PicoIrisSemanticTyping.v](PICOBridge/PicoIrisSemanticTyping.v) |
| PICO Iris logical relation facade | The roadmap needs stable logical-relation names before replacing pure semantic typing with ghost-backed interpretation | LR-facing value, environment, expression, thread-step environment, typed-thread environment package, statement, method-body, thread, thread-entry, config, literal cache-update, and compute/write phase predicates currently use first-stage pure interpretations, with explicit `Prop` interpretation names for expression/thread-step/statement/thread/method/config entries | The facade exposes value/environment/expression constructors, bridge lemmas between explicit LR interpretations and the current Iris propositions, value/env elimination lemmas, config-entry/config-interpretation equivalence lemmas, LR-named config safety, semantic execution, final-read, global-prefix, and execution-prefix wrappers, a named thread-step environment predicate with pure interpretation constructors for assignment, field read/write, and sequence steps, typed-thread package elimination for pairing `pico_lr_threadI` with `pico_lr_envI`, typed-thread state-facade and WP-state bridge step transport, interp-backed generic and case-specific thread-step state/env transport, interp-backed WP-state bridge/env transport, a covered-step post predicate and single config closure theorem, covered-step final-read endpoints, post-entry closure final-read endpoints, covered-step state/bridge transport, post-entry state/bridge final-read endpoints, post-thread-entry/config update lemmas for covered weak steps, closed multi-step final-read validity, post-environment-aware sequence residual/config update wrappers, LR-named compute/write phase constructors, tail-thread/config projections, a WP tail-step rule, a closed final-read rule for the tail config, and invariant/state/WP-bridge tail read variants, value subtyping, lookup, local-null extension, assignment-style update, field-write state/env transport, plus WP, semantic execution, allowed-write final-read, state-interpretation transport/state/history/read endpoints under names intended to survive the later ghost-state implementation | `pico_lr_expr_interp`, `pico_lr_thread_step_env_interp`, `pico_lr_thread_step_envI_from_interp`, `pico_lr_assign_int_thread_step_env_interp`, `pico_lr_field_read_thread_step_env_interp`, `pico_lr_fldwrite_thread_step_env_interp`, `pico_lr_seqskip_thread_step_env_interp`, `pico_lr_seqstep_thread_step_env_interp`, `pico_lr_valueI_elim`, `pico_lr_envI_elim`, `pico_lr_exprI_from_interp`, `pico_lr_exprI_interp`, `pico_lr_stmt_interp`, `pico_lr_thread_interp`, `pico_lr_method_body_interp`, `pico_lr_config_entries`, `pico_lr_stmtI_from_interp`, `pico_lr_stmtI_interp`, `pico_lr_threadI_from_interp`, `pico_lr_threadI_interp`, `pico_lr_typed_threadI`, `pico_lr_typed_threadI_intro`, `pico_lr_typed_threadI_elim`, `pico_lr_typed_threadI_thread`, `pico_lr_typed_threadI_env`, `pico_lr_typed_thread_state_env_step_update`, `pico_lr_typed_thread_wp_state_bridge_env_step_update`, `pico_lr_method_bodyI_from_interp`, `pico_lr_method_bodyI_interp`, `pico_lr_configI_from_entries`, `pico_lr_configI_entries`, `pico_lr_config_entries_interp`, `pico_lr_config_interp_entries`, `pico_lr_config_entries_cache_safe_config`, `pico_lr_config_interp_cache_safe_config`, `pico_lr_configI_cache_safe_config`, `pico_lr_config_interp_semantic_cache_safe`, `pico_lr_config_interp_semantic_cache_safeI`, `pico_lr_config_interp_semantic_executionI`, `pico_lr_config_interp_final_read_valid`, `pico_lr_config_interp_final_read_validI`, `pico_lr_config_interp_semantic_execution_read_validI`, `pico_lr_config_prefix_interp`, `pico_lr_config_prefix_interpI`, `pico_lr_config_prefix_interpI_intro`, `pico_lr_config_prefix_interpI_elim`, `pico_lr_config_prefix_interp_semantic_cache_safeI`, `pico_lr_config_prefix_interp_semantic_executionI`, `pico_lr_config_prefix_interp_final_read_validI`, `pico_lr_config_prefix_interp_semantic_execution_read_validI`, `pico_lr_config_execution_prefix_interp`, `pico_lr_config_execution_prefix_interpI`, `pico_lr_config_execution_prefix_interpI_intro`, `pico_lr_config_execution_prefix_interpI_elim`, `pico_lr_config_execution_prefix_from_global_prefix`, `pico_lr_config_execution_prefixI_from_global_prefixI`, `pico_lr_config_execution_prefix_from_closure`, `pico_lr_config_execution_prefixI_from_closureI`, `pico_lr_config_execution_prefix_preserve_cache_history`, `pico_lr_config_execution_prefix_preserve_cache_historyI`, `pico_lr_config_execution_prefix_final_read_valid`, `pico_lr_config_execution_prefix_final_read_validI`, `pico_lr_config_execution_prefix_read_specI`, `pico_lr_config_execution_prefix_read_specI_intro`, `pico_lr_config_execution_prefix_read_specI_elim`, `pico_lr_config_execution_prefix_read_specI_final_read_validI`, `pico_lr_config_execution_prefix_read_specI_from_global_prefixI`, `pico_lr_config_execution_prefix_read_specI_from_closureI`, `pico_lr_config_execution_prefix_read_specI_from_thread_postI`, `pico_lr_config_execution_prefix_read_specI_from_coveredI`, `pico_lr_config_inv_execution_prefix_steps_update`, `pico_lr_config_inv_execution_prefix_steps_read_valid`, `pico_lr_config_inv_alloc_execution_prefix_steps_read_valid`, `pico_lr_config_inv_alloc_execution_prefix_read_specI`, `pico_lr_config_inv_alloc_execution_prefix_read_specI_from_coveredI`, `pico_lr_config_inv_alloc_execution_prefix_read_specI_from_thread_postI`, `pico_lr_config_state_execution_prefix_steps_update`, `pico_lr_config_state_execution_prefix_steps_read_valid`, `pico_lr_config_state_alloc_execution_prefix_steps_read_valid`, `pico_lr_config_state_alloc_execution_prefix_read_specI`, `pico_lr_config_state_alloc_execution_prefix_read_specI_from_coveredI`, `pico_lr_config_state_alloc_execution_prefix_read_specI_from_thread_postI`, `pico_lr_wp_state_bridge_after_execution_prefix_steps`, `pico_lr_wp_state_bridge_after_execution_prefix_steps_read_valid`, `pico_lr_wp_state_bridge_alloc_execution_prefix_steps_read_valid`, `pico_lr_wp_state_bridge_alloc_execution_prefix_read_specI`, `pico_lr_wp_state_bridge_alloc_execution_prefix_read_specI_from_coveredI`, `pico_lr_wp_state_bridge_alloc_execution_prefix_read_specI_from_thread_postI`, `pico_lr_valueI`, `pico_lr_envI`, `pico_lr_exprI`, `pico_lr_thread_step_envI`, `pico_lr_thread_state_env_step_update_from_interp`, `pico_lr_thread_wp_state_bridge_env_step_update_from_interp`, `pico_lr_assign_int_thread_step_envI`, `pico_lr_field_read_thread_step_envI`, `pico_lr_fldwrite_thread_step_envI`, `pico_lr_seqskip_thread_step_envI`, `pico_lr_seqstep_thread_step_envI`, `pico_lr_cache_update_sequenceI`, `pico_lr_cache_update_sequence_intro`, `pico_lr_cache_update_sequence_tail_threadI`, `pico_lr_cache_compute_then_write_phasesI`, `pico_lr_cache_compute_then_write_phases_intro`, `pico_lr_cache_update_sequence_phasesI`, `pico_lr_cache_compute_then_write_phases_elim`, `pico_lr_cache_compute_then_write_phases_tail_threadI`, `pico_lr_cache_compute_then_write_phases_tail_configI`, `pico_lr_cache_compute_then_write_phases_tail_closed_final_read_validI`, `pico_lr_cache_compute_then_write_phases_tail_inv_closure_read_valid`, `pico_lr_cache_compute_then_write_phases_tail_state_closure_read_valid`, `pico_lr_cache_compute_then_write_phases_tail_wp_bridge_closure_read_valid`, `wp_pico_lr_cache_compute_then_write_tail_step`, `wp_pico_lr_sem_cache_update_sequence_with_tail`, `pico_lr_covered_thread_step_post`, `pico_lr_covered_thread_step_post_entry`, `pico_lr_config_covered_step_update`, `pico_lr_config_covered_steps_read_validI`, `pico_lr_covered_steps_read_valid_fupd`, `pico_lr_config_thread_post_steps_read_validI`, `pico_lr_config_thread_post_steps_preserve_cache_history`, `pico_lr_config_covered_steps_preserve_cache_history`, `pico_lr_config_state_covered_steps_update`, `pico_lr_config_state_covered_steps_read_valid`, `pico_lr_config_state_alloc_covered_steps_read_valid`, `pico_lr_wp_state_bridge_after_covered_steps`, `pico_lr_wp_state_bridge_after_covered_steps_read_valid`, `pico_lr_wp_state_bridge_alloc_covered_steps_read_valid`, `pico_lr_config_state_thread_post_steps_read_valid`, `pico_lr_config_state_alloc_thread_post_steps_read_valid`, `pico_lr_wp_state_bridge_after_thread_post_steps_read_valid`, `pico_lr_wp_state_bridge_alloc_thread_post_steps_read_valid`, `pico_lr_thread_entry_assign_int_post`, `pico_lr_thread_entry_field_read_post`, `pico_lr_thread_entry_fldwrite_post`, `pico_lr_thread_entry_seqskip_post`, `pico_lr_thread_entry_seqstep_residual_post`, `pico_lr_thread_entry_seqstep_assign_int_post`, `pico_lr_thread_entry_seqstep_field_read_post`, `pico_lr_thread_entry_seqstep_fldwrite_post`, `pico_lr_config_assign_int_step_update`, `pico_lr_config_field_read_step_update`, `pico_lr_config_fldwrite_step_update`, `pico_lr_config_seqskip_step_update`, `pico_lr_config_seqstep_step_update`, `pico_lr_config_seqstep_residual_step_update`, `pico_lr_config_seqstep_assign_int_step_update`, `pico_lr_config_seqstep_field_read_step_update`, `pico_lr_config_seqstep_fldwrite_step_update`, `pico_lr_thread_state_env_step_update`, `pico_lr_thread_wp_state_bridge_env_step_update`, `pico_lr_assign_int_wp_state_bridge_env_step_update`, `pico_lr_field_read_wp_state_bridge_env_step_update`, `pico_lr_fldwrite_wp_state_bridge_env_step_update`, `pico_lr_seqskip_wp_state_bridge_env_step_update`, `pico_lr_seqstep_wp_state_bridge_env_step_update`, `pico_lr_config_step_update`, `pico_lr_config_closed_steps_read_validI`, `pico_lr_assign_int_state_env_step_update`, `pico_lr_field_read_state_env_step_update`, `pico_lr_fldwrite_generic_state_env_step_update`, `pico_lr_seqskip_state_env_step_update`, `pico_lr_seqstep_state_env_step_update`, `pico_lr_objectI`, `pico_lr_valueI_subtype`, `pico_lr_envI_lookup`, `pico_lr_envI_local_null`, `pico_lr_envI_update`, `pico_lr_envI_update_subtype`, `pico_lr_int_exprI`, `pico_lr_var_exprI`, `pico_lr_assign_int_env_update`, `pico_lr_assign_expr_env_update`, `pico_lr_field_read_assign_env_update`, `pico_lr_fldwrite_state_env_step_update`, `pico_lr_stmtI`, `pico_lr_method_bodyI`, `pico_lr_threadI`, `pico_lr_config_allowed_steps_read_validI`, `pico_lr_thread_state_step_update`, `pico_lr_thread_wp_state_bridge_step_update`, `pico_lr_fldwrite_wp_state_bridge_step_update`, `pico_lr_wp_state_bridge_after_steps`, `pico_lr_wp_state_bridge_after_steps_read_valid`, `pico_lr_wp_state_bridge_alloc_steps_read_valid`, `pico_lr_wp_state_bridge_alloc_steps_read_unknown_or_derived`, `pico_lr_wp_state_bridge_alloc_closed_steps_read_unknown_or_derived`, `pico_lr_wp_state_bridge_alloc_closure_steps_read_unknown_or_derived`, `pico_lr_cache_update_selected_first_inv_final_read_validI`, `pico_lr_config_state_steps_update`, `pico_lr_config_state_steps_read_valid`, `wp_pico_lr_cache_update_sequence_with_tail` in [PICOBridge/PicoIrisLogicalRelation.v](PICOBridge/PicoIrisLogicalRelation.v) |
| PICO Iris LR selected-step bridge | Scheduled LR configs should reuse the selected thread interpretation for one-step state transport | `pico_lr_configI` can recover the selected `pico_lr_threadI` and feed existing per-thread state/WP bridge transport | A selected thread step updates either `pico_cache_state_interp` or `pico_wp_state_cfg_bridge` while returning the selected thread interpretation, with env-aware package variants for matched step-env/env resources, bundled typed-thread resources, named selected-config resources, named result resources, raw compatibility views, and pure step-env interpretations | `pico_lr_configI_nth_state_step_update`, `pico_lr_configI_nth_wp_state_bridge_step_update`, `pico_lr_configI_nth_state_env_step_update_package`, `pico_lr_configI_nth_wp_state_bridge_env_step_update_package`, `pico_lr_thread_step_env_package_from_interp`, `pico_lr_typed_thread_step_envI`, `pico_lr_typed_thread_step_envI_intro`, `pico_lr_typed_thread_step_envI_elim`, `pico_lr_typed_thread_step_envI_from_interp`, `pico_lr_typed_thread_step_resultI`, `pico_lr_typed_thread_step_resultI_intro`, `pico_lr_typed_thread_step_resultI_elim`, `pico_lr_typed_thread_step_resultI_thread`, `pico_lr_typed_thread_step_resultI_env`, `pico_lr_config_nth_typed_thread_step_envI`, `pico_lr_config_nth_typed_thread_step_envI_intro`, `pico_lr_config_nth_typed_thread_step_envI_from_interp`, `pico_lr_config_nth_typed_thread_step_envI_from_step_env`, `pico_lr_config_nth_typed_thread_step_envI_from_thread_env_interp`, `pico_lr_config_nth_typed_thread_step_envI_from_thread_step_env_package`, `pico_lr_config_nth_typed_thread_step_envI_from_interp_package`, `pico_lr_config_nth_typed_thread_step_envI_elim`, `pico_lr_config_nth_typed_thread_step_envI_configI`, `pico_lr_config_nth_typed_thread_step_envI_nth`, `pico_lr_config_nth_typed_thread_step_envI_typed_step_envI`, `pico_lr_config_nth_typed_thread_step_envI_raw_step_envI`, `pico_lr_config_nth_typed_thread_step_resultI`, `pico_lr_config_nth_typed_thread_step_resultI_intro`, `pico_lr_config_nth_typed_thread_step_resultI_elim`, `pico_lr_config_nth_typed_thread_step_resultI_nth`, `pico_lr_config_nth_typed_thread_step_resultI_typed_resultI`, `pico_lr_config_nth_typed_thread_step_resultI_raw`, `pico_lr_config_nth_typed_thread_step_envI_thread_entryI`, `pico_lr_config_nth_typed_thread_step_envI_thread_cache_safeI`, `pico_lr_config_nth_typed_thread_step_envI_state_update_result`, `pico_lr_config_nth_typed_thread_step_envI_state_update_result_package`, `pico_lr_config_nth_typed_thread_step_resultI_state_update_raw`, `pico_lr_config_nth_typed_thread_step_resultI_state_read_valid`, `pico_lr_config_nth_typed_thread_step_resultI_state_read_unknown_or_derived`, `pico_lr_config_nth_typed_thread_step_envI_state_update_raw`, `pico_lr_config_nth_typed_thread_step_envI_wp_state_bridge_update_result`, `pico_lr_config_nth_typed_thread_step_envI_wp_state_bridge_update_result_package`, `pico_lr_config_nth_typed_thread_step_resultI_wp_state_bridge_update_raw`, `pico_lr_config_nth_typed_thread_step_resultI_wp_state_bridge_read_valid`, `pico_lr_config_nth_typed_thread_step_resultI_wp_state_bridge_read_unknown_or_derived`, `pico_lr_config_nth_typed_thread_step_envI_wp_state_bridge_update_raw`, `pico_lr_typed_thread_step_env_state_update`, `pico_lr_typed_thread_step_env_state_update_result`, `pico_lr_typed_thread_step_env_wp_state_bridge_update`, `pico_lr_typed_thread_step_env_wp_state_bridge_update_result`, `pico_lr_typed_thread_step_env_package_from_interp`, `pico_lr_configI_nth_typed_state_env_step_update_package`, `pico_lr_configI_nth_typed_state_env_step_update_package_result`, `pico_lr_configI_nth_typed_state_env_step_update_from_interp_package`, `pico_lr_configI_nth_typed_state_env_step_update_from_interp_package_result`, `pico_lr_configI_nth_typed_state_env_step_update_result_raw`, `pico_lr_configI_nth_typed_wp_state_bridge_env_step_update_package`, `pico_lr_configI_nth_typed_wp_state_bridge_env_step_update_package_result`, `pico_lr_configI_nth_typed_wp_state_bridge_env_step_update_from_interp_package`, `pico_lr_configI_nth_typed_wp_state_bridge_env_step_update_from_interp_package_result`, `pico_lr_configI_nth_typed_wp_state_bridge_env_step_update_result_raw`, `pico_lr_configI_nth_state_env_step_update_from_interp_package`, `pico_lr_configI_nth_wp_state_bridge_env_step_update_from_interp_package`, `pico_lr_configI_nth_state_env_step_update_from_interp_package_via_step_env`, `pico_lr_configI_nth_wp_state_bridge_env_step_update_from_interp_package_via_step_env` in [PICOBridge/PicoIrisLogicalRelation.v](PICOBridge/PicoIrisLogicalRelation.v) |
| Derived cache, SC concurrency | Thread-pool execution uses one shared heap and interleaves one thread step at a time | Every heap transition is cache-safe for the target derived cache | The shared derived-cache invariant is preserved across all interleavings | `concurrent_steps_preserve_cache_state` in [PICOBridge/ConcurrentPico.v](PICOBridge/ConcurrentPico.v) |
| Derived cache, SC accepted/rejected examples | SC cache writes may update only the assignable derived cache slot, not final abstract fields | Accepted transitions are stutters or derived-cache writes; rejected transitions change final-field reads | Accepted examples preserve the cache protocol; final-field changes are rejected | `simple_sc_accepts_cache_write`, `simple_sc_rejects_final_field_change` in [Examples/ConcurrentPicoExamples.v](Examples/ConcurrentPicoExamples.v) |
| Derived cache, weak observations | Weak executions expose the abstract-field values observed by a cache computation | A weak cache-write event is accepted only when its observed final-field snapshot is coherent with the heap at commit time | Coherent weak cache writes preserve the derived-cache protocol | `weak_accepts_preserves_protocol`, `weak_execution_preserves_cache_state_for_target` in [PICOBridge/WeakPico.v](PICOBridge/WeakPico.v) |
| Derived cache, weak rejected examples | Mixed or stale observations can compute a cache value that does not match the actual final fields | Candidate weak event observes values inconsistent with the heap snapshot at commit time | The candidate event/execution is rejected | `simple_weak_rejects_incoherent_cache_write`, `pair_weak_rejects_mixed_snapshot_execution` in [Examples/WeakPicoExamples.v](Examples/WeakPicoExamples.v) |
| Iris comparison model | A String-like derived hash cache is modeled in Iris heap_lang with atomic heap operations and fork/join | `ImmString` invariant protects immutable payload and mutable cache fields; concurrency is heap_lang SC interleaving, not Java weak memory | Two joined concurrent `hashCode` calls both return the deterministic hash and preserve the invariant | `hashCode_spawn2_join_spec` in [Examples/StringCacheIris.v](Examples/StringCacheIris.v) |
| Bridge summary | The artifact separates sequential PICO, SC PICO concurrency, weak-observation PICO, and Iris comparison results | Each model has an explicit theorem boundary and does not silently imply a stronger memory model | Main result shapes are re-exported as compact entry points | `pico_sequential_cache_result_from_eval`, `pico_concurrent_cache_result_from_steps`, `pico_weak_cache_result_from_coherent_execution`, `iris_sc_concurrent_hash_result_from_spawn` in [PICOBridge/PicoIrisCacheBridge.v](PICOBridge/PicoIrisCacheBridge.v) |
| Proof integrity | No axioms/admitted proof gaps in submitted sources | Artifact sources exclude forbidden `Axiom`, `Admitted`, and `admit`, except bundled `LibTactics.v` support library | Mechanical checker passes | [scripts/check-no-axioms-admits.py](scripts/check-no-axioms-admits.py) via `make check` |

The semantic typing layer also exposes named cache-update execution/read
wrappers:
`pico_sem_cache_update_sequence_tail_pool_cache_safe_executionI`,
`pico_sem_cache_update_sequence_selected_first_execution_safeI`, and
`pico_sem_cache_update_sequence_selected_first_final_read_validI`.
The concrete literal update first-step boundary also exposes progress facts:
`cache_update_sequence_safe_first_step_exists`,
`cache_update_sequence_safe_first_step_not_stuck`,
`pico_sem_cache_update_sequence_first_step_existsI`,
`pico_sem_cache_update_sequence_not_stuckI`,
`pico_lr_cache_update_sequence_first_step_existsI`, and
`pico_lr_cache_update_sequence_not_stuckI`.
The LR step-environment layer exposes matching operation-level progress
wrappers:
`pico_lr_assign_int_not_stuckI`, `pico_lr_field_read_not_stuckI`,
`pico_lr_fldwrite_not_stuckI`, `pico_lr_seqskip_not_stuckI`, and
`pico_lr_seqstep_not_stuckI`.
For state-independent progress cases, the LR WP layer also discharges the
`NotStuck` witness directly via `wp_pico_lr_assign_int_step_progress` and
`wp_pico_lr_seqskip_step_progress`.
For state-dependent read/write cases, `wp_pico_lr_field_read_step_progress`
and `wp_pico_lr_fldwrite_step_progress` discharge progress from read/write
witnesses supplied after `state_interp` exposes the current weak state.
For compositional sequences, `wp_pico_lr_seqstep_step_progress` does the same
from a first-component weak-step witness.
The semantic layer also exposes the literal cache-update tail write as
`wp_pico_sem_cache_update_tail_fldwrite_step_progress` and the full
selected-assignment-plus-tail path as
`wp_pico_lift_sem_cache_update_sequence_full_progress`.
The LR facade mirrors that route through
`wp_pico_lr_cache_update_tail_fldwrite_step_progress` and
`wp_pico_lr_sem_cache_update_sequence_full_progress`, delegating the proof to
the semantic WP boundary while preserving LR-facing names.
It also packages the literal post-compute tail execution boundary as
`pico_sem_cache_update_sequence_tail_execution_specI`, with final
cache-history preservation and `wm_semantic_cache_safe_executionI` endpoints.
The read-specific wrapper `pico_sem_cache_update_sequence_tail_read_specI`
adds the final weak read and derives final-read validity from that execution
spec.  The
semantic closure evidence `sem_typed_config_step_closureI` and
`sem_typed_thread_post_stepsI` let callers build that spec without passing a
raw closure function.  The related `sem_typed_covered_stepsI` names per-thread
semantic preservation evidence and also constructs the same tail read spec.
Semantic thread invariant transport also routes through
`pico_sem_typed_thread_cacheI_cache_safe`.

The LR facade exposes `pico_lr_thread_cache_safeI`, `pico_lr_threadI_entry`,
and `pico_lr_configI_interp`, connecting `pico_lr_threadI` to the WP-facing
thread-safety proposition and thread-entry interpretation, and
`pico_lr_configI` to the config-level interpretation.
The compute/write phase tail read boundary also has allocation-to-read wrappers
for the invariant, state interpretation, and WP-state bridge:
`pico_lr_cache_compute_then_write_phases_tail_inv_alloc_closure_read_valid`,
`pico_lr_cache_compute_then_write_phases_tail_state_alloc_closure_read_valid`,
and
`pico_lr_cache_compute_then_write_phases_tail_wp_bridge_alloc_closure_read_valid`.
The direct invariant/state/WP-bridge closure forms also expose generic
`cache_valid` endpoints:
`pico_lr_cache_compute_then_write_phases_tail_inv_closure_read_valid_generic`,
`pico_lr_cache_compute_then_write_phases_tail_state_closure_read_valid_generic`,
and
`pico_lr_cache_compute_then_write_phases_tail_wp_bridge_closure_read_valid_generic`.
The same phase-tail boundary also has final-resource transport/allocation
wrappers:
`pico_lr_cache_compute_then_write_phases_tail_inv_closure_update`,
`pico_lr_cache_compute_then_write_phases_tail_state_closure_update`,
`pico_lr_cache_compute_then_write_phases_tail_wp_bridge_closure_update`,
`pico_lr_cache_compute_then_write_phases_tail_inv_alloc_closure_update`,
`pico_lr_cache_compute_then_write_phases_tail_state_alloc_closure_update`, and
`pico_lr_cache_compute_then_write_phases_tail_wp_bridge_alloc_closure_update`.
Combined allocation/update-read variants return the final resource together
with the read-validity fact:
`pico_lr_cache_compute_then_write_phases_tail_inv_alloc_closure_update_read_valid`,
`pico_lr_cache_compute_then_write_phases_tail_state_alloc_closure_update_read_valid`,
and
`pico_lr_cache_compute_then_write_phases_tail_wp_bridge_alloc_closure_update_read_valid`.
The general compute/write phase tail now also has named semantic and LR
execution/read specs:
`pico_sem_cache_compute_then_write_phases_tail_execution_specI`,
`pico_sem_cache_compute_then_write_phases_tail_read_specI`,
`pico_lr_cache_compute_then_write_phases_tail_execution_specI`, and
`pico_lr_cache_compute_then_write_phases_tail_read_specI`.  These package the
post-compute cache-write execution boundary before specializing to the literal
cache-update sequence.  Direct LR resource endpoints consume those specs:
`pico_lr_cache_compute_then_write_phases_tail_inv_alloc_execution_specI`,
`pico_lr_cache_compute_then_write_phases_tail_state_alloc_execution_specI`,
`pico_lr_cache_compute_then_write_phases_tail_wp_bridge_alloc_execution_specI`,
`pico_lr_cache_compute_then_write_phases_tail_inv_alloc_read_specI`,
`pico_lr_cache_compute_then_write_phases_tail_state_alloc_read_specI`, and
`pico_lr_cache_compute_then_write_phases_tail_wp_bridge_alloc_read_specI`.
Each also has a `from_semI` wrapper, so semantic phase specs can allocate the
LR invariant, state interpretation, or WP-state bridge without manual
conversion.
Literal cache-update sequence wrappers expose the same combined endpoint from
`pico_lr_cache_update_sequenceI`:
`pico_lr_cache_update_sequence_tail_inv_alloc_closure_update_read_valid`,
`pico_lr_cache_update_sequence_tail_state_alloc_closure_update_read_valid`,
and
`pico_lr_cache_update_sequence_tail_wp_bridge_alloc_closure_update_read_valid`.
Thread-post and covered-step variants derive the closure internally from
`pico_lr_thread_post_stepsI` or `pico_lr_covered_stepsI` for the same three
resource layers.
The LR tail boundary now mirrors the semantic execution/read split.  The
execution-only spec `pico_lr_cache_update_sequence_tail_execution_specI`
packages the tail execution, initial cache-history fact, literal update
interpretation, and closure evidence, with final-history and semantic-execution
endpoints plus semantic-to-LR constructors from the semantic execution spec,
semantic thread-post evidence, and semantic covered-step evidence.  The bundled
tail read spec `pico_lr_cache_update_sequence_tail_read_specI` layers the final
weak read on top, with final-read and invariant/state/WP-bridge allocation
endpoints.  It can also be constructed from `pico_lr_thread_post_stepsI` or
`pico_lr_covered_stepsI` directly, and has direct resource/read endpoints for
those two evidence forms.  The execution spec also has direct final-resource
endpoints:
`pico_lr_cache_update_sequence_tail_inv_alloc_execution_specI`,
`pico_lr_cache_update_sequence_tail_state_alloc_execution_specI`, and
`pico_lr_cache_update_sequence_tail_wp_bridge_alloc_execution_specI`, with
matching variants from the semantic execution spec, semantic thread-post
evidence, and semantic covered-step evidence.
The LR bridge
`pico_lr_cache_update_sequence_tail_execution_specI_phaseI` and the semantic
bridge `pico_sem_cache_update_sequence_tail_execution_specI_phaseI` make the
literal update specs explicitly specialize the general compute/write phase
specs; the matching read bridges do the same for final weak reads, and the
literal read resource endpoints now delegate through the phase read-spec
resource endpoints.  The LR
bridge
`pico_lr_cache_update_sequence_tail_read_specI_from_semI` lifts the semantic
tail read spec into the LR-facing read spec, and direct `from_semI`
resource/read endpoints allocate the final invariant, state interpretation, or
WP-state bridge from that semantic spec.  Semantic thread-post evidence also
has direct LR resource/read endpoints through
`pico_lr_cache_update_sequence_tail_read_specI_from_sem_thread_postI`, and
semantic covered-step evidence has the parallel `from_sem_coveredI` endpoints.
The LR tail read spec mirrors the semantic final-history and semantic-execution
endpoints, and LR exposes direct final-history/semantic-execution wrappers from
the semantic execution spec.
Thread-step state and WP-state bridge transport in the LR facade use that
adapter instead of unfolding the LR thread predicate directly.
Scheduled typed-thread step results also expose generic cache-read endpoints
through
`pico_lr_config_nth_typed_thread_step_resultI_state_read_valid_generic` and
`pico_lr_config_nth_typed_thread_step_resultI_wp_state_bridge_read_valid_generic`,
so selected-step clients can conclude `cache_valid` directly from the post-step
state or WP bridge resource.
Config-level closure endpoints can now also consume `pico_lr_configI`
directly via `pico_lr_configI_closure_steps_read_validI`,
`pico_lr_configI_state_closure_steps_update`, and
`pico_lr_configI_state_closure_steps_read_valid`, plus the WP-state bridge
wrappers `pico_lr_configI_wp_state_bridge_after_closure_steps`,
`pico_lr_configI_wp_state_bridge_after_closure_steps_read_valid`, and
`pico_lr_configI_wp_state_bridge_alloc_closure_steps_read_valid`.  The
allocation-to-read closure wrappers also expose explicit unknown-or-derived
read-shape variants that consume `pico_lr_configI` directly:
`pico_lr_configI_state_alloc_closure_steps_read_unknown_or_derived` and
`pico_lr_configI_wp_state_bridge_alloc_closure_steps_read_unknown_or_derived`.
The literal cache-update execution facade reuses those variants through
selected-first, semantic selected-first, and execution-level state/WP allocation
wrappers, ending at
`pico_lr_cache_update_execution_state_alloc_read_unknown_or_derived` and
`pico_lr_cache_update_execution_wp_bridge_alloc_read_unknown_or_derived`, with
parallel `closedI`, `evidenceI`, and `specI` package wrappers for the same
state/WP allocation read shape.  The `specI` layer also has after-execution
state/WP allocation variants that return the final transported resource
together with the explicit unknown-or-derived read result, with `from_safe`
closure, thread-post, and covered-step constructors forwarding to that packaged
endpoint.
The invariant-backed execution facade now also exposes
`pico_lr_cache_update_execution_inv_read_unknown_or_derived` and
`pico_lr_cache_update_execution_inv_alloc_read_unknown_or_derived`.
The LR facade also exposes closed-execution state and WP-bridge endpoints:
`pico_lr_config_closed_steps_preserve_cache_history`,
`pico_lr_config_state_closed_steps_update`,
`pico_lr_config_state_closed_steps_read_valid`,
`pico_lr_config_state_alloc_closed_steps_read_valid`, `pico_lr_config_state_alloc_steps_read_unknown_or_derived`, `pico_lr_config_state_alloc_closed_steps_read_unknown_or_derived`, `pico_lr_config_state_alloc_closure_steps_read_unknown_or_derived`,
`pico_lr_wp_state_bridge_after_closed_steps`,
`pico_lr_wp_state_bridge_after_closed_steps_read_valid`, and
`pico_lr_wp_state_bridge_alloc_closed_steps_read_valid`.
The named closure contract `pico_lr_config_step_closure` has adapters from
post-thread-entry and covered-step evidence, plus pure, state-facade, and
WP-state bridge wrappers that consume the named closure directly.
The literal cache-update one-thread/config step-to-tail and invariant-backed
selected-first read endpoints also have variants consuming
`pico_lr_cache_update_sequenceI`.
The literal selected-first cache-update path also has closure-based execution,
final-read, existing state/WP bridge, state-facade allocation, and WP-state
bridge allocation endpoints.
Those selected-first endpoints also have `pico_lr_configI`-consuming variants,
so callers can keep both the config interpretation and cache-update facts at
the named Iris proposition boundary.
The selected-first closure execution/read endpoints also have semantic/LR
variants that consume `pico_lr_cache_update_sequenceI` directly, plus combined
variants consuming both `pico_lr_cache_update_sequenceI` and `pico_lr_configI`
across existing-resource and allocation-to-read paths.
Stable `pico_lr_cache_update_execution_*` facade lemmas expose that selected
first execution path under shorter execution-level names.
The `pico_lr_cache_update_execution_selectedI_*` variants also consume the
selected-first execution evidence as `pico_lr_cache_update_selected_first_executionI`.
The matching `pico_lr_cache_update_execution_closedI_*` variants consume the
named closure proposition `pico_lr_config_step_closureI`.
The `pico_lr_cache_update_execution_coveredI_*` variants derive that closure
from named covered-step evidence `pico_lr_covered_stepsI`.
The `pico_lr_cache_update_execution_thread_postI_*` variants do the same from
named post-thread-entry evidence `pico_lr_thread_post_stepsI`.
The `pico_lr_cache_update_execution_evidenceI_*` variants consume a bundled
selected-execution plus closure evidence proposition, including invariant/state/WP
allocation-to-read endpoints.
The `pico_lr_cache_update_execution_specI_*` variants consume a single
caller-facing spec proposition that also bundles the cache-update
interpretation, config interpretation, cache-history state, and selected slot.
That spec can be constructed from explicit closure, covered-step evidence, or
post-thread-entry evidence.
The `pico_lr_cache_update_execution_specI_from_safe_*` constructors also build
the spec directly from the cache-update safety record plus selected execution
and initial history facts.
The spec also has invariant allocation-to-read, spec-preserving invariant transport,
and allocation lemmas for `pico_cache_state_interp` and `pico_wp_state_cfg_bridge`,
preserving the spec while installing ghost-backed state resources.
It also transports those state resources to the selected execution's final
configuration while preserving the same spec.
Direct allocation-to-final-resource variants combine those two steps for the
invariant, state facade, and WP-state bridge.
Combined final-resource/read-validity variants also return the final resource
and the `derived_cache_msg_ok` fact together for all three resource layers.
Those spec read-validity endpoints and all three from-safe evidence paths
(closure, post-thread-entry, and covered-step) now also have generic
`cache_valid` variants, so callers using the bundled execution spec can stay
inside the generic cache-protocol story.
The same final-resource/read boundary has `from_safe_*` variants for explicit
closure, covered-step evidence, and post-thread-entry evidence.
The selected-first closure layer also exposes direct invariant-backed
read-validity and final-invariant transport endpoints, with semantic/configI
wrappers that consume the named cache-update and config interpretations.
Short execution-facade names now expose the same invariant read and transport
boundary for raw closure evidence, `pico_lr_config_step_closureI`,
covered-step evidence, post-thread-entry evidence, selected-execution evidence,
and bundled execution evidence.
The direct `closedI`, `coveredI`, and `thread_postI` read-validity facades now
also expose generic `cache_valid` variants for final reads, existing
invariant/state/WP resources, and allocation-to-read paths.
The semantic selected-first layer has matching generic closure/configI
read-validity wrappers, including existing-resource and allocation-to-read
forms.
The spec and from-safe constructor layers expose direct existing-invariant read
endpoints, existing-invariant transport/read endpoints, and allocation-based
final-resource endpoints with and without read-validity payloads.
The post-first-step tail-pool phase exposes matching closure-based final-read,
existing invariant/state/WP bridge, invariant/state-facade allocation, and
WP-state bridge allocation endpoints, plus final-invariant transport.
Those tail-pool endpoints also have semantic/LR variants that consume
`pico_lr_cache_update_sequenceI`, plus combined variants consuming both
`pico_lr_cache_update_sequenceI` and `pico_lr_configI` across invariant,
state-facade, and WP-state bridge packages, including invariant update endpoints.
The read-validity variants at each of those tail-pool layers now have generic
`cache_valid` forms, so callers no longer have to pass through the older
`derived_cache_msg_ok` conclusion to use the generic protocol story.
The embedded first step of the literal update sequence is also packaged as an
LR config bridge for arbitrary thread pools, with invariant, state-facade, and
WP-state bridge transport variants.
The embedded first-step bridge also has semantic/LR variants that consume
`pico_lr_cache_update_sequenceI`, plus combined variants consuming both
`pico_lr_cache_update_sequenceI` and `pico_lr_configI`.

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
  is coherent.  `Examples/StringCacheIris.v` is an Iris/heap_lang comparison model, not
  a replacement for the PICO semantics.
- The next weak-memory layer should use field-addressed histories from
  `PICOBridge/PicoMemoryModel.v`.  The existing deterministic `eval_stmt` semantics stays
  as the sequential source semantics.

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
