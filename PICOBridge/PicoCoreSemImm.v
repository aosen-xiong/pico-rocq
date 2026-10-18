From Stdlib Require Import List.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping Bigstep.
Require Import Core.GenericCacheProtocol.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoCoreLanguage
  PICOBridge.PicoCoreInvariant.

(** * Semantic Immutability Providers for the Core Machine

    A provider connects one object's representation in the core machine to a
    generic cache protocol: an adapter maps concrete field addresses and
    values to protocol fields and values, and an instantiation supplies the
    state invariant together with its preservation by unrelated writes, valid
    cache writes and allocation. *)

Section pico_core_cache_adapter.
  Context {AbsVal : Type}.
  Context (P : CacheProtocol AbsVal).

(** Adapter from concrete PICO field addresses and values to a generic cache
    protocol.  The LR keeps this explicit because the generic cache theorem is
    intentionally independent of PICO's concrete field identifiers and value
    syntax. *)
  Record PicoCoreCacheAdapter : Type := {
    pico_core_cache_field :
      FieldAddr -> option (cache_field P);
    pico_core_cache_value :
      forall k : cache_field P, Syntax.value -> option (cache_val P k)
  }.

  Definition PicoCoreCacheReadStep
      (A : PicoCoreCacheAdapter)
      (snap : CacheHistorySnapshot P)
      (addr : FieldAddr) (v : Syntax.value) : Prop :=
    exists k (cv : cache_val P k),
      pico_core_cache_field A addr = Some k /\
      pico_core_cache_value A k v = Some cv /\
      CacheReadStep P snap k cv.

  Definition PicoCoreCacheWriteStep
      (A : PicoCoreCacheAdapter)
      (a : AbsVal)
      (snap snap' : CacheHistorySnapshot P)
      (addr : FieldAddr) (v : Syntax.value) : Prop :=
    exists k (cv : cache_val P k),
      pico_core_cache_field A addr = Some k /\
      pico_core_cache_value A k v = Some cv /\
      CacheWriteStep P a snap snap' k cv.
End pico_core_cache_adapter.

Section pico_core_semimm_instantiation.
  Context `{Hmem : CacheMemoryModel}.
  Context {AbsVal Obj : Type}.
  Context (P : CacheProtocol AbsVal).
  Context (Stable : StableAbs Obj AbsVal).
  Context (a : AbsVal).
  Context (A : PicoCoreCacheAdapter P).

  (** A semantic object protocol is an instantiation boundary, not a theorem
      derived from arbitrary PICO typing.  A client supplies the abstraction
      function, identifies its cache fields, and proves that the concrete
      field histories and writes implement that protocol.  The LR below then
      derives execution safety from source typing *relative to this
      instantiation*.

      Ordinary field typing remains the responsibility of the resource LR.
      This provider justifies mapped cache observations through
      [pcsi_cache_history_covers].  Publication is derived from protocol
      validity by [cache_valid_published]. *)
  Record PicoCoreSemImmInstantiation : Type := {
    (** Concrete states representing this object/protocol instance.  The
        semantic provider need only describe reachable states satisfying this
        invariant, not arbitrary PICO heaps and weak memories. *)
    pcsi_state_inv : pico_core_state -> Prop;
    pcsi_object : pico_core_state -> Obj;
    pcsi_snapshot : pico_core_state -> CacheHistorySnapshot P;
    pcsi_abstract_field : FieldAddr -> Prop;

    pcsi_stable : forall state,
      pcsi_state_inv state ->
      Stable (pcsi_object state) a;

    (** Every concrete complete value in a mapped cache-field history occurs
        in the protocol snapshot after conversion to that field's cache value.
        Together with [wm_read_from_history], this derives the cache-read
        bridge used by [SemImmI]. *)
    pcsi_cache_history_covers :
      forall state addr k (v : Syntax.value),
        pcsi_state_inv state ->
        pico_core_cache_field P A addr = Some k ->
        List.In v (values_written_to (pcs_weak state) addr) ->
        exists cv : cache_val P k,
          pico_core_cache_value P A k v = Some cv /\
          List.In cv (pcsi_snapshot state k);

    pcsi_unrelated_write_effect :
      forall h h' sigma sigma' V V' loc f v,
        pcsi_state_inv (mkPicoCoreState h sigma) ->
        h' = update_field h loc f v ->
        wm_write sigma sigma' V V' (loc, f) v ->
        pico_core_cache_field P A (loc, f) = None ->
        ~ pcsi_abstract_field (loc, f) ->
        let before := mkPicoCoreState h sigma in
        let after := mkPicoCoreState h' sigma' in
        pcsi_object after = pcsi_object before /\
        pcsi_snapshot after = pcsi_snapshot before /\
        pcsi_state_inv after;

    pcsi_valid_cache_write_effect :
      forall h h' sigma sigma' V V' loc f v k
        (cv : cache_val P k),
        pcsi_state_inv (mkPicoCoreState h sigma) ->
        h' = update_field h loc f v ->
        wm_write sigma sigma' V V' (loc, f) v ->
        pico_core_cache_field P A (loc, f) = Some k ->
        pico_core_cache_value P A k v = Some cv ->
        cache_valid P a k cv ->
        let before := mkPicoCoreState h sigma in
        let after := mkPicoCoreState h' sigma' in
        PicoCoreCacheWriteStep P A a
          (pcsi_snapshot before) (pcsi_snapshot after) (loc, f) v /\
        pcsi_state_inv after;

    pcsi_alloc_unchanged :
      forall h sigma o V,
        pcsi_state_inv (mkPicoCoreState h sigma) ->
        let before := mkPicoCoreState h sigma in
        let after := mkPicoCoreState
          (h ++ [o]) (pico_core_alloc_weak sigma o V) in
        pcsi_object after = pcsi_object before /\
        pcsi_snapshot after = pcsi_snapshot before /\
        pcsi_state_inv after
  }.

  Lemma pico_core_semimm_cache_read_from_history :
    forall M state V addr v V' k,
      pcsi_state_inv M state ->
      wm_read (pcs_weak state) V addr v V' ->
      pico_core_cache_field P A addr = Some k ->
      PicoCoreCacheReadStep P A (pcsi_snapshot M state) addr v.
  Proof.
    intros M state V addr v V' k Hstate Hread Hfield.
    destruct (wm_read_from_history _ _ _ _ _ Hread)
      as (msg & Hmessage & Hvalue).
    subst v.
    assert (Hwritten :
      List.In (msg_val msg) (values_written_to (pcs_weak state) addr)).
    {
      unfold values_written_to.
      eapply in_map.
      exact Hmessage.
    }
    destruct
      (pcsi_cache_history_covers M state addr k (msg_val msg)
        Hstate Hfield Hwritten)
      as (cv & Hconvert & Hsnapshot).
    exists k, cv.
    repeat split; assumption.
  Qed.
End pico_core_semimm_instantiation.

(** ** Method contracts

    A semantic method contract states a precondition on the entry frame and
    state and a postcondition on the returned value. *)
Record PicoSemanticMethodContract : Type := {
  psmc_pre : r_env -> pico_core_state -> Prop;
  psmc_post : r_env -> pico_core_val -> Prop;
}.

(** Evidence exported at a successful callable-method return.  This is the
    normalized bridge between a method-specific functional contract and the
    ordinary PICO return-transfer theorem. *)
Definition PicoCallableReturnEvidence
    (CT : class_table) (entry_heap : heap) (entry_receiver : Loc)
    (mdef : method_def) (callee_done : r_env)
    (final_state : pico_core_state) (returned : value) : Prop :=
  exists body_sGamma' body_ret_type,
    static_getType body_sGamma' (mreturn (mbody mdef)) =
      Some body_ret_type /\
    qualified_type_subtype CT body_ret_type (mret (msignature mdef)) /\
    pico_core_typed_env CT body_sGamma' callee_done
      (pcs_heap final_state) /\
    get_this_var_mapping (vars callee_done) = Some entry_receiver /\
    pico_core_heap_types_extend entry_heap (pcs_heap final_state) /\
    pico_core_lr_state CT final_state /\
    runtime_getVal callee_done (mreturn (mbody mdef)) = Some returned.
