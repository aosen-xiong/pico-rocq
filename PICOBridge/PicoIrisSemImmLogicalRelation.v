From iris.program_logic Require Import weakestpre ownp.
From iris.proofmode Require Import proofmode.
From Stdlib Require Import List.

Require Import Syntax Helpers Typing Subtyping Bigstep.
Require Import Core.GenericCacheProtocol Iris.GenericCacheGhostState
  Iris.IrisSemanticBridge.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage
  PICOBridge.PicoIrisCoreInvariant PICOBridge.PicoIrisSemImmOperations
  PICOBridge.PicoIrisTypingFundamental
  PICOBridge.PicoIrisResourceLogicalRelation.

(** * Ghost-Backed SemImm Resource for the PICO LR *)

Section pico_semimm_logical_relation.
  Context `{Hmem : CacheMemoryModel}.
  Context `{Hprogress : CacheMemoryModelProgress}.
  Context (CT : class_table).
  Context `{!ownPGS (pico_core_language CT) Sigma}.
  Context {AbsVal Obj : Type}.
  Context (P : CacheProtocol AbsVal).
  Context `{!genericCacheG P Sigma}.
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

    pcsi_abstract_cache_disjoint : forall addr k,
      pcsi_abstract_field addr ->
      pico_core_cache_field P A addr = Some k ->
      False;

    pcsi_mapped_field_declared : forall state loc f k,
      pcsi_state_inv state ->
      pico_core_cache_field P A (loc, f) = Some k ->
      exists rt,
        wm_get_type (pcs_weak state) loc = Some rt /\
        derived_cache_field CT (rctype rt) f;

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

  Definition pico_core_semimm_worldI
      (M : PicoCoreSemImmInstantiation)
      (state : pico_core_state) : iProp Sigma :=
    ∃ gamma,
      ⌜pcsi_state_inv M state⌝ ∗
      SemImmI P Stable gamma
        (pcsi_object M state) a (pcsi_snapshot M state).

  Definition PicoCoreWriteAdmissible
      (M : PicoCoreSemImmInstantiation)
      (addr : FieldAddr) (v : Syntax.value) : Prop :=
    (pico_core_cache_field P A addr = None /\
      ~ pcsi_abstract_field M addr) \/
    exists k (cv : cache_val P k),
      pico_core_cache_field P A addr = Some k /\
      pico_core_cache_value P A k v = Some cv /\
      cache_valid P a k cv.

  Theorem pico_core_semimm_admissible_write_ruleI :
    forall M h h' sigma sigma' V V' loc f v,
      h' = update_field h loc f v ->
      wm_write sigma sigma' V V' (loc, f) v ->
      PicoCoreWriteAdmissible M (loc, f) v ->
      pico_core_semimm_worldI M (mkPicoCoreState h sigma) ==∗
      pico_core_semimm_worldI M (mkPicoCoreState h' sigma').
  Proof.
    intros M h h' sigma sigma' V V' loc f v Hheap Hwrite Hadmissible.
    iIntros "Hworld".
    unfold pico_core_semimm_worldI.
    iDestruct "Hworld" as (gamma) "[%Hstate Hsem]".
    destruct Hadmissible as
      [[Hnoncache Hunrelated] | (k & cv & Hfield & Hvalue & Hvalid)].
    - pose proof (pcsi_unrelated_write_effect M h h' sigma sigma' V V'
        loc f v Hstate Hheap Hwrite Hnoncache Hunrelated)
        as (Hobject & Hsnapshot & Hstate_after).
      simpl in Hobject, Hsnapshot, Hstate_after.
      iModIntro. iExists gamma. iSplit.
      + iPureIntro. exact Hstate_after.
      + rewrite Hobject Hsnapshot. iExact "Hsem".
    - pose proof (pcsi_valid_cache_write_effect M h h' sigma sigma' V V'
        loc f v k cv Hstate Hheap Hwrite Hfield Hvalue Hvalid)
        as [Hcache_write Hstate_after].
      simpl in Hcache_write, Hstate_after.
      iMod
          (pico_core_cache_write_semimmI
            P A Stable gamma
            (pcsi_object M (mkPicoCoreState h sigma))
            (pcsi_object M (mkPicoCoreState h' sigma'))
            a
            (pcsi_snapshot M (mkPicoCoreState h sigma))
            (pcsi_snapshot M (mkPicoCoreState h' sigma'))
            (loc, f) v
            (pcsi_stable M (mkPicoCoreState h' sigma') Hstate_after)
            with "Hsem []") as "Hsem".
      { iPureIntro. exact Hcache_write. }
      iModIntro. iExists gamma. iSplit.
      + iPureIntro. exact Hstate_after.
      + iExact "Hsem".
  Qed.

  Theorem pico_core_semimm_alloc_ruleI :
    forall M,
      ⊢ pico_core_resource_alloc_ruleI
        (pico_core_semimm_worldI M).
  Proof.
    intros M.
    unfold pico_core_resource_alloc_ruleI.
    iModIntro.
    iIntros (h sigma o V) "Hworld".
    iDestruct "Hworld" as (gamma) "[%Hstate Hsem]".
    pose proof (pcsi_alloc_unchanged M h sigma o V Hstate)
      as [Hobject [Hsnapshot Hstate_after]].
    simpl in Hobject, Hsnapshot, Hstate_after.
    unfold pico_core_semimm_worldI.
    iModIntro.
    iExists gamma.
    iSplit.
    - iPureIntro.
      exact Hstate_after.
    - rewrite Hobject Hsnapshot.
      iExact "Hsem".
  Qed.

  (** Whole-program typing alone cannot close a [SemImmI] statement WP:
      ordinary field-write typing does not imply protocol validity.  Clients
      therefore consume the pointwise read, allocation, and admissible-write
      rules above inside method-specific semantic API proofs. *)
End pico_semimm_logical_relation.
