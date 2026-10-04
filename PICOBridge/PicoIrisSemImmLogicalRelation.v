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

  Local Notation PicoCoreSemImmInstantiation :=
    (PicoCoreSemImmInstantiation P Stable a A).
  Local Notation pcsi_state_inv := (pcsi_state_inv P Stable a A).
  Local Notation pcsi_object := (pcsi_object P Stable a A).
  Local Notation pcsi_snapshot := (pcsi_snapshot P Stable a A).
  Local Notation pcsi_abstract_field := (pcsi_abstract_field P Stable a A).
  Local Notation pcsi_stable := (pcsi_stable P Stable a A).
  Local Notation pcsi_cache_history_covers := (pcsi_cache_history_covers P Stable a A).
  Local Notation pcsi_unrelated_write_effect := (pcsi_unrelated_write_effect P Stable a A).
  Local Notation pcsi_valid_cache_write_effect := (pcsi_valid_cache_write_effect P Stable a A).
  Local Notation pcsi_alloc_unchanged := (pcsi_alloc_unchanged P Stable a A).
  Local Notation pico_core_semimm_cache_read_from_history := (pico_core_semimm_cache_read_from_history P Stable a A).

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
