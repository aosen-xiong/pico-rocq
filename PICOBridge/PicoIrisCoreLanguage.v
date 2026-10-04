From iris.program_logic Require Import language.

From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Bigstep ViewpointAdaptation
  PICOBridge.PicoMemoryModel.
Require Export PICOBridge.PicoCoreLanguage.

(** * Core Iris Language for PICO

    The Iris language instance for the machine of [PicoCoreLanguage]. *)

Definition pico_core_prim_step
    `{CacheMemoryModel} (CT : class_table) :
    pico_core_expr -> pico_core_state -> list unit ->
    pico_core_expr -> pico_core_state -> list pico_core_expr -> Prop :=
  fun e sigma k e' sigma' efs =>
    k = [] /\ efs = [] /\ pico_core_step CT e sigma e' sigma'.

Lemma pico_core_no_step_from_value :
  forall `{CacheMemoryModel} CT r rΓ V sigma e' sigma',
    not (pico_core_step CT (CoreDone r rΓ V) sigma e' sigma').
Proof.
  intros Hmem CT r rΓ V sigma e' sigma' Hstep.
  inversion Hstep.
Qed.

Program Definition pico_core_language_mixin `{CacheMemoryModel} (CT : class_table) :
  LanguageMixin
    pico_core_of_val
    pico_core_to_val
    (pico_core_prim_step CT) := {|
  mixin_to_of_val := _;
  mixin_of_to_val := _;
  mixin_val_stuck := _
|}.
Next Obligation.
  apply pico_core_to_of_val.
Qed.
Next Obligation.
  symmetry.
  eapply pico_core_of_to_val; eauto.
Qed.
Next Obligation.
  match goal with
  | Hstep : pico_core_prim_step _ _ _ _ _ _ _ |- _ =>
      unfold pico_core_prim_step in Hstep;
      destruct Hstep as [_ [_ Hcore]]
  end.
  destruct e as [rΓ s V K | r rΓ V]; simpl; try reflexivity.
  exfalso.
  eapply pico_core_no_step_from_value; eauto.
Qed.

Canonical Structure pico_core_language `{CacheMemoryModel} (CT : class_table) :
  language :=
  Language (pico_core_language_mixin CT).

Lemma pico_core_prim_step_no_forks :
  forall `{CacheMemoryModel} CT e sigma k e' sigma' efs
    (Hstep : @prim_step (pico_core_language CT) e sigma k e' sigma' efs),
    efs = [].
Proof.
  intros Hmem CT e sigma k e' sigma' efs Hstep.
  exact (proj1 (proj2 Hstep)).
Qed.

Lemma pico_core_prim_step_is_core_step :
  forall `{CacheMemoryModel} CT e sigma k e' sigma' efs
    (Hstep : @prim_step (pico_core_language CT) e sigma k e' sigma' efs),
    pico_core_step CT e sigma e' sigma'.
Proof.
  intros Hmem CT e sigma k e' sigma' efs Hstep.
  exact (proj2 (proj2 Hstep)).
Qed.

Lemma pico_core_step_is_prim_step :
  forall `{CacheMemoryModel} CT e sigma e' sigma'
    (Hstep : pico_core_step CT e sigma e' sigma'),
    @prim_step (pico_core_language CT) e sigma [] e' sigma' [].
Proof.
  intros Hmem CT e sigma e' sigma' Hstep.
  repeat split; assumption.
Qed.

Lemma pico_core_reducible_from_step :
  forall `{CacheMemoryModel} CT e sigma e' sigma'
    (Hstep : pico_core_step CT e sigma e' sigma'),
    @reducible (pico_core_language CT) e sigma.
Proof.
  intros Hmem CT e sigma e' sigma' Hstep.
  exists (@nil unit), e', sigma', (@nil pico_core_expr).
  apply pico_core_step_is_prim_step.
  exact Hstep.
Qed.

Lemma pico_core_step_from_reducible :
  forall `{CacheMemoryModel} CT e sigma
    (Hred : @reducible (pico_core_language CT) e sigma),
    exists e' sigma',
      pico_core_step CT e sigma e' sigma'.
Proof.
  intros Hmem CT e sigma Hred.
  destruct Hred as [k [e' [sigma' [efs Hprim]]]].
  exists e', sigma'.
  eapply pico_core_prim_step_is_core_step; eauto.
Qed.

Lemma pico_core_reducible_iff_step :
  forall `{CacheMemoryModel} CT e sigma,
    @reducible (pico_core_language CT) e sigma <->
    exists e' sigma',
      pico_core_step CT e sigma e' sigma'.
Proof.
  intros Hmem CT e sigma.
  split.
  - apply pico_core_step_from_reducible.
  - intros [e' [sigma' Hstep]].
    eapply pico_core_reducible_from_step; eauto.
Qed.

Lemma pico_core_not_stuck_from_step :
  forall `{CacheMemoryModel} CT e sigma e' sigma'
    (Hstep : pico_core_step CT e sigma e' sigma'),
    @not_stuck (pico_core_language CT) e sigma.
Proof.
  intros Hmem CT e sigma e' sigma' Hstep.
  right.
  eapply pico_core_reducible_from_step; eauto.
Qed.
