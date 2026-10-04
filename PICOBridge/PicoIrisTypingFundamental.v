From iris.program_logic Require Import weakestpre ownp.
From iris.proofmode Require Import proofmode.

Require Import Syntax Helpers Typing Subtyping Bigstep Properties
  ViewpointAdaptation.
Require Export PICOBridge.PicoCoreTyping.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage
  PICOBridge.PicoIrisCoreInvariant PICOBridge.PicoIrisTypingSupport.

(** * Typing-Directed PICO Core WP

    This file contains the progress-facing fundamental-theorem development.
    It is kept separate from the typed-environment support file so each new
    typing case can be checked without recompiling semantic resource proofs.

    Unlike the older runtime-outcome endpoint, rules here derive primitive-step
    readiness from typing plus [pico_core_typed_env] and
    [pico_core_state_wf].  They target [NotStuck]. *)

Section pico_typing_fundamental_ownp.
  Context `{Hmem : CacheMemoryModel}.
  Context `{Hprogress : CacheMemoryModelProgress}.
  Context (CT : class_table).
  Context `{!ownPGS (pico_core_language CT) Sigma}.

  Local Notation pico_core_typed_env_real_lr_env := (pico_core_typed_env_real_lr_env CT) (only parsing).
  Local Notation pico_core_cont_typed := (pico_core_cont_typed CT) (only parsing).
  Local Notation pico_core_stmt_post := (pico_core_stmt_post CT) (only parsing).
  Local Notation pico_core_typed_skip_call_ready := (pico_core_typed_skip_call_ready CT) (only parsing).
  Local Notation pico_core_typed_value_env_independent := (pico_core_typed_value_env_independent CT) (only parsing).
  Local Notation pico_core_typed_value_real_lr_value := (pico_core_typed_value_real_lr_value CT) (only parsing).
  Local Notation pico_core_typed_value_subtype := (pico_core_typed_value_subtype CT) (only parsing).
  Local Notation pico_core_subtype_preserves_reference := (pico_core_subtype_preserves_reference CT) (only parsing).
  Local Notation pico_core_typed_value_heap_types_extend := (pico_core_typed_value_heap_types_extend CT) (only parsing).
  Local Notation pico_core_wf_renv_heap_types_extend := (pico_core_wf_renv_heap_types_extend CT) (only parsing).
  Local Notation pico_core_typed_env_heap_types_extend := (pico_core_typed_env_heap_types_extend CT) (only parsing).
  Local Notation pico_core_cont_typed_heap_types_extend := (pico_core_cont_typed_heap_types_extend CT) (only parsing).
  Local Notation pico_core_typed_resolved_method_static := (pico_core_typed_resolved_method_static CT) (only parsing).
  Local Notation pico_core_typed_resolved_method_body := (pico_core_typed_resolved_method_body CT) (only parsing).
  Local Notation pico_core_resolved_method_frame_wf_renv := (pico_core_resolved_method_frame_wf_renv CT) (only parsing).
  Local Notation pico_core_typed_env_after_update := (pico_core_typed_env_after_update CT) (only parsing).
  Local Notation pico_core_typed_env_update_value := (pico_core_typed_env_update_value CT) (only parsing).
  Local Notation pico_core_typed_env_update_value_from_subtype := (pico_core_typed_env_update_value_from_subtype CT) (only parsing).
  Local Notation pico_core_wf_r_typable_adapted_subtype_abstract_state := (pico_core_wf_r_typable_adapted_subtype_abstract_state CT) (only parsing).
  Local Notation pico_core_wf_r_typable_adapted_subtype_readonly_state := (pico_core_wf_r_typable_adapted_subtype_readonly_state CT) (only parsing).
  Local Notation pico_core_wf_r_typable_call_argument_abstract_state := (pico_core_wf_r_typable_call_argument_abstract_state CT) (only parsing).
  Local Notation pico_core_wf_r_typable_call_argument_readonly_state := (pico_core_wf_r_typable_call_argument_readonly_state CT) (only parsing).
  Local Notation pico_core_wf_r_typable_call_argument_abstract_state_special := (pico_core_wf_r_typable_call_argument_abstract_state_special CT) (only parsing).
  Local Notation pico_core_wf_r_typable_call_argument_readonly_state_special := (pico_core_wf_r_typable_call_argument_readonly_state_special CT) (only parsing).
  Local Notation pico_core_typed_location_call_argument_abstract_state := (pico_core_typed_location_call_argument_abstract_state CT) (only parsing).
  Local Notation pico_core_typed_location_call_argument_readonly_state := (pico_core_typed_location_call_argument_readonly_state CT) (only parsing).
  Local Notation pico_core_typed_location_call_argument_abstract_state_direct := (pico_core_typed_location_call_argument_abstract_state_direct CT) (only parsing).
  Local Notation pico_core_typed_location_call_argument_readonly_state_direct := (pico_core_typed_location_call_argument_readonly_state_direct CT) (only parsing).
  Local Notation pico_core_typed_return_value_refined_abstract_state := (pico_core_typed_return_value_refined_abstract_state CT) (only parsing).
  Local Notation pico_core_typed_return_value_refined_readonly_state := (pico_core_typed_return_value_refined_readonly_state CT) (only parsing).
  Local Notation pico_core_typed_return_value_abstract_state := (pico_core_typed_return_value_abstract_state CT) (only parsing).
  Local Notation pico_core_typed_return_value_readonly_state := (pico_core_typed_return_value_readonly_state CT) (only parsing).
  Local Notation pico_core_typed_method_frame_env := (pico_core_typed_method_frame_env CT) (only parsing).
  Local Notation pico_core_typed_env_lookup_at_context := (pico_core_typed_env_lookup_at_context CT) (only parsing).
  Local Notation pico_core_typed_call_params_abstract_state := (pico_core_typed_call_params_abstract_state CT) (only parsing).
  Local Notation pico_core_typed_call_params_readonly_state := (pico_core_typed_call_params_readonly_state CT) (only parsing).
  Local Notation pico_core_typed_call_params_abstract_state_special := (pico_core_typed_call_params_abstract_state_special CT) (only parsing).
  Local Notation pico_core_typed_call_params_readonly_state_special := (pico_core_typed_call_params_readonly_state_special CT) (only parsing).
  Local Notation pico_core_stmt_typing_call_abs_components := (pico_core_stmt_typing_call_abs_components CT) (only parsing).
  Local Notation pico_core_concrete_state_call_as_abs := (pico_core_concrete_state_call_as_abs CT) (only parsing).
  Local Notation pico_core_stmt_typing_call_safe_components := (pico_core_stmt_typing_call_safe_components CT) (only parsing).
  Local Notation pico_core_typed_env_receiver_qualifier := (pico_core_typed_env_receiver_qualifier CT) (only parsing).
  Local Notation pico_core_typed_call_receiver_qualifiers := (pico_core_typed_call_receiver_qualifiers CT) (only parsing).
  Local Notation pico_core_typed_location_call_receiver_abstract_state_regular := (pico_core_typed_location_call_receiver_abstract_state_regular CT) (only parsing).
  Local Notation pico_core_typed_env_refine_frame := (pico_core_typed_env_refine_frame CT) (only parsing).
  Local Notation pico_core_typed_call_frame_abstract_state_regular := (pico_core_typed_call_frame_abstract_state_regular CT) (only parsing).
  Local Notation pico_core_typed_location_call_receiver_readonly_state_regular := (pico_core_typed_location_call_receiver_readonly_state_regular CT) (only parsing).
  Local Notation pico_core_typed_call_frame_readonly_state_regular := (pico_core_typed_call_frame_readonly_state_regular CT) (only parsing).
  Local Notation pico_core_typed_resolved_method_return_abstract_state := (pico_core_typed_resolved_method_return_abstract_state CT) (only parsing).
  Local Notation pico_core_typed_resolved_method_return_readonly_state := (pico_core_typed_resolved_method_return_readonly_state CT) (only parsing).
  Local Notation pico_core_typed_resolved_method_return := (pico_core_typed_resolved_method_return CT) (only parsing).
  Local Notation pico_core_typed_env_after_assign_null := (pico_core_typed_env_after_assign_null CT) (only parsing).
  Local Notation pico_core_typed_env_after_local := (pico_core_typed_env_after_local CT) (only parsing).
  Local Notation pico_core_typed_env_after_assign_int := (pico_core_typed_env_after_assign_int CT) (only parsing).
  Local Notation pico_core_typed_env_after_assign_var := (pico_core_typed_env_after_assign_var CT) (only parsing).
  Local Notation pico_core_typed_value_after_field_update := (pico_core_typed_value_after_field_update CT) (only parsing).
  Local Notation pico_core_typed_env_after_fldwrite_success := (pico_core_typed_env_after_fldwrite_success CT) (only parsing).
  Local Notation pico_core_typed_value_heap_extension := (pico_core_typed_value_heap_extension CT) (only parsing).
  Local Notation pico_core_typed_env_after_new_success := (pico_core_typed_env_after_new_success CT) (only parsing).
  Local Notation pico_core_typed_env_after_assign_field_read := (pico_core_typed_env_after_assign_field_read CT) (only parsing).
  Local Notation pico_core_typed_varass_field_step_post := (pico_core_typed_varass_field_step_post CT) (only parsing).
  Local Notation pico_core_typed_assign_null_step_post := (pico_core_typed_assign_null_step_post CT) (only parsing).
  Local Notation pico_core_typed_local_step_post := (pico_core_typed_local_step_post CT) (only parsing).
  Local Notation pico_core_typed_assign_int_step_post := (pico_core_typed_assign_int_step_post CT) (only parsing).
  Local Notation pico_core_typed_assign_var_step_post := (pico_core_typed_assign_var_step_post CT) (only parsing).
  Local Notation pico_core_typed_fldwrite_step_post := (pico_core_typed_fldwrite_step_post CT) (only parsing).
  Local Notation pico_core_typed_new_step_post := (pico_core_typed_new_step_post CT) (only parsing).
  Local Notation pico_core_typed_location_call_receiver_abstract_state_special := (pico_core_typed_location_call_receiver_abstract_state_special CT) (only parsing).
  Local Notation pico_core_typed_call_frame_abstract_state_special := (pico_core_typed_call_frame_abstract_state_special CT) (only parsing).
  Local Notation pico_core_typed_resolved_method_frame_abstract_state := (pico_core_typed_resolved_method_frame_abstract_state CT) (only parsing).
  Local Notation pico_core_typed_call_frame_readonly_state_special := (pico_core_typed_call_frame_readonly_state_special CT) (only parsing).
  Local Notation pico_core_typed_resolved_method_frame_readonly_state := (pico_core_typed_resolved_method_frame_readonly_state CT) (only parsing).
  Local Notation pico_core_typed_resolved_method_frame := (pico_core_typed_resolved_method_frame CT) (only parsing).

  Definition pico_core_stmt_post_contI
      (sGamma' : s_env) (K : pico_core_cont)
      (E : coPset)
      (Phi : val (pico_core_language CT) -> iProp Sigma) : iProp Sigma :=
    ▷ ∀ e' state',
      ⌜pico_core_stmt_post sGamma' K e' state'⌝ -∗
      ownP state' -∗
      WP e' @ NotStuck; E {{ Phi }}.

  Definition pico_core_typed_outcome_contI
      (sGamma' : s_env) (K : pico_core_cont)
      (E : coPset)
      (Phi : val (pico_core_language CT) -> iProp Sigma) : iProp Sigma :=
    (□ ∀ rGamma state V,
      ⌜pico_core_typed_env CT sGamma' rGamma (pcs_heap state)⌝ -∗
      ⌜pico_core_lr_state CT state⌝ -∗
      ownP state -∗
      WP CoreRun rGamma SSkip V K @ NotStuck; E {{ Phi }}) ∗
    (□ ∀ rGamma state V,
      ⌜pico_core_lr_state CT state⌝ -∗
      ownP state -∗
      WP CoreDone NPE rGamma V @ NotStuck; E {{ Phi }}) ∗
    (□ ∀ rGamma state V,
      ⌜pico_core_lr_state CT state⌝ -∗
      ownP state -∗
      WP CoreDone MUTATIONEXP rGamma V @ NotStuck; E {{ Phi }}).

  Lemma pico_core_stmt_post_cont_from_outcomeI :
    forall sGamma' K E Phi,
      pico_core_typed_outcome_contI sGamma' K E Phi -∗
      pico_core_stmt_post_contI sGamma' K E Phi.
  Proof.
    intros sGamma' K E Phi.
    iIntros "[#Hok [#Hnpe #Hmutation]]".
    unfold pico_core_stmt_post_contI.
    iNext.
    iIntros (e' state') "Hpost Hown".
    iDestruct "Hpost" as %Hpost.
    inversion Hpost; subst.
    - iApply ("Hok" with "[] [] Hown"); iPureIntro; assumption.
    - iApply ("Hnpe" with "[] Hown").
      iPureIntro.
      assumption.
    - iApply ("Hmutation" with "[] Hown").
      iPureIntro.
      assumption.
  Qed.

  Definition pico_core_typed_stmt_wpI
      (sGamma : s_env) (mt : method_scope)
      (s : stmt) (sGamma' : s_env) : iProp Sigma :=
    □ ∀ rGamma h sigma V K E Phi,
      ⌜pico_core_typed_env CT sGamma rGamma h⌝ -∗
      ⌜pico_core_lr_state CT (mkPicoCoreState h sigma)⌝ -∗
      ownP (mkPicoCoreState h sigma) -∗
      pico_core_typed_outcome_contI sGamma' K E Phi -∗
      WP CoreRun rGamma s V K @ NotStuck; E {{ Phi }}.

  (** [ownP_lift_step] temporarily closes every invariant while handing the
      concrete machine state to the operational semantics.  This derived rule
      retains the corresponding mask-restoration token, so a direct semantic
      continuation can resume at the caller's original mask after the step. *)
  Lemma pico_core_ownP_wp_from_direct_step_contI :
    forall E Phi e state
      (Hready : exists e' state', pico_core_step CT e state e' state'),
      ownP state -∗
      (▷ ∀ e' state',
        ⌜pico_core_step CT e state e' state'⌝ -∗
        ownP state' -∗
        WP e' @ NotStuck; E {{ Phi }}) -∗
      WP e @ NotStuck; E {{ Phi }}.
  Proof.
    intros E Phi e state Hready.
    iIntros "Hown Hcont".
    iApply ownP_lift_step.
    iMod (fupd_mask_subseteq ∅) as "Hclose".
    { set_solver. }
    iModIntro.
    iExists state.
    iSplit.
    - iPureIntro.
      apply pico_core_reducible_iff_step.
      exact Hready.
    - iSplitL "Hown".
      + iNext.
        iExact "Hown".
      + iNext.
        iIntros (k e' state' efs Hprim) "Hown".
        pose proof
          (pico_core_prim_step_no_forks CT e state k e' state' efs Hprim)
          as ->.
        pose proof
          (pico_core_prim_step_is_core_step
            CT e state k e' state' [] Hprim)
          as Hstep.
        iPoseProof
          ("Hcont" $! e' state' with "[] Hown") as "Hwp".
        { iPureIntro. exact Hstep. }
        iMod "Hclose".
        iModIntro.
        simpl.
        iFrame.
  Qed.

  Lemma pico_core_stmt_post_ownP_not_stuck_wpI :
    forall E Phi e state sGamma' K
      (Hready : exists e' state', pico_core_step CT e state e' state')
      (Hpost : forall e' state',
        pico_core_step CT e state e' state' ->
        pico_core_stmt_post sGamma' K e' state'),
      ownP state -∗
      pico_core_stmt_post_contI sGamma' K E Phi -∗
      WP e @ NotStuck; E {{ Phi }}.
  Proof.
    intros E Phi e state sGamma' K Hready Hpost.
    iIntros "Hown Hcont".
    iApply
      (pico_core_ownP_wp_from_direct_step_contI
        E Phi e state Hready with "Hown [Hcont]").
    iNext.
    iIntros (e' state') "%Hstep Hown".
    iApply ("Hcont" $! e' state' with "[] Hown").
    iPureIntro.
    eapply Hpost; eauto.
  Qed.

  Lemma pico_core_typed_local_reducible :
    forall sGamma sGamma' rGamma h sigma mt T x V K
      (Htyping : stmt_typing CT sGamma mt (SLocal T x) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h),
      @reducible
        (pico_core_language CT)
        (CoreRun rGamma (SLocal T x) V K)
        (mkPicoCoreState h sigma).
  Proof.
    intros sGamma sGamma' rGamma h sigma mt T x V K Htyping Henv.
    inversion Htyping; subst.
    pose proof
      (pico_core_typed_env_real_lr_env sGamma rGamma h Henv)
      as Hreal.
    pose proof
      (pico_typed_runtime_env_local_runtime_absent
        CT sGamma rGamma h x Hreal Hnone)
      as Hruntime_none.
    eapply pico_core_reducible_from_step.
    eapply PCS_Local.
    exact Hruntime_none.
  Qed.

  Lemma pico_core_typed_assign_null_reducible :
    forall sGamma rGamma h sigma mt x V K
      (Htyping : stmt_typing CT sGamma mt (SVarAss x ENull) sGamma)
      (Henv : pico_core_typed_env CT sGamma rGamma h),
      @reducible
        (pico_core_language CT)
        (CoreRun rGamma (SVarAss x ENull) V K)
        (mkPicoCoreState h sigma).
  Proof.
    intros sGamma rGamma h sigma mt x V K Htyping Henv.
    inversion Htyping; subst.
    destruct
      (pico_core_typed_env_lookup
        CT sGamma rGamma h x Tx Henv Hget_x)
      as (qcontext & old & Hx & Htyped).
    eapply pico_core_reducible_from_step.
    eapply PCS_AssignNull; eauto.
  Qed.

  Lemma pico_core_typed_assign_int_reducible :
    forall sGamma rGamma h sigma mt x n V K
      (Htyping : stmt_typing CT sGamma mt (SVarAss x (EInt n)) sGamma)
      (Henv : pico_core_typed_env CT sGamma rGamma h),
      @reducible
        (pico_core_language CT)
        (CoreRun rGamma (SVarAss x (EInt n)) V K)
        (mkPicoCoreState h sigma).
  Proof.
    intros sGamma rGamma h sigma mt x n V K Htyping Henv.
    inversion Htyping; subst.
    destruct
      (pico_core_typed_env_lookup
        CT sGamma rGamma h x Tx Henv Hget_x)
      as (qcontext & old & Hx & Htyped).
    eapply pico_core_reducible_from_step.
    eapply PCS_AssignInt; eauto.
  Qed.

  Lemma pico_core_typed_assign_var_reducible :
    forall sGamma rGamma h sigma mt x y V K
      (Htyping : stmt_typing CT sGamma mt (SVarAss x (EVar y)) sGamma)
      (Henv : pico_core_typed_env CT sGamma rGamma h),
      @reducible
        (pico_core_language CT)
        (CoreRun rGamma (SVarAss x (EVar y)) V K)
        (mkPicoCoreState h sigma).
  Proof.
    intros sGamma rGamma h sigma mt x y V K Htyping Henv.
    inversion Htyping; subst.
    inversion Htype_e; subst.
    destruct
      (pico_core_typed_env_lookup
        CT sGamma rGamma h x Tx Henv Hget_x)
      as (qcontext_x & old & Hx & Htyped_x).
    destruct
      (pico_core_typed_env_lookup
        CT sGamma rGamma h y _ Henv Hget)
      as (qcontext_y & val_y & Hy & Htyped_y).
    eapply pico_core_reducible_from_step.
    eapply PCS_AssignVar; eauto.
  Qed.

  Lemma pico_core_typed_seq_reducible :
    forall sGamma sGamma'' rGamma h sigma mt s1 s2 V K
      (Htyping : stmt_typing CT sGamma mt (SSeq s1 s2) sGamma''),
      @reducible
        (pico_core_language CT)
        (CoreRun rGamma (SSeq s1 s2) V K)
        (mkPicoCoreState h sigma).
  Proof.
    intros sGamma sGamma'' rGamma h sigma mt s1 s2 V K Htyping.
    eapply pico_core_reducible_from_step.
    apply PCS_Seq.
  Qed.

  Lemma pico_core_typed_local_ownP_not_stuck_wpI :
    forall sGamma sGamma' rGamma h sigma mt T x V K E Phi
      (Htyping : stmt_typing CT sGamma mt (SLocal T x) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hlrstate : pico_core_lr_state CT (mkPicoCoreState h sigma)),
      ownP (mkPicoCoreState h sigma) -∗
      pico_core_stmt_post_contI sGamma' K E Phi -∗
      WP CoreRun rGamma (SLocal T x) V K
        @ NotStuck; E {{ Phi }}.
  Proof.
    intros sGamma sGamma' rGamma h sigma mt T x V K E Phi
      Htyping Henv Hlrstate.
    assert (Hready :
      exists e' state',
        pico_core_step CT
          (CoreRun rGamma (SLocal T x) V K)
          (mkPicoCoreState h sigma) e' state').
    {
      apply pico_core_step_from_reducible.
      eapply pico_core_typed_local_reducible; eauto.
    }
    assert (Hpost : forall e' state',
      pico_core_step CT
        (CoreRun rGamma (SLocal T x) V K)
        (mkPicoCoreState h sigma) e' state' ->
      pico_core_stmt_post sGamma' K e' state').
    {
      intros e' state' Hstep.
      eapply pico_core_typed_local_step_post; eauto.
    }
    iIntros "Hown Hcont".
    iApply
      (pico_core_stmt_post_ownP_not_stuck_wpI
        E Phi
        (CoreRun rGamma (SLocal T x) V K)
        (mkPicoCoreState h sigma)
        sGamma' K Hready Hpost
        with "Hown Hcont").
  Qed.

  Lemma pico_core_typed_assign_null_ownP_not_stuck_wpI :
    forall sGamma rGamma h sigma mt x V K E Phi
      (Htyping : stmt_typing CT sGamma mt (SVarAss x ENull) sGamma)
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hlrstate : pico_core_lr_state CT (mkPicoCoreState h sigma)),
      ownP (mkPicoCoreState h sigma) -∗
      pico_core_stmt_post_contI sGamma K E Phi -∗
      WP CoreRun rGamma (SVarAss x ENull) V K
        @ NotStuck; E {{ Phi }}.
  Proof.
    intros sGamma rGamma h sigma mt x V K E Phi
      Htyping Henv Hlrstate.
    assert (Hready :
      exists e' state',
        pico_core_step CT
          (CoreRun rGamma (SVarAss x ENull) V K)
          (mkPicoCoreState h sigma) e' state').
    {
      apply pico_core_step_from_reducible.
      eapply pico_core_typed_assign_null_reducible; eauto.
    }
    assert (Hpost : forall e' state',
      pico_core_step CT
        (CoreRun rGamma (SVarAss x ENull) V K)
        (mkPicoCoreState h sigma) e' state' ->
      pico_core_stmt_post sGamma K e' state').
    {
      intros e' state' Hstep.
      eapply pico_core_typed_assign_null_step_post; eauto.
    }
    iIntros "Hown Hcont".
    iApply
      (pico_core_stmt_post_ownP_not_stuck_wpI
        E Phi
        (CoreRun rGamma (SVarAss x ENull) V K)
        (mkPicoCoreState h sigma)
        sGamma K Hready Hpost
        with "Hown Hcont").
  Qed.

  Lemma pico_core_typed_assign_int_ownP_not_stuck_wpI :
    forall sGamma rGamma h sigma mt x n V K E Phi
      (Htyping : stmt_typing CT sGamma mt (SVarAss x (EInt n)) sGamma)
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hlrstate : pico_core_lr_state CT (mkPicoCoreState h sigma)),
      ownP (mkPicoCoreState h sigma) -∗
      pico_core_stmt_post_contI sGamma K E Phi -∗
      WP CoreRun rGamma (SVarAss x (EInt n)) V K
        @ NotStuck; E {{ Phi }}.
  Proof.
    intros sGamma rGamma h sigma mt x n V K E Phi
      Htyping Henv Hlrstate.
    assert (Hready :
      exists e' state',
        pico_core_step CT
          (CoreRun rGamma (SVarAss x (EInt n)) V K)
          (mkPicoCoreState h sigma) e' state').
    {
      apply pico_core_step_from_reducible.
      eapply pico_core_typed_assign_int_reducible; eauto.
    }
    assert (Hpost : forall e' state',
      pico_core_step CT
        (CoreRun rGamma (SVarAss x (EInt n)) V K)
        (mkPicoCoreState h sigma) e' state' ->
      pico_core_stmt_post sGamma K e' state').
    {
      intros e' state' Hstep.
      eapply pico_core_typed_assign_int_step_post; eauto.
    }
    iIntros "Hown Hcont".
    iApply
      (pico_core_stmt_post_ownP_not_stuck_wpI
        E Phi
        (CoreRun rGamma (SVarAss x (EInt n)) V K)
        (mkPicoCoreState h sigma)
        sGamma K Hready Hpost
        with "Hown Hcont").
  Qed.

  Lemma pico_core_typed_assign_var_ownP_not_stuck_wpI :
    forall sGamma rGamma h sigma mt x y V K E Phi
      (Htyping : stmt_typing CT sGamma mt (SVarAss x (EVar y)) sGamma)
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hlrstate : pico_core_lr_state CT (mkPicoCoreState h sigma)),
      ownP (mkPicoCoreState h sigma) -∗
      pico_core_stmt_post_contI sGamma K E Phi -∗
      WP CoreRun rGamma (SVarAss x (EVar y)) V K
        @ NotStuck; E {{ Phi }}.
  Proof.
    intros sGamma rGamma h sigma mt x y V K E Phi
      Htyping Henv Hlrstate.
    assert (Hready :
      exists e' state',
        pico_core_step CT
          (CoreRun rGamma (SVarAss x (EVar y)) V K)
          (mkPicoCoreState h sigma) e' state').
    {
      apply pico_core_step_from_reducible.
      eapply pico_core_typed_assign_var_reducible; eauto.
    }
    assert (Hpost : forall e' state',
      pico_core_step CT
        (CoreRun rGamma (SVarAss x (EVar y)) V K)
        (mkPicoCoreState h sigma) e' state' ->
      pico_core_stmt_post sGamma K e' state').
    {
      intros e' state' Hstep.
      eapply pico_core_typed_assign_var_step_post; eauto.
    }
    iIntros "Hown Hcont".
    iApply
      (pico_core_stmt_post_ownP_not_stuck_wpI
        E Phi
        (CoreRun rGamma (SVarAss x (EVar y)) V K)
        (mkPicoCoreState h sigma)
        sGamma K Hready Hpost
        with "Hown Hcont").
  Qed.

  Lemma pico_core_typed_varass_field_ownP_not_stuck_wpI :
    forall sGamma sGamma' rGamma h sigma mt x y f V K E Phi
      (Htyping :
        stmt_typing CT sGamma mt (SVarAss x (EField y f)) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hlrstate : pico_core_lr_state CT (mkPicoCoreState h sigma))
      (Hread_typed :
        forall loc v V',
          runtime_getVal rGamma y = Some (Iot loc) ->
          wm_read sigma V (loc, f) v V' ->
          pico_core_typed_env CT sGamma'
            (set_vars rGamma (update x v (vars rGamma))) h),
      ownP (mkPicoCoreState h sigma) -∗
      pico_core_stmt_post_contI sGamma' K E Phi -∗
      WP CoreRun rGamma (SVarAss x (EField y f)) V K
        @ NotStuck; E {{ Phi }}.
  Proof.
    intros sGamma sGamma' rGamma h sigma mt x y f V K E Phi
      Htyping Henv Hlrstate Hread_typed.
    assert (Hready :
      exists e' state',
        pico_core_step CT
          (CoreRun rGamma (SVarAss x (EField y f)) V K)
          (mkPicoCoreState h sigma)
          e' state').
    {
      apply pico_core_step_from_reducible.
      eapply pico_core_typed_varass_field_reducible; eauto.
    }
    iIntros "Hown Hcont".
    iApply
      (pico_core_ownP_wp_from_direct_step_contI
        E Phi
        (CoreRun rGamma (SVarAss x (EField y f)) V K)
        (mkPicoCoreState h sigma)
        Hready
        with "Hown [Hcont]").
    iNext.
    iIntros (e' state') "%Hstep Hown".
    iApply ("Hcont" $! e' state' with "[] Hown").
    iPureIntro.
    eapply pico_core_typed_varass_field_step_post; eauto.
  Qed.

  Theorem pico_core_typed_pure_varass_ownP_not_stuck_wpI :
    forall sGamma rGamma h sigma mt x e V K E Phi
      (Htyping : stmt_typing CT sGamma mt (SVarAss x e) sGamma)
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hlrstate : pico_core_lr_state CT (mkPicoCoreState h sigma))
      (Hpure : match e with EField _ _ => False | _ => True end),
      ownP (mkPicoCoreState h sigma) -∗
      pico_core_stmt_post_contI sGamma K E Phi -∗
      WP CoreRun rGamma (SVarAss x e) V K
        @ NotStuck; E {{ Phi }}.
  Proof.
    intros sGamma rGamma h sigma mt x e V K E Phi
      Htyping Henv Hlrstate Hpure.
    destruct e as [|y|n|y f].
    - iIntros "Hown Hcont".
      iApply
        (pico_core_typed_assign_null_ownP_not_stuck_wpI
          with "Hown Hcont"); eauto.
    - iIntros "Hown Hcont".
      iApply
        (pico_core_typed_assign_var_ownP_not_stuck_wpI
          with "Hown Hcont"); eauto.
    - iIntros "Hown Hcont".
      iApply
        (pico_core_typed_assign_int_ownP_not_stuck_wpI
          with "Hown Hcont"); eauto.
    - contradiction.
  Qed.

  Theorem pico_core_typed_fldwrite_progress_ownP_not_stuck_wpI :
    forall sGamma sGamma' rGamma h sigma mt x f y V K E Phi
      (Htyping : stmt_typing CT sGamma mt (SFldWrite x f y) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h),
      ownP (mkPicoCoreState h sigma) -∗
      (▷ ∀ e' state',
        ⌜pico_core_step CT
          (CoreRun rGamma (SFldWrite x f y) V K)
          (mkPicoCoreState h sigma) e' state'⌝ -∗
        ownP state' -∗
        WP e' @ NotStuck; E {{ Phi }}) -∗
      WP CoreRun rGamma (SFldWrite x f y) V K
        @ NotStuck; E {{ Phi }}.
  Proof.
    intros sGamma sGamma' rGamma h sigma mt x f y V K E Phi
      Htyping Henv.
    assert (Hready :
      exists e' state',
        pico_core_step CT
          (CoreRun rGamma (SFldWrite x f y) V K)
          (mkPicoCoreState h sigma) e' state').
    {
      apply pico_core_step_from_reducible.
      eapply pico_core_typed_fldwrite_reducible; eauto.
    }
    iIntros "Hown Hnext".
    iApply
      (pico_core_ownP_wp_from_direct_step_contI
        E Phi
        (CoreRun rGamma (SFldWrite x f y) V K)
        (mkPicoCoreState h sigma) Hready
        with "Hown Hnext").
  Qed.

  Theorem pico_core_typed_fldwrite_fundamentalI :
    forall sGamma sGamma' mt x f y
      (Htyping : stmt_typing CT sGamma mt (SFldWrite x f y) sGamma'),
      ⊢ pico_core_typed_stmt_wpI
        sGamma mt (SFldWrite x f y) sGamma'.
  Proof.
    intros sGamma sGamma' mt x f y Htyping.
    unfold pico_core_typed_stmt_wpI.
    iModIntro.
    iIntros (rGamma h sigma V K E Phi)
      "%Henv %Hlrstate Hown Houtcomes".
    iPoseProof
      (pico_core_stmt_post_cont_from_outcomeI
        sGamma' K E Phi with "Houtcomes") as "Hpost".
    iApply
      (pico_core_typed_fldwrite_progress_ownP_not_stuck_wpI
        with "Hown [Hpost]"); eauto.
    iNext.
    iIntros (e' state') "%Hstep Hown".
    iApply ("Hpost" $! e' state' with "[] Hown").
    iPureIntro.
    eapply pico_core_typed_fldwrite_step_post; eauto.
  Qed.

  Theorem pico_core_typed_new_progress_ownP_not_stuck_wpI :
    forall sGamma sGamma' rGamma h sigma mt x qc C args V K E Phi
      (Htyping : stmt_typing CT sGamma mt (SNew x qc C args) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h),
      ownP (mkPicoCoreState h sigma) -∗
      (▷ ∀ e' state',
        ⌜pico_core_step CT
          (CoreRun rGamma (SNew x qc C args) V K)
          (mkPicoCoreState h sigma) e' state'⌝ -∗
        ownP state' -∗
        WP e' @ NotStuck; E {{ Phi }}) -∗
      WP CoreRun rGamma (SNew x qc C args) V K
        @ NotStuck; E {{ Phi }}.
  Proof.
    intros sGamma sGamma' rGamma h sigma mt x qc C args V K E Phi
      Htyping Henv.
    assert (Hready :
      exists e' state',
        pico_core_step CT
          (CoreRun rGamma (SNew x qc C args) V K)
          (mkPicoCoreState h sigma) e' state').
    {
      apply pico_core_step_from_reducible.
      eapply pico_core_typed_new_reducible; eauto.
    }
    iIntros "Hown Hnext".
    iApply
      (pico_core_ownP_wp_from_direct_step_contI
        E Phi
        (CoreRun rGamma (SNew x qc C args) V K)
        (mkPicoCoreState h sigma) Hready
        with "Hown Hnext").
  Qed.

  Theorem pico_core_typed_new_fundamentalI :
    forall sGamma sGamma' mt x qc C args
      (Htyping : stmt_typing CT sGamma mt (SNew x qc C args) sGamma'),
      ⊢ pico_core_typed_stmt_wpI
        sGamma mt (SNew x qc C args) sGamma'.
  Proof.
    intros sGamma sGamma' mt x qc C args Htyping.
    unfold pico_core_typed_stmt_wpI.
    iModIntro.
    iIntros (rGamma h sigma V K E Phi)
      "%Henv %Hlrstate Hown Houtcomes".
    iPoseProof
      (pico_core_stmt_post_cont_from_outcomeI
        sGamma' K E Phi with "Houtcomes") as "Hpost".
    iApply
      (pico_core_typed_new_progress_ownP_not_stuck_wpI
        with "Hown [Hpost]"); eauto.
    iNext.
    iIntros (e' state') "%Hstep Hown".
    iApply ("Hpost" $! e' state' with "[] Hown").
    iPureIntro.
    eapply pico_core_typed_new_step_post; eauto.
  Qed.

  Theorem pico_core_typed_call_progress_ownP_not_stuck_wpI :
    forall sGamma sGamma' rGamma h sigma mt x y m args V K E Phi
      (Htyping : stmt_typing CT sGamma mt (SCall x m y args) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h),
      ownP (mkPicoCoreState h sigma) -∗
      (▷ ∀ e' state',
        ⌜pico_core_step CT
          (CoreRun rGamma (SCall x m y args) V K)
          (mkPicoCoreState h sigma) e' state'⌝ -∗
        ownP state' -∗
        WP e' @ NotStuck; E {{ Phi }}) -∗
      WP CoreRun rGamma (SCall x m y args) V K
        @ NotStuck; E {{ Phi }}.
  Proof.
    intros sGamma sGamma' rGamma h sigma mt x y m args V K E Phi
      Htyping Henv.
    assert (Hready :
      exists e' state',
        pico_core_step CT
          (CoreRun rGamma (SCall x m y args) V K)
          (mkPicoCoreState h sigma) e' state').
    {
      apply pico_core_step_from_reducible.
      eapply pico_core_typed_call_reducible; eauto.
    }
    iIntros "Hown Hnext".
    iApply
      (pico_core_ownP_wp_from_direct_step_contI
        E Phi
        (CoreRun rGamma (SCall x m y args) V K)
        (mkPicoCoreState h sigma) Hready
        with "Hown Hnext").
  Qed.

  Theorem pico_core_typed_skip_fundamentalI :
    forall sGamma mt
      (Htyping : stmt_typing CT sGamma mt SSkip sGamma),
      ⊢ pico_core_typed_stmt_wpI sGamma mt SSkip sGamma.
  Proof.
    intros sGamma mt Htyping.
    unfold pico_core_typed_stmt_wpI.
    iModIntro.
    iIntros (rGamma h sigma V K E Phi)
      "%Henv %Hlrstate Hown Hcont".
    unfold pico_core_typed_outcome_contI.
    iDestruct "Hcont" as "[#Hok _]".
    iApply ("Hok" with "[] [] Hown").
    - iPureIntro.
      exact Henv.
    - iPureIntro.
      exact Hlrstate.
  Qed.

  Theorem pico_core_typed_local_fundamentalI :
    forall sGamma sGamma' mt T x
      (Htyping : stmt_typing CT sGamma mt (SLocal T x) sGamma'),
      ⊢ pico_core_typed_stmt_wpI sGamma mt (SLocal T x) sGamma'.
  Proof.
    intros sGamma sGamma' mt T x Htyping.
    unfold pico_core_typed_stmt_wpI.
    iModIntro.
    iIntros (rGamma h sigma V K E Phi)
      "%Henv %Hlrstate Hown Hcont".
    iPoseProof
      (pico_core_stmt_post_cont_from_outcomeI
        sGamma' K E Phi with "Hcont") as "Hpost".
    iApply
      (pico_core_typed_local_ownP_not_stuck_wpI
        with "Hown Hpost"); eauto.
  Qed.

  Theorem pico_core_typed_pure_varass_fundamentalI :
    forall sGamma mt x e
      (Htyping : stmt_typing CT sGamma mt (SVarAss x e) sGamma)
      (Hpure : match e with EField _ _ => False | _ => True end),
      ⊢ pico_core_typed_stmt_wpI sGamma mt (SVarAss x e) sGamma.
  Proof.
    intros sGamma mt x e Htyping Hpure.
    unfold pico_core_typed_stmt_wpI.
    iModIntro.
    iIntros (rGamma h sigma V K E Phi)
      "%Henv %Hlrstate Hown Hcont".
    iPoseProof
      (pico_core_stmt_post_cont_from_outcomeI
        sGamma K E Phi with "Hcont") as "Hpost".
    iApply
      (pico_core_typed_pure_varass_ownP_not_stuck_wpI
        with "Hown Hpost"); eauto.
  Qed.

  (** Sequential composition is the first genuinely compositional LR rule.
      The first statement runs under a [KSeq] frame.  Its successful outcome
      takes the administrative [PCS_SkipSeq] step and starts the second typed
      statement; exceptional outcomes are propagated to the caller unchanged. *)
  Theorem pico_core_typed_seq_compositionI :
    forall sGamma sGamma_mid sGamma' mt s1 s2,
      pico_core_typed_stmt_wpI sGamma mt s1 sGamma_mid -∗
      pico_core_typed_stmt_wpI sGamma_mid mt s2 sGamma' -∗
      pico_core_typed_stmt_wpI
        sGamma mt (SSeq s1 s2) sGamma'.
  Proof.
    intros sGamma sGamma_mid sGamma' mt s1 s2.
    iIntros "#Hfirst #Hsecond".
    unfold pico_core_typed_stmt_wpI.
    iModIntro.
    iIntros (rGamma h sigma V K E Phi)
      "%Henv %Hstate Hown #Hfinal".
    iPoseProof "Hfinal" as "#Hfinal_cases".
    iDestruct "Hfinal_cases" as
      "[#Hfinal_ok [#Hfinal_npe #Hfinal_mutation]]".
    assert (Hseq_ready :
      exists e' state',
        pico_core_step CT
          (CoreRun rGamma (SSeq s1 s2) V K)
          (mkPicoCoreState h sigma) e' state').
    {
      exists (CoreRun rGamma s1 V (KSeq s2 :: K)).
      exists (mkPicoCoreState h sigma).
      apply PCS_Seq.
    }
    iApply
      (pico_core_ownP_wp_from_direct_step_contI
        E Phi
        (CoreRun rGamma (SSeq s1 s2) V K)
        (mkPicoCoreState h sigma) Hseq_ready
        with "Hown").
    iNext.
    iIntros (e' state') "%Hseq Hown".
    inversion Hseq; subst.
    iApply
      ("Hfirst" $! rGamma h sigma V (KSeq s2 :: K) E Phi
        with "[] [] Hown").
    - iPureIntro.
      exact Henv.
    - iPureIntro.
      exact Hstate.
    - unfold pico_core_typed_outcome_contI.
      iSplit.
      + iModIntro.
        iIntros (rGamma_mid state_mid V_mid)
          "%Henv_mid %Hstate_mid Hown_mid".
        destruct state_mid as [h_mid sigma_mid].
        assert (Hskip_ready :
          exists e'' state'',
            pico_core_step CT
              (CoreRun rGamma_mid SSkip V_mid (KSeq s2 :: K))
              (mkPicoCoreState h_mid sigma_mid) e'' state'').
        {
          exists (CoreRun rGamma_mid s2 V_mid K).
          exists (mkPicoCoreState h_mid sigma_mid).
          apply PCS_SkipSeq.
        }
        iApply
          (pico_core_ownP_wp_from_direct_step_contI
            E Phi
            (CoreRun rGamma_mid SSkip V_mid (KSeq s2 :: K))
            (mkPicoCoreState h_mid sigma_mid) Hskip_ready
            with "Hown_mid").
        iNext.
        iIntros (e'' state'') "%Hskip Hown_second".
        inversion Hskip; subst.
        iApply
          ("Hsecond" $! rGamma_mid h_mid sigma_mid V_mid K E Phi
            with "[] [] Hown_second Hfinal").
        * iPureIntro.
          exact Henv_mid.
        * iPureIntro.
          exact Hstate_mid.
      + iSplit.
        * iModIntro.
          iIntros (rGamma_done state_done V_done)
            "%Hstate_done Hown_done".
          iApply ("Hfinal_npe" with "[] Hown_done").
          iPureIntro.
          exact Hstate_done.
        * iModIntro.
          iIntros (rGamma_done state_done V_done)
            "%Hstate_done Hown_done".
          iApply ("Hfinal_mutation" with "[] Hown_done").
          iPureIntro.
          exact Hstate_done.
  Qed.

  (** Semantic implementations of the weak/effectful PICO primitives.  This
      is the sole open-recursion boundary of the structural LR: field reads
      and writes are supplied by the cache protocol, allocation by the state
      invariant, and calls by the guarded method environment. *)
  Definition pico_core_semantic_primitivesI : iProp Sigma :=
    (□ ∀ (sGamma : s_env) (mt : method_scope) (x y f : var),
      ⌜stmt_typing CT sGamma mt
        (SVarAss x (EField y f)) sGamma⌝ -∗
      pico_core_typed_stmt_wpI
        sGamma mt (SVarAss x (EField y f)) sGamma) ∗
    (□ ∀ (sGamma sGamma' : s_env) (mt : method_scope)
          (x f y : var),
      ⌜stmt_typing CT sGamma mt (SFldWrite x f y) sGamma'⌝ -∗
      pico_core_typed_stmt_wpI
        sGamma mt (SFldWrite x f y) sGamma') ∗
    (□ ∀ (sGamma sGamma' : s_env) (mt : method_scope)
          (x : var) (qc : q_c) (C : class_name) (args : list var),
      ⌜stmt_typing CT sGamma mt (SNew x qc C args) sGamma'⌝ -∗
      pico_core_typed_stmt_wpI
        sGamma mt (SNew x qc C args) sGamma') ∗
    (□ ∀ (sGamma sGamma' : s_env) (mt : method_scope)
          (x y : var) (m : method_name) (args : list var),
      ⌜stmt_typing CT sGamma mt (SCall x m y args) sGamma'⌝ -∗
      pico_core_typed_stmt_wpI
        sGamma mt (SCall x m y args) sGamma') ∗
    (□ ∀ (sGamma sGamma' : s_env) (mt : method_scope)
          (x : var) (s_zero s_nonzero : stmt),
      ⌜stmt_typing CT sGamma mt
        (SIfZero x s_zero s_nonzero) sGamma'⌝ -∗
      pico_core_typed_stmt_wpI
        sGamma mt (SIfZero x s_zero s_nonzero) sGamma').

  Definition pico_core_field_read_handlerI : iProp Sigma :=
    □ ∀ (sGamma : s_env) (mt : method_scope) (x y f : var),
      ⌜stmt_typing CT sGamma mt
        (SVarAss x (EField y f)) sGamma⌝ -∗
      pico_core_typed_stmt_wpI
        sGamma mt (SVarAss x (EField y f)) sGamma.

  Definition pico_core_call_handlerI : iProp Sigma :=
    □ ∀ (sGamma sGamma' : s_env) (mt : method_scope)
          (x y : var) (m : method_name) (args : list var),
      ⌜stmt_typing CT sGamma mt (SCall x m y args) sGamma'⌝ -∗
      pico_core_typed_stmt_wpI
        sGamma mt (SCall x m y args) sGamma'.

  (** This older typed-WP handler is the operational boundary for integer
      guards. The canonical resource LR proves [SIfZero] structurally from the
      strict [TInt] value relation and does not require this handler. *)
  Definition pico_core_ifzero_handlerI : iProp Sigma :=
    □ ∀ (sGamma sGamma' : s_env) (mt : method_scope)
          (x : var) (s_zero s_nonzero : stmt),
      ⌜stmt_typing CT sGamma mt
        (SIfZero x s_zero s_nonzero) sGamma'⌝ -∗
      pico_core_typed_stmt_wpI
        sGamma mt (SIfZero x s_zero s_nonzero) sGamma'.

  Theorem pico_core_semantic_primitives_introI :
    pico_core_field_read_handlerI -∗
    pico_core_call_handlerI -∗
    pico_core_ifzero_handlerI -∗
    pico_core_semantic_primitivesI.
  Proof.
    iIntros "#Hread #Hcall #Hifzero".
    unfold pico_core_semantic_primitivesI.
    iSplit; [iExact "Hread" |].
    iSplit.
    - iModIntro.
      iIntros (sGamma sGamma' mt x f y) "%Htyping".
      iApply pico_core_typed_fldwrite_fundamentalI.
      exact Htyping.
    - iSplit.
      + iModIntro.
        iIntros (sGamma sGamma' mt x qc C args) "%Htyping".
        iApply pico_core_typed_new_fundamentalI.
        exact Htyping.
      + iSplit; [iExact "Hcall" | iExact "Hifzero"].
  Qed.

  (** Fundamental theorem for the complete source statement grammar, relative
      only to semantic implementations of its weak/effectful primitives. *)
  Theorem pico_core_stmt_fundamentalI :
    forall sGamma mt s sGamma'
      (Htyping : stmt_typing CT sGamma mt s sGamma'),
      pico_core_semantic_primitivesI -∗
      pico_core_typed_stmt_wpI sGamma mt s sGamma'.
  Proof.
    intros sGamma mt s sGamma' Htyping.
    remember CT as CT_index eqn:HCT in Htyping.
    induction Htyping.
    all: subst CT0.
    - iIntros "_".
      iApply pico_core_typed_skip_fundamentalI.
      constructor.
      exact Hwf.
    - iIntros "_".
      iApply pico_core_typed_local_fundamentalI.
      econstructor; eauto.
    - destruct e as [|source|n|receiver field].
      + iIntros "_".
        iApply pico_core_typed_pure_varass_fundamentalI.
        * econstructor; eauto.
        * exact I.
      + iIntros "_".
        iApply pico_core_typed_pure_varass_fundamentalI.
        * econstructor; eauto.
        * exact I.
      + iIntros "_".
        iApply pico_core_typed_pure_varass_fundamentalI.
        * econstructor; eauto.
        * exact I.
      + iIntros "#Hprimitives".
        iDestruct "Hprimitives" as "[#Hread _]".
        iApply ("Hread" $! sΓ mt x receiver field).
        iPureIntro.
        econstructor; eauto.
    - iIntros "#Hprimitives".
      iDestruct "Hprimitives" as "[_ [#Hwrite _]]".
      iApply ("Hwrite" $! sΓ sΓ AbstractState x f y).
      iPureIntro.
      econstructor; eauto.
    - iIntros "#Hprimitives".
      iDestruct "Hprimitives" as "[_ [#Hwrite _]]".
      iApply ("Hwrite" $! sΓ sΓ ConcreteState x f y).
      iPureIntro.
      econstructor; eauto.
    - iIntros "#Hprimitives".
      iDestruct "Hprimitives" as "[_ [#Hwrite _]]".
      iApply ("Hwrite" $! sΓ sΓ ReadonlyState x f y).
      iPureIntro.
      econstructor; eauto.
    - iIntros "#Hprimitives".
      iDestruct "Hprimitives" as "[_ [#Hwrite _]]".
      iApply ("Hwrite" $! sΓ sΓ TransitiveState x f y).
      iPureIntro.
      econstructor; eauto.
    - iIntros "#Hprimitives".
      iDestruct "Hprimitives" as "[_ [_ [#Hnew _]]]".
      iApply ("Hnew" $! sΓ sΓ mt x qc C args).
      iPureIntro.
      econstructor; eauto.
    - iIntros "#Hprimitives".
      iDestruct "Hprimitives" as "[_ [_ [_ [#Hcall _]]]]".
      iApply ("Hcall" $! sΓ sΓ mt x y m args).
      iPureIntro.
      eapply ST_Call; eauto.
    - iIntros "#Hprimitives".
      iDestruct "Hprimitives" as "[_ [_ [_ [#Hcall _]]]]".
      iApply ("Hcall" $! sΓ sΓ mt x y m args).
      iPureIntro.
      eapply ST_Call_readonly_state; eauto.
    - iIntros "#Hprimitives".
      iApply pico_core_typed_seq_compositionI.
      + iApply (IHHtyping1 eq_refl).
        iExact "Hprimitives".
      + iApply (IHHtyping2 eq_refl).
        iExact "Hprimitives".
    - iIntros "#Hprimitives".
      iDestruct "Hprimitives" as "[_ [_ [_ [_ #Hifzero]]]]".
      iApply ("Hifzero" $! sΓ sΓ' mt x s_zero s_nonzero).
      iPureIntro.
      econstructor; eauto.
  Qed.
End pico_typing_fundamental_ownp.
