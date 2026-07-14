From iris.program_logic Require Import weakestpre ownp.
From iris.proofmode Require Import proofmode.

Require Import Syntax Helpers Typing Bigstep Properties ViewpointAdaptation.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage
  PICOBridge.PicoIrisCoreInvariant PICOBridge.PicoIrisTypingFundamental.

(** * Linear-Resource PICO Statement Interpretation

    The core typing LR proves operational safety and typed runtime outcomes.
    This layer additionally threads one linear semantic resource [R state]
    through the actually selected outcome.  The resource is state-indexed so
    cache-history ghost ownership can track weak-memory updates without being
    duplicated across success and exceptional branches. *)

Section pico_resource_logical_relation.
  Context `{Hmem : CacheMemoryModel}.
  Context `{Hprogress : CacheMemoryModelProgress}.
  Context (CT : class_table).
  Context `{!ownPGS (pico_core_language CT) Sigma}.

  (** The source language reserves variable [0] for the receiver.  A statement
      interpretation records its concrete receiver identity, not merely the
      receiver's type, because call-return viewpoint adaptation depends on the
      callee still denoting the object selected at call entry. *)
  Definition pico_core_receiver_eq (receiver : Loc) (rGamma : r_env) : Prop :=
    get_this_var_mapping (vars rGamma) = Some receiver.

  Definition pico_core_expr_receiver_eq
      (receiver : Loc) (e : pico_core_expr) : Prop :=
    match e with
    | CoreRun rGamma _ _ _ => pico_core_receiver_eq receiver rGamma
    | CoreDone _ _ _ => True
    end.

  Definition pico_core_resource_outcome_contI
      (R : pico_core_state -> iProp Sigma)
      (entry_heap : heap) (entry_receiver : Loc)
      (sGamma' : s_env) (K : pico_core_cont)
      (E : coPset)
      (Phi : val (pico_core_language CT) -> iProp Sigma) : iProp Sigma :=
    (□ ∀ rGamma state V,
      ⌜pico_core_typed_env CT sGamma' rGamma (pcs_heap state)⌝ -∗
      ⌜pico_core_lr_state CT state⌝ -∗
      ⌜pico_core_heap_types_extend entry_heap (pcs_heap state)⌝ -∗
      ⌜pico_core_receiver_eq entry_receiver rGamma⌝ -∗
      R state -∗
      ownP state -∗
      WP CoreRun rGamma SSkip V K @ NotStuck; E {{ Phi }}) ∗
    (□ ∀ rGamma state V,
      ⌜pico_core_lr_state CT state⌝ -∗
      ⌜pico_core_heap_types_extend entry_heap (pcs_heap state)⌝ -∗
      R state -∗
      ownP state -∗
      WP CoreDone NPE rGamma V @ NotStuck; E {{ Phi }}) ∗
    (□ ∀ rGamma state V,
      ⌜pico_core_lr_state CT state⌝ -∗
      ⌜pico_core_heap_types_extend entry_heap (pcs_heap state)⌝ -∗
      R state -∗
      ownP state -∗
      WP CoreDone MUTATIONEXP rGamma V @ NotStuck; E {{ Phi }}).

  Definition pico_core_resource_post_contI
      (R : pico_core_state -> iProp Sigma)
      (entry_heap : heap) (entry_receiver : Loc)
      (sGamma' : s_env) (K : pico_core_cont)
      (E : coPset)
      (Phi : val (pico_core_language CT) -> iProp Sigma) : iProp Sigma :=
    ▷ ∀ e' state',
      ⌜pico_core_stmt_post CT sGamma' K e' state'⌝ -∗
      ⌜pico_core_heap_types_extend entry_heap (pcs_heap state')⌝ -∗
      ⌜pico_core_expr_receiver_eq entry_receiver e'⌝ -∗
      R state' -∗
      ownP state' -∗
      WP e' @ NotStuck; E {{ Phi }}.

  Definition pico_core_resource_stmt_wpI
      (R : pico_core_state -> iProp Sigma)
      (sGamma : s_env) (mt : method_type)
      (s : stmt) (sGamma' : s_env) : iProp Sigma :=
    □ ∀ rGamma entry_receiver h sigma V K E Phi,
      ⌜pico_core_typed_env CT sGamma rGamma h⌝ -∗
      ⌜pico_core_receiver_eq entry_receiver rGamma⌝ -∗
      ⌜pico_core_lr_state CT (mkPicoCoreState h sigma)⌝ -∗
      R (mkPicoCoreState h sigma) -∗
      ownP (mkPicoCoreState h sigma) -∗
      pico_core_resource_outcome_contI
        R h entry_receiver sGamma' K E Phi -∗
      WP CoreRun rGamma s V K @ NotStuck; E {{ Phi }}.

  Lemma pico_core_resource_post_cont_from_outcomeI :
    forall R entry_heap entry_receiver sGamma' K E Phi,
      pico_core_resource_outcome_contI
        R entry_heap entry_receiver sGamma' K E Phi -∗
      pico_core_resource_post_contI
        R entry_heap entry_receiver sGamma' K E Phi.
  Proof.
    intros R entry_heap entry_receiver sGamma' K E Phi.
    iIntros "[#Hok [#Hnpe #Hmutation]]".
    unfold pico_core_resource_post_contI.
    iNext.
    iIntros (e' state') "Hpost Hextend Hreceiver HR Hown".
    iDestruct "Hpost" as %Hpost.
    inversion Hpost; subst.
    - iApply ("Hok" with "[] [] Hextend Hreceiver HR Hown");
        iPureIntro; assumption.
    - iApply ("Hnpe" with "[] Hextend HR Hown").
      iPureIntro.
      assumption.
    - iApply ("Hmutation" with "[] Hextend HR Hown").
      iPureIntro.
      assumption.
  Qed.

  (** Generic lifting rule for a typed primitive whose operational step does
      not change the core state. *)
  Lemma pico_core_resource_same_state_atomic_wpI :
    forall R E Phi e state entry_receiver sGamma' K
      (Hready : exists e' state', pico_core_step CT e state e' state')
      (Hpost : forall e' state',
        pico_core_step CT e state e' state' ->
        pico_core_stmt_post CT sGamma' K e' state')
      (Hsame : forall e' state',
        pico_core_step CT e state e' state' -> state' = state)
      (Hreceiver : forall e' state',
        pico_core_step CT e state e' state' ->
        pico_core_expr_receiver_eq entry_receiver e'),
      R state -∗
      ownP state -∗
      pico_core_resource_post_contI
        R (pcs_heap state) entry_receiver sGamma' K E Phi -∗
      WP e @ NotStuck; E {{ Phi }}.
  Proof.
    intros R E Phi e state entry_receiver sGamma' K Hready Hpost Hsame
      Hreceiver.
    iIntros "HR Hown Hcont".
    iApply
      (pico_core_ownP_wp_from_direct_step_contI
        CT E Phi e state Hready with "Hown [HR Hcont]").
    iNext.
    iIntros (e' state') "%Hstep Hown".
    pose proof (Hsame e' state' Hstep) as ->.
    iApply ("Hcont" $! e' state with "[] [] [] HR Hown").
    - iPureIntro.
      eapply Hpost; eauto.
    - iPureIntro.
      apply pico_core_heap_types_extend_refl.
    - iPureIntro.
      eapply Hreceiver; eauto.
  Qed.

  (** Every nonterminal, non-call core step preserves the concrete receiver.
      A terminal [Skip] may pop a call frame, and calls change the active
      frame, so their stronger entry/return relation is proved separately. *)
  Lemma pico_core_typed_primitive_step_preserves_receiver :
    forall sGamma sGamma' mt s rGamma h sigma V K e' state' receiver,
      stmt_typing CT sGamma mt s sGamma' ->
      pico_core_receiver_eq receiver rGamma ->
      (match s with
       | SSkip | SCall _ _ _ _ => False
       | _ => True
       end) ->
      pico_core_step CT
        (CoreRun rGamma s V K) (mkPicoCoreState h sigma) e' state' ->
      pico_core_expr_receiver_eq receiver e'.
  Proof.
    intros sGamma sGamma' mt s rGamma h sigma V K e' state' receiver
      Htyping Hreceiver Hnoncall Hstep.
    destruct s; simpl in Hnoncall; try contradiction.
    - inversion Hstep; subst; simpl.
      + change (get_this_var_mapping
          (vars (set_vars rGamma (vars rGamma ++ [default_value q]))) =
          Some receiver).
        rewrite get_this_var_mapping_update_vars_app_default.
        exact Hreceiver.
    - destruct e; inversion Hstep; subst;
        unfold pico_core_expr_receiver_eq, pico_core_receiver_eq.
      + inversion Htyping; subst.
        rewrite get_this_var_mapping_update_vars_nonzero; eauto.
      + inversion Htyping; subst.
        rewrite get_this_var_mapping_update_vars_nonzero; eauto.
      + inversion Htyping; subst.
        rewrite get_this_var_mapping_update_vars_nonzero; eauto.
      + inversion Htyping; subst.
        rewrite get_this_var_mapping_update_vars_nonzero; eauto.
      + exact I.
    - inversion Hstep; subst;
        unfold pico_core_expr_receiver_eq, pico_core_receiver_eq.
      + exact Hreceiver.
      + exact I.
      + exact I.
    - inversion Hstep; subst;
        unfold pico_core_expr_receiver_eq, pico_core_receiver_eq.
      inversion Htyping; subst.
      rewrite get_this_var_mapping_update_vars_nonzero; eauto.
    - inversion Hstep; subst; simpl.
      exact Hreceiver.
    - inversion Hstep; subst; simpl; auto.
  Qed.

  Lemma pico_core_typed_call_return_preserves_receiver :
    forall sGamma sGamma' mt x y m args rGamma receiver retval,
      stmt_typing CT sGamma mt (SCall x y m args) sGamma' ->
      pico_core_receiver_eq receiver rGamma ->
      pico_core_receiver_eq receiver
        (set_vars rGamma (update x retval (vars rGamma))).
  Proof.
    intros sGamma sGamma' mt x y m args rGamma receiver retval
      Htyping Hreceiver.
    unfold pico_core_receiver_eq in *.
    inversion Htyping; subst;
      rewrite get_this_var_mapping_update_vars_nonzero; eauto.
  Qed.

  Theorem pico_core_resource_skip_fundamentalI :
    forall R sGamma mt
      (Htyping : stmt_typing CT sGamma mt SSkip sGamma),
      ⊢ pico_core_resource_stmt_wpI R sGamma mt SSkip sGamma.
  Proof.
    intros R sGamma mt Htyping.
    unfold pico_core_resource_stmt_wpI.
    iModIntro.
    iIntros (rGamma entry_receiver h sigma V K E Phi)
      "%Henv %Hreceiver %Hstate HR Hown Houtcomes".
    unfold pico_core_resource_outcome_contI.
    iDestruct "Houtcomes" as "[#Hok _]".
    iApply ("Hok" with "[] [] [] [] HR Hown").
    - iPureIntro. exact Henv.
    - iPureIntro. exact Hstate.
    - iPureIntro. apply pico_core_heap_types_extend_refl.
    - iPureIntro. exact Hreceiver.
  Qed.

  Theorem pico_core_resource_local_fundamentalI :
    forall R sGamma sGamma' mt T x
      (Htyping : stmt_typing CT sGamma mt (SLocal T x) sGamma'),
      ⊢ pico_core_resource_stmt_wpI
        R sGamma mt (SLocal T x) sGamma'.
  Proof.
    intros R sGamma sGamma' mt T x Htyping.
    unfold pico_core_resource_stmt_wpI.
    iModIntro.
    iIntros (rGamma entry_receiver h sigma V K E Phi)
      "%Henv %Hreceiver %Hstate HR Hown Houtcomes".
    iPoseProof
      (pico_core_resource_post_cont_from_outcomeI
        R h entry_receiver sGamma' K E Phi with "Houtcomes") as "Hpost".
    assert (Hready :
      exists e' state',
        pico_core_step CT
          (CoreRun rGamma (SLocal T x) V K)
          (mkPicoCoreState h sigma) e' state').
    {
      apply pico_core_step_from_reducible.
      eapply pico_core_typed_local_reducible; eauto.
    }
    iApply
      (pico_core_resource_same_state_atomic_wpI
        R E Phi
        (CoreRun rGamma (SLocal T x) V K)
        (mkPicoCoreState h sigma) entry_receiver sGamma' K Hready
        with "HR Hown Hpost").
    - intros e' state' Hstep.
      eapply pico_core_typed_local_step_post; eauto.
    - intros e' state' Hstep.
      inversion Hstep; subst; reflexivity.
    - intros e' state' Hstep.
      eapply pico_core_typed_primitive_step_preserves_receiver; eauto.
      exact I.
  Qed.

  Theorem pico_core_resource_pure_varass_fundamentalI :
    forall R sGamma mt x e
      (Htyping : stmt_typing CT sGamma mt (SVarAss x e) sGamma)
      (Hpure : match e with EField _ _ => False | _ => True end),
      ⊢ pico_core_resource_stmt_wpI
        R sGamma mt (SVarAss x e) sGamma.
  Proof.
    intros R sGamma mt x e Htyping Hpure.
    unfold pico_core_resource_stmt_wpI.
    iModIntro.
    iIntros (rGamma entry_receiver h sigma V K E Phi)
      "%Henv %Hreceiver %Hstate HR Hown Houtcomes".
    iPoseProof
      (pico_core_resource_post_cont_from_outcomeI
        R h entry_receiver sGamma K E Phi with "Houtcomes") as "Hpost".
    destruct e as [|y|n|y f].
    - assert (Hready :
        exists e' state',
          pico_core_step CT
            (CoreRun rGamma (SVarAss x ENull) V K)
            (mkPicoCoreState h sigma) e' state').
      {
        apply pico_core_step_from_reducible.
        eapply pico_core_typed_assign_null_reducible; eauto.
      }
      iApply
        (pico_core_resource_same_state_atomic_wpI
          R E Phi (CoreRun rGamma (SVarAss x ENull) V K)
          (mkPicoCoreState h sigma) entry_receiver sGamma K Hready
          with "HR Hown Hpost").
      + intros e' state' Hstep.
        eapply pico_core_typed_assign_null_step_post; eauto.
      + intros e' state' Hstep.
        inversion Hstep; subst; reflexivity.
      + intros e' state' Hstep.
        eapply pico_core_typed_primitive_step_preserves_receiver; eauto.
    - assert (Hready :
        exists e' state',
          pico_core_step CT
            (CoreRun rGamma (SVarAss x (EVar y)) V K)
            (mkPicoCoreState h sigma) e' state').
      {
        apply pico_core_step_from_reducible.
        eapply pico_core_typed_assign_var_reducible; eauto.
      }
      iApply
        (pico_core_resource_same_state_atomic_wpI
          R E Phi (CoreRun rGamma (SVarAss x (EVar y)) V K)
          (mkPicoCoreState h sigma) entry_receiver sGamma K Hready
          with "HR Hown Hpost").
      + intros e' state' Hstep.
        eapply pico_core_typed_assign_var_step_post; eauto.
      + intros e' state' Hstep.
        inversion Hstep; subst; reflexivity.
      + intros e' state' Hstep.
        eapply pico_core_typed_primitive_step_preserves_receiver; eauto.
    - assert (Hready :
        exists e' state',
          pico_core_step CT
            (CoreRun rGamma (SVarAss x (EInt n)) V K)
            (mkPicoCoreState h sigma) e' state').
      {
        apply pico_core_step_from_reducible.
        eapply pico_core_typed_assign_int_reducible; eauto.
      }
      iApply
        (pico_core_resource_same_state_atomic_wpI
          R E Phi (CoreRun rGamma (SVarAss x (EInt n)) V K)
          (mkPicoCoreState h sigma) entry_receiver sGamma K Hready
          with "HR Hown Hpost").
      + intros e' state' Hstep.
        eapply pico_core_typed_assign_int_step_post; eauto.
      + intros e' state' Hstep.
        inversion Hstep; subst; reflexivity.
      + intros e' state' Hstep.
        eapply pico_core_typed_primitive_step_preserves_receiver; eauto.
    - contradiction.
  Qed.

  Definition pico_core_resource_read_ruleI
      (R : pico_core_state -> iProp Sigma) : iProp Sigma :=
    □ ∀ (sGamma : s_env) (mt : method_type)
          (rGamma : r_env) (h : heap) (sigma : wm_state)
          (x y f : var) (V : view) (loc : Loc) (v : value) (V' : view),
      ⌜stmt_typing CT sGamma mt
        (SVarAss x (EField y f)) sGamma⌝ -∗
      ⌜pico_core_typed_env CT sGamma rGamma h⌝ -∗
      ⌜runtime_getVal rGamma y = Some (Iot loc)⌝ -∗
      ⌜wm_read sigma V (loc, f) v V'⌝ -∗
      R (mkPicoCoreState h sigma) -∗
      R (mkPicoCoreState h sigma) ∗
      ⌜pico_core_typed_env CT sGamma
        (set_vars rGamma (update x v (vars rGamma))) h⌝.

  Definition pico_core_resource_write_ruleI
      (R : pico_core_state -> iProp Sigma) : iProp Sigma :=
    □ ∀ (h h' : heap) (sigma sigma' : wm_state)
          (V V' : view) (loc : Loc) (f : var) (v : value),
      ⌜h' = update_field h loc f v⌝ -∗
      ⌜wm_write sigma sigma' V V' (loc, f) v⌝ -∗
      R (mkPicoCoreState h sigma) ==∗
      R (mkPicoCoreState h' sigma').

  Definition pico_core_resource_alloc_ruleI
      (R : pico_core_state -> iProp Sigma) : iProp Sigma :=
    □ ∀ (h : heap) (sigma : wm_state) (o : Obj) (V : view),
      R (mkPicoCoreState h sigma) ==∗
      R (mkPicoCoreState
        (h ++ [o]) (pico_core_alloc_weak sigma o V)).

  Definition pico_core_resource_call_handlerI
      (R : pico_core_state -> iProp Sigma) : iProp Sigma :=
    □ ∀ (sGamma sGamma' : s_env) (mt : method_type)
          (x y : var) (m : method_name) (args : list var),
      ⌜stmt_typing CT sGamma mt (SCall x y m args) sGamma'⌝ -∗
      pico_core_resource_stmt_wpI
        R sGamma mt (SCall x y m args) sGamma'.

  Theorem pico_core_resource_read_handlerI :
    forall R,
      pico_core_resource_read_ruleI R -∗
      □ ∀ (sGamma : s_env) (mt : method_type) (x y f : var),
        ⌜stmt_typing CT sGamma mt
          (SVarAss x (EField y f)) sGamma⌝ -∗
        pico_core_resource_stmt_wpI
          R sGamma mt (SVarAss x (EField y f)) sGamma.
  Proof.
    intros R.
    iIntros "#Hread_rule".
    iModIntro.
    iIntros (sGamma mt x y f) "%Htyping".
    unfold pico_core_resource_stmt_wpI.
    iModIntro.
    iIntros (rGamma entry_receiver h sigma V K E Phi)
      "%Henv %Hreceiver %Hstate HR Hown Houtcomes".
    iPoseProof
      (pico_core_resource_post_cont_from_outcomeI
        R h entry_receiver sGamma K E Phi with "Houtcomes") as "Hpost".
    assert (Hready :
      exists e' state',
        pico_core_step CT
          (CoreRun rGamma (SVarAss x (EField y f)) V K)
          (mkPicoCoreState h sigma) e' state').
    {
      apply pico_core_step_from_reducible.
      eapply pico_core_typed_varass_field_reducible; eauto.
    }
    iApply
      (pico_core_ownP_wp_from_direct_step_contI
        CT E Phi
        (CoreRun rGamma (SVarAss x (EField y f)) V K)
        (mkPicoCoreState h sigma) Hready
        with "Hown [HR Hpost]").
    iNext.
    iIntros (e' state') "%Hstep Hown".
    inversion Hstep; subst; try discriminate; try congruence.
    - iDestruct
        ("Hread_rule" $! sGamma mt rGamma h sigma x y f V
          loc_y v V' with "[] [] [] [] HR")
        as "[HR %Henv_next]".
      + iPureIntro. exact Htyping.
      + iPureIntro. exact Henv.
      + iPureIntro. assumption.
      + iPureIntro. assumption.
      + iApply ("Hpost" with "[] [] [] HR Hown").
        * iPureIntro. apply PCSP_Ok; assumption.
        * iPureIntro. apply pico_core_heap_types_extend_refl.
        * iPureIntro.
          eapply pico_core_typed_primitive_step_preserves_receiver; eauto.
          exact I.
    - iApply ("Hpost" with "[] [] [] HR Hown").
      + iPureIntro. apply PCSP_NPE. exact Hstate.
      + iPureIntro. apply pico_core_heap_types_extend_refl.
      + iPureIntro. exact I.
  Qed.

  Theorem pico_core_resource_write_handlerI :
    forall R,
      pico_core_resource_write_ruleI R -∗
      □ ∀ (sGamma sGamma' : s_env) (mt : method_type)
            (x f y : var),
        ⌜stmt_typing CT sGamma mt (SFldWrite x f y) sGamma'⌝ -∗
        pico_core_resource_stmt_wpI
          R sGamma mt (SFldWrite x f y) sGamma'.
  Proof.
    intros R.
    iIntros "#Hwrite_rule".
    iModIntro.
    iIntros (sGamma sGamma' mt x f y) "%Htyping".
    unfold pico_core_resource_stmt_wpI.
    iModIntro.
    iIntros (rGamma entry_receiver h sigma V K E Phi)
      "%Henv %Hreceiver %Hstate HR Hown Houtcomes".
    iPoseProof
      (pico_core_resource_post_cont_from_outcomeI
        R h entry_receiver sGamma' K E Phi with "Houtcomes") as "Hpost".
    assert (Hready :
      exists e' state',
        pico_core_step CT
          (CoreRun rGamma (SFldWrite x f y) V K)
          (mkPicoCoreState h sigma) e' state').
    {
      apply pico_core_step_from_reducible.
      eapply pico_core_typed_fldwrite_reducible; eauto.
    }
    iApply
      (pico_core_ownP_wp_from_direct_step_contI
        CT E Phi (CoreRun rGamma (SFldWrite x f y) V K)
        (mkPicoCoreState h sigma) Hready
        with "Hown [HR Hpost]").
    iNext.
    iIntros (e' state') "%Hstep Hown".
    pose proof Hstep as Hstep_copy.
    inversion Hstep; subst; try discriminate; try congruence.
    - match goal with
      | Hwrite : wm_write sigma ?sigma_next V ?view_next
          (loc_x, f) val_y |- _ =>
          iMod
            ("Hwrite_rule" $! h (update_field h loc_x f val_y)
              sigma sigma_next V view_next loc_x f val_y
              with "[] [] HR") as "HR"
      end.
      + iPureIntro. reflexivity.
      + iPureIntro. assumption.
      + iApply ("Hpost" with "[] [] [] HR Hown").
        * iPureIntro. eapply pico_core_typed_fldwrite_step_post; eauto.
        * iPureIntro.
          pose proof
            (pico_core_step_preserves_heap_types
              CT _ _ _ _ Hstep_copy) as Hextend.
          simpl in Hextend. exact Hextend.
        * iPureIntro.
          eapply pico_core_typed_primitive_step_preserves_receiver; eauto.
          exact I.
    - iApply ("Hpost" with "[] [] [] HR Hown").
      + iPureIntro. eapply pico_core_typed_fldwrite_step_post; eauto.
      + iPureIntro.
        pose proof
          (pico_core_step_preserves_heap_types
            CT _ _ _ _ Hstep_copy) as Hextend.
        simpl in Hextend. exact Hextend.
      + iPureIntro. exact I.
    - iApply ("Hpost" with "[] [] [] HR Hown").
      + iPureIntro. eapply pico_core_typed_fldwrite_step_post; eauto.
      + iPureIntro.
        pose proof
          (pico_core_step_preserves_heap_types
            CT _ _ _ _ Hstep_copy) as Hextend.
        simpl in Hextend. exact Hextend.
      + iPureIntro. exact I.
  Qed.

  Theorem pico_core_resource_alloc_handlerI :
    forall R,
      pico_core_resource_alloc_ruleI R -∗
      □ ∀ (sGamma sGamma' : s_env) (mt : method_type)
            (x : var) (qc : q_c) (C : class_name) (args : list var),
        ⌜stmt_typing CT sGamma mt (SNew x qc C args) sGamma'⌝ -∗
        pico_core_resource_stmt_wpI
          R sGamma mt (SNew x qc C args) sGamma'.
  Proof.
    intros R.
    iIntros "#Halloc_rule".
    iModIntro.
    iIntros (sGamma sGamma' mt x qc C args) "%Htyping".
    unfold pico_core_resource_stmt_wpI.
    iModIntro.
    iIntros (rGamma entry_receiver h sigma V K E Phi)
      "%Henv %Hreceiver %Hstate HR Hown Houtcomes".
    iPoseProof
      (pico_core_resource_post_cont_from_outcomeI
        R h entry_receiver sGamma' K E Phi with "Houtcomes") as "Hpost".
    assert (Hready :
      exists e' state',
        pico_core_step CT
          (CoreRun rGamma (SNew x qc C args) V K)
          (mkPicoCoreState h sigma) e' state').
    {
      apply pico_core_step_from_reducible.
      eapply pico_core_typed_new_reducible; eauto.
    }
    iApply
      (pico_core_ownP_wp_from_direct_step_contI
        CT E Phi (CoreRun rGamma (SNew x qc C args) V K)
        (mkPicoCoreState h sigma) Hready
        with "Hown [HR Hpost]").
    iNext.
    iIntros (e' state') "%Hstep Hown".
    pose proof Hstep as Hstep_copy.
    inversion Hstep; subst; try discriminate; try congruence.
    iMod
      ("Halloc_rule" $! h sigma
        (mkObj
          (mkruntime_type
            (vpa_mutability_object_creation qthisr qc) C)
          vals) V
        with "HR") as "HR".
    iApply ("Hpost" with "[] [] [] HR Hown").
    - iPureIntro. eapply pico_core_typed_new_step_post; eauto.
    - iPureIntro.
      pose proof
        (pico_core_step_preserves_heap_types
          CT _ _ _ _ Hstep_copy) as Hextend.
      simpl in Hextend. exact Hextend.
    - iPureIntro.
      eapply pico_core_typed_primitive_step_preserves_receiver; eauto.
      exact I.
  Qed.

  Theorem pico_core_resource_seq_compositionI :
    forall R sGamma sGamma_mid sGamma' mt s1 s2,
      pico_core_resource_stmt_wpI R sGamma mt s1 sGamma_mid -∗
      pico_core_resource_stmt_wpI R sGamma_mid mt s2 sGamma' -∗
      pico_core_resource_stmt_wpI
        R sGamma mt (SSeq s1 s2) sGamma'.
  Proof.
    intros R sGamma sGamma_mid sGamma' mt s1 s2.
    iIntros "#Hfirst #Hsecond".
    unfold pico_core_resource_stmt_wpI.
    iModIntro.
    iIntros (rGamma entry_receiver h sigma V K E Phi)
      "%Henv %Hreceiver %Hstate HR Hown #Hfinal".
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
        CT E Phi
        (CoreRun rGamma (SSeq s1 s2) V K)
        (mkPicoCoreState h sigma) Hseq_ready
        with "Hown [HR]").
    iNext.
    iIntros (e' state') "%Hseq Hown".
    inversion Hseq; subst.
    iApply
      ("Hfirst" $! rGamma entry_receiver h sigma V (KSeq s2 :: K) E Phi
        with "[] [] [] HR Hown").
    - iPureIntro. exact Henv.
    - iPureIntro. exact Hreceiver.
    - iPureIntro. exact Hstate.
    - unfold pico_core_resource_outcome_contI.
      iSplit.
      + iModIntro.
        iIntros (rGamma_mid state_mid V_mid)
          "%Henv_mid %Hstate_mid %Hextend_first %Hreceiver_mid HR_mid Hown_mid".
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
            CT E Phi
            (CoreRun rGamma_mid SSkip V_mid (KSeq s2 :: K))
            (mkPicoCoreState h_mid sigma_mid) Hskip_ready
            with "Hown_mid [HR_mid]").
        iNext.
        iIntros (e'' state'') "%Hskip Hown_second".
        inversion Hskip; subst.
        iApply
          ("Hsecond" $! rGamma_mid entry_receiver h_mid sigma_mid V_mid K E Phi
            with "[] [] [] HR_mid Hown_second").
        * iPureIntro. exact Henv_mid.
        * iPureIntro. exact Hreceiver_mid.
        * iPureIntro. exact Hstate_mid.
        * unfold pico_core_resource_outcome_contI.
          iSplit.
          -- iModIntro.
             iIntros (rGamma_done state_done V_done)
               "%Henv_done %Hstate_done %Hextend_second %Hreceiver_done HR_done Hown_done".
             iApply
               ("Hfinal_ok" with "[] [] [] [] HR_done Hown_done").
             ++ iPureIntro. exact Henv_done.
             ++ iPureIntro. exact Hstate_done.
             ++ iPureIntro.
                eapply pico_core_heap_types_extend_trans; eauto.
             ++ iPureIntro. exact Hreceiver_done.
          -- iSplit.
             ++ iModIntro.
                iIntros (rGamma_done state_done V_done)
                  "%Hstate_done %Hextend_second HR_done Hown_done".
                iApply
                  ("Hfinal_npe" with "[] [] HR_done Hown_done").
                ** iPureIntro. exact Hstate_done.
                ** iPureIntro.
                   eapply pico_core_heap_types_extend_trans; eauto.
             ++ iModIntro.
                iIntros (rGamma_done state_done V_done)
                  "%Hstate_done %Hextend_second HR_done Hown_done".
                iApply
                  ("Hfinal_mutation" with "[] [] HR_done Hown_done").
                ** iPureIntro. exact Hstate_done.
                ** iPureIntro.
                   eapply pico_core_heap_types_extend_trans; eauto.
      + iSplit.
        * iModIntro.
          iIntros (rGamma_done state_done V_done)
            "%Hstate_done %Hextend_done HR_done Hown_done".
          iApply
            ("Hfinal_npe" with "[] [] HR_done Hown_done").
          -- iPureIntro. exact Hstate_done.
          -- iPureIntro. exact Hextend_done.
        * iModIntro.
          iIntros (rGamma_done state_done V_done)
            "%Hstate_done %Hextend_done HR_done Hown_done".
          iApply
            ("Hfinal_mutation" with "[] [] HR_done Hown_done").
          -- iPureIntro. exact Hstate_done.
          -- iPureIntro. exact Hextend_done.
  Qed.

  Definition pico_core_resource_semantic_primitivesI
      (R : pico_core_state -> iProp Sigma) : iProp Sigma :=
    (□ ∀ (sGamma : s_env) (mt : method_type) (x y f : var),
      ⌜stmt_typing CT sGamma mt
        (SVarAss x (EField y f)) sGamma⌝ -∗
      pico_core_resource_stmt_wpI
        R sGamma mt (SVarAss x (EField y f)) sGamma) ∗
    (□ ∀ (sGamma sGamma' : s_env) (mt : method_type)
          (x f y : var),
      ⌜stmt_typing CT sGamma mt (SFldWrite x f y) sGamma'⌝ -∗
      pico_core_resource_stmt_wpI
        R sGamma mt (SFldWrite x f y) sGamma') ∗
    (□ ∀ (sGamma sGamma' : s_env) (mt : method_type)
          (x : var) (qc : q_c) (C : class_name) (args : list var),
      ⌜stmt_typing CT sGamma mt (SNew x qc C args) sGamma'⌝ -∗
      pico_core_resource_stmt_wpI
        R sGamma mt (SNew x qc C args) sGamma') ∗
    □ ∀ (sGamma sGamma' : s_env) (mt : method_type)
          (x y : var) (m : method_name) (args : list var),
      ⌜stmt_typing CT sGamma mt (SCall x y m args) sGamma'⌝ -∗
      pico_core_resource_stmt_wpI
        R sGamma mt (SCall x y m args) sGamma'.

  Theorem pico_core_resource_stmt_fundamentalI :
    forall R sGamma mt s sGamma'
      (Htyping : stmt_typing CT sGamma mt s sGamma'),
      pico_core_resource_semantic_primitivesI R -∗
      pico_core_resource_stmt_wpI R sGamma mt s sGamma'.
  Proof.
    intros R sGamma mt s sGamma' Htyping.
    remember CT as CT_index eqn:HCT in Htyping.
    induction Htyping.
    all: subst CT0.
    - iIntros "_".
      iApply pico_core_resource_skip_fundamentalI.
      constructor. exact Hwf.
    - iIntros "_".
      iApply pico_core_resource_local_fundamentalI.
      econstructor; eauto.
    - destruct e as [|source|n|receiver field].
      + iIntros "_".
        iApply pico_core_resource_pure_varass_fundamentalI.
        * econstructor; eauto.
        * exact I.
      + iIntros "_".
        iApply pico_core_resource_pure_varass_fundamentalI.
        * econstructor; eauto.
        * exact I.
      + iIntros "_".
        iApply pico_core_resource_pure_varass_fundamentalI.
        * econstructor; eauto.
        * exact I.
      + iIntros "#Hprimitives".
        iDestruct "Hprimitives" as "[#Hread _]".
        iApply ("Hread" $! sΓ mt x receiver field).
        iPureIntro. econstructor; eauto.
    - iIntros "#Hprimitives".
      iDestruct "Hprimitives" as "[_ [#Hwrite _]]".
      iApply ("Hwrite" $! sΓ sΓ AbstractImm x f y).
      iPureIntro. econstructor; eauto.
    - iIntros "#Hprimitives".
      iDestruct "Hprimitives" as "[_ [#Hwrite _]]".
      iApply ("Hwrite" $! sΓ sΓ SafeRO x f y).
      iPureIntro. econstructor; eauto.
    - iIntros "#Hprimitives".
      iDestruct "Hprimitives" as "[_ [#Hwrite _]]".
      iApply ("Hwrite" $! sΓ sΓ ConcreteImm x f y).
      iPureIntro. econstructor; eauto.
    - iIntros "#Hprimitives".
      iDestruct "Hprimitives" as "[_ [_ [#Hnew _]]]".
      iApply ("Hnew" $! sΓ sΓ mt x qc C args).
      iPureIntro. econstructor; eauto.
    - iIntros "#Hprimitives".
      iDestruct "Hprimitives" as "[_ [_ [_ #Hcall]]]".
      iApply ("Hcall" $! sΓ sΓ AbstractImm x y m args).
      iPureIntro. econstructor; eauto.
    - iIntros "#Hprimitives".
      iDestruct "Hprimitives" as "[_ [_ [_ #Hcall]]]".
      iApply ("Hcall" $! sΓ sΓ mt x y m args).
      iPureIntro. econstructor; eauto.
    - iIntros "#Hprimitives".
      iApply pico_core_resource_seq_compositionI.
      + iApply (IHHtyping1 eq_refl). iExact "Hprimitives".
      + iApply (IHHtyping2 eq_refl). iExact "Hprimitives".
    - iIntros "#Hprimitives".
      unfold pico_core_resource_stmt_wpI.
      iModIntro.
      iIntros (rGamma entry_receiver h sigma V K E Phi)
        "%Henv %Hreceiver %Hstate HR Hown #Houtcomes".
      pose proof
        (pico_core_typed_env_whole_int_guard
          CT sΓ rGamma h x Tx Henv H1 H2) as [n Hguard].
      destruct n as [|n].
      + assert (Hready : exists e' state',
          pico_core_step CT
            (CoreRun rGamma (SIfZero x s_zero s_nonzero) V K)
            (mkPicoCoreState h sigma) e' state').
        {
          eexists (CoreRun rGamma s_zero V K), (mkPicoCoreState h sigma).
          apply PCS_IfZero.
          exact Hguard.
        }
        iApply (pico_core_ownP_wp_from_direct_step_contI
          CT E Phi
          (CoreRun rGamma (SIfZero x s_zero s_nonzero) V K)
          (mkPicoCoreState h sigma) Hready with "Hown [HR]").
        iNext.
        iIntros (e' state') "%Hstep Hown".
        inversion Hstep; subst; try discriminate; try congruence.
        iPoseProof ((IHHtyping1 eq_refl) with "Hprimitives") as "#Hzero".
        iApply ("Hzero" $! rGamma entry_receiver h sigma V K E Phi
          with "[] [] [] HR Hown Houtcomes").
        * iPureIntro. exact Henv.
        * iPureIntro. exact Hreceiver.
        * iPureIntro. exact Hstate.
      + assert (Hready : exists e' state',
          pico_core_step CT
            (CoreRun rGamma (SIfZero x s_zero s_nonzero) V K)
            (mkPicoCoreState h sigma) e' state').
        {
          eexists (CoreRun rGamma s_nonzero V K), (mkPicoCoreState h sigma).
          apply PCS_IfNonzero with (n := n).
          exact Hguard.
        }
        iApply (pico_core_ownP_wp_from_direct_step_contI
          CT E Phi
          (CoreRun rGamma (SIfZero x s_zero s_nonzero) V K)
          (mkPicoCoreState h sigma) Hready with "Hown [HR]").
        iNext.
        iIntros (e' state') "%Hstep Hown".
        inversion Hstep; subst; try discriminate; try congruence.
        iPoseProof ((IHHtyping2 eq_refl) with "Hprimitives") as "#Hnonzero".
        iApply ("Hnonzero" $! rGamma entry_receiver h sigma V K E Phi
          with "[] [] [] HR Hown Houtcomes").
        * iPureIntro. exact Henv.
        * iPureIntro. exact Hreceiver.
        * iPureIntro. exact Hstate.
  Qed.

  (** Calls are the only recursive source construct.  One core call step enters
      the resolved body, so the Löb hypothesis is available exactly when the
      callee needs the semantic primitive environment.  The linear resource is
      passed through the callee outcome and returned to the caller unchanged
      except for transitions justified by the body itself. *)
  Theorem pico_core_resource_guarded_call_handlerI :
    forall R,
      (□ (pico_core_resource_call_handlerI R -∗
          pico_core_resource_semantic_primitivesI R)) -∗
      pico_core_resource_call_handlerI R.
  Proof.
    intros R.
    iIntros "#Hassemble".
    iLöb as "IH".
    unfold pico_core_resource_call_handlerI.
    iModIntro.
    iIntros (sGamma sGamma' mt x y m args) "%Htyping".
    unfold pico_core_resource_stmt_wpI.
    iModIntro.
    iIntros (caller entry_receiver h sigma V K E Phi)
      "%Hcaller_env %Hcaller_receiver %Hstate HR Hown Houtcomes".
    iPoseProof "Houtcomes" as "#Hfinal_cases".
    iDestruct "Hfinal_cases" as
      "[#Hfinal_ok [#Hfinal_npe #Hfinal_mutation]]".
    assert (Hready :
      exists e' state',
        pico_core_step CT
          (CoreRun caller (SCall x y m args) V K)
          (mkPicoCoreState h sigma) e' state').
    {
      apply pico_core_step_from_reducible.
      eapply pico_core_typed_call_reducible; eauto.
    }
    iApply
      (pico_core_ownP_wp_from_direct_step_contI
        CT E Phi
        (CoreRun caller (SCall x y m args) V K)
        (mkPicoCoreState h sigma) Hready
        with "Hown [HR]").
    iNext.
    iIntros (e' state') "%Hstep Hown".
    inversion Hstep as
      [ | | | | | | | | | | | | |
        rGamma0 x0 y0 m0 args0 vals0 loc0 C0 mdef0 body0 mstmt0 ret0
        h0 sigma0 V0 K0 Hreceiver Hbase Hfind Hbody Hstmt Hret Hargs |
        rGamma0 x0 y0 m0 args0 V0 K0 sigma0 Hnull | | | | ];
      subst; try discriminate; try congruence.
    all: try (
      iApply ("Hfinal_npe" with "[] [] HR Hown");
      [iPureIntro; exact Hstate |
       iPureIntro; apply pico_core_heap_types_extend_refl]).
    - pose proof
        (pico_core_typed_resolved_method_body
          CT sGamma sGamma' caller h mt x y m args
          loc0 C0 mdef0 vals0
          Htyping Hcaller_env Hreceiver Hbase Hfind Hargs)
        as Hbody_facts.
      destruct Hbody_facts as
        (body_sGamma' & body_ret_type & Hbody_typing &
         Hret_static & Hbody_return_sub).
      assert (Hcallee_env : pico_core_typed_env CT
        (mreceiver (msignature mdef0) :: mparams (msignature mdef0))
        (mkr_env (Iot loc0 :: vals0)) h) by
        (eapply pico_core_typed_resolved_method_frame; eauto).
      iPoseProof ("Hassemble" with "IH") as "#Hprimitives".
      iPoseProof
        (pico_core_resource_stmt_fundamentalI
          R _ _ _ _ Hbody_typing with "Hprimitives") as "#Hbody".
      iApply
        ("Hbody" $!
          (mkr_env (Iot loc0 :: vals0)) loc0 h sigma V
          (KCall caller x (mreturn (mbody mdef0)) :: K) E Phi
          with "[] [] [] HR Hown").
      + iPureIntro.
        exact Hcallee_env.
      + iPureIntro.
        reflexivity.
      + iPureIntro.
        exact Hstate.
      + unfold pico_core_resource_outcome_contI.
        iSplit.
        * iModIntro.
          iIntros (callee state_after V_after)
            "%Hcallee_env_after %Hstate_after %Hextend_body %Hcallee_receiver HR_after Hown_after".
          destruct state_after as [h_after sigma_after].
          destruct
            (pico_core_typed_env_lookup
              CT body_sGamma' callee h_after
              (mreturn (mbody mdef0)) body_ret_type
              Hcallee_env_after Hret_static)
            as (qcontext & retval & Hretval & Hretval_typed).
          assert (Hreturn_ready :
            exists e'' state'',
              pico_core_step CT
                  (CoreRun callee SSkip V_after
                  (KCall caller x (mreturn (mbody mdef0)) :: K))
                (mkPicoCoreState h_after sigma_after) e'' state'').
          {
            exists
              (CoreRun
                (set_vars caller (update x retval (vars caller)))
                SSkip V_after K).
            exists (mkPicoCoreState h_after sigma_after).
            eapply PCS_SkipCall.
            exact Hretval.
          }
          iApply
            (pico_core_ownP_wp_from_direct_step_contI
              CT E Phi
                (CoreRun callee SSkip V_after
                (KCall caller x (mreturn (mbody mdef0)) :: K))
              (mkPicoCoreState h_after sigma_after) Hreturn_ready
              with "Hown_after [HR_after]").
          iNext.
          iIntros (e'' state'') "%Hreturn_step Hown_return".
          inversion Hreturn_step; subst; try discriminate; try congruence.
          iApply
            ("Hfinal_ok" with "[] [] [] [] HR_after Hown_return").
          -- iPureIntro.
             assert (Hretval_eq : retval0 = retval) by congruence.
             subst retval0.
             change (pico_core_typed_env CT sGamma'
               (set_vars caller (update x retval (vars caller))) h_after).
             eapply pico_core_typed_resolved_method_return; eauto.
          -- iPureIntro.
             exact Hstate_after.
          -- iPureIntro.
             exact Hextend_body.
          -- iPureIntro.
             eapply pico_core_typed_call_return_preserves_receiver; eauto.
        * iSplit.
          -- iModIntro.
             iIntros (callee state_after V_after)
               "%Hstate_after %Hextend_body HR_after Hown_after".
             iApply
               ("Hfinal_npe" with "[] [] HR_after Hown_after").
             ++ iPureIntro. exact Hstate_after.
             ++ iPureIntro. exact Hextend_body.
          -- iModIntro.
             iIntros (callee state_after V_after)
               "%Hstate_after %Hextend_body HR_after Hown_after".
             iApply
               ("Hfinal_mutation" with "[] [] HR_after Hown_after").
             ++ iPureIntro. exact Hstate_after.
             ++ iPureIntro. exact Hextend_body.
  Qed.

  Definition pico_core_safe_value (v : pico_core_val) : Prop :=
    pico_core_result_allowed (pcv_result v).

  Definition pico_core_safe_postI (v : pico_core_val) : iProp Sigma :=
    ⌜pico_core_safe_value v⌝.

  (** Terminal continuation used by adequacy.  It accepts exactly the three
      modeled PICO outcomes and takes the final [SSkip] step on success. *)
  Theorem pico_core_resource_terminal_outcomesI :
    forall R entry_heap entry_receiver sGamma,
      ⊢ pico_core_resource_outcome_contI
        R entry_heap entry_receiver sGamma [] top pico_core_safe_postI.
  Proof.
    intros R entry_heap entry_receiver sGamma.
    unfold pico_core_resource_outcome_contI.
    iSplit.
    - iModIntro.
      iIntros (rGamma state V)
        "%Henv %Hstate %Hextend %Hreceiver HR Hown".
      assert (Hready :
        exists e' state',
          pico_core_step CT
            (CoreRun rGamma SSkip V []) state e' state').
      {
        exists (CoreDone OK rGamma V), state.
        apply PCS_SkipDone.
      }
      iApply
        (pico_core_ownP_wp_from_direct_step_contI
          CT top pico_core_safe_postI
          (CoreRun rGamma SSkip V []) state Hready
          with "Hown [HR]").
      iNext.
      iIntros (e' state') "%Hstep Hown".
      inversion Hstep; subst.
      iApply
        (@wp_value'
          _ (pico_core_language CT) Sigma _ NotStuck top
          pico_core_safe_postI (mkPicoCoreVal OK rGamma V)).
      unfold pico_core_safe_postI, pico_core_safe_value,
        pico_core_result_allowed.
      iPureIntro.
      simpl.
      auto.
    - iSplit.
      + iModIntro.
        iIntros (rGamma state V) "%Hstate %Hextend HR Hown".
        iApply
          (@wp_value'
            _ (pico_core_language CT) Sigma _ NotStuck top
            pico_core_safe_postI (mkPicoCoreVal NPE rGamma V)).
        unfold pico_core_safe_postI, pico_core_safe_value,
          pico_core_result_allowed.
        iPureIntro.
        simpl.
        auto.
      + iModIntro.
        iIntros (rGamma state V) "%Hstate %Hextend HR Hown".
        iApply
          (@wp_value'
            _ (pico_core_language CT) Sigma _ NotStuck top
            pico_core_safe_postI
            (mkPicoCoreVal MUTATIONEXP rGamma V)).
        unfold pico_core_safe_postI, pico_core_safe_value,
          pico_core_result_allowed.
        iPureIntro.
        simpl.
        auto.
  Qed.
End pico_resource_logical_relation.
