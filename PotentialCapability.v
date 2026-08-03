Require Import Syntax Notations Helpers Typing Subtyping Bigstep.
Require Import ViewpointAdaptation Properties Preservation ReadonlyHelper.
Require Import Reachability MutableCapability ComponentColoring.
Require Import ExecutionConfinement ProtectionHistory ForwardCapabilityHistory.
Require Import AuthorityCapability AuthorityHistory WatchedFrames
  LiveCapabilityStack.
Require Export PotentialCapabilityResume.
Require Import PotentialCapabilityRDMPop.
From Stdlib Require Import List Sets.Ensembles Relations.Relation_Operators
  Program.Equality.
Import ListNotations.

Theorem successful_stmt_preserves_potential_history :
  forall P CT rGamma h statement rGamma' h',
    eval_stmt CT rGamma h statement OK rGamma' h' ->
    forall sGamma mt sGamma' authority stack Z cutoff,
      potential_live_history_state CT P Z cutoff
        (mk_watched_frame authority sGamma rGamma) stack h ->
      stmt_typing CT sGamma mt statement sGamma' ->
      readonly_state_method_scope mt ->
      potential_live_history_state CT P Z cutoff
        (mk_watched_frame authority sGamma' rGamma') stack h'.
Proof.
{
  intros P CT rGamma h statement rGamma' h' Heval.
  have Heval_copy := Heval.
  revert P.
  dependent induction Heval;
    intros P sGamma mt sGamma' authority stack Z cutoff Hstate Htyping Hsafe.
  - inversion Htyping; subst. exact Hstate.
  - eapply potential_history_after_local; eauto.
  - inversion Htyping; subst.
    assert (Hupdate :
      set_vars rΓ (update x v2 (vars rΓ)) = update_r_env_value rΓ x v2).
    { destruct rΓ. reflexivity. }
    rewrite Hupdate.
    eapply potential_history_after_assignment with
      (CT := CT) (P := P) (Z := Z) (cutoff := cutoff)
      (authority := authority) (mt := mt)
      (rGamma := rΓ) (h := h) (stack := stack)
      (x := x) (e := e) (old := v1) (value := v2).
    + exact Hstate.
    + exact Htyping.
    + exact Hsafe.
    + exact Hval.
    + exact Heval.
  - eapply potential_history_after_field_write.
    + exact Hstate.
    + exact Htyping.
    + exact Hsafe.
    + exact Heval_copy.
  - eapply potential_history_after_new; eauto.
  - destruct Hfind as [Hfind_method Hbody_definition].
    subst mbody. subst mstmt. subst mret. subst rΓ'. subst rΓ'''.
    have Hcaller_wf : wf_r_config CT sGamma rΓ h :=
      proj1 (proj1 (proj2 (proj1 Hstate))).
    destruct (safe_typed_call_static_result CT sGamma mt rΓ h x m y zs
      sGamma' ly cy mdef Hcaller_wf Htyping Hsafe Hval_y Hbase Hfind_method)
      as [destination_type [receiver_type [static_mdef Hstatic_result]]].
    destruct Hstatic_result as
      [HsGamma [Hdestination_not_receiver [Hdestination_type
        [Hreceiver_type [Hfind_static
          [Hsignature_refinement
            [Hresult_sub Hstatic_receiver_sub]]]]]]].
    subst sGamma'.
    have Hcallee_safe := safe_typed_call_target_method_safe CT sGamma mt rΓ
      h x m y zs sGamma ly cy mdef Hcaller_wf Htyping Hsafe Hval_y Hbase
      Hfind_method.
    destruct (typed_call_target CT sGamma mt rΓ h x m y zs sGamma vals ly
      cy mdef Hcaller_wf Htyping Hval_y Hbase Hfind_method Hargs) as
      [declaring_class [declaring_def [body_end
        [Hruntime_sub [Hdeclaring_class [Hmethod_member
          [Hmethod_wf [Hbody_typing Hcallee_initial_wf]]]]]]]].
    unfold wf_method in Hmethod_wf. simpl in Hmethod_wf.
    destruct Hmethod_wf as
      [_ [method_end [body_return_type
        [Hmethod_body_typing [Hreturn_dom
          [Hreturn_type [Hbody_sub Hoverriding]]]]]]].
    destruct (potential_history_enter_call CT P Z cutoff authority sGamma mt
      rΓ h stack x m y zs sGamma vals ly cy mdef receiver_type Hstate
      Htyping Hsafe Hreceiver_type Hval_y Hbase Hfind_method Hargs) as
      [origins [entry_destination_type [Hentry_destination Hentry]]].
    assert (entry_destination_type = destination_type) by congruence.
    subst entry_destination_type.
    have Hbody_post := IHHeval eq_refl Heval P
      (mreceiver (msignature mdef) :: mparams (msignature mdef))
      (mscope (msignature mdef)) method_end
      (call_authority authority (sqtype receiver_type))
      (mk_watched_call_boundary
        (mk_watched_frame authority sGamma rΓ)
        (mreceiver (msignature mdef) :: mparams (msignature mdef))
        (mkr_env (Iot ly :: vals)) (sqtype receiver_type) (mreturn (mbody mdef)) (sqtype destination_type) (sqtype (mret (msignature mdef))) (dom h) origins :: stack)
      Z cutoff Hentry Hmethod_body_typing Hcallee_safe.
    set (body_initial_reachable :=
      reachable_locations_from_initial_env h (mkr_env (Iot ly :: vals))).
    have Hsignature_safe :
        signature_has_no_mutable_roots (msignature mdef).
    { exact ((proj2 (proj2 Hoverriding)) Hcallee_safe). }
    have Hbody_initial_env :
        env_respects_protected_set body_initial_reachable
          (mreceiver (msignature mdef) :: mparams (msignature mdef))
          (mkr_env (Iot ly :: vals)).
    { eapply confinement_from_all_readonly_env; [exact Hcallee_initial_wf|].
      intros variable variable_type Hvariable_type.
      destruct Hsignature_safe as [Hreceiver_safe Hparams_safe].
      destruct variable as [|parameter].
      - simpl in Hvariable_type. injection Hvariable_type as <-.
        exact Hreceiver_safe.
      - simpl in Hvariable_type.
        eapply Forall_nth_error in Hparams_safe; eauto. }
    have Hbody_initial_local := initial_potential_live_history CT
      (mreceiver (msignature mdef) :: mparams (msignature mdef))
      (mkr_env (Iot ly :: vals)) h Hcallee_initial_wf Hbody_initial_env.
    have Hbody_local_post := IHHeval eq_refl Heval body_initial_reachable
      (mreceiver (msignature mdef) :: mparams (msignature mdef))
      (mscope (msignature mdef)) method_end Imm_r []
      body_initial_reachable (dom h) Hbody_initial_local
      Hmethod_body_typing Hcallee_safe.
    have Hlive_start := proj1 Hstate.
    have Hauthority_start := proj1 Hlive_start.
    have Hcomponent_start := proj1 Hauthority_start.
    have Hcaller_zone : zone_env_safe Z sGamma rΓ :=
      proj1 (proj2 Hcomponent_start).
    have Hcaller_env : env_is_confined P cutoff rΓ :=
      proj1 (proj1 (proj2 (proj2 Hcomponent_start))).
    have Hcaller_final_wf := preservation_pico CT sGamma mt rΓ h
      (SCall x m y zs) (set_vars rΓ (update x retval (vars rΓ))) h' sGamma
      Hcaller_wf Htyping Heval_copy.
    assert (Hupdate : set_vars rΓ (update x retval (vars rΓ)) =
        update_r_env_value rΓ x retval).
    { destruct rΓ. reflexivity. }
    rewrite Hupdate in Hcaller_final_wf |- *.
    destruct retval as [|return_location].
    + eapply potential_history_leave_call_null with
        (caller_h := h) (destination_type := destination_type)
        (receiver_type := receiver_type)
        (entry_senv := mreceiver (msignature mdef) ::
          mparams (msignature mdef))
        (entry_renv := mkr_env (Iot ly :: vals))
        (origins := origins) (callee_senv := method_end)
        (callee_renv := rΓ'') (callee_h := h'); eauto.
    + refine (potential_history_leave_call CT P Z cutoff authority sGamma rΓ
        h stack x destination_type y ly receiver_type
        (mreceiver (msignature mdef) :: mparams (msignature mdef))
        (mkr_env (Iot ly :: vals)) origins method_end rΓ'' h'
        (mreturn (mbody mdef)) body_return_type (msignature mdef)
        (msignature static_mdef) return_location Hcaller_zone Hcaller_env
        Hcaller_wf Hdestination_not_receiver Hdestination_type Hreceiver_type
        Hval_y Hreturn_type Hretval Hbody_sub Hsignature_refinement Hresult_sub
        Hbody_post Hcaller_final_wf _).
      intros Hdestination_rdm.
      have Hbody_live := proj1 Hbody_post.
      have Hbody_frames : live_frames_wf CT h'
          (mk_watched_frame
            (call_authority authority (sqtype receiver_type))
            method_end rΓ'')
          (mk_watched_call_boundary
            (mk_watched_frame authority sGamma rΓ)
            (mreceiver (msignature mdef) :: mparams (msignature mdef))
            (mkr_env (Iot ly :: vals)) (sqtype receiver_type) (mreturn (mbody mdef)) (sqtype destination_type) (sqtype (mret (msignature mdef))) (dom h) origins ::
            stack) := proj1 (proj2 Hbody_live).
      have Hcallee_final_wf :
          wf_r_config CT method_end rΓ'' h' := proj1 Hbody_frames.
      have Hbody_sounds : live_frames_authority_sound h'
          (mk_watched_frame
            (call_authority authority (sqtype receiver_type))
            method_end rΓ'')
          (mk_watched_call_boundary
            (mk_watched_frame authority sGamma rΓ)
            (mreceiver (msignature mdef) :: mparams (msignature mdef))
            (mkr_env (Iot ly :: vals)) (sqtype receiver_type) (mreturn (mbody mdef)) (sqtype destination_type) (sqtype (mret (msignature mdef))) (dom h) origins ::
            stack) := proj1 (proj2 (proj2 Hbody_live)).
      have Hcaller_current_wf : wf_r_config CT sGamma rΓ h'.
      { exact (Forall_inv (proj2 Hbody_frames)). }
      have Hcaller_sound :
          authority_context_sound h' rΓ authority.
      { exact (Forall_inv (proj2 Hbody_sounds)). }
      have Hreceiver_nonbottom : sqtype receiver_type <> Bot.
      { eapply (wf_config_nonnull_variable_not_bot CT sGamma rΓ h y
          receiver_type ly); eauto. }
      have Hreturn_nonbottom : sqtype body_return_type <> Bot.
      { eapply (wf_config_nonnull_variable_not_bot CT method_end rΓ'' h'
          (mreturn (mbody mdef)) body_return_type return_location); eauto. }
      destruct (refined_call_rdm_result_classifies_body_return CT
        receiver_type body_return_type (msignature mdef)
        (msignature static_mdef) destination_type Hbody_sub
        Hsignature_refinement Hresult_sub Hreceiver_nonbottom
        Hreturn_nonbottom Hdestination_rdm) as
        [Hreceiver_rdm Hbody_cases].
      have Hcaller_receiver_root :
          typed_root RDM sGamma rΓ ly.
      { exists y, receiver_type. repeat split; assumption. }
      have Hcaller_result_root :
          typed_root RDM sGamma
            (update_r_env_value rΓ x (Iot return_location))
            return_location.
      { exists x, destination_type. repeat split; try assumption.
        have Hxdomain := Hdestination_type.
        apply static_getType_dom in Hxdomain.
        unfold wf_r_config in Hcaller_wf.
        destruct Hcaller_wf as [_ [_ [_ [_ [Hlength _]]]]].
        eapply runtime_getVal_update_same. lia. }
      destruct (extract_receiver_from_wf_config CT sGamma rΓ h Hcaller_wf)
        as [caller_this [caller_runtime
          [Hcaller_this [Hcaller_this_dom Hcaller_this_runtime]]]].
      have Hcaller_this_value :=
        get_this_var_mapping_runtime_getVal rΓ caller_this Hcaller_this.
      have Hcaller_post_this_value := runtime_getVal_update_diff rΓ x 0
        (Iot return_location) Hdestination_not_receiver.
      rewrite Hcaller_this_value in Hcaller_post_this_value.
      have Hreceiver_runtime := typed_rdm_root_matches_receiver_runtime CT
        sGamma rΓ h' caller_this caller_runtime ly Hcaller_current_wf
        Hcaller_this_value
        (ltac:(eapply eval_stmt_preserves_r_muttype; eauto))
        Hcaller_receiver_root.
      have Hreturn_runtime := typed_rdm_root_matches_receiver_runtime CT
        sGamma (update_r_env_value rΓ x (Iot return_location)) h'
        caller_this caller_runtime return_location Hcaller_final_wf
        Hcaller_post_this_value
        (ltac:(eapply eval_stmt_preserves_r_muttype; eauto))
        Hcaller_result_root.
      have Hincluded : Included Loc
          (live_capability_set CT h'
            (mk_watched_frame authority sGamma
              (update_r_env_value rΓ x (Iot return_location))) stack)
          (live_capability_set CT h'
            (mk_watched_frame
              (call_authority authority (sqtype receiver_type))
              method_end rΓ'')
            (mk_watched_call_boundary
              (mk_watched_frame authority sGamma rΓ)
              (mreceiver (msignature mdef) :: mparams (msignature mdef))
              (mkr_env (Iot ly :: vals)) (sqtype receiver_type)
              (mreturn (mbody mdef)) (sqtype destination_type)
              (sqtype (mret (msignature mdef))) (dom h) origins ::
              stack)).
      { intros location Hlocation.
        eapply call_return_live_reachability_reflects_before_pop with
          (caller_h := h) (destination_type := destination_type)
          (receiver := y) (receiver_location := ly)
          (receiver_type := receiver_type)
          (entry_senv := mreceiver (msignature mdef) ::
            mparams (msignature mdef))
          (entry_renv := mkr_env (Iot ly :: vals)) (origins := origins)
          (callee_senv := method_end) (callee_renv := rΓ'')
          (return_var := mreturn (mbody mdef))
          (body_return_type := body_return_type)
          (runtime_sig := msignature mdef)
          (static_sig := msignature static_mdef)
          (return_location := return_location); eauto. }
      eapply classified_rdm_call_pop_merge_safe with
        (P := P) (Z := Z) (cutoff := cutoff) (stack := stack)
        (caller_authority := authority) (caller_senv := sGamma)
        (caller_renv := rΓ) (destination := x)
        (destination_type := destination_type) (receiver := y)
        (receiver_type := receiver_type) (receiver_location := ly)
        (callee_senv := method_end) (callee_renv := rΓ'')
        (return_var := mreturn (mbody mdef))
        (body_return_type := body_return_type)
        (return_location := return_location)
        (boundary :=
          mk_watched_call_boundary
            (mk_watched_frame authority sGamma rΓ)
            (mreceiver (msignature mdef) :: mparams (msignature mdef))
            (mkr_env (Iot ly :: vals)) (sqtype receiver_type)
            (mreturn (mbody mdef)) (sqtype destination_type)
            (sqtype (mret (msignature mdef))) (dom h) origins);
        try reflexivity; try assumption.
      * rewrite Hreturn_runtime. rewrite Hreceiver_runtime. reflexivity.
      * destruct Hbody_cases as [Hbody_rdm | [Hbody_mut | Hbody_imm]].
        -- left. split; [exact Hbody_rdm|].
          simpl.
          eapply refined_call_rdm_rdm_body_signature_return with
            (receiver_type := receiver_type)
            (body_return_type := body_return_type)
            (static_sig := msignature static_mdef)
            (destination_type := destination_type); eauto.
        -- right. left. exact Hbody_mut.
        -- right. right. split; [exact Hbody_imm|].
          eapply typed_imm_root_runtime_immutable_live;
            [exact Hcallee_final_wf|].
          exists (mreturn (mbody mdef)), body_return_type.
          repeat split; [exact Hreturn_type|exact Hretval|exact Hbody_imm].
      * (* Residual: Imm_r caller authority with a covariant Mut body return. *)
        intros Hauthority_imm Hbody_mut.
        admit.
  - inversion Htyping; subst.
    eapply (IHHeval2 eq_refl Heval2 P).
    + eapply (IHHeval1 eq_refl Heval1 P); eauto.
    + exact Htype2.
    + exact Hsafe.
}
Admitted.
