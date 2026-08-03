Require Import Syntax Notations Helpers Typing Subtyping Bigstep.
Require Import ViewpointAdaptation Properties Preservation ReadonlyHelper.
Require Import Reachability MutableCapability ComponentColoring.
Require Import ExecutionConfinement ProtectionHistory ForwardCapabilityHistory.
Require Import AuthorityCapability AuthorityHistory WatchedFrames
  LiveCapabilityStack.
Require Export PotentialCapabilityResume.
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
      unfold call_pop_merge_safe.
      intros capability protected Hcapability Hprotected Hbridge.
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
      have Hcapability_pre : In Loc
          (live_capability_set CT h'
            (mk_watched_frame
              (call_authority authority (sqtype receiver_type))
              method_end rΓ'')
            (mk_watched_call_boundary
              (mk_watched_frame authority sGamma rΓ)
              (mreceiver (msignature mdef) :: mparams (msignature mdef))
              (mkr_env (Iot ly :: vals)) (sqtype receiver_type) (mreturn (mbody mdef)) (sqtype destination_type) (sqtype (mret (msignature mdef))) (dom h) origins ::
              stack)) capability.
      { eapply call_return_live_reachability_reflects_before_pop with
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
      have Hcapability_runtime :
          r_muttype h' capability = Some Mut_r.
      { eapply live_capability_members_runtime_mutable; eauto. }
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
      have Hpotential_body := proj1 (proj2 Hbody_post).
      destruct Hbridge as
        [[Hcap_receiver Hreturn_protected] |
         [Hcap_return Hreceiver_protected]];
        destruct Hbody_cases as [Hbody_rdm | [Hbody_mut | Hbody_imm]].
      * idtac.
        have Hruntime_return_rdm :=
          refined_call_rdm_rdm_body_signature_return CT receiver_type
            body_return_type (msignature mdef) (msignature static_mdef)
            destination_type Hbody_sub Hsignature_refinement Hresult_sub
            Hreceiver_nonbottom Hdestination_rdm Hbody_rdm.
        have Hreturn_receiver :
            potential_connected CT h'
              (mk_watched_frame
                (call_authority authority (sqtype receiver_type))
                method_end rΓ'')
              (mk_watched_call_boundary
                (mk_watched_frame authority sGamma rΓ)
                (mreceiver (msignature mdef) :: mparams (msignature mdef))
                (mkr_env (Iot ly :: vals)) (sqtype receiver_type) (mreturn (mbody mdef)) (sqtype destination_type) (sqtype (mret (msignature mdef))) (dom h) origins ::
                stack)
              return_location ly.
        { apply rt_step. right. right.
          exists
            (mk_watched_frame
              (call_authority authority (sqtype receiver_type))
              method_end rΓ''),
            (mk_watched_call_boundary
              (mk_watched_frame authority sGamma rΓ)
              (mreceiver (msignature mdef) :: mparams (msignature mdef))
              (mkr_env (Iot ly :: vals)) (sqtype receiver_type) (mreturn (mbody mdef)) (sqtype destination_type) (sqtype (mret (msignature mdef))) (dom h) origins).
          split; [constructor|]. split; [simpl; exact Hreceiver_rdm|].
          split; [simpl; exact Hruntime_return_rdm|]. split;
            [rewrite Hreturn_runtime; rewrite Hreceiver_runtime; reflexivity
            |left; split;
              [exists (mreturn (mbody mdef)), body_return_type;
                repeat split; assumption
              |exact Hcaller_receiver_root]]. }
        have Hreceiver_return :
            potential_connected CT h'
              (mk_watched_frame
                (call_authority authority (sqtype receiver_type))
                method_end rΓ'')
              (mk_watched_call_boundary
                (mk_watched_frame authority sGamma rΓ)
                (mreceiver (msignature mdef) :: mparams (msignature mdef))
                (mkr_env (Iot ly :: vals)) (sqtype receiver_type) (mreturn (mbody mdef)) (sqtype destination_type) (sqtype (mret (msignature mdef))) (dom h) origins ::
                stack)
              ly return_location.
        { apply rt_step. right. right.
          exists
            (mk_watched_frame
              (call_authority authority (sqtype receiver_type))
              method_end rΓ''),
            (mk_watched_call_boundary
              (mk_watched_frame authority sGamma rΓ)
              (mreceiver (msignature mdef) :: mparams (msignature mdef))
              (mkr_env (Iot ly :: vals)) (sqtype receiver_type) (mreturn (mbody mdef)) (sqtype destination_type) (sqtype (mret (msignature mdef))) (dom h) origins).
          split; [constructor|]. split; [simpl; exact Hreceiver_rdm|].
          split; [simpl; exact Hruntime_return_rdm|]. split;
            [rewrite Hreturn_runtime; rewrite Hreceiver_runtime; reflexivity
            |right; split;
              [exact Hcaller_receiver_root
              |exists (mreturn (mbody mdef)), body_return_type;
                repeat split; assumption]]. }
        apply (Hpotential_body capability protected Hcapability_pre
          Hprotected).
        eapply potential_connected_trans; [exact Hcap_receiver|].
        eapply potential_connected_trans; eauto.
      * idtac.
        have Hreturn_capability : In Loc
            (live_capability_set CT h'
              (mk_watched_frame
                (call_authority authority (sqtype receiver_type))
                method_end rΓ'')
              (mk_watched_call_boundary
                (mk_watched_frame authority sGamma rΓ)
                (mreceiver (msignature mdef) :: mparams (msignature mdef))
                (mkr_env (Iot ly :: vals)) (sqtype receiver_type) (mreturn (mbody mdef)) (sqtype destination_type) (sqtype (mret (msignature mdef))) (dom h) origins ::
                stack)) return_location.
        { eapply typed_mut_root_is_active_live_capability.
          exists (mreturn (mbody mdef)), body_return_type.
          repeat split; assumption. }
        apply (Hpotential_body return_location protected Hreturn_capability
          Hprotected Hreturn_protected).
      * idtac.
        have Hreturn_immutable :
            r_muttype h' return_location = Some Imm_r.
        { eapply typed_imm_root_runtime_immutable_live;
            [exact Hcallee_final_wf|].
          exists (mreturn (mbody mdef)), body_return_type.
          repeat split; [exact Hreturn_type|exact Hretval|exact Hbody_imm]. }
        have Hreceiver_mutable :=
          potential_connected_preserves_runtime_mutability CT h'
            (mk_watched_frame
              (call_authority authority (sqtype receiver_type))
              method_end rΓ'')
            (mk_watched_call_boundary
              (mk_watched_frame authority sGamma rΓ)
              (mreceiver (msignature mdef) :: mparams (msignature mdef))
              (mkr_env (Iot ly :: vals)) (sqtype receiver_type) (mreturn (mbody mdef)) (sqtype destination_type) (sqtype (mret (msignature mdef))) (dom h) origins ::
              stack)
            capability ly Mut_r Hbody_frames
            (proj1 (proj2 Hcallee_final_wf)) Hcap_receiver
            Hcapability_runtime.
        rewrite Hreceiver_runtime in Hreceiver_mutable.
        rewrite Hreturn_runtime in Hreturn_immutable.
        congruence.
      * idtac.
        have Hruntime_return_rdm :=
          refined_call_rdm_rdm_body_signature_return CT receiver_type
            body_return_type (msignature mdef) (msignature static_mdef)
            destination_type Hbody_sub Hsignature_refinement Hresult_sub
            Hreceiver_nonbottom Hdestination_rdm Hbody_rdm.
        have Hreturn_receiver :
            potential_connected CT h'
              (mk_watched_frame
                (call_authority authority (sqtype receiver_type))
                method_end rΓ'')
              (mk_watched_call_boundary
                (mk_watched_frame authority sGamma rΓ)
                (mreceiver (msignature mdef) :: mparams (msignature mdef))
                (mkr_env (Iot ly :: vals)) (sqtype receiver_type) (mreturn (mbody mdef)) (sqtype destination_type) (sqtype (mret (msignature mdef))) (dom h) origins ::
                stack)
              return_location ly.
        { apply rt_step. right. right.
          exists
            (mk_watched_frame
              (call_authority authority (sqtype receiver_type))
              method_end rΓ''),
            (mk_watched_call_boundary
              (mk_watched_frame authority sGamma rΓ)
              (mreceiver (msignature mdef) :: mparams (msignature mdef))
              (mkr_env (Iot ly :: vals)) (sqtype receiver_type) (mreturn (mbody mdef)) (sqtype destination_type) (sqtype (mret (msignature mdef))) (dom h) origins).
          split; [constructor|]. split; [simpl; exact Hreceiver_rdm|].
          split; [simpl; exact Hruntime_return_rdm|]. split;
            [rewrite Hreturn_runtime; rewrite Hreceiver_runtime; reflexivity
            |left; split;
              [exists (mreturn (mbody mdef)), body_return_type;
                repeat split; assumption
              |exact Hcaller_receiver_root]]. }
        apply (Hpotential_body capability protected Hcapability_pre
          Hprotected).
        eapply potential_connected_trans; [exact Hcap_return|].
        eapply potential_connected_trans; eauto.
      * idtac.
        destruct (refined_call_rdm_mut_body_signature_shape CT receiver_type
          body_return_type (msignature mdef) (msignature static_mdef)
          destination_type Hbody_sub Hsignature_refinement Hresult_sub
          Hreceiver_nonbottom Hdestination_rdm Hbody_mut) as
          [Hstatic_return_rdm Hruntime_return_mut].
        have Hstatic_receiver_shape :
            sqtype (mreceiver (msignature static_mdef)) = RDM \/
            sqtype (mreceiver (msignature static_mdef)) = RO.
        { eapply readonly_rdm_call_receiver_signature.
          - exact Hreceiver_rdm.
          - exact Hstatic_receiver_sub. }
        have Hruntime_receiver_ro :
            sqtype (mreceiver (msignature mdef)) = RO.
        { eapply method_signature_refinement_mut_from_rdm_has_ro_receiver.
          - exact Hsignature_refinement.
          - exact Hsignature_safe.
          - exact Hstatic_return_rdm.
          - exact Hstatic_receiver_shape.
          - exact Hruntime_return_mut. }
        have Hcallee_entry_no_rdm :
            forall root,
              ~ typed_root RDM
                  (mreceiver (msignature mdef) ::
                    mparams (msignature mdef))
                  (mkr_env (Iot ly :: vals)) root.
        { intros root.
          eapply refined_mut_return_call_entry_has_no_rdm_roots
            with (receiver_type := receiver_type)
              (runtime_mdef := mdef) (static_mdef := static_mdef);
            eauto. }
        destruct authority.
        -- have Hreceiver_capability : In Loc
             (live_capability_set CT h'
               (mk_watched_frame
                 (call_authority Mut_r (sqtype receiver_type))
                 method_end rΓ'')
               (mk_watched_call_boundary
                 (mk_watched_frame Mut_r sGamma rΓ)
                 (mreceiver (msignature mdef) :: mparams (msignature mdef))
                 (mkr_env (Iot ly :: vals)) (sqtype receiver_type) (mreturn (mbody mdef)) (sqtype destination_type) (sqtype (mret (msignature mdef))) (dom h) origins ::
                 stack)) ly.
           { exists ly. split;
             [right; exists (mk_watched_call_boundary
                (mk_watched_frame Mut_r sGamma rΓ)
                (mreceiver (msignature mdef) :: mparams (msignature mdef))
                (mkr_env (Iot ly :: vals)) (sqtype receiver_type) (mreturn (mbody mdef)) (sqtype destination_type) (sqtype (mret (msignature mdef))) (dom h) origins);
              split; [left; reflexivity|];
              exists y, receiver_type; repeat split; try assumption;
              unfold capability_in_context; right; split;
                [exact Hreceiver_rdm|reflexivity]
             |constructor]. }
           apply (Hpotential_body ly protected Hreceiver_capability
             Hprotected Hreceiver_protected).
	        -- (* The immutable-authority case is the provenance obligation:
	              a surviving old capability cannot reach the fresh mutable
	              result without reflecting through the receiver component. *)
	           have Hcapability_caller : In Loc
	               (live_capability_set CT h'
	                 (mk_watched_frame Imm_r sGamma rΓ) stack) capability.
	           { eapply immutable_rdm_update_live_capability_included;
	               eauto. }
	           have Hlocal_live := proj1 Hbody_local_post.
           have Hlocal_component := proj1 (proj1 Hlocal_live).
           have Hlocal_env : env_is_confined body_initial_reachable
               (dom h) rΓ'' :=
             proj1 (proj1 (proj2 (proj2 Hlocal_component))).
           have Hlocal_potential := proj1 (proj2 Hbody_local_post).
           have Hreturn_local_capability : In Loc
               (live_capability_set CT h'
                 (mk_watched_frame Imm_r method_end rΓ'') [])
               return_location.
           { eapply typed_mut_root_is_active_live_capability.
             exists (mreturn (mbody mdef)), body_return_type.
             repeat split; assumption. }
           have Hreturn_fresh : dom h <= return_location.
           { destruct (Hlocal_env (mreturn (mbody mdef)) return_location
               Hretval) as [Hreturn_initial | Hreturn_fresh];
               [|exact Hreturn_fresh].
             exfalso.
             apply (Hlocal_potential return_location return_location
               Hreturn_local_capability Hreturn_initial).
             apply rt_refl. }
           have Hstart_frames : live_frames_wf CT h
               (mk_watched_frame Imm_r sGamma rΓ) stack :=
             proj1 (proj2 (proj1 Hstate)).
           assert (Hold_live_rdm_root :
             forall frame root,
               live_frame_member (mk_watched_frame Imm_r sGamma rΓ)
                 stack frame ->
               typed_root RDM frame.(frame_senv) frame.(frame_renv) root ->
               root < dom h).
           { intros frame root Hlive
               [variable [T [Htype [Hvalue Hrdm]]]].
             have Hframe_wf := live_frame_member_wf CT h
               (mk_watched_frame Imm_r sGamma rΓ) stack frame
               Hstart_frames Hlive.
             eapply wf_config_value_dom; eauto. }
           assert (Hcapability_seed :
             capability < dom h \/
             exists initial,
               In Loc body_initial_reachable initial /\
               potential_connected CT h'
                 (mk_watched_frame Imm_r method_end rΓ'') []
                 initial capability).
           { destruct Hcapability as
               [root [[Hactive_root | [boundary [Hin Hboundary_root]]]
                 Hretained]].
             - destruct Hactive_root as
                 [variable [T [Htype [Hvalue Hcap]]]].
               unfold capability_in_context in Hcap.
               destruct Hcap as [Hmut | [Hrdm Hbad]]; [|discriminate].
               assert (Hroot_old : root < dom h).
               { destruct (Nat.eq_dec variable x) as [Heq | Hneq].
                 - subst variable. rewrite Hdestination_type in Htype.
                   injection Htype as <-. rewrite Hdestination_rdm in Hmut.
                   discriminate.
                 - have Hold_value := runtime_getVal_update_diff rΓ x variable
                     (Iot return_location) (ltac:(congruence)).
                   rewrite Hvalue in Hold_value.
                   eapply wf_config_value_dom.
                   -- exact Hcaller_wf.
                   -- symmetry. exact Hold_value. }
               destruct (le_lt_dec (dom h) capability) as
                 [Hcap_fresh | Hcap_old]; [right|left; exact Hcap_old].
               destruct
                 (eval_old_retained_reaches_fresh_has_initial_reachable_suffix
                   CT
                   (mreceiver (msignature mdef) ::
                     mparams (msignature mdef))
                   (mkr_env (Iot ly :: vals)) h
                   (mbody_stmt (mbody mdef)) rΓ'' h' root capability
                   Hcallee_initial_wf Heval Hroot_old Hcap_fresh Hretained)
                 as [initial [Hinitial Hsuffix]].
               exists initial. split; [exact Hinitial|].
               eapply retained_reachable_is_potential_connected; eauto.
             - have Hstack_wf := proj2 Hstart_frames.
               apply Forall_forall with (x := boundary) in Hstack_wf;
                 [|exact Hin].
               have Hroot_old := frame_capability_root_dom CT h
                 boundary.(boundary_caller) root Hstack_wf Hboundary_root.
               destruct (le_lt_dec (dom h) capability) as
                 [Hcap_fresh | Hcap_old]; [right|left; exact Hcap_old].
               destruct
                 (eval_old_retained_reaches_fresh_has_initial_reachable_suffix
                   CT
                   (mreceiver (msignature mdef) ::
                     mparams (msignature mdef))
                   (mkr_env (Iot ly :: vals)) h
                   (mbody_stmt (mbody mdef)) rΓ'' h' root capability
                   Hcallee_initial_wf Heval Hroot_old Hcap_fresh Hretained)
                 as [initial [Hinitial Hsuffix]].
               exists initial. split; [exact Hinitial|].
               eapply retained_reachable_is_potential_connected; eauto. }
           assert (Hstep :
             forall left right,
               potential_connected CT h'
                 (mk_watched_frame
                   (call_authority Imm_r (sqtype receiver_type))
                   method_end rΓ'')
                 (mk_watched_call_boundary
                   (mk_watched_frame Imm_r sGamma rΓ)
                   (mreceiver (msignature mdef) :: mparams (msignature mdef))
                   (mkr_env (Iot ly :: vals)) (sqtype receiver_type) (mreturn (mbody mdef)) (sqtype destination_type) (sqtype (mret (msignature mdef))) (dom h) origins ::
                   stack)
                 capability left ->
               (left < dom h \/
                exists initial,
                  In Loc body_initial_reachable initial /\
                  potential_connected CT h'
                    (mk_watched_frame Imm_r method_end rΓ'') []
                    initial left) ->
               potential_adjacent CT h'
                 (mk_watched_frame
                   (call_authority Imm_r (sqtype receiver_type))
                   method_end rΓ'')
                 (mk_watched_call_boundary
                   (mk_watched_frame Imm_r sGamma rΓ)
                   (mreceiver (msignature mdef) :: mparams (msignature mdef))
                   (mkr_env (Iot ly :: vals)) (sqtype receiver_type) (mreturn (mbody mdef)) (sqtype destination_type) (sqtype (mret (msignature mdef))) (dom h) origins ::
                   stack)
                 left right ->
               (right < dom h \/
                exists initial,
                  In Loc body_initial_reachable initial /\
                  potential_connected CT h'
                    (mk_watched_frame Imm_r method_end rΓ'') []
                    initial right) \/
               potential_connected CT h'
                 (mk_watched_frame
                   (call_authority Imm_r (sqtype receiver_type))
                   method_end rΓ'')
                 (mk_watched_call_boundary
                   (mk_watched_frame Imm_r sGamma rΓ)
                   (mreceiver (msignature mdef) :: mparams (msignature mdef))
                   (mkr_env (Iot ly :: vals)) (sqtype receiver_type) (mreturn (mbody mdef)) (sqtype destination_type) (sqtype (mret (msignature mdef))) (dom h) origins ::
                   stack)
                 capability ly).
           { intros left right Hcap_left Hleft_state
               [Hheap_edge | [Hframe_edge | Hreturn_edge]].
             - destruct (le_lt_dec (dom h) right) as
                 [Hright_fresh | Hright_old];
                 [|left; left; exact Hright_old].
               left; right.
               destruct Hheap_edge as [Hforward | Hbackward].
               + destruct Hleft_state as
                   [Hleft_old | [initial [Hinitial Hinitial_left]]].
                 * have Hleft_initial :=
                     eval_old_retained_edge_to_fresh_source_is_reachable
                       CT
                       (mreceiver (msignature mdef) ::
                         mparams (msignature mdef))
                       (mkr_env (Iot ly :: vals)) h
                       (mbody_stmt (mbody mdef)) rΓ'' h' left right
                       Hcallee_initial_wf Heval Hleft_old Hright_fresh
                       Hforward.
                   exists left. split; [exact Hleft_initial|].
                   apply rt_step. left. left. exact Hforward.
                 * exists initial. split; [exact Hinitial|].
                   eapply potential_connected_trans;
                     [exact Hinitial_left|].
                   apply rt_step. left. left. exact Hforward.
               + destruct Hleft_state as
                   [Hleft_old | [initial [Hinitial Hinitial_left]]].
                 * have Hcross :=
                     eval_fresh_mutable_adjacent_is_fresh_or_protected CT
                       (mreceiver (msignature mdef) ::
                         mparams (msignature mdef))
                       (mkr_env (Iot ly :: vals)) h
                       (mbody_stmt (mbody mdef)) rΓ'' h' right left
                       Hcallee_initial_wf Heval Hright_fresh
                       (ltac:(left; exact Hbackward)).
                   destruct Hcross as [Hleft_fresh | Hleft_initial];
                     [lia|].
                   exists left. split; [exact Hleft_initial|].
                   apply rt_step. left. right. exact Hbackward.
                 * exists initial. split; [exact Hinitial|].
                   eapply potential_connected_trans;
                     [exact Hinitial_left|].
                   apply rt_step. left. right. exact Hbackward.
             - destruct Hframe_edge as
                 [frame [Hlive [Hleft Hright]]].
               inversion Hlive; subst.
               + left; right.
                 destruct Hleft_state as
                   [Hleft_old | [initial [Hinitial Hinitial_left]]].
                 * destruct Hleft as
                     [variable [T [Htype [Hvalue Hrdm]]]].
                   destruct (Hlocal_env variable left Hvalue) as
                     [Hleft_initial | Hleft_fresh]; [|lia].
                   exists left. split; [exact Hleft_initial|].
                   apply rt_step. right. left.
                   exists (mk_watched_frame Imm_r method_end rΓ'').
                   repeat split; try constructor.
                   -- exists variable, T. repeat split; assumption.
                   -- exact Hright.
                 * exists initial. split; [exact Hinitial|].
                   eapply potential_connected_trans;
                     [exact Hinitial_left|].
                   apply rt_step. right. left.
                   exists (mk_watched_frame Imm_r method_end rΓ'').
                   repeat split; try constructor; assumption.
               + left; left.
                 simpl in H.
                 destruct H as [Heq | Hin].
                 * subst boundary.
                   eapply Hold_live_rdm_root; eauto.
                   constructor.
                 * eapply Hold_live_rdm_root; eauto.
                   constructor. exact Hin.
             - destruct Hreturn_edge as
                 [callee [boundary
                   [Hboundary [Hview [Hcallee_return
                     [Hruntime [Hroots | Hroots]]]]]]].
               + inversion Hboundary; subst.
                 * simpl in Hcallee_return.
                   rewrite Hruntime_return_mut in Hcallee_return.
                   discriminate.
                 * left; left.
                   eapply Hold_live_rdm_root.
                   -- eapply live_call_boundary_caller_is_live; eauto.
                   -- exact (proj2 Hroots).
               + inversion Hboundary; subst.
                 * simpl in Hcallee_return.
                   rewrite Hruntime_return_mut in Hcallee_return.
                   discriminate.
                 * left; left.
                   have Hcallee_live : live_frame_member
                       (mk_watched_frame Imm_r sGamma rΓ) stack callee.
                   { eapply live_call_boundary_callee_is_live.
                     match goal with
                     | Htail : live_call_boundary _ _ _ _ |- _ =>
                         exact Htail
                     end. }
                   eapply Hold_live_rdm_root.
                   -- exact Hcallee_live.
                   -- exact (proj2 Hroots). }
           assert (Hpropagate :
             forall left right,
               potential_connected CT h'
                 (mk_watched_frame
                   (call_authority Imm_r (sqtype receiver_type))
                   method_end rΓ'')
                 (mk_watched_call_boundary
                   (mk_watched_frame Imm_r sGamma rΓ)
                   (mreceiver (msignature mdef) :: mparams (msignature mdef))
                   (mkr_env (Iot ly :: vals)) (sqtype receiver_type) (mreturn (mbody mdef)) (sqtype destination_type) (sqtype (mret (msignature mdef))) (dom h) origins ::
                   stack)
                 left right ->
               potential_connected CT h'
                 (mk_watched_frame
                   (call_authority Imm_r (sqtype receiver_type))
                   method_end rΓ'')
                 (mk_watched_call_boundary
                   (mk_watched_frame Imm_r sGamma rΓ)
                   (mreceiver (msignature mdef) :: mparams (msignature mdef))
                   (mkr_env (Iot ly :: vals)) (sqtype receiver_type) (mreturn (mbody mdef)) (sqtype destination_type) (sqtype (mret (msignature mdef))) (dom h) origins ::
                   stack)
                 capability left ->
               (left < dom h \/
                exists initial,
                  In Loc body_initial_reachable initial /\
                  potential_connected CT h'
                    (mk_watched_frame Imm_r method_end rΓ'') []
                    initial left) ->
               (right < dom h \/
                exists initial,
                  In Loc body_initial_reachable initial /\
                  potential_connected CT h'
                    (mk_watched_frame Imm_r method_end rΓ'') []
                    initial right) \/
               potential_connected CT h'
                 (mk_watched_frame
                   (call_authority Imm_r (sqtype receiver_type))
                   method_end rΓ'')
                 (mk_watched_call_boundary
                   (mk_watched_frame Imm_r sGamma rΓ)
                   (mreceiver (msignature mdef) :: mparams (msignature mdef))
                   (mkr_env (Iot ly :: vals)) (sqtype receiver_type) (mreturn (mbody mdef)) (sqtype destination_type) (sqtype (mret (msignature mdef))) (dom h) origins ::
                   stack)
                 capability ly).
           { intros left right Hconnected.
             induction Hconnected; intros Hcap_left Hleft_state.
             - eapply Hstep; eauto.
             - left. exact Hleft_state.
             - destruct (IHHconnected1 Hcap_left Hleft_state) as
                 [Hmiddle_state | Hcap_receiver];
                 [|right; exact Hcap_receiver].
               have Hcap_middle :
                   potential_connected CT h'
                     (mk_watched_frame
                       (call_authority Imm_r (sqtype receiver_type))
                       method_end rΓ'')
                     (mk_watched_call_boundary
                       (mk_watched_frame Imm_r sGamma rΓ)
                       (mreceiver (msignature mdef) ::
                         mparams (msignature mdef))
                       (mkr_env (Iot ly :: vals)) (sqtype receiver_type)
                       (mreturn (mbody mdef)) (sqtype destination_type)
                       (sqtype (mret (msignature mdef))) (dom h) origins ::
                       stack)
                     capability y0.
               { eapply potential_connected_trans.
                 - exact Hcap_left.
                 - exact Hconnected1. }
               eapply IHHconnected2; eauto. }
           destruct (Hpropagate capability return_location Hcap_return
             (ltac:(apply rt_refl)) Hcapability_seed) as
             [[Hreturn_old | [initial [Hinitial Hinitial_return]]] |
               Hcap_receiver].
           ++ lia.
           ++ apply (Hlocal_potential return_location initial
               Hreturn_local_capability Hinitial).
             eapply potential_connected_sym; exact Hinitial_return.
           ++ apply (Hpotential_body capability protected Hcapability_pre
               Hprotected).
             eapply potential_connected_trans;
               [exact Hcap_receiver|exact Hreceiver_protected].
      * idtac.
        have Hreturn_immutable :
            r_muttype h' return_location = Some Imm_r.
        { eapply typed_imm_root_runtime_immutable_live;
            [exact Hcallee_final_wf|].
          exists (mreturn (mbody mdef)), body_return_type.
          repeat split; [exact Hreturn_type|exact Hretval|exact Hbody_imm]. }
        have Hreturn_mutable :=
          potential_connected_preserves_runtime_mutability CT h'
            (mk_watched_frame
              (call_authority authority (sqtype receiver_type))
              method_end rΓ'')
            (mk_watched_call_boundary
              (mk_watched_frame authority sGamma rΓ)
              (mreceiver (msignature mdef) :: mparams (msignature mdef))
              (mkr_env (Iot ly :: vals)) (sqtype receiver_type) (mreturn (mbody mdef)) (sqtype destination_type) (sqtype (mret (msignature mdef))) (dom h) origins ::
              stack)
            capability return_location Mut_r Hbody_frames
            (proj1 (proj2 Hcallee_final_wf)) Hcap_return
            Hcapability_runtime.
        rewrite Hreturn_immutable in Hreturn_mutable. discriminate.
  - inversion Htyping; subst.
    eapply (IHHeval2 eq_refl Heval2 P).
    + eapply (IHHeval1 eq_refl Heval1 P); eauto.
    + exact Htype2.
    + exact Hsafe.
}
Qed.
