Require Import Syntax Helpers Typing Bigstep ReadonlyHelper Properties
  Preservation ForwardCapabilityHistory ProtectionHistory WatchedFrames
  ExecutionConfinement MutableCapability AuthorityCapability
  PotentialCapabilityCore LiveCapabilityStack PotentialCapabilityStatement.
Require Export PotentialCapabilityNonNullCall.
From Stdlib Require Import Sets.Ensembles Relations.Relation_Operators.

(** Every runtime-mutable non-null result is already a mutable-authority root
    of the completed callee, independently of which result qualifier was
    selected by flexible overriding.  [RDM] supplies the prospective root,
    [Mut] supplies the capability root, and [Imm] contradicts runtime
    mutability.  This is the single classifier consumed by the generalized
    policy-pop transport in [PotentialCapabilityPolicyPop]. *)
Lemma classified_body_return_is_mutable_authority_root :
  forall CT authority callee_senv callee_renv h return_var return_type
    return_location,
    wf_r_config CT callee_senv callee_renv h ->
    static_getType callee_senv return_var = Some return_type ->
    runtime_getVal callee_renv return_var = Some (Iot return_location) ->
    (sqtype return_type = RDM \/
     sqtype return_type = Mut \/
     sqtype return_type = Imm) ->
    r_muttype h return_location = Some Mut_r ->
    mutable_authority_root
      (mk_watched_frame authority callee_senv callee_renv) h return_location.
Proof.
  intros CT authority callee_senv callee_renv h return_var return_type
    return_location Hwf Htype Hvalue
    [Hrdm | [Hmut | Himm]] Hruntime.
  - right. split.
    + exists return_var, return_type. repeat split; assumption.
    + exact Hruntime.
  - left. exists return_var, return_type. repeat split; assumption.
  - have Himmutable := typed_imm_root_runtime_immutable_live CT callee_senv
      callee_renv h return_location Hwf.
    specialize (Himmutable (ltac:(exists return_var, return_type;
      repeat split; assumption))).
    rewrite Hruntime in Himmutable. discriminate.
Qed.
(** Obsolete unrestricted RDM-return reconstruction.  It predates the saved
    resumed-target policy below and incorrectly tries to discharge an RDM
    destination with the non-RDM pop theorem.  Kept temporarily as migration
    history; remove once the policy-aware branch is fully connected. *)
(*
Lemma private_advancing_policy_successful_rdm_call_case_proved :
  forall P CT rGamma h destination method receiver args vals
    receiver_location runtime_class runtime_mdef body_renv h'
    return_location destination_type caller_senv caller_scope
    caller_final_senv caller_authority stack Z cutoff caller_incoming
    caller_snapshots caller_policies,
    runtime_getVal rGamma receiver = Some (Iot receiver_location) ->
    r_basetype h receiver_location = Some runtime_class ->
    FindMethodWithName CT runtime_class method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    eval_stmt CT (mkr_env (Iot receiver_location :: vals)) h
      (mbody_stmt (mbody runtime_mdef)) OK body_renv h' ->
    runtime_getVal body_renv (mreturn (mbody runtime_mdef)) =
      Some (Iot return_location) ->
    (forall entry_senv entry_scope final_senv callee_authority callee_stack
      incoming snapshots policies,
      principled_phased_authority_live_history_state CT P Z cutoff
        (mk_watched_frame callee_authority entry_senv
          (mkr_env (Iot receiver_location :: vals))) callee_stack incoming
        h ->
      private_advancing_policy_statement_state CT P Z cutoff
        (mk_watched_frame callee_authority entry_senv
          (mkr_env (Iot receiver_location :: vals))) callee_stack incoming
        snapshots policies h ->
      stmt_typing CT entry_senv entry_scope
        (mbody_stmt (mbody runtime_mdef)) final_senv ->
      readonly_state_method_scope entry_scope ->
      exists final_snapshots,
        private_advancing_policy_statement_result CT P Z cutoff
          callee_authority final_senv body_renv callee_stack incoming snapshots
          final_snapshots policies h' /\
        executing_authority_old_colors_reflected CT h
          (mk_watched_frame callee_authority entry_senv
            (mkr_env (Iot receiver_location :: vals))) incoming h'
          (mk_watched_frame callee_authority final_senv body_renv) incoming) ->
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority caller_senv rGamma) stack
      caller_incoming h ->
    private_advancing_policy_statement_state CT P Z cutoff
      (mk_watched_frame caller_authority caller_senv rGamma) stack
      caller_incoming caller_snapshots caller_policies h ->
    stmt_typing CT caller_senv caller_scope
      (SCall destination method receiver args) caller_final_senv ->
    readonly_state_method_scope caller_scope ->
    static_getType caller_senv destination = Some destination_type ->
    sqtype destination_type = RDM ->
    exists final_snapshots,
      private_advancing_policy_statement_result CT P Z cutoff
        caller_authority caller_final_senv
        (update_r_env_value rGamma destination (Iot return_location)) stack
        caller_incoming caller_snapshots final_snapshots caller_policies h' /\
      executing_authority_old_colors_reflected CT h
        (mk_watched_frame caller_authority caller_senv rGamma)
        caller_incoming h'
        (mk_watched_frame caller_authority caller_final_senv
          (update_r_env_value rGamma destination (Iot return_location)))
        caller_incoming.
Proof.
  intros P CT rGamma h destination method receiver args vals
    receiver_location runtime_class runtime_mdef body_renv h'
    return_location destination_type caller_senv caller_scope
    caller_final_senv caller_authority stack Z cutoff caller_incoming
    caller_snapshots caller_policies Hreceiver_value Hbase Hfind Hargs Heval
    Hreturn IH Hpotential Hprivate Htyping Hscope Hdestination_type
    Hdestination_rdm.
  have Hcaller_main := private_policy_statement_state_main CT P Z
    cutoff (mk_watched_frame caller_authority caller_senv rGamma) stack
    caller_incoming caller_snapshots caller_policies h (proj1 Hprivate).
  have Hcaller_wf : wf_r_config CT caller_senv rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hcaller_main))))).
  destruct (safe_typed_call_static_result CT caller_senv caller_scope rGamma h
    destination method receiver args caller_final_senv receiver_location
    runtime_class runtime_mdef Hcaller_wf Htyping Hscope Hreceiver_value Hbase
    Hfind) as [typed_destination [receiver_type [static_mdef Hstatic]]].
  destruct Hstatic as
    [Hcaller_final [Hdestination_receiver [Htyped_destination
      [Hreceiver_type [Hfind_static
        [Hsignature_refinement [Hresult_sub Hreceiver_sub]]]]]]].
  subst caller_final_senv.
  assert (typed_destination = destination_type) by congruence.
  subst typed_destination.
  destruct (typed_call_target CT caller_senv caller_scope rGamma h
    destination method receiver args caller_senv vals receiver_location
    runtime_class runtime_mdef Hcaller_wf Htyping Hreceiver_value Hbase Hfind
    Hargs) as [declaring_class [declaring_def [body_end
      [Hruntime_sub [Hdeclaring [Hmember [Hmethod_wf Hcallee_entry_wf]]]]]]].
  unfold wf_method in Hmethod_wf. simpl in Hmethod_wf.
  destruct Hmethod_wf as
    [_ [method_end [body_return_type
      [Hmethod_body_typing [Hreturn_dom
        [Hreturn_type [Hbody_sub Hoverriding]]]]]]].
  have Hcallee_scope : readonly_state_method_scope
      (mscope (msignature runtime_mdef)) :=
    safe_typed_call_target_method_safe CT caller_senv caller_scope rGamma h
      destination method receiver args caller_senv receiver_location
      runtime_class runtime_mdef Hcaller_wf Htyping Hscope Hreceiver_value
      Hbase Hfind.
  have Hcaller_fresh := proj1 (proj1 (proj1 Hprivate)).
  have Hcaller_witness_fresh :=
    private_advancing_policy_statement_witness_state_is_private_fresh CT P Z
      cutoff (mk_watched_frame caller_authority caller_senv rGamma) stack
      caller_incoming caller_snapshots caller_policies h Hprivate.
  destruct (private_fresh_frozen_statement_enter_call_untracked CT P Z cutoff
    caller_authority caller_senv caller_scope rGamma h stack caller_incoming
    caller_snapshots destination method receiver args caller_senv vals
    receiver_location runtime_class runtime_mdef receiver_type Hcaller_fresh
    Htyping Hscope Hreceiver_type Hreceiver_value Hbase Hfind Hargs) as
    [origins [entry_destination [Hentry_destination Hentry_fresh]]].
  assert (entry_destination = destination_type) by congruence.
  subst entry_destination.
  destruct (private_fresh_frozen_statement_enter_call_untracked CT P Z cutoff
    caller_authority caller_senv caller_scope rGamma h stack caller_incoming
    caller_policies.(suspended_frame_resume_witnesses) destination method
    receiver args caller_senv vals receiver_location runtime_class runtime_mdef
    receiver_type Hcaller_witness_fresh Htyping Hscope Hreceiver_type
    Hreceiver_value Hbase Hfind Hargs) as
    [witness_origins [witness_destination
      [Hwitness_destination Hentry_witness_fresh]]].
  assert (witness_destination = destination_type) by congruence.
  subst witness_destination.
  assert (witness_origins = origins) by apply proof_irrelevance.
  subst witness_origins.
  set (caller := mk_watched_frame caller_authority caller_senv rGamma).
  set (callee := mk_watched_frame
    (call_authority caller_authority (sqtype receiver_type))
    (mreceiver (msignature runtime_mdef) :: mparams (msignature runtime_mdef))
    (mkr_env (Iot receiver_location :: vals))).
  set (boundary := mk_watched_call_boundary caller
    (mreceiver (msignature runtime_mdef) :: mparams (msignature runtime_mdef))
    (mkr_env (Iot receiver_location :: vals)) (sqtype receiver_type)
    (mreturn (mbody runtime_mdef)) (sqtype destination_type)
    (sqtype (mret (msignature runtime_mdef))) (dom h) origins).
  set (callee_incoming := executing_authority_color_set CT h caller
    caller_incoming).
  set (entry_snapshots := None :: advance_frozen_caller_snapshots CT h callee
    caller_snapshots).
  set (entry_policies := enter_private_frame_join_policies_advanced CT h callee
    (Some (private_nested_frozen_call_head CT h caller callee callee_incoming
      caller_snapshots
      caller_policies.(suspended_frame_target_witnesses)))
    None caller_policies).
  have Hentry_main := proj1 (proj1 (proj1 Hentry_fresh)).
  have Hcallee_wf : wf_r_config CT callee.(frame_senv) callee.(frame_renv) h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hentry_main))))).
  have Hcallee_sound : authority_context_sound h callee.(frame_renv)
      callee.(frame_authority) :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hentry_main)))))).
  have Hentry_policy : private_advancing_policy_statement_state CT P Z cutoff
      callee (boundary :: stack) callee_incoming entry_snapshots
      entry_policies h.
  { unfold caller, callee, boundary, callee_incoming, entry_snapshots,
      entry_policies in *.
    eapply private_advancing_policy_statement_enter_untracked_safe_call;
      eauto. }
  have Hbody := IH callee.(frame_senv) (mscope (msignature runtime_mdef))
    method_end callee.(frame_authority) (boundary :: stack) callee_incoming
    entry_snapshots entry_policies.
  unfold callee, boundary in Hbody.
  destruct (Hbody Hentry_main Hentry_policy Hmethod_body_typing Hcallee_scope)
    as [body_snapshots [Hbody_result Hbody_reflection]].
  destruct Hbody_result as
    [body_policies
      (Hbody_policy_metadata & Hbody_witness_growth & Hbody_fixed &
       Hbody_cover & Hbody_phase & Hbody_roots & Hbody_nested &
       Hbody_completed & Hbody_stack_safe & Hbody_before & Hbody_temporal &
       Hbody_target_state)].
  destruct Hbody_fixed as
    [Hbody_principled [Hpolicies_aligned
      [Hpolicies_valid Hbody_separated]]].
  destruct Hbody_principled as [Hbody_statement Hbody_disjoint].
  destruct Hbody_statement as
    [Hbody_potential [Hbody_fresh [Hbody_metadata Hbody_exposure]]].
  destruct (frozen_caller_snapshot_list_metadata_eq_head_none body_snapshots
    (advance_frozen_caller_snapshots CT h callee caller_snapshots)
    Hbody_metadata) as [body_tail [Hbody_snapshots Htail_metadata]].
  subst body_snapshots.
  have Hbody_target_witness_metadata :=
    proj1 (proj2 (proj2 Hbody_policy_metadata)).
  destruct (frozen_caller_snapshot_list_metadata_eq_head_some
    body_policies.(suspended_frame_target_witnesses)
    (private_nested_frozen_call_head CT h caller callee callee_incoming
      caller_snapshots
      caller_policies.(suspended_frame_target_witnesses))
    (advance_frozen_caller_snapshots CT h callee
      caller_policies.(suspended_frame_target_witnesses))
    Hbody_target_witness_metadata) as
    [body_target_witness [body_target_witness_tail
      [Hbody_target_witnesses
        [Hbody_target_head_metadata Hbody_target_witness_tail_metadata]]]].
  have Hbody_witness_metadata :=
    proj2 (proj2 (proj2 Hbody_policy_metadata)).
  destruct (frozen_caller_snapshot_list_metadata_eq_head_none
    body_policies.(suspended_frame_resume_witnesses)
    (advance_frozen_caller_snapshots CT h callee
      caller_policies.(suspended_frame_resume_witnesses))
    Hbody_witness_metadata) as
    [body_witness_tail [Hbody_witnesses Hbody_witness_tail_metadata]].
  set (caller_leave_policies := mk_private_frame_join_policies
    caller_policies.(active_frame_join_targets)
    caller_policies.(suspended_frame_join_targets) body_target_witness_tail
    body_witness_tail).
  set (callee_final := mk_watched_frame callee.(frame_authority) method_end
    body_renv).
  set (caller_post := mk_watched_frame caller_authority caller_senv
    (update_r_env_value rGamma destination (Iot return_location))).
  set (caller_final_policies := advance_private_frame_resume_witnesses CT h'
    caller_post caller_leave_policies).
  have Hleave_policies :
      leave_private_frame_join_policies_advanced body_policies =
      Some caller_leave_policies.
  { unfold leave_private_frame_join_policies_advanced,
      caller_leave_policies. rewrite (proj1 (proj2 Hbody_policy_metadata)).
    unfold entry_policies, enter_private_frame_join_policies_advanced.
    simpl. rewrite Hbody_target_witnesses. rewrite Hbody_witnesses.
    reflexivity. }
  have Hcaller_final_policy_metadata :
      private_frame_join_policies_metadata_eq caller_final_policies
        caller_policies.
  { unfold private_frame_join_policies_metadata_eq, caller_final_policies,
      advance_private_frame_resume_witnesses, caller_leave_policies. simpl.
    split; [reflexivity|]. split; [reflexivity|]. split.
    - eapply frozen_caller_snapshot_list_metadata_eq_trans.
      + apply advance_frozen_caller_snapshots_metadata_eq.
      + eapply frozen_caller_snapshot_list_metadata_eq_trans.
        * exact Hbody_target_witness_tail_metadata.
        * apply advance_frozen_caller_snapshots_metadata_eq.
    - eapply frozen_caller_snapshot_list_metadata_eq_trans.
      + apply advance_frozen_caller_snapshots_metadata_eq.
      + eapply frozen_caller_snapshot_list_metadata_eq_trans.
        * exact Hbody_witness_tail_metadata.
        * apply advance_frozen_caller_snapshots_metadata_eq. }
  have Hcaller_sound : authority_context_sound h rGamma caller_authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hcaller_main)))))).
  have Hcaller_incoming_runtime : authority_colors_runtime_mutable h
      caller_incoming := proj1 (proj2 (proj2 Hcaller_main)).
  have Hcallee_to_caller : forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT h' callee_final callee_incoming)
        (mode, location) ->
      location < dom h ->
      exists caller_mode,
        authority_mode_dangerous caller_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h caller caller_incoming)
          (caller_mode, location).
  { intros mode location Hmode Hcolor Hold.
    unfold caller, callee, callee_final, callee_incoming in *.
    eapply safe_call_body_old_colors_reflect_to_caller; eauto. }
  have Hbody_main := proj1 (proj1 (proj1 Hbody_fresh)).
  have Hbody_frames := proj1 (proj2 (proj2 (proj2 (proj2 Hbody_main)))).
  have Hbody_sounds := proj1 (proj2 (proj2 (proj2 (proj2
    (proj2 Hbody_main))))).
  have Hcaller_current_wf : wf_r_config CT caller_senv rGamma h' :=
    Forall_inv (proj2 Hbody_frames).
  have Hcaller_current_sound : authority_context_sound h' rGamma
      caller_authority := Forall_inv (proj2 Hbody_sounds).
  have Heval_call_raw : eval_stmt CT rGamma h
      (SCall destination method receiver args) OK
      (set_vars rGamma
        (update destination (Iot return_location) rGamma.(vars))) h'.
  { econstructor; eauto. }
  assert (Hupdate : set_vars rGamma
      (update destination (Iot return_location) rGamma.(vars)) =
      update_r_env_value rGamma destination (Iot return_location)).
  { destruct rGamma. reflexivity. }
  rewrite Hupdate in Heval_call_raw.
  have Hcaller_post_wf := preservation_pico CT caller_senv caller_scope
    rGamma h (SCall destination method receiver args)
    (update_r_env_value rGamma destination (Iot return_location)) h'
    caller_senv Hcaller_wf Htyping Heval_call_raw.
  have Hcallee_final_wf : wf_r_config CT method_end body_renv h' :=
    proj1 Hbody_frames.
  have Hcallee_final_sound : authority_context_sound h' body_renv
      callee_final.(frame_authority) := proj1 Hbody_sounds.
  have Hreturn_capability_data :
      capability_in_context caller_authority (sqtype destination_type) ->
      frame_owned_location CT h' callee_final return_location /\
      r_muttype h' return_location = Some Mut_r.
  { intros Hdestination_capability.
    have Hreturn_root : frame_capability_root callee_final return_location.
    { unfold callee_final, callee.
      eapply safe_call_return_value_is_callee_capability_root with
        (caller_h := h) (destination := destination) (receiver := receiver)
        (receiver_location := receiver_location)
        (receiver_type := receiver_type)
        (destination_type := destination_type)
        (return_var := mreturn (mbody runtime_mdef))
        (body_return_type := body_return_type)
        (runtime_sig := msignature runtime_mdef)
        (static_sig := msignature static_mdef).
      - exact Hcaller_wf.
      - exact Hdestination_receiver.
      - exact Hreceiver_type.
      - exact Hreceiver_value.
      - exact Hcallee_final_wf.
      - exact Hreturn_type.
      - exact Hreturn.
      - exact Hbody_sub.
      - exact Hsignature_refinement.
      - exact Hresult_sub.
      - exact Hdestination_type.
      - exact Hcaller_post_wf.
      - exact Hcaller_current_sound.
      - exact Hdestination_capability. }
    have Hreturn_owned : frame_owned_location CT h' callee_final
        return_location.
    { exists return_location. split; [exact Hreturn_root|constructor]. }
    split; [exact Hreturn_owned|].
    exact (frame_capability_root_runtime_mutable CT h' callee_final
      return_location Hcallee_final_wf Hcallee_final_sound Hreturn_root). }
  have Howned_completed : forall anchor,
      frame_owned_location CT h' caller_post anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h' callee_final callee_incoming)
        (FlowPowered, anchor).
  { intros anchor Howned.
    unfold caller, caller_post, callee, callee_final, callee_incoming in *.
    eapply (caller_post_owned_is_callee_powered CT caller_authority
      caller_senv rGamma h destination destination_type receiver
      receiver_location receiver_type
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot receiver_location :: vals)) origins method_end body_renv h'
      (mreturn (mbody runtime_mdef)) body_return_type
      (msignature runtime_mdef) (msignature static_mdef) return_location
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        method_end body_renv) caller_incoming
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority caller_senv rGamma)
        caller_incoming) anchor).
    - exact Hcaller_wf.
    - exact Hdestination_receiver.
    - exact Hdestination_type.
    - exact Hreceiver_type.
    - exact Hreceiver_value.
    - exact Hcallee_final_wf.
    - exact Hreturn_type.
    - exact Hreturn.
    - exact Hbody_sub.
    - exact Hsignature_refinement.
    - exact Hresult_sub.
    - exact Hcaller_post_wf.
    - exact Hcaller_current_sound.
    - reflexivity.
    - reflexivity.
    - exact Howned. }
  have Hwhole_reflection : executing_authority_old_colors_reflected CT h
      caller caller_incoming h' caller_post caller_incoming.
  { unfold caller, caller_post in *.
    eapply non_rdm_nonnull_call_old_colors_reflected with
      (callee := callee_final) (callee_incoming := callee_incoming)
      (destination_type := destination_type); eauto. }
  have Hpop : executing_authority_call_pop_safe CT h' Z callee_final
      callee_incoming caller_post caller_incoming.
  { eapply executing_authority_call_pop_safe_from_old_colors_reflected;
      eauto. }
  have Hcaller_post_sound : authority_context_sound h'
      (update_r_env_value rGamma destination (Iot return_location))
      caller_authority.
  { eapply authority_context_sound_after_nonreceiver_update_live; eauto. }
  have Hpost_main : principled_phased_authority_live_history_state CT P Z
      cutoff caller_post stack caller_incoming h'.
  { eapply principled_phased_authority_history_leave_call_nonnull with
      (P := P) (Z := Z) (cutoff := cutoff) (caller := caller)
      (stack := stack) (caller_incoming := caller_incoming) (caller_h := h)
      (callee := callee_final) (boundary := boundary)
      (callee_senv := method_end) (callee_renv := body_renv)
      (callee_incoming := callee_incoming) (destination := destination)
      (return_var := mreturn (mbody runtime_mdef))
      (return_location := return_location).
    - exact Hcaller_main.
    - unfold boundary. reflexivity.
    - unfold callee_final. reflexivity.
    - exact Hbody_main.
    - unfold callee_incoming. reflexivity.
    - exact Hdestination_receiver.
    - exact Hreturn.
    - exact Hcaller_post_wf.
    - exact Hpop. }
  have Hbody_policy : private_policy_statement_state CT P Z cutoff
      callee_final (boundary :: stack) callee_incoming (None :: body_tail)
      body_policies h'.
  { split.
    - split; assumption.
    - split; [exact Hpolicies_aligned|]. split; assumption. }
  have Hbody_witness_fresh : private_fresh_frozen_statement_state CT P Z
      cutoff callee_final (boundary :: stack) callee_incoming
      (None :: body_witness_tail) h'.
  { eapply private_resume_witness_state_is_private_fresh.
    - exact Hbody_main.
    - unfold frozen_caller_snapshots_aligned.
      rewrite <- Hbody_witnesses.
      exact (proj2 (proj2 Hpolicies_aligned)).
    - rewrite <- Hbody_witnesses. exact Hbody_stack_safe.
    - rewrite <- Hbody_witnesses. exact Hbody_before.
    - rewrite <- Hbody_witnesses. exact Hbody_temporal. }
  have Hroots_reflect : forall snapshot mode source,
      List.In (Some snapshot) body_tail ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT h' caller_post caller_incoming)
        (mode, source) ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
      (exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h' callee_final callee_incoming)
          (callee_mode, source)) \/
      frozen_snapshot_resume_exposure_avoids Z snapshot.
  { intros snapshot mode source _ Hmode Hcolor _.
    left.
    eapply nonnull_post_dangerous_color_is_completed_callee_color with
      (caller_senv := caller_senv) (caller_renv := rGamma)
      (caller_h := h) (caller_post := caller_post).
    - exact Hcaller_wf.
    - unfold callee_incoming, caller. reflexivity.
    - exact Hcallee_to_caller.
    - intros root Hroot. unfold caller_post in Hroot.
      eapply non_rdm_destination_post_rdm_root_is_old; eauto.
    - exact Howned_completed.
    - exact Hmode.
    - exact Hcolor. }
  have Hresumed_pop : executing_resumed_authority_call_pop_safe CT h' Z
      callee_final callee_incoming
      caller_leave_policies.(active_frame_join_targets) caller_post
      caller_incoming.
  { eapply executing_authority_call_pop_safe_implies_resumed. exact Hpop. }
  have Hpost_leave_policy : private_policy_statement_state CT P Z cutoff
      caller_post stack caller_incoming
      (advance_frozen_caller_snapshots CT h' caller_post body_tail)
      caller_leave_policies h'.
  { destruct (capability_in_context_dec caller_authority
      (sqtype destination_type)) as
      [Hdestination_capability | Hdestination_noncapability].
    - destruct (Hreturn_capability_data Hdestination_capability) as
        [Hreturn_owned Hreturn_runtime].
      eapply private_policy_statement_after_untracked_nonnull_pop with
        (active := callee_final) (boundary := boundary) (stack := stack)
        (active_incoming := callee_incoming) (snapshots := body_tail)
        (policies := body_policies)
        (caller_policies := caller_leave_policies)
        (caller_authority := caller_authority) (caller_senv := caller_senv)
        (caller_renv := rGamma) (destination := destination)
        (destination_type := destination_type)
        (return_location := return_location); eauto.
    - eapply private_policy_statement_after_untracked_noncap_nonrdm_pop with
        (active := callee_final) (boundary := boundary) (stack := stack)
        (active_incoming := callee_incoming) (snapshots := body_tail)
        (policies := body_policies)
        (caller_policies := caller_leave_policies)
        (caller_authority := caller_authority) (caller_senv := caller_senv)
        (caller_renv := rGamma) (destination := destination)
        (destination_type := destination_type)
        (value := Iot return_location).
      + exact Hbody_policy.
      + exact Hleave_policies.
      + exact Hpost_main.
      + unfold caller, boundary. reflexivity.
      + exact Hdestination_receiver.
      + exact Hcaller_current_wf.
      + exact Hcaller_post_wf.
      + exact Hcaller_current_sound.
      + exact Hcaller_post_sound.
      + exact Hdestination_type.
      + exact Hdestination_rdm.
      + exact Hdestination_noncapability.
      + exact Hroots_reflect.
      + exact Hresumed_pop. }
  have Hpost_policy : private_policy_statement_state CT P Z cutoff caller_post
      stack caller_incoming
      (advance_frozen_caller_snapshots CT h' caller_post body_tail)
      caller_final_policies h'.
  { unfold caller_final_policies. eapply
      private_policy_statement_state_advance_resume_witnesses.
    exact Hpost_leave_policy. }
  have Hroots_reflect_witness : forall snapshot mode source,
      List.In (Some snapshot) body_witness_tail ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT h' caller_post caller_incoming)
        (mode, source) ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
      (exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h' callee_final callee_incoming)
          (callee_mode, source)) \/
      frozen_snapshot_resume_exposure_avoids Z snapshot.
  { intros snapshot mode source _ Hmode Hcolor _.
    left.
    eapply nonnull_post_dangerous_color_is_completed_callee_color with
      (caller_senv := caller_senv) (caller_renv := rGamma)
      (caller_h := h) (caller_post := caller_post).
    - exact Hcaller_wf.
    - unfold callee_incoming, caller. reflexivity.
    - exact Hcallee_to_caller.
    - intros root Hroot. unfold caller_post in Hroot.
      eapply non_rdm_destination_post_rdm_root_is_old; eauto.
    - exact Howned_completed.
    - exact Hmode.
    - exact Hcolor. }
  have Hpost_witness_structural : private_frozen_snapshot_structural_state CT
      h' caller_post
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail)
      stack.
  { destruct (private_frozen_statement_advance_tail_structural_state CT P Z
      cutoff callee_final boundary stack callee_incoming None
      body_witness_tail h' caller_post (proj1 Hbody_witness_fresh)
      Hcaller_post_wf) as [Hstructural _].
    exact Hstructural. }
  have Hpost_witness_fresh : private_fresh_frozen_statement_state CT P Z
      cutoff caller_post stack caller_incoming
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail) h'.
  { destruct (capability_in_context_dec caller_authority
      (sqtype destination_type)) as
      [Hdestination_capability | Hdestination_noncapability].
    - destruct (Hreturn_capability_data Hdestination_capability) as
        [Hreturn_owned Hreturn_runtime].
      destruct (private_fresh_return_partitions_after_nonnull_pop CT P Z
        cutoff callee_final boundary stack callee_incoming None
        body_witness_tail h' caller_authority caller_senv rGamma destination
        destination_type return_location Hbody_witness_fresh
        (ltac:(unfold boundary, caller; reflexivity)) Hdestination_receiver
        Hcallee_final_wf Hcallee_final_sound Hcaller_current_wf
        Hcaller_post_wf Hcaller_post_sound Hdestination_type Hreturn_owned
        Hreturn_runtime) as
        [Hpost_witness_components
          [Hpost_witness_prospective Hpost_witness_after]].
      have Hpost_witness_return_safety :
          private_frozen_snapshot_return_safety CT h' Z caller_post
            caller_incoming
            (advance_frozen_caller_snapshots CT h' caller_post
              body_witness_tail).
      { eapply
          private_frozen_snapshot_return_safety_after_untracked_return_parts
          with (callee := callee_final) (boundary := boundary)
            (incoming := callee_incoming) (head_slot := None)
            (snapshots := body_witness_tail); eauto. }
      eapply private_fresh_frozen_statement_after_nonnull_return_parts with
        (active := callee_final) (boundary := boundary)
        (active_incoming := callee_incoming) (head_slot := None)
        (snapshots := body_witness_tail)
        (caller_authority := caller_authority) (caller_senv := caller_senv)
        (caller_renv := rGamma) (destination := destination)
        (destination_type := destination_type)
        (return_location := return_location); eauto.
    - destruct
        (private_fresh_return_partitions_after_noncap_nonrdm_pop CT P Z cutoff
          callee_final boundary stack callee_incoming None body_witness_tail h'
          caller_authority caller_senv rGamma destination destination_type
          (Iot return_location) Hbody_witness_fresh
          (ltac:(unfold boundary, caller; reflexivity)) Hdestination_receiver
          Hcaller_current_wf Hcaller_current_sound Hdestination_type
          Hdestination_rdm Hdestination_noncapability) as
        [Hpost_witness_components
          [Hpost_witness_prospective Hpost_witness_after]].
      have Hpost_witness_return_safety :
          private_frozen_snapshot_return_safety CT h' Z caller_post
            caller_incoming
            (advance_frozen_caller_snapshots CT h' caller_post
              body_witness_tail).
      { eapply
          private_frozen_snapshot_return_safety_after_untracked_return_parts
          with (callee := callee_final) (boundary := boundary)
            (incoming := callee_incoming) (head_slot := None)
            (snapshots := body_witness_tail); eauto. }
      eapply
        private_fresh_frozen_statement_after_noncap_nonrdm_return_parts with
        (active := callee_final) (boundary := boundary)
        (active_incoming := callee_incoming) (head := None)
        (snapshots := body_witness_tail)
        (caller_authority := caller_authority) (caller_senv := caller_senv)
        (caller_renv := rGamma) (destination := destination)
        (destination_type := destination_type)
        (value := Iot return_location); eauto.
  }
  have Hfinal_witness_stack_safe : private_resume_witness_stack_safe CT h' Z
      caller_post caller_incoming
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail) :=
    private_fresh_frozen_statement_state_has_resume_witness_stack_safe CT P Z
      cutoff caller_post stack caller_incoming
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail) h'
      Hpost_witness_fresh.
  have Hbody_cover_shape := Hbody_cover.
  rewrite Hbody_witnesses in Hbody_cover_shape.
  have Hfinal_witness_cover : private_resume_witnesses_cover_snapshots Z
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail)
      (advance_frozen_caller_snapshots CT h' caller_post body_tail).
  { eapply private_resume_witnesses_cover_snapshots_after_pop_advance.
    exact Hbody_cover_shape. }
  destruct (private_resume_witness_relations_from_stack_safe CT h' Z
    caller_post caller_incoming
    (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail)
    (advance_frozen_caller_snapshots CT h' caller_post body_tail)
    Hfinal_witness_cover Hfinal_witness_stack_safe) as
    (Hfinal_witness_phase & Hfinal_witness_roots & Hfinal_witness_nested &
      Hfinal_witness_completed).
  have Hfinal_witness_before : frozen_caller_snapshots_before_boundaries
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail)
      stack := proj1 (proj2 (proj2 (proj1 Hpost_witness_fresh))).
  have Hfinal_witness_temporal : private_resume_witness_temporal_state CT h' Z
      cutoff caller_post stack
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail) :=
    private_fresh_frozen_statement_state_has_resume_temporal_state CT P Z
      cutoff caller_post stack caller_incoming
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail) h'
      Hpost_witness_fresh.
  have Hbody_witness_growth_shape := Hbody_witness_growth.
  rewrite Hbody_witnesses in Hbody_witness_growth_shape.
  unfold entry_policies, enter_private_frame_join_policies_advanced in
    Hbody_witness_growth_shape. simpl in Hbody_witness_growth_shape.
  have Hfinal_witness_growth : frozen_caller_snapshot_list_phase_images_grow
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail)
      caller_policies.(suspended_frame_resume_witnesses).
  { eapply returned_policy_tail_phase_images_grow_initial with
      (entry := callee) (entry_head := None) (final_head := None).
    exact Hbody_witness_growth_shape. }
  destruct Hpost_policy as
    [Hpost_principled [Hpost_aligned_policy
      [Hpost_valid_policy Hpost_separated_policy]]].
  destruct Hpost_principled as [Hpost_fresh Hpost_disjoint].
  have Hpost_fresh_copy := Hpost_fresh.
  destruct Hpost_fresh_copy as
    [Hpost_private [Hpost_components [Hpost_prospective Hpost_after]]].
  have Hpost_aligned := proj1 (proj2 (proj1 Hpost_private)).
  have Hreturn_exposure :=
    frozen_snapshot_list_resume_exposure_reflected_after_return_parts CT P Z
      cutoff callee_final boundary stack callee_incoming None body_tail h'
      caller_post Hbody_fresh Hpost_aligned Hpost_prospective Hpost_after
      (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
        (proj2 Hpost_main)))))))) Hcaller_post_wf Hcaller_post_sound.
  have Hentry_exposure :=
    frozen_snapshot_list_resume_exposure_reflected_after_safe_call_entry CT P
      Z cutoff caller_authority caller_senv caller_scope rGamma h stack
      caller_incoming caller_snapshots destination method receiver args
      caller_senv vals receiver_location runtime_class runtime_mdef
      receiver_type Hcaller_fresh Htyping Hscope Hreceiver_type
      Hreceiver_value Hbase Hfind Hargs.
  have Hfinal_metadata := returned_untracked_tail_metadata_eq_initial CT h h'
    callee caller_post caller_snapshots body_tail Hbody_metadata.
  have Hfinal_exposure := returned_untracked_tail_exposure_reflected_initial
    CT h h' Z callee caller_post caller_snapshots body_tail Hreturn_exposure
    Hbody_exposure Hentry_exposure.
  exists (advance_frozen_caller_snapshots CT h' caller_post body_tail). split.
  - exists caller_final_policies. split.
    + exact Hcaller_final_policy_metadata.
    + split; [exact Hfinal_witness_growth|].
      split.
      * split.
        -- split.
           ++ unfold private_statement_preservation_result.
              split; [exact Hpost_main|]. split; [exact Hpost_fresh|].
              split; assumption.
           ++ exact Hpost_disjoint.
        -- split; [exact Hpost_aligned_policy|]. split; assumption.
      * split; [exact Hfinal_witness_cover|].
        split; [exact Hfinal_witness_phase|].
        split; [exact Hfinal_witness_roots|].
        split; [exact Hfinal_witness_nested|].
        split; [exact Hfinal_witness_completed|].
        split; [exact Hfinal_witness_stack_safe|].
        split; [exact Hfinal_witness_before|exact Hfinal_witness_temporal].
  - exact Hwhole_reflection.
Qed.
*)


(** Isolated contract for the RDM-destination half of non-null call
    preservation.  The structural reducer below derives the destination
    type from ordinary call typing and eliminates this contract before the
    recursive statement theorem is exposed. *)
Definition private_advancing_policy_successful_rdm_call_case : Prop :=
  forall P CT rGamma h destination method receiver args vals
    receiver_location runtime_class runtime_mdef body_renv h'
    return_location destination_type caller_senv caller_scope
    caller_final_senv caller_authority stack Z cutoff caller_incoming
    caller_snapshots caller_policies,
    runtime_getVal rGamma receiver = Some (Iot receiver_location) ->
    r_basetype h receiver_location = Some runtime_class ->
    FindMethodWithName CT runtime_class method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    eval_stmt CT (mkr_env (Iot receiver_location :: vals)) h
      (mbody_stmt (mbody runtime_mdef)) OK body_renv h' ->
    runtime_getVal body_renv (mreturn (mbody runtime_mdef)) =
      Some (Iot return_location) ->
    (forall entry_senv entry_scope final_senv callee_authority callee_stack
      incoming snapshots policies,
      principled_phased_authority_live_history_state CT P Z cutoff
        (mk_watched_frame callee_authority entry_senv
          (mkr_env (Iot receiver_location :: vals))) callee_stack incoming
        h ->
      private_advancing_policy_statement_state CT P Z cutoff
        (mk_watched_frame callee_authority entry_senv
          (mkr_env (Iot receiver_location :: vals))) callee_stack incoming
        snapshots policies h ->
      stmt_typing CT entry_senv entry_scope
        (mbody_stmt (mbody runtime_mdef)) final_senv ->
      readonly_state_method_scope entry_scope ->
      exists final_snapshots,
        private_advancing_policy_statement_result CT P Z cutoff
          callee_authority final_senv body_renv callee_stack incoming snapshots
          final_snapshots policies h' /\
        executing_authority_old_colors_reflected CT h
          (mk_watched_frame callee_authority entry_senv
            (mkr_env (Iot receiver_location :: vals))) incoming h'
          (mk_watched_frame callee_authority final_senv body_renv) incoming) ->
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority caller_senv rGamma) stack
      caller_incoming h ->
    private_advancing_policy_statement_state CT P Z cutoff
      (mk_watched_frame caller_authority caller_senv rGamma) stack
      caller_incoming caller_snapshots caller_policies h ->
    stmt_typing CT caller_senv caller_scope
      (SCall destination method receiver args) caller_final_senv ->
    readonly_state_method_scope caller_scope ->
    static_getType caller_senv destination = Some destination_type ->
    sqtype destination_type = RDM ->
    exists final_snapshots,
      private_advancing_policy_statement_result CT P Z cutoff
        caller_authority caller_final_senv
        (update_r_env_value rGamma destination (Iot return_location)) stack
        caller_incoming caller_snapshots final_snapshots caller_policies h' /\
      executing_authority_old_colors_reflected CT h
        (mk_watched_frame caller_authority caller_senv rGamma)
        caller_incoming h'
        (mk_watched_frame caller_authority caller_final_senv
          (update_r_env_value rGamma destination (Iot return_location)))
        caller_incoming.

Lemma private_advancing_policy_successful_nonnull_rule_from_rdm_case :
  private_advancing_policy_successful_rdm_call_case ->
  private_advancing_policy_successful_nonnull_call_rule.
Proof.
  intros Hrdm.
  unfold private_advancing_policy_successful_nonnull_call_rule.
  intros P CT rGamma h destination method receiver args vals
    receiver_location runtime_class runtime_mdef body_renv h' return_location
    Hreceiver_value Hbase Hfind Hargs Heval Hreturn IH caller_senv caller_scope
    caller_final_senv caller_authority stack Z cutoff caller_incoming
    caller_snapshots caller_policies Hpotential Hprivate Htyping Hscope.
  have Hcaller_main := private_policy_statement_state_main CT P Z cutoff
    (mk_watched_frame caller_authority caller_senv rGamma) stack
    caller_incoming caller_snapshots caller_policies h (proj1 Hprivate).
  have Hcaller_wf : wf_r_config CT caller_senv rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hcaller_main))))).
  destruct (safe_typed_call_static_result CT caller_senv caller_scope rGamma h
    destination method receiver args caller_final_senv receiver_location
    runtime_class runtime_mdef Hcaller_wf Htyping Hscope Hreceiver_value Hbase
    Hfind) as [destination_type [receiver_type [static_mdef Hstatic]]].
  destruct Hstatic as
    [_ [_ [Hdestination_type
      [Hreceiver_type [Hfind_static
        [Hsignature_refinement [Hresult_sub Hreceiver_sub]]]]]]].
  destruct (sqtype destination_type) eqn:Hdestination_q.
  - eapply private_advancing_policy_successful_non_rdm_call_case with
      (destination_type := destination_type); eauto.
  - eapply private_advancing_policy_successful_non_rdm_call_case with
      (destination_type := destination_type); eauto.
  - eapply Hrdm with (destination_type := destination_type); eauto.
  - eapply private_advancing_policy_successful_non_rdm_call_case with
      (destination_type := destination_type); eauto.
  - eapply private_advancing_policy_successful_non_rdm_call_case with
      (destination_type := destination_type); eauto.
  - eapply private_advancing_policy_successful_non_rdm_call_case with
      (destination_type := destination_type); eauto.
Qed.

(** Immutable [RDM] return note.

    The final immutable-authority branch must be proved against
    [executing_resumed_authority_color_set] and the saved target policy.  In
    particular, do not instantiate
    [untracked_immutable_resumed_call_pop_safe_from_witness] by postulating a
    heap-wide rule saying that every non-join step into the fresh suffix has
    a fresh source.  Legal allocation can create an edge between a fresh
    object and an old reference, so that rule is not a semantic invariant of
    the language.

    The required proof is target-directed instead.  Under immutable
    authority, every frame-join target is one of the captured pre-call RDM
    roots.  The evolved policy witness classifies authority arriving at such
    a root by its current resume exposure, while its prospective-component
    partition prevents a callee-side fresh component from reaching an older
    protected resume root.  This proof-local classification is the remaining
    immutable branch below; it must be eliminated before the public
    preservation theorem. *)

(** Target-policy-aware counterpart of the older unrestricted call-pop
    classifier.  The derivation is already restricted by [eligible], so the
    only callback concerns an RDM join whose *target* is admitted by the
    saved policy.  Non-join steps reuse the ordinary frozen classification
    and therefore require no allocation-boundary premise. *)
Lemma resumed_dangerous_derivation_class_given_target_joins :
  forall CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h eligible caller caller_incoming state,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some snapshot :: snapshots) h ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state caller_incoming (mode, location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (mode, location)) ->
    (forall location,
      frame_owned_location CT h caller location ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, location)) ->
    (forall mode left right,
      authority_mode_dangerous mode ->
      tracked_resume_frozen_color_class CT h Z active active_incoming caller
        caller_incoming snapshot (mode, left) ->
      typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
      typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
      resumed_frame_join_target eligible caller left ->
      resumed_frame_join_target eligible caller right ->
      tracked_resume_frozen_color_class CT h Z active active_incoming caller
        caller_incoming snapshot (FlowProspective, right)) ->
    resumed_dangerous_color_derivation CT h eligible caller caller_incoming
      state ->
    tracked_resume_frozen_color_class CT h Z active active_incoming caller
      caller_incoming snapshot state.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h eligible caller caller_incoming state Hfull Hincoming Howned
    Hjoin Hderivation.
  induction Hderivation as
    [state Hmode Hincoming_state | location Howned_location |
      source target Hsource IH Hstep].
  - left. destruct state as [mode location]. eapply Hincoming; eauto.
  - right. left. split.
    + eapply Howned. exact Howned_location.
    + eapply resumed_caller_owned_has_frozen_origin. exact Howned_location.
  - inversion Hstep; subst.
    + eapply tracked_resume_nonjoin_step_preserves_class; eauto.
      * eapply frozen_nonjoin_step_in_frame. exact H.
      * eapply frozen_nonjoin_step_in_frame. exact H.
      * eapply frozen_nonjoin_step_is_phased. exact H.
    + eapply Hjoin; eauto. left. reflexivity.
    + eapply Hjoin; eauto. right. reflexivity.
Qed.

Lemma resumed_snapshot_call_pop_safe_given_target_join_classification :
  forall CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h eligible caller caller_incoming,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some snapshot :: snapshots) h ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state caller_incoming (mode, location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (mode, location)) ->
    (forall location,
      frame_owned_location CT h caller location ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, location)) ->
    (forall mode left right,
      authority_mode_dangerous mode ->
      tracked_resume_frozen_color_class CT h Z active active_incoming caller
        caller_incoming snapshot (mode, left) ->
      typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
      typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
      resumed_frame_join_target eligible caller left ->
      resumed_frame_join_target eligible caller right ->
      tracked_resume_frozen_color_class CT h Z active active_incoming caller
        caller_incoming snapshot (FlowProspective, right)) ->
    executing_resumed_authority_call_pop_safe CT h Z active active_incoming
      eligible caller caller_incoming.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h eligible caller caller_incoming Hfull Hincoming Howned Hjoin
    mode location Hmode Hcolor.
  have Hderivation := executing_resumed_dangerous_color_has_derivation CT h
    eligible caller caller_incoming mode location Hmode Hcolor.
  have Hclass :=
    resumed_dangerous_derivation_class_given_target_joins CT P Z cutoff
      active boundary stack active_incoming snapshot snapshots h eligible
      caller caller_incoming (mode, location) Hfull Hincoming Howned Hjoin
      Hderivation.
  eapply tracked_resume_frozen_class_implies_pop_safe; eauto.
Qed.

(** Under immutable authority a dangerous resumed join is necessarily an
    old-root/old-root join: both endpoints had to pass the saved eligibility
    test.  Mapping that private policy into the tracked head's captured root
    set reduces the join to the existing entry-or-safe resume classifier. *)
Lemma immutable_saved_target_join_preserves_tracked_class :
  forall CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h eligible caller caller_incoming mode left right,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some snapshot :: snapshots) h ->
    caller.(frame_authority) = Imm_r ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    (forall location,
      typed_root RDM caller.(frame_senv) caller.(frame_renv) location ->
      resumed_frame_join_target eligible caller location ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) location) ->
    (forall incoming_mode incoming_location,
      authority_mode_dangerous incoming_mode ->
      In authority_flow_state active_incoming
        (incoming_mode, incoming_location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (incoming_mode, incoming_location)) ->
    authority_mode_dangerous mode ->
    tracked_resume_frozen_color_class CT h Z active active_incoming caller
      caller_incoming snapshot (mode, left) ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    resumed_frame_join_target eligible caller left ->
    resumed_frame_join_target eligible caller right ->
    tracked_resume_frozen_color_class CT h Z active active_incoming caller
      caller_incoming snapshot (FlowProspective, right).
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h eligible caller caller_incoming mode left right Hfull
    Hauthority Hcaller_wf Hcaptured Hincoming Hmode Hclass Hleft Hright
    Hleft_target Hright_target.
  have Hleft_captured :
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) left.
  { eapply Hcaptured; eauto. }
  have Hright_captured :
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) right.
  { eapply Hcaptured; eauto. }
  eapply tracked_old_resume_join_preserves_class with
    (caller := caller) (caller_incoming := caller_incoming); eauto.
Qed.

Lemma immutable_saved_target_resumed_call_pop_safe :
  forall CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h eligible caller caller_incoming,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some snapshot :: snapshots) h ->
    caller.(frame_authority) = Imm_r ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    (forall location,
      typed_root RDM caller.(frame_senv) caller.(frame_renv) location ->
      resumed_frame_join_target eligible caller location ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) location) ->
    (forall incoming_mode incoming_location,
      authority_mode_dangerous incoming_mode ->
      In authority_flow_state active_incoming
        (incoming_mode, incoming_location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (incoming_mode, incoming_location)) ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state caller_incoming (mode, location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (mode, location)) ->
    (forall location,
      frame_owned_location CT h caller location ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, location)) ->
    executing_resumed_authority_call_pop_safe CT h Z active active_incoming
      eligible caller caller_incoming.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h eligible caller caller_incoming Hfull Hauthority Hcaller_wf
    Hcaptured Hactive_incoming Hcaller_incoming Howned.
  eapply resumed_snapshot_call_pop_safe_given_target_join_classification;
    eauto.
  intros mode left right Hmode Hclass Hleft Hright Hleft_target
    Hright_target.
  eapply immutable_saved_target_join_preserves_tracked_class; eauto.
Qed.

(** The restored policy cannot accidentally include the newly installed
    return root.  A post-call RDM root is either an old caller root or the
    return itself; policy validity makes every saved target older than the
    call boundary, whereas the mutable body return is in the fresh suffix. *)
Lemma immutable_rdm_persistent_target_is_captured :
  forall CT caller_senv caller_renv caller_h policy_h destination destination_type
    return_location location boundary stack policies caller_policies snapshot
    caller_post,
    wf_r_config CT caller_senv caller_renv caller_h ->
    static_getType caller_senv destination = Some destination_type ->
    sqtype destination_type = RDM ->
    caller_post = mk_watched_frame Imm_r caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) ->
    boundary.(boundary_entry_cutoff) = dom caller_h ->
    private_frame_join_policies_valid policy_h policies (boundary :: stack) ->
    leave_private_frame_join_policies policies = Some caller_policies ->
    Same_set Loc snapshot.(frozen_snapshot_resume_rdm_roots)
      (frame_rdm_root_set
        (mk_watched_frame Imm_r caller_senv caller_renv)) ->
    boundary.(boundary_entry_cutoff) <= return_location ->
    typed_root RDM caller_post.(frame_senv) caller_post.(frame_renv) location ->
    resumed_frame_join_target
      caller_policies.(active_frame_join_targets) caller_post location ->
    In Loc snapshot.(frozen_snapshot_resume_rdm_roots) location.
Proof.
  intros CT caller_senv caller_renv caller_h policy_h destination destination_type
    return_location location boundary stack policies caller_policies snapshot
    caller_post Hcaller_wf Hdestination Hdestination_rdm Hcaller_post
    Hboundary_cutoff Hpolicies_valid Hleave Hroots Hreturn_fresh Hroot
    Htarget.
  subst caller_post.
  destruct Htarget as [Hmutable | Heligible]; [discriminate|].
  destruct (caller_post_rdm_root_origin CT caller_senv caller_renv caller_h
    destination destination_type return_location location Hcaller_wf
    Hdestination Hroot) as [Hold | [Hreturn _]].
  - eapply (proj2 Hroots). exact Hold.
  - subst location.
    have Hold := leave_private_frame_join_targets_before_boundary policy_h
      boundary stack policies caller_policies Hpolicies_valid Hleave
      return_location Heligible.
    rewrite Hboundary_cutoff in Hold, Hreturn_fresh. lia.
Qed.

(** Package the evolved policy head into the exact immutable pop
    obligation.  All provenance and closure facts come from the private
    witness state; the call-specific inputs are only metadata equalities,
    the restored policy stack, and the derived fresh-return bound. *)
Lemma immutable_rdm_policy_witness_resumed_call_pop_safe :
  forall CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv caller_h caller_incoming destination
    destination_type return_location policies caller_policies caller_post,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some snapshot :: snapshots) h ->
    caller_post = mk_watched_frame Imm_r caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) ->
    wf_r_config CT caller_senv caller_renv caller_h ->
    wf_r_config CT caller_post.(frame_senv) caller_post.(frame_renv) h ->
    static_getType caller_senv destination = Some destination_type ->
    sqtype destination_type = RDM ->
    boundary.(boundary_entry_cutoff) = dom caller_h ->
    private_frame_join_policies_valid h policies (boundary :: stack) ->
    leave_private_frame_join_policies policies = Some caller_policies ->
    Same_set Loc snapshot.(frozen_snapshot_resume_rdm_roots)
      (frame_rdm_root_set
        (mk_watched_frame Imm_r caller_senv caller_renv)) ->
    Same_set authority_flow_state active_incoming
      snapshot.(frozen_snapshot_phase_incoming) ->
    Included authority_flow_state caller_incoming active_incoming ->
    (forall location,
      frame_owned_location CT h caller_post location ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, location)) ->
    boundary.(boundary_entry_cutoff) <= return_location ->
    executing_resumed_authority_call_pop_safe CT h Z active active_incoming
      caller_policies.(active_frame_join_targets) caller_post caller_incoming.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv caller_h caller_incoming destination
    destination_type return_location policies caller_policies caller_post
    Hfresh Hcaller_post Hcaller_wf Hcaller_post_wf Hdestination
    Hdestination_rdm Hboundary_cutoff Hpolicies_valid Hleave Hroots
    Hphase_incoming Hcaller_included Howned Hreturn_fresh.
  have Hfull := proj1 (proj1 Hfresh).
  have Hfull_parts := Hfull.
  destruct Hfull_parts as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hphase_covered).
  have Hactive_covered : forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state active_incoming (mode, location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (mode, location).
  { intros mode location Hmode Hincoming.
    eapply Hphase_covered; [simpl; auto|exact Hmode|].
    eapply (proj1 Hphase_incoming). exact Hincoming. }
  have Hcaller_covered : forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state caller_incoming (mode, location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (mode, location).
  { intros mode location Hmode Hincoming.
    eapply Hactive_covered; [exact Hmode|].
    eapply Hcaller_included. exact Hincoming. }
  subst caller_post.
  eapply immutable_saved_target_resumed_call_pop_safe with
    (boundary := boundary) (stack := stack) (snapshot := snapshot)
    (snapshots := snapshots); eauto.
  intros location Hroot Htarget.
  eapply immutable_rdm_persistent_target_is_captured with
    (caller_h := caller_h) (policy_h := h) (destination := destination)
    (destination_type := destination_type) (return_location := return_location)
    (boundary := boundary) (stack := stack) (policies := policies)
    (caller_policies := caller_policies); eauto.
Qed.

(** Recover the immutable call-entry metadata from an evolved policy head
    and derive return freshness from the head's callee-side component
    partition.  This is the form consumed immediately after the recursive
    body result has exposed its final witness list. *)
Lemma immutable_rdm_evolved_policy_head_pop_safe :
  forall CT P Z cutoff active boundary stack active_incoming final_head
    final_tail h caller_senv caller_renv caller_h caller_incoming destination
    destination_type return_var return_type return_location policies
    caller_policies caller_post entry_caller entry_callee entry_snapshots
    entry_witnesses,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some final_head :: final_tail) h ->
    frozen_caller_snapshot_metadata_eq final_head
      (private_nested_frozen_call_head CT caller_h entry_caller entry_callee
        active_incoming entry_snapshots entry_witnesses) ->
    entry_caller = mk_watched_frame Imm_r caller_senv caller_renv ->
    caller_post = mk_watched_frame Imm_r caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) ->
    wf_r_config CT caller_senv caller_renv caller_h ->
    wf_r_config CT caller_post.(frame_senv) caller_post.(frame_renv) h ->
    static_getType caller_senv destination = Some destination_type ->
    sqtype destination_type = RDM ->
    boundary.(boundary_entry_cutoff) = dom caller_h ->
    private_frame_join_policies_valid h policies (boundary :: stack) ->
    leave_private_frame_join_policies policies = Some caller_policies ->
    Included authority_flow_state caller_incoming active_incoming ->
    (forall location,
      frame_owned_location CT h caller_post location ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, location)) ->
    static_getType active.(frame_senv) return_var = Some return_type ->
    runtime_getVal active.(frame_renv) return_var =
      Some (Iot return_location) ->
    sqtype return_type = Mut ->
    r_muttype h return_location = Some Mut_r ->
    executing_resumed_authority_call_pop_safe CT h Z active active_incoming
      caller_policies.(active_frame_join_targets) caller_post caller_incoming.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming final_head
    final_tail h caller_senv caller_renv caller_h caller_incoming destination
    destination_type return_var return_type return_location policies
    caller_policies caller_post entry_caller entry_callee entry_snapshots
    entry_witnesses Hfresh Hhead_metadata Hentry_caller Hcaller_post
    Hcaller_wf Hcaller_post_wf Hdestination Hdestination_rdm Hboundary_cutoff
    Hpolicies_valid Hleave Hcaller_included Howned Hreturn_type Hreturn_value
    Hreturn_mut Hreturn_runtime.
  have Hroots : Same_set Loc final_head.(frozen_snapshot_resume_rdm_roots)
      (frame_rdm_root_set
        (mk_watched_frame Imm_r caller_senv caller_renv)).
  { subst entry_caller.
    unfold private_nested_frozen_call_head in Hhead_metadata.
    eapply nested_frozen_head_metadata_recovers_resume_roots.
    exact Hhead_metadata. }
  have Hphase : Same_set authority_flow_state
      final_head.(frozen_snapshot_phase_incoming) active_incoming.
  { unfold private_nested_frozen_call_head in Hhead_metadata.
    eapply nested_frozen_head_metadata_recovers_phase_incoming.
    exact Hhead_metadata. }
  have Hreturn_fresh : boundary.(boundary_entry_cutoff) <= return_location.
  { eapply tracked_head_mut_return_retained_component_is_fresh with
      (active := active) (snapshot := final_head) (snapshots := final_tail)
      (stack := stack) (return_var := return_var)
      (return_type := return_type); eauto.
    - exact (proj1 (proj2 Hfresh)).
    - constructor. }
  subst caller_post.
  eapply immutable_rdm_policy_witness_resumed_call_pop_safe with
    (snapshot := final_head) (snapshots := final_tail)
    (caller_h := caller_h) (policies := policies)
    (caller_policies := caller_policies); eauto.
  exact (conj (proj2 Hphase) (proj1 Hphase)).
Qed.

(** If every RDM root of the resumed caller is already represented by a
    dangerous completed-callee color, caller-frame joins need no historical
    reconstruction: their target is itself already completed. *)
Lemma nonnull_post_frozen_path_preserves_completed_color_from_rdm_roots :
  forall CT final_h callee callee_incoming caller_post source target,
    (forall root,
      typed_root RDM caller_post.(frame_senv) caller_post.(frame_renv) root ->
      exists root_mode,
        authority_mode_dangerous root_mode /\
        In authority_flow_state
          (executing_authority_color_set CT final_h callee callee_incoming)
          (root_mode, root)) ->
    authority_mode_dangerous (fst source) ->
    In authority_flow_state
      (executing_authority_color_set CT final_h callee callee_incoming)
      source ->
    frozen_caller_authority_connected CT final_h caller_post source target ->
    authority_mode_dangerous (fst target) /\
    In authority_flow_state
      (executing_authority_color_set CT final_h callee callee_incoming)
      target.
Proof.
  intros CT final_h callee callee_incoming caller_post source target
    Hroot_completed Hsource_mode Hsource Hpath.
  induction Hpath as [left right Hstep | state | left middle right Hleft IHleft
    Hright IHright].
  - destruct left as [left_mode left_location].
    destruct right as [right_mode right_location]. simpl in *.
    inversion Hstep; subst.
    + split; [left; reflexivity|].
      eapply executing_authority_dangerous_retained; eauto.
    + split; [right; reflexivity|].
      eapply executing_authority_dangerous_retained; eauto.
    + split; [right; reflexivity|].
      eapply executing_authority_dangerous_reverse_rdm; eauto.
    + split; [right; reflexivity|].
      eapply executing_authority_dangerous_reverse_rdm; eauto.
    + destruct (ltac:(eapply Hroot_completed; eauto)) as
        [root_mode [Hroot_mode Hroot_color]].
      split; [right; reflexivity|].
      destruct Hroot_mode as [Hpowered | Hprospective]; subst root_mode.
      * destruct Hroot_color as [seed [Hseed Hprefix]].
        exists seed. split; [exact Hseed|].
        eapply rt_trans; [exact Hprefix|].
        apply rt_step. apply phased_authority_mark_prospective.
      * exact Hroot_color.
    + destruct (ltac:(eapply Hroot_completed; eauto)) as
        [root_mode [Hroot_mode Hroot_color]].
      split; [right; reflexivity|].
      destruct Hroot_mode as [Hpowered | Hprospective]; subst root_mode.
      * destruct Hroot_color as [seed [Hseed Hprefix]].
        exists seed. split; [exact Hseed|].
        eapply rt_trans; [exact Hprefix|].
        apply rt_step. apply phased_authority_mark_prospective.
      * exact Hroot_color.
    + split; [right; reflexivity|].
      destruct Hsource as [seed [Hseed Hprefix]].
      exists seed. split; [exact Hseed|].
      eapply rt_trans; [exact Hprefix|].
      apply rt_step. apply phased_authority_mark_prospective.
  - destruct state. split; assumption.
  - destruct (IHleft Hsource_mode Hsource) as
      [Hmiddle_mode Hmiddle_color].
    eapply IHright; eauto.
Qed.

Lemma nonnull_post_dangerous_color_is_completed_from_rdm_roots :
  forall CT final_h callee callee_incoming caller_incoming caller_post mode
    location,
    (forall root,
      typed_root RDM caller_post.(frame_senv) caller_post.(frame_renv) root ->
      exists root_mode,
        authority_mode_dangerous root_mode /\
        In authority_flow_state
          (executing_authority_color_set CT final_h callee callee_incoming)
          (root_mode, root)) ->
    (forall anchor,
      frame_owned_location CT final_h caller_post anchor ->
      In authority_flow_state
        (executing_authority_color_set CT final_h callee callee_incoming)
        (FlowPowered, anchor)) ->
    Included authority_flow_state caller_incoming callee_incoming ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT final_h caller_post caller_incoming)
      (mode, location) ->
    exists callee_mode,
      authority_mode_dangerous callee_mode /\
      In authority_flow_state
        (executing_authority_color_set CT final_h callee callee_incoming)
        (callee_mode, location).
Proof.
  intros CT final_h callee callee_incoming caller_incoming caller_post mode
    location Hroots Howned Hincoming Hmode [seed [Hseed Hpath]].
  destruct (phased_dangerous_path_has_frozen_origin_or_owned_promotion CT
    final_h caller_post seed (mode, location) Hmode Hpath) as
    [[Hseed_mode Hfrozen] | [anchor [Hanchor_owned Hfrozen]]].
  - have Hseed_color : In authority_flow_state
        (executing_authority_color_set CT final_h callee callee_incoming) seed.
    { inversion Hseed as [state Hcaller_incoming | state Hpowered]; subst seed.
      - apply executing_authority_color_set_contains_incoming.
        apply Hincoming. exact Hcaller_incoming.
      - destruct Hpowered as [owned [Heq Hanchor]]. inversion Heq; subst.
        eapply Howned. exact Hanchor. }
    destruct
      (nonnull_post_frozen_path_preserves_completed_color_from_rdm_roots CT
        final_h callee callee_incoming caller_post seed (mode, location)
        Hroots Hseed_mode Hseed_color Hfrozen) as [_ Htarget_color].
    exists mode. split; assumption.
  - have Hanchor_color := Howned anchor Hanchor_owned.
    destruct
      (nonnull_post_frozen_path_preserves_completed_color_from_rdm_roots CT
        final_h callee callee_incoming caller_post (FlowPowered, anchor)
        (mode, location) Hroots (or_introl eq_refl) Hanchor_color Hfrozen)
      as [_ Htarget_color].
    exists mode. split; assumption.
Qed.

(** Under mutable caller authority, every RDM root is a capability root.
    Therefore the generic completed-callee ownership classifier supplies the
    root premise required above. *)
Lemma mutable_post_rdm_roots_are_completed_callee_colors :
  forall CT final_h callee callee_incoming caller_senv caller_renv root,
    (forall anchor,
      frame_owned_location CT final_h
        (mk_watched_frame Mut_r caller_senv caller_renv) anchor ->
      In authority_flow_state
        (executing_authority_color_set CT final_h callee callee_incoming)
        (FlowPowered, anchor)) ->
    typed_root RDM caller_senv caller_renv root ->
    exists root_mode,
      authority_mode_dangerous root_mode /\
      In authority_flow_state
        (executing_authority_color_set CT final_h callee callee_incoming)
        (root_mode, root).
Proof.
  intros CT final_h callee callee_incoming caller_senv caller_renv root
    Howned Hroot.
  exists FlowPowered. split; [left; reflexivity|].
  apply Howned. exists root. split.
  - destruct Hroot as [variable [T [Htype [Hvalue Hrdm]]]].
    exists variable, T. repeat split; try assumption.
    right. split; [exact Hrdm|reflexivity].
  - constructor.
Qed.

Lemma mutable_rdm_nonnull_call_old_colors_reflected :
  forall CT caller_senv caller_renv caller_h final_h callee callee_incoming
    caller_incoming caller_post_renv,
    callee_incoming = executing_authority_color_set CT caller_h
      (mk_watched_frame Mut_r caller_senv caller_renv) caller_incoming ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT final_h callee callee_incoming)
        (mode, location) ->
      location < dom caller_h ->
      exists caller_mode,
        authority_mode_dangerous caller_mode /\
        In authority_flow_state
          (executing_authority_color_set CT caller_h
            (mk_watched_frame Mut_r caller_senv caller_renv) caller_incoming)
          (caller_mode, location)) ->
    (forall anchor,
      frame_owned_location CT final_h
        (mk_watched_frame Mut_r caller_senv caller_post_renv) anchor ->
      In authority_flow_state
        (executing_authority_color_set CT final_h callee callee_incoming)
        (FlowPowered, anchor)) ->
    executing_authority_old_colors_reflected CT caller_h
      (mk_watched_frame Mut_r caller_senv caller_renv) caller_incoming final_h
      (mk_watched_frame Mut_r caller_senv caller_post_renv) caller_incoming.
Proof.
  intros CT caller_senv caller_renv caller_h final_h callee callee_incoming
    caller_incoming caller_post_renv Hincoming Hbody Howned.
  eapply completed_callee_classifier_implies_call_old_colors_reflected with
    (callee := callee) (callee_incoming := callee_incoming).
  - intros mode location Hmode Hcolor.
    eapply nonnull_post_dangerous_color_is_completed_from_rdm_roots with
      (callee := callee) (callee_incoming := callee_incoming)
      (caller_incoming := caller_incoming)
      (caller_post := mk_watched_frame Mut_r caller_senv caller_post_renv).
    + intros root Hroot.
      exact (mutable_post_rdm_roots_are_completed_callee_colors CT final_h
        callee callee_incoming caller_senv caller_post_renv root Howned Hroot).
    + exact Howned.
    + intros state Hstate. rewrite Hincoming.
      apply executing_authority_color_set_contains_incoming. exact Hstate.
    + exact Hmode.
    + exact Hcolor.
  - exact Hbody.
Qed.

(** Public merge for the non-exceptional RDM return shapes.  A dynamic RDM
    result installs the ordinary bidirectional call-return bridge, so either
    bridge orientation is already visible to the callee-side potential
    invariant.  A dynamic immutable result cannot lie on a bridge from a
    live capability because potential connectivity preserves runtime
    mutability.  The only shape intentionally absent here is the covariant
    [Mut] result under immutable caller authority. *)
Lemma regular_rdm_call_pop_merge_safe :
  forall CT P Z cutoff final_h caller_post stack callee boundary
    receiver_location return_location,
    potential_live_history_state CT P Z cutoff callee (boundary :: stack)
      final_h ->
    Included Loc
      (live_capability_set CT final_h caller_post stack)
      (live_capability_set CT final_h callee (boundary :: stack)) ->
    typed_root RDM boundary.(boundary_caller).(frame_senv)
      boundary.(boundary_caller).(frame_renv) receiver_location ->
    r_muttype final_h return_location =
      r_muttype final_h receiver_location ->
    ((typed_root RDM callee.(frame_senv) callee.(frame_renv)
        return_location /\
      boundary.(boundary_receiver_view) = RDM /\
      boundary.(boundary_callee_return_qualifier) = RDM) \/
     (typed_root Imm callee.(frame_senv) callee.(frame_renv)
        return_location /\
      r_muttype final_h return_location = Some Imm_r)) ->
    call_pop_merge_safe CT final_h
      (live_capability_set CT final_h caller_post stack) Z callee
      (boundary :: stack) receiver_location return_location.
Proof.
  intros CT P Z cutoff final_h caller_post stack callee boundary
    receiver_location return_location Hbody Hpost_in_pre Hreceiver_root
    Hruntime Hcase capability protected Hcapability
    Hprotected Hbridge.
  have Hbody_live := proj1 Hbody.
  have Hbody_frames := proj1 (proj2 Hbody_live).
  have Hbody_sounds := proj1 (proj2 (proj2 Hbody_live)).
  have Hbody_heap := proj1 (proj2 (proj1 Hbody_frames)).
  have Hbody_separated := proj1 (proj2 Hbody).
  have Hcapability_pre := Hpost_in_pre capability Hcapability.
  have Hcapability_runtime : r_muttype final_h capability = Some Mut_r.
  { eapply live_capability_members_runtime_mutable.
    - exact Hbody_frames.
    - exact Hbody_sounds.
    - exact Hcapability_pre. }
  destruct Hcase as [Hrdm_case | Himm_case].
  destruct Hrdm_case as
      [Hreturn_root [Hreceiver_view Hreturn_qualifier]].
  - have Hreturn_receiver : potential_connected CT final_h callee
        (boundary :: stack) return_location receiver_location.
    { apply rt_step. right. right. exists callee, boundary.
      split; [constructor|]. split; [exact Hreceiver_view|].
      split; [exact Hreturn_qualifier|]. split.
      - exact Hruntime.
      - left. split; assumption. }
    have Hreceiver_return : potential_connected CT final_h callee
        (boundary :: stack) receiver_location return_location.
    { apply rt_step. right. right. exists callee, boundary.
      split; [constructor|]. split; [exact Hreceiver_view|].
      split; [exact Hreturn_qualifier|]. split.
      - symmetry. exact Hruntime.
      - right. split; assumption. }
    apply (Hbody_separated capability protected Hcapability_pre Hprotected).
    destruct Hbridge as
      [[Hcap_receiver Hreturn_protected] |
       [Hcap_return Hreceiver_protected]].
    + eapply potential_connected_trans; [exact Hcap_receiver|].
      eapply potential_connected_trans; eauto.
    + eapply potential_connected_trans; [exact Hcap_return|].
      eapply potential_connected_trans; eauto.
  - destruct Himm_case as [Hreturn_root Hreturn_immutable].
    destruct Hbridge as
      [[Hcap_receiver _] | [Hcap_return _]].
    + have Hreceiver_mutable :=
        potential_connected_preserves_runtime_mutability CT final_h callee
          (boundary :: stack) capability receiver_location Mut_r Hbody_frames
          Hbody_heap Hcap_receiver Hcapability_runtime.
      rewrite Hruntime in Hreturn_immutable.
      rewrite Hreceiver_mutable in Hreturn_immutable. discriminate.
    + have Hreturn_mutable :=
        potential_connected_preserves_runtime_mutability CT final_h callee
          (boundary :: stack) capability return_location Mut_r Hbody_frames
          Hbody_heap Hcap_return Hcapability_runtime.
      rewrite Hreturn_mutable in Hreturn_immutable. discriminate.
Qed.

(** The legacy merge obligation is discharged directionally under mutable
    caller authority.  If the body returns RDM or Mut, the bridge's protected
    endpoint is itself a live capability (the return or the suspended
    receiver).  If it returns Imm, final caller typing would make the same
    value runtime mutable and immutable simultaneously.  No symmetry of
    [potential_connected] is used. *)
Lemma mutable_rdm_call_pop_merge_safe :
  forall CT P Z cutoff caller_senv caller_renv stack destination
    destination_type receiver receiver_type receiver_location boundary
    callee_senv callee_renv final_h return_var body_return_type
    return_location,
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    sqtype destination_type = RDM ->
    static_getType caller_senv receiver = Some receiver_type ->
    runtime_getVal caller_renv receiver = Some (Iot receiver_location) ->
    sqtype receiver_type = RDM ->
    boundary.(boundary_caller) =
      mk_watched_frame Mut_r caller_senv caller_renv ->
    static_getType callee_senv return_var = Some body_return_type ->
    runtime_getVal callee_renv return_var = Some (Iot return_location) ->
    (sqtype body_return_type = RDM \/
     sqtype body_return_type = Mut \/
     sqtype body_return_type = Imm) ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location))
      final_h ->
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame
        (call_authority Mut_r (sqtype receiver_type)) callee_senv callee_renv)
      (boundary :: stack) final_h ->
    call_pop_merge_safe CT final_h
      (live_capability_set CT final_h
        (mk_watched_frame Mut_r caller_senv
          (update_r_env_value caller_renv destination (Iot return_location)))
        stack)
      Z
      (mk_watched_frame
        (call_authority Mut_r (sqtype receiver_type)) callee_senv callee_renv)
      (boundary :: stack) receiver_location return_location.
Proof.
  intros CT P Z cutoff caller_senv caller_renv stack destination
    destination_type receiver receiver_type receiver_location boundary
    callee_senv callee_renv final_h return_var body_return_type return_location
    Hdestination_nonzero Hdestination Hdestination_rdm Hreceiver
    Hreceiver_value Hreceiver_rdm Hboundary Hreturn_type Hreturn_value
    Hbody_cases Hcaller_post_wf Hbody capability protected _ Hprotected
    Hbridge.
  have Hbody_separated := proj1 (proj2 Hbody).
  have Hreceiver_live : In Loc
      (live_capability_set CT final_h
        (mk_watched_frame
          (call_authority Mut_r (sqtype receiver_type)) callee_senv callee_renv)
        (boundary :: stack)) receiver_location.
  { exists receiver_location. split.
    - right. exists boundary. split; [simpl; auto|].
      unfold boundary_capability_root. rewrite Hboundary.
      exists receiver, receiver_type. repeat split; try assumption.
      right. split; [exact Hreceiver_rdm|reflexivity].
    - constructor. }
  destruct Hbody_cases as [Hbody_rdm | [Hbody_mut | Hbody_imm]].
  - have Hreturn_live : In Loc
        (live_capability_set CT final_h
          (mk_watched_frame
            (call_authority Mut_r (sqtype receiver_type)) callee_senv
            callee_renv) (boundary :: stack)) return_location.
    { exists return_location. split; [left|constructor].
      exists return_var, body_return_type. repeat split; try assumption.
      right. split; [exact Hbody_rdm|].
      unfold call_authority. rewrite Hreceiver_rdm. reflexivity. }
    destruct Hbridge as [[_ Hreturn_protected] | [_ Hreceiver_protected]].
    + exact (Hbody_separated return_location protected Hreturn_live Hprotected
        Hreturn_protected).
    + exact (Hbody_separated receiver_location protected Hreceiver_live
        Hprotected Hreceiver_protected).
  - have Hreturn_live : In Loc
        (live_capability_set CT final_h
          (mk_watched_frame
            (call_authority Mut_r (sqtype receiver_type)) callee_senv
            callee_renv) (boundary :: stack)) return_location.
    { exists return_location. split; [left|constructor].
      exists return_var, body_return_type. repeat split; try assumption.
      left. exact Hbody_mut. }
    destruct Hbridge as [[_ Hreturn_protected] | [_ Hreceiver_protected]].
    + exact (Hbody_separated return_location protected Hreturn_live Hprotected
        Hreturn_protected).
    + exact (Hbody_separated receiver_location protected Hreceiver_live
        Hprotected Hreceiver_protected).
  - have Hbody_live := proj1 Hbody.
    have Hbody_frames := proj1 (proj2 Hbody_live).
    have Hbody_sounds := proj1 (proj2 (proj2 Hbody_live)).
    have Hcaller_current_wf : wf_r_config CT caller_senv caller_renv final_h.
    { have Hsaved := Forall_inv (proj2 Hbody_frames).
      rewrite Hboundary in Hsaved. exact Hsaved. }
    have Hcaller_sound : authority_context_sound final_h caller_renv Mut_r.
    { have Hsaved := Forall_inv (proj2 Hbody_sounds).
      rewrite Hboundary in Hsaved. exact Hsaved. }
    have Hcaller_post_sound : authority_context_sound final_h
        (update_r_env_value caller_renv destination (Iot return_location))
        Mut_r.
    { eapply authority_context_sound_after_nonreceiver_update_live; eauto. }
    have Hreturn_root : frame_capability_root
        (mk_watched_frame Mut_r caller_senv
          (update_r_env_value caller_renv destination (Iot return_location)))
        return_location.
    { exists destination, destination_type. repeat split; try assumption.
      - have Hdom := Hdestination. apply static_getType_dom in Hdom.
        unfold wf_r_config in Hcaller_current_wf.
        destruct Hcaller_current_wf as [_ [_ [_ [_ [Hlength _]]]]].
        eapply runtime_getVal_update_same. lia.
      - right. split; [exact Hdestination_rdm|reflexivity]. }
    have Hreturn_mutable := frame_capability_root_runtime_mutable CT final_h
      (mk_watched_frame Mut_r caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      return_location Hcaller_post_wf Hcaller_post_sound Hreturn_root.
    have Hcallee_wf : wf_r_config CT callee_senv callee_renv final_h :=
      proj1 Hbody_frames.
    have Hreturn_immutable := typed_imm_root_runtime_immutable_live CT
      callee_senv callee_renv final_h return_location Hcallee_wf
      (ltac:(exists return_var, body_return_type;
        repeat split; assumption)).
    rewrite Hreturn_mutable in Hreturn_immutable. discriminate.
Qed.

(** Complete case split for an RDM destination.  The ordinary dynamic-RDM
    and dynamic-immutable results are discharged by
    [regular_rdm_call_pop_merge_safe], while mutable caller authority is
    discharged by [mutable_rdm_call_pop_merge_safe].  Consequently the only
    proof supplied by the policy-aware call reconstruction is the genuinely
    exceptional shape: immutable caller authority and a dynamically mutable
    result.  Keeping that callback here makes it impossible for the
    exceptional obligation to escape into the public statement theorem. *)
Lemma classified_rdm_call_pop_merge_safe :
  forall CT P Z cutoff caller_authority caller_senv caller_renv stack
    destination destination_type receiver receiver_type receiver_location
    boundary callee_senv callee_renv final_h return_var body_return_type
    return_location caller_post callee,
    caller_post = mk_watched_frame caller_authority caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) ->
    callee = mk_watched_frame
      (call_authority caller_authority (sqtype receiver_type))
      callee_senv callee_renv ->
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    sqtype destination_type = RDM ->
    static_getType caller_senv receiver = Some receiver_type ->
    runtime_getVal caller_renv receiver = Some (Iot receiver_location) ->
    sqtype receiver_type = RDM ->
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    boundary.(boundary_receiver_view) = RDM ->
    static_getType callee_senv return_var = Some body_return_type ->
    runtime_getVal callee_renv return_var = Some (Iot return_location) ->
    r_muttype final_h return_location =
      r_muttype final_h receiver_location ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location))
      final_h ->
    potential_live_history_state CT P Z cutoff callee (boundary :: stack)
      final_h ->
    Included Loc
      (live_capability_set CT final_h caller_post stack)
      (live_capability_set CT final_h callee (boundary :: stack)) ->
    typed_root RDM boundary.(boundary_caller).(frame_senv)
      boundary.(boundary_caller).(frame_renv) receiver_location ->
    ((sqtype body_return_type = RDM /\
      boundary.(boundary_callee_return_qualifier) = RDM) \/
     sqtype body_return_type = Mut \/
     (sqtype body_return_type = Imm /\
      r_muttype final_h return_location = Some Imm_r)) ->
    (caller_authority = Imm_r ->
      sqtype body_return_type = Mut ->
      call_pop_merge_safe CT final_h
        (live_capability_set CT final_h caller_post stack) Z callee
        (boundary :: stack) receiver_location return_location) ->
    call_pop_merge_safe CT final_h
      (live_capability_set CT final_h caller_post stack) Z callee
      (boundary :: stack) receiver_location return_location.
Proof.
  intros CT P Z cutoff caller_authority caller_senv caller_renv stack
    destination destination_type receiver receiver_type receiver_location
    boundary callee_senv callee_renv final_h return_var body_return_type
    return_location caller_post callee Hcaller_post Hcallee
    Hdestination_nonzero Hdestination Hdestination_rdm Hreceiver
    Hreceiver_value Hreceiver_rdm Hboundary Hreceiver_view Hreturn_type
    Hreturn_value Hruntime Hcaller_post_wf Hbody Hpost_in_pre Hreceiver_root
    Hbody_case Hexception.
  subst caller_post callee.
  destruct caller_authority.
  - eapply mutable_rdm_call_pop_merge_safe with
      (destination_type := destination_type) (receiver := receiver)
      (return_var := return_var) (body_return_type := body_return_type);
      eauto.
    destruct Hbody_case as [[Hbody_rdm _] | [Hbody_mut | [Hbody_imm _]]];
      auto.
  - destruct Hbody_case as
      [[Hbody_rdm Hcallee_return] | [Hbody_mut | [Hbody_imm Hreturn_imm]]].
    + eapply regular_rdm_call_pop_merge_safe with
        (P := P) (cutoff := cutoff); eauto.
      left. split.
      * exists return_var, body_return_type. repeat split; assumption.
      * split; assumption.
    + eapply Hexception; eauto.
    + eapply regular_rdm_call_pop_merge_safe with
        (P := P) (cutoff := cutoff); eauto.
      right. split.
      * exists return_var, body_return_type. repeat split; assumption.
      * exact Hreturn_imm.
Qed.
