Require Import Syntax Helpers Typing Bigstep ReadonlyHelper Properties Preservation
  ForwardCapabilityHistory ProtectionHistory WatchedFrames
  ExecutionConfinement MutableCapability AuthorityCapability PotentialCapabilityCore
  LiveCapabilityStack PotentialCapabilityStatement.
Require Export PotentialCapabilityCall.
From Stdlib Require Import Sets.Ensembles Relations.Relation_Operators.

(** Proof-local contract for the non-null half of successful call
    preservation.  Its eventual theorem is consumed by the structural call
    rule and eliminated before the public preservation statement. *)
Definition private_advancing_policy_successful_nonnull_call_rule : Prop :=
  forall P CT rGamma h destination method receiver args vals
    receiver_location runtime_class runtime_mdef body_renv h'
    return_location,
    runtime_getVal rGamma receiver = Some (Iot receiver_location) ->
    r_basetype h receiver_location = Some runtime_class ->
    FindMethodWithName CT runtime_class method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    eval_stmt CT (mkr_env (Iot receiver_location :: vals)) h
      (mbody_stmt (mbody runtime_mdef)) OK body_renv h' ->
    runtime_getVal body_renv (mreturn (mbody runtime_mdef)) =
      Some (Iot return_location) ->
    (forall entry_senv entry_scope final_senv callee_authority callee_stack
      Z cutoff incoming snapshots policies,
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
        private_advancing_policy_statement_result CT P Z cutoff callee_authority
          final_senv body_renv callee_stack incoming snapshots final_snapshots
          policies h' /\
        executing_authority_old_colors_reflected CT h
          (mk_watched_frame callee_authority entry_senv
            (mkr_env (Iot receiver_location :: vals))) incoming h'
          (mk_watched_frame callee_authority final_senv body_renv) incoming) ->
    forall caller_senv caller_scope caller_final_senv caller_authority stack Z
      cutoff caller_incoming caller_snapshots caller_policies,
      principled_phased_authority_live_history_state CT P Z cutoff
        (mk_watched_frame caller_authority caller_senv rGamma) stack
        caller_incoming h ->
      private_advancing_policy_statement_state CT P Z cutoff
        (mk_watched_frame caller_authority caller_senv rGamma) stack
        caller_incoming caller_snapshots caller_policies h ->
      stmt_typing CT caller_senv caller_scope
        (SCall destination method receiver args) caller_final_senv ->
      readonly_state_method_scope caller_scope ->
      exists final_snapshots,
        private_advancing_policy_statement_result CT P Z cutoff caller_authority
          caller_final_senv
          (update_r_env_value rGamma destination (Iot return_location)) stack
          caller_incoming caller_snapshots final_snapshots caller_policies h' /\
        executing_authority_old_colors_reflected CT h
          (mk_watched_frame caller_authority caller_senv rGamma)
          caller_incoming h'
          (mk_watched_frame caller_authority caller_final_senv
            (update_r_env_value rGamma destination (Iot return_location)))
          caller_incoming.

(** Result-independent completion for calls whose destination does not add
    an RDM root.  The two callbacks deliberately isolate the only
    call-specific facts: every post-call RDM root is an old caller root, and
    every independently owned post-call capability is already powered in the
    completed callee. *)
Lemma nonnull_post_frozen_path_preserves_completed_color :
  forall CT caller_senv caller_renv caller_h final_h callee callee_incoming
    caller_incoming caller_post source target,
    wf_r_config CT caller_senv caller_renv caller_h ->
    callee_incoming = executing_authority_color_set CT caller_h
      (mk_watched_frame caller_post.(frame_authority) caller_senv caller_renv)
      caller_incoming ->
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
            (mk_watched_frame caller_post.(frame_authority) caller_senv
              caller_renv) caller_incoming) (caller_mode, location)) ->
    (forall root,
      typed_root RDM caller_post.(frame_senv) caller_post.(frame_renv) root ->
      typed_root RDM caller_senv caller_renv root) ->
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
  intros CT caller_senv caller_renv caller_h final_h callee callee_incoming
    caller_incoming caller_post source target Hwf Hincoming Hreflect
    Hroot_old Hsource_mode Hsource Hpath.
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
    + have Hleft_old : typed_root RDM caller_senv caller_renv left_location.
      { eapply Hroot_old; eauto. }
      have Hright_old : typed_root RDM caller_senv caller_renv right_location.
      { eapply Hroot_old; eauto. }
      destruct Hleft_old as
        [variable [T [Htype [Hvalue Hrdm]]]].
      have Hleft_dom := wf_config_value_dom CT caller_senv caller_renv
        caller_h variable left_location Hwf Hvalue.
      destruct (Hreflect FlowPowered left_location (or_introl eq_refl)
        Hsource Hleft_dom) as [caller_mode [Hcaller_mode Hcaller_color]].
      have Hcaller_target := executing_authority_dangerous_frame_join CT
        caller_h
        (mk_watched_frame caller_post.(frame_authority) caller_senv
          caller_renv) caller_incoming caller_mode left_location
        right_location Hcaller_mode Hcaller_color
        (ex_intro _ variable (ex_intro _ T
          (conj Htype (conj Hvalue Hrdm)))) Hright_old.
      split; [right; reflexivity|].
      apply executing_authority_color_set_contains_incoming.
      exact Hcaller_target.
    + have Hleft_old : typed_root RDM caller_senv caller_renv left_location.
      { eapply Hroot_old; eauto. }
      have Hright_old : typed_root RDM caller_senv caller_renv right_location.
      { eapply Hroot_old; eauto. }
      destruct Hleft_old as
        [variable [T [Htype [Hvalue Hrdm]]]].
      have Hleft_dom := wf_config_value_dom CT caller_senv caller_renv
        caller_h variable left_location Hwf Hvalue.
      destruct (Hreflect FlowProspective left_location (or_intror eq_refl)
        Hsource Hleft_dom) as [caller_mode [Hcaller_mode Hcaller_color]].
      have Hcaller_target := executing_authority_dangerous_frame_join CT
        caller_h
        (mk_watched_frame caller_post.(frame_authority) caller_senv
          caller_renv) caller_incoming caller_mode left_location
        right_location Hcaller_mode Hcaller_color
        (ex_intro _ variable (ex_intro _ T
          (conj Htype (conj Hvalue Hrdm)))) Hright_old.
      split; [right; reflexivity|].
      apply executing_authority_color_set_contains_incoming.
      exact Hcaller_target.
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

Lemma nonnull_post_dangerous_color_is_completed_callee_color :
  forall CT caller_senv caller_renv caller_h final_h callee callee_incoming
    caller_incoming caller_post mode location,
    wf_r_config CT caller_senv caller_renv caller_h ->
    callee_incoming = executing_authority_color_set CT caller_h
      (mk_watched_frame caller_post.(frame_authority) caller_senv caller_renv)
      caller_incoming ->
    (forall source_mode source,
      authority_mode_dangerous source_mode ->
      In authority_flow_state
        (executing_authority_color_set CT final_h callee callee_incoming)
        (source_mode, source) ->
      source < dom caller_h ->
      exists caller_mode,
        authority_mode_dangerous caller_mode /\
        In authority_flow_state
          (executing_authority_color_set CT caller_h
            (mk_watched_frame caller_post.(frame_authority) caller_senv
              caller_renv) caller_incoming) (caller_mode, source)) ->
    (forall root,
      typed_root RDM caller_post.(frame_senv) caller_post.(frame_renv) root ->
      typed_root RDM caller_senv caller_renv root) ->
    (forall anchor,
      frame_owned_location CT final_h caller_post anchor ->
      In authority_flow_state
        (executing_authority_color_set CT final_h callee callee_incoming)
        (FlowPowered, anchor)) ->
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
  intros CT caller_senv caller_renv caller_h final_h callee callee_incoming
    caller_incoming caller_post mode location Hwf Hentry Hreflect Hroot_old
    Howned Hmode [seed [Hseed Hpath]].
  destruct (phased_dangerous_path_has_frozen_origin_or_owned_promotion CT
    final_h caller_post seed (mode, location) Hmode Hpath) as
    [[Hseed_mode Hfrozen] | [anchor [Hanchor_owned Hfrozen]]].
  - have Hseed_color : In authority_flow_state
      (executing_authority_color_set CT final_h callee callee_incoming) seed.
    { inversion Hseed as [state Hin | state Hpowered]; subst seed.
      - apply executing_authority_color_set_contains_incoming.
        rewrite Hentry.
        apply executing_authority_color_set_contains_incoming. exact Hin.
      - destruct Hpowered as [anchor [Heq Hanchor]]. inversion Heq; subst.
        eapply Howned. exact Hanchor. }
    destruct (nonnull_post_frozen_path_preserves_completed_color CT
      caller_senv caller_renv caller_h final_h callee callee_incoming
      caller_incoming caller_post seed (mode, location) Hwf Hentry Hreflect
      Hroot_old Hseed_mode Hseed_color Hfrozen) as [_ Htarget].
    exists mode. split; assumption.
  - have Hanchor_color := Howned anchor Hanchor_owned.
    destruct (nonnull_post_frozen_path_preserves_completed_color CT
      caller_senv caller_renv caller_h final_h callee callee_incoming
      caller_incoming caller_post (FlowPowered, anchor) (mode, location) Hwf
      Hentry Hreflect Hroot_old (or_introl eq_refl) Hanchor_color Hfrozen)
      as [_ Htarget].
    exists mode. split; assumption.
Qed.

Lemma non_rdm_destination_post_rdm_root_is_old :
  forall CT caller_senv caller_renv caller_h destination
    destination_type return_location root,
    wf_r_config CT caller_senv caller_renv caller_h ->
    static_getType caller_senv destination = Some destination_type ->
    sqtype destination_type <> RDM ->
    typed_root RDM caller_senv
      (update_r_env_value caller_renv destination (Iot return_location))
      root ->
    typed_root RDM caller_senv caller_renv root.
Proof.
  intros CT caller_senv caller_renv caller_h destination
    destination_type return_location root Hwf Hdestination Hnot_rdm Hroot.
  destruct (caller_post_rdm_root_origin CT caller_senv caller_renv caller_h
    destination destination_type return_location root Hwf Hdestination Hroot)
    as [Hold | [_ Hrdm]].
  - exact Hold.
  - contradiction.
Qed.

Lemma non_rdm_nonnull_call_old_colors_reflected :
  forall CT caller_authority caller_senv caller_renv caller_h final_h
    destination destination_type return_location callee callee_incoming
    caller_incoming,
    let caller := mk_watched_frame caller_authority caller_senv caller_renv in
    let caller_post := mk_watched_frame caller_authority caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) in
    wf_r_config CT caller_senv caller_renv caller_h ->
    static_getType caller_senv destination = Some destination_type ->
    sqtype destination_type <> RDM ->
    callee_incoming = executing_authority_color_set CT caller_h caller
      caller_incoming ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT final_h callee callee_incoming)
        (mode, location) ->
      location < dom caller_h ->
      exists caller_mode,
        authority_mode_dangerous caller_mode /\
        In authority_flow_state
          (executing_authority_color_set CT caller_h caller caller_incoming)
          (caller_mode, location)) ->
    (forall anchor,
      frame_owned_location CT final_h caller_post anchor ->
      In authority_flow_state
        (executing_authority_color_set CT final_h callee callee_incoming)
        (FlowPowered, anchor)) ->
    executing_authority_old_colors_reflected CT caller_h caller
      caller_incoming final_h caller_post caller_incoming.
Proof.
  intros CT caller_authority caller_senv caller_renv caller_h final_h
    destination destination_type return_location callee callee_incoming
    caller_incoming caller caller_post Hwf Hdestination Hnot_rdm Hincoming
    Hbody Howned.
  eapply completed_callee_classifier_implies_call_old_colors_reflected with
    (callee := callee) (callee_incoming := callee_incoming).
  - intros mode location Hmode Hcolor.
    eapply nonnull_post_dangerous_color_is_completed_callee_color with
      (caller_senv := caller_senv) (caller_renv := caller_renv)
      (caller_h := caller_h) (caller_post := caller_post).
    + exact Hwf.
    + exact Hincoming.
    + exact Hbody.
    + intros root Hroot.
      unfold caller_post in Hroot.
      exact (non_rdm_destination_post_rdm_root_is_old CT caller_senv
        caller_renv caller_h destination destination_type return_location root
        Hwf Hdestination Hnot_rdm Hroot).
    + exact Howned.
    + exact Hmode.
    + exact Hcolor.
  - exact Hbody.
Qed.

(** Complete non-null call reconstruction when the destination is not RDM.
    Capability-bearing destinations use the completed-callee return root;
    all other destinations preserve both capability and RDM roots exactly. *)
Lemma private_advancing_policy_successful_non_rdm_call_case :
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
    sqtype destination_type <> RDM ->
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
    Hdestination_non_rdm.
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
    (Some (private_nested_target_call_head CT h caller callee callee_incoming
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
    eapply (private_advancing_policy_statement_enter_untracked_safe_call
      CT P Z cutoff caller_authority caller_senv caller_scope rGamma h stack
      caller_incoming caller_snapshots caller_policies destination method
      receiver args caller_senv vals receiver_location runtime_class
      runtime_mdef receiver_type boundary); eauto. }
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
  destruct (frozen_target_snapshot_list_metadata_le_head_some
    body_policies.(suspended_frame_target_witnesses)
    (private_nested_target_call_head CT h caller callee callee_incoming
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
    - eapply frozen_target_snapshot_list_metadata_le_trans.
      + apply frozen_caller_snapshot_list_metadata_eq_target_le.
        apply advance_frozen_caller_snapshots_metadata_eq.
      + eapply frozen_target_snapshot_list_metadata_le_trans.
        * exact Hbody_target_witness_tail_metadata.
        * apply frozen_caller_snapshot_list_metadata_eq_target_le.
          apply advance_frozen_caller_snapshots_metadata_eq.
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
  { intros snapshot mode source Hsnapshot.
    exfalso.
    eapply private_resume_witnesses_cover_snapshots_none with
      (witnesses := body_witness_tail) (snapshots := body_tail)
      (snapshot := snapshot).
    - have Hcover := Hbody_cover.
      rewrite Hbody_witnesses in Hcover. simpl in Hcover.
      exact (proj2 Hcover).
    - exact Hsnapshot. }
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
      + exact Hdestination_non_rdm.
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
          Hdestination_non_rdm Hdestination_noncapability) as
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
  admit.
Admitted.
