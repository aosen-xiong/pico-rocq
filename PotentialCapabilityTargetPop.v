Require Import Syntax Notations Helpers Typing Subtyping Bigstep.
Require Import ViewpointAdaptation Properties Preservation ReadonlyHelper.
Require Import Reachability MutableCapability ComponentColoring.
Require Import ExecutionConfinement ProtectionHistory ForwardCapabilityHistory.
Require Import AuthorityCapability AuthorityHistory WatchedFrames
  LiveCapabilityStack.
Require Export PotentialCapabilityPolicyPop.

From Stdlib Require Import List Sets.Ensembles Relations.Relation_Operators.
Import ListNotations.

(** Target witnesses intentionally carry less state than ordinary frozen
    snapshots.  Their structural package nevertheless contains exactly the
    runtime and closure facts needed to classify colors introduced when an
    older target is reclosed under a resumed caller. *)
Lemma target_advanced_color_class_after_return :
  forall CT h callee targets caller old_snapshot mode location,
    private_target_witness_stack_structural CT h callee targets ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    List.In (Some old_snapshot) targets ->
    In authority_flow_state
      (advance_frozen_caller_snapshot CT h caller old_snapshot).(
        frozen_snapshot_current_colors) (mode, location) ->
    pop_resume_exposure_state_class CT h caller
      old_snapshot.(frozen_snapshot_current_colors) (mode, location).
Proof.
  intros CT h callee targets caller old_snapshot mode location
    (_ & Hruntime & _ & Hclosed & _ & _ & _ & _) Hcaller_wf Hcaller_sound
    Holder [source [Hsource Hpath]].
  eapply pop_resume_exposure_state_class_connected with
    (active := callee) (source := source).
  - exact Hcaller_wf.
  - exact Hcaller_sound.
  - eapply Hruntime. exact Holder.
  - eapply Hclosed. exact Holder.
  - left. exact Hsource.
  - exact Hpath.
Qed.

Lemma target_advanced_exposure_class_after_return :
  forall CT h callee targets caller old_snapshot mode location,
    private_target_witness_stack_structural CT h callee targets ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    List.In (Some old_snapshot) targets ->
    In authority_flow_state
      (advance_frozen_caller_snapshot CT h caller old_snapshot).(
        frozen_snapshot_current_resume_exposure) (mode, location) ->
    pop_resume_exposure_state_class CT h caller
      old_snapshot.(frozen_snapshot_current_resume_exposure) (mode, location).
Proof.
  intros CT h callee targets caller old_snapshot mode location
    (_ & _ & _ & _ & _ & Hexposure & _ & _) Hcaller_wf Hcaller_sound
    Holder [source [Hsource Hpath]].
  eapply pop_resume_exposure_state_class_connected with
    (active := callee) (source := source).
  - exact Hcaller_wf.
  - exact Hcaller_sound.
  - eapply (proj1 Hexposure). exact Holder.
  - eapply (proj1 (proj2 Hexposure)). exact Holder.
  - left. exact Hsource.
  - exact Hpath.
Qed.

Lemma target_advanced_exposure_reflected_or_outside :
  forall CT h Z callee targets caller old_snapshot,
    private_target_witness_stack_structural CT h callee targets ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    List.In (Some old_snapshot) targets ->
    (forall location,
      prospective_location_covered_by_frame CT h caller location ->
      ~ In Loc Z location) ->
    policy_pop_exposure_reflected_or_outside CT h Z caller old_snapshot.
Proof.
  intros CT h Z callee targets caller old_snapshot Htargets Hwf Hsound
    Holder Hprospective mode location Hmode Hcolor Hprotected.
  have Hclass := target_advanced_exposure_class_after_return CT h callee
    targets caller old_snapshot mode location Htargets Hwf Hsound Holder Hcolor.
  destruct Hclass as [Hold | [_ Hcovered]].
  - left. exists mode. split; assumption.
  - right. exact (Hprospective location Hcovered).
Qed.

Lemma target_advanced_color_reflected_or_outside :
  forall CT h Z callee targets caller old_snapshot mode location,
    private_target_witness_stack_structural CT h callee targets ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    List.In (Some old_snapshot) targets ->
    (forall target,
      prospective_location_covered_by_frame CT h caller target ->
      ~ In Loc Z target) ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (advance_frozen_caller_snapshot CT h caller old_snapshot).(
        frozen_snapshot_current_colors) (mode, location) ->
    (exists old_mode,
      authority_mode_dangerous old_mode /\
      In authority_flow_state old_snapshot.(frozen_snapshot_current_colors)
        (old_mode, location)) \/
    ~ In Loc Z location.
Proof.
  intros CT h Z callee targets caller old_snapshot mode location Htargets Hwf
    Hsound Holder Hprospective Hmode Hcolor.
  have Hclass := target_advanced_color_class_after_return CT h callee targets
    caller old_snapshot mode location Htargets Hwf Hsound Holder Hcolor.
  destruct Hclass as [Hold | [_ Hcovered]].
  - left. exists mode. split; assumption.
  - right. exact (Hprospective location Hcovered).
Qed.

(** Private provenance used only while rebuilding an untracked caller.  A
    caller-side color either remains represented by the completed callee, or
    it belongs to the saved target's latent resume exposure and that whole
    exposure is harmless for the protected zone. *)
Definition target_phase_pop_color_class
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (active : watched_frame) (incoming : Ensemble authority_flow_state)
  (snapshot : frozen_caller_color_snapshot)
  (state : authority_flow_state) : Prop :=
  In authority_flow_state
    (executing_authority_color_set CT h active incoming) state \/
  (In authority_flow_state snapshot.(frozen_snapshot_current_resume_exposure)
      state /\
   frozen_snapshot_resume_exposure_avoids Z snapshot).

Lemma target_phase_pop_nonjoin_preserves_class :
  forall CT h Z active incoming snapshot source target,
    Included authority_flow_state
      (frozen_caller_authority_closure CT h active
        snapshot.(frozen_snapshot_current_resume_exposure))
      snapshot.(frozen_snapshot_current_resume_exposure) ->
    target_phase_pop_color_class CT h Z active incoming snapshot source ->
    frozen_caller_authority_nonjoin_step CT h source target ->
    target_phase_pop_color_class CT h Z active incoming snapshot target.
Proof.
  intros CT h Z active incoming snapshot source target Hclosed Hclass Hstep.
  destruct Hclass as [Hcompleted | [Hexposure Hsafe]].
  - left. destruct Hcompleted as [seed [Hseed Hpath]].
    exists seed. split; [exact Hseed|].
    eapply rt_trans; [exact Hpath|]. apply rt_step.
    eapply frozen_nonjoin_step_is_phased. exact Hstep.
  - right. split; [|exact Hsafe]. eapply Hclosed.
    exists source. split; [exact Hexposure|]. apply rt_step.
    eapply frozen_nonjoin_step_in_frame. exact Hstep.
Qed.

Lemma target_phase_pop_join_preserves_class :
  forall CT h Z active incoming snapshot caller mode left right,
    (forall source_mode source,
      authority_mode_dangerous source_mode ->
      In authority_flow_state
        (executing_authority_color_set CT h active incoming)
        (source_mode, source) ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
      (exists phase_mode,
        authority_mode_dangerous phase_mode /\
        In authority_flow_state snapshot.(frozen_snapshot_phase_incoming)
          (phase_mode, source)) \/
      frozen_snapshot_resume_exposure_avoids Z snapshot) ->
    (forall root,
      typed_root RDM caller.(frame_senv) caller.(frame_renv) root ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) root) ->
    (forall phase_mode,
      authority_mode_dangerous phase_mode ->
      In authority_flow_state snapshot.(frozen_snapshot_phase_incoming)
        (phase_mode, left) ->
      In authority_flow_state
        (executing_authority_color_set CT h active incoming)
        (FlowProspective, right)) ->
    (typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
      In authority_flow_state
        snapshot.(frozen_snapshot_current_resume_exposure)
        (FlowProspective, right)) ->
    authority_mode_dangerous mode ->
    target_phase_pop_color_class CT h Z active incoming snapshot (mode, left) ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    target_phase_pop_color_class CT h Z active incoming snapshot
      (FlowProspective, right).
Proof.
  intros CT h Z active incoming snapshot caller mode left right Hphase_safe
    Hroot Hphase_join Hexposure_join Hmode Hclass Hleft Hright.
  destruct Hclass as [Hcompleted | [Hexposure Hsafe]].
  - destruct (Hphase_safe mode left Hmode Hcompleted (Hroot left Hleft)) as
      [[phase_mode [Hphase_mode Hphase]] | Hsafe].
    + left. eapply Hphase_join; eauto.
    + right. split; [eapply Hexposure_join; eauto|exact Hsafe].
  - right. split; [eapply Hexposure_join; eauto|exact Hsafe].
Qed.

Lemma target_phase_pop_step_preserves_class_given_joins :
  forall CT h Z active incoming snapshot caller source target,
    Included authority_flow_state
      (frozen_caller_authority_closure CT h active
        snapshot.(frozen_snapshot_current_resume_exposure))
      snapshot.(frozen_snapshot_current_resume_exposure) ->
    (forall mode left right,
      authority_mode_dangerous mode ->
      target_phase_pop_color_class CT h Z active incoming snapshot
        (mode, left) ->
      typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
      typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
      target_phase_pop_color_class CT h Z active incoming snapshot
        (FlowProspective, right)) ->
    authority_mode_dangerous (fst source) ->
    target_phase_pop_color_class CT h Z active incoming snapshot source ->
    frozen_caller_authority_step CT h caller source target ->
    target_phase_pop_color_class CT h Z active incoming snapshot target.
Proof.
  intros CT h Z active incoming snapshot caller source target Hclosed Hjoin
    Hsource_mode Hsource Hstep.
  inversion Hstep; subst; simpl in *.
  - eapply target_phase_pop_nonjoin_preserves_class; eauto.
    apply frozen_nonjoin_retained. exact H.
  - eapply target_phase_pop_nonjoin_preserves_class; eauto.
    apply frozen_nonjoin_prospective_retained. exact H.
  - eapply target_phase_pop_nonjoin_preserves_class; eauto.
    apply frozen_nonjoin_prospective_rdm_backward. exact H.
  - eapply target_phase_pop_nonjoin_preserves_class; eauto.
    apply frozen_nonjoin_reverse_rdm. exact H.
  - eapply Hjoin; eauto.
  - eapply Hjoin; eauto.
  - eapply target_phase_pop_nonjoin_preserves_class; eauto.
    apply frozen_nonjoin_mark_prospective.
Qed.

Lemma target_phase_pop_connected_preserves_class_given_joins :
  forall CT h Z active incoming snapshot caller source target,
    Included authority_flow_state
      (frozen_caller_authority_closure CT h active
        snapshot.(frozen_snapshot_current_resume_exposure))
      snapshot.(frozen_snapshot_current_resume_exposure) ->
    (forall mode left right,
      authority_mode_dangerous mode ->
      target_phase_pop_color_class CT h Z active incoming snapshot
        (mode, left) ->
      typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
      typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
      target_phase_pop_color_class CT h Z active incoming snapshot
        (FlowProspective, right)) ->
    authority_mode_dangerous (fst source) ->
    target_phase_pop_color_class CT h Z active incoming snapshot source ->
    frozen_caller_authority_connected CT h caller source target ->
    target_phase_pop_color_class CT h Z active incoming snapshot target.
Proof.
  intros CT h Z active incoming snapshot caller source target Hclosed Hjoin
    Hsource_mode Hsource Hconnected.
  induction Hconnected.
  - eapply target_phase_pop_step_preserves_class_given_joins; eauto.
  - exact Hsource.
  - have Hmiddle_mode : authority_mode_dangerous (fst y).
    { eapply frozen_caller_authority_connected_preserves_dangerous; eauto. }
    have Hmiddle := IHHconnected1 Hsource_mode Hsource.
    exact (IHHconnected2 Hmiddle_mode Hmiddle).
Qed.

Lemma target_phase_pop_class_is_completed_or_outside :
  forall CT h Z active incoming snapshot mode location,
    authority_mode_dangerous mode ->
    target_phase_pop_color_class CT h Z active incoming snapshot
      (mode, location) ->
    (exists completed_mode,
      authority_mode_dangerous completed_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h active incoming)
        (completed_mode, location)) \/
    ~ In Loc Z location.
Proof.
  intros CT h Z active incoming snapshot mode location Hmode Hclass.
  destruct Hclass as [Hcompleted | [Hexposure Hsafe]].
  - left. exists mode. split; assumption.
  - right. eapply Hsafe; eauto.
Qed.

(** Eliminate the saved-head class at a root owned by an older target.  The
    second-order phase certificate is what makes the harmless head-exposure
    alternative compositional across consecutive untracked boundaries. *)
Lemma target_phase_pop_head_class_at_older_root :
  forall CT h Z active incoming head target_tail resume_head resume_tail older
    mode source,
    private_target_exposures_support_resume_phase Z
      (Some head :: target_tail) (resume_head :: resume_tail) ->
    List.In (Some older) resume_tail ->
    authority_mode_dangerous mode ->
    In Loc older.(frozen_snapshot_resume_rdm_roots) source ->
    target_phase_pop_color_class CT h Z active incoming head (mode, source) ->
    (exists completed_mode,
      authority_mode_dangerous completed_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h active incoming)
        (completed_mode, source)) \/
    (exists phase_mode,
      authority_mode_dangerous phase_mode /\
      In authority_flow_state older.(frozen_snapshot_phase_incoming)
        (phase_mode, source)) \/
    frozen_snapshot_resume_exposure_avoids Z older.
Proof.
  intros CT h Z active incoming head target_tail resume_head resume_tail older
    mode source Hnested Holder Hmode Hroot
    [Hcompleted | [Hexposure _]].
  - left. exists mode. split; assumption.
  - right. eapply private_target_exposures_support_resume_phase_head; eauto.
Qed.

(** The un-erased form of the caller-pop classifier.  Keeping the saved
    target in the conclusion is essential when rebuilding an older retained
    witness: the harmless alternative certifies the whole resume exposure,
    rather than merely the one color being classified. *)
Lemma target_phase_pop_executing_color_has_class :
  forall CT h Z active active_incoming snapshot caller caller_incoming
    mode location,
    Included authority_flow_state caller_incoming
      (executing_authority_color_set CT h active active_incoming) ->
    (forall owned,
      frame_owned_location CT h caller owned ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, owned)) ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h active
        snapshot.(frozen_snapshot_current_resume_exposure))
      snapshot.(frozen_snapshot_current_resume_exposure) ->
    (forall source_mode left right,
      authority_mode_dangerous source_mode ->
      target_phase_pop_color_class CT h Z active active_incoming snapshot
        (source_mode, left) ->
      typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
      typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
      target_phase_pop_color_class CT h Z active active_incoming snapshot
        (FlowProspective, right)) ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT h caller caller_incoming)
      (mode, location) ->
    target_phase_pop_color_class CT h Z active active_incoming snapshot
      (mode, location).
Proof.
  intros CT h Z active active_incoming snapshot caller caller_incoming mode
    location Hincoming Howned Hclosed Hjoin Hmode [seed [Hseed Hpath]].
  destruct (phased_dangerous_path_has_frozen_origin_or_owned_promotion CT h
    caller seed (mode, location) Hmode Hpath) as
    [[Hseed_mode Hfrozen] | [anchor [Hanchor_owned Hfrozen]]].
  - have Hseed_class : target_phase_pop_color_class CT h Z active
        active_incoming snapshot seed.
    { left. destruct Hseed as
        [seed_state Hincoming_seed | seed_state Howned_seed].
      - exact (Hincoming seed_state Hincoming_seed).
      - destruct Howned_seed as [owned [Heq Howned_seed]].
        inversion Heq; subst. eapply Howned; eauto. }
    eapply target_phase_pop_connected_preserves_class_given_joins; eauto.
  - have Hanchor_class : target_phase_pop_color_class CT h Z active
        active_incoming snapshot (FlowPowered, anchor).
    { left. eapply Howned. exact Hanchor_owned. }
    eapply target_phase_pop_connected_preserves_class_given_joins; eauto.
    exact (or_introl eq_refl).
Qed.

Lemma target_phase_pop_executing_color_is_completed_or_outside :
  forall CT h Z active active_incoming snapshot caller caller_incoming
    mode location,
    Included authority_flow_state caller_incoming
      (executing_authority_color_set CT h active active_incoming) ->
    (forall owned,
      frame_owned_location CT h caller owned ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, owned)) ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h active
        snapshot.(frozen_snapshot_current_resume_exposure))
      snapshot.(frozen_snapshot_current_resume_exposure) ->
    (forall source_mode left right,
      authority_mode_dangerous source_mode ->
      target_phase_pop_color_class CT h Z active active_incoming snapshot
        (source_mode, left) ->
      typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
      typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
      target_phase_pop_color_class CT h Z active active_incoming snapshot
        (FlowProspective, right)) ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT h caller caller_incoming)
      (mode, location) ->
    (exists completed_mode,
      authority_mode_dangerous completed_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (completed_mode, location)) \/
    ~ In Loc Z location.
Proof.
  intros CT h Z active active_incoming snapshot caller caller_incoming mode
    location Hincoming Howned Hclosed Hjoin Hmode Hcolor.
  have Hclass := target_phase_pop_executing_color_has_class CT h Z active
    active_incoming snapshot caller caller_incoming mode location Hincoming
    Howned Hclosed Hjoin Hmode Hcolor.
  exact (target_phase_pop_class_is_completed_or_outside CT h Z active
    active_incoming snapshot mode location Hmode Hclass).
Qed.
