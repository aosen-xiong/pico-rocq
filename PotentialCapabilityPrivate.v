Require Import Syntax Notations Helpers Typing Subtyping Bigstep.
Require Import ViewpointAdaptation Properties Preservation ReadonlyHelper.
Require Import Reachability MutableCapability ComponentColoring.
Require Import ExecutionConfinement ProtectionHistory ForwardCapabilityHistory.
Require Import AuthorityCapability AuthorityHistory WatchedFrames
  LiveCapabilityStack.
Require Export PotentialCapabilityAtomic.
From Stdlib Require Import List Sets.Ensembles Relations.Relation_Operators
  Program.Equality.
Import ListNotations.

(** Result package for the strengthened, proof-internal statement induction.
    The first conjunct is the phase-aware authority history maintained by the
    flexible-call semantics.  It deliberately does not assert separation in
    the unrestricted potential graph: allocation through a read-only alias
    may create a benign fresh potential overlap without transferring mutation
    authority.  The remaining conjuncts are ghost state: [final_snapshots]
    may evolve while a statement executes, but its immutable call-entry
    metadata continues to correspond pointwise to [initial_snapshots], and
    every protected latent exposure reflects to the corresponding entry
    image. *)
Definition private_statement_preservation_result
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (authority : q_r) (final_senv : s_env) (final_renv : r_env)
  (stack : list watched_boundary) (incoming : Ensemble authority_flow_state)
  (initial_snapshots final_snapshots : list frozen_caller_snapshot_slot)
  (final_h : heap) : Prop :=
  principled_phased_authority_live_history_state CT P Z cutoff
    (mk_watched_frame authority final_senv final_renv) stack incoming
    final_h /\
  private_fresh_frozen_statement_state CT P Z cutoff
    (mk_watched_frame authority final_senv final_renv) stack incoming
    final_snapshots final_h /\
  frozen_caller_snapshot_list_metadata_eq final_snapshots initial_snapshots /\
  frozen_snapshot_list_resume_exposure_protected_reflected Z final_snapshots
    initial_snapshots.

Lemma private_statement_preservation_result_refl :
  forall CT P Z cutoff authority sGamma rGamma stack incoming snapshots h,
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming h ->
    private_fresh_frozen_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots h ->
    private_statement_preservation_result CT P Z cutoff authority sGamma
      rGamma stack incoming snapshots snapshots h.
Proof.
  intros CT P Z cutoff authority sGamma rGamma stack incoming snapshots h
    Hmain Hprivate.
  unfold private_statement_preservation_result. split.
  - exact (proj1 (proj1 (proj1 Hprivate))).
  - split; [exact Hprivate|].
    split.
    + clear Hprivate.
      induction snapshots as [|slot tail IH].
      * constructor.
      * constructor.
        -- destruct slot; simpl.
           ++ unfold frozen_caller_snapshot_metadata_eq. repeat split;
                intros state Hstate; exact Hstate.
           ++ exact I.
        -- exact IH.
    + apply frozen_snapshot_list_resume_exposure_protected_reflected_refl.
Qed.

Lemma caller_post_capability_root_origin_private :
  forall caller_authority caller_senv caller_renv destination
    destination_type return_location root,
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    frame_capability_root
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination
          (Iot return_location))) root ->
    frame_capability_root
      (mk_watched_frame caller_authority caller_senv caller_renv) root \/
    root = return_location.
Proof.
  intros caller_authority caller_senv caller_renv destination
    destination_type return_location root Hdestination_nonzero Hdestination
    Hlength [variable [T [Htype [Hvalue Hcapability]]]].
  destruct (Nat.eq_dec variable destination) as [Heq | Hneq].
  - subst variable. have Hdestination_dom := Hdestination.
    apply static_getType_dom in Hdestination_dom. rewrite Hlength in Hdestination_dom.
    rewrite (runtime_getVal_update_same caller_renv destination
      (Iot return_location) Hdestination_dom) in Hvalue.
    injection Hvalue as <-. right. reflexivity.
  - left. exists variable, T. split; [exact Htype|]. split.
    + have Hold_value := runtime_getVal_update_diff caller_renv destination
        variable (Iot return_location) (ltac:(congruence)).
      rewrite Hvalue in Hold_value. symmetry. exact Hold_value.
    + exact Hcapability.
Qed.

Lemma caller_post_rdm_root_origin_private :
  forall caller_senv caller_renv destination destination_type return_location
    root,
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    typed_root RDM caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) root ->
    typed_root RDM caller_senv caller_renv root \/
    (root = return_location /\ sqtype destination_type = RDM).
Proof.
  intros caller_senv caller_renv destination destination_type return_location
    root Hdestination_nonzero Hdestination Hlength
    [variable [T [Htype [Hvalue Hrdm]]]].
  destruct (Nat.eq_dec variable destination) as [Heq | Hneq].
  - subst variable. have Hdestination_dom := Hdestination.
    apply static_getType_dom in Hdestination_dom. rewrite Hlength in Hdestination_dom.
    rewrite (runtime_getVal_update_same caller_renv destination
      (Iot return_location) Hdestination_dom) in Hvalue.
    injection Hvalue as <-. right. split; [reflexivity|]. congruence.
  - left. exists variable, T. split; [exact Htype|]. split.
    + have Hold_value := runtime_getVal_update_diff caller_renv destination
        variable (Iot return_location) (ltac:(congruence)).
      rewrite Hvalue in Hold_value. symmetry. exact Hold_value.
    + exact Hrdm.
Qed.

Definition return_pop_location_covered
  (CT : class_table) (h : heap) (caller callee : watched_frame)
  (location : Loc) : Prop :=
  prospective_location_covered_by_frame CT h caller location \/
  prospective_location_covered_by_frame CT h callee location.

Lemma return_pop_prospective_step_covered :
  forall CT h caller callee caller_authority caller_senv caller_renv
    destination destination_type return_location source target,
    caller = mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    r_muttype h target = Some Mut_r ->
    prospective_location_covered_by_frame CT h callee return_location ->
    return_pop_location_covered CT h caller callee source ->
    frozen_caller_authority_step CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      (FlowProspective, source) (FlowProspective, target) ->
    return_pop_location_covered CT h caller callee target.
Proof.
  intros CT h caller callee caller_authority caller_senv caller_renv
    destination destination_type return_location source target Hcaller
    Hdestination_nonzero Hdestination Hlength Htarget_runtime Hreturn Hsource
    Hstep.
  inversion Hstep; subst.
  - destruct Hsource as
      [[root [Hroot Hpath]] | [root [Hroot Hpath]]].
    + left. exists root. split; [exact Hroot|].
      eapply rt_trans; [exact Hpath|]. apply rt_step.
      apply frozen_caller_prospective_retained. exact H1.
    + right. exists root. split; [exact Hroot|].
      eapply rt_trans; [exact Hpath|]. apply rt_step.
      apply frozen_caller_prospective_retained. exact H1.
  - destruct Hsource as
      [[root [Hroot Hpath]] | [root [Hroot Hpath]]].
    + left. exists root. split; [exact Hroot|].
      eapply rt_trans; [exact Hpath|]. apply rt_step.
      apply frozen_caller_prospective_rdm_backward. exact H1.
    + right. exists root. split; [exact Hroot|].
      eapply rt_trans; [exact Hpath|]. apply rt_step.
      apply frozen_caller_prospective_rdm_backward. exact H1.
  - destruct (caller_post_rdm_root_origin_private caller_senv caller_renv
      destination destination_type return_location target
      Hdestination_nonzero Hdestination Hlength H2) as
      [Hold_root | [Hreturn_root Hdestination_rdm]].
    + left. exists target. split.
      * right. split.
        -- exact Hold_root.
        -- exact Htarget_runtime.
      * apply rt_refl.
    + subst target. right. exact Hreturn.
Qed.

Definition return_pop_prospective_state_covered
  (CT : class_table) (h : heap) (caller callee : watched_frame)
  (state : authority_flow_state) : Prop :=
  fst state = FlowProspective /\
  r_muttype h (snd state) = Some Mut_r /\
  return_pop_location_covered CT h caller callee (snd state).

Lemma return_pop_prospective_state_step_covered :
  forall CT h caller callee caller_authority caller_senv caller_renv
    destination destination_type return_location source target,
    caller = mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    prospective_location_covered_by_frame CT h callee return_location ->
    return_pop_prospective_state_covered CT h caller callee source ->
    frozen_caller_authority_step CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      source target ->
    return_pop_prospective_state_covered CT h caller callee target.
Proof.
  intros CT h caller callee caller_authority caller_senv caller_renv
    destination destination_type return_location [source_mode source]
    [target_mode target] Hcaller Hdestination_nonzero Hdestination Hlength
    Hpost_wf Hreturn [Hsource_mode [Hsource_runtime Hsource]] Hstep.
  simpl in *. subst source_mode.
  have Htarget_mode : target_mode = FlowProspective.
  { inversion Hstep; reflexivity. }
  subst target_mode.
  have Htarget_runtime := phased_authority_frame_step_preserves_runtime_mutability
    CT h
    (mk_watched_frame caller_authority caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)))
    (FlowProspective, source) (FlowProspective, target) Mut_r Hpost_wf
    (frozen_caller_authority_step_is_phased CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      (FlowProspective, source) (FlowProspective, target) Hstep)
    Hsource_runtime.
  split; [reflexivity|]. split; [exact Htarget_runtime|].
  eapply return_pop_prospective_step_covered; eauto.
Qed.

Lemma return_pop_prospective_state_connected_covered :
  forall CT h caller callee caller_authority caller_senv caller_renv
    destination destination_type return_location source target,
    caller = mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    prospective_location_covered_by_frame CT h callee return_location ->
    return_pop_prospective_state_covered CT h caller callee source ->
    frozen_caller_authority_connected CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      source target ->
    return_pop_prospective_state_covered CT h caller callee target.
Proof.
  intros CT h caller callee caller_authority caller_senv caller_renv
    destination destination_type return_location source target Hcaller
    Hdestination_nonzero Hdestination Hlength Hpost_wf Hreturn Hsource
    Hconnected.
  induction Hconnected.
  - eapply return_pop_prospective_state_step_covered; eauto.
  - exact Hsource.
  - apply IHHconnected2. apply IHHconnected1. exact Hsource.
Qed.

Lemma caller_post_mutable_authority_root_covered :
  forall CT caller_authority caller_senv caller_renv destination destination_type
    return_location h callee root,
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    r_muttype h root = Some Mut_r ->
    prospective_location_covered_by_frame CT h callee return_location ->
    mutable_authority_root
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      h root ->
    return_pop_location_covered CT h
      (mk_watched_frame caller_authority caller_senv caller_renv) callee root.
Proof.
  intros CT caller_authority caller_senv caller_renv destination destination_type
    return_location h callee root Hdestination_nonzero Hdestination Hlength
    Hroot_runtime Hreturn [Hmut | [Hrdm Hruntime]].
  - have Hcapability : frame_capability_root
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination (Iot return_location)))
        root.
    { destruct Hmut as [variable [T [Htype [Hvalue Hmut]]]].
      exists variable, T. repeat split; try assumption.
      unfold capability_in_context. left. exact Hmut. }
    destruct (caller_post_capability_root_origin_private caller_authority
      caller_senv caller_renv destination destination_type return_location
      root Hdestination_nonzero Hdestination Hlength Hcapability) as
      [Hold_root | Hreturn_root].
    + left. exists root. split; [|apply rt_refl].
      destruct Hold_root as
        [variable [T [Htype [Hvalue [Hold_mut | [Hold_rdm Hauthority]]]]]].
      * left. exists variable, T. repeat split; assumption.
      * right. split.
        -- exists variable, T. repeat split; assumption.
        -- exact Hroot_runtime.
    + subst root. right. exact Hreturn.
  - destruct (caller_post_rdm_root_origin_private caller_senv caller_renv
      destination destination_type return_location root
      Hdestination_nonzero Hdestination Hlength Hrdm) as
      [Hold_root | [Hreturn_root Hdestination_rdm]].
    + left. exists root. split.
      * right. split; assumption.
      * apply rt_refl.
    + subst root. right. exact Hreturn.
Qed.

Lemma live_prospective_mutable_authority_components_after_return_pop :
  forall CT h cutoff active boundary stack caller_authority caller_senv
    caller_renv destination destination_type return_location,
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT caller_senv caller_renv h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    authority_context_sound h
      (update_r_env_value caller_renv destination (Iot return_location))
      caller_authority ->
    static_getType caller_senv destination = Some destination_type ->
    prospective_location_covered_by_frame CT h active return_location ->
    live_prospective_mutable_authority_components_after_cutoff CT h cutoff
      active (boundary :: stack) ->
    live_prospective_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      stack.
Proof.
  intros CT h cutoff active boundary stack caller_authority caller_senv
    caller_renv destination destination_type return_location Hcaller
    Hdestination_nonzero Hcaller_wf Hpost_wf Hpost_sound Hdestination Hreturn
    Hold frame root target Hlive [Hroot Hpath].
  have Hlength : length caller_senv = length caller_renv.(vars) :=
    proj1 (proj2 (proj2 (proj2 (proj2 Hcaller_wf)))).
  inversion Hlive; subst.
  - have Hroot_runtime := mutable_authority_root_runtime_mutable CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      root Hpost_wf Hpost_sound Hroot.
    have Hroot_covered := caller_post_mutable_authority_root_covered
      CT caller_authority caller_senv caller_renv destination destination_type
      return_location h active root Hdestination_nonzero Hdestination Hlength
      Hroot_runtime Hreturn Hroot.
    have Hsource : return_pop_prospective_state_covered CT h
        (mk_watched_frame caller_authority caller_senv caller_renv) active
        (FlowProspective, root).
    { split; [reflexivity|]. split; [exact Hroot_runtime|exact Hroot_covered]. }
    have Htarget := return_pop_prospective_state_connected_covered CT h
      (mk_watched_frame caller_authority caller_senv caller_renv) active
      caller_authority caller_senv caller_renv destination destination_type
      return_location (FlowProspective, root) (FlowProspective, target)
      eq_refl Hdestination_nonzero Hdestination Hlength Hpost_wf Hreturn
      Hsource Hpath.
    destruct Htarget as [_ [_
      [[caller_root [Hcaller_root Hcaller_path]] |
       [callee_root [Hcallee_root Hcallee_path]]]]].
    + eapply Hold with (frame := boundary.(boundary_caller))
        (root := caller_root).
      * constructor. simpl. left. reflexivity.
      * rewrite Hcaller. split; assumption.
    + eapply Hold with (frame := active) (root := callee_root).
      * constructor.
      * split; assumption.
  - eapply Hold with (frame := boundary0.(boundary_caller)) (root := root).
    + constructor. simpl. right. exact H.
    + split; assumption.
Qed.

Lemma live_mutable_authority_components_after_return_pop :
  forall CT h cutoff active boundary stack caller_authority caller_senv
    caller_renv destination destination_type return_location,
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT caller_senv caller_renv h ->
    static_getType caller_senv destination = Some destination_type ->
    live_mutable_authority_components_after_cutoff CT h cutoff active
      (boundary :: stack) ->
    (forall target,
      retained_mut_reachable CT h return_location target ->
      cutoff <= target) ->
    live_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination
          (Iot return_location))) stack.
Proof.
  intros CT h cutoff active boundary stack caller_authority caller_senv
    caller_renv destination destination_type return_location Hcaller
    Hdestination_nonzero Hcaller_wf Hdestination Hlive Hreturn frame root
    target Hframe Hreachable.
  have Hlength : length caller_senv = length caller_renv.(vars) :=
    proj1 (proj2 (proj2 (proj2 (proj2 Hcaller_wf)))).
  inversion Hframe; subst.
  - inversion Hreachable; subst.
    + destruct (caller_post_capability_root_origin_private caller_authority
        caller_senv caller_renv destination destination_type return_location
        root Hdestination_nonzero Hdestination Hlength H) as
        [Hold_root | Hreturn_root].
      * eapply Hlive with (frame := boundary.(boundary_caller)) (root := root).
        -- constructor. simpl. left. reflexivity.
        -- apply mutable_authority_reachable_capability.
           ++ rewrite Hcaller. exact Hold_root.
           ++ exact H0.
           ++ exact H1.
      * subst root. eapply Hreturn. exact H1.
    + destruct (caller_post_rdm_root_origin_private caller_senv caller_renv
        destination destination_type return_location root
        Hdestination_nonzero Hdestination Hlength H) as
        [Hold_root | [Hreturn_root Hdestination_rdm]].
      * eapply Hlive with (frame := boundary.(boundary_caller)) (root := root).
        -- constructor. simpl. left. reflexivity.
        -- apply mutable_authority_reachable_rdm.
           ++ rewrite Hcaller. exact Hold_root.
           ++ exact H0.
           ++ exact H1.
      * subst root. eapply Hreturn. exact H1.
  - eapply Hlive with (frame := boundary0.(boundary_caller)) (root := root).
    + constructor. simpl. right. exact H.
    + exact Hreachable.
Qed.

Lemma frozen_callee_side_components_after_return_pop :
  forall CT h active boundary stack head_slot snapshots caller_authority
    caller_senv caller_renv destination destination_type return_location,
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    wf_r_config CT caller_senv caller_renv h ->
    static_getType caller_senv destination = Some destination_type ->
    frame_owned_location CT h active return_location ->
    r_muttype h return_location = Some Mut_r ->
    frozen_callee_side_mutable_components_after_boundaries CT h active
      (head_slot :: snapshots) (boundary :: stack) ->
    frozen_callee_side_mutable_components_after_boundaries CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination
          (Iot return_location)))
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination
            (Iot return_location))) snapshots) stack.
Proof.
  intros CT h active boundary stack head_slot snapshots caller_authority
    caller_senv caller_renv destination destination_type return_location
    Hcaller Hdestination_nonzero Hactive_wf Hcaller_wf Hdestination
    Hreturn_owned Hreturn_runtime Hold snapshot tracked_boundary above below
    Hpartition.
  set (caller_post := mk_watched_frame caller_authority caller_senv
    (update_r_env_value caller_renv destination (Iot return_location))).
  destruct (advance_frozen_snapshot_live_partition_reflects CT h caller_post
    snapshots stack snapshot tracked_boundary above below Hpartition) as
    [old_snapshot Hold_partition].
  have Hinput_partition : frozen_snapshot_live_partition
      (head_slot :: snapshots) (boundary :: stack) old_snapshot
      tracked_boundary (boundary :: above) below.
  { constructor. exact Hold_partition. }
  have Hinput_components := Hold old_snapshot tracked_boundary
    (boundary :: above) below Hinput_partition.
  have Hreturn_component : forall target,
      retained_mut_reachable CT h return_location target ->
      tracked_boundary.(boundary_entry_cutoff) <= target.
  { intros target Hreturn_target.
    destruct Hreturn_owned as [owner [Howner Howner_return]].
    have Howner_runtime : r_muttype h owner = Some Mut_r.
    { eapply retained_reachable_reflects_runtime_context_private;
        [exact (proj1 (proj2 Hactive_wf))|exact Howner_return|].
      exact Hreturn_runtime. }
    eapply Hinput_components with (frame := active) (root := owner).
    - constructor.
    - apply mutable_authority_reachable_capability.
      + exact Howner.
      + exact Howner_runtime.
      + eapply retained_mut_reachable_transitive; eauto. }
  unfold caller_post.
  eapply live_mutable_authority_components_after_return_pop; eauto.
Qed.

(** The prospective analogue of the return/pop transport.  The returned
    location is covered by the completed callee component because frame
    ownership supplies a capability root and a retained path to the result.
    All other post-return prospective paths are classified by
    [live_prospective_mutable_authority_components_after_return_pop]. *)
Lemma frozen_callee_side_prospective_components_after_return_pop :
  forall CT h active boundary stack head_slot snapshots caller_authority
    caller_senv caller_renv destination destination_type return_location,
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    authority_context_sound h active.(frame_renv) active.(frame_authority) ->
    wf_r_config CT caller_senv caller_renv h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    authority_context_sound h
      (update_r_env_value caller_renv destination (Iot return_location))
      caller_authority ->
    static_getType caller_senv destination = Some destination_type ->
    frame_owned_location CT h active return_location ->
    r_muttype h return_location = Some Mut_r ->
    frozen_callee_side_prospective_components_after_boundaries CT h active
      (head_slot :: snapshots) (boundary :: stack) ->
    frozen_callee_side_prospective_components_after_boundaries CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination
            (Iot return_location))) snapshots) stack.
Proof.
  intros CT h active boundary stack head_slot snapshots caller_authority
    caller_senv caller_renv destination destination_type return_location
    Hcaller Hdestination_nonzero Hactive_wf Hactive_sound Hcaller_wf
    Hcaller_post_wf Hcaller_post_sound Hdestination Hreturn_owned
    Hreturn_runtime Hold snapshot tracked_boundary above below Hpartition.
  set (caller_post := mk_watched_frame caller_authority caller_senv
    (update_r_env_value caller_renv destination (Iot return_location))).
  destruct (advance_frozen_snapshot_live_partition_reflects CT h caller_post
    snapshots stack snapshot tracked_boundary above below Hpartition) as
    [old_snapshot Hold_partition].
  have Hinput_partition : frozen_snapshot_live_partition
      (head_slot :: snapshots) (boundary :: stack) old_snapshot
      tracked_boundary (boundary :: above) below.
  { constructor. exact Hold_partition. }
  have Hinput_components := Hold old_snapshot tracked_boundary
    (boundary :: above) below Hinput_partition.
  have Hreturn_covered : prospective_location_covered_by_frame CT h active
      return_location.
  { destruct Hreturn_owned as [owner [Howner Howner_return]].
    have Howner_runtime : r_muttype h owner = Some Mut_r.
    { eapply retained_reachable_reflects_runtime_context_private;
        [exact (proj1 (proj2 Hactive_wf))|exact Howner_return|].
      exact Hreturn_runtime. }
    exists owner. split.
    - destruct Howner as
        [variable [T [Htype [Hvalue [Hmut | [Hrdm Hauthority]]]]]].
      + left. exists variable, T. repeat split; assumption.
      + right. split.
        * exists variable, T. repeat split; assumption.
        * exact Howner_runtime.
    - eapply frozen_caller_prospective_retained_forward.
      exact Howner_return. }
  unfold caller_post.
  eapply live_prospective_mutable_authority_components_after_return_pop;
    eauto.
Qed.

Lemma caller_null_post_capability_root_is_old :
  forall caller_authority caller_senv caller_renv destination
    destination_type root,
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    frame_capability_root
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination Null_a)) root ->
    frame_capability_root
      (mk_watched_frame caller_authority caller_senv caller_renv) root.
Proof.
  intros caller_authority caller_senv caller_renv destination
    destination_type root Hdestination_nonzero Hdestination Hlength
    [variable [T [Htype [Hvalue Hcapability]]]].
  destruct (Nat.eq_dec variable destination) as [Heq | Hneq].
  - subst variable. have Hdestination_dom := Hdestination.
    apply static_getType_dom in Hdestination_dom.
    rewrite Hlength in Hdestination_dom.
    rewrite (runtime_getVal_update_same caller_renv destination Null_a
      Hdestination_dom) in Hvalue. discriminate.
  - exists variable, T. split; [exact Htype|]. split.
    + have Hold_value := runtime_getVal_update_diff caller_renv destination
        variable Null_a (ltac:(congruence)).
      rewrite Hvalue in Hold_value. symmetry. exact Hold_value.
    + exact Hcapability.
Qed.

Lemma caller_null_post_rdm_root_is_old :
  forall caller_senv caller_renv destination destination_type root,
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    typed_root RDM caller_senv
      (update_r_env_value caller_renv destination Null_a) root ->
    typed_root RDM caller_senv caller_renv root.
Proof.
  intros caller_senv caller_renv destination destination_type root
    Hdestination_nonzero Hdestination Hlength
    [variable [T [Htype [Hvalue Hrdm]]]].
  destruct (Nat.eq_dec variable destination) as [Heq | Hneq].
  - subst variable. have Hdestination_dom := Hdestination.
    apply static_getType_dom in Hdestination_dom.
    rewrite Hlength in Hdestination_dom.
    rewrite (runtime_getVal_update_same caller_renv destination Null_a
      Hdestination_dom) in Hvalue. discriminate.
  - exists variable, T. split; [exact Htype|]. split.
    + have Hold_value := runtime_getVal_update_diff caller_renv destination
        variable Null_a (ltac:(congruence)).
      rewrite Hvalue in Hold_value. symmetry. exact Hold_value.
    + exact Hrdm.
Qed.

Lemma caller_null_post_rdm_roots_descend :
  forall CT h caller_senv caller_renv destination destination_type,
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    rdm_roots_descend_from CT h caller_senv caller_renv caller_senv
      (update_r_env_value caller_renv destination Null_a).
Proof.
  intros CT h caller_senv caller_renv destination destination_type
    Hdestination_nonzero Hdestination Hlength root Hroot.
  exists root. split.
  - eapply caller_null_post_rdm_root_is_old; eauto.
  - constructor.
Qed.

Lemma caller_null_post_owned_is_old :
  forall CT h caller_authority caller_senv caller_renv destination
    destination_type,
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination Null_a)))
      (phase_frame_capability_set CT h
        (mk_watched_frame caller_authority caller_senv caller_renv)).
Proof.
  intros CT h caller_authority caller_senv caller_renv destination
    destination_type Hdestination_nonzero Hdestination Hlength location
    [root [Hroot Hreachable]].
  exists root. split; [|exact Hreachable].
  eapply caller_null_post_capability_root_is_old; eauto.
Qed.

Lemma live_prospective_components_after_plain_pop :
  forall CT h cutoff active boundary stack caller,
    boundary.(boundary_caller) = caller ->
    live_prospective_mutable_authority_components_after_cutoff CT h cutoff
      active (boundary :: stack) ->
    live_prospective_mutable_authority_components_after_cutoff CT h cutoff
      caller stack.
Proof.
  intros CT h cutoff active boundary stack caller Hcaller Hold frame root
    target Hlive Hreachable.
  inversion Hlive; subst.
  - eapply Hold with (frame := boundary.(boundary_caller)) (root := root).
    + constructor. simpl. left. reflexivity.
    + exact Hreachable.
  - eapply Hold with (frame := boundary0.(boundary_caller)) (root := root).
    + constructor. simpl. right. exact H.
    + exact Hreachable.
Qed.

Lemma frozen_callee_side_prospective_components_after_null_return_pop :
  forall CT h active boundary stack head snapshots caller_authority
    caller_senv caller_renv destination destination_type,
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT caller_senv caller_renv h ->
    authority_context_sound h caller_renv caller_authority ->
    static_getType caller_senv destination = Some destination_type ->
    frozen_callee_side_prospective_components_after_boundaries CT h active
      (head :: snapshots) (boundary :: stack) ->
    frozen_callee_side_prospective_components_after_boundaries CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination Null_a))
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination Null_a)) snapshots)
      stack.
Proof.
  intros CT h active boundary stack head snapshots caller_authority
    caller_senv caller_renv destination destination_type Hcaller
    Hdestination_nonzero Hcaller_wf Hcaller_sound Hdestination Hold snapshot
    tracked_boundary above below Hpartition.
  set (caller_post := mk_watched_frame caller_authority caller_senv
    (update_r_env_value caller_renv destination Null_a)).
  destruct (advance_frozen_snapshot_live_partition_reflects CT h caller_post
    snapshots stack snapshot tracked_boundary above below Hpartition) as
    [old_snapshot Hold_partition].
  have Hinput_partition : frozen_snapshot_live_partition
      (head :: snapshots) (boundary :: stack) old_snapshot tracked_boundary
      (boundary :: above) below.
  { constructor. exact Hold_partition. }
  have Hinput_components := Hold old_snapshot tracked_boundary
    (boundary :: above) below Hinput_partition.
  have Hcaller_components :
      live_prospective_mutable_authority_components_after_cutoff CT h
        tracked_boundary.(boundary_entry_cutoff)
        (mk_watched_frame caller_authority caller_senv caller_renv) above.
  { eapply live_prospective_components_after_plain_pop with
      (active := active) (boundary := boundary).
    - exact Hcaller.
    - exact Hinput_components. }
  have Hlength : length caller_senv = length caller_renv.(vars) :=
    proj1 (proj2 (proj2 (proj2 (proj2 Hcaller_wf)))).
  unfold caller_post.
  eapply live_prospective_mutable_authority_components_after_active_descent.
  - exact Hcaller_wf.
  - exact Hcaller_sound.
  - eapply caller_null_post_rdm_roots_descend; eauto.
  - eapply caller_null_post_owned_is_old; eauto.
  - exact Hcaller_components.
Qed.

Lemma live_mutable_authority_components_after_null_return_pop :
  forall CT h cutoff active boundary stack caller_authority caller_senv
    caller_renv destination destination_type,
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT caller_senv caller_renv h ->
    static_getType caller_senv destination = Some destination_type ->
    live_mutable_authority_components_after_cutoff CT h cutoff active
      (boundary :: stack) ->
    live_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination Null_a)) stack.
Proof.
  intros CT h cutoff active boundary stack caller_authority caller_senv
    caller_renv destination destination_type Hcaller Hdestination_nonzero
    Hcaller_wf Hdestination Hold frame root target Hlive Hreachable.
  have Hlength : length caller_senv = length caller_renv.(vars) :=
    proj1 (proj2 (proj2 (proj2 (proj2 Hcaller_wf)))).
  inversion Hlive; subst.
  - inversion Hreachable; subst.
    + eapply Hold with (frame := boundary.(boundary_caller)) (root := root).
      * constructor. simpl. left. reflexivity.
      * apply mutable_authority_reachable_capability.
        -- rewrite Hcaller. eapply caller_null_post_capability_root_is_old;
             eauto.
        -- exact H0.
        -- exact H1.
    + eapply Hold with (frame := boundary.(boundary_caller)) (root := root).
      * constructor. simpl. left. reflexivity.
      * apply mutable_authority_reachable_rdm.
        -- rewrite Hcaller. eapply caller_null_post_rdm_root_is_old; eauto.
        -- exact H0.
        -- exact H1.
  - eapply Hold with (frame := boundary0.(boundary_caller)) (root := root).
    + constructor. simpl. right. exact H.
    + exact Hreachable.
Qed.

Lemma frozen_callee_side_components_after_null_return_pop :
  forall CT h active boundary stack head snapshots caller_authority
    caller_senv caller_renv destination destination_type,
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT caller_senv caller_renv h ->
    static_getType caller_senv destination = Some destination_type ->
    frozen_callee_side_mutable_components_after_boundaries CT h active
      (head :: snapshots) (boundary :: stack) ->
    frozen_callee_side_mutable_components_after_boundaries CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination Null_a))
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination Null_a)) snapshots)
      stack.
Proof.
  intros CT h active boundary stack head snapshots caller_authority
    caller_senv caller_renv destination destination_type Hcaller
    Hdestination_nonzero Hcaller_wf Hdestination Hold snapshot
    tracked_boundary above below Hpartition.
  set (caller_post := mk_watched_frame caller_authority caller_senv
    (update_r_env_value caller_renv destination Null_a)).
  destruct (advance_frozen_snapshot_live_partition_reflects CT h caller_post
    snapshots stack snapshot tracked_boundary above below Hpartition) as
    [old_snapshot Hold_partition].
  have Hinput_partition : frozen_snapshot_live_partition
      (head :: snapshots) (boundary :: stack) old_snapshot tracked_boundary
      (boundary :: above) below.
  { constructor. exact Hold_partition. }
  have Hinput_components := Hold old_snapshot tracked_boundary
    (boundary :: above) below Hinput_partition.
  unfold caller_post.
  eapply live_mutable_authority_components_after_null_return_pop; eauto.
Qed.

Lemma advance_frozen_caller_snapshots_resume_roots_in_heap :
  forall CT h active snapshots,
    frozen_caller_snapshots_resume_roots_in_heap h snapshots ->
    frozen_caller_snapshots_resume_roots_in_heap h
      (advance_frozen_caller_snapshots CT h active snapshots).
Proof.
  intros CT h active snapshots Hroots snapshot root Hsnapshot Hroot.
  unfold advance_frozen_caller_snapshots in Hsnapshot.
  apply in_map_iff in Hsnapshot.
  destruct Hsnapshot as [slot [Heq Hslot]].
  destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst snapshot. simpl in Hroot.
  eapply Hroots; eauto.
Qed.

(** Cross-phase form used at return.  The old closure certificate is relative
    to the completed callee and need not hold for the resumed caller.  Only
    the frame-independent parts of the old exposure certificate are reused;
    closure under [new_active] is rebuilt by taking its closure explicitly. *)
Lemma advance_frozen_caller_snapshots_resume_exposures_wf_from_any_active :
  forall CT h old_active new_active snapshots,
    wf_r_config CT new_active.(frame_senv) new_active.(frame_renv) h ->
    frozen_caller_snapshots_resume_exposures_wf CT h old_active snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h new_active
      (advance_frozen_caller_snapshots CT h new_active snapshots).
Proof.
  intros CT h old_active new_active snapshots Hwf
    [Hruntime [_ [Hdangerous [Hentry Hroots]]]].
  repeat split.
  - intros snapshot Hsnapshot.
    unfold advance_frozen_caller_snapshots in Hsnapshot.
    apply in_map_iff in Hsnapshot.
    destruct Hsnapshot as [slot [Heq Hslot]].
    destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as Heq. subst snapshot. simpl.
    eapply advance_frozen_caller_snapshot_runtime_mutable; eauto.
  - intros snapshot Hsnapshot.
    unfold advance_frozen_caller_snapshots in Hsnapshot.
    apply in_map_iff in Hsnapshot.
    destruct Hsnapshot as [slot [Heq Hslot]].
    destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as Heq. subst snapshot. simpl.
    apply (proj1 (frozen_caller_authority_closure_idempotent CT h new_active
      old_snapshot.(frozen_snapshot_current_resume_exposure))).
  - intros snapshot mode location Hsnapshot Hcolor.
    unfold advance_frozen_caller_snapshots in Hsnapshot.
    apply in_map_iff in Hsnapshot.
    destruct Hsnapshot as [slot [Heq Hslot]].
    destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as Heq. subst snapshot. simpl in Hcolor.
    destruct Hcolor as [seed [Hseed Hpath]].
    destruct seed as [seed_mode seed_location].
    have Hseed_mode := Hdangerous old_snapshot seed_mode seed_location
      Hslot Hseed.
    exact (frozen_caller_authority_connected_preserves_dangerous CT h
      new_active (seed_mode, seed_location) (mode, location) Hseed_mode
      Hpath).
  - intros snapshot Hsnapshot state Hstate.
    unfold advance_frozen_caller_snapshots in Hsnapshot.
    apply in_map_iff in Hsnapshot.
    destruct Hsnapshot as [slot [Heq Hslot]].
    destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as Heq. subst snapshot. simpl in *.
    apply frozen_caller_authority_closure_contains.
    eapply Hentry; eauto.
  - intros snapshot root Hsnapshot Hroot Hroot_runtime.
    unfold advance_frozen_caller_snapshots in Hsnapshot.
    apply in_map_iff in Hsnapshot.
    destruct Hsnapshot as [slot [Heq Hslot]].
    destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as Heq. subst snapshot. simpl in *.
    apply frozen_caller_authority_closure_contains.
    eapply Hroots; eauto.
Qed.

(** The structural part of the private frozen state.  These facts are
    transported uniformly whenever a suspended snapshot is advanced through
    the currently active frame.  The protected-zone and resume-safety facts
    are intentionally absent: those are the semantic obligations discharged
    by the pop classifier. *)
Definition private_frozen_snapshot_structural_state
  (CT : class_table) (h : heap) (active : watched_frame)
  (snapshots : list frozen_caller_snapshot_slot)
  (stack : list watched_boundary) : Prop :=
  frozen_caller_snapshots_aligned snapshots stack /\
  frozen_caller_snapshots_runtime_mutable h snapshots /\
  frozen_caller_snapshots_closed CT h active snapshots /\
  frozen_caller_snapshots_retain_entry snapshots /\
  frozen_caller_snapshots_dangerous snapshots /\
  frozen_caller_snapshots_resume_roots_in_heap h snapshots /\
  frozen_caller_snapshots_resume_exposures_wf CT h active snapshots /\
  frozen_caller_snapshots_before_boundaries snapshots stack /\
  frozen_caller_snapshots_nested_covered snapshots /\
  frozen_caller_snapshots_entry_exposure_covered snapshots /\
  frozen_caller_snapshots_cover_phase_incoming snapshots.

Lemma advance_frozen_caller_snapshots_structural_state :
  forall CT h old_active new_active snapshots stack,
    wf_r_config CT new_active.(frame_senv) new_active.(frame_renv) h ->
    private_frozen_snapshot_structural_state CT h old_active snapshots stack ->
    private_frozen_snapshot_structural_state CT h new_active
      (advance_frozen_caller_snapshots CT h new_active snapshots) stack /\
    frozen_caller_snapshot_list_metadata_eq
      (advance_frozen_caller_snapshots CT h new_active snapshots) snapshots.
Proof.
  intros CT h old_active new_active snapshots stack Hwf
    (Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Hroots &
      Hexposure & Hbefore & Hnested & Hentry & Hphase).
  split.
  - refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))).
    + unfold frozen_caller_snapshots_aligned in *.
      unfold advance_frozen_caller_snapshots. rewrite length_map.
      exact Haligned.
    + eapply advance_frozen_caller_snapshots_runtime_mutable; eauto.
    + apply advance_frozen_caller_snapshots_closed.
    + eapply advance_frozen_caller_snapshots_retain_entry; eauto.
    + eapply advance_frozen_caller_snapshots_dangerous; eauto.
    + eapply advance_frozen_caller_snapshots_resume_roots_in_heap; eauto.
    + eapply advance_frozen_caller_snapshots_resume_exposures_wf_from_any_active;
        eauto.
    + eapply advance_frozen_caller_snapshots_before_boundaries; eauto.
    + eapply advance_frozen_caller_snapshots_nested_covered; eauto.
    + eapply advance_frozen_caller_snapshots_entry_exposure_covered; eauto.
    + eapply advance_frozen_caller_snapshots_cover_phase_incoming; eauto.
  - apply advance_frozen_caller_snapshots_metadata_eq.
Qed.

(** Dropping the snapshot paired with the top call boundary exposes exactly
    the structural data for the older suspended callers. *)
Lemma private_frozen_statement_tail_structural_state :
  forall CT P Z cutoff active boundary stack incoming slot snapshots h,
    private_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (slot :: snapshots) h ->
    private_frozen_snapshot_structural_state CT h active snapshots stack.
Proof.
  intros CT P Z cutoff active boundary stack incoming slot snapshots h
    [Hfrozen [_ [Hbefore [Hnested _]]]].
  destruct Hfrozen as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))).
  - eapply frozen_caller_snapshots_aligned_pop; eauto.
  - intros snapshot Hsnapshot. eapply Hruntime. simpl. right. exact Hsnapshot.
  - intros snapshot Hsnapshot. eapply Hclosed. simpl. right. exact Hsnapshot.
  - intros snapshot Hsnapshot. eapply Hretain. simpl. right. exact Hsnapshot.
  - intros snapshot mode location Hsnapshot. eapply Hdangerous.
    simpl. right. exact Hsnapshot.
  - intros snapshot root Hsnapshot. eapply Hroots.
    simpl. right. exact Hsnapshot.
  - destruct Hexposure as
      (Hexposure_runtime & Hexposure_closed & Hexposure_dangerous &
        Hexposure_entry & Hexposure_roots).
    repeat split.
    + intros snapshot Hsnapshot. eapply Hexposure_runtime.
      simpl. right. exact Hsnapshot.
    + intros snapshot Hsnapshot. eapply Hexposure_closed.
      simpl. right. exact Hsnapshot.
    + intros snapshot mode location Hsnapshot. eapply Hexposure_dangerous.
      simpl. right. exact Hsnapshot.
    + intros snapshot Hsnapshot. eapply Hexposure_entry.
      simpl. right. exact Hsnapshot.
    + intros snapshot root Hsnapshot. eapply Hexposure_roots.
      simpl. right. exact Hsnapshot.
  - inversion Hbefore; subst. exact H4.
  - eapply frozen_caller_snapshots_nested_covered_tail. exact Hnested.
  - intros snapshot source_mode source Hsnapshot. eapply Hentry.
    simpl. right. exact Hsnapshot.
  - intros snapshot mode location Hsnapshot. eapply Hphase.
    simpl. right. exact Hsnapshot.
Qed.

(** The genuinely semantic residue of a return transition.  Keeping this
    separate from structural snapshot transport makes explicit that all
    assumptions remain proof-local: none can become a dispatch check or a
    premise of [successful_stmt_preserves_potential_history]. *)
Definition private_frozen_snapshot_return_safety
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (active : watched_frame) (incoming : Ensemble authority_flow_state)
  (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  frozen_caller_snapshots_active_resume_justified CT h Z active snapshots /\
  frozen_caller_snapshots_avoid_protected Z snapshots /\
  frozen_caller_snapshots_nested_resume_safe Z snapshots /\
  frozen_caller_snapshots_resume_roots_safe CT h Z active snapshots /\
  frozen_caller_snapshots_resume_joins_safe Z snapshots /\
  frozen_completed_colors_resume_safe Z
    (executing_authority_color_set CT h active incoming) snapshots.

Definition boundary_view_anchor
  (boundary : watched_boundary) (root : Loc) : Prop :=
  match boundary.(boundary_receiver_view) with
  | Mut => typed_root Mut
      boundary.(boundary_caller).(frame_senv)
      boundary.(boundary_caller).(frame_renv) root
  | Imm => typed_root Imm
      boundary.(boundary_caller).(frame_senv)
      boundary.(boundary_caller).(frame_renv) root
  | RDM => typed_root RDM
      boundary.(boundary_caller).(frame_senv)
      boundary.(boundary_caller).(frame_renv) root
  | RO | Lost | Bot => False
  end.

Definition boundary_view_attachment
  (CT : class_table) (h : heap) (boundary : watched_boundary)
  (stack : list watched_boundary) (root : Loc) : Prop :=
  exists anchor,
    boundary_view_anchor boundary anchor /\
    potential_connected CT h boundary.(boundary_caller) stack anchor root.

Definition boundary_view_entry
  (CT : class_table) (h : heap) (boundary : watched_boundary)
  (stack : list watched_boundary) (root : Loc) : Prop :=
  exists anchor,
    boundary_view_anchor boundary anchor /\
    potential_connected CT h boundary.(boundary_caller) stack root anchor.

Definition authority_boundary_view_attachment
  (CT : class_table) (h : heap) (boundary : watched_boundary)
  (stack : list watched_boundary) (root : Loc) : Prop :=
  exists anchor,
    boundary_view_anchor boundary anchor /\
    authority_color_connected CT h boundary.(boundary_caller) stack
      anchor root.

Definition authority_boundary_view_entry
  (CT : class_table) (h : heap) (boundary : watched_boundary)
  (stack : list watched_boundary) (root : Loc) : Prop :=
  exists anchor,
    boundary_view_anchor boundary anchor /\
    authority_color_connected CT h boundary.(boundary_caller) stack
      root anchor.

Lemma authority_boundary_view_attachment_root :
  forall CT h boundary stack root,
    boundary_view_anchor boundary root ->
    authority_boundary_view_attachment CT h boundary stack root.
Proof.
  intros. exists root. split; [assumption|apply rt_refl].
Qed.

Lemma authority_boundary_view_entry_root :
  forall CT h boundary stack root,
    boundary_view_anchor boundary root ->
    authority_boundary_view_entry CT h boundary stack root.
Proof.
  intros. exists root. split; [assumption|apply rt_refl].
Qed.

Lemma authority_boundary_view_attachment_transport :
  forall CT h boundary stack first second,
    authority_boundary_view_attachment CT h boundary stack first ->
    authority_color_connected CT h boundary.(boundary_caller) stack
      first second ->
    authority_boundary_view_attachment CT h boundary stack second.
Proof.
  intros CT h boundary stack first second
    [anchor [Hanchor Hanchor_first]] Hfirst_second.
  exists anchor. split; [exact Hanchor|].
  eapply authority_color_connected_trans; eauto.
Qed.

Lemma authority_boundary_view_entry_transport :
  forall CT h boundary stack first second,
    authority_color_connected CT h boundary.(boundary_caller) stack
      first second ->
    authority_boundary_view_entry CT h boundary stack second ->
    authority_boundary_view_entry CT h boundary stack first.
Proof.
  intros CT h boundary stack first second Hfirst_second
    [anchor [Hanchor Hsecond_anchor]].
  exists anchor. split; [exact Hanchor|].
  eapply authority_color_connected_trans; eauto.
Qed.

Definition boundary_color_attachment
  (CT : class_table) (h : heap) (boundary : watched_boundary)
  (stack : list watched_boundary) (root : Loc) : Prop :=
  exists anchor,
    boundary_view_anchor boundary anchor /\
    boundary_connected CT h boundary.(boundary_caller) stack anchor root.

Definition boundary_color_entry
  (CT : class_table) (h : heap) (boundary : watched_boundary)
  (stack : list watched_boundary) (root : Loc) : Prop :=
  exists anchor,
    boundary_view_anchor boundary anchor /\
    boundary_connected CT h boundary.(boundary_caller) stack root anchor.

Lemma boundary_view_attachment_root :
  forall CT h boundary stack root,
    boundary_view_anchor boundary root ->
    boundary_view_attachment CT h boundary stack root.
Proof.
  intros. exists root. split; [assumption|apply rt_refl].
Qed.

Lemma boundary_view_entry_root :
  forall CT h boundary stack root,
    boundary_view_anchor boundary root ->
    boundary_view_entry CT h boundary stack root.
Proof.
  intros. exists root. split; [assumption|apply rt_refl].
Qed.

Lemma boundary_view_attachment_transport :
  forall CT h boundary stack first second,
    boundary_view_attachment CT h boundary stack first ->
    potential_connected CT h boundary.(boundary_caller) stack first second ->
    boundary_view_attachment CT h boundary stack second.
Proof.
  intros CT h boundary stack first second
    [anchor [Hanchor Hanchor_first]] Hfirst_second.
  exists anchor. split; [exact Hanchor|].
  eapply potential_connected_trans; eauto.
Qed.

Lemma boundary_view_entry_transport :
  forall CT h boundary stack first second,
    potential_connected CT h boundary.(boundary_caller) stack first second ->
    boundary_view_entry CT h boundary stack second ->
    boundary_view_entry CT h boundary stack first.
Proof.
  intros CT h boundary stack first second Hfirst_second
    [anchor [Hanchor Hsecond_anchor]].
  exists anchor. split; [exact Hanchor|].
  eapply potential_connected_trans; eauto.
Qed.

Lemma readonly_boundary_roots_equal :
  forall boundary left right,
    boundary.(boundary_receiver_view) = RO ->
    typed_root RDM boundary.(boundary_callee_entry_senv)
      boundary.(boundary_callee_entry_renv) left ->
    typed_root RDM boundary.(boundary_callee_entry_senv)
      boundary.(boundary_callee_entry_renv) right ->
    left = right.
Proof.
  intros boundary left right Hview Hleft Hright.
  have Hleft_origin := boundary_entry_rdm_root_by_view boundary left Hleft.
  have Hright_origin := boundary_entry_rdm_root_by_view boundary right Hright.
  rewrite Hview in Hleft_origin, Hright_origin.
  destruct Hleft_origin as
    [left_receiver [Hleft_receiver [Hleft_eq Hleft_root]]].
  destruct Hright_origin as
    [right_receiver [Hright_receiver [Hright_eq Hright_root]]].
  rewrite Hleft_receiver in Hright_receiver.
  injection Hright_receiver as <-. congruence.
Qed.

Lemma potential_adjacent_after_call_push :
  forall CT h boundary stack callee_authority left right,
    potential_adjacent CT h
      (mk_watched_frame callee_authority
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv))
      (boundary :: stack) left right ->
    potential_connected CT h boundary.(boundary_caller) stack left right \/
    (boundary_view_entry CT h boundary stack left /\
     boundary_view_attachment CT h boundary stack right).
Proof.
  intros CT h boundary stack callee_authority left right
    [Hheap | [Hframe | Hreturn]].
  - left. apply rt_step. left. exact Hheap.
  - destruct Hframe as
      [frame [Hlive [Hleft Hright]]].
    inversion Hlive; subst.
    + have Hleft_origin := boundary_entry_rdm_root_by_view boundary left Hleft.
      have Hright_origin := boundary_entry_rdm_root_by_view boundary right Hright.
      destruct boundary.(boundary_receiver_view) eqn:Hview;
        simpl in Hleft_origin, Hright_origin.
      * right. split.
        -- apply boundary_view_entry_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
        -- apply boundary_view_attachment_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
      * right. split.
        -- apply boundary_view_entry_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
        -- apply boundary_view_attachment_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
      * right. split.
        -- apply boundary_view_entry_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
        -- apply boundary_view_attachment_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
      * left. have Heq := readonly_boundary_roots_equal boundary left right
          Hview Hleft Hright. subst right. apply rt_refl.
      * contradiction.
      * contradiction.
    + simpl in H.
      destruct H as [Htop | Htail].
      * subst boundary0. left. eapply live_frame_rdm_roots_potentially_connected
          with (frame := boundary.(boundary_caller)).
        -- constructor.
        -- exact Hleft.
        -- exact Hright.
      * left. apply rt_step. right. left. exists boundary0.(boundary_caller).
        repeat split; try assumption. constructor. exact Htail.
  - destruct Hreturn as
      [callee [return_boundary
        [Hlive [Hview [Hcallee_return
          [Hruntime [Hroots | Hroots]]]]]]].
    + inversion Hlive; subst.
      * have Horigin := boundary_entry_rdm_root_by_view return_boundary left
          (proj1 Hroots).
        rewrite Hview in Horigin. simpl in Horigin.
        left. eapply live_frame_rdm_roots_potentially_connected with
          (frame := return_boundary.(boundary_caller)).
        -- constructor.
        -- exact Horigin.
        -- exact (proj2 Hroots).
      * left. apply rt_step. right. right. exists callee, return_boundary.
        split.
        { match goal with
          | Htail : live_call_boundary _ _ _ _ |- _ => exact Htail
          end. }
        split; [exact Hview|]. split; [exact Hcallee_return|].
        split; [exact Hruntime|]. left. exact Hroots.
    + inversion Hlive; subst.
      * have Horigin := boundary_entry_rdm_root_by_view return_boundary right
          (proj2 Hroots).
        rewrite Hview in Horigin. simpl in Horigin.
        left. eapply live_frame_rdm_roots_potentially_connected with
          (frame := return_boundary.(boundary_caller)).
        -- constructor.
        -- exact (proj1 Hroots).
        -- exact Horigin.
      * left. apply rt_step. right. right. exists callee, return_boundary.
        split.
        { match goal with
          | Htail : live_call_boundary _ _ _ _ |- _ => exact Htail
          end. }
        split; [exact Hview|]. split; [exact Hcallee_return|].
        split; [exact Hruntime|]. right. exact Hroots.
Qed.

Lemma potential_connected_after_call_push :
  forall CT h boundary stack callee_authority left right,
    potential_connected CT h
      (mk_watched_frame callee_authority
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv))
      (boundary :: stack) left right ->
    potential_connected CT h boundary.(boundary_caller) stack left right \/
    (boundary_view_entry CT h boundary stack left /\
     boundary_view_attachment CT h boundary stack right).
Proof.
  intros CT h boundary stack callee_authority left right Hconnected.
  induction Hconnected.
  - eapply potential_adjacent_after_call_push; eauto.
  - left. apply rt_refl.
  - destruct IHHconnected1 as [Hxy | [Hentry_x Hattach_y]];
      destruct IHHconnected2 as [Hyz | [Hentry_y Hattach_z]].
    + left. eapply potential_connected_trans; eauto.
    + right. split.
      * eapply boundary_view_entry_transport; eauto.
      * exact Hattach_z.
    + right. split.
      * exact Hentry_x.
      * eapply boundary_view_attachment_transport; eauto.
    + right. split; assumption.
Qed.

Lemma authority_color_adjacent_after_call_push :
  forall CT h boundary stack callee_authority left right,
    authority_color_adjacent CT h
      (mk_watched_frame callee_authority
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv))
      (boundary :: stack) left right ->
    authority_color_connected CT h boundary.(boundary_caller) stack
      left right \/
    (authority_boundary_view_entry CT h boundary stack left /\
     authority_boundary_view_attachment CT h boundary stack right).
Proof.
  intros CT h boundary stack callee_authority left right [Hheap | Hframe].
  - left. apply rt_step. left. exact Hheap.
  - destruct Hframe as [frame [Hlive [Hleft Hright]]].
    inversion Hlive; subst.
    + have Hleft_origin := boundary_entry_rdm_root_by_view boundary left Hleft.
      have Hright_origin :=
        boundary_entry_rdm_root_by_view boundary right Hright.
      destruct boundary.(boundary_receiver_view) eqn:Hview;
        simpl in Hleft_origin, Hright_origin.
      * right. split.
        -- apply authority_boundary_view_entry_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
        -- apply authority_boundary_view_attachment_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
      * right. split.
        -- apply authority_boundary_view_entry_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
        -- apply authority_boundary_view_attachment_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
      * right. split.
        -- apply authority_boundary_view_entry_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
        -- apply authority_boundary_view_attachment_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
      * left. have Heq := readonly_boundary_roots_equal boundary left right
          Hview Hleft Hright. subst right. apply rt_refl.
      * contradiction.
      * contradiction.
    + simpl in H.
      destruct H as [Htop | Htail].
      * subst boundary0. left. apply rt_step. right.
        exists boundary.(boundary_caller).
        split; [constructor|]. split; assumption.
      * left. apply rt_step. right. exists boundary0.(boundary_caller).
        split; [constructor; exact Htail|]. split; assumption.
Qed.

Lemma authority_call_push_live_capability_included_in_caller :
  forall CT h boundary above location,
    In Loc
      (live_capability_set CT h
        (mk_watched_frame
          (call_authority boundary.(boundary_caller).(frame_authority)
            boundary.(boundary_receiver_view))
          boundary.(boundary_callee_entry_senv)
          boundary.(boundary_callee_entry_renv))
        (boundary :: above)) location ->
    In Loc
      (live_capability_set CT h boundary.(boundary_caller) above) location.
Proof.
  intros CT h boundary above location
    [root [[Hactive | [suspended [Hin Hsuspended]]] Hreach]].
  - exists root. split; [left|exact Hreach].
    exact (boundary_capability_origins boundary root Hactive).
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + subst suspended. exists root.
      split; [left; exact Hsuspended|exact Hreach].
    + exists root. split.
      * right. exists suspended. split; assumption.
      * exact Hreach.
Qed.

Lemma authority_flow_step_after_call_push_decomposes :
  forall CT h boundary stack source target,
    wf_r_config CT boundary.(boundary_caller).(frame_senv)
      boundary.(boundary_caller).(frame_renv) h ->
    r_muttype h (snd source) = Some Mut_r ->
    authority_flow_step CT h
      (mk_watched_frame
        (call_authority boundary.(boundary_caller).(frame_authority)
          boundary.(boundary_receiver_view))
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv))
      (boundary :: stack) source target ->
    authority_flow_connected CT h boundary.(boundary_caller) stack
      source target \/
    exists anchor,
      typed_root Mut boundary.(boundary_caller).(frame_senv)
        boundary.(boundary_caller).(frame_renv) anchor /\
      authority_flow_connected CT h boundary.(boundary_caller) stack
        source (FlowPowered, anchor).
Proof.
  intros CT h boundary stack source target Hcaller_wf Hsource_runtime Hstep.
  inversion Hstep; subst; simpl in *.
  - left. apply rt_step. apply authority_flow_retained. exact H.
  - left. apply rt_step. apply authority_flow_reverse_rdm. exact H.
  - left. apply rt_step. apply authority_flow_neutral_rdm_forward. exact H.
  - left. apply rt_step. apply authority_flow_neutral_rdm_backward. exact H.
  - destruct H as [frame [Hlive [Hleft Hright]]].
    inversion Hlive; subst.
    + have Hleft_origin :=
        boundary_entry_rdm_root_by_view boundary left Hleft.
      have Hright_origin :=
        boundary_entry_rdm_root_by_view boundary right Hright.
      destruct boundary.(boundary_receiver_view) eqn:Hview;
        simpl in Hleft_origin, Hright_origin.
      * right. exists left. split; [exact Hleft_origin|apply rt_refl].
      * have Hleft_immutable :=
          typed_imm_root_runtime_immutable CT
            boundary.(boundary_caller).(frame_senv)
            boundary.(boundary_caller).(frame_renv) h left Hcaller_wf
            Hleft_origin.
        congruence.
      * left. apply rt_step. apply authority_flow_powered_frame.
        exists boundary.(boundary_caller).
        split; [constructor|]. split; assumption.
      * left.
        have Heq := readonly_boundary_roots_equal boundary left right Hview
          Hleft Hright.
        subst right. apply rt_step. apply authority_flow_forget.
      * contradiction.
      * contradiction.
    + simpl in H. destruct H as [Htop | Htail].
      * subst boundary0. left. apply rt_step.
        apply authority_flow_powered_frame.
        exists boundary.(boundary_caller).
        split; [constructor|]. split; assumption.
      * left. apply rt_step. apply authority_flow_powered_frame.
        exists boundary0.(boundary_caller).
        split; [constructor; exact Htail|]. split; assumption.
  - destruct H as [frame [Hlive [Hleft Hright]]].
    inversion Hlive; subst.
    + have Hleft_origin :=
        boundary_entry_rdm_root_by_view boundary left Hleft.
      have Hright_origin :=
        boundary_entry_rdm_root_by_view boundary right Hright.
      destruct boundary.(boundary_receiver_view) eqn:Hview;
        simpl in Hleft_origin, Hright_origin.
      * right. exists left. split; [exact Hleft_origin|].
        apply rt_step. apply authority_flow_promote.
        eapply typed_mut_root_is_live_capability. exact Hleft_origin.
      * have Hleft_immutable :=
          typed_imm_root_runtime_immutable CT
            boundary.(boundary_caller).(frame_senv)
            boundary.(boundary_caller).(frame_renv) h left Hcaller_wf
            Hleft_origin.
        congruence.
      * left. apply rt_step. apply authority_flow_neutral_frame.
        exists boundary.(boundary_caller).
        split; [constructor|]. split; assumption.
      * left.
        have Heq := readonly_boundary_roots_equal boundary left right Hview
          Hleft Hright.
        subst right. apply rt_refl.
      * contradiction.
      * contradiction.
    + simpl in H. destruct H as [Htop | Htail].
      * subst boundary0. left. apply rt_step.
        apply authority_flow_neutral_frame.
        exists boundary.(boundary_caller).
        split; [constructor|]. split; assumption.
      * left. apply rt_step. apply authority_flow_neutral_frame.
        exists boundary0.(boundary_caller).
        split; [constructor; exact Htail|]. split; assumption.
  - left. apply rt_step. apply authority_flow_forget.
  - left. apply rt_step. apply authority_flow_promote.
    eapply authority_call_push_live_capability_included_in_caller.
    exact H.
Qed.

Lemma potential_history_enter_call :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack
    x method y args sGamma' vals ly cy runtime_mdef Ty,
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    exists origins destination_type,
      static_getType sGamma x = Some destination_type /\
      potential_live_history_state CT P Z cutoff
        (mk_watched_frame
          (call_authority caller_authority (sqtype Ty))
          (mreceiver (msignature runtime_mdef) ::
            mparams (msignature runtime_mdef))
          (mkr_env (Iot ly :: vals)))
        (mk_watched_call_boundary
          (mk_watched_frame caller_authority sGamma rGamma)
          (mreceiver (msignature runtime_mdef) ::
            mparams (msignature runtime_mdef))
          (mkr_env (Iot ly :: vals)) (sqtype Ty)
          (mreturn (mbody runtime_mdef)) (sqtype destination_type)
          (sqtype (mret (msignature runtime_mdef))) (dom h) origins ::
          stack) h.
Proof.
  intros CT P Z cutoff caller_authority sGamma mt rGamma h stack
    x method y args sGamma' vals ly cy runtime_mdef Ty
    [Hlive [Hpotential Hcutoffs]]
    Htyping Hscope Hgety Hvalue Hbase Hfind Hargs.
  have Hcomponent : component_forward_history_state CT P Z
      (live_capability_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) stack)
      cutoff sGamma rGamma h.
  { eapply mutable_authority_component_history
      with (authority := caller_authority).
    exact (proj1 Hlive). }
  destruct (live_history_enter_call CT P Z cutoff caller_authority sGamma mt
    rGamma h stack x method y args sGamma' vals ly cy runtime_mdef Ty Hlive
    Hcomponent Htyping Hscope Hgety Hvalue Hbase Hfind Hargs) as
    [origins [destination_type [Hdestination Hlive_post]]].
  exists origins, destination_type. split; [exact Hdestination|].
  split; [exact Hlive_post|].
  split.
  {
  set (caller := mk_watched_frame caller_authority sGamma rGamma).
  set (callee_senv := mreceiver (msignature runtime_mdef) ::
    mparams (msignature runtime_mdef)).
  set (callee_renv := mkr_env (Iot ly :: vals)).
  set (boundary := mk_watched_call_boundary caller callee_senv callee_renv
    (sqtype Ty) (mreturn (mbody runtime_mdef)) (sqtype destination_type)
    (sqtype (mret (msignature runtime_mdef))) (dom h) origins).
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 Hlive)).
  have Hframes : live_frames_wf CT h caller stack.
  { unfold caller. exact (proj1 (proj2 Hlive)). }
  have Hsound : live_frames_authority_sound h caller stack.
  { unfold caller. exact (proj1 (proj2 (proj2 Hlive))). }
  intros capability protected Hcapability Hprotected Hconnected.
  have Hcapability_old : In Loc
      (live_capability_set CT h caller stack) capability.
  { unfold boundary, caller, callee_senv, callee_renv in Hcapability |- *.
    apply (proj1 (call_push_live_reachability_equivalent CT caller_authority
      sGamma mt rGamma h x method y args sGamma' vals ly cy runtime_mdef Ty
      origins (mreturn (mbody runtime_mdef)) (sqtype destination_type)
      (sqtype (mret (msignature runtime_mdef))) (dom h) stack capability
      Hwf Htyping Hscope Hgety Hvalue Hbase Hfind
      Hargs)).
    exact Hcapability. }
  destruct (potential_connected_after_call_push CT h boundary stack
    (call_authority caller_authority (sqtype Ty)) capability protected
    Hconnected) as
    [Hold_connected | [Hcapability_entry Hprotected_attachment]].
  - unfold caller in Hcapability_old, Hold_connected, Hframes, Hsound |- *.
    exact (Hpotential capability protected Hcapability_old Hprotected
      Hold_connected).
  - destruct (sqtype Ty) eqn:Hview.
    + destruct Hprotected_attachment as
        [zone_anchor [Hzone_anchor Hzone_connected]].
      unfold boundary_view_anchor in Hzone_anchor.
      unfold boundary in Hzone_anchor, Hzone_connected. simpl in *.
      have Hzone_capability : In Loc
          (live_capability_set CT h caller stack) zone_anchor.
      { unfold caller. eapply typed_mut_root_is_live_capability; eauto. }
      unfold caller in Hzone_capability, Hzone_connected.
      exact (Hpotential zone_anchor protected Hzone_capability Hprotected
        Hzone_connected).
    + destruct Hcapability_entry as
        [capability_anchor [Hcapability_anchor Hanchor_connected]].
      unfold boundary_view_anchor in Hcapability_anchor.
      unfold boundary in Hcapability_anchor, Hanchor_connected. simpl in *.
      have Hcapability_runtime := live_capability_members_runtime_mutable CT h
        caller stack Hframes Hsound capability Hcapability_old.
      have Hanchor_immutable := typed_imm_root_runtime_immutable CT sGamma
        rGamma h capability_anchor Hwf Hcapability_anchor.
      have Hheap_wf : wf_heap CT h := proj1 (proj2 Hwf).
      have Hanchor_runtime := potential_connected_preserves_runtime_mutability
        CT h caller stack capability capability_anchor Mut_r Hframes Hheap_wf
        Hanchor_connected Hcapability_runtime.
      rewrite Hanchor_immutable in Hanchor_runtime. discriminate.
    + destruct Hcapability_entry as
        [capability_anchor [Hcapability_anchor Hcapability_connected]].
      destruct Hprotected_attachment as
        [zone_anchor [Hzone_anchor Hzone_connected]].
      unfold boundary_view_anchor in Hcapability_anchor, Hzone_anchor.
      unfold boundary in Hcapability_anchor, Hzone_anchor,
        Hcapability_connected, Hzone_connected. simpl in *.
      unfold caller in Hcapability_old, Hcapability_connected, Hzone_connected.
      apply (Hpotential capability protected Hcapability_old Hprotected).
      eapply potential_connected_trans.
	      * exact Hcapability_connected.
      * eapply potential_connected_trans.
        -- eapply live_frame_rdm_roots_potentially_connected
             with (frame := mk_watched_frame caller_authority sGamma rGamma).
           ++ constructor.
           ++ exact Hcapability_anchor.
           ++ exact Hzone_anchor.
        -- exact Hzone_connected.
    + destruct Hcapability_entry as
        [anchor [Hanchor Hanchor_connected]].
      unfold boundary_view_anchor in Hanchor.
      unfold boundary in Hanchor. simpl in Hanchor.
      contradiction.
    + destruct Hcapability_entry as
        [anchor [Hanchor Hanchor_connected]].
      unfold boundary_view_anchor in Hanchor.
      unfold boundary in Hanchor. simpl in Hanchor.
      contradiction.
    + destruct Hcapability_entry as
        [anchor [Hanchor Hanchor_connected]].
      unfold boundary_view_anchor in Hanchor.
      unfold boundary in Hanchor. simpl in Hanchor.
      contradiction.
  }
  { constructor.
    - simpl. lia.
    - exact Hcutoffs.
  }
Qed.

Lemma readonly_adaptation_subtype_rdm :
  forall receiver_q return_q,
    receiver_q <> Bot ->
    q_subtype
      (vpa_mutability_qq_readonly_state receiver_q return_q) RDM ->
    (receiver_q = RDM /\ return_q = RDM) \/ return_q = Bot.
Proof.
  intros receiver_q return_q Hreceiver Hsub.
  destruct receiver_q, return_q; simpl in Hsub;
    inversion Hsub; subst; auto; contradiction.
Qed.

Lemma refined_call_rdm_result_classifies_body_return :
  forall CT receiver_type body_return_type runtime_sig static_sig
    destination_type,
    qualified_type_subtype CT body_return_type (mret runtime_sig) ->
    method_signature_refinement CT runtime_sig static_sig ->
    qualified_type_subtype CT
      (vpa_mutability_tt_readonly_state receiver_type (mret static_sig))
      destination_type ->
    sqtype receiver_type <> Bot ->
    sqtype body_return_type <> Bot ->
    sqtype destination_type = RDM ->
    sqtype receiver_type = RDM /\
    (sqtype body_return_type = RDM \/
     sqtype body_return_type = Mut \/
     sqtype body_return_type = Imm).
Proof.
  intros CT receiver_type body_return_type runtime_sig static_sig
    destination_type Hbody Hrefine Hresult Hreceiver_nonbottom
    Hbody_nonbottom Hdestination.
  have Hresult_q := qualified_type_subtype_q_subtype CT
    (vpa_mutability_tt_readonly_state receiver_type (mret static_sig))
    destination_type Hresult.
  rewrite sq_vpa_tt_eq_qq_readonly_state in Hresult_q.
  rewrite Hdestination in Hresult_q.
  destruct (readonly_adaptation_subtype_rdm
    (sqtype receiver_type) (sqtype (mret static_sig))
    Hreceiver_nonbottom Hresult_q) as
    [[Hreceiver_rdm Hstatic_rdm] | Hstatic_bot].
  - split; [exact Hreceiver_rdm|].
    have Hruntime_cases :
      is_concrete_or_rdm_or_bot (sqtype (mret runtime_sig)).
    { eapply method_signature_refinement_return_concrete_or_rdm_or_bot;
        eauto.
      unfold is_concrete_or_rdm_or_bot. auto. }
    have Hbody_cases :
      is_concrete_or_rdm_or_bot (sqtype body_return_type).
    { eapply subtype_concrete_or_rdm_or_bot; eauto. }
    unfold is_concrete_or_rdm_or_bot in Hbody_cases.
    destruct Hbody_cases as
      [Hmut | [Himm | [Hrdm | Hbot]]]; auto.
    contradiction.
  - have Hruntime_bot :
      sqtype (mret runtime_sig) = Bot.
    { eapply method_signature_refinement_return_bot; eauto. }
    have Hbody_q := qualified_type_subtype_q_subtype CT
      body_return_type (mret runtime_sig) Hbody.
    rewrite Hruntime_bot in Hbody_q.
    have Hbody_bot : sqtype body_return_type = Bot.
    { inversion Hbody_q; subst; reflexivity. }
    contradiction.
Qed.

Lemma refined_call_rdm_mut_body_signature_shape :
  forall CT receiver_type body_return_type runtime_sig static_sig
    destination_type,
    qualified_type_subtype CT body_return_type (mret runtime_sig) ->
    method_signature_refinement CT runtime_sig static_sig ->
    qualified_type_subtype CT
      (vpa_mutability_tt_readonly_state receiver_type (mret static_sig))
      destination_type ->
    sqtype receiver_type <> Bot ->
    sqtype destination_type = RDM ->
    sqtype body_return_type = Mut ->
    sqtype (mret static_sig) = RDM /\
    sqtype (mret runtime_sig) = Mut.
Proof.
  intros CT receiver_type body_return_type runtime_sig static_sig
    destination_type Hbody Hrefine Hresult Hreceiver_nonbottom Hdestination
    Hbody_mut.
  have Hresult_q := qualified_type_subtype_q_subtype CT
    (vpa_mutability_tt_readonly_state receiver_type (mret static_sig))
    destination_type Hresult.
  rewrite sq_vpa_tt_eq_qq_readonly_state in Hresult_q.
  rewrite Hdestination in Hresult_q.
  destruct (readonly_adaptation_subtype_rdm
    (sqtype receiver_type) (sqtype (mret static_sig))
    Hreceiver_nonbottom Hresult_q) as
    [[_ Hstatic_rdm] | Hstatic_bot].
  - split; [exact Hstatic_rdm|].
    have Hruntime_cases :
        is_concrete_or_rdm_or_bot (sqtype (mret runtime_sig)).
    { eapply method_signature_refinement_return_concrete_or_rdm_or_bot;
        eauto.
      unfold is_concrete_or_rdm_or_bot. auto. }
    have Hbody_q := qualified_type_subtype_q_subtype CT
      body_return_type (mret runtime_sig) Hbody.
    rewrite Hbody_mut in Hbody_q.
    unfold is_concrete_or_rdm_or_bot in Hruntime_cases.
    destruct Hruntime_cases as
      [Hruntime_mut | [Hruntime_imm | [Hruntime_rdm | Hruntime_bot]]].
    + exact Hruntime_mut.
    + rewrite Hruntime_imm in Hbody_q. inversion Hbody_q.
    + rewrite Hruntime_rdm in Hbody_q. inversion Hbody_q.
    + rewrite Hruntime_bot in Hbody_q. inversion Hbody_q.
  - have Hruntime_bot :
        sqtype (mret runtime_sig) = Bot.
    { eapply method_signature_refinement_return_bot; eauto. }
    have Hbody_q := qualified_type_subtype_q_subtype CT
      body_return_type (mret runtime_sig) Hbody.
    rewrite Hbody_mut in Hbody_q.
    rewrite Hruntime_bot in Hbody_q. inversion Hbody_q.
Qed.

Lemma refined_call_rdm_rdm_body_signature_return :
  forall CT receiver_type body_return_type runtime_sig static_sig
    destination_type,
    qualified_type_subtype CT body_return_type (mret runtime_sig) ->
    method_signature_refinement CT runtime_sig static_sig ->
    qualified_type_subtype CT
      (vpa_mutability_tt_readonly_state receiver_type (mret static_sig))
      destination_type ->
    sqtype receiver_type <> Bot ->
    sqtype destination_type = RDM ->
    sqtype body_return_type = RDM ->
    sqtype (mret runtime_sig) = RDM.
Proof.
  intros CT receiver_type body_return_type runtime_sig static_sig
    destination_type Hbody Hrefine Hresult Hreceiver_nonbottom Hdestination
    Hbody_rdm.
  have Hresult_q := qualified_type_subtype_q_subtype CT
    (vpa_mutability_tt_readonly_state receiver_type (mret static_sig))
    destination_type Hresult.
  rewrite sq_vpa_tt_eq_qq_readonly_state in Hresult_q.
  rewrite Hdestination in Hresult_q.
  destruct (readonly_adaptation_subtype_rdm
    (sqtype receiver_type) (sqtype (mret static_sig))
    Hreceiver_nonbottom Hresult_q) as
    [[_ Hstatic_rdm] | Hstatic_bot].
  - have Hruntime_cases :
        is_concrete_or_rdm_or_bot (sqtype (mret runtime_sig)).
    { eapply method_signature_refinement_return_concrete_or_rdm_or_bot;
        eauto.
      unfold is_concrete_or_rdm_or_bot. auto. }
    have Hbody_q := qualified_type_subtype_q_subtype CT
      body_return_type (mret runtime_sig) Hbody.
    rewrite Hbody_rdm in Hbody_q.
    unfold is_concrete_or_rdm_or_bot in Hruntime_cases.
    destruct Hruntime_cases as
      [Hruntime_mut | [Hruntime_imm | [Hruntime_rdm | Hruntime_bot]]].
    + rewrite Hruntime_mut in Hbody_q. inversion Hbody_q.
    + rewrite Hruntime_imm in Hbody_q. inversion Hbody_q.
    + exact Hruntime_rdm.
    + rewrite Hruntime_bot in Hbody_q. inversion Hbody_q.
  - have Hruntime_bot :
        sqtype (mret runtime_sig) = Bot.
    { eapply method_signature_refinement_return_bot; eauto. }
    have Hbody_q := qualified_type_subtype_q_subtype CT
      body_return_type (mret runtime_sig) Hbody.
    rewrite Hbody_rdm in Hbody_q.
    rewrite Hruntime_bot in Hbody_q. inversion Hbody_q.
Qed.

(** In the only flexible-override shape that refines a statically RDM result
    to a dynamically mutable result, the callee cannot start with a non-null
    RDM root.  The receiver is RO.  For an ordinary dynamic RDM parameter,
    class-bounded contravariance forces the corresponding static parameter to
    be Bot, so a well-formed caller can pass only null at that position.

    This is the signature-level fact that rules out publishing a fresh Mut
    result through an old RDM parameter; it follows from behavioral subtyping
    rather than from a dispatch-side premise. *)
Lemma refined_mut_return_call_entry_has_no_rdm_roots :
  forall CT sGamma mt rGamma h x method receiver args vals receiver_location
    receiver_type runtime_mdef static_mdef,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method receiver args) sGamma ->
    readonly_state_method_scope mt ->
    static_getType sGamma receiver = Some receiver_type ->
    runtime_getVal rGamma receiver = Some (Iot receiver_location) ->
    runtime_lookup_list rGamma args = Some vals ->
    FindMethodWithName CT (sctype receiver_type) method static_mdef ->
    method_signature_refinement CT
      (msignature runtime_mdef) (msignature static_mdef) ->
    sqtype (mret (msignature static_mdef)) = RDM ->
    sqtype (mret (msignature runtime_mdef)) = Mut ->
    sqtype (mreceiver (msignature runtime_mdef)) = RO ->
    forall root,
      ~ typed_root RDM
          (mreceiver (msignature runtime_mdef) ::
            mparams (msignature runtime_mdef))
          (mkr_env (Iot receiver_location :: vals)) root.
Proof.
  intros CT sGamma mt rGamma h x method receiver args vals
    receiver_location receiver_type runtime_mdef static_mdef Hwf Htyping
    Hsafe Hreceiver_type Hreceiver_value Hargs Hfind_static Hrefine
    Hstatic_return Hruntime_return Hruntime_receiver root
    [variable [T [Htype [Hvalue Hrdm]]]].
  inversion Htyping; subst.
  - destruct Hsafe as [Hrs | Hts]; subst;
      destruct Hscope as [Has | [Hcs _]]; discriminate.
  - assert (Ty = receiver_type) by congruence. subst Ty.
    have Hstatic_method :=
      find_method_with_name_deterministic CT (sctype receiver_type) method
        mdef static_mdef Hfind_m Hfind_static.
    subst mdef.
    destruct variable as [|i].
    + simpl in Htype. injection Htype as <-.
      rewrite Hruntime_receiver in Hrdm. discriminate.
    + simpl in Htype, Hvalue.
      unfold static_getType in Htype.
      assert (Hi_runtime :
          i < length (mparams (msignature runtime_mdef))).
      { apply nth_error_Some. rewrite Htype. discriminate. }
      have Hrefine_lengths :=
        method_signature_refinement_params_length CT
          (msignature runtime_mdef) (msignature static_mdef) Hrefine.
      assert (Hi_static :
          i < length (mparams (msignature static_mdef))) by lia.
      destruct (nth_error_Some_exists
        (mparams (msignature static_mdef)) i Hi_static) as
        [static_parameter Hstatic_parameter].
      have Hstatic_parameter_bot :
          sqtype static_parameter = Bot.
      { eapply method_signature_refinement_mut_return_rdm_parameter_parent_bot;
          eauto. }
      have Harg_lengths := Forall2_length Harg_sub.
      assert (Hi_argtypes : i < length argtypes) by lia.
      destruct (nth_error_Some_exists argtypes i Hi_argtypes)
        as [argument_type Hargument_type].
      have Hsub_i := Harg_sub.
      eapply Forall2_nth_error with
        (i := i) (a := argument_type) (b := static_parameter) in Hsub_i;
        [|exact Hargument_type|exact Hstatic_parameter].
      destruct (static_getType_list_nth_zs _ args argtypes i argument_type
        Hget_args Hargument_type) as
        [argument [Hargument_index Hargument_static]].
      destruct (runtime_lookup_list_nth_zs rGamma args vals i (Iot root)
        Hargs Hvalue) as
        [runtime_argument [Hruntime_index Hargument_value]].
      rewrite Hargument_index in Hruntime_index.
      injection Hruntime_index as <-.
      apply qualified_type_subtype_q_subtype in Hsub_i.
      unfold vpa_mutability_tt_readonly_state in Hsub_i.
      rewrite Hstatic_parameter_bot in Hsub_i. simpl in Hsub_i.
      have Hargument_not_bot :=
        wf_config_nonnull_variable_not_bot CT sGamma rGamma h argument
          argument_type root Hwf Hargument_static Hargument_value.
      destruct (sqtype receiver_type);
        destruct (sqtype argument_type) eqn:Hargument_q;
        simpl in Hsub_i;
        inversion Hsub_i;
        subst;
        try congruence.
Qed.

(** The flexible RDM-to-Mut refinement gives a stronger entry fact than
    immutable authority alone: the dynamic frame has neither mutable nor RDM
    roots.  Consequently it has no capability root under either runtime
    authority. *)
Lemma safe_signature_without_rdm_has_no_capability_root :
  forall msig rGamma authority root,
    signature_has_no_mutable_roots msig ->
    (forall location,
      ~ typed_root RDM (mreceiver msig :: mparams msig) rGamma location) ->
    ~ frame_capability_root
        (mk_watched_frame authority
          (mreceiver msig :: mparams msig) rGamma) root.
Proof.
  intros msig rGamma authority root [Hreceiver_safe Hparams_safe] Hno_rdm
    [variable [T [Htype [Hvalue Hcapability]]]].
  unfold capability_in_context in Hcapability.
  destruct Hcapability as [Hmut | [Hrdm Hauthority]].
  - destruct variable as [|parameter].
    + simpl in Htype. injection Htype as <-.
      unfold is_nonmutable_qualifier in Hreceiver_safe.
      rewrite Hmut in Hreceiver_safe.
      destruct Hreceiver_safe as
        [Hbad | [Hbad | [Hbad | Hbad]]]; discriminate.
    + simpl in Htype. unfold static_getType in Htype.
      have Hparameter_safe : is_nonmutable_qualifier (sqtype T).
      { exact (Forall_nth_error _ _ _ _ Hparams_safe Htype). }
      unfold is_nonmutable_qualifier in Hparameter_safe.
      rewrite Hmut in Hparameter_safe.
      destruct Hparameter_safe as
        [Hbad | [Hbad | [Hbad | Hbad]]]; discriminate.
  - apply (Hno_rdm root).
    exists variable, T. repeat split; assumption.
Qed.

Lemma channel_free_boundary_from_safe_signature_without_rdm :
  forall caller receiver_view msig rGamma return_var result_q return_q
    entry_cutoff origins,
    signature_has_no_mutable_roots msig ->
    (forall location,
      ~ typed_root RDM (mreceiver msig :: mparams msig) rGamma location) ->
    entry_ownership_channel_free
      (mk_watched_call_boundary caller
        (mreceiver msig :: mparams msig) rGamma receiver_view return_var
        result_q return_q entry_cutoff origins).
Proof.
  intros caller receiver_view msig rGamma return_var result_q return_q
    entry_cutoff origins Hsafe Hno_rdm.
  split.
  - intros root Hroot.
    eapply safe_signature_without_rdm_has_no_capability_root
      with (msig := msig) (rGamma := rGamma)
        (authority := call_authority caller.(frame_authority) receiver_view)
        (root := root); eauto.
  - exact Hno_rdm.
Qed.

(** Confinement is directional, but an execution cannot create the reverse
    half of an RDM-component edge from an old unreachable object into the
    fresh part of the heap.  Such an old source object is unchanged, and the
    initial well-formed heap could not already contain a pointer to a location
    beyond its domain. *)
Lemma eval_fresh_mutable_adjacent_is_fresh_or_protected :
  forall CT sGamma rGamma h stmt rGamma' h' fresh next,
    wf_r_config CT sGamma rGamma h ->
    eval_stmt CT rGamma h stmt OK rGamma' h' ->
    dom h <= fresh ->
    mutable_adjacent CT h' fresh next ->
    dom h <= next \/
    In Loc (reachable_locations_from_initial_env h rGamma) next.
Proof.
  intros CT sGamma rGamma h stmt rGamma' h' fresh next Hwf Heval
    Hfresh [Hforward | Hbackward].
  - have Hinitial := initial_state_is_confined CT sGamma rGamma h Hwf.
    have Hfinal := eval_stmt_preserves_confinement CT rGamma h stmt OK
      rGamma' h' (reachable_locations_from_initial_env h rGamma) (dom h)
      (Nat.le_refl _) Hinitial Heval.
    destruct Hfinal as [_ Hheap].
    have Hraw : raw_heap_edge h' fresh next.
    { inversion Hforward; subst. exists o, f. split; assumption. }
    destruct (Hheap fresh next (ltac:(right; exact Hfresh)) Hraw)
      as [Hreachable | Hnext_fresh].
    + right. exact Hreachable.
    + left. exact Hnext_fresh.
  - destruct (le_lt_dec (dom h) next) as [Hnext_fresh | Hnext_old].
    + left. exact Hnext_fresh.
    + destruct (reachable_locations_from_initial_env_dec h rGamma next)
        as [Hnext_protected | Hnext_outside].
      * right. exact Hnext_protected.
      * exfalso.
        inversion Hbackward as
          [source target final_obj field D fdef Hfinal_obj Hfield
            Hbase Hfield_def Hrdm]; subst.
        destruct (runtime_getObj_Some h next ltac:(lia)) as
          [old_type [old_fields Hold_obj]].
        destruct old_type as [old_runtime_q old_class].
        destruct (runtime_preserves_r_type_heap CT rGamma h next
          (mkruntime_type old_runtime_q old_class) h'
          old_fields stmt rGamma' Hold_obj Heval) as
          [final_fields Hfinal_same_type].
        rewrite Hfinal_obj in Hfinal_same_type.
        injection Hfinal_same_type as Hfinal_fields.
        subst final_obj.
        have Hfields_unchanged := confined_eval_preserves_old_object CT
          rGamma h stmt rGamma' h'
          (reachable_locations_from_initial_env h rGamma) (dom h) next
          old_class old_runtime_q old_fields final_fields
          (Nat.le_refl _) (initial_state_is_confined CT sGamma rGamma h Hwf)
          Heval Hold_obj Hfinal_obj Hnext_old.
        assert (Hnot_reachable :
          ~ In Loc (reachable_locations_from_initial_env h rGamma) next).
        { exact Hnext_outside. }
        specialize (Hfields_unchanged Hnot_reachable).
        subst final_fields.
        have Hinitial_raw : raw_heap_edge h next fresh.
        { exists (mkObj (mkruntime_type old_runtime_q old_class) old_fields),
            field.
          split; assumption. }
        have Hheap_wf : wf_heap CT h := proj1 (proj2 Hwf).
        have Hfresh_old := wf_raw_edge_target_dom CT h next fresh
          Hheap_wf Hinitial_raw.
        lia.
Qed.

Lemma caller_post_rdm_root_origin :
  forall CT caller_senv caller_renv h destination destination_type
    return_location root,
    wf_r_config CT caller_senv caller_renv h ->
    static_getType caller_senv destination = Some destination_type ->
    typed_root RDM caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) root ->
    typed_root RDM caller_senv caller_renv root \/
    (root = return_location /\ sqtype destination_type = RDM).
Proof.
  intros CT caller_senv caller_renv h destination destination_type
    return_location root Hwf Hdestination
    [variable [T [Htype [Hvalue Hrdm]]]].
  destruct (Nat.eq_dec variable destination) as [Heq | Hneq].
  - subst variable. rewrite Hdestination in Htype. injection Htype as <-.
    have Hdestination_dom := Hdestination.
    apply static_getType_dom in Hdestination_dom.
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [_ [_ [Hlength Hcorr]]]]].
    assert (Hruntime_dom : destination < dom (vars caller_renv)) by lia.
    have Hupdated := runtime_getVal_update_same caller_renv destination
      (Iot return_location) Hruntime_dom.
    rewrite Hupdated in Hvalue. injection Hvalue as <-.
    right. split; [reflexivity|exact Hrdm].
  - have Hunchanged := runtime_getVal_update_diff caller_renv destination
      variable (Iot return_location).
    assert (Hdestination_variable : destination <> variable) by congruence.
    specialize (Hunchanged Hdestination_variable).
    rewrite Hunchanged in Hvalue.
    left. exists variable, T. repeat split; assumption.
Qed.

Lemma caller_post_rdm_root_reflects_before_pop :
  forall CT caller_senv caller_renv h destination destination_type receiver
    receiver_location receiver_type callee_senv callee_renv return_var
    body_return_type runtime_sig static_sig return_location root,
    wf_r_config CT caller_senv caller_renv h ->
    static_getType caller_senv destination = Some destination_type ->
    static_getType caller_senv receiver = Some receiver_type ->
    runtime_getVal caller_renv receiver = Some (Iot receiver_location) ->
    wf_r_config CT callee_senv callee_renv h ->
    static_getType callee_senv return_var = Some body_return_type ->
    runtime_getVal callee_renv return_var = Some (Iot return_location) ->
    qualified_type_subtype CT body_return_type (mret runtime_sig) ->
    method_signature_refinement CT runtime_sig static_sig ->
    qualified_type_subtype CT
      (vpa_mutability_tt_readonly_state receiver_type (mret static_sig))
      destination_type ->
    typed_root RDM caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) root ->
    typed_root RDM caller_senv caller_renv root \/
    (root = return_location /\
     sqtype destination_type = RDM /\
     sqtype receiver_type = RDM /\
     (typed_root RDM callee_senv callee_renv root \/
      typed_root Mut callee_senv callee_renv root \/
      typed_root Imm callee_senv callee_renv root)).
Proof.
  intros CT caller_senv caller_renv h destination destination_type receiver
    receiver_location receiver_type callee_senv callee_renv return_var
    body_return_type runtime_sig static_sig return_location root Hcaller_wf
    Hdestination Hreceiver_type Hreceiver_value Hcallee_wf Hreturn_type
    Hreturn_value Hbody_sub Hrefine Hresult_sub Hroot.
  destruct (caller_post_rdm_root_origin CT caller_senv caller_renv h
    destination destination_type return_location root Hcaller_wf Hdestination
    Hroot) as [Hold | [Hroot_return Hdestination_rdm]].
  - left. exact Hold.
  - right. subst root. split; [reflexivity|].
    split; [exact Hdestination_rdm|].
    have Hreceiver_nonbottom : sqtype receiver_type <> Bot.
    { eapply (wf_config_nonnull_variable_not_bot CT caller_senv caller_renv h
        receiver receiver_type receiver_location); eauto. }
    have Hreturn_nonbottom : sqtype body_return_type <> Bot.
    { eapply (wf_config_nonnull_variable_not_bot CT callee_senv callee_renv h
        return_var body_return_type return_location); eauto. }
    destruct (refined_call_rdm_result_classifies_body_return CT receiver_type
      body_return_type runtime_sig static_sig destination_type Hbody_sub
      Hrefine Hresult_sub Hreceiver_nonbottom Hreturn_nonbottom
      Hdestination_rdm) as [Hreceiver_rdm Hbody_cases].
    split; [exact Hreceiver_rdm|].
    destruct Hbody_cases as [Hbody_rdm | [Hbody_mut | Hbody_imm]].
    + left. exists return_var, body_return_type. repeat split; assumption.
    + right. left. exists return_var, body_return_type.
      repeat split; assumption.
    + right. right. exists return_var, body_return_type.
      repeat split; assumption.
Qed.

Definition call_pop_bridge
  (CT : class_table) (h : heap)
  (callee : watched_frame) (stack : list watched_boundary)
  (receiver_location return_location left right : Loc) : Prop :=
  (potential_connected CT h callee stack left receiver_location /\
   potential_connected CT h callee stack return_location right) \/
  (potential_connected CT h callee stack left return_location /\
   potential_connected CT h callee stack receiver_location right).

Definition call_pop_merge_safe
  (CT : class_table) (h : heap) (M Z : Ensemble Loc)
  (callee : watched_frame) (stack : list watched_boundary)
  (receiver_location return_location : Loc) : Prop :=
  forall capability protected,
    In Loc M capability ->
    In Loc Z protected ->
    ~ call_pop_bridge CT h callee stack receiver_location return_location
      capability protected.

Lemma potential_adjacent_after_call_pop_decomposes :
  forall CT h caller_authority caller_senv caller_renv stack destination
    destination_type receiver receiver_location receiver_type entry_senv
    entry_renv origins callee_senv callee_renv return_var body_return_type
    runtime_sig static_sig entry_cutoff return_location left right,
    wf_r_config CT caller_senv caller_renv h ->
    destination <> 0 ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    static_getType caller_senv destination = Some destination_type ->
    static_getType caller_senv receiver = Some receiver_type ->
    runtime_getVal caller_renv receiver = Some (Iot receiver_location) ->
    wf_r_config CT callee_senv callee_renv h ->
    static_getType callee_senv return_var = Some body_return_type ->
    runtime_getVal callee_renv return_var = Some (Iot return_location) ->
    qualified_type_subtype CT body_return_type (mret runtime_sig) ->
    method_signature_refinement CT runtime_sig static_sig ->
    qualified_type_subtype CT
      (vpa_mutability_tt_readonly_state receiver_type (mret static_sig))
      destination_type ->
    potential_adjacent CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      stack left right ->
    potential_connected CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_call_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type)
        return_var (sqtype destination_type) (sqtype (mret runtime_sig)) entry_cutoff origins :: stack)
      left right \/
    (sqtype destination_type = RDM /\
     call_pop_bridge CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_call_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type)
        return_var (sqtype destination_type) (sqtype (mret runtime_sig)) entry_cutoff origins :: stack)
      receiver_location return_location left right).
Proof.
  intros CT h caller_authority caller_senv caller_renv stack destination
    destination_type receiver receiver_location receiver_type entry_senv
    entry_renv origins callee_senv callee_renv return_var body_return_type
    runtime_sig static_sig entry_cutoff return_location left right Hcaller_wf
    Hdestination_not_receiver Hcaller_post_wf Hdestination Hreceiver_type Hreceiver_value
    Hcallee_wf Hreturn_type
    Hreturn_value Hbody_sub Hrefine Hresult_sub
    [Hheap | [Hframe | Hreturn]].
  - left. apply rt_step. left. exact Hheap.
  - destruct Hframe as
      [frame [Hlive [Hleft Hright]]].
    inversion Hlive; subst.
    + destruct (caller_post_rdm_root_reflects_before_pop CT caller_senv
        caller_renv h destination destination_type receiver receiver_location
        receiver_type callee_senv callee_renv return_var body_return_type
        runtime_sig static_sig return_location left Hcaller_wf Hdestination
        Hreceiver_type Hreceiver_value Hcallee_wf Hreturn_type Hreturn_value
        Hbody_sub Hrefine Hresult_sub Hleft) as
        [Hleft_old |
          [Hleft_return [Hdestination_rdm_left [Hview_left Hleft_body]]]];
      destruct (caller_post_rdm_root_reflects_before_pop CT caller_senv
        caller_renv h destination destination_type receiver receiver_location
        receiver_type callee_senv callee_renv return_var body_return_type
        runtime_sig static_sig return_location right Hcaller_wf Hdestination
        Hreceiver_type Hreceiver_value Hcallee_wf Hreturn_type Hreturn_value
        Hbody_sub Hrefine Hresult_sub Hright) as
        [Hright_old |
          [Hright_return
            [Hdestination_rdm_right [Hview_right Hright_body]]]].
      * left. eapply live_frame_rdm_roots_potentially_connected with
          (frame := mk_watched_frame caller_authority caller_senv caller_renv).
        -- apply live_frame_suspended with
             (boundary := mk_watched_call_boundary
               (mk_watched_frame caller_authority caller_senv caller_renv)
               entry_senv entry_renv (sqtype receiver_type)
               return_var (sqtype destination_type) (sqtype (mret runtime_sig)) entry_cutoff origins).
           left. reflexivity.
        -- exact Hleft_old.
        -- exact Hright_old.
      * right. split; [exact Hdestination_rdm_right|].
        left. subst right. split; [|apply rt_refl].
        eapply live_frame_rdm_roots_potentially_connected with
          (frame := mk_watched_frame caller_authority caller_senv caller_renv).
        -- apply live_frame_suspended with
             (boundary := mk_watched_call_boundary
               (mk_watched_frame caller_authority caller_senv caller_renv)
               entry_senv entry_renv (sqtype receiver_type)
               return_var (sqtype destination_type) (sqtype (mret runtime_sig)) entry_cutoff origins).
           left. reflexivity.
        -- exact Hleft_old.
        -- exists receiver, receiver_type. repeat split; assumption.
      * right. split; [exact Hdestination_rdm_left|].
        right. subst left. split; [apply rt_refl|].
        eapply live_frame_rdm_roots_potentially_connected with
          (frame := mk_watched_frame caller_authority caller_senv caller_renv).
        -- apply live_frame_suspended with
             (boundary := mk_watched_call_boundary
               (mk_watched_frame caller_authority caller_senv caller_renv)
               entry_senv entry_renv (sqtype receiver_type)
               return_var (sqtype destination_type) (sqtype (mret runtime_sig)) entry_cutoff origins).
           left. reflexivity.
        -- exists receiver, receiver_type. repeat split; assumption.
        -- exact Hright_old.
      * left. subst left right. apply rt_refl.
    + left. apply rt_step. right. left. exists boundary.(boundary_caller).
      split.
      * apply live_frame_suspended with (boundary := boundary).
        right. exact H.
      * split; assumption.
  - destruct Hreturn as
      [return_callee [return_boundary
        [Hlive [Hview [Hcallee_return [Hruntime Hroots]]]]]].
    inversion Hlive; subst.
    + destruct Hroots as [Hroots | Hroots].
      * destruct (caller_post_rdm_root_reflects_before_pop CT caller_senv
          caller_renv h destination destination_type receiver receiver_location
          receiver_type callee_senv callee_renv return_var body_return_type
          runtime_sig static_sig return_location left Hcaller_wf Hdestination
          Hreceiver_type Hreceiver_value Hcallee_wf Hreturn_type Hreturn_value
          Hbody_sub Hrefine Hresult_sub (proj1 Hroots)) as
          [Hleft_old |
            [Hleft_return
              [Hdestination_rdm [Hreceiver_rdm Hleft_body]]]].
        -- left. apply rt_step. right. right. exists
             (mk_watched_frame caller_authority caller_senv caller_renv),
             return_boundary.
           split; [constructor; constructor|]. split; [exact Hview|].
           split; [exact Hcallee_return|].
           split; [exact Hruntime|]. left. split;
             [exact Hleft_old|exact (proj2 Hroots)].
        -- subst left. right. split; [exact Hdestination_rdm|].
           right. split; [apply rt_refl|].
           assert (Hcaller_receiver_root :
             typed_root RDM caller_senv caller_renv receiver_location).
           { exists receiver, receiver_type. repeat split; assumption. }
           destruct (extract_receiver_from_wf_config CT caller_senv caller_renv
             h Hcaller_wf) as
             [this [runtime_q [Hthis [Hthis_dom Hthis_runtime]]]].
           have Hthis_value := get_this_var_mapping_runtime_getVal caller_renv
             this Hthis.
           have Hpost_this_value := runtime_getVal_update_diff caller_renv
             destination 0 (Iot return_location) Hdestination_not_receiver.
           rewrite Hthis_value in Hpost_this_value.
           have Hleft_runtime := typed_rdm_root_matches_receiver_runtime CT
             caller_senv
             (update_r_env_value caller_renv destination (Iot return_location))
             h this runtime_q return_location Hcaller_post_wf
             Hpost_this_value Hthis_runtime
             (proj1 Hroots).
           have Hreceiver_runtime := typed_rdm_root_matches_receiver_runtime CT
             caller_senv caller_renv h this runtime_q receiver_location
             Hcaller_wf Hthis_value Hthis_runtime Hcaller_receiver_root.
           apply rt_step. right. right. exists
             (mk_watched_frame caller_authority caller_senv caller_renv),
             return_boundary.
           split; [constructor; constructor|]. split; [exact Hview|].
           split; [exact Hcallee_return|].
           split.
           ++ rewrite Hreceiver_runtime. rewrite <- Hruntime.
              symmetry. exact Hleft_runtime.
           ++ left. split;
                [exact Hcaller_receiver_root|exact (proj2 Hroots)].
      * destruct (caller_post_rdm_root_reflects_before_pop CT caller_senv
          caller_renv h destination destination_type receiver receiver_location
          receiver_type callee_senv callee_renv return_var body_return_type
          runtime_sig static_sig return_location right Hcaller_wf Hdestination
          Hreceiver_type Hreceiver_value Hcallee_wf Hreturn_type Hreturn_value
          Hbody_sub Hrefine Hresult_sub (proj2 Hroots)) as
          [Hright_old |
            [Hright_return
              [Hdestination_rdm [Hreceiver_rdm Hright_body]]]].
        -- left. apply rt_step. right. right. exists
             (mk_watched_frame caller_authority caller_senv caller_renv),
             return_boundary.
           split; [constructor; constructor|]. split; [exact Hview|].
           split; [exact Hcallee_return|].
           split; [exact Hruntime|]. right. split;
             [exact (proj1 Hroots)|exact Hright_old].
        -- subst right. right. split; [exact Hdestination_rdm|].
           left. split; [|apply rt_refl].
           assert (Hcaller_receiver_root :
             typed_root RDM caller_senv caller_renv receiver_location).
           { exists receiver, receiver_type. repeat split; assumption. }
           destruct (extract_receiver_from_wf_config CT caller_senv caller_renv
             h Hcaller_wf) as
             [this [runtime_q [Hthis [Hthis_dom Hthis_runtime]]]].
           have Hthis_value := get_this_var_mapping_runtime_getVal caller_renv
             this Hthis.
           have Hpost_this_value := runtime_getVal_update_diff caller_renv
             destination 0 (Iot return_location) Hdestination_not_receiver.
           rewrite Hthis_value in Hpost_this_value.
           have Hright_runtime := typed_rdm_root_matches_receiver_runtime CT
             caller_senv
             (update_r_env_value caller_renv destination (Iot return_location))
             h this runtime_q return_location Hcaller_post_wf
             Hpost_this_value Hthis_runtime
             (proj2 Hroots).
           have Hreceiver_runtime := typed_rdm_root_matches_receiver_runtime CT
             caller_senv caller_renv h this runtime_q receiver_location
             Hcaller_wf Hthis_value Hthis_runtime Hcaller_receiver_root.
           apply rt_step. right. right. exists
             (mk_watched_frame caller_authority caller_senv caller_renv),
             return_boundary.
           split; [constructor; constructor|]. split; [exact Hview|].
           split; [exact Hcallee_return|].
           split.
           ++ transitivity (Some runtime_q).
              ** rewrite Hruntime. exact Hright_runtime.
              ** symmetry. exact Hreceiver_runtime.
           ++ right. split;
                [exact (proj1 Hroots)|exact Hcaller_receiver_root].
    + left. apply rt_step. right. right. exists return_callee, return_boundary.
      split; [constructor; constructor; exact H|].
      split; [exact Hview|].
      split; [exact Hcallee_return|].
      split; assumption.
Qed.

Lemma potential_connected_after_call_pop_decomposes :
  forall CT h caller_authority caller_senv caller_renv stack destination
    destination_type receiver receiver_location receiver_type entry_senv
    entry_renv origins callee_senv callee_renv return_var body_return_type
    runtime_sig static_sig entry_cutoff return_location left right,
    wf_r_config CT caller_senv caller_renv h ->
    destination <> 0 ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    static_getType caller_senv destination = Some destination_type ->
    static_getType caller_senv receiver = Some receiver_type ->
    runtime_getVal caller_renv receiver = Some (Iot receiver_location) ->
    wf_r_config CT callee_senv callee_renv h ->
    static_getType callee_senv return_var = Some body_return_type ->
    runtime_getVal callee_renv return_var = Some (Iot return_location) ->
    qualified_type_subtype CT body_return_type (mret runtime_sig) ->
    method_signature_refinement CT runtime_sig static_sig ->
    qualified_type_subtype CT
      (vpa_mutability_tt_readonly_state receiver_type (mret static_sig))
      destination_type ->
    potential_connected CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      stack left right ->
    potential_connected CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_call_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type)
        return_var (sqtype destination_type) (sqtype (mret runtime_sig)) entry_cutoff origins :: stack)
      left right \/
    (sqtype destination_type = RDM /\
     call_pop_bridge CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_call_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type)
        return_var (sqtype destination_type) (sqtype (mret runtime_sig)) entry_cutoff origins :: stack)
      receiver_location return_location left right).
Proof.
  intros CT h caller_authority caller_senv caller_renv stack destination
    destination_type receiver receiver_location receiver_type entry_senv
    entry_renv origins callee_senv callee_renv return_var body_return_type
    runtime_sig static_sig entry_cutoff return_location left right Hcaller_wf
    Hdestination_not_receiver Hcaller_post_wf Hdestination Hreceiver_type Hreceiver_value
    Hcallee_wf Hreturn_type
    Hreturn_value Hbody_sub Hrefine Hresult_sub Hconnected.
  induction Hconnected.
  - eapply potential_adjacent_after_call_pop_decomposes; eauto.
  - left. apply rt_refl.
  - destruct IHHconnected1 as
      [Hxy |
        [Hdestination_rdm1
          [[Hx_receiver Hreturn_y] | [Hx_return Hreceiver_y]]]];
      destruct IHHconnected2 as
      [Hyz |
        [Hdestination_rdm2
          [[Hy_receiver Hreturn_z] | [Hy_return Hreceiver_z]]]].
    + left. eapply potential_connected_trans; eauto.
    + right. split; [exact Hdestination_rdm2|]. left. split.
      * eapply potential_connected_trans; eauto.
      * exact Hreturn_z.
    + right. split; [exact Hdestination_rdm2|]. right. split.
      * eapply potential_connected_trans; eauto.
      * exact Hreceiver_z.
    + right. split; [exact Hdestination_rdm1|].
      left. split; [exact Hx_receiver|].
      eapply potential_connected_trans; eauto.
    + right. split; [exact Hdestination_rdm1|].
      left. split; [exact Hx_receiver|exact Hreturn_z].
    + left. eapply potential_connected_trans; eauto.
    + right. split; [exact Hdestination_rdm1|].
      right. split; [exact Hx_return|].
      eapply potential_connected_trans; eauto.
    + left. eapply potential_connected_trans; eauto.
    + right. split; [exact Hdestination_rdm1|].
      right. split; [exact Hx_return|exact Hreceiver_z].
Qed.

Definition authority_call_pop_bridge
  (CT : class_table) (h : heap)
  (callee : watched_frame) (stack : list watched_boundary)
  (receiver_location return_location left right : Loc) : Prop :=
  (authority_color_connected CT h callee stack left receiver_location /\
   authority_color_connected CT h callee stack return_location right) \/
  (authority_color_connected CT h callee stack left return_location /\
   authority_color_connected CT h callee stack receiver_location right).

Lemma potential_history_leave_call :
  forall CT P Z cutoff caller_authority caller_senv caller_renv caller_h stack
    destination destination_type receiver receiver_location receiver_type
    entry_senv entry_renv origins callee_senv callee_renv callee_h return_var
    body_return_type runtime_sig static_sig return_location,
    zone_env_safe Z caller_senv caller_renv ->
    env_is_confined P cutoff caller_renv ->
    wf_r_config CT caller_senv caller_renv caller_h ->
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    static_getType caller_senv receiver = Some receiver_type ->
    runtime_getVal caller_renv receiver = Some (Iot receiver_location) ->
    static_getType callee_senv return_var = Some body_return_type ->
    runtime_getVal callee_renv return_var = Some (Iot return_location) ->
    qualified_type_subtype CT body_return_type (mret runtime_sig) ->
    method_signature_refinement CT runtime_sig static_sig ->
    qualified_type_subtype CT
      (vpa_mutability_tt_readonly_state receiver_type (mret static_sig))
      destination_type ->
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_call_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type)
        return_var (sqtype destination_type) (sqtype (mret runtime_sig)) (dom caller_h) origins :: stack)
      callee_h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location))
      callee_h ->
    (sqtype destination_type = RDM ->
    call_pop_merge_safe CT callee_h
      (live_capability_set CT callee_h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination
            (Iot return_location)))
        stack)
      Z
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_call_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type)
        return_var (sqtype destination_type) (sqtype (mret runtime_sig)) (dom caller_h) origins :: stack)
      receiver_location return_location) ->
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      stack callee_h.
Proof.
  intros CT P Z cutoff caller_authority caller_senv caller_renv caller_h stack
    destination destination_type receiver receiver_location receiver_type
    entry_senv entry_renv origins callee_senv callee_renv callee_h return_var
    body_return_type runtime_sig static_sig return_location Hcaller_zone
    Hcaller_confined Hcaller_wf Hdestination_not_receiver Hdestination_type
    Hreceiver_type Hreceiver_value Hreturn_type Hreturn_value Hbody_sub
    Hrefine Hresult_sub [Hlive [Hpotential Hcutoffs]] Hcaller_post_wf
    Hmerge_safe.
  set (callee_frame := mk_watched_frame
    (call_authority caller_authority (sqtype receiver_type))
    callee_senv callee_renv).
  set (caller_boundary := mk_watched_call_boundary
    (mk_watched_frame caller_authority caller_senv caller_renv)
    entry_senv entry_renv (sqtype receiver_type)
    return_var (sqtype destination_type) (sqtype (mret runtime_sig)) (dom caller_h) origins).
  set (caller_post := mk_watched_frame caller_authority caller_senv
    (update_r_env_value caller_renv destination (Iot return_location))).
  have Hpre_frames : live_frames_wf CT callee_h callee_frame
      (caller_boundary :: stack) := proj1 (proj2 Hlive).
  have Hcallee_wf : wf_r_config CT callee_senv callee_renv callee_h :=
    proj1 Hpre_frames.
  have Hcaller_current_wf : wf_r_config CT caller_senv caller_renv callee_h.
  { have Hcaller_boundary_wf := Forall_inv (proj2 Hpre_frames).
    change (wf_r_config CT caller_senv caller_renv callee_h)
      in Hcaller_boundary_wf.
    exact Hcaller_boundary_wf. }
  set (Mpre := live_capability_set CT callee_h callee_frame
    (caller_boundary :: stack)).
  set (Mpost := live_capability_set CT callee_h caller_post stack).
  have Hpre_sounds : live_frames_authority_sound callee_h callee_frame
      (caller_boundary :: stack) := proj1 (proj2 (proj2 Hlive)).
  have Hcaller_sound :
      authority_context_sound callee_h caller_renv caller_authority.
  { exact (Forall_inv (proj2 Hpre_sounds)). }
  have Hpost_in_pre : Included Loc Mpost Mpre.
  { intros location Hlocation.
    unfold Mpost, caller_post in Hlocation.
    unfold Mpre, callee_frame, caller_boundary.
    eapply call_return_live_reachability_reflects_before_pop with
      (caller_h := caller_h) (destination_type := destination_type)
      (receiver := receiver) (receiver_location := receiver_location)
      (receiver_type := receiver_type) (entry_senv := entry_senv)
      (entry_renv := entry_renv) (origins := origins)
      (callee_senv := callee_senv) (callee_renv := callee_renv)
      (return_var := return_var) (body_return_type := body_return_type)
      (runtime_sig := runtime_sig) (static_sig := static_sig)
      (return_location := return_location); eauto. }
  assert (Hpost_separated :
    potential_colors_separated CT callee_h Mpost Z caller_post stack).
  { intros capability protected Hcapability Hprotected Hconnected.
    unfold caller_post, callee_frame, caller_boundary in *.
    destruct (potential_connected_after_call_pop_decomposes CT callee_h
      caller_authority caller_senv caller_renv stack destination
      destination_type receiver receiver_location receiver_type entry_senv
      entry_renv origins callee_senv callee_renv return_var body_return_type
      runtime_sig static_sig (dom caller_h) return_location capability protected
      Hcaller_current_wf Hdestination_not_receiver Hcaller_post_wf
      Hdestination_type Hreceiver_type Hreceiver_value Hcallee_wf Hreturn_type
      Hreturn_value Hbody_sub Hrefine Hresult_sub Hconnected)
      as [Hreflected | [Hdestination_rdm Hbridge]].
    - exact (Hpotential capability protected (Hpost_in_pre _ Hcapability)
        Hprotected Hreflected).
    - exact (Hmerge_safe Hdestination_rdm capability protected Hcapability
        Hprotected Hbridge). }
  have Hcaller_components :
      component_colors_separated CT callee_h Mpost Z.
  { eapply potential_colors_imply_component_colors; eauto. }
  have Hcaller_colors :
      watched_frame_colors CT callee_h Mpost Z caller_post.
  { eapply potential_colors_imply_active_colors; eauto. }
  have Hlive_post := live_history_leave_call_given_caller_colors CT P Z cutoff
    caller_authority caller_senv caller_renv caller_h stack destination
    destination_type receiver receiver_location receiver_type entry_senv
    entry_renv origins callee_senv callee_renv callee_h return_var
    body_return_type runtime_sig static_sig return_location Hcaller_zone
    Hcaller_confined Hcaller_wf Hdestination_not_receiver Hdestination_type
    Hreceiver_type Hreceiver_value Hreturn_type Hreturn_value Hbody_sub
    Hrefine Hresult_sub Hlive Hcaller_post_wf
    (ltac:(unfold Mpost, caller_post in Hcaller_components;
      exact Hcaller_components))
    (ltac:(unfold Mpost, caller_post in Hcaller_colors;
      exact Hcaller_colors)).
  split; [exact Hlive_post|]. split.
  intros capability protected Hcapability Hprotected Hconnected.
  apply (Hpost_separated capability protected).
  - exact Hcapability.
  - exact Hprotected.
  - exact Hconnected.
  - exact (Forall_inv_tail Hcutoffs).
Qed.

Lemma caller_null_rdm_roots_descend :
  forall CT caller_senv caller_renv h destination destination_type,
    wf_r_config CT caller_senv caller_renv h ->
    static_getType caller_senv destination = Some destination_type ->
    rdm_roots_descend_from CT h caller_senv caller_renv caller_senv
      (update_r_env_value caller_renv destination Null_a).
Proof.
  intros CT caller_senv caller_renv h destination destination_type Hwf
    Hdestination root [variable [T [Htype [Hvalue Hrdm]]]].
  destruct (Nat.eq_dec variable destination) as [Heq | Hneq].
  - subst variable.
    have Hdestination_dom := Hdestination.
    apply static_getType_dom in Hdestination_dom.
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [_ [_ [Hlength Hcorr]]]]].
    assert (Hruntime_dom : destination < dom (vars caller_renv)) by lia.
    have Hupdated := runtime_getVal_update_same caller_renv destination
      Null_a Hruntime_dom.
    rewrite Hupdated in Hvalue. discriminate.
  - have Hunchanged := runtime_getVal_update_diff caller_renv destination
      variable Null_a.
    assert (Hdestination_variable : destination <> variable) by congruence.
    specialize (Hunchanged Hdestination_variable).
    rewrite Hunchanged in Hvalue.
    exists root. split.
    + exists variable, T. repeat split; assumption.
    + constructor.
Qed.

Lemma potential_adjacent_before_call_pop_included :
  forall CT h caller_frame stack callee_frame entry_senv entry_renv
    receiver_view return_var result_qualifier callee_return_qualifier
    entry_cutoff origins left right,
    potential_adjacent CT h caller_frame stack left right ->
    potential_adjacent CT h callee_frame
      (mk_watched_call_boundary caller_frame entry_senv entry_renv receiver_view
        return_var result_qualifier callee_return_qualifier entry_cutoff
        origins :: stack) left right.
Proof.
  intros CT h caller_frame stack callee_frame entry_senv entry_renv
    receiver_view return_var result_qualifier callee_return_qualifier
    entry_cutoff origins left right [Hheap | [Hframe | Hreturn]].
  - left. exact Hheap.
  - right. left.
    destruct Hframe as
      [frame [Hlive [Hleft Hright]]].
    exists frame. split.
    + inversion Hlive; subst.
      * apply live_frame_suspended with
          (boundary := mk_watched_call_boundary frame entry_senv entry_renv
            receiver_view return_var result_qualifier
            callee_return_qualifier entry_cutoff origins).
        left. reflexivity.
      * apply live_frame_suspended with (boundary := boundary).
        right. exact H.
    + split; assumption.
  - right. right.
    destruct Hreturn as
      [return_callee [return_boundary
        [Hlive [Hview [Hcallee_return [Hruntime Hroots]]]]]].
    exists return_callee, return_boundary. split.
    + constructor. exact Hlive.
    + split; [exact Hview|].
      split; [exact Hcallee_return|].
      split; assumption.
Qed.

Lemma potential_connected_before_call_pop_included :
  forall CT h caller_frame stack callee_frame entry_senv entry_renv
    receiver_view return_var result_qualifier callee_return_qualifier
    entry_cutoff origins left right,
    potential_connected CT h caller_frame stack left right ->
    potential_connected CT h callee_frame
      (mk_watched_call_boundary caller_frame entry_senv entry_renv receiver_view
        return_var result_qualifier callee_return_qualifier entry_cutoff
        origins :: stack) left right.
Proof.
  intros CT h caller_frame stack callee_frame entry_senv entry_renv
    receiver_view return_var result_qualifier callee_return_qualifier
    entry_cutoff origins left right Hconnected.
  eapply potential_connected_map_edges; [|exact Hconnected].
  intros edge_left edge_right Hedge. apply rt_step.
  eapply potential_adjacent_before_call_pop_included; eauto.
Qed.

Lemma potential_history_leave_call_null :
  forall CT P Z cutoff caller_authority caller_senv caller_renv caller_h stack
    destination destination_type receiver_type entry_senv entry_renv return_var
    callee_return_q origins
    callee_senv callee_renv callee_h,
    zone_env_safe Z caller_senv caller_renv ->
    env_is_confined P cutoff caller_renv ->
    wf_r_config CT caller_senv caller_renv caller_h ->
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_call_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type)
        return_var (sqtype destination_type) callee_return_q
        (dom caller_h) origins :: stack)
      callee_h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination Null_a) callee_h ->
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination Null_a)) stack callee_h.
Proof.
  intros CT P Z cutoff caller_authority caller_senv caller_renv caller_h stack
    destination destination_type receiver_type entry_senv entry_renv return_var
    callee_return_q origins
    callee_senv callee_renv callee_h Hcaller_zone Hcaller_env Hcaller_wf
    Hdestination_not_receiver Hdestination_type
    [Hlive [Hpotential Hcutoffs]]
    Hcaller_post_wf.
  set (callee_frame := mk_watched_frame
    (call_authority caller_authority (sqtype receiver_type))
    callee_senv callee_renv).
  set (caller_boundary := mk_watched_call_boundary
    (mk_watched_frame caller_authority caller_senv caller_renv)
    entry_senv entry_renv (sqtype receiver_type)
    return_var (sqtype destination_type) callee_return_q
    (dom caller_h) origins).
  set (caller_old := mk_watched_frame caller_authority caller_senv caller_renv).
  set (caller_post := mk_watched_frame caller_authority caller_senv
    (update_r_env_value caller_renv destination Null_a)).
  have Hpre_frames : live_frames_wf CT callee_h callee_frame
      (caller_boundary :: stack) := proj1 (proj2 Hlive).
  have Hcaller_current_wf : wf_r_config CT caller_senv caller_renv callee_h.
  { have Hcaller_boundary_wf := Forall_inv (proj2 Hpre_frames).
    change (wf_r_config CT caller_senv caller_renv callee_h)
      in Hcaller_boundary_wf.
    exact Hcaller_boundary_wf. }
  have Hdescend := caller_null_rdm_roots_descend CT caller_senv caller_renv
    callee_h destination destination_type Hcaller_current_wf Hdestination_type.
  set (Mpre := live_capability_set CT callee_h callee_frame
    (caller_boundary :: stack)).
  assert (Hpost_separated_pre :
    potential_colors_separated CT callee_h Mpre Z caller_post stack).
  { intros capability protected Hcapability Hprotected Hconnected.
    destruct (potential_connected_after_active_descent_reflects CT callee_h
      caller_authority caller_senv caller_renv caller_senv
      (update_r_env_value caller_renv destination Null_a) stack capability
      protected Hcaller_current_wf Hdescend Hconnected) as
      [Hold_connected | [anchor [Hanchor_live Hanchor_path]]].
    - apply (Hpotential capability protected Hcapability Hprotected).
      unfold callee_frame, caller_boundary, caller_old.
      eapply potential_connected_before_call_pop_included; eauto.
    - have Hanchor_pre : In Loc Mpre anchor.
      { unfold Mpre, caller_post, callee_frame, caller_boundary in *.
        eapply call_return_null_live_reachability_reflects_before_pop with
          (caller_h := caller_h) (destination_type := destination_type);
          eauto. }
      apply (Hpotential anchor protected Hanchor_pre Hprotected).
      unfold callee_frame, caller_boundary, caller_old.
      eapply potential_connected_before_call_pop_included; eauto. }
  set (Mpost := live_capability_set CT callee_h caller_post stack).
  have Hpost_in_pre : Included Loc Mpost Mpre.
  { intros location Hlocation.
    unfold Mpost, caller_post in Hlocation.
    unfold Mpre, callee_frame, caller_boundary.
    eapply call_return_null_live_reachability_reflects_before_pop with
      (caller_h := caller_h) (destination_type := destination_type); eauto. }
  have Hcaller_components_pre :
      component_colors_separated CT callee_h Mpre Z.
  { eapply potential_colors_imply_component_colors; eauto. }
  have Hcaller_components :
      component_colors_separated CT callee_h Mpost Z.
  { intros capability protected Hcapability Hprotected Hconnected.
    eapply Hcaller_components_pre; eauto. }
  have Hcaller_colors_pre :
      watched_frame_colors CT callee_h Mpre Z caller_post.
  { eapply potential_colors_imply_active_colors; eauto. }
  have Hcaller_colors :
      watched_frame_colors CT callee_h Mpost Z caller_post.
  { intros capability_root zone_root Hcapability_root
      [capability [Hcapability Hcapability_connected]]
      Hzone_root Hzone_connected.
    eapply Hcaller_colors_pre with
      (capability_root := capability_root) (zone_root := zone_root); eauto.
    exists capability. split; [eapply Hpost_in_pre; eauto|].
    exact Hcapability_connected. }
  have Hlive_post := live_history_leave_call_null_given_caller_colors CT P Z
    cutoff caller_authority caller_senv caller_renv caller_h stack destination
    destination_type receiver_type entry_senv entry_renv return_var
    callee_return_q origins callee_senv callee_renv callee_h Hcaller_zone
    Hcaller_env Hcaller_wf
    Hdestination_not_receiver Hdestination_type Hlive Hcaller_post_wf
    (ltac:(unfold Mpost, caller_post in Hcaller_components;
      exact Hcaller_components))
    (ltac:(unfold Mpost, caller_post in Hcaller_colors;
      exact Hcaller_colors)).
  split; [exact Hlive_post|]. split.
  intros capability protected Hcapability Hprotected Hconnected.
  apply (Hpost_separated_pre capability protected).
  - unfold Mpre, caller_post, callee_frame, caller_boundary.
    eapply call_return_null_live_reachability_reflects_before_pop with
      (caller_h := caller_h) (destination_type := destination_type); eauto.
  - exact Hprotected.
  - exact Hconnected.
  - exact (Forall_inv_tail Hcutoffs).
Qed.

Lemma safe_typed_call_target_method_safe :
  forall CT sGamma mt rGamma h x method y args sGamma' ly cy runtime_mdef,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    readonly_state_method_scope (mscope (msignature runtime_mdef)).
Proof.
  intros CT sGamma mt rGamma h x method y args sGamma' ly cy runtime_mdef
    Hwf Htyping Hsafe Hvalue Hbase Hfind.
  inversion Htyping; subst.
  - destruct Hsafe as [Hrs | Hts]; subst mt;
      destruct Hscope as [Has | [Hcs Hcallee]]; discriminate.
  - have Hscope_eq :
      mscope (msignature runtime_mdef) = mscope (msignature mdef).
    { eapply runtime_call_scope_eq; eauto. }
    rewrite Hscope_eq.
    eapply readonly_state_submethod; eauto.
Qed.

Lemma safe_typed_call_static_result :
  forall CT sGamma mt rGamma h x method y args sGamma' ly cy runtime_mdef,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    exists destination_type receiver_type static_mdef,
      sGamma' = sGamma /\
      x <> 0 /\
      static_getType sGamma x = Some destination_type /\
      static_getType sGamma y = Some receiver_type /\
      FindMethodWithName CT (sctype receiver_type) method static_mdef /\
      method_signature_refinement CT
        (msignature runtime_mdef) (msignature static_mdef) /\
      qualified_type_subtype CT
        (vpa_mutability_tt_readonly_state receiver_type
          (mret (msignature static_mdef))) destination_type /\
      (qualified_type_subtype CT receiver_type
        (vpa_mutability_tt_readonly_state receiver_type
          (mreceiver (msignature static_mdef))) \/
       (sqtype receiver_type = RO /\
        sqtype (mreceiver (msignature static_mdef)) = RDM /\
        base_subtype CT (sctype receiver_type)
          (sctype (mreceiver (msignature static_mdef))))).
Proof.
  intros CT sGamma mt rGamma h x method y args sGamma' ly cy runtime_mdef
    Hwf Htyping Hsafe Hvalue Hbase Hfind.
  inversion Htyping; subst.
  - destruct Hsafe as [Hrs | Hts]; subst mt;
      destruct Hscope as [Has | [Hcs Hcallee]]; discriminate.
  - exists Tx, Ty, mdef. repeat split; try assumption;
      try (exact Hrcv_sub).
    eapply runtime_call_signature_refines; eauto.
Qed.

Lemma safe_call_callee_owned_reflects_to_caller :
  forall CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty location,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    frame_owned_location CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals))) location ->
    frame_owned_location CT h
      (mk_watched_frame caller_authority sGamma rGamma) location.
Proof.
  intros CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty location Hwf Htyping Hscope Hgety Hvalue Hbase
    Hfind Hargs [root [Hroot Hreachable]].
  exists root. split; [|exact Hreachable].
  eapply safe_call_callee_capability_root_reflects_to_caller; eauto.
Qed.

Lemma safe_call_callee_mutable_authority_root_reflects_to_caller :
  forall CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty root,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    mutable_authority_root
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals))) h root ->
    mutable_authority_root
      (mk_watched_frame caller_authority sGamma rGamma) h root \/
    (sqtype Ty = RO /\ root = ly /\ typed_root RO sGamma rGamma root /\
     r_muttype h root = Some Mut_r).
Proof.
  intros CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty root Hwf Htyping Hscope Hgety Hvalue Hbase
    Hfind Hargs [Hmut | [Hrdm Hruntime]].
  - left. left. eapply safe_call_callee_mut_root_origin; eauto.
  - destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x
      method y args sGamma' vals ly cy runtime_mdef root Hwf Htyping Hscope
      Hvalue Hbase Hfind Hargs Hrdm) as
      [caller_T [Hcaller_type [[Hshape Hcaller_root] |
        [Hro [Hrooteq Hro_root]]]]].
    + assert (caller_T = Ty) by congruence. subst caller_T.
      destruct Hshape as [Hcaller_mut | [Hcaller_imm | Hcaller_rdm]].
      * left. left. rewrite Hcaller_mut in Hcaller_root. exact Hcaller_root.
      * have Himmutable := typed_imm_root_runtime_immutable CT sGamma rGamma
          h root Hwf (ltac:(rewrite Hcaller_imm in Hcaller_root;
            exact Hcaller_root)).
        congruence.
      * left. right. split.
        -- rewrite Hcaller_rdm in Hcaller_root. exact Hcaller_root.
        -- exact Hruntime.
    + assert (caller_T = Ty) by congruence. subst caller_T.
      right. split; [exact Hro|]. split; [exact Hrooteq|].
      split; [exact Hro_root | exact Hruntime].
Qed.

Lemma safe_call_prospective_step_covered_by_caller :
  forall CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty source target,
    wf_r_config CT sGamma rGamma h ->
    authority_context_sound h rGamma caller_authority ->
    wf_r_config CT
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    prospective_location_covered_by_frame CT h
      (mk_watched_frame caller_authority sGamma rGamma) source ->
    frozen_caller_authority_step CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals)))
      (FlowProspective, source) (FlowProspective, target) ->
    prospective_location_covered_by_frame CT h
      (mk_watched_frame caller_authority sGamma rGamma) target.
Proof.
  intros CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty source target Hwf Hsound Hcallee_wf Htyping
    Hscope Hgety Hvalue Hbase Hfind Hargs Hsource Hstep.
  have Hsource_runtime := prospective_location_covered_by_frame_runtime_mutable
    CT h (mk_watched_frame caller_authority sGamma rGamma) source Hwf Hsound
    Hsource.
  inversion Hstep; subst.
  - destruct Hsource as [root [Hroot Hpath]]. exists root. split;
      [exact Hroot|].
    eapply rt_trans; [exact Hpath|]. apply rt_step.
    apply frozen_caller_prospective_retained. exact H1.
  - destruct Hsource as [root [Hroot Hpath]]. exists root. split;
      [exact Hroot|].
    eapply rt_trans; [exact Hpath|]. apply rt_step.
    apply frozen_caller_prospective_rdm_backward. exact H1.
  - have Htarget_runtime : r_muttype h target = Some Mut_r.
    { destruct (active_rdm_roots_share_runtime_context CT
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals)) h source target Hcallee_wf H1 H2) as
        [runtime_q [Hsource_context Htarget_context]].
      rewrite Hsource_runtime in Hsource_context.
      injection Hsource_context as <-. exact Htarget_context. }
    destruct (safe_call_callee_mutable_authority_root_reflects_to_caller
        CT caller_authority sGamma mt rGamma h x method y args sGamma' vals
        ly cy runtime_mdef Ty target Hwf Htyping Hscope Hgety Hvalue Hbase
        Hfind Hargs (or_intror (conj H2 Htarget_runtime))) as
      [Hcaller_root | [Hro [Htarget_eq [Hro_root Hro_runtime]]]].
    + exists target. split; [exact Hcaller_root | apply rt_refl].
    + destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x
        method y args sGamma' vals ly cy runtime_mdef source Hwf Htyping
        Hscope Hvalue Hbase Hfind Hargs H1) as
        [Ts [Hgets [[Hshape_s _] | [_ [Hsource_eq _]]]]].
      * exfalso. assert (Ts = Ty) by congruence. subst Ts.
        destruct Hshape_s as [Hq | [Hq | Hq]]; congruence.
      * rewrite Hsource_eq in Hsource. rewrite Htarget_eq. exact Hsource.
Qed.

Definition prospective_state_covered_by_frame
  (CT : class_table) (h : heap) (frame : watched_frame)
  (state : authority_flow_state) : Prop :=
  fst state = FlowProspective /\
  prospective_location_covered_by_frame CT h frame (snd state).

Lemma safe_call_prospective_state_step_covered_by_caller :
  forall CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty source target,
    wf_r_config CT sGamma rGamma h ->
    authority_context_sound h rGamma caller_authority ->
    wf_r_config CT
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    prospective_state_covered_by_frame CT h
      (mk_watched_frame caller_authority sGamma rGamma) source ->
    frozen_caller_authority_step CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals))) source target ->
    prospective_state_covered_by_frame CT h
      (mk_watched_frame caller_authority sGamma rGamma) target.
Proof.
  intros CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty [source_mode source] [target_mode target] Hwf
    Hsound Hcallee_wf Htyping Hscope Hgety Hvalue Hbase Hfind Hargs
    [Hsource_mode Hsource] Hstep. simpl in *. subst source_mode.
  have Htarget_mode : target_mode = FlowProspective.
  { inversion Hstep; reflexivity. }
  subst target_mode. split; [reflexivity|].
  eapply safe_call_prospective_step_covered_by_caller; eauto.
Qed.

Lemma safe_call_prospective_state_connected_covered_by_caller :
  forall CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty source target,
    wf_r_config CT sGamma rGamma h ->
    authority_context_sound h rGamma caller_authority ->
    wf_r_config CT
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    prospective_state_covered_by_frame CT h
      (mk_watched_frame caller_authority sGamma rGamma) source ->
    frozen_caller_authority_connected CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals))) source target ->
    prospective_state_covered_by_frame CT h
      (mk_watched_frame caller_authority sGamma rGamma) target.
Proof.
  intros CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty source target Hwf Hsound Hcallee_wf Htyping
    Hscope Hgety Hvalue Hbase Hfind Hargs Hsource Hconnected.
  induction Hconnected.
  - eapply safe_call_prospective_state_step_covered_by_caller; eauto.
  - exact Hsource.
  - apply IHHconnected2. apply IHHconnected1. exact Hsource.
Qed.

Lemma live_prospective_mutable_authority_components_enter_safe_call :
  forall CT cutoff caller_authority sGamma mt rGamma h stack x method y args
    sGamma' vals ly cy runtime_mdef Ty boundary,
    wf_r_config CT sGamma rGamma h ->
    authority_context_sound h rGamma caller_authority ->
    wf_r_config CT
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority sGamma rGamma ->
    live_prospective_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack ->
    forall frame root target,
      live_frame_member
        (mk_watched_frame
          (call_authority caller_authority (sqtype Ty))
          (mreceiver (msignature runtime_mdef) ::
            mparams (msignature runtime_mdef))
          (mkr_env (Iot ly :: vals))) (boundary :: stack) frame ->
      prospective_mutable_authority_reachable CT h frame root target ->
      cutoff <= target \/
      (sqtype Ty = RO /\ root = ly /\ typed_root RO sGamma rGamma root /\
       r_muttype h root = Some Mut_r).
Proof.
  intros CT cutoff caller_authority sGamma mt rGamma h stack x method y args
    sGamma' vals ly cy runtime_mdef Ty boundary Hwf Hsound Hcallee_wf Htyping
    Hscope Hgety Hvalue Hbase Hfind Hargs Hboundary Hold frame root target
    Hlive [Hroot Hpath].
  inversion Hlive; subst.
  - destruct (safe_call_callee_mutable_authority_root_reflects_to_caller
        CT caller_authority sGamma mt rGamma h x method y args sGamma' vals
        ly cy runtime_mdef Ty root Hwf Htyping Hscope Hgety Hvalue Hbase
        Hfind Hargs Hroot) as [Hcaller_root | Hspecial];
      [|right; exact Hspecial].
    left.
    have Hsource : prospective_state_covered_by_frame CT h
        (mk_watched_frame caller_authority sGamma rGamma)
        (FlowProspective, root).
    { split; [reflexivity|]. exists root. split;
        [exact Hcaller_root|apply rt_refl]. }
    have Htarget := safe_call_prospective_state_connected_covered_by_caller
      CT caller_authority sGamma mt rGamma h x method y args sGamma' vals ly
      cy runtime_mdef Ty (FlowProspective, root) (FlowProspective, target)
      Hwf Hsound Hcallee_wf Htyping Hscope Hgety Hvalue Hbase Hfind Hargs
      Hsource Hpath.
    destruct Htarget as [_ [caller_root [Hcaller_root' Hcaller_path]]].
    eapply Hold with
      (frame := mk_watched_frame caller_authority sGamma rGamma)
      (root := caller_root).
    + constructor.
    + split; assumption.
  - left. simpl in H. destruct H as [Heq | Hin].
    + subst boundary0. rewrite Hboundary in Hroot, Hpath.
      eapply Hold with
        (frame := mk_watched_frame caller_authority sGamma rGamma)
        (root := root).
      * constructor.
      * split; assumption.
    + eapply Hold with (frame := boundary0.(boundary_caller)) (root := root).
      * constructor. exact Hin.
      * split; assumption.
Qed.

Lemma live_mutable_authority_components_enter_safe_call :
  forall CT cutoff caller_authority sGamma mt rGamma h stack x method y args
    sGamma' vals ly cy runtime_mdef Ty boundary,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority sGamma rGamma ->
    live_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack ->
    forall frame root target,
      live_frame_member
        (mk_watched_frame
          (call_authority caller_authority (sqtype Ty))
          (mreceiver (msignature runtime_mdef) ::
            mparams (msignature runtime_mdef))
          (mkr_env (Iot ly :: vals))) (boundary :: stack) frame ->
      mutable_authority_reachable CT h frame root target ->
      cutoff <= target \/
      (sqtype Ty = RO /\ root = ly /\ typed_root RO sGamma rGamma root /\
       r_muttype h root = Some Mut_r).
Proof.
  intros CT cutoff caller_authority sGamma mt rGamma h stack x method y args
    sGamma' vals ly cy runtime_mdef Ty boundary Hwf Htyping Hscope Hgety
    Hvalue Hbase Hfind Hargs Hboundary Hold frame root target Hlive
    Hreachable.
  inversion Hlive; subst.
  - destruct Hreachable as
      [root target Hcallee_capability Hruntime Hretained
      |root target Hcallee_rdm Hruntime Hmutable].
    + left. eapply Hold; [constructor|].
      apply mutable_authority_reachable_capability.
      * eapply safe_call_callee_capability_root_reflects_to_caller; eauto.
      * exact Hruntime.
      * exact Hretained.
    + destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x
        method y args sGamma' vals ly cy runtime_mdef root Hwf Htyping Hscope
        Hvalue Hbase Hfind Hargs Hcallee_rdm) as
        [caller_T [Hcaller_type [[Hshape Hcaller_root] |
          [Hro [Hrooteq Hro_root]]]]].
      * assert (caller_T = Ty) by congruence. subst caller_T.
        destruct Hshape as [Hcaller_mut | [Hcaller_imm | Hcaller_rdm]].
        -- left. eapply Hold; [constructor|].
           apply mutable_authority_reachable_capability.
           ++ rewrite Hcaller_mut in Hcaller_root.
              destruct Hcaller_root as
                [variable [root_T [Htype [Hroot_value Hmut]]]].
              exists variable, root_T. split; [exact Htype|].
              split; [exact Hroot_value|].
              unfold capability_in_context. left. exact Hmut.
           ++ exact Hruntime.
           ++ exact Hmutable.
        -- have Himmutable := typed_imm_root_runtime_immutable CT sGamma
             rGamma h root Hwf (ltac:(rewrite Hcaller_imm in Hcaller_root;
               exact Hcaller_root)).
           congruence.
        -- left. eapply Hold; [constructor|].
           apply mutable_authority_reachable_rdm.
           ++ rewrite Hcaller_rdm in Hcaller_root. exact Hcaller_root.
           ++ exact Hruntime.
           ++ exact Hmutable.
      * assert (caller_T = Ty) by congruence. subst caller_T.
        right. split; [exact Hro|]. split; [exact Hrooteq|].
        split; [exact Hro_root | exact Hruntime].
  - left. destruct H as [Heq | Hin].
    + subst boundary0. rewrite Hboundary in Hreachable.
      eapply Hold; eauto. constructor.
    + eapply Hold; eauto. constructor. exact Hin.
Qed.

Lemma safe_call_callee_rdm_join_is_caller_colored :
  forall CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty incoming old_mode left right,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    authority_colors_runtime_mutable h
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) incoming) ->
    authority_mode_dangerous old_mode ->
    In authority_flow_state
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) incoming)
      (old_mode, left) ->
    typed_root RDM
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) left ->
    typed_root RDM
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) right ->
    exists target_mode,
      authority_mode_dangerous target_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h
          (mk_watched_frame caller_authority sGamma rGamma) incoming)
        (target_mode, right).
Proof.
  intros CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty incoming old_mode left right Hwf Htyping
    Hscope Hgety Hvalue Hbase Hfind Hargs Hruntime Hold_mode Hold_color
    Hleft Hright.
  destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x method
    y args sGamma' vals ly cy runtime_mdef left Hwf Htyping Hscope Hvalue
    Hbase Hfind Hargs Hleft) as
    [left_T [Hleft_get Hleft_cases]].
  destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x
    method y args sGamma' vals ly cy runtime_mdef right Hwf Htyping Hscope
    Hvalue Hbase Hfind Hargs Hright) as
    [right_T [Hright_get Hright_cases]].
  assert (left_T = Ty) by congruence.
  assert (right_T = Ty) by congruence. subst left_T right_T.
  destruct Hleft_cases as [[Hleft_shape Hleft_root] |
      [Hleft_ro [Hleft_eq Hleft_ro_root]]];
    destruct Hright_cases as [[Hright_shape Hright_root] |
      [Hright_ro [Hright_eq Hright_ro_root]]].
  - destruct Hleft_shape as [Hview | [Hview | Hview]].
    + exists FlowPowered. split; [left; reflexivity|].
      eapply executing_authority_typed_mut_root_is_powered.
      rewrite Hview in Hright_root. exact Hright_root.
    + have Hleft_immutable := typed_imm_root_runtime_immutable CT sGamma
        rGamma h left Hwf (ltac:(rewrite Hview in Hleft_root;
          exact Hleft_root)).
      have Hleft_mutable := Hruntime old_mode left Hold_color.
      congruence.
    + exists FlowProspective. split; [right; reflexivity|].
      eapply executing_authority_dangerous_frame_join; eauto.
      * rewrite Hview in Hleft_root. exact Hleft_root.
      * rewrite Hview in Hright_root. exact Hright_root.
  - destruct Hleft_shape as [Hq | [Hq | Hq]]; congruence.
  - destruct Hright_shape as [Hq | [Hq | Hq]]; congruence.
  - exists old_mode. split; [exact Hold_mode|].
    rewrite Hright_eq. rewrite <- Hleft_eq. exact Hold_color.
Qed.

Lemma safe_call_callee_frame_step_preserves_coverage :
  forall CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty incoming source target,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    authority_colors_runtime_mutable h
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) incoming) ->
    authority_state_covered
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) incoming) source ->
    phased_authority_frame_step CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals))) source target ->
    authority_state_covered
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) incoming) target.
Proof.
  intros CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty incoming source target Hwf Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs Hruntime Hcovered Hstep.
  inversion Hstep; subst; simpl in *.
  - intros _. destruct (Hcovered (or_introl eq_refl)) as
      [old_mode [Hold_mode Hold_color]]. exists old_mode.
    split; [exact Hold_mode|].
    eapply executing_authority_dangerous_retained; eauto.
  - intros _. destruct (Hcovered (or_intror eq_refl)) as
      [old_mode [Hold_mode Hold_color]]. exists old_mode.
    split; [exact Hold_mode|].
    eapply executing_authority_dangerous_retained; eauto.
  - intros _. destruct (Hcovered (or_intror eq_refl)) as
      [old_mode [Hold_mode Hold_color]]. exists FlowProspective.
    split; [right; reflexivity|].
    eapply executing_authority_dangerous_reverse_rdm; eauto.
  - intros _. destruct (Hcovered (or_introl eq_refl)) as
      [old_mode [Hold_mode Hold_color]]. exists FlowProspective.
    split; [right; reflexivity|].
    eapply executing_authority_dangerous_reverse_rdm; eauto.
  - intros Hdangerous. destruct Hdangerous as [Hbad | Hbad]; discriminate.
  - intros Hdangerous. destruct Hdangerous as [Hbad | Hbad]; discriminate.
  - intros _. destruct (Hcovered (or_introl eq_refl)) as
      [old_mode [Hold_mode Hold_color]].
    eapply safe_call_callee_rdm_join_is_caller_colored; eauto.
  - intros _. destruct (Hcovered (or_intror eq_refl)) as
      [old_mode [Hold_mode Hold_color]].
    eapply safe_call_callee_rdm_join_is_caller_colored; eauto.
  - intros Hdangerous. destruct Hdangerous as [Hbad | Hbad]; discriminate.
  - intros Hdangerous. destruct Hdangerous as [Hbad | Hbad]; discriminate.
  - intros Hdangerous. destruct Hdangerous as [Hbad | Hbad]; discriminate.
  - intros _. destruct (Hcovered (or_introl eq_refl)) as
      [old_mode [Hold_mode Hold_color]]. exists old_mode. split; assumption.
  - intros _. exists FlowPowered. split; [left; reflexivity|].
    apply executing_authority_owned_is_powered.
    eapply safe_call_callee_owned_reflects_to_caller; eauto.
Qed.

Lemma safe_call_callee_frame_connected_preserves_coverage :
  forall CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty incoming source target,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    authority_colors_runtime_mutable h
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) incoming) ->
    authority_state_covered
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) incoming) source ->
    phased_authority_frame_connected CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals))) source target ->
    authority_state_covered
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) incoming) target.
Proof.
  intros CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty incoming source target Hwf Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs Hruntime Hcovered Hconnected.
  induction Hconnected.
  - eapply safe_call_callee_frame_step_preserves_coverage; eauto.
  - exact Hcovered.
  - apply IHHconnected2. apply IHHconnected1. exact Hcovered.
Qed.

(** Call entry is origin-reflecting: every dangerous color introduced by
    the callee view is represented in the caller's completed entry colors.
    This is the summary bridge used to compose a recursively proved body
    summary with its caller. *)
Lemma executing_authority_colors_enter_call_covered :
  forall CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty incoming,
    wf_r_config CT sGamma rGamma h ->
    authority_context_sound h rGamma caller_authority ->
    authority_colors_runtime_mutable h incoming ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT h
          (mk_watched_frame
            (call_authority caller_authority (sqtype Ty))
            (mreceiver (msignature runtime_mdef) ::
              mparams (msignature runtime_mdef))
            (mkr_env (Iot ly :: vals)))
          (executing_authority_color_set CT h
            (mk_watched_frame caller_authority sGamma rGamma) incoming))
        (mode, location) ->
      exists caller_mode,
        authority_mode_dangerous caller_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h
            (mk_watched_frame caller_authority sGamma rGamma) incoming)
          (caller_mode, location).
Proof.
  intros CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty incoming Hwf Hsound Hincoming Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs mode location Hmode
    [seed [Hseed Hconnected]].
  set (old_colors := executing_authority_color_set CT h
    (mk_watched_frame caller_authority sGamma rGamma) incoming).
  have Hold_runtime : authority_colors_runtime_mutable h old_colors.
  { unfold old_colors. eapply executing_authority_colors_runtime_mutable;
      eauto. }
  assert (Hseed_covered : authority_state_covered old_colors seed).
  { destruct seed as [seed_mode seed_location]. simpl. intros Hseed_mode.
    inversion Hseed; subst.
    - exists seed_mode. split; [exact Hseed_mode|exact H].
    - destruct H as [owned [Heq Howned]]. inversion Heq; subst.
      exists FlowPowered. split; [left; reflexivity|].
      unfold old_colors. apply executing_authority_owned_is_powered.
      eapply safe_call_callee_owned_reflects_to_caller; eauto. }
  have Hcovered := safe_call_callee_frame_connected_preserves_coverage CT
    caller_authority sGamma mt rGamma h x method y args sGamma' vals ly cy
    runtime_mdef Ty incoming seed (mode, location) Hwf Htyping Hscope Hgety
    Hvalue Hbase Hfind Hargs Hold_runtime Hseed_covered Hconnected Hmode.
  destruct Hcovered as [caller_mode [Hcaller_mode Hcaller_color]].
  exists caller_mode. split; [exact Hcaller_mode|].
  unfold old_colors in Hcaller_color. exact Hcaller_color.
Qed.

Lemma executing_authority_colors_enter_call :
  forall CT Z caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty incoming,
    wf_r_config CT sGamma rGamma h ->
    authority_context_sound h rGamma caller_authority ->
    authority_colors_runtime_mutable h incoming ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    executing_authority_colors_separated CT h Z
      (mk_watched_frame caller_authority sGamma rGamma) incoming ->
    executing_authority_colors_separated CT h Z
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals)))
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) incoming).
Proof.
  intros CT Z caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty incoming Hwf Hsound Hincoming Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs Hseparated mode protected Hmode
    [seed [Hseed Hconnected]] Hprotected.
  set (old_colors := executing_authority_color_set CT h
    (mk_watched_frame caller_authority sGamma rGamma) incoming).
  have Hold_runtime : authority_colors_runtime_mutable h old_colors.
  { unfold old_colors. eapply executing_authority_colors_runtime_mutable;
      eauto. }
  assert (Hseed_covered : authority_state_covered old_colors seed).
  { destruct seed as [seed_mode seed_location]. simpl. intros Hseed_mode.
    inversion Hseed; subst.
    - exists seed_mode. split; [exact Hseed_mode|exact H].
    - destruct H as [location [Heq Howned]]. inversion Heq; subst.
      exists FlowPowered. split; [left; reflexivity|].
      unfold old_colors. apply executing_authority_owned_is_powered.
      eapply safe_call_callee_owned_reflects_to_caller; eauto. }
  have Hcovered := safe_call_callee_frame_connected_preserves_coverage CT
    caller_authority sGamma mt rGamma h x method y args sGamma' vals ly cy
    runtime_mdef Ty incoming seed (mode, protected) Hwf Htyping Hscope Hgety
    Hvalue Hbase Hfind Hargs Hold_runtime Hseed_covered Hconnected Hmode.
  destruct Hcovered as [old_mode [Hold_mode Hold_color]].
  unfold old_colors in Hold_color.
  exact (Hseparated old_mode protected Hold_mode Hold_color Hprotected).
Qed.

Lemma frozen_caller_snapshots_after_safe_call_entry_avoid_protected :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_frozen_authority_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_caller_snapshots_avoid_protected Z
      (advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty
    [Hmain [Haligned [Hruntime [Hclosed
      [Hretain [Hdangerous [Havoid [Hroots [Hexposure
        [Hresume [Hjoins [Hentry_covered Hphase_covered]]]]]]]]]]]]
    Htyping Hscope Hgety Hvalue Hbase
    Hfind Hargs callee new_snapshot mode location Hnew Hmode Hcolor Hprotected.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot.
  simpl in Hcolor.
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hsound : authority_context_sound h rGamma caller_authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
  have Hmain_separated := proj1 (proj2 (proj2 (proj2 Hmain))).
  have Hcallee_color : In authority_flow_state
      (executing_authority_color_set CT h callee
        (executing_authority_color_set CT h
          (mk_watched_frame caller_authority sGamma rGamma)
          old_snapshot.(frozen_snapshot_current_colors)))
      (mode, location).
  { destruct Hcolor as [seed [Hseed Hpath]]. exists seed. split.
    - left. apply executing_authority_color_set_contains_incoming. exact Hseed.
    - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
  destruct (executing_authority_colors_enter_call_covered CT caller_authority
    sGamma mt rGamma h x method y args sGamma' vals ly cy runtime_mdef Ty
    old_snapshot.(frozen_snapshot_current_colors) Hwf Hsound
    (Hruntime old_snapshot Hold) Htyping Hscope Hgety Hvalue Hbase Hfind Hargs
    mode location Hmode Hcallee_color) as
    [caller_mode [Hcaller_mode Hcaller_color]].
  destruct
    (executing_with_frozen_incoming_dangerous_covered_by_old_or_active CT h
      (mk_watched_frame caller_authority sGamma rGamma)
      old_snapshot.(frozen_snapshot_current_colors) caller_mode location
      (Hclosed old_snapshot Hold) Hcaller_mode Hcaller_color) as
    [[snapshot_mode [Hsnapshot_mode Hsnapshot_color]] |
     [active_mode [Hactive_mode Hactive_color]]].
  - exact (Havoid old_snapshot snapshot_mode location Hold Hsnapshot_mode
      Hsnapshot_color Hprotected).
  - eapply Hmain_separated; [exact Hactive_mode| |exact Hprotected].
    eapply independent_active_authority_colors_in_executing.
    exact Hactive_color.
Qed.

Lemma frozen_caller_snapshots_after_safe_call_entry_roots_in_heap :
  forall CT h callee snapshots,
    frozen_caller_snapshots_resume_roots_in_heap h snapshots ->
    frozen_caller_snapshots_resume_roots_in_heap h
      (advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT h callee snapshots Hroots new_snapshot root Hnew Hroot.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot. simpl in Hroot.
  eapply Hroots; eauto.
Qed.

Lemma frozen_caller_snapshots_after_safe_call_entry_exposures_wf :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_frozen_authority_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_caller_snapshots_resume_exposures_wf CT h callee
      (advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty
    [Hmain [Haligned [Hruntime [Hclosed
      [Hretain [Hdangerous [Havoid [Hroots [Hexposure
        [Hresume [Hjoins [Hentry_covered Hphase_covered]]]]]]]]]]]]
    Htyping Hscope Hgety Hvalue Hbase Hfind Hargs callee.
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hcallee_wf : wf_r_config CT callee.(frame_senv)
      callee.(frame_renv) h.
  { unfold callee. simpl.
    destruct (typed_call_has_wf_callee_frame CT sGamma mt rGamma h x method
      y args sGamma' vals ly cy runtime_mdef Hwf Htyping Hvalue Hbase Hfind
      Hargs) as [body_end [_ Hframe]]. exact Hframe. }
  split.
  - intros new_snapshot Hnew mode location Hcolor.
    unfold advance_frozen_caller_snapshots in Hnew.
    apply in_map_iff in Hnew.
    destruct Hnew as [old_slot [Heq Hold]].
    destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as Heq. subst new_snapshot. simpl in Hcolor.
    eapply (advance_frozen_caller_snapshot_runtime_mutable CT h callee
      old_snapshot.(frozen_snapshot_current_resume_exposure)); eauto.
    eapply (proj1 Hexposure); eauto.
  - split.
    + intros new_snapshot Hnew.
      unfold advance_frozen_caller_snapshots in Hnew.
      apply in_map_iff in Hnew.
      destruct Hnew as [old_slot [Heq Hold]].
      destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
      injection Heq as Heq. subst new_snapshot. simpl.
      exact (proj1 (frozen_caller_authority_closure_idempotent CT h callee
        old_snapshot.(frozen_snapshot_current_resume_exposure))).
    + split.
      * intros new_snapshot mode location Hnew Hcolor.
        unfold advance_frozen_caller_snapshots in Hnew.
        apply in_map_iff in Hnew.
        destruct Hnew as [old_slot [Heq Hold]].
        destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
        injection Heq as Heq. subst new_snapshot. simpl in Hcolor.
        eapply frozen_caller_authority_closure_dangerous; [|exact Hcolor].
        intros old_mode old_location Hold_color.
        eapply (proj1 (proj2 (proj2 Hexposure))) with
          (snapshot := old_snapshot); eauto.
      * split.
        -- intros new_snapshot Hnew state Hentry.
           unfold advance_frozen_caller_snapshots in Hnew.
           apply in_map_iff in Hnew.
           destruct Hnew as [old_slot [Heq Hold]].
           destruct old_slot as [old_snapshot|]; simpl in Heq;
             [|discriminate].
           injection Heq as Heq. subst new_snapshot. simpl in *.
           apply frozen_caller_authority_closure_contains.
           eapply (proj1 (proj2 (proj2 (proj2 Hexposure)))); eauto.
        -- intros new_snapshot root Hnew Hroot Hroot_runtime.
           unfold advance_frozen_caller_snapshots in Hnew.
           apply in_map_iff in Hnew.
           destruct Hnew as [old_slot [Heq Hold]].
           destruct old_slot as [old_snapshot|]; simpl in Heq;
             [|discriminate].
           injection Heq as Heq. subst new_snapshot. simpl in *.
           apply frozen_caller_authority_closure_contains.
           eapply (proj2 (proj2 (proj2 (proj2 Hexposure)))); eauto.
Qed.

Lemma frozen_caller_snapshots_after_safe_call_entry_resume_roots_safe :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_frozen_authority_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_caller_snapshots_resume_roots_safe CT h Z callee
      (advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty
    [Hmain [Haligned [Hruntime [Hclosed
      [Hretain [Hdangerous [Havoid [Hroots [Hexposure
        [Hresume [Hjoins [Hentry_covered Hphase_covered]]]]]]]]]]]]
    Htyping Hscope Hgety Hvalue Hbase Hfind Hargs callee new_snapshot
    active_mode source exposure_mode target Hnew Hactive_mode Hactive Hsource
    Hexposure_mode Htarget Hprotected.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot. simpl in *.
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hsound : authority_context_sound h rGamma caller_authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
  have Hcallee_color : In authority_flow_state
      (executing_authority_color_set CT h callee
        (executing_authority_color_set CT h
          (mk_watched_frame caller_authority sGamma rGamma)
          (Empty_set authority_flow_state)))
      (active_mode, source).
  { eapply independent_active_authority_colors_in_executing. exact Hactive. }
  destruct (executing_authority_colors_enter_call_covered CT caller_authority
    sGamma mt rGamma h x method y args sGamma' vals ly cy runtime_mdef Ty
    (Empty_set authority_flow_state) Hwf Hsound
    (ltac:(intros mode location Hempty; inversion Hempty)) Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs active_mode source Hactive_mode
    Hcallee_color) as [old_mode [Hold_mode Hold_active]].
  have Hcallee_target : In authority_flow_state
      (executing_authority_color_set CT h callee
        (executing_authority_color_set CT h
          (mk_watched_frame caller_authority sGamma rGamma)
          old_snapshot.(frozen_snapshot_current_resume_exposure)))
      (exposure_mode, target).
  { destruct Htarget as [seed [Hseed Hpath]]. exists seed. split.
    - left. apply executing_authority_color_set_contains_incoming. exact Hseed.
    - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
  destruct (executing_authority_colors_enter_call_covered CT caller_authority
    sGamma mt rGamma h x method y args sGamma' vals ly cy runtime_mdef Ty
    old_snapshot.(frozen_snapshot_current_resume_exposure) Hwf Hsound
    ((proj1 Hexposure) old_snapshot Hold) Htyping Hscope Hgety Hvalue Hbase
    Hfind Hargs exposure_mode target Hexposure_mode Hcallee_target) as
    [old_exposure_mode [Hold_exposure_mode Hold_target]].
  destruct
    (executing_with_frozen_incoming_dangerous_covered_by_old_or_active CT h
      (mk_watched_frame caller_authority sGamma rGamma)
      old_snapshot.(frozen_snapshot_current_resume_exposure)
      old_exposure_mode target
      ((proj1 (proj2 Hexposure)) old_snapshot Hold)
      Hold_exposure_mode Hold_target) as
    [[snapshot_mode [Hsnapshot_mode Hsnapshot_target]] |
     [target_active_mode [Htarget_active_mode Htarget_active]]].
  - eapply Hresume with (snapshot := old_snapshot) (active_mode := old_mode)
      (source := source) (exposure_mode := snapshot_mode); eauto.
  - have Hmain_separated := proj1 (proj2 (proj2 (proj2 Hmain))).
    eapply Hmain_separated; [exact Htarget_active_mode| |exact Hprotected].
    eapply independent_active_authority_colors_in_executing.
    exact Htarget_active.
Qed.

Lemma frozen_caller_snapshots_after_safe_call_entry_resume_joins_safe :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_frozen_authority_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_caller_snapshots_resume_joins_safe Z
      (advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty
    [Hmain [Haligned [Hruntime [Hclosed [Hretain [Hdangerous
      [Havoid [Hroots [Hexposure
        [Hresume [Hjoins [Hentry_covered Hphase_covered]]]]]]]]]]]]
    Htyping Hscope Hgety Hvalue Hbase Hfind Hargs callee new_snapshot
    source_mode source Hnew Hsource_mode Hsource_color Hsource_root.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot. simpl in *.
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hsound : authority_context_sound h rGamma caller_authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
  have Hmain_separated := proj1 (proj2 (proj2 (proj2 Hmain))).
  assert (Hclassify : forall colors mode location,
      authority_colors_runtime_mutable h colors ->
      Included authority_flow_state
        (frozen_caller_authority_closure CT h
          (mk_watched_frame caller_authority sGamma rGamma) colors) colors ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (frozen_caller_authority_closure CT h callee colors)
        (mode, location) ->
      (exists old_mode,
        authority_mode_dangerous old_mode /\
        In authority_flow_state colors (old_mode, location)) \/
      (exists active_mode,
        authority_mode_dangerous active_mode /\
        In authority_flow_state
          (independent_active_authority_colors CT h
            (mk_watched_frame caller_authority sGamma rGamma))
          (active_mode, location))).
  { intros colors mode location Hcolors_runtime Hcolors_closed Hmode Hcolor.
    have Hcallee_color : In authority_flow_state
        (executing_authority_color_set CT h callee
          (executing_authority_color_set CT h
            (mk_watched_frame caller_authority sGamma rGamma) colors))
        (mode, location).
    { destruct Hcolor as [seed [Hseed Hpath]]. exists seed. split.
      - left. apply executing_authority_color_set_contains_incoming.
        exact Hseed.
      - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
    destruct (executing_authority_colors_enter_call_covered CT caller_authority
      sGamma mt rGamma h x method y args sGamma' vals ly cy runtime_mdef Ty
      colors Hwf Hsound Hcolors_runtime Htyping Hscope Hgety Hvalue Hbase
      Hfind Hargs mode location Hmode Hcallee_color) as
      [caller_mode [Hcaller_mode Hcaller_color]].
    exact
      (executing_with_frozen_incoming_dangerous_covered_by_old_or_active CT h
        (mk_watched_frame caller_authority sGamma rGamma) colors caller_mode
        location Hcolors_closed Hcaller_mode Hcaller_color). }
  have Hsource_cases := Hclassify
    old_snapshot.(frozen_snapshot_current_colors) source_mode source
    (Hruntime old_snapshot Hold) (Hclosed old_snapshot Hold) Hsource_mode
    Hsource_color.
  assert (Hclassify_target : forall exposure_mode target,
      authority_mode_dangerous exposure_mode ->
      In authority_flow_state
        (frozen_caller_authority_closure CT h callee
          old_snapshot.(frozen_snapshot_current_resume_exposure))
        (exposure_mode, target) ->
      (exists old_exposure_mode,
        authority_mode_dangerous old_exposure_mode /\
        In authority_flow_state
          old_snapshot.(frozen_snapshot_current_resume_exposure)
          (old_exposure_mode, target)) \/
      (exists target_active_mode,
        authority_mode_dangerous target_active_mode /\
        In authority_flow_state
          (independent_active_authority_colors CT h
            (mk_watched_frame caller_authority sGamma rGamma))
          (target_active_mode, target))).
  { intros exposure_mode target Hexposure_mode Htarget.
    eapply Hclassify; eauto.
    - eapply (proj1 Hexposure); eauto.
    - eapply (proj1 (proj2 Hexposure)); eauto. }
  destruct Hsource_cases as
    [[old_source_mode [Hold_source_mode Hold_source]] |
     [active_source_mode [Hactive_source_mode Hactive_source]]].
  - destruct (Hjoins old_snapshot old_source_mode source Hold
      Hold_source_mode Hold_source Hsource_root) as
      [[entry_mode [Hentry_mode Hentry]] | Hsafe].
    + left. exists entry_mode. split; assumption.
    + right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
      destruct (Hclassify_target exposure_mode target Hexposure_mode Htarget) as
        [[old_exposure_mode [Hold_exposure_mode Hold_target]] |
         [target_active_mode [Htarget_active_mode Htarget_active]]].
      * exact (Hsafe old_exposure_mode target Hold_exposure_mode Hold_target
          Hprotected).
      * eapply Hmain_separated; [exact Htarget_active_mode| |exact Hprotected].
        eapply independent_active_authority_colors_in_executing.
        exact Htarget_active.
  - right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
    destruct (Hclassify_target exposure_mode target Hexposure_mode Htarget) as
      [[old_exposure_mode [Hold_exposure_mode Hold_target]] |
       [target_active_mode [Htarget_active_mode Htarget_active]]].
    + eapply Hresume with (snapshot := old_snapshot)
        (active_mode := active_source_mode) (source := source)
        (exposure_mode := old_exposure_mode); eauto.
    + eapply Hmain_separated; [exact Htarget_active_mode| |exact Hprotected].
      eapply independent_active_authority_colors_in_executing.
      exact Htarget_active.
Qed.

Lemma frozen_caller_snapshots_nested_resume_safe_after_safe_call_entry :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_frozen_authority_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    frozen_caller_snapshots_nested_resume_safe Z snapshots ->
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_caller_snapshots_nested_resume_safe Z
      (advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty
    Hfrozen Htyping Hscope Hgety Hvalue Hbase Hfind Hargs Hnested callee.
  destruct Hfrozen as
    [Hmain [Haligned [Hruntime [Hclosed [Hretain [Hdangerous [Havoid
      [Hroots [Hexposure [Hresume [Hjoins
        [Hentry_covered Hphase_covered]]]]]]]]]]]].
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hsound : authority_context_sound h rGamma caller_authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
  have Hmain_separated := proj1 (proj2 (proj2 (proj2 Hmain))).
  set (caller := mk_watched_frame caller_authority sGamma rGamma).
  set (exceptional := independent_active_authority_colors CT h caller).
  assert (Hclassify : forall colors mode location,
      authority_colors_runtime_mutable h colors ->
      Included authority_flow_state
        (frozen_caller_authority_closure CT h caller colors) colors ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (frozen_caller_authority_closure CT h callee colors)
        (mode, location) ->
      (exists old_mode,
        authority_mode_dangerous old_mode /\
        In authority_flow_state colors (old_mode, location)) \/
      (exists active_mode,
        authority_mode_dangerous active_mode /\
        In authority_flow_state exceptional (active_mode, location))).
  { intros colors mode location Hcolors_runtime Hcolors_closed Hmode Hcolor.
    have Hcallee_color : In authority_flow_state
        (executing_authority_color_set CT h callee
          (executing_authority_color_set CT h caller colors))
        (mode, location).
    { destruct Hcolor as [seed [Hseed Hpath]]. exists seed. split.
      - left. apply executing_authority_color_set_contains_incoming.
        exact Hseed.
      - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
    destruct (executing_authority_colors_enter_call_covered CT
      caller_authority sGamma mt rGamma h x method y args sGamma' vals ly cy
      runtime_mdef Ty colors Hwf Hsound Hcolors_runtime Htyping Hscope Hgety
      Hvalue Hbase Hfind Hargs mode location Hmode Hcallee_color) as
      [caller_mode [Hcaller_mode Hcaller_color]].
    unfold caller, exceptional.
    eapply executing_with_frozen_incoming_dangerous_covered_by_old_or_active;
      eauto. }
  eapply frozen_caller_snapshots_nested_resume_safe_after_classified_advance
    with (exceptional := exceptional).
  - exact Hnested.
  - unfold exceptional, caller. exact Hresume.
  - intros active_mode location Hactive_mode Hactive Hprotected.
    eapply Hmain_separated; [exact Hactive_mode| |exact Hprotected].
    eapply independent_active_authority_colors_in_executing. exact Hactive.
  - intros snapshot older mode location Hsnapshot _ Hmode Hcolor _.
    eapply Hclassify; eauto.
  - intros snapshot mode location Hsnapshot Hmode Hcolor _.
    eapply Hclassify; eauto using (proj1 Hexposure),
      (proj1 (proj2 Hexposure)).
Qed.

Lemma frozen_completed_colors_resume_safe_after_safe_call_entry :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_frozen_authority_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) incoming)
      snapshots ->
    let caller := mk_watched_frame caller_authority sGamma rGamma in
    let caller_colors := executing_authority_color_set CT h caller incoming in
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h callee caller_colors)
      (advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty
    Hfrozen Htyping Hscope Hgety Hvalue Hbase Hfind Hargs Hcompleted
    caller caller_colors callee.
  destruct Hfrozen as
    [Hmain [Haligned [Hruntime [Hclosed [Hretain [Hdangerous [Havoid
      [Hroots [Hexposure [Hresume [Hjoins
        [Hentry_covered Hphase_covered]]]]]]]]]]]].
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hsound : authority_context_sound h rGamma caller_authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
  have Hincoming_runtime : authority_colors_runtime_mutable h incoming :=
    proj1 (proj2 (proj2 Hmain)).
  have Hmain_separated := proj1 (proj2 (proj2 (proj2 Hmain))).
  intros new_snapshot source_mode source Hnew Hsource_mode Hsource Hroot.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot. simpl in *.
  destruct (executing_authority_colors_enter_call_covered CT
    caller_authority sGamma mt rGamma h x method y args sGamma' vals ly cy
    runtime_mdef Ty incoming Hwf Hsound Hincoming_runtime Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs source_mode source Hsource_mode Hsource) as
    [caller_mode [Hcaller_mode Hcaller_source]].
  destruct (Hcompleted old_snapshot caller_mode source Hold Hcaller_mode
    Hcaller_source Hroot) as
    [[entry_mode [Hentry_mode Hentry]] | Hsafe].
  - left. exists entry_mode. split; assumption.
  - right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
    have Hcallee_target : In authority_flow_state
        (executing_authority_color_set CT h callee
          (executing_authority_color_set CT h caller
            old_snapshot.(frozen_snapshot_current_resume_exposure)))
        (exposure_mode, target).
    { destruct Htarget as [seed [Hseed Hpath]]. exists seed. split.
      - left. apply executing_authority_color_set_contains_incoming.
        exact Hseed.
      - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
    destruct (executing_authority_colors_enter_call_covered CT
      caller_authority sGamma mt rGamma h x method y args sGamma' vals ly cy
      runtime_mdef Ty old_snapshot.(frozen_snapshot_current_resume_exposure)
      Hwf Hsound ((proj1 Hexposure) old_snapshot Hold) Htyping Hscope Hgety
      Hvalue Hbase Hfind Hargs exposure_mode target Hexposure_mode
      Hcallee_target) as [caller_target_mode [Hcaller_target_mode Hcaller_target]].
    destruct (executing_with_frozen_incoming_dangerous_covered_by_old_or_active
      CT h caller old_snapshot.(frozen_snapshot_current_resume_exposure)
      caller_target_mode target ((proj1 (proj2 Hexposure)) old_snapshot Hold)
      Hcaller_target_mode Hcaller_target) as
      [[old_target_mode [Hold_target_mode Hold_target]] |
       [active_target_mode [Hactive_target_mode Hactive_target]]].
    + exact (Hsafe old_target_mode target Hold_target_mode Hold_target
        Hprotected).
    + eapply Hmain_separated; [exact Hactive_target_mode| |exact Hprotected].
      eapply independent_active_authority_colors_in_executing.
      exact Hactive_target.
Qed.

Lemma frozen_caller_snapshots_after_safe_call_entry_entry_exposure_covered :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_frozen_authority_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    let caller := mk_watched_frame caller_authority sGamma rGamma in
    let caller_colors :=
      executing_authority_color_set CT h caller incoming in
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_caller_snapshots_entry_exposure_covered
      (enter_frozen_caller_snapshots CT h caller callee caller_colors
        snapshots).
Proof.
  intros CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty
    [Hmain [Haligned [Hruntime [Hclosed [Hretain [Hdangerous
      [Havoid [Hroots [Hexposure
        [Hresume [Hjoins [Hentry_covered Hphase_covered]]]]]]]]]]]]
    Htyping Hscope Hgety Hvalue Hbase Hfind Hargs caller caller_colors callee
    snapshot source_mode source Hsnapshot Hsource_mode Hsource_color
    Hsource_root.
  unfold enter_frozen_caller_snapshots in Hsnapshot.
  simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
  - injection Heq as Heq. subst snapshot. simpl in *.
    have Hwf : wf_r_config CT sGamma rGamma h :=
      proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
    have Hsound : authority_context_sound h rGamma caller_authority :=
      proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
    have Hincoming_runtime : authority_colors_runtime_mutable h incoming :=
      proj1 (proj2 (proj2 Hmain)).
    have Hcallee_color : In authority_flow_state
        (executing_authority_color_set CT h callee
          (executing_authority_color_set CT h caller incoming))
        (source_mode, source).
    { destruct Hsource_color as [seed [[Hseed Hseed_mode] Hpath]].
      exists seed. split; [left; exact Hseed|].
      eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
    destruct (executing_authority_colors_enter_call_covered CT
      caller_authority sGamma mt rGamma h x method y args sGamma' vals ly cy
      runtime_mdef Ty incoming Hwf Hsound Hincoming_runtime Htyping Hscope
      Hgety Hvalue Hbase Hfind Hargs source_mode source Hsource_mode
      Hcallee_color) as [caller_mode [Hcaller_mode Hcaller_source]].
    apply frozen_caller_authority_closure_monotone.
    intros exposure_state Hexposure_state. split.
    + eapply frame_resume_exposure_colors_in_executing_from_dangerous_rdm_root
        with (source_mode := caller_mode) (source := source); eauto.
    + destruct exposure_state as [exposure_mode exposure_location].
      eapply frame_resume_exposure_colors_dangerous. exact Hexposure_state.
  - eapply (advance_frozen_caller_snapshots_entry_exposure_covered
      CT h callee snapshots Hentry_covered); eauto.
Qed.

Lemma principled_phased_authority_history_enter_call :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    exists origins destination_type,
      static_getType sGamma x = Some destination_type /\
      principled_phased_authority_live_history_state CT P Z cutoff
        (mk_watched_frame
          (call_authority caller_authority (sqtype Ty))
          (mreceiver (msignature runtime_mdef) ::
            mparams (msignature runtime_mdef))
          (mkr_env (Iot ly :: vals)))
        (mk_watched_call_boundary
          (mk_watched_frame caller_authority sGamma rGamma)
          (mreceiver (msignature runtime_mdef) ::
            mparams (msignature runtime_mdef))
          (mkr_env (Iot ly :: vals)) (sqtype Ty)
          (mreturn (mbody runtime_mdef)) (sqtype destination_type)
          (sqtype (mret (msignature runtime_mdef))) (dom h) origins :: stack)
        (executing_authority_color_set CT h
          (mk_watched_frame caller_authority sGamma rGamma) incoming) h.
Proof.
  intros CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    x method y args sGamma' vals ly cy runtime_mdef Ty Hstate Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs.
  destruct Hstate as [Hcontains Hstate].
  destruct Hstate as [Hconfined Hstate].
  destruct Hstate as [Hincoming_runtime Hstate].
  destruct Hstate as [Hphased Hstate].
  destruct Hstate as [Hframes Hstate].
  destruct Hstate as [Hsound Hstate].
  destruct Hstate as [Hcutoff Hstate].
  destruct Hstate as [Hzone [Hchain Hcutoffs]].
  set (caller := mk_watched_frame caller_authority sGamma rGamma).
  set (callee_senv := mreceiver (msignature runtime_mdef) ::
    mparams (msignature runtime_mdef)).
  set (callee_renv := mkr_env (Iot ly :: vals)).
  set (callee := mk_watched_frame
    (call_authority caller_authority (sqtype Ty)) callee_senv callee_renv).
  set (callee_incoming := executing_authority_color_set CT h caller incoming).
  have Hwf : wf_r_config CT sGamma rGamma h := proj1 Hframes.
  set (origins := Build_call_boundary_origins caller (sqtype Ty)
    callee_senv callee_renv
    (safe_call_rdm_roots_reflect_through_view CT sGamma mt rGamma h x
      method y args sGamma' vals ly cy runtime_mdef Ty Hwf Htyping Hscope
      Hgety Hvalue Hbase Hfind Hargs)
    (safe_call_capability_roots_reflect_through_view CT caller_authority
      sGamma mt rGamma h x method y args sGamma' vals ly cy runtime_mdef Ty
      Hwf Htyping Hscope Hgety Hvalue Hbase Hfind Hargs)).
  assert (Hdestination : exists destination_type,
      static_getType sGamma x = Some destination_type).
  { inversion Htyping; subst; eauto. }
  destruct Hdestination as [destination_type Hdestination].
  set (boundary := mk_watched_call_boundary caller callee_senv callee_renv
    (sqtype Ty) (mreturn (mbody runtime_mdef)) (sqtype destination_type)
    (sqtype (mret (msignature runtime_mdef))) (dom h) origins).
  have Hcallee_wf : wf_r_config CT callee_senv callee_renv h.
  { unfold callee_senv, callee_renv.
    destruct (typed_call_has_wf_callee_frame CT sGamma mt rGamma h x method
      y args sGamma' vals ly cy runtime_mdef Hwf Htyping Hvalue Hbase Hfind
      Hargs) as [body_end [_ Hframe]]. exact Hframe. }
  have Hcallee_confined : state_is_confined P cutoff callee_renv h.
  { destruct Hconfined as [Hcaller_env Hheap]. split; [|exact Hheap].
    intros variable location Hcallee_value. unfold callee_renv in *.
    destruct variable as [|index].
    - simpl in Hcallee_value. injection Hcallee_value as <-.
      eapply Hcaller_env; eauto.
    - simpl in Hcallee_value.
      destruct (runtime_lookup_list_nth_zs rGamma args vals index
        (Iot location) Hargs Hcallee_value) as
        [argument [Hargument_index Hargument_value]].
      eapply Hcaller_env; eauto. }
  have Hcaller_sound : authority_context_sound h rGamma caller_authority :=
    proj1 Hsound.
  have Hcallee_sound : authority_context_sound h callee_renv
      (call_authority caller_authority (sqtype Ty)).
  { intros Hcallee_authority. exists ly. split; [reflexivity|].
    have Hnotbot := wf_config_nonnull_variable_not_bot CT sGamma rGamma h y
      Ty ly Hwf Hgety Hvalue.
    have Hreceiver_capability : capability_in_context caller_authority
        (sqtype Ty).
    { eapply safe_call_receiver_authority_reflects; [exact Hnotbot|].
      unfold capability_in_context. right. split; [reflexivity|].
      exact Hcallee_authority. }
    eapply frame_capability_root_runtime_mutable with (frame := caller).
    - exact Hwf.
    - exact Hcaller_sound.
    - exists y, Ty. repeat split; try assumption. }
  have Hcallee_frames : live_frames_wf CT h callee (boundary :: stack).
  { split; [exact Hcallee_wf|]. constructor; [exact Hwf|exact (proj2 Hframes)]. }
  have Hcallee_sounds : live_frames_authority_sound h callee
      (boundary :: stack).
  { split; [exact Hcallee_sound|].
    constructor; [exact Hcaller_sound|exact (proj2 Hsound)]. }
  have Hcallee_incoming_runtime : authority_colors_runtime_mutable h
      callee_incoming.
  { unfold callee_incoming, caller.
    eapply executing_authority_colors_runtime_mutable; eauto. }
  have Hcallee_phased : executing_authority_colors_separated CT h Z callee
      callee_incoming.
  { unfold callee, callee_senv, callee_renv, callee_incoming, caller.
    eapply executing_authority_colors_enter_call; eauto. }
  exists origins, destination_type. split; [exact Hdestination|].
  refine (conj Hcontains (conj Hcallee_confined _)).
  refine (conj Hcallee_incoming_runtime (conj Hcallee_phased _)).
  refine (conj Hcallee_frames (conj Hcallee_sounds (conj Hcutoff
    (conj Hzone (conj _ _))))).
  - unfold callee, boundary. simpl. split; [reflexivity|exact Hchain].
  - unfold boundary. constructor; [simpl; lia|exact Hcutoffs].
Qed.

(** A frozen caller color advanced through a safe callee is either still
    represented by the caller snapshot or has acquired the snapshot's
    root-scoped resume-origin witness.  The only interesting callee step is
    an RDM frame join.  Its roots reflect through class-bounded adaptation to
    caller [Mut], [Imm], or [RDM] roots: [Mut] is independently caller-owned,
    [Imm] contradicts the runtime mutability of the source color, and [RDM]
    is the corresponding caller-frame join. *)
Lemma safe_call_frozen_step_covered_by_old_or_resume_origin :
  forall CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty snapshot (fallback : Prop) source target,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    authority_colors_runtime_mutable h
      snapshot.(frozen_snapshot_current_colors) ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h
        (mk_watched_frame caller_authority sGamma rGamma)
        snapshot.(frozen_snapshot_current_colors))
      snapshot.(frozen_snapshot_current_colors) ->
    (forall snapshot_mode active_mode location,
      authority_mode_dangerous snapshot_mode ->
      authority_mode_dangerous active_mode ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (snapshot_mode, location) ->
      (In authority_flow_state
         (independent_active_authority_colors CT h
           (mk_watched_frame caller_authority sGamma rGamma))
         (active_mode, location) \/
       typed_root RDM sGamma rGamma location) ->
      fallback) ->
    frozen_state_covered_by_old_or snapshot fallback source ->
    frozen_caller_authority_step CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals))) source target ->
    frozen_state_covered_by_old_or snapshot fallback target.
Proof.
  intros CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty snapshot fallback source target Hwf Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs Hruntime Hclosed Horigins Hsource Hstep
    Htarget_mode.
  have Hsource_mode : authority_mode_dangerous (fst source).
  { inversion Hstep; subst; simpl;
      first [left; reflexivity | right; reflexivity]. }
  destruct (Hsource Hsource_mode) as
    [[old_mode [Hold_mode Hold_color]] | Horigin];
    [|right; exact Horigin].
  inversion Hstep; subst; simpl in *.
  - left. exists old_mode. split; [exact Hold_mode|].
    eapply frozen_caller_color_dangerous_retained; eauto.
  - left. exists old_mode. split; [exact Hold_mode|].
    eapply frozen_caller_color_dangerous_retained; eauto.
  - left. exists FlowProspective. split; [right; reflexivity|].
    eapply frozen_caller_color_dangerous_reverse_rdm; eauto.
  - left. exists FlowProspective. split; [right; reflexivity|].
    eapply frozen_caller_color_dangerous_reverse_rdm; eauto.
  - destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x
      method y args sGamma' vals ly cy runtime_mdef left Hwf Htyping Hscope
      Hvalue Hbase Hfind Hargs H) as
      [left_T [Hleft_get Hleft_cases]].
    destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x
      method y args sGamma' vals ly cy runtime_mdef right Hwf Htyping Hscope
      Hvalue Hbase Hfind Hargs H0) as
      [right_T [Hright_get Hright_cases]].
    assert (left_T = Ty) by congruence.
    assert (right_T = Ty) by congruence. subst left_T right_T.
    destruct Hleft_cases as [[Hleft_shape Hleft_root] |
        [Hleft_ro [Hleft_eq Hleft_ro_root]]];
      destruct Hright_cases as [[Hright_shape Hright_root] |
        [Hright_ro [Hright_eq Hright_ro_root]]].
    + destruct Hleft_shape as [Hmut | [Himm | Hrdm]].
      * right. apply (Horigins old_mode FlowPowered left Hold_mode
          (or_introl eq_refl) Hold_color).
        left. unfold independent_active_authority_colors.
        eapply executing_authority_typed_mut_root_is_powered.
        rewrite Hmut in Hleft_root. exact Hleft_root.
      * have Hmutable := Hruntime old_mode left Hold_color.
        have Himmutable := typed_imm_root_runtime_immutable CT sGamma rGamma
          h left Hwf (ltac:(rewrite Himm in Hleft_root; exact Hleft_root)).
        congruence.
      * left. exists FlowProspective. split; [right; reflexivity|].
        apply Hclosed. exists (old_mode, left). split; [exact Hold_color|].
        apply rt_step. destruct Hold_mode as [-> | ->].
        -- apply frozen_caller_powered_frame_join.
           ++ rewrite Hrdm in Hleft_root. exact Hleft_root.
           ++ rewrite Hrdm in Hright_root. exact Hright_root.
        -- apply frozen_caller_prospective_frame_join.
           ++ rewrite Hrdm in Hleft_root. exact Hleft_root.
           ++ rewrite Hrdm in Hright_root. exact Hright_root.
    + destruct Hleft_shape as [Hq | [Hq | Hq]]; congruence.
    + destruct Hright_shape as [Hq | [Hq | Hq]]; congruence.
    + left. exists old_mode. split; [exact Hold_mode|].
      rewrite Hright_eq. rewrite <- Hleft_eq. exact Hold_color.
  - destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x
      method y args sGamma' vals ly cy runtime_mdef left Hwf Htyping Hscope
      Hvalue Hbase Hfind Hargs H) as
      [left_T [Hleft_get Hleft_cases]].
    destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x
      method y args sGamma' vals ly cy runtime_mdef right Hwf Htyping Hscope
      Hvalue Hbase Hfind Hargs H0) as
      [right_T [Hright_get Hright_cases]].
    assert (left_T = Ty) by congruence.
    assert (right_T = Ty) by congruence. subst left_T right_T.
    destruct Hleft_cases as [[Hleft_shape Hleft_root] |
        [Hleft_ro [Hleft_eq Hleft_ro_root]]];
      destruct Hright_cases as [[Hright_shape Hright_root] |
        [Hright_ro [Hright_eq Hright_ro_root]]].
    + destruct Hleft_shape as [Hmut | [Himm | Hrdm]].
      * right. apply (Horigins old_mode FlowPowered left Hold_mode
          (or_introl eq_refl) Hold_color).
        left. unfold independent_active_authority_colors.
        eapply executing_authority_typed_mut_root_is_powered.
        rewrite Hmut in Hleft_root. exact Hleft_root.
      * have Hmutable := Hruntime old_mode left Hold_color.
        have Himmutable := typed_imm_root_runtime_immutable CT sGamma rGamma
          h left Hwf (ltac:(rewrite Himm in Hleft_root; exact Hleft_root)).
        congruence.
      * left. exists FlowProspective. split; [right; reflexivity|].
        apply Hclosed. exists (old_mode, left). split; [exact Hold_color|].
        apply rt_step. destruct Hold_mode as [-> | ->].
        -- apply frozen_caller_powered_frame_join.
           ++ rewrite Hrdm in Hleft_root. exact Hleft_root.
           ++ rewrite Hrdm in Hright_root. exact Hright_root.
        -- apply frozen_caller_prospective_frame_join.
           ++ rewrite Hrdm in Hleft_root. exact Hleft_root.
           ++ rewrite Hrdm in Hright_root. exact Hright_root.
    + destruct Hleft_shape as [Hq | [Hq | Hq]]; congruence.
    + destruct Hright_shape as [Hq | [Hq | Hq]]; congruence.
    + left. exists old_mode. split; [exact Hold_mode|].
      rewrite Hright_eq. rewrite <- Hleft_eq. exact Hold_color.
  - left. exists FlowProspective. split; [right; reflexivity|].
    destruct Hold_mode as [-> | ->].
    + apply Hclosed. exists (FlowPowered, location).
      split; [exact Hold_color|]. apply rt_step.
      apply frozen_caller_mark_prospective.
    + exact Hold_color.
Qed.

(** The internal call-pop obligation is deliberately disjunctive.  A
    dangerous color in the resumed caller must either be represented by a
    dangerous color of the completed callee phase, or its location must be
    outside the protected zone.  Requiring callee-color containment alone
    would be too strong for a fresh flexible-return component that is
    harmless but was not present in the callee's entry frame. *)
Definition executing_authority_call_pop_safe
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (callee : watched_frame)
  (callee_incoming : Ensemble authority_flow_state)
  (caller : watched_frame)
  (caller_incoming : Ensemble authority_flow_state) : Prop :=
  forall mode location,
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT h caller caller_incoming)
      (mode, location) ->
    (exists callee_mode,
      authority_mode_dangerous callee_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h callee callee_incoming)
        (callee_mode, location)) \/
    ~ In Loc Z location.

Lemma phased_dangerous_path_has_frozen_origin_or_owned_promotion :
  forall CT h frame source target,
    authority_mode_dangerous (fst target) ->
    phased_authority_frame_connected CT h frame source target ->
    (authority_mode_dangerous (fst source) /\
      frozen_caller_authority_connected CT h frame source target) \/
    (exists anchor,
      frame_owned_location CT h frame anchor /\
      frozen_caller_authority_connected CT h frame
        (FlowPowered, anchor) target).
Proof.
  intros CT h frame source target Htarget Hconnected.
  induction Hconnected.
  - inversion H; subst; simpl in *.
    + left. split; [left; reflexivity|].
      apply rt_step. apply frozen_caller_retained. exact H0.
    + left. split; [right; reflexivity|].
      apply rt_step. apply frozen_caller_prospective_retained. exact H0.
    + left. split; [right; reflexivity|].
      apply rt_step. apply frozen_caller_prospective_rdm_backward. exact H0.
    + left. split; [left; reflexivity|].
      apply rt_step. apply frozen_caller_reverse_rdm. exact H0.
    + destruct Htarget as [Hbad | Hbad]; discriminate.
    + destruct Htarget as [Hbad | Hbad]; discriminate.
    + left. split; [left; reflexivity|].
      apply rt_step. eapply frozen_caller_powered_frame_join; eauto.
    + left. split; [right; reflexivity|].
      apply rt_step. eapply frozen_caller_prospective_frame_join; eauto.
    + destruct Htarget as [Hbad | Hbad]; discriminate.
    + destruct Htarget as [Hbad | Hbad]; discriminate.
    + destruct Htarget as [Hbad | Hbad]; discriminate.
    + left. split; [left; reflexivity|].
      apply rt_step. apply frozen_caller_mark_prospective.
    + right. eexists. split; [eassumption|apply rt_refl].
  - left. split; [exact Htarget|apply rt_refl].
  - destruct (IHHconnected2 Htarget) as
      [[Hmiddle Hfrozen_tail] | [anchor [Howned Hfrozen_tail]]].
    + destruct (IHHconnected1 Hmiddle) as
        [[Hsource Hfrozen_prefix] | [anchor [Howned Hfrozen_prefix]]].
      * left. split; [exact Hsource|].
        eapply rt_trans; eauto.
      * right. exists anchor. split; [exact Howned|].
        eapply rt_trans; eauto.
    + right. exists anchor. split; assumption.
Qed.

(** A dangerous color created independently by the active frame belongs to
    the prospective component of one of that frame's mutable-authority
    roots.  Promotions are handled by restarting at the frame-owned anchor,
    then projecting the remaining frozen path prospectively. *)
Lemma independent_active_dangerous_has_prospective_root :
  forall CT h active mode target,
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    authority_context_sound h active.(frame_renv)
      active.(frame_authority) ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (independent_active_authority_colors CT h active) (mode, target) ->
    exists root,
      mutable_authority_root active h root /\
      frozen_caller_authority_connected CT h active
        (FlowProspective, root) (FlowProspective, target).
Proof.
  intros CT h active mode target Hwf Hsound Hmode [seed [Hseed Hpath]].
  destruct (phased_dangerous_path_has_frozen_origin_or_owned_promotion CT h
    active seed (mode, target) Hmode Hpath) as
    [[Hseed_mode Hfrozen] | [anchor [Howned Hfrozen]]].
  - inversion Hseed; subst.
    + inversion H.
    + destruct H as [anchor [Heq Howned]]. inversion Heq; subst.
      destruct Howned as [root [Hroot Hroot_anchor]].
      exists root. split.
      * have Hruntime : r_muttype h root = Some Mut_r.
        { eapply frame_capability_root_runtime_mutable; eauto. }
        destruct Hroot as
          [variable [T [Htype [Hvalue [Hmut | [Hrdm Hauthority]]]]]].
        -- left. exists variable, T. repeat split; assumption.
        -- right. split.
           ++ exists variable, T. repeat split; assumption.
           ++ exact Hruntime.
      * eapply rt_trans.
        -- eapply frozen_caller_prospective_retained_forward.
           exact Hroot_anchor.
        -- exact (frozen_caller_connected_as_prospective CT h active
             (FlowPowered, anchor) (mode, target) Hfrozen).
  - destruct Howned as [root [Hroot Hroot_anchor]].
    exists root. split.
    + have Hruntime : r_muttype h root = Some Mut_r.
      { eapply frame_capability_root_runtime_mutable; eauto. }
      destruct Hroot as
        [variable [T [Htype [Hvalue [Hmut | [Hrdm Hauthority]]]]]].
      * left. exists variable, T. repeat split; assumption.
      * right. split.
        -- exists variable, T. repeat split; assumption.
        -- exact Hruntime.
    + eapply rt_trans.
      * eapply frozen_caller_prospective_retained_forward.
        exact Hroot_anchor.
      * exact (frozen_caller_connected_as_prospective CT h active
          (FlowPowered, anchor) (mode, target) Hfrozen).
Qed.

(** Coverage used only while proving that a write preserves a boundary-local
    prospective component.  The first frame is the tracked live frame whose
    old component is being advanced; the second is the currently executing
    frame that owns or types the newly installed edge. *)
Definition prospective_location_covered_by_old_or_active
  (CT : class_table) (h : heap) (old_frame : watched_frame)
  (active : watched_frame) (location : Loc) : Prop :=
  (exists old_root,
    mutable_authority_root old_frame h old_root /\
    frozen_caller_authority_connected CT h old_frame
      (FlowProspective, old_root) (FlowProspective, location)) \/
  exists active_root,
    mutable_authority_root active h active_root /\
    frozen_caller_authority_connected CT h active
      (FlowProspective, active_root) (FlowProspective, location).

Lemma prospective_location_covered_runtime_mutable :
  forall CT h old_frame active location,
    wf_r_config CT old_frame.(frame_senv) old_frame.(frame_renv) h ->
    authority_context_sound h old_frame.(frame_renv)
      old_frame.(frame_authority) ->
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    authority_context_sound h active.(frame_renv) active.(frame_authority) ->
    prospective_location_covered_by_old_or_active CT h old_frame active
      location ->
    r_muttype h location = Some Mut_r.
Proof.
  intros CT h old_frame active location Hold_wf Hold_sound Hactive_wf
    Hactive_sound [[old_root [Hold_root Hold]] |
      [active_root [Hactive_root Hpath]]].
  - have Hroot_runtime := mutable_authority_root_runtime_mutable CT h
      old_frame old_root Hold_wf Hold_sound Hold_root.
    have Hphased := frozen_caller_authority_connected_is_phased CT h old_frame
      (FlowProspective, old_root) (FlowProspective, location) Hold.
    exact (phased_authority_frame_connected_preserves_runtime_mutability CT h
      old_frame (FlowProspective, old_root) (FlowProspective, location) Mut_r
      Hold_wf Hphased Hroot_runtime).
  - have Hactive_runtime := mutable_authority_root_runtime_mutable CT h active
      active_root Hactive_wf Hactive_sound Hactive_root.
    have Hphased := frozen_caller_authority_connected_is_phased CT h active
      (FlowProspective, active_root) (FlowProspective, location) Hpath.
    exact (phased_authority_frame_connected_preserves_runtime_mutability CT h
      active (FlowProspective, active_root) (FlowProspective, location) Mut_r
      Hactive_wf Hphased Hactive_runtime).
Qed.

Lemma active_owned_has_prospective_root :
  forall CT h active location,
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    authority_context_sound h active.(frame_renv) active.(frame_authority) ->
    frame_owned_location CT h active location ->
    exists root,
      mutable_authority_root active h root /\
      frozen_caller_authority_connected CT h active
        (FlowProspective, root) (FlowProspective, location).
Proof.
  intros CT h active location Hwf Hsound [root [Hroot Hreachable]].
  exists root. split.
  - have Hruntime := frame_capability_root_runtime_mutable CT h active root
      Hwf Hsound Hroot.
    destruct Hroot as
      [variable [T [Htype [Hvalue [Hmut | [Hrdm Hauthority]]]]]].
    + left. exists variable, T. repeat split; assumption.
    + right. split.
      * exists variable, T. repeat split; assumption.
      * exact Hruntime.
  - eapply frozen_caller_prospective_retained_forward. exact Hreachable.
Qed.

Lemma frozen_prospective_step_after_safe_field_update_covered :
  forall CT h old_frame active lx old field written source target,
    wf_r_config CT old_frame.(frame_senv) old_frame.(frame_renv) h ->
    authority_context_sound h old_frame.(frame_renv)
      old_frame.(frame_authority) ->
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    authority_context_sound h active.(frame_renv) active.(frame_authority) ->
    runtime_getObj h lx = Some old ->
    authority_safe_field_endpoints CT h active lx written ->
    prospective_location_covered_by_old_or_active CT h old_frame active
      source ->
    frozen_caller_authority_step CT
      (update_field h lx field (Iot written)) old_frame
      (FlowProspective, source) (FlowProspective, target) ->
    prospective_location_covered_by_old_or_active CT h old_frame active
      target.
Proof.
  intros CT h old_frame active lx old field written source target Hold_wf
    Hold_sound Hactive_wf Hactive_sound Hobj Hendpoints Hsource Hstep.
  have Hsource_runtime := prospective_location_covered_runtime_mutable CT h
    old_frame active source Hold_wf Hold_sound Hactive_wf Hactive_sound
    Hsource.
  inversion Hstep; subst.
  - destruct (retained_edge_after_field_update CT h lx old field
      (Iot written) source target Hobj H1) as
      [Hold_edge | [Heq_left [Heq_value Hnew_edge]]].
    + destruct Hsource as
        [[old_component_root [Hold_root Hold_path]] |
         [active_root [Hactive_root Hpath]]].
      * left. exists old_component_root. split; [exact Hold_root|].
        eapply rt_trans; [exact Hold_path|].
        apply rt_step. apply frozen_caller_prospective_retained.
        exact Hold_edge.
      * right. exists active_root. split; [exact Hactive_root|].
        eapply rt_trans; [exact Hpath|].
        apply rt_step. apply frozen_caller_prospective_retained.
        exact Hold_edge.
    + injection Heq_value as Heq_right. subst source target.
      inversion Hendpoints; subst.
      * right. eapply active_owned_has_prospective_root; eauto.
      * rewrite H in Hsource_runtime. discriminate.
      * right. exists written. split.
        -- right. split; [exact H0|].
           destruct (active_rdm_roots_share_runtime_context CT
             active.(frame_senv) active.(frame_renv) h lx written Hactive_wf
             H H0) as [runtime_q [Hleft_runtime Hright_runtime]].
           rewrite Hsource_runtime in Hleft_runtime.
           injection Hleft_runtime as <-. exact Hright_runtime.
        -- apply rt_refl.
  - destruct (mutable_edge_after_field_update CT h lx old field
      (Iot written) target source Hobj H1) as
      [Hold_edge | [Heq_right [Heq_value Hnew_edge]]].
    + destruct Hsource as
        [[old_component_root [Hold_root Hold_path]] |
         [active_root [Hactive_root Hpath]]].
      * left. exists old_component_root. split; [exact Hold_root|].
        eapply rt_trans; [exact Hold_path|].
        apply rt_step. apply frozen_caller_prospective_rdm_backward.
        exact Hold_edge.
      * right. exists active_root. split; [exact Hactive_root|].
        eapply rt_trans; [exact Hpath|].
        apply rt_step. apply frozen_caller_prospective_rdm_backward.
        exact Hold_edge.
    + injection Heq_value as Heq_left. subst source target.
      inversion Hendpoints; subst.
      * right. eapply active_owned_has_prospective_root; eauto.
      * rewrite H0 in Hsource_runtime. discriminate.
      * right. exists lx. split.
        -- right. split; [exact H|].
           destruct (active_rdm_roots_share_runtime_context CT
             active.(frame_senv) active.(frame_renv) h lx written Hactive_wf
             H H0) as [runtime_q [Hleft_runtime Hright_runtime]].
           rewrite Hsource_runtime in Hright_runtime.
           injection Hright_runtime as <-. exact Hleft_runtime.
        -- apply rt_refl.
  - have Htarget_runtime : r_muttype h target = Some Mut_r.
    { destruct (active_rdm_roots_share_runtime_context CT
        old_frame.(frame_senv) old_frame.(frame_renv) h source target Hold_wf
        H1 H2) as [runtime_q [Hleft_runtime Hright_runtime]].
      rewrite Hsource_runtime in Hleft_runtime.
      injection Hleft_runtime as <-. exact Hright_runtime. }
    left. exists target. split.
    + right. split; [exact H2|exact Htarget_runtime].
    + apply rt_refl.
Qed.

Definition prospective_state_covered_by_old_or_active
  (CT : class_table) (h : heap) (old_frame active : watched_frame)
  (state : authority_flow_state) : Prop :=
  fst state = FlowProspective /\
  prospective_location_covered_by_old_or_active CT h old_frame active
    (snd state).

Lemma frozen_state_step_after_safe_field_update_covered :
  forall CT h old_frame active lx old field written source target,
    wf_r_config CT old_frame.(frame_senv) old_frame.(frame_renv) h ->
    authority_context_sound h old_frame.(frame_renv)
      old_frame.(frame_authority) ->
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    authority_context_sound h active.(frame_renv) active.(frame_authority) ->
    runtime_getObj h lx = Some old ->
    authority_safe_field_endpoints CT h active lx written ->
    prospective_state_covered_by_old_or_active CT h old_frame active source ->
    frozen_caller_authority_step CT
      (update_field h lx field (Iot written)) old_frame source target ->
    prospective_state_covered_by_old_or_active CT h old_frame active target.
Proof.
  intros CT h old_frame active lx old field written
    [source_mode source] [target_mode target] Hold_wf Hold_sound Hactive_wf
    Hactive_sound Hobj Hendpoints [Hsource_mode Hsource] Hstep. simpl in *.
  subst source_mode.
  have Htarget_mode : target_mode = FlowProspective.
  { inversion Hstep; reflexivity. }
  subst target_mode. split; [reflexivity|].
  eapply frozen_prospective_step_after_safe_field_update_covered; eauto.
Qed.

Lemma frozen_state_connected_after_safe_field_update_covered :
  forall CT h old_frame active lx old field written source target,
    wf_r_config CT old_frame.(frame_senv) old_frame.(frame_renv) h ->
    authority_context_sound h old_frame.(frame_renv)
      old_frame.(frame_authority) ->
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    authority_context_sound h active.(frame_renv) active.(frame_authority) ->
    runtime_getObj h lx = Some old ->
    authority_safe_field_endpoints CT h active lx written ->
    prospective_state_covered_by_old_or_active CT h old_frame active source ->
    frozen_caller_authority_connected CT
      (update_field h lx field (Iot written)) old_frame source target ->
    prospective_state_covered_by_old_or_active CT h old_frame active target.
Proof.
  intros CT h old_frame active lx old field written source target Hold_wf
    Hold_sound Hactive_wf Hactive_sound Hobj Hendpoints Hsource Hconnected.
  induction Hconnected.
  - eapply frozen_state_step_after_safe_field_update_covered; eauto.
  - exact Hsource.
  - apply IHHconnected2. apply IHHconnected1. exact Hsource.
Qed.

Lemma live_prospective_mutable_authority_components_after_safe_field_update :
  forall CT cutoff active stack h lx old field written,
    live_frames_wf CT h active stack ->
    live_frames_authority_sound h active stack ->
    live_prospective_mutable_authority_components_after_cutoff CT h cutoff
      active stack ->
    runtime_getObj h lx = Some old ->
    authority_safe_field_endpoints CT h active lx written ->
    live_prospective_mutable_authority_components_after_cutoff CT
      (update_field h lx field (Iot written)) cutoff active stack.
Proof.
  intros CT cutoff active stack h lx old field written Hframes Hsounds Hold
    Hobj Hendpoints frame root target Hlive [Hroot Hpath].
  have Hframe_wf := live_frame_member_wf CT h active stack frame Hframes Hlive.
  have Hframe_sound := live_frame_member_authority_sound h active stack frame
    Hsounds Hlive.
  have Hactive_wf := live_frame_member_wf CT h active stack active Hframes
    (live_frame_active active stack).
  have Hactive_sound := live_frame_member_authority_sound h active stack
    active Hsounds (live_frame_active active stack).
  have Hroot_old : mutable_authority_root frame h root.
  { destruct Hroot as [Hmut | [Hrdm Hruntime]].
    - left. exact Hmut.
    - right. split; [exact Hrdm|].
      rewrite r_muttype_update_field_preserve in Hruntime. exact Hruntime. }
  have Hsource : prospective_state_covered_by_old_or_active CT h frame active
      (FlowProspective, root).
  { split; [reflexivity|]. left. exists root. split.
    - exact Hroot_old.
    - apply rt_refl. }
  have Htarget := frozen_state_connected_after_safe_field_update_covered CT h
    frame active lx old field written (FlowProspective, root)
    (FlowProspective, target) Hframe_wf Hframe_sound Hactive_wf Hactive_sound
    Hobj Hendpoints Hsource Hpath.
  destruct Htarget as [_
    [[old_root [Hold_root Hold_path]] |
     [active_root [Hactive_root Hactive_path]]]].
  - eapply Hold with (frame := frame) (root := old_root).
    + exact Hlive.
    + split; assumption.
  - eapply Hold with (frame := active) (root := active_root).
    + constructor.
    + split; assumption.
Qed.

Lemma frozen_callee_side_prospective_components_after_safe_field_update :
  forall CT P Z cutoff active stack incoming snapshots h lx old field written,
    principled_phased_authority_live_history_state CT P Z cutoff
      active stack incoming h ->
    frozen_callee_side_prospective_components_after_boundaries CT h active
      snapshots stack ->
    runtime_getObj h lx = Some old ->
    authority_safe_field_endpoints CT h active lx written ->
    frozen_callee_side_prospective_components_after_boundaries CT
      (update_field h lx field (Iot written)) active
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) active snapshots) stack.
Proof.
  intros CT P Z cutoff active stack incoming snapshots h lx old field written
    Hstate Hold Hobj Hendpoints snapshot boundary above below Hpartition.
  destruct (advance_frozen_snapshot_live_partition_reflects CT
    (update_field h lx field (Iot written)) active snapshots stack snapshot
    boundary above below Hpartition) as [old_snapshot Hold_partition].
  have Hold_components := Hold old_snapshot boundary above below
    Hold_partition.
  have Hframes := proj1 (proj2 (proj2 (proj2 (proj2 Hstate)))).
  have Hsounds := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hstate))))).
  have Habove_frames := live_call_partition_above_frames_wf CT h active stack
    boundary above below (frozen_snapshot_live_partition_is_live_call
      snapshots stack old_snapshot boundary above below active Hold_partition)
    Hframes.
  have Habove_sounds := live_call_partition_above_frames_authority_sound h
    active stack boundary above below
    (frozen_snapshot_live_partition_is_live_call snapshots stack old_snapshot
      boundary above below active Hold_partition) Hsounds.
  eapply live_prospective_mutable_authority_components_after_safe_field_update;
    eauto.
Qed.

Lemma private_fresh_frozen_statement_after_field_write :
  forall CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    x field y sGamma' rGamma' h',
    private_fresh_frozen_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots h ->
    stmt_typing CT sGamma mt (SFldWrite x field y) sGamma' ->
    readonly_state_method_scope mt ->
    eval_stmt CT rGamma h (SFldWrite x field y) OK rGamma' h' ->
    private_fresh_frozen_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma' rGamma') stack incoming
      (advance_frozen_caller_snapshots CT h'
        (mk_watched_frame authority sGamma' rGamma') snapshots) h'.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    x field y sGamma' rGamma' h'
    [Hprivate [Hcomponents [Hprospective Hafter]]] Htyping Hscope Heval.
  have Hfrozen := proj1 Hprivate.
  have Hmain := proj1 Hfrozen.
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Heffect := typed_field_write_component_effect CT authority sGamma mt
    rGamma h x field y sGamma' rGamma' h' Hwf Htyping Hscope Heval.
  have Hpost := private_frozen_statement_after_field_write CT P Z cutoff
    authority sGamma mt rGamma h stack incoming snapshots x field y sGamma'
    rGamma' h' Hprivate Htyping Hscope Heval.
  assert (HsGamma : sGamma' = sGamma) by
    (inversion Htyping; reflexivity).
  assert (HrGamma : rGamma' = rGamma) by
    (inversion Heval; reflexivity).
  subst sGamma' rGamma'. split; [exact Hpost|].
  destruct Heffect as
    [[Hruntimes [Hmutable [Hretained Howned]]] |
     [lx [old [written [Hheap [Hobj Hendpoints]]]]]].
  - split.
    + eapply frozen_callee_side_components_after_graph_reflection; eauto.
    + split.
      * eapply frozen_callee_side_prospective_components_after_graph_reflection;
          eauto.
      * eapply advance_snapshot_boundaries_after_cutoff. exact Hafter.
  - subst h'.
    split.
    + eapply frozen_callee_side_components_after_safe_field_update; eauto.
    + split.
      * eapply frozen_callee_side_prospective_components_after_safe_field_update;
          eauto.
      * eapply advance_snapshot_boundaries_after_cutoff. exact Hafter.
Qed.

(** Private evidence that a color observed while the callee executes really
    originates in authority of the suspended caller.  In particular, mere
    membership in the callee's executing colors is not enough: independently
    owned callee authority is demoted at return. *)
Definition resumed_caller_frozen_origin
  (CT : class_table) (h : heap) (caller : watched_frame)
  (caller_incoming : Ensemble authority_flow_state)
  (state : authority_flow_state) : Prop :=
  frozen_authority_origin CT h caller caller_incoming state.

Lemma resumed_caller_incoming_has_frozen_origin :
  forall CT h caller caller_incoming state,
    authority_mode_dangerous (fst state) ->
    In authority_flow_state caller_incoming state ->
    resumed_caller_frozen_origin CT h caller caller_incoming state.
Proof.
  intros CT h caller caller_incoming state Hmode Hincoming.
  exists state. split.
  - left. split; assumption.
  - apply rt_refl.
Qed.

Lemma resumed_caller_owned_has_frozen_origin :
  forall CT h caller caller_incoming anchor,
    frame_owned_location CT h caller anchor ->
    resumed_caller_frozen_origin CT h caller caller_incoming
      (FlowPowered, anchor).
Proof.
  intros CT h caller caller_incoming anchor Howned.
  exists (FlowPowered, anchor). split.
  - right. exists anchor. split; [reflexivity|exact Howned].
  - apply rt_refl.
Qed.

Lemma resumed_caller_frozen_origin_connected :
  forall CT h caller caller_incoming source target,
    resumed_caller_frozen_origin CT h caller caller_incoming source ->
    frozen_caller_authority_connected CT h caller source target ->
    resumed_caller_frozen_origin CT h caller caller_incoming target.
Proof.
  intros CT h caller caller_incoming source target
    [seed [Hseed Hprefix]] Hsuffix.
  exists seed. split; [exact Hseed|].
  eapply rt_trans; eauto.
Qed.

(** Classification maintained while a resumed caller follows only dangerous
    frozen flow.  The callee-color case carries the private caller-origin
    evidence above.  The final case remembers a whole resume-exposure set
    plus its already-derived protected-zone certificate. *)
Definition tracked_resume_frozen_color_class
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (callee : watched_frame) (callee_incoming : Ensemble authority_flow_state)
  (caller : watched_frame) (caller_incoming : Ensemble authority_flow_state)
  (snapshot : frozen_caller_color_snapshot)
  (state : authority_flow_state) : Prop :=
  In authority_flow_state snapshot.(frozen_snapshot_current_colors) state \/
  (In authority_flow_state
     (executing_authority_color_set CT h callee callee_incoming) state /\
   resumed_caller_frozen_origin CT h caller caller_incoming state) \/
  (In authority_flow_state
      snapshot.(frozen_snapshot_current_resume_exposure) state /\
   forall mode location,
     authority_mode_dangerous mode ->
     In authority_flow_state
       snapshot.(frozen_snapshot_current_resume_exposure) (mode, location) ->
     ~ In Loc Z location).

(** Root-scoped pop classification for a harmless frozen/active overlap.
    The overlap itself may be fresh and is therefore not forbidden.  Its
    captured resume-root witness is classified by the snapshot's pairwise
    join certificate; the requested old caller target is already present in
    the frozen resume-exposure set. *)
Lemma tracked_active_overlap_join_has_class_from_resume_origin :
  forall CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller caller_incoming target,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some snapshot :: snapshots) h ->
    (exists root_mode root,
      authority_mode_dangerous root_mode /\
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (root_mode, root) /\
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) root) ->
    In Loc snapshot.(frozen_snapshot_resume_rdm_roots) target ->
    r_muttype h target = Some Mut_r ->
    tracked_resume_frozen_color_class CT h Z active active_incoming caller
      caller_incoming snapshot (FlowProspective, target).
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller caller_incoming target Hfull
    [root_mode [root [Hroot_mode [Hroot_color Hroot]]]]
    Htarget Htarget_runtime.
  destruct Hfull as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous &
      Havoid & Hroots & Hexposure & Hresume & Hjoins & Hentry_covered &
      Hphase_covered).
  have Hsnapshot : List.In (Some snapshot) (Some snapshot :: snapshots) by
    (simpl; auto).
  have Htarget_exposure : In authority_flow_state
      snapshot.(frozen_snapshot_current_resume_exposure)
      (FlowProspective, target).
  { eapply (proj2 (proj2 (proj2 (proj2 Hexposure)))); eauto. }
  destruct (Hjoins snapshot root_mode root Hsnapshot Hroot_mode Hroot_color
    Hroot) as [[entry_mode [Hentry_mode Hentry]] | Hsafe].
  - left. eapply (Hentry_covered snapshot entry_mode root Hsnapshot
      Hentry_mode Hentry Hroot). exact Htarget_exposure.
  - right. right. split; [exact Htarget_exposure|].
    intros mode location Hmode Hcolor. eapply Hsafe; eauto.
Qed.

Inductive frozen_caller_authority_nonjoin_step
  (CT : class_table) (h : heap) :
  authority_flow_state -> authority_flow_state -> Prop :=
| frozen_nonjoin_retained : forall left right,
    retained_mut_edge CT h left right ->
    frozen_caller_authority_nonjoin_step CT h
      (FlowPowered, left) (FlowPowered, right)
| frozen_nonjoin_prospective_retained : forall left right,
    retained_mut_edge CT h left right ->
    frozen_caller_authority_nonjoin_step CT h
      (FlowProspective, left) (FlowProspective, right)
| frozen_nonjoin_prospective_rdm_backward : forall left right,
    mutable_edge CT h right left ->
    frozen_caller_authority_nonjoin_step CT h
      (FlowProspective, left) (FlowProspective, right)
| frozen_nonjoin_reverse_rdm : forall left right,
    mutable_edge CT h right left ->
    frozen_caller_authority_nonjoin_step CT h
      (FlowPowered, left) (FlowProspective, right)
| frozen_nonjoin_mark_prospective : forall location,
    frozen_caller_authority_nonjoin_step CT h
      (FlowPowered, location) (FlowProspective, location).

Lemma frozen_nonjoin_step_in_frame :
  forall CT h frame source target,
    frozen_caller_authority_nonjoin_step CT h source target ->
    frozen_caller_authority_step CT h frame source target.
Proof.
  intros CT h frame source target Hstep. inversion Hstep; subst.
  - apply frozen_caller_retained. exact H.
  - apply frozen_caller_prospective_retained. exact H.
  - apply frozen_caller_prospective_rdm_backward. exact H.
  - apply frozen_caller_reverse_rdm. exact H.
  - apply frozen_caller_mark_prospective.
Qed.

Lemma frozen_nonjoin_step_is_phased :
  forall CT h frame source target,
    frozen_caller_authority_nonjoin_step CT h source target ->
    phased_authority_frame_step CT h frame source target.
Proof.
  intros CT h frame source target Hstep. inversion Hstep; subst.
  - apply phased_authority_retained. exact H.
  - apply phased_authority_prospective_retained. exact H.
  - apply phased_authority_prospective_rdm_backward. exact H.
  - apply phased_authority_reverse_rdm. exact H.
  - apply phased_authority_mark_prospective.
Qed.

(** Lossless proof-local provenance for resumed-caller flow.  Unlike the
    extensional class above, this object remembers the strictly smaller
    derivation that crossed each caller-frame RDM join.  The return proof can
    therefore peel a return-root source back to the join that introduced it,
    rather than postulating a global pop-compatibility premise. *)
Inductive tracked_resume_frozen_color_derivation
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (callee : watched_frame) (callee_incoming : Ensemble authority_flow_state)
  (caller : watched_frame) (caller_incoming : Ensemble authority_flow_state)
  (snapshot : frozen_caller_color_snapshot) :
  authority_flow_state -> Prop :=
| tracked_resume_from_snapshot : forall state,
    In authority_flow_state snapshot.(frozen_snapshot_current_colors) state ->
    In authority_flow_state caller_incoming state ->
    resumed_caller_frozen_origin CT h caller caller_incoming state ->
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot state
| tracked_resume_from_caller_owned : forall anchor,
    frame_owned_location CT h caller anchor ->
    In authority_flow_state
      (executing_authority_color_set CT h callee callee_incoming)
      (FlowPowered, anchor) ->
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot (FlowPowered, anchor)
| tracked_resume_by_nonjoin : forall source target,
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot source ->
    frozen_caller_authority_nonjoin_step CT h source target ->
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot target
| tracked_resume_by_frame_join : forall mode left right,
    authority_mode_dangerous mode ->
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot (mode, left) ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot (FlowProspective, right).

(** Relational structural measure for the lossless provenance object.  The
    derivation remains proof-irrelevant in [Prop]; recording its height as a
    second proposition nevertheless permits well-founded induction when a
    fresh-return path is rerouted through a strictly smaller predecessor. *)
Inductive tracked_resume_frozen_color_derivation_has_height
  CT h Z callee callee_incoming caller caller_incoming snapshot :
  forall state,
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot state -> nat -> Prop :=
| tracked_resume_snapshot_height : forall state Hsnapshot Hincoming Horigin,
    tracked_resume_frozen_color_derivation_has_height CT h Z callee
      callee_incoming caller caller_incoming snapshot state
      (tracked_resume_from_snapshot CT h Z callee callee_incoming caller
        caller_incoming snapshot state Hsnapshot Hincoming Horigin) 1
| tracked_resume_owned_height : forall anchor Howned Hcallee,
    tracked_resume_frozen_color_derivation_has_height CT h Z callee
      callee_incoming caller caller_incoming snapshot
      (FlowPowered, anchor)
      (tracked_resume_from_caller_owned CT h Z callee callee_incoming caller
        caller_incoming snapshot anchor Howned Hcallee) 1
| tracked_resume_nonjoin_height : forall source target previous Hstep n,
    tracked_resume_frozen_color_derivation_has_height CT h Z callee
      callee_incoming caller caller_incoming snapshot source previous n ->
    tracked_resume_frozen_color_derivation_has_height CT h Z callee
      callee_incoming caller caller_incoming snapshot target
      (tracked_resume_by_nonjoin CT h Z callee callee_incoming caller
        caller_incoming snapshot source target previous Hstep) (S n)
| tracked_resume_join_height : forall mode left right Hmode previous
    Hleft Hright n,
    tracked_resume_frozen_color_derivation_has_height CT h Z callee
      callee_incoming caller caller_incoming snapshot (mode, left) previous n ->
    tracked_resume_frozen_color_derivation_has_height CT h Z callee
      callee_incoming caller caller_incoming snapshot (FlowProspective, right)
      (tracked_resume_by_frame_join CT h Z callee callee_incoming caller
        caller_incoming snapshot mode left right Hmode previous Hleft Hright)
      (S n).

(** Second-order provenance for advancing an older snapshot's resume
    exposure across a nested return.  This is intentionally distinct from
    [nested_frozen_pop_derivation]: exposure membership is not ordinary
    frozen-color membership, and conflating the two would silently assume
    the very nested-pop fact that must be proved. *)
Inductive nested_resume_exposure_pop_derivation
  (CT : class_table) (h : heap) (caller : watched_frame)
  (exposure : Ensemble authority_flow_state) :
  authority_flow_state -> Prop :=
| nested_exposure_from_base : forall state,
    In authority_flow_state exposure state ->
    nested_resume_exposure_pop_derivation CT h caller exposure state
| nested_exposure_by_nonjoin : forall source target,
    nested_resume_exposure_pop_derivation CT h caller exposure source ->
    frozen_caller_authority_nonjoin_step CT h source target ->
    nested_resume_exposure_pop_derivation CT h caller exposure target
| nested_exposure_by_frame_join : forall mode left right,
    authority_mode_dangerous mode ->
    nested_resume_exposure_pop_derivation CT h caller exposure (mode, left) ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    nested_resume_exposure_pop_derivation CT h caller exposure
      (FlowProspective, right).

Lemma nested_resume_exposure_pop_step_derives :
  forall CT h caller exposure source target,
    authority_mode_dangerous (fst source) ->
    nested_resume_exposure_pop_derivation CT h caller exposure source ->
    frozen_caller_authority_step CT h caller source target ->
    nested_resume_exposure_pop_derivation CT h caller exposure target.
Proof.
  intros CT h caller exposure source target Hmode Hsource Hstep.
  inversion Hstep; subst; simpl in *.
  - eapply nested_exposure_by_nonjoin; eauto.
    apply frozen_nonjoin_retained. exact H.
  - eapply nested_exposure_by_nonjoin; eauto.
    apply frozen_nonjoin_prospective_retained. exact H.
  - eapply nested_exposure_by_nonjoin; eauto.
    apply frozen_nonjoin_prospective_rdm_backward. exact H.
  - eapply nested_exposure_by_nonjoin; eauto.
    apply frozen_nonjoin_reverse_rdm. exact H.
  - eapply nested_exposure_by_frame_join; eauto.
  - eapply nested_exposure_by_frame_join; eauto.
  - eapply nested_exposure_by_nonjoin; eauto.
    apply frozen_nonjoin_mark_prospective.
Qed.

(** Classification used only to transport older frozen slots across the
    immediate pop.  Unlike [tracked_resume_frozen_color_class], the completed
    callee alternative deliberately carries no immediate-caller origin: an
    older frozen base does not in general have one. *)
Definition nested_frozen_pop_color_class
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (callee : watched_frame) (callee_incoming : Ensemble authority_flow_state)
  (snapshot : frozen_caller_color_snapshot)
  (state : authority_flow_state) : Prop :=
  In authority_flow_state snapshot.(frozen_snapshot_current_colors) state \/
  In authority_flow_state
    (executing_authority_color_set CT h callee callee_incoming) state \/
  (In authority_flow_state
      snapshot.(frozen_snapshot_current_resume_exposure) state /\
   forall mode location,
     authority_mode_dangerous mode ->
     In authority_flow_state
       snapshot.(frozen_snapshot_current_resume_exposure) (mode, location) ->
     ~ In Loc Z location).

(** A tracked derivation that has not crossed a caller-frame RDM join is
    still represented by the frozen snapshot.  Caller-owned bases are folded
    into the same set by the exceptional channel-free pop argument, and
    non-join steps remain there because the snapshot is closed under the
    completed callee phase.  Otherwise the first alternative exposes a
    concrete join predecessor with a strictly smaller derivation. *)
Lemma tracked_derivation_is_snapshot_or_has_frame_join_predecessor :
  forall CT h Z callee callee_incoming caller caller_incoming snapshot state
    (derivation : tracked_resume_frozen_color_derivation CT h Z callee
      callee_incoming caller caller_incoming snapshot state)
    derivation_height,
    tracked_resume_frozen_color_derivation_has_height CT h Z callee
      callee_incoming caller caller_incoming snapshot state derivation
      derivation_height ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h callee
        snapshot.(frozen_snapshot_current_colors))
      snapshot.(frozen_snapshot_current_colors) ->
    (forall anchor,
      frame_owned_location CT h caller anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h callee callee_incoming)
        (FlowPowered, anchor) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (FlowPowered, anchor)) ->
    In authority_flow_state snapshot.(frozen_snapshot_current_colors) state \/
    exists predecessor_mode predecessor_location predecessor
      predecessor_height,
      authority_mode_dangerous predecessor_mode /\
      tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
        caller caller_incoming snapshot
        (predecessor_mode, predecessor_location) /\
      tracked_resume_frozen_color_derivation_has_height CT h Z callee
        callee_incoming caller caller_incoming snapshot
        (predecessor_mode, predecessor_location) predecessor
        predecessor_height /\
      typed_root RDM caller.(frame_senv) caller.(frame_renv)
        predecessor_location /\
      S predecessor_height <= derivation_height.
Proof.
  intros CT h Z callee callee_incoming caller caller_incoming snapshot state
    derivation derivation_height Hheight Hclosed Howned_snapshot.
  induction Hheight as
    [state Hsnapshot Hincoming Horigin
    |anchor Howned Hcallee
    |source target previous Hstep n Hprevious_height IH
    |mode left right Hmode previous Hleft Hright n Hprevious_height IH].
  - left. exact Hsnapshot.
  - left. eapply Howned_snapshot; eauto.
  - destruct IH as [Hsource_snapshot | Hjoin].
    + left. eapply Hclosed. exists source. split; [exact Hsource_snapshot|].
      apply rt_step. eapply frozen_nonjoin_step_in_frame. exact Hstep.
    + right. destruct Hjoin as
        [predecessor_mode [predecessor_location [predecessor
          [predecessor_height
            [Hpredecessor_mode [Hpredecessor
              [Hpredecessor_height [Hpredecessor_root Hbound]]]]]]]].
      exists predecessor_mode, predecessor_location, predecessor,
        predecessor_height. repeat split; try assumption. lia.
  - right. exists mode, left, previous, n.
    repeat split; try assumption. lia.
Qed.

(** Abstract normalization used by the fresh-return proof.  If derivation
    bases predate [boundary_cutoff] and a non-join step cannot enter the fresh
    suffix from an old source, then any derivation ending in that suffix must
    contain a caller-frame RDM join.  The derivation immediately before that
    join is short enough that joining it directly to another caller RDM root
    is a strictly smaller replacement for one more outer join. *)
Lemma tracked_fresh_derivation_has_frame_join_predecessor :
  forall CT h Z callee callee_incoming caller caller_incoming snapshot
    boundary_cutoff state
    (derivation : tracked_resume_frozen_color_derivation CT h Z callee
      callee_incoming caller caller_incoming snapshot state)
    derivation_height,
    tracked_resume_frozen_color_derivation_has_height CT h Z callee
      callee_incoming caller caller_incoming snapshot state derivation
      derivation_height ->
    (forall mode location,
      In authority_flow_state caller_incoming (mode, location) ->
      location < boundary_cutoff) ->
    (forall anchor,
      frame_owned_location CT h caller anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h callee callee_incoming)
        (FlowPowered, anchor) ->
      anchor < boundary_cutoff) ->
    (forall source target
        (source_derivation : tracked_resume_frozen_color_derivation CT h Z
          callee callee_incoming caller caller_incoming snapshot source)
        source_height,
      tracked_resume_frozen_color_derivation_has_height CT h Z callee
        callee_incoming caller caller_incoming snapshot source
        source_derivation source_height ->
      frozen_caller_authority_nonjoin_step CT h source target ->
      boundary_cutoff <= snd target ->
      boundary_cutoff <= snd source) ->
    boundary_cutoff <= snd state ->
    exists predecessor_mode predecessor_location predecessor
      predecessor_height,
      authority_mode_dangerous predecessor_mode /\
      tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
        caller caller_incoming snapshot
        (predecessor_mode, predecessor_location) /\
      tracked_resume_frozen_color_derivation_has_height CT h Z callee
        callee_incoming caller caller_incoming snapshot
        (predecessor_mode, predecessor_location) predecessor
        predecessor_height /\
      typed_root RDM caller.(frame_senv) caller.(frame_renv)
        predecessor_location /\
      S predecessor_height <= derivation_height.
Proof.
  intros CT h Z callee callee_incoming caller caller_incoming snapshot
    boundary_cutoff state derivation derivation_height Hheight Hincoming_old
    Howned_old Hnonjoin_back Hfresh.
  induction Hheight as
    [state Hsnapshot Hincoming Horigin
    |anchor Howned Hcallee
    |source target previous Hstep n Hprevious_height IH
    |mode left right Hmode previous Hleft Hright n Hprevious_height IH].
  - destruct state as [mode location]. simpl in *.
    have Hold := Hincoming_old mode location Hincoming. lia.
  - have Hold := Howned_old anchor Howned Hcallee. simpl in Hfresh. lia.
  - have Hsource_fresh := Hnonjoin_back source target previous n
      Hprevious_height Hstep Hfresh.
    destruct (IH Hsource_fresh) as
      [predecessor_mode [predecessor_location [predecessor
        [predecessor_height
          [Hpredecessor_mode [Hpredecessor
            [Hpredecessor_height [Hpredecessor_root Hbound]]]]]]]].
    exists predecessor_mode, predecessor_location, predecessor,
      predecessor_height. repeat split; try assumption. lia.
  - destruct (le_lt_dec boundary_cutoff left) as [Hleft_fresh | Hleft_old].
    + destruct (IH Hleft_fresh) as
        [predecessor_mode [predecessor_location [predecessor
          [predecessor_height
            [Hpredecessor_mode [Hpredecessor
              [Hpredecessor_height [Hpredecessor_root Hbound]]]]]]]].
      exists predecessor_mode, predecessor_location, predecessor,
        predecessor_height. repeat split; try assumption. lia.
    + exists mode, left, previous, n. repeat split; try assumption. lia.
Qed.

Lemma tracked_resume_frozen_step_derives :
  forall CT h Z callee callee_incoming caller caller_incoming snapshot
    source target,
    authority_mode_dangerous (fst source) ->
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot source ->
    frozen_caller_authority_step CT h caller source target ->
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot target.
Proof.
  intros CT h Z callee callee_incoming caller caller_incoming snapshot
    source target Hmode Hsource Hstep.
  inversion Hstep; subst; simpl in *.
  - eapply tracked_resume_by_nonjoin; eauto.
    apply frozen_nonjoin_retained. exact H.
  - eapply tracked_resume_by_nonjoin; eauto.
    apply frozen_nonjoin_prospective_retained. exact H.
  - eapply tracked_resume_by_nonjoin; eauto.
    apply frozen_nonjoin_prospective_rdm_backward. exact H.
  - eapply tracked_resume_by_nonjoin; eauto.
    apply frozen_nonjoin_reverse_rdm. exact H.
  - eapply tracked_resume_by_frame_join; eauto.
  - eapply tracked_resume_by_frame_join; eauto.
  - eapply tracked_resume_by_nonjoin; eauto.
    apply frozen_nonjoin_mark_prospective.
Qed.

Lemma tracked_resume_frozen_connected_derives :
  forall CT h Z callee callee_incoming caller caller_incoming snapshot
    source target,
    authority_mode_dangerous (fst source) ->
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot source ->
    frozen_caller_authority_connected CT h caller source target ->
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot target.
Proof.
  intros CT h Z callee callee_incoming caller caller_incoming snapshot
    source target Hmode Hsource Hconnected.
  induction Hconnected.
  - eapply tracked_resume_frozen_step_derives; eauto.
  - exact Hsource.
  - have Hmiddle_mode : authority_mode_dangerous (fst y).
    { eapply frozen_caller_authority_connected_preserves_dangerous; eauto. }
    have Hmiddle := IHHconnected1 Hmode Hsource.
    exact (IHHconnected2 Hmiddle_mode Hmiddle).
Qed.

Lemma tracked_resume_frozen_derivation_has_origin :
  forall CT h Z callee callee_incoming caller caller_incoming snapshot state,
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot state ->
    resumed_caller_frozen_origin CT h caller caller_incoming state.
Proof.
  intros CT h Z callee callee_incoming caller caller_incoming snapshot state
    Hderivation.
  induction Hderivation.
  - exact H1.
  - eapply resumed_caller_owned_has_frozen_origin. exact H.
  - eapply resumed_caller_frozen_origin_connected; [exact IHHderivation|].
    apply rt_step. eapply frozen_nonjoin_step_in_frame. exact H.
  - eapply resumed_caller_frozen_origin_connected; [exact IHHderivation|].
    apply rt_step. destruct H as [Hmode | Hmode]; subst mode.
    + apply frozen_caller_powered_frame_join; assumption.
    + apply frozen_caller_prospective_frame_join; assumption.
Qed.

(** A caller-frame RDM join may target any location whose dangerous
    authority is already represented by the completed callee.  The target
    need not be a statically [Mut] root: this is the branch used when an RDM
    return retained its entry-derived authority color.  The caller-origin
    half is obtained from the strictly smaller source derivation, so this is
    provenance, not a dispatch assumption. *)
Lemma tracked_join_to_callee_colored_root_has_class :
  forall CT h Z active incoming caller caller_incoming snapshot mode left
    right target_mode,
    authority_mode_dangerous mode ->
    tracked_resume_frozen_color_derivation CT h Z active incoming caller
      caller_incoming snapshot (mode, left) ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    authority_mode_dangerous target_mode ->
    In authority_flow_state
      (executing_authority_color_set CT h active incoming)
      (target_mode, right) ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot (FlowProspective, right).
Proof.
  intros CT h Z active incoming caller caller_incoming snapshot mode left
    right target_mode Hmode Hderivation Hleft Hright Htarget_mode Htarget.
  right. left. split.
  - destruct Htarget_mode as [Hpowered | Hprospective].
    + subst target_mode. destruct Htarget as [seed [Hseed Hpath]].
      exists seed. split; [exact Hseed|].
      eapply rt_trans; [exact Hpath|].
      apply rt_step. apply phased_authority_mark_prospective.
    + subst target_mode. exact Htarget.
  - have Horigin := tracked_resume_frozen_derivation_has_origin CT h Z active
      incoming caller caller_incoming snapshot (mode, left) Hderivation.
    eapply resumed_caller_frozen_origin_connected; [exact Horigin|].
    apply rt_step. destruct Hmode as [Hpowered | Hprospective]; subst mode.
    + apply frozen_caller_powered_frame_join; assumption.
    + apply frozen_caller_prospective_frame_join; assumption.
Qed.

Lemma tracked_join_under_mutable_caller_has_class :
  forall CT h Z active incoming caller_senv caller_renv caller_incoming
    snapshot mode left right,
    let caller := mk_watched_frame Mut_r caller_senv caller_renv in
    authority_mode_dangerous mode ->
    tracked_resume_frozen_color_derivation CT h Z active incoming caller
      caller_incoming snapshot (mode, left) ->
    typed_root RDM caller_senv caller_renv left ->
    typed_root RDM caller_senv caller_renv right ->
    (forall location,
      frame_owned_location CT h caller location ->
      In authority_flow_state
        (executing_authority_color_set CT h active incoming)
        (FlowPowered, location)) ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot (FlowProspective, right).
Proof.
  intros CT h Z active incoming caller_senv caller_renv caller_incoming
    snapshot mode left right caller Hmode Hderivation Hleft Hright Howned.
  have Hright_owned : frame_owned_location CT h caller right.
  { apply frame_owned_location_iff_active_live.
    eapply typed_rdm_root_is_live_under_mut_authority. exact Hright. }
  right. left. split.
  - have Hpowered := Howned right Hright_owned.
    destruct Hpowered as [seed [Hseed Hpath]].
    exists seed. split; [exact Hseed|].
    eapply rt_trans; [exact Hpath|].
    apply rt_step. apply phased_authority_mark_prospective.
  - have Horigin := tracked_resume_frozen_derivation_has_origin CT h Z active
      incoming caller caller_incoming snapshot (mode, left) Hderivation.
    eapply resumed_caller_frozen_origin_connected; [exact Horigin|].
    apply rt_step. destruct Hmode as [Hmode | Hmode]; subst mode.
    + apply frozen_caller_powered_frame_join; assumption.
    + apply frozen_caller_prospective_frame_join; assumption.
Qed.

Lemma tracked_snapshot_call_color_has_derivation :
  forall CT h Z active active_incoming snapshot caller caller_incoming
    mode location,
    (forall incoming_mode incoming_location,
      authority_mode_dangerous incoming_mode ->
      In authority_flow_state caller_incoming
        (incoming_mode, incoming_location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (incoming_mode, incoming_location)) ->
    (forall owned,
      frame_owned_location CT h caller owned ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, owned)) ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT h caller caller_incoming)
      (mode, location) ->
    tracked_resume_frozen_color_derivation CT h Z active active_incoming
      caller caller_incoming snapshot (mode, location).
Proof.
  intros CT h Z active active_incoming snapshot caller caller_incoming
    mode location Hincoming Howned Hmode [seed [Hseed Hpath]].
  destruct (phased_dangerous_path_has_frozen_origin_or_owned_promotion CT h
    caller seed (mode, location) Hmode Hpath) as
    [[Hseed_mode Hfrozen] | [anchor [Hanchor_owned Hfrozen]]].
  - have Hseed_derivation :
      tracked_resume_frozen_color_derivation CT h Z active active_incoming
        caller caller_incoming snapshot seed.
    { inversion Hseed; subst.
      - apply tracked_resume_from_snapshot.
        destruct seed as [seed_mode seed_location].
        eapply Hincoming; eauto.
        exact H.
        eapply resumed_caller_incoming_has_frozen_origin; eauto.
      - destruct H as [anchor [Heq Hanchor_owned]]. inversion Heq; subst.
        eapply tracked_resume_from_caller_owned; eauto. }
    eapply tracked_resume_frozen_connected_derives; eauto.
  - have Hanchor_derivation :
      tracked_resume_frozen_color_derivation CT h Z active active_incoming
        caller caller_incoming snapshot (FlowPowered, anchor).
    { eapply tracked_resume_from_caller_owned; eauto. }
    eapply tracked_resume_frozen_connected_derives; eauto.
    left. reflexivity.
Qed.

Lemma tracked_resume_frozen_color_class_runtime_mutable :
  forall CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming mode location,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some snapshot :: snapshots) h ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot (mode, location) ->
    r_muttype h location = Some Mut_r.
Proof.
  intros CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming mode location
    (Hstate & Haligned & Hruntime & Hclosed & Hretain & Hdangerous &
      Havoid & Hroots & Hexposure & Hresume & Hjoins & Hentry_covered &
      Hphase_covered)
    [Hsnapshot | [[Hcallee Horigin] | [Hexposure_color Hexposure_safe]]].
  - eapply Hruntime; [simpl; auto|exact Hsnapshot].
  - have Hactive_wf :
        wf_r_config CT active.(frame_senv) active.(frame_renv) h :=
      proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hstate))))).
    have Hactive_sound :
        authority_context_sound h active.(frame_renv)
          active.(frame_authority) :=
      proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hstate)))))).
    have Hincoming_runtime : authority_colors_runtime_mutable h incoming :=
      proj1 (proj2 (proj2 Hstate)).
    eapply executing_authority_colors_runtime_mutable; eauto.
  - eapply (proj1 Hexposure); [simpl; auto|exact Hexposure_color].
Qed.

Lemma executing_dangerous_covered_by_frozen_or_independent :
  forall CT h frame incoming colors mode location,
    Included authority_flow_state
      (frozen_caller_authority_closure CT h frame colors) colors ->
    (forall incoming_mode incoming_location,
      authority_mode_dangerous incoming_mode ->
      In authority_flow_state incoming (incoming_mode, incoming_location) ->
      In authority_flow_state colors (incoming_mode, incoming_location)) ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT h frame incoming) (mode, location) ->
    (exists frozen_mode,
      authority_mode_dangerous frozen_mode /\
      In authority_flow_state colors (frozen_mode, location)) \/
    (exists active_mode,
      authority_mode_dangerous active_mode /\
      In authority_flow_state
        (independent_active_authority_colors CT h frame)
        (active_mode, location)).
Proof.
  intros CT h frame incoming colors mode location Hclosed Hincoming Hmode
    [seed [Hseed Hpath]].
  destruct (phased_dangerous_path_has_frozen_origin_or_owned_promotion CT h
    frame seed (mode, location) Hmode Hpath) as
    [[Hseed_mode Hfrozen] | [anchor [Howned Hfrozen]]].
  - inversion Hseed; subst.
    + left. exists mode. split; [exact Hmode|].
      apply Hclosed. exists seed. split.
      * destruct seed as [seed_mode seed_location].
        eapply Hincoming; eauto.
      * exact Hfrozen.
    + right. exists mode. split; [exact Hmode|].
      exists seed. split.
      * right. exact H.
      * eapply frozen_caller_authority_connected_is_phased. exact Hfrozen.
  - right. exists mode. split; [exact Hmode|].
    exists (FlowPowered, anchor). split.
    + right. exists anchor. split; [reflexivity|exact Howned].
    + eapply frozen_caller_authority_connected_is_phased. exact Hfrozen.
Qed.

Lemma tracked_resume_nonjoin_step_preserves_class :
  forall CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming source target,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some snapshot :: snapshots) h ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot source ->
    frozen_caller_authority_step CT h caller source target ->
    frozen_caller_authority_step CT h active source target ->
    phased_authority_frame_step CT h active source target ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot target.
Proof.
  intros CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming source target
    [Hmain [Haligned [Hruntime [Hclosed [Hretain [Hdangerous
      [Havoid [Hroots [Hexposure
        [Hresume [Hjoins [Hentry_covered Hphase_covered]]]]]]]]]]]]
    [Hsnapshot | [Hcallee | [Hexposure_color Hexposure_safe]]]
    Hcaller_frozen Hfrozen Hphased.
  - left. eapply Hclosed.
    + simpl. left. reflexivity.
    + exists source. split; [exact Hsnapshot|].
      apply rt_step. exact Hfrozen.
  - right. left. destruct Hcallee as [Hcallee Horigin]. split.
    + destruct Hcallee as [seed [Hseed Hpath]].
      exists seed. split; [exact Hseed|].
      eapply rt_trans; [exact Hpath|]. apply rt_step. exact Hphased.
    + destruct Horigin as [seed [Hseed Hpath]].
      exists seed. split; [exact Hseed|].
      eapply rt_trans; [exact Hpath|].
      apply rt_step. exact Hcaller_frozen.
  - right. right. split; [|exact Hexposure_safe].
    eapply (proj1 (proj2 Hexposure)).
    + simpl. left. reflexivity.
    + exists source. split; [exact Hexposure_color|].
      apply rt_step. exact Hfrozen.
Qed.

Lemma tracked_old_resume_join_preserves_class :
  forall CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming mode left right,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some snapshot :: snapshots) h ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    (forall incoming_mode incoming_location,
      authority_mode_dangerous incoming_mode ->
      In authority_flow_state incoming (incoming_mode, incoming_location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (incoming_mode, incoming_location)) ->
    authority_mode_dangerous mode ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot
      (mode, left) ->
    In Loc snapshot.(frozen_snapshot_resume_rdm_roots) left ->
    In Loc snapshot.(frozen_snapshot_resume_rdm_roots) right ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot
      (FlowProspective, right).
Proof.
  intros CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming mode left right
    Hfull
    Hcaller_wf Hincoming_covered Hmode Hclass Hleft_root Hright_root Hleft
    Hright.
  have Hfull_copy := Hfull.
  destruct Hfull as
    (Hstate & Haligned & Hruntime & Hclosed & Hretain & Hdangerous &
      Havoid & Hroots & Hexposure & Hresume & Hjoins & Hentry_covered &
      Hphase_covered).
  have Hsnapshot_in : List.In (Some snapshot) (Some snapshot :: snapshots) by
    (simpl; auto).
  have Hactive_wf : wf_r_config CT active.(frame_senv) active.(frame_renv) h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hstate))))).
  have Hactive_sound :
      authority_context_sound h active.(frame_renv) active.(frame_authority) :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hstate)))))).
  have Hincoming_runtime : authority_colors_runtime_mutable h incoming :=
    proj1 (proj2 (proj2 Hstate)).
  have Hcallee_runtime : authority_colors_runtime_mutable h
      (executing_authority_color_set CT h active incoming) :=
    executing_authority_colors_runtime_mutable CT h active incoming
      Hactive_wf Hactive_sound Hincoming_runtime.
  have Hleft_runtime : r_muttype h left = Some Mut_r.
  { destruct Hclass as
      [Hsnapshot_color | [Hcallee_color | [Hexposure_color Hsafe]]].
    - eapply Hruntime; eauto.
    - eapply Hcallee_runtime; exact (proj1 Hcallee_color).
    - eapply (proj1 Hexposure); eauto. }
  have Hright_runtime : r_muttype h right = Some Mut_r.
  { destruct (active_rdm_roots_share_runtime_context CT caller.(frame_senv)
      caller.(frame_renv) h left right Hcaller_wf Hleft Hright) as
      [context [Hleft_context Hright_context]].
    rewrite Hleft_runtime in Hleft_context. injection Hleft_context as <-.
    exact Hright_context. }
  assert (Hexposure_safe : forall exposure_mode target,
      authority_mode_dangerous exposure_mode ->
      In authority_flow_state
        snapshot.(frozen_snapshot_current_resume_exposure)
        (exposure_mode, target) ->
      ~ In Loc Z target).
  { intros exposure_mode target Hexposure_mode Htarget.
    destruct Hclass as
      [Hsnapshot_color | [Hcallee_color | [Hexposure_color Hsafe]]].
    - exact (tracked_snapshot_resume_exposure_avoids_protected CT P Z cutoff
        active boundary stack incoming snapshot snapshots h mode left
        exposure_mode target Hfull_copy Hmode Hsnapshot_color Hleft_root
        Hexposure_mode Htarget).
    - destruct
        (executing_dangerous_covered_by_frozen_or_independent CT h active
          incoming snapshot.(frozen_snapshot_current_colors) mode left
          (Hclosed snapshot Hsnapshot_in) Hincoming_covered Hmode
          (proj1 Hcallee_color)) as
        [[snapshot_mode [Hsnapshot_mode Hsnapshot_color]] |
         [active_mode [Hactive_mode Hactive_color]]].
      + exact (tracked_snapshot_resume_exposure_avoids_protected CT P Z cutoff
          active boundary stack incoming snapshot snapshots h snapshot_mode
          left exposure_mode target Hfull_copy Hsnapshot_mode Hsnapshot_color
          Hleft_root Hexposure_mode Htarget).
      + exact
          (tracked_snapshot_active_resume_exposure_avoids_protected CT P Z
            cutoff active boundary stack incoming snapshot snapshots h
            active_mode left exposure_mode target Hfull_copy Hactive_mode
            Hactive_color Hleft_root Hexposure_mode Htarget).
    - eapply Hsafe; eauto. }
  right. right. split; [|exact Hexposure_safe].
  eapply (proj2 (proj2 (proj2 (proj2 Hexposure)))); eauto.
Qed.

Lemma tracked_captured_resume_derivation_implies_class :
  forall CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming state,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some snapshot :: snapshots) h ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    (forall incoming_mode incoming_location,
      authority_mode_dangerous incoming_mode ->
      In authority_flow_state incoming (incoming_mode, incoming_location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (incoming_mode, incoming_location)) ->
    (forall root,
      typed_root RDM caller.(frame_senv) caller.(frame_renv) root ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) root) ->
    tracked_resume_frozen_color_derivation CT h Z active incoming caller
      caller_incoming snapshot state ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot state.
Proof.
  intros CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming state Hfull Hcaller_wf Hincoming_covered
    Hcaptured Hderivation.
  induction Hderivation.
  - left. exact H.
  - right. left. split; [exact H0|].
    eapply resumed_caller_owned_has_frozen_origin. exact H.
  - eapply tracked_resume_nonjoin_step_preserves_class; eauto.
    + eapply frozen_nonjoin_step_in_frame. exact H.
    + eapply frozen_nonjoin_step_in_frame. exact H.
    + eapply frozen_nonjoin_step_is_phased. exact H.
  - eapply tracked_old_resume_join_preserves_class with
      (caller := caller) (caller_incoming := caller_incoming); eauto.
Qed.

Lemma tracked_resume_frozen_class_implies_pop_safe :
  forall CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming mode location,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some snapshot :: snapshots) h ->
    authority_mode_dangerous mode ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot
      (mode, location) ->
    (exists callee_mode,
      authority_mode_dangerous callee_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h active incoming)
        (callee_mode, location)) \/
    ~ In Loc Z location.
Proof.
  intros CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming mode location Hfull Hmode
    [Hsnapshot | [Hcallee | [Hexposure Hexposure_safe]]].
  - right. intros Hprotected.
    destruct Hfull as
      (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous &
        Havoid & Hroots & Hexposure_wf & Hresume & Hjoins & Hentry_covered &
        Hphase_covered).
    eapply Havoid; [simpl; auto|exact Hmode|exact Hsnapshot|exact Hprotected].
  - left. exists mode. split; [exact Hmode|exact (proj1 Hcallee)].
  - right. eapply Hexposure_safe; eauto.
Qed.

(** Derivation-indexed post-update elimination.  All joins between captured
    caller roots are discharged here.  The private return callback receives
    the strictly smaller derivation of the join source, which is the measure
    needed by the directional return-root argument. *)
Lemma tracked_post_update_derivation_implies_class :
  forall CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination destination_type
    return_location caller_incoming state,
    let caller_post := mk_watched_frame
      boundary.(boundary_caller).(frame_authority) caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) in
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some snapshot :: snapshots) h ->
    wf_r_config CT caller_senv caller_renv h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    static_getType caller_senv destination = Some destination_type ->
    Same_set Loc snapshot.(frozen_snapshot_resume_rdm_roots)
      (frame_rdm_root_set
        (mk_watched_frame boundary.(boundary_caller).(frame_authority)
          caller_senv caller_renv)) ->
    Same_set authority_flow_state active_incoming
      snapshot.(frozen_snapshot_phase_incoming) ->
    (forall anchor,
      frame_owned_location CT h caller_post anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, anchor) ->
      tracked_resume_frozen_color_class CT h Z active active_incoming
        caller_post caller_incoming snapshot (FlowPowered, anchor)) ->
    (forall mode left right,
      authority_mode_dangerous mode ->
      tracked_resume_frozen_color_derivation CT h Z active active_incoming
        caller_post caller_incoming snapshot (mode, left) ->
      tracked_resume_frozen_color_class CT h Z active active_incoming
        caller_post caller_incoming snapshot (mode, left) ->
      typed_root RDM caller_senv
        (update_r_env_value caller_renv destination (Iot return_location))
        left ->
      typed_root RDM caller_senv
        (update_r_env_value caller_renv destination (Iot return_location))
        right ->
      (left = return_location \/ right = return_location) ->
      tracked_resume_frozen_color_class CT h Z active active_incoming
        caller_post caller_incoming snapshot (FlowProspective, right)) ->
    tracked_resume_frozen_color_derivation CT h Z active active_incoming
      caller_post caller_incoming snapshot state ->
    tracked_resume_frozen_color_class CT h Z active active_incoming
      caller_post caller_incoming snapshot state.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination destination_type
    return_location caller_incoming state caller_post Hfull Hcaller_wf
    Hcaller_post_wf Hdestination Hroots_match Hincoming_match Howned_base
    Hreturn Hderivation.
  induction Hderivation.
  - left. exact H.
  - eapply Howned_base; eauto.
  - eapply tracked_resume_nonjoin_step_preserves_class; eauto.
    + eapply frozen_nonjoin_step_in_frame. exact H.
    + eapply frozen_nonjoin_step_in_frame. exact H.
    + eapply frozen_nonjoin_step_is_phased. exact H.
  - destruct (caller_post_rdm_root_origin CT caller_senv caller_renv h
      destination destination_type return_location left Hcaller_wf
      Hdestination H0) as [Hleft_old | [Hleft_return Hleft_rdm]];
    destruct (caller_post_rdm_root_origin CT caller_senv caller_renv h
      destination destination_type return_location right Hcaller_wf
      Hdestination H1) as [Hright_old | [Hright_return Hright_rdm]].
    + have Hsnapshot_in : List.In (Some snapshot)
          (Some snapshot :: snapshots) by (simpl; auto).
      have Hincoming_covered : forall incoming_mode incoming_location,
          authority_mode_dangerous incoming_mode ->
          In authority_flow_state active_incoming
            (incoming_mode, incoming_location) ->
          In authority_flow_state snapshot.(frozen_snapshot_current_colors)
            (incoming_mode, incoming_location).
      { intros incoming_mode incoming_location Hincoming_mode Hincoming_color.
        destruct Hfull as
          (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous &
            Havoid & Hroots & Hexposure & Hresume & Hjoins & Hentry_covered &
            Hphase_covered).
        eapply Hphase_covered; [exact Hsnapshot_in|exact Hincoming_mode|].
        eapply (proj1 Hincoming_match). exact Hincoming_color. }
      eapply tracked_old_resume_join_preserves_class with
        (caller := caller_post) (caller_incoming := caller_incoming); eauto.
      * eapply (proj2 Hroots_match). exact Hleft_old.
      * eapply (proj2 Hroots_match). exact Hright_old.
    + eapply Hreturn; eauto.
    + eapply Hreturn; eauto.
    + eapply Hreturn; eauto.
Qed.

(** Well-founded classifier for the top snapshot when it is used as the
    summary of older frozen slots.  Its base constructor is frozen
    membership, not immediate-caller provenance.  The only exceptional case
    is leaving a fresh return root: a snapshot base is discharged by the
    root-scoped overlap certificate, while a join-derived base is rerouted to
    its strictly smaller predecessor. *)
(** An older resume-exposure whose captured root already has caller-entry
    provenance is not a new pop obligation.  Nested coverage maps the whole
    exposure derivation into the tracked head, whose well-founded classifier
    then supplies the ordinary pop class.  All arguments are components of
    the private frozen state or consequences of the return typing derivation;
    in particular, this lemma introduces no public preservation premise. *)
(** Stronger, reusable form of
    [advance_nested_frozen_tail_after_return_avoids_protected].  The latter
    is the safety projection needed by the phased state, whereas the private
    statement induction also needs the provenance of every newly closed
    older-slot color.  The provenance is deliberately expressed by
    [nested_frozen_pop_color_class]: no compatibility test is performed at
    dispatch, and no hypothesis is added to the public preservation theorem.

    Keeping the corresponding old snapshot in the conclusion is useful for
    metadata-preserving obligations at an enclosing return. *)
Definition pop_resume_exposure_state_class
  (CT : class_table) (h : heap) (caller : watched_frame)
  (old_exposure : Ensemble authority_flow_state)
  (state : authority_flow_state) : Prop :=
  In authority_flow_state old_exposure state \/
  (fst state = FlowProspective /\
   prospective_location_covered_by_frame CT h caller (snd state)).

Lemma prospective_location_covered_after_prospective_frame_step :
  forall CT h frame source target,
    wf_r_config CT frame.(frame_senv) frame.(frame_renv) h ->
    authority_context_sound h frame.(frame_renv) frame.(frame_authority) ->
    prospective_location_covered_by_frame CT h frame source ->
    frozen_caller_authority_step CT h frame
      (FlowProspective, source) (FlowProspective, target) ->
    prospective_location_covered_by_frame CT h frame target.
Proof.
  intros CT h frame source target Hwf Hsound Hsource Hstep.
  have Hsource_runtime := prospective_location_covered_by_frame_runtime_mutable
    CT h frame source Hwf Hsound Hsource.
  have Htarget_runtime := phased_authority_frame_step_preserves_runtime_mutability
    CT h frame (FlowProspective, source) (FlowProspective, target) Mut_r Hwf
    (frozen_caller_authority_step_is_phased CT h frame
      (FlowProspective, source) (FlowProspective, target) Hstep)
    Hsource_runtime.
  inversion Hstep; subst.
  - destruct Hsource as [root [Hroot Hpath]]. exists root. split;
      [exact Hroot|].
    eapply rt_trans; [exact Hpath|]. apply rt_step.
    apply frozen_caller_prospective_retained. exact H1.
  - destruct Hsource as [root [Hroot Hpath]]. exists root. split;
      [exact Hroot|].
    eapply rt_trans; [exact Hpath|]. apply rt_step.
    apply frozen_caller_prospective_rdm_backward. exact H1.
  - exists target. split.
    + right. split; [exact H2|exact Htarget_runtime].
    + apply rt_refl.
Qed.

Lemma pop_resume_exposure_state_class_step :
  forall CT h active caller old_exposure source target,
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    authority_colors_runtime_mutable h old_exposure ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h active old_exposure)
      old_exposure ->
    pop_resume_exposure_state_class CT h caller old_exposure source ->
    frozen_caller_authority_step CT h caller source target ->
    pop_resume_exposure_state_class CT h caller old_exposure target.
Proof.
  intros CT h active caller old_exposure [source_mode source]
    [target_mode target] Hcaller_wf Hcaller_sound Hruntime Hclosed Hclass
    Hstep. simpl in *.
  destruct Hclass as [Hold | [Hsource_mode Hcovered]].
  - inversion Hstep; subst.
    + left. eapply Hclosed. exists (FlowPowered, source). split;
        [exact Hold|]. apply rt_step. apply frozen_caller_retained. assumption.
    + left. eapply Hclosed. exists (FlowProspective, source). split;
        [exact Hold|]. apply rt_step.
      apply frozen_caller_prospective_retained. assumption.
    + left. eapply Hclosed. exists (FlowProspective, source). split;
        [exact Hold|]. apply rt_step.
      apply frozen_caller_prospective_rdm_backward. assumption.
    + left. eapply Hclosed. exists (FlowPowered, source). split;
        [exact Hold|]. apply rt_step.
      apply frozen_caller_reverse_rdm. assumption.
    + right. split; [reflexivity|].
      have Hsource_runtime := Hruntime FlowPowered source Hold.
      destruct (active_rdm_roots_share_runtime_context CT
        caller.(frame_senv) caller.(frame_renv) h source target Hcaller_wf
        (ltac:(eassumption)) (ltac:(eassumption))) as
        [runtime_q [Hsource_context Htarget_context]].
      rewrite Hsource_runtime in Hsource_context. injection Hsource_context as <-.
      exists target. split.
      * right. split; [eassumption|exact Htarget_context].
      * apply rt_refl.
    + right. split; [reflexivity|].
      have Hsource_runtime := Hruntime FlowProspective source Hold.
      destruct (active_rdm_roots_share_runtime_context CT
        caller.(frame_senv) caller.(frame_renv) h source target Hcaller_wf
        (ltac:(eassumption)) (ltac:(eassumption))) as
        [runtime_q [Hsource_context Htarget_context]].
      rewrite Hsource_runtime in Hsource_context. injection Hsource_context as <-.
      exists target. split.
      * right. split; [eassumption|exact Htarget_context].
      * apply rt_refl.
    + left. eapply Hclosed. exists (FlowPowered, target). split;
        [exact Hold|]. apply rt_step. apply frozen_caller_mark_prospective.
  - change (source_mode = FlowProspective) in Hsource_mode.
    subst source_mode.
    have Htarget_mode : target_mode = FlowProspective.
    { inversion Hstep; reflexivity. }
    subst target_mode. right. split; [reflexivity|].
    eapply prospective_location_covered_after_prospective_frame_step; eauto.
Qed.

Lemma pop_resume_exposure_state_class_connected :
  forall CT h active caller old_exposure source target,
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    authority_colors_runtime_mutable h old_exposure ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h active old_exposure)
      old_exposure ->
    pop_resume_exposure_state_class CT h caller old_exposure source ->
    frozen_caller_authority_connected CT h caller source target ->
    pop_resume_exposure_state_class CT h caller old_exposure target.
Proof.
  intros CT h active caller old_exposure source target Hcaller_wf
    Hcaller_sound Hruntime Hclosed Hsource Hconnected.
  induction Hconnected.
  - eapply pop_resume_exposure_state_class_step; eauto.
  - exact Hsource.
  - apply IHHconnected2.
    apply IHHconnected1. exact Hsource.
Qed.

Lemma advanced_tail_resume_exposure_protected_reflected_after_tracked_pop :
  forall CT P Z cutoff active boundary stack incoming slot snapshots h
    caller old_snapshot new_snapshot,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (slot :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    List.In (Some old_snapshot) snapshots ->
    new_snapshot = advance_frozen_caller_snapshot CT h caller old_snapshot ->
    frozen_snapshot_resume_exposure_protected_reflected Z new_snapshot
      old_snapshot.
Proof.
  intros CT P Z cutoff active boundary stack incoming slot snapshots h
    caller old_snapshot new_snapshot Hprivate Hcaller Hcaller_wf
    Hcaller_sound Hold Heq mode location Hmode Htarget Hprotected.
  subst caller.
  subst new_snapshot. simpl in Htarget.
  destruct Htarget as [source [Hsource Hpath]].
  destruct source as [source_mode source_location]. simpl in *.
  have Hfrozen := proj1 (proj1 Hprivate).
  destruct Hfrozen as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  have Hclass := pop_resume_exposure_state_class_connected CT h active
    boundary.(boundary_caller)
    old_snapshot.(frozen_snapshot_current_resume_exposure)
    (source_mode, source_location)
    (mode, location) Hcaller_wf Hcaller_sound
    ((proj1 Hexposure) old_snapshot (ltac:(simpl; right; exact Hold)))
    ((proj1 (proj2 Hexposure)) old_snapshot
      (ltac:(simpl; right; exact Hold))) (or_introl Hsource) Hpath.
  destruct Hclass as [Hold_target | [_
    [root [Hroot Hroot_path]]]].
  - exists mode. split; assumption.
  - exfalso. eapply (private_head_slot_prospective_component_avoids_older_protected
      CT P Z cutoff active slot snapshots boundary stack incoming h
      old_snapshot root location Hprivate Hold).
    split; [exact Hroot|exact Hroot_path].
    exact Hprotected.
Qed.

Lemma frozen_snapshot_resume_exposure_avoids_after_reflection :
  forall Z final initial,
    frozen_snapshot_resume_exposure_protected_reflected Z final initial ->
    frozen_snapshot_resume_exposure_avoids Z initial ->
    frozen_snapshot_resume_exposure_avoids Z final.
Proof.
  intros Z final initial Hreflection Hsafe mode location Hmode Hcolor
    Hprotected.
  destruct (Hreflection mode location Hmode Hcolor Hprotected) as
    [initial_mode [Hinitial_mode Hinitial_color]].
  exact (Hsafe initial_mode location Hinitial_mode Hinitial_color Hprotected).
Qed.

Lemma frozen_snapshot_live_partition_before_boundary :
  forall snapshots stack snapshot boundary above below,
    frozen_caller_snapshots_before_boundaries snapshots stack ->
    frozen_snapshot_live_partition snapshots stack snapshot boundary above
      below ->
    frozen_snapshot_slot_before_boundary (Some snapshot) boundary.
Proof.
  intros snapshots stack snapshot boundary above below Hbefore Hpartition.
  induction Hpartition.
  - inversion Hbefore; subst. exact H2.
  - inversion Hbefore; subst. apply IHHpartition. exact H4.
Qed.

Lemma private_tracked_head_prospective_component_disjoint_older_resume_root :
  forall CT P Z cutoff active head snapshots boundary stack incoming h older
    root target,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (Some head :: snapshots) h ->
    List.In (Some older) snapshots ->
    prospective_mutable_authority_reachable CT h
      boundary.(boundary_caller) root target ->
    In Loc older.(frozen_snapshot_resume_rdm_roots) target ->
    False.
Proof.
  intros CT P Z cutoff active head snapshots boundary stack incoming h older
    root target Hprivate Hold Hreachable Htarget_root.
  destruct Hprivate as
    [[Hfull [_ [Hbefore _]]] [_ [Hprospective _]]].
  have Haligned := proj1 (proj2 Hfull).
  destruct (frozen_snapshot_in_tail_has_partition_below_head head snapshots
    boundary stack older Haligned Hold) as
    [older_boundary [above [below Hpartition]]].
  have Hfresh : older_boundary.(boundary_entry_cutoff) <= target.
  { eapply Hprospective with (snapshot := older)
      (above := boundary :: above) (below := below) (root := root).
    - exact Hpartition.
    - apply live_frame_suspended with (boundary := boundary). simpl. auto.
    - exact Hreachable. }
  have Hold_slot := frozen_snapshot_live_partition_before_boundary
    (Some head :: snapshots) (boundary :: stack) older older_boundary
    (boundary :: above) below Hbefore Hpartition.
  simpl in Hold_slot. have Hold_target := (proj2 Hold_slot) target Htarget_root.
  lia.
Qed.

(** Tail version of the preceding component/age contradiction.  The proof
    uses only stack alignment and the older tracked slot; the top slot may be
    [None]. *)
Lemma private_head_slot_prospective_component_disjoint_older_resume_root :
  forall CT P Z cutoff active slot snapshots boundary stack incoming h older
    root target,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (slot :: snapshots) h ->
    List.In (Some older) snapshots ->
    prospective_mutable_authority_reachable CT h
      boundary.(boundary_caller) root target ->
    In Loc older.(frozen_snapshot_resume_rdm_roots) target ->
    False.
Proof.
  intros CT P Z cutoff active slot snapshots boundary stack incoming h older
    root target Hprivate Hold Hreachable Htarget_root.
  destruct Hprivate as
    [[Hfull [_ [Hbefore _]]] [_ [Hprospective _]]].
  have Haligned := proj1 (proj2 Hfull).
  destruct (frozen_snapshot_in_tail_has_partition_below_slot slot snapshots
    boundary stack older Haligned Hold) as
    [older_boundary [above [below Hpartition]]].
  have Hfresh : older_boundary.(boundary_entry_cutoff) <= target.
  { eapply Hprospective with (snapshot := older)
      (above := boundary :: above) (below := below) (root := root).
    - exact Hpartition.
    - apply live_frame_suspended with (boundary := boundary). simpl. auto.
    - exact Hreachable. }
  have Hold_slot := frozen_snapshot_live_partition_before_boundary
    (slot :: snapshots) (boundary :: stack) older older_boundary
    (boundary :: above) below Hbefore Hpartition.
  simpl in Hold_slot. have Hold_target := (proj2 Hold_slot) target Htarget_root.
  lia.
Qed.

Lemma active_prospective_component_disjoint_frozen_resume_root :
  forall CT h active snapshots stack older root target,
    frozen_caller_snapshots_aligned snapshots stack ->
    frozen_callee_side_prospective_components_after_boundaries CT h active
      snapshots stack ->
    frozen_caller_snapshots_before_boundaries snapshots stack ->
    List.In (Some older) snapshots ->
    prospective_mutable_authority_reachable CT h active root target ->
    In Loc older.(frozen_snapshot_resume_rdm_roots) target ->
    False.
Proof.
  intros CT h active snapshots stack older root target Haligned Hcomponents
    Hbefore Hold Hreachable Htarget_root.
  destruct (frozen_snapshot_in_has_live_partition snapshots stack older
    Haligned Hold) as [boundary [above [below Hpartition]]].
  have Hfresh : boundary.(boundary_entry_cutoff) <= target.
  { eapply Hcomponents with (snapshot := older) (boundary := boundary)
      (above := above) (below := below) (root := root).
    - exact Hpartition.
    - constructor.
    - exact Hreachable. }
  have Hold_slot := frozen_snapshot_live_partition_before_boundary snapshots
    stack older boundary above below Hbefore Hpartition.
  simpl in Hold_slot. have Hold_target := (proj2 Hold_slot) target Htarget_root.
  lia.
Qed.

Lemma nested_frozen_call_head_resume_exposure_disjoint_advanced_tail :
  forall CT h boundary caller_colors snapshots stack older new_older,
    let caller := boundary.(boundary_caller) in
    let callee := mk_watched_frame
      (call_authority caller.(frame_authority)
        boundary.(boundary_receiver_view))
      boundary.(boundary_callee_entry_senv)
      boundary.(boundary_callee_entry_renv) in
    entry_ownership_channel_free boundary ->
    frozen_caller_snapshots_aligned snapshots stack ->
    frozen_callee_side_prospective_components_after_boundaries CT h caller
      snapshots stack ->
    frozen_caller_snapshots_before_boundaries snapshots stack ->
    List.In (Some older) snapshots ->
    new_older = advance_frozen_caller_snapshot CT h callee older ->
    frozen_snapshot_resume_exposure_disjoint_from
      (nested_frozen_call_head CT h caller callee caller_colors snapshots)
      new_older.
Proof.
  intros CT h boundary caller_colors snapshots stack older new_older caller
    callee Hfree Haligned Hcomponents Hbefore Hold Heq mode location Hcolor
    Hroot.
  subst new_older. simpl in Hroot.
  unfold nested_frozen_call_head in Hcolor. simpl in Hcolor.
  destruct Hcolor as [caller_state [Hcaller_state Hcallee_path]].
  unfold frame_resume_exposure_colors in Hcaller_state.
  destruct Hcaller_state as [seed [Hseed Hcaller_path]].
  unfold frame_resume_exposure_seeds in Hseed.
  destruct Hseed as [root [Hrdm [Hruntime Heq]]]. subst seed.
  have Hcallee_reflected : frozen_caller_authority_connected CT h caller
      (FlowProspective, root) (mode, location).
  { eapply rt_trans; [exact Hcaller_path|].
    eapply channel_free_entry_frozen_connected_reflects; eauto. }
  have Hprospective_path := frozen_caller_connected_as_prospective CT h caller
    (FlowProspective, root) (mode, location) Hcallee_reflected.
  simpl in Hprospective_path.
  eapply active_prospective_component_disjoint_frozen_resume_root with
    (older := older) (root := root); eauto.
  split.
  - right. split; assumption.
  - exact Hprospective_path.
Qed.

Lemma frozen_caller_snapshots_newer_resume_exposure_disjoint_after_reflected_advance :
  forall CT h active snapshots,
    frozen_caller_snapshots_newer_resume_exposure_disjoint snapshots ->
    (forall newer older mode location,
      List.In (Some newer) snapshots ->
      List.In (Some older) snapshots ->
      In authority_flow_state
        (frozen_caller_authority_closure CT h active
          newer.(frozen_snapshot_current_resume_exposure)) (mode, location) ->
      In Loc older.(frozen_snapshot_resume_rdm_roots) location ->
      exists old_mode,
        In authority_flow_state
          newer.(frozen_snapshot_current_resume_exposure)
          (old_mode, location)) ->
    frozen_caller_snapshots_newer_resume_exposure_disjoint
      (advance_frozen_caller_snapshots CT h active snapshots).
Proof.
  intros CT h active snapshots Hdisjoint Hreflect.
  induction snapshots as [|slot tail IH]; simpl in *; [exact I|].
  destruct slot as [head|].
  - destruct Hdisjoint as [Hhead Htail]. split.
    + intros new_older Hnew mode location Hcolor Hroot.
      unfold advance_frozen_caller_snapshots in Hnew.
      apply in_map_iff in Hnew.
      destruct Hnew as [old_slot [Heq Hold]].
      destruct old_slot as [old_older|]; simpl in Heq; [|discriminate].
      injection Heq as Heq. subst new_older. simpl in Hroot.
      destruct (Hreflect head old_older mode location (ltac:(simpl; auto))
        (ltac:(simpl; right; exact Hold)) Hcolor Hroot) as
        [old_mode Hold_color].
      eapply (Hhead old_older Hold old_mode location); eauto.
    + apply IH.
      * exact Htail.
      * intros newer older mode location Hnewer Holder.
        eapply Hreflect; simpl; right; eauto.
  - apply IH.
    + exact Hdisjoint.
    + intros newer older mode location Hnewer Holder.
      eapply Hreflect; simpl; right; eauto.
Qed.

Lemma advanced_tail_resume_exposure_at_any_older_root_reflected_after_pop :
  forall CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    exposure_snapshot root_snapshot mode location,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    List.In (Some exposure_snapshot) snapshots ->
    List.In (Some root_snapshot) snapshots ->
    In authority_flow_state
      (frozen_caller_authority_closure CT h caller
        exposure_snapshot.(frozen_snapshot_current_resume_exposure))
      (mode, location) ->
    In Loc root_snapshot.(frozen_snapshot_resume_rdm_roots) location ->
    exists old_mode,
      In authority_flow_state
        exposure_snapshot.(frozen_snapshot_current_resume_exposure)
        (old_mode, location).
Proof.
  intros CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    exposure_snapshot root_snapshot mode location Hprivate Hcaller Hcaller_wf
    Hcaller_sound Hexposure_slot Hroot_slot Hcolor Hresume_root.
  destruct Hcolor as [seed [Hseed Hpath]].
  have Hfrozen := proj1 (proj1 Hprivate).
  destruct Hfrozen as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  have Hclass := pop_resume_exposure_state_class_connected CT h active caller
    exposure_snapshot.(frozen_snapshot_current_resume_exposure) seed
    (mode, location) Hcaller_wf Hcaller_sound
    ((proj1 Hexposure) exposure_snapshot
      (ltac:(simpl; right; exact Hexposure_slot)))
    ((proj1 (proj2 Hexposure)) exposure_snapshot
      (ltac:(simpl; right; exact Hexposure_slot))) (or_introl Hseed) Hpath.
  destruct Hclass as [Hold | [Hmode Hcovered]].
  - exists mode. exact Hold.
  - change (mode = FlowProspective) in Hmode. subst mode.
    destruct Hcovered as [root [Hroot Hroot_path]]. exfalso.
    eapply
      (private_head_slot_prospective_component_disjoint_older_resume_root
        CT P Z cutoff active head_slot snapshots boundary stack incoming h
        root_snapshot root location Hprivate Hroot_slot).
    + rewrite <- Hcaller. split; [exact Hroot|exact Hroot_path].
    + exact Hresume_root.
Qed.

Lemma advanced_tail_current_color_class_after_tracked_pop :
  forall CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    old_snapshot new_snapshot state,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    List.In (Some old_snapshot) snapshots ->
    new_snapshot = advance_frozen_caller_snapshot CT h caller old_snapshot ->
    In authority_flow_state new_snapshot.(frozen_snapshot_current_colors)
      state ->
    pop_resume_exposure_state_class CT h caller
      old_snapshot.(frozen_snapshot_current_colors) state.
Proof.
  intros CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    old_snapshot new_snapshot state Hprivate Hcaller Hcaller_wf Hcaller_sound
    Hold Heq Hstate.
  subst new_snapshot. simpl in Hstate. destruct Hstate as [source [Hsource Hpath]].
  have Hfrozen := proj1 (proj1 Hprivate).
  destruct Hfrozen as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  eapply pop_resume_exposure_state_class_connected with (active := active);
    eauto.
  - eapply Hruntime. simpl. right. exact Hold.
  - eapply Hclosed. simpl. right. exact Hold.
  - left. exact Hsource.
Qed.

Lemma advanced_tail_current_color_at_resume_root_reflected_after_tracked_pop :
  forall CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    old_snapshot new_snapshot mode location,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    List.In (Some old_snapshot) snapshots ->
    new_snapshot = advance_frozen_caller_snapshot CT h caller old_snapshot ->
    authority_mode_dangerous mode ->
    In authority_flow_state new_snapshot.(frozen_snapshot_current_colors)
      (mode, location) ->
    In Loc new_snapshot.(frozen_snapshot_resume_rdm_roots) location ->
    In authority_flow_state old_snapshot.(frozen_snapshot_current_colors)
      (mode, location).
Proof.
  intros CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    old_snapshot new_snapshot mode location Hprivate Hcaller Hcaller_wf
    Hcaller_sound Hold Heq Hmode Hcolor Hresume_root.
  have Hclass := advanced_tail_current_color_class_after_tracked_pop CT P Z
    cutoff active boundary stack incoming head_slot snapshots h caller old_snapshot
    new_snapshot (mode, location) Hprivate Hcaller Hcaller_wf Hcaller_sound
    Hold Heq Hcolor.
  destruct Hclass as [Hold_color | [Hprospective Hcovered]].
  - exact Hold_color.
  - subst new_snapshot. simpl in Hresume_root.
    change (mode = FlowProspective) in Hprospective. subst mode.
    destruct Hcovered as [root [Hauthority_root Hpath]].
    exfalso. eapply
      (private_head_slot_prospective_component_disjoint_older_resume_root
        CT P Z cutoff active head_slot snapshots boundary stack incoming h
        old_snapshot root location Hprivate Hold).
    + rewrite <- Hcaller. split; [exact Hauthority_root|exact Hpath].
    + exact Hresume_root.
Qed.

Lemma independent_active_authority_avoids_older_resume_roots_after_tracked_pop :
  forall CT P Z cutoff active boundary stack incoming head_slot snapshots h caller,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    forall snapshot active_mode source,
      List.In (Some snapshot)
        (advance_frozen_caller_snapshots CT h caller snapshots) ->
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h caller)
        (active_mode, source) ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
      False.
Proof.
  intros CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    Hprivate Hcaller Hcaller_wf Hcaller_sound snapshot active_mode source
    Hsnapshot Hactive_mode Hactive Hroot.
  unfold advance_frozen_caller_snapshots in Hsnapshot.
  apply in_map_iff in Hsnapshot.
  destruct Hsnapshot as [slot [Heq Hslot]].
  destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst snapshot. simpl in Hroot.
  destruct (independent_active_dangerous_has_prospective_root CT h caller
    active_mode source Hcaller_wf Hcaller_sound Hactive_mode Hactive) as
    [root [Hauthority_root Hpath]].
  eapply private_head_slot_prospective_component_disjoint_older_resume_root
    with (older := old_snapshot) (root := root) (target := source); eauto.
  rewrite <- Hcaller. split; assumption.
Qed.

Lemma advanced_tail_current_color_at_any_older_resume_root_reflected :
  forall CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    color_snapshot root_snapshot new_color_snapshot new_root_snapshot mode
    location,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    List.In (Some color_snapshot) snapshots ->
    List.In (Some root_snapshot) snapshots ->
    new_color_snapshot =
      advance_frozen_caller_snapshot CT h caller color_snapshot ->
    new_root_snapshot =
      advance_frozen_caller_snapshot CT h caller root_snapshot ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      new_color_snapshot.(frozen_snapshot_current_colors) (mode, location) ->
    In Loc new_root_snapshot.(frozen_snapshot_resume_rdm_roots) location ->
    In authority_flow_state color_snapshot.(frozen_snapshot_current_colors)
      (mode, location).
Proof.
  intros CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    color_snapshot root_snapshot new_color_snapshot new_root_snapshot mode
    location Hprivate Hcaller Hcaller_wf Hcaller_sound Hcolor_slot Hroot_slot
    Hnew_color Hnew_root Hmode Hcolor Hresume_root.
  have Hclass := advanced_tail_current_color_class_after_tracked_pop CT P Z
    cutoff active boundary stack incoming head_slot snapshots h caller color_snapshot
    new_color_snapshot (mode, location) Hprivate Hcaller Hcaller_wf
    Hcaller_sound Hcolor_slot Hnew_color Hcolor.
  destruct Hclass as [Hold_color | [Hprospective Hcovered]].
  - exact Hold_color.
  - subst new_root_snapshot. simpl in Hresume_root.
    change (mode = FlowProspective) in Hprospective. subst mode.
    destruct Hcovered as [root [Hauthority_root Hpath]]. exfalso.
    eapply
      (private_head_slot_prospective_component_disjoint_older_resume_root
        CT P Z cutoff active head_slot snapshots boundary stack incoming h
        root_snapshot root location Hprivate Hroot_slot).
    + rewrite <- Hcaller. split; [exact Hauthority_root|exact Hpath].
    + exact Hresume_root.
Qed.

(** A prospective component of the resumed active frame lies on the callee
    side of every older frozen boundary.  Consequently it cannot reach the
    protected prefix.  This is the post-update counterpart of the head-slot
    age argument: it consumes the independently reconstructed tail
    partitions, so it does not identify the resumed frame with the saved
    pre-call frame. *)
Lemma active_prospective_component_avoids_frozen_protected :
  forall CT h Z cutoff active snapshots stack older root target,
    frozen_caller_snapshots_aligned snapshots stack ->
    frozen_callee_side_prospective_components_after_boundaries CT h active
      snapshots stack ->
    frozen_snapshot_boundaries_after_cutoff cutoff snapshots stack ->
    protected_zone_before_cutoff Z cutoff ->
    List.In (Some older) snapshots ->
    prospective_mutable_authority_reachable CT h active root target ->
    ~ In Loc Z target.
Proof.
  intros CT h Z cutoff active snapshots stack older root target Haligned
    Hcomponents Hafter Hzone Holder Hreachable Hprotected.
  destruct (frozen_snapshot_in_has_live_partition snapshots stack older
    Haligned Holder) as [boundary [above [below Hpartition]]].
  have Hfresh : boundary.(boundary_entry_cutoff) <= target.
  { eapply Hcomponents with (snapshot := older) (above := above)
      (below := below) (root := root).
    - exact Hpartition.
    - constructor.
    - exact Hreachable. }
  have Hboundary_after : cutoff <= boundary.(boundary_entry_cutoff).
  { eapply frozen_snapshot_partition_boundary_after_cutoff; eauto. }
  have Hprotected_before := Hzone target Hprotected. lia.
Qed.

(** Classify a color added while an older tail snapshot is closed under the
    post-return caller.  The old snapshot remains closed under the completed
    callee, which is exactly the premise required by the generic connected
    classifier; no equality between the pre- and post-update callers is
    needed. *)
Lemma advanced_tail_color_class_after_return :
  forall CT P Z cutoff callee boundary stack incoming head_slot snapshots h
    caller old_snapshot mode location,
    private_fresh_frozen_statement_state CT P Z cutoff callee
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    List.In (Some old_snapshot) snapshots ->
    In authority_flow_state
      (advance_frozen_caller_snapshot CT h caller old_snapshot)
        .(frozen_snapshot_current_colors) (mode, location) ->
    pop_resume_exposure_state_class CT h caller
      old_snapshot.(frozen_snapshot_current_colors) (mode, location).
Proof.
  intros CT P Z cutoff callee boundary stack incoming head_slot snapshots h
    caller old_snapshot mode location Hbody Hcaller_wf Hcaller_sound Holder
    [source [Hsource Hpath]].
  have Hfrozen := proj1 (proj1 Hbody).
  destruct Hfrozen as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  eapply pop_resume_exposure_state_class_connected with (active := callee);
    eauto.
  - eapply Hruntime. simpl. right. exact Holder.
  - eapply Hclosed. simpl. right. exact Holder.
  - left. exact Hsource.
Qed.

Lemma advanced_tail_exposure_class_after_return :
  forall CT P Z cutoff callee boundary stack incoming head_slot snapshots h
    caller old_snapshot mode location,
    private_fresh_frozen_statement_state CT P Z cutoff callee
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    List.In (Some old_snapshot) snapshots ->
    In authority_flow_state
      (advance_frozen_caller_snapshot CT h caller old_snapshot)
        .(frozen_snapshot_current_resume_exposure) (mode, location) ->
    pop_resume_exposure_state_class CT h caller
      old_snapshot.(frozen_snapshot_current_resume_exposure) (mode, location).
Proof.
  intros CT P Z cutoff callee boundary stack incoming head_slot snapshots h
    caller old_snapshot mode location Hbody Hcaller_wf Hcaller_sound Holder
    [source [Hsource Hpath]].
  have Hfrozen := proj1 (proj1 Hbody).
  destruct Hfrozen as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  eapply pop_resume_exposure_state_class_connected with (active := callee);
    eauto.
  - eapply (proj1 Hexposure). simpl. right. exact Holder.
  - eapply (proj1 (proj2 Hexposure)). simpl. right. exact Holder.
  - left. exact Hsource.
Qed.

(** Final strengthened induction state.  The disjointness conjunct is ghost
    state initialized by [None] slots at the public boundary; it is never a
    premise of the public preservation theorem. *)
Definition private_principled_statement_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary)
  (incoming : Ensemble authority_flow_state)
  (snapshots : list frozen_caller_snapshot_slot) (h : heap) : Prop :=
  private_fresh_frozen_statement_state CT P Z cutoff active stack incoming
    snapshots h /\
  frozen_caller_snapshots_newer_resume_exposure_disjoint snapshots.

Definition private_principled_statement_result
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (authority : q_r) (final_senv : s_env) (final_renv : r_env)
  (stack : list watched_boundary) (incoming : Ensemble authority_flow_state)
  (initial_snapshots final_snapshots : list frozen_caller_snapshot_slot)
  (final_h : heap) : Prop :=
  private_statement_preservation_result CT P Z cutoff authority final_senv
    final_renv stack incoming initial_snapshots final_snapshots final_h /\
  frozen_caller_snapshots_newer_resume_exposure_disjoint final_snapshots.
