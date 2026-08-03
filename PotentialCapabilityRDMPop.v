(** Salvaged potential-graph call-pop machinery.

    These lemmas were extracted from the retired [PotentialCapabilityRDMCall]
    development.  They are stated and proved entirely against the public
    spine ([PotentialCapabilityCore], [...Private], [...Resume]) and do not
    depend on the retired statement-level policy packaging.

    Two groups are kept:

    - the [Imm_r] saved-target policy suite, and
    - the symmetry-free RDM call-pop merge lemmas, whose combinator
      [classified_rdm_call_pop_merge_safe] reduces the whole RDM-destination
      pop obligation to the single [Imm_r] / covariant-[Mut] return case. *)

Require Import Syntax Helpers Typing Bigstep ReadonlyHelper Properties
  Preservation ForwardCapabilityHistory ProtectionHistory WatchedFrames
  ExecutionConfinement MutableCapability AuthorityCapability
  PotentialCapabilityCore LiveCapabilityStack.
Require Export PotentialCapabilityResume.
From Stdlib Require Import Sets.Ensembles Relations.Relation_Operators.

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
