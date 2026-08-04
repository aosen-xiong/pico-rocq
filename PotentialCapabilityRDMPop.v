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

Require Import Syntax Helpers Typing Subtyping Bigstep ViewpointAdaptation ReadonlyHelper Properties
  Preservation ForwardCapabilityHistory ProtectionHistory WatchedFrames
  ExecutionConfinement MutableCapability AuthorityCapability ComponentColoring
  PotentialCapabilityCore LiveCapabilityStack.
Require Export PotentialCapabilityResume.
From Stdlib Require Import List Sets.Ensembles Relations.Relation_Operators
  Program.Equality.
Import ListNotations.

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

(** Two RDM roots of a suspended caller frame remain adjacent in the callee's
    potential graph: the caller frame is still a live frame member across the
    boundary, and [potential_frame_edge] carries no authority condition.

    This is the collapse used by the immutable call-pop residual.  An RDM
    parameter's argument is forced below
    [vpa_mutability_tt_readonly_state Ty T], which for an RDM receiver and an
    RDM parameter is RDM, so any old object the callee holds through such a
    parameter is a caller RDM root and is therefore joined to the receiver. *)
Lemma boundary_caller_rdm_roots_are_adjacent :
  forall CT h callee boundary stack left right,
    typed_root RDM boundary.(boundary_caller).(frame_senv)
      boundary.(boundary_caller).(frame_renv) left ->
    typed_root RDM boundary.(boundary_caller).(frame_senv)
      boundary.(boundary_caller).(frame_renv) right ->
    potential_adjacent CT h callee (boundary :: stack) left right.
Proof.
  intros CT h callee boundary stack left right Hleft Hright.
  right. left.
  exists boundary.(boundary_caller). split.
  - apply live_frame_suspended. left. reflexivity.
  - split; [exact Hleft|exact Hright].
Qed.

Lemma boundary_caller_rdm_roots_are_connected :
  forall CT h callee boundary stack left right,
    typed_root RDM boundary.(boundary_caller).(frame_senv)
      boundary.(boundary_caller).(frame_renv) left ->
    typed_root RDM boundary.(boundary_caller).(frame_senv)
      boundary.(boundary_caller).(frame_renv) right ->
    potential_connected CT h callee (boundary :: stack) left right.
Proof.
  intros CT h callee boundary stack left right Hleft Hright.
  apply rt_step.
  eapply boundary_caller_rdm_roots_are_adjacent; eauto.
Qed.

(** Every [Mut]-typed root of a frame whose protected zone coincides with its
    confinement set lies above the cutoff.

    Instantiating the statement induction a second time with
    [P = Z = body_initial_reachable] and [cutoff = dom h] therefore shows that
    every [Mut]-typed variable of a readonly-state callee holds a freshly
    allocated location.  This is the fact behind the [Mut_f] row of the
    old-to-fresh crossing analysis: a [Mut_f] write needs a [Mut]-typed
    receiver variable, and such a variable never denotes an old object.

    Deriving it here avoids [principled_phased_local_mut_root_is_fresh], whose
    [principled_phased_authority_live_history_state] premise has no bridge
    from [potential_live_history_state] in this development. *)
Lemma potential_local_mut_root_is_fresh :
  forall CT P cutoff active stack h variable T root,
    potential_live_history_state CT P P cutoff active stack h ->
    static_getType active.(frame_senv) variable = Some T ->
    runtime_getVal active.(frame_renv) variable = Some (Iot root) ->
    sqtype T = Mut ->
    cutoff <= root.
Proof.
  intros CT P cutoff active stack h variable T root Hstate Htype Hvalue Hmut.
  have Hcapability : In Loc (live_capability_set CT h active stack) root.
  { eapply typed_mut_root_is_active_live_capability.
    exists variable, T. repeat split; assumption. }
  have Hseparated := proj1 (proj2 Hstate).
  have Hnot_protected : ~ In Loc P root.
  { intros Hin.
    exact (Hseparated root root Hcapability Hin (rt_refl _ _ _)). }
  have Henv : env_is_confined P cutoff active.(frame_renv) :=
    proj1 (proj1 (proj2 (proj2 (proj1 (proj1 (proj1 Hstate)))))).
  destruct (Henv variable root Hvalue) as [HinP | Hfresh].
  - contradiction.
  - exact Hfresh.
Qed.

(** [potential_adjacent] is [authority_color_adjacent] plus
    [potential_return_edge], so the converse of
    [authority_color_connected_is_potential_connected] holds exactly when no
    live boundary contributes a return edge.

    This is the step that lets a potential-graph bridge be replayed in the
    colour formalism, where authority provenance is tracked. *)
Lemma potential_connected_is_authority_color_connected_without_return :
  forall CT h active stack left right,
    (forall l r, ~ potential_return_edge h active stack l r) ->
    potential_connected CT h active stack left right ->
    authority_color_connected CT h active stack left right.
Proof.
  intros CT h active stack left right Hno_return Hconnected.
  induction Hconnected.
  - apply rt_step. destruct H as [Hheap | [Hframe | Hreturn]].
    + left. exact Hheap.
    + right. exact Hframe.
    + exfalso. exact (Hno_return x y Hreturn).
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

(** A boundary whose callee return qualifier is not [RDM] contributes no
    return edge.  In the covariant [Mut] return branch
    [sqtype body_return_type = Mut] together with
    [body_return_type <= mret runtime_sig] forces
    [sqtype (mret runtime_sig)] into [{Mut, RO}], so the head boundary of that
    branch is always of this shape. *)
Lemma no_return_edge_when_callee_return_not_rdm :
  forall h active stack,
    (forall callee boundary,
      live_call_boundary active stack callee boundary ->
      boundary.(boundary_callee_return_qualifier) <> RDM) ->
    forall l r, ~ potential_return_edge h active stack l r.
Proof.
  intros h active stack Hnot_rdm l r
    [callee [boundary [Hlive [_ [Hreturn_rdm _]]]]].
  exact (Hnot_rdm callee boundary Hlive Hreturn_rdm).
Qed.

(** Recovered from the retired [PotentialCapabilityCall] development.
    In the covariant [Mut] return branch the callee receiver is forced to
    [RO] and the callee entry frame has no RDM roots at all, so the tracked
    channel-free call entry applies. *)
Lemma refined_mut_return_call_has_channel_free_entry_shape :
  forall CT sGamma mt rGamma h x method receiver args vals
    receiver_location receiver_type destination_type body_return_type
    runtime_mdef static_mdef,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method receiver args) sGamma ->
    readonly_state_method_scope mt ->
    static_getType sGamma receiver = Some receiver_type ->
    runtime_getVal rGamma receiver = Some (Iot receiver_location) ->
    runtime_lookup_list rGamma args = Some vals ->
    FindMethodWithName CT (sctype receiver_type) method static_mdef ->
    qualified_type_subtype CT body_return_type
      (mret (msignature runtime_mdef)) ->
    method_signature_refinement CT
      (msignature runtime_mdef) (msignature static_mdef) ->
    qualified_type_subtype CT
      (vpa_mutability_tt_readonly_state receiver_type
        (mret (msignature static_mdef)))
      destination_type ->
    sqtype receiver_type <> Bot ->
    sqtype destination_type = RDM ->
    sqtype body_return_type = Mut ->
    (qualified_type_subtype CT receiver_type
       (vpa_mutability_tt_readonly_state receiver_type
         (mreceiver (msignature static_mdef))) \/
     (sqtype receiver_type = RO /\
      sqtype (mreceiver (msignature static_mdef)) = RDM /\
      base_subtype CT (sctype receiver_type)
        (sctype (mreceiver (msignature static_mdef))))) ->
    signature_has_no_mutable_roots (msignature runtime_mdef) ->
    sqtype (mreceiver (msignature runtime_mdef)) = RO /\
    (forall root,
      ~ typed_root RDM
          (mreceiver (msignature runtime_mdef) ::
            mparams (msignature runtime_mdef))
          (mkr_env (Iot receiver_location :: vals)) root).
Proof.
  intros CT sGamma mt rGamma h x method receiver args vals
    receiver_location receiver_type destination_type body_return_type
    runtime_mdef static_mdef
    Hwf Htyping Hscope Hreceiver_type Hreceiver_value Hargs Hfind_static
    Hbody_sub Hrefine Hresult_sub Hreceiver_nonbottom
    Hdestination_rdm Hbody_mut Hreceiver_sub Hsignature_safe.
  destruct (refined_call_rdm_result_classifies_body_return CT receiver_type
    body_return_type (msignature runtime_mdef) (msignature static_mdef)
    destination_type Hbody_sub Hrefine Hresult_sub Hreceiver_nonbottom
    (ltac:(rewrite Hbody_mut; discriminate)) Hdestination_rdm) as
    [Hreceiver_rdm _].
  destruct Hreceiver_sub as [Hreceiver_sub | [Hreceiver_ro _]];
    [| rewrite Hreceiver_rdm in Hreceiver_ro; discriminate].
  destruct (refined_call_rdm_mut_body_signature_shape CT receiver_type
    body_return_type (msignature runtime_mdef) (msignature static_mdef)
    destination_type Hbody_sub Hrefine Hresult_sub Hreceiver_nonbottom
    Hdestination_rdm Hbody_mut) as [Hstatic_return Hruntime_return].
  have Hstatic_receiver :
      sqtype (mreceiver (msignature static_mdef)) = RDM \/
      sqtype (mreceiver (msignature static_mdef)) = RO.
  { eapply readonly_rdm_call_receiver_signature.
    - exact Hreceiver_rdm.
    - exact Hreceiver_sub. }
  have Hruntime_receiver :
      sqtype (mreceiver (msignature runtime_mdef)) = RO.
  { eapply method_signature_refinement_mut_from_rdm_has_ro_receiver; eauto. }
  split; [exact Hruntime_receiver|].
  intros root.
  eapply refined_mut_return_call_entry_has_no_rdm_roots with
    (receiver_type := receiver_type) (runtime_mdef := runtime_mdef)
    (static_mdef := static_mdef); eauto.
Qed.

(** Readonly-state field adaptation admits a [Mut] value in exactly two ways.

    - Through an [RO_f] field: the slot adapts to [RO], so the value fits, but
      the reference stored is readonly and carries no mutable authority.
    - Otherwise the receiver must itself be [Mut]: [Mut_f] adapts to [Mut] only
      under a [Mut] receiver and to [Lost] otherwise, [RDM_f] adapts to the
      receiver's own qualifier and collapses to [Lost] under [RO], and [Imm_f]
      adapts to [Imm].

    This is the dichotomy an RS body faces whenever it tries to publish a
    mutable value: either the connection it makes is not a mutable one, or it
    is making it through a [Mut] variable -- and in the flexible-call callee
    every [Mut] variable denotes a freshly allocated object. *)
Lemma mut_into_readonly_state_field_is_ro_or_mut_receiver :
  forall q1 fm,
    q_subtype Mut (vpa_mutability_stype_fld_readonly_state q1 fm) ->
    fm = RO_f \/ q1 = Mut.
Proof.
  intros q1 fm Hq.
  destruct fm; [| | |left; reflexivity];
    destruct q1; simpl in Hq; try (right; reflexivity); inversion Hq.
Qed.

(** Backward form of the local result-component bound.  [mutable_connected] is
    the reflexive-transitive closure of a *symmetric* adjacency
    ([mutable_adjacent_symmetric]), so it relates components rather than
    directed reachability, and the forward bound transports.

    Read together with
    [mut_into_readonly_state_field_is_ro_or_mut_receiver]: a readonly-state
    body can only put a [Mut] value behind an [RO_f] slot, which carries no
    mutable edge, or through a [Mut] receiver, which is fresh.  So nothing old
    ends up in the [Mut] result's mutable component -- which is what this
    states. *)
Lemma principled_local_mut_result_component_source_is_fresh :
  forall CT sGamma rGamma h statement rGamma' h' active stack incoming
    return_var return_type return_location source,
    wf_r_config CT sGamma rGamma h ->
    eval_stmt CT rGamma h statement OK rGamma' h' ->
    principled_phased_authority_live_history_state CT
      (reachable_locations_from_initial_env h rGamma)
      (reachable_locations_from_initial_env h rGamma) (dom h)
      active stack incoming h' ->
    static_getType active.(frame_senv) return_var = Some return_type ->
    runtime_getVal active.(frame_renv) return_var = Some (Iot return_location) ->
    sqtype return_type = Mut ->
    mutable_connected CT h' source return_location ->
    dom h <= source.
Proof.
  intros CT sGamma rGamma h statement rGamma' h' active stack incoming
    return_var return_type return_location source Hwf Heval Hstate Htype
    Hvalue Hmut Hconnected.
  eapply principled_local_mut_result_component_is_fresh; eauto.
  apply mutable_connected_sym. exact Hconnected.
Qed.

(** Companion to [mut_into_readonly_state_field_is_ro_or_mut_receiver], for
    the receivers a channel-free [RO]-receiver callee can actually hold.

    Such a callee never names an old object at [Mut] or [RDM] type: its
    receiver is [RO], reading through [RO] gives [Lost] on [RDM_f] and
    [Mut_f] and [Imm]/[RO] otherwise, and channel-freeness rules out [RDM]
    parameters.  Writing through any such variable into a slot that could
    carry a mutable edge therefore admits only immutable values -- through
    [RO] and [Lost] the slot adapts to [Lost] and admits nothing but [Bot],
    and through [Imm] an [RDM_f] slot adapts to [Imm].

    So every mutable edge this callee creates out of an old object points at
    an immutable value, and the fresh [Mut] result can never sit on the far
    side of one. *)
Lemma mut_edge_write_through_non_mutable_receiver_is_immutable :
  forall q1 fm qv,
    (fm = RDM_f \/ fm = Mut_f) ->
    q1 <> Mut ->
    q1 <> RDM ->
    q_subtype qv (vpa_mutability_stype_fld_readonly_state q1 fm) ->
    qv = Imm \/ qv = Bot.
Proof.
  intros q1 fm qv Hfm Hnot_mut Hnot_rdm Hq.
  destruct Hfm as [-> | ->]; destruct q1;
    try (exfalso; congruence);
    simpl in Hq; inversion Hq; subst; auto; congruence.
Qed.

(** The invariant the residual's induction carries: a frame never names a
    pre-existing object at [Mut] or [RDM] type.

    It is what makes the two write-level facts apply at *every* write in the
    body rather than only the first -- writing through a variable that holds
    an old object is always a write through an [RO], [Imm] or [Lost]
    viewpoint, so by
    [mut_edge_write_through_non_mutable_receiver_is_immutable] it can only
    publish immutable values, and the fresh [Mut] result is never among
    them. *)
Definition old_values_non_mutably_typed
  (h : heap) (sGamma : s_env) (rGamma : r_env) : Prop :=
  forall x T l,
    static_getType sGamma x = Some T ->
    runtime_getVal rGamma x = Some (Iot l) ->
    l < dom h ->
    sqtype T <> Mut /\ sqtype T <> RDM.

(** It holds at a channel-free entry.  [signature_has_no_mutable_roots]
    excludes [Mut], and channel-freeness -- no [RDM] root at all -- excludes
    [RDM].  Both are supplied for this call by
    [refined_mut_return_call_has_channel_free_entry_shape]. *)
Lemma channel_free_entry_old_values_non_mutably_typed :
  forall h msig rGamma,
    signature_has_no_mutable_roots msig ->
    (forall root,
      ~ typed_root RDM (mreceiver msig :: mparams msig) rGamma root) ->
    old_values_non_mutably_typed h (mreceiver msig :: mparams msig) rGamma.
Proof.
  intros h msig rGamma [Hreceiver_safe Hparams_safe] Hno_rdm x T l
    Htype Hvalue Hold.
  split.
  - destruct x as [|parameter].
    + simpl in Htype. injection Htype as <-.
      unfold is_nonmutable_qualifier in Hreceiver_safe.
      destruct Hreceiver_safe as [-> | [-> | [-> | ->]]]; discriminate.
    + simpl in Htype. unfold static_getType in Htype.
      have Hsafe : is_nonmutable_qualifier (sqtype T) :=
        Forall_nth_error _ _ _ _ Hparams_safe Htype.
      unfold is_nonmutable_qualifier in Hsafe.
      destruct Hsafe as [-> | [-> | [-> | ->]]]; discriminate.
  - intros Hrdm. apply (Hno_rdm l).
    exists x, T. repeat split; assumption.
Qed.

(** Preservation, field write.  The environment is unchanged and
    [update_field] preserves the heap domain, so the invariant transports
    verbatim. *)
Lemma old_values_non_mutably_typed_after_field_write :
  forall h sGamma rGamma lx f v,
    old_values_non_mutably_typed h sGamma rGamma ->
    old_values_non_mutably_typed (update_field h lx f v) sGamma rGamma.
Proof.
  intros h sGamma rGamma lx f v Hinv x T l Htype Hvalue Hold.
  rewrite update_field_length in Hold.
  exact (Hinv x T l Htype Hvalue Hold).
Qed.

(** Preservation, local declaration.  The appended slot holds [Null_a], so it
    contributes no location; every older slot keeps both its type and its
    value. *)
Lemma old_values_non_mutably_typed_after_local :
  forall h sGamma rGamma T,
    old_values_non_mutably_typed h sGamma rGamma ->
    length sGamma = length (vars rGamma) ->
    old_values_non_mutably_typed h (sGamma ++ [T])
      (set_vars rGamma (vars rGamma ++ [Null_a])).
Proof.
  intros h sGamma rGamma T Hinv Hlen x T' l Htype Hvalue Hold.
  unfold static_getType in Htype. unfold runtime_getVal in Hvalue.
  simpl in Hvalue.
  destruct (lt_dec x (length (vars rGamma))) as [Hlt | Hge].
  - assert (Hts : nth_error (sGamma ++ [T]) x = nth_error sGamma x).
    { apply nth_error_app1. lia. }
    assert (Hvs : nth_error (vars rGamma ++ [Null_a]) x
                  = nth_error (vars rGamma) x).
    { apply nth_error_app1. lia. }
    rewrite Hts in Htype. rewrite Hvs in Hvalue.
    exact (Hinv x T' l Htype Hvalue Hold).
  - assert (Hvs : nth_error (vars rGamma ++ [Null_a]) x
                  = nth_error [Null_a] (x - length (vars rGamma))).
    { apply nth_error_app2. lia. }
    rewrite Hvs in Hvalue.
    destruct (x - length (vars rGamma)) as [|k]; simpl in Hvalue;
      [discriminate | destruct k; simpl in Hvalue; discriminate].
Qed.

(** Read side of the invariant.  A field read through a receiver that is
    neither [Mut] nor [RDM] never yields a [Mut] or [RDM] type: [RO] and
    [Lost] collapse [RDM_f] and [Mut_f] to [Lost], [Imm] sends [RDM_f] to
    [Imm] and [Mut_f] to [Lost], [Imm_f] always gives [Imm], and [RO_f]
    always gives [RO].

    So a frame that starts without [Mut]- or [RDM]-typed access to old
    objects cannot acquire it by reading: this is what keeps
    [old_values_non_mutably_typed] true across assignments. *)
Lemma readonly_state_field_read_through_non_mutable_is_non_mutable :
  forall q1 fm,
    q1 <> Mut ->
    q1 <> RDM ->
    vpa_mutability_stype_fld_readonly_state q1 fm <> Mut /\
    vpa_mutability_stype_fld_readonly_state q1 fm <> RDM.
Proof.
  intros q1 fm Hnot_mut Hnot_rdm.
  destruct q1; try (exfalso; congruence);
    destruct fm; simpl; split; discriminate.
Qed.

(** Subtyping side: a value whose own type is neither [Mut] nor [RDM], and
    which is not [Bot], can only be stored in a variable whose type is also
    neither.  [Bot] is excluded for a variable holding a location by
    [wf_config_nonnull_variable_not_bot]. *)
Lemma non_mutable_value_needs_non_mutable_slot :
  forall qe qx,
    qe <> Mut -> qe <> RDM -> qe <> Bot ->
    q_subtype qe qx ->
    qx <> Mut /\ qx <> RDM.
Proof.
  intros qe qx Hnot_mut Hnot_rdm Hnot_bot Hsub.
  inversion Hsub; subst; split; try congruence.
Qed.

(** A value fitting [Lost] is [Bot]. *)
Lemma q_subtype_lost_inversion :
  forall qa, q_subtype qa Lost -> qa = Bot.
Proof.
  intros qa Hsub.
  inversion Hsub; subst; congruence.
Qed.

(** * The RS mutable-freshness invariant

    The residual's refutation characterises what a readonly-state body can
    publish.  Three conjuncts, all relative to the entry heap [h0]:

    - J ([rs_mut_vars_fresh]): a [Mut]- or [RDM]-typed variable holding a
      runtime-mutable object holds a fresh one;
    - K ([rs_fresh_mut_fields_fresh]): mutable fields of fresh [Mut_r]
      objects hold fresh values whenever those values are runtime-mutable;
    - L ([rs_old_mut_fields_old]): mutable fields of old [Mut_r] objects
      still hold old values -- the body cannot write them at all. *)

Definition rs_mut_vars_fresh
  (h0 : heap) (sGamma : s_env) (rGamma : r_env) (h : heap) : Prop :=
  forall x T l,
    static_getType sGamma x = Some T ->
    runtime_getVal rGamma x = Some (Iot l) ->
    (sqtype T = Mut \/ sqtype T = RDM) ->
    r_muttype h l = Some Mut_r ->
    dom h0 <= l.

Definition rs_fresh_mut_fields_fresh
  (CT : class_table) (h0 h : heap) : Prop :=
  forall v o f l D fdef,
    dom h0 <= v ->
    runtime_getObj h v = Some o ->
    r_muttype h v = Some Mut_r ->
    getVal o.(fields_map) f = Some (Iot l) ->
    base_subtype CT (rctype (rt_type o)) D ->
    sf_def_rel CT D f fdef ->
    (mutability (ftype fdef) = RDM_f \/ mutability (ftype fdef) = Mut_f) ->
    r_muttype h l = Some Mut_r ->
    dom h0 <= l.

Definition rs_old_mut_fields_old
  (CT : class_table) (h0 h : heap) : Prop :=
  forall v o f l D fdef,
    v < dom h0 ->
    runtime_getObj h v = Some o ->
    r_muttype h v = Some Mut_r ->
    getVal o.(fields_map) f = Some (Iot l) ->
    base_subtype CT (rctype (rt_type o)) D ->
    sf_def_rel CT D f fdef ->
    (mutability (ftype fdef) = RDM_f \/ mutability (ftype fdef) = Mut_f) ->
    l < dom h0.

(** * The two-sided partition invariant

    Under the restored RO/RDM call rule a readonly-state frame may hold an
    OLD object at declared-RDM receiver type, so the freshness conjunct J is
    not hereditary across special call entries.  What is hereditary: every
    frame's [Mut]/[RDM]-typed [Mut_r] values lie entirely on ONE side of a
    partition of the [Mut_r] locations into [Old ∪ S] versus [Fresh ∖ S],
    where [S] collects exactly the locations allocated by left-side frames,
    and no retained/mutable edge between [Mut_r] endpoints ever crosses the
    partition. *)

Definition rs_left (h0 : heap) (S : list Loc) (l : Loc) : Prop :=
  l < dom h0 \/ List.In l S.

Definition rs_pool_left (h0 : heap) (S : list Loc)
    (sGamma : s_env) (rGamma : r_env) (h : heap) : Prop :=
  forall x T l, static_getType sGamma x = Some T ->
    runtime_getVal rGamma x = Some (Iot l) ->
    (sqtype T = Mut \/ sqtype T = RDM) ->
    r_muttype h l = Some Mut_r -> rs_left h0 S l.

Definition rs_pool_right (h0 : heap) (S : list Loc)
    (sGamma : s_env) (rGamma : r_env) (h : heap) : Prop :=
  forall x T l, static_getType sGamma x = Some T ->
    runtime_getVal rGamma x = Some (Iot l) ->
    (sqtype T = Mut \/ sqtype T = RDM) ->
    r_muttype h l = Some Mut_r -> dom h0 <= l /\ ~ List.In l S.

Definition rs_pool_sided h0 S (side : bool) sGamma rGamma h : Prop :=
  if side then rs_pool_right h0 S sGamma rGamma h
  else rs_pool_left h0 S sGamma rGamma h.

Definition rs_stitch_set_wf (h0 h : heap) (S : list Loc) : Prop :=
  forall l, List.In l S -> dom h0 <= l /\ l < dom h.

Definition rs_mut_edges_respect_sides CT (h0 : heap) (S : list Loc) h : Prop :=
  forall u v, retained_mut_edge CT h u v ->
    r_muttype h u = Some Mut_r -> r_muttype h v = Some Mut_r ->
    (rs_left h0 S u <-> rs_left h0 S v).

(** Side membership, uniform over the flag. *)
Definition rs_side (h0 : heap) (S : list Loc) (side : bool) (l : Loc) : Prop :=
  if side then dom h0 <= l /\ ~ List.In l S else rs_left h0 S l.

Lemma rs_pool_sided_spec :
  forall h0 S side sGamma rGamma h,
    rs_pool_sided h0 S side sGamma rGamma h <->
    (forall x T l, static_getType sGamma x = Some T ->
      runtime_getVal rGamma x = Some (Iot l) ->
      (sqtype T = Mut \/ sqtype T = RDM) ->
      r_muttype h l = Some Mut_r -> rs_side h0 S side l).
Proof.
  intros h0 S side sGamma rGamma h.
  destruct side; split; intros H; exact H.
Qed.

Lemma rs_side_not_left :
  forall h0 S l, (dom h0 <= l /\ ~ List.In l S) <-> ~ rs_left h0 S l.
Proof.
  intros h0 S l. unfold rs_left. split.
  - intros [Hge Hnin] [Hlt | Hin]; [lia | exact (Hnin Hin)].
  - intros Hnl. split.
    + destruct (lt_dec l (dom h0)) as [Hlt | Hge]; [|lia].
      exfalso. apply Hnl. left. exact Hlt.
    + intros Hin. apply Hnl. right. exact Hin.
Qed.

Lemma rs_side_edge_transport :
  forall CT h0 S h side u v,
    rs_mut_edges_respect_sides CT h0 S h ->
    retained_mut_edge CT h u v ->
    r_muttype h u = Some Mut_r ->
    r_muttype h v = Some Mut_r ->
    rs_side h0 S side u ->
    rs_side h0 S side v.
Proof.
  intros CT h0 S h side u v Hsides Hedge Hu Hv Hside.
  have Hiff := Hsides u v Hedge Hu Hv.
  destruct side; simpl in *.
  - apply (proj2 (rs_side_not_left h0 S v)).
    have Hnl := proj1 (rs_side_not_left h0 S u) Hside.
    intros Hleft. apply Hnl. apply (proj2 Hiff). exact Hleft.
  - apply (proj1 Hiff). exact Hside.
Qed.

Lemma rs_side_pair_iff :
  forall h0 S side u v,
    rs_side h0 S side u -> rs_side h0 S side v ->
    (rs_left h0 S u <-> rs_left h0 S v).
Proof.
  intros h0 S side u v Hu Hv.
  destruct side; simpl in *.
  - have Hnu := proj1 (rs_side_not_left h0 S u) Hu.
    have Hnv := proj1 (rs_side_not_left h0 S v) Hv.
    split; intros H; [exact (False_ind _ (Hnu H)) |
      exact (False_ind _ (Hnv H))].
  - split; intros _; assumption.
Qed.

Lemma rs_left_mono :
  forall h0 S S' l,
    (forall a, List.In a S -> List.In a S') ->
    rs_left h0 S l -> rs_left h0 S' l.
Proof.
  intros h0 S S' l Hincl [Hlt | Hin];
    [left; exact Hlt | right; apply Hincl; exact Hin].
Qed.

(** For a location below the growth cutoff, membership on the left is
    unchanged by growing the stitch set above the cutoff. *)
Lemma rs_left_grow_old_iff :
  forall (h0 h : heap) (S S' : list Loc) l,
    (forall a, List.In a S -> List.In a S') ->
    (forall a, List.In a S' -> List.In a S \/ dom h <= a) ->
    l < dom h ->
    (rs_left h0 S' l <-> rs_left h0 S l).
Proof.
  intros h0 h S S' l Hincl Hgrow Hl. unfold rs_left. split.
  - intros [Hlt | Hin]; [left; exact Hlt|].
    destruct (Hgrow l Hin) as [HinS | Hge]; [right; exact HinS | lia].
  - intros [Hlt | Hin]; [left; exact Hlt | right; apply Hincl; exact Hin].
Qed.

Lemma rs_side_grow :
  forall (h0 h : heap) (S S' : list Loc) side l,
    (forall a, List.In a S -> List.In a S') ->
    (forall a, List.In a S' -> List.In a S \/ dom h <= a) ->
    l < dom h ->
    rs_side h0 S side l -> rs_side h0 S' side l.
Proof.
  intros h0 h S S' side l Hincl Hgrow Hl Hside.
  destruct side; simpl in *.
  - destruct Hside as [Hge Hnin]. split; [exact Hge|].
    intros Hin.
    destruct (Hgrow l Hin) as [HinS | Hfresh]; [exact (Hnin HinS) | lia].
  - eapply rs_left_mono; [exact Hincl | exact Hside].
Qed.

(** Entry forms: at [h0 = h] with [S = []] every [Mut_r] location is on the
    left, so the partition holds trivially, and the channel-free entry pool
    is right-sided. *)
Lemma rs_mut_edges_respect_sides_entry :
  forall CT h, wf_heap CT h -> rs_mut_edges_respect_sides CT h [] h.
Proof.
  intros CT h Hheap u v Hedge Hu Hv.
  have Hu_dom : u < dom h.
  { inversion Hedge; subst.
    - inversion H; subst. eapply runtime_getObj_dom; eauto.
    - eapply runtime_getObj_dom; eauto. }
  have Hv_dom : v < dom h.
  { eapply retained_edge_target_dom; eauto. }
  unfold rs_left. split; intros _; left; assumption.
Qed.

Lemma rs_pool_right_from_mut_vars_fresh :
  forall h0 sGamma rGamma h,
    rs_mut_vars_fresh h0 sGamma rGamma h ->
    rs_pool_right h0 [] sGamma rGamma h.
Proof.
  intros h0 sGamma rGamma h HJ x T l Htype Hvalue Hkind Hmut.
  split; [eapply HJ; eauto | intros Hin; inversion Hin].
Qed.

(** A [Mut]-typed variable of a well-formed configuration denotes a
    runtime-mutable object.  Mirror of [typed_imm_root_runtime_immutable_live]:
    [vpa_mutability_runtime ctx Mut = Mut], and [qualifier_typable_context]
    rejects [Mut] under an [Imm_r] runtime type. *)
Lemma typed_mut_root_runtime_mutable_live :
  forall CT sGamma rGamma h root,
    wf_r_config CT sGamma rGamma h ->
    typed_root Mut sGamma rGamma root ->
    r_muttype h root = Some Mut_r.
Proof.
  intros CT sGamma rGamma h root Hwf
    [variable [T [Htype [Hvalue Hmut]]]].
  destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwf) as
    [receiver [context [Hreceiver [_ Hcontext]]]].
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [_ [_ [_ Hcorrespondence]]]]].
  have Hvariable_dom := Htype. apply static_getType_dom in Hvariable_dom.
  specialize (Hcorrespondence receiver context Hreceiver Hcontext variable
    Hvariable_dom T Htype).
  rewrite Hvalue in Hcorrespondence.
  unfold wf_r_typable, r_type in Hcorrespondence.
  destruct (runtime_getObj h root) as [object|] eqn:Hobject;
    try contradiction.
  destruct Hcorrespondence as [_ Hqualifier].
  unfold qualifier_typable_context, vpa_mutability_runtime in Hqualifier.
  rewrite Hmut in Hqualifier.
  unfold r_muttype. rewrite Hobject. simpl.
  destruct (rqtype (rt_type object)).
  - reflexivity.
  - destruct context; contradiction.
Qed.

(** Field values of a well-formed heap lie in its domain. *)
Lemma wf_heap_field_value_dom :
  forall CT h v o f l,
    wf_heap CT h ->
    runtime_getObj h v = Some o ->
    getVal o.(fields_map) f = Some (Iot l) ->
    l < dom h.
Proof.
  intros CT h v o f l Hheap Hobj Hval.
  have Hvdom : v < dom h.
  { eapply runtime_getObj_dom. exact Hobj. }
  specialize (Hheap v Hvdom). unfold wf_obj in Hheap.
  rewrite Hobj in Hheap.
  destruct Hheap as [_ [field_defs [_ [Hlen Hfields]]]].
  unfold getVal in Hval.
  destruct (nth_error field_defs f) as [fdef|] eqn:Hfdef.
  - have Hpair := Forall2_nth_error _ _ _ _ _ _ Hfields Hval Hfdef.
    simpl in Hpair.
    destruct (runtime_getObj h l) as [lobj|] eqn:Hlobj; [|contradiction].
    eapply runtime_getObj_dom. exact Hlobj.
  - exfalso.
    have Hlt : f < length o.(fields_map).
    { apply nth_error_Some. rewrite Hval. discriminate. }
    rewrite Hlen in Hlt.
    apply nth_error_Some in Hlt. congruence.
Qed.

(** Entry forms of the three conjuncts, at [h0 = h]. *)
Lemma rs_mut_vars_fresh_channel_free_entry :
  forall h0 h msig rGamma,
    signature_has_no_mutable_roots msig ->
    (forall root,
      ~ typed_root RDM (mreceiver msig :: mparams msig) rGamma root) ->
    rs_mut_vars_fresh h0 (mreceiver msig :: mparams msig) rGamma h.
Proof.
  intros h0 h msig rGamma [Hreceiver_safe Hparams_safe] Hno_rdm x T l
    Htype Hvalue Hkind Hruntime.
  exfalso. destruct Hkind as [Hmut | Hrdm].
  - destruct x as [|parameter].
    + simpl in Htype. injection Htype as <-.
      unfold is_nonmutable_qualifier in Hreceiver_safe.
      rewrite Hmut in Hreceiver_safe.
      destruct Hreceiver_safe as [Hbad | [Hbad | [Hbad | Hbad]]];
        discriminate.
    + simpl in Htype. unfold static_getType in Htype.
      have Hsafe : is_nonmutable_qualifier (sqtype T) :=
        Forall_nth_error _ _ _ _ Hparams_safe Htype.
      unfold is_nonmutable_qualifier in Hsafe.
      rewrite Hmut in Hsafe.
      destruct Hsafe as [Hbad | [Hbad | [Hbad | Hbad]]]; discriminate.
  - apply (Hno_rdm l). exists x, T. repeat split; assumption.
Qed.

Lemma rs_fresh_mut_fields_fresh_entry :
  forall CT h,
    rs_fresh_mut_fields_fresh CT h h.
Proof.
  intros CT h v o f l D fdef Hfresh Hobj Hmut Hval Hsub Hfd Hfm Hlmut.
  exfalso.
  have Hvdom : v < dom h.
  { eapply runtime_getObj_dom. exact Hobj. }
  lia.
Qed.

Lemma rs_old_mut_fields_old_entry :
  forall CT h,
    wf_heap CT h ->
    rs_old_mut_fields_old CT h h.
Proof.
  intros CT h Hheap v o f l D fdef Hold Hobj Hmut Hval Hsub Hfd Hfm.
  eapply wf_heap_field_value_dom; eauto.
Qed.

(** ** Table micro-lemmas for the preservation induction *)

(** Subtyping into a [Mut]/[RDM] slot admits only the same qualifier or
    [Bot]. *)
Lemma mutable_slot_subtype_inversion :
  forall qe qx,
    q_subtype qe qx ->
    (qx = Mut \/ qx = RDM) ->
    qe = qx \/ qe = Bot.
Proof.
  intros qe qx Hsub Hkind.
  inversion Hsub; subst; auto.
  destruct Hkind; discriminate.
Qed.

(** The readonly-state field-read table yields [Mut]/[RDM] only from a
    [Mut]/[RDM] receiver on a mutable field. *)
Lemma readonly_state_field_read_mutable_inversion :
  forall t fm,
    (vpa_mutability_stype_fld_readonly_state t fm = Mut \/
     vpa_mutability_stype_fld_readonly_state t fm = RDM) ->
    (t = Mut /\ (fm = RDM_f \/ fm = Mut_f)) \/
    (t = RDM /\ fm = RDM_f).
Proof.
  intros t fm Hread.
  destruct t; destruct fm; simpl in Hread;
    destruct Hread as [Hread | Hread]; try discriminate; auto.
Qed.

(** Writing a location into a mutable field slot: the receiver is [Imm]
    (and the value [Imm]), or the receiver and value are both mutable. *)
Lemma readonly_state_mut_field_write_inversion :
  forall t fm qy,
    (fm = RDM_f \/ fm = Mut_f) ->
    q_subtype qy (vpa_mutability_stype_fld_readonly_state t fm) ->
    qy = Bot \/
    (t = Imm /\ qy = Imm) \/
    ((t = Mut \/ t = RDM) /\ (qy = Mut \/ qy = RDM)).
Proof.
  intros t fm qy Hfm Hsub.
  destruct Hfm as [-> | ->]; destruct t; simpl in Hsub;
    inversion Hsub; subst; try congruence; auto 7.
Qed.

(** The readonly-state call channel: a [Mut]/[RDM] parameter receives only
    [Mut]/[RDM]-typed (or [Bot]) arguments, except that an [Imm] receiver
    view feeds an [RDM] parameter with [Imm]-typed arguments. *)
Lemma readonly_state_call_channel_inversion :
  forall t p qa,
    (p = Mut \/ p = RDM) ->
    q_subtype qa (vpa_mutability_qq_readonly_state t p) ->
    qa = Bot \/
    (t = Imm /\ p = RDM /\ qa = Imm) \/
    ((t = Mut \/ t = RDM) /\ (qa = Mut \/ qa = RDM)).
Proof.
  intros t p qa Hp Hsub.
  destruct Hp as [-> | ->]; destruct t; simpl in Hsub;
    inversion Hsub; subst; try congruence; auto 8.
Qed.

(** Base-subtype extraction for a variable's heap object. *)
Lemma typed_var_object_base_subtype :
  forall CT sGamma rGamma h y T w o,
    wf_r_config CT sGamma rGamma h ->
    static_getType sGamma y = Some T ->
    runtime_getVal rGamma y = Some (Iot w) ->
    runtime_getObj h w = Some o ->
    base_subtype CT (rctype (rt_type o)) (sctype T).
Proof.
  intros CT sGamma rGamma h y T w o Hwf Htype Hvalue Hobj.
  destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwf) as
    [receiver [context [Hreceiver [_ Hcontext]]]].
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [_ [_ [_ Hcorrespondence]]]]].
  have Hdom := Htype. apply static_getType_dom in Hdom.
  specialize (Hcorrespondence receiver context Hreceiver Hcontext y Hdom
    T Htype).
  rewrite Hvalue in Hcorrespondence.
  unfold wf_r_typable, r_type in Hcorrespondence.
  rewrite Hobj in Hcorrespondence.
  exact (proj1 Hcorrespondence).
Qed.

(** ** Per-statement preservation of the partition *)

(** Variable assignment.  The heap is unchanged; only the [x] slot of the
    pool changes.  A location can be assigned at [Mut]/[RDM] type only from
    a variable of the same qualifier (the pool applies directly) or by
    reading a mutable field of a [Mut]/[RDM] receiver -- in which case the
    receiver's object is runtime-mutable and pool-sided, and the edge
    condition transports the side across the field edge. *)
Lemma rs_sides_after_assignment :
  forall CT h0 S side sGamma mt rGamma h x e old value,
    wf_r_config CT sGamma rGamma h ->
    readonly_state_method_scope mt ->
    stmt_typing CT sGamma mt (SVarAss x e) sGamma ->
    runtime_getVal rGamma x = Some old ->
    eval_expr CT rGamma h e value OK rGamma h ->
    rs_mut_edges_respect_sides CT h0 S h ->
    rs_pool_sided h0 S side sGamma rGamma h ->
    rs_pool_sided h0 S side sGamma (update_r_env_value rGamma x value) h.
Proof.
  intros CT h0 S side sGamma mt rGamma h x e old value Hwf Hscope Htyping Hx
    Heval Hsides Hpool.
  have Huse := proj1 (rs_pool_sided_spec _ _ _ _ _ _) Hpool.
  apply (proj2 (rs_pool_sided_spec _ _ _ _ _ _)).
  intros y T l Htype Hvalue Hkind Hmut.
  destruct (Nat.eq_dec y x) as [-> | Hneq].
  2:{ have Hxy : x <> y by (intros ->; apply Hneq; reflexivity).
      have Hold_value := runtime_getVal_update_diff rGamma x y value Hxy.
      rewrite Hvalue in Hold_value.
      eapply Huse; eauto. }
  (* the updated slot *)
  have Hxdom : x < dom (vars rGamma).
  { unfold runtime_getVal in Hx. apply nth_error_Some. rewrite Hx.
    discriminate. }
  have Hsame := runtime_getVal_update_same rGamma x value Hxdom.
  rewrite Hsame in Hvalue. injection Hvalue as ->.
  inversion Htyping; subst.
  assert (T = Tx) by congruence. subst T.
  inversion Heval; subst.
  - (* EVar z *)
    inversion Htype_e; subst.
    have Hq := qualified_type_subtype_q_subtype _ _ _ Hsub.
    destruct (mutable_slot_subtype_inversion _ _ Hq Hkind) as [Heq | Hbot].
    + eapply Huse; eauto. rewrite Heq. exact Hkind.
    + exfalso.
      eapply wf_config_nonnull_variable_not_bot; eauto.
  - (* EField z f *)
    inversion Htype_e; subst.
    { destruct Hscope as [Hrs | Hts]; destruct Hmt as [Hmt | Hmt];
        congruence. }
    have Hq := qualified_type_subtype_q_subtype _ _ _ Hsub.
    simpl in Hq.
    destruct (mutable_slot_subtype_inversion _ _ Hq Hkind) as [Heq | Hbot].
    2:{ exfalso.
        assert (Hzbot : sqtype T = Bot).
        { destruct (sqtype T); destruct (mutability (ftype fDef));
            simpl in Hbot; try discriminate; reflexivity. }
        eapply wf_config_nonnull_variable_not_bot with (x := x0); eauto. }
    assert (Hkind' : vpa_mutability_stype_fld_readonly_state (sqtype T)
        (mutability (ftype fDef)) = Mut \/
      vpa_mutability_stype_fld_readonly_state (sqtype T)
        (mutability (ftype fDef)) = RDM).
    { rewrite Heq. exact Hkind. }
    have Hheap : wf_heap CT h := proj1 (proj2 Hwf).
    have Hbase : base_subtype CT (rctype (rt_type o)) (sctype T).
    { eapply typed_var_object_base_subtype; eauto. }
    destruct (readonly_state_field_read_mutable_inversion _ _ Hkind') as
      [[Hz_mut Hfm] | [Hz_rdm Hfm]].
    + (* receiver variable typed Mut: its object is runtime-mutable *)
      have Hw_mut : r_muttype h v = Some Mut_r.
      { eapply typed_mut_root_runtime_mutable_live; eauto.
        exists x0, T. repeat split; assumption. }
      have Hedge : retained_mut_edge CT h v l.
      { destruct Hfm as [Hrdm_f | Hmut_f].
        - apply retained_edge_rdm. eapply mutable_edge_rdm; eauto.
        - eapply retained_edge_mut; eauto. }
      have Hside_v : rs_side h0 S side v.
      { eapply Huse with (x := x0) (T := T);
          [assumption | assumption | left; exact Hz_mut | exact Hw_mut]. }
      eapply rs_side_edge_transport; eauto.
    + (* receiver variable typed RDM on an RDM_f field *)
      have Hmedge : mutable_edge CT h v l.
      { eapply mutable_edge_rdm; eauto. }
      have Hw_mut : r_muttype h v = Some Mut_r.
      { eapply mutable_edge_reflects_runtime_mutability; eauto. }
      have Hside_v : rs_side h0 S side v.
      { eapply Huse with (x := x0) (T := T);
          [assumption | assumption | right; exact Hz_rdm | exact Hw_mut]. }
      eapply rs_side_edge_transport; eauto.
      apply retained_edge_rdm. exact Hmedge.
Qed.

(** Field write.  The environment is unchanged and [update_field] preserves
    both the heap domain and runtime mutability, so the stitch set and pool
    transport verbatim.  The edge condition gains exactly one edge -- the
    written slot -- whose endpoints are both pool members of the writing
    frame (the [Imm] and [Bot] channels cannot put a [Mut_r] value behind a
    mutable field), hence on the same side. *)
Lemma rs_sides_after_field_write :
  forall CT h0 S side sGamma mt rGamma h x f y sGamma' rGamma' h',
    wf_r_config CT sGamma rGamma h ->
    readonly_state_method_scope mt ->
    stmt_typing CT sGamma mt (SFldWrite x f y) sGamma' ->
    eval_stmt CT rGamma h (SFldWrite x f y) OK rGamma' h' ->
    rs_stitch_set_wf h0 h S ->
    rs_mut_edges_respect_sides CT h0 S h ->
    rs_pool_sided h0 S side sGamma rGamma h ->
    rs_stitch_set_wf h0 h' S /\
    rs_mut_edges_respect_sides CT h0 S h' /\
    rs_pool_sided h0 S side sGamma' rGamma' h'.
Proof.
  intros CT h0 S side sGamma mt rGamma h x f y sGamma' rGamma' h' Hwf Hscope
    Htyping Heval Hstitch Hsides Hpool.
  have Huse := proj1 (rs_pool_sided_spec _ _ _ _ _ _) Hpool.
  inversion Heval; subst.
  assert (Hstatic : exists Tx Ty fieldT,
      static_getType sGamma x = Some Tx /\
      static_getType sGamma y = Some Ty /\
      sf_def_rel CT (sctype Tx) f fieldT /\
      qualified_type_subtype CT Ty
        (Build_qualified_type
          (vpa_mutability_stype_fld_readonly_state (sqtype Tx)
            (mutability (ftype fieldT)))
          (f_base_type (ftype fieldT))) /\
      sGamma' = sGamma).
  { inversion Htyping; subst;
      try (destruct Hscope as [Hbad | Hbad]; discriminate).
    - exists Tx, Ty, fieldT. repeat split; assumption.
    - exists Tx, Ty, fieldT. repeat split; assumption. }
  destruct Hstatic as [Tx [Ty [fieldT [Hget_x [Hget_y [Hfld [Hsub ->]]]]]]].
  have Hlocdom : loc_x < dom h.
  { eapply runtime_getObj_dom. eassumption. }
  split; [|split].
  - (* stitch set: the domain is unchanged *)
    intros l Hin. destruct (Hstitch l Hin) as [Hge Hlt].
    split; [exact Hge|]. rewrite update_field_length. exact Hlt.
  - (* edge condition *)
    intros u v Hedge Humut Hvmut.
    rewrite r_muttype_update_field_preserve in Humut.
    rewrite r_muttype_update_field_preserve in Hvmut.
    destruct (retained_edge_after_field_update CT h loc_x o f val_y u v Hobj
      Hedge) as [Hold_edge | [-> [Hval_eq [D' [fdef' [Hbase' [Hfd' Hfm']]]]]]].
    + eapply Hsides; eauto.
    + (* the written slot: u = loc_x, val_y = Iot v *)
      subst val_y.
      have Hbase_x : base_subtype CT (rctype (rt_type o)) (sctype Tx).
      { eapply typed_var_object_base_subtype; eauto. }
      have Hfd_C : FieldLookup CT (rctype (rt_type o)) f fdef'.
      { eapply field_inheritance_subtyping; [exact Hbase' | exact Hfd']. }
      have Hft_C : FieldLookup CT (rctype (rt_type o)) f fieldT.
      { eapply field_inheritance_subtyping; [exact Hbase_x | exact Hfld]. }
      have Hfdef_eq : fdef' = fieldT.
      { eapply field_lookup_deterministic_rel; eauto. }
      subst fdef'.
      have Hq := qualified_type_subtype_q_subtype _ _ _ Hsub. simpl in Hq.
      destruct (readonly_state_mut_field_write_inversion _ _ _ Hfm' Hq) as
        [Hybot | [[Hximm Hyimm] | [Hxmut Hymut]]].
      * exfalso. eapply wf_config_nonnull_variable_not_bot with (x := y);
          eauto.
      * exfalso.
        have Himm : r_muttype h loc_x = Some Imm_r.
        { eapply typed_imm_root_runtime_immutable_live; eauto.
          exists x, Tx. repeat split; assumption. }
        congruence.
      * have Hside_u : rs_side h0 S side loc_x.
        { eapply Huse with (x := x) (T := Tx);
            [exact Hget_x | exact Hval_x | exact Hxmut | exact Humut]. }
        have Hside_v : rs_side h0 S side v.
        { eapply Huse with (x := y) (T := Ty);
            [exact Hget_y | exact Hval_y | exact Hymut | exact Hvmut]. }
        eapply rs_side_pair_iff; [exact Hside_u | exact Hside_v].
  - (* pool: environment unchanged, runtime types unchanged *)
    apply (proj2 (rs_pool_sided_spec _ _ _ _ _ _)).
    intros z T l Htype Hvalue Hkind Hmut.
    rewrite r_muttype_update_field_preserve in Hmut.
    eapply Huse; eauto.
Qed.

(** Local declaration: the appended slot holds [Null_a] and the heap is
    unchanged. *)
Lemma rs_sides_after_local :
  forall h0 S side sGamma rGamma h T,
    length sGamma = length (vars rGamma) ->
    rs_pool_sided h0 S side sGamma rGamma h ->
    rs_pool_sided h0 S side (sGamma ++ [T])
      (set_vars rGamma (vars rGamma ++ [Null_a])) h.
Proof.
  intros h0 S side sGamma rGamma h T Hlen Hpool.
  have Huse := proj1 (rs_pool_sided_spec _ _ _ _ _ _) Hpool.
  apply (proj2 (rs_pool_sided_spec _ _ _ _ _ _)).
  intros x T' l Htype Hvalue Hkind Hmut.
  unfold static_getType in Htype. unfold runtime_getVal in Hvalue.
  simpl in Hvalue.
  destruct (lt_dec x (length (vars rGamma))) as [Hlt | Hge].
  - assert (Hts : nth_error (sGamma ++ [T]) x = nth_error sGamma x).
    { apply nth_error_app1. lia. }
    assert (Hvs : nth_error (vars rGamma ++ [Null_a]) x
                  = nth_error (vars rGamma) x).
    { apply nth_error_app1. lia. }
    rewrite Hts in Htype. rewrite Hvs in Hvalue.
    eapply Huse; eauto.
  - assert (Hvs : nth_error (vars rGamma ++ [Null_a]) x
                  = nth_error [Null_a] (x - length (vars rGamma))).
    { apply nth_error_app2. lia. }
    rewrite Hvs in Hvalue.
    destruct (x - length (vars rGamma)) as [|k]; simpl in Hvalue;
      [discriminate | destruct k; simpl in Hvalue; discriminate].
Qed.

(** [r_muttype] is stable on the left of a heap append. *)
Lemma r_muttype_app_left :
  forall h ext l,
    l < dom h ->
    r_muttype (h ++ [ext]) l = r_muttype h l.
Proof.
  intros h ext l Hl.
  unfold r_muttype, runtime_getObj.
  rewrite nth_error_app1; [exact Hl | reflexivity].
Qed.

(** Constructor micro-lemmas for the [SNew] case.  A mutable field's
    corresponding constructor parameter is [Mut], [RDM], [Imm] or [Bot]... *)
Lemma constructor_mut_field_param_shape :
  forall cq p fm,
    (fm = RDM_f \/ fm = Mut_f) ->
    q_subtype (vpa_mutability_qq_abstract_state (qc2q cq) p)
      (vpa_mutability_constructor_fld cq fm) ->
    p = Mut \/ p = RDM \/ p = Imm \/ p = Bot.
Proof.
  intros cq p fm Hfm Hsub.
  destruct Hfm as [-> | ->]; destruct cq; destruct p; simpl in Hsub;
    inversion Hsub; subst; try congruence; auto.
Qed.

(** ...and the call-site adaptation of such a parameter admits only [Bot],
    [Imm], [Mut] or [RDM] argument qualifiers. *)
Lemma constructor_param_site_channel :
  forall qc p qa,
    (p = Mut \/ p = RDM \/ p = Imm \/ p = Bot) ->
    q_subtype qa (vpa_mutability_qq_abstract_state (qc2q qc) p) ->
    qa = Bot \/ qa = Imm \/ qa = Mut \/ qa = RDM.
Proof.
  intros qc p qa Hp Hsub.
  destruct Hp as [-> | [-> | [-> | ->]]]; destruct qc; simpl in Hsub;
    inversion Hsub; subst; try congruence; auto.
Qed.

(** A mutable field of a freshly constructed object holding a runtime-mutable
    value is fed by a [Mut]/[RDM]-typed argument variable of the creating
    frame: the constructor channel admits only [Bot] (killed by non-nullity),
    [Imm] (the value would be runtime-immutable) or [Mut]/[RDM]. *)
Lemma rs_new_object_mut_field_arg_is_pool_member :
  forall CT sGamma mt rGamma h x qc C args sGamma' vals f D fdef v,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    getVal vals f = Some (Iot v) ->
    base_subtype CT C D ->
    sf_def_rel CT D f fdef ->
    (mutability (ftype fdef) = RDM_f \/ mutability (ftype fdef) = Mut_f) ->
    r_muttype h v = Some Mut_r ->
    exists z A,
      static_getType sGamma z = Some A /\
      runtime_getVal rGamma z = Some (Iot v) /\
      (sqtype A = Mut \/ sqtype A = RDM).
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' vals f D fdef v Hwf
    Htyping Hargs Hval' Hbase Hfd Hfm Hvmut.
  inversion Htyping; subst.
  (* locate the argument variable feeding slot f *)
  destruct (runtime_lookup_list_nth_zs _ _ _ _ _ Hargs Hval') as
    [z [Hzs Hzval]].
  (* fdef is the f-th collected field *)
  have Hfl : FieldLookup CT C f fdef.
  { eapply field_inheritance_subtyping; [exact Hbase | exact Hfd]. }
  (* constructor well-formedness *)
  have HCdom : C < dom CT.
  { unfold constructor_sig_lookup, constructor_def_lookup in Hconsig.
    destruct (find_class CT C) as [cdef|] eqn:Hfind; [|discriminate].
    eapply find_class_dom. exact Hfind. }
  have Hwf_ct : wf_class_table CT := proj1 Hwf.
  have Hctor := constructor_lookup_wf CT C consig Hwf_ct HCdom Hconsig.
  unfold wf_constructor in Hctor.
  destruct Hctor as [Hbound [Hparams_wf [field_defs
    [Hcollect [Hlen_pf Hcompat]]]]].
  (* the two field collections coincide *)
  inversion Hfl; subst.
  have Hfields_eq : fields = field_defs.
  { eapply collect_fields_deterministic_rel; eauto. }
  subst fields.
  (* the f-th constructor parameter exists *)
  have Hf_lt : f < length field_defs.
  { apply nth_error_Some. unfold gget in Hget. rewrite Hget.
    discriminate. }
  have Hcp : exists cp, nth_error (cparams consig) f = Some cp.
  { destruct (nth_error (cparams consig) f) as [cp|] eqn:Hcp_eq.
    - exists cp. reflexivity.
    - exfalso. apply nth_error_None in Hcp_eq. lia. }
  destruct Hcp as [cp Hcp].
  (* wf side: the parameter fits the field *)
  have Hwf_pair := Forall2_nth_error _ _ _ _ _ _ Hcompat Hcp Hget.
  (* site side: the argument fits the adapted parameter *)
  have Hlen_at : length argtypes = length (cparams consig).
  { have Hl1 := Forall2_length Harg_sub.
    rewrite length_map in Hl1. exact Hl1. }
  have Hat : exists T_arg, nth_error argtypes f = Some T_arg.
  { destruct (nth_error argtypes f) as [T_arg|] eqn:Hat_eq.
    - exists T_arg. reflexivity.
    - exfalso. apply nth_error_None in Hat_eq. lia. }
  destruct Hat as [T_arg Hat].
  have Hmap_nth : nth_error
      (map (vpa_mutability_constructor_param qc) (cparams consig)) f
    = Some (vpa_mutability_constructor_param qc cp).
  { eapply map_nth_error. exact Hcp. }
  have Hsite_pair := Forall2_nth_error _ _ _ _ _ _ Harg_sub Hat Hmap_nth.
  have Hz_type : static_getType sGamma' z = Some T_arg.
  { eapply static_getType_list_index_strong; eauto. }
  (* q-level analysis *)
  have Hwf_q := qualified_type_subtype_q_subtype _ _ _ Hwf_pair.
  simpl in Hwf_q.
  have Hsite_q := qualified_type_subtype_q_subtype _ _ _ Hsite_pair.
  simpl in Hsite_q.
  have Hp_shape : sqtype cp = Mut \/ sqtype cp = RDM \/
      sqtype cp = Imm \/ sqtype cp = Bot.
  { eapply constructor_mut_field_param_shape with
      (cq := cqualifier consig); eauto. }
  have Hqa_shape := constructor_param_site_channel _ _ _ Hp_shape Hsite_q.
  destruct Hqa_shape as [Hbot | [Himm | Hkind]].
  - exfalso. eapply wf_config_nonnull_variable_not_bot with (x := z);
      eauto.
  - exfalso.
    have Hlimm : r_muttype h v = Some Imm_r.
    { eapply typed_imm_root_runtime_immutable_live; eauto.
      exists z, T_arg. repeat split; assumption. }
    congruence.
  - exists z, T_arg. repeat split; assumption.
Qed.

(** Object creation.  The new slot is fresh; old objects are untouched by
    the append.  With [side = false] the fresh location joins the stitch
    set, with [side = true] it stays on the right -- either way the new
    object lands on the creating frame's own side, and its mutable fields
    are constructor arguments on the same side. *)
Lemma rs_sides_after_new :
  forall CT h0 S side sGamma mt rGamma h x qc C args sGamma' rGamma' h',
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    eval_stmt CT rGamma h (SNew x qc C args) OK rGamma' h' ->
    dom h0 <= dom h ->
    rs_stitch_set_wf h0 h S ->
    rs_mut_edges_respect_sides CT h0 S h ->
    rs_pool_sided h0 S side sGamma rGamma h ->
    exists S',
      (forall l, List.In l S -> List.In l S') /\
      (forall l, List.In l S' -> List.In l S \/ dom h <= l) /\
      rs_stitch_set_wf h0 h' S' /\
      rs_mut_edges_respect_sides CT h0 S' h' /\
      rs_pool_sided h0 S' side sGamma' rGamma' h'.
Proof.
  intros CT h0 S side sGamma mt rGamma h x qc C args sGamma' rGamma' h' Hwf
    Htyping Heval Hgrow Hstitch Hsides Hpool.
  have Huse := proj1 (rs_pool_sided_spec _ _ _ _ _ _) Hpool.
  have Htyping_copy := Htyping.
  inversion Heval; subst.
  inversion Htyping; subst.
  have Hheap : wf_heap CT h := proj1 (proj2 Hwf).
  exists (if side then S else dom h :: S).
  assert (Hincl : forall l, List.In l S ->
      List.In l (if side then S else dom h :: S)).
  { destruct side; intros l Hin; [exact Hin | right; exact Hin]. }
  assert (Hgrow' : forall l, List.In l (if side then S else dom h :: S) ->
      List.In l S \/ dom h <= l).
  { destruct side; intros l Hin; [left; exact Hin|].
    destruct Hin as [<- | Hin]; [right; lia | left; exact Hin]. }
  assert (Hnew_side : rs_side h0 (if side then S else dom h :: S) side
      (dom h)).
  { destruct side; simpl.
    - split; [exact Hgrow|]. intros Hin.
      have Hbad := proj2 (Hstitch _ Hin). lia.
    - right. left. reflexivity. }
  split; [exact Hincl|]. split; [exact Hgrow'|]. split; [|split].
  - (* stitch set *)
    intros l Hin.
    rewrite length_app. simpl.
    destruct (Hgrow' l Hin) as [HinS | Hfresh].
    + destruct (Hstitch l HinS) as [Hge Hlt]. split; [exact Hge | lia].
    + destruct side.
      * destruct (Hstitch l Hin) as [Hge Hlt]. split; [exact Hge | lia].
      * destruct Hin as [<- | HinS]; [split; [exact Hgrow | lia]|].
        destruct (Hstitch l HinS) as [Hge Hlt]. split; [exact Hge | lia].
  - (* edge condition *)
    intros u v Hedge Humut Hvmut.
    destruct (retained_edge_after_append CT h _ u v Hedge) as
      [Hold_edge | [-> [f [D [fdef [Hval' [Hbase [Hfd Hfm]]]]]]]].
    + (* an edge of h: both endpoints below dom h *)
      have Hu_dom : u < dom h.
      { inversion Hold_edge; subst.
        - inversion H; subst. eapply runtime_getObj_dom; eauto.
        - eapply runtime_getObj_dom; eauto. }
      have Hv_dom : v < dom h.
      { eapply retained_edge_target_dom; eauto. }
      rewrite r_muttype_app_left in Humut; [exact Hu_dom|].
      rewrite r_muttype_app_left in Hvmut; [exact Hv_dom|].
      have Hiff := Hsides u v Hold_edge Humut Hvmut.
      split; intros Hmem.
      * apply (proj2 (rs_left_grow_old_iff h0 h S _ v Hincl Hgrow' Hv_dom)).
        apply (proj1 Hiff).
        apply (proj1 (rs_left_grow_old_iff h0 h S _ u Hincl Hgrow' Hu_dom)).
        exact Hmem.
      * apply (proj2 (rs_left_grow_old_iff h0 h S _ u Hincl Hgrow' Hu_dom)).
        apply (proj2 Hiff).
        apply (proj1 (rs_left_grow_old_iff h0 h S _ v Hincl Hgrow' Hv_dom)).
        exact Hmem.
    + (* the new object's edge: u = dom h, v is a constructor argument *)
      simpl in Hval', Hbase.
      destruct (runtime_lookup_list_nth_zs _ _ _ _ _ Hargs Hval') as
        [z0 [Hz0s Hz0val]].
      have Hv_dom : v < dom h.
      { eapply wf_config_value_dom; eauto. }
      rewrite r_muttype_app_left in Hvmut; [exact Hv_dom|].
      destruct (rs_new_object_mut_field_arg_is_pool_member CT _ mt
        _ h x qc _ args _ vals f D fdef v Hwf Htyping_copy Hargs
        Hval' Hbase Hfd Hfm Hvmut) as [z [A [Hz_type [Hz_val Hz_kind]]]].
      have Hside_v : rs_side h0 S side v.
      { eapply Huse with (x := z) (T := A);
          [exact Hz_type | exact Hz_val | exact Hz_kind | exact Hvmut]. }
      have Hside_v' : rs_side h0 (if side then S else dom h :: S) side v.
      { eapply rs_side_grow with (S := S) (h := h);
          [exact Hincl | exact Hgrow' | exact Hv_dom | exact Hside_v]. }
      eapply rs_side_pair_iff; [exact Hnew_side | exact Hside_v'].
  - (* pool *)
    apply (proj2 (rs_pool_sided_spec _ _ _ _ _ _)).
    intros z T l Htype Hvalue Hkind Hzmut.
    assert (Henv_eq : set_vars rGamma (update x (Iot (dom h)) (vars rGamma))
        = update_r_env_value rGamma x (Iot (dom h))).
    { destruct rGamma. reflexivity. }
    rewrite Henv_eq in Hvalue.
    destruct (Nat.eq_dec z x) as [-> | Hneq].
    + have Hxs : x < length sGamma'.
      { apply nth_error_Some. unfold static_getType in Htype.
        rewrite Htype. discriminate. }
      have Hlength := proj1 (proj2 (proj2 (proj2 (proj2 Hwf)))).
      have Hxdom : x < dom (vars rGamma).
      { lia. }
      have Hsame := runtime_getVal_update_same rGamma x (Iot (dom h)) Hxdom.
      rewrite Hsame in Hvalue. injection Hvalue as <-.
      exact Hnew_side.
    + have Hxz : x <> z by congruence.
      have Hold_value := runtime_getVal_update_diff rGamma x z
        (Iot (dom h)) Hxz.
      rewrite Hold_value in Hvalue.
      have Hldom : l < dom h.
      { eapply wf_config_value_dom; eauto. }
      rewrite r_muttype_app_left in Hzmut; [exact Hldom|].
      eapply rs_side_grow with (S := S) (h := h);
        [exact Hincl | exact Hgrow' | exact Hldom |].
      eapply Huse; eauto.
Qed.

(** J at a nested call entry, over the DYNAMIC callee signature.  A dynamic
    [Mut] position is excluded by [signature_has_no_mutable_roots]; a dynamic
    [RDM] position reflects to an [RDM]-or-[Bot] static position
    (refinement), whose readonly-state call channel admits only [Bot]
    (killed by non-nullity), [Imm]-typed arguments (the value is
    runtime-immutable) or [Mut]/[RDM]-typed arguments (J applies in the
    caller). *)
Lemma rs_mut_vars_fresh_call_entry :
  forall CT h0 sGamma rGamma h y Ty ly args vals argtypes runtime_mdef
    static_sig,
    wf_r_config CT sGamma rGamma h ->
    rs_mut_vars_fresh h0 sGamma rGamma h ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    runtime_lookup_list rGamma args = Some vals ->
    static_getType_list sGamma args = Some argtypes ->
    method_signature_refinement CT (msignature runtime_mdef) static_sig ->
    signature_has_no_mutable_roots (msignature runtime_mdef) ->
    qualified_type_subtype CT Ty
      (vpa_mutability_tt_readonly_state Ty (mreceiver static_sig)) ->
    Forall2 (fun arg T => qualified_type_subtype CT arg
        (vpa_mutability_tt_readonly_state Ty T))
      argtypes (mparams static_sig) ->
    rs_mut_vars_fresh h0
      (mreceiver (msignature runtime_mdef)
        :: mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) h.
Proof.
  intros CT h0 sGamma rGamma h y Ty ly args vals argtypes runtime_mdef
    static_sig Hwf HJ Hget_y Hval_y Hargs Hget_args Hrefine
    [Hrec_safe Hparams_safe] Hrcv_sub Harg_sub.
  intros pos T l Htype Hvalue Hkind Hmut.
  destruct pos as [|i].
  - (* receiver *)
    simpl in Htype. injection Htype as <-.
    simpl in Hvalue. injection Hvalue as <-.
    destruct Hkind as [Hkmut | Hkrdm].
    { exfalso. unfold is_nonmutable_qualifier in Hrec_safe.
      rewrite Hkmut in Hrec_safe.
      destruct Hrec_safe as [Hb | [Hb | [Hb | Hb]]]; discriminate. }
    have Hstatic_rdm : is_rdm_or_bot (sqtype (mreceiver static_sig)).
    { eapply method_signature_refinement_receiver_rdm_or_bot; eauto.
      left. exact Hkrdm. }
    have Hq := qualified_type_subtype_q_subtype _ _ _ Hrcv_sub.
    simpl in Hq.
    destruct Hstatic_rdm as [Hsr | Hsr]; rewrite Hsr in Hq.
    + (* static receiver RDM *)
      destruct (readonly_state_call_channel_inversion _ _ _
          (or_intror eq_refl) Hq) as
        [Hbot | [[Ht [_ Hqa]] | [_ Hqa]]].
      * exfalso.
        eapply wf_config_nonnull_variable_not_bot with (x := y); eauto.
      * exfalso.
        have Himm : r_muttype h ly = Some Imm_r.
        { eapply typed_imm_root_runtime_immutable_live; eauto.
          exists y, Ty. repeat split; assumption. }
        congruence.
      * eapply HJ with (x := y); eauto.
    + (* static receiver Bot *)
      exfalso.
      assert (Hybot : sqtype Ty = Bot).
      { destruct (sqtype Ty); simpl in Hq; inversion Hq; subst;
          congruence. }
      eapply wf_config_nonnull_variable_not_bot with (x := y); eauto.
  - (* parameter i *)
    simpl in Htype. unfold static_getType in Htype.
    simpl in Hvalue.
    destruct Hkind as [Hkmut | Hkrdm].
    { exfalso.
      have Hsafe : is_nonmutable_qualifier (sqtype T) :=
        Forall_nth_error _ _ _ _ Hparams_safe Htype.
      unfold is_nonmutable_qualifier in Hsafe.
      rewrite Hkmut in Hsafe.
      destruct Hsafe as [Hb | [Hb | [Hb | Hb]]]; discriminate. }
    (* static parameter exists and is RDM-or-Bot *)
    have Hlen := method_signature_refinement_params_length _ _ _ Hrefine.
    have Hi : i < length (mparams static_sig).
    { rewrite <- Hlen. apply nth_error_Some. rewrite Htype. discriminate. }
    have Hsp : exists P, nth_error (mparams static_sig) i = Some P.
    { destruct (nth_error (mparams static_sig) i) as [P|] eqn:HP.
      - exists P. reflexivity.
      - exfalso. apply nth_error_None in HP. lia. }
    destruct Hsp as [P HP].
    have Hstatic_rdm : is_rdm_or_bot (sqtype P).
    { eapply method_signature_refinement_parameter_rdm_or_bot; eauto.
      left. exact Hkrdm. }
    (* the argument variable *)
    destruct (runtime_lookup_list_nth_zs _ _ _ _ _ Hargs Hvalue) as
      [z [Hzi Hzval]].
    have Hlen_at : length argtypes = length (mparams static_sig).
    { have Hl := Forall2_length Harg_sub. exact Hl. }
    have Hat : exists A, nth_error argtypes i = Some A.
    { destruct (nth_error argtypes i) as [A|] eqn:HA.
      - exists A. reflexivity.
      - exfalso. apply nth_error_None in HA. lia. }
    destruct Hat as [A HA].
    have Hz_type : static_getType sGamma z = Some A.
    { eapply static_getType_list_index_strong; eauto. }
    have Hpair := Forall2_nth_error _ _ _ _ _ _ Harg_sub HA HP.
    have Hq := qualified_type_subtype_q_subtype _ _ _ Hpair. simpl in Hq.
    destruct Hstatic_rdm as [Hsr | Hsr]; rewrite Hsr in Hq.
    + destruct (readonly_state_call_channel_inversion _ _ _
          (or_intror eq_refl) Hq) as
        [Hbot | [[Ht [_ Hqa]] | [_ Hqa]]].
      * exfalso.
        eapply wf_config_nonnull_variable_not_bot with (x := z); eauto.
      * exfalso.
        have Himm : r_muttype h l = Some Imm_r.
        { eapply typed_imm_root_runtime_immutable_live; eauto.
          exists z, A. repeat split; assumption. }
        congruence.
      * eapply HJ with (x := z); eauto.
    + exfalso.
      assert (Hzbot : sqtype A = Bot).
      { destruct (sqtype Ty); simpl in Hq; inversion Hq; subst; congruence. }
      eapply wf_config_nonnull_variable_not_bot with (x := z); eauto.
Qed.

(** The return-slot channel: if the adapted static return fits a [Mut]/[RDM]
    destination, the receiver view and the static return are pinned. *)
Lemma readonly_state_return_channel_inversion :
  forall t m qx,
    (qx = Mut \/ qx = RDM) ->
    vpa_mutability_qq_readonly_state t m = qx ->
    (t = Mut /\ (m = Mut \/ m = RDM)) \/ (t = RDM /\ m = RDM).
Proof.
  intros t m qx Hkind Heq.
  destruct Hkind as [-> | ->]; destruct t; destruct m;
    simpl in Heq; try discriminate; auto.
Qed.

(** J after binding a call's return value.  Unchanged variables transport
    backwards through the body's heap extension; the destination slot routes
    through the nested frame's final J via the covariant return channel. *)
Lemma rs_mut_vars_fresh_call_return :
  forall CT h0 sGamma rGamma h h' x Tx y Ty ly retval
    runtime_mdef static_sig method_end rGamma'' body_return_type,
    wf_r_config CT sGamma rGamma h ->
    wf_r_config CT method_end rGamma'' h' ->
    rs_mut_vars_fresh h0 sGamma rGamma h ->
    rs_mut_vars_fresh h0 method_end rGamma'' h' ->
    (forall loc q, r_muttype h loc = Some q -> r_muttype h' loc = Some q) ->
    static_getType sGamma x = Some Tx ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    static_getType method_end (mreturn (mbody runtime_mdef))
      = Some body_return_type ->
    runtime_getVal rGamma'' (mreturn (mbody runtime_mdef)) = Some retval ->
    qualified_type_subtype CT body_return_type
      (mret (msignature runtime_mdef)) ->
    method_signature_refinement CT (msignature runtime_mdef) static_sig ->
    qualified_type_subtype CT
      (vpa_mutability_tt_readonly_state Ty (mret static_sig)) Tx ->
    rs_mut_vars_fresh h0 sGamma
      (update_r_env_value rGamma x retval) h'.
Proof.
  intros CT h0 sGamma rGamma h h' x Tx y Ty ly retval runtime_mdef
    static_sig method_end rGamma'' body_return_type
    Hcaller_wf Hcallee_wf HJ HJ'' Hpreserve Hget_x Hget_y Hval_y
    Hret_type Hretval Hbody_sub Hrefine Hret_sub.
  intros z T l Htype Hvalue Hkind Hmut.
  destruct (Nat.eq_dec z x) as [-> | Hneq].
  2:{ have Hxz : x <> z by congruence.
      have Hold := runtime_getVal_update_diff rGamma x z retval Hxz.
      rewrite Hold in Hvalue.
      have Hldom : l < dom h.
      { eapply wf_config_value_dom with (h := h); eauto. }
      destruct (r_muttype h l) as [q0|] eqn:Hq0.
      2:{ exfalso. unfold r_muttype in Hq0.
          destruct (runtime_getObj h l) as [o0|] eqn:Ho0;
            [discriminate|].
          apply nth_error_None in Ho0. lia. }
      have Hq0' := Hpreserve _ _ Hq0.
      assert (q0 = Mut_r) by congruence. subst q0.
      eapply HJ; eauto. }
  (* the destination slot *)
  assert (T = Tx) by congruence. subst T.
  have Hxdom : x < dom (vars rGamma).
  { have Hxs : x < length sGamma.
    { apply nth_error_Some. unfold static_getType in Hget_x.
      rewrite Hget_x. discriminate. }
    have Hlength := proj1 (proj2 (proj2 (proj2 (proj2 Hcaller_wf)))).
    lia. }
  have Hsame := runtime_getVal_update_same rGamma x retval Hxdom.
  rewrite Hsame in Hvalue. injection Hvalue as ->.
  have Hq := qualified_type_subtype_q_subtype _ _ _ Hret_sub. simpl in Hq.
  destruct (mutable_slot_subtype_inversion _ _ Hq Hkind) as [Heq | Hbot].
  2:{ (* adapted return is Bot *)
      exfalso.
      assert (Hcases : sqtype (mret static_sig) = Bot \/ sqtype Ty = Bot).
      { destruct (sqtype Ty); destruct (sqtype (mret static_sig));
          simpl in Hbot; try discriminate; auto. }
      destruct Hcases as [Hmb | Hyb].
      - have Hdynb := method_signature_refinement_return_bot _ _ _
          Hrefine Hmb.
        have Hbq := qualified_type_subtype_q_subtype _ _ _ Hbody_sub.
        rewrite Hdynb in Hbq.
        assert (Hbrb : sqtype body_return_type = Bot).
        { inversion Hbq; subst; congruence. }
        exact (wf_config_nonnull_variable_not_bot CT method_end rGamma'' h'
          (mreturn (mbody runtime_mdef)) body_return_type l
          Hcallee_wf Hret_type Hretval Hbrb).
      - exact (wf_config_nonnull_variable_not_bot CT sGamma rGamma h y Ty ly
          Hcaller_wf Hget_y Hval_y Hyb). }
  assert (Hm : sqtype (mret static_sig) = Mut \/
               sqtype (mret static_sig) = RDM).
  { destruct (readonly_state_return_channel_inversion _ _ _ Hkind Heq) as
      [[_ Hm] | [_ Hm]]; [exact Hm | right; exact Hm]. }
  have Hconc : is_concrete_or_rdm_or_bot (sqtype (mret static_sig)).
  { unfold is_concrete_or_rdm_or_bot.
    destruct Hm as [-> | ->]; auto. }
  have Hdyn := method_signature_refinement_return_concrete_or_rdm_or_bot
    _ _ _ Hrefine Hconc.
  have Hbq := qualified_type_subtype_q_subtype _ _ _ Hbody_sub.
  unfold is_concrete_or_rdm_or_bot in Hdyn.
  assert (Hbody_cases : sqtype body_return_type = Mut \/
      sqtype body_return_type = RDM \/
      sqtype body_return_type = Imm \/
      sqtype body_return_type = Bot).
  { destruct Hdyn as [Hd | [Hd | [Hd | Hd]]]; rewrite Hd in Hbq;
      inversion Hbq; subst; auto. }
  destruct Hbody_cases as [Hb | [Hb | [Hb | Hb]]].
  - eapply HJ'' with (x := mreturn (mbody runtime_mdef)); eauto.
  - eapply HJ'' with (x := mreturn (mbody runtime_mdef)); eauto.
  - exfalso.
    have Himm : r_muttype h' l = Some Imm_r.
    { eapply typed_imm_root_runtime_immutable_live; [exact Hcallee_wf|].
      exists (mreturn (mbody runtime_mdef)), body_return_type.
      repeat split; assumption. }
    congruence.
  - exfalso.
    exact (wf_config_nonnull_variable_not_bot CT method_end rGamma'' h'
      (mreturn (mbody runtime_mdef)) body_return_type l
      Hcallee_wf Hret_type Hretval Hb).
Qed.

(** ** The pool at a nested call entry, under the restored rule

    The plain branch routes every [Mut]/[RDM]-typed entry slot through the
    caller's pool, so the callee frame inherits the caller's side.  The
    special branch ([RO] receiver on a declared-[RDM] method) adapts every
    parameter channel through [RO], which collapses [RDM] to [Lost] and
    admits only [Bot] -- so the receiver is the frame's ONLY possible pool
    member, and the callee's side is whichever side the receiver's location
    is on, decided constructively. *)
Lemma rs_pool_sided_call_entry :
  forall CT h0 S side sGamma rGamma h y Ty ly args vals argtypes runtime_mdef
    static_sig,
    wf_r_config CT sGamma rGamma h ->
    rs_pool_sided h0 S side sGamma rGamma h ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    runtime_lookup_list rGamma args = Some vals ->
    static_getType_list sGamma args = Some argtypes ->
    method_signature_refinement CT (msignature runtime_mdef) static_sig ->
    signature_has_no_mutable_roots (msignature runtime_mdef) ->
    (qualified_type_subtype CT Ty
       (vpa_mutability_tt_readonly_state Ty (mreceiver static_sig)) \/
     (sqtype Ty = RO /\ sqtype (mreceiver static_sig) = RDM /\
      base_subtype CT (sctype Ty) (sctype (mreceiver static_sig)))) ->
    Forall2 (fun arg T => qualified_type_subtype CT arg
        (vpa_mutability_tt_readonly_state Ty T))
      argtypes (mparams static_sig) ->
    exists side',
      (side' = side \/ sqtype Ty = RO) /\
      rs_pool_sided h0 S side'
        (mreceiver (msignature runtime_mdef)
          :: mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals)) h.
Proof.
  intros CT h0 S side sGamma rGamma h y Ty ly args vals argtypes runtime_mdef
    static_sig Hwf Hpool Hget_y Hval_y Hargs Hget_args Hrefine
    [Hrec_safe Hparams_safe] Hrcv_sub Harg_sub.
  have Huse := proj1 (rs_pool_sided_spec _ _ _ _ _ _) Hpool.
  destruct Hrcv_sub as [Hrcv_sub | [Hro [Hstatic_rec_rdm _]]].
  - (* plain branch: the callee inherits the caller's side *)
    exists side. split; [left; reflexivity|].
    apply (proj2 (rs_pool_sided_spec _ _ _ _ _ _)).
    intros pos T l Htype Hvalue Hkind Hmut.
    destruct pos as [|i].
    + (* receiver *)
      simpl in Htype. injection Htype as <-.
      simpl in Hvalue. injection Hvalue as <-.
      destruct Hkind as [Hkmut | Hkrdm].
      { exfalso. unfold is_nonmutable_qualifier in Hrec_safe.
        rewrite Hkmut in Hrec_safe.
        destruct Hrec_safe as [Hb | [Hb | [Hb | Hb]]]; discriminate. }
      have Hstatic_rdm : is_rdm_or_bot (sqtype (mreceiver static_sig)).
      { eapply method_signature_refinement_receiver_rdm_or_bot; eauto.
        left. exact Hkrdm. }
      have Hq := qualified_type_subtype_q_subtype _ _ _ Hrcv_sub.
      simpl in Hq.
      destruct Hstatic_rdm as [Hsr | Hsr]; rewrite Hsr in Hq.
      * (* static receiver RDM *)
        destruct (readonly_state_call_channel_inversion _ _ _
            (or_intror eq_refl) Hq) as
          [Hbot | [[Ht [_ Hqa]] | [_ Hqa]]].
        { exfalso.
          eapply wf_config_nonnull_variable_not_bot with (x := y); eauto. }
        { exfalso.
          have Himm : r_muttype h ly = Some Imm_r.
          { eapply typed_imm_root_runtime_immutable_live; eauto.
            exists y, Ty. repeat split; assumption. }
          congruence. }
        { eapply Huse with (x := y) (T := Ty);
            [exact Hget_y | exact Hval_y | exact Hqa | exact Hmut]. }
      * (* static receiver Bot *)
        exfalso.
        assert (Hybot : sqtype Ty = Bot).
        { destruct (sqtype Ty); simpl in Hq; inversion Hq; subst;
            congruence. }
        eapply wf_config_nonnull_variable_not_bot with (x := y); eauto.
    + (* parameter i *)
      simpl in Htype. unfold static_getType in Htype.
      simpl in Hvalue.
      destruct Hkind as [Hkmut | Hkrdm].
      { exfalso.
        have Hsafe : is_nonmutable_qualifier (sqtype T) :=
          Forall_nth_error _ _ _ _ Hparams_safe Htype.
        unfold is_nonmutable_qualifier in Hsafe.
        rewrite Hkmut in Hsafe.
        destruct Hsafe as [Hb | [Hb | [Hb | Hb]]]; discriminate. }
      have Hlen := method_signature_refinement_params_length _ _ _ Hrefine.
      have Hi : i < length (mparams static_sig).
      { rewrite <- Hlen. apply nth_error_Some. rewrite Htype. discriminate. }
      have Hsp : exists P, nth_error (mparams static_sig) i = Some P.
      { destruct (nth_error (mparams static_sig) i) as [P|] eqn:HP.
        - exists P. reflexivity.
        - exfalso. apply nth_error_None in HP. lia. }
      destruct Hsp as [P HP].
      have Hstatic_rdm : is_rdm_or_bot (sqtype P).
      { eapply method_signature_refinement_parameter_rdm_or_bot; eauto.
        left. exact Hkrdm. }
      destruct (runtime_lookup_list_nth_zs _ _ _ _ _ Hargs Hvalue) as
        [z [Hzi Hzval]].
      have Hlen_at : length argtypes = length (mparams static_sig).
      { have Hl := Forall2_length Harg_sub. exact Hl. }
      have Hat : exists A, nth_error argtypes i = Some A.
      { destruct (nth_error argtypes i) as [A|] eqn:HA.
        - exists A. reflexivity.
        - exfalso. apply nth_error_None in HA. lia. }
      destruct Hat as [A HA].
      have Hz_type : static_getType sGamma z = Some A.
      { eapply static_getType_list_index_strong; eauto. }
      have Hpair := Forall2_nth_error _ _ _ _ _ _ Harg_sub HA HP.
      have Hq := qualified_type_subtype_q_subtype _ _ _ Hpair. simpl in Hq.
      destruct Hstatic_rdm as [Hsr | Hsr]; rewrite Hsr in Hq.
      * destruct (readonly_state_call_channel_inversion _ _ _
            (or_intror eq_refl) Hq) as
          [Hbot | [[Ht [_ Hqa]] | [_ Hqa]]].
        { exfalso.
          eapply wf_config_nonnull_variable_not_bot with (x := z); eauto. }
        { exfalso.
          have Himm : r_muttype h l = Some Imm_r.
          { eapply typed_imm_root_runtime_immutable_live; eauto.
            exists z, A. repeat split; assumption. }
          congruence. }
        { eapply Huse with (x := z) (T := A);
            [exact Hz_type | exact Hzval | exact Hqa | exact Hmut]. }
      * exfalso.
        assert (Hzbot : sqtype A = Bot).
        { destruct (sqtype Ty); simpl in Hq; inversion Hq; subst;
            congruence. }
        eapply wf_config_nonnull_variable_not_bot with (x := z); eauto.
  - (* special branch: RO receiver on a declared-RDM method *)
    assert (Hpool_special : forall sd, rs_side h0 S sd ly ->
        rs_pool_sided h0 S sd
          (mreceiver (msignature runtime_mdef)
            :: mparams (msignature runtime_mdef))
          (mkr_env (Iot ly :: vals)) h).
    { intros sd Hly_side.
      apply (proj2 (rs_pool_sided_spec _ _ _ _ _ _)).
      intros pos T l Htype Hvalue Hkind Hmut.
      destruct pos as [|i].
      - (* receiver: the only possible pool member, on the chosen side *)
        simpl in Htype. injection Htype as <-.
        simpl in Hvalue. injection Hvalue as <-.
        exact Hly_side.
      - (* parameters: the RO view collapses their channels to Lost/Bot *)
        exfalso.
        simpl in Htype. unfold static_getType in Htype.
        simpl in Hvalue.
        destruct Hkind as [Hkmut | Hkrdm].
        { have Hsafe : is_nonmutable_qualifier (sqtype T) :=
            Forall_nth_error _ _ _ _ Hparams_safe Htype.
          unfold is_nonmutable_qualifier in Hsafe.
          rewrite Hkmut in Hsafe.
          destruct Hsafe as [Hb | [Hb | [Hb | Hb]]]; discriminate. }
        have Hlen := method_signature_refinement_params_length _ _ _ Hrefine.
        have Hi : i < length (mparams static_sig).
        { rewrite <- Hlen. apply nth_error_Some. rewrite Htype.
          discriminate. }
        have Hsp : exists P, nth_error (mparams static_sig) i = Some P.
        { destruct (nth_error (mparams static_sig) i) as [P|] eqn:HP.
          - exists P. reflexivity.
          - exfalso. apply nth_error_None in HP. lia. }
        destruct Hsp as [P HP].
        have Hstatic_rdm : is_rdm_or_bot (sqtype P).
        { eapply method_signature_refinement_parameter_rdm_or_bot; eauto.
          left. exact Hkrdm. }
        destruct (runtime_lookup_list_nth_zs _ _ _ _ _ Hargs Hvalue) as
          [z [Hzi Hzval]].
        have Hlen_at : length argtypes = length (mparams static_sig).
        { have Hl := Forall2_length Harg_sub. exact Hl. }
        have Hat : exists A, nth_error argtypes i = Some A.
        { destruct (nth_error argtypes i) as [A|] eqn:HA.
          - exists A. reflexivity.
          - exfalso. apply nth_error_None in HA. lia. }
        destruct Hat as [A HA].
        have Hz_type : static_getType sGamma z = Some A.
        { eapply static_getType_list_index_strong; eauto. }
        have Hpair := Forall2_nth_error _ _ _ _ _ _ Harg_sub HA HP.
        have Hq := qualified_type_subtype_q_subtype _ _ _ Hpair.
        simpl in Hq.
        rewrite Hro in Hq.
        assert (Hzbot : sqtype A = Bot).
        { destruct Hstatic_rdm as [Hsr | Hsr]; rewrite Hsr in Hq;
            simpl in Hq.
          - eapply q_subtype_lost_inversion. exact Hq.
          - inversion Hq; subst; congruence. }
        eapply wf_config_nonnull_variable_not_bot with (x := z); eauto. }
    destruct (lt_dec ly (dom h0)) as [Hly_old | Hly_not_old].
    { exists false. split; [right; exact Hro|].
      apply Hpool_special. left. exact Hly_old. }
    destruct (in_dec Nat.eq_dec ly S) as [Hly_in | Hly_nin].
    { exists false. split; [right; exact Hro|].
      apply Hpool_special. right. exact Hly_in. }
    exists true. split; [right; exact Hro|].
    apply Hpool_special. split; [lia | exact Hly_nin].
Qed.

(** ** The pool after binding a call's return value

    Unchanged variables transport backwards through the body's heap
    extension and forwards through the stitch-set growth (their values are
    below the call heap, where the set only grew above).  The destination
    slot routes through the callee's final pool: the return channel pins
    the receiver type to [Mut]/[RDM] whenever the destination is
    [Mut]/[RDM], which refutes the cross-side special case ([Ty = RO]) and
    forces the callee's side to be the caller's. *)
Lemma rs_pool_sided_call_return :
  forall CT h0 S S' side side' sGamma rGamma h h' x Tx y Ty ly retval
    runtime_mdef static_sig method_end rGamma'' body_return_type,
    wf_r_config CT sGamma rGamma h ->
    wf_r_config CT method_end rGamma'' h' ->
    rs_pool_sided h0 S side sGamma rGamma h ->
    rs_pool_sided h0 S' side' method_end rGamma'' h' ->
    (forall l, List.In l S -> List.In l S') ->
    (forall l, List.In l S' -> List.In l S \/ dom h <= l) ->
    (side' = side \/ sqtype Ty = RO) ->
    (forall loc q, r_muttype h loc = Some q -> r_muttype h' loc = Some q) ->
    static_getType sGamma x = Some Tx ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    static_getType method_end (mreturn (mbody runtime_mdef))
      = Some body_return_type ->
    runtime_getVal rGamma'' (mreturn (mbody runtime_mdef)) = Some retval ->
    qualified_type_subtype CT body_return_type
      (mret (msignature runtime_mdef)) ->
    method_signature_refinement CT (msignature runtime_mdef) static_sig ->
    qualified_type_subtype CT
      (vpa_mutability_tt_readonly_state Ty (mret static_sig)) Tx ->
    rs_pool_sided h0 S' side sGamma
      (update_r_env_value rGamma x retval) h'.
Proof.
  intros CT h0 S S' side side' sGamma rGamma h h' x Tx y Ty ly retval
    runtime_mdef static_sig method_end rGamma'' body_return_type
    Hcaller_wf Hcallee_wf Hpool Hpool'' Hincl Hgrow Hside_case Hpreserve
    Hget_x Hget_y Hval_y Hret_type Hretval Hbody_sub Hrefine Hret_sub.
  have Huse := proj1 (rs_pool_sided_spec _ _ _ _ _ _) Hpool.
  have Huse'' := proj1 (rs_pool_sided_spec _ _ _ _ _ _) Hpool''.
  apply (proj2 (rs_pool_sided_spec _ _ _ _ _ _)).
  intros z T l Htype Hvalue Hkind Hmut.
  destruct (Nat.eq_dec z x) as [-> | Hneq].
  2:{ have Hxz : x <> z by congruence.
      have Hold := runtime_getVal_update_diff rGamma x z retval Hxz.
      rewrite Hold in Hvalue.
      have Hldom : l < dom h.
      { eapply wf_config_value_dom with (h := h); eauto. }
      destruct (r_muttype h l) as [q0|] eqn:Hq0.
      2:{ exfalso. unfold r_muttype in Hq0.
          destruct (runtime_getObj h l) as [o0|] eqn:Ho0;
            [discriminate|].
          apply nth_error_None in Ho0. lia. }
      have Hq0' := Hpreserve _ _ Hq0.
      assert (q0 = Mut_r) by congruence. subst q0.
      eapply rs_side_grow with (S := S) (h := h);
        [exact Hincl | exact Hgrow | exact Hldom |].
      eapply Huse; eauto. }
  (* the destination slot *)
  assert (T = Tx) by congruence. subst T.
  have Hxdom : x < dom (vars rGamma).
  { have Hxs : x < length sGamma.
    { apply nth_error_Some. unfold static_getType in Hget_x.
      rewrite Hget_x. discriminate. }
    have Hlength := proj1 (proj2 (proj2 (proj2 (proj2 Hcaller_wf)))).
    lia. }
  have Hsame := runtime_getVal_update_same rGamma x retval Hxdom.
  rewrite Hsame in Hvalue. injection Hvalue as ->.
  have Hq := qualified_type_subtype_q_subtype _ _ _ Hret_sub. simpl in Hq.
  destruct (mutable_slot_subtype_inversion _ _ Hq Hkind) as [Heq | Hbot].
  2:{ (* adapted return is Bot *)
      exfalso.
      assert (Hcases : sqtype (mret static_sig) = Bot \/ sqtype Ty = Bot).
      { destruct (sqtype Ty); destruct (sqtype (mret static_sig));
          simpl in Hbot; try discriminate; auto. }
      destruct Hcases as [Hmb | Hyb].
      - have Hdynb := method_signature_refinement_return_bot _ _ _
          Hrefine Hmb.
        have Hbq := qualified_type_subtype_q_subtype _ _ _ Hbody_sub.
        rewrite Hdynb in Hbq.
        assert (Hbrb : sqtype body_return_type = Bot).
        { inversion Hbq; subst; congruence. }
        exact (wf_config_nonnull_variable_not_bot CT method_end rGamma'' h'
          (mreturn (mbody runtime_mdef)) body_return_type l
          Hcallee_wf Hret_type Hretval Hbrb).
      - exact (wf_config_nonnull_variable_not_bot CT sGamma rGamma h y Ty ly
          Hcaller_wf Hget_y Hval_y Hyb). }
  (* the return channel pins the receiver and the static return *)
  assert (Hchan : (sqtype Ty = Mut \/ sqtype Ty = RDM) /\
      (sqtype (mret static_sig) = Mut \/ sqtype (mret static_sig) = RDM)).
  { destruct (readonly_state_return_channel_inversion _ _ _ Hkind Heq) as
      [[Hty Hm] | [Hty Hm]].
    - split; [left; exact Hty | exact Hm].
    - split; [right; exact Hty | right; exact Hm]. }
  destruct Hchan as [Hty_mr Hm].
  (* the cross-side special case is refuted *)
  have Hside_eq : side' = side.
  { destruct Hside_case as [Hs | Hro]; [exact Hs|].
    exfalso.
    destruct Hty_mr as [Hty | Hty]; rewrite Hro in Hty; discriminate. }
  subst side'.
  have Hconc : is_concrete_or_rdm_or_bot (sqtype (mret static_sig)).
  { unfold is_concrete_or_rdm_or_bot.
    destruct Hm as [-> | ->]; auto. }
  have Hdyn := method_signature_refinement_return_concrete_or_rdm_or_bot
    _ _ _ Hrefine Hconc.
  have Hbq := qualified_type_subtype_q_subtype _ _ _ Hbody_sub.
  unfold is_concrete_or_rdm_or_bot in Hdyn.
  assert (Hbody_cases : sqtype body_return_type = Mut \/
      sqtype body_return_type = RDM \/
      sqtype body_return_type = Imm \/
      sqtype body_return_type = Bot).
  { destruct Hdyn as [Hd | [Hd | [Hd | Hd]]]; rewrite Hd in Hbq;
      inversion Hbq; subst; auto. }
  destruct Hbody_cases as [Hb | [Hb | [Hb | Hb]]].
  - eapply Huse'' with (x := mreturn (mbody runtime_mdef))
      (T := body_return_type);
      [exact Hret_type | exact Hretval | left; exact Hb | exact Hmut].
  - eapply Huse'' with (x := mreturn (mbody runtime_mdef))
      (T := body_return_type);
      [exact Hret_type | exact Hretval | right; exact Hb | exact Hmut].
  - exfalso.
    have Himm : r_muttype h' l = Some Imm_r.
    { eapply typed_imm_root_runtime_immutable_live; [exact Hcallee_wf|].
      exists (mreturn (mbody runtime_mdef)), body_return_type.
      repeat split; assumption. }
    congruence.
  - exfalso.
    exact (wf_config_nonnull_variable_not_bot CT method_end rGamma'' h'
      (mreturn (mbody runtime_mdef)) body_return_type l
      Hcallee_wf Hret_type Hretval Hb).
Qed.

(** ** The master preservation induction

    The partition invariant survives any successful readonly-state
    statement, including nested calls -- special ones included.  The
    stitch set only ever grows, and only above the statement's entry
    heap; that growth clause is what transports a suspended caller's
    pool across a nested call (its values are below the entry heap). *)
Lemma rs_mutable_freshness_preserved :
  forall CT rGamma h statement rGamma' h',
    eval_stmt CT rGamma h statement OK rGamma' h' ->
    forall sGamma mt sGamma' h0 S side,
      stmt_typing CT sGamma mt statement sGamma' ->
      readonly_state_method_scope mt ->
      wf_r_config CT sGamma rGamma h ->
      dom h0 <= dom h ->
      rs_stitch_set_wf h0 h S ->
      rs_mut_edges_respect_sides CT h0 S h ->
      rs_pool_sided h0 S side sGamma rGamma h ->
      exists S',
        (forall l, List.In l S -> List.In l S') /\
        (forall l, List.In l S' -> List.In l S \/ dom h <= l) /\
        rs_stitch_set_wf h0 h' S' /\
        rs_mut_edges_respect_sides CT h0 S' h' /\
        rs_pool_sided h0 S' side sGamma' rGamma' h'.
Proof.
  intros CT rGamma h statement rGamma' h' Heval.
  have Heval_copy := Heval.
  dependent induction Heval;
    intros sGamma mt sGamma' h0 S side Htyping Hscope Hwf Hgrow Hstitch
      Hsides Hpool.
  - (* skip *)
    inversion Htyping; subst.
    exists S. split; [intros l Hin; exact Hin|].
    split; [intros l Hin; left; exact Hin|].
    split; [exact Hstitch|]. split; [exact Hsides|]. exact Hpool.
  - (* local *)
    inversion Htyping; subst.
    exists S. split; [intros l Hin; exact Hin|].
    split; [intros l Hin; left; exact Hin|].
    split; [exact Hstitch|]. split; [exact Hsides|].
    eapply rs_sides_after_local; [|exact Hpool].
    exact (proj1 (proj2 (proj2 (proj2 (proj2 Hwf))))).
  - (* var assignment *)
    inversion Htyping; subst.
    assert (Hupdate : set_vars rΓ (update x v2 (vars rΓ)) =
        update_r_env_value rΓ x v2).
    { destruct rΓ. reflexivity. }
    rewrite Hupdate.
    exists S. split; [intros l Hin; exact Hin|].
    split; [intros l Hin; left; exact Hin|].
    split; [exact Hstitch|]. split; [exact Hsides|].
    eapply rs_sides_after_assignment; eauto.
  - (* field write *)
    destruct (rs_sides_after_field_write CT h0 S side sGamma mt rΓ h x f y
      sGamma' rΓ h' Hwf Hscope Htyping Heval_copy Hstitch Hsides Hpool) as
      [Hstitch' [Hsides' Hpool']].
    exists S. split; [intros l Hin; exact Hin|].
    split; [intros l Hin; left; exact Hin|].
    split; [exact Hstitch'|]. split; [exact Hsides'|]. exact Hpool'.
  - (* new *)
    eapply rs_sides_after_new; eauto.
  - (* call *)
    destruct Hfind as [Hfind_method Hbody_definition].
    subst mbody mstmt mret. subst.
    destruct (safe_typed_call_static_result CT sGamma mt rΓ h x m y zs
      sGamma' ly cy mdef Hwf Htyping Hscope Hval_y Hbase Hfind_method)
      as [destination_type [receiver_type [static_mdef
        [HsGamma [Hx_nonzero [Hdestination_type [Hreceiver_type
          [Hfind_static [Hrefine [Hret_sub Hrcv_sub]]]]]]]]]].
    subst sGamma'.
    have Hcallee_scope := safe_typed_call_target_method_safe CT sGamma mt rΓ
      h x m y zs sGamma ly cy mdef Hwf Htyping Hscope Hval_y Hbase
      Hfind_method.
    destruct (typed_call_target CT sGamma mt rΓ h x m y zs sGamma vals ly
      cy mdef Hwf Htyping Hval_y Hbase Hfind_method Hargs) as
      [declaring_class [declaring_def [body_end
        [Hruntime_sub [Hdeclaring_class [Hmethod_member
          [Hmethod_wf [Hbody_typing Hcallee_initial_wf]]]]]]]].
    unfold wf_method in Hmethod_wf. simpl in Hmethod_wf.
    destruct Hmethod_wf as
      [_ [method_end [body_return_type
        [Hmethod_body_typing [Hreturn_dom
          [Hreturn_type [Hbody_sub Hoverriding]]]]]]].
    have Hsig_safe : signature_has_no_mutable_roots (msignature mdef).
    { exact ((proj2 (proj2 Hoverriding)) Hcallee_scope). }
    (* argument channel facts, from the typing rule directly *)
    assert (Hcall_args : exists argtypes,
        static_getType_list sGamma zs = Some argtypes /\
        Forall2 (fun arg T => qualified_type_subtype CT arg
            (vpa_mutability_tt_readonly_state receiver_type T))
          argtypes (mparams (msignature static_mdef))).
    { inversion Htyping; subst.
      - destruct Hscope as [Hbad | Hbad]; destruct Hscope0 as
          [Habs | [Hcs _]]; congruence.
      - assert (Ty = receiver_type) by congruence. subst Ty.
        assert (mdef0 = static_mdef).
        { eapply find_method_with_name_deterministic; eauto. }
        subst mdef0.
        exists argtypes. split; assumption. }
    destruct Hcall_args as [argtypes [Hget_args Harg_sub]].
    (* enter the callee: the pool lands on some side *)
    destruct (rs_pool_sided_call_entry CT h0 S side sGamma rΓ h y
      receiver_type ly zs vals argtypes mdef (msignature static_mdef)
      Hwf Hpool Hreceiver_type Hval_y Hargs Hget_args Hrefine Hsig_safe
      Hrcv_sub Harg_sub) as [side' [Hside'_case Hentry_pool]].
    (* run the body *)
    destruct (IHHeval eq_refl Heval
      (mreceiver (msignature mdef) :: mparams (msignature mdef))
      (mscope (msignature mdef)) method_end h0 S side'
      Hmethod_body_typing Hcallee_scope Hcallee_initial_wf Hgrow Hstitch
      Hsides Hentry_pool) as
      [S'' [Hincl'' [Hgrow'' [Hstitch'' [Hsides'' Hpool'']]]]].
    have Hcallee_final_wf := preservation_pico CT
      (mreceiver (msignature mdef) :: mparams (msignature mdef))
      (mscope (msignature mdef)) (mkr_env (Iot ly :: vals)) h
      (mbody_stmt (Syntax.mbody mdef)) rΓ'' h' method_end
      Hcallee_initial_wf Hmethod_body_typing Heval.
    assert (Hupdate : set_vars rΓ (update x retval (vars rΓ)) =
        update_r_env_value rΓ x retval).
    { destruct rΓ. reflexivity. }
    rewrite Hupdate.
    have Hpreserve : forall loc q, r_muttype h loc = Some q ->
        r_muttype h' loc = Some q.
    { intros loc q Hq.
      eapply eval_stmt_preserves_r_muttype; eauto.
      unfold r_muttype in Hq.
      destruct (runtime_getObj h loc) as [o0|] eqn:Ho0; [|discriminate].
      eapply runtime_getObj_dom. exact Ho0. }
    exists S''.
    split; [exact Hincl''|]. split; [exact Hgrow''|].
    split; [exact Hstitch''|]. split; [exact Hsides''|].
    eapply rs_pool_sided_call_return with
      (S := S) (side' := side') (y := y) (Ty := receiver_type) (ly := ly)
      (runtime_mdef := mdef) (static_sig := msignature static_mdef)
      (method_end := method_end) (rGamma'' := rΓ'')
      (body_return_type := body_return_type); eauto.
  - (* seq *)
    inversion Htyping; subst.
    have Hmid_wf := preservation_pico CT sGamma mt rΓ h s1 rΓ' h' sΓ'
      Hwf Htype1 Heval1.
    have Hg1 := eval_stmt_preserves_heap_domain_simple CT rΓ h s1 rΓ' h'
      Heval1.
    destruct (IHHeval1 eq_refl Heval1 sGamma mt sΓ' h0 S side Htype1 Hscope
      Hwf Hgrow Hstitch Hsides Hpool) as
      [S1 [Hincl1 [Hgrow1 [Hstitch1 [Hsides1 Hpool1]]]]].
    have Hmid_grow : dom h0 <= dom h' by lia.
    destruct (IHHeval2 eq_refl Heval2 sΓ' mt sGamma' h0 S1 side Htype2
      Hscope Hmid_wf Hmid_grow Hstitch1 Hsides1 Hpool1) as
      [S2 [Hincl2 [Hgrow2 [Hstitch2 [Hsides2 Hpool2]]]]].
    exists S2.
    split; [intros l Hin; apply Hincl2; apply Hincl1; exact Hin|].
    split.
    { intros l Hin.
      destruct (Hgrow2 l Hin) as [Hin1 | Hge]; [|right; lia].
      destruct (Hgrow1 l Hin1) as [HinS | Hge];
        [left; exact HinS | right; exact Hge]. }
    split; [exact Hstitch2|]. split; [exact Hsides2|]. exact Hpool2.
Qed.

(** Stack-shape auxiliaries for the per-edge lemma. *)
Lemma live_call_boundary_in :
  forall active stack callee bd,
    live_call_boundary active stack callee bd ->
    List.In bd stack.
Proof.
  intros active stack callee bd Hlive.
  induction Hlive; [left; reflexivity | right; exact IHHlive].
Qed.

Lemma live_call_boundary_callee_shape :
  forall active stack callee bd,
    live_call_boundary active stack callee bd ->
    callee = active \/
    exists b, List.In b stack /\ callee = b.(boundary_caller).
Proof.
  intros active stack callee bd Hlive.
  induction Hlive.
  - left. reflexivity.
  - right.
    destruct IHHlive as [-> | [b [Hin ->]]].
    + exists head. split; [left; reflexivity | reflexivity].
    + exists b. split; [right; exact Hin | reflexivity].
Qed.

(** ** The partitioned walk

    From a left-side runtime-mutable node, every potential-adjacent step
    lands on a left-side node (and stays runtime-mutable).  Heap edges in
    either orientation are absorbed by the partition's edge condition;
    active-frame joins are refuted by the right-side pool; stored-frame
    joins and return edges land on stored-frame values, which are old.  The
    head boundary contributes no return edge because its callee return
    qualifier is not RDM. *)
Lemma rs_potential_adjacent_from_old_mut_stays_left :
  forall CT h0 S h active boundary stack u v,
    rs_pool_right h0 S active.(frame_senv) active.(frame_renv) h ->
    rs_mut_edges_respect_sides CT h0 S h ->
    wf_heap CT h ->
    live_frames_wf CT h active (boundary :: stack) ->
    boundary.(boundary_callee_return_qualifier) <> RDM ->
    (forall b, List.In b (boundary :: stack) -> forall x l,
       runtime_getVal b.(boundary_caller).(frame_renv) x = Some (Iot l) ->
       l < dom h0) ->
    potential_adjacent CT h active (boundary :: stack) u v ->
    rs_left h0 S u -> r_muttype h u = Some Mut_r ->
    rs_left h0 S v /\ r_muttype h v = Some Mut_r.
Proof.
  intros CT h0 S h active boundary stack u v Hpool Hsides Hheap Hframes
    Hhead_not_rdm Hstack_old Hadj Hleft Hmut.
  have Hv_mut : r_muttype h v = Some Mut_r.
  { eapply potential_adjacent_preserves_runtime_mutability; eauto. }
  split; [|exact Hv_mut].
  destruct Hadj as [[Hforward | Hbackward] | [Hframe | Hreturn]].
  - (* forward retained edge out of u *)
    apply (proj1 (Hsides u v Hforward Hmut Hv_mut)). exact Hleft.
  - (* backward mutable edge from v into u *)
    apply (proj2 (Hsides v u (retained_edge_rdm CT h v u Hbackward) Hv_mut
      Hmut)).
    exact Hleft.
  - (* frame join *)
    destruct Hframe as [frame [Hmember [Hu_root Hv_root]]].
    inversion Hmember; subst.
    + (* the active frame: contradicts the right-side pool *)
      exfalso.
      destruct Hu_root as [xvar [T [Htype [Hvalue Hrdm]]]].
      destruct (Hpool xvar T u Htype Hvalue (or_intror Hrdm) Hmut) as
        [Hge Hnin].
      destruct Hleft as [Hlt | Hin]; [lia | exact (Hnin Hin)].
    + (* a stored caller frame *)
      destruct Hv_root as [xvar [T [Htype [Hvalue Hrdm]]]].
      left. eapply Hstack_old; eauto.
  - (* return edge *)
    destruct Hreturn as [callee' [boundary' [Hlive [Hview [Hretq Hrest]]]]].
    inversion Hlive; subst.
    { exfalso. exact (Hhead_not_rdm Hretq). }
    match goal with
    | Hdeep : live_call_boundary (boundary_caller boundary) stack
        callee' boundary' |- _ =>
        have Hbd_in' := live_call_boundary_in _ _ _ _ Hdeep;
        have Hshape := live_call_boundary_callee_shape _ _ _ _ Hdeep
    end.
    have Hcallee_old : forall x l,
        runtime_getVal callee'.(frame_renv) x = Some (Iot l) ->
        l < dom h0.
    { destruct Hshape as [-> | [b [Hb_in ->]]].
      - intros x l Hv. eapply Hstack_old with (b := boundary);
          [left; reflexivity | exact Hv].
      - intros x l Hv. eapply Hstack_old with (b := b);
          [right; exact Hb_in | exact Hv]. }
    destruct Hrest as [Hmutty [[Hu_root Hv_root] | [Hu_root Hv_root]]].
    + (* v is a root of boundary'.(boundary_caller) *)
      destruct Hv_root as [xvar [T [Htype [Hvalue Hrdm]]]].
      left. eapply Hstack_old with (b := boundary');
        [right; exact Hbd_in' | exact Hvalue].
    + (* v is a root of the deeper callee, itself a stored caller frame *)
      destruct Hv_root as [xvar [T [Htype [Hvalue Hrdm]]]].
      left. eapply Hcallee_old. exact Hvalue.
Qed.

(** The path form. *)
Lemma rs_potential_path_from_old_mut_stays_left :
  forall CT h0 S h active boundary stack u w,
    rs_pool_right h0 S active.(frame_senv) active.(frame_renv) h ->
    rs_mut_edges_respect_sides CT h0 S h ->
    wf_heap CT h ->
    live_frames_wf CT h active (boundary :: stack) ->
    boundary.(boundary_callee_return_qualifier) <> RDM ->
    (forall b, List.In b (boundary :: stack) -> forall x l,
       runtime_getVal b.(boundary_caller).(frame_renv) x = Some (Iot l) ->
       l < dom h0) ->
    potential_connected CT h active (boundary :: stack) u w ->
    rs_left h0 S u -> r_muttype h u = Some Mut_r ->
    rs_left h0 S w /\ r_muttype h w = Some Mut_r.
Proof.
  intros CT h0 S h active boundary stack u w Hpool Hsides Hheap Hframes
    Hhead Hstack_old Hconn.
  induction Hconn; intros Hleft Hmut.
  - eapply rs_potential_adjacent_from_old_mut_stays_left; eauto.
  - split; assumption.
  - destruct (IHHconn1 Hleft Hmut) as [Hmid_left Hmid_mut].
    exact (IHHconn2 Hmid_left Hmid_mut).
Qed.
