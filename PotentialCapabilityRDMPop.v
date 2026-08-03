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
  ExecutionConfinement MutableCapability AuthorityCapability
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
    qualified_type_subtype CT receiver_type
      (vpa_mutability_tt_readonly_state receiver_type
        (mreceiver (msignature static_mdef))) ->
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

(** Private state threaded by the call-pop induction.

    Only two components are needed.  [private_fresh_frozen_statement_state]
    already contains [principled_phased_authority_live_history_state] through
    [principled_frozen_authority_history_state], so the phased layer needs no
    separate thread; and [potential_live_history_state] is threaded by the
    public theorem's own induction.

    Keeping the state this small is what makes the call case work without
    proof irrelevance: the boundary is produced by the single frozen entry
    lemma, and the policy component is transported onto it by
    [private_frame_join_policies_valid_origins_transfer]. *)
Definition private_call_pop_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary)
  (incoming : Ensemble authority_flow_state)
  (snapshots : list frozen_caller_snapshot_slot)
  (policies : private_frame_join_policies) (h : heap) : Prop :=
  private_fresh_frozen_statement_state CT P Z cutoff active stack incoming
    snapshots h /\
  private_frame_join_policies_valid h policies stack.

(** The whole package is derived from the public invariant, so none of it
    becomes a premise of the public theorem. *)
Lemma potential_live_history_starts_private_call_pop_state :
  forall CT P Z cutoff active stack h,
    potential_live_history_state CT P Z cutoff active stack h ->
    private_call_pop_state CT P Z cutoff active stack
      (Empty_set authority_flow_state)
      (repeat None (length stack))
      (initial_private_frame_join_policies active stack) h.
Proof.
  intros CT P Z cutoff active stack h Hstate.
  split.
  { apply potential_live_history_starts_private_fresh_frozen_statement.
    exact Hstate. }
  eapply initial_private_frame_join_policies_valid.
  exact (proj1 (proj2 (proj1 Hstate))).
Qed.

Lemma private_call_pop_state_after_local :
  forall CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    policies T x sGamma',
    private_call_pop_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots
      policies h ->
    stmt_typing CT sGamma mt (SLocal T x) sGamma' ->
    runtime_getVal rGamma x = None ->
    private_call_pop_state CT P Z cutoff
      (mk_watched_frame authority sGamma'
        (set_vars rGamma (vars rGamma ++ [Null_a]))) stack incoming
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority sGamma'
          (set_vars rGamma (vars rGamma ++ [Null_a]))) snapshots)
      policies h.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    policies T x sGamma' [Hfrozen Hpolicies] Htyping Hnone.
  split; [eapply private_fresh_frozen_statement_after_local; eauto|].
  exact Hpolicies.
Qed.

Lemma private_call_pop_state_after_assignment :
  forall CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    policies x expression old value,
    private_call_pop_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots
      policies h ->
    stmt_typing CT sGamma mt (SVarAss x expression) sGamma ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma x = Some old ->
    eval_expr CT rGamma h expression value OK rGamma h ->
    private_call_pop_state CT P Z cutoff
      (mk_watched_frame authority sGamma
        (update_r_env_value rGamma x value)) stack incoming
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority sGamma
          (update_r_env_value rGamma x value)) snapshots)
      policies h.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    policies x expression old value [Hfrozen Hpolicies]
    Htyping Hscope Hx Heval.
  split; [eapply private_fresh_frozen_statement_after_assignment; eauto|].
  exact Hpolicies.
Qed.

Lemma private_call_pop_state_after_new :
  forall CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    policies x qc C args sGamma' rGamma' h',
    private_call_pop_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots
      policies h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    eval_stmt CT rGamma h (SNew x qc C args) OK rGamma' h' ->
    private_call_pop_state CT P Z cutoff
      (mk_watched_frame authority sGamma' rGamma') stack incoming
      (advance_frozen_caller_snapshots CT h'
        (mk_watched_frame authority sGamma' rGamma') snapshots)
      policies h'.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    policies x qc C args sGamma' rGamma' h' [Hfrozen Hpolicies]
    Htyping Heval.
  have Hgrowth := eval_stmt_preserves_heap_domain_simple CT rGamma h
    (SNew x qc C args) rGamma' h' Heval.
  split; [eapply private_fresh_frozen_statement_after_new; eauto|].
  eapply private_frame_join_policies_valid_heap_growth;
    [exact Hgrowth|exact Hpolicies].
Qed.

Lemma private_call_pop_state_after_field_write :
  forall CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    policies x field y sGamma' rGamma' h',
    private_call_pop_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots
      policies h ->
    stmt_typing CT sGamma mt (SFldWrite x field y) sGamma' ->
    readonly_state_method_scope mt ->
    eval_stmt CT rGamma h (SFldWrite x field y) OK rGamma' h' ->
    private_call_pop_state CT P Z cutoff
      (mk_watched_frame authority sGamma' rGamma') stack incoming
      (advance_frozen_caller_snapshots CT h'
        (mk_watched_frame authority sGamma' rGamma') snapshots)
      policies h'.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    policies x field y sGamma' rGamma' h' [Hfrozen Hpolicies]
    Htyping Hscope Heval.
  have Hgrowth := eval_stmt_preserves_heap_domain_simple CT rGamma h
    (SFldWrite x field y) rGamma' h' Heval.
  split; [eapply private_fresh_frozen_statement_after_field_write; eauto|].
  eapply private_frame_join_policies_valid_heap_growth;
    [exact Hgrowth|exact Hpolicies].
Qed.

(** The join policies do not depend on which [call_boundary_origins] proof a
    boundary carries: [private_frame_join_targets_before_boundary] projects
    only [boundary_entry_cutoff].  Conversion alone cannot see this because
    [Forall2] is indexed by the boundary list, but destructing and rebuilding
    it suffices.

    This is what lets the private layers be combined over a *single*
    boundary without proof irrelevance.  The boundary, and hence its origins
    proof, is taken from the one call-entry lemma that produces it; every
    other layer is transported onto that boundary.  The retired chain instead
    identified two origins proofs with [proof_irrelevance], which is why
    [private_statement_enter_call_channel_free] depends on
    [Classical_Prop.classic] and could never satisfy
    [check-public-assumptions.py]. *)
Lemma private_frame_join_policies_valid_origins_transfer :
  forall h policies caller esenv erenv view rv rq cq cf
    origins1 origins2 stack,
    private_frame_join_policies_valid h policies
      (build_watched_boundary caller esenv erenv view rv rq cq cf origins1
        :: stack) ->
    private_frame_join_policies_valid h policies
      (build_watched_boundary caller esenv erenv view rv rq cq cf origins2
        :: stack).
Proof.
  intros h policies caller esenv erenv view rv rq cq cf origins1 origins2
    stack [Hactive Hsuspended].
  split; [exact Hactive|].
  inversion Hsuspended as [|target targets bnd rest Hhead Htail Heq1 Heq2];
    subst.
  constructor; [exact Hhead|exact Htail].
Qed.

(** Per-statement active-colour reflection summaries, recovered from the
    retired [PotentialCapabilityStatement] development.  They are the
    payload the threading induction must carry alongside the private
    state, because call-pop safety is reached only through
    [executing_authority_call_pop_safe_from_old_colors_reflected_or_outside],
    whose reflection premise runs from caller entry to caller post. *)
Lemma assignment_old_colors_reflected :
  forall CT authority sGamma mt rGamma h incoming x expression old value,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SVarAss x expression) sGamma ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma x = Some old ->
    eval_expr CT rGamma h expression value OK rGamma h ->
    executing_authority_old_colors_reflected CT h
      (mk_watched_frame authority sGamma rGamma) incoming h
      (mk_watched_frame authority sGamma
        (update_r_env_value rGamma x value)) incoming.
Proof.
  intros CT authority sGamma mt rGamma h incoming x expression old value
    Hwf Htyping Hscope Hvalue Heval mode location Hmode Hcolor Hlocation.
  have Hdescend := rdm_roots_descend_after_assignment CT sGamma mt rGamma h
    x expression old value Hwf Htyping Hscope Hvalue Heval.
  eapply executing_authority_colors_after_active_descent_covered; eauto.
  intros owned Howned.
  apply frame_owned_location_iff_active_live.
  eapply assignment_live_reachability_is_old with
    (mt := mt) (x := x) (e := expression) (old := old) (value := value)
    (stack := []); eauto.
  apply frame_owned_location_iff_active_live. exact Howned.
Qed.

Lemma local_old_colors_reflected :
  forall CT authority sGamma mt rGamma h incoming T x sGamma',
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SLocal T x) sGamma' ->
    runtime_getVal rGamma x = None ->
    executing_authority_old_colors_reflected CT h
      (mk_watched_frame authority sGamma rGamma) incoming h
      (mk_watched_frame authority sGamma'
        (set_vars rGamma (vars rGamma ++ [Null_a]))) incoming.
Proof.
  intros CT authority sGamma mt rGamma h incoming T x sGamma' Hwf Htyping
    Hnone mode location Hmode Hcolor Hlocation.
  have Hdescend := rdm_roots_descend_after_local CT sGamma mt rGamma h T x
    sGamma' Hwf Htyping Hnone.
  eapply executing_authority_colors_after_active_descent_covered; eauto.
  intros owned Howned.
  apply frame_owned_location_iff_active_live.
  eapply local_live_reachability_is_old with (stack := []); eauto.
  apply frame_owned_location_iff_active_live. exact Howned.
Qed.

Lemma field_write_old_colors_reflected :
  forall CT authority sGamma mt rGamma h incoming x field y sGamma' rGamma'
    h',
    wf_r_config CT sGamma rGamma h ->
    authority_context_sound h rGamma authority ->
    authority_colors_runtime_mutable h incoming ->
    stmt_typing CT sGamma mt (SFldWrite x field y) sGamma' ->
    readonly_state_method_scope mt ->
    eval_stmt CT rGamma h (SFldWrite x field y) OK rGamma' h' ->
    executing_authority_old_colors_reflected CT h
      (mk_watched_frame authority sGamma rGamma) incoming h'
      (mk_watched_frame authority sGamma' rGamma') incoming.
Proof.
  intros CT authority sGamma mt rGamma h incoming x field y sGamma' rGamma'
    h' Hwf Hsound Hincoming Htyping Hscope Heval mode location Hmode Hcolor
    Hlocation.
  eapply executing_authority_colors_after_typed_field_write_covered; eauto.
  eapply executing_authority_colors_runtime_mutable; eauto.
Qed.

Lemma new_old_colors_reflected :
  forall CT authority sGamma mt rGamma h incoming x qc C args sGamma' rGamma'
    h',
    wf_r_config CT sGamma rGamma h ->
    wf_r_config CT sGamma' rGamma' h' ->
    authority_context_sound h rGamma authority ->
    authority_context_sound h' rGamma' authority ->
    authority_colors_runtime_mutable h incoming ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    eval_stmt CT rGamma h (SNew x qc C args) OK rGamma' h' ->
    executing_authority_old_colors_reflected CT h
      (mk_watched_frame authority sGamma rGamma) incoming h'
      (mk_watched_frame authority sGamma' rGamma') incoming.
Proof.
  intros CT authority sGamma mt rGamma h incoming x qc C args sGamma' rGamma'
    h' Hwf Hpost_wf Hsound Hpost_sound Hincoming Htyping Heval.
  inversion Heval; subst.
  assert (Hupdate :
      set_vars rGamma (update x (Iot (dom h)) (vars rGamma)) =
      update_r_env_value rGamma x (Iot (dom h))).
  { destruct rGamma. reflexivity. }
  rewrite Hupdate in Hpost_wf, Hpost_sound |- *.
  intros mode location Hmode Hcolor Hlocation.
  eapply executing_authority_colors_after_new_covered; eauto.
Qed.

(** Composition bridge for a call body.  The recursive summary first maps a
    final callee color to the callee-entry phase; safe-call entry coverage
    then maps that entry color to the suspended caller phase. *)
Lemma call_body_old_color_reflects_to_caller_entry :
  forall CT caller_h caller caller_incoming callee_entry callee_incoming
    final_h callee_final mode location,
    callee_incoming = executing_authority_color_set CT caller_h caller
      caller_incoming ->
    (forall entry_mode entry_location,
      authority_mode_dangerous entry_mode ->
      In authority_flow_state
        (executing_authority_color_set CT caller_h callee_entry
          callee_incoming) (entry_mode, entry_location) ->
      exists caller_mode,
        authority_mode_dangerous caller_mode /\
        In authority_flow_state
          (executing_authority_color_set CT caller_h caller caller_incoming)
          (caller_mode, entry_location)) ->
    executing_authority_old_colors_reflected CT caller_h callee_entry
      callee_incoming final_h callee_final callee_incoming ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT final_h callee_final callee_incoming)
      (mode, location) ->
    location < dom caller_h ->
    exists caller_mode,
      authority_mode_dangerous caller_mode /\
      In authority_flow_state
        (executing_authority_color_set CT caller_h caller caller_incoming)
        (caller_mode, location).
Proof.
  intros CT caller_h caller caller_incoming callee_entry callee_incoming
    final_h callee_final mode location Hincoming Hentry Hbody Hmode Hcolor
    Hold.
  destruct (Hbody mode location Hmode Hcolor Hold) as
    [entry_mode [Hentry_mode Hentry_color]].
  eapply Hentry; eauto.
Qed.

(** If the whole call summary reflects a resumed caller color to the
    pre-call caller, that representative is present in the completed callee:
    caller colors are precisely the callee incoming colors and incoming
    colors are seeds of the final callee closure. *)
Lemma call_old_reflection_supplies_completed_callee_color :
  forall CT caller_h caller caller_incoming final_h caller_post callee
    callee_incoming mode location,
    callee_incoming = executing_authority_color_set CT caller_h caller
      caller_incoming ->
    executing_authority_old_colors_reflected CT caller_h caller
      caller_incoming final_h caller_post caller_incoming ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT final_h caller_post caller_incoming)
      (mode, location) ->
    location < dom caller_h ->
    exists callee_mode,
      authority_mode_dangerous callee_mode /\
      In authority_flow_state
        (executing_authority_color_set CT final_h callee callee_incoming)
        (callee_mode, location).
Proof.
  intros CT caller_h caller caller_incoming final_h caller_post callee
    callee_incoming mode location Hincoming Hreflect Hmode Hcolor Hold.
  destruct (Hreflect mode location Hmode Hcolor Hold) as
    [caller_mode [Hcaller_mode Hcaller_color]].
  exists caller_mode. split; [exact Hcaller_mode|].
  apply executing_authority_color_set_contains_incoming.
  rewrite Hincoming. exact Hcaller_color.
Qed.

(** Well-formedness of the executing frame, projected out of the threaded
    state.  Used by the per-statement reflection lemmas. *)
Lemma private_call_pop_state_wf :
  forall CT P Z cutoff active stack incoming snapshots policies h,
    private_call_pop_state CT P Z cutoff active stack incoming snapshots
      policies h ->
    wf_r_config CT active.(frame_senv) active.(frame_renv) h.
Proof.
  intros CT P Z cutoff active stack incoming snapshots policies h [Hfrozen _].
  exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2
    (proj1 (proj1 (proj1 Hfrozen))))))))).
Qed.

Lemma private_call_pop_state_sound :
  forall CT P Z cutoff active stack incoming snapshots policies h,
    private_call_pop_state CT P Z cutoff active stack incoming snapshots
      policies h ->
    authority_context_sound h active.(frame_renv) active.(frame_authority).
Proof.
  intros CT P Z cutoff active stack incoming snapshots policies h [Hfrozen _].
  exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2
    (proj1 (proj1 (proj1 Hfrozen)))))))))).
Qed.

Lemma private_call_pop_state_incoming_runtime_mutable :
  forall CT P Z cutoff active stack incoming snapshots policies h,
    private_call_pop_state CT P Z cutoff active stack incoming snapshots
      policies h ->
    authority_colors_runtime_mutable h incoming.
Proof.
  intros CT P Z cutoff active stack incoming snapshots policies h [Hfrozen _].
  exact (proj1 (proj2 (proj2 (proj1 (proj1 (proj1 Hfrozen)))))).
Qed.

(** The call case of the threading induction, isolated as a contract exactly
    as the retired development isolated
    [private_advancing_policy_successful_call_rule].  Both the contract and
    the induction carry the active-colour reflection summary alongside the
    private state, because call-pop safety is reached only through
    [executing_authority_call_pop_safe_from_old_colors_reflected_or_outside]
    and its reflection premise cannot come from the post-state's own
    separation. *)
Definition private_call_pop_call_rule : Prop :=
  forall CT P Z cutoff rGamma h x m y zs vals ly cy mdef retval h' rGamma''
    sGamma mt sGamma' authority stack incoming snapshots policies,
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m mdef ->
    runtime_lookup_list rGamma zs = Some vals ->
    eval_stmt CT (mkr_env (Iot ly :: vals)) h
      (mbody_stmt (mbody mdef)) OK rGamma'' h' ->
    runtime_getVal rGamma'' (mreturn (mbody mdef)) = Some retval ->
    (forall entry_senv entry_scope final_senv callee_authority callee_stack
       callee_incoming callee_snapshots callee_policies,
       private_call_pop_state CT P Z cutoff
         (mk_watched_frame callee_authority entry_senv
           (mkr_env (Iot ly :: vals)))
         callee_stack callee_incoming callee_snapshots callee_policies h ->
       stmt_typing CT entry_senv entry_scope
         (mbody_stmt (mbody mdef)) final_senv ->
       readonly_state_method_scope entry_scope ->
       exists final_snapshots,
         private_call_pop_state CT P Z cutoff
           (mk_watched_frame callee_authority final_senv rGamma'')
           callee_stack callee_incoming final_snapshots callee_policies h' /\
         executing_authority_old_colors_reflected_or_outside CT Z h
           (mk_watched_frame callee_authority entry_senv
             (mkr_env (Iot ly :: vals))) callee_incoming h'
           (mk_watched_frame callee_authority final_senv rGamma'')
           callee_incoming) ->
    private_call_pop_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots
      policies h ->
    stmt_typing CT sGamma mt (SCall x m y zs) sGamma' ->
    readonly_state_method_scope mt ->
    exists final_snapshots,
      private_call_pop_state CT P Z cutoff
        (mk_watched_frame authority sGamma'
          (set_vars rGamma (update x retval (vars rGamma))))
        stack incoming final_snapshots policies h' /\
      executing_authority_old_colors_reflected_or_outside CT Z h
        (mk_watched_frame authority sGamma rGamma) incoming h'
        (mk_watched_frame authority sGamma'
          (set_vars rGamma (update x retval (vars rGamma)))) incoming.

Lemma private_call_pop_state_preserved_from_call_rule :
  private_call_pop_call_rule ->
  forall CT P Z cutoff rGamma h statement rGamma' h',
    eval_stmt CT rGamma h statement OK rGamma' h' ->
    forall sGamma mt sGamma' authority stack incoming snapshots policies,
      private_call_pop_state CT P Z cutoff
        (mk_watched_frame authority sGamma rGamma) stack incoming snapshots
        policies h ->
      stmt_typing CT sGamma mt statement sGamma' ->
      readonly_state_method_scope mt ->
      exists final_snapshots,
        private_call_pop_state CT P Z cutoff
          (mk_watched_frame authority sGamma' rGamma') stack incoming
          final_snapshots policies h' /\
        executing_authority_old_colors_reflected_or_outside CT Z h
          (mk_watched_frame authority sGamma rGamma) incoming h'
          (mk_watched_frame authority sGamma' rGamma') incoming.
Proof.
  intros Hrule CT P Z cutoff rGamma h statement rGamma' h' Heval.
  have Heval_copy := Heval.
  dependent induction Heval;
    intros sGamma mt sGamma' authority stack incoming snapshots policies
      Hstate Htyping Hscope.
  - inversion Htyping; subst. exists snapshots. split; [exact Hstate|].
    apply executing_authority_old_colors_reflected_or_outside_refl.
  - have Hwf := private_call_pop_state_wf _ _ _ _ _ _ _ _ _ _ Hstate.
    have Hsound := private_call_pop_state_sound _ _ _ _ _ _ _ _ _ _ Hstate.
    have Hmutable :=
      private_call_pop_state_incoming_runtime_mutable
        _ _ _ _ _ _ _ _ _ _ Hstate.
    simpl in Hwf, Hsound.
    eexists. split; [eapply private_call_pop_state_after_local; eauto|].
    apply executing_authority_old_colors_reflected_implies_or_outside.
    eapply local_old_colors_reflected; eauto.
  - have Hwf := private_call_pop_state_wf _ _ _ _ _ _ _ _ _ _ Hstate.
    have Hsound := private_call_pop_state_sound _ _ _ _ _ _ _ _ _ _ Hstate.
    have Hmutable :=
      private_call_pop_state_incoming_runtime_mutable
        _ _ _ _ _ _ _ _ _ _ Hstate.
    simpl in Hwf, Hsound.
    inversion Htyping; subst.
    assert (Hupdate : set_vars rΓ (update x v2 (vars rΓ)) =
        update_r_env_value rΓ x v2).
    { destruct rΓ. reflexivity. }
    rewrite Hupdate.
    eexists. split.
    + eapply private_call_pop_state_after_assignment; eauto.
    + apply executing_authority_old_colors_reflected_implies_or_outside.
      eapply assignment_old_colors_reflected; eauto.
  - have Hwf := private_call_pop_state_wf _ _ _ _ _ _ _ _ _ _ Hstate.
    have Hsound := private_call_pop_state_sound _ _ _ _ _ _ _ _ _ _ Hstate.
    have Hmutable :=
      private_call_pop_state_incoming_runtime_mutable
        _ _ _ _ _ _ _ _ _ _ Hstate.
    simpl in Hwf, Hsound.
    eexists. split; [eapply private_call_pop_state_after_field_write; eauto|].
    apply executing_authority_old_colors_reflected_implies_or_outside.
    eapply field_write_old_colors_reflected; eauto.
  - have Hwf := private_call_pop_state_wf _ _ _ _ _ _ _ _ _ _ Hstate.
    have Hsound := private_call_pop_state_sound _ _ _ _ _ _ _ _ _ _ Hstate.
    have Hmutable :=
      private_call_pop_state_incoming_runtime_mutable
        _ _ _ _ _ _ _ _ _ _ Hstate.
    simpl in Hwf, Hsound.
    assert (Hpost : private_call_pop_state CT P Z cutoff
        (mk_watched_frame authority sGamma' rΓ') stack incoming
        (advance_frozen_caller_snapshots CT h'
          (mk_watched_frame authority sGamma' rΓ') snapshots)
        policies h').
    { eapply private_call_pop_state_after_new; eauto. }
    have Hpost_wf := private_call_pop_state_wf _ _ _ _ _ _ _ _ _ _ Hpost.
    have Hpost_sound :=
      private_call_pop_state_sound _ _ _ _ _ _ _ _ _ _ Hpost.
    simpl in Hpost_wf, Hpost_sound.
    eexists. split; [exact Hpost|].
    apply executing_authority_old_colors_reflected_implies_or_outside.
    eapply new_old_colors_reflected; eauto.
  - destruct Hfind as [Hfind_method Hbody_definition].
    subst mbody mstmt mret. subst.
    eapply Hrule; eauto.
  - inversion Htyping; subst.
    destruct (IHHeval1 eq_refl Heval1 sGamma mt sΓ' authority stack
      incoming snapshots policies Hstate Htype1 Hscope)
      as [middle [Hmiddle Hrefl1]].
    destruct (IHHeval2 eq_refl Heval2 sΓ' mt sGamma' authority stack
      incoming middle policies Hmiddle Htype2 Hscope)
      as [final [Hfinal Hrefl2]].
    exists final. split; [exact Hfinal|].
    eapply executing_authority_old_colors_reflected_or_outside_trans;
      [|exact Hrefl1|exact Hrefl2].
    eapply eval_stmt_preserves_heap_domain_simple. exact Heval1.
Qed.

