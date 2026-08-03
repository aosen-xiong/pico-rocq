Require Import Syntax Helpers Typing Bigstep MutableCapability WatchedFrames
  ProtectionHistory ForwardCapabilityHistory PotentialCapabilityCore.
Require Export PotentialCapabilityResume.
From Stdlib Require Import Sets.Ensembles.

(** Immutable resumed-frame pop under the persistent target policy.

    The substantive proof is the private, height-indexed classifier
    [tracked_overlap_post_update_call_pop_safe].  It classifies each
    dangerous resumed color from its lossless derivation.  A harmless overlap
    at the returned object is discharged by the proof-local resume-origin
    certificate; otherwise the classifier peels a strictly smaller join
    predecessor.  No allocation-age or reverse-connectivity premise is used.

    The classifier proves the unrestricted phased pop obligation.  A
    persistent target policy only removes frame-join edges, so the restricted
    resumed obligation follows by inclusion. *)
Lemma immutable_policy_resumed_call_pop_safe :
  forall CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination destination_type
    return_location caller_incoming eligible,
    let caller_post := mk_watched_frame
      boundary.(boundary_caller).(frame_authority) caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) in
    boundary.(boundary_caller).(frame_authority) = Imm_r ->
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some snapshot :: snapshots) h ->
    frozen_caller_snapshots_active_overlap_justified CT h Z active
      (Some snapshot :: snapshots) ->
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
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state caller_incoming (mode, location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (mode, location)) ->
    (forall location,
      frame_owned_location CT h caller_post location ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, location)) ->
    (forall anchor,
      frame_owned_location CT h caller_post anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, anchor) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (FlowPowered, anchor)) ->
    frame_owned_location CT h active return_location ->
    (exists return_mode,
      authority_mode_dangerous return_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (return_mode, return_location)) ->
    executing_resumed_authority_call_pop_safe CT h Z active active_incoming
      eligible caller_post caller_incoming.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination destination_type
    return_location caller_incoming eligible caller_post Hauthority Hfull
    Hoverlap Hcaller_wf Hcaller_post_wf Hdestination Hroots Hincoming
    Hcaller_incoming Howned Howned_snapshot Hreturn_owned Hreturn_color.
  eapply executing_authority_call_pop_safe_implies_resumed.
  eapply tracked_overlap_post_update_call_pop_safe; eauto.
Qed.
