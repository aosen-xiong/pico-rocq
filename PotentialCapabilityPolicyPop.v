Require Import Syntax Notations Helpers Typing Subtyping Bigstep.
Require Import ViewpointAdaptation Properties Preservation ReadonlyHelper.
Require Import Reachability MutableCapability ComponentColoring.
Require Import ExecutionConfinement ProtectionHistory ForwardCapabilityHistory.
Require Import AuthorityCapability AuthorityHistory WatchedFrames
  LiveCapabilityStack.
Require Export PotentialCapabilityStatement.

From Stdlib Require Import List Sets.Ensembles Relations.Relation_Operators
  Program.Equality.
Import ListNotations.

Lemma capability_in_context_dec :
  forall authority qualifier,
    {capability_in_context authority qualifier} +
    {~ capability_in_context authority qualifier}.
Proof.
  intros authority qualifier. unfold capability_in_context.
  destruct authority, qualifier; simpl; intuition congruence.
Qed.

(** Proof-local return lemmas for the policy-only witness stack.  This file
    is intentionally separate from statement preservation and call
    reconstruction: the pop classifier is recursive and recompiling it must
    not force recompilation of the statement induction. *)

(** Updating a caller variable whose declared qualifier carries no authority
    cannot introduce a new capability root.  This is the non-null analogue
    of [caller_null_post_capability_root_is_old]. *)
Lemma caller_noncap_post_capability_root_is_old :
  forall caller_authority caller_senv caller_renv destination
    destination_type value root,
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    ~ capability_in_context caller_authority (sqtype destination_type) ->
    frame_capability_root
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination value)) root ->
    frame_capability_root
      (mk_watched_frame caller_authority caller_senv caller_renv) root.
Proof.
  intros caller_authority caller_senv caller_renv destination
    destination_type value root Hdestination_nonzero Hdestination Hlength
    Hnoncap [variable [T [Htype [Hvalue Hcapability]]]].
  destruct (Nat.eq_dec variable destination) as [Heq | Hneq].
  - subst variable. rewrite Hdestination in Htype. injection Htype as <-.
    contradiction.
  - exists variable, T. split; [exact Htype|]. split.
    + have Hold_value := runtime_getVal_update_diff caller_renv destination
        variable value (ltac:(congruence)).
      rewrite Hvalue in Hold_value. symmetry. exact Hold_value.
    + exact Hcapability.
Qed.

(** A non-RDM destination cannot introduce a new RDM join root. *)
Lemma caller_nonrdm_post_rdm_root_is_old :
  forall caller_senv caller_renv destination destination_type value root,
    static_getType caller_senv destination = Some destination_type ->
    sqtype destination_type <> RDM ->
    typed_root RDM caller_senv
      (update_r_env_value caller_renv destination value) root ->
    typed_root RDM caller_senv caller_renv root.
Proof.
  intros caller_senv caller_renv destination destination_type value root
    Hdestination Hnonrdm
    [variable [T [Htype [Hvalue Hrdm]]]].
  destruct (Nat.eq_dec variable destination) as [Heq | Hneq].
  - subst variable. rewrite Hdestination in Htype. injection Htype as <-.
    contradiction.
  - exists variable, T. split; [exact Htype|]. split.
    + have Hold_value := runtime_getVal_update_diff caller_renv destination
        variable value (ltac:(congruence)).
      rewrite Hvalue in Hold_value. symmetry. exact Hold_value.
    + exact Hrdm.
Qed.

Lemma caller_noncap_nonrdm_post_rdm_roots_descend :
  forall CT h caller_senv caller_renv destination destination_type value,
    static_getType caller_senv destination = Some destination_type ->
    sqtype destination_type <> RDM ->
    rdm_roots_descend_from CT h caller_senv caller_renv caller_senv
      (update_r_env_value caller_renv destination value).
Proof.
  intros CT h caller_senv caller_renv destination destination_type value
    Hdestination Hnonrdm root Hroot.
  exists root. split.
  - eapply caller_nonrdm_post_rdm_root_is_old; eauto.
  - constructor.
Qed.

Lemma caller_noncap_post_owned_is_old :
  forall CT h caller_authority caller_senv caller_renv destination
    destination_type value,
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    ~ capability_in_context caller_authority (sqtype destination_type) ->
    Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination value)))
      (phase_frame_capability_set CT h
        (mk_watched_frame caller_authority caller_senv caller_renv)).
Proof.
  intros CT h caller_authority caller_senv caller_renv destination
    destination_type value Hdestination_nonzero Hdestination Hlength Hnoncap
    location [root [Hroot Hreachable]].
  exists root. split; [|exact Hreachable].
  eapply caller_noncap_post_capability_root_is_old; eauto.
Qed.

(** Plain non-capability/non-RDM updates are an active-frame descent: both
    the capability roots and the RDM roots of the resumed frame come from the
    suspended caller. *)
Lemma frozen_callee_side_prospective_components_after_noncap_nonrdm_pop :
  forall CT h active boundary stack head snapshots caller_authority
    caller_senv caller_renv destination destination_type value,
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT caller_senv caller_renv h ->
    authority_context_sound h caller_renv caller_authority ->
    static_getType caller_senv destination = Some destination_type ->
    sqtype destination_type <> RDM ->
    ~ capability_in_context caller_authority (sqtype destination_type) ->
    frozen_callee_side_prospective_components_after_boundaries CT h active
      (head :: snapshots) (boundary :: stack) ->
    let caller_post := mk_watched_frame caller_authority caller_senv
      (update_r_env_value caller_renv destination value) in
    frozen_callee_side_prospective_components_after_boundaries CT h
      caller_post
      (advance_frozen_caller_snapshots CT h caller_post snapshots) stack.
Proof.
  intros CT h active boundary stack head snapshots caller_authority
    caller_senv caller_renv destination destination_type value Hcaller
    Hdestination_nonzero Hcaller_wf Hcaller_sound Hdestination Hnonrdm Hnoncap
    Hold caller_post snapshot tracked_boundary above below Hpartition.
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
      (active := active) (boundary := boundary); eauto. }
  have Hlength : length caller_senv = length caller_renv.(vars) :=
    proj1 (proj2 (proj2 (proj2 (proj2 Hcaller_wf)))).
  unfold caller_post.
  eapply live_prospective_mutable_authority_components_after_active_descent.
  - exact Hcaller_wf.
  - exact Hcaller_sound.
  - eapply caller_noncap_nonrdm_post_rdm_roots_descend; eauto.
  - eapply caller_noncap_post_owned_is_old; eauto.
  - exact Hcaller_components.
Qed.

Lemma live_mutable_authority_components_after_noncap_nonrdm_pop :
  forall CT h cutoff active boundary stack caller_authority caller_senv
    caller_renv destination destination_type value,
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT caller_senv caller_renv h ->
    static_getType caller_senv destination = Some destination_type ->
    sqtype destination_type <> RDM ->
    ~ capability_in_context caller_authority (sqtype destination_type) ->
    live_mutable_authority_components_after_cutoff CT h cutoff active
      (boundary :: stack) ->
    live_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination value)) stack.
Proof.
  intros CT h cutoff active boundary stack caller_authority caller_senv
    caller_renv destination destination_type value Hcaller
    Hdestination_nonzero Hcaller_wf Hdestination Hnonrdm Hnoncap Hold frame
    root target Hlive Hreachable.
  have Hlength : length caller_senv = length caller_renv.(vars) :=
    proj1 (proj2 (proj2 (proj2 (proj2 Hcaller_wf)))).
  inversion Hlive; subst.
  - inversion Hreachable; subst.
    + eapply Hold with (frame := boundary.(boundary_caller)) (root := root).
      * constructor. simpl. left. reflexivity.
      * apply mutable_authority_reachable_capability.
        -- rewrite Hcaller. eapply caller_noncap_post_capability_root_is_old;
             eauto.
        -- exact H0.
        -- exact H1.
    + eapply Hold with (frame := boundary.(boundary_caller)) (root := root).
      * constructor. simpl. left. reflexivity.
      * apply mutable_authority_reachable_rdm.
        -- rewrite Hcaller. eapply caller_nonrdm_post_rdm_root_is_old; eauto.
        -- exact H0.
        -- exact H1.
  - eapply Hold with (frame := boundary0.(boundary_caller)) (root := root).
    + constructor. simpl. right. exact H.
    + exact Hreachable.
Qed.

Lemma frozen_callee_side_components_after_noncap_nonrdm_pop :
  forall CT h active boundary stack head snapshots caller_authority
    caller_senv caller_renv destination destination_type value,
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT caller_senv caller_renv h ->
    static_getType caller_senv destination = Some destination_type ->
    sqtype destination_type <> RDM ->
    ~ capability_in_context caller_authority (sqtype destination_type) ->
    frozen_callee_side_mutable_components_after_boundaries CT h active
      (head :: snapshots) (boundary :: stack) ->
    let caller_post := mk_watched_frame caller_authority caller_senv
      (update_r_env_value caller_renv destination value) in
    frozen_callee_side_mutable_components_after_boundaries CT h caller_post
      (advance_frozen_caller_snapshots CT h caller_post snapshots) stack.
Proof.
  intros CT h active boundary stack head snapshots caller_authority
    caller_senv caller_renv destination destination_type value Hcaller
    Hdestination_nonzero Hcaller_wf Hdestination Hnonrdm Hnoncap Hold
    caller_post snapshot tracked_boundary above below Hpartition.
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
  eapply live_mutable_authority_components_after_noncap_nonrdm_pop; eauto.
Qed.

Lemma private_fresh_return_partitions_after_noncap_nonrdm_pop :
  forall CT P Z cutoff active boundary stack incoming head snapshots h
    caller_authority caller_senv caller_renv destination destination_type value,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (head :: snapshots) h ->
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT caller_senv caller_renv h ->
    authority_context_sound h caller_renv caller_authority ->
    static_getType caller_senv destination = Some destination_type ->
    sqtype destination_type <> RDM ->
    ~ capability_in_context caller_authority (sqtype destination_type) ->
    let caller_post := mk_watched_frame caller_authority caller_senv
      (update_r_env_value caller_renv destination value) in
    let tail_snapshots := advance_frozen_caller_snapshots CT h caller_post
      snapshots in
    frozen_callee_side_mutable_components_after_boundaries CT h caller_post
      tail_snapshots stack /\
    frozen_callee_side_prospective_components_after_boundaries CT h
      caller_post tail_snapshots stack /\
    frozen_snapshot_boundaries_after_cutoff cutoff tail_snapshots stack.
Proof.
  intros CT P Z cutoff active boundary stack incoming head snapshots h
    caller_authority caller_senv caller_renv destination destination_type value
    [Hprivate [Hcomponents [Hprospective Hafter]]] Hcaller
    Hdestination_nonzero Hcaller_wf Hcaller_sound Hdestination Hnonrdm Hnoncap
    caller_post tail_snapshots.
  split.
  - unfold caller_post, tail_snapshots.
    eapply frozen_callee_side_components_after_noncap_nonrdm_pop; eauto.
  - split.
    + unfold caller_post, tail_snapshots.
      eapply frozen_callee_side_prospective_components_after_noncap_nonrdm_pop;
        eauto.
    + unfold tail_snapshots.
      eapply advance_snapshot_boundaries_after_cutoff.
      eapply snapshot_boundaries_after_cutoff_tail. exact Hafter.
Qed.

Lemma private_fresh_frozen_statement_after_noncap_nonrdm_return_parts :
  forall CT P Z cutoff active boundary stack active_incoming head snapshots h
    caller_incoming caller_authority caller_senv caller_renv destination
    destination_type value,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) active_incoming (head :: snapshots) h ->
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination value))
      stack caller_incoming h ->
    private_frozen_snapshot_return_safety CT h Z
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination value)) caller_incoming
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination value)) snapshots) ->
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT caller_senv caller_renv h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination value) h ->
    authority_context_sound h caller_renv caller_authority ->
    static_getType caller_senv destination = Some destination_type ->
    sqtype destination_type <> RDM ->
    ~ capability_in_context caller_authority (sqtype destination_type) ->
    private_fresh_frozen_statement_state CT P Z cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination value))
      stack caller_incoming
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination value)) snapshots) h.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming head snapshots h
    caller_incoming caller_authority caller_senv caller_renv destination
    destination_type value Hbody Hpost Hreturn_safety Hcaller
    Hdestination_nonzero Hcaller_wf Hcaller_post_wf Hcaller_sound Hdestination
    Hnonrdm Hnoncap.
  set (caller_post := mk_watched_frame caller_authority caller_senv
    (update_r_env_value caller_renv destination value)).
  set (tail_snapshots := advance_frozen_caller_snapshots CT h caller_post
    snapshots).
  have Hbody_private := proj1 Hbody.
  destruct (private_frozen_statement_advance_tail_structural_state CT P Z
    cutoff active boundary stack active_incoming head snapshots h caller_post
    Hbody_private Hcaller_post_wf) as [Hstructural _].
  destruct (private_fresh_return_partitions_after_noncap_nonrdm_pop CT P Z
    cutoff active boundary stack active_incoming head snapshots h
    caller_authority caller_senv caller_renv destination destination_type value
    Hbody Hcaller Hdestination_nonzero Hcaller_wf Hcaller_sound Hdestination
    Hnonrdm Hnoncap) as [Hcomponents [Hprospective Hafter]].
  unfold caller_post, tail_snapshots in *.
  eapply private_fresh_frozen_statement_state_from_return_parts; eauto.
Qed.

(** Policy-aware [None]-slot pop for a non-null value installed into a
    destination that is neither an RDM join root nor a capability root. *)
Lemma private_policy_statement_after_untracked_noncap_nonrdm_pop :
  forall CT P Z cutoff active boundary stack active_incoming snapshots h
    caller_incoming policies caller_policies caller_authority caller_senv
    caller_renv destination destination_type value,
    let caller_post := mk_watched_frame caller_authority caller_senv
      (update_r_env_value caller_renv destination value) in
    private_policy_statement_state CT P Z cutoff active (boundary :: stack)
      active_incoming (None :: snapshots) policies h ->
    leave_private_frame_join_policies policies = Some caller_policies ->
    principled_phased_authority_live_history_state CT P Z cutoff caller_post
      stack caller_incoming h ->
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT caller_senv caller_renv h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination value) h ->
    authority_context_sound h caller_renv caller_authority ->
    authority_context_sound h
      (update_r_env_value caller_renv destination value) caller_authority ->
    static_getType caller_senv destination = Some destination_type ->
    sqtype destination_type <> RDM ->
    ~ capability_in_context caller_authority (sqtype destination_type) ->
    (forall snapshot mode source,
      List.In (Some snapshot) snapshots ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT h caller_post caller_incoming)
        (mode, source) ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
      (exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h active active_incoming)
          (callee_mode, source)) \/
      frozen_snapshot_resume_exposure_avoids Z snapshot) ->
    executing_resumed_authority_call_pop_safe CT h Z active active_incoming
      caller_policies.(active_frame_join_targets) caller_post caller_incoming ->
    private_policy_statement_state CT P Z cutoff caller_post stack
      caller_incoming
      (advance_frozen_caller_snapshots CT h caller_post snapshots)
      caller_policies h.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshots h
    caller_incoming policies caller_policies caller_authority caller_senv
    caller_renv destination destination_type value caller_post Hstate Hleave
    Hpost Hboundary Hdestination Hcaller_wf Hcaller_post_wf Hcaller_sound
    Hcaller_post_sound Hdestination_type Hnonrdm Hnoncap Hroots_reflect Hpop.
  have Hprivate := proj1 (proj1 Hstate).
  have Hstructural : private_frozen_snapshot_structural_state CT h caller_post
      (advance_frozen_caller_snapshots CT h caller_post snapshots) stack.
  { destruct (private_frozen_statement_advance_tail_structural_state CT P Z
      cutoff active boundary stack active_incoming None snapshots h caller_post
      (proj1 Hprivate) Hcaller_post_wf) as [Hresult _].
    exact Hresult. }
  destruct (private_fresh_return_partitions_after_noncap_nonrdm_pop CT P Z
    cutoff active boundary stack active_incoming None snapshots h
    caller_authority caller_senv caller_renv destination destination_type value
    Hprivate Hboundary Hdestination Hcaller_wf Hcaller_sound Hdestination_type
    Hnonrdm Hnoncap) as [Hcomponents [Hprospective Hafter]].
  have Hreturn_safety : private_frozen_snapshot_return_safety CT h Z
      caller_post caller_incoming
      (advance_frozen_caller_snapshots CT h caller_post snapshots).
  { unfold caller_post in Hcomponents, Hprospective, Hafter |- *.
    eapply private_frozen_snapshot_return_safety_after_untracked_return_parts
      with (callee := active) (boundary := boundary)
        (incoming := active_incoming) (head_slot := None); eauto. }
  have Hpost_fresh : private_fresh_frozen_statement_state CT P Z cutoff
      caller_post stack caller_incoming
      (advance_frozen_caller_snapshots CT h caller_post snapshots) h.
  { unfold caller_post in *.
    eapply private_fresh_frozen_statement_after_noncap_nonrdm_return_parts;
      eauto. }
  have Hpost_disjoint : frozen_caller_snapshots_newer_resume_exposure_disjoint
      (advance_frozen_caller_snapshots CT h caller_post snapshots).
  { unfold caller_post in Hcomponents, Hprospective, Hafter |- *.
    eapply
      frozen_caller_snapshots_newer_resume_exposure_disjoint_after_return_parts
      with (callee := active) (boundary := boundary)
        (incoming := active_incoming) (head_slot := None); eauto.
    eapply frozen_caller_snapshots_newer_resume_exposure_disjoint_tail.
    exact (proj2 (proj1 Hstate)). }
  have Hpost_principled : private_principled_statement_state CT P Z cutoff
      caller_post stack caller_incoming
      (advance_frozen_caller_snapshots CT h caller_post snapshots) h :=
    conj Hpost_fresh Hpost_disjoint.
  eapply private_policy_statement_after_untracked_pop_from_parts; eauto.
Qed.

(** Result-qualifier-independent return transport.  The caller may install a
    fresh RDM root even when that root is not a capability under the caller's
    authority.  What the component invariants need is exactly the weaker,
    semantic fact below: if the returned object is runtime mutable, then the
    completed callee already records it as a mutable-authority root.  A
    [Mut] result supplies a capability root, an [RDM] result supplies a
    runtime-mutable RDM root, and an [Imm] result makes the premise vacuous. *)
Lemma frozen_callee_side_components_after_classified_return_pop :
  forall CT h active boundary stack head snapshots caller_authority
    caller_senv caller_renv destination destination_type return_location,
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    wf_r_config CT caller_senv caller_renv h ->
    static_getType caller_senv destination = Some destination_type ->
    (r_muttype h return_location = Some Mut_r ->
      mutable_authority_root active h return_location) ->
    frozen_callee_side_mutable_components_after_boundaries CT h active
      (head :: snapshots) (boundary :: stack) ->
    let caller_post := mk_watched_frame caller_authority caller_senv
      (update_r_env_value caller_renv destination
        (Iot return_location)) in
    frozen_callee_side_mutable_components_after_boundaries CT h caller_post
      (advance_frozen_caller_snapshots CT h caller_post snapshots) stack.
Proof.
  intros CT h active boundary stack head snapshots caller_authority
    caller_senv caller_renv destination destination_type return_location
    Hcaller Hdestination_nonzero Hactive_wf Hcaller_wf Hdestination
    Hreturn_root Hold caller_post snapshot tracked_boundary above below
    Hpartition.
  destruct (advance_frozen_snapshot_live_partition_reflects CT h caller_post
    snapshots stack snapshot tracked_boundary above below Hpartition) as
    [old_snapshot Hold_partition].
  have Hinput_partition : frozen_snapshot_live_partition
      (head :: snapshots) (boundary :: stack) old_snapshot tracked_boundary
      (boundary :: above) below.
  { constructor. exact Hold_partition. }
  have Hinput_components := Hold old_snapshot tracked_boundary
    (boundary :: above) below Hinput_partition.
  have Hreturn_component : forall target,
      r_muttype h return_location = Some Mut_r ->
      retained_mut_reachable CT h return_location target ->
      tracked_boundary.(boundary_entry_cutoff) <= target.
  { intros target Hreturn_runtime Hreturn_target.
    eapply Hinput_components with (frame := active)
      (root := return_location).
    - constructor.
    - destruct (Hreturn_root Hreturn_runtime) as
        [Hmut | [Hrdm _]].
      + apply mutable_authority_reachable_capability.
        * destruct Hmut as [variable [T [Htype [Hvalue Hmut]]]].
          exists variable, T. repeat split; try assumption.
          unfold capability_in_context. left. exact Hmut.
        * exact Hreturn_runtime.
        * exact Hreturn_target.
      + apply mutable_authority_reachable_rdm; assumption. }
  unfold caller_post.
  intros frame root target Hlive Hreachable.
  have Hlength : length caller_senv = length caller_renv.(vars) :=
    proj1 (proj2 (proj2 (proj2 (proj2 Hcaller_wf)))).
  inversion Hlive; subst.
  - inversion Hreachable; subst.
    + destruct (caller_post_capability_root_origin_private caller_authority
        caller_senv caller_renv destination destination_type return_location
        root Hdestination_nonzero Hdestination Hlength H) as
        [Hold_root | Hreturn].
      * eapply Hinput_components with
          (frame := boundary.(boundary_caller)) (root := root).
        -- constructor. simpl. left. reflexivity.
        -- apply mutable_authority_reachable_capability.
           ++ rewrite Hcaller. exact Hold_root.
           ++ exact H0.
           ++ exact H1.
      * subst root. eapply Hreturn_component; eauto.
    + destruct (caller_post_rdm_root_origin_private caller_senv caller_renv
        destination destination_type return_location root
        Hdestination_nonzero Hdestination Hlength H) as
        [Hold_root | [Hreturn _]].
      * eapply Hinput_components with
          (frame := boundary.(boundary_caller)) (root := root).
        -- constructor. simpl. left. reflexivity.
        -- apply mutable_authority_reachable_rdm.
           ++ rewrite Hcaller. exact Hold_root.
           ++ exact H0.
           ++ exact H1.
      * subst root. eapply Hreturn_component; eauto.
  - eapply Hinput_components with
      (frame := boundary0.(boundary_caller)) (root := root).
    + constructor. simpl. right. exact H.
    + exact Hreachable.
Qed.

Lemma return_pop_prospective_step_covered_classified :
  forall CT h caller callee caller_authority caller_senv caller_renv
    destination destination_type return_location source target,
    caller = mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    r_muttype h target = Some Mut_r ->
    (r_muttype h return_location = Some Mut_r ->
      prospective_location_covered_by_frame CT h callee return_location) ->
    return_pop_location_covered CT h caller callee source ->
    frozen_caller_authority_step CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination
          (Iot return_location)))
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
      [Hold_root | [Hreturn_root _]].
    + left. exists target. split.
      * right. split; [exact Hold_root|exact Htarget_runtime].
      * apply rt_refl.
    + subst target. right. exact (Hreturn Htarget_runtime).
Qed.

Lemma return_pop_prospective_state_connected_covered_classified :
  forall CT h caller callee caller_authority caller_senv caller_renv
    destination destination_type return_location source target,
    caller = mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination
        (Iot return_location)) h ->
    (r_muttype h return_location = Some Mut_r ->
      prospective_location_covered_by_frame CT h callee return_location) ->
    return_pop_prospective_state_covered CT h caller callee source ->
    frozen_caller_authority_connected CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination
          (Iot return_location))) source target ->
    return_pop_prospective_state_covered CT h caller callee target.
Proof.
  intros CT h caller callee caller_authority caller_senv caller_renv
    destination destination_type return_location source target Hcaller
    Hdestination_nonzero Hdestination Hlength Hpost_wf Hreturn Hsource
    Hconnected.
  induction Hconnected.
  - destruct x as [source_mode source_location].
    destruct y as [target_mode target_location]. simpl in *.
    destruct Hsource as [Hsource_mode [Hsource_runtime Hsource]].
    change (source_mode = FlowProspective) in Hsource_mode.
    subst source_mode.
    have Htarget_mode : target_mode = FlowProspective.
    { inversion H; reflexivity. }
    subst target_mode.
    have Htarget_runtime :=
      phased_authority_frame_step_preserves_runtime_mutability CT h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination
            (Iot return_location)))
        (FlowProspective, source_location)
        (FlowProspective, target_location) Mut_r Hpost_wf
        (frozen_caller_authority_step_is_phased CT h
          (mk_watched_frame caller_authority caller_senv
            (update_r_env_value caller_renv destination
              (Iot return_location)))
          (FlowProspective, source_location)
          (FlowProspective, target_location) H) Hsource_runtime.
    split; [reflexivity|]. split; [exact Htarget_runtime|].
    eapply return_pop_prospective_step_covered_classified; eauto.
  - exact Hsource.
  - apply IHHconnected2. apply IHHconnected1. exact Hsource.
Qed.

Lemma caller_post_mutable_authority_root_covered_classified :
  forall CT caller_authority caller_senv caller_renv destination
    destination_type return_location h callee root,
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    r_muttype h root = Some Mut_r ->
    (r_muttype h return_location = Some Mut_r ->
      prospective_location_covered_by_frame CT h callee return_location) ->
    mutable_authority_root
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination
          (Iot return_location))) h root ->
    return_pop_location_covered CT h
      (mk_watched_frame caller_authority caller_senv caller_renv) callee root.
Proof.
  intros CT caller_authority caller_senv caller_renv destination
    destination_type return_location h callee root Hdestination_nonzero
    Hdestination Hlength Hroot_runtime Hreturn [Hmut | [Hrdm _]].
  - have Hcapability : frame_capability_root
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination
            (Iot return_location))) root.
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
    + subst root. right. exact (Hreturn Hroot_runtime).
  - destruct (caller_post_rdm_root_origin_private caller_senv caller_renv
      destination destination_type return_location root
      Hdestination_nonzero Hdestination Hlength Hrdm) as
      [Hold_root | [Hreturn_root _]].
    + left. exists root. split.
      * right. split; assumption.
      * apply rt_refl.
    + subst root. right. exact (Hreturn Hroot_runtime).
Qed.

Lemma frozen_callee_side_prospective_components_after_classified_return_pop :
  forall CT h active boundary stack head snapshots caller_authority
    caller_senv caller_renv destination destination_type return_location,
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT caller_senv caller_renv h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination
        (Iot return_location)) h ->
    authority_context_sound h
      (update_r_env_value caller_renv destination
        (Iot return_location)) caller_authority ->
    static_getType caller_senv destination = Some destination_type ->
    (r_muttype h return_location = Some Mut_r ->
      mutable_authority_root active h return_location) ->
    frozen_callee_side_prospective_components_after_boundaries CT h active
      (head :: snapshots) (boundary :: stack) ->
    let caller_post := mk_watched_frame caller_authority caller_senv
      (update_r_env_value caller_renv destination
        (Iot return_location)) in
    frozen_callee_side_prospective_components_after_boundaries CT h
      caller_post
      (advance_frozen_caller_snapshots CT h caller_post snapshots) stack.
Proof.
  intros CT h active boundary stack head snapshots caller_authority
    caller_senv caller_renv destination destination_type return_location
    Hcaller Hdestination_nonzero Hcaller_wf Hcaller_post_wf
    Hcaller_post_sound Hdestination Hreturn_root Hold caller_post snapshot
    tracked_boundary above below Hpartition.
  destruct (advance_frozen_snapshot_live_partition_reflects CT h caller_post
    snapshots stack snapshot tracked_boundary above below Hpartition) as
    [old_snapshot Hold_partition].
  have Hinput_partition : frozen_snapshot_live_partition
      (head :: snapshots) (boundary :: stack) old_snapshot tracked_boundary
      (boundary :: above) below.
  { constructor. exact Hold_partition. }
  have Hinput_components := Hold old_snapshot tracked_boundary
    (boundary :: above) below Hinput_partition.
  have Hreturn_covered : r_muttype h return_location = Some Mut_r ->
      prospective_location_covered_by_frame CT h active return_location.
  { intros Hruntime. exists return_location. split.
    - exact (Hreturn_root Hruntime).
    - apply rt_refl. }
  unfold caller_post.
  intros frame root target Hlive [Hroot Hpath].
  have Hlength : length caller_senv = length caller_renv.(vars) :=
    proj1 (proj2 (proj2 (proj2 (proj2 Hcaller_wf)))).
  inversion Hlive; subst.
  - have Hroot_runtime := mutable_authority_root_runtime_mutable CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination
          (Iot return_location))) root Hcaller_post_wf
      Hcaller_post_sound Hroot.
    have Hroot_covered := caller_post_mutable_authority_root_covered_classified
      CT caller_authority caller_senv caller_renv destination destination_type
      return_location h active root Hdestination_nonzero Hdestination Hlength
      Hroot_runtime Hreturn_covered Hroot.
    have Hsource : return_pop_prospective_state_covered CT h
        (mk_watched_frame caller_authority caller_senv caller_renv) active
        (FlowProspective, root).
    { split; [reflexivity|]. split; [exact Hroot_runtime|exact Hroot_covered]. }
    have Htarget := return_pop_prospective_state_connected_covered_classified
      CT h
      (mk_watched_frame caller_authority caller_senv caller_renv) active
      caller_authority caller_senv caller_renv destination destination_type
      return_location (FlowProspective, root) (FlowProspective, target)
      eq_refl Hdestination_nonzero Hdestination Hlength Hcaller_post_wf
      Hreturn_covered Hsource Hpath.
    destruct Htarget as [_ [_
      [[caller_root [Hcaller_root Hcaller_path]] |
       [callee_root [Hcallee_root Hcallee_path]]]]].
    + eapply Hinput_components with
        (frame := boundary.(boundary_caller)) (root := caller_root).
      * constructor. simpl. left. reflexivity.
      * rewrite Hcaller. split; assumption.
    + eapply Hinput_components with (frame := active) (root := callee_root).
      * constructor.
      * split; assumption.
  - eapply Hinput_components with
      (frame := boundary0.(boundary_caller)) (root := root).
    + constructor. simpl. right. exact H.
    + split; assumption.
Qed.

Lemma private_fresh_return_partitions_after_classified_return_pop :
  forall CT P Z cutoff active boundary stack incoming head snapshots h
    caller_authority caller_senv caller_renv destination destination_type
    return_location,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (head :: snapshots) h ->
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    wf_r_config CT caller_senv caller_renv h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination
        (Iot return_location)) h ->
    authority_context_sound h
      (update_r_env_value caller_renv destination
        (Iot return_location)) caller_authority ->
    static_getType caller_senv destination = Some destination_type ->
    (r_muttype h return_location = Some Mut_r ->
      mutable_authority_root active h return_location) ->
    let caller_post := mk_watched_frame caller_authority caller_senv
      (update_r_env_value caller_renv destination
        (Iot return_location)) in
    let tail_snapshots := advance_frozen_caller_snapshots CT h caller_post
      snapshots in
    frozen_callee_side_mutable_components_after_boundaries CT h caller_post
      tail_snapshots stack /\
    frozen_callee_side_prospective_components_after_boundaries CT h
      caller_post tail_snapshots stack /\
    frozen_snapshot_boundaries_after_cutoff cutoff tail_snapshots stack.
Proof.
  intros CT P Z cutoff active boundary stack incoming head snapshots h
    caller_authority caller_senv caller_renv destination destination_type
    return_location [Hprivate [Hcomponents [Hprospective Hafter]]] Hcaller
    Hdestination_nonzero Hactive_wf Hcaller_wf Hcaller_post_wf
    Hcaller_post_sound Hdestination Hreturn_root caller_post tail_snapshots.
  split.
  - unfold caller_post, tail_snapshots.
    eapply frozen_callee_side_components_after_classified_return_pop; eauto.
  - split.
    + unfold caller_post, tail_snapshots.
      eapply
        frozen_callee_side_prospective_components_after_classified_return_pop;
        eauto.
    + unfold tail_snapshots.
      eapply advance_snapshot_boundaries_after_cutoff.
      eapply snapshot_boundaries_after_cutoff_tail. exact Hafter.
Qed.

Lemma private_fresh_frozen_statement_after_classified_return_parts :
  forall CT P Z cutoff active boundary stack active_incoming head snapshots h
    caller_incoming caller_authority caller_senv caller_renv destination
    destination_type return_location,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) active_incoming (head :: snapshots) h ->
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination
          (Iot return_location))) stack caller_incoming h ->
    private_frozen_snapshot_return_safety CT h Z
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination
          (Iot return_location))) caller_incoming
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination
            (Iot return_location))) snapshots) ->
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    wf_r_config CT caller_senv caller_renv h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination
        (Iot return_location)) h ->
    authority_context_sound h
      (update_r_env_value caller_renv destination
        (Iot return_location)) caller_authority ->
    static_getType caller_senv destination = Some destination_type ->
    (r_muttype h return_location = Some Mut_r ->
      mutable_authority_root active h return_location) ->
    private_fresh_frozen_statement_state CT P Z cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination
          (Iot return_location))) stack caller_incoming
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination
            (Iot return_location))) snapshots) h.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming head snapshots h
    caller_incoming caller_authority caller_senv caller_renv destination
    destination_type return_location Hbody Hpost Hreturn_safety Hcaller
    Hdestination_nonzero Hactive_wf Hcaller_wf Hcaller_post_wf
    Hcaller_post_sound Hdestination Hreturn_root.
  set (caller_post := mk_watched_frame caller_authority caller_senv
    (update_r_env_value caller_renv destination (Iot return_location))).
  set (tail_snapshots := advance_frozen_caller_snapshots CT h caller_post
    snapshots).
  have Hbody_private := proj1 Hbody.
  destruct (private_frozen_statement_advance_tail_structural_state CT P Z
    cutoff active boundary stack active_incoming head snapshots h caller_post
    Hbody_private Hcaller_post_wf) as [Hstructural _].
  destruct (private_fresh_return_partitions_after_classified_return_pop CT P
    Z cutoff active boundary stack active_incoming head snapshots h
    caller_authority caller_senv caller_renv destination destination_type
    return_location Hbody Hcaller Hdestination_nonzero Hactive_wf Hcaller_wf
    Hcaller_post_wf Hcaller_post_sound Hdestination Hreturn_root) as
    [Hcomponents [Hprospective Hafter]].
  unfold caller_post, tail_snapshots in *.
  eapply private_fresh_frozen_statement_state_from_return_parts; eauto.
Qed.

(** Policy-aware [None]-slot reconstruction for an arbitrary non-null RDM
    result.  Unlike the older capability-only wrapper, this version does not
    assume that the return is caller-owned; it consumes the exact
    runtime-mutable-root classifier established from the dynamic body result. *)
Lemma private_policy_statement_after_untracked_classified_return_pop :
  forall CT P Z cutoff active boundary stack active_incoming snapshots h
    caller_incoming policies caller_policies caller_authority caller_senv
    caller_renv destination destination_type return_location,
    let caller_post := mk_watched_frame caller_authority caller_senv
      (update_r_env_value caller_renv destination
        (Iot return_location)) in
    private_policy_statement_state CT P Z cutoff active (boundary :: stack)
      active_incoming (None :: snapshots) policies h ->
    leave_private_frame_join_policies policies = Some caller_policies ->
    principled_phased_authority_live_history_state CT P Z cutoff caller_post
      stack caller_incoming h ->
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    wf_r_config CT caller_senv caller_renv h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination
        (Iot return_location)) h ->
    authority_context_sound h
      (update_r_env_value caller_renv destination
        (Iot return_location)) caller_authority ->
    static_getType caller_senv destination = Some destination_type ->
    (r_muttype h return_location = Some Mut_r ->
      mutable_authority_root active h return_location) ->
    (forall snapshot mode source,
      List.In (Some snapshot) snapshots ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT h caller_post caller_incoming)
        (mode, source) ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
      (exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h active active_incoming)
          (callee_mode, source)) \/
      frozen_snapshot_resume_exposure_avoids Z snapshot) ->
    executing_resumed_authority_call_pop_safe CT h Z active active_incoming
      caller_policies.(active_frame_join_targets) caller_post caller_incoming ->
    private_policy_statement_state CT P Z cutoff caller_post stack
      caller_incoming
      (advance_frozen_caller_snapshots CT h caller_post snapshots)
      caller_policies h.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshots h
    caller_incoming policies caller_policies caller_authority caller_senv
    caller_renv destination destination_type return_location caller_post
    Hstate Hleave Hpost Hboundary Hdestination Hactive_wf Hcaller_wf
    Hcaller_post_wf Hcaller_post_sound Hdestination_type Hreturn_root
    Hroots_reflect Hpop.
  have Hprivate := proj1 (proj1 Hstate).
  have Hstructural : private_frozen_snapshot_structural_state CT h caller_post
      (advance_frozen_caller_snapshots CT h caller_post snapshots) stack.
  { destruct (private_frozen_statement_advance_tail_structural_state CT P Z
      cutoff active boundary stack active_incoming None snapshots h
      caller_post (proj1 Hprivate) Hcaller_post_wf) as [Hresult _].
    exact Hresult. }
  destruct (private_fresh_return_partitions_after_classified_return_pop CT P
    Z cutoff active boundary stack active_incoming None snapshots h
    caller_authority caller_senv caller_renv destination destination_type
    return_location Hprivate Hboundary Hdestination Hactive_wf Hcaller_wf
    Hcaller_post_wf Hcaller_post_sound Hdestination_type Hreturn_root) as
    [Hcomponents [Hprospective Hafter]].
  have Hreturn_safety : private_frozen_snapshot_return_safety CT h Z
      caller_post caller_incoming
      (advance_frozen_caller_snapshots CT h caller_post snapshots).
  { unfold caller_post in Hcomponents, Hprospective, Hafter |- *.
    eapply private_frozen_snapshot_return_safety_after_untracked_return_parts
      with (callee := active) (boundary := boundary)
        (incoming := active_incoming) (head_slot := None); eauto. }
  have Hpost_fresh : private_fresh_frozen_statement_state CT P Z cutoff
      caller_post stack caller_incoming
      (advance_frozen_caller_snapshots CT h caller_post snapshots) h.
  { unfold caller_post in *.
    eapply private_fresh_frozen_statement_after_classified_return_parts;
      eauto. }
  have Hpost_disjoint : frozen_caller_snapshots_newer_resume_exposure_disjoint
      (advance_frozen_caller_snapshots CT h caller_post snapshots).
  { unfold caller_post in Hcomponents, Hprospective, Hafter |- *.
    eapply
      frozen_caller_snapshots_newer_resume_exposure_disjoint_after_return_parts
      with (callee := active) (boundary := boundary)
        (incoming := active_incoming) (head_slot := None); eauto.
    eapply frozen_caller_snapshots_newer_resume_exposure_disjoint_tail.
    exact (proj2 (proj1 Hstate)). }
  have Hpost_principled : private_principled_statement_state CT P Z cutoff
      caller_post stack caller_incoming
      (advance_frozen_caller_snapshots CT h caller_post snapshots) h :=
    conj Hpost_fresh Hpost_disjoint.
  eapply private_policy_statement_after_untracked_pop_from_parts; eauto.
Qed.

Lemma private_resume_witnesses_cover_snapshots_tail :
  forall Z witness witnesses snapshot snapshots,
    private_resume_witnesses_cover_snapshots Z
      (witness :: witnesses) (snapshot :: snapshots) ->
    private_resume_witnesses_cover_snapshots Z witnesses snapshots.
Proof.
  intros Z witness witnesses snapshot snapshots Hcover.
  destruct snapshot; simpl in Hcover; [contradiction|exact (proj2 Hcover)].
Qed.

Lemma private_resume_witnesses_phase_wf_tail :
  forall CT h active witness witnesses snapshot snapshots,
    private_resume_witnesses_phase_wf CT h active
      (witness :: witnesses) (snapshot :: snapshots) ->
    private_resume_witnesses_phase_wf CT h active witnesses snapshots.
Proof.
  intros CT h active witness witnesses snapshot snapshots Hphase.
  simpl in Hphase. exact (proj2 (proj2 (proj2 (proj2 Hphase)))).
Qed.

Lemma private_resume_witnesses_roots_safe_tail :
  forall CT h Z active witness witnesses snapshot snapshots,
    private_resume_witnesses_roots_safe CT h Z active
      (witness :: witnesses) (snapshot :: snapshots) ->
    private_resume_witnesses_roots_safe CT h Z active witnesses snapshots.
Proof.
  intros CT h Z active witness witnesses snapshot snapshots Hsafe.
  simpl in Hsafe. exact (proj2 Hsafe).
Qed.

Lemma private_resume_witnesses_nested_resume_safe_tail :
  forall Z witness witnesses snapshot snapshots,
    private_resume_witnesses_nested_resume_safe Z
      (witness :: witnesses) (snapshot :: snapshots) ->
    private_resume_witnesses_nested_resume_safe Z witnesses snapshots.
Proof.
  intros Z witness witnesses snapshot snapshots Hsafe.
  simpl in Hsafe. exact (proj2 Hsafe).
Qed.

Lemma private_resume_witnesses_completed_safe_tail :
  forall CT h Z active incoming witness witnesses snapshot snapshots,
    private_resume_witnesses_completed_safe CT h Z active incoming
      (witness :: witnesses) (snapshot :: snapshots) ->
    private_resume_witnesses_completed_safe CT h Z active incoming witnesses
      snapshots.
Proof.
  intros CT h Z active incoming witness witnesses snapshot snapshots Hsafe.
  simpl in Hsafe. exact (proj2 Hsafe).
Qed.

Lemma private_resume_witness_stack_safe_tail :
  forall CT h Z active incoming witness witnesses,
    private_resume_witness_stack_safe CT h Z active incoming
      (witness :: witnesses) ->
    private_resume_witness_stack_safe CT h Z active incoming witnesses.
Proof.
  intros CT h Z active incoming witness witnesses
    (Hcovered & Hruntime & Hdangerous & Hclosed & Hroots & Hexposure &
      Hactive & Hjoins & Hnested & Hcompleted & Hretain & Hphase).
  unfold private_resume_witness_stack_safe.
  refine (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ (conj _ _))))))))).
  - eapply frozen_caller_snapshots_nested_covered_tail. exact Hcovered.
  - intros snapshot Hsnapshot. eapply Hruntime. simpl. right. exact Hsnapshot.
  - intros snapshot mode location Hsnapshot Hcolor.
    eapply Hdangerous; [simpl; right; exact Hsnapshot|exact Hcolor].
  - intros snapshot Hsnapshot state Hstate.
    eapply Hclosed; [simpl; right; exact Hsnapshot|exact Hstate].
  - intros snapshot root Hsnapshot Hroot.
    eapply Hroots; [simpl; right; exact Hsnapshot|exact Hroot].
  - repeat split.
    + intros snapshot Hsnapshot. eapply (proj1 Hexposure). simpl. right.
      exact Hsnapshot.
    + intros snapshot Hsnapshot. eapply (proj1 (proj2 Hexposure)). simpl.
      right. exact Hsnapshot.
    + intros snapshot mode location Hsnapshot.
      eapply (proj1 (proj2 (proj2 Hexposure))). simpl. right.
      exact Hsnapshot.
    + intros snapshot Hsnapshot.
      eapply (proj1 (proj2 (proj2 (proj2 Hexposure)))). simpl. right.
      exact Hsnapshot.
    + intros snapshot root Hsnapshot.
      eapply (proj2 (proj2 (proj2 (proj2 Hexposure)))). simpl. right.
      exact Hsnapshot.
  - intros snapshot mode source Hsnapshot Hmode Hsource Hroot.
    eapply Hactive; [simpl; right; exact Hsnapshot|exact Hmode|exact Hsource|
      exact Hroot].
  - intros snapshot mode source Hsnapshot Hmode Hsource Hroot.
    eapply Hjoins; [simpl; right; exact Hsnapshot|exact Hmode|exact Hsource|
      exact Hroot].
  - eapply frozen_caller_snapshots_nested_resume_safe_tail. exact Hnested.
  - split.
    + intros snapshot mode source Hsnapshot Hmode Hsource Hroot.
      eapply Hcompleted; [simpl; right; exact Hsnapshot|exact Hmode|
        exact Hsource|exact Hroot].
    + split.
      * intros snapshot Hsnapshot state Hstate.
        eapply Hretain; [simpl; right; exact Hsnapshot|exact Hstate].
      * intros snapshot mode location Hsnapshot Hmode Hstate.
        eapply Hphase; [simpl; right; exact Hsnapshot|exact Hmode|
          exact Hstate].
Qed.

Lemma private_resume_witnesses_cover_snapshots_after_pop_advance :
  forall CT h Z caller witness witnesses snapshot snapshots,
    private_resume_witnesses_cover_snapshots Z
      (witness :: witnesses) (snapshot :: snapshots) ->
    private_resume_witnesses_cover_snapshots Z
      (advance_frozen_caller_snapshots CT h caller witnesses)
      (advance_frozen_caller_snapshots CT h caller snapshots).
Proof.
  intros CT h Z caller witness witnesses snapshot snapshots Hcover.
  eapply private_resume_witnesses_cover_snapshots_after_advance.
  eapply private_resume_witnesses_cover_snapshots_tail. exact Hcover.
Qed.

Lemma private_resume_witnesses_cover_snapshots_activation_from_advance :
  forall CT h Z caller actual targets snapshots,
    private_resume_witnesses_cover_snapshots Z
      (advance_frozen_caller_snapshots CT h caller targets) snapshots ->
    private_resume_witnesses_cover_snapshots Z
      (activate_frozen_target_snapshots CT h caller actual targets) snapshots.
Proof.
  intros CT h Z caller actual targets.
  induction targets as [|target tail IH]; intros snapshots Hcover.
  - destruct snapshots; exact Hcover.
  - destruct snapshots as [|snapshot snapshots]; [exact Hcover|].
    destruct snapshot as [snapshot|]; [exact Hcover|].
    destruct target as [target|]; simpl in Hcover |-*.
    + destruct Hcover as [Hhead Htail]. split.
      * intros older Holder state Hstate.
        eapply advance_current_colors_in_activate_target.
        eapply Hhead; eauto.
      * eapply IH. exact Htail.
    + destruct Hcover as [Hhead Htail]. split; [exact Hhead|].
      eapply IH. exact Htail.
Qed.

Lemma private_resume_witnesses_cover_snapshots_after_pop_activate :
  forall CT h Z caller actual witness targets snapshot snapshots,
    private_resume_witnesses_cover_snapshots Z
      (witness :: targets) (snapshot :: snapshots) ->
    private_resume_witnesses_cover_snapshots Z
      (activate_frozen_target_snapshots CT h caller actual targets)
      (advance_frozen_caller_snapshots CT h caller snapshots).
Proof.
  intros CT h Z caller actual witness targets snapshot snapshots Hcover.
  eapply private_resume_witnesses_cover_snapshots_activation_from_advance.
  eapply private_resume_witnesses_cover_snapshots_after_pop_advance.
  exact Hcover.
Qed.

Lemma private_resume_witnesses_phase_wf_after_pop_advance :
  forall CT h old_active caller witness witnesses snapshot snapshots,
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    private_resume_witnesses_phase_wf CT h old_active
      (witness :: witnesses) (snapshot :: snapshots) ->
    private_resume_witnesses_phase_wf CT h caller
      (advance_frozen_caller_snapshots CT h caller witnesses)
      (advance_frozen_caller_snapshots CT h caller snapshots).
Proof.
  intros CT h old_active caller witness witnesses snapshot snapshots Hwf
    Hphase.
  eapply private_resume_witnesses_phase_wf_after_advance_from_any_active;
    [exact Hwf|].
  eapply private_resume_witnesses_phase_wf_tail. exact Hphase.
Qed.

Lemma returned_policy_tail_phase_images_grow_initial :
  forall CT entry_h final_h entry caller initial entry_head final_head tail,
    frozen_caller_snapshot_list_phase_images_grow
      (final_head :: tail)
      (entry_head :: advance_frozen_caller_snapshots CT entry_h entry initial) ->
    frozen_caller_snapshot_list_phase_images_grow
      (advance_frozen_caller_snapshots CT final_h caller tail) initial.
Proof.
  intros CT entry_h final_h entry caller initial entry_head final_head tail
    Hbody.
  inversion Hbody; subst.
  eapply frozen_caller_snapshot_list_phase_images_grow_trans.
  - apply advance_frozen_caller_snapshots_phase_images_grow.
  - eapply frozen_caller_snapshot_list_phase_images_grow_trans.
    + exact H4.
    + apply advance_frozen_caller_snapshots_phase_images_grow.
Qed.

(** The eight purely structural fields of the policy witness package.  The
    four safety fields are intentionally excluded: they are reconstructed by
    the policy-aware pop classifier from the popped head. *)
Definition private_resume_witness_stack_structural
  (CT : class_table) (h : heap) (active : watched_frame)
  (witnesses : list frozen_caller_snapshot_slot) : Prop :=
  frozen_caller_snapshots_nested_covered witnesses /\
  frozen_caller_snapshots_runtime_mutable h witnesses /\
  frozen_caller_snapshots_dangerous witnesses /\
  frozen_caller_snapshots_closed CT h active witnesses /\
  frozen_caller_snapshots_resume_roots_in_heap h witnesses /\
  frozen_caller_snapshots_resume_exposures_wf CT h active witnesses /\
  frozen_caller_snapshots_retain_entry witnesses /\
  frozen_caller_snapshots_cover_phase_incoming witnesses.

Lemma private_resume_witness_stack_safe_from_parts :
  forall CT h Z active incoming witnesses,
    private_resume_witness_stack_structural CT h active witnesses ->
    frozen_caller_snapshots_active_resume_safe CT h Z active witnesses ->
    frozen_caller_snapshots_resume_joins_safe Z witnesses ->
    frozen_caller_snapshots_nested_resume_safe Z witnesses ->
    frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h active incoming) witnesses ->
    private_resume_witness_stack_safe CT h Z active incoming witnesses.
Proof.
  intros CT h Z active incoming witnesses
    (Hcovered & Hruntime & Hdangerous & Hclosed & Hroots & Hexposure &
      Hretain & Hphase) Hactive Hjoins Hnested Hcompleted.
  unfold private_resume_witness_stack_safe.
  exact (conj Hcovered (conj Hruntime (conj Hdangerous (conj Hclosed
    (conj Hroots (conj Hexposure (conj Hactive (conj Hjoins
      (conj Hnested (conj Hcompleted (conj Hretain Hphase))))))))))).
Qed.

Lemma private_resume_witness_stack_structural_after_pop_advance :
  forall CT h Z old_active incoming caller head tail,
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    private_resume_witness_stack_safe CT h Z old_active incoming
      (head :: tail) ->
    private_resume_witness_stack_structural CT h caller
      (advance_frozen_caller_snapshots CT h caller tail).
Proof.
  intros CT h Z old_active incoming caller head tail Hwf Hsafe.
  have Htail := private_resume_witness_stack_safe_tail CT h Z old_active
    incoming head tail Hsafe.
  destruct Htail as
    (Hcovered & Hruntime & Hdangerous & Hclosed & Hroots & Hexposure &
      Hactive & Hjoins & Hnested & Hcompleted & Hretain & Hphase).
  unfold private_resume_witness_stack_structural.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  - eapply advance_frozen_caller_snapshots_nested_covered. exact Hcovered.
  - eapply advance_frozen_caller_snapshots_runtime_mutable; eauto.
  - eapply advance_frozen_caller_snapshots_dangerous. exact Hdangerous.
  - eapply advance_frozen_caller_snapshots_closed.
  - eapply advance_frozen_caller_snapshots_resume_roots_in_heap; eauto.
  - eapply advance_frozen_caller_snapshots_resume_exposures_wf_from_any_active;
      eauto.
  - eapply advance_frozen_caller_snapshots_retain_entry. exact Hretain.
  - eapply advance_frozen_caller_snapshots_cover_phase_incoming. exact Hphase.
Qed.

Lemma private_resume_witness_combined_slot_in_policy_stack :
  forall Z witness witnesses snapshots snapshot,
    private_resume_witnesses_cover_snapshots Z
      (witness :: witnesses) (None :: snapshots) ->
    List.In (Some snapshot) (witness :: snapshots) ->
    List.In (Some snapshot) (witness :: witnesses).
Proof.
  intros Z witness witnesses snapshots snapshot Hcover Hin.
  simpl in Hcover, Hin |-*.
  destruct Hin as [Hhead | Hsnapshot]; [left; exact Hhead|].
  exfalso.
  eapply private_resume_witnesses_cover_snapshots_none
    with (witnesses := witnesses) (snapshots := snapshots)
      (snapshot := snapshot); [exact (proj2 Hcover)|exact Hsnapshot].
Qed.

(** The mixed policy/ordinary relations carry no additional semantic
    obligation once the policy stack itself is safe: coverage guarantees
    that every ordinary slot in this channel is [None]. *)
Lemma private_resume_witness_relations_from_stack_safe :
  forall CT h Z active incoming witnesses snapshots,
    private_resume_witnesses_cover_snapshots Z witnesses snapshots ->
    private_resume_witness_stack_safe CT h Z active incoming witnesses ->
    private_resume_witnesses_phase_wf CT h active witnesses snapshots /\
    private_resume_witnesses_roots_safe CT h Z active witnesses snapshots /\
    private_resume_witnesses_nested_resume_safe Z witnesses snapshots /\
    private_resume_witnesses_completed_safe CT h Z active incoming witnesses
      snapshots.
Proof.
  intros CT h Z active incoming witnesses.
  induction witnesses as [|witness witnesses IH]; intros snapshots Hcover
    Hsafe.
  - destruct snapshots; simpl in Hcover |-*; [repeat split|contradiction].
  - destruct snapshots as [|slot snapshots];
      [simpl in Hcover; contradiction|].
    destruct slot as [snapshot|]; [simpl in Hcover; contradiction|].
    pose proof Hcover as Hcover_full.
    simpl in Hcover. destruct Hcover as [Hhead_cover Htail_cover].
    have Hsnapshots_none :
        snapshots = repeat None (length snapshots) :=
      private_resume_witnesses_snapshots_are_repeat_none Z witnesses
        snapshots Htail_cover.
    have Htail_safe := private_resume_witness_stack_safe_tail CT h Z active
      incoming witness witnesses Hsafe.
    destruct (IH snapshots Htail_cover Htail_safe) as
      (Htail_phase & Htail_roots & Htail_nested & Htail_completed).
    destruct Hsafe as
      (Hcovered & Hruntime & Hdangerous & Hclosed & Hroots & Hexposure &
        Hactive & Hjoins & Hnested & Hcompleted & Hretain & Hphase).
    have Hcombined_policy : forall combined,
        List.In (Some combined) (witness :: snapshots) ->
        List.In (Some combined) (witness :: witnesses).
    { intros combined Hcombined.
      eapply private_resume_witness_combined_slot_in_policy_stack;
        [exact Hcover_full|exact Hcombined]. }
    split.
    + simpl. refine (conj _ (conj _ (conj _ (conj _ Htail_phase)))).
      * intros combined Hcombined.
        eapply Hruntime. exact (Hcombined_policy combined Hcombined).
      * intros combined Hcombined.
        eapply Hclosed. exact (Hcombined_policy combined Hcombined).
      * intros combined root Hcombined Hroot.
        eapply Hroots;
          [exact (Hcombined_policy combined Hcombined)|exact Hroot].
      * repeat split.
        -- intros combined Hcombined. eapply (proj1 Hexposure).
           exact (Hcombined_policy combined Hcombined).
        -- intros combined Hcombined. eapply (proj1 (proj2 Hexposure)).
           exact (Hcombined_policy combined Hcombined).
        -- intros combined mode location Hcombined. eapply (proj1 (proj2
             (proj2 Hexposure))).
           exact (Hcombined_policy combined Hcombined).
        -- intros combined Hcombined. eapply (proj1 (proj2 (proj2
             (proj2 Hexposure)))).
           exact (Hcombined_policy combined Hcombined).
        -- intros combined root Hcombined. eapply (proj2 (proj2 (proj2
             (proj2 Hexposure)))).
           exact (Hcombined_policy combined Hcombined).
    + split.
      * simpl. split.
        -- intros combined mode source Hcombined Hmode Hsource Hroot.
           eapply Hactive.
           ++ exact (Hcombined_policy combined Hcombined).
           ++ exact Hmode.
           ++ exact Hsource.
           ++ exact Hroot.
        -- exact Htail_roots.
      * split.
        -- simpl. split.
           ++ destruct witness as [head|].
              ** simpl. split.
                 --- intros older Holder. exfalso.
                     eapply private_resume_witnesses_cover_snapshots_none
                       with (witnesses := witnesses)
                         (snapshots := snapshots) (snapshot := older); eauto.
                 --- rewrite Hsnapshots_none.
                     apply repeat_none_snapshots_nested_resume_safe.
              ** rewrite Hsnapshots_none.
                 apply repeat_none_snapshots_nested_resume_safe.
           ++ exact Htail_nested.
        -- simpl. split.
           ++ intros combined mode source Hcombined Hmode Hsource Hroot.
              eapply Hcompleted.
              ** exact (Hcombined_policy combined Hcombined).
              ** exact Hmode.
              ** exact Hsource.
              ** exact Hroot.
           ++ exact Htail_completed.
Qed.

(** Semantic interface exported by the well-founded policy-pop classifier.
    It separates the derivation-heavy part (reflection) from the routine
    reconstruction of the entry-or-safe certificates. *)
Definition policy_pop_exposure_protected_reflects
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (caller : watched_frame) (old : frozen_caller_color_snapshot) : Prop :=
  forall mode location,
    authority_mode_dangerous mode ->
    In authority_flow_state
      (advance_frozen_caller_snapshot CT h caller old).(
        frozen_snapshot_current_resume_exposure) (mode, location) ->
    In Loc Z location ->
    exists old_mode,
      authority_mode_dangerous old_mode /\
      In authority_flow_state old.(frozen_snapshot_current_resume_exposure)
        (old_mode, location).

(** The policy-only target stack does not require exact provenance for every
    exposure introduced while a callee executes.  At a protected location it
    is enough that the exposure reflects to the retained witness; otherwise
    the location itself is already harmless. *)
Definition policy_pop_exposure_reflected_or_outside
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (caller : watched_frame) (old : frozen_caller_color_snapshot) : Prop :=
  forall mode location,
    authority_mode_dangerous mode ->
    In authority_flow_state
      (advance_frozen_caller_snapshot CT h caller old).(
        frozen_snapshot_current_resume_exposure) (mode, location) ->
    In Loc Z location ->
    (exists old_mode,
      authority_mode_dangerous old_mode /\
      In authority_flow_state old.(frozen_snapshot_current_resume_exposure)
        (old_mode, location)) \/
    ~ In Loc Z location.

(** Advancing a frozen exposure through a frame cannot manufacture a
    protected dangerous color: closure provenance is either the old exposure
    itself or independent authority of the active frame. *)
Lemma policy_pop_exposure_protected_reflects_from_active_separation :
  forall CT h Z caller old,
    Included authority_flow_state
      (frozen_caller_authority_closure CT h caller
        old.(frozen_snapshot_current_resume_exposure))
      old.(frozen_snapshot_current_resume_exposure) ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h caller) (mode, location) ->
      ~ In Loc Z location) ->
    policy_pop_exposure_protected_reflects CT h Z caller old.
Proof.
  intros CT h Z caller old Hclosed Hactive mode location Hmode Hadvanced
    Hprotected.
  have Hexecuting : In authority_flow_state
      (executing_authority_color_set CT h caller
        old.(frozen_snapshot_current_resume_exposure)) (mode, location).
  { destruct Hadvanced as [seed [Hseed Hpath]]. exists seed. split.
    - left. exact Hseed.
    - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
  destruct (executing_with_frozen_incoming_dangerous_covered_by_old_or_active
    CT h caller old.(frozen_snapshot_current_resume_exposure) mode location
    Hclosed Hmode Hexecuting) as
    [[old_mode [Hold_mode Hold]] |
     [active_mode [Hactive_mode Hactive_color]]].
  - exists old_mode. split; assumption.
  - exfalso. exact (Hactive active_mode location Hactive_mode Hactive_color
      Hprotected).
Qed.

Lemma policy_pop_source_set_resume_safe :
  forall CT h Z callee callee_incoming caller old_snapshots source_set,
    frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h callee callee_incoming)
      old_snapshots ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state source_set (mode, location) ->
      exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h callee callee_incoming)
          (callee_mode, location)) ->
    (forall old,
      List.In (Some old) old_snapshots ->
      policy_pop_exposure_protected_reflects CT h Z caller old) ->
    frozen_completed_colors_resume_safe Z source_set
      (advance_frozen_caller_snapshots CT h caller old_snapshots).
Proof.
  intros CT h Z callee callee_incoming caller old_snapshots source_set
    Hold Hsource Hexposure new_snapshot mode source Hnew Hmode Hnew_source
    Hroot.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [slot [Heq Hslot]].
  destruct slot as [old|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in Hroot.
  destruct (Hsource mode source Hmode Hnew_source) as
    [callee_mode [Hcallee_mode Hcallee_source]].
  destruct (Hold old callee_mode source Hslot Hcallee_mode Hcallee_source
    Hroot) as [[entry_mode [Hentry_mode Hentry]] | Hold_safe].
  - left. exists entry_mode. simpl. split; assumption.
  - right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
    destruct (Hexposure old Hslot exposure_mode target Hexposure_mode Htarget
      Hprotected) as [old_mode [Hold_mode Hold_target]].
    eapply Hold_safe; eauto.
Qed.

(** Root-scoped counterpart of [policy_pop_source_set_resume_safe].  A
    resumed source need not globally reflect into the completed callee when
    the particular retained witness already certifies that every exposure
    from that root avoids the protected zone. *)
Lemma policy_pop_source_set_resume_safe_classified :
  forall CT h Z callee callee_incoming caller old_snapshots source_set,
    frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h callee callee_incoming)
      old_snapshots ->
    (forall old mode source,
      List.In (Some old) old_snapshots ->
      authority_mode_dangerous mode ->
      In authority_flow_state source_set (mode, source) ->
      In Loc old.(frozen_snapshot_resume_rdm_roots) source ->
      (exists entry_mode,
        authority_mode_dangerous entry_mode /\
        In authority_flow_state old.(frozen_snapshot_entry_colors)
          (entry_mode, source)) \/
      (exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h callee callee_incoming)
          (callee_mode, source)) \/
      frozen_snapshot_resume_exposure_avoids Z old) ->
    (forall old,
      List.In (Some old) old_snapshots ->
      policy_pop_exposure_reflected_or_outside CT h Z caller old) ->
    frozen_completed_colors_resume_safe Z source_set
      (advance_frozen_caller_snapshots CT h caller old_snapshots).
Proof.
  intros CT h Z callee callee_incoming caller old_snapshots source_set
    Hold Hsource Hexposure new_snapshot mode source Hnew Hmode Hnew_source
    Hroot.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [slot [Heq Hslot]].
  destruct slot as [old|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in Hroot.
  destruct (Hsource old mode source Hslot Hmode Hnew_source Hroot) as
    [[entry_mode [Hentry_mode Hentry]] |
     [[callee_mode [Hcallee_mode Hcallee_source]] | Hold_safe]].
  - left. exists entry_mode. simpl. split; assumption.
  - destruct (Hold old callee_mode source Hslot Hcallee_mode Hcallee_source
      Hroot) as [[entry_mode [Hentry_mode Hentry]] | Hold_safe].
    + left. exists entry_mode. simpl. split; assumption.
    + right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
      destruct (Hexposure old Hslot exposure_mode target Hexposure_mode
        Htarget Hprotected) as [[old_mode [Hold_mode Hold_target]] | Houtside].
      * eapply Hold_safe; eauto.
      * exact (Houtside Hprotected).
  - right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
    destruct (Hexposure old Hslot exposure_mode target Hexposure_mode Htarget
      Hprotected)
      as [[old_mode [Hold_mode Hold_target]] | Houtside].
    + eapply Hold_safe; eauto.
    + exact (Houtside Hprotected).
Qed.

Lemma policy_pop_resume_joins_safe :
  forall CT h Z callee callee_incoming caller old_snapshots,
    frozen_caller_snapshots_resume_joins_safe Z old_snapshots ->
    frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h callee callee_incoming)
      old_snapshots ->
    (forall old target mode location,
      List.In (Some old) old_snapshots ->
      List.In (Some target) old_snapshots ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (advance_frozen_caller_snapshot CT h caller old).(
          frozen_snapshot_current_colors) (mode, location) ->
      In Loc target.(frozen_snapshot_resume_rdm_roots) location ->
      (exists old_mode,
        authority_mode_dangerous old_mode /\
        In authority_flow_state old.(frozen_snapshot_current_colors)
          (old_mode, location)) \/
      (exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h callee callee_incoming)
          (callee_mode, location))) ->
    (forall old,
      List.In (Some old) old_snapshots ->
      policy_pop_exposure_protected_reflects CT h Z caller old) ->
    frozen_caller_snapshots_resume_joins_safe Z
      (advance_frozen_caller_snapshots CT h caller old_snapshots).
Proof.
  intros CT h Z callee callee_incoming caller old_snapshots Hold_joins
    Hold_completed Hcolor Hexposure new_snapshot mode source Hnew Hmode
    Hnew_source Hroot.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [slot [Heq Hslot]].
  destruct slot as [old|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in Hroot.
  destruct (Hcolor old old mode source Hslot Hslot Hmode Hnew_source Hroot) as
    [[old_mode [Hold_mode Hold_source]] |
     [callee_mode [Hcallee_mode Hcallee_source]]].
  - destruct (Hold_joins old old_mode source Hslot Hold_mode Hold_source Hroot)
      as [[entry_mode [Hentry_mode Hentry]] | Hold_safe].
    + left. exists entry_mode. simpl. split; assumption.
    + right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
      destruct (Hexposure old Hslot exposure_mode target Hexposure_mode
        Htarget Hprotected) as [old_exposure_mode
          [Hold_exposure_mode Hold_target]].
      eapply Hold_safe; eauto.
  - destruct (Hold_completed old callee_mode source Hslot Hcallee_mode
      Hcallee_source Hroot) as
      [[entry_mode [Hentry_mode Hentry]] | Hold_safe].
    + left. exists entry_mode. simpl. split; assumption.
    + right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
      destruct (Hexposure old Hslot exposure_mode target Hexposure_mode
        Htarget Hprotected) as [old_exposure_mode
          [Hold_exposure_mode Hold_target]].
      eapply Hold_safe; eauto.
Qed.

Lemma policy_pop_resume_joins_safe_classified :
  forall CT h Z callee callee_incoming caller old_snapshots,
    frozen_caller_snapshots_resume_joins_safe Z old_snapshots ->
    frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h callee callee_incoming)
      old_snapshots ->
    (forall old target mode location,
      List.In (Some old) old_snapshots ->
      List.In (Some target) old_snapshots ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (advance_frozen_caller_snapshot CT h caller old).(
          frozen_snapshot_current_colors) (mode, location) ->
      In Loc target.(frozen_snapshot_resume_rdm_roots) location ->
      (exists old_mode,
        authority_mode_dangerous old_mode /\
        In authority_flow_state old.(frozen_snapshot_current_colors)
          (old_mode, location)) \/
      (exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h callee callee_incoming)
          (callee_mode, location)) \/
      frozen_snapshot_resume_exposure_avoids Z target) ->
    (forall old,
      List.In (Some old) old_snapshots ->
      policy_pop_exposure_reflected_or_outside CT h Z caller old) ->
    frozen_caller_snapshots_resume_joins_safe Z
      (advance_frozen_caller_snapshots CT h caller old_snapshots).
Proof.
  intros CT h Z callee callee_incoming caller old_snapshots Hold_joins
    Hold_completed Hcolor Hexposure new_snapshot mode source Hnew Hmode
    Hnew_source Hroot.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [slot [Heq Hslot]].
  destruct slot as [old|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in Hroot.
  destruct (Hcolor old old mode source Hslot Hslot Hmode Hnew_source Hroot) as
    [[old_mode [Hold_mode Hold_source]] |
     [[callee_mode [Hcallee_mode Hcallee_source]] | Hold_safe]].
  - destruct (Hold_joins old old_mode source Hslot Hold_mode Hold_source Hroot)
      as [[entry_mode [Hentry_mode Hentry]] | Hold_safe].
    + left. exists entry_mode. simpl. split; assumption.
    + right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
      destruct (Hexposure old Hslot exposure_mode target Hexposure_mode
        Htarget Hprotected) as [[old_exposure_mode
          [Hold_exposure_mode Hold_target]] | Houtside].
      * eapply Hold_safe; eauto.
      * exact (Houtside Hprotected).
  - destruct (Hold_completed old callee_mode source Hslot Hcallee_mode
      Hcallee_source Hroot) as
      [[entry_mode [Hentry_mode Hentry]] | Hold_safe].
    + left. exists entry_mode. simpl. split; assumption.
    + right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
      destruct (Hexposure old Hslot exposure_mode target Hexposure_mode
        Htarget Hprotected) as [[old_exposure_mode
          [Hold_exposure_mode Hold_target]] | Houtside].
      * eapply Hold_safe; eauto.
      * exact (Houtside Hprotected).
  - right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
    destruct (Hexposure old Hslot exposure_mode target Hexposure_mode Htarget
      Hprotected)
      as [[old_exposure_mode [Hold_exposure_mode Hold_target]] | Houtside].
    + eapply Hold_safe; eauto.
    + exact (Houtside Hprotected).
Qed.

Lemma policy_pop_nested_resume_safe :
  forall CT h Z callee callee_incoming caller old_snapshots,
    frozen_caller_snapshots_nested_resume_safe Z old_snapshots ->
    frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h callee callee_incoming)
      old_snapshots ->
    (forall old target mode location,
      List.In (Some old) old_snapshots ->
      List.In (Some target) old_snapshots ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (advance_frozen_caller_snapshot CT h caller old).(
          frozen_snapshot_current_colors) (mode, location) ->
      In Loc target.(frozen_snapshot_resume_rdm_roots) location ->
      (exists old_mode,
        authority_mode_dangerous old_mode /\
        In authority_flow_state old.(frozen_snapshot_current_colors)
          (old_mode, location)) \/
      (exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h callee callee_incoming)
          (callee_mode, location))) ->
    (forall old,
      List.In (Some old) old_snapshots ->
      policy_pop_exposure_protected_reflects CT h Z caller old) ->
    frozen_caller_snapshots_nested_resume_safe Z
      (advance_frozen_caller_snapshots CT h caller old_snapshots).
Proof.
  intros CT h Z callee callee_incoming caller old_snapshots Hnested
    Hcompleted Hcolor Hexposure.
  induction old_snapshots as [|slot tail IH]; simpl in *; [exact I|].
  destruct slot as [head|].
  - destruct Hnested as [Hhead_nested Htail_nested]. split.
    + intros new_older Hnew_older mode source Hmode Hsource Hroot.
      unfold advance_frozen_caller_snapshots in Hnew_older.
      apply in_map_iff in Hnew_older.
      destruct Hnew_older as [old_slot [Heq Hold_slot]].
      destruct old_slot as [old_older|]; simpl in Heq; [|discriminate].
      injection Heq as <-. simpl in Hroot.
      destruct (Hcolor head old_older mode source (ltac:(simpl; auto))
        (ltac:(simpl; right; exact Hold_slot)) Hmode Hsource Hroot) as
        [[old_mode [Hold_mode Hold_source]] |
         [callee_mode [Hcallee_mode Hcallee_source]]].
      * destruct (Hhead_nested old_older Hold_slot old_mode source Hold_mode
          Hold_source Hroot) as
          [[entry_mode [Hentry_mode Hentry]] | Hold_safe].
        -- left. exists entry_mode. simpl. split; assumption.
        -- right. intros exposure_mode target Hexposure_mode Htarget
             Hprotected.
           destruct (Hexposure old_older (ltac:(simpl; right; exact Hold_slot))
             exposure_mode target Hexposure_mode Htarget Hprotected) as
             [old_exposure_mode [Hold_exposure_mode Hold_target]].
           eapply Hold_safe; eauto.
      * destruct (Hcompleted old_older callee_mode source
          (ltac:(simpl; right; exact Hold_slot)) Hcallee_mode Hcallee_source
          Hroot) as [[entry_mode [Hentry_mode Hentry]] | Hold_safe].
        -- left. exists entry_mode. simpl. split; assumption.
        -- right. intros exposure_mode target Hexposure_mode Htarget
             Hprotected.
           destruct (Hexposure old_older (ltac:(simpl; right; exact Hold_slot))
             exposure_mode target Hexposure_mode Htarget Hprotected) as
             [old_exposure_mode [Hold_exposure_mode Hold_target]].
           eapply Hold_safe; eauto.
    + eapply IH.
      * exact Htail_nested.
      * intros older mode source Holder.
        eapply Hcompleted. simpl. right. exact Holder.
      * intros old target mode location Hold Htarget.
        eapply Hcolor; simpl; right; eauto.
      * intros old Hold. eapply Hexposure. simpl. right. exact Hold.
  - eapply IH.
    + exact Hnested.
    + intros older mode source Holder.
      eapply Hcompleted. simpl. right. exact Holder.
    + intros old target mode location Hold Htarget.
      eapply Hcolor; simpl; right; eauto.
    + intros old Hold. eapply Hexposure. simpl. right. exact Hold.
Qed.

Lemma policy_pop_nested_resume_safe_classified :
  forall CT h Z callee callee_incoming caller old_snapshots,
    frozen_caller_snapshots_nested_resume_safe Z old_snapshots ->
    frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h callee callee_incoming)
      old_snapshots ->
    (forall old target mode location,
      List.In (Some old) old_snapshots ->
      List.In (Some target) old_snapshots ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (advance_frozen_caller_snapshot CT h caller old).(
          frozen_snapshot_current_colors) (mode, location) ->
      In Loc target.(frozen_snapshot_resume_rdm_roots) location ->
      (exists old_mode,
        authority_mode_dangerous old_mode /\
        In authority_flow_state old.(frozen_snapshot_current_colors)
          (old_mode, location)) \/
      (exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h callee callee_incoming)
          (callee_mode, location)) \/
      frozen_snapshot_resume_exposure_avoids Z target) ->
    (forall old,
      List.In (Some old) old_snapshots ->
      policy_pop_exposure_reflected_or_outside CT h Z caller old) ->
    frozen_caller_snapshots_nested_resume_safe Z
      (advance_frozen_caller_snapshots CT h caller old_snapshots).
Proof.
  intros CT h Z callee callee_incoming caller old_snapshots Hnested
    Hcompleted Hcolor Hexposure.
  induction old_snapshots as [|slot tail IH]; simpl in *; [exact I|].
  destruct slot as [head|].
  - destruct Hnested as [Hhead_nested Htail_nested]. split.
    + intros new_older Hnew_older mode source Hmode Hsource Hroot.
      unfold advance_frozen_caller_snapshots in Hnew_older.
      apply in_map_iff in Hnew_older.
      destruct Hnew_older as [old_slot [Heq Hold_slot]].
      destruct old_slot as [old_older|]; simpl in Heq; [|discriminate].
      injection Heq as <-. simpl in Hroot.
      destruct (Hcolor head old_older mode source (ltac:(simpl; auto))
        (ltac:(simpl; right; exact Hold_slot)) Hmode Hsource Hroot) as
        [[old_mode [Hold_mode Hold_source]] |
         [[callee_mode [Hcallee_mode Hcallee_source]] | Hold_safe]].
      * destruct (Hhead_nested old_older Hold_slot old_mode source Hold_mode
          Hold_source Hroot) as
          [[entry_mode [Hentry_mode Hentry]] | Hold_safe].
        -- left. exists entry_mode. simpl. split; assumption.
        -- right. intros exposure_mode target Hexposure_mode Htarget
             Hprotected.
           destruct (Hexposure old_older (ltac:(simpl; right; exact Hold_slot))
             exposure_mode target Hexposure_mode Htarget Hprotected) as
             [[old_exposure_mode [Hold_exposure_mode Hold_target]] | Houtside].
           ++ eapply Hold_safe; eauto.
           ++ exact (Houtside Hprotected).
      * destruct (Hcompleted old_older callee_mode source
          (ltac:(simpl; right; exact Hold_slot)) Hcallee_mode Hcallee_source
          Hroot) as [[entry_mode [Hentry_mode Hentry]] | Hold_safe].
        -- left. exists entry_mode. simpl. split; assumption.
        -- right. intros exposure_mode target Hexposure_mode Htarget
             Hprotected.
           destruct (Hexposure old_older (ltac:(simpl; right; exact Hold_slot))
             exposure_mode target Hexposure_mode Htarget Hprotected) as
             [[old_exposure_mode [Hold_exposure_mode Hold_target]] | Houtside].
           ++ eapply Hold_safe; eauto.
           ++ exact (Houtside Hprotected).
      * right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
        destruct (Hexposure old_older (ltac:(simpl; right; exact Hold_slot))
          exposure_mode target Hexposure_mode Htarget Hprotected) as
          [[old_exposure_mode [Hold_exposure_mode Hold_target]] | Houtside].
        -- eapply Hold_safe; eauto.
        -- exact (Houtside Hprotected).
    + eapply IH.
      * exact Htail_nested.
      * intros older mode source Holder.
        eapply Hcompleted. simpl. right. exact Holder.
      * intros old target mode location Hold Htarget.
        eapply Hcolor; simpl; right; eauto.
      * intros old Hold. eapply Hexposure. simpl. right. exact Hold.
  - eapply IH.
    + exact Hnested.
    + intros older mode source Holder.
      eapply Hcompleted. simpl. right. exact Holder.
    + intros old target mode location Hold Htarget.
      eapply Hcolor; simpl; right; eauto.
    + intros old Hold. eapply Hexposure. simpl. right. exact Hold.
Qed.

Lemma private_resume_witness_stack_safe_after_policy_pop_from_reflection :
  forall CT h Z callee callee_incoming caller caller_incoming old_snapshots,
    private_resume_witness_stack_structural CT h caller
      (advance_frozen_caller_snapshots CT h caller old_snapshots) ->
    private_resume_witness_stack_safe CT h Z callee callee_incoming
      old_snapshots ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h caller) (mode, location) ->
      exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h callee callee_incoming)
          (callee_mode, location)) ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT h caller caller_incoming)
        (mode, location) ->
      exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h callee callee_incoming)
          (callee_mode, location)) ->
    (forall old target mode location,
      List.In (Some old) old_snapshots ->
      List.In (Some target) old_snapshots ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (advance_frozen_caller_snapshot CT h caller old).(
          frozen_snapshot_current_colors) (mode, location) ->
      In Loc target.(frozen_snapshot_resume_rdm_roots) location ->
      (exists old_mode,
        authority_mode_dangerous old_mode /\
        In authority_flow_state old.(frozen_snapshot_current_colors)
          (old_mode, location)) \/
      (exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h callee callee_incoming)
          (callee_mode, location))) ->
    (forall old,
      List.In (Some old) old_snapshots ->
      policy_pop_exposure_protected_reflects CT h Z caller old) ->
    private_resume_witness_stack_safe CT h Z caller caller_incoming
      (advance_frozen_caller_snapshots CT h caller old_snapshots).
Proof.
  intros CT h Z callee callee_incoming caller caller_incoming old_snapshots
    Hstructural Hstack Hactive_reflect Hcompleted_reflect Hcolor Hexposure.
  destruct Hstack as
    (Hcovered & Hruntime & Hdangerous & Hclosed & Hroots & Hexposure_wf &
      Hactive & Hjoins & Hnested & Hcompleted & Hretain & Hphase).
  eapply private_resume_witness_stack_safe_from_parts.
  - exact Hstructural.
  - unfold frozen_caller_snapshots_active_resume_safe.
    eapply policy_pop_source_set_resume_safe; eauto.
  - eapply policy_pop_resume_joins_safe; eauto.
  - eapply policy_pop_nested_resume_safe; eauto.
  - eapply policy_pop_source_set_resume_safe; eauto.
Qed.

(** Principled policy-pop reconstruction.  Every semantic premise is scoped
    to the retained witness whose resume root is actually reached.  The
    alternative to completed-callee provenance is that witness's own
    protected-exposure certificate, never a new public assumption. *)
Lemma private_resume_witness_stack_safe_after_policy_pop_classified :
  forall CT h Z callee callee_incoming caller caller_incoming old_snapshots,
    private_resume_witness_stack_structural CT h caller
      (advance_frozen_caller_snapshots CT h caller old_snapshots) ->
    private_resume_witness_stack_safe CT h Z callee callee_incoming
      old_snapshots ->
    (forall old mode source,
      List.In (Some old) old_snapshots ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h caller) (mode, source) ->
      In Loc old.(frozen_snapshot_resume_rdm_roots) source ->
      (exists entry_mode,
        authority_mode_dangerous entry_mode /\
        In authority_flow_state old.(frozen_snapshot_entry_colors)
          (entry_mode, source)) \/
      (exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h callee callee_incoming)
          (callee_mode, source)) \/
      frozen_snapshot_resume_exposure_avoids Z old) ->
    (forall old mode source,
      List.In (Some old) old_snapshots ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT h caller caller_incoming)
        (mode, source) ->
      In Loc old.(frozen_snapshot_resume_rdm_roots) source ->
      (exists entry_mode,
        authority_mode_dangerous entry_mode /\
        In authority_flow_state old.(frozen_snapshot_entry_colors)
          (entry_mode, source)) \/
      (exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h callee callee_incoming)
          (callee_mode, source)) \/
      frozen_snapshot_resume_exposure_avoids Z old) ->
    (forall old target mode location,
      List.In (Some old) old_snapshots ->
      List.In (Some target) old_snapshots ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (advance_frozen_caller_snapshot CT h caller old).(
          frozen_snapshot_current_colors) (mode, location) ->
      In Loc target.(frozen_snapshot_resume_rdm_roots) location ->
      (exists old_mode,
        authority_mode_dangerous old_mode /\
        In authority_flow_state old.(frozen_snapshot_current_colors)
          (old_mode, location)) \/
      (exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h callee callee_incoming)
          (callee_mode, location)) \/
      frozen_snapshot_resume_exposure_avoids Z target) ->
    (forall old,
      List.In (Some old) old_snapshots ->
      policy_pop_exposure_reflected_or_outside CT h Z caller old) ->
    private_resume_witness_stack_safe CT h Z caller caller_incoming
      (advance_frozen_caller_snapshots CT h caller old_snapshots).
Proof.
  intros CT h Z callee callee_incoming caller caller_incoming old_snapshots
    Hstructural Hstack Hactive Hcompleted Hcolor Hexposure.
  destruct Hstack as
    (Hcovered & Hruntime & Hdangerous & Hclosed & Hroots & Hexposure_wf &
      Hold_active & Hold_joins & Hold_nested & Hold_completed & Hretain &
      Hphase).
  eapply private_resume_witness_stack_safe_from_parts.
  - exact Hstructural.
  - unfold frozen_caller_snapshots_active_resume_safe.
    eapply policy_pop_source_set_resume_safe_classified; eauto.
  - eapply policy_pop_resume_joins_safe_classified; eauto.
  - eapply policy_pop_nested_resume_safe_classified; eauto.
  - eapply policy_pop_source_set_resume_safe_classified; eauto.
Qed.

(** Eliminate the tracked color class at a root belonging to an older
    policy witness.  The three classifier cases have exactly the intended
    temporal meanings: a frozen-head color is handled by the stored
    head/older continuation certificate, a completed-callee color is kept,
    and a head resume-exposure color cannot occur at an older captured root.
    The older-entry alternative is already legitimate behavioral provenance;
    it must not be forced through an unrelated completed-callee image. *)
Lemma tracked_policy_head_class_at_older_root_is_classified :
  forall CT h Z callee callee_incoming caller caller_incoming head tail old
    mode source,
    private_resume_witness_stack_safe CT h Z callee callee_incoming
      (Some head :: tail) ->
    frozen_caller_snapshots_newer_resume_exposure_disjoint
      (Some head :: tail) ->
    List.In (Some old) tail ->
    authority_mode_dangerous mode ->
    In Loc old.(frozen_snapshot_resume_rdm_roots) source ->
    tracked_resume_frozen_color_class CT h Z callee callee_incoming caller
      caller_incoming head (mode, source) ->
    (exists entry_mode,
      authority_mode_dangerous entry_mode /\
      In authority_flow_state old.(frozen_snapshot_entry_colors)
        (entry_mode, source)) \/
    (exists callee_mode,
      authority_mode_dangerous callee_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h callee callee_incoming)
        (callee_mode, source)) \/
    frozen_snapshot_resume_exposure_avoids Z old.
Proof.
  intros CT h Z callee callee_incoming caller caller_incoming head tail old
    mode source Hstack Hdisjoint Hold Hmode Hroot Hclass.
  destruct Hstack as
    (_ & _ & _ & _ & _ & _ & _ & _ & Hnested & _ & _ & _).
  simpl in Hnested. destruct Hnested as [Hhead_nested _].
  simpl in Hdisjoint. destruct Hdisjoint as [Hhead_disjoint _].
  destruct Hclass as
    [Hhead | [[Hcallee _] | [Hexposure _]]].
  - destruct (Hhead_nested old Hold mode source Hmode Hhead Hroot) as
      [[entry_mode [Hentry_mode Hentry]] | Hold_safe].
    + left. exists entry_mode. split; assumption.
    + right. right. exact Hold_safe.
  - right. left. exists mode. split; assumption.
  - exfalso. eapply (Hhead_disjoint old Hold mode source); eauto.
Qed.

(** Call-facing wrapper for the policy-only [Some]-head pop.  The caller
    supplies the tracked classifier for its two post-pop source sets and the
    mechanical reflection of an advanced tail color at an older root.  This
    wrapper consumes the popped witness and returns a safe advanced tail;
    none of these proof-local arguments survive into statement preservation. *)
Lemma private_resume_witness_stack_safe_after_tracked_policy_head_pop :
  forall CT h Z callee callee_incoming caller caller_incoming head tail,
    private_resume_witness_stack_structural CT h caller
      (advance_frozen_caller_snapshots CT h caller tail) ->
    private_resume_witness_stack_safe CT h Z callee callee_incoming
      (Some head :: tail) ->
    frozen_caller_snapshots_newer_resume_exposure_disjoint
      (Some head :: tail) ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h caller) (mode, location) ->
      tracked_resume_frozen_color_class CT h Z callee callee_incoming caller
        caller_incoming head (mode, location)) ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT h caller caller_incoming)
        (mode, location) ->
      tracked_resume_frozen_color_class CT h Z callee callee_incoming caller
        caller_incoming head (mode, location)) ->
    (forall old target mode location,
      List.In (Some old) tail ->
      List.In (Some target) tail ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (advance_frozen_caller_snapshot CT h caller old).(
          frozen_snapshot_current_colors) (mode, location) ->
      In Loc target.(frozen_snapshot_resume_rdm_roots) location ->
      In authority_flow_state old.(frozen_snapshot_current_colors)
        (mode, location)) ->
    (forall old,
      List.In (Some old) tail ->
      policy_pop_exposure_reflected_or_outside CT h Z caller old) ->
    private_resume_witness_stack_safe CT h Z caller caller_incoming
      (advance_frozen_caller_snapshots CT h caller tail).
Proof.
  intros CT h Z callee callee_incoming caller caller_incoming head tail
    Hstructural Hstack Hdisjoint Hactive_class Hcompleted_class Hcolor
    Hexposure.
  eapply private_resume_witness_stack_safe_after_policy_pop_classified.
  - exact Hstructural.
  - eapply private_resume_witness_stack_safe_tail. exact Hstack.
  - intros old mode source Hold Hmode Hsource Hroot.
    eapply tracked_policy_head_class_at_older_root_is_classified; eauto.
  - intros old mode source Hold Hmode Hsource Hroot.
    eapply tracked_policy_head_class_at_older_root_is_classified; eauto.
  - intros old target mode location Hold Htarget Hmode Hsource Hroot.
    left. exists mode. split; [exact Hmode|].
    eapply Hcolor; eauto.
  - exact Hexposure.
Qed.
