Require Import Syntax Notations Helpers Typing Subtyping Bigstep.
Require Import ViewpointAdaptation Properties Preservation ReadonlyHelper.
Require Import Reachability MutableCapability ComponentColoring.
Require Import ExecutionConfinement ProtectionHistory ForwardCapabilityHistory.
Require Import AuthorityCapability AuthorityHistory WatchedFrames
  LiveCapabilityStack.
Require Export PotentialCapabilityTargetPop.

From Stdlib Require Import List Sets.Ensembles Relations.Relation_Operators
  Program.Equality.
Import ListNotations.

(** Call-entry transport for the private cross-channel target certificate.
    These lemmas are kept separate from statement preservation because they
    use the safe-call reflection argument in both the source and resumed
    exposure channels. *)

Lemma frozen_source_resume_phase_safe_after_safe_call_entry_from_parts :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    source_colors resumes x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    authority_colors_runtime_mutable h source_colors ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h
        (mk_watched_frame caller_authority sGamma rGamma) source_colors)
      source_colors ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame caller_authority sGamma rGamma) resumes ->
    frozen_completed_colors_resume_phase_safe Z source_colors resumes ->
    frozen_completed_colors_resume_phase_safe Z
      (independent_active_authority_colors CT h
        (mk_watched_frame caller_authority sGamma rGamma)) resumes ->
    let caller := mk_watched_frame caller_authority sGamma rGamma in
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_completed_colors_resume_phase_safe Z
      (frozen_caller_authority_closure CT h callee source_colors)
      (advance_frozen_caller_snapshots CT h callee resumes).
Proof.
  intros CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    source_colors resumes x method y args sGamma' vals ly cy runtime_mdef Ty
    Hmain Htyping Hscope Hgety Hvalue Hbase Hfind Hargs Hsource_runtime
    Hsource_closed Hresume_exposure Hsafe Hactive_phase caller callee.
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hsound : authority_context_sound h rGamma caller_authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
  have Hseparated := proj1 (proj2 (proj2 (proj2 Hmain))).
  intros new_resume source_mode source Hnew Hsource_mode Hsource Hroot.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_resume|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  have Hlift_phase_safe :
      ((exists phase_mode,
          authority_mode_dangerous phase_mode /\
          In authority_flow_state old_resume.(frozen_snapshot_phase_incoming)
            (phase_mode, source)) \/
       frozen_snapshot_resume_exposure_avoids Z old_resume) ->
      ((exists phase_mode,
          authority_mode_dangerous phase_mode /\
          In authority_flow_state old_resume.(frozen_snapshot_phase_incoming)
            (phase_mode, source)) \/
       frozen_snapshot_resume_exposure_avoids Z
         (advance_frozen_caller_snapshot CT h callee old_resume)).
  { intros [[phase_mode [Hphase_mode Hphase]] | Hold_safe].
    - left. exists phase_mode. split; assumption.
    - right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
      have Hcallee_target : In authority_flow_state
          (executing_authority_color_set CT h callee
            (executing_authority_color_set CT h caller
              old_resume.(frozen_snapshot_current_resume_exposure)))
          (exposure_mode, target).
      { destruct Htarget as [seed [Hseed Hpath]]. exists seed. split.
        - left. apply executing_authority_color_set_contains_incoming.
          exact Hseed.
        - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
      destruct (executing_authority_colors_enter_call_covered CT
        caller_authority sGamma mt rGamma h x method y args sGamma' vals ly
        cy runtime_mdef Ty
        old_resume.(frozen_snapshot_current_resume_exposure) Hwf Hsound
        ((proj1 Hresume_exposure) old_resume Hold) Htyping Hscope Hgety
        Hvalue Hbase Hfind Hargs exposure_mode target Hexposure_mode
        Hcallee_target) as
        [caller_target_mode [Hcaller_target_mode Hcaller_target]].
      destruct
        (executing_with_frozen_incoming_dangerous_covered_by_old_or_active
          CT h caller old_resume.(frozen_snapshot_current_resume_exposure)
          caller_target_mode target
          ((proj1 (proj2 Hresume_exposure)) old_resume Hold)
          Hcaller_target_mode Hcaller_target) as
        [[old_target_mode [Hold_target_mode Hold_target]] |
         [active_target_mode [Hactive_target_mode Hactive_target]]].
      + exact (Hold_safe old_target_mode target Hold_target_mode Hold_target
          Hprotected).
      + eapply Hseparated; [exact Hactive_target_mode| |exact Hprotected].
        eapply independent_active_authority_colors_in_executing.
        exact Hactive_target. }
  have Hcallee_source : In authority_flow_state
      (executing_authority_color_set CT h callee
        (executing_authority_color_set CT h caller source_colors))
      (source_mode, source).
  { destruct Hsource as [seed [Hseed Hpath]]. exists seed. split.
    - left. apply executing_authority_color_set_contains_incoming.
      exact Hseed.
    - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
  destruct (executing_authority_colors_enter_call_covered CT
    caller_authority sGamma mt rGamma h x method y args sGamma' vals ly cy
    runtime_mdef Ty source_colors Hwf Hsound Hsource_runtime Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs source_mode source Hsource_mode
    Hcallee_source) as [caller_mode [Hcaller_mode Hcaller_source]].
  destruct (executing_with_frozen_incoming_dangerous_covered_by_old_or_active
    CT h caller source_colors caller_mode source Hsource_closed Hcaller_mode
    Hcaller_source) as
    [[old_mode [Hold_mode Hold_source]] |
     [active_mode [Hactive_mode Hactive_source]]].
  - apply Hlift_phase_safe. eapply Hsafe; eauto.
  - apply Hlift_phase_safe. eapply Hactive_phase; eauto.
Qed.

(** Safe call entry transports the pairwise target relation through the
    closure taken in the callee frame.  The saved authority is metadata, so
    a head that is authoritative after transport was authoritative before
    transport as well. *)
Lemma frozen_caller_snapshots_nested_resume_phase_safe_after_safe_call_entry :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    targets x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame caller_authority sGamma rGamma) targets ->
    frozen_caller_snapshots_nested_resume_phase_safe Z targets ->
    frozen_completed_colors_resume_phase_safe Z
      (independent_active_authority_colors CT h
        (mk_watched_frame caller_authority sGamma rGamma)) targets ->
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_caller_snapshots_nested_resume_phase_safe Z
      (advance_frozen_caller_snapshots CT h callee targets).
Proof.
  intros CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    targets. induction targets as [|slot tail IH]; intros x method y args
    sGamma' vals ly cy runtime_mdef Ty Hmain Htyping Hscope Hgety Hvalue
    Hbase Hfind Hargs Hexposure Hnested Hactive_phase callee; simpl in *;
    [exact I|].
  destruct slot as [head|].
  - destruct Hnested as [Hhead Htail]. split.
    + intros Hauthority.
      eapply frozen_source_resume_phase_safe_after_safe_call_entry_from_parts;
        eauto.
      * exact ((proj1 Hexposure) head (ltac:(simpl; auto))).
      * exact ((proj1 (proj2 Hexposure)) head (ltac:(simpl; auto))).
      * eapply frozen_caller_snapshots_resume_exposures_wf_drop_head.
        exact Hexposure.
      * intros snapshot source_mode source Hsnapshot.
        eapply Hactive_phase. simpl; right; exact Hsnapshot.
    + eapply IH; eauto using
        frozen_caller_snapshots_resume_exposures_wf_drop_head.
      intros snapshot source_mode source Hsnapshot.
      eapply Hactive_phase. simpl; right; exact Hsnapshot.
  - eapply IH; eauto using
      frozen_caller_snapshots_resume_exposures_wf_drop_head.
    intros snapshot source_mode source Hsnapshot.
    eapply Hactive_phase. simpl; right; exact Hsnapshot.
Qed.

(** The target channel's directional phase relation uses the saved resume
    exposure.  Call entry therefore transports exactly the legacy pairwise
    certificate; the current-color image is reserved for pop reconstruction. *)
Lemma frozen_target_nested_phase_safe_after_safe_call_entry :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    targets x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    frozen_caller_snapshots_runtime_mutable h targets ->
    frozen_caller_snapshots_closed CT h
      (mk_watched_frame caller_authority sGamma rGamma) targets ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame caller_authority sGamma rGamma) targets ->
    frozen_target_snapshots_nested_resume_phase_safe CT h Z targets ->
    frozen_completed_colors_resume_phase_safe Z
      (independent_active_authority_colors CT h
        (mk_watched_frame caller_authority sGamma rGamma)) targets ->
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_target_snapshots_nested_resume_phase_safe CT h Z
      (advance_frozen_caller_snapshots CT h callee targets).
Proof.
  intros CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    targets x method y args sGamma' vals ly cy runtime_mdef Ty Hmain Htyping
    Hscope Hgety Hvalue Hbase Hfind Hargs _ _ Hexposure Hnested Hactive_phase
    callee.
  apply (proj2 (frozen_target_nested_phase_safe_iff_legacy CT h Z _)).
  eapply frozen_caller_snapshots_nested_resume_phase_safe_after_safe_call_entry;
    eauto.
  apply (proj1 (frozen_target_nested_phase_safe_iff_legacy CT h Z _)).
  exact Hnested.
Qed.

(** The freshly pushed target head represents the caller's latent RDM
    authority.  Under mutable caller authority that exposure is contained in
    independent active authority, so the pre-call phase certificate classifies
    every overlap with an older target. *)
Lemma private_nested_target_target_exposure_phase_safe_at_call_entry :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    snapshots target_sources x method y args sGamma' vals ly cy runtime_mdef
    Ty,
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming h ->
    (caller_authority = Mut_r \/
     exists mode root,
       authority_mode_dangerous mode /\
       In authority_flow_state
         (executing_authority_color_set CT h
           (mk_watched_frame caller_authority sGamma rGamma) incoming)
         (mode, root) /\
       typed_root RDM sGamma rGamma root) ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame caller_authority sGamma rGamma) target_sources ->
    frozen_completed_colors_resume_phase_safe Z
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) incoming)
      target_sources ->
    frozen_completed_colors_resume_phase_safe Z
      (independent_active_authority_colors CT h
        (mk_watched_frame caller_authority sGamma rGamma)) target_sources ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    let caller := mk_watched_frame caller_authority sGamma rGamma in
    let caller_colors := executing_authority_color_set CT h caller incoming in
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_completed_colors_resume_phase_safe Z
      (private_nested_frozen_call_head CT h caller callee caller_colors
        snapshots target_sources).(frozen_snapshot_current_resume_exposure)
      (advance_frozen_caller_snapshots CT h callee target_sources).
Proof.
  intros CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    snapshots target_sources x method y args sGamma' vals ly cy runtime_mdef
    Ty Hmain Hactivation Htarget_exposure Hcompleted_phase Hactive_phase
    Htyping Hscope Hgety Hvalue Hbase Hfind Hargs caller caller_colors callee.
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hsound : authority_context_sound h rGamma caller_authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
  intros new_target source_mode source Hnew Hsource_mode Hsource Hroot.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_target|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in Hroot.
  have Hlift_phase_safe :
      ((exists phase_mode,
          authority_mode_dangerous phase_mode /\
          In authority_flow_state old_target.(frozen_snapshot_phase_incoming)
            (phase_mode, source)) \/
       frozen_snapshot_resume_exposure_avoids Z old_target) ->
      ((exists phase_mode,
          authority_mode_dangerous phase_mode /\
          In authority_flow_state old_target.(frozen_snapshot_phase_incoming)
            (phase_mode, source)) \/
       frozen_snapshot_resume_exposure_avoids Z
         (advance_frozen_caller_snapshot CT h callee old_target)).
  { intros [[phase_mode [Hphase_mode Hphase]] | Hold_safe].
    - left. exists phase_mode. split; assumption.
    - right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
      have Hcallee_target : In authority_flow_state
          (executing_authority_color_set CT h callee
            (executing_authority_color_set CT h caller
              old_target.(frozen_snapshot_current_resume_exposure)))
          (exposure_mode, target).
      { destruct Htarget as [seed [Hseed Hpath]]. exists seed. split.
        - left. apply executing_authority_color_set_contains_incoming.
          exact Hseed.
        - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
      destruct (executing_authority_colors_enter_call_covered CT
        caller_authority sGamma mt rGamma h x method y args sGamma' vals ly
        cy runtime_mdef Ty
        old_target.(frozen_snapshot_current_resume_exposure) Hwf Hsound
        ((proj1 Htarget_exposure) old_target Hold) Htyping Hscope Hgety
        Hvalue Hbase Hfind Hargs exposure_mode target Hexposure_mode
        Hcallee_target) as
        [caller_target_mode [Hcaller_target_mode Hcaller_target]].
      destruct
        (executing_with_frozen_incoming_dangerous_covered_by_old_or_active
          CT h caller old_target.(frozen_snapshot_current_resume_exposure)
          caller_target_mode target
          ((proj1 (proj2 Htarget_exposure)) old_target Hold)
          Hcaller_target_mode Hcaller_target) as
        [[old_target_mode [Hold_target_mode Hold_target]] |
         [active_target_mode [Hactive_target_mode Hactive_target]]].
      + exact (Hold_safe old_target_mode target Hold_target_mode Hold_target
          Hprotected).
      + eapply (proj1 (proj2 (proj2 (proj2 Hmain))));
          [exact Hactive_target_mode| |exact Hprotected].
        eapply independent_active_authority_colors_in_executing.
        exact Hactive_target. }
  unfold private_nested_frozen_call_head, nested_frozen_call_head in Hsource.
  simpl in Hsource.
  have Hcallee_source : In authority_flow_state
      (executing_authority_color_set CT h callee
        (executing_authority_color_set CT h caller
          (frame_resume_exposure_colors CT h caller)))
      (source_mode, source).
  { destruct Hsource as [seed [Hseed Hpath]]. exists seed. split.
    - left. apply executing_authority_color_set_contains_incoming.
      exact Hseed.
    - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
  destruct (executing_authority_colors_enter_call_covered CT
    caller_authority sGamma mt rGamma h x method y args sGamma' vals ly cy
    runtime_mdef Ty (frame_resume_exposure_colors CT h caller) Hwf Hsound
    (frame_resume_exposure_colors_runtime_mutable CT h caller Hwf) Htyping
    Hscope Hgety Hvalue Hbase Hfind Hargs source_mode source Hsource_mode
    Hcallee_source) as [caller_mode [Hcaller_mode Hcaller_source]].
  destruct (executing_with_frozen_incoming_dangerous_covered_by_old_or_active
    CT h caller (frame_resume_exposure_colors CT h caller) caller_mode source
    (ltac:(unfold frame_resume_exposure_colors;
      apply (proj1 (frozen_caller_authority_closure_idempotent CT h caller
        (frame_resume_exposure_seeds h caller)))))
    Hcaller_mode Hcaller_source) as
    [[old_mode [Hold_mode Hold_source]] |
     [active_mode [Hactive_mode Hactive_source]]].
  - apply Hlift_phase_safe.
    destruct Hactivation as [Hauthority | [trigger_mode [trigger
      [Htrigger_mode [Htrigger_color Htrigger_root]]]]].
    + eapply Hactive_phase; eauto.
      eapply frame_resume_exposure_colors_in_independent_active;
        [exact Hauthority|exact Hold_source].
    + eapply Hcompleted_phase; eauto.
      eapply frame_resume_exposure_colors_in_executing_from_dangerous_rdm_root
        with (source_mode := trigger_mode) (source := trigger); eauto.
  - apply Hlift_phase_safe. eapply Hactive_phase; eauto.
Qed.

Lemma private_target_exposures_support_resume_phase_after_safe_call_entry :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    targets resumes x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame caller_authority sGamma rGamma) targets ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame caller_authority sGamma rGamma) resumes ->
    private_target_exposures_support_resume_phase Z targets resumes ->
    frozen_completed_colors_resume_phase_safe Z
      (independent_active_authority_colors CT h
        (mk_watched_frame caller_authority sGamma rGamma)) resumes ->
    let caller := mk_watched_frame caller_authority sGamma rGamma in
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    private_target_exposures_support_resume_phase Z
      (advance_frozen_caller_snapshots CT h callee targets)
      (advance_frozen_caller_snapshots CT h callee resumes).
Proof.
  intros CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    targets. induction targets as [|target target_tail IH]; intros resumes x
    method y args sGamma' vals ly cy runtime_mdef Ty Hmain Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs Htarget_exposure Hresume_exposure Hcross
    Hactive_phase caller callee.
  - destruct resumes; simpl in *; [exact I|exact Hcross].
  - destruct resumes as [|resume resume_tail].
    + destruct target; exact Hcross.
    + simpl in *. destruct target as [target|].
      * destruct Hcross as [Hhead Htail]. split.
        -- eapply
             frozen_source_resume_phase_safe_after_safe_call_entry_from_parts;
             eauto.
           ++ exact ((proj1 Htarget_exposure) target (ltac:(simpl; auto))).
           ++ exact ((proj1 (proj2 Htarget_exposure)) target
                (ltac:(simpl; auto))).
           ++ eapply frozen_caller_snapshots_resume_exposures_wf_drop_head.
              exact Hresume_exposure.
           ++ intros snapshot source_mode source Hsnapshot.
              eapply Hactive_phase. simpl; right; exact Hsnapshot.
        -- eapply IH; eauto using
             frozen_caller_snapshots_resume_exposures_wf_drop_head.
           intros snapshot source_mode source Hsnapshot.
           eapply Hactive_phase. simpl; right; exact Hsnapshot.
      * eapply IH; eauto using
          frozen_caller_snapshots_resume_exposures_wf_drop_head.
        intros snapshot source_mode source Hsnapshot.
        eapply Hactive_phase. simpl; right; exact Hsnapshot.
Qed.

Lemma private_nested_target_resume_exposure_phase_safe_at_call_entry :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    snapshots target_sources resumes x method y args sGamma' vals ly cy
    runtime_mdef Ty,
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming h ->
    frozen_caller_snapshots_aligned snapshots stack ->
    private_resume_witnesses_cover_snapshots Z resumes snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame caller_authority sGamma rGamma) resumes ->
    frozen_caller_snapshots_before_boundaries resumes stack ->
    private_resume_witness_temporal_state CT h Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack resumes ->
    frozen_completed_colors_resume_phase_safe Z
      (independent_active_authority_colors CT h
        (mk_watched_frame caller_authority sGamma rGamma)) resumes ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    let caller := mk_watched_frame caller_authority sGamma rGamma in
    let caller_colors := executing_authority_color_set CT h caller incoming in
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_completed_colors_resume_phase_safe Z
      (private_nested_frozen_call_head CT h caller callee caller_colors
        snapshots target_sources).(frozen_snapshot_current_resume_exposure)
      (advance_frozen_caller_snapshots CT h callee resumes).
Proof.
  intros CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    snapshots target_sources resumes x method y args sGamma' vals ly cy
    runtime_mdef Ty Hmain Haligned Hcover Hresume_exposure Hbefore Htemporal
    Hactive_phase Htyping Hscope Hgety Hvalue Hbase Hfind Hargs caller
    caller_colors callee.
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hsound : authority_context_sound h rGamma caller_authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
  have Hseparated := proj1 (proj2 (proj2 (proj2 Hmain))).
  have Hresume_aligned : frozen_caller_snapshots_aligned resumes stack.
  { unfold frozen_caller_snapshots_aligned in *.
    rewrite (private_resume_witnesses_cover_snapshots_length Z resumes
      snapshots Hcover). exact Haligned. }
  have Hprospective := proj1 (proj2 (proj2 (proj2 Htemporal))).
  intros new_resume source_mode source Hnew Hsource_mode Hsource Hroot.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_resume|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in Hroot.
  have Hlift_phase_safe :
      ((exists phase_mode,
          authority_mode_dangerous phase_mode /\
          In authority_flow_state old_resume.(frozen_snapshot_phase_incoming)
            (phase_mode, source)) \/
       frozen_snapshot_resume_exposure_avoids Z old_resume) ->
      ((exists phase_mode,
          authority_mode_dangerous phase_mode /\
          In authority_flow_state old_resume.(frozen_snapshot_phase_incoming)
            (phase_mode, source)) \/
       frozen_snapshot_resume_exposure_avoids Z
         (advance_frozen_caller_snapshot CT h callee old_resume)).
  { intros [[phase_mode [Hphase_mode Hphase]] | Hold_safe].
    - left. exists phase_mode. split; assumption.
    - right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
      have Hcallee_target : In authority_flow_state
          (executing_authority_color_set CT h callee
            (executing_authority_color_set CT h caller
              old_resume.(frozen_snapshot_current_resume_exposure)))
          (exposure_mode, target).
      { destruct Htarget as [seed [Hseed Hpath]]. exists seed. split.
        - left. apply executing_authority_color_set_contains_incoming.
          exact Hseed.
        - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
      destruct (executing_authority_colors_enter_call_covered CT
        caller_authority sGamma mt rGamma h x method y args sGamma' vals ly
        cy runtime_mdef Ty
        old_resume.(frozen_snapshot_current_resume_exposure) Hwf Hsound
        ((proj1 Hresume_exposure) old_resume Hold) Htyping Hscope Hgety
        Hvalue Hbase Hfind Hargs exposure_mode target Hexposure_mode
        Hcallee_target) as
        [caller_target_mode [Hcaller_target_mode Hcaller_target]].
      destruct
        (executing_with_frozen_incoming_dangerous_covered_by_old_or_active
          CT h caller old_resume.(frozen_snapshot_current_resume_exposure)
          caller_target_mode target
          ((proj1 (proj2 Hresume_exposure)) old_resume Hold)
          Hcaller_target_mode Hcaller_target) as
        [[old_target_mode [Hold_target_mode Hold_target]] |
         [active_target_mode [Hactive_target_mode Hactive_target]]].
      + exact (Hold_safe old_target_mode target Hold_target_mode Hold_target
          Hprotected).
      + eapply Hseparated; [exact Hactive_target_mode| |exact Hprotected].
        eapply independent_active_authority_colors_in_executing.
        exact Hactive_target. }
  unfold private_nested_frozen_call_head, nested_frozen_call_head in Hsource.
  simpl in Hsource.
  have Hcallee_source : In authority_flow_state
      (executing_authority_color_set CT h callee
        (executing_authority_color_set CT h caller
          (frame_resume_exposure_colors CT h caller)))
      (source_mode, source).
  { destruct Hsource as [seed [Hseed Hpath]]. exists seed. split.
    - left. apply executing_authority_color_set_contains_incoming.
      exact Hseed.
    - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
  destruct (executing_authority_colors_enter_call_covered CT
    caller_authority sGamma mt rGamma h x method y args sGamma' vals ly cy
    runtime_mdef Ty (frame_resume_exposure_colors CT h caller) Hwf Hsound
    (frame_resume_exposure_colors_runtime_mutable CT h caller Hwf) Htyping
    Hscope Hgety Hvalue Hbase Hfind Hargs source_mode source Hsource_mode
    Hcallee_source) as [caller_mode [Hcaller_mode Hcaller_source]].
  destruct (executing_with_frozen_incoming_dangerous_covered_by_old_or_active
    CT h caller (frame_resume_exposure_colors CT h caller) caller_mode source
    (ltac:(unfold frame_resume_exposure_colors;
      apply (proj1 (frozen_caller_authority_closure_idempotent CT h caller
        (frame_resume_exposure_seeds h caller)))))
    Hcaller_mode Hcaller_source) as
    [[old_mode [Hold_mode Hold_source]] |
     [active_mode [Hactive_mode Hactive_source]]].
  - exfalso.
    unfold frame_resume_exposure_colors in Hold_source.
    destruct Hold_source as [seed [Hseed Hpath]].
    destruct Hseed as [root [Hrdm [Hruntime Heq]]]. subst seed.
    eapply active_prospective_component_disjoint_frozen_resume_root with
      (snapshots := resumes) (stack := stack) (older := old_resume)
      (root := root) (target := source); eauto.
    split.
    + right. split; assumption.
    + have Hprospective_path := frozen_caller_connected_as_prospective CT h
        caller (FlowProspective, root) (old_mode, source) Hpath.
      simpl in Hprospective_path. exact Hprospective_path.
  - apply Hlift_phase_safe.
    exact (Hactive_phase old_resume active_mode source Hold Hactive_mode
      Hactive_source Hroot).
Qed.
