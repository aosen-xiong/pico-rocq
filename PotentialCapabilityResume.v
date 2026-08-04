Require Import Syntax Notations Helpers Typing Subtyping Bigstep.
Require Import ViewpointAdaptation Properties Preservation ReadonlyHelper.
Require Import Reachability MutableCapability ComponentColoring.
Require Import ExecutionConfinement ProtectionHistory ForwardCapabilityHistory.
Require Import AuthorityCapability AuthorityHistory WatchedFrames
  LiveCapabilityStack.
Require Export PotentialCapabilityPrivate.
From Stdlib Require Import List Sets.Ensembles Relations.Relation_Operators
  Program.Equality.
Import ListNotations.

(** Return-safety and policy-pop helpers accept either completed-callee
    provenance or the retained witness's certified-safe resume exposure. *)

(** The color set constructed at the pop transition.  Completed callee
    colors cross the return boundary only after being demoted; the caller's
    saved incoming authority is restored independently, and caller-owned
    capabilities are powered in the resumed phase.  Thus no return edge is
    present while the callee executes. *)

(** A frame that resumes after a call does not acquire authority merely
    because the returned value is installed in a fresh [RDM] destination.
    For a mutable caller every [RDM] root is independently powered and is
    therefore an admissible join target.  For an immutable caller, only an
    [RDM] root that was already present in the saved pre-call frame is an
    admissible target.  Notice that this restriction is directional: the
    returned root may be the source of a neutral component-identification
    step, but authority from an old root cannot be projected into it.

    This is proof-local call-pop structure.  It neither changes dynamic
    dispatch nor adds a premise to the public preservation theorem. *)
Definition resumed_frame_join_target
  (eligible : Ensemble Loc) (caller : watched_frame)
  (location : Loc) : Prop :=
  caller.(frame_authority) = Mut_r \/
  In Loc eligible location.

Lemma resumed_frame_join_target_mutable :
  forall eligible caller location,
    caller.(frame_authority) = Mut_r ->
    resumed_frame_join_target eligible caller location.
Proof.
  intros eligible caller location Hauthority. left. exact Hauthority.
Qed.

(** Location-level projection of every resumed-frame step other than an RDM
    root join.  Keeping this relation independent of authority modes makes
    the allocation-age argument below reusable for dangerous and neutral
    paths alike. *)
Inductive resumed_authority_nonjoin_location_step
  (CT : class_table) (h : heap) : Loc -> Loc -> Prop :=
| resumed_nonjoin_location_retained : forall left right,
    retained_mut_edge CT h left right ->
    resumed_authority_nonjoin_location_step CT h left right
| resumed_nonjoin_location_mutable_forward : forall left right,
    mutable_edge CT h left right ->
    resumed_authority_nonjoin_location_step CT h left right
| resumed_nonjoin_location_mutable_backward : forall left right,
    mutable_edge CT h right left ->
    resumed_authority_nonjoin_location_step CT h left right
| resumed_nonjoin_location_refl : forall location,
    resumed_authority_nonjoin_location_step CT h location location.

Inductive resumed_authority_frame_step
  (CT : class_table) (h : heap)
  (eligible : Ensemble Loc) (caller : watched_frame) :
  authority_flow_state -> authority_flow_state -> Prop :=
| resumed_authority_retained : forall left right,
    retained_mut_edge CT h left right ->
    resumed_authority_frame_step CT h eligible caller
      (FlowPowered, left) (FlowPowered, right)
| resumed_authority_prospective_retained : forall left right,
    retained_mut_edge CT h left right ->
    resumed_authority_frame_step CT h eligible caller
      (FlowProspective, left) (FlowProspective, right)
| resumed_authority_prospective_rdm_backward : forall left right,
    mutable_edge CT h right left ->
    resumed_authority_frame_step CT h eligible caller
      (FlowProspective, left) (FlowProspective, right)
| resumed_authority_reverse_rdm : forall left right,
    mutable_edge CT h right left ->
    resumed_authority_frame_step CT h eligible caller
      (FlowPowered, left) (FlowProspective, right)
| resumed_authority_neutral_rdm_forward : forall left right,
    mutable_edge CT h left right ->
    resumed_authority_frame_step CT h eligible caller
      (FlowNeutral, left) (FlowNeutral, right)
| resumed_authority_neutral_rdm_backward : forall left right,
    mutable_edge CT h right left ->
    resumed_authority_frame_step CT h eligible caller
      (FlowNeutral, left) (FlowNeutral, right)
| resumed_authority_powered_frame_join : forall left right,
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    resumed_frame_join_target eligible caller left ->
    resumed_frame_join_target eligible caller right ->
    resumed_authority_frame_step CT h eligible caller
      (FlowPowered, left) (FlowProspective, right)
| resumed_authority_prospective_frame_join : forall left right,
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    resumed_frame_join_target eligible caller left ->
    resumed_frame_join_target eligible caller right ->
    resumed_authority_frame_step CT h eligible caller
      (FlowProspective, left) (FlowProspective, right)
| resumed_authority_neutral_frame_join : forall left right,
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    resumed_frame_join_target eligible caller right ->
    resumed_authority_frame_step CT h eligible caller
      (FlowNeutral, left) (FlowNeutral, right)
| resumed_authority_forget : forall location,
    resumed_authority_frame_step CT h eligible caller
      (FlowPowered, location) (FlowNeutral, location)
| resumed_authority_prospective_forget : forall location,
    resumed_authority_frame_step CT h eligible caller
      (FlowProspective, location) (FlowNeutral, location)
| resumed_authority_mark_prospective : forall location,
    resumed_authority_frame_step CT h eligible caller
      (FlowPowered, location) (FlowProspective, location)
| resumed_authority_promote : forall location,
    frame_owned_location CT h caller location ->
    resumed_authority_frame_step CT h eligible caller
      (FlowNeutral, location) (FlowPowered, location).

Definition resumed_authority_frame_connected
  (CT : class_table) (h : heap)
  (eligible : Ensemble Loc) (caller : watched_frame) :
  authority_flow_state -> authority_flow_state -> Prop :=
  clos_refl_trans authority_flow_state
    (resumed_authority_frame_step CT h eligible caller).

Definition resumed_authority_frame_closure
  (CT : class_table) (h : heap)
  (eligible : Ensemble Loc) (caller : watched_frame)
  (seeds : Ensemble authority_flow_state) :
  Ensemble authority_flow_state :=
  fun state => exists seed,
    In authority_flow_state seeds seed /\
    resumed_authority_frame_connected CT h eligible caller seed state.

Lemma resumed_authority_frame_step_is_phased :
  forall CT h saved caller source target,
    resumed_authority_frame_step CT h saved caller source target ->
    phased_authority_frame_step CT h caller source target.
Proof.
  intros CT h saved caller source target Hstep.
  inversion Hstep; subst.
  - apply phased_authority_retained. exact H.
  - apply phased_authority_prospective_retained. exact H.
  - apply phased_authority_prospective_rdm_backward. exact H.
  - apply phased_authority_reverse_rdm. exact H.
  - apply phased_authority_neutral_rdm_forward. exact H.
  - apply phased_authority_neutral_rdm_backward. exact H.
  - eapply phased_authority_powered_frame_join; eauto.
  - eapply phased_authority_prospective_frame_join; eauto.
  - eapply phased_authority_neutral_frame_join; eauto.
  - apply phased_authority_forget.
  - apply phased_authority_prospective_forget.
  - apply phased_authority_mark_prospective.
  - apply phased_authority_promote. exact H.
Qed.

Lemma resumed_authority_frame_connected_is_phased :
  forall CT h saved caller source target,
    resumed_authority_frame_connected CT h saved caller source target ->
    phased_authority_frame_connected CT h caller source target.
Proof.
  intros CT h saved caller source target Hconnected.
  induction Hconnected.
  - apply rt_step. eapply resumed_authority_frame_step_is_phased. exact H.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

(** Persistent phase closure for a frame whose admissible RDM join targets
    were frozen in [eligible].  This ensemble is ghost state; neither
    evaluation nor lookup consults it. *)
Definition executing_resumed_authority_color_set
  (CT : class_table) (h : heap) (eligible : Ensemble Loc)
  (active : watched_frame)
  (incoming : Ensemble authority_flow_state) :
  Ensemble authority_flow_state :=
  resumed_authority_frame_closure CT h eligible active
    (Union authority_flow_state incoming
      (phased_frame_powered_seeds CT h active)).

(** Dangerous-only projection of the resumed graph.  Neutral bookkeeping is
    intentionally absent.  A later promotion restarts authority at a
    caller-owned anchor, so a dangerous suffix never needs to attribute
    authority to an earlier neutral path. *)
Inductive resumed_frozen_authority_step
  (CT : class_table) (h : heap) (eligible : Ensemble Loc)
  (caller : watched_frame) :
  authority_flow_state -> authority_flow_state -> Prop :=
| resumed_frozen_nonjoin : forall source target,
    frozen_caller_authority_nonjoin_step CT h source target ->
    resumed_frozen_authority_step CT h eligible caller source target
| resumed_frozen_powered_join : forall left right,
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    resumed_frame_join_target eligible caller left ->
    resumed_frame_join_target eligible caller right ->
    resumed_frozen_authority_step CT h eligible caller
      (FlowPowered, left) (FlowProspective, right)
| resumed_frozen_prospective_join : forall left right,
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    resumed_frame_join_target eligible caller left ->
    resumed_frame_join_target eligible caller right ->
    resumed_frozen_authority_step CT h eligible caller
      (FlowProspective, left) (FlowProspective, right).

Definition resumed_frozen_authority_connected
  (CT : class_table) (h : heap) (eligible : Ensemble Loc)
  (caller : watched_frame) :
  authority_flow_state -> authority_flow_state -> Prop :=
  clos_refl_trans authority_flow_state
    (resumed_frozen_authority_step CT h eligible caller).

Inductive resumed_dangerous_color_derivation
  (CT : class_table) (h : heap) (eligible : Ensemble Loc)
  (caller : watched_frame) (incoming : Ensemble authority_flow_state) :
  authority_flow_state -> Prop :=
| resumed_dangerous_from_incoming : forall state,
    authority_mode_dangerous (fst state) ->
    In authority_flow_state incoming state ->
    resumed_dangerous_color_derivation CT h eligible caller incoming state
| resumed_dangerous_from_owned : forall location,
    frame_owned_location CT h caller location ->
    resumed_dangerous_color_derivation CT h eligible caller incoming
      (FlowPowered, location)
| resumed_dangerous_by_frozen_step : forall source target,
    resumed_dangerous_color_derivation CT h eligible caller incoming source ->
    resumed_frozen_authority_step CT h eligible caller source target ->
    resumed_dangerous_color_derivation CT h eligible caller incoming target.

Definition executing_resumed_authority_colors_separated
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (eligible : Ensemble Loc) (active : watched_frame)
  (incoming : Ensemble authority_flow_state) : Prop :=
  forall mode protected,
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_resumed_authority_color_set CT h eligible active incoming)
      (mode, protected) ->
    ~ In Loc Z protected.

Lemma executing_resumed_authority_color_set_in_phased :
  forall CT h eligible active incoming,
    Included authority_flow_state
      (executing_resumed_authority_color_set CT h eligible active incoming)
      (executing_authority_color_set CT h active incoming).
Proof.
  intros CT h eligible active incoming state [seed [Hseed Hpath]].
  exists seed. split; [exact Hseed|].
  eapply resumed_authority_frame_connected_is_phased. exact Hpath.
Qed.

(** Policy-indexed form of the internal pop obligation.  It is the exact
    interface required by an immutable resumed frame: paths quantify only
    over joins whose targets remain eligible in that frame's persistent
    policy. *)
Definition executing_resumed_authority_call_pop_safe
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (callee : watched_frame)
  (callee_incoming : Ensemble authority_flow_state)
  (eligible : Ensemble Loc)
  (caller : watched_frame)
  (caller_incoming : Ensemble authority_flow_state) : Prop :=
  forall mode location,
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_resumed_authority_color_set CT h eligible caller
        caller_incoming) (mode, location) ->
    (exists callee_mode,
      authority_mode_dangerous callee_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h callee callee_incoming)
        (callee_mode, location)) \/
    ~ In Loc Z location.

(** Stack discipline for the persistent target policy.  Every active frame
    has one set of eligible RDM target locations; suspension pushes that set
    unchanged, and return restores it unchanged.  A callee starts with the
    RDM roots present in its entry environment. *)
Record private_frame_join_policies : Type := mk_private_frame_join_policies {
  active_frame_join_targets : Ensemble Loc;
  suspended_frame_join_targets : list (Ensemble Loc);
  (** Lightweight caller summaries, one per operational boundary.  Unlike
      the exceptional witnesses below, these are not required to satisfy the
      callee-side freshness partition; they exist solely to classify saved
      resume targets at an untracked [None] pop. *)
  suspended_frame_target_witnesses : list frozen_caller_snapshot_slot;
  suspended_frame_resume_witnesses : list frozen_caller_snapshot_slot
}.

(** Color-coverage component of the policy witness relation.  A separate
    private relation must carry the pairwise resume-safety certificate; set
    inclusion alone is intentionally not described as sufficient here. *)
Definition private_resume_witness_covers_tail
  (Z : Ensemble Loc) (witness : frozen_caller_snapshot_slot)
  (tail : list frozen_caller_snapshot_slot) : Prop :=
  match witness with
  | None => forall older, List.In (Some older) tail -> False
  | Some head =>
      forall older,
        List.In (Some older) tail ->
        Included authority_flow_state
          older.(frozen_snapshot_current_colors)
          head.(frozen_snapshot_current_colors)
  end.

(** Pointwise stack relation between phase-current policy witnesses and the
    ordinary snapshot slots.  A witness at the current index covers the
    strict snapshot tail because it denotes the caller suspended at that
    boundary. *)
Fixpoint private_resume_witnesses_cover_snapshots
  (Z : Ensemble Loc) (witnesses snapshots : list frozen_caller_snapshot_slot)
  : Prop :=
  match witnesses, snapshots with
  | [], [] => True
  | witness :: witness_tail, None :: snapshot_tail =>
      private_resume_witness_covers_tail Z witness
        snapshot_tail /\
      private_resume_witnesses_cover_snapshots Z witness_tail snapshot_tail
  | _, _ => False
  end.

(** Policy witnesses use the same entry-or-safe rule as completed colors.
    Requiring the stronger ordinary-snapshot [resume_roots_safe] property
    here would incorrectly reject a resumed color that was already present
    at the older caller's entry.  Such an entry color is legitimate
    historical provenance; only a color with neither entry provenance nor a
    safe exposure is problematic. *)
Definition frozen_caller_snapshots_active_resume_safe
  (CT : class_table) (h : heap) (Z : Ensemble Loc) (active : watched_frame)
  (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  frozen_completed_colors_resume_safe Z
    (independent_active_authority_colors CT h active) snapshots.

(** Entry-aware variant of the generic classified-advance lemma.  The
    exceptional source may itself have valid entry provenance; in that case
    the nested obligation is already discharged and no absolute separation
    premise is needed for that source. *)
Lemma frozen_caller_snapshots_nested_resume_safe_after_classified_advance_entry :
  forall CT new_h Z new_active snapshots exceptional,
    frozen_caller_snapshots_nested_resume_safe Z snapshots ->
    (forall snapshot active_mode source,
      List.In (Some snapshot) snapshots ->
      authority_mode_dangerous active_mode ->
      In authority_flow_state exceptional (active_mode, source) ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
      (exists entry_mode,
        authority_mode_dangerous entry_mode /\
        In authority_flow_state snapshot.(frozen_snapshot_entry_colors)
          (entry_mode, source)) \/
      (forall exposure_mode target,
        authority_mode_dangerous exposure_mode ->
        In authority_flow_state
          snapshot.(frozen_snapshot_current_resume_exposure)
          (exposure_mode, target) ->
        ~ In Loc Z target)) ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state exceptional (active_mode, location) ->
      ~ In Loc Z location) ->
    (forall snapshot older mode location,
      List.In (Some snapshot) snapshots ->
      List.In (Some older) snapshots ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (frozen_caller_authority_closure CT new_h new_active
          snapshot.(frozen_snapshot_current_colors)) (mode, location) ->
      In Loc older.(frozen_snapshot_resume_rdm_roots) location ->
      (exists old_mode,
        authority_mode_dangerous old_mode /\
        In authority_flow_state snapshot.(frozen_snapshot_current_colors)
          (old_mode, location)) \/
      (exists active_mode,
        authority_mode_dangerous active_mode /\
        In authority_flow_state exceptional (active_mode, location))) ->
    (forall snapshot mode location,
      List.In (Some snapshot) snapshots ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (frozen_caller_authority_closure CT new_h new_active
          snapshot.(frozen_snapshot_current_resume_exposure))
        (mode, location) ->
      In Loc Z location ->
      (exists old_mode,
        authority_mode_dangerous old_mode /\
        In authority_flow_state
          snapshot.(frozen_snapshot_current_resume_exposure)
          (old_mode, location)) \/
      (exists active_mode,
        authority_mode_dangerous active_mode /\
        In authority_flow_state exceptional (active_mode, location))) ->
    frozen_caller_snapshots_nested_resume_safe Z
      (advance_frozen_caller_snapshots CT new_h new_active snapshots).
Proof.
  intros CT new_h Z new_active snapshots exceptional Hnested Hresume
    Hactive_safe Hclassify_color Hclassify_exposure.
  induction snapshots as [|slot tail IH]; simpl in *; [exact I|].
  destruct slot as [head|].
  - destruct Hnested as [Hhead Htail]. split.
    + intros new_older Hnew_older.
      unfold advance_frozen_caller_snapshots in Hnew_older.
      apply in_map_iff in Hnew_older.
      destruct Hnew_older as [old_slot [Heq Hold_slot]].
      destruct old_slot as [old_older|]; simpl in Heq; [|discriminate].
      injection Heq as <-.
      intros source_mode source Hsource_mode Hsource Hsource_root.
      destruct (Hclassify_color head old_older source_mode source
        (ltac:(simpl; auto)) (ltac:(simpl; right; exact Hold_slot))
        Hsource_mode Hsource Hsource_root) as
        [[old_source_mode [Hold_source_mode Hold_source]] |
         [active_source_mode [Hactive_source_mode Hactive_source]]].
      * destruct (Hhead old_older Hold_slot old_source_mode source
          Hold_source_mode Hold_source Hsource_root) as
          [[entry_mode [Hentry_mode Hentry]] | Hold_safe].
        -- left. exists entry_mode. split; assumption.
        -- right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
           destruct (Hclassify_exposure old_older exposure_mode target
             (ltac:(simpl; right; exact Hold_slot)) Hexposure_mode Htarget
             Hprotected) as
             [[old_exposure_mode [Hold_exposure_mode Hold_target]] |
              [active_target_mode [Hactive_target_mode Hactive_target]]].
           ++ eapply Hold_safe; eauto.
           ++ eapply Hactive_safe; eauto.
      * destruct (Hresume old_older active_source_mode source
          (ltac:(simpl; right; exact Hold_slot)) Hactive_source_mode
          Hactive_source Hsource_root) as
          [[entry_mode [Hentry_mode Hentry]] | Hexceptional_safe].
        -- left. exists entry_mode. simpl. split; assumption.
        -- right. intros exposure_mode target Hexposure_mode Htarget
             Hprotected.
           destruct (Hclassify_exposure old_older exposure_mode target
             (ltac:(simpl; right; exact Hold_slot)) Hexposure_mode Htarget
             Hprotected) as
             [[old_exposure_mode [Hold_exposure_mode Hold_target]] |
              [active_target_mode [Hactive_target_mode Hactive_target]]].
           ++ eapply Hexceptional_safe; eauto.
           ++ eapply Hactive_safe; eauto.
    + apply IH.
      * exact Htail.
      * intros snapshot active_mode source Hsnapshot.
        eapply Hresume. simpl. right. exact Hsnapshot.
      * intros snapshot older mode location Hsnapshot Holder.
        eapply Hclassify_color.
        -- simpl. right. exact Hsnapshot.
        -- simpl. right. exact Holder.
      * intros snapshot mode location Hsnapshot.
        eapply Hclassify_exposure. simpl. right. exact Hsnapshot.
  - apply IH.
    + exact Hnested.
    + intros snapshot active_mode source Hsnapshot.
      eapply Hresume. simpl. right. exact Hsnapshot.
    + intros snapshot older mode location Hsnapshot Holder.
      eapply Hclassify_color.
      * simpl. right. exact Hsnapshot.
      * simpl. right. exact Holder.
    + intros snapshot mode location Hsnapshot.
      eapply Hclassify_exposure. simpl. right. exact Hsnapshot.
Qed.

(** Precise saved-target provenance.  The ordinary entry-color image of a
    policy witness is intentionally aggregate; [phase_incoming] is the exact
    executing caller color set captured at that boundary.  A completed color
    at a resume root must therefore either reflect to that exact phase or
    certify the witness's whole latent exposure as harmless. *)
Definition frozen_completed_colors_resume_phase_safe
  (Z : Ensemble Loc) (completed : Ensemble authority_flow_state)
  (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  forall snapshot source_mode source,
    List.In (Some snapshot) snapshots ->
    authority_mode_dangerous source_mode ->
    In authority_flow_state completed (source_mode, source) ->
    In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
    (exists phase_mode,
      authority_mode_dangerous phase_mode /\
      In authority_flow_state snapshot.(frozen_snapshot_phase_incoming)
        (phase_mode, source)) \/
    frozen_snapshot_resume_exposure_avoids Z snapshot.

(** Cross-channel second-order certificate.  A lightweight target exists at
    every boundary, but only a [Some] resume witness is later consumed by the
    exceptional return reconstruction.  Consequently each target exposure
    is related to the strict tail of retained resume witnesses, not to the
    target tail itself. *)
Fixpoint private_target_exposures_support_resume_phase
  (Z : Ensemble Loc) (targets resumes : list frozen_caller_snapshot_slot) :
  Prop :=
  match targets, resumes with
  | [], [] => True
  | Some target :: target_tail, _ :: resume_tail =>
      frozen_completed_colors_resume_phase_safe Z
        target.(frozen_snapshot_current_resume_exposure) resume_tail /\
      private_target_exposures_support_resume_phase Z target_tail resume_tail
  | None :: target_tail, _ :: resume_tail =>
      private_target_exposures_support_resume_phase Z target_tail resume_tail
  | _, _ => False
  end.

(** The optional exceptional witness is a refinement of the lightweight
    target witness at the same boundary.  They may carry different current
    color summaries, but their static phase metadata and their evolving
    resume exposure agree. *)
Fixpoint private_target_supports_resume_witnesses
  (targets resumes : list frozen_caller_snapshot_slot) : Prop :=
  match targets, resumes with
  | [], [] => True
  | Some target :: target_tail, Some resume :: resume_tail =>
      Same_set authority_flow_state
        resume.(frozen_snapshot_phase_incoming)
        target.(frozen_snapshot_entry_phase) /\
      Same_set Loc resume.(frozen_snapshot_resume_rdm_roots)
        target.(frozen_snapshot_resume_rdm_roots) /\
      Same_set authority_flow_state
        resume.(frozen_snapshot_entry_resume_exposure)
        target.(frozen_snapshot_entry_resume_exposure) /\
      Same_set authority_flow_state
        resume.(frozen_snapshot_current_resume_exposure)
        target.(frozen_snapshot_current_resume_exposure) /\
      private_target_supports_resume_witnesses target_tail resume_tail
  | Some _ :: target_tail, None :: resume_tail =>
      private_target_supports_resume_witnesses target_tail resume_tail
  | None :: target_tail, None :: resume_tail =>
      private_target_supports_resume_witnesses target_tail resume_tail
  | _, _ => False
  end.

(** The target channel may remember activations that the exact resume phase
    intentionally does not.  This pairwise certificate records why such a
    historical target color is nevertheless safe at the corresponding
    resume root. *)
Fixpoint private_target_history_supports_resume_phase
  (Z : Ensemble Loc) (targets resumes : list frozen_caller_snapshot_slot) :
  Prop :=
  match targets, resumes with
  | [], [] => True
  | Some target :: target_tail, Some resume :: resume_tail =>
      (forall source_mode source,
        authority_mode_dangerous source_mode ->
        In authority_flow_state target.(frozen_snapshot_phase_incoming)
          (source_mode, source) ->
        In Loc resume.(frozen_snapshot_resume_rdm_roots) source ->
        (exists phase_mode,
          authority_mode_dangerous phase_mode /\
          In authority_flow_state resume.(frozen_snapshot_phase_incoming)
            (phase_mode, source)) \/
        frozen_snapshot_resume_exposure_avoids Z resume) /\
      private_target_history_supports_resume_phase Z target_tail resume_tail
  | Some _ :: target_tail, None :: resume_tail =>
      private_target_history_supports_resume_phase Z target_tail resume_tail
  | None :: target_tail, None :: resume_tail =>
      private_target_history_supports_resume_phase Z target_tail resume_tail
  | _, _ => False
  end.

(** Lightweight saved-target summaries.  These are present at every call
    boundary, including an operational [None] boundary.  They intentionally
    omit the strong callee-side freshness partition required only by the
    exceptional immutable-RDM/mutable-return witness. *)
Definition private_target_witness_stack_structural
  (CT : class_table) (h : heap) (active : watched_frame)
  (witnesses : list frozen_caller_snapshot_slot) : Prop :=
  True /\
  frozen_caller_snapshots_runtime_mutable h witnesses /\
  frozen_caller_snapshots_dangerous witnesses /\
  frozen_caller_snapshots_closed CT h active witnesses /\
  frozen_caller_snapshots_resume_roots_in_heap h witnesses /\
  frozen_caller_snapshots_resume_exposures_wf CT h active witnesses /\
  frozen_caller_snapshots_retain_entry witnesses /\
  frozen_caller_snapshots_cover_phase_incoming witnesses.

Definition private_target_witness_temporal_state
  (CT : class_table) (h : heap) (Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary)
  (targets : list frozen_caller_snapshot_slot) : Prop :=
  frozen_snapshot_boundaries_after_cutoff cutoff targets stack.

Lemma frozen_caller_snapshots_nested_resume_safe_after_new :
  forall CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qreceiver qruntime authority snapshots,
    wf_r_config CT sGamma rGamma h ->
    wf_r_config CT sGamma'
      (update_r_env_value rGamma x (Iot (dom h)))
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) ->
    authority_context_sound h rGamma authority ->
    authority_context_sound
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (update_r_env_value rGamma x (Iot (dom h))) authority ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    vpa_mutability_object_creation qreceiver qc = qruntime ->
    cutoff <= dom h ->
    protected_zone_before_cutoff Z cutoff ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_closed CT h
      (mk_watched_frame authority sGamma rGamma) snapshots ->
    frozen_caller_snapshots_resume_roots_in_heap h snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame authority sGamma rGamma) snapshots ->
    frozen_caller_snapshots_nested_resume_safe Z snapshots ->
    frozen_caller_snapshots_active_resume_safe CT h Z
      (mk_watched_frame authority sGamma rGamma) snapshots ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h
          (mk_watched_frame authority sGamma rGamma))
        (active_mode, location) ->
      ~ In Loc Z location) ->
    frozen_caller_snapshots_nested_resume_safe Z
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) snapshots).
Proof.
  intros CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals qreceiver
    qruntime authority snapshots Hwf Hpost_wf Hsound Hpost_sound Htyping
    Hvals Hadapt Hcutoff Hzone Hruntime Hclosed Hroots Hexposure Hnested
    Hresume Hactive_safe.
  eapply
    frozen_caller_snapshots_nested_resume_safe_after_classified_advance_entry
    with (exceptional := independent_active_authority_colors CT h
      (mk_watched_frame authority sGamma rGamma)).
  - exact Hnested.
  - unfold frozen_caller_snapshots_active_resume_safe in Hresume.
    exact Hresume.
  - exact Hactive_safe.
  - intros snapshot older mode location Hsnapshot Holder Hmode Hcolor Hroot.
    have Hlocation_old : location < dom h by (eapply Hroots; eauto).
    have Hpost_color : In authority_flow_state
        (executing_authority_color_set CT
          (h ++ [mkObj (mkruntime_type qruntime C) vals])
          (mk_watched_frame authority sGamma'
            (update_r_env_value rGamma x (Iot (dom h))))
          snapshot.(frozen_snapshot_current_colors)) (mode, location).
    { destruct Hcolor as [seed [Hseed Hpath]]. exists seed. split.
      - left. exact Hseed.
      - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
    destruct (executing_authority_colors_after_new_covered CT sGamma mt
      rGamma h x qc C args sGamma' vals qreceiver qruntime authority
      snapshot.(frozen_snapshot_current_colors) Hwf Hpost_wf Hsound
      Hpost_sound (Hruntime snapshot Hsnapshot) Htyping Hvals Hadapt mode
      location Hmode Hpost_color Hlocation_old) as
      [old_mode [Hold_mode Hold_color]].
    exact (executing_with_frozen_incoming_dangerous_covered_by_old_or_active
      CT h (mk_watched_frame authority sGamma rGamma)
      snapshot.(frozen_snapshot_current_colors) old_mode location
      (Hclosed snapshot Hsnapshot) Hold_mode Hold_color).
  - intros snapshot mode location Hsnapshot Hmode Hcolor Hprotected.
    have Hlocation_old : location < dom h.
    { have Hbefore := Hzone location Hprotected. lia. }
    have Hpost_color : In authority_flow_state
        (executing_authority_color_set CT
          (h ++ [mkObj (mkruntime_type qruntime C) vals])
          (mk_watched_frame authority sGamma'
            (update_r_env_value rGamma x (Iot (dom h))))
          snapshot.(frozen_snapshot_current_resume_exposure))
        (mode, location).
    { destruct Hcolor as [seed [Hseed Hpath]]. exists seed. split.
      - left. exact Hseed.
      - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
    destruct (executing_authority_colors_after_new_covered CT sGamma mt
      rGamma h x qc C args sGamma' vals qreceiver qruntime authority
      snapshot.(frozen_snapshot_current_resume_exposure) Hwf Hpost_wf Hsound
      Hpost_sound ((proj1 Hexposure) snapshot Hsnapshot) Htyping Hvals Hadapt
      mode location Hmode Hpost_color Hlocation_old) as
      [old_mode [Hold_mode Hold_color]].
    exact (executing_with_frozen_incoming_dangerous_covered_by_old_or_active
      CT h (mk_watched_frame authority sGamma rGamma)
      snapshot.(frozen_snapshot_current_resume_exposure) old_mode location
      ((proj1 (proj2 Hexposure)) snapshot Hsnapshot) Hold_mode Hold_color).
Qed.

Lemma frozen_completed_colors_resume_safe_after_new :
  forall CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qreceiver qruntime authority incoming snapshots,
    wf_r_config CT sGamma rGamma h ->
    wf_r_config CT sGamma'
      (update_r_env_value rGamma x (Iot (dom h)))
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) ->
    authority_context_sound h rGamma authority ->
    authority_context_sound
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (update_r_env_value rGamma x (Iot (dom h))) authority ->
    authority_colors_runtime_mutable h incoming ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    vpa_mutability_object_creation qreceiver qc = qruntime ->
    cutoff <= dom h ->
    protected_zone_before_cutoff Z cutoff ->
    frozen_caller_snapshots_resume_roots_in_heap h snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame authority sGamma rGamma) snapshots ->
    frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h
        (mk_watched_frame authority sGamma rGamma) incoming) snapshots ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h
          (mk_watched_frame authority sGamma rGamma))
        (active_mode, location) ->
      ~ In Loc Z location) ->
    frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) incoming)
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) snapshots).
Proof.
  intros CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals qreceiver
    qruntime authority incoming snapshots Hwf Hpost_wf Hsound Hpost_sound
    Hincoming_runtime Htyping Hvals Hadapt Hcutoff Hzone Hroots Hexposure
    Hcompleted Hactive_safe new_snapshot source_mode source Hnew Hsource_mode
    Hsource Hsource_root.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  have Hsource_old : source < dom h by (eapply Hroots; eauto).
  destruct (executing_authority_colors_after_new_covered CT sGamma mt
    rGamma h x qc C args sGamma' vals qreceiver qruntime authority incoming
    Hwf Hpost_wf Hsound Hpost_sound Hincoming_runtime Htyping Hvals Hadapt
    source_mode source Hsource_mode Hsource Hsource_old) as
    [old_source_mode [Hold_source_mode Hold_source]].
  destruct (Hcompleted old_snapshot old_source_mode source Hold
    Hold_source_mode Hold_source Hsource_root) as
    [[entry_mode [Hentry_mode Hentry]] | Hsafe].
  - left. exists entry_mode. split; assumption.
  - right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
    have Htarget_old : target < dom h.
    { have Hbefore := Hzone target Hprotected. lia. }
    have Hpost_target : In authority_flow_state
        (executing_authority_color_set CT
          (h ++ [mkObj (mkruntime_type qruntime C) vals])
          (mk_watched_frame authority sGamma'
            (update_r_env_value rGamma x (Iot (dom h))))
          old_snapshot.(frozen_snapshot_current_resume_exposure))
        (exposure_mode, target).
    { destruct Htarget as [seed [Hseed Hpath]]. exists seed. split.
      - left. exact Hseed.
      - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
    destruct (executing_authority_colors_after_new_covered CT sGamma mt
      rGamma h x qc C args sGamma' vals qreceiver qruntime authority
      old_snapshot.(frozen_snapshot_current_resume_exposure) Hwf Hpost_wf
      Hsound Hpost_sound ((proj1 Hexposure) old_snapshot Hold) Htyping Hvals
      Hadapt exposure_mode target Hexposure_mode Hpost_target Htarget_old) as
      [old_target_mode [Hold_target_mode Hold_target]].
    destruct (executing_with_frozen_incoming_dangerous_covered_by_old_or_active
      CT h (mk_watched_frame authority sGamma rGamma)
      old_snapshot.(frozen_snapshot_current_resume_exposure) old_target_mode
      target ((proj1 (proj2 Hexposure)) old_snapshot Hold) Hold_target_mode
      Hold_target) as
      [[old_exposure_mode [Hold_exposure_mode Hold_exposure]] |
       [active_mode [Hactive_mode Hactive]]].
    + exact (Hsafe old_exposure_mode target Hold_exposure_mode Hold_exposure
        Hprotected).
    + exact (Hactive_safe active_mode target Hactive_mode Hactive Hprotected).
Qed.

(** The two phase-current policy images grow monotonically while a statement
    executes.  Static metadata equality alone cannot express this temporal
    fact, yet it is exactly what lets a later pop distinguish retained entry
    provenance from colors introduced by the completed callee. *)
Definition frozen_caller_snapshot_phase_images_grow
  (final initial : frozen_caller_color_snapshot) : Prop :=
  Included authority_flow_state initial.(frozen_snapshot_current_colors)
    final.(frozen_snapshot_current_colors) /\
  Included authority_flow_state
    initial.(frozen_snapshot_current_resume_exposure)
    final.(frozen_snapshot_current_resume_exposure).

Definition frozen_caller_snapshot_slot_phase_images_grow
  (final initial : frozen_caller_snapshot_slot) : Prop :=
  match final, initial with
  | Some final_snapshot, Some initial_snapshot =>
      frozen_caller_snapshot_phase_images_grow final_snapshot initial_snapshot
  | None, None => True
  | _, _ => False
  end.

Definition leave_private_frame_join_policies
  (policies : private_frame_join_policies) :
  option private_frame_join_policies :=
  match policies.(suspended_frame_join_targets),
        policies.(suspended_frame_target_witnesses),
        policies.(suspended_frame_resume_witnesses) with
  | caller_targets :: target_tail, _ :: target_witness_tail,
      _ :: witness_tail =>
      Some (mk_private_frame_join_policies caller_targets target_tail
        target_witness_tail witness_tail)
  | _, _, _ => None
  end.

Definition private_frame_join_policies_aligned
  (policies : private_frame_join_policies)
  (stack : list watched_boundary) : Prop :=
  length policies.(suspended_frame_join_targets) = length stack /\
  length policies.(suspended_frame_target_witnesses) = length stack /\
  length policies.(suspended_frame_resume_witnesses) = length stack.

(** Allocation-age invariant for the persistent target policy.  Active
    targets denote locations already present in the current heap.  Each
    suspended target set is stronger: its locations predate the exact call
    boundary at which that frame was suspended.  Consequently a result
    allocated by that call can never become eligible merely by being
    installed in the resumed frame. *)
Definition private_frame_join_targets_in_heap
  (h : heap) (targets : Ensemble Loc) : Prop :=
  forall location, In Loc targets location -> location < dom h.

Definition private_frame_join_targets_before_boundary
  (targets : Ensemble Loc) (boundary : watched_boundary) : Prop :=
  forall location,
    In Loc targets location ->
    location < boundary.(boundary_entry_cutoff).

Definition private_frame_join_policies_valid
  (h : heap) (policies : private_frame_join_policies)
  (stack : list watched_boundary) : Prop :=
  private_frame_join_targets_in_heap h
    policies.(active_frame_join_targets) /\
  Forall2 private_frame_join_targets_before_boundary
    policies.(suspended_frame_join_targets) stack.

Lemma executing_authority_colors_separated_after_call_pop :
  forall CT h Z callee callee_incoming caller caller_incoming,
    executing_authority_colors_separated CT h Z callee callee_incoming ->
    executing_authority_call_pop_safe CT h Z callee callee_incoming
      caller caller_incoming ->
    executing_authority_colors_separated CT h Z caller caller_incoming.
Proof.
  intros CT h Z callee callee_incoming caller caller_incoming
    Hcallee Hpop mode protected Hmode Hcaller Hprotected.
  destruct (Hpop mode protected Hmode Hcaller) as
    [[callee_mode [Hcallee_mode Hcallee_color]] | Houtside].
  - exact (Hcallee callee_mode protected Hcallee_mode Hcallee_color
      Hprotected).
  - exact (Houtside Hprotected).
Qed.

Lemma readonly_rdm_call_receiver_signature :
  forall CT receiver_type method_receiver,
    sqtype receiver_type = RDM ->
    qualified_type_subtype CT receiver_type
      (vpa_mutability_tt_readonly_state receiver_type method_receiver) ->
    sqtype method_receiver = RDM \/ sqtype method_receiver = RO.
Proof.
  intros CT receiver_type method_receiver Hreceiver Hsub.
  apply qualified_type_subtype_q_subtype in Hsub.
  rewrite sq_vpa_tt_eq_qq_readonly_state in Hsub.
  rewrite Hreceiver in Hsub.
  destruct (sqtype method_receiver); simpl in Hsub;
    inversion Hsub; subst; auto.
Qed.

(** Statement preservation keeps its original public interface.  The proof
    below is strengthened internally with phase-sensitive authority flow;
    no additional hypothesis is exposed to callers. *)
