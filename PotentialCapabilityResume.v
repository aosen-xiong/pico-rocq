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

Lemma immutable_fresh_return_is_not_resumed_join_target :
  forall CT entry_h eligible caller_authority caller_senv caller_renv
    caller_post return_location,
    Included Loc eligible
      (frame_rdm_root_set
        (mk_watched_frame caller_authority caller_senv caller_renv)) ->
    caller_post.(frame_authority) = Imm_r ->
    wf_r_config CT caller_senv caller_renv entry_h ->
    dom entry_h <= return_location ->
    ~ resumed_frame_join_target eligible caller_post return_location.
Proof.
  intros CT entry_h eligible caller_authority caller_senv caller_renv
    caller_post return_location Heligible Hauthority Hwf Hfresh Htarget.
  destruct Htarget as [Hmutable | Hroot].
  - congruence.
  - apply Heligible in Hroot.
    unfold frame_rdm_root_set in Hroot; simpl in Hroot.
    destruct Hroot as [variable [T [Htype [Hvalue Hrdm]]]].
    have Hdom := wf_config_value_dom CT caller_senv caller_renv entry_h
      variable return_location Hwf Hvalue.
    lia.
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

Lemma resumed_authority_frame_step_location_class :
  forall CT h eligible caller source target,
    resumed_authority_frame_step CT h eligible caller source target ->
    resumed_frame_join_target eligible caller (snd target) \/
    resumed_authority_nonjoin_location_step CT h
      (snd source) (snd target).
Proof.
  intros CT h eligible caller source target Hstep.
  inversion Hstep; subst; simpl.
  - right. apply resumed_nonjoin_location_retained. exact H.
  - right. apply resumed_nonjoin_location_retained. exact H.
  - right. apply resumed_nonjoin_location_mutable_backward. exact H.
  - right. apply resumed_nonjoin_location_mutable_backward. exact H.
  - right. apply resumed_nonjoin_location_mutable_forward. exact H.
  - right. apply resumed_nonjoin_location_mutable_backward. exact H.
  - left. exact H2.
  - left. exact H2.
  - left. exact H1.
  - right. apply resumed_nonjoin_location_refl.
  - right. apply resumed_nonjoin_location_refl.
  - right. apply resumed_nonjoin_location_refl.
  - right. apply resumed_nonjoin_location_refl.
Qed.

(** Under immutable authority, target eligibility and allocation age turn a
    fresh target into a fresh predecessor.  The only semantic input is the
    corresponding property for ordinary heap-flow steps; frame joins are
    discharged by the saved-target policy itself. *)
Lemma immutable_resumed_step_to_fresh_has_fresh_source :
  forall CT h eligible caller boundary_cutoff source target,
    caller.(frame_authority) = Imm_r ->
    (forall location,
      In Loc eligible location ->
      location < boundary_cutoff) ->
    (forall left right,
      resumed_authority_nonjoin_location_step CT h left right ->
      boundary_cutoff <= right ->
      boundary_cutoff <= left) ->
    resumed_authority_frame_step CT h eligible caller source target ->
    boundary_cutoff <= snd target ->
    boundary_cutoff <= snd source.
Proof.
  intros CT h eligible caller boundary_cutoff source target Hauthority
    Heligible Hnonjoin Hstep Htarget.
  destruct (resumed_authority_frame_step_location_class CT h eligible caller
    source target Hstep) as [Hjoin | Hordinary].
  - destruct Hjoin as [Hmutable | Heligible_target].
    + congruence.
    + have Hold := Heligible (snd target) Heligible_target. lia.
  - eapply Hnonjoin; eauto.
Qed.

Definition resumed_authority_frame_connected
  (CT : class_table) (h : heap)
  (eligible : Ensemble Loc) (caller : watched_frame) :
  authority_flow_state -> authority_flow_state -> Prop :=
  clos_refl_trans authority_flow_state
    (resumed_authority_frame_step CT h eligible caller).

Lemma immutable_resumed_path_to_fresh_has_fresh_source :
  forall CT h eligible caller boundary_cutoff source target,
    caller.(frame_authority) = Imm_r ->
    (forall location,
      In Loc eligible location ->
      location < boundary_cutoff) ->
    (forall left right,
      resumed_authority_nonjoin_location_step CT h left right ->
      boundary_cutoff <= right ->
      boundary_cutoff <= left) ->
    resumed_authority_frame_connected CT h eligible caller source target ->
    boundary_cutoff <= snd target ->
    boundary_cutoff <= snd source.
Proof.
  intros CT h eligible caller boundary_cutoff source target Hauthority
    Heligible Hnonjoin Hpath.
  induction Hpath; intros Hfresh.
  - eapply immutable_resumed_step_to_fresh_has_fresh_source; eauto.
  - exact Hfresh.
  - apply IHHpath1.
    apply IHHpath2. exact Hfresh.
Qed.

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

Lemma resumed_authority_frame_connected_refl :
  forall CT h saved caller state,
    resumed_authority_frame_connected CT h saved caller state state.
Proof. intros. apply rt_refl. Qed.

Lemma resumed_authority_frame_connected_trans :
  forall CT h saved caller first middle last,
    resumed_authority_frame_connected CT h saved caller first middle ->
    resumed_authority_frame_connected CT h saved caller middle last ->
    resumed_authority_frame_connected CT h saved caller first last.
Proof. intros. eapply rt_trans; eauto. Qed.

Lemma resumed_authority_frame_closure_contains :
  forall CT h saved caller seeds,
    Included authority_flow_state seeds
      (resumed_authority_frame_closure CT h saved caller seeds).
Proof.
  intros CT h saved caller seeds state Hstate.
  exists state. split; [exact Hstate|apply rt_refl].
Qed.

Lemma resumed_authority_frame_closure_monotone :
  forall CT h saved caller old new,
    Included authority_flow_state old new ->
    Included authority_flow_state
      (resumed_authority_frame_closure CT h saved caller old)
      (resumed_authority_frame_closure CT h saved caller new).
Proof.
  intros CT h saved caller old new Hincluded state
    [seed [Hseed Hpath]].
  exists seed. split; [apply Hincluded; exact Hseed|exact Hpath].
Qed.

Lemma resumed_authority_frame_connected_preserves_runtime_mutability :
  forall CT h saved caller source target runtime_q,
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    resumed_authority_frame_connected CT h saved caller source target ->
    r_muttype h (snd source) = Some runtime_q ->
    r_muttype h (snd target) = Some runtime_q.
Proof.
  intros CT h saved caller source target runtime_q Hwf Hpath Hruntime.
  eapply phased_authority_frame_connected_preserves_runtime_mutability;
    eauto using resumed_authority_frame_connected_is_phased.
Qed.

Lemma phased_authority_frame_step_is_resumed_under_mutable :
  forall CT h saved caller source target,
    caller.(frame_authority) = Mut_r ->
    phased_authority_frame_step CT h caller source target ->
    resumed_authority_frame_step CT h saved caller source target.
Proof.
  intros CT h saved caller source target Hauthority Hstep.
  inversion Hstep; subst.
  - apply resumed_authority_retained. exact H.
  - apply resumed_authority_prospective_retained. exact H.
  - apply resumed_authority_prospective_rdm_backward. exact H.
  - apply resumed_authority_reverse_rdm. exact H.
  - apply resumed_authority_neutral_rdm_forward. exact H.
  - apply resumed_authority_neutral_rdm_backward. exact H.
  - eapply resumed_authority_powered_frame_join; eauto;
      apply resumed_frame_join_target_mutable; exact Hauthority.
  - eapply resumed_authority_prospective_frame_join; eauto;
      apply resumed_frame_join_target_mutable; exact Hauthority.
  - eapply resumed_authority_neutral_frame_join; eauto.
    apply resumed_frame_join_target_mutable. exact Hauthority.
  - apply resumed_authority_forget.
  - apply resumed_authority_prospective_forget.
  - apply resumed_authority_mark_prospective.
  - apply resumed_authority_promote. exact H.
Qed.

Lemma phased_authority_frame_connected_is_resumed_under_mutable :
  forall CT h saved caller source target,
    caller.(frame_authority) = Mut_r ->
    phased_authority_frame_connected CT h caller source target ->
    resumed_authority_frame_connected CT h saved caller source target.
Proof.
  intros CT h saved caller source target Hauthority Hconnected.
  induction Hconnected.
  - apply rt_step. eapply phased_authority_frame_step_is_resumed_under_mutable;
      eauto.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma resumed_authority_frame_closure_eq_phased_under_mutable :
  forall CT h saved caller seeds,
    caller.(frame_authority) = Mut_r ->
    Same_set authority_flow_state
      (resumed_authority_frame_closure CT h saved caller seeds)
      (phased_authority_frame_closure CT h caller seeds).
Proof.
  intros CT h saved caller seeds Hauthority. split.
  - intros state [seed [Hseed Hpath]]. exists seed. split; [exact Hseed|].
    eapply resumed_authority_frame_connected_is_phased. exact Hpath.
  - intros state [seed [Hseed Hpath]]. exists seed. split; [exact Hseed|].
    eapply phased_authority_frame_connected_is_resumed_under_mutable; eauto.
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

(** Proof-relevant membership in the resumed color set.  This form retains
    the predecessor derivation needed by the source-sensitive allocation-age
    argument: an uncolored old heap node may legally point into the fresh
    suffix, whereas an old node already carrying caller authority may not do
    so silently. *)
Inductive resumed_authority_color_derivation
  (CT : class_table) (h : heap) (eligible : Ensemble Loc)
  (caller : watched_frame) (incoming : Ensemble authority_flow_state) :
  authority_flow_state -> Prop :=
| resumed_color_from_incoming : forall state,
    In authority_flow_state incoming state ->
    resumed_authority_color_derivation CT h eligible caller incoming state
| resumed_color_from_owned : forall location,
    frame_owned_location CT h caller location ->
    resumed_authority_color_derivation CT h eligible caller incoming
      (FlowPowered, location)
| resumed_color_by_step : forall source target,
    resumed_authority_color_derivation CT h eligible caller incoming source ->
    resumed_authority_frame_step CT h eligible caller source target ->
    resumed_authority_color_derivation CT h eligible caller incoming target.

Lemma resumed_authority_color_derivation_connected :
  forall CT h eligible caller incoming source target,
    resumed_authority_color_derivation CT h eligible caller incoming source ->
    resumed_authority_frame_connected CT h eligible caller source target ->
    resumed_authority_color_derivation CT h eligible caller incoming target.
Proof.
  intros CT h eligible caller incoming source target Hsource Hpath.
  induction Hpath.
  - eapply resumed_color_by_step; eauto.
  - exact Hsource.
  - apply IHHpath2. apply IHHpath1. exact Hsource.
Qed.

Lemma resumed_authority_color_derivation_iff :
  forall CT h eligible caller incoming state,
    resumed_authority_color_derivation CT h eligible caller incoming state <->
    In authority_flow_state
      (executing_resumed_authority_color_set CT h eligible caller incoming)
      state.
Proof.
  intros CT h eligible caller incoming state. split.
  - intros Hderivation. induction Hderivation as
      [state Hincoming_state | location Howned_location |
        source target Hsource IH Hstep].
    + exists state. split; [left; exact Hincoming_state|apply rt_refl].
    + exists (FlowPowered, location). split.
      * right. exists location. split; [reflexivity|exact Howned_location].
      * apply rt_refl.
    + destruct IH as [seed [Hseed Hpath]].
      exists seed. split; [exact Hseed|].
      eapply rt_trans; [exact Hpath|]. apply rt_step. exact Hstep.
  - intros [seed [Hseed Hpath]].
    have Hseed_derivation :
        resumed_authority_color_derivation CT h eligible caller incoming seed.
    { destruct Hseed as [seed Hincoming | seed Howned].
      - apply resumed_color_from_incoming. exact Hincoming.
      - destruct Howned as [location [Heq Hlocation]]. subst seed.
        apply resumed_color_from_owned. exact Hlocation. }
    eapply resumed_authority_color_derivation_connected; eauto.
Qed.

(** Exact target-only fresh-source result.  The non-join premise is
    deliberately source-sensitive: it is required only when the predecessor
    already has a resumed-color derivation.  This is the form established by
    evaluation provenance, unlike the stronger heap-wide condition used by
    [immutable_resumed_color_cannot_be_fresh] below. *)
Lemma immutable_resumed_derived_color_cannot_be_fresh :
  forall CT h eligible caller incoming boundary_cutoff state,
    caller.(frame_authority) = Imm_r ->
    (forall target,
      In Loc eligible target ->
      target < boundary_cutoff) ->
    (forall incoming_mode incoming_location,
      In authority_flow_state incoming (incoming_mode, incoming_location) ->
      incoming_location < boundary_cutoff) ->
    (forall owned,
      frame_owned_location CT h caller owned ->
      owned < boundary_cutoff) ->
    (forall (source target : authority_flow_state),
      resumed_authority_color_derivation CT h eligible caller incoming
        source ->
      resumed_authority_nonjoin_location_step CT h
        (snd source) (snd target) ->
      boundary_cutoff <= snd target ->
      boundary_cutoff <= snd source) ->
    resumed_authority_color_derivation CT h eligible caller incoming state ->
    boundary_cutoff <= snd state ->
    False.
Proof.
  intros CT h eligible caller incoming boundary_cutoff state Hauthority
    Heligible Hincoming Howned Hnonjoin Hderivation.
  induction Hderivation as
    [state Hincoming_state | location Howned_location |
      source target Hsource IH Hstep]; intros Hfresh.
  - destruct state as [mode location]. simpl in Hfresh.
    have Hold := Hincoming mode location Hincoming_state. lia.
  - simpl in Hfresh. have Hold := Howned location Howned_location. lia.
  - destruct (resumed_authority_frame_step_location_class CT h eligible
      caller source target Hstep) as [Hjoin | Hordinary].
    + destruct Hjoin as [Hmutable | Heligible_target].
      * congruence.
      * have Hold := Heligible (snd target) Heligible_target. lia.
    + apply IH. eapply Hnonjoin; eauto.
Qed.

Lemma immutable_resumed_color_excludes_fresh_source :
  forall CT h eligible caller incoming boundary_cutoff mode location,
    caller.(frame_authority) = Imm_r ->
    (forall target,
      In Loc eligible target ->
      target < boundary_cutoff) ->
    (forall incoming_mode incoming_location,
      In authority_flow_state incoming (incoming_mode, incoming_location) ->
      incoming_location < boundary_cutoff) ->
    (forall owned,
      frame_owned_location CT h caller owned ->
      owned < boundary_cutoff) ->
    (forall (source target : authority_flow_state),
      resumed_authority_color_derivation CT h eligible caller incoming
        source ->
      resumed_authority_nonjoin_location_step CT h
        (snd source) (snd target) ->
      boundary_cutoff <= snd target ->
      boundary_cutoff <= snd source) ->
    In authority_flow_state
      (executing_resumed_authority_color_set CT h eligible caller incoming)
      (mode, location) ->
    boundary_cutoff <= location ->
    False.
Proof.
  intros CT h eligible caller incoming boundary_cutoff mode location
    Hauthority Heligible Hincoming Howned Hnonjoin Hcolor Hfresh.
  have Hderivation :=
    (proj2 (resumed_authority_color_derivation_iff CT h eligible caller
      incoming (mode, location))) Hcolor.
  apply (immutable_resumed_derived_color_cannot_be_fresh CT h eligible caller
    incoming boundary_cutoff (mode, location) Hauthority Heligible Hincoming
    Howned Hnonjoin Hderivation). simpl. exact Hfresh.
Qed.

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

Lemma resumed_dangerous_path_has_frozen_origin_or_owned_promotion :
  forall CT h eligible caller source target,
    authority_mode_dangerous (fst target) ->
    resumed_authority_frame_connected CT h eligible caller source target ->
    (authority_mode_dangerous (fst source) /\
      resumed_frozen_authority_connected CT h eligible caller source target) \/
    (exists anchor,
      frame_owned_location CT h caller anchor /\
      resumed_frozen_authority_connected CT h eligible caller
        (FlowPowered, anchor) target).
Proof.
  intros CT h eligible caller source target Htarget Hconnected.
  induction Hconnected.
  - inversion H; subst; simpl in *.
    + left. split; [left; reflexivity|]. apply rt_step.
      apply resumed_frozen_nonjoin. apply frozen_nonjoin_retained. exact H0.
    + left. split; [right; reflexivity|]. apply rt_step.
      apply resumed_frozen_nonjoin.
      apply frozen_nonjoin_prospective_retained. exact H0.
    + left. split; [right; reflexivity|]. apply rt_step.
      apply resumed_frozen_nonjoin.
      apply frozen_nonjoin_prospective_rdm_backward. exact H0.
    + left. split; [left; reflexivity|]. apply rt_step.
      apply resumed_frozen_nonjoin. apply frozen_nonjoin_reverse_rdm. exact H0.
    + destruct Htarget as [Hbad | Hbad]; discriminate.
    + destruct Htarget as [Hbad | Hbad]; discriminate.
    + left. split; [left; reflexivity|]. apply rt_step.
      eapply resumed_frozen_powered_join; eauto.
    + left. split; [right; reflexivity|]. apply rt_step.
      eapply resumed_frozen_prospective_join; eauto.
    + destruct Htarget as [Hbad | Hbad]; discriminate.
    + destruct Htarget as [Hbad | Hbad]; discriminate.
    + destruct Htarget as [Hbad | Hbad]; discriminate.
    + left. split; [left; reflexivity|]. apply rt_step.
      apply resumed_frozen_nonjoin. apply frozen_nonjoin_mark_prospective.
    + right. eexists. split; [eassumption|apply rt_refl].
  - left. split; [exact Htarget|apply rt_refl].
  - destruct (IHHconnected2 Htarget) as
      [[Hmiddle Htail] | [anchor [Howned Htail]]].
    + destruct (IHHconnected1 Hmiddle) as
        [[Hsource Hprefix] | [anchor [Howned Hprefix]]].
      * left. split; [exact Hsource|]. eapply rt_trans; eauto.
      * right. exists anchor. split; [exact Howned|].
        eapply rt_trans; eauto.
    + right. exists anchor. split; assumption.
Qed.

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

Lemma resumed_dangerous_color_derivation_connected :
  forall CT h eligible caller incoming source target,
    resumed_dangerous_color_derivation CT h eligible caller incoming source ->
    resumed_frozen_authority_connected CT h eligible caller source target ->
    resumed_dangerous_color_derivation CT h eligible caller incoming target.
Proof.
  intros CT h eligible caller incoming source target Hsource Hpath.
  induction Hpath.
  - eapply resumed_dangerous_by_frozen_step; eauto.
  - exact Hsource.
  - apply IHHpath2. apply IHHpath1. exact Hsource.
Qed.

Lemma executing_resumed_dangerous_color_has_derivation :
  forall CT h eligible caller incoming mode location,
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_resumed_authority_color_set CT h eligible caller incoming)
      (mode, location) ->
    resumed_dangerous_color_derivation CT h eligible caller incoming
      (mode, location).
Proof.
  intros CT h eligible caller incoming mode location Hmode
    [seed [Hseed Hpath]].
  destruct (resumed_dangerous_path_has_frozen_origin_or_owned_promotion CT h
    eligible caller seed (mode, location) Hmode Hpath) as
    [[Hseed_mode Hfrozen] | [anchor [Howned Hfrozen]]].
  - have Hseed_derivation :
        resumed_dangerous_color_derivation CT h eligible caller incoming seed.
    { destruct Hseed as [seed Hincoming | seed Howned_seed].
      - eapply resumed_dangerous_from_incoming; eauto.
      - destruct Howned_seed as [owned [Heq Howned_location]]. subst seed.
        apply resumed_dangerous_from_owned. exact Howned_location. }
    eapply resumed_dangerous_color_derivation_connected; eauto.
  - eapply resumed_dangerous_color_derivation_connected; [|exact Hfrozen].
    apply resumed_dangerous_from_owned. exact Howned.
Qed.

(** Final focused obligation for target-only immutable resume.  Ordinary
    dangerous flow is source-sensitive; neutral component-identification
    paths are irrelevant because promotion restarts at an old owned anchor.
    Hence a fresh dangerous source is impossible without restricting neutral
    joins or adding a public theorem premise. *)
Lemma immutable_resumed_dangerous_color_cannot_be_fresh :
  forall CT h eligible caller incoming boundary_cutoff state,
    caller.(frame_authority) = Imm_r ->
    (forall target,
      In Loc eligible target ->
      target < boundary_cutoff) ->
    (forall incoming_mode incoming_location,
      authority_mode_dangerous incoming_mode ->
      In authority_flow_state incoming (incoming_mode, incoming_location) ->
      incoming_location < boundary_cutoff) ->
    (forall owned,
      frame_owned_location CT h caller owned ->
      owned < boundary_cutoff) ->
    (forall source target,
      resumed_dangerous_color_derivation CT h eligible caller incoming
        source ->
      frozen_caller_authority_nonjoin_step CT h source target ->
      boundary_cutoff <= snd target ->
      boundary_cutoff <= snd source) ->
    resumed_dangerous_color_derivation CT h eligible caller incoming state ->
    boundary_cutoff <= snd state ->
    False.
Proof.
  intros CT h eligible caller incoming boundary_cutoff state Hauthority
    Heligible Hincoming Howned Hnonjoin Hderivation.
  induction Hderivation as
    [state Hmode Hincoming_state | location Howned_location |
      source target Hsource IH Hstep]; intros Hfresh.
  - destruct state as [mode location]. simpl in Hfresh.
    have Hold := Hincoming mode location Hmode Hincoming_state. lia.
  - simpl in Hfresh. have Hold := Howned location Howned_location. lia.
  - inversion Hstep; subst; simpl in Hfresh.
    + apply IH. eapply Hnonjoin; eauto.
    + destruct H2 as [Hmutable | Heligible_target].
      * congruence.
      * have Hold := Heligible right Heligible_target. lia.
    + destruct H2 as [Hmutable | Heligible_target].
      * congruence.
      * have Hold := Heligible right Heligible_target. lia.
Qed.

Lemma immutable_resumed_dangerous_color_excludes_fresh_source :
  forall CT h eligible caller incoming boundary_cutoff mode location,
    caller.(frame_authority) = Imm_r ->
    (forall target,
      In Loc eligible target ->
      target < boundary_cutoff) ->
    (forall incoming_mode incoming_location,
      authority_mode_dangerous incoming_mode ->
      In authority_flow_state incoming (incoming_mode, incoming_location) ->
      incoming_location < boundary_cutoff) ->
    (forall owned,
      frame_owned_location CT h caller owned ->
      owned < boundary_cutoff) ->
    (forall source target,
      resumed_dangerous_color_derivation CT h eligible caller incoming
        source ->
      frozen_caller_authority_nonjoin_step CT h source target ->
      boundary_cutoff <= snd target ->
      boundary_cutoff <= snd source) ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_resumed_authority_color_set CT h eligible caller incoming)
      (mode, location) ->
    boundary_cutoff <= location ->
    False.
Proof.
  intros CT h eligible caller incoming boundary_cutoff mode location
    Hauthority Heligible Hincoming Howned Hnonjoin Hmode Hcolor Hfresh.
  have Hderivation := executing_resumed_dangerous_color_has_derivation CT h
    eligible caller incoming mode location Hmode Hcolor.
  apply (immutable_resumed_dangerous_color_cannot_be_fresh CT h eligible
    caller incoming boundary_cutoff (mode, location) Hauthority Heligible
    Hincoming Howned Hnonjoin Hderivation). simpl. exact Hfresh.
Qed.

(** The policy-indexed dangerous derivation erases to the established
    tracked frozen derivation.  Eligibility is extra information used only
    to rule out a fresh join target; all ordinary provenance remains exactly
    the provenance already maintained by the statement induction. *)
Lemma resumed_dangerous_derivation_is_tracked :
  forall CT h Z active active_incoming eligible caller caller_incoming
    snapshot state,
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
    resumed_dangerous_color_derivation CT h eligible caller caller_incoming
      state ->
    tracked_resume_frozen_color_derivation CT h Z active active_incoming
      caller caller_incoming snapshot state.
Proof.
  intros CT h Z active active_incoming eligible caller caller_incoming
    snapshot state Hincoming Howned Hderivation.
  induction Hderivation as
    [state Hmode Hincoming_state | location Howned_location |
      source target Hsource IH Hstep].
  - apply tracked_resume_from_snapshot.
    + destruct state as [mode location]. eapply Hincoming; eauto.
    + exact Hincoming_state.
    + eapply resumed_caller_incoming_has_frozen_origin; eauto.
  - eapply tracked_resume_from_caller_owned; eauto.
  - inversion Hstep; subst.
    + eapply tracked_resume_by_nonjoin; eauto.
    + eapply tracked_resume_by_frame_join; eauto. left. reflexivity.
    + eapply tracked_resume_by_frame_join; eauto. right. reflexivity.
Qed.

Lemma tracked_nonjoin_freshness_implies_resumed_freshness :
  forall CT h Z active active_incoming eligible caller caller_incoming
    snapshot boundary_cutoff,
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
    (forall source target
        (derivation : tracked_resume_frozen_color_derivation CT h Z active
          active_incoming caller caller_incoming snapshot source)
        derivation_height,
      tracked_resume_frozen_color_derivation_has_height CT h Z active
        active_incoming caller caller_incoming snapshot source derivation
        derivation_height ->
      frozen_caller_authority_nonjoin_step CT h source target ->
      boundary_cutoff <= snd target ->
      boundary_cutoff <= snd source) ->
    forall source target,
      resumed_dangerous_color_derivation CT h eligible caller caller_incoming
        source ->
      frozen_caller_authority_nonjoin_step CT h source target ->
      boundary_cutoff <= snd target ->
      boundary_cutoff <= snd source.
Proof.
  intros CT h Z active active_incoming eligible caller caller_incoming
    snapshot boundary_cutoff Hincoming Howned Htracked source target
    Hsource Hstep Htarget.
  have Hsource_tracked := resumed_dangerous_derivation_is_tracked CT h Z
    active active_incoming eligible caller caller_incoming snapshot source
    Hincoming Howned Hsource.
  destruct (tracked_resume_frozen_color_derivation_has_some_height CT h Z
    active active_incoming caller caller_incoming snapshot source
    Hsource_tracked) as [height Hheight].
  eapply Htracked; eauto.
Qed.

(** The target-only design point is now discharged against the existing
    proof products.  This theorem contains no new semantic assumption: its
    final premise is precisely the tracked non-join freshness property
    already generated for immutable fresh returns. *)
Lemma immutable_resumed_fresh_source_excluded_from_tracked_provenance :
  forall CT h Z active active_incoming eligible caller caller_incoming
    snapshot boundary_cutoff mode location,
    caller.(frame_authority) = Imm_r ->
    (forall target,
      In Loc eligible target ->
      target < boundary_cutoff) ->
    (forall incoming_mode incoming_location,
      authority_mode_dangerous incoming_mode ->
      In authority_flow_state caller_incoming
        (incoming_mode, incoming_location) ->
      incoming_location < boundary_cutoff) ->
    (forall owned,
      frame_owned_location CT h caller owned ->
      owned < boundary_cutoff) ->
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
    (forall source target
        (derivation : tracked_resume_frozen_color_derivation CT h Z active
          active_incoming caller caller_incoming snapshot source)
        derivation_height,
      tracked_resume_frozen_color_derivation_has_height CT h Z active
        active_incoming caller caller_incoming snapshot source derivation
        derivation_height ->
      frozen_caller_authority_nonjoin_step CT h source target ->
      boundary_cutoff <= snd target ->
      boundary_cutoff <= snd source) ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_resumed_authority_color_set CT h eligible caller
        caller_incoming) (mode, location) ->
    boundary_cutoff <= location ->
    False.
Proof.
  intros CT h Z active active_incoming eligible caller caller_incoming
    snapshot boundary_cutoff mode location Hauthority Heligible Hincoming_old
    Howned_old Hincoming_snapshot Howned_callee Htracked Hmode Hcolor Hfresh.
  have Hnonjoin := tracked_nonjoin_freshness_implies_resumed_freshness CT h Z
    active active_incoming eligible caller caller_incoming snapshot
    boundary_cutoff Hincoming_snapshot Howned_callee Htracked.
  exact (immutable_resumed_dangerous_color_excludes_fresh_source CT h eligible
    caller caller_incoming boundary_cutoff mode location Hauthority Heligible
    Hincoming_old Howned_old Hnonjoin Hmode Hcolor Hfresh).
Qed.

(** Focused fresh-source theorem for the approved target-only policy.  If
    saved caller colors and caller-owned capability seeds predate the call,
    and ordinary heap-flow cannot cross from the old prefix into the fresh
    suffix, then the resumed immutable frame has no color at any fresh
    location.  In particular, a fresh return cannot become the dangerous
    source of a join into an old protected caller root. *)
Lemma immutable_resumed_color_cannot_be_fresh :
  forall CT h eligible caller incoming boundary_cutoff mode location,
    caller.(frame_authority) = Imm_r ->
    (forall target,
      In Loc eligible target ->
      target < boundary_cutoff) ->
    (forall incoming_mode incoming_location,
      In authority_flow_state incoming (incoming_mode, incoming_location) ->
      incoming_location < boundary_cutoff) ->
    (forall owned,
      frame_owned_location CT h caller owned ->
      owned < boundary_cutoff) ->
    (forall left right,
      resumed_authority_nonjoin_location_step CT h left right ->
      boundary_cutoff <= right ->
      boundary_cutoff <= left) ->
    In authority_flow_state
      (executing_resumed_authority_color_set CT h eligible caller incoming)
      (mode, location) ->
    boundary_cutoff <= location ->
    False.
Proof.
  intros CT h eligible caller incoming boundary_cutoff mode location
    Hauthority Heligible Hincoming Howned Hnonjoin
    [seed [Hseed Hpath]] Hfresh.
  have Hseed_fresh : boundary_cutoff <= snd seed.
  { apply (immutable_resumed_path_to_fresh_has_fresh_source CT h eligible
      caller boundary_cutoff seed (mode, location) Hauthority Heligible
      Hnonjoin Hpath). simpl. exact Hfresh. }
  destruct Hseed as [seed Hincoming_seed | seed Howned_seed].
  - destruct seed as [seed_mode seed_location]. simpl in Hseed_fresh.
    have Hold := Hincoming seed_mode seed_location Hincoming_seed. lia.
  - destruct Howned_seed as
      [owned [Heq Howned_location]].
    subst seed. simpl in Hseed_fresh.
    have Hold := Howned owned Howned_location. lia.
Qed.

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

Lemma executing_authority_separation_implies_resumed_separation :
  forall CT h Z eligible active incoming,
    executing_authority_colors_separated CT h Z active incoming ->
    executing_resumed_authority_colors_separated CT h Z eligible active
      incoming.
Proof.
  intros CT h Z eligible active incoming Hseparated mode protected Hmode
    Hcolor.
  eapply Hseparated; [exact Hmode|].
  eapply executing_resumed_authority_color_set_in_phased. exact Hcolor.
Qed.

Lemma executing_resumed_authority_color_set_eq_under_mutable :
  forall CT h eligible active incoming,
    active.(frame_authority) = Mut_r ->
    Same_set authority_flow_state
      (executing_resumed_authority_color_set CT h eligible active incoming)
      (executing_authority_color_set CT h active incoming).
Proof.
  intros CT h eligible active incoming Hauthority.
  unfold executing_resumed_authority_color_set,
    executing_authority_color_set.
  eapply resumed_authority_frame_closure_eq_phased_under_mutable.
  exact Hauthority.
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

Lemma executing_authority_call_pop_safe_implies_resumed :
  forall CT h Z callee callee_incoming eligible caller caller_incoming,
    executing_authority_call_pop_safe CT h Z callee callee_incoming caller
      caller_incoming ->
    executing_resumed_authority_call_pop_safe CT h Z callee callee_incoming
      eligible caller caller_incoming.
Proof.
  intros CT h Z callee callee_incoming eligible caller caller_incoming Hsafe
    mode location Hmode Hcolor.
  eapply Hsafe; [exact Hmode|].
  eapply executing_resumed_authority_color_set_in_phased. exact Hcolor.
Qed.

Lemma executing_resumed_authority_colors_separated_after_call_pop :
  forall CT h Z callee callee_incoming eligible caller caller_incoming,
    executing_authority_colors_separated CT h Z callee callee_incoming ->
    executing_resumed_authority_call_pop_safe CT h Z callee callee_incoming
      eligible caller caller_incoming ->
    executing_resumed_authority_colors_separated CT h Z eligible caller
      caller_incoming.
Proof.
  intros CT h Z callee callee_incoming eligible caller caller_incoming
    Hcallee Hpop mode location Hmode Hcolor Hprotected.
  destruct (Hpop mode location Hmode Hcolor) as
    [[callee_mode [Hcallee_mode Hcallee_color]] | Houtside].
  - eapply Hcallee; eauto.
  - exact (Houtside Hprotected).
Qed.

Lemma tracked_mutable_post_update_resumed_call_pop_safe :
  forall CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination destination_type
    return_location caller_incoming eligible,
    let caller_post := mk_watched_frame
      boundary.(boundary_caller).(frame_authority) caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) in
    boundary.(boundary_caller).(frame_authority) = Mut_r ->
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
    executing_resumed_authority_call_pop_safe CT h Z active active_incoming
      eligible caller_post caller_incoming.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination destination_type
    return_location caller_incoming eligible caller_post Hauthority Hfull
    Hcaller_wf Hcaller_post_wf Hdestination Hroots Hincoming
    Hcaller_incoming Howned.
  eapply executing_authority_call_pop_safe_implies_resumed.
  eapply tracked_mutable_post_update_call_pop_safe; eauto.
Qed.

Lemma tracked_null_post_update_resumed_call_pop_safe :
  forall CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination caller_incoming eligible,
    let caller_post := mk_watched_frame
      boundary.(boundary_caller).(frame_authority) caller_senv
      (update_r_env_value caller_renv destination Null_a) in
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some snapshot :: snapshots) h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination Null_a) h ->
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
    executing_resumed_authority_call_pop_safe CT h Z active active_incoming
      eligible caller_post caller_incoming.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination caller_incoming eligible
    caller_post Hfull Hcaller_post_wf Hroots Hincoming Hcaller_incoming
    Howned.
  eapply executing_authority_call_pop_safe_implies_resumed.
  eapply tracked_null_post_update_call_pop_safe; eauto.
Qed.

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

(** Phase-local well-formedness for each witness together with the strict
    snapshot tail it summarizes.  Stating the properties on the combined
    list lets the existing nested-certificate preservation lemmas be reused
    without rebuilding an earlier caller closure on a later heap. *)
Fixpoint private_resume_witnesses_phase_wf
  (CT : class_table) (h : heap) (active : watched_frame)
  (witnesses snapshots : list frozen_caller_snapshot_slot) : Prop :=
  match witnesses, snapshots with
  | [], [] => True
  | witness :: witness_tail, _ :: snapshot_tail =>
      frozen_caller_snapshots_runtime_mutable h (witness :: snapshot_tail) /\
      frozen_caller_snapshots_closed CT h active (witness :: snapshot_tail) /\
      frozen_caller_snapshots_resume_roots_in_heap h
        (witness :: snapshot_tail) /\
      frozen_caller_snapshots_resume_exposures_wf CT h active
        (witness :: snapshot_tail) /\
      private_resume_witnesses_phase_wf CT h active witness_tail snapshot_tail
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

Fixpoint private_resume_witnesses_roots_safe
  (CT : class_table) (h : heap) (Z : Ensemble Loc) (active : watched_frame)
  (witnesses snapshots : list frozen_caller_snapshot_slot) : Prop :=
  match witnesses, snapshots with
  | [], [] => True
  | witness :: witness_tail, _ :: snapshot_tail =>
      frozen_caller_snapshots_active_resume_safe CT h Z active
        (witness :: snapshot_tail) /\
      private_resume_witnesses_roots_safe CT h Z active witness_tail
        snapshot_tail
  | _, _ => False
  end.

(** Pairwise continuation safety for every policy witness.  At one boundary
    the witness is considered together with the strict ordinary-snapshot
    tail that it summarizes.  This certificate is deliberately separate
    from color coverage and from active-root safety: neither of those facts
    explains an older caller's latent resume exposure when a newer frozen
    color reaches one of its captured roots. *)
Fixpoint private_resume_witnesses_nested_resume_safe
  (Z : Ensemble Loc) (witnesses snapshots : list frozen_caller_snapshot_slot)
  : Prop :=
  match witnesses, snapshots with
  | [], [] => True
  | witness :: witness_tail, _ :: snapshot_tail =>
      frozen_caller_snapshots_nested_resume_safe Z
        (witness :: snapshot_tail) /\
      private_resume_witnesses_nested_resume_safe Z witness_tail
        snapshot_tail
  | _, _ => False
  end.

(** The currently executing phase may contain inherited incoming authority,
    so it cannot be replaced by independent active colors.  This recursive
    certificate records, at each suspended boundary, how the completed phase
    is safe against the witness and strict snapshot tail that the boundary
    will expose on a later pop. *)
Fixpoint private_resume_witnesses_completed_safe
  (CT : class_table) (h : heap) (Z : Ensemble Loc) (active : watched_frame)
  (incoming : Ensemble authority_flow_state)
  (witnesses snapshots : list frozen_caller_snapshot_slot) : Prop :=
  match witnesses, snapshots with
  | [], [] => True
  | witness :: witness_tail, _ :: snapshot_tail =>
      frozen_completed_colors_resume_safe Z
        (executing_authority_color_set CT h active incoming)
        (witness :: snapshot_tail) /\
      private_resume_witnesses_completed_safe CT h Z active incoming
        witness_tail snapshot_tail
  | _, _ => False
  end.

(** Policy witnesses also form a frozen stack in their own right.  An
    ordinary [None] slot contains no colors, so the relation against the
    ordinary snapshot tail cannot account for authority stored only in an
    older policy witness.  This package supplies that missing recursive
    dimension without exposing it outside the private statement induction. *)
Definition private_resume_witness_stack_safe
  (CT : class_table) (h : heap) (Z : Ensemble Loc) (active : watched_frame)
  (incoming : Ensemble authority_flow_state)
  (witnesses : list frozen_caller_snapshot_slot) : Prop :=
  frozen_caller_snapshots_nested_covered witnesses /\
  frozen_caller_snapshots_runtime_mutable h witnesses /\
  frozen_caller_snapshots_dangerous witnesses /\
  frozen_caller_snapshots_closed CT h active witnesses /\
  frozen_caller_snapshots_resume_roots_in_heap h witnesses /\
  frozen_caller_snapshots_resume_exposures_wf CT h active witnesses /\
  frozen_caller_snapshots_active_resume_safe CT h Z active witnesses /\
  frozen_caller_snapshots_resume_joins_safe Z witnesses /\
  frozen_caller_snapshots_nested_resume_safe Z witnesses /\
  frozen_completed_colors_resume_safe Z
    (executing_authority_color_set CT h active incoming) witnesses /\
  frozen_caller_snapshots_retain_entry witnesses /\
  frozen_caller_snapshots_cover_phase_incoming witnesses.

(** Temporal facts that make the policy-only witness list a genuine frozen
    stack.  A [Some] policy slot is installed only at a channel-free entry;
    general and null-return calls install [None].  Therefore the ordinary
    tracked allocation partition is truthful for every [Some] slot without
    adding a public premise. *)
Definition private_resume_witness_temporal_state
  (CT : class_table) (h : heap) (Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary)
  (witnesses : list frozen_caller_snapshot_slot) : Prop :=
  frozen_caller_snapshots_avoid_protected Z witnesses /\
  frozen_caller_snapshots_entry_exposure_covered witnesses /\
  frozen_callee_side_mutable_components_after_boundaries CT h active
    witnesses stack /\
  frozen_callee_side_prospective_components_after_boundaries CT h active
    witnesses stack /\
  frozen_snapshot_boundaries_after_cutoff cutoff witnesses stack.

(** The first tracked policy witness summarizes every older policy witness.
    An operational [None] may precede it in the strong exceptional channel;
    the always-present target channel starts with [Some]. *)
Fixpoint private_policy_head_active_overlap_justified
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (active : watched_frame) (witnesses : list frozen_caller_snapshot_slot) :
  Prop :=
  match witnesses with
  | Some _ :: _ =>
      frozen_caller_snapshots_active_overlap_justified CT h Z active
        witnesses
  | None :: tail =>
      private_policy_head_active_overlap_justified CT h Z active tail
  | _ => True
  end.

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

Lemma frozen_completed_colors_resume_phase_safe_after_self_activation :
  forall CT h Z caller completed targets,
    frozen_completed_colors_resume_phase_safe Z completed
      (activate_frozen_target_snapshots CT h caller
        (dangerous_authority_colors completed) targets).
Proof.
  intros CT h Z caller completed targets snapshot source_mode source
    Hsnapshot Hmode Hcompleted Hroot.
  left. exists source_mode. split; [exact Hmode|].
  unfold activate_frozen_target_snapshots in Hsnapshot.
  apply in_map_iff in Hsnapshot.
  destruct Hsnapshot as [slot [Heq Hslot]].
  destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl. right. split; [exact Hcompleted|].
  simpl. exact Hmode.
Qed.

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

(** Saved-frame counterpart used by the target policy.  Its source exposure
    does not change merely because execution enters or leaves a nested
    callee; the ordinary resume witness remains phase-current. *)
Definition private_saved_target_exposures_support_resume_phase
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (targets resumes : list frozen_caller_snapshot_slot) : Prop :=
  private_target_exposures_support_resume_phase Z targets resumes.


Lemma repeat_none_target_exposures_support_resume_phase :
  forall Z count,
    private_target_exposures_support_resume_phase Z
      (repeat None count) (repeat None count).
Proof.
  intros Z count. induction count; simpl; [exact I|exact IHcount].
Qed.

Lemma private_target_exposures_support_resume_phase_head :
  forall Z head target_tail resume_head resume_tail resume source_mode source,
    private_target_exposures_support_resume_phase Z
      (Some head :: target_tail) (resume_head :: resume_tail) ->
    List.In (Some resume) resume_tail ->
    authority_mode_dangerous source_mode ->
    In authority_flow_state head.(frozen_snapshot_current_resume_exposure)
      (source_mode, source) ->
    In Loc resume.(frozen_snapshot_resume_rdm_roots) source ->
    (exists phase_mode,
      authority_mode_dangerous phase_mode /\
      In authority_flow_state resume.(frozen_snapshot_phase_incoming)
        (phase_mode, source)) \/
    frozen_snapshot_resume_exposure_avoids Z resume.
Proof.
  intros Z head target_tail resume_head resume_tail resume source_mode source
    [Hhead _] Hresume Hmode Hcolor Hroot. eapply Hhead; eauto.
Qed.

Lemma frozen_caller_snapshots_resume_exposures_wf_drop_head :
  forall CT h active slot tail,
    frozen_caller_snapshots_resume_exposures_wf CT h active (slot :: tail) ->
    frozen_caller_snapshots_resume_exposures_wf CT h active tail.
Proof.
  intros CT h active slot tail Hexposure. repeat split.
  - intros snapshot Hsnapshot. eapply (proj1 Hexposure); simpl; eauto.
  - intros snapshot Hsnapshot. eapply (proj1 (proj2 Hexposure)); simpl; eauto.
  - intros snapshot mode location Hsnapshot. eapply
      (proj1 (proj2 (proj2 Hexposure))); simpl; eauto.
  - intros snapshot Hsnapshot. eapply
      (proj1 (proj2 (proj2 (proj2 Hexposure)))); simpl; eauto.
  - intros snapshot root Hsnapshot. eapply
      (proj2 (proj2 (proj2 (proj2 Hexposure)))); simpl; eauto.
Qed.

(** Second-order saved-target certificate.  A newer latent resume exposure
    matters only when it can actually be activated by class-bounded or
    inherited authority.  In that case the usual phase-or-safe alternative
    must hold against every older target. *)
Fixpoint frozen_caller_snapshots_nested_resume_phase_safe
  (Z : Ensemble Loc) (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  match snapshots with
  | [] => True
  | Some newer :: tail =>
      (frozen_snapshot_resume_activated newer ->
       frozen_completed_colors_resume_phase_safe Z
         newer.(frozen_snapshot_current_resume_exposure) tail) /\
      frozen_caller_snapshots_nested_resume_phase_safe Z tail
  | None :: tail =>
      frozen_caller_snapshots_nested_resume_phase_safe Z tail
  end.

Lemma frozen_target_nested_phase_safe_iff_legacy :
  forall CT h Z targets,
    frozen_target_snapshots_nested_resume_phase_safe CT h Z targets <->
    frozen_caller_snapshots_nested_resume_phase_safe Z targets.
Proof.
  intros CT h Z targets. induction targets as [|slot tail]; simpl.
  - tauto.
  - destruct slot as [head|]; simpl.
    + rewrite IHtail. tauto.
    + exact IHtail.
Qed.

Lemma repeat_none_nested_resume_phase_safe :
  forall Z count,
    frozen_caller_snapshots_nested_resume_phase_safe Z
      (repeat None count).
Proof.
  intros Z count. induction count; simpl; [exact I|exact IHcount].
Qed.

Lemma frozen_caller_snapshots_nested_resume_phase_safe_head :
  forall Z head tail older source_mode source,
    frozen_caller_snapshots_nested_resume_phase_safe Z (Some head :: tail) ->
    frozen_snapshot_resume_activated head ->
    List.In (Some older) tail ->
    authority_mode_dangerous source_mode ->
    In authority_flow_state head.(frozen_snapshot_current_resume_exposure)
      (source_mode, source) ->
    In Loc older.(frozen_snapshot_resume_rdm_roots) source ->
    (exists phase_mode,
      authority_mode_dangerous phase_mode /\
      In authority_flow_state older.(frozen_snapshot_phase_incoming)
        (phase_mode, source)) \/
    frozen_snapshot_resume_exposure_avoids Z older.
Proof.
  intros Z head tail older source_mode source [Hhead _] Hactivated Holder Hmode
    Hcolor Hroot. eapply Hhead; eauto.
Qed.

Lemma repeat_none_completed_colors_resume_phase_safe :
  forall Z completed count,
    frozen_completed_colors_resume_phase_safe Z completed
      (repeat None count).
Proof.
  intros Z completed count snapshot source_mode source Hsnapshot.
  induction count; simpl in Hsnapshot; [contradiction|].
  destruct Hsnapshot as [Hbad | Htail]; [discriminate|].
  apply IHcount. exact Htail.
Qed.

Lemma frozen_completed_colors_resume_phase_safe_after_active_descent :
  forall CT h Z authority old_senv old_renv new_senv new_renv incoming
    snapshots,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame authority new_senv new_renv))
      (phase_frame_capability_set CT h
        (mk_watched_frame authority old_senv old_renv)) ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame authority old_senv old_renv) snapshots ->
    frozen_completed_colors_resume_phase_safe Z
      (executing_authority_color_set CT h
        (mk_watched_frame authority old_senv old_renv) incoming) snapshots ->
    frozen_completed_colors_resume_phase_safe Z
      (executing_authority_color_set CT h
        (mk_watched_frame authority new_senv new_renv) incoming)
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) snapshots).
Proof.
  intros CT h Z authority old_senv old_renv new_senv new_renv incoming
    snapshots Hdescend Howned Hexposure Hsafe new_snapshot source_mode source
    Hnew Hsource_mode Hsource Hroot.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  have Hold_source : In authority_flow_state
      (executing_authority_color_set CT h
        (mk_watched_frame authority old_senv old_renv) incoming)
      (source_mode, source).
  { eapply executing_authority_colors_after_active_descent_included; eauto. }
  destruct (Hsafe old_snapshot source_mode source Hold Hsource_mode
    Hold_source Hroot) as
    [[phase_mode [Hphase_mode Hphase]] | Hold_safe].
  - left. exists phase_mode. split; assumption.
  - right. intros exposure_mode target Hexposure_mode Htarget.
    eapply Hold_safe; [exact Hexposure_mode|].
    eapply (proj1 (proj2 Hexposure)); [exact Hold|].
    destruct Htarget as [seed [Hseed Hpath]]. exists seed.
    split; [exact Hseed|].
    eapply frozen_caller_connected_after_descent_reflects; eauto.
Qed.

Lemma frozen_caller_snapshots_nested_resume_phase_safe_after_active_descent :
  forall CT h Z authority old_senv old_renv new_senv new_renv snapshots,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame authority old_senv old_renv) snapshots ->
    frozen_caller_snapshots_nested_resume_phase_safe Z snapshots ->
    frozen_caller_snapshots_nested_resume_phase_safe Z
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) snapshots).
Proof.
  intros CT h Z authority old_senv old_renv new_senv new_renv snapshots
    Hdescend Hexposure Hnested.
  induction snapshots as [|slot tail IH]; simpl in *; [exact I|].
  destruct slot as [head|].
  - destruct Hnested as [Hhead Htail]. split.
    + intros Hhead_authority new_older source_mode source Hnew Hsource_mode
        Hsource Hroot.
      unfold advance_frozen_caller_snapshots in Hnew.
      apply in_map_iff in Hnew.
      destruct Hnew as [old_slot [Heq Hold]].
      destruct old_slot as [older|]; simpl in Heq; [|discriminate].
      injection Heq as <-. simpl in *.
      have Hold_source : In authority_flow_state
          head.(frozen_snapshot_current_resume_exposure)
          (source_mode, source).
      { eapply (proj1 (proj2 Hexposure)); [simpl; auto|].
        destruct Hsource as [seed [Hseed Hpath]]. exists seed.
        split; [exact Hseed|].
        eapply frozen_caller_connected_after_descent_reflects; eauto. }
      destruct (Hhead Hhead_authority older source_mode source Hold
        Hsource_mode Hold_source Hroot) as
        [[phase_mode [Hphase_mode Hphase]] | Hold_safe].
      * left. exists phase_mode. simpl. split; assumption.
      * right. intros exposure_mode target Hexposure_mode Htarget.
        eapply Hold_safe; [exact Hexposure_mode|].
        eapply (proj1 (proj2 Hexposure)); [simpl; right; exact Hold|].
        destruct Htarget as [seed [Hseed Hpath]]. exists seed.
        split; [exact Hseed|].
        eapply frozen_caller_connected_after_descent_reflects; eauto.
    + eapply IH.
      * repeat split.
        -- intros snapshot Hsnapshot. eapply (proj1 Hexposure); simpl; eauto.
        -- intros snapshot Hsnapshot. eapply (proj1 (proj2 Hexposure));
             simpl; eauto.
        -- intros snapshot mode location Hsnapshot. eapply
             (proj1 (proj2 (proj2 Hexposure))); simpl; eauto.
        -- intros snapshot Hsnapshot. eapply
             (proj1 (proj2 (proj2 (proj2 Hexposure)))); simpl; eauto.
        -- intros snapshot root Hsnapshot. eapply
             (proj2 (proj2 (proj2 (proj2 Hexposure)))); simpl; eauto.
      * exact Htail.
  - eapply IH.
    + repeat split.
      * intros snapshot Hsnapshot. eapply (proj1 Hexposure); simpl; eauto.
      * intros snapshot Hsnapshot. eapply (proj1 (proj2 Hexposure));
          simpl; eauto.
      * intros snapshot mode location Hsnapshot. eapply
          (proj1 (proj2 (proj2 Hexposure))); simpl; eauto.
      * intros snapshot Hsnapshot. eapply
          (proj1 (proj2 (proj2 (proj2 Hexposure)))); simpl; eauto.
      * intros snapshot root Hsnapshot. eapply
          (proj2 (proj2 (proj2 (proj2 Hexposure)))); simpl; eauto.
    + exact Hnested.
Qed.

Lemma frozen_source_resume_phase_safe_after_active_descent :
  forall CT h Z authority old_senv old_renv new_senv new_renv source resumes,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h
        (mk_watched_frame authority old_senv old_renv) source) source ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame authority old_senv old_renv) resumes ->
    frozen_completed_colors_resume_phase_safe Z source resumes ->
    frozen_completed_colors_resume_phase_safe Z
      (frozen_caller_authority_closure CT h
        (mk_watched_frame authority new_senv new_renv) source)
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) resumes).
Proof.
  intros CT h Z authority old_senv old_renv new_senv new_renv source resumes
    Hdescend Hsource_closed Hexposure Hsafe new_resume source_mode location
    Hnew Hmode [seed [Hseed Hpath]] Hroot.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_resume|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  have Hold_source : In authority_flow_state source (source_mode, location).
  { eapply Hsource_closed. exists seed. split; [exact Hseed|].
    eapply frozen_caller_connected_after_descent_reflects; eauto. }
  destruct (Hsafe old_resume source_mode location Hold Hmode Hold_source Hroot)
    as [[phase_mode [Hphase_mode Hphase]] | Hold_safe].
  - left. exists phase_mode. simpl. split; assumption.
  - right. intros exposure_mode target Hexposure_mode Htarget.
    eapply Hold_safe; [exact Hexposure_mode|].
    eapply (proj1 (proj2 Hexposure)); [exact Hold|].
    destruct Htarget as [target_seed [Htarget_seed Htarget_path]].
    exists target_seed. split; [exact Htarget_seed|].
    eapply frozen_caller_connected_after_descent_reflects; eauto.
Qed.

Lemma private_target_exposures_support_resume_phase_after_active_descent :
  forall CT h Z authority old_senv old_renv new_senv new_renv targets resumes,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame authority old_senv old_renv) targets ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame authority old_senv old_renv) resumes ->
    private_target_exposures_support_resume_phase Z targets resumes ->
    private_target_exposures_support_resume_phase Z
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) targets)
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) resumes).
Proof.
  intros CT h Z authority old_senv old_renv new_senv new_renv targets.
  induction targets as [|target target_tail IH]; intros resumes Hdescend
    Htarget_exposure Hresume_exposure Hsupport.
  - destruct resumes; simpl in *; [exact I|exact Hsupport].
  - destruct resumes as [|resume resume_tail].
    + destruct target; exact Hsupport.
    + simpl in *.
    destruct target as [target|].
    * destruct Hsupport as [Hhead Htail]. split.
      -- eapply frozen_source_resume_phase_safe_after_active_descent.
         ++ exact Hdescend.
         ++ exact ((proj1 (proj2 Htarget_exposure)) target
              (ltac:(simpl; auto))).
         ++ repeat split.
            ** intros snapshot Hsnapshot. eapply (proj1 Hresume_exposure);
                 simpl; eauto.
            ** intros snapshot Hsnapshot. eapply
                 (proj1 (proj2 Hresume_exposure)); simpl; eauto.
            ** intros snapshot mode location Hsnapshot. eapply
                 (proj1 (proj2 (proj2 Hresume_exposure))); simpl; eauto.
            ** intros snapshot Hsnapshot. eapply
                 (proj1 (proj2 (proj2 (proj2 Hresume_exposure))));
                 simpl; eauto.
            ** intros snapshot root Hsnapshot. eapply
                 (proj2 (proj2 (proj2 (proj2 Hresume_exposure))));
                 simpl; eauto.
         ++ exact Hhead.
      -- eapply IH; eauto.
         ++ eapply frozen_caller_snapshots_resume_exposures_wf_drop_head.
            exact Htarget_exposure.
         ++ eapply frozen_caller_snapshots_resume_exposures_wf_drop_head.
            exact Hresume_exposure.
    * eapply IH; eauto.
      -- eapply frozen_caller_snapshots_resume_exposures_wf_drop_head.
         exact Htarget_exposure.
      -- eapply frozen_caller_snapshots_resume_exposures_wf_drop_head.
         exact Hresume_exposure.
Qed.

Lemma frozen_completed_colors_resume_phase_safe_after_graph_reflection :
  forall CT h h' Z active incoming snapshots,
    (forall location,
      frame_owned_location CT h' active location ->
      frame_owned_location CT h active location) ->
    (forall left right,
      retained_mut_edge CT h' left right -> retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right -> mutable_edge CT h left right) ->
    frozen_caller_snapshots_resume_exposures_wf CT h active snapshots ->
    frozen_completed_colors_resume_phase_safe Z
      (executing_authority_color_set CT h active incoming) snapshots ->
    frozen_completed_colors_resume_phase_safe Z
      (executing_authority_color_set CT h' active incoming)
      (advance_frozen_caller_snapshots CT h' active snapshots).
Proof.
  intros CT h h' Z active incoming snapshots Howned Hretained Hmutable
    Hexposure Hsafe new_snapshot source_mode source Hnew Hsource_mode Hsource
    Hroot.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  destruct (executing_authority_colors_after_graph_reflection_covered CT h
    h' active incoming Howned Hretained Hmutable source_mode source
    Hsource_mode Hsource) as [old_mode [Hold_mode Hold_source]].
  destruct (Hsafe old_snapshot old_mode source Hold Hold_mode Hold_source
    Hroot) as [[phase_mode [Hphase_mode Hphase]] | Hold_safe].
  - left. exists phase_mode. split; assumption.
  - right. intros exposure_mode target Hexposure_mode Htarget.
    eapply Hold_safe; [exact Hexposure_mode|].
    eapply frozen_caller_closure_after_graph_reflection_included;
      [exact Hretained|exact Hmutable| |exact Htarget].
    exact ((proj1 (proj2 Hexposure)) old_snapshot Hold).
Qed.

Lemma frozen_caller_snapshots_nested_resume_phase_safe_after_graph_reflection :
  forall CT h h' Z active snapshots,
    (forall left right,
      retained_mut_edge CT h' left right -> retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right -> mutable_edge CT h left right) ->
    frozen_caller_snapshots_resume_exposures_wf CT h active snapshots ->
    frozen_caller_snapshots_nested_resume_phase_safe Z snapshots ->
    frozen_caller_snapshots_nested_resume_phase_safe Z
      (advance_frozen_caller_snapshots CT h' active snapshots).
Proof.
  intros CT h h' Z active snapshots Hretained Hmutable Hexposure Hnested.
  induction snapshots as [|slot tail IH]; simpl in *; [exact I|].
  destruct slot as [head|].
  - destruct Hnested as [Hhead Htail]. split.
    + intros Hhead_authority new_older source_mode source Hnew Hsource_mode
        Hsource Hroot.
      unfold advance_frozen_caller_snapshots in Hnew.
      apply in_map_iff in Hnew.
      destruct Hnew as [old_slot [Heq Hold]].
      destruct old_slot as [older|]; simpl in Heq; [|discriminate].
      injection Heq as <-. simpl in *.
      have Hold_source : In authority_flow_state
          head.(frozen_snapshot_current_resume_exposure)
          (source_mode, source).
      { eapply frozen_caller_closure_after_graph_reflection_included;
          [exact Hretained|exact Hmutable| |exact Hsource].
        exact ((proj1 (proj2 Hexposure)) head (ltac:(simpl; auto))). }
      destruct (Hhead Hhead_authority older source_mode source Hold
        Hsource_mode Hold_source Hroot) as
        [[phase_mode [Hphase_mode Hphase]] | Hold_safe].
      * left. exists phase_mode. simpl. split; assumption.
      * right. intros exposure_mode target Hexposure_mode Htarget.
        eapply Hold_safe; [exact Hexposure_mode|].
        eapply frozen_caller_closure_after_graph_reflection_included;
          [exact Hretained|exact Hmutable| |exact Htarget].
        exact ((proj1 (proj2 Hexposure)) older
          (ltac:(simpl; right; exact Hold))).
    + eapply IH.
      * repeat split.
        -- intros snapshot Hsnapshot. eapply (proj1 Hexposure); simpl; eauto.
        -- intros snapshot Hsnapshot. eapply (proj1 (proj2 Hexposure));
             simpl; eauto.
        -- intros snapshot mode location Hsnapshot. eapply
             (proj1 (proj2 (proj2 Hexposure))); simpl; eauto.
        -- intros snapshot Hsnapshot. eapply
             (proj1 (proj2 (proj2 (proj2 Hexposure)))); simpl; eauto.
        -- intros snapshot root Hsnapshot. eapply
             (proj2 (proj2 (proj2 (proj2 Hexposure)))); simpl; eauto.
      * exact Htail.
  - eapply IH.
    + repeat split.
      * intros snapshot Hsnapshot. eapply (proj1 Hexposure); simpl; eauto.
      * intros snapshot Hsnapshot. eapply (proj1 (proj2 Hexposure));
          simpl; eauto.
      * intros snapshot mode location Hsnapshot. eapply
          (proj1 (proj2 (proj2 Hexposure))); simpl; eauto.
      * intros snapshot Hsnapshot. eapply
          (proj1 (proj2 (proj2 (proj2 Hexposure)))); simpl; eauto.
      * intros snapshot root Hsnapshot. eapply
          (proj2 (proj2 (proj2 (proj2 Hexposure)))); simpl; eauto.
    + exact Hnested.
Qed.

Lemma frozen_source_resume_phase_safe_after_graph_reflection :
  forall CT h h' Z active source resumes,
    (forall left right,
      retained_mut_edge CT h' left right -> retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right -> mutable_edge CT h left right) ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h active source) source ->
    frozen_caller_snapshots_resume_exposures_wf CT h active resumes ->
    frozen_completed_colors_resume_phase_safe Z source resumes ->
    frozen_completed_colors_resume_phase_safe Z
      (frozen_caller_authority_closure CT h' active source)
      (advance_frozen_caller_snapshots CT h' active resumes).
Proof.
  intros CT h h' Z active source resumes Hretained Hmutable Hsource_closed
    Hexposure Hsafe new_resume source_mode location Hnew Hmode Hsource Hroot.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_resume|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  have Hold_source : In authority_flow_state source (source_mode, location).
  { eapply frozen_caller_closure_after_graph_reflection_included.
    - exact Hretained.
    - exact Hmutable.
    - exact Hsource_closed.
    - exact Hsource. }
  destruct (Hsafe old_resume source_mode location Hold Hmode Hold_source Hroot)
    as [[phase_mode [Hphase_mode Hphase]] | Hold_safe].
  - left. exists phase_mode. simpl. split; assumption.
  - right. intros exposure_mode target Hexposure_mode Htarget.
    eapply Hold_safe; [exact Hexposure_mode|].
    eapply frozen_caller_closure_after_graph_reflection_included.
    + exact Hretained.
    + exact Hmutable.
    + exact ((proj1 (proj2 Hexposure)) old_resume Hold).
    + exact Htarget.
Qed.

Lemma private_target_exposures_support_resume_phase_after_graph_reflection :
  forall CT h h' Z active targets resumes,
    (forall left right,
      retained_mut_edge CT h' left right -> retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right -> mutable_edge CT h left right) ->
    frozen_caller_snapshots_resume_exposures_wf CT h active targets ->
    frozen_caller_snapshots_resume_exposures_wf CT h active resumes ->
    private_target_exposures_support_resume_phase Z targets resumes ->
    private_target_exposures_support_resume_phase Z
      (advance_frozen_caller_snapshots CT h' active targets)
      (advance_frozen_caller_snapshots CT h' active resumes).
Proof.
  intros CT h h' Z active targets. induction targets as
    [|target target_tail IH]; intros resumes Hretained Hmutable
    Htarget_exposure Hresume_exposure Hsupport.
  - destruct resumes; simpl in *; [exact I|exact Hsupport].
  - destruct resumes as [|resume resume_tail].
    + destruct target; exact Hsupport.
    + simpl in *. destruct target as [target|].
      * destruct Hsupport as [Hhead Htail]. split.
        -- eapply frozen_source_resume_phase_safe_after_graph_reflection.
           ++ exact Hretained.
           ++ exact Hmutable.
           ++ exact ((proj1 (proj2 Htarget_exposure)) target
                (ltac:(simpl; auto))).
           ++ eapply frozen_caller_snapshots_resume_exposures_wf_drop_head.
              exact Hresume_exposure.
           ++ exact Hhead.
        -- eapply IH; eauto using
             frozen_caller_snapshots_resume_exposures_wf_drop_head.
      * eapply IH; eauto using
          frozen_caller_snapshots_resume_exposures_wf_drop_head.
Qed.

Lemma frozen_caller_closure_after_graph_reflection_between :
  forall CT h h' active old_colors new_colors,
    (forall left right,
      retained_mut_edge CT h' left right -> retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right -> mutable_edge CT h left right) ->
    Included authority_flow_state new_colors old_colors ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h active old_colors) old_colors ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h' active new_colors) old_colors.
Proof.
  intros CT h h' active old_colors new_colors Hretained Hmutable Hseeds
    Hclosed state Hstate.
  have Hmono : In authority_flow_state
      (frozen_caller_authority_closure CT h' active old_colors) state.
  { eapply frozen_caller_authority_closure_monotone.
    - exact Hseeds.
    - exact Hstate. }
  exact (frozen_caller_closure_after_graph_reflection_included CT h h'
    active old_colors Hretained Hmutable Hclosed state Hmono).
Qed.

Lemma frozen_target_colors_resume_phase_safe_after_graph_reflection :
  forall CT h h' Z active incoming targets,
    (forall location,
      frame_owned_location CT h' active location ->
      frame_owned_location CT h active location) ->
    (forall left right,
      retained_mut_edge CT h' left right -> retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right -> mutable_edge CT h left right) ->
    frozen_caller_snapshots_resume_exposures_wf CT h active targets ->
    frozen_target_colors_resume_phase_safe CT h Z
      (executing_authority_color_set CT h active incoming) targets ->
    frozen_target_colors_resume_phase_safe CT h' Z
      (executing_authority_color_set CT h' active incoming)
      (advance_frozen_caller_snapshots CT h' active targets).
Proof.
  intros CT h h' Z active incoming targets Howned Hretained Hmutable
    Hexposure Hsafe.
  unfold frozen_target_colors_resume_phase_safe in *.
  eapply frozen_completed_colors_resume_phase_safe_after_graph_reflection;
    eauto.
Qed.

Lemma frozen_target_snapshots_nested_phase_safe_after_graph_reflection :
  forall CT h h' Z active targets,
    (forall left right,
      retained_mut_edge CT h' left right -> retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right -> mutable_edge CT h left right) ->
    frozen_caller_snapshots_resume_exposures_wf CT h active targets ->
    frozen_caller_snapshots_nested_resume_phase_safe Z targets ->
    frozen_target_snapshots_nested_resume_phase_safe CT h Z targets ->
    frozen_caller_snapshots_nested_resume_phase_safe Z
      (advance_frozen_caller_snapshots CT h' active targets).
Proof.
  intros CT h h' Z active targets Hretained Hmutable Hexposure Hlegacy Hsafe.
  eapply frozen_caller_snapshots_nested_resume_phase_safe_after_graph_reflection;
    eauto using Hlegacy.
Qed.

Lemma private_saved_target_exposures_after_graph_reflection :
  forall CT h h' Z active targets resumes,
    (forall left right,
      retained_mut_edge CT h' left right -> retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right -> mutable_edge CT h left right) ->
    frozen_caller_snapshots_resume_exposures_wf CT h active targets ->
    frozen_caller_snapshots_resume_exposures_wf CT h active resumes ->
    private_target_exposures_support_resume_phase Z targets resumes ->
    private_saved_target_exposures_support_resume_phase CT h Z targets
      resumes ->
    private_target_exposures_support_resume_phase Z
      (advance_frozen_caller_snapshots CT h' active targets)
      (advance_frozen_caller_snapshots CT h' active resumes).
Proof.
  intros CT h h' Z active targets resumes Hretained Hmutable
    Htarget_exposure Hresume_exposure Hlegacy Hsupport.
  eapply private_target_exposures_support_resume_phase_after_graph_reflection;
    eauto using Hlegacy.
Qed.

Lemma frozen_completed_colors_resume_phase_safe_after_safe_field_update :
  forall CT h Z frame incoming snapshots lx old field written,
    runtime_getObj h lx = Some old ->
    authority_colors_runtime_mutable h
      (executing_authority_color_set CT h frame incoming) ->
    frozen_caller_snapshots_resume_exposures_wf CT h frame snapshots ->
    authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h frame) ->
    authority_safe_field_endpoints CT h frame lx written ->
    frozen_completed_colors_resume_phase_safe Z
      (executing_authority_color_set CT h frame incoming) snapshots ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h frame)
        (active_mode, location) ->
      ~ In Loc Z location) ->
    frozen_completed_colors_resume_phase_safe Z
      (executing_authority_color_set CT
        (update_field h lx field (Iot written)) frame incoming)
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame snapshots).
Proof.
  intros CT h Z frame incoming snapshots lx old field written Hobj
    Hcompleted_runtime Hexposure Hactive_runtime Hendpoints Hsafe Hactive_safe
    new_snapshot source_mode source Hnew Hsource_mode Hsource Hsource_root.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  destruct (executing_authority_colors_after_safe_field_update_covered CT h
    frame incoming lx old field written Hobj Hcompleted_runtime Hendpoints
    source_mode source Hsource_mode Hsource) as
    [old_source_mode [Hold_source_mode Hold_source]].
  destruct (Hsafe old_snapshot old_source_mode source Hold Hold_source_mode
    Hold_source Hsource_root) as
    [[phase_mode [Hphase_mode Hphase]] | Hold_safe].
  - left. exists phase_mode. split; assumption.
  - right. intros exposure_mode target Hexposure_mode Htarget.
    destruct Htarget as [seed [Hseed Hpath]].
    destruct seed as [seed_mode seed_location].
    have Hseed_covered : frozen_authority_state_covered_by_old_or_active
        old_snapshot.(frozen_snapshot_current_resume_exposure)
        (independent_active_authority_colors CT h frame)
        (seed_mode, seed_location).
    { intros Hseed_mode. left. exists seed_mode. split; assumption. }
    have Hcovered :=
      frozen_caller_connected_after_safe_field_update_covered_by_old_or_active
        CT h frame old_snapshot.(frozen_snapshot_current_resume_exposure)
        lx old field written (seed_mode, seed_location)
        (exposure_mode, target) Hobj
        ((proj1 Hexposure) old_snapshot Hold)
        ((proj1 (proj2 Hexposure)) old_snapshot Hold)
        Hactive_runtime Hendpoints Hseed_covered Hpath.
    destruct (Hcovered Hexposure_mode) as
      [[old_target_mode [Hold_target_mode Hold_target]] |
       [active_target_mode [Hactive_target_mode Hactive_target]]].
    + exact (Hold_safe old_target_mode target Hold_target_mode Hold_target).
    + exact (Hactive_safe active_target_mode target Hactive_target_mode
        Hactive_target).
Qed.

Lemma frozen_caller_snapshots_nested_resume_phase_safe_after_safe_field_update :
  forall CT h Z frame snapshots lx old field written,
    runtime_getObj h lx = Some old ->
    frozen_caller_snapshots_resume_exposures_wf CT h frame snapshots ->
    authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h frame) ->
    authority_safe_field_endpoints CT h frame lx written ->
    frozen_caller_snapshots_nested_resume_phase_safe Z snapshots ->
    frozen_completed_colors_resume_phase_safe Z
      (independent_active_authority_colors CT h frame) snapshots ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h frame)
        (active_mode, location) ->
      ~ In Loc Z location) ->
    frozen_caller_snapshots_nested_resume_phase_safe Z
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame snapshots).
Proof.
  intros CT h Z frame snapshots lx old field written Hobj Hexposure
    Hactive_runtime Hendpoints Hnested Hactive_phase Hactive_safe.
  induction snapshots as [|slot tail IH]; simpl in *; [exact I|].
  destruct slot as [head|].
  - destruct Hnested as [Hhead Htail]. split.
    + intros Hhead_authority new_older source_mode source Hnew Hsource_mode
        Hsource Hroot.
      unfold advance_frozen_caller_snapshots in Hnew.
      apply in_map_iff in Hnew.
      destruct Hnew as [old_slot [Heq Hold]].
      destruct old_slot as [older|]; simpl in Heq; [|discriminate].
      injection Heq as <-. simpl in *.
      destruct Hsource as [seed [Hseed Hpath]].
      destruct seed as [seed_mode seed_location].
      have Hseed_mode := (proj1 (proj2 (proj2 Hexposure))) head seed_mode
        seed_location (ltac:(simpl; auto)) Hseed.
      have Hseed_covered : frozen_authority_state_covered_by_old_or_active
          head.(frozen_snapshot_current_resume_exposure)
          (independent_active_authority_colors CT h frame)
          (seed_mode, seed_location).
      { intros Hseed_dangerous. left. exists seed_mode.
        split; [exact Hseed_dangerous|exact Hseed]. }
      have Hcovered :=
        frozen_caller_connected_after_safe_field_update_covered_by_old_or_active
          CT h frame head.(frozen_snapshot_current_resume_exposure)
          lx old field written (seed_mode, seed_location)
          (source_mode, source) Hobj
          ((proj1 Hexposure) head (ltac:(simpl; auto)))
          ((proj1 (proj2 Hexposure)) head (ltac:(simpl; auto)))
          Hactive_runtime Hendpoints Hseed_covered Hpath.
      destruct (Hcovered Hsource_mode) as
        [[old_mode [Hold_mode Hold_source]] |
         [active_mode [Hactive_mode Hactive_source]]].
      * destruct (Hhead Hhead_authority older old_mode source Hold Hold_mode
          Hold_source Hroot)
          as [[phase_mode [Hphase_mode Hphase]] | Hold_safe].
        -- left. exists phase_mode. simpl. split; assumption.
        -- right. intros exposure_mode target Hexposure_mode Htarget.
           destruct Htarget as [target_seed [Htarget_seed Htarget_path]].
           destruct target_seed as [target_seed_mode target_seed_location].
           have Htarget_seed_covered :
               frozen_authority_state_covered_by_old_or_active
                 older.(frozen_snapshot_current_resume_exposure)
                 (independent_active_authority_colors CT h frame)
                 (target_seed_mode, target_seed_location).
           { intros Htarget_seed_dangerous. left. exists target_seed_mode.
             split; [exact Htarget_seed_dangerous|exact Htarget_seed]. }
           have Htarget_covered :=
             frozen_caller_connected_after_safe_field_update_covered_by_old_or_active
               CT h frame older.(frozen_snapshot_current_resume_exposure)
               lx old field written
               (target_seed_mode, target_seed_location)
               (exposure_mode, target) Hobj
               ((proj1 Hexposure) older (ltac:(simpl; right; exact Hold)))
               ((proj1 (proj2 Hexposure)) older
                 (ltac:(simpl; right; exact Hold)))
               Hactive_runtime Hendpoints Htarget_seed_covered Htarget_path.
           destruct (Htarget_covered Hexposure_mode) as
             [[old_target_mode [Hold_target_mode Hold_target]] |
              [active_target_mode [Hactive_target_mode Hactive_target]]].
           ++ eapply Hold_safe; eauto.
           ++ eapply Hactive_safe; eauto.
      * destruct (Hactive_phase older active_mode source
          (ltac:(simpl; right; exact Hold)) Hactive_mode Hactive_source Hroot)
          as [[phase_mode [Hphase_mode Hphase]] | Hold_safe].
        -- left. exists phase_mode. simpl. split; assumption.
        -- right. intros exposure_mode target Hexposure_mode Htarget.
           destruct Htarget as [target_seed [Htarget_seed Htarget_path]].
           destruct target_seed as [target_seed_mode target_seed_location].
           have Htarget_seed_covered :
               frozen_authority_state_covered_by_old_or_active
                 older.(frozen_snapshot_current_resume_exposure)
                 (independent_active_authority_colors CT h frame)
                 (target_seed_mode, target_seed_location).
           { intros Htarget_seed_dangerous. left. exists target_seed_mode.
             split; [exact Htarget_seed_dangerous|exact Htarget_seed]. }
           have Htarget_covered :=
             frozen_caller_connected_after_safe_field_update_covered_by_old_or_active
               CT h frame older.(frozen_snapshot_current_resume_exposure)
               lx old field written
               (target_seed_mode, target_seed_location)
               (exposure_mode, target) Hobj
               ((proj1 Hexposure) older (ltac:(simpl; right; exact Hold)))
               ((proj1 (proj2 Hexposure)) older
                 (ltac:(simpl; right; exact Hold)))
               Hactive_runtime Hendpoints Htarget_seed_covered Htarget_path.
           destruct (Htarget_covered Hexposure_mode) as
             [[old_target_mode [Hold_target_mode Hold_target]] |
              [active_target_mode [Hactive_target_mode Hactive_target]]].
           ++ eapply Hold_safe; eauto.
           ++ eapply Hactive_safe; eauto.
    + eapply IH.
      * repeat split.
        -- intros snapshot Hsnapshot. eapply (proj1 Hexposure); simpl; eauto.
        -- intros snapshot Hsnapshot. eapply (proj1 (proj2 Hexposure));
             simpl; eauto.
        -- intros snapshot mode location Hsnapshot. eapply
             (proj1 (proj2 (proj2 Hexposure))); simpl; eauto.
        -- intros snapshot Hsnapshot. eapply
             (proj1 (proj2 (proj2 (proj2 Hexposure)))); simpl; eauto.
        -- intros snapshot root Hsnapshot. eapply
             (proj2 (proj2 (proj2 (proj2 Hexposure)))); simpl; eauto.
      * exact Htail.
      * intros snapshot source_mode source Hsnapshot. eapply Hactive_phase.
        simpl; right; exact Hsnapshot.
  - eapply IH.
    + repeat split.
      * intros snapshot Hsnapshot. eapply (proj1 Hexposure); simpl; eauto.
      * intros snapshot Hsnapshot. eapply (proj1 (proj2 Hexposure));
          simpl; eauto.
      * intros snapshot mode location Hsnapshot. eapply
          (proj1 (proj2 (proj2 Hexposure))); simpl; eauto.
      * intros snapshot Hsnapshot. eapply
          (proj1 (proj2 (proj2 (proj2 Hexposure)))); simpl; eauto.
      * intros snapshot root Hsnapshot. eapply
          (proj2 (proj2 (proj2 (proj2 Hexposure)))); simpl; eauto.
    + exact Hnested.
    + intros snapshot source_mode source Hsnapshot. eapply Hactive_phase.
      simpl; right; exact Hsnapshot.
Qed.

Lemma frozen_source_resume_phase_safe_after_safe_field_update :
  forall CT h Z frame source resumes lx old field written,
    runtime_getObj h lx = Some old ->
    authority_colors_runtime_mutable h source ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h frame source) source ->
    frozen_caller_snapshots_resume_exposures_wf CT h frame resumes ->
    authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h frame) ->
    authority_safe_field_endpoints CT h frame lx written ->
    frozen_completed_colors_resume_phase_safe Z source resumes ->
    frozen_completed_colors_resume_phase_safe Z
      (independent_active_authority_colors CT h frame) resumes ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h frame)
        (active_mode, location) ->
      ~ In Loc Z location) ->
    frozen_completed_colors_resume_phase_safe Z
      (frozen_caller_authority_closure CT
        (update_field h lx field (Iot written)) frame source)
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame resumes).
Proof.
  intros CT h Z frame source resumes lx old field written Hobj Hsource_runtime
    Hsource_closed Hexposure Hactive_runtime Hendpoints Hsafe Hactive_phase
    Hactive_safe new_resume source_mode location Hnew Hmode
    [seed [Hseed Hpath]] Hroot.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_resume|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  destruct seed as [seed_mode seed_location].
  have Hseed_covered : frozen_authority_state_covered_by_old_or_active source
      (independent_active_authority_colors CT h frame)
      (seed_mode, seed_location).
  { intros Hseed_mode. left. exists seed_mode. split; assumption. }
  have Hcovered :=
    frozen_caller_connected_after_safe_field_update_covered_by_old_or_active
      CT h frame source lx old field written (seed_mode, seed_location)
      (source_mode, location) Hobj Hsource_runtime Hsource_closed
      Hactive_runtime Hendpoints Hseed_covered Hpath.
  have Hlift_safe : frozen_snapshot_resume_exposure_avoids Z old_resume ->
      frozen_snapshot_resume_exposure_avoids Z
        (advance_frozen_caller_snapshot CT
          (update_field h lx field (Iot written)) frame old_resume).
  { intros Hold_safe exposure_mode target Hexposure_mode Htarget.
    destruct Htarget as [target_seed [Htarget_seed Htarget_path]].
    destruct target_seed as [target_seed_mode target_seed_location].
    have Htarget_seed_covered : frozen_authority_state_covered_by_old_or_active
        old_resume.(frozen_snapshot_current_resume_exposure)
        (independent_active_authority_colors CT h frame)
        (target_seed_mode, target_seed_location).
    { intros Htarget_seed_mode. left. exists target_seed_mode.
      split; assumption. }
    have Htarget_covered :=
      frozen_caller_connected_after_safe_field_update_covered_by_old_or_active
        CT h frame old_resume.(frozen_snapshot_current_resume_exposure)
        lx old field written (target_seed_mode, target_seed_location)
        (exposure_mode, target) Hobj
        ((proj1 Hexposure) old_resume Hold)
        ((proj1 (proj2 Hexposure)) old_resume Hold)
        Hactive_runtime Hendpoints Htarget_seed_covered Htarget_path.
    destruct (Htarget_covered Hexposure_mode) as
      [[old_target_mode [Hold_target_mode Hold_target]] |
       [active_target_mode [Hactive_target_mode Hactive_target]]].
    - eapply Hold_safe; eauto.
    - eapply Hactive_safe; eauto. }
  destruct (Hcovered Hmode) as
    [[old_mode [Hold_mode Hold_source]] |
     [active_mode [Hactive_mode Hactive_source]]].
  - destruct (Hsafe old_resume old_mode location Hold Hold_mode Hold_source
      Hroot) as [[phase_mode [Hphase_mode Hphase]] | Hold_safe].
    + left. exists phase_mode. simpl. split; assumption.
    + right. exact (Hlift_safe Hold_safe).
  - destruct (Hactive_phase old_resume active_mode location Hold Hactive_mode
      Hactive_source Hroot) as
      [[phase_mode [Hphase_mode Hphase]] | Hold_safe].
    + left. exists phase_mode. simpl. split; assumption.
    + right. exact (Hlift_safe Hold_safe).
Qed.

Lemma private_target_exposures_support_resume_phase_after_safe_field_update :
  forall CT h Z frame targets resumes lx old field written,
    runtime_getObj h lx = Some old ->
    frozen_caller_snapshots_resume_exposures_wf CT h frame targets ->
    frozen_caller_snapshots_resume_exposures_wf CT h frame resumes ->
    authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h frame) ->
    authority_safe_field_endpoints CT h frame lx written ->
    private_target_exposures_support_resume_phase Z targets resumes ->
    frozen_completed_colors_resume_phase_safe Z
      (independent_active_authority_colors CT h frame) resumes ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h frame)
        (active_mode, location) ->
      ~ In Loc Z location) ->
    private_target_exposures_support_resume_phase Z
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame targets)
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame resumes).
Proof.
  intros CT h Z frame targets. induction targets as [|target target_tail IH];
    intros resumes lx old field written Hobj Htarget_exposure Hresume_exposure
      Hactive_runtime Hendpoints Hsupport Hactive_phase Hactive_safe.
  - destruct resumes; simpl in *; [exact I|exact Hsupport].
  - destruct resumes as [|resume resume_tail].
    + destruct target; exact Hsupport.
    + simpl in *. destruct target as [target|].
      * destruct Hsupport as [Hhead Htail]. split.
        -- eapply frozen_source_resume_phase_safe_after_safe_field_update.
           ++ exact Hobj.
           ++ exact ((proj1 Htarget_exposure) target (ltac:(simpl; auto))).
           ++ exact ((proj1 (proj2 Htarget_exposure)) target
                (ltac:(simpl; auto))).
           ++ eapply frozen_caller_snapshots_resume_exposures_wf_drop_head.
              exact Hresume_exposure.
           ++ exact Hactive_runtime.
           ++ exact Hendpoints.
           ++ exact Hhead.
           ++ intros snapshot source_mode source Hsnapshot.
              eapply Hactive_phase. simpl; right; exact Hsnapshot.
           ++ exact Hactive_safe.
        -- eapply IH; eauto using
             frozen_caller_snapshots_resume_exposures_wf_drop_head.
           intros snapshot source_mode source Hsnapshot.
           eapply Hactive_phase. simpl; right; exact Hsnapshot.
      * eapply IH; eauto using
          frozen_caller_snapshots_resume_exposures_wf_drop_head.
        intros snapshot source_mode source Hsnapshot.
        eapply Hactive_phase. simpl; right; exact Hsnapshot.
Qed.

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

Lemma private_target_history_supports_resume_phase_in :
  forall Z targets resumes resume,
    private_target_supports_resume_witnesses targets resumes ->
    private_target_history_supports_resume_phase Z targets resumes ->
    List.In (Some resume) resumes ->
    exists target,
      List.In (Some target) targets /\
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
      (forall source_mode source,
        authority_mode_dangerous source_mode ->
        In authority_flow_state target.(frozen_snapshot_phase_incoming)
          (source_mode, source) ->
        In Loc resume.(frozen_snapshot_resume_rdm_roots) source ->
        (exists phase_mode,
          authority_mode_dangerous phase_mode /\
          In authority_flow_state resume.(frozen_snapshot_phase_incoming)
            (phase_mode, source)) \/
        frozen_snapshot_resume_exposure_avoids Z resume).
Proof.
  intros Z targets. induction targets as [|target tail IH];
    intros resumes resume Hmetadata Hhistory Hin.
  - destruct resumes; simpl in *; contradiction.
  - destruct resumes as [|resume_slot resume_tail];
      [simpl in Hmetadata; contradiction|].
    destruct target as [target|], resume_slot as [resume_head|];
      simpl in Hmetadata, Hhistory, Hin; try contradiction.
    + destruct Hmetadata as
        [Hphase [Hroots [Hentry [Hexposure Hmetadata_tail]]]].
      destruct Hhistory as [Hhead Hhistory_tail].
      destruct Hin as [Heq | Hin].
      * injection Heq as <-. exists target. split; [simpl; auto|].
        exact (conj Hphase (conj Hroots
          (conj Hentry (conj Hexposure Hhead)))).
      * destruct (IH resume_tail resume Hmetadata_tail Hhistory_tail Hin) as
          [older [Holder Hrelations]].
        exists older. split; [simpl; right; exact Holder|exact Hrelations].
    + destruct Hin as [Hbad | Hin]; [discriminate|].
      destruct (IH resume_tail resume Hmetadata Hhistory Hin) as
        [older [Holder Hrelations]].
      exists older. split; [simpl; right; exact Holder|exact Hrelations].
    + destruct Hin as [Hbad | Hin]; [discriminate|].
      destruct (IH resume_tail resume Hmetadata Hhistory Hin) as
        [older [Holder Hrelations]].
      exists older. split; [simpl; right; exact Holder|exact Hrelations].
Qed.

Lemma private_target_history_supports_resume_phase_after_advance :
  forall CT h Z active targets resumes,
    private_target_history_supports_resume_phase Z targets resumes ->
    (forall resume,
      List.In (Some resume) resumes ->
      frozen_snapshot_resume_exposure_avoids Z resume ->
      frozen_snapshot_resume_exposure_avoids Z
        (advance_frozen_caller_snapshot CT h active resume)) ->
    private_target_history_supports_resume_phase Z
      (advance_frozen_caller_snapshots CT h active targets)
      (advance_frozen_caller_snapshots CT h active resumes).
Proof.
  intros CT h Z active targets. induction targets as [|target tail IH];
    intros resumes Hhistory Hsafe.
  - destruct resumes; simpl in *; assumption.
  - destruct resumes as [|resume resume_tail]; simpl in *.
    + destruct target; exact Hhistory.
    + destruct target as [target|], resume as [resume|]; simpl in *.
      * destruct Hhistory as [Hhead Htail]. split.
        -- intros source_mode source Hmode Hphase Hroot.
           destruct (Hhead source_mode source Hmode Hphase Hroot) as
             [Hresume_phase | Hresume_safe].
           ++ left. exact Hresume_phase.
           ++ right. eapply Hsafe; [simpl; auto|exact Hresume_safe].
        -- eapply IH; [exact Htail|].
           intros older Holder. eapply Hsafe. simpl; right; exact Holder.
      * eapply IH; [exact Hhistory|].
        intros older Holder. eapply Hsafe. simpl; right; exact Holder.
      * contradiction.
      * eapply IH; [exact Hhistory|].
        intros older Holder. eapply Hsafe. simpl; right; exact Holder.
Qed.

Lemma private_target_history_supports_resume_phase_after_active_descent :
  forall CT h Z authority old_senv old_renv new_senv new_renv targets resumes,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame authority old_senv old_renv) resumes ->
    private_target_history_supports_resume_phase Z targets resumes ->
    private_target_history_supports_resume_phase Z
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) targets)
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) resumes).
Proof.
  intros CT h Z authority old_senv old_renv new_senv new_renv targets
    resumes Hdescend Hexposure Hhistory.
  eapply private_target_history_supports_resume_phase_after_advance;
    [exact Hhistory|].
  intros resume Hresume Hsafe exposure_mode location Hmode Hcolor.
  eapply Hsafe; [exact Hmode|].
  eapply (proj1 (proj2 Hexposure)); [exact Hresume|].
  destruct Hcolor as [seed [Hseed Hpath]]. exists seed.
  split; [exact Hseed|].
  eapply frozen_caller_connected_after_descent_reflects; eauto.
Qed.

Lemma private_target_history_supports_resume_phase_after_graph_reflection :
  forall CT h h' Z active targets resumes,
    (forall left right,
      retained_mut_edge CT h' left right -> retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right -> mutable_edge CT h left right) ->
    frozen_caller_snapshots_resume_exposures_wf CT h active resumes ->
    private_target_history_supports_resume_phase Z targets resumes ->
    private_target_history_supports_resume_phase Z
      (advance_frozen_caller_snapshots CT h' active targets)
      (advance_frozen_caller_snapshots CT h' active resumes).
Proof.
  intros CT h h' Z active targets resumes Hretained Hmutable Hexposure
    Hhistory.
  eapply private_target_history_supports_resume_phase_after_advance;
    [exact Hhistory|].
  intros resume Hresume Hsafe exposure_mode location Hmode Hcolor.
  eapply Hsafe; [exact Hmode|].
  eapply frozen_caller_closure_after_graph_reflection_included.
  - exact Hretained.
  - exact Hmutable.
  - exact ((proj1 (proj2 Hexposure)) resume Hresume).
  - exact Hcolor.
Qed.

Lemma private_target_history_supports_resume_phase_after_safe_field_update :
  forall CT h Z frame targets resumes lx old field written,
    runtime_getObj h lx = Some old ->
    frozen_caller_snapshots_resume_exposures_wf CT h frame resumes ->
    authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h frame) ->
    authority_safe_field_endpoints CT h frame lx written ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h frame)
        (active_mode, location) ->
      ~ In Loc Z location) ->
    private_target_history_supports_resume_phase Z targets resumes ->
    private_target_history_supports_resume_phase Z
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame targets)
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame resumes).
Proof.
  intros CT h Z frame targets resumes lx old field written Hobj Hexposure
    Hactive_runtime Hendpoints Hactive_safe Hhistory.
  eapply private_target_history_supports_resume_phase_after_advance;
    [exact Hhistory|].
  intros resume Hresume Hsafe exposure_mode location Hmode Hcolor.
  destruct Hcolor as [seed [Hseed Hpath]].
  destruct seed as [seed_mode seed_location].
  have Hseed_covered : frozen_authority_state_covered_by_old_or_active
      resume.(frozen_snapshot_current_resume_exposure)
      (independent_active_authority_colors CT h frame)
      (seed_mode, seed_location).
  { intros Hseed_mode. left. exists seed_mode. split; assumption. }
  have Hcovered :=
    frozen_caller_connected_after_safe_field_update_covered_by_old_or_active
      CT h frame resume.(frozen_snapshot_current_resume_exposure)
      lx old field written (seed_mode, seed_location)
      (exposure_mode, location) Hobj
      ((proj1 Hexposure) resume Hresume)
      ((proj1 (proj2 Hexposure)) resume Hresume)
      Hactive_runtime Hendpoints Hseed_covered Hpath.
  destruct (Hcovered Hmode) as
    [[old_mode [Hold_mode Hold_color]] |
     [active_mode [Hactive_mode Hactive_color]]].
  - eapply Hsafe; eauto.
  - eapply Hactive_safe; eauto.
Qed.

Lemma private_target_supports_resume_witnesses_in :
  forall targets resumes resume,
    private_target_supports_resume_witnesses targets resumes ->
    List.In (Some resume) resumes ->
    exists target,
      List.In (Some target) targets /\
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
        target.(frozen_snapshot_current_resume_exposure).
Proof.
  intros targets. induction targets as [|target target_tail IH];
    intros resumes resume Hsupport Hin.
  - destruct resumes; simpl in *; contradiction.
  - destruct resumes as [|resume_slot resume_tail];
      [simpl in Hsupport; contradiction|].
    destruct target as [target|], resume_slot as [resume_head|];
      simpl in Hsupport, Hin; try contradiction.
    + destruct Hsupport as
        [Hphase [Hroots [Hentry [Hcurrent Htail]]]].
      destruct Hin as [Heq | Hin].
      * injection Heq as <-. exists target. split.
        -- simpl; auto.
        -- split; [exact Hphase|]. split; [exact Hroots|].
           split; assumption.
      * destruct (IH resume_tail resume Htail Hin) as
          [older [Holder Hrelations]].
        exists older. split; [simpl; right; exact Holder|exact Hrelations].
    + destruct Hin as [Hbad | Hin]; [discriminate|].
      destruct (IH resume_tail resume Hsupport Hin) as
        [older [Holder Hrelations]].
      exists older. split; [simpl; right; exact Holder|exact Hrelations].
    + destruct Hin as [Hbad | Hin]; [discriminate|].
      destruct (IH resume_tail resume Hsupport Hin) as
        [older [Holder Hrelations]].
      exists older. split; [simpl; right; exact Holder|exact Hrelations].
Qed.

Lemma target_support_phase_or_safe_transfers_to_resume :
  forall Z target resume source,
    Same_set authority_flow_state
      resume.(frozen_snapshot_phase_incoming)
      target.(frozen_snapshot_phase_incoming) ->
    Same_set authority_flow_state
      resume.(frozen_snapshot_current_resume_exposure)
      target.(frozen_snapshot_current_resume_exposure) ->
    ((exists phase_mode,
      authority_mode_dangerous phase_mode /\
      In authority_flow_state target.(frozen_snapshot_phase_incoming)
        (phase_mode, source)) \/
     frozen_snapshot_resume_exposure_avoids Z target) ->
    (exists phase_mode,
      authority_mode_dangerous phase_mode /\
      In authority_flow_state resume.(frozen_snapshot_phase_incoming)
        (phase_mode, source)) \/
    frozen_snapshot_resume_exposure_avoids Z resume.
Proof.
  intros Z target resume source Hphase Hexposure [Hphase_color | Hsafe].
  - left. destruct Hphase_color as
      [phase_mode [Hphase_mode Hphase_color]].
    exists phase_mode. split; [exact Hphase_mode|].
    eapply (proj2 Hphase). exact Hphase_color.
  - right. intros exposure_mode location Hmode Hcolor.
    eapply Hsafe; [exact Hmode|]. eapply (proj1 Hexposure). exact Hcolor.
Qed.

Lemma target_phase_safe_transfers_to_resume_witnesses :
  forall Z completed targets resumes,
    private_target_supports_resume_witnesses targets resumes ->
    private_target_history_supports_resume_phase Z targets resumes ->
    frozen_completed_colors_resume_phase_safe Z completed targets ->
    frozen_completed_colors_resume_phase_safe Z completed resumes.
Proof.
  intros Z completed targets resumes Hsupport Hhistory Hsafe resume source_mode
    source Hresume Hmode Hcolor Hroot.
  destruct (private_target_history_supports_resume_phase_in Z targets resumes
    resume Hsupport Hhistory Hresume) as
    [target [Htarget [_ [Hroots [_ [Hexposure Hhistory_property]]]]]].
  have Htarget_root : In Loc target.(frozen_snapshot_resume_rdm_roots) source.
  { eapply (proj1 Hroots). exact Hroot. }
  destruct (Hsafe target source_mode source Htarget Hmode Hcolor Htarget_root)
    as [[phase_mode [Hphase_mode Hphase]] | Htarget_safe].
  - exact (Hhistory_property phase_mode source Hphase_mode Hphase Hroot).
  - right. intros exposure_mode location Hexposure_mode Hresume_color.
    eapply Htarget_safe; [exact Hexposure_mode|].
    eapply (proj1 Hexposure). exact Hresume_color.
Qed.

Lemma frozen_caller_authority_closure_same_set :
  forall CT h active left right,
    Same_set authority_flow_state left right ->
    Same_set authority_flow_state
      (frozen_caller_authority_closure CT h active left)
      (frozen_caller_authority_closure CT h active right).
Proof.
  intros CT h active left right [Hleft Hright]. split;
    eapply frozen_caller_authority_closure_monotone; assumption.
Qed.

Lemma private_target_supports_resume_witnesses_after_advance :
  forall CT h active targets resumes,
    private_target_supports_resume_witnesses targets resumes ->
    private_target_supports_resume_witnesses
      (advance_frozen_caller_snapshots CT h active targets)
      (advance_frozen_caller_snapshots CT h active resumes).
Proof.
  intros CT h active targets. induction targets as [|target target_tail IH];
    intros resumes Hsupport; destruct resumes as [|resume resume_tail].
  - exact I.
  - destruct resume; exact Hsupport.
  - destruct target; exact Hsupport.
  - destruct target as [target|], resume as [resume|]; simpl in *;
      try contradiction.
    + destruct Hsupport as
      [Hphase [Hroots [Hentry_exposure [Hexposure Htail]]]].
      unfold advance_frozen_caller_snapshot. simpl. split; [exact Hphase|].
      split; [exact Hroots|]. split; [exact Hentry_exposure|]. split.
      * eapply frozen_caller_authority_closure_same_set. exact Hexposure.
      * eapply IH. exact Htail.
    + eapply IH. exact Hsupport.
    + eapply IH. exact Hsupport.
Qed.

Lemma private_target_supports_resume_witnesses_after_target_activation :
  forall CT h caller actual targets resumes,
    private_target_supports_resume_witnesses targets resumes ->
    private_target_supports_resume_witnesses
      (activate_frozen_target_snapshots CT h caller actual targets)
      (advance_frozen_caller_snapshots CT h caller resumes).
Proof.
  intros CT h caller actual targets.
  induction targets as [|target target_tail IH]; intros resumes Hsupport;
    destruct resumes as [|resume resume_tail].
  - exact I.
  - destruct resume; exact Hsupport.
  - destruct target; exact Hsupport.
  - destruct target as [target|], resume as [resume|]; simpl in *;
      try contradiction.
    + destruct Hsupport as
        [Hphase [Hroots [Hentry_exposure [Hexposure Htail]]]].
      split; [exact Hphase|]. split; [exact Hroots|].
      split; [exact Hentry_exposure|]. split.
      * eapply frozen_caller_authority_closure_same_set. exact Hexposure.
      * eapply IH. exact Htail.
    + eapply IH. exact Hsupport.
    + eapply IH. exact Hsupport.
Qed.

Lemma private_target_history_supports_resume_phase_after_target_activation :
  forall CT h Z caller actual targets resumes,
    private_target_history_supports_resume_phase Z targets resumes ->
    (forall resume,
      List.In (Some resume) resumes ->
      frozen_snapshot_resume_exposure_avoids Z resume ->
      frozen_snapshot_resume_exposure_avoids Z
        (advance_frozen_caller_snapshot CT h caller resume)) ->
    frozen_completed_colors_resume_phase_safe Z actual
      (advance_frozen_caller_snapshots CT h caller resumes) ->
    private_target_history_supports_resume_phase Z
      (activate_frozen_target_snapshots CT h caller actual targets)
      (advance_frozen_caller_snapshots CT h caller resumes).
Proof.
  intros CT h Z caller actual targets. induction targets as
    [|target target_tail IH]; intros resumes Hhistory Hlift Hactual;
    destruct resumes as [|resume resume_tail]; simpl in *.
  - exact I.
  - contradiction.
  - destruct target; exact Hhistory.
  - destruct target as [target|], resume as [resume|]; simpl in *;
      try contradiction.
    + destruct Hhistory as [Hhead Htail]. split.
      * intros source_mode source Hmode Hphase Hroot.
        have Hphase_cases :
            In authority_flow_state target.(frozen_snapshot_phase_incoming)
              (source_mode, source) \/
            In authority_flow_state actual (source_mode, source).
        { inversion Hphase; subst; auto. }
        destruct Hphase_cases as [Hold_phase | Hactual_phase].
        -- destruct (Hhead source_mode source Hmode Hold_phase Hroot) as
             [Hresume_phase | Hresume_safe].
           ++ left. exact Hresume_phase.
           ++ right. eapply Hlift; [simpl; auto|exact Hresume_safe].
        -- have Hactual_result := Hactual
             (advance_frozen_caller_snapshot CT h caller resume)
             source_mode source (ltac:(simpl; auto)) Hmode Hactual_phase Hroot.
           simpl in Hactual_result. exact Hactual_result.
      * eapply IH.
        -- exact Htail.
        -- intros older Holder. eapply Hlift. simpl; right; exact Holder.
        -- intros snapshot source_mode source Hsnapshot.
           eapply Hactual. simpl; right; exact Hsnapshot.
    + eapply IH.
      * exact Hhistory.
      * intros older Holder. eapply Hlift. simpl; right; exact Holder.
      * intros snapshot source_mode source Hsnapshot.
        eapply Hactual. simpl; right; exact Hsnapshot.
    + eapply IH.
      * exact Hhistory.
      * intros older Holder. eapply Hlift. simpl; right; exact Holder.
      * intros snapshot source_mode source Hsnapshot.
        eapply Hactual. simpl; right; exact Hsnapshot.
Qed.

Lemma advance_resume_exposure_avoids_from_list_reflection :
  forall CT h Z caller resumes,
    frozen_snapshot_list_resume_exposure_protected_reflected Z
      (advance_frozen_caller_snapshots CT h caller resumes) resumes ->
    forall resume,
      List.In (Some resume) resumes ->
      frozen_snapshot_resume_exposure_avoids Z resume ->
      frozen_snapshot_resume_exposure_avoids Z
        (advance_frozen_caller_snapshot CT h caller resume).
Proof.
  intros CT h Z caller resumes Hreflection.
  induction resumes as [|slot tail IH]; intros resume Hresume Hsafe;
    simpl in Hresume; [contradiction|].
  inversion Hreflection as [|final_slot initial_slot final_tail initial_tail
    Hhead Htail]; subst.
  destruct Hresume as [Heq | Hresume].
  - subst slot. simpl in Hhead.
    eapply frozen_snapshot_resume_exposure_avoids_after_reflection; eauto.
  - eapply IH; eauto.
Qed.

Lemma repeat_none_target_supports_resume_witnesses :
  forall count,
    private_target_supports_resume_witnesses
      (repeat None count) (repeat None count).
Proof.
  intros count. induction count; simpl; [exact I|exact IHcount].
Qed.

Lemma repeat_none_target_history_supports_resume_phase :
  forall Z count,
    private_target_history_supports_resume_phase Z
      (repeat None count) (repeat None count).
Proof.
  intros Z count. induction count; simpl; [exact I|exact IHcount].
Qed.

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

Lemma private_target_witness_stack_structural_of_safe :
  forall CT h Z active incoming witnesses,
    private_resume_witness_stack_safe CT h Z active incoming witnesses ->
    private_target_witness_stack_structural CT h active witnesses.
Proof.
  intros CT h Z active incoming witnesses
    (_ & Hruntime & Hdangerous & Hclosed & Hroots & Hexposure &
      _ & _ & _ & _ & Hretain & Hphase).
  exact (conj I (conj Hruntime (conj Hdangerous (conj Hclosed
    (conj Hroots (conj Hexposure (conj Hretain Hphase))))))).
Qed.

Lemma private_target_witness_stack_structural_tail :
  forall CT h active head tail,
    private_target_witness_stack_structural CT h active (head :: tail) ->
    private_target_witness_stack_structural CT h active tail.
Proof.
  intros CT h active head tail
    (_ & Hruntime & Hdangerous & Hclosed & Hroots & Hexposure &
      Hretain & Hphase).
  unfold private_target_witness_stack_structural.
  refine (conj I (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  - intros snapshot Hsnapshot. eapply Hruntime. simpl; right; exact Hsnapshot.
  - intros snapshot mode location Hsnapshot. eapply Hdangerous; simpl; eauto.
  - intros snapshot Hsnapshot. eapply Hclosed. simpl; right; exact Hsnapshot.
  - intros snapshot root Hsnapshot. eapply Hroots; simpl; eauto.
  - eapply frozen_caller_snapshots_resume_exposures_wf_drop_head.
    exact Hexposure.
  - intros snapshot Hsnapshot. eapply Hretain. simpl; right; exact Hsnapshot.
  - intros snapshot mode location Hsnapshot. eapply Hphase; simpl; eauto.
Qed.

Lemma private_target_witness_stack_structural_after_advance :
  forall CT h old_active new_active witnesses,
    wf_r_config CT new_active.(frame_senv) new_active.(frame_renv) h ->
    private_target_witness_stack_structural CT h old_active witnesses ->
    private_target_witness_stack_structural CT h new_active
      (advance_frozen_caller_snapshots CT h new_active witnesses).
Proof.
  intros CT h old_active active witnesses Hwf
    (_ & Hruntime & Hdangerous & Hclosed & Hroots & Hexposure &
      Hretain & Hphase).
  unfold private_target_witness_stack_structural.
  refine (conj I (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  - eapply advance_frozen_caller_snapshots_runtime_mutable; eauto.
  - eapply advance_frozen_caller_snapshots_dangerous. exact Hdangerous.
  - eapply advance_frozen_caller_snapshots_closed.
  - eapply advance_frozen_caller_snapshots_resume_roots_in_heap; eauto.
  - eapply advance_frozen_caller_snapshots_resume_exposures_wf_from_any_active;
      eauto.
  - exact (advance_frozen_caller_snapshots_retain_entry CT h active witnesses
      Hretain).
  - exact (advance_frozen_caller_snapshots_cover_phase_incoming CT h active
      witnesses Hphase).
Qed.

Lemma private_target_witness_stack_structural_after_activation :
  forall CT h old_active caller actual witnesses,
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_colors_runtime_mutable h actual ->
    (forall mode location,
      In authority_flow_state actual (mode, location) ->
      authority_mode_dangerous mode) ->
    private_target_witness_stack_structural CT h old_active witnesses ->
    private_target_witness_stack_structural CT h caller
      (activate_frozen_target_snapshots CT h caller actual witnesses).
Proof.
  intros CT h old_active caller actual witnesses Hwf Hactual_runtime
    Hactual_dangerous
    (_ & Hruntime & Hdangerous & Hclosed & Hroots & Hexposure & Hretain & Hphase).
  have Hadvanced := private_target_witness_stack_structural_after_advance CT h
    old_active caller witnesses Hwf
    (conj I (conj Hruntime (conj Hdangerous (conj Hclosed
      (conj Hroots (conj Hexposure (conj Hretain Hphase))))))).
  destruct Hadvanced as
    (_ & _ & _ & _ & Hadvanced_roots & Hadvanced_exposure & _ & _).
  unfold private_target_witness_stack_structural.
  refine (conj I (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  - intros snapshot Hsnapshot.
    unfold activate_frozen_target_snapshots in Hsnapshot.
    apply in_map_iff in Hsnapshot.
    destruct Hsnapshot as [slot [Heq Hslot]].
    destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as <-. simpl.
    eapply advance_frozen_caller_snapshot_runtime_mutable; [exact Hwf|].
    intros mode location Hunion. inversion Hunion; subst.
    + eapply Hruntime with (snapshot := old_snapshot); [exact Hslot|exact H].
    + eapply Hactual_runtime. exact H.
  - intros snapshot mode location Hsnapshot Hcolor.
    unfold activate_frozen_target_snapshots in Hsnapshot.
    apply in_map_iff in Hsnapshot.
    destruct Hsnapshot as [slot [Heq Hslot]].
    destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as <-. simpl in Hcolor.
    destruct Hcolor as [seed [Hseed Hpath]].
    destruct seed as [seed_mode seed_location].
    have Hseed_dangerous : authority_mode_dangerous seed_mode.
    { inversion Hseed; subst.
      - eapply Hdangerous; eauto.
      - eapply Hactual_dangerous. exact H. }
    have Hresult := frozen_caller_authority_connected_preserves_dangerous
      CT h caller (seed_mode, seed_location) (mode, location)
      Hseed_dangerous Hpath.
    simpl in Hresult. exact Hresult.
  - intros snapshot Hsnapshot.
    unfold activate_frozen_target_snapshots in Hsnapshot.
    apply in_map_iff in Hsnapshot.
    destruct Hsnapshot as [slot [Heq Hslot]].
    destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as <-. unfold activate_frozen_target_snapshot. simpl.
    exact (proj1 (frozen_caller_authority_closure_idempotent CT h caller
      (Union authority_flow_state
        old_snapshot.(frozen_snapshot_current_colors) actual))).
  - intros snapshot root Hsnapshot Hroot.
    unfold activate_frozen_target_snapshots in Hsnapshot.
    apply in_map_iff in Hsnapshot.
    destruct Hsnapshot as [slot [Heq Hslot]].
    destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as <-. simpl in Hroot.
    eapply Hroots; eauto.
  - repeat split.
    + intros snapshot Hsnapshot.
      unfold activate_frozen_target_snapshots in Hsnapshot.
      apply in_map_iff in Hsnapshot.
      destruct Hsnapshot as [slot [Heq Hslot]].
      destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
      injection Heq as <-. simpl.
      eapply advance_frozen_caller_snapshot_runtime_mutable; eauto.
      eapply (proj1 Hexposure). exact Hslot.
    + intros snapshot Hsnapshot.
      unfold activate_frozen_target_snapshots in Hsnapshot.
      apply in_map_iff in Hsnapshot.
      destruct Hsnapshot as [slot [Heq Hslot]].
      destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
      injection Heq as <-. simpl.
      exact (proj1 (frozen_caller_authority_closure_idempotent CT h caller
        old_snapshot.(frozen_snapshot_current_resume_exposure))).
    + intros snapshot mode location Hsnapshot Hcolor.
      unfold activate_frozen_target_snapshots in Hsnapshot.
      apply in_map_iff in Hsnapshot.
      destruct Hsnapshot as [slot [Heq Hslot]].
      destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
      injection Heq as <-. simpl in Hcolor.
      destruct Hcolor as [seed [Hseed Hpath]].
      destruct seed as [seed_mode seed_location].
      have Hseed_dangerous : authority_mode_dangerous seed_mode.
      { eapply (proj1 (proj2 (proj2 Hexposure))); eauto. }
      have Hresult := frozen_caller_authority_connected_preserves_dangerous
        CT h caller (seed_mode, seed_location) (mode, location)
        Hseed_dangerous Hpath.
      simpl in Hresult. exact Hresult.
    + intros snapshot Hsnapshot state Hstate.
      unfold activate_frozen_target_snapshots in Hsnapshot.
      apply in_map_iff in Hsnapshot.
      destruct Hsnapshot as [slot [Heq Hslot]].
      destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
      injection Heq as <-. simpl in *.
      apply frozen_caller_authority_closure_contains.
      eapply (proj1 (proj2 (proj2 (proj2 Hexposure)))); eauto.
    + intros snapshot root Hsnapshot Hroot Hroot_runtime.
      unfold activate_frozen_target_snapshots in Hsnapshot.
      apply in_map_iff in Hsnapshot.
      destruct Hsnapshot as [slot [Heq Hslot]].
      destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
      injection Heq as <-. simpl in *.
      apply frozen_caller_authority_closure_contains.
      eapply (proj2 (proj2 (proj2 (proj2 Hexposure)))); eauto.
  - intros snapshot Hsnapshot state Hentry.
    unfold activate_frozen_target_snapshots in Hsnapshot.
    apply in_map_iff in Hsnapshot.
    destruct Hsnapshot as [slot [Heq Hslot]].
    destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as <-. simpl in *.
    apply frozen_caller_authority_closure_contains. left.
    eapply Hretain; eauto.
  - intros snapshot mode location Hsnapshot Hmode Hphase_color.
    unfold activate_frozen_target_snapshots in Hsnapshot.
    apply in_map_iff in Hsnapshot.
    destruct Hsnapshot as [slot [Heq Hslot]].
    destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as <-. simpl in *.
    apply frozen_caller_authority_closure_contains.
    inversion Hphase_color; subst.
    + left. eapply Hphase; eauto.
    + right. exact H.
Qed.

Definition private_target_witness_temporal_state
  (CT : class_table) (h : heap) (Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary)
  (targets : list frozen_caller_snapshot_slot) : Prop :=
  frozen_snapshot_boundaries_after_cutoff cutoff targets stack.

Definition private_target_witness_state
  (CT : class_table) (h : heap) (Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (incoming : Ensemble authority_flow_state)
  (snapshots target_witnesses resume_witnesses :
    list frozen_caller_snapshot_slot)
  (stack : list watched_boundary) : Prop :=
  private_resume_witnesses_cover_snapshots Z target_witnesses snapshots /\
  private_target_witness_stack_structural CT h active target_witnesses /\
  frozen_completed_colors_resume_phase_safe Z
    (executing_authority_color_set CT h active incoming) target_witnesses /\
  private_target_exposures_support_resume_phase Z target_witnesses
    resume_witnesses /\
  frozen_target_snapshots_nested_resume_phase_safe CT h Z target_witnesses /\
  frozen_caller_snapshots_before_boundaries target_witnesses stack /\
  private_target_supports_resume_witnesses target_witnesses resume_witnesses /\
  private_target_history_supports_resume_phase Z target_witnesses
    resume_witnesses /\
  private_target_witness_temporal_state CT h Z cutoff active stack
    target_witnesses.

Lemma private_target_witness_temporal_after_active_descent :
  forall CT h Z cutoff authority old_senv old_renv new_senv new_renv
    targets stack,
    wf_r_config CT old_senv old_renv h ->
    authority_context_sound h old_renv authority ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame authority new_senv new_renv))
      (phase_frame_capability_set CT h
        (mk_watched_frame authority old_senv old_renv)) ->
    private_target_witness_stack_structural CT h
      (mk_watched_frame authority old_senv old_renv) targets ->
    private_target_witness_temporal_state CT h Z cutoff
      (mk_watched_frame authority old_senv old_renv) stack targets ->
    private_target_witness_temporal_state CT h Z cutoff
      (mk_watched_frame authority new_senv new_renv) stack
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) targets).
Proof.
  intros CT h Z cutoff authority old_senv old_renv new_senv new_renv
    targets stack Hwf Hsound Hdescend Howned Hstack Htemporal.
  eapply advance_snapshot_boundaries_after_cutoff. exact Htemporal.
Qed.

Lemma private_target_witness_temporal_after_graph_reflection :
  forall CT old_h new_h Z cutoff active targets stack,
    (forall location, r_muttype new_h location = r_muttype old_h location) ->
    (forall left right,
      retained_mut_edge CT new_h left right ->
      retained_mut_edge CT old_h left right) ->
    (forall left right,
      mutable_edge CT new_h left right -> mutable_edge CT old_h left right) ->
    (forall location,
      frame_owned_location CT new_h active location ->
      frame_owned_location CT old_h active location) ->
    private_target_witness_stack_structural CT old_h active targets ->
    private_target_witness_temporal_state CT old_h Z cutoff active stack targets ->
    private_target_witness_temporal_state CT new_h Z cutoff active stack
      (advance_frozen_caller_snapshots CT new_h active targets).
Proof.
  intros CT old_h new_h Z cutoff active targets stack Hruntimes
    Hretained Hmutable Howned Hstack Htemporal.
  eapply advance_snapshot_boundaries_after_cutoff. exact Htemporal.
Qed.

Lemma private_target_witness_temporal_after_safe_field_update :
  forall CT P Z cutoff active stack incoming targets h lx old field written,
    principled_phased_authority_live_history_state CT P Z cutoff active stack
      incoming h ->
    runtime_getObj h lx = Some old ->
    authority_safe_field_endpoints CT h active lx written ->
    private_target_witness_stack_structural CT h active targets ->
    principled_phased_authority_live_history_state CT P Z cutoff active stack
      incoming (update_field h lx field (Iot written)) ->
    private_target_witness_temporal_state CT h Z cutoff active stack targets ->
    private_target_witness_temporal_state CT
      (update_field h lx field (Iot written)) Z cutoff active stack
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) active targets).
Proof.
  intros CT P Z cutoff active stack incoming targets h lx old field written
    Hmain Hobj Hendpoints Hstack Hpost Htemporal.
  eapply advance_snapshot_boundaries_after_cutoff. exact Htemporal.
Qed.

Lemma private_target_witness_temporal_after_new :
  forall CT P Z cutoff authority sGamma mt rGamma h stack incoming targets
    x qc C args sGamma' vals qreceiver qruntime,
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming h ->
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h)))) stack incoming
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    vpa_mutability_object_creation qreceiver qc = qruntime ->
    eval_stmt CT rGamma h (SNew x qc C args) OK
      (update_r_env_value rGamma x (Iot (dom h)))
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) ->
    private_target_witness_stack_structural CT h
      (mk_watched_frame authority sGamma rGamma) targets ->
    private_target_witness_temporal_state CT h Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack targets ->
    private_target_witness_temporal_state CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) Z cutoff
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h)))) stack
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) targets).
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack incoming targets
    x qc C args sGamma' vals qreceiver qruntime Hmain Hpost Htyping Hargs
    Hadapt Heval Hstack Htemporal.
  eapply advance_snapshot_boundaries_after_cutoff. exact Htemporal.
Qed.

Lemma frozen_target_nested_phase_safe_after_active_descent :
  forall CT h Z authority old_senv old_renv new_senv new_renv targets,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    frozen_caller_snapshots_closed CT h
      (mk_watched_frame authority old_senv old_renv) targets ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame authority old_senv old_renv) targets ->
    frozen_target_snapshots_nested_resume_phase_safe CT h Z targets ->
    frozen_target_snapshots_nested_resume_phase_safe CT h Z
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) targets).
Proof.
  intros CT h Z authority old_senv old_renv new_senv new_renv targets.
  induction targets as [|slot tail IH]; intros Hdescend Hclosed Hexposure Hsafe;
    simpl in *; [exact I|].
  destruct slot as [head|].
  - destruct Hsafe as [Hhead Htail]. split.
    + intros Hauthority. eapply frozen_source_resume_phase_safe_after_active_descent.
      * exact Hdescend.
      * exact ((proj1 (proj2 Hexposure)) head (ltac:(simpl; auto))).
      * eapply frozen_caller_snapshots_resume_exposures_wf_drop_head.
        exact Hexposure.
      * exact (Hhead Hauthority).
    + eapply IH.
      * exact Hdescend.
      * intros snapshot Hsnapshot. eapply Hclosed. simpl; right; exact Hsnapshot.
      * eapply frozen_caller_snapshots_resume_exposures_wf_drop_head.
        exact Hexposure.
      * exact Htail.
  - eapply IH.
    + exact Hdescend.
    + intros snapshot Hsnapshot. eapply Hclosed. simpl; right; exact Hsnapshot.
    + eapply frozen_caller_snapshots_resume_exposures_wf_drop_head.
      exact Hexposure.
    + exact Hsafe.
Qed.

Lemma frozen_target_nested_phase_safe_after_graph_reflection :
  forall CT h h' Z active targets,
    (forall left right,
      retained_mut_edge CT h' left right -> retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right -> mutable_edge CT h left right) ->
    frozen_caller_snapshots_closed CT h active targets ->
    frozen_caller_snapshots_resume_exposures_wf CT h active targets ->
    frozen_target_snapshots_nested_resume_phase_safe CT h Z targets ->
    frozen_target_snapshots_nested_resume_phase_safe CT h' Z
      (advance_frozen_caller_snapshots CT h' active targets).
Proof.
  intros CT h h' Z active targets. induction targets as [|slot tail IH];
    intros Hretained Hmutable Hclosed Hexposure Hsafe; simpl in *; [exact I|].
  destruct slot as [head|].
  - destruct Hsafe as [Hhead Htail]. split.
    + intros Hauthority. eapply frozen_source_resume_phase_safe_after_graph_reflection.
      * exact Hretained.
      * exact Hmutable.
      * exact ((proj1 (proj2 Hexposure)) head (ltac:(simpl; auto))).
      * eapply frozen_caller_snapshots_resume_exposures_wf_drop_head.
        exact Hexposure.
      * exact (Hhead Hauthority).
    + eapply IH; eauto.
      * intros snapshot Hsnapshot. eapply Hclosed. simpl; right; exact Hsnapshot.
      * eapply frozen_caller_snapshots_resume_exposures_wf_drop_head.
        exact Hexposure.
  - eapply IH; eauto.
    + intros snapshot Hsnapshot. eapply Hclosed. simpl; right; exact Hsnapshot.
    + eapply frozen_caller_snapshots_resume_exposures_wf_drop_head.
      exact Hexposure.
Qed.

Lemma frozen_target_nested_phase_safe_after_safe_field_update :
  forall CT h Z frame targets lx old field written,
    runtime_getObj h lx = Some old ->
    frozen_caller_snapshots_runtime_mutable h targets ->
    frozen_caller_snapshots_closed CT h frame targets ->
    frozen_caller_snapshots_resume_exposures_wf CT h frame targets ->
    authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h frame) ->
    authority_safe_field_endpoints CT h frame lx written ->
    frozen_target_snapshots_nested_resume_phase_safe CT h Z targets ->
    frozen_completed_colors_resume_phase_safe Z
      (independent_active_authority_colors CT h frame) targets ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h frame)
        (active_mode, location) ->
      ~ In Loc Z location) ->
    frozen_target_snapshots_nested_resume_phase_safe CT
      (update_field h lx field (Iot written)) Z
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame targets).
Proof.
  intros CT h Z frame targets. induction targets as [|slot tail IH];
    intros lx old field written Hobj Htarget_runtime Htarget_closed Hexposure Hruntime Hendpoints Hsafe
      Hactive Houtside; simpl in *; [exact I|].
  destruct slot as [head|].
  - destruct Hsafe as [Hhead Htail]. split.
    + intros Hauthority. eapply frozen_source_resume_phase_safe_after_safe_field_update.
      * exact Hobj.
      * exact ((proj1 Hexposure) head (ltac:(simpl; auto))).
      * exact ((proj1 (proj2 Hexposure)) head (ltac:(simpl; auto))).
      * eapply frozen_caller_snapshots_resume_exposures_wf_drop_head.
        exact Hexposure.
      * exact Hruntime.
      * exact Hendpoints.
      * exact (Hhead Hauthority).
      * intros snapshot source_mode source Hsnapshot.
        eapply Hactive. simpl; right; exact Hsnapshot.
      * exact Houtside.
    + eapply IH; eauto.
      * intros snapshot Hsnapshot. eapply Htarget_runtime; simpl; eauto.
      * intros snapshot Hsnapshot. eapply Htarget_closed; simpl; eauto.
      * eapply frozen_caller_snapshots_resume_exposures_wf_drop_head.
        exact Hexposure.
      * intros snapshot source_mode source Hsnapshot.
        eapply Hactive. simpl; right; exact Hsnapshot.
  - eapply IH; eauto.
    + intros snapshot Hsnapshot. eapply Htarget_runtime; simpl; eauto.
    + intros snapshot Hsnapshot. eapply Htarget_closed; simpl; eauto.
    + eapply frozen_caller_snapshots_resume_exposures_wf_drop_head.
      exact Hexposure.
    + intros snapshot source_mode source Hsnapshot.
      eapply Hactive. simpl; right; exact Hsnapshot.
Qed.

Lemma private_resume_witnesses_roots_safe_from_entry_or_safe :
  forall CT h Z active witnesses,
    frozen_caller_snapshots_active_resume_safe CT h Z active witnesses ->
    frozen_caller_snapshots_avoid_protected Z witnesses ->
    frozen_caller_snapshots_entry_exposure_covered witnesses ->
    frozen_caller_snapshots_resume_roots_safe CT h Z active witnesses.
Proof.
  intros CT h Z active witnesses Hactive Havoid Hentry snapshot active_mode
    source exposure_mode target Hsnapshot Hactive_mode Hactive_color Hroot
    Hexposure_mode Hexposure.
  destruct (Hactive snapshot active_mode source Hsnapshot Hactive_mode
    Hactive_color Hroot) as [[entry_mode [Hentry_mode Hentry_color]] | Hsafe].
  - intros Hprotected. eapply Havoid with (snapshot := snapshot)
      (mode := exposure_mode) (location := target); eauto.
    eapply (Hentry snapshot entry_mode source Hsnapshot Hentry_mode
      Hentry_color Hroot). exact Hexposure.
  - eapply Hsafe; eauto.
Qed.

Lemma private_resume_witness_state_is_private_fresh :
  forall CT P Z cutoff active stack incoming witnesses h,
    principled_phased_authority_live_history_state CT P Z cutoff active stack
      incoming h ->
    frozen_caller_snapshots_aligned witnesses stack ->
    private_resume_witness_stack_safe CT h Z active incoming witnesses ->
    frozen_caller_snapshots_before_boundaries witnesses stack ->
    private_resume_witness_temporal_state CT h Z cutoff active stack
      witnesses ->
    private_fresh_frozen_statement_state CT P Z cutoff active stack incoming
      witnesses h.
Proof.
  intros CT P Z cutoff active stack incoming witnesses h Hmain Haligned
    (Hcovered & Hruntime & Hdangerous & Hclosed & Hroots & Hexposure &
      Hactive & Hjoins & Hnested & Hcompleted & Hretain & Hphase)
    Hbefore (Havoid & Hentry & Hcomponents & Hprospective & Hafter).
  split.
  - split.
    + unfold principled_frozen_authority_history_state.
      split; [exact Hmain|].
      split; [exact Haligned|].
      split; [exact Hruntime|].
      split; [exact Hclosed|].
      split; [exact Hretain|].
      split; [exact Hdangerous|].
      split; [exact Havoid|].
      split; [exact Hroots|].
      split; [exact Hexposure|].
      split.
      * eapply private_resume_witnesses_roots_safe_from_entry_or_safe; eauto.
      * split; [exact Hjoins|].
        split; [exact Hentry|exact Hphase].
    + split.
      * eapply frozen_resume_joins_and_retain_imply_active_resume_justified;
          eauto.
      * split; [exact Hbefore|].
        split; [exact Hcovered|].
        split; [exact Hnested|exact Hcompleted].
  - split; [exact Hcomponents|].
    split; [exact Hprospective|exact Hafter].
Qed.

Lemma private_fresh_frozen_statement_state_has_resume_temporal_state :
  forall CT P Z cutoff active stack incoming witnesses h,
    private_fresh_frozen_statement_state CT P Z cutoff active stack incoming
      witnesses h ->
    private_resume_witness_temporal_state CT h Z cutoff active stack
      witnesses.
Proof.
  intros CT P Z cutoff active stack incoming witnesses h
    [Hprivate [Hcomponents [Hprospective Hafter]]].
  destruct Hprivate as [Hprincipled _].
  destruct Hprincipled as
    (_ & _ & _ & _ & _ & _ & Havoid & _ & _ & _ & _ & Hentry & _).
  repeat split; assumption.
Qed.

Lemma private_fresh_frozen_statement_state_has_resume_witness_stack_safe :
  forall CT P Z cutoff active stack incoming witnesses h,
    private_fresh_frozen_statement_state CT P Z cutoff active stack incoming
      witnesses h ->
    private_resume_witness_stack_safe CT h Z active incoming witnesses.
Proof.
  intros CT P Z cutoff active stack incoming witnesses h
    [[Hprincipled [Hactive_justified [Hbefore
      [Hcovered [Hnested Hcompleted]]]]] Htemporal].
  destruct Hprincipled as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  split; [exact Hcovered|].
  split; [exact Hruntime|].
  split; [exact Hdangerous|].
  split; [exact Hclosed|].
  split; [exact Hroots|].
  split; [exact Hexposure|].
  split.
  - unfold frozen_caller_snapshots_active_resume_safe.
    intros snapshot active_mode source Hsnapshot Hactive_mode Hactive Hroot.
    right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
    exact (Hresume snapshot active_mode source exposure_mode target Hsnapshot
      Hactive_mode Hactive Hroot Hexposure_mode Htarget Hprotected).
  - split; [exact Hjoins|].
    split; [exact Hnested|].
    split; [exact Hcompleted|].
    split; [exact Hretain|exact Hphase].
Qed.

(** The policy witness pushed at an untracked nested call must preserve both
    provenance channels.  Ordinary snapshots record tracked operational
    boundaries, while policy witnesses may retain caller authority at an
    ordinary [None] slot.  The new head therefore freezes the union of both
    source lists; using only [snapshots] would lose the latter authority at
    the next nested pop. *)
Definition private_nested_frozen_call_head
  (CT : class_table) (h : heap) (caller callee : watched_frame)
  (caller_colors : Ensemble authority_flow_state)
  (snapshots witnesses : list frozen_caller_snapshot_slot) :
  frozen_caller_color_snapshot :=
  nested_frozen_call_head CT h caller callee caller_colors
    (snapshots ++ witnesses).

Fixpoint frozen_target_resume_exposure_union
  (targets : list frozen_caller_snapshot_slot) :
  Ensemble authority_flow_state :=
  match targets with
  | [] => Empty_set authority_flow_state
  | None :: tail => frozen_target_resume_exposure_union tail
  | Some target :: tail =>
      Union authority_flow_state
        target.(frozen_snapshot_current_resume_exposure)
        (frozen_target_resume_exposure_union tail)
  end.

Definition private_target_call_color_seeds
  (caller_colors : Ensemble authority_flow_state)
  (snapshots targets : list frozen_caller_snapshot_slot) :
  Ensemble authority_flow_state :=
  Union authority_flow_state
    (nested_frozen_call_entry_seeds caller_colors (snapshots ++ targets))
    (frozen_target_resume_exposure_union targets).

Definition private_target_call_resume_exposure_seeds
  (CT : class_table) (h : heap) (caller : watched_frame)
  (targets : list frozen_caller_snapshot_slot) :
  Ensemble authority_flow_state :=
  Union authority_flow_state
    (frame_resume_exposure_colors CT h caller)
    (frozen_target_resume_exposure_union targets).

Definition private_target_call_full_seeds
  (CT : class_table) (h : heap) (caller : watched_frame)
  (caller_colors : Ensemble authority_flow_state)
  (snapshots targets : list frozen_caller_snapshot_slot) :
  Ensemble authority_flow_state :=
  Union authority_flow_state
    (private_target_call_color_seeds caller_colors snapshots targets)
    (frame_resume_exposure_colors CT h caller).

Lemma frozen_target_resume_exposure_union_runtime_mutable :
  forall CT h active targets,
    frozen_caller_snapshots_resume_exposures_wf CT h active targets ->
    authority_colors_runtime_mutable h
      (frozen_target_resume_exposure_union targets).
Proof.
  intros CT h active targets Hexposure mode location Hcolor.
  induction targets as [|slot tail IH]; simpl in Hcolor; [inversion Hcolor|].
  destruct slot as [target|].
  - inversion Hcolor as [state Hhead | state Htail]; subst state.
    + eapply (proj1 Hexposure); [simpl; auto|exact Hhead].
    + eapply IH; [|exact Htail].
      eapply frozen_caller_snapshots_resume_exposures_wf_drop_head.
      exact Hexposure.
  - eapply IH; [|exact Hcolor].
    eapply frozen_caller_snapshots_resume_exposures_wf_drop_head.
    exact Hexposure.
Qed.

Lemma frozen_target_resume_exposure_union_dangerous :
  forall CT h active targets mode location,
    frozen_caller_snapshots_resume_exposures_wf CT h active targets ->
    In authority_flow_state (frozen_target_resume_exposure_union targets)
      (mode, location) ->
    authority_mode_dangerous mode.
Proof.
  intros CT h active targets. induction targets as [|slot tail IH];
    intros mode location Hexposure Hcolor; simpl in Hcolor;
    [inversion Hcolor|].
  destruct slot as [target|].
  - inversion Hcolor as [state Hhead | state Htail]; subst state.
    + eapply (proj1 (proj2 (proj2 Hexposure)));
        [simpl; auto|exact Hhead].
    + eapply IH; [|exact Htail].
      eapply frozen_caller_snapshots_resume_exposures_wf_drop_head.
      exact Hexposure.
  - eapply IH; [|exact Hcolor].
    eapply frozen_caller_snapshots_resume_exposures_wf_drop_head.
    exact Hexposure.
Qed.

Lemma private_target_call_color_seeds_runtime_mutable :
  forall CT h caller caller_colors snapshots targets,
    authority_colors_runtime_mutable h caller_colors ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_runtime_mutable h targets ->
    frozen_caller_snapshots_resume_exposures_wf CT h caller targets ->
    authority_colors_runtime_mutable h
      (private_target_call_color_seeds caller_colors snapshots targets).
Proof.
  intros CT h caller caller_colors snapshots targets Hcaller Hsnapshots
    Htargets Hexposure mode location Hseed.
  inversion Hseed as [state Hnested | state Htarget]; subst state.
  - inversion Hnested as [state Hcaller_seed | state Hsnapshot]; subst state.
    + eapply Hcaller. exact (proj1 Hcaller_seed).
    + destruct Hsnapshot as [snapshot [Hin Hcolor]].
      apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * eapply Hsnapshots; eauto.
      * eapply Htargets; eauto.
  - eapply frozen_target_resume_exposure_union_runtime_mutable; eauto.
Qed.

Lemma private_target_call_color_seeds_dangerous :
  forall CT h caller caller_colors snapshots targets mode location,
    frozen_caller_snapshots_dangerous snapshots ->
    frozen_caller_snapshots_dangerous targets ->
    frozen_caller_snapshots_resume_exposures_wf CT h caller targets ->
    In authority_flow_state
      (private_target_call_color_seeds caller_colors snapshots targets)
      (mode, location) ->
    authority_mode_dangerous mode.
Proof.
  intros CT h caller caller_colors snapshots targets mode location Hsnapshots
    Htargets Hexposure Hseed.
  inversion Hseed as [state Hnested | state Htarget]; subst state.
  - inversion Hnested as [state Hcaller_seed | state Hsnapshot]; subst state.
    + exact (proj2 Hcaller_seed).
    + destruct Hsnapshot as [snapshot [Hin Hcolor]].
      apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * eapply Hsnapshots; eauto.
      * eapply Htargets; eauto.
  - eapply frozen_target_resume_exposure_union_dangerous; eauto.
Qed.

Lemma private_target_call_full_seeds_runtime_mutable :
  forall CT h caller caller_colors snapshots targets,
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_colors_runtime_mutable h caller_colors ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_runtime_mutable h targets ->
    frozen_caller_snapshots_resume_exposures_wf CT h caller targets ->
    authority_colors_runtime_mutable h
      (private_target_call_full_seeds CT h caller caller_colors snapshots
        targets).
Proof.
  intros CT h caller caller_colors snapshots targets Hwf Hcaller Hsnapshots
    Htargets Hexposure mode location Hseed.
  inversion Hseed as [state Htarget | state Hresume]; subst state.
  - exact (private_target_call_color_seeds_runtime_mutable CT h caller
      caller_colors snapshots targets Hcaller Hsnapshots Htargets Hexposure
      mode location Htarget).
  - exact (frame_resume_exposure_colors_runtime_mutable CT h caller Hwf mode
      location Hresume).
Qed.

Lemma private_target_call_resume_exposure_seeds_runtime_mutable :
  forall CT h caller targets,
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    frozen_caller_snapshots_resume_exposures_wf CT h caller targets ->
    authority_colors_runtime_mutable h
      (private_target_call_resume_exposure_seeds CT h caller targets).
Proof.
  intros CT h caller targets Hwf Hexposure mode location Hseed.
  inversion Hseed as [state Hcaller | state Htargets]; subst state.
  - eapply frame_resume_exposure_colors_runtime_mutable; eauto.
  - eapply frozen_target_resume_exposure_union_runtime_mutable; eauto.
Qed.

Lemma private_target_call_resume_exposure_seeds_dangerous :
  forall CT h caller targets mode location,
    frozen_caller_snapshots_resume_exposures_wf CT h caller targets ->
    In authority_flow_state
      (private_target_call_resume_exposure_seeds CT h caller targets)
      (mode, location) ->
    authority_mode_dangerous mode.
Proof.
  intros CT h caller targets mode location Hexposure Hseed.
  inversion Hseed as [state Hcaller | state Htargets]; subst state.
  - eapply frame_resume_exposure_colors_dangerous; eauto.
  - eapply frozen_target_resume_exposure_union_dangerous; eauto.
Qed.

Lemma private_target_call_full_seeds_dangerous :
  forall CT h caller caller_colors snapshots targets mode location,
    frozen_caller_snapshots_dangerous snapshots ->
    frozen_caller_snapshots_dangerous targets ->
    frozen_caller_snapshots_resume_exposures_wf CT h caller targets ->
    In authority_flow_state
      (private_target_call_full_seeds CT h caller caller_colors snapshots
        targets) (mode, location) ->
    authority_mode_dangerous mode.
Proof.
  intros CT h caller caller_colors snapshots targets mode location Hsnapshots
    Htargets Hexposure Hseed.
  inversion Hseed as [state Htarget | state Hresume]; subst state.
  - exact (private_target_call_color_seeds_dangerous CT h caller
      caller_colors snapshots targets mode location Hsnapshots Htargets
      Hexposure Htarget).
  - exact (frame_resume_exposure_colors_dangerous CT h caller mode location
      Hresume).
Qed.

(** The target and exceptional-return channels describe the same suspended
    boundary.  They may have different source lists, but must retain identical
    phase, root, and exposure metadata so either return path composes with the
    same boundary invariant. *)
Definition private_nested_target_call_head
  (CT : class_table) (h : heap) (caller callee : watched_frame)
  (caller_colors : Ensemble authority_flow_state)
  (snapshots witnesses : list frozen_caller_snapshot_slot) :
  frozen_caller_color_snapshot :=
  private_nested_frozen_call_head CT h caller callee caller_colors
    snapshots witnesses.

(** The aggregate head introduces no new protected color.  Its seed set is
    precisely the dangerous caller colors together with the current colors
    of the two older stacks.  The former are covered by callee separation;
    each latter seed followed by the head closure is a member of the
    corresponding advanced snapshot. *)
Lemma private_nested_frozen_call_head_avoids_protected_from_parts :
  forall CT h Z caller callee caller_colors snapshots witnesses,
    executing_authority_colors_separated CT h Z callee caller_colors ->
    frozen_caller_snapshots_avoid_protected Z
      (advance_frozen_caller_snapshots CT h callee snapshots) ->
    frozen_caller_snapshots_avoid_protected Z
      (advance_frozen_caller_snapshots CT h callee witnesses) ->
    forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (private_nested_frozen_call_head CT h caller callee caller_colors
          snapshots witnesses).(frozen_snapshot_current_colors)
        (mode, location) ->
      ~ In Loc Z location.
Proof.
  intros CT h Z caller callee caller_colors snapshots witnesses Hcallee
    Hsnapshots Hwitnesses mode location Hmode Hcolor.
  unfold private_nested_frozen_call_head, nested_frozen_call_head in Hcolor.
  simpl in Hcolor.
  destruct Hcolor as [seed [Hseed Hpath]].
  destruct seed as [seed_mode seed_location].
  inversion Hseed as [state Hcaller | state Hstack]; subst state.
  - intros Hprotected. eapply Hcallee; [exact Hmode| |exact Hprotected].
    destruct Hcaller as [Hcaller _].
    exists (seed_mode, seed_location). split.
    + left. exact Hcaller.
    + eapply frozen_caller_authority_connected_is_phased. exact Hpath.
  - destruct Hstack as [snapshot [Hsnapshot Hsnapshot_color]].
    apply in_app_iff in Hsnapshot. destruct Hsnapshot as [Hsnapshot | Hwitness].
    + eapply Hsnapshots with
        (snapshot := advance_frozen_caller_snapshot CT h callee snapshot)
        (mode := mode).
      * unfold advance_frozen_caller_snapshots. apply in_map_iff.
        exists (Some snapshot). split; [reflexivity|exact Hsnapshot].
      * exact Hmode.
      * simpl. exists (seed_mode, seed_location). split; assumption.
    + eapply Hwitnesses with
        (snapshot := advance_frozen_caller_snapshot CT h callee snapshot)
        (mode := mode).
      * unfold advance_frozen_caller_snapshots. apply in_map_iff.
        exists (Some snapshot). split; [reflexivity|exact Hwitness].
      * exact Hmode.
      * simpl. exists (seed_mode, seed_location). split; assumption.
Qed.

Lemma private_nested_frozen_call_heads_support :
  forall CT h caller callee caller_colors snapshots target_sources
    resume_sources,
    Same_set authority_flow_state
      (private_nested_frozen_call_head CT h caller callee caller_colors
        snapshots resume_sources).(frozen_snapshot_phase_incoming)
      (private_nested_frozen_call_head CT h caller callee caller_colors
        snapshots target_sources).(frozen_snapshot_phase_incoming) /\
    Same_set Loc
      (private_nested_frozen_call_head CT h caller callee caller_colors
        snapshots resume_sources).(frozen_snapshot_resume_rdm_roots)
      (private_nested_frozen_call_head CT h caller callee caller_colors
        snapshots target_sources).(frozen_snapshot_resume_rdm_roots) /\
    Same_set authority_flow_state
      (private_nested_frozen_call_head CT h caller callee caller_colors
        snapshots resume_sources).(frozen_snapshot_entry_resume_exposure)
      (private_nested_frozen_call_head CT h caller callee caller_colors
        snapshots target_sources).(frozen_snapshot_entry_resume_exposure) /\
    Same_set authority_flow_state
      (private_nested_frozen_call_head CT h caller callee caller_colors
        snapshots resume_sources).(frozen_snapshot_current_resume_exposure)
      (private_nested_frozen_call_head CT h caller callee caller_colors
        snapshots target_sources).(frozen_snapshot_current_resume_exposure).
Proof.
  intros. unfold private_nested_frozen_call_head, nested_frozen_call_head. simpl.
  repeat split; intros state Hstate; exact Hstate.
Qed.

Lemma private_nested_frozen_call_head_before_boundary :
  forall CT h caller callee caller_colors snapshots witnesses boundary,
    boundary.(boundary_entry_cutoff) = dom h ->
    authority_colors_runtime_mutable h caller_colors ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    frozen_snapshot_slot_before_boundary
      (Some (private_nested_frozen_call_head CT h caller callee caller_colors
        snapshots witnesses)) boundary.
Proof.
  intros CT h caller callee caller_colors snapshots witnesses boundary
    Hcutoff Hruntime Hcaller_wf.
  unfold frozen_snapshot_slot_before_boundary,
    private_nested_frozen_call_head, nested_frozen_call_head. simpl.
  split.
  - intros mode location Hcolor. rewrite Hcutoff.
    eapply r_muttype_some_dom. eapply Hruntime. exact Hcolor.
  - intros root Hroot. rewrite Hcutoff.
    destruct (typed_rdm_root_has_runtime_context CT caller.(frame_senv)
      caller.(frame_renv) h root Hcaller_wf Hroot) as
      [runtime_q Hruntime_root].
    eapply r_muttype_some_dom. exact Hruntime_root.
Qed.

Lemma private_nested_target_call_head_before_boundary :
  forall CT h caller callee caller_colors snapshots witnesses boundary,
    boundary.(boundary_entry_cutoff) = dom h ->
    authority_colors_runtime_mutable h caller_colors ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    frozen_snapshot_slot_before_boundary
      (Some (private_nested_target_call_head CT h caller callee caller_colors
        snapshots witnesses)) boundary.
Proof.
  intros CT h caller callee caller_colors snapshots witnesses boundary
    Hcutoff Hruntime Hcaller_wf.
  unfold frozen_snapshot_slot_before_boundary,
    private_nested_target_call_head. simpl.
  split.
  - intros mode location Hcolor. rewrite Hcutoff.
    eapply r_muttype_some_dom. eapply Hruntime. exact Hcolor.
  - intros root Hroot. rewrite Hcutoff.
    destruct (typed_rdm_root_has_runtime_context CT caller.(frame_senv)
      caller.(frame_renv) h root Hcaller_wf Hroot) as
      [runtime_q Hruntime_root].
    eapply r_muttype_some_dom. exact Hruntime_root.
Qed.

Lemma frozen_caller_snapshot_current_color_union_app_none_l :
  forall snapshots witnesses,
    (forall snapshot, ~ List.In (Some snapshot) snapshots) ->
    frozen_caller_snapshot_current_color_union (snapshots ++ witnesses) =
    frozen_caller_snapshot_current_color_union witnesses.
Proof.
  intros snapshots witnesses Hnone.
  apply Extensionality_Ensembles. split; intros state Hstate.
  - destruct Hstate as [snapshot [Hin Hcolor]].
    apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + exfalso. exact (Hnone snapshot Hin).
    + exists snapshot. split; assumption.
  - destruct Hstate as [snapshot [Hin Hcolor]].
    exists snapshot. split; [apply in_or_app; right; exact Hin|exact Hcolor].
Qed.

(** In the advancing induction every ordinary slot aligned with a policy
    witness is [None].  Hence the aggregate head is definitionally the same
    frozen certificate as entering a tracked call over the policy-witness
    channel alone.  This equality is what permits the existing tracked-pop
    classifier to consume the policy head privately. *)
Lemma private_nested_frozen_call_head_eq_witness_head :
  forall CT h caller callee caller_colors snapshots witnesses,
    (forall snapshot, ~ List.In (Some snapshot) snapshots) ->
    private_nested_frozen_call_head CT h caller callee caller_colors
      snapshots witnesses =
    nested_frozen_call_head CT h caller callee caller_colors witnesses.
Proof.
  intros CT h caller callee caller_colors snapshots witnesses Hnone.
  unfold private_nested_frozen_call_head, nested_frozen_call_head,
    nested_frozen_call_entry_seeds.
  rewrite (frozen_caller_snapshot_current_color_union_app_none_l snapshots
    witnesses Hnone).
  reflexivity.
Qed.

Lemma private_nested_frozen_call_head_covers_advanced_witnesses :
  forall CT h (Z : Ensemble Loc) caller callee caller_colors snapshots witnesses,
    private_resume_witness_covers_tail Z
      (Some (private_nested_frozen_call_head CT h caller callee caller_colors
        snapshots witnesses))
      (advance_frozen_caller_snapshots CT h callee witnesses).
Proof.
  intros CT h Z caller callee caller_colors snapshots witnesses new_older
    Hnew mode_location Hcolor.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_older|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  destruct Hcolor as [seed [Hseed Hpath]]. exists seed. split.
  - right. exists old_older. split; [apply in_or_app; right; exact Hold|].
    exact Hseed.
  - exact Hpath.
Qed.

Lemma private_nested_frozen_call_head_builds_nested_covered :
  forall CT h (Z : Ensemble Loc) caller callee caller_colors snapshots witnesses,
    frozen_caller_snapshots_nested_covered witnesses ->
    frozen_caller_snapshots_nested_covered
      (Some (private_nested_frozen_call_head CT h caller callee caller_colors
        snapshots witnesses) ::
       advance_frozen_caller_snapshots CT h callee witnesses).
Proof.
  intros CT h Z caller callee caller_colors snapshots witnesses Hcovered.
  simpl. split.
  - exact (private_nested_frozen_call_head_covers_advanced_witnesses CT h Z
      caller callee caller_colors snapshots witnesses).
  - apply advance_frozen_caller_snapshots_nested_covered. exact Hcovered.
Qed.

Lemma private_entry_witnesses_in_combined_entry :
  forall CT h caller callee caller_colors snapshots witnesses slot,
    List.In slot
      (Some (private_nested_frozen_call_head CT h caller callee caller_colors
        snapshots witnesses) ::
       advance_frozen_caller_snapshots CT h callee witnesses) ->
    List.In slot
      (enter_nested_frozen_caller_snapshots CT h caller callee caller_colors
        (snapshots ++ witnesses)).
Proof.
  intros CT h caller callee caller_colors snapshots witnesses slot Hin.
  unfold private_nested_frozen_call_head,
    enter_nested_frozen_caller_snapshots in *. simpl in *.
  destruct Hin as [<- | Hin].
  - left. reflexivity.
  - right. unfold advance_frozen_caller_snapshots in *.
    apply in_map_iff in Hin.
    destruct Hin as [old_slot [<- Hold]].
    apply in_map_iff. exists old_slot. split; [reflexivity|].
    apply in_or_app. right. exact Hold.
Qed.

Lemma private_entry_witnesses_phase_wf :
  forall CT h caller callee caller_colors snapshots witnesses,
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    wf_r_config CT callee.(frame_senv) callee.(frame_renv) h ->
    authority_colors_runtime_mutable h caller_colors ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_dangerous snapshots ->
    frozen_caller_snapshots_resume_roots_in_heap h snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h caller snapshots ->
    frozen_caller_snapshots_runtime_mutable h witnesses ->
    frozen_caller_snapshots_dangerous witnesses ->
    frozen_caller_snapshots_closed CT h caller witnesses ->
    frozen_caller_snapshots_resume_roots_in_heap h witnesses ->
    frozen_caller_snapshots_resume_exposures_wf CT h caller witnesses ->
    let entered :=
      Some (private_nested_frozen_call_head CT h caller callee caller_colors
        snapshots witnesses) ::
      advance_frozen_caller_snapshots CT h callee witnesses in
    frozen_caller_snapshots_runtime_mutable h entered /\
    frozen_caller_snapshots_closed CT h callee entered /\
    frozen_caller_snapshots_resume_roots_in_heap h entered /\
    frozen_caller_snapshots_resume_exposures_wf CT h callee entered.
Proof.
  intros CT h caller callee caller_colors snapshots witnesses Hcaller_wf
    Hcallee_wf Hcaller_runtime Hsnapshot_runtime Hsnapshot_dangerous
    Hsnapshot_roots Hsnapshot_exposure Hwitness_runtime Hwitness_dangerous Hwitness_closed
    Hwitness_roots Hwitness_exposure entered.
  pose proof Hwitness_exposure as Hwitness_exposure_all.
  destruct Hsnapshot_exposure as
    (Hsnapshot_exposure_runtime & Hsnapshot_exposure_closed &
      Hsnapshot_exposure_dangerous & Hsnapshot_exposure_entry &
      Hsnapshot_exposure_roots).
  destruct Hwitness_exposure as
    (Hwitness_exposure_runtime & Hwitness_exposure_closed &
      Hwitness_exposure_dangerous & Hwitness_exposure_entry &
      Hwitness_exposure_roots).
  have Hcombined_runtime : frozen_caller_snapshots_runtime_mutable h
      (snapshots ++ witnesses).
  { intros snapshot Hin. apply in_app_or in Hin. destruct Hin; eauto. }
  have Hcombined_dangerous : frozen_caller_snapshots_dangerous
      (snapshots ++ witnesses).
  { intros snapshot mode location Hin Hcolor. apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    - eapply Hsnapshot_dangerous; eauto.
    - eapply Hwitness_dangerous; eauto. }
  have Hcombined_roots : frozen_caller_snapshots_resume_roots_in_heap h
      (snapshots ++ witnesses).
  { intros snapshot root Hin Hroot. apply in_app_or in Hin.
    destruct Hin; eauto. }
  have Hcombined_exposure : frozen_caller_snapshots_resume_exposures_wf CT h
      caller (snapshots ++ witnesses).
  { repeat split.
    - intros snapshot Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      + exact (Hsnapshot_exposure_runtime snapshot Hin).
      + exact (Hwitness_exposure_runtime snapshot Hin).
    - intros snapshot Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      + exact (Hsnapshot_exposure_closed snapshot Hin).
      + exact (Hwitness_exposure_closed snapshot Hin).
    - intros snapshot mode location Hin Hcolor. apply in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      + exact (Hsnapshot_exposure_dangerous snapshot mode location Hin Hcolor).
      + exact (Hwitness_exposure_dangerous snapshot mode location Hin Hcolor).
    - intros snapshot Hin state Hstate. apply in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      + exact (Hsnapshot_exposure_entry snapshot Hin state Hstate).
      + exact (Hwitness_exposure_entry snapshot Hin state Hstate).
    - intros snapshot root Hin Hroot Hruntime. apply in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      + exact (Hsnapshot_exposure_roots snapshot root Hin Hroot Hruntime).
      + exact (Hwitness_exposure_roots snapshot root Hin Hroot Hruntime). }
  unfold entered. simpl.
  set (head := private_nested_frozen_call_head CT h caller callee
    caller_colors snapshots witnesses).
  set (tail := advance_frozen_caller_snapshots CT h callee witnesses).
  have Hseed_runtime : authority_colors_runtime_mutable h
      (nested_frozen_call_entry_seeds caller_colors
        (snapshots ++ witnesses)).
  { intros mode location Hseed. inversion Hseed; subst.
    - eapply Hcaller_runtime. exact (proj1 H).
    - destruct H as [snapshot [Hsnapshot Hcolor]].
      eapply Hcombined_runtime; eauto. }
  have Hhead_runtime : authority_colors_runtime_mutable h
      head.(frozen_snapshot_current_colors).
  { unfold head, private_nested_frozen_call_head,
      nested_frozen_call_head. simpl.
    eapply advance_frozen_caller_snapshot_runtime_mutable; eauto. }
  have Htail_runtime : frozen_caller_snapshots_runtime_mutable h tail.
  { unfold tail. eapply advance_frozen_caller_snapshots_runtime_mutable;
      eauto. }
  split.
  - intros snapshot Hsnapshot mode location Hcolor. simpl in Hsnapshot.
    destruct Hsnapshot as [Heq | Htail].
    + injection Heq as <-. eapply Hhead_runtime. exact Hcolor.
    + eapply Htail_runtime; eauto.
  - split.
    + intros snapshot Hsnapshot. simpl in Hsnapshot.
      destruct Hsnapshot as [Heq | Htail].
      * injection Heq as <-. unfold head, private_nested_frozen_call_head.
        apply nested_frozen_call_head_closed.
      * unfold tail in Htail.
        eapply advance_frozen_caller_snapshots_closed; eauto.
    + split.
      * intros snapshot root Hsnapshot Hroot. simpl in Hsnapshot.
        destruct Hsnapshot as [Heq | Htail].
        -- injection Heq as <-.
           unfold head, private_nested_frozen_call_head,
             nested_frozen_call_head in Hroot. simpl in Hroot.
           unfold frame_rdm_root_set, typed_root in Hroot.
           destruct Hroot as [variable [T [Htype [Hvalue Hrdm]]]].
           exact (wf_config_value_dom CT caller.(frame_senv)
             caller.(frame_renv) h variable root Hcaller_wf Hvalue).
        -- unfold tail in Htail.
           have Htail_roots :=
             advance_frozen_caller_snapshots_resume_roots_in_heap CT h
               callee witnesses Hwitness_roots.
           eapply Htail_roots; eauto.
      * repeat split.
        -- intros snapshot Hsnapshot mode location Hcolor. simpl in Hsnapshot.
           destruct Hsnapshot as [Heq | Htail].
           ++ injection Heq as <-.
              unfold head, private_nested_frozen_call_head,
                nested_frozen_call_head in Hcolor. simpl in Hcolor.
              eapply advance_frozen_caller_snapshot_runtime_mutable;
                [exact Hcallee_wf| |exact Hcolor].
              apply frame_resume_exposure_colors_runtime_mutable.
              exact Hcaller_wf.
           ++ have Htail_exposure :=
                advance_frozen_caller_snapshots_resume_exposures_wf_from_any_active
                  CT h caller callee witnesses Hcallee_wf
                  Hwitness_exposure_all.
              eapply (proj1 Htail_exposure); eauto.
        -- intros snapshot Hsnapshot. simpl in Hsnapshot.
           destruct Hsnapshot as [Heq | Htail].
           ++ injection Heq as <-.
              unfold head, private_nested_frozen_call_head,
                nested_frozen_call_head. simpl.
              apply (proj1 (frozen_caller_authority_closure_idempotent CT h
                callee (frame_resume_exposure_colors CT h caller))).
           ++ have Htail_exposure :=
                advance_frozen_caller_snapshots_resume_exposures_wf_from_any_active
                  CT h caller callee witnesses Hcallee_wf
                  Hwitness_exposure_all.
              eapply (proj1 (proj2 Htail_exposure)); eauto.
        -- intros snapshot mode location Hsnapshot Hcolor. simpl in Hsnapshot.
           destruct Hsnapshot as [Heq | Htail].
           ++ injection Heq as <-.
              unfold head, private_nested_frozen_call_head,
                nested_frozen_call_head in Hcolor. simpl in Hcolor.
              eapply frozen_caller_authority_closure_dangerous;
                [|exact Hcolor].
              apply frame_resume_exposure_colors_dangerous.
           ++ have Htail_exposure :=
                advance_frozen_caller_snapshots_resume_exposures_wf_from_any_active
                  CT h caller callee witnesses Hcallee_wf
                  Hwitness_exposure_all.
              eapply (proj1 (proj2 (proj2 Htail_exposure))); eauto.
        -- intros snapshot Hsnapshot state Hstate. simpl in Hsnapshot.
           destruct Hsnapshot as [Heq | Htail].
           ++ injection Heq as <-.
              unfold head, private_nested_frozen_call_head,
                nested_frozen_call_head in *. simpl in *.
              apply frozen_caller_authority_closure_contains. exact Hstate.
           ++ have Htail_exposure :=
                advance_frozen_caller_snapshots_resume_exposures_wf_from_any_active
                  CT h caller callee witnesses Hcallee_wf
                  Hwitness_exposure_all.
              eapply (proj1 (proj2 (proj2 (proj2 Htail_exposure)))); eauto.
        -- intros snapshot root Hsnapshot Hroot Hroot_runtime.
           simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
           ++ injection Heq as <-.
              unfold head, private_nested_frozen_call_head,
                nested_frozen_call_head in *. simpl in *.
              apply frozen_caller_authority_closure_contains.
              unfold frame_resume_exposure_colors.
              apply frozen_caller_authority_closure_contains.
              unfold frame_resume_exposure_seeds.
              exists root. repeat split; try assumption.
           ++ have Htail_exposure :=
                advance_frozen_caller_snapshots_resume_exposures_wf_from_any_active
                  CT h caller callee witnesses Hcallee_wf
                  Hwitness_exposure_all.
              eapply (proj2 (proj2 (proj2 (proj2 Htail_exposure)))); eauto.
Qed.

Lemma repeat_none_resume_witnesses_cover_snapshots :
  forall Z count,
    private_resume_witnesses_cover_snapshots Z
      (repeat None count) (repeat None count).
Proof.
  intros Z count. induction count as [|count IH]; simpl; [exact I|].
  split.
  - intros older Hin. change (List.In (Some older)
      (repeat None count)) in Hin.
    apply repeat_spec in Hin. discriminate.
  - exact IH.
Qed.

Lemma repeat_none_resume_witnesses_phase_wf :
  forall CT h active count,
    private_resume_witnesses_phase_wf CT h active
      (repeat None count) (repeat None count).
Proof.
  intros CT h active count. induction count as [|count IH]; simpl; [exact I|].
  split.
  - change (frozen_caller_snapshots_runtime_mutable h
      (repeat None (S count))).
    apply frozen_caller_snapshots_none_runtime_mutable.
  - split.
    + change (frozen_caller_snapshots_closed CT h active
        (repeat None (S count))).
      apply frozen_caller_snapshots_none_closed.
    + split.
      * change (frozen_caller_snapshots_resume_roots_in_heap h
          (repeat None (S count))).
        apply frozen_caller_snapshots_none_resume_roots_in_heap.
      * split.
        -- change (frozen_caller_snapshots_resume_exposures_wf CT h active
          (repeat None (S count))).
           apply frozen_caller_snapshots_none_resume_exposures_wf.
        -- exact IH.
Qed.

Lemma repeat_none_resume_witnesses_roots_safe :
  forall CT h Z active count,
    private_resume_witnesses_roots_safe CT h Z active
      (repeat None count) (repeat None count).
Proof.
  intros CT h Z active count. induction count as [|count IH]; simpl;
    [exact I|].
  split.
  - unfold frozen_caller_snapshots_active_resume_safe.
    intros snapshot mode source Hin.
    change (List.In (Some snapshot) (repeat None (S count))) in Hin.
    apply repeat_spec in Hin. discriminate.
  - exact IH.
Qed.

Lemma repeat_none_resume_witnesses_nested_resume_safe :
  forall Z count,
    private_resume_witnesses_nested_resume_safe Z
      (repeat None count) (repeat None count).
Proof.
  intros Z count. induction count as [|count IH]; simpl; [exact I|].
  split.
  - apply repeat_none_snapshots_nested_resume_safe.
  - exact IH.
Qed.

Lemma repeat_none_resume_witnesses_completed_safe :
  forall CT h Z active incoming count,
    private_resume_witnesses_completed_safe CT h Z active incoming
      (repeat None count) (repeat None count).
Proof.
  intros CT h Z active incoming count. induction count as [|count IH];
    simpl; [exact I|].
  split.
  - change (frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h active incoming)
      (repeat None (S count))).
    apply repeat_none_completed_colors_resume_safe.
  - exact IH.
Qed.

Lemma repeat_none_resume_witness_stack_safe :
  forall CT h Z active incoming count,
    private_resume_witness_stack_safe CT h Z active incoming
      (repeat None count).
Proof.
  intros CT h Z active incoming count.
  unfold private_resume_witness_stack_safe.
  refine (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ (conj _ (conj _
      (conj _ _))))))))))).
  - apply repeat_none_snapshots_nested_covered.
  - apply frozen_caller_snapshots_none_runtime_mutable.
  - apply frozen_caller_snapshots_none_dangerous.
  - apply frozen_caller_snapshots_none_closed.
  - apply frozen_caller_snapshots_none_resume_roots_in_heap.
  - apply frozen_caller_snapshots_none_resume_exposures_wf.
  - unfold frozen_caller_snapshots_active_resume_safe.
    apply repeat_none_completed_colors_resume_safe.
  - apply frozen_caller_snapshots_none_resume_joins_safe.
  - apply repeat_none_snapshots_nested_resume_safe.
  - apply repeat_none_completed_colors_resume_safe.
  - apply frozen_caller_snapshots_none_retain_entry.
  - apply frozen_caller_snapshots_none_cover_phase_incoming.
Qed.

Lemma private_resume_witnesses_cover_snapshots_length :
  forall Z witnesses snapshots,
    private_resume_witnesses_cover_snapshots Z witnesses snapshots ->
    length witnesses = length snapshots.
Proof.
  intros Z witnesses. induction witnesses as [|witness witness_tail IH];
    intros snapshots Hcovers; destruct snapshots as [|snapshot snapshot_tail].
  - reflexivity.
  - simpl in Hcovers. contradiction.
  - simpl in Hcovers. contradiction.
  - destruct snapshot as [snapshot|]; [simpl in Hcovers; contradiction|].
    simpl in Hcovers. destruct Hcovers as [_ Htail]. simpl.
    f_equal. eapply IH. exact Htail.
Qed.

Lemma private_resume_witnesses_cover_snapshot_color_union :
  forall Z witnesses snapshots,
    private_resume_witnesses_cover_snapshots Z witnesses snapshots ->
    Included authority_flow_state
      (frozen_caller_snapshot_current_color_union snapshots)
      (frozen_caller_snapshot_current_color_union witnesses).
Proof.
  intros Z witnesses. induction witnesses as [|witness witness_tail IH];
    intros snapshots Hcover state Hstate.
  - destruct snapshots as [|snapshot snapshot_tail].
    + destruct Hstate as [source_snapshot [Hbad Hcolor]]. contradiction.
    + simpl in Hcover. contradiction.
  - destruct snapshots as [|snapshot snapshot_tail];
      [simpl in Hcover; contradiction|].
    destruct snapshot as [snapshot|]; [simpl in Hcover; contradiction|].
    simpl in Hcover. destruct Hcover as [Hhead Htail].
    destruct Hstate as [source_snapshot [[Hbad | Hsource] Hcolor]].
    + discriminate.
    + have Htail_state := IH snapshot_tail Htail state
        (ex_intro _ source_snapshot (conj Hsource Hcolor)).
      destruct Htail_state as [policy_snapshot [Hpolicy Hpolicy_color]].
      exists policy_snapshot. split; [simpl; right; exact Hpolicy|].
      exact Hpolicy_color.
Qed.

Lemma private_resume_witnesses_cover_snapshots_none :
  forall Z witnesses snapshots snapshot,
    private_resume_witnesses_cover_snapshots Z witnesses snapshots ->
    ~ List.In (Some snapshot) snapshots.
Proof.
  intros Z witnesses. induction witnesses as [|witness witness_tail IH];
    intros snapshots snapshot Hcover Hsnapshot.
  - destruct snapshots; simpl in *; contradiction.
  - destruct snapshots as [|slot tail]; [simpl in Hcover; contradiction|].
    destruct slot as [head|]; [simpl in Hcover; contradiction|].
    simpl in Hcover, Hsnapshot. destruct Hcover as [Hhead Htail].
    destruct Hsnapshot as [Hbad | Hsnapshot]; [discriminate|].
    eapply IH; eauto.
Qed.

Lemma private_resume_witnesses_snapshots_are_repeat_none :
  forall Z witnesses snapshots,
    private_resume_witnesses_cover_snapshots Z witnesses snapshots ->
    snapshots = repeat None (length snapshots).
Proof.
  intros Z witnesses. induction witnesses as [|witness witness_tail IH];
    intros snapshots Hcover.
  - destruct snapshots; simpl in Hcover; [reflexivity|contradiction].
  - destruct snapshots as [|slot tail]; [simpl in Hcover; contradiction|].
    destruct slot as [snapshot|]; [simpl in Hcover; contradiction|].
    simpl in Hcover. destruct Hcover as [Hhead Htail]. simpl.
    f_equal. eapply IH. exact Htail.
Qed.

Lemma private_resume_witnesses_cover_snapshots_after_advance :
  forall CT h Z active witnesses snapshots,
    private_resume_witnesses_cover_snapshots Z witnesses snapshots ->
    private_resume_witnesses_cover_snapshots Z
      (advance_frozen_caller_snapshots CT h active witnesses)
      (advance_frozen_caller_snapshots CT h active snapshots).
Proof.
  intros CT h Z active witnesses. induction witnesses as
    [|witness witness_tail IH]; intros snapshots Hcover;
    destruct snapshots as [|snapshot snapshot_tail].
  - exact I.
  - simpl in Hcover. contradiction.
  - simpl in Hcover. contradiction.
  - destruct snapshot as [snapshot|]; [simpl in Hcover; contradiction|].
    simpl in Hcover |-*. destruct Hcover as [Hhead Htail]. split.
    + destruct witness as [head|]; simpl in *.
      * intros new_older Hnew state Hstate.
      unfold advance_frozen_caller_snapshots in Hnew.
      apply in_map_iff in Hnew.
      destruct Hnew as [old_slot [Heq Hold]].
      destruct old_slot as [old_older|]; simpl in Heq; [|discriminate].
      injection Heq as <-. simpl in *.
      eapply frozen_caller_authority_closure_monotone.
        -- eapply Hhead. exact Hold.
        -- exact Hstate.
      * intros new_older Hnew.
      unfold advance_frozen_caller_snapshots in Hnew.
      apply in_map_iff in Hnew.
      destruct Hnew as [old_slot [Heq Hold]].
      destruct old_slot as [old_older|]; simpl in Heq; [|discriminate].
      injection Heq as <-. eapply Hhead. exact Hold.
    + eapply IH. exact Htail.
Qed.

Lemma private_resume_witnesses_cover_snapshots_enter_private_nested :
  forall CT h Z caller callee caller_colors witnesses snapshots,
    private_resume_witnesses_cover_snapshots Z witnesses snapshots ->
    private_resume_witnesses_cover_snapshots Z
      (Some (private_nested_frozen_call_head CT h caller callee caller_colors
        snapshots witnesses) ::
       advance_frozen_caller_snapshots CT h callee witnesses)
      (None :: advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT h Z caller callee caller_colors witnesses snapshots Hcover.
  simpl. split.
  - intros new_older Hnew.
    unfold advance_frozen_caller_snapshots in Hnew.
    apply in_map_iff in Hnew.
    destruct Hnew as [old_slot [Heq Hold]].
    destruct old_slot as [old_older|]; simpl in Heq; [|discriminate].
    injection Heq as <-.
    intros state Hstate. exfalso.
    eapply private_resume_witnesses_cover_snapshots_none; eauto.
  - eapply private_resume_witnesses_cover_snapshots_after_advance.
    exact Hcover.
Qed.

Lemma private_resume_witnesses_cover_snapshots_enter_nested :
  forall CT h Z caller callee caller_colors witnesses snapshots,
    private_resume_witnesses_cover_snapshots Z witnesses snapshots ->
    private_resume_witnesses_cover_snapshots Z
      (Some (nested_frozen_call_head CT h caller callee caller_colors
        snapshots) ::
       advance_frozen_caller_snapshots CT h callee witnesses)
      (None :: advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT h Z caller callee caller_colors witnesses snapshots Hcover.
  simpl. split.
  - intros new_older Hnew mode_location Hcolor.
    unfold advance_frozen_caller_snapshots in Hnew.
    apply in_map_iff in Hnew.
    destruct Hnew as [old_slot [Heq Hold]].
    destruct old_slot as [old_older|]; simpl in Heq; [|discriminate].
    injection Heq as <-. simpl in *.
    destruct Hcolor as [seed [Hseed Hpath]].
    exists seed. split.
    + right. exists old_older. split; assumption.
    + exact Hpath.
  - eapply private_resume_witnesses_cover_snapshots_after_advance.
    exact Hcover.
Qed.

Lemma enter_nested_frozen_caller_snapshots_phase_wf :
  forall CT h caller callee caller_colors snapshots,
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    wf_r_config CT callee.(frame_senv) callee.(frame_renv) h ->
    authority_colors_runtime_mutable h caller_colors ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_dangerous snapshots ->
    frozen_caller_snapshots_resume_roots_in_heap h snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h caller snapshots ->
    let entered := enter_nested_frozen_caller_snapshots CT h caller callee
      caller_colors snapshots in
    frozen_caller_snapshots_runtime_mutable h entered /\
    frozen_caller_snapshots_closed CT h callee entered /\
    frozen_caller_snapshots_resume_roots_in_heap h entered /\
    frozen_caller_snapshots_resume_exposures_wf CT h callee entered.
Proof.
  intros CT h caller callee caller_colors snapshots Hcaller_wf Hcallee_wf
    Hcaller_runtime Hruntime Hdangerous Hroots Hexposure entered.
  unfold entered, enter_nested_frozen_caller_snapshots. simpl.
  set (head := nested_frozen_call_head CT h caller callee caller_colors
    snapshots).
  set (tail := advance_frozen_caller_snapshots CT h callee snapshots).
  have Hseed_runtime : authority_colors_runtime_mutable h
      (nested_frozen_call_entry_seeds caller_colors snapshots).
  { intros mode location Hseed. inversion Hseed; subst.
    - eapply Hcaller_runtime. exact (proj1 H).
    - destruct H as [snapshot [Hsnapshot Hcolor]].
      eapply Hruntime; eauto. }
  have Hhead_runtime : authority_colors_runtime_mutable h
      head.(frozen_snapshot_current_colors).
  { unfold head, nested_frozen_call_head. simpl.
    eapply advance_frozen_caller_snapshot_runtime_mutable; eauto. }
  have Htail_runtime : frozen_caller_snapshots_runtime_mutable h tail.
  { unfold tail. eapply advance_frozen_caller_snapshots_runtime_mutable;
      eauto. }
  split.
  - intros snapshot Hsnapshot mode location Hcolor. simpl in Hsnapshot.
    destruct Hsnapshot as [Heq | Htail].
    + injection Heq as <-. eapply Hhead_runtime. exact Hcolor.
    + eapply Htail_runtime; eauto.
  - split.
    + intros snapshot Hsnapshot. simpl in Hsnapshot.
      destruct Hsnapshot as [Heq | Htail].
      * injection Heq as <-. unfold head. apply nested_frozen_call_head_closed.
      * unfold tail in Htail.
        eapply advance_frozen_caller_snapshots_closed; eauto.
    + split.
      * intros snapshot root Hsnapshot Hroot. simpl in Hsnapshot.
        destruct Hsnapshot as [Heq | Htail].
        -- injection Heq as <-.
           unfold head, nested_frozen_call_head in Hroot. simpl in Hroot.
           unfold frame_rdm_root_set, typed_root in Hroot.
           destruct Hroot as [variable [T [Htype [Hvalue Hrdm]]]].
           exact (wf_config_value_dom CT caller.(frame_senv)
             caller.(frame_renv) h variable root Hcaller_wf Hvalue).
        -- unfold tail in Htail.
           have Htail_roots :=
             advance_frozen_caller_snapshots_resume_roots_in_heap CT h
               callee snapshots Hroots.
           eapply Htail_roots; eauto.
      * repeat split.
        -- intros snapshot Hsnapshot mode location Hcolor. simpl in Hsnapshot.
           destruct Hsnapshot as [Heq | Htail].
           ++ injection Heq as <-.
              unfold head, nested_frozen_call_head in Hcolor. simpl in Hcolor.
              eapply advance_frozen_caller_snapshot_runtime_mutable;
                [exact Hcallee_wf| |exact Hcolor].
              apply frame_resume_exposure_colors_runtime_mutable.
              exact Hcaller_wf.
           ++ have Htail_exposure :=
                advance_frozen_caller_snapshots_resume_exposures_wf_from_any_active
                  CT h caller callee snapshots Hcallee_wf Hexposure.
              eapply (proj1 Htail_exposure); eauto.
        -- intros snapshot Hsnapshot. simpl in Hsnapshot.
           destruct Hsnapshot as [Heq | Htail].
           ++ injection Heq as <-. unfold head, nested_frozen_call_head. simpl.
              apply (proj1 (frozen_caller_authority_closure_idempotent CT h
                callee (frame_resume_exposure_colors CT h caller))).
           ++ have Htail_exposure :=
                advance_frozen_caller_snapshots_resume_exposures_wf_from_any_active
                  CT h caller callee snapshots Hcallee_wf Hexposure.
              eapply (proj1 (proj2 Htail_exposure)); eauto.
        -- intros snapshot mode location Hsnapshot Hcolor. simpl in Hsnapshot.
           destruct Hsnapshot as [Heq | Htail].
           ++ injection Heq as <-.
              unfold head, nested_frozen_call_head in Hcolor. simpl in Hcolor.
              eapply frozen_caller_authority_closure_dangerous;
                [|exact Hcolor].
              apply frame_resume_exposure_colors_dangerous.
           ++ have Htail_exposure :=
                advance_frozen_caller_snapshots_resume_exposures_wf_from_any_active
                  CT h caller callee snapshots Hcallee_wf Hexposure.
              eapply (proj1 (proj2 (proj2 Htail_exposure))); eauto.
        -- intros snapshot Hsnapshot state Hstate. simpl in Hsnapshot.
           destruct Hsnapshot as [Heq | Htail].
           ++ injection Heq as <-. unfold head, nested_frozen_call_head in *.
              simpl in *. apply frozen_caller_authority_closure_contains.
              exact Hstate.
           ++ have Htail_exposure :=
                advance_frozen_caller_snapshots_resume_exposures_wf_from_any_active
                  CT h caller callee snapshots Hcallee_wf Hexposure.
              eapply (proj1 (proj2 (proj2 (proj2 Htail_exposure)))); eauto.
        -- intros snapshot root Hsnapshot Hroot Hroot_runtime.
           simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
           ++ injection Heq as <-. unfold head, nested_frozen_call_head in *.
              simpl in *. apply frozen_caller_authority_closure_contains.
              unfold frame_resume_exposure_colors.
              apply frozen_caller_authority_closure_contains.
              unfold frame_resume_exposure_seeds.
              exists root. repeat split; try assumption.
           ++ have Htail_exposure :=
                advance_frozen_caller_snapshots_resume_exposures_wf_from_any_active
                  CT h caller callee snapshots Hcallee_wf Hexposure.
              eapply (proj2 (proj2 (proj2 (proj2 Htail_exposure)))); eauto.
Qed.

Lemma private_resume_witnesses_phase_wf_enter_nested :
  forall CT h caller callee caller_colors witnesses snapshots,
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    wf_r_config CT callee.(frame_senv) callee.(frame_renv) h ->
    authority_colors_runtime_mutable h caller_colors ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_dangerous snapshots ->
    frozen_caller_snapshots_resume_roots_in_heap h snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h caller snapshots ->
    private_resume_witnesses_phase_wf CT h caller witnesses snapshots ->
    private_resume_witnesses_phase_wf CT h callee
      (Some (nested_frozen_call_head CT h caller callee caller_colors
        snapshots) ::
       advance_frozen_caller_snapshots CT h callee witnesses)
      (None :: advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT h caller callee caller_colors witnesses snapshots Hcaller_wf
    Hcallee_wf Hcaller_runtime Hruntime Hdangerous Hroots Hexposure Hphase.
  simpl.
  have Hentered := enter_nested_frozen_caller_snapshots_phase_wf CT h caller
    callee caller_colors snapshots Hcaller_wf Hcallee_wf Hcaller_runtime
    Hruntime Hdangerous Hroots Hexposure.
  unfold enter_nested_frozen_caller_snapshots in Hentered. simpl in Hentered.
  destruct Hentered as
    [Hentered_runtime [Hentered_closed [Hentered_roots Hentered_exposure]]].
  split; [exact Hentered_runtime|].
  split; [exact Hentered_closed|].
  split; [exact Hentered_roots|].
  split; [exact Hentered_exposure|].
  clear Hentered_runtime Hentered_closed Hentered_roots Hentered_exposure.
  clear Hruntime Hdangerous Hroots Hexposure.
  revert snapshots Hphase. induction witnesses as [|witness witness_tail IH];
    intros snapshots Hphase;
    destruct snapshots as [|snapshot snapshot_tail]; simpl in *;
    try contradiction; [exact I|].
  destruct Hphase as
    [Hw_runtime [Hw_closed [Hw_roots [Hw_exposure Hw_tail]]]].
  split.
  - change (frozen_caller_snapshots_runtime_mutable h
      (advance_frozen_caller_snapshots CT h callee
        (witness :: snapshot_tail))).
    eapply advance_frozen_caller_snapshots_runtime_mutable; eauto.
  - split.
    + change (frozen_caller_snapshots_closed CT h callee
        (advance_frozen_caller_snapshots CT h callee
          (witness :: snapshot_tail))).
      apply advance_frozen_caller_snapshots_closed.
    + split.
      * change (frozen_caller_snapshots_resume_roots_in_heap h
          (advance_frozen_caller_snapshots CT h callee
            (witness :: snapshot_tail))).
        eapply advance_frozen_caller_snapshots_resume_roots_in_heap; eauto.
      * split.
        -- change (frozen_caller_snapshots_resume_exposures_wf CT h callee
            (advance_frozen_caller_snapshots CT h callee
              (witness :: snapshot_tail))).
           eapply
             advance_frozen_caller_snapshots_resume_exposures_wf_from_any_active;
             eauto.
        -- eapply IH. exact Hw_tail.
Qed.

(** Self-resume safety is the diagonal companion of the pairwise nested
    certificate.  The same old-or-exceptional classification used for two
    distinct snapshots also transports a snapshot's own join certificate.
    Keeping this lemma separate makes the policy-only witness stack closed
    under phase advance without adding anything to the public state. *)
Lemma frozen_caller_snapshots_resume_joins_safe_after_classified_advance :
  forall CT new_h Z new_active snapshots exceptional,
    frozen_caller_snapshots_resume_joins_safe Z snapshots ->
    (forall snapshot active_mode source exposure_mode target,
      List.In (Some snapshot) snapshots ->
      authority_mode_dangerous active_mode ->
      In authority_flow_state exceptional (active_mode, source) ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
      authority_mode_dangerous exposure_mode ->
      In authority_flow_state
        snapshot.(frozen_snapshot_current_resume_exposure)
        (exposure_mode, target) ->
      ~ In Loc Z target) ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state exceptional (active_mode, location) ->
      ~ In Loc Z location) ->
    (forall snapshot mode location,
      List.In (Some snapshot) snapshots ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (frozen_caller_authority_closure CT new_h new_active
          snapshot.(frozen_snapshot_current_colors)) (mode, location) ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) location ->
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
    frozen_caller_snapshots_resume_joins_safe Z
      (advance_frozen_caller_snapshots CT new_h new_active snapshots).
Proof.
  intros CT new_h Z new_active snapshots exceptional Hjoins Hresume
    Hactive_safe Hclassify_color Hclassify_exposure new_snapshot source_mode
    source Hnew Hsource_mode Hsource Hsource_root.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  destruct (Hclassify_color old_snapshot source_mode source Hold Hsource_mode
    Hsource Hsource_root) as
    [[old_source_mode [Hold_source_mode Hold_source]] |
     [active_source_mode [Hactive_source_mode Hactive_source]]].
  - destruct (Hjoins old_snapshot old_source_mode source Hold
      Hold_source_mode Hold_source Hsource_root) as
      [[entry_mode [Hentry_mode Hentry]] | Hold_safe].
    + left. exists entry_mode. split; assumption.
    + right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
      destruct (Hclassify_exposure old_snapshot exposure_mode target Hold
        Hexposure_mode Htarget Hprotected) as
        [[old_exposure_mode [Hold_exposure_mode Hold_target]] |
         [active_target_mode [Hactive_target_mode Hactive_target]]].
      * eapply Hold_safe; eauto.
      * eapply Hactive_safe; eauto.
  - right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
    destruct (Hclassify_exposure old_snapshot exposure_mode target Hold
      Hexposure_mode Htarget Hprotected) as
      [[old_exposure_mode [Hold_exposure_mode Hold_target]] |
       [active_target_mode [Hactive_target_mode Hactive_target]]].
    + eapply Hresume with (snapshot := old_snapshot)
        (active_mode := active_source_mode) (source := source)
        (exposure_mode := old_exposure_mode); eauto.
    + eapply Hactive_safe; eauto.
Qed.

Lemma frozen_caller_snapshots_resume_joins_safe_after_classified_advance_entry :
  forall CT new_h Z new_active snapshots exceptional,
    frozen_caller_snapshots_resume_joins_safe Z snapshots ->
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
    (forall snapshot mode location,
      List.In (Some snapshot) snapshots ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (frozen_caller_authority_closure CT new_h new_active
          snapshot.(frozen_snapshot_current_colors)) (mode, location) ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) location ->
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
    frozen_caller_snapshots_resume_joins_safe Z
      (advance_frozen_caller_snapshots CT new_h new_active snapshots).
Proof.
  intros CT new_h Z new_active snapshots exceptional Hjoins Hresume
    Hactive_safe Hclassify_color Hclassify_exposure new_snapshot source_mode
    source Hnew Hsource_mode Hsource Hsource_root.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  destruct (Hclassify_color old_snapshot source_mode source Hold Hsource_mode
    Hsource Hsource_root) as
    [[old_source_mode [Hold_source_mode Hold_source]] |
     [active_source_mode [Hactive_source_mode Hactive_source]]].
  - destruct (Hjoins old_snapshot old_source_mode source Hold
      Hold_source_mode Hold_source Hsource_root) as
      [[entry_mode [Hentry_mode Hentry]] | Hold_safe].
    + left. exists entry_mode. split; assumption.
    + right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
      destruct (Hclassify_exposure old_snapshot exposure_mode target Hold
        Hexposure_mode Htarget Hprotected) as
        [[old_exposure_mode [Hold_exposure_mode Hold_target]] |
         [active_target_mode [Hactive_target_mode Hactive_target]]].
      * eapply Hold_safe; eauto.
      * eapply Hactive_safe; eauto.
  - destruct (Hresume old_snapshot active_source_mode source Hold
      Hactive_source_mode Hactive_source Hsource_root) as
      [[entry_mode [Hentry_mode Hentry]] | Hexceptional_safe].
    + left. exists entry_mode. simpl. split; assumption.
    + right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
      destruct (Hclassify_exposure old_snapshot exposure_mode target Hold
        Hexposure_mode Htarget Hprotected) as
        [[old_exposure_mode [Hold_exposure_mode Hold_target]] |
         [active_target_mode [Hactive_target_mode Hactive_target]]].
      * eapply Hexceptional_safe; eauto.
      * eapply Hactive_safe; eauto.
Qed.

Lemma frozen_caller_snapshots_resume_joins_safe_after_active_descent :
  forall CT h Z authority old_senv old_renv new_senv new_renv snapshots,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    frozen_caller_snapshots_closed CT h
      (mk_watched_frame authority old_senv old_renv) snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame authority old_senv old_renv) snapshots ->
    frozen_caller_snapshots_resume_joins_safe Z snapshots ->
    frozen_caller_snapshots_resume_joins_safe Z
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) snapshots).
Proof.
  intros CT h Z authority old_senv old_renv new_senv new_renv snapshots
    Hdescend Hclosed Hexposure Hjoins new_snapshot source_mode source Hnew
    Hsource_mode Hsource Hsource_root.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  have Hold_source : In authority_flow_state
      old_snapshot.(frozen_snapshot_current_colors) (source_mode, source).
  { eapply Hclosed; [exact Hold|].
    destruct Hsource as [seed [Hseed Hpath]]. exists seed.
    split; [exact Hseed|].
    eapply frozen_caller_connected_after_descent_reflects; eauto. }
  destruct (Hjoins old_snapshot source_mode source Hold Hsource_mode
    Hold_source Hsource_root) as
    [[entry_mode [Hentry_mode Hentry]] | Hsafe].
  - left. exists entry_mode. split; assumption.
  - right. intros exposure_mode target Hexposure_mode Htarget.
    eapply Hsafe; [exact Hexposure_mode|].
    eapply (proj1 (proj2 Hexposure)); [exact Hold|].
    destruct Htarget as [seed [Hseed Hpath]]. exists seed.
    split; [exact Hseed|].
    eapply frozen_caller_connected_after_descent_reflects; eauto.
Qed.

Lemma frozen_caller_snapshots_resume_joins_safe_after_graph_reflection :
  forall CT h h' Z active snapshots,
    (forall left right,
      retained_mut_edge CT h' left right -> retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right -> mutable_edge CT h left right) ->
    frozen_caller_snapshots_closed CT h active snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h active snapshots ->
    frozen_caller_snapshots_resume_joins_safe Z snapshots ->
    frozen_caller_snapshots_resume_joins_safe Z
      (advance_frozen_caller_snapshots CT h' active snapshots).
Proof.
  intros CT h h' Z active snapshots Hretained Hmutable Hclosed Hexposure
    Hjoins.
  eapply frozen_caller_snapshots_resume_joins_safe_after_classified_advance
    with (exceptional := Empty_set authority_flow_state).
  - exact Hjoins.
  - intros snapshot mode source exposure_mode target Hsnapshot Hmode Hempty.
    inversion Hempty.
  - intros mode location Hmode Hempty. inversion Hempty.
  - intros snapshot mode location Hsnapshot Hmode Hcolor Hroot.
    left. exists mode. split; [exact Hmode|].
    eapply frozen_caller_closure_after_graph_reflection_included; eauto.
  - intros snapshot mode location Hsnapshot Hmode Hcolor Hprotected.
    left. exists mode. split; [exact Hmode|].
    eapply frozen_caller_closure_after_graph_reflection_included; eauto.
    exact ((proj1 (proj2 Hexposure)) snapshot Hsnapshot).
Qed.

Lemma frozen_caller_snapshots_resume_joins_safe_after_safe_field_update :
  forall CT h Z frame snapshots lx old field written,
    runtime_getObj h lx = Some old ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_closed CT h frame snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h frame snapshots ->
    authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h frame) ->
    authority_safe_field_endpoints CT h frame lx written ->
    frozen_caller_snapshots_resume_roots_safe CT h Z frame snapshots ->
    frozen_caller_snapshots_resume_joins_safe Z snapshots ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h frame)
        (active_mode, location) ->
      ~ In Loc Z location) ->
    frozen_caller_snapshots_resume_joins_safe Z
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame snapshots).
Proof.
  intros CT h Z frame snapshots lx old field written Hobj Hruntime Hclosed
    Hexposure Hactive_runtime Hendpoints Hresume Hjoins Hactive_safe.
  eapply frozen_caller_snapshots_resume_joins_safe_after_classified_advance
    with (exceptional := independent_active_authority_colors CT h frame).
  - exact Hjoins.
  - exact Hresume.
  - exact Hactive_safe.
  - intros snapshot mode location Hsnapshot Hmode [seed [Hseed Hpath]] _.
    destruct seed as [seed_mode seed_location].
    have Hseed_covered : frozen_authority_state_covered_by_old_or_active
        snapshot.(frozen_snapshot_current_colors)
        (independent_active_authority_colors CT h frame)
        (seed_mode, seed_location).
    { intros Hseed_mode. left. exists seed_mode. split; assumption. }
    have Hcovered :=
      frozen_caller_connected_after_safe_field_update_covered_by_old_or_active
        CT h frame snapshot.(frozen_snapshot_current_colors) lx old field
        written (seed_mode, seed_location) (mode, location) Hobj
        (Hruntime snapshot Hsnapshot) (Hclosed snapshot Hsnapshot)
        Hactive_runtime Hendpoints Hseed_covered Hpath.
    exact (Hcovered Hmode).
  - intros snapshot mode location Hsnapshot Hmode [seed [Hseed Hpath]] _.
    destruct seed as [seed_mode seed_location].
    have Hseed_covered : frozen_authority_state_covered_by_old_or_active
        snapshot.(frozen_snapshot_current_resume_exposure)
        (independent_active_authority_colors CT h frame)
        (seed_mode, seed_location).
    { intros Hseed_mode. left. exists seed_mode. split; assumption. }
    have Hcovered :=
      frozen_caller_connected_after_safe_field_update_covered_by_old_or_active
        CT h frame snapshot.(frozen_snapshot_current_resume_exposure)
        lx old field written (seed_mode, seed_location) (mode, location) Hobj
        ((proj1 Hexposure) snapshot Hsnapshot)
        ((proj1 (proj2 Hexposure)) snapshot Hsnapshot)
        Hactive_runtime Hendpoints Hseed_covered Hpath.
    exact (Hcovered Hmode).
Qed.

Lemma frozen_caller_snapshots_resume_joins_safe_after_safe_field_update_entry :
  forall CT h Z frame snapshots lx old field written,
    runtime_getObj h lx = Some old ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_closed CT h frame snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h frame snapshots ->
    authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h frame) ->
    authority_safe_field_endpoints CT h frame lx written ->
    frozen_caller_snapshots_active_resume_safe CT h Z frame snapshots ->
    frozen_caller_snapshots_resume_joins_safe Z snapshots ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h frame)
        (active_mode, location) ->
      ~ In Loc Z location) ->
    frozen_caller_snapshots_resume_joins_safe Z
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame snapshots).
Proof.
  intros CT h Z frame snapshots lx old field written Hobj Hruntime Hclosed
    Hexposure Hactive_runtime Hendpoints Hresume Hjoins Hactive_safe.
  eapply
    frozen_caller_snapshots_resume_joins_safe_after_classified_advance_entry
    with (exceptional := independent_active_authority_colors CT h frame).
  - exact Hjoins.
  - unfold frozen_caller_snapshots_active_resume_safe in Hresume.
    exact Hresume.
  - exact Hactive_safe.
  - intros snapshot mode location Hsnapshot Hmode [seed [Hseed Hpath]] _.
    destruct seed as [seed_mode seed_location].
    have Hseed_covered : frozen_authority_state_covered_by_old_or_active
        snapshot.(frozen_snapshot_current_colors)
        (independent_active_authority_colors CT h frame)
        (seed_mode, seed_location).
    { intros Hseed_mode. left. exists seed_mode. split; assumption. }
    have Hcovered :=
      frozen_caller_connected_after_safe_field_update_covered_by_old_or_active
        CT h frame snapshot.(frozen_snapshot_current_colors) lx old field
        written (seed_mode, seed_location) (mode, location) Hobj
        (Hruntime snapshot Hsnapshot) (Hclosed snapshot Hsnapshot)
        Hactive_runtime Hendpoints Hseed_covered Hpath.
    exact (Hcovered Hmode).
  - intros snapshot mode location Hsnapshot Hmode [seed [Hseed Hpath]] _.
    destruct seed as [seed_mode seed_location].
    have Hseed_covered : frozen_authority_state_covered_by_old_or_active
        snapshot.(frozen_snapshot_current_resume_exposure)
        (independent_active_authority_colors CT h frame)
        (seed_mode, seed_location).
    { intros Hseed_mode. left. exists seed_mode. split; assumption. }
    have Hcovered :=
      frozen_caller_connected_after_safe_field_update_covered_by_old_or_active
        CT h frame snapshot.(frozen_snapshot_current_resume_exposure)
        lx old field written (seed_mode, seed_location) (mode, location) Hobj
        ((proj1 Hexposure) snapshot Hsnapshot)
        ((proj1 (proj2 Hexposure)) snapshot Hsnapshot)
        Hactive_runtime Hendpoints Hseed_covered Hpath.
    exact (Hcovered Hmode).
Qed.

Lemma frozen_caller_snapshots_resume_roots_safe_after_safe_call_entry_from_parts :
  forall CT Z caller_authority sGamma mt rGamma h snapshots x method y args
    sGamma' vals ly cy runtime_mdef Ty,
    wf_r_config CT sGamma rGamma h ->
    authority_context_sound h rGamma caller_authority ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame caller_authority sGamma rGamma) snapshots ->
    frozen_caller_snapshots_resume_roots_safe CT h Z
      (mk_watched_frame caller_authority sGamma rGamma) snapshots ->
    executing_authority_colors_separated CT h Z
      (mk_watched_frame caller_authority sGamma rGamma)
      (Empty_set authority_flow_state) ->
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_caller_snapshots_resume_roots_safe CT h Z callee
      (advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT Z caller_authority sGamma mt rGamma h snapshots x method y args
    sGamma' vals ly cy runtime_mdef Ty Hwf Hsound Htyping Hscope Hgety Hvalue
    Hbase Hfind Hargs Hexposure Hresume Hseparated callee new_snapshot
    active_mode source exposure_mode target Hnew Hactive_mode Hactive Hroot
    Hexposure_mode Htarget Hprotected.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  have Hcallee_color : In authority_flow_state
      (executing_authority_color_set CT h callee
        (executing_authority_color_set CT h
          (mk_watched_frame caller_authority sGamma rGamma)
          (Empty_set authority_flow_state))) (active_mode, source).
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
  destruct (executing_with_frozen_incoming_dangerous_covered_by_old_or_active
    CT h (mk_watched_frame caller_authority sGamma rGamma)
    old_snapshot.(frozen_snapshot_current_resume_exposure) old_exposure_mode
    target ((proj1 (proj2 Hexposure)) old_snapshot Hold)
    Hold_exposure_mode Hold_target) as
    [[snapshot_mode [Hsnapshot_mode Hsnapshot_target]] |
     [target_active_mode [Htarget_active_mode Htarget_active]]].
  - eapply Hresume with (snapshot := old_snapshot) (active_mode := old_mode)
      (source := source) (exposure_mode := snapshot_mode); eauto.
  - eapply Hseparated; [exact Htarget_active_mode| |exact Hprotected].
    eapply independent_active_authority_colors_in_executing.
    exact Htarget_active.
Qed.

Lemma nested_frozen_call_head_resume_roots_safe_at_safe_call_entry :
  forall CT Z caller_authority sGamma mt rGamma h caller_colors snapshots
    x method y args sGamma' vals ly cy runtime_mdef Ty,
    wf_r_config CT sGamma rGamma h ->
    authority_context_sound h rGamma caller_authority ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    executing_authority_colors_separated CT h Z
      (mk_watched_frame caller_authority sGamma rGamma)
      (Empty_set authority_flow_state) ->
    let caller := mk_watched_frame caller_authority sGamma rGamma in
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_caller_snapshots_resume_roots_safe CT h Z callee
      [Some (nested_frozen_call_head CT h caller callee caller_colors
        snapshots)].
Proof.
  intros CT Z caller_authority sGamma mt rGamma h caller_colors snapshots
    x method y args sGamma' vals ly cy runtime_mdef Ty Hwf Hsound Htyping
    Hscope Hgety Hvalue Hbase Hfind Hargs Hseparated caller callee snapshot
    active_mode source exposure_mode target Hsnapshot Hactive_mode Hactive
    Hroot Hexposure_mode Htarget Hprotected.
  simpl in Hsnapshot. destruct Hsnapshot as [Heq | Hbad]; [|contradiction].
  injection Heq as <-. simpl in *.
  have Hcallee_color : In authority_flow_state
      (executing_authority_color_set CT h callee
        (independent_active_authority_colors CT h caller))
      (active_mode, source).
  { eapply independent_active_authority_colors_in_executing. exact Hactive. }
  destruct (executing_authority_colors_enter_call_covered CT caller_authority
    sGamma mt rGamma h x method y args sGamma' vals ly cy runtime_mdef Ty
    (Empty_set authority_flow_state) Hwf Hsound
    (ltac:(intros mode location Hempty; inversion Hempty)) Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs active_mode source Hactive_mode
    Hcallee_color) as [old_mode [Hold_mode Hold_source]].
  have Hcallee_target : In authority_flow_state
      (executing_authority_color_set CT h callee
        (executing_authority_color_set CT h caller
          (frame_resume_exposure_colors CT h caller)))
      (exposure_mode, target).
  { destruct Htarget as [seed [Hseed Hpath]]. exists seed. split.
    - left. apply executing_authority_color_set_contains_incoming. exact Hseed.
    - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
  destruct (executing_authority_colors_enter_call_covered CT caller_authority
    sGamma mt rGamma h x method y args sGamma' vals ly cy runtime_mdef Ty
    (frame_resume_exposure_colors CT h caller) Hwf Hsound
    (frame_resume_exposure_colors_runtime_mutable CT h caller Hwf) Htyping
    Hscope Hgety Hvalue Hbase Hfind Hargs exposure_mode target Hexposure_mode
    Hcallee_target) as [caller_target_mode
      [Hcaller_target_mode Hcaller_target]].
  destruct (executing_with_frozen_incoming_dangerous_covered_by_old_or_active
    CT h caller (frame_resume_exposure_colors CT h caller)
    caller_target_mode target
    (ltac:(unfold frame_resume_exposure_colors;
      apply (proj1 (frozen_caller_authority_closure_idempotent CT h caller
        (frame_resume_exposure_seeds h caller)))))
    Hcaller_target_mode Hcaller_target) as
    [[resume_mode [Hresume_mode Hresume_target]] |
     [independent_mode [Hindependent_mode Hindependent_target]]].
  - have Hexposure_in_independent : Included authority_flow_state
        (frame_resume_exposure_colors CT h caller)
        (independent_active_authority_colors CT h caller).
    { eapply dangerous_rdm_root_color_covers_frame_resume_exposure
        with (mode := old_mode) (source := source).
      - apply independent_active_authority_colors_frozen_closed.
      - exact Hold_mode.
      - exact Hold_source.
      - exact Hroot. }
    eapply Hseparated; [exact Hresume_mode| |exact Hprotected].
    eapply independent_active_authority_colors_in_executing.
    apply Hexposure_in_independent. exact Hresume_target.
  - eapply Hseparated; [exact Hindependent_mode| |exact Hprotected].
    eapply independent_active_authority_colors_in_executing.
    exact Hindependent_target.
Qed.

Lemma frozen_caller_snapshots_active_resume_safe_after_safe_call_entry_from_parts :
  forall CT Z caller_authority sGamma mt rGamma h snapshots x method y args
    sGamma' vals ly cy runtime_mdef Ty,
    wf_r_config CT sGamma rGamma h ->
    authority_context_sound h rGamma caller_authority ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    executing_authority_colors_separated CT h Z
      (mk_watched_frame caller_authority sGamma rGamma)
      (Empty_set authority_flow_state) ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame caller_authority sGamma rGamma) snapshots ->
    frozen_caller_snapshots_active_resume_safe CT h Z
      (mk_watched_frame caller_authority sGamma rGamma) snapshots ->
    let caller := mk_watched_frame caller_authority sGamma rGamma in
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_caller_snapshots_active_resume_safe CT h Z callee
      (advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT Z caller_authority sGamma mt rGamma h snapshots x method y args
    sGamma' vals ly cy runtime_mdef Ty Hwf Hsound Htyping Hscope Hgety
    Hvalue Hbase Hfind Hargs Hseparated Hexposure Hsafe caller callee.
  unfold frozen_caller_snapshots_active_resume_safe in *.
  intros new_snapshot source_mode source Hnew Hsource_mode Hsource Hroot.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  have Hsource_completed : In authority_flow_state
      (executing_authority_color_set CT h callee
        (executing_authority_color_set CT h caller
          (Empty_set authority_flow_state))) (source_mode, source).
  { eapply independent_active_authority_colors_in_executing. exact Hsource. }
  destruct (executing_authority_colors_enter_call_covered CT
    caller_authority sGamma mt rGamma h x method y args sGamma' vals ly cy
    runtime_mdef Ty (Empty_set authority_flow_state) Hwf Hsound
    (ltac:(intros mode location Hempty; inversion Hempty)) Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs source_mode source Hsource_mode
    Hsource_completed) as
    [caller_mode [Hcaller_mode Hcaller_source]].
  destruct (Hsafe old_snapshot caller_mode source Hold Hcaller_mode
    Hcaller_source Hroot) as
    [[entry_mode [Hentry_mode Hentry]] | Hold_safe].
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
      Hcallee_target) as
      [caller_target_mode [Hcaller_target_mode Hcaller_target]].
    destruct (executing_with_frozen_incoming_dangerous_covered_by_old_or_active
      CT h caller old_snapshot.(frozen_snapshot_current_resume_exposure)
      caller_target_mode target ((proj1 (proj2 Hexposure)) old_snapshot Hold)
      Hcaller_target_mode Hcaller_target) as
      [[old_target_mode [Hold_target_mode Hold_target]] |
       [active_target_mode [Hactive_target_mode Hactive_target]]].
    + exact (Hold_safe old_target_mode target Hold_target_mode Hold_target
        Hprotected).
    + eapply Hseparated; [exact Hactive_target_mode| |exact Hprotected].
      eapply independent_active_authority_colors_in_executing.
      exact Hactive_target.
Qed.

Lemma private_resume_witnesses_roots_safe_enter_nested :
  forall CT Z caller_authority sGamma mt rGamma h caller_colors witnesses
    snapshots x method y args sGamma' vals ly cy runtime_mdef Ty,
    wf_r_config CT sGamma rGamma h ->
    authority_context_sound h rGamma caller_authority ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    executing_authority_colors_separated CT h Z
      (mk_watched_frame caller_authority sGamma rGamma)
      (Empty_set authority_flow_state) ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame caller_authority sGamma rGamma) snapshots ->
    frozen_caller_snapshots_resume_roots_safe CT h Z
      (mk_watched_frame caller_authority sGamma rGamma) snapshots ->
    private_resume_witnesses_phase_wf CT h
      (mk_watched_frame caller_authority sGamma rGamma) witnesses snapshots ->
    private_resume_witnesses_roots_safe CT h Z
      (mk_watched_frame caller_authority sGamma rGamma) witnesses snapshots ->
    let caller := mk_watched_frame caller_authority sGamma rGamma in
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    private_resume_witnesses_roots_safe CT h Z callee
      (Some (nested_frozen_call_head CT h caller callee caller_colors
        snapshots) ::
       advance_frozen_caller_snapshots CT h callee witnesses)
      (None :: advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT Z caller_authority sGamma mt rGamma h caller_colors witnesses
    snapshots x method y args sGamma' vals ly cy runtime_mdef Ty Hwf Hsound
    Htyping Hscope Hgety Hvalue Hbase Hfind Hargs Hseparated
    Hactual_exposure Hactual_safe Hphase Hsafe caller callee. simpl.
  split.
  - have Hhead := nested_frozen_call_head_resume_roots_safe_at_safe_call_entry
      CT Z caller_authority sGamma mt rGamma h caller_colors snapshots x
      method y args sGamma' vals ly cy runtime_mdef Ty Hwf Hsound Htyping
      Hscope Hgety Hvalue Hbase Hfind Hargs Hseparated.
    have Htail :=
      frozen_caller_snapshots_resume_roots_safe_after_safe_call_entry_from_parts
        CT Z caller_authority sGamma mt rGamma h snapshots x method y args
        sGamma' vals ly cy runtime_mdef Ty Hwf Hsound Htyping Hscope Hgety
        Hvalue Hbase Hfind Hargs Hactual_exposure Hactual_safe Hseparated.
    unfold frozen_caller_snapshots_active_resume_safe.
    intros snapshot active_mode source Hsnapshot Hactive_mode Hactive Hroot.
    simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail_slot].
    + right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
      exact (Hhead snapshot active_mode source exposure_mode target
        (ltac:(simpl; left; exact Heq)) Hactive_mode Hactive Hroot
        Hexposure_mode Htarget Hprotected).
    + right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
      exact (Htail snapshot active_mode source exposure_mode target Htail_slot
        Hactive_mode Hactive Hroot Hexposure_mode Htarget Hprotected).
  - clear Hactual_exposure Hactual_safe.
    revert snapshots Hphase Hsafe. induction witnesses as
      [|witness witness_tail IH]; intros snapshots Hphase Hsafe;
      destruct snapshots as [|snapshot snapshot_tail]; simpl in *;
      try contradiction; [exact I|].
    destruct Hphase as
      [Hruntime [Hclosed [Hroots [Hexposure Htail_phase]]]].
    destruct Hsafe as [Hhead_safe Htail_safe]. split.
    + change (frozen_caller_snapshots_active_resume_safe CT h Z callee
        (advance_frozen_caller_snapshots CT h callee
          (witness :: snapshot_tail))).
      eapply
        frozen_caller_snapshots_active_resume_safe_after_safe_call_entry_from_parts;
        eauto.
    + eapply IH; eauto.
Qed.

Lemma frozen_caller_snapshots_nested_resume_safe_after_safe_call_entry_from_parts :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_closed CT h
      (mk_watched_frame caller_authority sGamma rGamma) snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame caller_authority sGamma rGamma) snapshots ->
    frozen_caller_snapshots_active_resume_safe CT h Z
      (mk_watched_frame caller_authority sGamma rGamma) snapshots ->
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
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty Hmain
    Htyping Hscope Hgety Hvalue Hbase Hfind Hargs Hruntime Hclosed Hexposure
    Hresume Hnested callee.
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
  eapply
    frozen_caller_snapshots_nested_resume_safe_after_classified_advance_entry
    with (exceptional := exceptional).
  - exact Hnested.
  - unfold exceptional, caller,
      frozen_caller_snapshots_active_resume_safe in Hresume.
    exact Hresume.
  - intros active_mode location Hactive_mode Hactive Hprotected.
    eapply Hmain_separated; [exact Hactive_mode| |exact Hprotected].
    eapply independent_active_authority_colors_in_executing. exact Hactive.
  - intros snapshot older mode location Hsnapshot _ Hmode Hcolor _.
    eapply Hclassify; eauto.
  - intros snapshot mode location Hsnapshot Hmode Hcolor _.
    eapply Hclassify.
    + exact ((proj1 Hexposure) snapshot Hsnapshot).
    + exact ((proj1 (proj2 Hexposure)) snapshot Hsnapshot).
    + exact Hmode.
    + exact Hcolor.
Qed.

Lemma frozen_caller_snapshots_resume_joins_safe_after_safe_call_entry_from_parts :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_closed CT h
      (mk_watched_frame caller_authority sGamma rGamma) snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame caller_authority sGamma rGamma) snapshots ->
    frozen_caller_snapshots_active_resume_safe CT h Z
      (mk_watched_frame caller_authority sGamma rGamma) snapshots ->
    frozen_caller_snapshots_resume_joins_safe Z snapshots ->
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_caller_snapshots_resume_joins_safe Z
      (advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty Hmain
    Htyping Hscope Hgety Hvalue Hbase Hfind Hargs Hruntime Hclosed Hexposure
    Hresume Hjoins callee.
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
  eapply
    frozen_caller_snapshots_resume_joins_safe_after_classified_advance_entry
    with (exceptional := exceptional).
  - exact Hjoins.
  - unfold exceptional, caller,
      frozen_caller_snapshots_active_resume_safe in Hresume.
    exact Hresume.
  - intros active_mode location Hactive_mode Hactive Hprotected.
    eapply Hmain_separated; [exact Hactive_mode| |exact Hprotected].
    eapply independent_active_authority_colors_in_executing. exact Hactive.
  - intros snapshot mode location Hsnapshot Hmode Hcolor _.
    eapply Hclassify; eauto.
  - intros snapshot mode location Hsnapshot Hmode Hcolor _.
    eapply Hclassify.
    + exact ((proj1 Hexposure) snapshot Hsnapshot).
    + exact ((proj1 (proj2 Hexposure)) snapshot Hsnapshot).
    + exact Hmode.
    + exact Hcolor.
Qed.

Lemma frozen_completed_colors_resume_safe_after_safe_call_entry_from_parts :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty,
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
      (mk_watched_frame caller_authority sGamma rGamma) snapshots ->
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
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty Hmain
    Htyping Hscope Hgety Hvalue Hbase Hfind Hargs Hexposure Hcompleted caller
    caller_colors callee.
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
  injection Heq as <-. simpl in *.
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
      Hcallee_target) as
      [caller_target_mode [Hcaller_target_mode Hcaller_target]].
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

Lemma frozen_completed_colors_resume_phase_safe_after_safe_call_entry_from_parts :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty,
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
      (mk_watched_frame caller_authority sGamma rGamma) snapshots ->
    frozen_completed_colors_resume_phase_safe Z
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
    frozen_completed_colors_resume_phase_safe Z
      (executing_authority_color_set CT h callee caller_colors)
      (advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty Hmain
    Htyping Hscope Hgety Hvalue Hbase Hfind Hargs Hexposure Hsafe caller
    caller_colors callee.
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
  injection Heq as <-. simpl in *.
  destruct (executing_authority_colors_enter_call_covered CT
    caller_authority sGamma mt rGamma h x method y args sGamma' vals ly cy
    runtime_mdef Ty incoming Hwf Hsound Hincoming_runtime Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs source_mode source Hsource_mode Hsource) as
    [caller_mode [Hcaller_mode Hcaller_source]].
  destruct (Hsafe old_snapshot caller_mode source Hold Hcaller_mode
    Hcaller_source Hroot) as
    [[phase_mode [Hphase_mode Hphase]] | Hold_safe].
  - left. exists phase_mode. split; assumption.
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
      Hcallee_target) as
      [caller_target_mode [Hcaller_target_mode Hcaller_target]].
    destruct (executing_with_frozen_incoming_dangerous_covered_by_old_or_active
      CT h caller old_snapshot.(frozen_snapshot_current_resume_exposure)
      caller_target_mode target ((proj1 (proj2 Hexposure)) old_snapshot Hold)
      Hcaller_target_mode Hcaller_target) as
      [[old_target_mode [Hold_target_mode Hold_target]] |
       [active_target_mode [Hactive_target_mode Hactive_target]]].
    + exact (Hold_safe old_target_mode target Hold_target_mode Hold_target
        Hprotected).
    + eapply Hmain_separated; [exact Hactive_target_mode| |exact Hprotected].
      eapply independent_active_authority_colors_in_executing.
      exact Hactive_target.
Qed.

Lemma private_resume_witnesses_nested_resume_safe_after_safe_call_entry :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    witnesses snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    private_resume_witnesses_phase_wf CT h
      (mk_watched_frame caller_authority sGamma rGamma) witnesses snapshots ->
    private_resume_witnesses_roots_safe CT h Z
      (mk_watched_frame caller_authority sGamma rGamma) witnesses snapshots ->
    private_resume_witnesses_nested_resume_safe Z witnesses snapshots ->
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    private_resume_witnesses_nested_resume_safe Z
      (advance_frozen_caller_snapshots CT h callee witnesses)
      (advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    witnesses. induction witnesses as [|witness witness_tail IH];
    intros snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty
    Hmain Htyping Hscope Hgety Hvalue Hbase Hfind Hargs Hphase Hroots Hnested
    callee; destruct snapshots as [|snapshot snapshot_tail]; simpl in *;
    try contradiction; [exact I|].
  destruct Hphase as
    [Hruntime [Hclosed [Hphase_roots [Hexposure Htail_phase]]]].
  destruct Hroots as [Hhead_roots Htail_roots].
  destruct Hnested as [Hhead_nested Htail_nested]. split.
  - change (frozen_caller_snapshots_nested_resume_safe Z
      (advance_frozen_caller_snapshots CT h callee
        (witness :: snapshot_tail))).
    eapply
      frozen_caller_snapshots_nested_resume_safe_after_safe_call_entry_from_parts;
      eauto.
  - eapply IH; eauto.
Qed.

Lemma private_resume_witnesses_completed_safe_after_safe_call_entry :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    witnesses snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    private_resume_witnesses_phase_wf CT h
      (mk_watched_frame caller_authority sGamma rGamma) witnesses snapshots ->
    private_resume_witnesses_completed_safe CT h Z
      (mk_watched_frame caller_authority sGamma rGamma) incoming witnesses
      snapshots ->
    let caller := mk_watched_frame caller_authority sGamma rGamma in
    let caller_colors := executing_authority_color_set CT h caller incoming in
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    private_resume_witnesses_completed_safe CT h Z callee caller_colors
      (advance_frozen_caller_snapshots CT h callee witnesses)
      (advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    witnesses. induction witnesses as [|witness witness_tail IH];
    intros snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty
    Hmain Htyping Hscope Hgety Hvalue Hbase Hfind Hargs Hphase Hcompleted
    caller caller_colors callee;
    destruct snapshots as [|snapshot snapshot_tail]; simpl in *;
    try contradiction; [exact I|].
  destruct Hphase as
    [Hruntime [Hclosed [Hphase_roots [Hexposure Htail_phase]]]].
  destruct Hcompleted as [Hhead_completed Htail_completed]. split.
  - change (frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h callee caller_colors)
      (advance_frozen_caller_snapshots CT h callee
        (witness :: snapshot_tail))).
    eapply
      frozen_completed_colors_resume_safe_after_safe_call_entry_from_parts;
      eauto.
  - eapply IH; eauto.
Qed.

(** The policy-only head created at an untracked call is safe against every
    older ordinary snapshot.  Unlike the channel-free tracked-entry helper,
    this proof uses the safe-call reflection theorem directly: a dangerous
    head color is classified as either completed immediate-caller authority
    or an imported older frozen color. *)
Lemma nested_frozen_call_head_resume_safe_against_advanced_tail_at_safe_call_entry :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_frozen_authority_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots h ->
    frozen_caller_snapshots_nested_covered snapshots ->
    frozen_caller_snapshots_nested_resume_safe Z snapshots ->
    frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) incoming)
      snapshots ->
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
    forall new_older,
      List.In (Some new_older)
        (advance_frozen_caller_snapshots CT h callee snapshots) ->
      frozen_snapshot_resume_safe_against Z
        (nested_frozen_call_head CT h caller callee caller_colors snapshots)
        new_older.
Proof.
  intros CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty Hfrozen
    Hcovered Hnested Hcompleted Htyping Hscope Hgety Hvalue Hbase Hfind Hargs
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
  have Hcaller_colors_runtime : authority_colors_runtime_mutable h
      caller_colors.
  { unfold caller_colors, caller.
    eapply executing_authority_colors_runtime_mutable; eauto. }
  have Hmain_separated := proj1 (proj2 (proj2 (proj2 Hmain))).
  set (seeds := nested_frozen_call_entry_seeds caller_colors snapshots).
  have Hseeds_runtime : authority_colors_runtime_mutable h seeds.
  { intros mode location Hseed. unfold seeds,
      nested_frozen_call_entry_seeds in Hseed.
    inversion Hseed; subst.
    - destruct H as [Hcaller_color Hcaller_mode].
      eapply Hcaller_colors_runtime. exact Hcaller_color.
    - destruct H as [snapshot [Hsnapshot Hsnapshot_color]].
      eapply Hruntime; eauto. }
  have Hseeds_closed : Included authority_flow_state
      (frozen_caller_authority_closure CT h caller seeds) seeds.
  { intros state [seed [Hseed Hpath]]. unfold seeds,
      nested_frozen_call_entry_seeds in *.
    inversion Hseed; subst.
    - destruct H as [Hcaller_seed Hseed_mode]. left. split.
      + unfold caller_colors in *.
        eapply executing_authority_color_set_frozen_closed.
        exists seed. split; assumption.
      + eapply frozen_caller_authority_connected_preserves_dangerous;
          eauto.
    - destruct H as [snapshot [Hsnapshot Hsnapshot_seed]].
      right. exists snapshot. split; [exact Hsnapshot|].
      eapply Hclosed; [exact Hsnapshot|]. exists seed. split; assumption. }
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
        In authority_flow_state
          (independent_active_authority_colors CT h caller)
          (active_mode, location))).
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
    eapply executing_with_frozen_incoming_dangerous_covered_by_old_or_active;
      eauto. }
  have Hhead_classify : forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (nested_frozen_call_head CT h caller callee caller_colors snapshots)
          .(frozen_snapshot_current_colors) (mode, location) ->
      (exists caller_mode,
        authority_mode_dangerous caller_mode /\
        In authority_flow_state caller_colors (caller_mode, location)) \/
      (exists snapshot_mode,
        authority_mode_dangerous snapshot_mode /\
        In authority_flow_state
          (frozen_caller_snapshot_current_color_union snapshots)
          (snapshot_mode, location)).
  { intros mode location Hmode Hcolor.
    change (In authority_flow_state
      (frozen_caller_authority_closure CT h callee seeds)
      (mode, location)) in Hcolor.
    destruct (Hclassify seeds mode location Hseeds_runtime Hseeds_closed Hmode
      Hcolor) as
      [[seed_mode [Hseed_mode Hseed]] |
       [active_mode [Hactive_mode Hactive]]].
    - unfold seeds, nested_frozen_call_entry_seeds in Hseed.
      inversion Hseed; subst.
      + destruct H as [Hcaller_color Hcaller_dangerous].
        left. exists seed_mode. split; assumption.
      + right. exists seed_mode. split; assumption.
    - left. exists active_mode. split; [exact Hactive_mode|].
      unfold caller_colors.
      eapply independent_active_authority_colors_in_executing. exact Hactive. }
  intros new_older Hnew source_mode source Hsource_mode Hsource Hsource_root.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_older|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  have Hlift_safe : forall exposure_mode target,
      authority_mode_dangerous exposure_mode ->
      In authority_flow_state
        (frozen_caller_authority_closure CT h callee
          old_older.(frozen_snapshot_current_resume_exposure))
        (exposure_mode, target) ->
      (forall old_mode,
        authority_mode_dangerous old_mode ->
        In authority_flow_state
          old_older.(frozen_snapshot_current_resume_exposure)
          (old_mode, target) ->
        ~ In Loc Z target) ->
      ~ In Loc Z target.
  { intros exposure_mode target Hexposure_mode Htarget Hold_safe Hprotected.
    destruct (Hclassify
      old_older.(frozen_snapshot_current_resume_exposure) exposure_mode target
      ((proj1 Hexposure) old_older Hold)
      ((proj1 (proj2 Hexposure)) old_older Hold) Hexposure_mode Htarget) as
      [[old_mode [Hold_mode Hold_target]] |
       [active_mode [Hactive_mode Hactive]]].
    - exact (Hold_safe old_mode Hold_mode Hold_target Hprotected).
    - eapply Hmain_separated; [exact Hactive_mode| |exact Hprotected].
      eapply independent_active_authority_colors_in_executing. exact Hactive. }
  destruct (Hhead_classify source_mode source Hsource_mode Hsource) as
    [[caller_mode [Hcaller_mode Hcaller_source]] |
     [snapshot_mode [Hsnapshot_mode Hsnapshot_source]]].
  - destruct (Hcompleted old_older caller_mode source Hold Hcaller_mode
      Hcaller_source Hsource_root) as
      [[entry_mode [Hentry_mode Hentry]] | Hsafe].
    + left. exists entry_mode. split; assumption.
    + right. intros exposure_mode target Hexposure_mode Htarget.
      eapply Hlift_safe; eauto.
  - destruct (frozen_snapshot_current_color_union_resume_safe Z snapshots
      old_older snapshot_mode source Hcovered Hnested Hjoins Hold
      Hsnapshot_mode Hsnapshot_source Hsource_root) as
      [[entry_mode [Hentry_mode Hentry]] | Hsafe].
    + left. exists entry_mode. split; assumption.
    + right. intros exposure_mode target Hexposure_mode Htarget.
      eapply Hlift_safe; eauto.
Qed.

(** Aggregate policy-entry head.  Ordinary tracked snapshots are first
    reduced to the policy-witness union by the lockstep coverage invariant;
    self and pairwise policy resume certificates then classify every source
    against the older witness being resumed. *)
Lemma private_nested_frozen_call_head_resume_safe_against_advanced_witnesses :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots witnesses mt x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_frozen_authority_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots h ->
    private_resume_witnesses_cover_snapshots Z witnesses snapshots ->
    private_resume_witness_stack_safe CT h Z
      (mk_watched_frame caller_authority sGamma rGamma) incoming witnesses ->
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
    forall new_older,
      List.In (Some new_older)
        (advance_frozen_caller_snapshots CT h callee witnesses) ->
      frozen_snapshot_resume_safe_against Z
        (private_nested_frozen_call_head CT h caller callee caller_colors
          snapshots witnesses) new_older.
Proof.
  intros CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots witnesses mt x method y args sGamma' vals ly cy runtime_mdef Ty
    Hfrozen Hcover
    (Hwitness_covered & Hwitness_runtime & Hwitness_dangerous &
      Hwitness_closed & Hwitness_roots & Hwitness_exposure &
      Hwitness_resume & Hwitness_joins & Hwitness_nested &
      Hwitness_completed & Hwitness_retain & Hwitness_phase)
    Htyping Hscope Hgety Hvalue Hbase Hfind Hargs caller caller_colors callee.
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
  have Hcaller_colors_runtime : authority_colors_runtime_mutable h
      caller_colors.
  { unfold caller_colors, caller.
    eapply executing_authority_colors_runtime_mutable; eauto. }
  have Hmain_separated := proj1 (proj2 (proj2 (proj2 Hmain))).
  set (sources := snapshots ++ witnesses).
  have Hsources_runtime : frozen_caller_snapshots_runtime_mutable h sources.
  { intros snapshot Hsnapshot. unfold sources in Hsnapshot.
    apply in_app_or in Hsnapshot. destruct Hsnapshot; eauto. }
  have Hsources_closed : frozen_caller_snapshots_closed CT h caller sources.
  { intros snapshot Hsnapshot. unfold sources in Hsnapshot.
    apply in_app_or in Hsnapshot. destruct Hsnapshot; eauto. }
  set (seeds := nested_frozen_call_entry_seeds caller_colors sources).
  have Hseeds_runtime : authority_colors_runtime_mutable h seeds.
  { intros mode location Hseed. unfold seeds,
      nested_frozen_call_entry_seeds in Hseed.
    inversion Hseed; subst.
    - destruct H as [Hcaller_color Hcaller_mode].
      eapply Hcaller_colors_runtime. exact Hcaller_color.
    - destruct H as [snapshot [Hsnapshot Hsnapshot_color]].
      eapply Hsources_runtime; eauto. }
  have Hseeds_closed : Included authority_flow_state
      (frozen_caller_authority_closure CT h caller seeds) seeds.
  { intros state [seed [Hseed Hpath]]. unfold seeds,
      nested_frozen_call_entry_seeds in *.
    inversion Hseed; subst.
    - destruct H as [Hcaller_seed Hseed_mode]. left. split.
      + unfold caller_colors in *.
        eapply executing_authority_color_set_frozen_closed.
        exists seed. split; assumption.
      + eapply frozen_caller_authority_connected_preserves_dangerous;
          eauto.
    - destruct H as [snapshot [Hsnapshot Hsnapshot_seed]].
      right. exists snapshot. split; [exact Hsnapshot|].
      eapply Hsources_closed; [exact Hsnapshot|].
      exists seed. split; [exact Hsnapshot_seed|exact Hpath]. }
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
        In authority_flow_state
          (independent_active_authority_colors CT h caller)
          (active_mode, location))).
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
    eapply executing_with_frozen_incoming_dangerous_covered_by_old_or_active;
      eauto. }
  have Hhead_classify : forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (private_nested_frozen_call_head CT h caller callee caller_colors
          snapshots witnesses).(frozen_snapshot_current_colors)
        (mode, location) ->
      (exists caller_mode,
        authority_mode_dangerous caller_mode /\
        In authority_flow_state caller_colors (caller_mode, location)) \/
      (exists source_mode,
        authority_mode_dangerous source_mode /\
        In authority_flow_state
          (frozen_caller_snapshot_current_color_union sources)
          (source_mode, location)).
  { intros mode location Hmode Hcolor.
    change (In authority_flow_state
      (frozen_caller_authority_closure CT h callee seeds)
      (mode, location)) in Hcolor.
    destruct (Hclassify seeds mode location Hseeds_runtime Hseeds_closed Hmode
      Hcolor) as
      [[seed_mode [Hseed_mode Hseed]] |
       [active_mode [Hactive_mode Hactive]]].
    - unfold seeds, nested_frozen_call_entry_seeds in Hseed.
      inversion Hseed; subst.
      + destruct H as [Hcaller_color Hcaller_dangerous].
        left. exists seed_mode. split; assumption.
      + right. exists seed_mode. split; assumption.
    - left. exists active_mode. split; [exact Hactive_mode|].
      unfold caller_colors.
      eapply independent_active_authority_colors_in_executing. exact Hactive. }
  intros new_older Hnew source_mode source Hsource_mode Hsource Hsource_root.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_older|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  have Hlift_safe : forall exposure_mode target,
      authority_mode_dangerous exposure_mode ->
      In authority_flow_state
        (frozen_caller_authority_closure CT h callee
          old_older.(frozen_snapshot_current_resume_exposure))
        (exposure_mode, target) ->
      (forall old_mode,
        authority_mode_dangerous old_mode ->
        In authority_flow_state
          old_older.(frozen_snapshot_current_resume_exposure)
          (old_mode, target) ->
        ~ In Loc Z target) ->
      ~ In Loc Z target.
  { intros exposure_mode target Hexposure_mode Htarget Hold_safe Hprotected.
    destruct (Hclassify
      old_older.(frozen_snapshot_current_resume_exposure) exposure_mode target
      ((proj1 Hwitness_exposure) old_older Hold)
      ((proj1 (proj2 Hwitness_exposure)) old_older Hold) Hexposure_mode
      Htarget) as
      [[old_mode [Hold_mode Hold_target]] |
       [active_mode [Hactive_mode Hactive]]].
    - exact (Hold_safe old_mode Hold_mode Hold_target Hprotected).
    - eapply Hmain_separated; [exact Hactive_mode| |exact Hprotected].
      eapply independent_active_authority_colors_in_executing. exact Hactive. }
  destruct (Hhead_classify source_mode source Hsource_mode Hsource) as
    [[caller_mode [Hcaller_mode Hcaller_source]] |
     [snapshot_mode [Hsnapshot_mode Hsnapshot_source]]].
  - destruct (Hwitness_completed old_older caller_mode source Hold
      Hcaller_mode Hcaller_source Hsource_root) as
      [[entry_mode [Hentry_mode Hentry]] | Hsafe].
    + left. exists entry_mode. split; assumption.
    + right. intros exposure_mode target Hexposure_mode Htarget.
      eapply Hlift_safe; eauto.
  - have Hpolicy_source : In authority_flow_state
        (frozen_caller_snapshot_current_color_union witnesses)
        (snapshot_mode, source).
    { unfold sources in Hsnapshot_source.
      destruct Hsnapshot_source as
        [source_snapshot [Hsource_snapshot Hsource_color]].
      apply in_app_or in Hsource_snapshot.
      destruct Hsource_snapshot as [Hordinary | Hpolicy].
      - eapply private_resume_witnesses_cover_snapshot_color_union;
          [exact Hcover|].
        exists source_snapshot. split; assumption.
      - exists source_snapshot. split; assumption. }
    destruct (frozen_snapshot_current_color_union_resume_safe Z witnesses
      old_older snapshot_mode source Hwitness_covered Hwitness_nested
      Hwitness_joins Hold Hsnapshot_mode Hpolicy_source Hsource_root) as
      [[entry_mode [Hentry_mode Hentry]] | Hsafe].
    + left. exists entry_mode. split; assumption.
    + right. intros exposure_mode target Hexposure_mode Htarget.
      eapply Hlift_safe; eauto.
Qed.

Lemma private_resume_witness_stack_safe_enter_safe_call :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots witnesses mt x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_frozen_authority_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots h ->
    private_resume_witnesses_cover_snapshots Z witnesses snapshots ->
    private_resume_witness_stack_safe CT h Z
      (mk_watched_frame caller_authority sGamma rGamma) incoming witnesses ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    wf_r_config CT
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) h ->
    let caller := mk_watched_frame caller_authority sGamma rGamma in
    let caller_colors := executing_authority_color_set CT h caller incoming in
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    private_resume_witness_stack_safe CT h Z callee caller_colors
      (Some (private_nested_frozen_call_head CT h caller callee caller_colors
        snapshots witnesses) ::
       advance_frozen_caller_snapshots CT h callee witnesses).
Proof.
  intros CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots witnesses mt x method y args sGamma' vals ly cy runtime_mdef Ty
    Hfrozen Hcover Hstack Htyping Hscope Hgety Hvalue Hbase Hfind Hargs
    Hcallee_wf caller caller_colors callee.
  pose proof Hfrozen as Hfrozen_copy.
  pose proof Hstack as Hstack_copy.
  destruct Hfrozen as
    [Hmain [Haligned [Hruntime [Hclosed [Hretain [Hdangerous [Havoid
      [Hroots [Hexposure [Hresume [Hjoins
        [Hentry_covered Hphase_covered]]]]]]]]]]]].
  destruct Hstack as
    (Hwitness_covered & Hwitness_runtime & Hwitness_dangerous &
      Hwitness_closed & Hwitness_roots & Hwitness_exposure &
      Hwitness_resume & Hwitness_joins & Hwitness_nested &
      Hwitness_completed & Hwitness_retain & Hwitness_phase).
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hsound : authority_context_sound h rGamma caller_authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
  have Hincoming_runtime : authority_colors_runtime_mutable h incoming :=
    proj1 (proj2 (proj2 Hmain)).
  have Hcaller_colors_runtime : authority_colors_runtime_mutable h
      caller_colors.
  { unfold caller_colors, caller.
    eapply executing_authority_colors_runtime_mutable; eauto. }
  have Hcaller_independent_separated : executing_authority_colors_separated
      CT h Z caller (Empty_set authority_flow_state).
  { intros mode location Hmode Hcolor Hprotected.
    eapply (proj1 (proj2 (proj2 (proj2 Hmain))));
      [exact Hmode| |exact Hprotected].
    eapply independent_active_authority_colors_in_executing. exact Hcolor. }
  have Hentry_phase := private_entry_witnesses_phase_wf CT h caller callee
    caller_colors snapshots witnesses Hwf Hcallee_wf Hcaller_colors_runtime
    Hruntime Hdangerous Hroots Hexposure Hwitness_runtime
    Hwitness_dangerous Hwitness_closed Hwitness_roots Hwitness_exposure.
  destruct Hentry_phase as
    [Hentry_runtime [Hentry_closed [Hentry_roots Hentry_exposure]]].
  have Htail_resume :=
    frozen_caller_snapshots_active_resume_safe_after_safe_call_entry_from_parts
      CT Z caller_authority sGamma mt rGamma h witnesses x method y args
      sGamma' vals ly cy runtime_mdef Ty Hwf Hsound Htyping Hscope Hgety
      Hvalue Hbase Hfind Hargs Hcaller_independent_separated
      Hwitness_exposure Hwitness_resume.
  have Htail_joins :=
    frozen_caller_snapshots_resume_joins_safe_after_safe_call_entry_from_parts
      CT P Z cutoff caller_authority sGamma rGamma h stack incoming witnesses
      mt x method y args sGamma' vals ly cy runtime_mdef Ty Hmain Htyping
      Hscope Hgety Hvalue Hbase Hfind Hargs Hwitness_runtime Hwitness_closed
      Hwitness_exposure Hwitness_resume Hwitness_joins.
  have Htail_nested :=
    frozen_caller_snapshots_nested_resume_safe_after_safe_call_entry_from_parts
      CT P Z cutoff caller_authority sGamma rGamma h stack incoming witnesses
      mt x method y args sGamma' vals ly cy runtime_mdef Ty Hmain Htyping
      Hscope Hgety Hvalue Hbase Hfind Hargs Hwitness_runtime Hwitness_closed
      Hwitness_exposure Hwitness_resume Hwitness_nested.
  have Htail_completed :=
    frozen_completed_colors_resume_safe_after_safe_call_entry_from_parts CT P
      Z cutoff caller_authority sGamma rGamma h stack incoming witnesses mt x
      method y args sGamma' vals ly cy runtime_mdef Ty Hmain Htyping Hscope
      Hgety Hvalue Hbase Hfind Hargs Hwitness_exposure Hwitness_completed.
  unfold private_resume_witness_stack_safe.
  refine (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))))).
  - exact (private_nested_frozen_call_head_builds_nested_covered CT h Z
      caller callee caller_colors snapshots witnesses Hwitness_covered).
  - exact Hentry_runtime.
  - intros snapshot mode location Hsnapshot Hcolor.
    simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
    + injection Heq as <-.
      unfold private_nested_frozen_call_head.
      eapply (nested_frozen_call_head_dangerous CT h caller callee
        caller_colors (snapshots ++ witnesses)).
      * intros old_snapshot old_mode old_location Hold Hstate.
        apply in_app_or in Hold. destruct Hold; eauto.
      * exact Hcolor.
    + eapply advance_frozen_caller_snapshots_dangerous; eauto.
  - exact Hentry_closed.
  - exact Hentry_roots.
  - exact Hentry_exposure.
  - unfold frozen_caller_snapshots_active_resume_safe.
    intros snapshot active_mode source Hsnapshot Hactive_mode Hactive Hroot.
    simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
    + right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
      injection Heq as <-.
      have Hhead :=
        nested_frozen_call_head_resume_roots_safe_at_safe_call_entry CT Z
          caller_authority sGamma mt rGamma h caller_colors
          (snapshots ++ witnesses) x method y args sGamma' vals ly cy
          runtime_mdef Ty Hwf Hsound Htyping Hscope Hgety Hvalue Hbase Hfind
          Hargs Hcaller_independent_separated.
      unfold private_nested_frozen_call_head.
      eapply Hhead.
      * simpl. left. reflexivity.
      * exact Hactive_mode.
      * exact Hactive.
      * exact Hroot.
      * exact Hexposure_mode.
      * exact Htarget.
      * exact Hprotected.
    + eapply Htail_resume; eauto.
  - intros snapshot source_mode source Hsnapshot Hsource_mode Hsource Hroot.
    simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
    + injection Heq as <-. left. exists source_mode. split; assumption.
    + eapply Htail_joins; eauto.
  - simpl. split.
    + eapply private_nested_frozen_call_head_resume_safe_against_advanced_witnesses;
        eauto.
    + exact Htail_nested.
  - intros snapshot source_mode source Hsnapshot Hsource_mode Hsource Hroot.
    simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
    + injection Heq as <-.
      destruct (executing_authority_colors_enter_call_covered CT
        caller_authority sGamma mt rGamma h x method y args sGamma' vals ly
        cy runtime_mdef Ty incoming Hwf Hsound Hincoming_runtime Htyping
        Hscope Hgety Hvalue Hbase Hfind Hargs source_mode source Hsource_mode
        Hsource) as [caller_mode [Hcaller_mode Hcaller_source]].
      left. exists caller_mode. split; [exact Hcaller_mode|].
      unfold private_nested_frozen_call_head, nested_frozen_call_head. simpl.
      apply frozen_caller_authority_closure_contains.
      left. split; assumption.
    + eapply Htail_completed; eauto.
  - intros snapshot Hsnapshot. simpl in Hsnapshot.
    destruct Hsnapshot as [Heq | Htail].
    + injection Heq as <-. unfold private_nested_frozen_call_head.
      apply nested_frozen_call_head_retains_entry.
    + eapply advance_frozen_caller_snapshots_retain_entry; eauto.
  - intros snapshot mode location Hsnapshot Hmode Hincoming.
    simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
    + injection Heq as <-.
      unfold private_nested_frozen_call_head, nested_frozen_call_head in *.
      simpl in *. apply frozen_caller_authority_closure_contains.
      left. split; assumption.
    + eapply advance_frozen_caller_snapshots_cover_phase_incoming; eauto.
Qed.

Lemma private_target_witness_stack_structural_enter_call :
  forall CT P Z cutoff caller stack incoming h callee caller_colors snapshots
    witnesses,
    principled_frozen_authority_history_state CT P Z cutoff caller stack
      incoming snapshots h ->
    wf_r_config CT callee.(frame_senv) callee.(frame_renv) h ->
    authority_colors_runtime_mutable h caller_colors ->
    private_target_witness_stack_structural CT h caller witnesses ->
    private_target_witness_stack_structural CT h callee
      (Some (private_nested_target_call_head CT h caller callee caller_colors
        snapshots witnesses) ::
       advance_frozen_caller_snapshots CT h callee witnesses).
Proof.
  intros CT P Z cutoff caller stack incoming h callee caller_colors snapshots
    witnesses Hfrozen Hcallee_wf Hcaller_colors_runtime
    (Hwitness_covered & Hwitness_runtime & Hwitness_dangerous &
      Hwitness_closed & Hwitness_roots & Hwitness_exposure &
      Hwitness_retain & Hwitness_phase).
  destruct Hfrozen as
    [Hmain [Haligned [Hruntime [Hclosed [Hretain [Hdangerous [Havoid
      [Hroots [Hexposure [Hresume [Hjoins
        [Hentry_covered Hphase_covered]]]]]]]]]]]].
  have Hcaller_wf : wf_r_config CT caller.(frame_senv) caller.(frame_renv) h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hentry_phase := private_entry_witnesses_phase_wf CT h caller callee
    caller_colors snapshots witnesses Hcaller_wf Hcallee_wf
    Hcaller_colors_runtime Hruntime Hdangerous Hroots Hexposure
    Hwitness_runtime Hwitness_dangerous Hwitness_closed Hwitness_roots
    Hwitness_exposure.
  destruct Hentry_phase as
    [Hentry_runtime [Hentry_closed [Hentry_roots Hentry_exposure]]].
  unfold private_target_witness_stack_structural.
  refine (conj I (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  - intros snapshot Hsnapshot mode location Hcolor. simpl in Hsnapshot.
    destruct Hsnapshot as [Heq | Htail].
    + injection Heq as <-. unfold private_nested_target_call_head in Hcolor.
      simpl in Hcolor.
      eapply Hentry_runtime with
        (snapshot := private_nested_frozen_call_head CT h caller callee
          caller_colors snapshots witnesses).
      * simpl; left; reflexivity.
      * exact Hcolor.
    + eapply Hentry_runtime; [simpl; right; exact Htail|exact Hcolor].
  - intros snapshot mode location Hsnapshot Hcolor.
    simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
    + injection Heq as <-. unfold private_nested_target_call_head in Hcolor.
      simpl in Hcolor.
      eapply (nested_frozen_call_head_dangerous CT h caller callee
        caller_colors (snapshots ++ witnesses)).
      * intros old_snapshot old_mode old_location Hold Hstate.
        apply in_app_or in Hold. destruct Hold; eauto.
      * exact Hcolor.
    + eapply advance_frozen_caller_snapshots_dangerous; eauto.
  - intros snapshot Hsnapshot. simpl in Hsnapshot.
    destruct Hsnapshot as [Heq | Htail].
    + injection Heq as <-. unfold private_nested_target_call_head. simpl.
      apply (proj1 (frozen_caller_authority_closure_idempotent CT h callee
        (nested_frozen_call_entry_seeds caller_colors
          (snapshots ++ witnesses)))).
    + eapply Hentry_closed. simpl; right; exact Htail.
  - intros snapshot root Hsnapshot Hroot. simpl in Hsnapshot.
    destruct Hsnapshot as [Heq | Htail].
    + injection Heq as <-.
      unfold private_nested_target_call_head in Hroot. simpl in Hroot.
      unfold frame_rdm_root_set, typed_root in Hroot.
      destruct Hroot as [variable [T [Htype [Hvalue Hrdm]]]].
      exact (wf_config_value_dom CT caller.(frame_senv) caller.(frame_renv) h
        variable root Hcaller_wf Hvalue).
    + eapply Hentry_roots; [simpl; right; exact Htail|exact Hroot].
  - unfold private_nested_target_call_head. exact Hentry_exposure.
  - intros snapshot Hsnapshot. simpl in Hsnapshot.
    destruct Hsnapshot as [Heq | Htail].
    + injection Heq as <-. unfold private_nested_target_call_head. simpl.
      intros state Hstate. exact Hstate.
    + eapply advance_frozen_caller_snapshots_retain_entry; eauto.
  - intros snapshot mode location Hsnapshot Hmode Hincoming.
    simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
    + injection Heq as <-. unfold private_nested_target_call_head,
        nested_frozen_call_entry_seeds in *.
      simpl in *. apply frozen_caller_authority_closure_contains.
      left. split; assumption.
    + eapply advance_frozen_caller_snapshots_cover_phase_incoming; eauto.
Qed.

Lemma nested_frozen_call_head_completed_safe_at_safe_call_entry :
  forall CT Z caller_authority sGamma mt rGamma h incoming snapshots
    x method y args sGamma' vals ly cy runtime_mdef Ty,
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
    let caller := mk_watched_frame caller_authority sGamma rGamma in
    let caller_colors := executing_authority_color_set CT h caller incoming in
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h callee caller_colors)
      [Some (nested_frozen_call_head CT h caller callee caller_colors
        snapshots)].
Proof.
  intros CT Z caller_authority sGamma mt rGamma h incoming snapshots x
    method y args sGamma' vals ly cy runtime_mdef Ty Hwf Hsound
    Hincoming_runtime Htyping Hscope Hgety Hvalue Hbase Hfind Hargs caller
    caller_colors callee snapshot source_mode source Hsnapshot Hsource_mode
    Hsource Hroot.
  simpl in Hsnapshot. destruct Hsnapshot as [Heq | Hbad]; [|contradiction].
  injection Heq as <-. simpl in *.
  destruct (executing_authority_colors_enter_call_covered CT
    caller_authority sGamma mt rGamma h x method y args sGamma' vals ly cy
    runtime_mdef Ty incoming Hwf Hsound Hincoming_runtime Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs source_mode source Hsource_mode Hsource) as
    [caller_mode [Hcaller_mode Hcaller_source]].
  left. exists caller_mode. split; [exact Hcaller_mode|].
  apply frozen_caller_authority_closure_contains.
  left. split; assumption.
Qed.

Lemma private_resume_witnesses_nested_resume_safe_enter_nested :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    witnesses snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty,
    private_frozen_statement_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    private_resume_witnesses_phase_wf CT h
      (mk_watched_frame caller_authority sGamma rGamma) witnesses snapshots ->
    private_resume_witnesses_roots_safe CT h Z
      (mk_watched_frame caller_authority sGamma rGamma) witnesses snapshots ->
    private_resume_witnesses_nested_resume_safe Z witnesses snapshots ->
    let caller := mk_watched_frame caller_authority sGamma rGamma in
    let caller_colors := executing_authority_color_set CT h caller incoming in
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    private_resume_witnesses_nested_resume_safe Z
      (Some (nested_frozen_call_head CT h caller callee caller_colors
        snapshots) ::
       advance_frozen_caller_snapshots CT h callee witnesses)
      (None :: advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    witnesses snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty
    Hprivate Htyping Hscope Hgety Hvalue Hbase Hfind Hargs Hphase Hroots
    Hnested_policy caller caller_colors callee. simpl. split.
  - destruct Hprivate as
      [Hfrozen [Hactive_justified [Hbefore
        [Hcovered [Hnested Hcompleted]]]]].
    split.
    + eapply
        nested_frozen_call_head_resume_safe_against_advanced_tail_at_safe_call_entry;
        eauto.
    + eapply frozen_caller_snapshots_nested_resume_safe_after_safe_call_entry;
        eauto.
  - have Hmain := proj1 (proj1 Hprivate).
    eapply private_resume_witnesses_nested_resume_safe_after_safe_call_entry;
      eauto.
Qed.

Lemma private_resume_witnesses_completed_safe_enter_nested :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    witnesses snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty,
    private_frozen_statement_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    private_resume_witnesses_phase_wf CT h
      (mk_watched_frame caller_authority sGamma rGamma) witnesses snapshots ->
    private_resume_witnesses_completed_safe CT h Z
      (mk_watched_frame caller_authority sGamma rGamma) incoming witnesses
      snapshots ->
    let caller := mk_watched_frame caller_authority sGamma rGamma in
    let caller_colors := executing_authority_color_set CT h caller incoming in
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    private_resume_witnesses_completed_safe CT h Z callee caller_colors
      (Some (nested_frozen_call_head CT h caller callee caller_colors
        snapshots) ::
       advance_frozen_caller_snapshots CT h callee witnesses)
      (None :: advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    witnesses snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty
    Hprivate Htyping Hscope Hgety Hvalue Hbase Hfind Hargs Hphase Hcompleted
    caller caller_colors callee. simpl. split.
  - intros snapshot source_mode source Hsnapshot Hsource_mode Hsource Hroot.
    simpl in Hsnapshot. destruct Hsnapshot as [Hhead | Htail].
    + injection Hhead as <-.
      have Hmain := proj1 (proj1 Hprivate).
      have Hwf : wf_r_config CT sGamma rGamma h :=
        proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
      have Hsound : authority_context_sound h rGamma caller_authority :=
        proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
      have Hincoming_runtime : authority_colors_runtime_mutable h incoming :=
        proj1 (proj2 (proj2 Hmain)).
      eapply nested_frozen_call_head_completed_safe_at_safe_call_entry with
        (snapshots := snapshots) (x := x) (method := method) (y := y)
        (args := args) (sGamma' := sGamma') (vals := vals) (ly := ly)
        (cy := cy) (runtime_mdef := runtime_mdef) (Ty := Ty); eauto.
      simpl. left. reflexivity.
    + have Hfrozen := proj1 Hprivate.
      have Htail_completed :=
        frozen_completed_colors_resume_safe_after_safe_call_entry CT P Z
          cutoff caller_authority sGamma rGamma h stack incoming snapshots mt
          x method y args sGamma' vals ly cy runtime_mdef Ty Hfrozen Htyping
          Hscope Hgety Hvalue Hbase Hfind Hargs
          (proj2 (proj2 (proj2 (proj2 (proj2 Hprivate))))).
      eapply Htail_completed; eauto.
  - have Hmain := proj1 (proj1 Hprivate).
    eapply private_resume_witnesses_completed_safe_after_safe_call_entry;
      eauto.
Qed.

Lemma private_resume_witnesses_cover_snapshots_after_active_descent :
  forall CT h Z authority old_senv old_renv new_senv new_renv witnesses
    snapshots,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    private_resume_witnesses_cover_snapshots Z witnesses snapshots ->
    private_resume_witnesses_phase_wf CT h
      (mk_watched_frame authority old_senv old_renv) witnesses snapshots ->
    frozen_caller_snapshots_nested_covered snapshots ->
    frozen_caller_snapshots_nested_resume_safe Z snapshots ->
    private_resume_witnesses_cover_snapshots Z
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) witnesses)
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) snapshots).
Proof.
  intros CT h Z authority old_senv old_renv new_senv new_renv witnesses
    snapshots Hdescend Hcover Hphase Hnested_covered Hnested_safe.
  eapply private_resume_witnesses_cover_snapshots_after_advance.
  exact Hcover.
Qed.

Lemma private_resume_witnesses_phase_wf_after_advance_from_any_active :
  forall CT h old_active new_active witnesses snapshots,
    wf_r_config CT new_active.(frame_senv) new_active.(frame_renv) h ->
    private_resume_witnesses_phase_wf CT h old_active witnesses snapshots ->
    private_resume_witnesses_phase_wf CT h new_active
      (advance_frozen_caller_snapshots CT h new_active witnesses)
      (advance_frozen_caller_snapshots CT h new_active snapshots).
Proof.
  intros CT h old_active new_active witnesses.
  induction witnesses as [|witness witness_tail IH]; intros snapshots Hwf
    Hphase; destruct snapshots as [|snapshot snapshot_tail]; simpl in *;
    try contradiction; [exact I|].
  destruct Hphase as [Hruntime [Hclosed [Hroots [Hexposure Htail]]]].
  split.
  - change (frozen_caller_snapshots_runtime_mutable h
      (advance_frozen_caller_snapshots CT h new_active
        (witness :: snapshot_tail))).
    eapply advance_frozen_caller_snapshots_runtime_mutable; eauto.
  - split.
    + change (frozen_caller_snapshots_closed CT h new_active
        (advance_frozen_caller_snapshots CT h new_active
          (witness :: snapshot_tail))).
      apply advance_frozen_caller_snapshots_closed.
    + split.
      * change (frozen_caller_snapshots_resume_roots_in_heap h
          (advance_frozen_caller_snapshots CT h new_active
            (witness :: snapshot_tail))).
        eapply advance_frozen_caller_snapshots_resume_roots_in_heap; eauto.
      * split.
        -- change (frozen_caller_snapshots_resume_exposures_wf CT h new_active
          (advance_frozen_caller_snapshots CT h new_active
            (witness :: snapshot_tail))).
           eapply
             advance_frozen_caller_snapshots_resume_exposures_wf_from_any_active;
            eauto.
        -- eapply IH; eauto.
Qed.

(** Active descent cannot introduce an independent active color, and every
    advanced resume exposure reflects through the old frozen closure.  Thus
    a resume-root certificate transports pointwise to the advanced list. *)
Lemma frozen_caller_snapshots_resume_roots_safe_after_active_descent :
  forall CT h Z authority old_senv old_renv new_senv new_renv snapshots,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame authority new_senv new_renv))
      (phase_frame_capability_set CT h
        (mk_watched_frame authority old_senv old_renv)) ->
    frozen_caller_snapshots_closed CT h
      (mk_watched_frame authority old_senv old_renv) snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame authority old_senv old_renv) snapshots ->
    frozen_caller_snapshots_resume_roots_safe CT h Z
      (mk_watched_frame authority old_senv old_renv) snapshots ->
    frozen_caller_snapshots_resume_roots_safe CT h Z
      (mk_watched_frame authority new_senv new_renv)
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) snapshots).
Proof.
  intros CT h Z authority old_senv old_renv new_senv new_renv snapshots
    Hdescend Howned Hclosed Hexposure Hsafe new_snapshot active_mode source
    exposure_mode target Hnew Hactive_mode Hactive Hroot Hexposure_mode
    Htarget.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  have Hold_active : In authority_flow_state
      (independent_active_authority_colors CT h
        (mk_watched_frame authority old_senv old_renv))
      (active_mode, source).
  { unfold independent_active_authority_colors in *.
    eapply executing_authority_colors_after_active_descent_included; eauto. }
  have Hold_target : In authority_flow_state
      old_snapshot.(frozen_snapshot_current_resume_exposure)
      (exposure_mode, target).
  { eapply (proj1 (proj2 Hexposure)); [exact Hold|].
    destruct Htarget as [seed [Hseed Hpath]].
    exists seed. split; [exact Hseed|].
    eapply frozen_caller_connected_after_descent_reflects; eauto. }
  exact (Hsafe old_snapshot active_mode source exposure_mode target Hold
    Hactive_mode Hold_active Hroot Hexposure_mode Hold_target).
Qed.

Lemma private_resume_witnesses_roots_safe_after_active_descent :
  forall CT h Z authority old_senv old_renv new_senv new_renv witnesses
    snapshots,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame authority new_senv new_renv))
      (phase_frame_capability_set CT h
        (mk_watched_frame authority old_senv old_renv)) ->
    private_resume_witnesses_phase_wf CT h
      (mk_watched_frame authority old_senv old_renv) witnesses snapshots ->
    private_resume_witnesses_roots_safe CT h Z
      (mk_watched_frame authority old_senv old_renv) witnesses snapshots ->
    private_resume_witnesses_roots_safe CT h Z
      (mk_watched_frame authority new_senv new_renv)
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) witnesses)
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) snapshots).
Proof.
  intros CT h Z authority old_senv old_renv new_senv new_renv witnesses.
  induction witnesses as [|witness witness_tail IH]; intros snapshots Hdescend
    Howned Hphase Hsafe; destruct snapshots as [|snapshot snapshot_tail];
    simpl in *; try contradiction; [exact I|].
  destruct Hphase as
    [Hruntime [Hclosed [Hphase_roots [Hexposure Htail_phase]]]].
  destruct Hsafe as [Hhead_safe Htail_safe]. split.
  - change (frozen_caller_snapshots_active_resume_safe CT h Z
      (mk_watched_frame authority new_senv new_renv)
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv)
        (witness :: snapshot_tail))).
    unfold frozen_caller_snapshots_active_resume_safe in *.
    eapply frozen_completed_colors_resume_safe_after_active_descent; eauto.
  - eapply IH; eauto.
Qed.

Lemma private_resume_witnesses_nested_resume_safe_after_active_descent :
  forall CT h Z authority old_senv old_renv new_senv new_renv witnesses
    snapshots,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    private_resume_witnesses_phase_wf CT h
      (mk_watched_frame authority old_senv old_renv) witnesses snapshots ->
    private_resume_witnesses_nested_resume_safe Z witnesses snapshots ->
    private_resume_witnesses_nested_resume_safe Z
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) witnesses)
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) snapshots).
Proof.
  intros CT h Z authority old_senv old_renv new_senv new_renv witnesses.
  induction witnesses as [|witness witness_tail IH];
    intros snapshots Hdescend Hphase Hsafe;
    destruct snapshots as [|snapshot snapshot_tail]; simpl in *;
    try contradiction; [exact I|].
  destruct Hphase as
    [Hruntime [Hclosed [Hroots [Hexposure Htail_phase]]]].
  destruct Hsafe as [Hhead_safe Htail_safe]. split.
  - change (frozen_caller_snapshots_nested_resume_safe Z
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv)
        (witness :: snapshot_tail))).
    eapply frozen_caller_snapshots_nested_resume_safe_after_active_descent;
      eauto.
    exact (proj1 (proj2 Hexposure)).
  - eapply IH; eauto.
Qed.

Lemma private_resume_witnesses_completed_safe_after_active_descent :
  forall CT h Z authority old_senv old_renv new_senv new_renv incoming
    witnesses snapshots,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame authority new_senv new_renv))
      (phase_frame_capability_set CT h
        (mk_watched_frame authority old_senv old_renv)) ->
    private_resume_witnesses_phase_wf CT h
      (mk_watched_frame authority old_senv old_renv) witnesses snapshots ->
    private_resume_witnesses_completed_safe CT h Z
      (mk_watched_frame authority old_senv old_renv) incoming witnesses
      snapshots ->
    private_resume_witnesses_completed_safe CT h Z
      (mk_watched_frame authority new_senv new_renv) incoming
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) witnesses)
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) snapshots).
Proof.
  intros CT h Z authority old_senv old_renv new_senv new_renv incoming
    witnesses. induction witnesses as [|witness witness_tail IH];
    intros snapshots Hdescend Howned Hphase Hsafe;
    destruct snapshots as [|snapshot snapshot_tail]; simpl in *;
    try contradiction; [exact I|].
  destruct Hphase as
    [Hruntime [Hclosed [Hroots [Hexposure Htail_phase]]]].
  destruct Hsafe as [Hhead_safe Htail_safe]. split.
  - change (frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h
        (mk_watched_frame authority new_senv new_renv) incoming)
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv)
        (witness :: snapshot_tail))).
    eapply frozen_completed_colors_resume_safe_after_active_descent; eauto.
  - eapply IH; eauto.
Qed.

Lemma private_resume_witness_stack_safe_after_active_descent :
  forall CT h Z authority old_senv old_renv new_senv new_renv incoming
    witnesses,
    wf_r_config CT new_senv new_renv h ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame authority new_senv new_renv))
      (phase_frame_capability_set CT h
        (mk_watched_frame authority old_senv old_renv)) ->
    private_resume_witness_stack_safe CT h Z
      (mk_watched_frame authority old_senv old_renv) incoming witnesses ->
    private_resume_witness_stack_safe CT h Z
      (mk_watched_frame authority new_senv new_renv) incoming
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) witnesses).
Proof.
  intros CT h Z authority old_senv old_renv new_senv new_renv incoming
    witnesses Hwf Hdescend Howned
    (Hcovered & Hruntime & Hdangerous & Hclosed & Hroots & Hexposure & Hroots_safe &
      Hjoins & Hnested & Hcompleted & Hretain & Hphase).
  unfold private_resume_witness_stack_safe.
  refine (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ (conj _ _))))))))).
  - apply advance_frozen_caller_snapshots_nested_covered. exact Hcovered.
  - eapply advance_frozen_caller_snapshots_runtime_mutable; eauto.
  - eapply advance_frozen_caller_snapshots_dangerous. exact Hdangerous.
  - apply advance_frozen_caller_snapshots_closed.
  - eapply advance_frozen_caller_snapshots_resume_roots_in_heap; eauto.
  - eapply advance_frozen_caller_snapshots_resume_exposures_wf_from_any_active;
      eauto.
  - unfold frozen_caller_snapshots_active_resume_safe in *.
    eapply frozen_completed_colors_resume_safe_after_active_descent; eauto.
  - eapply frozen_caller_snapshots_resume_joins_safe_after_active_descent;
      eauto.
  - eapply frozen_caller_snapshots_nested_resume_safe_after_active_descent;
      eauto. exact (proj1 (proj2 Hexposure)).
  - split.
    + eapply frozen_completed_colors_resume_safe_after_active_descent; eauto.
    + split.
      * eapply advance_frozen_caller_snapshots_retain_entry; eauto.
      * eapply advance_frozen_caller_snapshots_cover_phase_incoming; eauto.
Qed.

Lemma frozen_caller_snapshots_resume_roots_safe_after_safe_field_update :
  forall CT h Z frame snapshots lx old field written,
    runtime_getObj h lx = Some old ->
    frozen_caller_snapshots_resume_exposures_wf CT h frame snapshots ->
    authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h frame) ->
    authority_safe_field_endpoints CT h frame lx written ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h frame)
        (active_mode, location) ->
      ~ In Loc Z location) ->
    frozen_caller_snapshots_resume_roots_safe CT h Z frame snapshots ->
    frozen_caller_snapshots_resume_roots_safe CT
      (update_field h lx field (Iot written)) Z frame
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame snapshots).
Proof.
  intros CT h Z frame snapshots lx old field written Hobj Hexposure
    Hactive_runtime Hendpoints Hactive_safe Hsafe new_snapshot active_mode
    source exposure_mode target Hnew Hactive_mode Hactive Hroot
    Hexposure_mode Htarget.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  destruct (executing_authority_colors_after_safe_field_update_covered CT h
    frame (Empty_set authority_flow_state) lx old field written Hobj
    Hactive_runtime Hendpoints active_mode source Hactive_mode Hactive) as
    [old_active_mode [Hold_active_mode Hold_active]].
  destruct Htarget as [seed [Hseed Hpath]].
  have Hseed_covered : frozen_authority_state_covered_by_old_or_active
      old_snapshot.(frozen_snapshot_current_resume_exposure)
      (independent_active_authority_colors CT h frame) seed.
  { intros Hseed_mode. left. exists (fst seed). split.
    - exact Hseed_mode.
    - destruct seed. exact Hseed. }
  have Htarget_covered :=
    frozen_caller_connected_after_safe_field_update_covered_by_old_or_active
      CT h frame old_snapshot.(frozen_snapshot_current_resume_exposure)
      lx old field written seed (exposure_mode, target) Hobj
      ((proj1 Hexposure) old_snapshot Hold)
      ((proj1 (proj2 Hexposure)) old_snapshot Hold) Hactive_runtime
      Hendpoints Hseed_covered Hpath Hexposure_mode.
  destruct Htarget_covered as
    [[old_exposure_mode [Hold_exposure_mode Hold_target]] |
     [old_target_mode [Hold_target_mode Hold_target]]].
  - exact (Hsafe old_snapshot old_active_mode source old_exposure_mode target
      Hold Hold_active_mode Hold_active Hroot Hold_exposure_mode Hold_target).
  - eapply Hactive_safe; eauto.
Qed.

Lemma private_resume_witnesses_roots_safe_after_safe_field_update :
  forall CT h Z frame witnesses snapshots lx old field written,
    runtime_getObj h lx = Some old ->
    private_resume_witnesses_phase_wf CT h frame witnesses snapshots ->
    authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h frame) ->
    authority_safe_field_endpoints CT h frame lx written ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h frame)
        (active_mode, location) ->
      ~ In Loc Z location) ->
    private_resume_witnesses_roots_safe CT h Z frame witnesses snapshots ->
    private_resume_witnesses_roots_safe CT
      (update_field h lx field (Iot written)) Z frame
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame witnesses)
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame snapshots).
Proof.
  intros CT h Z frame witnesses. induction witnesses as
    [|witness witness_tail IH]; intros snapshots lx old field written Hobj
    Hphase Hactive_runtime Hendpoints Hactive_safe Hsafe;
    destruct snapshots as [|snapshot snapshot_tail]; simpl in *;
    try contradiction; [exact I|].
  destruct Hphase as
    [Hruntime [Hclosed [Hphase_roots [Hexposure Htail_phase]]]].
  destruct Hsafe as [Hhead_safe Htail_safe]. split.
  - change (frozen_caller_snapshots_active_resume_safe CT
      (update_field h lx field (Iot written)) Z frame
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame
        (witness :: snapshot_tail))).
    unfold frozen_caller_snapshots_active_resume_safe in *.
    eapply frozen_completed_colors_resume_safe_after_safe_field_update;
      eauto.
  - eapply IH; eauto.
Qed.

Lemma frozen_caller_snapshots_nested_resume_safe_after_safe_field_update_entry :
  forall CT h Z frame snapshots lx old field written,
    runtime_getObj h lx = Some old ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_closed CT h frame snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h frame snapshots ->
    authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h frame) ->
    authority_safe_field_endpoints CT h frame lx written ->
    frozen_caller_snapshots_nested_resume_safe Z snapshots ->
    frozen_caller_snapshots_active_resume_safe CT h Z frame snapshots ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h frame)
        (active_mode, location) ->
      ~ In Loc Z location) ->
    frozen_caller_snapshots_nested_resume_safe Z
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame snapshots).
Proof.
  intros CT h Z frame snapshots lx old field written Hobj Hruntime Hclosed
    Hexposure Hactive_runtime Hendpoints Hnested Hresume Hactive_safe.
  eapply
    frozen_caller_snapshots_nested_resume_safe_after_classified_advance_entry
    with (exceptional := independent_active_authority_colors CT h frame).
  - exact Hnested.
  - unfold frozen_caller_snapshots_active_resume_safe in Hresume.
    exact Hresume.
  - exact Hactive_safe.
  - intros snapshot older mode location Hsnapshot _ Hmode
      [seed [Hseed Hpath]] _.
    destruct seed as [seed_mode seed_location].
    have Hseed_covered : frozen_authority_state_covered_by_old_or_active
        snapshot.(frozen_snapshot_current_colors)
        (independent_active_authority_colors CT h frame)
        (seed_mode, seed_location).
    { intros Hseed_mode. left. exists seed_mode. split; assumption. }
    have Hcovered :=
      frozen_caller_connected_after_safe_field_update_covered_by_old_or_active
        CT h frame snapshot.(frozen_snapshot_current_colors) lx old field
        written (seed_mode, seed_location) (mode, location) Hobj
        (Hruntime snapshot Hsnapshot) (Hclosed snapshot Hsnapshot)
        Hactive_runtime Hendpoints Hseed_covered Hpath.
    exact (Hcovered Hmode).
  - intros snapshot mode location Hsnapshot Hmode [seed [Hseed Hpath]] _.
    destruct seed as [seed_mode seed_location].
    have Hseed_covered : frozen_authority_state_covered_by_old_or_active
        snapshot.(frozen_snapshot_current_resume_exposure)
        (independent_active_authority_colors CT h frame)
        (seed_mode, seed_location).
    { intros Hseed_mode. left. exists seed_mode. split; assumption. }
    have Hcovered :=
      frozen_caller_connected_after_safe_field_update_covered_by_old_or_active
        CT h frame snapshot.(frozen_snapshot_current_resume_exposure)
        lx old field written (seed_mode, seed_location) (mode, location) Hobj
        ((proj1 Hexposure) snapshot Hsnapshot)
        ((proj1 (proj2 Hexposure)) snapshot Hsnapshot)
        Hactive_runtime Hendpoints Hseed_covered Hpath.
    exact (Hcovered Hmode).
Qed.

Lemma private_resume_witnesses_nested_resume_safe_after_safe_field_update :
  forall CT h Z frame witnesses snapshots lx old field written,
    runtime_getObj h lx = Some old ->
    private_resume_witnesses_phase_wf CT h frame witnesses snapshots ->
    authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h frame) ->
    authority_safe_field_endpoints CT h frame lx written ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h frame)
        (active_mode, location) ->
      ~ In Loc Z location) ->
    private_resume_witnesses_roots_safe CT h Z frame witnesses snapshots ->
    private_resume_witnesses_nested_resume_safe Z witnesses snapshots ->
    private_resume_witnesses_nested_resume_safe Z
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame witnesses)
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame snapshots).
Proof.
  intros CT h Z frame witnesses. induction witnesses as
    [|witness witness_tail IH]; intros snapshots lx old field written Hobj
    Hphase Hactive_runtime Hendpoints Hactive_safe Hroots_safe Hnested;
    destruct snapshots as [|snapshot snapshot_tail]; simpl in *;
    try contradiction; [exact I|].
  destruct Hphase as
    [Hruntime [Hclosed [Hphase_roots [Hexposure Htail_phase]]]].
  destruct Hroots_safe as [Hhead_roots_safe Htail_roots_safe].
  destruct Hnested as [Hhead_nested Htail_nested]. split.
  - change (frozen_caller_snapshots_nested_resume_safe Z
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame
        (witness :: snapshot_tail))).
    eapply
      frozen_caller_snapshots_nested_resume_safe_after_safe_field_update_entry;
      eauto.
  - eapply IH; eauto.
Qed.

Lemma private_resume_witnesses_completed_safe_after_safe_field_update :
  forall CT h Z frame incoming witnesses snapshots lx old field written,
    runtime_getObj h lx = Some old ->
    authority_colors_runtime_mutable h
      (executing_authority_color_set CT h frame incoming) ->
    private_resume_witnesses_phase_wf CT h frame witnesses snapshots ->
    authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h frame) ->
    authority_safe_field_endpoints CT h frame lx written ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h frame)
        (active_mode, location) ->
      ~ In Loc Z location) ->
    private_resume_witnesses_completed_safe CT h Z frame incoming witnesses
      snapshots ->
    private_resume_witnesses_completed_safe CT
      (update_field h lx field (Iot written)) Z frame incoming
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame witnesses)
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame snapshots).
Proof.
  intros CT h Z frame incoming witnesses. induction witnesses as
    [|witness witness_tail IH]; intros snapshots lx old field written Hobj
    Hcompleted_runtime Hphase Hactive_runtime Hendpoints Hactive_safe
    Hcompleted; destruct snapshots as [|snapshot snapshot_tail]; simpl in *;
    try contradiction; [exact I|].
  destruct Hphase as
    [Hruntime [Hclosed [Hphase_roots [Hexposure Htail_phase]]]].
  destruct Hcompleted as [Hhead_completed Htail_completed]. split.
  - change (frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT
        (update_field h lx field (Iot written)) frame incoming)
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame
        (witness :: snapshot_tail))).
    eapply frozen_completed_colors_resume_safe_after_safe_field_update;
      eauto.
  - eapply IH; eauto.
Qed.

(** Advancing a witness rebuilds both frozen closures in the new heap.  The
    only old-heap facts required are runtime mutability and the immutable
    dangerous/entry/root metadata; equality of runtime qualifiers transports
    the two heap-sensitive premises. *)
Lemma advance_resume_exposures_wf_from_runtime_equivalent_heap :
  forall CT old_h new_h old_active new_active snapshots,
    (forall location, location < dom old_h ->
      r_muttype new_h location = r_muttype old_h location) ->
    wf_r_config CT new_active.(frame_senv) new_active.(frame_renv) new_h ->
    frozen_caller_snapshots_resume_roots_in_heap old_h snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT old_h old_active
      snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT new_h new_active
      (advance_frozen_caller_snapshots CT new_h new_active snapshots).
Proof.
  intros CT old_h new_h old_active new_active snapshots Hruntimes Hwf
    Hroots_in_heap [Hruntime [_ [Hdangerous [Hentry Hroots]]]].
  repeat split.
  - intros snapshot Hsnapshot.
    unfold advance_frozen_caller_snapshots in Hsnapshot.
    apply in_map_iff in Hsnapshot.
    destruct Hsnapshot as [slot [Heq Hslot]].
    destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as Heq. subst snapshot. simpl.
    eapply advance_frozen_caller_snapshot_runtime_mutable; [exact Hwf|].
    intros mode location Hcolor.
    have Hold_runtime := Hruntime old_snapshot Hslot mode location Hcolor.
    have Hlocation : location < dom old_h :=
      r_muttype_some_dom old_h location Mut_r Hold_runtime.
    rewrite Hruntimes; assumption.
  - intros snapshot Hsnapshot.
    unfold advance_frozen_caller_snapshots in Hsnapshot.
    apply in_map_iff in Hsnapshot.
    destruct Hsnapshot as [slot [Heq Hslot]].
    destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as Heq. subst snapshot. simpl.
    apply (proj1 (frozen_caller_authority_closure_idempotent CT new_h
      new_active old_snapshot.(frozen_snapshot_current_resume_exposure))).
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
    exact (frozen_caller_authority_connected_preserves_dangerous CT new_h
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
    rewrite <- Hruntimes; [exact Hroot_runtime|].
    eapply Hroots_in_heap; eauto.
Qed.

Lemma private_target_witness_stack_structural_after_runtime_equivalent_heap :
  forall CT old_h new_h old_active new_active witnesses,
    (forall location, location < dom old_h ->
      r_muttype new_h location = r_muttype old_h location) ->
    dom old_h <= dom new_h ->
    wf_r_config CT new_active.(frame_senv) new_active.(frame_renv) new_h ->
    private_target_witness_stack_structural CT old_h old_active witnesses ->
    private_target_witness_stack_structural CT new_h new_active
      (advance_frozen_caller_snapshots CT new_h new_active witnesses).
Proof.
  intros CT old_h new_h old_active new_active witnesses Hruntimes Hdom Hwf
    (_ & Hruntime & Hdangerous & Hclosed & Hroots & Hexposure &
      Hretain & Hphase).
  have Hruntime_new : frozen_caller_snapshots_runtime_mutable new_h witnesses.
  { intros snapshot Hsnapshot mode location Hcolor.
    have Hold := Hruntime snapshot Hsnapshot mode location Hcolor.
    have Hlocation := r_muttype_some_dom old_h location Mut_r Hold.
    rewrite Hruntimes; assumption. }
  have Hroots_new : frozen_caller_snapshots_resume_roots_in_heap new_h
      witnesses.
  { intros snapshot root Hsnapshot Hroot.
    have Hold : root < dom old_h by (eapply Hroots; eauto). lia. }
  unfold private_target_witness_stack_structural.
  refine (conj I (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  - eapply advance_frozen_caller_snapshots_runtime_mutable; eauto.
  - eapply advance_frozen_caller_snapshots_dangerous. exact Hdangerous.
  - apply advance_frozen_caller_snapshots_closed.
  - eapply advance_frozen_caller_snapshots_resume_roots_in_heap.
    exact Hroots_new.
  - eapply advance_resume_exposures_wf_from_runtime_equivalent_heap; eauto.
  - eapply advance_frozen_caller_snapshots_retain_entry. exact Hretain.
  - eapply advance_frozen_caller_snapshots_cover_phase_incoming. exact Hphase.
Qed.

Lemma private_resume_witness_stack_safe_after_safe_field_update :
  forall CT h Z frame incoming witnesses lx old field written,
    runtime_getObj h lx = Some old ->
    wf_r_config CT frame.(frame_senv) frame.(frame_renv)
      (update_field h lx field (Iot written)) ->
    authority_colors_runtime_mutable h
      (executing_authority_color_set CT h frame incoming) ->
    authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h frame) ->
    authority_safe_field_endpoints CT h frame lx written ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h frame)
        (active_mode, location) ->
      ~ In Loc Z location) ->
    private_resume_witness_stack_safe CT h Z frame incoming witnesses ->
    private_resume_witness_stack_safe CT
      (update_field h lx field (Iot written)) Z frame incoming
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame witnesses).
Proof.
  intros CT h Z frame incoming witnesses lx old field written Hobj Hpost_wf
    Hcompleted_runtime Hactive_runtime Hendpoints Hactive_safe
    (Hcovered & Hruntime & Hdangerous & Hclosed & Hroots & Hexposure & Hroots_safe &
      Hjoins & Hnested & Hcompleted & Hretain & Hphase).
  have Hruntime_new : frozen_caller_snapshots_runtime_mutable
      (update_field h lx field (Iot written)) witnesses.
  { intros snapshot Hsnapshot mode location Hcolor.
    rewrite r_muttype_update_field_preserve.
    eapply Hruntime; eauto. }
  have Hroots_new : frozen_caller_snapshots_resume_roots_in_heap
      (update_field h lx field (Iot written)) witnesses.
  { intros snapshot root Hsnapshot Hroot.
    rewrite update_field_length. eapply Hroots; eauto. }
  unfold private_resume_witness_stack_safe.
  refine (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ (conj _ _))))))))).
  - apply advance_frozen_caller_snapshots_nested_covered. exact Hcovered.
  - eapply advance_frozen_caller_snapshots_runtime_mutable; eauto.
  - eapply advance_frozen_caller_snapshots_dangerous. exact Hdangerous.
  - apply advance_frozen_caller_snapshots_closed.
  - eapply advance_frozen_caller_snapshots_resume_roots_in_heap. exact Hroots_new.
  - eapply advance_resume_exposures_wf_from_runtime_equivalent_heap with
      (old_active := frame) (new_active := frame).
    + intros. apply r_muttype_update_field_preserve.
    + exact Hpost_wf.
    + exact Hroots.
    + exact Hexposure.
  - unfold frozen_caller_snapshots_active_resume_safe in *.
    eapply frozen_completed_colors_resume_safe_after_safe_field_update; eauto.
  - eapply
      frozen_caller_snapshots_resume_joins_safe_after_safe_field_update_entry;
      eauto.
  - eapply
      frozen_caller_snapshots_nested_resume_safe_after_safe_field_update_entry;
      eauto.
  - split.
    + eapply frozen_completed_colors_resume_safe_after_safe_field_update; eauto.
    + split.
      * eapply advance_frozen_caller_snapshots_retain_entry; eauto.
      * eapply advance_frozen_caller_snapshots_cover_phase_incoming; eauto.
Qed.

Lemma private_resume_witnesses_phase_wf_after_runtime_equivalent_heap :
  forall CT old_h new_h old_active new_active witnesses snapshots,
    (forall location, location < dom old_h ->
      r_muttype new_h location = r_muttype old_h location) ->
    dom old_h <= dom new_h ->
    wf_r_config CT new_active.(frame_senv) new_active.(frame_renv) new_h ->
    private_resume_witnesses_phase_wf CT old_h old_active witnesses snapshots ->
    private_resume_witnesses_phase_wf CT new_h new_active
      (advance_frozen_caller_snapshots CT new_h new_active witnesses)
      (advance_frozen_caller_snapshots CT new_h new_active snapshots).
Proof.
  intros CT old_h new_h old_active new_active witnesses. induction witnesses as
    [|witness witness_tail IH]; intros snapshots Hruntimes Hdom Hwf Hphase;
    destruct snapshots as [|snapshot snapshot_tail]; simpl in *;
    try contradiction; [exact I|].
  destruct Hphase as
    [Hruntime [Hclosed [Hphase_roots [Hexposure Htail]]]]. split.
  - change (frozen_caller_snapshots_runtime_mutable new_h
      (advance_frozen_caller_snapshots CT new_h new_active
        (witness :: snapshot_tail))).
    eapply advance_frozen_caller_snapshots_runtime_mutable; [exact Hwf|].
    intros old_snapshot Hold mode location Hcolor.
    have Hold_runtime := Hruntime old_snapshot Hold mode location Hcolor.
    have Hlocation : location < dom old_h :=
      r_muttype_some_dom old_h location Mut_r Hold_runtime.
    rewrite Hruntimes; assumption.
  - split.
    + change (frozen_caller_snapshots_closed CT new_h new_active
        (advance_frozen_caller_snapshots CT new_h new_active
          (witness :: snapshot_tail))).
      apply advance_frozen_caller_snapshots_closed.
    + split.
      * change (frozen_caller_snapshots_resume_roots_in_heap new_h
          (advance_frozen_caller_snapshots CT new_h new_active
            (witness :: snapshot_tail))).
        intros new_snapshot root Hnew Hroot.
        unfold advance_frozen_caller_snapshots in Hnew.
        apply in_map_iff in Hnew.
        destruct Hnew as [old_slot [Heq Hold]].
        destruct old_slot as [old_snapshot|]; simpl in Heq;
          [|discriminate].
        injection Heq as <-. simpl in Hroot.
        have Hold_root : root < dom old_h.
        { eapply Hphase_roots; eauto. }
        lia.
      * split.
        -- change (frozen_caller_snapshots_resume_exposures_wf CT new_h
          new_active (advance_frozen_caller_snapshots CT new_h new_active
            (witness :: snapshot_tail))).
           eapply advance_resume_exposures_wf_from_runtime_equivalent_heap;
          eauto.
        -- eapply IH; eauto.
Qed.

Lemma private_resume_witnesses_cover_snapshots_after_safe_field_update :
  forall CT h Z frame witnesses snapshots lx old field written,
    runtime_getObj h lx = Some old ->
    private_resume_witnesses_cover_snapshots Z witnesses snapshots ->
    private_resume_witnesses_phase_wf CT h frame witnesses snapshots ->
    private_resume_witnesses_roots_safe CT h Z frame witnesses snapshots ->
    frozen_caller_snapshots_nested_covered snapshots ->
    frozen_caller_snapshots_nested_resume_safe Z snapshots ->
    authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h frame) ->
    authority_safe_field_endpoints CT h frame lx written ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h frame)
        (active_mode, location) ->
      ~ In Loc Z location) ->
    private_resume_witnesses_cover_snapshots Z
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame witnesses)
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame snapshots).
Proof.
  intros CT h Z frame witnesses snapshots lx old field written Hobj Hcover
    Hphase Hroots Hnested_covered Hnested_safe Hactive_runtime Hendpoints
    Hactive_safe.
  eapply private_resume_witnesses_cover_snapshots_after_advance.
  exact Hcover.
Qed.

Lemma frozen_caller_snapshots_resume_roots_safe_after_graph_reflection :
  forall CT old_h new_h Z frame snapshots,
    (forall location,
      frame_owned_location CT new_h frame location ->
      frame_owned_location CT old_h frame location) ->
    (forall left right,
      retained_mut_edge CT new_h left right ->
      retained_mut_edge CT old_h left right) ->
    (forall left right,
      mutable_edge CT new_h left right -> mutable_edge CT old_h left right) ->
    frozen_caller_snapshots_resume_exposures_wf CT old_h frame snapshots ->
    frozen_caller_snapshots_resume_roots_safe CT old_h Z frame snapshots ->
    frozen_caller_snapshots_resume_roots_safe CT new_h Z frame
      (advance_frozen_caller_snapshots CT new_h frame snapshots).
Proof.
  intros CT old_h new_h Z frame snapshots Howned Hretained Hmutable
    Hexposure Hsafe new_snapshot active_mode source exposure_mode target Hnew
    Hactive_mode Hactive Hroot Hexposure_mode Htarget.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  destruct (executing_authority_colors_after_graph_reflection_covered CT
    old_h new_h frame (Empty_set authority_flow_state) Howned Hretained
    Hmutable active_mode source Hactive_mode Hactive) as
    [old_active_mode [Hold_active_mode Hold_active]].
  have Hold_target : In authority_flow_state
      old_snapshot.(frozen_snapshot_current_resume_exposure)
      (exposure_mode, target).
  { eapply frozen_caller_closure_after_graph_reflection_included; eauto.
    exact ((proj1 (proj2 Hexposure)) old_snapshot Hold). }
  exact (Hsafe old_snapshot old_active_mode source exposure_mode target Hold
    Hold_active_mode Hold_active Hroot Hexposure_mode Hold_target).
Qed.

Lemma private_resume_witnesses_roots_safe_after_graph_reflection :
  forall CT old_h new_h Z frame witnesses snapshots,
    (forall location,
      frame_owned_location CT new_h frame location ->
      frame_owned_location CT old_h frame location) ->
    (forall left right,
      retained_mut_edge CT new_h left right ->
      retained_mut_edge CT old_h left right) ->
    (forall left right,
      mutable_edge CT new_h left right -> mutable_edge CT old_h left right) ->
    private_resume_witnesses_phase_wf CT old_h frame witnesses snapshots ->
    private_resume_witnesses_roots_safe CT old_h Z frame witnesses snapshots ->
    private_resume_witnesses_roots_safe CT new_h Z frame
      (advance_frozen_caller_snapshots CT new_h frame witnesses)
      (advance_frozen_caller_snapshots CT new_h frame snapshots).
Proof.
  intros CT old_h new_h Z frame witnesses. induction witnesses as
    [|witness witness_tail IH]; intros snapshots Howned Hretained Hmutable
    Hphase Hsafe; destruct snapshots as [|snapshot snapshot_tail];
    simpl in *; try contradiction; [exact I|].
  destruct Hphase as
    [Hruntime [Hclosed [Hphase_roots [Hexposure Htail_phase]]]].
  destruct Hsafe as [Hhead_safe Htail_safe]. split.
  - change (frozen_caller_snapshots_active_resume_safe CT new_h Z frame
      (advance_frozen_caller_snapshots CT new_h frame
        (witness :: snapshot_tail))).
    unfold frozen_caller_snapshots_active_resume_safe in *.
    eapply frozen_completed_colors_resume_safe_after_graph_reflection; eauto.
  - eapply IH; eauto.
Qed.

Lemma private_resume_witnesses_nested_resume_safe_after_graph_reflection :
  forall CT old_h new_h Z frame witnesses snapshots,
    (forall left right,
      retained_mut_edge CT new_h left right ->
      retained_mut_edge CT old_h left right) ->
    (forall left right,
      mutable_edge CT new_h left right -> mutable_edge CT old_h left right) ->
    private_resume_witnesses_phase_wf CT old_h frame witnesses snapshots ->
    private_resume_witnesses_nested_resume_safe Z witnesses snapshots ->
    private_resume_witnesses_nested_resume_safe Z
      (advance_frozen_caller_snapshots CT new_h frame witnesses)
      (advance_frozen_caller_snapshots CT new_h frame snapshots).
Proof.
  intros CT old_h new_h Z frame witnesses. induction witnesses as
    [|witness witness_tail IH]; intros snapshots Hretained Hmutable Hphase
    Hnested; destruct snapshots as [|snapshot snapshot_tail]; simpl in *;
    try contradiction; [exact I|].
  destruct Hphase as
    [Hruntime [Hclosed [Hphase_roots [Hexposure Htail_phase]]]].
  destruct Hnested as [Hhead_nested Htail_nested]. split.
  - change (frozen_caller_snapshots_nested_resume_safe Z
      (advance_frozen_caller_snapshots CT new_h frame
        (witness :: snapshot_tail))).
    eapply frozen_caller_snapshots_nested_resume_safe_after_graph_reflection;
      eauto.
  - eapply IH; eauto.
Qed.

Lemma private_resume_witnesses_completed_safe_after_graph_reflection :
  forall CT old_h new_h Z frame incoming witnesses snapshots,
    (forall location,
      frame_owned_location CT new_h frame location ->
      frame_owned_location CT old_h frame location) ->
    (forall left right,
      retained_mut_edge CT new_h left right ->
      retained_mut_edge CT old_h left right) ->
    (forall left right,
      mutable_edge CT new_h left right -> mutable_edge CT old_h left right) ->
    private_resume_witnesses_phase_wf CT old_h frame witnesses snapshots ->
    private_resume_witnesses_completed_safe CT old_h Z frame incoming
      witnesses snapshots ->
    private_resume_witnesses_completed_safe CT new_h Z frame incoming
      (advance_frozen_caller_snapshots CT new_h frame witnesses)
      (advance_frozen_caller_snapshots CT new_h frame snapshots).
Proof.
  intros CT old_h new_h Z frame incoming witnesses. induction witnesses as
    [|witness witness_tail IH]; intros snapshots Howned Hretained Hmutable
    Hphase Hcompleted; destruct snapshots as [|snapshot snapshot_tail];
    simpl in *; try contradiction; [exact I|].
  destruct Hphase as
    [Hruntime [Hclosed [Hphase_roots [Hexposure Htail_phase]]]].
  destruct Hcompleted as [Hhead_completed Htail_completed]. split.
  - change (frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT new_h frame incoming)
      (advance_frozen_caller_snapshots CT new_h frame
        (witness :: snapshot_tail))).
    eapply frozen_completed_colors_resume_safe_after_graph_reflection; eauto.
  - eapply IH; eauto.
Qed.

Lemma private_resume_witness_stack_safe_after_graph_reflection :
  forall CT old_h new_h Z frame incoming witnesses,
    (forall location, location < dom old_h ->
      r_muttype new_h location = r_muttype old_h location) ->
    dom old_h <= dom new_h ->
    wf_r_config CT frame.(frame_senv) frame.(frame_renv) new_h ->
    (forall location,
      frame_owned_location CT new_h frame location ->
      frame_owned_location CT old_h frame location) ->
    (forall left right,
      retained_mut_edge CT new_h left right ->
      retained_mut_edge CT old_h left right) ->
    (forall left right,
      mutable_edge CT new_h left right -> mutable_edge CT old_h left right) ->
    private_resume_witness_stack_safe CT old_h Z frame incoming witnesses ->
    private_resume_witness_stack_safe CT new_h Z frame incoming
      (advance_frozen_caller_snapshots CT new_h frame witnesses).
Proof.
  intros CT old_h new_h Z frame incoming witnesses Hruntimes Hdom Hwf
    Howned Hretained Hmutable
    (Hcovered & Hruntime & Hdangerous & Hclosed & Hroots & Hexposure & Hroots_safe &
      Hjoins & Hnested & Hcompleted & Hretain & Hphase).
  have Hruntime_new : frozen_caller_snapshots_runtime_mutable new_h witnesses.
  { intros snapshot Hsnapshot mode location Hcolor.
    have Hold := Hruntime snapshot Hsnapshot mode location Hcolor.
    have Hlocation := r_muttype_some_dom old_h location Mut_r Hold.
    rewrite Hruntimes; assumption. }
  have Hroots_new : frozen_caller_snapshots_resume_roots_in_heap new_h
      witnesses.
  { intros snapshot root Hsnapshot Hroot.
    have Hold : root < dom old_h by (eapply Hroots; eauto). lia. }
  unfold private_resume_witness_stack_safe.
  refine (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ (conj _ _))))))))).
  - apply advance_frozen_caller_snapshots_nested_covered. exact Hcovered.
  - eapply advance_frozen_caller_snapshots_runtime_mutable; eauto.
  - eapply advance_frozen_caller_snapshots_dangerous. exact Hdangerous.
  - apply advance_frozen_caller_snapshots_closed.
  - eapply advance_frozen_caller_snapshots_resume_roots_in_heap. exact Hroots_new.
  - eapply advance_resume_exposures_wf_from_runtime_equivalent_heap; eauto.
  - unfold frozen_caller_snapshots_active_resume_safe in *.
    eapply frozen_completed_colors_resume_safe_after_graph_reflection; eauto.
  - eapply frozen_caller_snapshots_resume_joins_safe_after_graph_reflection;
      eauto.
  - eapply frozen_caller_snapshots_nested_resume_safe_after_graph_reflection;
      eauto.
  - split.
    + eapply frozen_completed_colors_resume_safe_after_graph_reflection; eauto.
    + split.
      * eapply advance_frozen_caller_snapshots_retain_entry; eauto.
      * eapply advance_frozen_caller_snapshots_cover_phase_incoming; eauto.
Qed.

Lemma private_resume_witnesses_cover_snapshots_after_graph_reflection :
  forall CT old_h new_h Z frame witnesses snapshots,
    (forall left right,
      retained_mut_edge CT new_h left right ->
      retained_mut_edge CT old_h left right) ->
    (forall left right,
      mutable_edge CT new_h left right -> mutable_edge CT old_h left right) ->
    private_resume_witnesses_cover_snapshots Z witnesses snapshots ->
    private_resume_witnesses_phase_wf CT old_h frame witnesses snapshots ->
    frozen_caller_snapshots_nested_covered snapshots ->
    frozen_caller_snapshots_nested_resume_safe Z snapshots ->
    private_resume_witnesses_cover_snapshots Z
      (advance_frozen_caller_snapshots CT new_h frame witnesses)
      (advance_frozen_caller_snapshots CT new_h frame snapshots).
Proof.
  intros CT old_h new_h Z frame witnesses snapshots Hretained Hmutable
    Hcover Hphase Hnested_covered Hnested_safe.
  eapply private_resume_witnesses_cover_snapshots_after_advance.
  exact Hcover.
Qed.

Lemma frozen_caller_snapshots_resume_roots_safe_after_new :
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
    frozen_caller_snapshots_resume_roots_in_heap h snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame authority sGamma rGamma) snapshots ->
    frozen_caller_snapshots_resume_roots_safe CT h Z
      (mk_watched_frame authority sGamma rGamma) snapshots ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h
          (mk_watched_frame authority sGamma rGamma))
        (active_mode, location) ->
      ~ In Loc Z location) ->
    frozen_caller_snapshots_resume_roots_safe CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) Z
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h))))
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) snapshots).
Proof.
  intros CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qreceiver qruntime authority snapshots Hwf Hpost_wf Hsound Hpost_sound
    Htyping Hvals Hadapt Hcutoff Hzone Hroots Hexposure Hsafe Hactive_safe
    new_snapshot active_mode source exposure_mode target Hnew Hactive_mode
    Hactive Hroot Hexposure_mode Htarget Hprotected.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  have Hsource_old : source < dom h.
  { eapply Hroots; eauto. }
  destruct (executing_authority_colors_after_new_covered CT sGamma mt
    rGamma h x qc C args sGamma' vals qreceiver qruntime authority
    (Empty_set authority_flow_state) Hwf Hpost_wf Hsound Hpost_sound
    (ltac:(intros mode location Hempty; inversion Hempty)) Htyping Hvals
    Hadapt active_mode source Hactive_mode Hactive Hsource_old) as
    [old_active_mode [Hold_active_mode Hold_active]].
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
     [old_independent_mode [Hold_independent_mode Hold_independent]]].
  - exact (Hsafe old_snapshot old_active_mode source old_exposure_mode target
      Hold Hold_active_mode Hold_active Hroot Hold_exposure_mode
      Hold_exposure Hprotected).
  - exact (Hactive_safe old_independent_mode target Hold_independent_mode
      Hold_independent Hprotected).
Qed.

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

Lemma frozen_caller_snapshots_resume_joins_safe_after_new :
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
    frozen_caller_snapshots_active_resume_safe CT h Z
      (mk_watched_frame authority sGamma rGamma) snapshots ->
    frozen_caller_snapshots_resume_joins_safe Z snapshots ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h
          (mk_watched_frame authority sGamma rGamma))
        (active_mode, location) ->
      ~ In Loc Z location) ->
    frozen_caller_snapshots_resume_joins_safe Z
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) snapshots).
Proof.
  intros CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals qreceiver
    qruntime authority snapshots Hwf Hpost_wf Hsound Hpost_sound Htyping
    Hvals Hadapt Hcutoff Hzone Hruntime Hclosed Hroots Hexposure Hresume
    Hjoins Hactive_safe.
  eapply
    frozen_caller_snapshots_resume_joins_safe_after_classified_advance_entry
    with (exceptional := independent_active_authority_colors CT h
      (mk_watched_frame authority sGamma rGamma)).
  - exact Hjoins.
  - unfold frozen_caller_snapshots_active_resume_safe in Hresume.
    exact Hresume.
  - exact Hactive_safe.
  - intros snapshot mode location Hsnapshot Hmode Hcolor Hroot.
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

Lemma frozen_completed_colors_resume_phase_safe_after_new :
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
    frozen_completed_colors_resume_phase_safe Z
      (executing_authority_color_set CT h
        (mk_watched_frame authority sGamma rGamma) incoming) snapshots ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h
          (mk_watched_frame authority sGamma rGamma))
        (active_mode, location) ->
      ~ In Loc Z location) ->
    frozen_completed_colors_resume_phase_safe Z
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
    Hsafe Hactive_safe new_snapshot source_mode source Hnew Hsource_mode
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
  destruct (Hsafe old_snapshot old_source_mode source Hold Hold_source_mode
    Hold_source Hsource_root) as
    [[phase_mode [Hphase_mode Hphase]] | Hold_safe].
  - left. exists phase_mode. split; assumption.
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
    + exact (Hold_safe old_exposure_mode target Hold_exposure_mode
        Hold_exposure Hprotected).
    + exact (Hactive_safe active_mode target Hactive_mode Hactive Hprotected).
Qed.

Lemma saved_exposure_after_new_covered_by_old_or_active :
  forall CT sGamma mt rGamma h x qc C args sGamma' vals qreceiver qruntime
    authority colors mode location,
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
    authority_colors_runtime_mutable h colors ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h
        (mk_watched_frame authority sGamma rGamma) colors) colors ->
    authority_mode_dangerous mode ->
    location < dom h ->
    In authority_flow_state
      (frozen_caller_authority_closure CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) colors)
      (mode, location) ->
    (exists old_mode,
      authority_mode_dangerous old_mode /\
      In authority_flow_state colors (old_mode, location)) \/
    (exists active_mode,
      authority_mode_dangerous active_mode /\
      In authority_flow_state
        (independent_active_authority_colors CT h
          (mk_watched_frame authority sGamma rGamma))
        (active_mode, location)).
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' vals qreceiver qruntime
    authority colors mode location Hwf Hpost_wf Hsound Hpost_sound Htyping
    Hvals Hadapt Hruntime Hclosed Hmode Hlocation Hcolor.
  have Hpost_color : In authority_flow_state
      (executing_authority_color_set CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) colors)
      (mode, location).
  { destruct Hcolor as [seed [Hseed Hpath]]. exists seed. split.
    - left. exact Hseed.
    - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
  destruct (executing_authority_colors_after_new_covered CT sGamma mt
    rGamma h x qc C args sGamma' vals qreceiver qruntime authority colors
    Hwf Hpost_wf Hsound Hpost_sound Hruntime Htyping Hvals Hadapt mode
    location Hmode Hpost_color Hlocation) as
    [old_mode [Hold_mode Hold_color]].
  eapply executing_with_frozen_incoming_dangerous_covered_by_old_or_active;
    eauto.
Qed.

Lemma private_target_history_supports_resume_phase_after_new :
  forall CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qreceiver qruntime authority targets resumes,
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
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame authority sGamma rGamma) resumes ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h
          (mk_watched_frame authority sGamma rGamma))
        (active_mode, location) ->
      ~ In Loc Z location) ->
    private_target_history_supports_resume_phase Z targets resumes ->
    private_target_history_supports_resume_phase Z
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) targets)
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) resumes).
Proof.
  intros CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qreceiver qruntime authority targets resumes Hwf Hpost_wf Hsound
    Hpost_sound Htyping Hvals Hadapt Hcutoff Hzone Hexposure Hactive_safe
    Hhistory.
  eapply private_target_history_supports_resume_phase_after_advance;
    [exact Hhistory|].
  intros resume Hresume Hsafe exposure_mode location Hmode Hcolor Hprotected.
  have Hlocation : location < dom h by (have := Hzone location Hprotected; lia).
  destruct (saved_exposure_after_new_covered_by_old_or_active CT sGamma mt
    rGamma h x qc C args sGamma' vals qreceiver qruntime authority
    resume.(frozen_snapshot_current_resume_exposure) exposure_mode location
    Hwf Hpost_wf Hsound Hpost_sound Htyping Hvals Hadapt
    ((proj1 Hexposure) resume Hresume)
    ((proj1 (proj2 Hexposure)) resume Hresume) Hmode Hlocation Hcolor) as
    [[old_mode [Hold_mode Hold_color]] |
     [active_mode [Hactive_mode Hactive_color]]].
  - exact (Hsafe old_mode location Hold_mode Hold_color Hprotected).
  - exact (Hactive_safe active_mode location Hactive_mode Hactive_color
      Hprotected).
Qed.

Lemma frozen_caller_snapshots_nested_resume_phase_safe_after_new :
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
    frozen_caller_snapshots_resume_roots_in_heap h snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame authority sGamma rGamma) snapshots ->
    frozen_caller_snapshots_nested_resume_phase_safe Z snapshots ->
    frozen_completed_colors_resume_phase_safe Z
      (independent_active_authority_colors CT h
        (mk_watched_frame authority sGamma rGamma)) snapshots ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h
          (mk_watched_frame authority sGamma rGamma))
        (active_mode, location) ->
      ~ In Loc Z location) ->
    frozen_caller_snapshots_nested_resume_phase_safe Z
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) snapshots).
Proof.
  intros CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals qreceiver
    qruntime authority snapshots Hwf Hpost_wf Hsound Hpost_sound Htyping
    Hvals Hadapt Hcutoff Hzone Hroots Hexposure Hnested Hactive_phase
    Hactive_safe.
  induction snapshots as [|slot tail IH]; simpl in *; [exact I|].
  destruct slot as [head|].
  - destruct Hnested as [Hhead Htail]. split.
    + intros Hhead_authority new_older source_mode source Hnew Hsource_mode
        Hsource Hroot.
      unfold advance_frozen_caller_snapshots in Hnew.
      apply in_map_iff in Hnew.
      destruct Hnew as [old_slot [Heq Hold]].
      destruct old_slot as [older|]; simpl in Heq; [|discriminate].
      injection Heq as <-. simpl in *.
      have Hsource_old : source < dom h by (eapply Hroots; simpl; eauto).
      destruct (saved_exposure_after_new_covered_by_old_or_active CT sGamma
        mt rGamma h x qc C args sGamma' vals qreceiver qruntime authority
        head.(frozen_snapshot_current_resume_exposure) source_mode source Hwf
        Hpost_wf Hsound Hpost_sound Htyping Hvals Hadapt
        ((proj1 Hexposure) head (ltac:(simpl; auto)))
        ((proj1 (proj2 Hexposure)) head (ltac:(simpl; auto))) Hsource_mode
        Hsource_old Hsource) as
        [[old_mode [Hold_mode Hold_source]] |
         [active_mode [Hactive_mode Hactive_source]]].
      * destruct (Hhead Hhead_authority older old_mode source Hold Hold_mode
          Hold_source Hroot)
          as [[phase_mode [Hphase_mode Hphase]] | Hold_safe].
        -- left. exists phase_mode. simpl. split; assumption.
        -- right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
           have Htarget_old : target < dom h.
           { have := Hzone target Hprotected. lia. }
           destruct (saved_exposure_after_new_covered_by_old_or_active CT
             sGamma mt rGamma h x qc C args sGamma' vals qreceiver qruntime
             authority older.(frozen_snapshot_current_resume_exposure)
             exposure_mode target Hwf Hpost_wf Hsound Hpost_sound Htyping
             Hvals Hadapt
             ((proj1 Hexposure) older (ltac:(simpl; right; exact Hold)))
             ((proj1 (proj2 Hexposure)) older
               (ltac:(simpl; right; exact Hold)))
             Hexposure_mode Htarget_old Htarget) as
             [[old_target_mode [Hold_target_mode Hold_target]] |
              [active_target_mode [Hactive_target_mode Hactive_target]]].
           ++ eapply Hold_safe; eauto.
           ++ eapply Hactive_safe; eauto.
      * destruct (Hactive_phase older active_mode source
          (ltac:(simpl; right; exact Hold)) Hactive_mode Hactive_source Hroot)
          as [[phase_mode [Hphase_mode Hphase]] | Hold_safe].
        -- left. exists phase_mode. simpl. split; assumption.
        -- right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
           have Htarget_old : target < dom h.
           { have := Hzone target Hprotected. lia. }
           destruct (saved_exposure_after_new_covered_by_old_or_active CT
             sGamma mt rGamma h x qc C args sGamma' vals qreceiver qruntime
             authority older.(frozen_snapshot_current_resume_exposure)
             exposure_mode target Hwf Hpost_wf Hsound Hpost_sound Htyping
             Hvals Hadapt
             ((proj1 Hexposure) older (ltac:(simpl; right; exact Hold)))
             ((proj1 (proj2 Hexposure)) older
               (ltac:(simpl; right; exact Hold)))
             Hexposure_mode Htarget_old Htarget) as
             [[old_target_mode [Hold_target_mode Hold_target]] |
              [active_target_mode [Hactive_target_mode Hactive_target]]].
           ++ eapply Hold_safe; eauto.
           ++ eapply Hactive_safe; eauto.
    + eapply IH.
      * intros snapshot root Hsnapshot. eapply Hroots; simpl; eauto.
      * repeat split.
        -- intros snapshot Hsnapshot. eapply (proj1 Hexposure); simpl; eauto.
        -- intros snapshot Hsnapshot. eapply (proj1 (proj2 Hexposure));
             simpl; eauto.
        -- intros snapshot mode location Hsnapshot. eapply
             (proj1 (proj2 (proj2 Hexposure))); simpl; eauto.
        -- intros snapshot Hsnapshot. eapply
             (proj1 (proj2 (proj2 (proj2 Hexposure)))); simpl; eauto.
        -- intros snapshot root Hsnapshot. eapply
             (proj2 (proj2 (proj2 (proj2 Hexposure)))); simpl; eauto.
      * exact Htail.
      * intros snapshot source_mode source Hsnapshot. eapply Hactive_phase.
        simpl; right; exact Hsnapshot.
  - eapply IH.
    + intros snapshot root Hsnapshot. eapply Hroots; simpl; eauto.
    + repeat split.
      * intros snapshot Hsnapshot. eapply (proj1 Hexposure); simpl; eauto.
      * intros snapshot Hsnapshot. eapply (proj1 (proj2 Hexposure));
          simpl; eauto.
      * intros snapshot mode location Hsnapshot. eapply
          (proj1 (proj2 (proj2 Hexposure))); simpl; eauto.
      * intros snapshot Hsnapshot. eapply
          (proj1 (proj2 (proj2 (proj2 Hexposure)))); simpl; eauto.
      * intros snapshot root Hsnapshot. eapply
          (proj2 (proj2 (proj2 (proj2 Hexposure)))); simpl; eauto.
    + exact Hnested.
    + intros snapshot source_mode source Hsnapshot. eapply Hactive_phase.
      simpl; right; exact Hsnapshot.
Qed.

Lemma frozen_source_resume_phase_safe_after_new :
  forall CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qreceiver qruntime authority source resumes,
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
    authority_colors_runtime_mutable h source ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h
        (mk_watched_frame authority sGamma rGamma) source) source ->
    frozen_caller_snapshots_resume_roots_in_heap h resumes ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame authority sGamma rGamma) resumes ->
    frozen_completed_colors_resume_phase_safe Z source resumes ->
    frozen_completed_colors_resume_phase_safe Z
      (independent_active_authority_colors CT h
        (mk_watched_frame authority sGamma rGamma)) resumes ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h
          (mk_watched_frame authority sGamma rGamma))
        (active_mode, location) ->
      ~ In Loc Z location) ->
    frozen_completed_colors_resume_phase_safe Z
      (frozen_caller_authority_closure CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) source)
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) resumes).
Proof.
  intros CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals qreceiver
    qruntime authority source resumes Hwf Hpost_wf Hsound Hpost_sound Htyping
    Hvals Hadapt Hcutoff Hzone Hsource_runtime Hsource_closed Hroots Hexposure
    Hsafe Hactive_phase Hactive_safe new_resume source_mode location Hnew
    Hmode Hsource Hroot.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_resume|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  have Hlocation_old : location < dom h by (eapply Hroots; eauto).
  have Hlift_safe : frozen_snapshot_resume_exposure_avoids Z old_resume ->
      frozen_snapshot_resume_exposure_avoids Z
        (advance_frozen_caller_snapshot CT
          (h ++ [mkObj (mkruntime_type qruntime C) vals])
          (mk_watched_frame authority sGamma'
            (update_r_env_value rGamma x (Iot (dom h)))) old_resume).
  { intros Hold_safe exposure_mode target Hexposure_mode Htarget Hprotected.
    have Htarget_old : target < dom h.
    { have := Hzone target Hprotected. lia. }
    destruct (saved_exposure_after_new_covered_by_old_or_active CT sGamma mt
      rGamma h x qc C args sGamma' vals qreceiver qruntime authority
      old_resume.(frozen_snapshot_current_resume_exposure) exposure_mode
      target Hwf Hpost_wf Hsound Hpost_sound Htyping Hvals Hadapt
      ((proj1 Hexposure) old_resume Hold)
      ((proj1 (proj2 Hexposure)) old_resume Hold) Hexposure_mode Htarget_old
      Htarget) as
      [[old_target_mode [Hold_target_mode Hold_target]] |
       [active_target_mode [Hactive_target_mode Hactive_target]]].
    - eapply Hold_safe; eauto.
    - eapply Hactive_safe; eauto. }
  destruct (saved_exposure_after_new_covered_by_old_or_active CT sGamma mt
    rGamma h x qc C args sGamma' vals qreceiver qruntime authority source
    source_mode location Hwf Hpost_wf Hsound Hpost_sound Htyping Hvals Hadapt
    Hsource_runtime Hsource_closed Hmode Hlocation_old Hsource) as
    [[old_mode [Hold_mode Hold_source]] |
     [active_mode [Hactive_mode Hactive_source]]].
  - destruct (Hsafe old_resume old_mode location Hold Hold_mode Hold_source
      Hroot) as [[phase_mode [Hphase_mode Hphase]] | Hold_safe].
    + left. exists phase_mode. simpl. split; assumption.
    + right. exact (Hlift_safe Hold_safe).
  - destruct (Hactive_phase old_resume active_mode location Hold Hactive_mode
      Hactive_source Hroot) as
      [[phase_mode [Hphase_mode Hphase]] | Hold_safe].
    + left. exists phase_mode. simpl. split; assumption.
    + right. exact (Hlift_safe Hold_safe).
Qed.

Lemma private_target_exposures_support_resume_phase_after_new :
  forall CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qreceiver qruntime authority targets resumes,
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
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame authority sGamma rGamma) targets ->
    frozen_caller_snapshots_resume_roots_in_heap h resumes ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame authority sGamma rGamma) resumes ->
    private_target_exposures_support_resume_phase Z targets resumes ->
    frozen_completed_colors_resume_phase_safe Z
      (independent_active_authority_colors CT h
        (mk_watched_frame authority sGamma rGamma)) resumes ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h
          (mk_watched_frame authority sGamma rGamma))
        (active_mode, location) ->
      ~ In Loc Z location) ->
    private_target_exposures_support_resume_phase Z
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) targets)
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) resumes).
Proof.
  intros CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals qreceiver
    qruntime authority targets. induction targets as [|target target_tail IH];
    intros resumes Hwf Hpost_wf Hsound Hpost_sound Htyping Hvals Hadapt
      Hcutoff Hzone Htarget_exposure Hroots Hresume_exposure Hsupport
      Hactive_phase Hactive_safe.
  - destruct resumes; simpl in *; [exact I|exact Hsupport].
  - destruct resumes as [|resume resume_tail].
    + destruct target; exact Hsupport.
    + simpl in *. destruct target as [target|].
      * destruct Hsupport as [Hhead Htail]. split.
        -- eapply frozen_source_resume_phase_safe_after_new; eauto.
           ++ exact ((proj1 Htarget_exposure) target (ltac:(simpl; auto))).
           ++ exact ((proj1 (proj2 Htarget_exposure)) target
                (ltac:(simpl; auto))).
           ++ intros snapshot root Hsnapshot. eapply Hroots; simpl; eauto.
           ++ eapply frozen_caller_snapshots_resume_exposures_wf_drop_head.
              exact Hresume_exposure.
           ++ intros snapshot source_mode source Hsnapshot.
              eapply Hactive_phase. simpl; right; exact Hsnapshot.
        -- eapply IH; eauto using
             frozen_caller_snapshots_resume_exposures_wf_drop_head.
           ++ intros snapshot root Hsnapshot. eapply Hroots; simpl; eauto.
           ++ intros snapshot source_mode source Hsnapshot.
              eapply Hactive_phase. simpl; right; exact Hsnapshot.
      * eapply IH; eauto using
          frozen_caller_snapshots_resume_exposures_wf_drop_head.
        -- intros snapshot root Hsnapshot. eapply Hroots; simpl; eauto.
        -- intros snapshot source_mode source Hsnapshot.
           eapply Hactive_phase. simpl; right; exact Hsnapshot.
Qed.

Lemma frozen_target_nested_phase_safe_after_new :
  forall CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qreceiver qruntime authority targets,
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
    frozen_caller_snapshots_runtime_mutable h targets ->
    frozen_caller_snapshots_closed CT h
      (mk_watched_frame authority sGamma rGamma) targets ->
    frozen_caller_snapshots_resume_roots_in_heap h targets ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame authority sGamma rGamma) targets ->
    frozen_target_snapshots_nested_resume_phase_safe CT h Z targets ->
    frozen_completed_colors_resume_phase_safe Z
      (independent_active_authority_colors CT h
        (mk_watched_frame authority sGamma rGamma)) targets ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h
          (mk_watched_frame authority sGamma rGamma))
        (active_mode, location) ->
      ~ In Loc Z location) ->
    frozen_target_snapshots_nested_resume_phase_safe CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) Z
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) targets).
Proof.
  intros CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals qreceiver
    qruntime authority targets. induction targets as [|slot tail IH];
    intros Hwf Hpost_wf Hsound Hpost_sound Htyping Hvals Hadapt Hcutoff Hzone
      Htarget_runtime Htarget_closed Hroots Hexposure Hsafe Hactive Houtside;
      simpl in *; [exact I|].
  destruct slot as [head|].
  - destruct Hsafe as [Hhead Htail]. split.
    + intros Hauthority. eapply frozen_source_resume_phase_safe_after_new;
        eauto.
      * exact ((proj1 Hexposure) head (ltac:(simpl; auto))).
      * exact ((proj1 (proj2 Hexposure)) head (ltac:(simpl; auto))).
      * intros snapshot root Hsnapshot. eapply Hroots; simpl; eauto.
      * eapply frozen_caller_snapshots_resume_exposures_wf_drop_head.
        exact Hexposure.
      * exact (Hhead Hauthority).
      * intros snapshot source_mode source Hsnapshot.
        eapply Hactive. simpl; right; exact Hsnapshot.
    + eapply IH; eauto using
        frozen_caller_snapshots_resume_exposures_wf_drop_head.
      * intros snapshot Hsnapshot. eapply Htarget_runtime; simpl; eauto.
      * intros snapshot Hsnapshot. eapply Htarget_closed; simpl; eauto.
      * intros snapshot root Hsnapshot. eapply Hroots; simpl; eauto.
      * intros snapshot source_mode source Hsnapshot.
        eapply Hactive. simpl; right; exact Hsnapshot.
  - eapply IH; eauto using
      frozen_caller_snapshots_resume_exposures_wf_drop_head.
    + intros snapshot Hsnapshot. eapply Htarget_runtime; simpl; eauto.
    + intros snapshot Hsnapshot. eapply Htarget_closed; simpl; eauto.
    + intros snapshot root Hsnapshot. eapply Hroots; simpl; eauto.
    + intros snapshot source_mode source Hsnapshot.
      eapply Hactive. simpl; right; exact Hsnapshot.
Qed.

Lemma private_resume_witnesses_roots_safe_after_new :
  forall CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qreceiver qruntime authority witnesses snapshots,
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
    private_resume_witnesses_phase_wf CT h
      (mk_watched_frame authority sGamma rGamma) witnesses snapshots ->
    private_resume_witnesses_roots_safe CT h Z
      (mk_watched_frame authority sGamma rGamma) witnesses snapshots ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h
          (mk_watched_frame authority sGamma rGamma))
        (active_mode, location) ->
      ~ In Loc Z location) ->
    private_resume_witnesses_roots_safe CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) Z
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h))))
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) witnesses)
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) snapshots).
Proof.
  intros CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals qreceiver
    qruntime authority witnesses. induction witnesses as
    [|witness witness_tail IH]; intros snapshots Hwf Hpost_wf Hsound
    Hpost_sound Htyping Hvals Hadapt Hcutoff Hzone Hphase Hsafe Hactive_safe;
    destruct snapshots as [|snapshot snapshot_tail]; simpl in *;
    try contradiction; [exact I|].
  destruct Hphase as
    [Hruntime [Hclosed [Hphase_roots [Hexposure Htail_phase]]]].
  destruct Hsafe as [Hhead_safe Htail_safe]. split.
  - change (frozen_caller_snapshots_active_resume_safe CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) Z
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h))))
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h))))
        (witness :: snapshot_tail))).
    unfold frozen_caller_snapshots_active_resume_safe in *.
    eapply frozen_completed_colors_resume_safe_after_new; eauto.
    intros mode location Hempty. inversion Hempty.
  - eapply IH; eauto.
Qed.

Lemma private_resume_witnesses_nested_resume_safe_after_new :
  forall CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qreceiver qruntime authority witnesses snapshots,
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
    private_resume_witnesses_phase_wf CT h
      (mk_watched_frame authority sGamma rGamma) witnesses snapshots ->
    private_resume_witnesses_roots_safe CT h Z
      (mk_watched_frame authority sGamma rGamma) witnesses snapshots ->
    private_resume_witnesses_nested_resume_safe Z witnesses snapshots ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h
          (mk_watched_frame authority sGamma rGamma))
        (active_mode, location) ->
      ~ In Loc Z location) ->
    private_resume_witnesses_nested_resume_safe Z
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) witnesses)
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) snapshots).
Proof.
  intros CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals qreceiver
    qruntime authority witnesses. induction witnesses as
    [|witness witness_tail IH]; intros snapshots Hwf Hpost_wf Hsound
    Hpost_sound Htyping Hvals Hadapt Hcutoff Hzone Hphase Hroots_safe Hnested
    Hactive_safe; destruct snapshots as [|snapshot snapshot_tail]; simpl in *;
    try contradiction; [exact I|].
  destruct Hphase as
    [Hruntime [Hclosed [Hphase_roots [Hexposure Htail_phase]]]].
  destruct Hroots_safe as [Hhead_roots_safe Htail_roots_safe].
  destruct Hnested as [Hhead_nested Htail_nested]. split.
  - change (frozen_caller_snapshots_nested_resume_safe Z
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h))))
        (witness :: snapshot_tail))).
    eapply frozen_caller_snapshots_nested_resume_safe_after_new; eauto.
  - eapply IH; eauto.
Qed.

Lemma private_resume_witnesses_completed_safe_after_new :
  forall CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qreceiver qruntime authority incoming witnesses snapshots,
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
    private_resume_witnesses_phase_wf CT h
      (mk_watched_frame authority sGamma rGamma) witnesses snapshots ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h
          (mk_watched_frame authority sGamma rGamma))
        (active_mode, location) ->
      ~ In Loc Z location) ->
    private_resume_witnesses_completed_safe CT h Z
      (mk_watched_frame authority sGamma rGamma) incoming witnesses
      snapshots ->
    private_resume_witnesses_completed_safe CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) Z
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h)))) incoming
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) witnesses)
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) snapshots).
Proof.
  intros CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals qreceiver
    qruntime authority incoming witnesses. induction witnesses as
    [|witness witness_tail IH]; intros snapshots Hwf Hpost_wf Hsound
    Hpost_sound Hincoming_runtime Htyping Hvals Hadapt Hcutoff Hzone Hphase
    Hactive_safe Hcompleted;
    destruct snapshots as [|snapshot snapshot_tail]; simpl in *;
    try contradiction; [exact I|].
  destruct Hphase as
    [Hruntime [Hclosed [Hphase_roots [Hexposure Htail_phase]]]].
  destruct Hcompleted as [Hhead_completed Htail_completed]. split.
  - change (frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) incoming)
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h))))
        (witness :: snapshot_tail))).
    eapply frozen_completed_colors_resume_safe_after_new; eauto.
  - eapply IH; eauto.
Qed.

Lemma private_resume_witness_stack_safe_after_new :
  forall CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qreceiver qruntime authority incoming witnesses,
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
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h
          (mk_watched_frame authority sGamma rGamma))
        (active_mode, location) ->
      ~ In Loc Z location) ->
    private_resume_witness_stack_safe CT h Z
      (mk_watched_frame authority sGamma rGamma) incoming witnesses ->
    private_resume_witness_stack_safe CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) Z
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h)))) incoming
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) witnesses).
Proof.
  intros CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qreceiver qruntime authority incoming witnesses Hwf Hpost_wf Hsound
    Hpost_sound Hincoming_runtime Htyping Hvals Hadapt Hcutoff Hzone
    Hactive_safe
    (Hcovered & Hruntime & Hdangerous & Hclosed & Hroots & Hexposure & Hroots_safe &
      Hjoins & Hnested & Hcompleted & Hretain & Hphase).
  have Hruntime_new : frozen_caller_snapshots_runtime_mutable
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) witnesses.
  { intros snapshot Hsnapshot mode location Hcolor.
    have Hold := Hruntime snapshot Hsnapshot mode location Hcolor.
    have Hlocation := r_muttype_some_dom h location Mut_r Hold.
    rewrite r_muttype_app_preserve_old; assumption. }
  have Hroots_new : frozen_caller_snapshots_resume_roots_in_heap
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) witnesses.
  { intros snapshot root Hsnapshot Hroot.
    have Hold : root < dom h by (eapply Hroots; eauto).
    rewrite length_app. simpl. lia. }
  unfold private_resume_witness_stack_safe.
  refine (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ (conj _ _))))))))).
  - apply advance_frozen_caller_snapshots_nested_covered. exact Hcovered.
  - eapply advance_frozen_caller_snapshots_runtime_mutable; eauto.
  - eapply advance_frozen_caller_snapshots_dangerous. exact Hdangerous.
  - apply advance_frozen_caller_snapshots_closed.
  - eapply advance_frozen_caller_snapshots_resume_roots_in_heap.
    exact Hroots_new.
  - eapply advance_resume_exposures_wf_from_runtime_equivalent_heap with
      (old_active := mk_watched_frame authority sGamma rGamma)
      (new_active := mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h)))).
    + intros location Hlocation.
      apply r_muttype_app_preserve_old. exact Hlocation.
    + exact Hpost_wf.
    + exact Hroots.
    + exact Hexposure.
  - unfold frozen_caller_snapshots_active_resume_safe in *.
    eapply frozen_completed_colors_resume_safe_after_new; eauto.
    intros mode location Hempty. inversion Hempty.
  - eapply frozen_caller_snapshots_resume_joins_safe_after_new; eauto.
  - eapply frozen_caller_snapshots_nested_resume_safe_after_new; eauto.
  - split.
    + eapply frozen_completed_colors_resume_safe_after_new; eauto.
    + split.
      * eapply advance_frozen_caller_snapshots_retain_entry; eauto.
      * eapply advance_frozen_caller_snapshots_cover_phase_incoming; eauto.
Qed.

Lemma private_resume_witnesses_cover_snapshots_after_new :
  forall CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qreceiver qruntime authority witnesses snapshots,
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
    private_resume_witnesses_cover_snapshots Z witnesses snapshots ->
    private_resume_witnesses_phase_wf CT h
      (mk_watched_frame authority sGamma rGamma) witnesses snapshots ->
    private_resume_witnesses_roots_safe CT h Z
      (mk_watched_frame authority sGamma rGamma) witnesses snapshots ->
    frozen_caller_snapshots_nested_covered snapshots ->
    frozen_caller_snapshots_nested_resume_safe Z snapshots ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h
          (mk_watched_frame authority sGamma rGamma))
        (active_mode, location) ->
      ~ In Loc Z location) ->
    private_resume_witnesses_cover_snapshots Z
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) witnesses)
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) snapshots).
Proof.
  intros CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals qreceiver
    qruntime authority witnesses snapshots Hwf Hpost_wf Hsound Hpost_sound
    Htyping Hvals Hadapt Hcutoff Hzone Hcover Hphase Hroots Hnested_covered
    Hnested_safe Hactive_safe.
  eapply private_resume_witnesses_cover_snapshots_after_advance.
  exact Hcover.
Qed.

(** The target component of a frame policy is persistent, but its suspended
    resume witnesses are phase-current ghost state.  Every statement phase
    advances those witnesses through the active frame exactly as it advances
    the stack-aligned frozen snapshots.  Keeping this operation explicit is
    important: retaining only the call-entry witness would reconstruct a
    suspended caller from stale colors at pop time. *)
Definition advance_private_frame_resume_witnesses
  (CT : class_table) (h : heap) (active : watched_frame)
  (policies : private_frame_join_policies) : private_frame_join_policies :=
  mk_private_frame_join_policies
    policies.(active_frame_join_targets)
    policies.(suspended_frame_join_targets)
    (advance_frozen_caller_snapshots CT h active
      policies.(suspended_frame_target_witnesses))
    (advance_frozen_caller_snapshots CT h active
      policies.(suspended_frame_resume_witnesses)).

(** Call entry pushes the immediate caller witness and advances every older
    suspended witness through the callee entry phase.  The newly pushed
    witness is already constructed in that phase, so it must not be advanced
    a second time. *)
Definition enter_private_frame_join_policies_advanced
  (CT : class_table) (h : heap) (callee : watched_frame)
  (target_witness : frozen_caller_snapshot_slot)
  (caller_witness : frozen_caller_snapshot_slot)
  (policies : private_frame_join_policies) : private_frame_join_policies :=
  mk_private_frame_join_policies
    (frame_rdm_root_set callee)
    (policies.(active_frame_join_targets) ::
      policies.(suspended_frame_join_targets))
    (target_witness :: advance_frozen_caller_snapshots CT h callee
      policies.(suspended_frame_target_witnesses))
    (caller_witness ::
      advance_frozen_caller_snapshots CT h callee
        policies.(suspended_frame_resume_witnesses)).

(** Pop restores the caller's persistent target set while retaining the
    phase-current tail of resume witnesses.  Unlike the old exact inverse of
    entry, this is intentionally state transforming. *)
Definition leave_private_frame_join_policies_advanced
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

(** Return-time policy transition.  Only the target channel accumulates the
    colors of the frame that actually resumes.  Exceptional resume witnesses
    retain their exact phase metadata and merely advance their two current
    closure images. *)
Definition activate_private_frame_targets_on_pop
  (CT : class_table) (h : heap) (caller : watched_frame)
  (incoming : Ensemble authority_flow_state)
  (policies : private_frame_join_policies) : private_frame_join_policies :=
  mk_private_frame_join_policies
    policies.(active_frame_join_targets)
    policies.(suspended_frame_join_targets)
    (activate_frozen_target_snapshots CT h caller
      (dangerous_authority_colors
        (executing_authority_color_set CT h caller incoming))
      policies.(suspended_frame_target_witnesses))
    (advance_frozen_caller_snapshots CT h caller
      policies.(suspended_frame_resume_witnesses)).

(** Statement evaluation does not change a frame's persistent join targets.
    It may only advance the phase-current colors of suspended witnesses. *)
Definition private_frame_join_policies_metadata_eq
  (final initial : private_frame_join_policies) : Prop :=
  final.(active_frame_join_targets) = initial.(active_frame_join_targets) /\
  final.(suspended_frame_join_targets) =
    initial.(suspended_frame_join_targets) /\
  frozen_target_snapshot_list_metadata_le
    final.(suspended_frame_target_witnesses)
    initial.(suspended_frame_target_witnesses) /\
  frozen_caller_snapshot_list_metadata_eq
    final.(suspended_frame_resume_witnesses)
    initial.(suspended_frame_resume_witnesses).

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

Definition frozen_caller_snapshot_list_phase_images_grow
  (final initial : list frozen_caller_snapshot_slot) : Prop :=
  Forall2 frozen_caller_snapshot_slot_phase_images_grow final initial.

Lemma frozen_caller_snapshot_list_phase_images_grow_refl :
  forall snapshots,
    frozen_caller_snapshot_list_phase_images_grow snapshots snapshots.
Proof.
  intros snapshots. induction snapshots as [|slot tail IH]; constructor;
    [|exact IH]. destruct slot; simpl; [split|exact I]; intros state Hstate;
    exact Hstate.
Qed.

Lemma frozen_caller_snapshot_slot_phase_images_grow_trans :
  forall first middle final,
    frozen_caller_snapshot_slot_phase_images_grow middle first ->
    frozen_caller_snapshot_slot_phase_images_grow final middle ->
    frozen_caller_snapshot_slot_phase_images_grow final first.
Proof.
  intros first middle final Hfirst Hsecond.
  destruct first as [first|], middle as [middle|], final as [final|];
    simpl in *; try contradiction; [|exact I].
  destruct Hfirst as [Hcolors1 Hexposure1].
  destruct Hsecond as [Hcolors2 Hexposure2]. split.
  - intros state Hstate. apply Hcolors2. apply Hcolors1. exact Hstate.
  - intros state Hstate. apply Hexposure2. apply Hexposure1. exact Hstate.
Qed.

Lemma frozen_caller_snapshot_list_phase_images_grow_trans :
  forall first middle final,
    frozen_caller_snapshot_list_phase_images_grow middle first ->
    frozen_caller_snapshot_list_phase_images_grow final middle ->
    frozen_caller_snapshot_list_phase_images_grow final first.
Proof.
  intros first. induction first as [|first_head first_tail IH];
    intros middle final Hfirst Hsecond.
  - inversion Hfirst; subst. inversion Hsecond; constructor.
  - destruct middle as [|middle_head middle_tail]; [inversion Hfirst|].
    destruct final as [|final_head final_tail]; [inversion Hsecond|].
    inversion Hfirst as
      [|first_head' middle_head' first_tail' middle_tail' Hhead1 Htail1];
      subst.
    inversion Hsecond as
      [|middle_head' final_head' middle_tail' final_tail' Hhead2 Htail2];
      subst.
    constructor.
    + eapply frozen_caller_snapshot_slot_phase_images_grow_trans; eauto.
    + eapply IH; eauto.
Qed.

Lemma advance_frozen_caller_snapshots_phase_images_grow :
  forall CT h active snapshots,
    frozen_caller_snapshot_list_phase_images_grow
      (advance_frozen_caller_snapshots CT h active snapshots) snapshots.
Proof.
  intros CT h active snapshots. induction snapshots as [|slot tail IH];
    constructor; [|exact IH]. destruct slot as [snapshot|]; simpl; [|exact I].
  split; intros state Hstate; apply frozen_caller_authority_closure_contains;
    exact Hstate.
Qed.

Lemma private_frame_join_policies_metadata_eq_refl :
  forall policies,
    private_frame_join_policies_metadata_eq policies policies.
Proof.
  intros [active_targets suspended_targets target_witnesses
    suspended_witnesses].
  unfold private_frame_join_policies_metadata_eq. simpl.
  split; [reflexivity|]. split; [reflexivity|]. split.
  - induction target_witnesses as [|slot tail IH].
    + constructor.
    + constructor; [|exact IH]. destruct slot as [snapshot|]; simpl;
        [|exact I].
      unfold frozen_target_snapshot_metadata_le, Same_set, Included.
      firstorder.
  - induction suspended_witnesses as [|slot tail IH].
    + constructor.
    + constructor; [|exact IH]. destruct slot as [snapshot|]; simpl;
        [|exact I].
      unfold frozen_caller_snapshot_metadata_eq, Same_set, Included.
      firstorder.
Qed.

Lemma private_frame_join_policies_metadata_eq_trans :
  forall first middle final,
    private_frame_join_policies_metadata_eq middle first ->
    private_frame_join_policies_metadata_eq final middle ->
    private_frame_join_policies_metadata_eq final first.
Proof.
  intros first middle final
    [Hactive1 [Hsuspended1 [Htarget1 Hwitness1]]]
    [Hactive2 [Hsuspended2 [Htarget2 Hwitness2]]].
  unfold private_frame_join_policies_metadata_eq.
  split; [congruence|]. split; [congruence|]. split.
  - eapply frozen_target_snapshot_list_metadata_le_trans; eauto.
  - eapply frozen_caller_snapshot_list_metadata_eq_trans; eauto.
Qed.

Lemma advance_private_frame_resume_witnesses_metadata_eq :
  forall CT h active policies,
    private_frame_join_policies_metadata_eq
      (advance_private_frame_resume_witnesses CT h active policies) policies.
Proof.
  intros CT h active [active_targets suspended_targets target_witnesses
    suspended_witnesses].
  unfold private_frame_join_policies_metadata_eq,
    advance_private_frame_resume_witnesses. simpl.
  repeat split; try reflexivity.
  - apply frozen_caller_snapshot_list_metadata_eq_target_le.
    apply advance_frozen_caller_snapshots_metadata_eq.
  - apply advance_frozen_caller_snapshots_metadata_eq.
Qed.

Definition initial_private_frame_join_policies
  (active : watched_frame) (stack : list watched_boundary) :
  private_frame_join_policies :=
  mk_private_frame_join_policies
    (frame_rdm_root_set active)
    (repeat (Empty_set Loc) (length stack))
    (repeat None (length stack))
    (repeat None (length stack)).

Definition enter_private_frame_join_policies
  (callee : watched_frame) (caller_witness : frozen_caller_snapshot_slot)
  (policies : private_frame_join_policies) :
  private_frame_join_policies :=
  mk_private_frame_join_policies
    (frame_rdm_root_set callee)
    (policies.(active_frame_join_targets) ::
      policies.(suspended_frame_join_targets))
    (None :: policies.(suspended_frame_target_witnesses))
    (caller_witness :: policies.(suspended_frame_resume_witnesses)).

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

Definition suspended_frame_resume_witness
  (policies : private_frame_join_policies) : frozen_caller_snapshot_slot :=
  match policies.(suspended_frame_resume_witnesses) with
  | witness :: _ => witness
  | [] => None
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

Lemma frame_rdm_root_set_in_heap :
  forall CT h frame,
    wf_r_config CT frame.(frame_senv) frame.(frame_renv) h ->
    private_frame_join_targets_in_heap h (frame_rdm_root_set frame).
Proof.
  intros CT h frame Hwf location
    [variable [T [Htype [Hvalue Hrdm]]]].
  eapply wf_config_value_dom; eauto.
Qed.

Lemma private_frame_join_targets_in_heap_growth :
  forall h h' targets,
    dom h <= dom h' ->
    private_frame_join_targets_in_heap h targets ->
    private_frame_join_targets_in_heap h' targets.
Proof.
  intros h h' targets Hgrowth Htargets location Hlocation.
  specialize (Htargets location Hlocation). lia.
Qed.

Lemma private_frame_join_policies_valid_heap_growth :
  forall h h' policies stack,
    dom h <= dom h' ->
    private_frame_join_policies_valid h policies stack ->
    private_frame_join_policies_valid h' policies stack.
Proof.
  intros h h' policies stack Hgrowth [Hactive Hsuspended]. split.
  - eapply private_frame_join_targets_in_heap_growth; eauto.
  - exact Hsuspended.
Qed.

Lemma initial_private_frame_join_policies_aligned :
  forall active stack,
    private_frame_join_policies_aligned
      (initial_private_frame_join_policies active stack) stack.
Proof.
  intros active stack. unfold private_frame_join_policies_aligned,
    initial_private_frame_join_policies. simpl. repeat split;
    apply repeat_length.
Qed.

Lemma initial_private_frame_join_policies_valid :
  forall CT h active stack,
    live_frames_wf CT h active stack ->
    private_frame_join_policies_valid h
      (initial_private_frame_join_policies active stack) stack.
Proof.
  intros CT h active stack [Hactive Hstack]. split.
  - eapply frame_rdm_root_set_in_heap. exact Hactive.
  - clear Hactive Hstack. induction stack as [|boundary tail IH]; simpl.
    + constructor.
    + constructor; [|exact IH].
      intros location Hempty. inversion Hempty.
Qed.

Lemma enter_private_frame_join_policies_valid :
  forall CT h caller callee caller_witness boundary stack policies,
    boundary.(boundary_caller) = caller ->
    boundary.(boundary_entry_cutoff) = dom h ->
    wf_r_config CT callee.(frame_senv) callee.(frame_renv) h ->
    private_frame_join_policies_valid h policies stack ->
    private_frame_join_policies_valid h
      (enter_private_frame_join_policies callee caller_witness policies)
      (boundary :: stack).
Proof.
  intros CT h caller callee caller_witness boundary stack policies Hcaller Hcutoff Hcallee
    [Hactive Hsuspended]. split.
  - eapply frame_rdm_root_set_in_heap. exact Hcallee.
  - constructor.
    + intros location Hlocation. rewrite Hcutoff.
      eapply Hactive. exact Hlocation.
    + exact Hsuspended.
Qed.

Lemma enter_private_frame_join_policies_advanced_valid :
  forall CT h caller callee target_witness caller_witness boundary stack policies,
    boundary.(boundary_caller) = caller ->
    boundary.(boundary_entry_cutoff) = dom h ->
    wf_r_config CT callee.(frame_senv) callee.(frame_renv) h ->
    private_frame_join_policies_valid h policies stack ->
    private_frame_join_policies_valid h
      (enter_private_frame_join_policies_advanced CT h callee target_witness
        caller_witness policies) (boundary :: stack).
Proof.
  intros CT h caller callee target_witness caller_witness boundary stack
    policies Hcaller Hcutoff Hcallee [Hactive Hsuspended]. split.
  - eapply frame_rdm_root_set_in_heap. exact Hcallee.
  - constructor.
    + intros location Hlocation. rewrite Hcutoff.
      eapply Hactive. exact Hlocation.
    + exact Hsuspended.
Qed.

Lemma enter_private_frame_join_policies_aligned :
  forall callee caller_witness boundary stack policies,
    private_frame_join_policies_aligned policies stack ->
    private_frame_join_policies_aligned
      (enter_private_frame_join_policies callee caller_witness policies)
      (boundary :: stack).
Proof.
  intros callee caller_witness boundary stack policies Haligned.
  unfold private_frame_join_policies_aligned,
    enter_private_frame_join_policies in *. simpl in *.
  destruct Haligned as [Htargets [Htarget_witnesses Hwitnesses]].
  repeat split; simpl; lia.
Qed.

Lemma advance_private_frame_resume_witnesses_aligned :
  forall CT h active policies stack,
    private_frame_join_policies_aligned policies stack ->
    private_frame_join_policies_aligned
      (advance_private_frame_resume_witnesses CT h active policies) stack.
Proof.
  intros CT h active
    [active_targets suspended_targets target_witnesses suspended_witnesses]
    stack [Htargets [Htarget_witnesses Hwitnesses]].
  unfold private_frame_join_policies_aligned,
    advance_private_frame_resume_witnesses in *. simpl in *.
  split; [exact Htargets|]. split.
  - rewrite length_map. exact Htarget_witnesses.
  - rewrite length_map. exact Hwitnesses.
Qed.

Lemma enter_private_frame_join_policies_advanced_aligned :
  forall CT h callee target_witness caller_witness boundary stack policies,
    private_frame_join_policies_aligned policies stack ->
    private_frame_join_policies_aligned
      (enter_private_frame_join_policies_advanced CT h callee target_witness
        caller_witness policies) (boundary :: stack).
Proof.
  intros CT h callee target_witness caller_witness boundary stack
    [active_targets suspended_targets target_witnesses suspended_witnesses]
    [Htargets [Htarget_witnesses Hwitnesses]].
  unfold private_frame_join_policies_aligned,
    enter_private_frame_join_policies_advanced in *. simpl in *.
  split; [lia|]. split; simpl; f_equal; rewrite length_map;
    assumption.
Qed.

Lemma leave_private_frame_join_policies_advanced_after_enter :
  forall CT h callee target_witness caller_witness policies,
    leave_private_frame_join_policies_advanced
      (enter_private_frame_join_policies_advanced CT h callee target_witness
        caller_witness policies) =
    Some (advance_private_frame_resume_witnesses CT h callee policies).
Proof.
  intros CT h callee target_witness caller_witness
    [active_targets suspended_targets target_witnesses
      suspended_witnesses]. reflexivity.
Qed.

Lemma suspended_frame_resume_witness_after_advanced_enter :
  forall CT h callee target_witness caller_witness policies,
    suspended_frame_resume_witness
      (enter_private_frame_join_policies_advanced CT h callee target_witness
        caller_witness policies) = caller_witness.
Proof. reflexivity. Qed.

Lemma leave_private_frame_join_policies_after_enter :
  forall callee caller_witness policies,
    leave_private_frame_join_policies
      (enter_private_frame_join_policies callee caller_witness policies) =
      Some policies.
Proof.
  intros callee caller_witness
    [active_targets suspended_targets target_witnesses
      suspended_witnesses]. reflexivity.
Qed.

Lemma suspended_frame_resume_witness_after_enter :
  forall callee caller_witness policies,
    suspended_frame_resume_witness
      (enter_private_frame_join_policies callee caller_witness policies) =
      caller_witness.
Proof. reflexivity. Qed.

Lemma leave_private_frame_join_policies_aligned :
  forall boundary stack policies caller_policies,
    private_frame_join_policies_aligned policies (boundary :: stack) ->
    leave_private_frame_join_policies policies = Some caller_policies ->
    private_frame_join_policies_aligned caller_policies stack.
Proof.
  intros boundary stack
    [active_targets suspended_targets target_witnesses suspended_witnesses]
    caller_policies [Htargets [Htarget_witnesses Hwitnesses]] Hleave.
  destruct suspended_targets as [|caller_targets target_tail];
    destruct target_witnesses as [|target_witness target_witness_tail];
    destruct suspended_witnesses as [|caller_witness witness_tail];
    simpl in Hleave; try discriminate.
  injection Hleave as <-. unfold private_frame_join_policies_aligned.
  simpl in *. repeat split; lia.
Qed.

Lemma leave_private_frame_join_policies_valid :
  forall h boundary stack policies caller_policies,
    private_frame_join_policies_valid h policies (boundary :: stack) ->
    boundary.(boundary_entry_cutoff) <= dom h ->
    leave_private_frame_join_policies policies = Some caller_policies ->
    private_frame_join_policies_valid h caller_policies stack.
Proof.
  intros h boundary stack
    [active_targets suspended_targets target_witnesses suspended_witnesses]
    caller_policies [Hactive Hsuspended] Hcutoff Hleave.
  destruct suspended_targets as [|caller_targets tail];
    destruct target_witnesses as [|target_witness target_witness_tail];
    destruct suspended_witnesses as [|caller_witness witness_tail];
    simpl in Hleave; try discriminate.
  injection Hleave as <-. inversion Hsuspended; subst. split.
  - intros location Hlocation. specialize (H2 location Hlocation). lia.
  - exact H4.
Qed.

Lemma leave_private_frame_join_targets_before_boundary :
  forall h boundary stack policies caller_policies,
    private_frame_join_policies_valid h policies (boundary :: stack) ->
    leave_private_frame_join_policies policies = Some caller_policies ->
    private_frame_join_targets_before_boundary
      caller_policies.(active_frame_join_targets) boundary.
Proof.
  intros h boundary stack
    [active_targets suspended_targets target_witnesses suspended_witnesses]
    caller_policies [Hactive Hsuspended] Hleave.
  destruct suspended_targets as [|caller_targets tail];
    destruct target_witnesses as [|target_witness target_witness_tail];
    destruct suspended_witnesses as [|caller_witness witness_tail];
    simpl in Hleave; try discriminate.
  injection Hleave as <-. inversion Hsuspended; subst. exact H2.
Qed.

Lemma immutable_fresh_return_is_not_persistent_join_target :
  forall h boundary stack policies caller_policies caller return_location,
    private_frame_join_policies_valid h policies (boundary :: stack) ->
    leave_private_frame_join_policies policies = Some caller_policies ->
    caller.(frame_authority) = Imm_r ->
    boundary.(boundary_entry_cutoff) <= return_location ->
    ~ resumed_frame_join_target
        caller_policies.(active_frame_join_targets) caller return_location.
Proof.
  intros h boundary stack policies caller_policies caller return_location
    Hvalid Hleave Hauthority Hfresh [Hmutable | Heligible].
  - congruence.
  - have Hold := leave_private_frame_join_targets_before_boundary h boundary
      stack policies caller_policies Hvalid Hleave return_location Heligible.
    lia.
Qed.

(** Policy-indexed wrapper for the final statement induction.  The policy is
    proof-only and stack aligned.  The ordinary private package is retained
    temporarily while the recursive proof is migrated; its separation fact
    immediately entails the restricted separation fact below. *)
Definition private_policy_statement_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary)
  (incoming : Ensemble authority_flow_state)
  (snapshots : list frozen_caller_snapshot_slot)
  (policies : private_frame_join_policies) (h : heap) : Prop :=
  private_principled_statement_state CT P Z cutoff active stack incoming
    snapshots h /\
  private_frame_join_policies_aligned policies stack /\
  private_frame_join_policies_valid h policies stack /\
  executing_resumed_authority_colors_separated CT h Z
    policies.(active_frame_join_targets) active incoming.

(** The allocation-stable overlap certificate is needed only for the
    policy-only tracked head consumed by the exceptional non-null pop.  An
    ordinary [None] boundary is reconstructed through the completed-color
    certificate instead; demanding executing overlap there would conflate
    inaccessible inherited authority with the active frame. *)
Lemma repeat_none_private_policy_head_overlap :
  forall CT h Z active count,
    private_policy_head_active_overlap_justified CT h Z active
      (repeat None count).
Proof.
  intros CT h Z active count. induction count; simpl;
    [exact I|exact IHcount].
Qed.

Definition private_advancing_policy_statement_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary)
  (incoming : Ensemble authority_flow_state)
  (snapshots : list frozen_caller_snapshot_slot)
  (policies : private_frame_join_policies) (h : heap) : Prop :=
  private_policy_statement_state CT P Z cutoff active stack incoming snapshots
    policies h /\
  private_resume_witnesses_cover_snapshots Z
    policies.(suspended_frame_resume_witnesses) snapshots /\
  private_resume_witnesses_phase_wf CT h active
    policies.(suspended_frame_resume_witnesses) snapshots /\
  private_resume_witnesses_roots_safe CT h Z active
    policies.(suspended_frame_resume_witnesses) snapshots /\
  private_resume_witnesses_nested_resume_safe Z
    policies.(suspended_frame_resume_witnesses) snapshots /\
  private_resume_witnesses_completed_safe CT h Z active incoming
    policies.(suspended_frame_resume_witnesses) snapshots /\
  private_resume_witness_stack_safe CT h Z active incoming
    policies.(suspended_frame_resume_witnesses) /\
  frozen_caller_snapshots_before_boundaries
    policies.(suspended_frame_resume_witnesses) stack /\
  private_resume_witness_temporal_state CT h Z cutoff active stack
    policies.(suspended_frame_resume_witnesses) /\
  private_target_witness_state CT h Z cutoff active incoming snapshots
    policies.(suspended_frame_target_witnesses)
    policies.(suspended_frame_resume_witnesses) stack.

Lemma private_advancing_policy_statement_state_temporal :
  forall CT P Z cutoff active stack incoming snapshots policies h,
    private_advancing_policy_statement_state CT P Z cutoff active stack
      incoming snapshots policies h ->
    private_resume_witness_temporal_state CT h Z cutoff active stack
      policies.(suspended_frame_resume_witnesses).
Proof.
  intros CT P Z cutoff active stack incoming snapshots policies h
    (_ & _ & _ & _ & _ & _ & _ & _ & Htemporal & _).
  exact Htemporal.
Qed.

Lemma private_advancing_policy_statement_state_target :
  forall CT P Z cutoff active stack incoming snapshots policies h,
    private_advancing_policy_statement_state CT P Z cutoff active stack
      incoming snapshots policies h ->
    private_target_witness_state CT h Z cutoff active incoming snapshots
      policies.(suspended_frame_target_witnesses)
      policies.(suspended_frame_resume_witnesses) stack.
Proof.
  intros CT P Z cutoff active stack incoming snapshots policies h
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & Htarget).
  exact Htarget.
Qed.

Lemma private_policy_statement_state_advance_resume_witnesses :
  forall CT P Z cutoff active stack incoming snapshots policies h,
    private_policy_statement_state CT P Z cutoff active stack incoming
      snapshots policies h ->
    private_policy_statement_state CT P Z cutoff active stack incoming
      snapshots (advance_private_frame_resume_witnesses CT h active policies)
      h.
Proof.
  intros CT P Z cutoff active stack incoming snapshots
    [active_targets suspended_targets suspended_witnesses] h
    [Hprivate [Haligned [Hvalid Hseparated]]].
  split; [exact Hprivate|]. split.
  - eapply advance_private_frame_resume_witnesses_aligned. exact Haligned.
  - split.
    + unfold private_frame_join_policies_valid,
        advance_private_frame_resume_witnesses in *. simpl in *.
      exact Hvalid.
    + unfold advance_private_frame_resume_witnesses. simpl. exact Hseparated.
Qed.

Definition private_policy_statement_result
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (authority : q_r) (final_senv : s_env) (final_renv : r_env)
  (stack : list watched_boundary) (incoming : Ensemble authority_flow_state)
  (initial_snapshots final_snapshots : list frozen_caller_snapshot_slot)
  (policies : private_frame_join_policies) (final_h : heap) : Prop :=
  private_principled_statement_result CT P Z cutoff authority final_senv
    final_renv stack incoming initial_snapshots final_snapshots final_h /\
  private_frame_join_policies_aligned policies stack /\
  private_frame_join_policies_valid final_h policies stack /\
  executing_resumed_authority_colors_separated CT final_h Z
    policies.(active_frame_join_targets)
    (mk_watched_frame authority final_senv final_renv) incoming.

(** Result package used by the completed policy-aware induction.  Persistent
    target sets are unchanged, while the final policy existentially carries
    the advanced suspended witnesses.  The older fixed-policy result remains
    as the state payload during migration; it cannot express witness
    evolution by itself. *)
Definition private_advancing_policy_statement_result
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (authority : q_r) (final_senv : s_env) (final_renv : r_env)
  (stack : list watched_boundary)
  (incoming : Ensemble authority_flow_state)
  (initial_snapshots final_snapshots : list frozen_caller_snapshot_slot)
  (initial_policies : private_frame_join_policies) (final_h : heap) : Prop :=
  exists final_policies,
    private_frame_join_policies_metadata_eq final_policies initial_policies /\
    frozen_caller_snapshot_list_phase_images_grow
      final_policies.(suspended_frame_resume_witnesses)
      initial_policies.(suspended_frame_resume_witnesses) /\
    private_policy_statement_result CT P Z cutoff authority final_senv
      final_renv stack incoming initial_snapshots final_snapshots
      final_policies final_h /\
    private_resume_witnesses_cover_snapshots Z
      final_policies.(suspended_frame_resume_witnesses) final_snapshots /\
    private_resume_witnesses_phase_wf CT final_h
      (mk_watched_frame authority final_senv final_renv)
      final_policies.(suspended_frame_resume_witnesses) final_snapshots /\
    private_resume_witnesses_roots_safe CT final_h Z
      (mk_watched_frame authority final_senv final_renv)
      final_policies.(suspended_frame_resume_witnesses) final_snapshots /\
    private_resume_witnesses_nested_resume_safe Z
      final_policies.(suspended_frame_resume_witnesses) final_snapshots /\
    private_resume_witnesses_completed_safe CT final_h Z
      (mk_watched_frame authority final_senv final_renv) incoming
      final_policies.(suspended_frame_resume_witnesses) final_snapshots /\
    private_resume_witness_stack_safe CT final_h Z
      (mk_watched_frame authority final_senv final_renv) incoming
      final_policies.(suspended_frame_resume_witnesses) /\
    frozen_caller_snapshots_before_boundaries
      final_policies.(suspended_frame_resume_witnesses) stack /\
    private_resume_witness_temporal_state CT final_h Z cutoff
      (mk_watched_frame authority final_senv final_renv) stack
      final_policies.(suspended_frame_resume_witnesses) /\
    private_target_witness_state CT final_h Z cutoff
      (mk_watched_frame authority final_senv final_renv) incoming
      final_snapshots final_policies.(suspended_frame_target_witnesses)
      final_policies.(suspended_frame_resume_witnesses)
      stack.

Lemma repeat_none_snapshots_executing_overlap_justified :
  forall CT h Z active incoming count,
    frozen_caller_snapshots_executing_overlap_justified CT h Z active incoming
      (repeat None count).
Proof.
  intros CT h Z active incoming count snapshot snapshot_mode active_mode
    location Hsnapshot. apply repeat_spec in Hsnapshot. discriminate.
Qed.

Lemma executing_authority_color_set_monotone :
  forall CT h active smaller larger,
    Included authority_flow_state smaller larger ->
    Included authority_flow_state
      (executing_authority_color_set CT h active smaller)
      (executing_authority_color_set CT h active larger).
Proof.
  intros CT h active smaller larger Hincluded.
  unfold executing_authority_color_set.
  eapply phased_authority_frame_closure_monotone.
  intros state Hstate. inversion Hstate; subst.
  - left. apply Hincluded. exact H.
  - right. exact H.
Qed.

(** The origin-or-safe overlap certificate is stable under the root descent
    performed by assignment and local declaration.  This is the generic
    transport lemma used by both atomic cases: post-step snapshot and active
    colors reflect to the pre-step phase, while the safe-exposure branch is
    transported by the corresponding exposure reflection. *)
Lemma frozen_active_overlap_justified_after_active_descent :
  forall CT h Z authority incoming old_senv old_renv new_senv new_renv
    snapshots,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame authority new_senv new_renv))
      (phase_frame_capability_set CT h
        (mk_watched_frame authority old_senv old_renv)) ->
    frozen_caller_snapshots_closed CT h
      (mk_watched_frame authority old_senv old_renv) snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame authority old_senv old_renv) snapshots ->
    frozen_caller_snapshots_executing_overlap_justified CT h Z
      (mk_watched_frame authority old_senv old_renv) incoming snapshots ->
    frozen_caller_snapshots_executing_overlap_justified CT h Z
      (mk_watched_frame authority new_senv new_renv) incoming
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) snapshots).
Proof.
  intros CT h Z authority incoming old_senv old_renv new_senv new_renv snapshots
    Hdescend Howned Hclosed Hexposure Hoverlap new_snapshot snapshot_mode
    active_mode location Hnew Hsnapshot_mode Hactive_mode Hsnapshot_color
    Htrigger.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  have Hold_snapshot_color : In authority_flow_state
      old_snapshot.(frozen_snapshot_current_colors)
      (snapshot_mode, location).
  { eapply Hclosed; [exact Hold|].
    destruct Hsnapshot_color as [seed [Hseed Hpath]].
    exists seed. split; [exact Hseed|].
    eapply frozen_caller_connected_after_descent_reflects; eauto. }
  have Hresult :
      (exists root_mode root,
        authority_mode_dangerous root_mode /\
        In authority_flow_state
          old_snapshot.(frozen_snapshot_current_colors) (root_mode, root) /\
        In Loc old_snapshot.(frozen_snapshot_resume_rdm_roots) root) \/
      frozen_snapshot_resume_exposure_avoids Z old_snapshot.
  { destruct Htrigger as [Hactive | Hrdm].
    - have Hold_active : In authority_flow_state
      (executing_authority_color_set CT h
            (mk_watched_frame authority old_senv old_renv) incoming)
          (active_mode, location).
      { eapply executing_authority_colors_after_active_descent_included;
          eauto. }
      exact (Hoverlap old_snapshot snapshot_mode active_mode location Hold
        Hsnapshot_mode Hactive_mode Hold_snapshot_color
        (or_introl Hold_active)).
    - destruct (Hdescend location Hrdm) as
        [old_root [Hold_root Hreachable]].
      have Hold_root_color : In authority_flow_state
          old_snapshot.(frozen_snapshot_current_colors)
          (FlowProspective, old_root).
      { eapply Hclosed; [exact Hold|].
        exists (snapshot_mode, location). split.
        - exact Hold_snapshot_color.
        - destruct Hsnapshot_mode as [-> | ->].
          + eapply frozen_caller_powered_mutable_reverse. exact Hreachable.
          + eapply frozen_caller_prospective_mutable_reverse.
            exact Hreachable. }
      exact (Hoverlap old_snapshot FlowProspective active_mode old_root Hold
        (or_intror eq_refl) Hactive_mode Hold_root_color
        (or_intror Hold_root)). }
  destruct Hresult as [Horigin | Hsafe].
  - left. destruct Horigin as
      [root_mode [root [Hroot_mode [Hroot_color Hroot]]]].
    exists root_mode, root. repeat split; try assumption.
    apply frozen_caller_authority_closure_contains. exact Hroot_color.
  - right. intros exposure_mode target Hexposure_mode Htarget.
    destruct Htarget as [seed [Hseed Hpath]].
    eapply Hsafe; [exact Hexposure_mode|].
    eapply (proj1 (proj2 Hexposure)); [exact Hold|].
    exists seed. split; [exact Hseed|].
    eapply frozen_caller_connected_after_descent_reflects; eauto.
Qed.

(** Heap changes that only remove authority edges transport the overlap
    certificate by reflection. *)
Lemma frozen_active_overlap_justified_after_graph_reflection :
  forall CT old_h new_h Z active incoming snapshots,
    (forall left right,
      retained_mut_edge CT new_h left right ->
      retained_mut_edge CT old_h left right) ->
    (forall left right,
      mutable_edge CT new_h left right ->
      mutable_edge CT old_h left right) ->
    (forall location,
      frame_owned_location CT new_h active location ->
      frame_owned_location CT old_h active location) ->
    frozen_caller_snapshots_closed CT old_h active snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT old_h active snapshots ->
    frozen_caller_snapshots_executing_overlap_justified CT old_h Z active
      incoming snapshots ->
    frozen_caller_snapshots_executing_overlap_justified CT new_h Z active
      incoming
      (advance_frozen_caller_snapshots CT new_h active snapshots).
Proof.
  intros CT old_h new_h Z active incoming snapshots Hretained Hmutable Howned Hclosed
    Hexposure Hoverlap new_snapshot snapshot_mode active_mode location Hnew
    Hsnapshot_mode Hactive_mode Hsnapshot_color Htrigger.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  have Hcolors := advance_frozen_caller_snapshot_after_graph_reflection_included
    CT old_h new_h active old_snapshot Hretained Hmutable Howned
    (Hclosed old_snapshot Hold).
  have Hold_color := Hcolors (snapshot_mode, location) Hsnapshot_color.
  have Hresult :
      (exists root_mode root,
        authority_mode_dangerous root_mode /\
        In authority_flow_state
          old_snapshot.(frozen_snapshot_current_colors) (root_mode, root) /\
        In Loc old_snapshot.(frozen_snapshot_resume_rdm_roots) root) \/
      frozen_snapshot_resume_exposure_avoids Z old_snapshot.
  { destruct Htrigger as [Hactive_color | Hrdm].
    - have Hold_active : exists old_mode,
          authority_mode_dangerous old_mode /\
          In authority_flow_state
            (executing_authority_color_set CT old_h active incoming)
            (old_mode, location).
      { eapply executing_authority_colors_after_heap_change_covered;
          [| | |exact Hactive_mode|exact Hactive_color].
        - intros owned Hnew_owned. exists FlowPowered. split;
            [left; reflexivity|].
          eapply executing_authority_owned_is_powered. apply Howned.
          exact Hnew_owned.
        - intros old_mode left right Hold_mode Hold_state Hedge.
          exists old_mode. split; [exact Hold_mode|].
          eapply executing_authority_dangerous_retained; eauto.
        - intros old_mode left right Hold_mode Hold_state Hedge.
          exists FlowProspective. split; [right; reflexivity|].
          eapply executing_authority_dangerous_reverse_rdm; eauto. }
      destruct Hold_active as [old_mode [Hold_mode Hold_active]].
      exact (Hoverlap old_snapshot snapshot_mode old_mode location Hold
        Hsnapshot_mode Hold_mode Hold_color (or_introl Hold_active)).
    - exact (Hoverlap old_snapshot snapshot_mode active_mode location Hold
        Hsnapshot_mode Hactive_mode Hold_color (or_intror Hrdm)). }
  destruct Hresult as [Horigin | Hsafe].
  - left. destruct Horigin as
      [root_mode [root [Hroot_mode [Hroot_color Hroot]]]].
    exists root_mode, root. repeat split; try assumption.
    apply frozen_caller_authority_closure_contains. exact Hroot_color.
  - right. intros exposure_mode target Hexposure_mode Htarget.
    eapply Hsafe; [exact Hexposure_mode|].
    eapply frozen_caller_closure_after_graph_reflection_included;
      [exact Hretained|exact Hmutable| |exact Htarget].
    exact ((proj1 (proj2 Hexposure)) old_snapshot Hold).
Qed.

(** A legal new field edge may create overlap only through active-frame
    authority.  The generic old-or-fallback closure records that event as
    the existing origin-or-safe certificate; latent exposure uses the same
    directional old-or-active argument and active separation. *)
Lemma frozen_active_overlap_justified_after_safe_field_update :
  forall CT h Z frame incoming snapshots lx old field written,
    runtime_getObj h lx = Some old ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_closed CT h frame snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h frame snapshots ->
    authority_colors_runtime_mutable h
      (executing_authority_color_set CT h frame incoming) ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (executing_authority_color_set CT h frame incoming)
        (active_mode, location) ->
      ~ In Loc Z location) ->
    authority_safe_field_endpoints CT h frame lx written ->
    frozen_caller_snapshots_executing_overlap_justified CT h Z frame incoming
      snapshots ->
    frozen_caller_snapshots_executing_overlap_justified CT
      (update_field h lx field (Iot written)) Z frame incoming
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame snapshots).
Proof.
  intros CT h Z frame incoming snapshots lx old field written Hobj Hruntime Hclosed
    Hexposure Hactive_runtime Hactive_safe Hendpoints Hoverlap new_snapshot
    snapshot_mode active_mode location Hnew Hsnapshot_mode Hactive_mode
    Hsnapshot_color Htrigger.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  have Hcovered :=
    advance_frozen_caller_snapshot_after_safe_field_update_covered_by_old_or_origin
      CT h frame old_snapshot
      ((exists root_mode root,
          authority_mode_dangerous root_mode /\
          In authority_flow_state
            old_snapshot.(frozen_snapshot_current_colors)
            (root_mode, root) /\
          In Loc old_snapshot.(frozen_snapshot_resume_rdm_roots) root) \/
        frozen_snapshot_resume_exposure_avoids Z old_snapshot)
      lx old field written Hobj (Hruntime old_snapshot Hold)
      (Hclosed old_snapshot Hold) Hendpoints
      (fun old_snapshot_mode old_active_mode old_location
        Hold_snapshot_mode Hold_active_mode Hold_color Hold_trigger =>
        Hoverlap old_snapshot old_snapshot_mode old_active_mode old_location
          Hold Hold_snapshot_mode Hold_active_mode Hold_color
          (ltac:(destruct Hold_trigger as [Hactive | Hroot];
            [left; eapply independent_active_authority_colors_in_executing;
              exact Hactive
            |right; exact Hroot])))
      snapshot_mode location Hsnapshot_mode Hsnapshot_color.
  have Hresult :
      (exists root_mode root,
        authority_mode_dangerous root_mode /\
        In authority_flow_state
          old_snapshot.(frozen_snapshot_current_colors) (root_mode, root) /\
        In Loc old_snapshot.(frozen_snapshot_resume_rdm_roots) root) \/
      frozen_snapshot_resume_exposure_avoids Z old_snapshot.
  { destruct Hcovered as
      [[old_snapshot_mode [Hold_snapshot_mode Hold_color]] | Hfallback];
      [|exact Hfallback].
    destruct Htrigger as [Hactive_color | Hrdm].
    - destruct (executing_authority_colors_after_safe_field_update_covered CT
        h frame incoming lx old field written Hobj
        Hactive_runtime Hendpoints active_mode location Hactive_mode
        Hactive_color) as [old_active_mode [Hold_active_mode Hold_active]].
      exact (Hoverlap old_snapshot old_snapshot_mode old_active_mode location
        Hold Hold_snapshot_mode Hold_active_mode Hold_color
        (or_introl Hold_active)).
    - exact (Hoverlap old_snapshot old_snapshot_mode active_mode location Hold
        Hold_snapshot_mode Hactive_mode Hold_color (or_intror Hrdm)). }
  destruct Hresult as [Horigin | Hsafe].
  - left. destruct Horigin as
      [root_mode [root [Hroot_mode [Hroot_color Hroot]]]].
    exists root_mode, root. repeat split; try assumption.
    apply frozen_caller_authority_closure_contains. exact Hroot_color.
  - right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
    have Hindependent_runtime : authority_colors_runtime_mutable h
        (independent_active_authority_colors CT h frame).
    { intros mode root Hcolor. eapply Hactive_runtime.
      eapply independent_active_authority_colors_in_executing. exact Hcolor. }
    have Hindependent_safe : forall active_mode location,
        authority_mode_dangerous active_mode ->
        In authority_flow_state
          (independent_active_authority_colors CT h frame)
          (active_mode, location) ->
        ~ In Loc Z location.
    { intros mode root Hmode Hcolor. eapply Hactive_safe; [exact Hmode|].
      eapply independent_active_authority_colors_in_executing. exact Hcolor. }
    destruct Htarget as [seed [Hseed Hpath]].
    have Hsource : frozen_authority_state_covered_by_old_or_active
        old_snapshot.(frozen_snapshot_current_resume_exposure)
        (independent_active_authority_colors CT h frame) seed.
    { intros Hseed_mode. left. exists (fst seed). split.
      - exact Hseed_mode.
      - destruct seed. exact Hseed. }
    have Htarget_covered :=
      frozen_caller_connected_after_safe_field_update_covered_by_old_or_active
        CT h frame old_snapshot.(frozen_snapshot_current_resume_exposure)
        lx old field written seed (exposure_mode, target) Hobj
        ((proj1 Hexposure) old_snapshot Hold)
        ((proj1 (proj2 Hexposure)) old_snapshot Hold) Hindependent_runtime
        Hendpoints Hsource Hpath Hexposure_mode.
    destruct Htarget_covered as
      [[old_mode [Hold_mode Hold_target]] |
       [old_active_mode [Hold_active_mode Hold_active]]].
    + eapply Hsafe; eauto.
    + eapply Hindependent_safe; eauto.
Qed.

(** Allocation preserves the overlap certificate.  Old post-allocation
    colors reflect to the pre-allocation phase.  A color reached through an
    allocation root is justified at that root (or ruled out by immutable
    runtime mutability), exactly as in the origin-only proof.  The safe
    alternative is lifted by [frozen_snapshot_resume_exposure_avoids_after_new]. *)
Lemma frozen_active_overlap_justified_after_new :
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
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    vpa_mutability_object_creation qreceiver qc = qruntime ->
    cutoff <= dom h ->
    protected_zone_before_cutoff Z cutoff ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_closed CT h
      (mk_watched_frame authority sGamma rGamma) snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame authority sGamma rGamma) snapshots ->
    authority_colors_runtime_mutable h incoming ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (executing_authority_color_set CT h
          (mk_watched_frame authority sGamma rGamma) incoming)
        (active_mode, location) ->
      ~ In Loc Z location) ->
    frozen_caller_snapshots_executing_overlap_justified CT h Z
      (mk_watched_frame authority sGamma rGamma) incoming snapshots ->
    frozen_caller_snapshots_executing_overlap_justified CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) Z
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h)))) incoming
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) snapshots).
Proof.
  intros CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qreceiver qruntime authority incoming snapshots Hwf Hpost_wf Hsound Hpost_sound
    Htyping Hvals Hadapt Hcutoff Hzone Hruntime Hclosed Hexposure
    Hincoming_runtime Hactive_safe Hoverlap new_snapshot snapshot_mode active_mode location Hnew
    Hsnapshot_mode Hactive_mode Hsnapshot_color Htrigger.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  have Hcovered := advance_frozen_caller_snapshot_after_new_covered CT sGamma
    mt rGamma h x qc C args sGamma' vals qruntime authority old_snapshot
    snapshot_mode location Hwf Htyping Hvals (Hruntime old_snapshot Hold)
    (Hclosed old_snapshot Hold) Hsnapshot_mode Hsnapshot_color.
  set (advanced := advance_frozen_caller_snapshot CT
    (h ++ [mkObj (mkruntime_type qruntime C) vals])
    (mk_watched_frame authority sGamma'
      (update_r_env_value rGamma x (Iot (dom h)))) old_snapshot).
  assert (Hlift :
      (frozen_snapshot_has_resume_origin old_snapshot \/
       frozen_snapshot_resume_exposure_avoids Z old_snapshot) ->
      (frozen_snapshot_has_resume_origin advanced \/
       frozen_snapshot_resume_exposure_avoids Z advanced)).
  { intros [Horigin | Hsafe].
    - left. destruct Horigin as
        [root_mode [root [Hroot_mode [Hroot_color Hroot]]]].
      unfold frozen_snapshot_has_resume_origin in *.
      exists root_mode, root. repeat split; try assumption.
      apply frozen_caller_authority_closure_contains. exact Hroot_color.
    - right. unfold advanced.
      eapply frozen_snapshot_resume_exposure_avoids_after_new; eauto.
      + exact ((proj1 Hexposure) old_snapshot Hold).
      + exact ((proj1 (proj2 Hexposure)) old_snapshot Hold).
      + intros mode root Hmode Hcolor. eapply Hactive_safe; [exact Hmode|].
        eapply independent_active_authority_colors_in_executing.
        exact Hcolor. }
  destruct Hcovered as
    [[old_snapshot_mode [Hold_snapshot_mode Hold_snapshot_color]] |
     [creation_mode [creation_root
       [Hcreation_mode [Hcreation_color Hcreation_root]]]]].
  - destruct Htrigger as [Hactive_color | Hrdm].
    + have Hlocation_old : location < dom h.
      { eapply r_muttype_some_dom. eapply Hruntime; eauto. }
      destruct (executing_authority_colors_after_new_covered CT sGamma mt
        rGamma h x qc C args sGamma' vals qreceiver qruntime authority
        incoming Hwf Hpost_wf Hsound Hpost_sound
        Hincoming_runtime Htyping Hvals Hadapt active_mode location Hactive_mode
        Hactive_color Hlocation_old) as
        [old_active_mode [Hold_active_mode Hold_active_color]].
      apply Hlift.
      exact (Hoverlap old_snapshot old_snapshot_mode old_active_mode location
        Hold Hold_snapshot_mode Hold_active_mode Hold_snapshot_color
        (or_introl Hold_active_color)).
    + destruct (new_active_rdm_root_origin CT sGamma mt rGamma h x qc C args
        sGamma' location Hwf Htyping Hrdm) as
        [Hold_rdm | [Hfresh Hrdm_creation]].
      * apply Hlift.
        exact (Hoverlap old_snapshot old_snapshot_mode active_mode location
          Hold Hold_snapshot_mode Hactive_mode Hold_snapshot_color
          (or_intror Hold_rdm)).
      * subst location qc.
        have Hfresh_runtime := Hruntime old_snapshot Hold old_snapshot_mode
          (dom h) Hold_snapshot_color.
        have Hdom := r_muttype_some_dom h (dom h) Mut_r Hfresh_runtime. lia.
  - destruct qc; simpl in Hcreation_root.
    + have Howned : frame_owned_location CT h
          (mk_watched_frame authority sGamma rGamma) creation_root.
      { apply frame_owned_location_iff_active_live.
        eapply typed_mut_root_is_live_capability. exact Hcreation_root. }
      have Hactive_color : In authority_flow_state
          (independent_active_authority_colors CT h
            (mk_watched_frame authority sGamma rGamma))
          (FlowPowered, creation_root).
      { unfold independent_active_authority_colors.
        apply executing_authority_owned_is_powered. exact Howned. }
      apply Hlift.
      exact (Hoverlap old_snapshot creation_mode FlowPowered creation_root
        Hold Hcreation_mode (or_introl eq_refl) Hcreation_color
        (or_introl (independent_active_authority_colors_in_executing CT h
          (mk_watched_frame authority sGamma rGamma) incoming
          (FlowPowered, creation_root) Hactive_color))).
    + have Hmut := Hruntime old_snapshot Hold creation_mode creation_root
        Hcreation_color.
      have Himm := typed_imm_root_runtime_immutable CT sGamma rGamma h
        creation_root Hwf Hcreation_root.
      rewrite Himm in Hmut. discriminate.
    + apply Hlift.
      exact (Hoverlap old_snapshot creation_mode active_mode creation_root
        Hold Hcreation_mode Hactive_mode Hcreation_color
        (or_intror Hcreation_root)).
Qed.

(** A globally safe latent resume exposure remains safe while entering a
    typed call.  Every dangerous callee color with that exposure as incoming
    reflects either to the old exposure or to independent caller authority;
    both alternatives avoid the protected zone. *)
Lemma frozen_snapshot_resume_exposure_avoids_after_safe_call_entry :
  forall CT Z caller_authority sGamma mt rGamma h caller_incoming snapshot
    x method y args sGamma' vals ly cy runtime_mdef Ty,
    wf_r_config CT sGamma rGamma h ->
    authority_context_sound h rGamma caller_authority ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    authority_colors_runtime_mutable h
      snapshot.(frozen_snapshot_current_resume_exposure) ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h
        (mk_watched_frame caller_authority sGamma rGamma)
        snapshot.(frozen_snapshot_current_resume_exposure))
      snapshot.(frozen_snapshot_current_resume_exposure) ->
    frozen_snapshot_resume_exposure_avoids Z snapshot ->
    executing_authority_colors_separated CT h Z
      (mk_watched_frame caller_authority sGamma rGamma) caller_incoming ->
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_snapshot_resume_exposure_avoids Z
      (advance_frozen_caller_snapshot CT h callee snapshot).
Proof.
  intros CT Z caller_authority sGamma mt rGamma h caller_incoming snapshot
    x method y args sGamma' vals ly cy runtime_mdef Ty Hwf Hsound Htyping
    Hscope Hgety Hvalue Hbase Hfind Hargs Hruntime Hclosed Hsafe Hseparated
    callee mode location Hmode Hcolor Hprotected.
  have Hcallee_color : In authority_flow_state
      (executing_authority_color_set CT h callee
        (executing_authority_color_set CT h
          (mk_watched_frame caller_authority sGamma rGamma)
          snapshot.(frozen_snapshot_current_resume_exposure)))
      (mode, location).
  { destruct Hcolor as [seed [Hseed Hpath]]. exists seed. split.
    - left. apply executing_authority_color_set_contains_incoming.
      exact Hseed.
    - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
  destruct (executing_authority_colors_enter_call_covered CT
    caller_authority sGamma mt rGamma h x method y args sGamma' vals ly cy
    runtime_mdef Ty snapshot.(frozen_snapshot_current_resume_exposure)
    Hwf Hsound Hruntime Htyping Hscope Hgety Hvalue Hbase Hfind Hargs mode
    location Hmode Hcallee_color) as
    [caller_mode [Hcaller_mode Hcaller_color]].
  destruct (executing_with_frozen_incoming_dangerous_covered_by_old_or_active
    CT h (mk_watched_frame caller_authority sGamma rGamma)
    snapshot.(frozen_snapshot_current_resume_exposure) caller_mode location
    Hclosed Hcaller_mode Hcaller_color) as
    [[old_mode [Hold_mode Hold_color]] |
     [active_mode [Hactive_mode Hactive_color]]].
  - exact (Hsafe old_mode location Hold_mode Hold_color Hprotected).
  - eapply Hseparated; [exact Hactive_mode| |exact Hprotected].
    eapply independent_active_authority_colors_in_executing.
    exact Hactive_color.
Qed.

(** Ordinary typed call entry transports the full origin-or-safe overlap
    certificate for every older snapshot.  The head [None] is vacuous.  A
    newly closed snapshot color is either old or already carries the old
    fallback; an active callee trigger reflects through class-bounded
    adaptation to caller [Mut], [Imm], or [RDM]. *)
Lemma frozen_active_overlap_justified_after_safe_call_entry :
  forall CT Z caller_authority sGamma mt rGamma h caller_incoming snapshots
    x method y args sGamma' vals ly cy runtime_mdef Ty,
    wf_r_config CT sGamma rGamma h ->
    authority_context_sound h rGamma caller_authority ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_closed CT h
      (mk_watched_frame caller_authority sGamma rGamma) snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame caller_authority sGamma rGamma) snapshots ->
    authority_colors_runtime_mutable h caller_incoming ->
    executing_authority_colors_separated CT h Z
      (mk_watched_frame caller_authority sGamma rGamma) caller_incoming ->
    frozen_caller_snapshots_executing_overlap_justified CT h Z
      (mk_watched_frame caller_authority sGamma rGamma) caller_incoming
      snapshots ->
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_caller_snapshots_executing_overlap_justified CT h Z callee
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) caller_incoming)
      (None :: advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT Z caller_authority sGamma mt rGamma h caller_incoming snapshots
    x method y args sGamma' vals ly cy runtime_mdef Ty Hwf Hsound Htyping
    Hscope Hgety Hvalue Hbase Hfind Hargs Hruntime Hclosed Hexposure
    Hincoming_runtime Hseparated Hoverlap callee new_snapshot snapshot_mode active_mode location
    Hnew Hsnapshot_mode Hactive_mode Hsnapshot_color Htrigger.
  simpl in Hnew. destruct Hnew as [Hnone | Hnew]; [discriminate|].
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in *.
  set (fallback := frozen_snapshot_has_resume_origin old_snapshot \/
    frozen_snapshot_resume_exposure_avoids Z old_snapshot).
  have Hsnapshot_case :
      (exists old_mode,
        authority_mode_dangerous old_mode /\
        In authority_flow_state old_snapshot.(frozen_snapshot_current_colors)
          (old_mode, location)) \/ fallback.
  { destruct Hsnapshot_color as [seed [Hseed Hpath]].
    have Hseed_covered : frozen_state_covered_by_old_or old_snapshot fallback
        seed.
    { unfold frozen_state_covered_by_old_or. intros Hseed_mode.
      left. exists (fst seed). split.
      - exact Hseed_mode.
      - destruct seed. exact Hseed. }
    have Hfinal_covered :=
      safe_call_frozen_connected_covered_by_old_or_resume_origin CT
        caller_authority sGamma mt rGamma h x method y args sGamma' vals ly
        cy runtime_mdef Ty old_snapshot fallback seed
        (snapshot_mode, location) Hwf Htyping Hscope Hgety Hvalue Hbase Hfind
        Hargs (Hruntime old_snapshot Hold) (Hclosed old_snapshot Hold)
        (fun old_mode caller_mode old_location Hold_mode Hcaller_mode
          Hold_color Hcaller_trigger =>
          Hoverlap old_snapshot old_mode caller_mode old_location Hold
            Hold_mode Hcaller_mode Hold_color
            (ltac:(destruct Hcaller_trigger as [Hactive | Hroot];
              [left; eapply independent_active_authority_colors_in_executing;
                exact Hactive
              |right; exact Hroot])))
        Hseed_covered Hpath.
    exact (Hfinal_covered Hsnapshot_mode). }
  assert (Hlift : fallback ->
      frozen_snapshot_has_resume_origin
        (advance_frozen_caller_snapshot CT h callee old_snapshot) \/
      frozen_snapshot_resume_exposure_avoids Z
        (advance_frozen_caller_snapshot CT h callee old_snapshot)).
  { unfold fallback. intros [Horigin | Hsafe].
    - left. unfold frozen_snapshot_has_resume_origin in *.
      destruct Horigin as
        [root_mode [root [Hroot_mode [Hroot_color Hroot]]]].
      exists root_mode, root. repeat split; try assumption.
      apply frozen_caller_authority_closure_contains. exact Hroot_color.
    - right. eapply frozen_snapshot_resume_exposure_avoids_after_safe_call_entry;
        eauto.
      + exact ((proj1 Hexposure) old_snapshot Hold).
      + exact ((proj1 (proj2 Hexposure)) old_snapshot Hold). }
  destruct Hsnapshot_case as
    [[old_mode [Hold_mode Hold_color]] | Hfallback]; [|exact (Hlift Hfallback)].
  have Hcaller_result : fallback.
  { destruct Htrigger as [Hactive | Hrdm].
    - destruct (executing_authority_colors_enter_call_covered CT
        caller_authority sGamma mt rGamma h x method y args sGamma' vals ly
        cy runtime_mdef Ty caller_incoming Hwf Hsound
        Hincoming_runtime Htyping Hscope
        Hgety Hvalue Hbase Hfind Hargs active_mode location Hactive_mode
        Hactive) as [caller_mode [Hcaller_mode Hcaller_color]].
      unfold fallback.
      exact (Hoverlap old_snapshot old_mode caller_mode location Hold
        Hold_mode Hcaller_mode Hold_color (or_introl Hcaller_color)).
    - destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x
        method y args sGamma' vals ly cy runtime_mdef location Hwf Htyping
        Hscope Hvalue Hbase Hfind Hargs Hrdm) as
        [caller_T [Hcaller_type [Hshape Hcaller_root]]].
      assert (caller_T = Ty) by congruence. subst caller_T.
      destruct Hshape as [Hmut | [Himm | Hcaller_rdm]].
      + have Hcaller_color : In authority_flow_state
            (independent_active_authority_colors CT h
              (mk_watched_frame caller_authority sGamma rGamma))
            (FlowPowered, location).
        { unfold independent_active_authority_colors.
          eapply executing_authority_typed_mut_root_is_powered.
          rewrite Hmut in Hcaller_root. exact Hcaller_root. }
        unfold fallback.
        exact (Hoverlap old_snapshot old_mode FlowPowered location Hold
          Hold_mode (or_introl eq_refl) Hold_color
          (or_introl (independent_active_authority_colors_in_executing CT h
            (mk_watched_frame caller_authority sGamma rGamma)
            caller_incoming (FlowPowered, location) Hcaller_color))).
      + have Hmutable := Hruntime old_snapshot Hold old_mode location
          Hold_color.
        have Himmutable := typed_imm_root_runtime_immutable CT sGamma rGamma
          h location Hwf
          (ltac:(rewrite Himm in Hcaller_root; exact Hcaller_root)).
        congruence.
      + unfold fallback.
        exact (Hoverlap old_snapshot old_mode active_mode location Hold
          Hold_mode Hactive_mode Hold_color
          (or_intror (ltac:(rewrite Hcaller_rdm in Hcaller_root;
            exact Hcaller_root)))). }
  exact (Hlift Hcaller_result).
Qed.

Lemma frozen_caller_snapshots_runtime_mutable_tail :
  forall h slot tail,
    frozen_caller_snapshots_runtime_mutable h (slot :: tail) ->
    frozen_caller_snapshots_runtime_mutable h tail.
Proof. intros h slot tail H snapshot Hin. eapply H. right. exact Hin. Qed.

Lemma frozen_caller_snapshots_closed_tail :
  forall CT h active slot tail,
    frozen_caller_snapshots_closed CT h active (slot :: tail) ->
    frozen_caller_snapshots_closed CT h active tail.
Proof. intros CT h active slot tail H snapshot Hin. eapply H. right. exact Hin. Qed.

Lemma frozen_caller_snapshots_resume_exposures_wf_tail :
  forall CT h active slot tail,
    frozen_caller_snapshots_resume_exposures_wf CT h active (slot :: tail) ->
    frozen_caller_snapshots_resume_exposures_wf CT h active tail.
Proof.
  intros CT h active slot tail
    (Hruntime & Hclosed & Hdangerous & Hentry & Hroots).
  repeat split; intros; eauto using in_cons.
Qed.

Lemma private_policy_head_overlap_after_active_descent :
  forall CT h Z authority old_senv old_renv new_senv new_renv witnesses,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame authority new_senv new_renv))
      (phase_frame_capability_set CT h
        (mk_watched_frame authority old_senv old_renv)) ->
    frozen_caller_snapshots_closed CT h
      (mk_watched_frame authority old_senv old_renv) witnesses ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame authority old_senv old_renv) witnesses ->
    private_policy_head_active_overlap_justified CT h Z
      (mk_watched_frame authority old_senv old_renv) witnesses ->
    private_policy_head_active_overlap_justified CT h Z
      (mk_watched_frame authority new_senv new_renv)
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) witnesses).
Proof.
  intros CT h Z authority old_senv old_renv new_senv new_renv witnesses
    Hdescend Howned Hclosed Hexposure Hoverlap.
  induction witnesses as [|slot tail IH].
  - exact I.
  - destruct slot as [head|].
    + change (frozen_caller_snapshots_active_overlap_justified CT h Z
      (mk_watched_frame authority old_senv old_renv) (Some head :: tail))
      in Hoverlap.
      change (frozen_caller_snapshots_active_overlap_justified CT h Z
      (mk_watched_frame authority new_senv new_renv)
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv)
        (Some head :: tail))).
      eapply frozen_active_overlap_justified_after_active_descent with
        (incoming := Empty_set authority_flow_state); eauto.
    + simpl in Hoverlap |- *.
      eapply IH; eauto using frozen_caller_snapshots_closed_tail,
        frozen_caller_snapshots_resume_exposures_wf_tail.
Qed.

Lemma private_policy_head_overlap_after_graph_reflection :
  forall CT old_h new_h Z active witnesses,
    (forall left right,
      retained_mut_edge CT new_h left right ->
      retained_mut_edge CT old_h left right) ->
    (forall left right,
      mutable_edge CT new_h left right ->
      mutable_edge CT old_h left right) ->
    (forall location,
      frame_owned_location CT new_h active location ->
      frame_owned_location CT old_h active location) ->
    frozen_caller_snapshots_closed CT old_h active witnesses ->
    frozen_caller_snapshots_resume_exposures_wf CT old_h active witnesses ->
    private_policy_head_active_overlap_justified CT old_h Z active witnesses ->
    private_policy_head_active_overlap_justified CT new_h Z active
      (advance_frozen_caller_snapshots CT new_h active witnesses).
Proof.
  intros CT old_h new_h Z active witnesses Hretained Hmutable Howned Hclosed
    Hexposure Hoverlap.
  induction witnesses as [|slot tail IH].
  - exact I.
  - destruct slot as [head|].
    + change (frozen_caller_snapshots_active_overlap_justified CT old_h Z
      active (Some head :: tail)) in Hoverlap.
      change (frozen_caller_snapshots_active_overlap_justified CT new_h Z
      active (advance_frozen_caller_snapshots CT new_h active
        (Some head :: tail))).
      eapply frozen_active_overlap_justified_after_graph_reflection with
        (incoming := Empty_set authority_flow_state); eauto.
    + simpl in Hoverlap |- *.
      eapply IH; eauto using frozen_caller_snapshots_closed_tail,
        frozen_caller_snapshots_resume_exposures_wf_tail.
Qed.

Lemma private_policy_head_overlap_after_safe_field_update :
  forall CT h Z frame witnesses lx old field written,
    runtime_getObj h lx = Some old ->
    frozen_caller_snapshots_runtime_mutable h witnesses ->
    frozen_caller_snapshots_closed CT h frame witnesses ->
    frozen_caller_snapshots_resume_exposures_wf CT h frame witnesses ->
    authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h frame) ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h frame)
        (active_mode, location) ->
      ~ In Loc Z location) ->
    authority_safe_field_endpoints CT h frame lx written ->
    private_policy_head_active_overlap_justified CT h Z frame witnesses ->
    private_policy_head_active_overlap_justified CT
      (update_field h lx field (Iot written)) Z frame
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame witnesses).
Proof.
  intros CT h Z frame witnesses lx old field written Hobj Hruntime Hclosed
    Hexposure Hactive_runtime Hactive_safe Hendpoints Hoverlap.
  induction witnesses as [|slot tail IH].
  - exact I.
  - destruct slot as [head|].
    + change (frozen_caller_snapshots_active_overlap_justified CT h Z frame
      (Some head :: tail)) in Hoverlap.
      change (frozen_caller_snapshots_active_overlap_justified CT
      (update_field h lx field (Iot written)) Z frame
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame (Some head :: tail))).
      eapply frozen_active_overlap_justified_after_safe_field_update with
        (incoming := Empty_set authority_flow_state); eauto.
    + simpl in Hoverlap |- *.
      eapply IH; eauto using frozen_caller_snapshots_runtime_mutable_tail,
        frozen_caller_snapshots_closed_tail,
        frozen_caller_snapshots_resume_exposures_wf_tail.
Qed.

Lemma private_policy_head_overlap_after_new :
  forall CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qreceiver qruntime authority witnesses,
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
    frozen_caller_snapshots_runtime_mutable h witnesses ->
    frozen_caller_snapshots_closed CT h
      (mk_watched_frame authority sGamma rGamma) witnesses ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame authority sGamma rGamma) witnesses ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h
          (mk_watched_frame authority sGamma rGamma))
        (active_mode, location) ->
      ~ In Loc Z location) ->
    private_policy_head_active_overlap_justified CT h Z
      (mk_watched_frame authority sGamma rGamma) witnesses ->
    private_policy_head_active_overlap_justified CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) Z
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h))))
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) witnesses).
Proof.
  intros CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals qreceiver
    qruntime authority witnesses Hwf Hpost_wf Hsound Hpost_sound Htyping
    Hvals Hadapt Hcutoff Hzone Hruntime Hclosed Hexposure Hactive_safe
    Hoverlap.
  induction witnesses as [|slot tail IH].
  - exact I.
  - destruct slot as [head|].
    + change (frozen_caller_snapshots_active_overlap_justified CT h Z
      (mk_watched_frame authority sGamma rGamma) (Some head :: tail))
      in Hoverlap.
      change (frozen_caller_snapshots_active_overlap_justified CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) Z
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h))))
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h))))
        (Some head :: tail))).
      eapply frozen_active_overlap_justified_after_new with
        (incoming := Empty_set authority_flow_state); eauto.
      intros mode location Hempty. inversion Hempty.
    + simpl in Hoverlap |- *.
      eapply IH; eauto using frozen_caller_snapshots_runtime_mutable_tail,
        frozen_caller_snapshots_closed_tail,
        frozen_caller_snapshots_resume_exposures_wf_tail.
Qed.

Lemma frozen_caller_snapshots_active_overlap_justified_tail :
  forall CT h Z active slot tail,
    frozen_caller_snapshots_active_overlap_justified CT h Z active
      (slot :: tail) ->
    frozen_caller_snapshots_active_overlap_justified CT h Z active tail.
Proof.
  intros CT h Z active slot tail H snapshot snapshot_mode active_mode
    location Hin Hsnapshot_mode Hactive_mode Hcolor Htrigger.
  exact (H snapshot snapshot_mode active_mode location (or_intror Hin)
    Hsnapshot_mode Hactive_mode Hcolor Htrigger).
Qed.

Lemma private_policy_head_overlap_after_safe_call_entry :
  forall CT Z caller_authority sGamma mt rGamma h witnesses x method y args
    sGamma' vals ly cy runtime_mdef Ty,
    wf_r_config CT sGamma rGamma h ->
    authority_context_sound h rGamma caller_authority ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    frozen_caller_snapshots_runtime_mutable h witnesses ->
    frozen_caller_snapshots_closed CT h
      (mk_watched_frame caller_authority sGamma rGamma) witnesses ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame caller_authority sGamma rGamma) witnesses ->
    executing_authority_colors_separated CT h Z
      (mk_watched_frame caller_authority sGamma rGamma)
      (Empty_set authority_flow_state) ->
    private_policy_head_active_overlap_justified CT h Z
      (mk_watched_frame caller_authority sGamma rGamma) witnesses ->
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    private_policy_head_active_overlap_justified CT h Z callee
      (None :: advance_frozen_caller_snapshots CT h callee witnesses).
Proof.
  intros CT Z caller_authority sGamma mt rGamma h witnesses x method y args
    sGamma' vals ly cy runtime_mdef Ty Hwf Hsound Htyping Hscope Hgety
    Hvalue Hbase Hfind Hargs Hruntime Hclosed Hexposure Hseparated Hoverlap
    callee.
  induction witnesses as [|slot tail IH].
  - exact I.
  - destruct slot as [head|].
    + simpl.
      eapply frozen_caller_snapshots_active_overlap_justified_tail with
        (slot := None).
      eapply executing_overlap_justified_implies_active_overlap_justified.
      exact (frozen_active_overlap_justified_after_safe_call_entry CT Z
          caller_authority sGamma mt rGamma h
          (Empty_set authority_flow_state) (Some head :: tail)
          x method y args sGamma' vals ly cy runtime_mdef Ty Hwf Hsound Htyping
          Hscope Hgety Hvalue Hbase Hfind Hargs Hruntime Hclosed Hexposure
          (ltac:(intros mode location Hempty; inversion Hempty)) Hseparated
          Hoverlap).
    + simpl in Hoverlap |- *.
      eapply IH.
      * eapply frozen_caller_snapshots_runtime_mutable_tail. exact Hruntime.
      * eapply frozen_caller_snapshots_closed_tail. exact Hclosed.
      * eapply frozen_caller_snapshots_resume_exposures_wf_tail.
        exact Hexposure.
      * exact Hoverlap.
Qed.

Lemma private_policy_statement_state_main :
  forall CT P Z cutoff active stack incoming snapshots policies h,
    private_policy_statement_state CT P Z cutoff active stack incoming
      snapshots policies h ->
    principled_phased_authority_live_history_state CT P Z cutoff active stack
      incoming h.
Proof.
  intros CT P Z cutoff active stack incoming snapshots policies h Hstate.
  exact (proj1 (proj1 (proj1 (proj1 (proj1 Hstate))))).
Qed.

(** The suspended policy witnesses are not merely auxiliary metadata: the
    advancing invariant contains exactly the certificates needed to regard
    them as an ordinary private frozen stack.  Keeping this bridge private
    lets every atomic preservation theorem reuse the mature frozen-state
    transport without strengthening the public preservation interface. *)
Lemma private_advancing_policy_statement_witness_state_is_private_fresh :
  forall CT P Z cutoff active stack incoming snapshots policies h,
    private_advancing_policy_statement_state CT P Z cutoff active stack
      incoming snapshots policies h ->
    private_fresh_frozen_statement_state CT P Z cutoff active stack incoming
      policies.(suspended_frame_resume_witnesses) h.
Proof.
  intros CT P Z cutoff active stack incoming snapshots policies h
    (Hpolicy & Hcover & Hphase & Hroots & Hnested & Hcompleted &
      Hstack_safe & Hbefore & Htemporal & Htarget).
  destruct Hpolicy as [Hprivate [Haligned [Hvalid Hseparated]]].
  eapply private_resume_witness_state_is_private_fresh.
  - exact (proj1 (proj1 (proj1 (proj1 Hprivate)))).
  - unfold frozen_caller_snapshots_aligned.
    exact (proj2 (proj2 Haligned)).
  - exact Hstack_safe.
  - exact Hbefore.
  - exact Htemporal.
Qed.

Lemma private_policy_statement_result_is_state :
  forall CT P Z cutoff authority final_senv final_renv stack incoming
    initial_snapshots final_snapshots policies final_h,
    private_policy_statement_result CT P Z cutoff authority final_senv
      final_renv stack incoming initial_snapshots final_snapshots policies
      final_h ->
    private_policy_statement_state CT P Z cutoff
      (mk_watched_frame authority final_senv final_renv) stack incoming
      final_snapshots policies final_h.
Proof.
  intros CT P Z cutoff authority final_senv final_renv stack incoming
    initial_snapshots final_snapshots policies final_h
    Hresult.
  destruct Hresult as [Hprincipled [Haligned [Hvalid Hseparated]]].
  destruct Hprincipled as [Hstatement Hdisjoint].
  destruct Hstatement as [Hpotential [Hfresh [Hmetadata Hreflection]]].
  split.
  - split; [exact Hfresh|exact Hdisjoint].
  - exact (conj Haligned (conj Hvalid Hseparated)).
Qed.

Lemma private_principled_statement_result_resumed_separated :
  forall CT P Z cutoff authority final_senv final_renv stack incoming
    initial_snapshots final_snapshots policies final_h,
    private_principled_statement_result CT P Z cutoff authority final_senv
      final_renv stack incoming initial_snapshots final_snapshots final_h ->
    executing_resumed_authority_colors_separated CT final_h Z
      policies.(active_frame_join_targets)
      (mk_watched_frame authority final_senv final_renv) incoming.
Proof.
  intros CT P Z cutoff authority final_senv final_renv stack incoming
    initial_snapshots final_snapshots policies final_h
    [[Hpotential [Hprivate [Hmetadata Hreflection]]] Hdisjoint].
  destruct Hprivate as [Hfrozen Hfresh_tail].
  destruct Hfrozen as [Hprincipled Hcertificates].
  have Hmain := proj1 Hprincipled.
  have Hseparated := proj1 (proj2 (proj2 (proj2 Hmain))).
  eapply executing_authority_separation_implies_resumed_separation.
  exact Hseparated.
Qed.

Lemma potential_live_history_starts_private_policy_statement :
  forall CT P Z cutoff authority sGamma rGamma stack h,
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack h ->
    private_policy_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack
      (Empty_set authority_flow_state) (repeat None (length stack))
      (initial_private_frame_join_policies
        (mk_watched_frame authority sGamma rGamma) stack) h.
Proof.
  intros CT P Z cutoff authority sGamma rGamma stack h Hstate.
  split.
  - eapply potential_live_history_starts_private_principled_statement.
    exact Hstate.
  - split.
    + apply initial_private_frame_join_policies_aligned.
    + split.
      * have Hprivate :=
          potential_live_history_starts_private_principled_statement CT P Z
            cutoff authority sGamma rGamma stack h Hstate.
        destruct Hprivate as [[Hfrozen Hfresh_tail] Hdisjoint].
        destruct Hfrozen as [Hprincipled Hcertificates].
        have Hmain := proj1 Hprincipled.
        have Hframes := proj1 (proj2 (proj2 (proj2 (proj2 Hmain)))).
        apply (initial_private_frame_join_policies_valid CT h
          (mk_watched_frame authority sGamma rGamma) stack).
        exact Hframes.
      * have Hprivate :=
          potential_live_history_starts_private_principled_statement CT P Z
            cutoff authority sGamma rGamma stack h Hstate.
        destruct Hprivate as [[Hfrozen Hfresh_tail] Hdisjoint].
        destruct Hfrozen as [Hprincipled Hcertificates].
        have Hmain := proj1 Hprincipled.
        have Hseparated := proj1 (proj2 (proj2 (proj2 Hmain))).
        eapply executing_authority_separation_implies_resumed_separation.
        exact Hseparated.
Qed.

Lemma potential_live_history_starts_private_advancing_policy_statement :
  forall CT P Z cutoff authority sGamma rGamma stack h,
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack h ->
    private_advancing_policy_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack
      (Empty_set authority_flow_state)
      (repeat None (length stack))
      (initial_private_frame_join_policies
        (mk_watched_frame authority sGamma rGamma) stack) h.
Proof.
  intros CT P Z cutoff authority sGamma rGamma stack h Hstate. split.
  - eapply potential_live_history_starts_private_policy_statement.
    exact Hstate.
  - split.
    + unfold initial_private_frame_join_policies. simpl.
      apply repeat_none_resume_witnesses_cover_snapshots.
    + split.
      * unfold initial_private_frame_join_policies. simpl.
        apply repeat_none_resume_witnesses_phase_wf.
      * split.
        -- unfold initial_private_frame_join_policies. simpl.
           apply repeat_none_resume_witnesses_roots_safe.
        -- split.
           ++ unfold initial_private_frame_join_policies. simpl.
              apply repeat_none_resume_witnesses_nested_resume_safe.
           ++ split.
              ** unfold initial_private_frame_join_policies. simpl.
                 apply repeat_none_resume_witnesses_completed_safe.
              ** unfold initial_private_frame_join_policies. simpl.
                 split.
                 { apply repeat_none_resume_witness_stack_safe. }
                 split.
                 { apply repeat_none_snapshots_before_boundaries. }
                 split.
                 { unfold private_resume_witness_temporal_state.
                   repeat split.
                   { apply frozen_caller_snapshots_none_avoid_protected. }
                   { apply frozen_caller_snapshots_none_entry_exposure_covered. }
                   { apply repeat_none_callee_side_components. }
                   { apply repeat_none_callee_side_prospective_components. }
                   { apply repeat_none_snapshot_boundaries_after_cutoff. } }
                 { unfold private_target_witness_state,
                     initial_private_frame_join_policies. simpl.
                   split.
                   { apply repeat_none_resume_witnesses_cover_snapshots. }
                   split.
                   { apply private_target_witness_stack_structural_of_safe
                       with (Z := Z)
                         (incoming := Empty_set authority_flow_state).
                     apply repeat_none_resume_witness_stack_safe. }
                   split.
                   { apply repeat_none_completed_colors_resume_phase_safe. }
                   split.
                   { apply repeat_none_target_exposures_support_resume_phase. }
                   split.
                   { apply (proj2 (frozen_target_nested_phase_safe_iff_legacy
                       CT h Z _)).
                     apply repeat_none_nested_resume_phase_safe. }
                   split.
                   { apply repeat_none_snapshots_before_boundaries. }
                   split.
                   { apply repeat_none_target_supports_resume_witnesses. }
                   split.
                   { apply repeat_none_target_history_supports_resume_phase. }
                   { unfold private_target_witness_temporal_state.
                     apply repeat_none_snapshot_boundaries_after_cutoff. } }
Qed.

Lemma private_policy_statement_result_from_principled :
  forall CT P Z cutoff authority final_senv final_renv stack incoming
    initial_snapshots final_snapshots policies final_h,
    private_principled_statement_result CT P Z cutoff authority final_senv
      final_renv stack incoming initial_snapshots final_snapshots final_h ->
    private_frame_join_policies_aligned policies stack ->
    private_frame_join_policies_valid final_h policies stack ->
    private_policy_statement_result CT P Z cutoff authority final_senv
      final_renv stack incoming initial_snapshots final_snapshots policies
      final_h.
Proof.
  intros CT P Z cutoff authority final_senv final_renv stack incoming
    initial_snapshots final_snapshots policies final_h Hresult Haligned Hvalid.
  split; [exact Hresult|]. split; [exact Haligned|]. split; [exact Hvalid|].
  eapply private_principled_statement_result_resumed_separated.
  exact Hresult.
Qed.

Lemma private_policy_statement_result_refl :
  forall CT P Z cutoff authority sGamma rGamma stack incoming snapshots
    policies h,
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming h ->
    private_policy_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots
      policies h ->
    private_policy_statement_result CT P Z cutoff authority sGamma rGamma
      stack incoming snapshots snapshots policies h.
Proof.
  intros CT P Z cutoff authority sGamma rGamma stack incoming snapshots
    policies h Hmain
    [Hprivate [Haligned [Hvalid Hseparated]]].
  split.
  - eapply private_principled_statement_result_refl; eauto.
  - exact (conj Haligned (conj Hvalid Hseparated)).
Qed.

Lemma private_policy_statement_result_trans :
  forall CT P Z cutoff authority middle_senv middle_renv final_senv
    final_renv stack incoming initial_snapshots middle_snapshots
    final_snapshots policies middle_h final_h,
    private_policy_statement_result CT P Z cutoff authority middle_senv
      middle_renv stack incoming initial_snapshots middle_snapshots policies
      middle_h ->
    private_policy_statement_result CT P Z cutoff authority final_senv
      final_renv stack incoming middle_snapshots final_snapshots policies
      final_h ->
    private_policy_statement_result CT P Z cutoff authority final_senv
      final_renv stack incoming initial_snapshots final_snapshots policies
      final_h.
Proof.
  intros CT P Z cutoff authority middle_senv middle_renv final_senv
    final_renv stack incoming initial_snapshots middle_snapshots
    final_snapshots policies middle_h final_h
    [Hfirst [Hfirst_aligned [Hfirst_valid Hfirst_separated]]]
    [Hsecond [Hsecond_aligned [Hsecond_valid Hsecond_separated]]].
  split.
  - eapply private_principled_statement_result_trans; eauto.
  - exact (conj Hsecond_aligned (conj Hsecond_valid Hsecond_separated)).
Qed.

Lemma private_advancing_policy_statement_result_is_state :
  forall CT P Z cutoff authority final_senv final_renv stack incoming
    initial_snapshots final_snapshots initial_policies final_h,
    private_advancing_policy_statement_result CT P Z cutoff authority
      final_senv final_renv stack incoming initial_snapshots
      final_snapshots initial_policies final_h ->
    exists final_policies,
      private_frame_join_policies_metadata_eq final_policies initial_policies /\
      private_advancing_policy_statement_state CT P Z cutoff
        (mk_watched_frame authority final_senv final_renv) stack incoming
        final_snapshots final_policies final_h.
Proof.
  intros CT P Z cutoff authority final_senv final_renv stack incoming
    initial_snapshots final_snapshots initial_policies final_h
    [final_policies [Hmetadata [Hgrows [Hresult [Hcover [Hphase Hroots]]]]]].
  exists final_policies. split; [exact Hmetadata|].
  split.
  - eapply private_policy_statement_result_is_state. exact Hresult.
  - split; [exact Hcover|split; assumption].
Qed.

Lemma private_advancing_policy_statement_result_refl :
  forall CT P Z cutoff authority sGamma rGamma stack incoming snapshots
    policies h,
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming h ->
    private_advancing_policy_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots
      policies h ->
    private_advancing_policy_statement_result CT P Z cutoff authority sGamma
      rGamma stack incoming snapshots snapshots policies h.
Proof.
  intros CT P Z cutoff authority sGamma rGamma stack incoming snapshots
    policies h Hmain [Hstate [Hcover [Hphase Hroots]]].
  exists policies. split.
  - apply private_frame_join_policies_metadata_eq_refl.
  - split.
    + apply frozen_caller_snapshot_list_phase_images_grow_refl.
    + split.
      * eapply private_policy_statement_result_refl; eauto.
      * split; [exact Hcover|split; assumption].
Qed.

Lemma private_advancing_policy_statement_result_trans_from_middle :
  forall CT P Z cutoff authority middle_senv middle_renv final_senv
    final_renv stack incoming initial_snapshots middle_snapshots
    final_snapshots initial_policies middle_policies middle_h final_h,
    private_policy_statement_result CT P Z cutoff authority
      middle_senv middle_renv stack incoming initial_snapshots middle_snapshots
      middle_policies middle_h ->
    private_frame_join_policies_metadata_eq middle_policies initial_policies ->
    frozen_caller_snapshot_list_phase_images_grow
      middle_policies.(suspended_frame_resume_witnesses)
      initial_policies.(suspended_frame_resume_witnesses) ->
    private_advancing_policy_statement_result CT P Z cutoff authority
      final_senv final_renv stack incoming middle_snapshots
      final_snapshots middle_policies final_h ->
    private_advancing_policy_statement_result CT P Z cutoff authority
      final_senv final_renv stack incoming initial_snapshots
      final_snapshots initial_policies final_h.
Proof.
  intros CT P Z cutoff authority middle_senv middle_renv final_senv
    final_renv stack incoming initial_snapshots middle_snapshots
    final_snapshots initial_policies middle_policies middle_h final_h
    Hfirst Hmiddle_metadata Hmiddle_grows
    [final_policies
      [Hfinal_metadata [Hfinal_grows
        [Hsecond [Hfinal_cover [Hfinal_phase Hfinal_roots]]]]]].
  destruct Hfirst as
    [Hfirst_principled [Hfirst_aligned [Hfirst_valid Hfirst_separated]]].
  destruct Hsecond as
    [Hsecond_principled [Hsecond_aligned [Hsecond_valid Hsecond_separated]]].
  exists final_policies. split.
  - eapply private_frame_join_policies_metadata_eq_trans; eauto.
  - split.
    + eapply frozen_caller_snapshot_list_phase_images_grow_trans; eauto.
    + split.
      * split.
        -- eapply private_principled_statement_result_trans; eauto.
        -- exact (conj Hsecond_aligned
             (conj Hsecond_valid Hsecond_separated)).
      * split; [exact Hfinal_cover|split; assumption].
Qed.

Lemma private_policy_statement_result_advance_witnesses :
  forall CT P Z cutoff authority final_senv final_renv stack incoming
    initial_snapshots final_snapshots policies final_h,
    private_policy_statement_result CT P Z cutoff authority final_senv
      final_renv stack incoming initial_snapshots final_snapshots policies
      final_h ->
    private_resume_witnesses_cover_snapshots Z
      (advance_frozen_caller_snapshots CT final_h
        (mk_watched_frame authority final_senv final_renv)
        policies.(suspended_frame_resume_witnesses)) final_snapshots ->
    private_resume_witnesses_phase_wf CT final_h
      (mk_watched_frame authority final_senv final_renv)
      (advance_frozen_caller_snapshots CT final_h
        (mk_watched_frame authority final_senv final_renv)
        policies.(suspended_frame_resume_witnesses)) final_snapshots ->
    private_resume_witnesses_roots_safe CT final_h Z
      (mk_watched_frame authority final_senv final_renv)
      (advance_frozen_caller_snapshots CT final_h
        (mk_watched_frame authority final_senv final_renv)
        policies.(suspended_frame_resume_witnesses)) final_snapshots ->
    private_resume_witnesses_nested_resume_safe Z
      (advance_frozen_caller_snapshots CT final_h
        (mk_watched_frame authority final_senv final_renv)
        policies.(suspended_frame_resume_witnesses)) final_snapshots ->
    private_resume_witnesses_completed_safe CT final_h Z
      (mk_watched_frame authority final_senv final_renv) incoming
      (advance_frozen_caller_snapshots CT final_h
        (mk_watched_frame authority final_senv final_renv)
        policies.(suspended_frame_resume_witnesses)) final_snapshots ->
    private_resume_witness_stack_safe CT final_h Z
      (mk_watched_frame authority final_senv final_renv) incoming
      (advance_frozen_caller_snapshots CT final_h
        (mk_watched_frame authority final_senv final_renv)
        policies.(suspended_frame_resume_witnesses)) ->
    frozen_caller_snapshots_before_boundaries
      (advance_frozen_caller_snapshots CT final_h
        (mk_watched_frame authority final_senv final_renv)
        policies.(suspended_frame_resume_witnesses)) stack ->
    private_resume_witness_temporal_state CT final_h Z cutoff
      (mk_watched_frame authority final_senv final_renv) stack
      (advance_frozen_caller_snapshots CT final_h
        (mk_watched_frame authority final_senv final_renv)
        policies.(suspended_frame_resume_witnesses)) ->
    private_target_witness_state CT final_h Z cutoff
      (mk_watched_frame authority final_senv final_renv) incoming
      final_snapshots
      (advance_frozen_caller_snapshots CT final_h
        (mk_watched_frame authority final_senv final_renv)
        policies.(suspended_frame_target_witnesses))
      (advance_frozen_caller_snapshots CT final_h
        (mk_watched_frame authority final_senv final_renv)
        policies.(suspended_frame_resume_witnesses)) stack ->
    private_advancing_policy_statement_result CT P Z cutoff authority
      final_senv final_renv stack incoming initial_snapshots
      final_snapshots policies final_h.
Proof.
  intros CT P Z cutoff authority final_senv final_renv stack incoming
    initial_snapshots final_snapshots policies final_h
    [Hprincipled [Haligned [Hvalid Hseparated]]] Hcover Hphase
    Hroots Hnested Hcompleted Hstack_safe Hbefore Htemporal Htarget.
  set (final_active :=
    mk_watched_frame authority final_senv final_renv).
  set (final_policies :=
    advance_private_frame_resume_witnesses CT final_h final_active policies).
  exists final_policies. split.
  - unfold final_policies.
    apply advance_private_frame_resume_witnesses_metadata_eq.
  - split.
    + unfold final_policies, advance_private_frame_resume_witnesses. simpl.
      apply advance_frozen_caller_snapshots_phase_images_grow.
    + split.
      * split; [exact Hprincipled|]. split.
        -- unfold final_policies.
           eapply advance_private_frame_resume_witnesses_aligned. exact Haligned.
        -- split.
           ++ unfold private_frame_join_policies_valid, final_policies,
                advance_private_frame_resume_witnesses in *. simpl in *.
              exact Hvalid.
           ++ unfold final_policies, advance_private_frame_resume_witnesses.
              simpl. exact Hseparated.
      * unfold final_policies, advance_private_frame_resume_witnesses. simpl.
        split; [exact Hcover|]. split; [exact Hphase|]. split;
          [exact Hroots|]. split; [exact Hnested|]. split;
          [exact Hcompleted|]. split; [exact Hstack_safe|]. split;
          [exact Hbefore|]. split; [exact Htemporal|exact Htarget].
Qed.

Lemma private_policy_statement_result_advance_witnesses_after_active_descent :
  forall CT P Z cutoff authority old_senv old_renv new_senv new_renv stack
    incoming snapshots policies h,
    private_advancing_policy_statement_state CT P Z cutoff
      (mk_watched_frame authority old_senv old_renv) stack incoming snapshots
      policies h ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame authority new_senv new_renv))
      (phase_frame_capability_set CT h
        (mk_watched_frame authority old_senv old_renv)) ->
    wf_r_config CT new_senv new_renv h ->
    private_resume_witness_temporal_state CT h Z cutoff
      (mk_watched_frame authority new_senv new_renv) stack
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv)
        policies.(suspended_frame_resume_witnesses)) ->
    private_policy_statement_result CT P Z cutoff authority new_senv new_renv
      stack incoming snapshots
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) snapshots)
      policies h ->
    private_advancing_policy_statement_result CT P Z cutoff authority
      new_senv new_renv stack incoming snapshots
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) snapshots)
      policies h.
Proof.
  intros CT P Z cutoff authority old_senv old_renv new_senv new_renv stack
    incoming snapshots policies h Hstate
    Hdescend Howned Hnew_wf Hnew_temporal Hresult.
  destruct Hstate as
    (Hold & Hwitness_cover & Hwitness_phase & Hwitness_roots &
      Hwitness_nested & Hwitness_completed & Hwitness_stack_safe &
      Hwitness_before & Hwitness_temporal & Htarget_state).
  destruct Htarget_state as
    (Htarget_cover & Htarget_stack_safe & Htarget_phase_safe &
      Htarget_cross_phase & Htarget_nested_phase & Htarget_before &
      Htarget_support & Htarget_history & Htarget_temporal).
  have Htarget_stack_parts := Htarget_stack_safe.
  destruct Htarget_stack_parts as
    (_ & _ & _ & Htarget_closed & _ & Htarget_exposure & _ & _).
  have Hwitness_stack_parts := Hwitness_stack_safe.
  destruct Hwitness_stack_parts as
    (_ & _ & _ & _ & _ & Hwitness_exposure & _ & _ & _ & _ & _ & _).
  have Hfresh := proj1 (proj1 Hold).
  have Hfrozen := proj1 Hfresh.
  destruct Hfrozen as
    [Hprincipled [Hactive_justified [Hbefore
      [Hnested_covered [Hnested_safe Hcompleted]]]]].
  have Hnew_cover :=
    private_resume_witnesses_cover_snapshots_after_active_descent CT h Z
      authority old_senv old_renv new_senv new_renv
      policies.(suspended_frame_resume_witnesses) snapshots Hdescend
      Hwitness_cover Hwitness_phase Hnested_covered Hnested_safe.
  have Hnew_phase :=
    private_resume_witnesses_phase_wf_after_advance_from_any_active CT h
      (mk_watched_frame authority old_senv old_renv)
      (mk_watched_frame authority new_senv new_renv)
      policies.(suspended_frame_resume_witnesses) snapshots Hnew_wf
      Hwitness_phase.
  have Hnew_roots :=
    private_resume_witnesses_roots_safe_after_active_descent CT h Z authority
      old_senv old_renv new_senv new_renv
      policies.(suspended_frame_resume_witnesses) snapshots Hdescend Howned
      Hwitness_phase Hwitness_roots.
  have Hnew_nested :=
    private_resume_witnesses_nested_resume_safe_after_active_descent CT h Z
      authority old_senv old_renv new_senv new_renv
      policies.(suspended_frame_resume_witnesses) snapshots Hdescend
      Hwitness_phase Hwitness_nested.
  have Hnew_completed :=
    private_resume_witnesses_completed_safe_after_active_descent CT h Z
      authority old_senv old_renv new_senv new_renv incoming
      policies.(suspended_frame_resume_witnesses) snapshots Hdescend Howned
      Hwitness_phase Hwitness_completed.
  have Hnew_stack_safe :=
    private_resume_witness_stack_safe_after_active_descent CT h Z authority
      old_senv old_renv new_senv new_renv incoming
      policies.(suspended_frame_resume_witnesses) Hnew_wf Hdescend Howned
      Hwitness_stack_safe.
  have Hnew_before :=
    advance_frozen_caller_snapshots_before_boundaries CT h
      (mk_watched_frame authority new_senv new_renv)
      policies.(suspended_frame_resume_witnesses) stack Hwitness_before.
  have Hnew_target_cover :=
    private_resume_witnesses_cover_snapshots_after_advance CT h Z
      (mk_watched_frame authority new_senv new_renv)
      policies.(suspended_frame_target_witnesses) snapshots Htarget_cover.
  have Hnew_target_stack_safe :=
    private_target_witness_stack_structural_after_advance CT h
      (mk_watched_frame authority old_senv old_renv)
      (mk_watched_frame authority new_senv new_renv)
      policies.(suspended_frame_target_witnesses) Hnew_wf Htarget_stack_safe.
  have Hnew_target_phase_safe :=
    frozen_completed_colors_resume_phase_safe_after_active_descent CT h Z
      authority old_senv old_renv new_senv new_renv incoming
      policies.(suspended_frame_target_witnesses) Hdescend Howned
      Htarget_exposure Htarget_phase_safe.
  have Hnew_target_cross_phase :=
    private_target_exposures_support_resume_phase_after_active_descent CT h Z
      authority old_senv old_renv new_senv new_renv
      policies.(suspended_frame_target_witnesses)
      policies.(suspended_frame_resume_witnesses) Hdescend Htarget_exposure
      Hwitness_exposure Htarget_cross_phase.
  have Hnew_target_nested_phase :=
    frozen_target_nested_phase_safe_after_active_descent CT h Z authority
      old_senv old_renv new_senv new_renv
      policies.(suspended_frame_target_witnesses) Hdescend Htarget_closed
      Htarget_exposure Htarget_nested_phase.
  have Hnew_target_before :=
    advance_frozen_caller_snapshots_before_boundaries CT h
      (mk_watched_frame authority new_senv new_renv)
      policies.(suspended_frame_target_witnesses) stack Htarget_before.
  have Hnew_target_support :=
    private_target_supports_resume_witnesses_after_advance CT h
      (mk_watched_frame authority new_senv new_renv)
      policies.(suspended_frame_target_witnesses)
      policies.(suspended_frame_resume_witnesses) Htarget_support.
  have Hnew_target_history :=
    private_target_history_supports_resume_phase_after_active_descent CT h Z
      authority old_senv old_renv new_senv new_renv
      policies.(suspended_frame_target_witnesses)
      policies.(suspended_frame_resume_witnesses) Hdescend Hwitness_exposure
      Htarget_history.
  have Hold_main := proj1 Hprincipled.
  have Hold_wf : wf_r_config CT old_senv old_renv h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hold_main))))).
  have Hold_sound : authority_context_sound h old_renv authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hold_main)))))).
  have Hnew_target_temporal :=
    private_target_witness_temporal_after_active_descent CT h Z cutoff authority
      old_senv old_renv new_senv new_renv
      policies.(suspended_frame_target_witnesses) stack Hold_wf Hold_sound
      Hdescend Howned Htarget_stack_safe Htarget_temporal.
  have Hnew_target_state : private_target_witness_state CT h Z cutoff
      (mk_watched_frame authority new_senv new_renv) incoming
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) snapshots)
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv)
        policies.(suspended_frame_target_witnesses))
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv)
        policies.(suspended_frame_resume_witnesses)) stack.
  { unfold private_target_witness_state. split; [exact Hnew_target_cover|].
      split; [exact Hnew_target_stack_safe|].
      split; [exact Hnew_target_phase_safe|].
      split; [exact Hnew_target_cross_phase|].
      split; [exact Hnew_target_nested_phase|].
      split; [exact Hnew_target_before|].
      split; [exact Hnew_target_support|].
      split; [exact Hnew_target_history|exact Hnew_target_temporal]. }
  eapply private_policy_statement_result_advance_witnesses; eauto.
Qed.

Lemma private_advancing_policy_statement_after_field_write :
  forall CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    policies x field y sGamma' rGamma' h',
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming h ->
    private_advancing_policy_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots
      policies h ->
    stmt_typing CT sGamma mt (SFldWrite x field y) sGamma' ->
    readonly_state_method_scope mt ->
    eval_stmt CT rGamma h (SFldWrite x field y) OK rGamma' h' ->
    private_policy_statement_result CT P Z cutoff authority sGamma' rGamma'
      stack incoming snapshots
      (advance_frozen_caller_snapshots CT h'
        (mk_watched_frame authority sGamma' rGamma') snapshots)
      policies h' ->
    private_advancing_policy_statement_result CT P Z cutoff authority
      sGamma' rGamma' stack incoming snapshots
      (advance_frozen_caller_snapshots CT h'
        (mk_watched_frame authority sGamma' rGamma') snapshots)
      policies h'.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    policies x field y sGamma' rGamma' h' Hpotential Hadvancing Htyping
    Hscope Heval Hfixed.
  have Hwitness_fresh :=
    private_advancing_policy_statement_witness_state_is_private_fresh CT P Z
      cutoff (mk_watched_frame authority sGamma rGamma) stack incoming
      snapshots policies h Hadvancing.
  have Hnew_witness_fresh :=
    private_fresh_frozen_statement_after_field_write CT P Z cutoff authority
      sGamma mt rGamma h stack incoming
      policies.(suspended_frame_resume_witnesses) x field y sGamma' rGamma'
      h' Hwitness_fresh Htyping Hscope Heval.
  have Hnew_temporal :=
    private_fresh_frozen_statement_state_has_resume_temporal_state CT P Z
      cutoff (mk_watched_frame authority sGamma' rGamma') stack incoming
      (advance_frozen_caller_snapshots CT h'
        (mk_watched_frame authority sGamma' rGamma')
        policies.(suspended_frame_resume_witnesses)) h'
      Hnew_witness_fresh.
  destruct Hadvancing as
    (Hold & Hcover & Hphase & Hroots & Hwitness_nested &
      Hwitness_completed & Hwitness_stack_safe & Hwitness_before &
      Hwitness_temporal & Htarget_state).
  destruct Htarget_state as
    (Htarget_cover & Htarget_stack_safe & Htarget_phase_safe &
      Htarget_cross_phase & Htarget_nested_phase & Htarget_before &
      Htarget_support & Htarget_history & Htarget_temporal).
  have Htarget_stack_parts := Htarget_stack_safe.
  destruct Htarget_stack_parts as
    (_ & Htarget_runtime & _ & Htarget_closed & _ & Htarget_exposure & _ & _).
  have Hwitness_stack_parts := Hwitness_stack_safe.
  destruct Hwitness_stack_parts as
    (_ & _ & _ & _ & _ & Hwitness_exposure & _ & _ & _ & _ & _ & _).
  have Hmain := private_policy_statement_state_main CT P Z cutoff
    (mk_watched_frame authority sGamma rGamma) stack incoming snapshots
    policies h Hold.
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hsound : authority_context_sound h rGamma authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
  have Hframes := proj1 (proj2 (proj2 (proj2 (proj2 Hmain)))).
  have Hsounds := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hfresh := proj1 (proj1 Hold).
  have Hfrozen := proj1 Hfresh.
  destruct Hfrozen as
    [Hprincipled [Hactive_justified [Hbefore
      [Hnested_covered [Hnested_safe Hcompleted]]]]].
  have Hactive_runtime : authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h
        (mk_watched_frame authority sGamma rGamma)).
  { eapply executing_authority_colors_runtime_mutable; eauto.
    intros mode location Hempty. inversion Hempty. }
  have Hcompleted_runtime : authority_colors_runtime_mutable h
      (executing_authority_color_set CT h
        (mk_watched_frame authority sGamma rGamma) incoming).
  { eapply executing_authority_colors_runtime_mutable; eauto.
    exact (proj1 (proj2 (proj2 Hmain))). }
  have Hactive_safe : forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h
          (mk_watched_frame authority sGamma rGamma))
        (active_mode, location) ->
      ~ In Loc Z location.
  { intros active_mode location Hmode Hcolor Hprotected.
    eapply (proj1 (proj2 (proj2 (proj2 Hmain))));
      [exact Hmode| |exact Hprotected].
    eapply independent_active_authority_colors_in_executing. exact Hcolor. }
  have Hcompleted_safe : forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (executing_authority_color_set CT h
          (mk_watched_frame authority sGamma rGamma) incoming)
        (active_mode, location) ->
      ~ In Loc Z location.
  { exact (proj1 (proj2 (proj2 (proj2 Hmain)))). }
  have Hresume_completed_phase : frozen_completed_colors_resume_phase_safe Z
      (executing_authority_color_set CT h
        (mk_watched_frame authority sGamma rGamma) incoming)
      policies.(suspended_frame_resume_witnesses).
  { eapply target_phase_safe_transfers_to_resume_witnesses; eauto. }
  have Hresume_active_phase : frozen_completed_colors_resume_phase_safe Z
      (independent_active_authority_colors CT h
        (mk_watched_frame authority sGamma rGamma))
      policies.(suspended_frame_resume_witnesses).
  { intros snapshot source_mode source Hsnapshot Hmode Hcolor Hroot.
    eapply Hresume_completed_phase; eauto.
    eapply independent_active_authority_colors_in_executing. exact Hcolor. }
  have Htarget_active_phase : frozen_completed_colors_resume_phase_safe Z
      (independent_active_authority_colors CT h
        (mk_watched_frame authority sGamma rGamma))
      policies.(suspended_frame_target_witnesses).
  { intros snapshot source_mode source Hsnapshot Hmode Hcolor Hroot.
    eapply Htarget_phase_safe; eauto.
    eapply independent_active_authority_colors_in_executing. exact Hcolor. }
  have Heffect := typed_field_write_component_effect CT authority sGamma mt
    rGamma h x field y sGamma' rGamma' h' Hwf Htyping Hscope Heval.
  assert (HsGamma : sGamma' = sGamma) by
    (inversion Htyping; reflexivity).
  assert (HrGamma : rGamma' = rGamma) by
    (inversion Heval; reflexivity).
  subst sGamma' rGamma'.
  have Hpost_state := private_policy_statement_result_is_state CT P Z cutoff
    authority sGamma rGamma stack incoming snapshots
    (advance_frozen_caller_snapshots CT h'
      (mk_watched_frame authority sGamma rGamma) snapshots)
    policies h' Hfixed.
  have Hpost_main := private_policy_statement_state_main CT P Z cutoff
    (mk_watched_frame authority sGamma rGamma) stack incoming
    (advance_frozen_caller_snapshots CT h'
      (mk_watched_frame authority sGamma rGamma) snapshots)
    policies h' Hpost_state.
  have Hpost_wf : wf_r_config CT sGamma rGamma h' :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hpost_main))))).
  have Hdom : dom h <= dom h'.
  { eapply eval_stmt_preserves_heap_domain_simple. exact Heval. }
  destruct Heffect as
    [[Hruntimes [Hmutable [Hretained Howned]]] |
     [lx [old [written [Hheap [Hobj Hendpoints]]]]]].
  - have Hnew_cover :=
      private_resume_witnesses_cover_snapshots_after_graph_reflection CT h h'
        Z (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_resume_witnesses) snapshots Hretained
        Hmutable Hcover Hphase Hnested_covered Hnested_safe.
    have Hnew_phase :=
      private_resume_witnesses_phase_wf_after_runtime_equivalent_heap CT h h'
        (mk_watched_frame authority sGamma rGamma)
        (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_resume_witnesses) snapshots
        (fun location _ => Hruntimes location)
        Hdom Hpost_wf Hphase.
    have Hnew_roots :=
      private_resume_witnesses_roots_safe_after_graph_reflection CT h h' Z
        (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_resume_witnesses) snapshots Howned
        Hretained Hmutable Hphase Hroots.
    have Hnew_nested :=
      private_resume_witnesses_nested_resume_safe_after_graph_reflection CT h
        h' Z (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_resume_witnesses) snapshots Hretained
        Hmutable Hphase Hwitness_nested.
    have Hnew_completed :=
      private_resume_witnesses_completed_safe_after_graph_reflection CT h h'
        Z (mk_watched_frame authority sGamma rGamma) incoming
        policies.(suspended_frame_resume_witnesses) snapshots Howned
        Hretained Hmutable Hphase Hwitness_completed.
    have Hnew_stack_safe :=
      private_resume_witness_stack_safe_after_graph_reflection CT h h' Z
        (mk_watched_frame authority sGamma rGamma) incoming
        policies.(suspended_frame_resume_witnesses)
        (fun location _ => Hruntimes location) Hdom Hpost_wf Howned Hretained
        Hmutable Hwitness_stack_safe.
    have Hnew_before :=
      advance_frozen_caller_snapshots_before_boundaries CT h'
        (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_resume_witnesses) stack Hwitness_before.
    have Hnew_target_cover :=
      private_resume_witnesses_cover_snapshots_after_advance CT h' Z
        (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_target_witnesses) snapshots Htarget_cover.
    have Hnew_target_stack_safe :=
      private_target_witness_stack_structural_after_runtime_equivalent_heap
        CT h h'
        (mk_watched_frame authority sGamma rGamma)
        (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_target_witnesses)
        (fun location _ => Hruntimes location) Hdom Hpost_wf
        Htarget_stack_safe.
    have Hnew_target_phase_safe :=
      frozen_completed_colors_resume_phase_safe_after_graph_reflection CT h h'
        Z (mk_watched_frame authority sGamma rGamma) incoming
        policies.(suspended_frame_target_witnesses) Howned Hretained Hmutable
        Htarget_exposure Htarget_phase_safe.
    have Hnew_target_cross_phase :=
      private_target_exposures_support_resume_phase_after_graph_reflection CT h
        h' Z (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_target_witnesses)
        policies.(suspended_frame_resume_witnesses) Hretained Hmutable
        Htarget_exposure Hwitness_exposure Htarget_cross_phase.
    have Hnew_target_nested_phase :=
      frozen_target_nested_phase_safe_after_graph_reflection CT h h' Z
        (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_target_witnesses) Hretained Hmutable
        Htarget_closed Htarget_exposure Htarget_nested_phase.
    have Hnew_target_before :=
      advance_frozen_caller_snapshots_before_boundaries CT h'
        (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_target_witnesses) stack Htarget_before.
    have Hnew_target_support :=
      private_target_supports_resume_witnesses_after_advance CT h'
        (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_target_witnesses)
        policies.(suspended_frame_resume_witnesses) Htarget_support.
    have Hnew_target_history :=
      private_target_history_supports_resume_phase_after_graph_reflection CT h
        h' Z (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_target_witnesses)
        policies.(suspended_frame_resume_witnesses) Hretained Hmutable
        Hwitness_exposure Htarget_history.
    have Hnew_target_temporal :=
      private_target_witness_temporal_after_graph_reflection CT h h' Z cutoff
        (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_target_witnesses) stack Hruntimes Hretained
        Hmutable Howned Htarget_stack_safe Htarget_temporal.
    have Hnew_target_state : private_target_witness_state CT h' Z cutoff
        (mk_watched_frame authority sGamma rGamma) incoming
        (advance_frozen_caller_snapshots CT h'
          (mk_watched_frame authority sGamma rGamma) snapshots)
        (advance_frozen_caller_snapshots CT h'
          (mk_watched_frame authority sGamma rGamma)
          policies.(suspended_frame_target_witnesses))
        (advance_frozen_caller_snapshots CT h'
          (mk_watched_frame authority sGamma rGamma)
          policies.(suspended_frame_resume_witnesses)) stack.
    { unfold private_target_witness_state.
      split; [exact Hnew_target_cover|].
      split; [exact Hnew_target_stack_safe|].
      split; [exact Hnew_target_phase_safe|].
      split; [exact Hnew_target_cross_phase|].
      split; [exact Hnew_target_nested_phase|].
      split; [exact Hnew_target_before|].
      split; [exact Hnew_target_support|].
      split; [exact Hnew_target_history|exact Hnew_target_temporal]. }
    eapply private_policy_statement_result_advance_witnesses; eauto.
  - subst h'.
    have Hnew_cover :=
      private_resume_witnesses_cover_snapshots_after_safe_field_update CT h Z
        (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_resume_witnesses) snapshots lx old field
        written Hobj Hcover Hphase Hroots Hnested_covered Hnested_safe
        Hactive_runtime Hendpoints Hactive_safe.
    have Hnew_phase :=
      private_resume_witnesses_phase_wf_after_runtime_equivalent_heap CT h
        (update_field h lx field (Iot written))
        (mk_watched_frame authority sGamma rGamma)
        (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_resume_witnesses) snapshots
        (ltac:(intros location _; apply r_muttype_update_field_preserve))
        Hdom Hpost_wf Hphase.
    have Hnew_roots :=
      private_resume_witnesses_roots_safe_after_safe_field_update CT h Z
        (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_resume_witnesses) snapshots lx old field
        written Hobj Hphase Hactive_runtime Hendpoints Hactive_safe Hroots.
    have Hnew_nested :=
      private_resume_witnesses_nested_resume_safe_after_safe_field_update CT
        h Z (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_resume_witnesses) snapshots lx old field
        written Hobj Hphase Hactive_runtime Hendpoints Hactive_safe Hroots
        Hwitness_nested.
    have Hnew_completed :=
      private_resume_witnesses_completed_safe_after_safe_field_update CT h Z
        (mk_watched_frame authority sGamma rGamma) incoming
        policies.(suspended_frame_resume_witnesses) snapshots lx old field
        written Hobj Hcompleted_runtime Hphase Hactive_runtime Hendpoints
        Hactive_safe Hwitness_completed.
    have Hnew_stack_safe :=
      private_resume_witness_stack_safe_after_safe_field_update CT h Z
        (mk_watched_frame authority sGamma rGamma) incoming
        policies.(suspended_frame_resume_witnesses) lx old field written Hobj
        Hpost_wf Hcompleted_runtime Hactive_runtime Hendpoints Hactive_safe
        Hwitness_stack_safe.
    have Hnew_before :=
      advance_frozen_caller_snapshots_before_boundaries CT
        (update_field h lx field (Iot written))
        (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_resume_witnesses) stack Hwitness_before.
    have Hnew_target_cover :=
      private_resume_witnesses_cover_snapshots_after_advance CT
        (update_field h lx field (Iot written)) Z
        (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_target_witnesses) snapshots Htarget_cover.
    have Hnew_target_stack_safe :=
      private_target_witness_stack_structural_after_runtime_equivalent_heap
        CT h (update_field h lx field (Iot written))
        (mk_watched_frame authority sGamma rGamma)
        (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_target_witnesses)
        (ltac:(intros location _; apply r_muttype_update_field_preserve))
        Hdom Hpost_wf
        Htarget_stack_safe.
    have Hnew_target_phase_safe :=
      frozen_completed_colors_resume_phase_safe_after_safe_field_update CT h Z
        (mk_watched_frame authority sGamma rGamma) incoming
        policies.(suspended_frame_target_witnesses) lx old field written Hobj
        Hcompleted_runtime Htarget_exposure Hactive_runtime Hendpoints
        Htarget_phase_safe Hactive_safe.
    have Hnew_target_cross_phase :=
      private_target_exposures_support_resume_phase_after_safe_field_update CT
        h Z (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_target_witnesses)
        policies.(suspended_frame_resume_witnesses) lx old field written Hobj
        Htarget_exposure Hwitness_exposure Hactive_runtime Hendpoints
        Htarget_cross_phase Hresume_active_phase Hactive_safe.
    have Hnew_target_nested_phase :=
      frozen_target_nested_phase_safe_after_safe_field_update CT h Z
        (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_target_witnesses) lx old field written Hobj
        Htarget_runtime Htarget_closed Htarget_exposure Hactive_runtime
        Hendpoints Htarget_nested_phase Htarget_active_phase Hactive_safe.
    have Hnew_target_before :=
      advance_frozen_caller_snapshots_before_boundaries CT
        (update_field h lx field (Iot written))
        (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_target_witnesses) stack Htarget_before.
    have Hnew_target_support :=
      private_target_supports_resume_witnesses_after_advance CT
        (update_field h lx field (Iot written))
        (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_target_witnesses)
        policies.(suspended_frame_resume_witnesses) Htarget_support.
    have Hnew_target_history :=
      private_target_history_supports_resume_phase_after_safe_field_update CT h
        Z (mk_watched_frame authority sGamma rGamma)
        policies.(suspended_frame_target_witnesses)
        policies.(suspended_frame_resume_witnesses) lx old field written Hobj
        Hwitness_exposure Hactive_runtime Hendpoints Hactive_safe
        Htarget_history.
    have Htarget_post_main : principled_phased_authority_live_history_state CT P Z
        cutoff (mk_watched_frame authority sGamma rGamma) stack incoming
        (update_field h lx field (Iot written)) :=
      proj1 (proj1 (proj1 Hnew_witness_fresh)).
    have Hnew_target_temporal :=
      private_target_witness_temporal_after_safe_field_update CT P Z cutoff
        (mk_watched_frame authority sGamma rGamma) stack incoming
        policies.(suspended_frame_target_witnesses) h lx old field written
        Hmain Hobj Hendpoints Htarget_stack_safe Htarget_post_main
        Htarget_temporal.
    have Hnew_target_state : private_target_witness_state CT
        (update_field h lx field (Iot written)) Z cutoff
        (mk_watched_frame authority sGamma rGamma) incoming
        (advance_frozen_caller_snapshots CT
          (update_field h lx field (Iot written))
          (mk_watched_frame authority sGamma rGamma) snapshots)
        (advance_frozen_caller_snapshots CT
          (update_field h lx field (Iot written))
          (mk_watched_frame authority sGamma rGamma)
          policies.(suspended_frame_target_witnesses))
        (advance_frozen_caller_snapshots CT
          (update_field h lx field (Iot written))
          (mk_watched_frame authority sGamma rGamma)
          policies.(suspended_frame_resume_witnesses)) stack.
    { unfold private_target_witness_state.
      split; [exact Hnew_target_cover|].
      split; [exact Hnew_target_stack_safe|].
      split; [exact Hnew_target_phase_safe|].
      split; [exact Hnew_target_cross_phase|].
      split; [exact Hnew_target_nested_phase|].
      split; [exact Hnew_target_before|].
      split; [exact Hnew_target_support|].
      split; [exact Hnew_target_history|exact Hnew_target_temporal]. }
    eapply private_policy_statement_result_advance_witnesses; eauto.
Qed.

Lemma private_advancing_policy_statement_after_new :
  forall CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    policies x qc C args sGamma' rGamma' h',
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming h ->
    private_advancing_policy_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots
      policies h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    eval_stmt CT rGamma h (SNew x qc C args) OK rGamma' h' ->
    private_policy_statement_result CT P Z cutoff authority sGamma' rGamma'
      stack incoming snapshots
      (advance_frozen_caller_snapshots CT h'
        (mk_watched_frame authority sGamma' rGamma') snapshots)
      policies h' ->
    private_advancing_policy_statement_result CT P Z cutoff authority
      sGamma' rGamma' stack incoming snapshots
      (advance_frozen_caller_snapshots CT h'
        (mk_watched_frame authority sGamma' rGamma') snapshots)
      policies h'.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    policies x qc C args sGamma' rGamma' h' Hpotential Hadvancing Htyping
    Heval Hfixed.
  have Hwitness_fresh :=
    private_advancing_policy_statement_witness_state_is_private_fresh CT P Z
      cutoff (mk_watched_frame authority sGamma rGamma) stack incoming
      snapshots policies h Hadvancing.
  have Hnew_witness_fresh :=
    private_fresh_frozen_statement_after_new CT P Z cutoff authority sGamma
      mt rGamma h stack incoming policies.(suspended_frame_resume_witnesses)
      x qc C args sGamma' rGamma' h' Hwitness_fresh Htyping Heval.
  have Hnew_temporal :=
    private_fresh_frozen_statement_state_has_resume_temporal_state CT P Z
      cutoff (mk_watched_frame authority sGamma' rGamma') stack incoming
      (advance_frozen_caller_snapshots CT h'
        (mk_watched_frame authority sGamma' rGamma')
        policies.(suspended_frame_resume_witnesses)) h'
      Hnew_witness_fresh.
  destruct Hadvancing as
    (Hold & Hcover & Hphase & Hroots & Hwitness_nested &
      Hwitness_completed & Hwitness_stack_safe & Hwitness_before &
      Hwitness_temporal & Htarget_state).
  destruct Htarget_state as
    (Htarget_cover & Htarget_stack_safe & Htarget_phase_safe &
      Htarget_cross_phase & Htarget_nested_phase & Htarget_before &
      Htarget_support & Htarget_history & Htarget_temporal).
  have Htarget_stack_parts := Htarget_stack_safe.
  destruct Htarget_stack_parts as
    (_ & Htarget_runtime & _ & Htarget_closed & Htarget_roots &
      Htarget_exposure & _ & _).
  have Hwitness_stack_parts := Hwitness_stack_safe.
  destruct Hwitness_stack_parts as
    (_ & _ & _ & _ & Hwitness_roots & Hwitness_exposure & _ & _ & _ & _ & _ &
      _).
  have Hmain := private_policy_statement_state_main CT P Z cutoff
    (mk_watched_frame authority sGamma rGamma) stack incoming snapshots
    policies h Hold.
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hsound : authority_context_sound h rGamma authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
  have Hcutoff : cutoff <= dom h :=
    proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
  have Hzone : protected_zone_before_cutoff Z cutoff :=
    proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
      (proj2 Hmain))))))).
  have Hincoming_runtime : authority_colors_runtime_mutable h incoming :=
    proj1 (proj2 (proj2 Hmain)).
  have Hfresh := proj1 (proj1 Hold).
  have Hfrozen := proj1 Hfresh.
  destruct Hfrozen as
    [Hprincipled [Hactive_justified [Hbefore
      [Hnested_covered [Hnested_safe Hcompleted]]]]].
  have Hactive_safe : forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h
          (mk_watched_frame authority sGamma rGamma))
        (active_mode, location) ->
      ~ In Loc Z location.
  { intros active_mode location Hmode Hcolor Hprotected.
    eapply (proj1 (proj2 (proj2 (proj2 Hmain))));
      [exact Hmode| |exact Hprotected].
    eapply independent_active_authority_colors_in_executing. exact Hcolor. }
  have Hexecuting_safe : forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (executing_authority_color_set CT h
          (mk_watched_frame authority sGamma rGamma) incoming)
        (active_mode, location) ->
      ~ In Loc Z location.
  { exact (proj1 (proj2 (proj2 (proj2 Hmain)))). }
  have Hresume_completed_phase : frozen_completed_colors_resume_phase_safe Z
      (executing_authority_color_set CT h
        (mk_watched_frame authority sGamma rGamma) incoming)
      policies.(suspended_frame_resume_witnesses).
  { eapply target_phase_safe_transfers_to_resume_witnesses; eauto. }
  have Hresume_active_phase : frozen_completed_colors_resume_phase_safe Z
      (independent_active_authority_colors CT h
        (mk_watched_frame authority sGamma rGamma))
      policies.(suspended_frame_resume_witnesses).
  { intros snapshot source_mode source Hsnapshot Hmode Hcolor Hroot.
    eapply Hresume_completed_phase; eauto.
    eapply independent_active_authority_colors_in_executing. exact Hcolor. }
  have Htarget_active_phase : frozen_completed_colors_resume_phase_safe Z
      (independent_active_authority_colors CT h
        (mk_watched_frame authority sGamma rGamma))
      policies.(suspended_frame_target_witnesses).
  { intros snapshot source_mode source Hsnapshot Hmode Hcolor Hroot.
    eapply Htarget_phase_safe; eauto.
    eapply independent_active_authority_colors_in_executing. exact Hcolor. }
  have Hpost_state := private_policy_statement_result_is_state CT P Z cutoff
    authority sGamma' rGamma' stack incoming snapshots
    (advance_frozen_caller_snapshots CT h'
      (mk_watched_frame authority sGamma' rGamma') snapshots)
    policies h' Hfixed.
  have Hpost_main := private_policy_statement_state_main CT P Z cutoff
    (mk_watched_frame authority sGamma' rGamma') stack incoming
    (advance_frozen_caller_snapshots CT h'
      (mk_watched_frame authority sGamma' rGamma') snapshots)
    policies h' Hpost_state.
  have Hpost_wf : wf_r_config CT sGamma' rGamma' h' :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hpost_main))))).
  have Hpost_sound : authority_context_sound h' rGamma' authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hpost_main)))))).
  inversion Heval; subst.
  assert (Hupdate :
      set_vars rGamma (update x (Iot (dom h)) (vars rGamma)) =
      update_r_env_value rGamma x (Iot (dom h))).
  { destruct rGamma. reflexivity. }
  rewrite Hupdate in Hpost_main, Hpost_wf, Hpost_sound, Hfixed,
    Hnew_temporal |- *.
  match type of Hpost_wf with
  | wf_r_config _ _ _
        (h ++ [mkObj (mkruntime_type ?runtime_q C) vals]) =>
      set (new_runtime := runtime_q) in *
  end.
  have Hframes := proj1 (proj2 (proj2 (proj2 (proj2 Hmain)))).
  have Hsounds := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hcutoffs := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
    (proj2 (proj2 Hmain)))))))).
  have Hpost_frames := proj1 (proj2 (proj2 (proj2 (proj2 Hpost_main)))).
  have Hpost_sounds := proj1 (proj2 (proj2 (proj2 (proj2
    (proj2 Hpost_main))))).
  have Hnew_cover :=
    private_resume_witnesses_cover_snapshots_after_new CT Z cutoff sGamma mt
      rGamma h x qc C args sGamma' vals qthisr new_runtime authority
      policies.(suspended_frame_resume_witnesses) snapshots Hwf Hpost_wf
      Hsound Hpost_sound Htyping Hargs (ltac:(unfold new_runtime; reflexivity))
      Hcutoff Hzone Hcover Hphase Hroots Hnested_covered Hnested_safe
      Hactive_safe.
  have Hnew_phase :=
    private_resume_witnesses_phase_wf_after_runtime_equivalent_heap CT h
      (h ++ [mkObj (mkruntime_type new_runtime C) vals])
      (mk_watched_frame authority sGamma rGamma)
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h))))
      policies.(suspended_frame_resume_witnesses) snapshots
      (ltac:(intros location Hlocation;
        apply r_muttype_app_preserve_old; exact Hlocation))
      (ltac:(rewrite length_app; simpl; lia)) Hpost_wf Hphase.
  have Hnew_roots :=
    private_resume_witnesses_roots_safe_after_new CT Z cutoff sGamma mt
      rGamma h x qc C args sGamma' vals qthisr new_runtime authority
      policies.(suspended_frame_resume_witnesses) snapshots Hwf Hpost_wf
      Hsound Hpost_sound Htyping Hargs (ltac:(unfold new_runtime; reflexivity))
      Hcutoff Hzone Hphase Hroots Hactive_safe.
  have Hnew_nested :=
    private_resume_witnesses_nested_resume_safe_after_new CT Z cutoff sGamma
      mt rGamma h x qc C args sGamma' vals qthisr new_runtime authority
      policies.(suspended_frame_resume_witnesses) snapshots Hwf Hpost_wf
      Hsound Hpost_sound Htyping Hargs (ltac:(unfold new_runtime; reflexivity))
      Hcutoff Hzone Hphase Hroots Hwitness_nested Hactive_safe.
  have Hnew_completed :=
    private_resume_witnesses_completed_safe_after_new CT Z cutoff sGamma mt
      rGamma h x qc C args sGamma' vals qthisr new_runtime authority incoming
      policies.(suspended_frame_resume_witnesses) snapshots Hwf Hpost_wf
      Hsound Hpost_sound Hincoming_runtime Htyping Hargs
      (ltac:(unfold new_runtime; reflexivity)) Hcutoff Hzone Hphase
      Hactive_safe Hwitness_completed.
  have Hnew_stack_safe :=
    private_resume_witness_stack_safe_after_new CT Z cutoff sGamma mt
      rGamma h x qc C args sGamma' vals qthisr new_runtime authority incoming
      policies.(suspended_frame_resume_witnesses) Hwf Hpost_wf Hsound
      Hpost_sound Hincoming_runtime Htyping Hargs
      (ltac:(unfold new_runtime; reflexivity)) Hcutoff Hzone Hactive_safe
      Hwitness_stack_safe.
  have Hnew_before :=
    advance_frozen_caller_snapshots_before_boundaries CT
      (h ++ [mkObj (mkruntime_type new_runtime C) vals])
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h))))
      policies.(suspended_frame_resume_witnesses) stack Hwitness_before.
  have Hnew_target_cover :=
    private_resume_witnesses_cover_snapshots_after_advance CT
      (h ++ [mkObj (mkruntime_type new_runtime C) vals]) Z
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h))))
      policies.(suspended_frame_target_witnesses) snapshots Htarget_cover.
  have Hnew_target_stack_safe :=
    private_target_witness_stack_structural_after_runtime_equivalent_heap CT h
      (h ++ [mkObj (mkruntime_type new_runtime C) vals])
      (mk_watched_frame authority sGamma rGamma)
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h))))
      policies.(suspended_frame_target_witnesses)
      (ltac:(intros location Hlocation;
        apply r_muttype_app_preserve_old; exact Hlocation))
      (ltac:(rewrite length_app; simpl; lia)) Hpost_wf
      Htarget_stack_safe.
  have Hnew_target_phase_safe :=
    frozen_completed_colors_resume_phase_safe_after_new CT Z cutoff sGamma mt
      rGamma h x qc C args sGamma' vals qthisr new_runtime authority incoming
      policies.(suspended_frame_target_witnesses) Hwf Hpost_wf Hsound
      Hpost_sound Hincoming_runtime Htyping Hargs
      (ltac:(unfold new_runtime; reflexivity)) Hcutoff Hzone Htarget_roots
      Htarget_exposure Htarget_phase_safe Hactive_safe.
  have Hnew_target_cross_phase :=
    private_target_exposures_support_resume_phase_after_new CT Z cutoff sGamma
      mt rGamma h x qc C args sGamma' vals qthisr new_runtime authority
      policies.(suspended_frame_target_witnesses)
      policies.(suspended_frame_resume_witnesses) Hwf Hpost_wf Hsound
      Hpost_sound Htyping Hargs (ltac:(unfold new_runtime; reflexivity))
      Hcutoff Hzone Htarget_exposure Hwitness_roots Hwitness_exposure
      Htarget_cross_phase Hresume_active_phase Hactive_safe.
  have Hnew_target_nested_phase :=
    frozen_target_nested_phase_safe_after_new CT Z cutoff sGamma mt rGamma h
      x qc C args sGamma' vals qthisr new_runtime authority
      policies.(suspended_frame_target_witnesses) Hwf Hpost_wf Hsound
      Hpost_sound Htyping Hargs (ltac:(unfold new_runtime; reflexivity))
      Hcutoff Hzone Htarget_runtime Htarget_closed Htarget_roots
      Htarget_exposure Htarget_nested_phase Htarget_active_phase Hactive_safe.
  have Hnew_target_before :=
    advance_frozen_caller_snapshots_before_boundaries CT
      (h ++ [mkObj (mkruntime_type new_runtime C) vals])
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h))))
      policies.(suspended_frame_target_witnesses) stack Htarget_before.
  have Hnew_target_support :=
    private_target_supports_resume_witnesses_after_advance CT
      (h ++ [mkObj (mkruntime_type new_runtime C) vals])
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h))))
      policies.(suspended_frame_target_witnesses)
      policies.(suspended_frame_resume_witnesses) Htarget_support.
  have Hnew_target_history :=
    private_target_history_supports_resume_phase_after_new CT Z cutoff sGamma
      mt rGamma h x qc C args sGamma' vals qthisr new_runtime authority
      policies.(suspended_frame_target_witnesses)
      policies.(suspended_frame_resume_witnesses) Hwf Hpost_wf Hsound
      Hpost_sound Htyping Hargs (ltac:(unfold new_runtime; reflexivity))
      Hcutoff Hzone Hwitness_exposure Hactive_safe Htarget_history.
  have Heval_new : eval_stmt CT rGamma h (SNew x qc C args) OK
      (update_r_env_value rGamma x (Iot (dom h)))
      (h ++ [mkObj (mkruntime_type new_runtime C) vals]).
  { econstructor; eauto. }
  have Hnew_target_temporal :=
    private_target_witness_temporal_after_new CT P Z cutoff authority sGamma
      mt rGamma h stack incoming policies.(suspended_frame_target_witnesses)
      x qc C args sGamma' vals qthisr new_runtime Hmain Hpost_main Htyping Hargs
      (ltac:(unfold new_runtime; reflexivity)) Heval_new Htarget_stack_safe
      Htarget_temporal.
  have Hnew_target_state : private_target_witness_state CT
      (h ++ [mkObj (mkruntime_type new_runtime C) vals]) Z cutoff
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h)))) incoming
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type new_runtime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) snapshots)
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type new_runtime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h))))
        policies.(suspended_frame_target_witnesses))
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type new_runtime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h))))
        policies.(suspended_frame_resume_witnesses)) stack.
  { unfold private_target_witness_state.
    split; [exact Hnew_target_cover|].
    split; [exact Hnew_target_stack_safe|].
    split; [exact Hnew_target_phase_safe|].
    split; [exact Hnew_target_cross_phase|].
    split; [exact Hnew_target_nested_phase|].
    split; [exact Hnew_target_before|].
    split; [exact Hnew_target_support|].
    split; [exact Hnew_target_history|exact Hnew_target_temporal]. }
  eapply private_policy_statement_result_advance_witnesses; eauto.
Qed.

Lemma private_policy_statement_after_assignment :
  forall CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    policies x expression old value,
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming h ->
    private_policy_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots
      policies h ->
    stmt_typing CT sGamma mt (SVarAss x expression) sGamma ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma x = Some old ->
    eval_expr CT rGamma h expression value OK rGamma h ->
    private_policy_statement_result CT P Z cutoff authority sGamma
      (update_r_env_value rGamma x value) stack incoming snapshots
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority sGamma
          (update_r_env_value rGamma x value)) snapshots) policies h.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    policies x expression old value Hpotential
    [Hprivate [Haligned [Hvalid Hpolicy]]]
    Htyping Hscope Hvalue Heval.
  eapply private_policy_statement_result_from_principled.
  - eapply private_principled_statement_after_assignment; eauto.
  - exact Haligned.
  - exact Hvalid.
Qed.

Lemma private_policy_statement_after_local :
  forall CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    policies T x sGamma',
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming h ->
    private_policy_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots
      policies h ->
    stmt_typing CT sGamma mt (SLocal T x) sGamma' ->
    runtime_getVal rGamma x = None ->
    private_policy_statement_result CT P Z cutoff authority sGamma'
      (set_vars rGamma (vars rGamma ++ [Null_a])) stack incoming snapshots
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority sGamma'
          (set_vars rGamma (vars rGamma ++ [Null_a]))) snapshots) policies h.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    policies T x sGamma' Hpotential
    [Hprivate [Haligned [Hvalid Hpolicy]]] Htyping
    Hnone.
  eapply private_policy_statement_result_from_principled.
  - eapply private_principled_statement_after_local; eauto.
  - exact Haligned.
  - exact Hvalid.
Qed.

Lemma private_policy_statement_after_field_write :
  forall CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    policies x field y sGamma' rGamma' h',
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming h ->
    private_policy_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots
      policies h ->
    stmt_typing CT sGamma mt (SFldWrite x field y) sGamma' ->
    readonly_state_method_scope mt ->
    eval_stmt CT rGamma h (SFldWrite x field y) OK rGamma' h' ->
    private_policy_statement_result CT P Z cutoff authority sGamma' rGamma'
      stack incoming snapshots
      (advance_frozen_caller_snapshots CT h'
        (mk_watched_frame authority sGamma' rGamma') snapshots) policies h'.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    policies x field y sGamma' rGamma' h' Hpotential
    [Hprivate [Haligned [Hvalid Hpolicy]]] Htyping Hscope Heval.
  eapply private_policy_statement_result_from_principled.
  - eapply private_principled_statement_after_field_write; eauto.
  - exact Haligned.
  - eapply private_frame_join_policies_valid_heap_growth; [|exact Hvalid].
    eapply eval_stmt_preserves_heap_domain_simple. exact Heval.
Qed.

Lemma private_policy_statement_after_new :
  forall CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    policies x qc C args sGamma' rGamma' h',
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming h ->
    private_policy_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots
      policies h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    eval_stmt CT rGamma h (SNew x qc C args) OK rGamma' h' ->
    private_policy_statement_result CT P Z cutoff authority sGamma' rGamma'
      stack incoming snapshots
      (advance_frozen_caller_snapshots CT h'
        (mk_watched_frame authority sGamma' rGamma') snapshots) policies h'.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    policies x qc C args sGamma' rGamma' h' Hpotential
    [Hprivate [Haligned [Hvalid Hpolicy]]] Htyping Heval.
  eapply private_policy_statement_result_from_principled.
  - eapply private_principled_statement_after_new; eauto.
  - exact Haligned.
  - eapply private_frame_join_policies_valid_heap_growth; [|exact Hvalid].
    eapply eval_stmt_preserves_heap_domain_simple. exact Heval.
Qed.

Lemma private_principled_statement_state_resumed_separated :
  forall CT P Z cutoff active stack incoming snapshots policies h,
    private_principled_statement_state CT P Z cutoff active stack incoming
      snapshots h ->
    executing_resumed_authority_colors_separated CT h Z
      policies.(active_frame_join_targets) active incoming.
Proof.
  intros CT P Z cutoff active stack incoming snapshots policies h
    [[Hfrozen Hfresh_tail] Hdisjoint].
  destruct Hfrozen as [Hprincipled Hcertificates].
  have Hmain := proj1 Hprincipled.
  have Hseparated := proj1 (proj2 (proj2 (proj2 Hmain))).
  eapply executing_authority_separation_implies_resumed_separation.
  exact Hseparated.
Qed.

Lemma private_policy_statement_enter_channel_free_from_parts :
  forall CT P Z cutoff caller stack incoming snapshots policies h boundary
    callee caller_colors,
    private_policy_statement_state CT P Z cutoff caller stack incoming
      snapshots policies h ->
    boundary.(boundary_caller) = caller ->
    boundary.(boundary_entry_cutoff) = dom h ->
    callee = mk_watched_frame
      (call_authority caller.(frame_authority)
        boundary.(boundary_receiver_view))
      boundary.(boundary_callee_entry_senv)
      boundary.(boundary_callee_entry_renv) ->
    entry_ownership_channel_free boundary ->
    private_fresh_frozen_statement_state CT P Z cutoff callee
      (boundary :: stack) caller_colors
      (enter_nested_frozen_caller_snapshots CT h caller callee caller_colors
        snapshots) h ->
    private_policy_statement_state CT P Z cutoff callee (boundary :: stack)
      caller_colors
      (enter_nested_frozen_caller_snapshots CT h caller callee caller_colors
        snapshots)
      (enter_private_frame_join_policies callee
        (Some (nested_frozen_call_head CT h caller callee caller_colors
          snapshots)) policies) h.
Proof.
  intros CT P Z cutoff caller stack incoming snapshots policies h boundary
    callee caller_colors
    [Hprivate [Haligned [Hvalid Hpolicy]]] Hboundary Hcutoff Hcallee Hfree
    Hentry.
  have Hpost := private_principled_statement_enter_channel_free_from_parts
    CT P Z cutoff caller stack incoming snapshots h boundary callee
    caller_colors Hprivate Hboundary Hcallee Hfree Hentry.
  split; [exact Hpost|]. split.
  - eapply enter_private_frame_join_policies_aligned. exact Haligned.
  - split.
    + have Hentry_main := proj1 (proj1 (proj1 Hentry)).
      have Hcallee_wf :=
        proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hentry_main))))).
      eapply enter_private_frame_join_policies_valid; eauto.
    + eapply private_principled_statement_state_resumed_separated.
      exact Hpost.
Qed.

Lemma private_policy_statement_enter_untracked_from_parts :
  forall CT P Z cutoff old_active new_active boundary stack old_incoming
    new_incoming snapshots policies h,
    private_policy_statement_state CT P Z cutoff old_active stack old_incoming
      snapshots policies h ->
    boundary.(boundary_caller) = old_active ->
    boundary.(boundary_entry_cutoff) = dom h ->
    private_fresh_frozen_statement_state CT P Z cutoff new_active
      (boundary :: stack) new_incoming
      (None :: advance_frozen_caller_snapshots CT h new_active snapshots) h ->
    wf_r_config CT new_active.(frame_senv) new_active.(frame_renv) h ->
    authority_context_sound h new_active.(frame_renv)
      new_active.(frame_authority) ->
    private_policy_statement_state CT P Z cutoff new_active
      (boundary :: stack) new_incoming
      (None :: advance_frozen_caller_snapshots CT h new_active snapshots)
      (enter_private_frame_join_policies new_active
        (Some (nested_frozen_call_head CT h old_active new_active new_incoming
          snapshots)) policies) h.
Proof.
  intros CT P Z cutoff old_active new_active boundary stack old_incoming
    new_incoming snapshots policies h
    [Hold [Haligned [Hvalid Hpolicy]]] Hcaller Hcutoff Hentry Hwf
    Hsound.
  have Hpost := private_principled_statement_enter_untracked_from_parts CT P Z
    cutoff old_active new_active boundary stack old_incoming new_incoming
    snapshots h Hold Hentry Hwf Hsound.
  split; [exact Hpost|]. split.
  - eapply enter_private_frame_join_policies_aligned. exact Haligned.
  - split.
    + eapply enter_private_frame_join_policies_valid; eauto.
    + eapply private_principled_statement_state_resumed_separated.
      exact Hpost.
Qed.

Lemma private_policy_statement_enter_untracked_advanced_from_parts :
  forall CT P Z cutoff old_active new_active boundary stack old_incoming
    new_incoming snapshots policies h target_witness caller_witness,
    private_policy_statement_state CT P Z cutoff old_active stack old_incoming
      snapshots policies h ->
    boundary.(boundary_caller) = old_active ->
    boundary.(boundary_entry_cutoff) = dom h ->
    private_fresh_frozen_statement_state CT P Z cutoff new_active
      (boundary :: stack) new_incoming
      (None :: advance_frozen_caller_snapshots CT h new_active snapshots) h ->
    wf_r_config CT new_active.(frame_senv) new_active.(frame_renv) h ->
    authority_context_sound h new_active.(frame_renv)
      new_active.(frame_authority) ->
    private_policy_statement_state CT P Z cutoff new_active
      (boundary :: stack) new_incoming
      (None :: advance_frozen_caller_snapshots CT h new_active snapshots)
      (enter_private_frame_join_policies_advanced CT h new_active
        target_witness caller_witness policies) h.
Proof.
  intros CT P Z cutoff old_active new_active boundary stack old_incoming
    new_incoming snapshots policies h target_witness caller_witness
    [Hold [Haligned [Hvalid Hpolicy]]] Hcaller Hcutoff Hentry Hwf
    Hsound.
  have Hpost := private_principled_statement_enter_untracked_from_parts CT P Z
    cutoff old_active new_active boundary stack old_incoming new_incoming
    snapshots h Hold Hentry Hwf Hsound.
  split; [exact Hpost|]. split.
  - eapply enter_private_frame_join_policies_advanced_aligned. exact Haligned.
  - split.
    + eapply enter_private_frame_join_policies_advanced_valid; eauto.
    + eapply private_principled_statement_state_resumed_separated.
      exact Hpost.
Qed.

Lemma private_policy_statement_after_tracked_pop_from_parts :
  forall CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    caller_incoming policies caller_policies,
    private_policy_statement_state CT P Z cutoff active (boundary :: stack)
      incoming (head_slot :: snapshots) policies h ->
    leave_private_frame_join_policies policies = Some caller_policies ->
    executing_resumed_authority_call_pop_safe CT h Z active incoming
      caller_policies.(active_frame_join_targets) caller caller_incoming ->
    private_principled_statement_state CT P Z cutoff caller stack
      caller_incoming
      (advance_frozen_caller_snapshots CT h caller snapshots) h ->
    private_policy_statement_state CT P Z cutoff caller stack caller_incoming
      (advance_frozen_caller_snapshots CT h caller snapshots) caller_policies
      h.
Proof.
  intros CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    caller_incoming policies caller_policies
    [Hprivate [Haligned [Hvalid Hpolicy]]] Hleave Hpop Hpost.
  split; [exact Hpost|]. split.
  - eapply leave_private_frame_join_policies_aligned; eauto.
  - split.
    + have Hmain := proj1 (proj1 (proj1 (proj1 Hprivate))).
      destruct Hmain as
        (Hcontains & Hconfined & Hruntime & Hseparated & Hframes & Hsounds &
          Hhistory_cutoff & Hzone & Hchain & Hcutoffs).
      eapply leave_private_frame_join_policies_valid; eauto.
      exact (Forall_inv Hcutoffs).
    + have Hmain := proj1 (proj1 (proj1 (proj1 Hprivate))).
      have Hcallee_separated := proj1 (proj2 (proj2 (proj2 Hmain))).
      eapply executing_resumed_authority_colors_separated_after_call_pop;
        eauto.
Qed.

Lemma private_policy_statement_after_untracked_pop_from_parts :
  forall CT P Z cutoff active boundary stack incoming snapshots h caller
    caller_incoming policies caller_policies,
    private_policy_statement_state CT P Z cutoff active (boundary :: stack)
      incoming (None :: snapshots) policies h ->
    leave_private_frame_join_policies policies = Some caller_policies ->
    executing_resumed_authority_call_pop_safe CT h Z active incoming
      caller_policies.(active_frame_join_targets) caller caller_incoming ->
    private_principled_statement_state CT P Z cutoff caller stack
      caller_incoming
      (advance_frozen_caller_snapshots CT h caller snapshots) h ->
    private_policy_statement_state CT P Z cutoff caller stack caller_incoming
      (advance_frozen_caller_snapshots CT h caller snapshots) caller_policies
      h.
Proof.
  intros. eapply private_policy_statement_after_tracked_pop_from_parts;
    eauto.
Qed.

(** Complete non-null [None]-slot reconstruction.  The reusable tail-color
    reflection used by this reconstruction is exported by the private layer
    so the policy-only tracked-head pop can consume the same temporal fact.
    The two semantic inputs
    are deliberately root-scoped and policy-scoped: the recursive body proof
    reflects resumed colors at older frozen roots into completed callee
    colors, while [Hpop] establishes separation for the target-restricted
    resumed caller.  Everything else is structural return bookkeeping. *)
Lemma private_policy_statement_after_untracked_nonnull_pop :
  forall CT P Z cutoff active boundary stack active_incoming snapshots h
    caller_incoming policies caller_policies caller_authority caller_senv
    caller_renv destination destination_type return_location,
    let caller_post := mk_watched_frame caller_authority caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) in
    private_policy_statement_state CT P Z cutoff active (boundary :: stack)
      active_incoming (None :: snapshots) policies h ->
    leave_private_frame_join_policies policies = Some caller_policies ->
    principled_phased_authority_live_history_state CT P Z cutoff caller_post
      stack caller_incoming h ->
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
    Hstate Hleave Hpost Hboundary Hdestination Hactive_wf Hactive_sound
    Hcaller_wf Hcaller_post_wf Hcaller_post_sound Hdestination_type
    Hreturn_owned Hreturn_runtime Hroots_reflect Hpop.
  have Hprivate := proj1 (proj1 Hstate).
  have Hreturn_safety : private_frozen_snapshot_return_safety CT h Z
      caller_post caller_incoming
      (advance_frozen_caller_snapshots CT h caller_post snapshots).
  { have Hbody_frozen := proj1 Hprivate.
    have Hstructural : private_frozen_snapshot_structural_state CT h
        caller_post (advance_frozen_caller_snapshots CT h caller_post snapshots)
        stack.
    { eapply private_frozen_statement_advance_tail_structural_state with
        (active := active) (boundary := boundary)
        (incoming := active_incoming) (slot := None); eauto. }
    destruct (private_fresh_return_partitions_after_nonnull_pop CT P Z cutoff
      active boundary stack active_incoming None snapshots h caller_authority
      caller_senv caller_renv destination destination_type return_location
      Hprivate Hboundary Hdestination Hactive_wf Hactive_sound Hcaller_wf
      Hcaller_post_wf Hcaller_post_sound Hdestination_type Hreturn_owned
      Hreturn_runtime) as [Hcomponents [Hprospective Hafter]].
    unfold caller_post in Hcomponents, Hprospective, Hafter |- *.
    eapply private_frozen_snapshot_return_safety_after_untracked_return_parts
      with (callee := active) (boundary := boundary)
        (incoming := active_incoming) (head_slot := None); eauto. }
  have Hpost_fresh : private_fresh_frozen_statement_state CT P Z cutoff
      caller_post stack caller_incoming
      (advance_frozen_caller_snapshots CT h caller_post snapshots) h.
  { unfold caller_post in *.
    eapply private_fresh_frozen_statement_after_nonnull_return_parts; eauto. }
  have Hpost_disjoint : frozen_caller_snapshots_newer_resume_exposure_disjoint
      (advance_frozen_caller_snapshots CT h caller_post snapshots).
  { have Hbody_frozen := proj1 Hprivate.
    have Hstructural : private_frozen_snapshot_structural_state CT h
        caller_post (advance_frozen_caller_snapshots CT h caller_post snapshots)
        stack.
    { eapply private_frozen_statement_advance_tail_structural_state with
        (active := active) (boundary := boundary)
        (incoming := active_incoming) (slot := None); eauto. }
    destruct (private_fresh_return_partitions_after_nonnull_pop CT P Z cutoff
      active boundary stack active_incoming None snapshots h caller_authority
      caller_senv caller_renv destination destination_type return_location
      Hprivate Hboundary Hdestination Hactive_wf Hactive_sound Hcaller_wf
      Hcaller_post_wf Hcaller_post_sound Hdestination_type Hreturn_owned
      Hreturn_runtime) as [Hcomponents [Hprospective Hafter]].
    unfold caller_post in Hcomponents, Hprospective, Hafter |- *.
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

Lemma private_policy_statement_after_untracked_null_pop :
  forall CT P Z cutoff active boundary stack active_incoming snapshots h
    caller_incoming policies caller_policies caller_authority caller_senv
    caller_renv destination destination_type,
    let caller_post := mk_watched_frame caller_authority caller_senv
      (update_r_env_value caller_renv destination Null_a) in
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
      (update_r_env_value caller_renv destination Null_a) h ->
    authority_context_sound h caller_renv caller_authority ->
    authority_context_sound h
      (update_r_env_value caller_renv destination Null_a) caller_authority ->
    static_getType caller_senv destination = Some destination_type ->
    (forall snapshot mode source,
      List.In (Some snapshot) snapshots ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT h caller_post caller_incoming)
        (mode, source) ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
      exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h active active_incoming)
          (callee_mode, source)) ->
    executing_resumed_authority_call_pop_safe CT h Z active active_incoming
      caller_policies.(active_frame_join_targets) caller_post caller_incoming ->
    private_policy_statement_state CT P Z cutoff caller_post stack
      caller_incoming
      (advance_frozen_caller_snapshots CT h caller_post snapshots)
      caller_policies h.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshots h
    caller_incoming policies caller_policies caller_authority caller_senv
    caller_renv destination destination_type caller_post Hstate Hleave Hpost
    Hboundary Hdestination Hcaller_wf Hcaller_post_wf Hcaller_sound
    Hcaller_post_sound Hdestination_type Hroots_reflect Hpop.
  have Hprivate := proj1 (proj1 Hstate).
  have Hreturn_safety : private_frozen_snapshot_return_safety CT h Z
      caller_post caller_incoming
      (advance_frozen_caller_snapshots CT h caller_post snapshots).
  { have Hbody_frozen := proj1 Hprivate.
    have Hstructural : private_frozen_snapshot_structural_state CT h
        caller_post (advance_frozen_caller_snapshots CT h caller_post snapshots)
        stack.
    { eapply private_frozen_statement_advance_tail_structural_state with
        (active := active) (boundary := boundary)
        (incoming := active_incoming) (slot := None); eauto. }
    destruct (private_fresh_return_partitions_after_null_pop CT P Z cutoff
      active boundary stack active_incoming None snapshots h caller_authority
      caller_senv caller_renv destination destination_type Hprivate Hboundary
      Hdestination Hcaller_wf Hcaller_sound Hdestination_type) as
      [Hcomponents [Hprospective Hafter]].
    unfold caller_post in Hcomponents, Hprospective, Hafter |- *.
    eapply private_frozen_snapshot_return_safety_after_untracked_return_parts
      with (callee := active) (boundary := boundary)
        (incoming := active_incoming) (head_slot := None); eauto. }
  have Hpost_fresh : private_fresh_frozen_statement_state CT P Z cutoff
      caller_post stack caller_incoming
      (advance_frozen_caller_snapshots CT h caller_post snapshots) h.
  { unfold caller_post in *.
    eapply private_fresh_frozen_statement_after_null_return_parts; eauto. }
  have Hpost_disjoint : frozen_caller_snapshots_newer_resume_exposure_disjoint
      (advance_frozen_caller_snapshots CT h caller_post snapshots).
  { have Hbody_frozen := proj1 Hprivate.
    have Hstructural : private_frozen_snapshot_structural_state CT h
        caller_post (advance_frozen_caller_snapshots CT h caller_post snapshots)
        stack.
    { eapply private_frozen_statement_advance_tail_structural_state with
        (active := active) (boundary := boundary)
        (incoming := active_incoming) (slot := None); eauto. }
    destruct (private_fresh_return_partitions_after_null_pop CT P Z cutoff
      active boundary stack active_incoming None snapshots h caller_authority
      caller_senv caller_renv destination destination_type Hprivate Hboundary
      Hdestination Hcaller_wf Hcaller_sound Hdestination_type) as
      [Hcomponents [Hprospective Hafter]].
    unfold caller_post in Hcomponents, Hprospective, Hafter |- *.
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

Definition call_pop_authority_color_set
  (CT : class_table) (h : heap)
  (callee : watched_frame) (boundary : watched_boundary)
  (callee_incoming : Ensemble authority_flow_state)
  (eligible : Ensemble Loc)
  (caller : watched_frame)
  (caller_incoming : Ensemble authority_flow_state) :
  Ensemble authority_flow_state :=
  resumed_authority_frame_closure CT h eligible caller
    (Union authority_flow_state caller_incoming
      (Union authority_flow_state
        (phased_authority_return_closure h callee boundary
          (demote_authority_set
            (executing_authority_color_set CT h callee callee_incoming)))
        (phased_frame_powered_seeds CT h caller))).

Definition call_pop_authority_colors_separated
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (callee : watched_frame) (boundary : watched_boundary)
  (callee_incoming : Ensemble authority_flow_state)
  (eligible : Ensemble Loc)
  (caller : watched_frame)
  (caller_incoming : Ensemble authority_flow_state) : Prop :=
  forall mode protected,
    authority_mode_dangerous mode ->
    In authority_flow_state
      (call_pop_authority_color_set CT h callee boundary callee_incoming
        eligible caller caller_incoming) (mode, protected) ->
    ~ In Loc Z protected.

(** Proof-local residual obligation after return demotion.  It talks only
    about paths that start at an independently owned caller capability; the
    preceding phase lemma proves that every dangerous path originating in a
    demoted return has this form. *)
Definition caller_owned_suffix_pop_safe
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (callee : watched_frame)
  (callee_incoming : Ensemble authority_flow_state)
  (caller : watched_frame) : Prop :=
  forall anchor mode location,
    frame_owned_location CT h caller anchor ->
    phased_authority_frame_connected CT h caller
      (FlowPowered, anchor) (mode, location) ->
    authority_mode_dangerous mode ->
    (exists callee_mode,
      authority_mode_dangerous callee_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h callee callee_incoming)
        (callee_mode, location)) \/
    ~ In Loc Z location.

Lemma returned_call_pop_colors_are_safe_from_owned_suffixes :
  forall CT h Z callee boundary callee_incoming caller mode location,
    caller_owned_suffix_pop_safe CT h Z callee callee_incoming caller ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (phased_authority_frame_closure CT h caller
        (phased_authority_return_closure h callee boundary
          (demote_authority_set
            (executing_authority_color_set CT h callee callee_incoming))))
      (mode, location) ->
    (exists callee_mode,
      authority_mode_dangerous callee_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h callee callee_incoming)
        (callee_mode, location)) \/
    ~ In Loc Z location.
Proof.
  intros CT h Z callee boundary callee_incoming caller mode location
    Hsuffix Hmode Hcolor.
  destruct (returned_authority_dangerous_has_caller_owned_promotion CT h
    callee boundary
    (executing_authority_color_set CT h callee callee_incoming) caller mode
    location Hmode Hcolor) as [anchor [Howned Hpath]].
  eapply Hsuffix; eauto.
Qed.

(** Separation of the complete restricted pop color set follows from the
    two phase-local certificates.  Caller seeds use the persistent eligible
    target policy directly.  A returned seed is demoted first; if it later
    becomes dangerous, the existing promotion decomposition exposes a
    caller-owned suffix, so either the same location was already a safe
    callee color or the suffix is outside the protected zone. *)
Lemma call_pop_authority_colors_separated_from_parts :
  forall CT h Z callee boundary callee_incoming eligible caller
    caller_incoming,
    executing_resumed_authority_colors_separated CT h Z eligible caller
      caller_incoming ->
    executing_authority_colors_separated CT h Z callee callee_incoming ->
    caller_owned_suffix_pop_safe CT h Z callee callee_incoming caller ->
    call_pop_authority_colors_separated CT h Z callee boundary
      callee_incoming eligible caller caller_incoming.
Proof.
  intros CT h Z callee boundary callee_incoming eligible caller
    caller_incoming Hcaller Hcallee Hsuffix mode location Hmode
    [seed [Hseed Hpath]] Hprotected.
  inversion Hseed as [source Hincoming | source Hrest]; subst.
  - eapply Hcaller; [exact Hmode| |exact Hprotected].
    eexists. split; [left; exact Hincoming|exact Hpath].
  - inversion Hrest as [source' Hreturned | source' Hpowered]; subst.
    + have Hreturned_after : In authority_flow_state
        (phased_authority_frame_closure CT h caller
          (phased_authority_return_closure h callee boundary
            (demote_authority_set
              (executing_authority_color_set CT h callee
                callee_incoming)))) (mode, location).
      { eexists. split; [exact Hreturned|].
        eapply resumed_authority_frame_connected_is_phased. exact Hpath. }
      destruct (returned_call_pop_colors_are_safe_from_owned_suffixes CT h Z
        callee boundary callee_incoming caller mode location Hsuffix Hmode
        Hreturned_after) as
        [[callee_mode [Hcallee_mode Hcallee_color]] | Houtside].
      * eapply Hcallee; eauto.
      * exact (Houtside Hprotected).
    + eapply Hcaller; [exact Hmode| |exact Hprotected].
      eexists. split; [right; exact Hpowered|exact Hpath].
Qed.

Lemma executing_authority_color_set_included_in_call_pop :
  forall CT h callee boundary callee_incoming eligible caller
    caller_incoming,
    caller.(frame_authority) = Mut_r ->
    Included authority_flow_state
      (executing_authority_color_set CT h caller caller_incoming)
      (call_pop_authority_color_set CT h callee boundary callee_incoming
        eligible caller caller_incoming).
Proof.
  intros CT h callee boundary callee_incoming eligible caller caller_incoming
    Hauthority.
  unfold executing_authority_color_set, call_pop_authority_color_set.
  intros state [seed [Hseed Hpath]].
  exists seed. split.
  - inversion Hseed; subst.
    + left. exact H.
    + right. right. exact H.
  - eapply phased_authority_frame_connected_is_resumed_under_mutable; eauto.
Qed.

Lemma call_pop_authority_colors_separated_implies_safe :
  forall CT h Z callee boundary callee_incoming eligible caller
    caller_incoming,
    caller.(frame_authority) = Mut_r ->
    call_pop_authority_colors_separated CT h Z callee boundary
      callee_incoming eligible caller caller_incoming ->
    executing_authority_call_pop_safe CT h Z callee callee_incoming
      caller caller_incoming.
Proof.
  intros CT h Z callee boundary callee_incoming eligible caller
    caller_incoming Hauthority Hseparated mode location Hmode Hcolor.
  right. intros Hprotected.
  eapply Hseparated; [exact Hmode| |exact Hprotected].
  eapply executing_authority_color_set_included_in_call_pop; eauto.
Qed.

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

(** Every capability independently owned by the resumed caller is already
    powered in the completed callee phase.  An unchanged root was a caller
    capability at entry and hence was injected into [callee_incoming]; the
    destination root, when it is a capability, is the callee's return root.
    Retained descendants are then followed in the final heap. *)
Lemma caller_post_owned_is_callee_powered :
  forall CT caller_authority caller_senv caller_renv caller_h
    destination destination_type receiver receiver_location receiver_type
    (entry_senv : s_env) (entry_renv : r_env)
    (origins : call_boundary_origins
      (mk_watched_frame caller_authority caller_senv caller_renv)
      (sqtype receiver_type) entry_senv entry_renv)
    callee_senv callee_renv callee_h
    return_var body_return_type runtime_sig static_sig return_location
    callee caller_incoming callee_incoming location,
    wf_r_config CT caller_senv caller_renv caller_h ->
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    static_getType caller_senv receiver = Some receiver_type ->
    runtime_getVal caller_renv receiver = Some (Iot receiver_location) ->
    wf_r_config CT callee_senv callee_renv callee_h ->
    static_getType callee_senv return_var = Some body_return_type ->
    runtime_getVal callee_renv return_var = Some (Iot return_location) ->
    qualified_type_subtype CT body_return_type (mret runtime_sig) ->
    method_signature_refinement CT runtime_sig static_sig ->
    qualified_type_subtype CT
      (vpa_mutability_tt_readonly_state receiver_type (mret static_sig))
      destination_type ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location))
      callee_h ->
    authority_context_sound callee_h caller_renv caller_authority ->
    callee = mk_watched_frame
      (call_authority caller_authority (sqtype receiver_type))
      callee_senv callee_renv ->
    callee_incoming = executing_authority_color_set CT caller_h
      (mk_watched_frame caller_authority caller_senv caller_renv)
      caller_incoming ->
    frame_owned_location CT callee_h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination
          (Iot return_location))) location ->
    In authority_flow_state
      (executing_authority_color_set CT callee_h callee callee_incoming)
      (FlowPowered, location).
Proof.
  intros CT caller_authority caller_senv caller_renv caller_h destination
    destination_type receiver receiver_location receiver_type entry_senv
    entry_renv origins callee_senv callee_renv callee_h return_var
    body_return_type runtime_sig static_sig return_location callee
    caller_incoming callee_incoming location Hcaller_wf Hdestination_nonzero
    Hdestination_type Hreceiver_type Hreceiver_value Hcallee_wf Hreturn_type
    Hreturn_value Hbody_sub Hrefine Hresult_sub Hcaller_post_wf
    Hcaller_sound Hcallee Hincoming [root [Hroot Hreachable]].
  have Hreflected := call_return_live_root_reflects_before_pop CT
    caller_authority caller_senv caller_renv caller_h [] destination
    destination_type receiver receiver_location receiver_type entry_senv
    entry_renv origins callee_senv callee_renv callee_h return_var
    body_return_type runtime_sig static_sig return_location root Hcaller_wf
    Hdestination_nonzero Hdestination_type Hreceiver_type Hreceiver_value
    Hcallee_wf Hreturn_type Hreturn_value Hbody_sub Hrefine Hresult_sub
    Hcaller_post_wf Hcaller_sound (or_introl Hroot).
  assert (Hroot_powered : In authority_flow_state
      (executing_authority_color_set CT callee_h callee callee_incoming)
      (FlowPowered, root)).
  { destruct Hreflected as
      [Hcallee_root | [boundary [Hin Hcaller_root]]].
    - apply executing_authority_owned_is_powered.
      rewrite Hcallee. exists root. split; [exact Hcallee_root|constructor].
    - simpl in Hin. destruct Hin as [Heq | Hnone]; [subst boundary|contradiction].
      have Hcaller_root_owned : frame_owned_location CT caller_h
          (mk_watched_frame caller_authority caller_senv caller_renv) root.
      { exists root. split; [exact Hcaller_root|constructor]. }
      have Hcaller_color : In authority_flow_state
          (executing_authority_color_set CT caller_h
            (mk_watched_frame caller_authority caller_senv caller_renv)
            caller_incoming) (FlowPowered, root).
      { eapply executing_authority_owned_is_powered.
        exact Hcaller_root_owned. }
      have Hentry_color : In authority_flow_state callee_incoming
          (FlowPowered, root).
      { rewrite Hincoming. exact Hcaller_color. }
      exists (FlowPowered, root). split; [left; exact Hentry_color|].
      apply rt_refl. }
  eapply executing_authority_dangerous_retained_reachable.
  - left. reflexivity.
  - exact Hroot_powered.
  - exact Hreachable.
Qed.

(** In an immutable caller, installing an [RDM] result creates no capability
    root.  Every capability owned after the pop therefore starts at an old
    caller root, which was injected into the callee's incoming colors, and
    follows only retained edges of the final heap. *)
Lemma immutable_rdm_caller_owned_is_callee_powered :
  forall CT caller_senv caller_renv caller_h callee_h destination
    destination_type value callee caller_incoming callee_incoming location,
    static_getType caller_senv destination = Some destination_type ->
    sqtype destination_type = RDM ->
    callee_incoming = executing_authority_color_set CT caller_h
      (mk_watched_frame Imm_r caller_senv caller_renv) caller_incoming ->
    frame_owned_location CT callee_h
      (mk_watched_frame Imm_r caller_senv
        (update_r_env_value caller_renv destination value)) location ->
    In authority_flow_state
      (executing_authority_color_set CT callee_h callee callee_incoming)
      (FlowPowered, location).
Proof.
  intros CT caller_senv caller_renv caller_h callee_h destination
    destination_type value callee caller_incoming callee_incoming location
    Hdestination Hrdm Hincoming Howned.
  apply frame_owned_location_iff_active_live in Howned.
  have Hold_live := immutable_rdm_update_live_capability_included CT callee_h
    caller_senv caller_renv [] destination destination_type value
    Hdestination Hrdm location Howned.
  destruct Hold_live as [root [[Hroot | [boundary [Hin _]]] Hreachable]].
  2: inversion Hin.
  have Hroot_owned_old : frame_owned_location CT caller_h
      (mk_watched_frame Imm_r caller_senv caller_renv) root.
  { apply frame_owned_location_iff_active_live.
    exists root. split; [left; exact Hroot|constructor]. }
  have Hroot_old_color : In authority_flow_state
      (executing_authority_color_set CT caller_h
        (mk_watched_frame Imm_r caller_senv caller_renv) caller_incoming)
      (FlowPowered, root).
  { eapply executing_authority_owned_is_powered. exact Hroot_owned_old. }
  have Hroot_incoming : In authority_flow_state callee_incoming
      (FlowPowered, root).
  { rewrite Hincoming. exact Hroot_old_color. }
  have Hroot_callee : In authority_flow_state
      (executing_authority_color_set CT callee_h callee callee_incoming)
      (FlowPowered, root).
  { exists (FlowPowered, root). split; [left; exact Hroot_incoming|].
    apply rt_refl. }
  eapply executing_authority_dangerous_retained_reachable.
  - left. reflexivity.
  - exact Hroot_callee.
  - exact Hreachable.
Qed.

(** The mutable-authority case differs only at the updated destination.  Old
    capability roots again arrive through [callee_incoming]; if the new RDM
    destination itself is a capability root, its location is exactly the
    returned value and must already be powered by the completed callee. *)
Lemma immutable_post_owned_is_frozen_snapshot_color :
  forall CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller_h caller_senv caller_renv destination destination_type value
    caller_incoming location,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some snapshot :: snapshots) h ->
    static_getType caller_senv destination = Some destination_type ->
    sqtype destination_type = RDM ->
    Same_set authority_flow_state
      snapshot.(frozen_snapshot_phase_incoming)
      (executing_authority_color_set CT caller_h
        (mk_watched_frame Imm_r caller_senv caller_renv) caller_incoming) ->
    frame_owned_location CT h
      (mk_watched_frame Imm_r caller_senv
        (update_r_env_value caller_renv destination value)) location ->
    In authority_flow_state snapshot.(frozen_snapshot_current_colors)
      (FlowPowered, location).
Proof.
  intros CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller_h caller_senv caller_renv destination destination_type value
    caller_incoming location Hstate Hdestination Hrdm Hincoming Howned.
  apply frame_owned_location_iff_active_live in Howned.
  have Hold_live := immutable_rdm_update_live_capability_included CT h
    caller_senv caller_renv [] destination destination_type value
    Hdestination Hrdm location Howned.
  destruct Hold_live as [root [[Hroot | [old_boundary [Hin _]]] Hreachable]].
  2: inversion Hin.
  have Hroot_owned : frame_owned_location CT caller_h
      (mk_watched_frame Imm_r caller_senv caller_renv) root.
  { exists root. split; [exact Hroot|constructor]. }
  have Hroot_caller : In authority_flow_state
      (executing_authority_color_set CT caller_h
        (mk_watched_frame Imm_r caller_senv caller_renv) caller_incoming)
      (FlowPowered, root).
  { eapply executing_authority_owned_is_powered. exact Hroot_owned. }
  have Hsnapshot_in : List.In (Some snapshot)
      (Some snapshot :: snapshots) by (simpl; auto).
  destruct Hstate as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous &
      Havoid & Hroots & Hexposure & Hresume & Hjoins & Hentry_covered &
      Hphase_covered).
  have Hroot_snapshot : In authority_flow_state
      snapshot.(frozen_snapshot_current_colors) (FlowPowered, root).
  { eapply Hphase_covered; [exact Hsnapshot_in|left; reflexivity|].
    eapply (proj2 Hincoming). exact Hroot_caller. }
  eapply Hclosed; [exact Hsnapshot_in|].
  exists (FlowPowered, root). split; [exact Hroot_snapshot|].
  eapply frozen_caller_powered_retained_forward. exact Hreachable.
Qed.

Lemma mutable_rdm_caller_owned_is_callee_powered :
  forall CT caller_senv caller_renv caller_h callee_h destination
    destination_type return_location callee caller_incoming callee_incoming
    location,
    static_getType caller_senv destination = Some destination_type ->
    sqtype destination_type = RDM ->
    runtime_getVal
      (update_r_env_value caller_renv destination (Iot return_location))
      destination = Some (Iot return_location) ->
    callee_incoming = executing_authority_color_set CT caller_h
      (mk_watched_frame Mut_r caller_senv caller_renv) caller_incoming ->
    In authority_flow_state
      (executing_authority_color_set CT callee_h callee callee_incoming)
      (FlowPowered, return_location) ->
    frame_owned_location CT callee_h
      (mk_watched_frame Mut_r caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      location ->
    In authority_flow_state
      (executing_authority_color_set CT callee_h callee callee_incoming)
      (FlowPowered, location).
Proof.
  intros CT caller_senv caller_renv caller_h callee_h destination
    destination_type return_location callee caller_incoming callee_incoming
    location Hdestination Hrdm Hdestination_value Hincoming Hreturn Howned.
  apply frame_owned_location_iff_active_live in Howned.
  destruct Howned as [root [[Hroot | [boundary [Hin _]]] Hreachable]].
  2: inversion Hin.
  destruct Hroot as
    [variable [variable_type [Htype [Hvalue Hcapability]]]].
  destruct (Nat.eq_dec variable destination) as [Heq | Hneq].
  - subst variable. rewrite Hdestination_value in Hvalue.
    injection Hvalue as <-.
    eapply executing_authority_dangerous_retained_reachable.
    + left. reflexivity.
    + exact Hreturn.
    + exact Hreachable.
  - have Hold_value := runtime_getVal_update_diff caller_renv destination
      variable (Iot return_location) (ltac:(congruence)).
    rewrite Hvalue in Hold_value.
    have Hroot_owned_old : frame_owned_location CT caller_h
        (mk_watched_frame Mut_r caller_senv caller_renv) root.
    { apply frame_owned_location_iff_active_live.
      exists root. split; [left|constructor].
      exists variable, variable_type. repeat split; try assumption.
      symmetry. exact Hold_value. }
    have Hroot_old_color : In authority_flow_state
        (executing_authority_color_set CT caller_h
          (mk_watched_frame Mut_r caller_senv caller_renv) caller_incoming)
        (FlowPowered, root).
    { eapply executing_authority_owned_is_powered. exact Hroot_owned_old. }
    have Hroot_incoming : In authority_flow_state callee_incoming
        (FlowPowered, root).
    { rewrite Hincoming. exact Hroot_old_color. }
    have Hroot_callee : In authority_flow_state
        (executing_authority_color_set CT callee_h callee callee_incoming)
        (FlowPowered, root).
    { exists (FlowPowered, root). split; [left; exact Hroot_incoming|].
      apply rt_refl. }
    eapply executing_authority_dangerous_retained_reachable.
    + left. reflexivity.
    + exact Hroot_callee.
    + exact Hreachable.
Qed.

(** Generic structural pop.  All hypotheses below are internal products of
    preservation, call-boundary bookkeeping, and the derived pop-safety
    proof.  In particular, this lemma adds no premise to the public statement
    theorem. *)
Lemma principled_phased_authority_history_leave_call_given_pop_safe :
  forall CT P Z cutoff caller stack caller_incoming callee boundary
    callee_incoming h,
    principled_phased_authority_live_history_state CT P Z cutoff
      callee (boundary :: stack) callee_incoming h ->
    caller.(frame_authority) =
      boundary.(boundary_caller).(frame_authority) ->
    state_is_confined P cutoff caller.(frame_renv) h ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    Included authority_flow_state caller_incoming callee_incoming ->
    executing_authority_call_pop_safe CT h Z callee callee_incoming
      caller caller_incoming ->
    principled_phased_authority_live_history_state CT P Z cutoff
      caller stack caller_incoming h.
Proof.
  intros CT P Z cutoff caller stack caller_incoming callee boundary
    callee_incoming h Hstate Hcaller_authority Hconfined Hcaller_wf
    Hcaller_sound Hincoming Hpop.
  destruct Hstate as [Hcontains Hstate].
  destruct Hstate as [Hcallee_confined Hstate].
  destruct Hstate as [Hcallee_incoming_runtime Hstate].
  destruct Hstate as [Hcallee_separated Hstate].
  destruct Hstate as [Hframes Hstate].
  destruct Hstate as [Hsounds Hstate].
  destruct Hstate as [Hcutoff Hstate].
  destruct Hstate as [Hzone [Hchain Hcutoffs]].
  have Hcaller_incoming_runtime :
      authority_colors_runtime_mutable h caller_incoming.
  { intros mode location Hcolor.
    eapply Hcallee_incoming_runtime. apply Hincoming. exact Hcolor. }
  have Hcaller_separated :
      executing_authority_colors_separated CT h Z caller caller_incoming.
  { eapply executing_authority_colors_separated_after_call_pop; eauto. }
  have Hcaller_frames : live_frames_wf CT h caller stack.
  { split; [exact Hcaller_wf|exact (Forall_inv_tail (proj2 Hframes))]. }
  have Hcaller_sounds : live_frames_authority_sound h caller stack.
  { split; [exact Hcaller_sound|exact (Forall_inv_tail (proj2 Hsounds))]. }
  have Hcaller_chain :
      live_stack_authorities_chain caller.(frame_authority) stack.
  { simpl in Hchain. destruct Hchain as [_ Htail].
    rewrite Hcaller_authority. exact Htail. }
  split; [exact Hcontains|].
  split; [exact Hconfined|].
  split; [exact Hcaller_incoming_runtime|].
  split; [exact Hcaller_separated|].
  split; [exact Hcaller_frames|].
  split; [exact Hcaller_sounds|].
  split; [exact Hcutoff|].
  split; [exact Hzone|].
  split; [exact Hcaller_chain|].
  exact (Forall_inv_tail Hcutoffs).
Qed.

(** Updating the caller's destination is the only environment change at
    return.  This wrapper derives confinement, authority soundness, and the
    restoration of the caller's incoming colors from the pre-call and
    completed-body states.  The remaining [call_pop_safe] argument is the
    semantic color obligation proved from typing and body evaluation. *)
Lemma principled_phased_authority_history_leave_call_update :
  forall CT P Z cutoff caller stack caller_incoming caller_h callee boundary
    callee_renv callee_incoming callee_h destination value,
    principled_phased_authority_live_history_state CT P Z cutoff
      caller stack caller_incoming caller_h ->
    boundary.(boundary_caller) = caller ->
    callee.(frame_renv) = callee_renv ->
    principled_phased_authority_live_history_state CT P Z cutoff
      callee (boundary :: stack) callee_incoming callee_h ->
    callee_incoming =
      executing_authority_color_set CT caller_h caller caller_incoming ->
    destination <> 0 ->
    (match value with
     | Null_a => True
     | Iot location => confined_loc P cutoff location
     end) ->
    wf_r_config CT caller.(frame_senv)
      (update_r_env_value caller.(frame_renv) destination value) callee_h ->
    executing_authority_call_pop_safe CT callee_h Z callee callee_incoming
      (mk_watched_frame caller.(frame_authority) caller.(frame_senv)
        (update_r_env_value caller.(frame_renv) destination value))
      caller_incoming ->
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame caller.(frame_authority) caller.(frame_senv)
        (update_r_env_value caller.(frame_renv) destination value))
      stack caller_incoming callee_h.
Proof.
  intros CT P Z cutoff caller stack caller_incoming caller_h callee boundary
    callee_renv callee_incoming callee_h destination value Hcaller
    Hboundary Hcallee_renv Hbody Hincoming Hdestination Hvalue Hpost_wf Hpop.
  have Hcaller_confined := proj1 (proj2 Hcaller).
  have Hbody_confined := proj1 (proj2 Hbody).
  have Hpost_confined : state_is_confined P cutoff
      (update_r_env_value caller.(frame_renv) destination value) callee_h.
  { split.
    - eapply env_confined_update; [exact (proj1 Hcaller_confined)|exact Hvalue].
    - exact (proj2 Hbody_confined). }
  have Hbody_sounds := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hbody))))).
  have Hold_caller_sound : authority_context_sound callee_h
      caller.(frame_renv) caller.(frame_authority).
  { have Hhead := Forall_inv (proj2 Hbody_sounds).
    rewrite Hboundary in Hhead. exact Hhead. }
  have Hpost_sound : authority_context_sound callee_h
      (update_r_env_value caller.(frame_renv) destination value)
      caller.(frame_authority).
  { eapply authority_context_sound_after_nonreceiver_update_live; eauto. }
  eapply principled_phased_authority_history_leave_call_given_pop_safe
    with (callee := callee) (boundary := boundary)
      (callee_incoming := callee_incoming).
  - exact Hbody.
  - rewrite Hboundary. reflexivity.
  - exact Hpost_confined.
  - exact Hpost_wf.
  - exact Hpost_sound.
  - rewrite Hincoming.
    apply executing_authority_color_set_contains_incoming.
  - exact Hpop.
Qed.

Lemma principled_phased_authority_history_leave_call_null :
  forall CT P Z cutoff caller stack caller_incoming caller_h callee boundary
    callee_renv callee_incoming callee_h destination,
    principled_phased_authority_live_history_state CT P Z cutoff
      caller stack caller_incoming caller_h ->
    boundary.(boundary_caller) = caller ->
    callee.(frame_renv) = callee_renv ->
    principled_phased_authority_live_history_state CT P Z cutoff
      callee (boundary :: stack) callee_incoming callee_h ->
    callee_incoming =
      executing_authority_color_set CT caller_h caller caller_incoming ->
    destination <> 0 ->
    wf_r_config CT caller.(frame_senv)
      (update_r_env_value caller.(frame_renv) destination Null_a) callee_h ->
    executing_authority_call_pop_safe CT callee_h Z callee callee_incoming
      (mk_watched_frame caller.(frame_authority) caller.(frame_senv)
        (update_r_env_value caller.(frame_renv) destination Null_a))
      caller_incoming ->
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame caller.(frame_authority) caller.(frame_senv)
        (update_r_env_value caller.(frame_renv) destination Null_a))
      stack caller_incoming callee_h.
Proof.
  intros. eapply principled_phased_authority_history_leave_call_update;
    eauto.
Qed.

Lemma principled_phased_authority_history_leave_call_nonnull :
  forall CT P Z cutoff caller stack caller_incoming caller_h callee boundary
    callee_senv callee_renv callee_incoming callee_h destination return_var
    return_location,
    principled_phased_authority_live_history_state CT P Z cutoff
      caller stack caller_incoming caller_h ->
    boundary.(boundary_caller) = caller ->
    callee = mk_watched_frame callee.(frame_authority)
      callee_senv callee_renv ->
    principled_phased_authority_live_history_state CT P Z cutoff
      callee (boundary :: stack) callee_incoming callee_h ->
    callee_incoming =
      executing_authority_color_set CT caller_h caller caller_incoming ->
    destination <> 0 ->
    runtime_getVal callee_renv return_var = Some (Iot return_location) ->
    wf_r_config CT caller.(frame_senv)
      (update_r_env_value caller.(frame_renv) destination
        (Iot return_location)) callee_h ->
    executing_authority_call_pop_safe CT callee_h Z callee callee_incoming
      (mk_watched_frame caller.(frame_authority) caller.(frame_senv)
        (update_r_env_value caller.(frame_renv) destination
          (Iot return_location))) caller_incoming ->
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame caller.(frame_authority) caller.(frame_senv)
        (update_r_env_value caller.(frame_renv) destination
          (Iot return_location))) stack caller_incoming callee_h.
Proof.
  intros CT P Z cutoff caller stack caller_incoming caller_h callee boundary
    callee_senv callee_renv callee_incoming callee_h destination return_var
    return_location Hcaller Hboundary Hcallee Hbody Hincoming Hdestination
    Hreturn Hpost_wf Hpop.
  have Hbody_confined := proj1 (proj2 Hbody).
  have Hreturn_confined : confined_loc P cutoff return_location.
  { apply (proj1 Hbody_confined return_var return_location).
    rewrite Hcallee. simpl. exact Hreturn. }
  eapply principled_phased_authority_history_leave_call_update
    with (callee_renv := callee_renv); eauto.
  rewrite Hcallee. reflexivity.
Qed.

(** Compositional pop rule for the proof-local mutable-RDM package.  The
    ordinary phased state is restored by the established pop theorem; the
    stack-wide component invariant is restored by classifying the updated
    caller's RDM roots into unchanged roots and the mutable return root. *)
Lemma principled_live_mutable_rdm_history_leave_call_nonnull :
  forall CT P Z cutoff caller stack caller_incoming caller_h callee boundary
    callee_senv callee_renv callee_incoming callee_h destination
    destination_type return_var return_location,
    principled_phased_authority_live_history_state CT P Z cutoff
      caller stack caller_incoming caller_h ->
    boundary.(boundary_caller) = caller ->
    callee = mk_watched_frame callee.(frame_authority)
      callee_senv callee_renv ->
    principled_live_mutable_rdm_history_state CT P Z cutoff
      callee (boundary :: stack) callee_incoming callee_h ->
    callee_incoming =
      executing_authority_color_set CT caller_h caller caller_incoming ->
    destination <> 0 ->
    static_getType caller.(frame_senv) destination = Some destination_type ->
    runtime_getVal callee_renv return_var = Some (Iot return_location) ->
    wf_r_config CT caller.(frame_senv)
      (update_r_env_value caller.(frame_renv) destination
        (Iot return_location)) callee_h ->
    executing_authority_call_pop_safe CT callee_h Z callee callee_incoming
      (mk_watched_frame caller.(frame_authority) caller.(frame_senv)
        (update_r_env_value caller.(frame_renv) destination
          (Iot return_location))) caller_incoming ->
    (forall target,
      mutable_reachable CT callee_h return_location target ->
      cutoff <= target) ->
    principled_live_mutable_rdm_history_state CT P Z cutoff
      (mk_watched_frame caller.(frame_authority) caller.(frame_senv)
        (update_r_env_value caller.(frame_renv) destination
          (Iot return_location))) stack caller_incoming callee_h.
Proof.
  intros CT P Z cutoff caller stack caller_incoming caller_h callee boundary
    callee_senv callee_renv callee_incoming callee_h destination
    destination_type return_var return_location Hcaller Hboundary Hcallee
    [Hbody Hcomponents] Hincoming Hdestination_not_receiver
    Hdestination Hreturn Hpost_wf Hpop Hreturn_component.
  split.
  - eapply principled_phased_authority_history_leave_call_nonnull with
      (caller_h := caller_h) (callee_senv := callee_senv)
      (return_var := return_var); eauto.
  - eapply live_mutable_rdm_components_after_mutable_return_pop with
      (active := callee) (boundary := boundary)
      (destination_type := destination_type).
    + rewrite Hboundary. destruct caller. reflexivity.
    + have Hbody_frames :=
        proj1 (proj2 (proj2 (proj2 (proj2 Hbody)))).
      have Hcaller_final_wf := Forall_inv (proj2 Hbody_frames).
      rewrite Hboundary in Hcaller_final_wf. exact Hcaller_final_wf.
    + exact Hdestination.
    + exact Hcomponents.
    + exact Hreturn_component.
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
