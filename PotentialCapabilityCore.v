Require Import Syntax Notations Helpers Typing Subtyping Bigstep.
Require Import ViewpointAdaptation Properties Preservation ReadonlyHelper.
Require Import Reachability MutableCapability ComponentColoring.
Require Import ExecutionConfinement ProtectionHistory ForwardCapabilityHistory.
Require Import AuthorityCapability AuthorityHistory WatchedFrames
  LiveCapabilityStack.
From Stdlib Require Import List Sets.Ensembles Relations.Relation_Operators
  Program.Equality.
Import ListNotations.

(** A frame is live when it is active or retained by a suspended call
    boundary.  RDM roots do not themselves grant mutable authority, but two
    such roots in the same frame may be joined by a future write to an
    explicitly [Assignable] RDM field.  This remains relevant in an immutable
    authority frame when the receiver is statically [RDM].  It does not apply
    to an [RO] receiver: [RO |> RDM_f = Lost].  Two [Mut] roots are also
    potential peers: a later call may adapt receiver-dependent formals to
    those mutable actuals and join them in its callee frame. *)
Inductive live_frame_member
  (active : watched_frame) (stack : list watched_boundary) :
  watched_frame -> Prop :=
| live_frame_active : live_frame_member active stack active
| live_frame_suspended : forall boundary,
    List.In boundary stack ->
    live_frame_member active stack boundary.(boundary_caller).

Definition frame_owned_location
  (CT : class_table) (h : heap) (frame : watched_frame)
  (location : Loc) : Prop :=
  exists root,
    frame_capability_root frame root /\
    retained_mut_reachable CT h root location.

Lemma frame_owned_location_iff_active_live :
  forall CT h frame location,
    frame_owned_location CT h frame location <->
    In Loc (live_capability_set CT h frame []) location.
Proof.
  intros CT h frame location. split.
  - intros [root [Hroot Hreach]].
    exists root. split; [left; exact Hroot|exact Hreach].
  - intros [root [[Hactive | [boundary [Hin _]]] Hreach]].
    + exists root. split; assumption.
    + inversion Hin.
Qed.

Definition potential_frame_edge
  (active : watched_frame) (stack : list watched_boundary)
  (left right : Loc) : Prop :=
  exists frame,
    live_frame_member active stack frame /\
    typed_root RDM frame.(frame_senv) frame.(frame_renv) left /\
    typed_root RDM frame.(frame_senv) frame.(frame_renv) right.

(** A live call boundary relates its current callee frame to the suspended
    caller saved at that boundary.  For the head boundary the current callee
    is the active frame; below the head it is the caller saved by the preceding
    boundary. *)
Inductive live_call_boundary :
  watched_frame -> list watched_boundary ->
  watched_frame -> watched_boundary -> Prop :=
| live_call_boundary_head : forall active boundary tail,
    live_call_boundary active (boundary :: tail) active boundary
| live_call_boundary_tail : forall active head tail callee boundary,
    live_call_boundary head.(boundary_caller) tail callee boundary ->
     live_call_boundary active (head :: tail) callee boundary.

(** A stack partition identifies the frames executing on behalf of a pending
    callee (the active frame plus callers saved above the boundary) and the
    authority that survives below the boundary. *)
Inductive live_call_partition
  (active : watched_frame) :
  list watched_boundary -> watched_boundary ->
  list watched_boundary -> list watched_boundary -> Prop :=
| live_call_partition_head : forall boundary below,
    live_call_partition active (boundary :: below) boundary [] below
| live_call_partition_tail : forall head tail boundary above below,
    live_call_partition active tail boundary above below ->
    live_call_partition active (head :: tail) boundary
      (head :: above) below.

Lemma live_call_partition_change_active :
  forall old_active new_active stack boundary above below,
    live_call_partition old_active stack boundary above below ->
    live_call_partition new_active stack boundary above below.
Proof.
  intros old_active new_active stack boundary above below Hpartition.
  induction Hpartition.
  - constructor.
  - constructor. exact IHHpartition.
Qed.

Lemma live_call_partition_stack_shape :
  forall active stack boundary above below,
    live_call_partition active stack boundary above below ->
    stack = above ++ boundary :: below.
Proof.
  intros active stack boundary above below Hpartition.
  induction Hpartition.
  - reflexivity.
  - simpl. rewrite IHHpartition. reflexivity.
Qed.

Lemma live_call_boundary_callee_is_live :
  forall active stack callee boundary,
    live_call_boundary active stack callee boundary ->
    live_frame_member active stack callee.
Proof.
  intros active stack callee boundary Hboundary.
  induction Hboundary.
  - constructor.
  - inversion IHHboundary; subst.
    + constructor. left. reflexivity.
    + constructor. right. exact H.
Qed.

Lemma live_call_boundary_boundary_in_stack :
  forall active stack callee boundary,
    live_call_boundary active stack callee boundary ->
    List.In boundary stack.
Proof.
  intros active stack callee boundary Hboundary.
  induction Hboundary.
  - left. reflexivity.
  - right. exact IHHboundary.
Qed.

Lemma live_call_boundary_caller_is_live :
  forall active stack callee boundary,
    live_call_boundary active stack callee boundary ->
    live_frame_member active stack boundary.(boundary_caller).
Proof.
  intros active stack callee boundary Hboundary.
  constructor. eapply live_call_boundary_boundary_in_stack; eauto.
Qed.

Lemma live_call_partition_above_frames_wf :
  forall CT h active stack boundary above below,
    live_call_partition active stack boundary above below ->
    live_frames_wf CT h active stack ->
    live_frames_wf CT h active above.
Proof.
  intros CT h active stack boundary above below Hpartition
    [Hactive Hstack].
  split; [exact Hactive|].
  rewrite (live_call_partition_stack_shape _ _ _ _ _ Hpartition) in Hstack.
  apply Forall_app in Hstack. exact (proj1 Hstack).
Qed.

Lemma live_call_partition_above_frames_authority_sound :
  forall h active stack boundary above below,
    live_call_partition active stack boundary above below ->
    live_frames_authority_sound h active stack ->
    live_frames_authority_sound h active above.
Proof.
  intros h active stack boundary above below Hpartition [Hactive Hstack].
  split; [exact Hactive|].
  rewrite (live_call_partition_stack_shape _ _ _ _ _ Hpartition) in Hstack.
  apply Forall_app in Hstack. exact (proj1 Hstack).
Qed.

Lemma live_frame_member_under_suspended_head :
  forall active head tail frame,
    live_frame_member head.(boundary_caller) tail frame ->
    live_frame_member active (head :: tail) frame.
Proof.
  intros active head tail frame Hlive. inversion Hlive; subst.
  - constructor. left. reflexivity.
  - constructor. right. exact H.
Qed.


(** Returning a non-null RDM result is possible only through an RDM receiver
    view and an actually RDM-returning dynamic signature.  Both facts are
    stored at call entry.  Requiring the dynamic return qualifier is crucial
    under flexible overriding: a static RDM result may dispatch to a method
    whose refined result is [Mut], but that call cannot return an arbitrary
    callee RDM root.

    This proof-only edge records the latent future connection while the body
    is still executing.  The runtime-context equality is semantic evidence
    that the two RDM roots can coexist in the same caller frame after return. *)
Definition potential_return_edge
  (h : heap) (active : watched_frame) (stack : list watched_boundary)
  (left right : Loc) : Prop :=
  exists callee boundary,
    live_call_boundary active stack callee boundary /\
    boundary.(boundary_receiver_view) = RDM /\
    boundary.(boundary_callee_return_qualifier) = RDM /\
    r_muttype h left = r_muttype h right /\
    ((typed_root RDM callee.(frame_senv) callee.(frame_renv) left /\
      typed_root RDM boundary.(boundary_caller).(frame_senv)
        boundary.(boundary_caller).(frame_renv) right) \/
     (typed_root RDM boundary.(boundary_caller).(frame_senv)
        boundary.(boundary_caller).(frame_renv) left /\
        typed_root RDM callee.(frame_senv) callee.(frame_renv) right)).

Definition potential_adjacent
  (CT : class_table) (h : heap)
  (active : watched_frame) (stack : list watched_boundary)
  (left right : Loc) : Prop :=
  (retained_mut_edge CT h left right \/
   mutable_edge CT h right left) \/
  potential_frame_edge active stack left right \/
  potential_return_edge h active stack left right.

Definition potential_connected
  (CT : class_table) (h : heap)
  (active : watched_frame) (stack : list watched_boundary) :
  Loc -> Loc -> Prop :=
  clos_refl_trans Loc (potential_adjacent CT h active stack).

Definition ownership_frame_edge
  (CT : class_table) (h : heap)
  (active : watched_frame) (stack : list watched_boundary)
  (left right : Loc) : Prop :=
  exists frame,
    live_frame_member active stack frame /\
    frame_owned_location CT h frame left /\
    frame_owned_location CT h frame right.

Definition boundary_adjacent
  (CT : class_table) (h : heap)
  (active : watched_frame) (stack : list watched_boundary)
  (left right : Loc) : Prop :=
  potential_adjacent CT h active stack left right \/
  ownership_frame_edge CT h active stack left right.

Definition entry_ownership_channel_free
  (boundary : watched_boundary) : Prop :=
  let entry_frame :=
    mk_watched_frame
      (call_authority boundary.(boundary_caller).(frame_authority)
        boundary.(boundary_receiver_view))
      boundary.(boundary_callee_entry_senv)
      boundary.(boundary_callee_entry_renv) in
  (forall root, ~ frame_capability_root entry_frame root) /\
  (forall root,
    ~ typed_root RDM entry_frame.(frame_senv) entry_frame.(frame_renv) root).

Definition potential_colors_separated
  (CT : class_table) (h : heap) (M Z : Ensemble Loc)
  (active : watched_frame) (stack : list watched_boundary) : Prop :=
  forall capability protected,
    In Loc M capability ->
    In Loc Z protected ->
    ~ potential_connected CT h active stack capability protected.

(** RDM-only core of the authority-sensitive color graph.  Its edges have
    three distinct
    operational meanings:

    - actual undirected RDM-component edges;
    - a possible RDM write between roots simultaneously in scope in a live
      frame;
    - the single RDM join that a pending call may introduce on return.

    Taking the transitive closure is necessary: a neutral component may link
    two differently colored components through two different prospective
    joins.  Explicit [Mut_f] edges are deliberately absent.  Their forward
    authority effect is already closed into [M] by [live_capability_set], and
    a prospective RDM join does not grant authority to traverse a root's
    [Mut_f] descendants. *)
Definition layered_color_adjacent
  (CT : class_table) (h : heap)
  (active : watched_frame) (stack : list watched_boundary)
  (left right : Loc) : Prop :=
  mutable_adjacent CT h left right \/
  potential_frame_edge active stack left right \/
  potential_return_edge h active stack left right.

Definition layered_color_connected
  (CT : class_table) (h : heap)
  (active : watched_frame) (stack : list watched_boundary) :
  Loc -> Loc -> Prop :=
  clos_refl_trans Loc (layered_color_adjacent CT h active stack).

(** Design boundary: [layered_color_connected] is intentionally not yet the
    final flexible-call invariant.  Excluding [Mut_f] prevents a prospective
    join in one call phase from granting fictitious authority in another, but
    it also means that, after an RDM join becomes actual, newly enabled
    forward [Mut_f] reachability is not represented by this graph alone.

    The full option-2 design must therefore be temporally stratified:

    - one prospective closure per live frame, containing actual forward
      retained edges and only that frame's RDM-root joins;
    - no return edge while the callee body is executing;
    - call pop as the transition that constructs and verifies the resumed
      caller closure.

    Do not promote this RDM-only core to the recursive preservation theorem
    until that per-frame staging replaces the cross-frame closure above. *)

(** Frame joins record possible alias connectivity, not authority seeds.
    Every syntactic RDM root therefore participates in these joins.  Whether
    such a root contributes authority is decided separately, by
    [capability_in_context] using the frame's class-bounded authority. *)
Definition effective_frame_rdm_root
  (frame : watched_frame) (root : Loc) : Prop :=
  typed_root RDM frame.(frame_senv) frame.(frame_renv) root.

(** A single execution phase may follow actual forward authority (including
    [Mut_f]), move backwards inside an actual RDM component, and anticipate
    RDM joins between roots simultaneously present in that frame. *)
Definition staged_frame_adjacent
  (CT : class_table) (h : heap) (frame : watched_frame)
  (left right : Loc) : Prop :=
  (retained_mut_edge CT h left right \/
   mutable_edge CT h right left) \/
  (effective_frame_rdm_root frame left /\
   effective_frame_rdm_root frame right).

Definition staged_frame_connected
  (CT : class_table) (h : heap) (frame : watched_frame) :
  Loc -> Loc -> Prop :=
  clos_refl_trans Loc (staged_frame_adjacent CT h frame).

Definition staged_frame_closure
  (CT : class_table) (h : heap) (frame : watched_frame)
  (seeds : Ensemble Loc) : Ensemble Loc :=
  fun location =>
    exists seed,
      In Loc seeds seed /\
      staged_frame_connected CT h frame seed location.

(** The return transition is separated from both adjacent frame phases.  It
    makes a possible RDM result available to the resumed caller, but it does
    not permit another traversal of the callee phase afterwards. *)
Definition staged_return_adjacent
  (h : heap) (callee : watched_frame) (boundary : watched_boundary)
  (left right : Loc) : Prop :=
  boundary.(boundary_receiver_view) = RDM /\
  boundary.(boundary_callee_return_qualifier) = RDM /\
  r_muttype h left = r_muttype h right /\
  ((effective_frame_rdm_root callee left /\
    effective_frame_rdm_root boundary.(boundary_caller) right) \/
   (effective_frame_rdm_root boundary.(boundary_caller) left /\
    effective_frame_rdm_root callee right)).

Definition staged_return_root
  (callee : watched_frame) (boundary : watched_boundary)
  (location : Loc) : Prop :=
  effective_frame_rdm_root callee location \/
  effective_frame_rdm_root boundary.(boundary_caller) location.

Definition staged_return_connected
  (h : heap) (callee : watched_frame) (boundary : watched_boundary) :
  Loc -> Loc -> Prop :=
  clos_refl_trans Loc (staged_return_adjacent h callee boundary).

Definition staged_return_closure
  (h : heap) (callee : watched_frame) (boundary : watched_boundary)
  (seeds : Ensemble Loc) : Ensemble Loc :=
  fun location =>
    exists seed,
      In Loc seeds seed /\
      staged_return_connected h callee boundary seed location.

(** Colors move monotonically forward in execution order:

      active frame; return to caller; caller frame; return again; ...

    A path can therefore use each call phase at most once and cannot
    "time-travel" from a resumed caller back into a completed callee. *)
Fixpoint staged_live_color_set
  (CT : class_table) (h : heap) (active : watched_frame)
  (stack : list watched_boundary) (seeds : Ensemble Loc) : Ensemble Loc :=
  match stack with
  | [] => staged_frame_closure CT h active seeds
  | boundary :: tail =>
      staged_live_color_set CT h boundary.(boundary_caller) tail
        (staged_return_closure h active boundary
          (staged_frame_closure CT h active seeds))
  end.

(** Phase-correct live coloring.

    [staged_live_color_set] above was the first temporal prototype.  Because
    its seed is the global [live_capability_set], it makes suspended-caller
    capabilities available during the callee phase.  That is too early: a
    path may use a caller-only prospective join and then return to an already
    completed callee join.

    The final phase construction below injects a frame's owned mutable
    capabilities only when execution reaches that frame.  Incoming colors
    from a completed callee are retained, the single return transition is
    applied, and only then are the resumed caller's capabilities added.  Thus
    the order is exactly

      callee capabilities / callee phase / return / caller capabilities /
      caller phase.

    No assumption is added to a typing or preservation theorem: this is a
    proof-maintained color computation over the existing live stack. *)
Definition phase_frame_capability_set
  (CT : class_table) (h : heap) (frame : watched_frame) : Ensemble Loc :=
  frame_owned_location CT h frame.

Fixpoint phased_live_color_set_from
  (CT : class_table) (h : heap) (active : watched_frame)
  (stack : list watched_boundary) (incoming : Ensemble Loc) : Ensemble Loc :=
  let after_frame := staged_frame_closure CT h active
    (Union Loc incoming (phase_frame_capability_set CT h active)) in
  match stack with
  | [] => after_frame
  | boundary :: tail =>
      phased_live_color_set_from CT h boundary.(boundary_caller) tail
        (staged_return_closure h active boundary after_frame)
  end.

(** The persistent authority-color graph.  RDM joins from every live frame
    may be accumulated because heap joins persist and commute across call
    phases.  Return is deliberately absent: installing a callee result in a
    suspended caller changes scope and is handled only by the call-pop
    transition. *)
Definition authority_color_adjacent
  (CT : class_table) (h : heap)
  (active : watched_frame) (stack : list watched_boundary)
  (left right : Loc) : Prop :=
  (retained_mut_edge CT h left right \/
   mutable_edge CT h right left) \/
  potential_frame_edge active stack left right.

Definition authority_color_connected
  (CT : class_table) (h : heap)
  (active : watched_frame) (stack : list watched_boundary) :
  Loc -> Loc -> Prop :=
  clos_refl_trans Loc (authority_color_adjacent CT h active stack).

(** Stateful authority flow for pending calls.

    [FlowPowered] means that the path currently carries actual mutable
    authority.  It may follow retained edges, including [Mut_f].
    Traversing an RDM edge backwards or crossing a prospective frame join
    enters [FlowNeutral]: the color may have joined, but mutable authority was
    not acquired.  A neutral path may move only inside RDM components and
    across RDM frame joins.  It becomes powered again only at a location that
    is independently live as a mutable capability. *)
Inductive authority_flow_mode : Type :=
| FlowPowered
| FlowProspective
| FlowNeutral.

Definition authority_flow_state : Type := (authority_flow_mode * Loc)%type.

(** Phase-local authority flow.  Unlike [authority_flow_step] below, the
    promotion rule is restricted to capabilities owned by the frame whose
    phase is currently executing.  Suspended-caller capabilities are injected
    only when the sequential construction reaches that caller. *)
Inductive phased_authority_frame_step
  (CT : class_table) (h : heap) (frame : watched_frame) :
  authority_flow_state -> authority_flow_state -> Prop :=
| phased_authority_retained : forall left right,
    retained_mut_edge CT h left right ->
    phased_authority_frame_step CT h frame
      (FlowPowered, left) (FlowPowered, right)
| phased_authority_prospective_retained : forall left right,
    retained_mut_edge CT h left right ->
    phased_authority_frame_step CT h frame
      (FlowProspective, left) (FlowProspective, right)
| phased_authority_prospective_rdm_backward : forall left right,
    mutable_edge CT h right left ->
    phased_authority_frame_step CT h frame
      (FlowProspective, left) (FlowProspective, right)
| phased_authority_reverse_rdm : forall left right,
    mutable_edge CT h right left ->
    phased_authority_frame_step CT h frame
      (FlowPowered, left) (FlowProspective, right)
| phased_authority_neutral_rdm_forward : forall left right,
    mutable_edge CT h left right ->
    phased_authority_frame_step CT h frame
      (FlowNeutral, left) (FlowNeutral, right)
| phased_authority_neutral_rdm_backward : forall left right,
    mutable_edge CT h right left ->
    phased_authority_frame_step CT h frame
      (FlowNeutral, left) (FlowNeutral, right)
| phased_authority_powered_frame_join : forall left right,
    effective_frame_rdm_root frame left ->
    effective_frame_rdm_root frame right ->
    phased_authority_frame_step CT h frame
      (FlowPowered, left) (FlowProspective, right)
| phased_authority_prospective_frame_join : forall left right,
    effective_frame_rdm_root frame left ->
    effective_frame_rdm_root frame right ->
    phased_authority_frame_step CT h frame
      (FlowProspective, left) (FlowProspective, right)
| phased_authority_neutral_frame_join : forall left right,
    effective_frame_rdm_root frame left ->
    effective_frame_rdm_root frame right ->
    phased_authority_frame_step CT h frame
      (FlowNeutral, left) (FlowNeutral, right)
| phased_authority_forget : forall location,
    phased_authority_frame_step CT h frame
      (FlowPowered, location) (FlowNeutral, location)
| phased_authority_prospective_forget : forall location,
    phased_authority_frame_step CT h frame
      (FlowProspective, location) (FlowNeutral, location)
| phased_authority_mark_prospective : forall location,
    phased_authority_frame_step CT h frame
      (FlowPowered, location) (FlowProspective, location)
| phased_authority_promote : forall location,
    frame_owned_location CT h frame location ->
    phased_authority_frame_step CT h frame
      (FlowNeutral, location) (FlowPowered, location).

Definition phased_authority_frame_connected
  (CT : class_table) (h : heap) (frame : watched_frame) :
  authority_flow_state -> authority_flow_state -> Prop :=
  clos_refl_trans authority_flow_state
    (phased_authority_frame_step CT h frame).

Definition phased_authority_frame_closure
  (CT : class_table) (h : heap) (frame : watched_frame)
  (seeds : Ensemble authority_flow_state) : Ensemble authority_flow_state :=
  fun state => exists seed,
    In authority_flow_state seeds seed /\
    phased_authority_frame_connected CT h frame seed state.

Inductive phased_authority_return_step
  (h : heap) (callee : watched_frame) (boundary : watched_boundary) :
  authority_flow_state -> authority_flow_state -> Prop :=
| phased_authority_powered_return : forall left right,
    staged_return_adjacent h callee boundary left right ->
    phased_authority_return_step h callee boundary
      (FlowPowered, left) (FlowNeutral, right)
| phased_authority_neutral_return : forall left right,
    staged_return_adjacent h callee boundary left right ->
    phased_authority_return_step h callee boundary
      (FlowNeutral, left) (FlowNeutral, right)
| phased_authority_return_forget : forall location,
    phased_authority_return_step h callee boundary
      (FlowPowered, location) (FlowNeutral, location).

Definition phased_authority_return_connected
  (h : heap) (callee : watched_frame) (boundary : watched_boundary) :
  authority_flow_state -> authority_flow_state -> Prop :=
  clos_refl_trans authority_flow_state
    (phased_authority_return_step h callee boundary).

Definition phased_authority_return_closure
  (h : heap) (callee : watched_frame) (boundary : watched_boundary)
  (seeds : Ensemble authority_flow_state) : Ensemble authority_flow_state :=
  fun state => exists seed,
    In authority_flow_state seeds seed /\
    phased_authority_return_connected h callee boundary seed state.

Definition phased_frame_powered_seeds
  (CT : class_table) (h : heap) (frame : watched_frame) :
  Ensemble authority_flow_state :=
  fun state => exists location,
    state = (FlowPowered, location) /\
    frame_owned_location CT h frame location.

(** A completed callee does not retain mutable authority merely because its
    location remains allocated.  Return carries component identity forward
    in neutral mode; the resumed caller is powered only by capabilities in
    its own updated frame. *)
Definition demote_authority_set
  (seeds : Ensemble authority_flow_state) : Ensemble authority_flow_state :=
  fun state => exists mode location,
    In authority_flow_state seeds (mode, location) /\
    state = (FlowNeutral, location).

Fixpoint phased_authority_color_set_from
  (CT : class_table) (h : heap) (active : watched_frame)
  (stack : list watched_boundary)
  (incoming : Ensemble authority_flow_state) :
  Ensemble authority_flow_state :=
  let after_frame := phased_authority_frame_closure CT h active
    (Union authority_flow_state incoming
      (phased_frame_powered_seeds CT h active)) in
  match stack with
  | [] => after_frame
  | boundary :: tail =>
      Union authority_flow_state after_frame
        (phased_authority_color_set_from CT h
          boundary.(boundary_caller) tail
          (phased_authority_return_closure h active boundary
            (demote_authority_set after_frame)))
  end.

(** Authority available while one frame is executing.  [incoming] is the
    caller-side authority that existed before the call and therefore remains
    semantically live while the caller is suspended.  It is passed inward at
    call entry and restored from the proof stack at return; callee results are
    not retroactively inserted into it. *)
Definition executing_authority_color_set
  (CT : class_table) (h : heap) (active : watched_frame)
  (incoming : Ensemble authority_flow_state) :
  Ensemble authority_flow_state :=
  phased_authority_frame_closure CT h active
    (Union authority_flow_state incoming
      (phased_frame_powered_seeds CT h active)).

Definition executing_authority_colors_separated
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (active : watched_frame) (incoming : Ensemble authority_flow_state) : Prop :=
  forall mode protected,
    (mode = FlowPowered \/ mode = FlowProspective) ->
    In authority_flow_state
      (executing_authority_color_set CT h active incoming)
      (mode, protected) ->
    ~ In Loc Z protected.

Definition authority_mode_dangerous (mode : authority_flow_mode) : Prop :=
  mode = FlowPowered \/ mode = FlowProspective.

Definition authority_state_covered
  (old_colors : Ensemble authority_flow_state)
  (state : authority_flow_state) : Prop :=
  authority_mode_dangerous (fst state) ->
  exists old_mode,
    authority_mode_dangerous old_mode /\
    In authority_flow_state old_colors (old_mode, snd state).

Definition authority_colors_runtime_mutable
  (h : heap) (colors : Ensemble authority_flow_state) : Prop :=
  forall mode location,
    In authority_flow_state colors (mode, location) ->
    r_muttype h location = Some Mut_r.

Lemma phased_authority_frame_step_preserves_runtime_mutability :
  forall CT h frame source target runtime_q,
    wf_r_config CT frame.(frame_senv) frame.(frame_renv) h ->
    phased_authority_frame_step CT h frame source target ->
    r_muttype h (snd source) = Some runtime_q ->
    r_muttype h (snd target) = Some runtime_q.
Proof.
  intros CT h frame source target runtime_q Hwf Hstep Hruntime.
  inversion Hstep; subst; simpl in *; try exact Hruntime.
  - eapply retained_edge_preserves_runtime_context; eauto.
    exact (proj1 (proj2 Hwf)).
  - eapply retained_edge_preserves_runtime_context; eauto.
    exact (proj1 (proj2 Hwf)).
  - eapply mutable_edge_reflects_runtime_mutability; eauto.
    exact (proj1 (proj2 Hwf)).
  - eapply mutable_edge_reflects_runtime_mutability; eauto.
    exact (proj1 (proj2 Hwf)).
  - eapply mutable_edge_preserves_runtime_mutability; eauto.
    exact (proj1 (proj2 Hwf)).
  - eapply mutable_edge_reflects_runtime_mutability; eauto.
    exact (proj1 (proj2 Hwf)).
  - destruct (active_rdm_roots_share_runtime_context CT
      frame.(frame_senv) frame.(frame_renv) h left right Hwf
      H H0) as
      [context [Hleft Hright]].
    rewrite Hruntime in Hleft. injection Hleft as <-. exact Hright.
  - destruct (active_rdm_roots_share_runtime_context CT
      frame.(frame_senv) frame.(frame_renv) h left right Hwf
      H H0) as
      [context [Hleft Hright]].
    rewrite Hruntime in Hleft. injection Hleft as <-. exact Hright.
  - destruct (active_rdm_roots_share_runtime_context CT
      frame.(frame_senv) frame.(frame_renv) h left right Hwf
      H H0) as
      [context [Hleft Hright]].
    rewrite Hruntime in Hleft. injection Hleft as <-. exact Hright.
Qed.

Lemma phased_authority_frame_connected_preserves_runtime_mutability :
  forall CT h frame source target runtime_q,
    wf_r_config CT frame.(frame_senv) frame.(frame_renv) h ->
    phased_authority_frame_connected CT h frame source target ->
    r_muttype h (snd source) = Some runtime_q ->
    r_muttype h (snd target) = Some runtime_q.
Proof.
  intros CT h frame source target runtime_q Hwf Hconnected.
  induction Hconnected; intros Hruntime.
  - eapply phased_authority_frame_step_preserves_runtime_mutability; eauto.
  - exact Hruntime.
  - apply IHHconnected2. apply IHHconnected1. exact Hruntime.
Qed.

Lemma executing_authority_colors_runtime_mutable :
  forall CT h frame incoming,
    wf_r_config CT frame.(frame_senv) frame.(frame_renv) h ->
    authority_context_sound h frame.(frame_renv) frame.(frame_authority) ->
    authority_colors_runtime_mutable h incoming ->
    authority_colors_runtime_mutable h
      (executing_authority_color_set CT h frame incoming).
Proof.
  intros CT h frame incoming Hwf Hsound Hincoming mode location
    [seed [Hseed Hconnected]].
  destruct seed as [seed_mode seed_location].
  have Hseed_runtime : r_muttype h (snd (seed_mode, seed_location)) =
      Some Mut_r.
  { inversion Hseed; subst.
    - eapply Hincoming. exact H.
    - destruct H as [powered_location [Heq Howned]].
      inversion Heq; subst. simpl.
      eapply (live_capability_members_runtime_mutable CT h frame []).
      + split; [exact Hwf|constructor].
      + split; [exact Hsound|constructor].
      + apply frame_owned_location_iff_active_live. exact Howned. }
  exact (phased_authority_frame_connected_preserves_runtime_mutability
    CT h frame (seed_mode, seed_location) (mode, location) Mut_r Hwf
    Hconnected Hseed_runtime).
Qed.

Lemma phased_authority_frame_step_preserves_coverage :
  forall CT h h' frame old_colors source target,
    (forall old_source old_target,
      In authority_flow_state old_colors old_source ->
      phased_authority_frame_connected CT h frame old_source old_target ->
      In authority_flow_state old_colors old_target) ->
    (forall location,
      frame_owned_location CT h' frame location ->
      exists old_mode,
        authority_mode_dangerous old_mode /\
        In authority_flow_state old_colors (old_mode, location)) ->
    (forall old_mode left right,
      authority_mode_dangerous old_mode ->
      In authority_flow_state old_colors (old_mode, left) ->
      retained_mut_edge CT h' left right ->
      exists target_mode,
        authority_mode_dangerous target_mode /\
        In authority_flow_state old_colors (target_mode, right)) ->
    (forall old_mode left right,
      authority_mode_dangerous old_mode ->
      In authority_flow_state old_colors (old_mode, left) ->
      mutable_edge CT h' right left ->
      exists target_mode,
        authority_mode_dangerous target_mode /\
        In authority_flow_state old_colors (target_mode, right)) ->
    authority_state_covered old_colors source ->
    phased_authority_frame_step CT h' frame source target ->
    authority_state_covered old_colors target.
Proof.
  intros CT h h' frame old_colors source target Hclosed Howned Hforward
    Hbackward Hsource Hstep Htarget_dangerous.
  inversion Hstep; subst; simpl in *.
  - destruct (Hsource (or_introl eq_refl)) as
      [old_mode [Hold_dangerous Hold]].
    eapply Hforward; eauto.
  - destruct (Hsource (or_intror eq_refl)) as
      [old_mode [Hold_dangerous Hold]].
    eapply Hforward; eauto.
  - destruct (Hsource (or_intror eq_refl)) as
      [old_mode [Hold_dangerous Hold]].
    eapply Hbackward; eauto.
  - destruct (Hsource (or_introl eq_refl)) as
      [old_mode [Hold_dangerous Hold]].
    eapply Hbackward; eauto.
  - destruct Htarget_dangerous as [Hbad | Hbad]; discriminate.
  - destruct Htarget_dangerous as [Hbad | Hbad]; discriminate.
  - destruct (Hsource (or_introl eq_refl)) as
      [old_mode [[-> | ->] Hold]].
    + exists FlowProspective. split; [right; reflexivity|].
      eapply Hclosed; [exact Hold|].
      apply rt_step. eapply phased_authority_powered_frame_join; eauto.
    + exists FlowProspective. split; [right; reflexivity|].
      eapply Hclosed; [exact Hold|].
      apply rt_step. eapply phased_authority_prospective_frame_join; eauto.
  - destruct (Hsource (or_intror eq_refl)) as
      [old_mode [[-> | ->] Hold]].
    + exists FlowProspective. split; [right; reflexivity|].
      eapply Hclosed; [exact Hold|].
      apply rt_step. eapply phased_authority_powered_frame_join; eauto.
    + exists FlowProspective. split; [right; reflexivity|].
      eapply Hclosed; [exact Hold|].
      apply rt_step. eapply phased_authority_prospective_frame_join; eauto.
  - destruct Htarget_dangerous as [Hbad | Hbad]; discriminate.
  - destruct Htarget_dangerous as [Hbad | Hbad]; discriminate.
  - destruct Htarget_dangerous as [Hbad | Hbad]; discriminate.
  - destruct (Hsource (or_introl eq_refl)) as
      [old_mode [[-> | ->] Hold]].
    + exists FlowProspective. split; [right; reflexivity|].
      eapply Hclosed; [exact Hold|].
      apply rt_step. apply phased_authority_mark_prospective.
    + exists FlowProspective. split; [right; reflexivity|exact Hold].
  - eapply Howned. exact H.
Qed.

Lemma phased_authority_frame_connected_preserves_coverage :
  forall CT h h' frame old_colors source target,
    (forall old_source old_target,
      In authority_flow_state old_colors old_source ->
      phased_authority_frame_connected CT h frame old_source old_target ->
      In authority_flow_state old_colors old_target) ->
    (forall location,
      frame_owned_location CT h' frame location ->
      exists old_mode,
        authority_mode_dangerous old_mode /\
        In authority_flow_state old_colors (old_mode, location)) ->
    (forall old_mode left right,
      authority_mode_dangerous old_mode ->
      In authority_flow_state old_colors (old_mode, left) ->
      retained_mut_edge CT h' left right ->
      exists target_mode,
        authority_mode_dangerous target_mode /\
        In authority_flow_state old_colors (target_mode, right)) ->
    (forall old_mode left right,
      authority_mode_dangerous old_mode ->
      In authority_flow_state old_colors (old_mode, left) ->
      mutable_edge CT h' right left ->
      exists target_mode,
        authority_mode_dangerous target_mode /\
        In authority_flow_state old_colors (target_mode, right)) ->
    authority_state_covered old_colors source ->
    phased_authority_frame_connected CT h' frame source target ->
    authority_state_covered old_colors target.
Proof.
  intros CT h h' frame old_colors source target Hclosed Howned Hforward
    Hbackward Hsource Hconnected.
  induction Hconnected.
  - eapply phased_authority_frame_step_preserves_coverage; eauto.
  - exact Hsource.
  - apply IHHconnected2. apply IHHconnected1. exact Hsource.
Qed.

(** Heap-changing statements are handled one executing phase at a time.  The
    hypotheses below describe only how newly owned locations and newly
    materialized heap edges are represented by the old phase colors.  They
    are proof obligations discharged from the existing typing premises; they
    are not premises of the public preservation theorem. *)
Lemma executing_authority_colors_after_heap_change :
  forall CT h h' frame incoming Z,
    executing_authority_colors_separated CT h Z frame incoming ->
    (forall location,
      frame_owned_location CT h' frame location ->
      exists old_mode,
        authority_mode_dangerous old_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h frame incoming)
          (old_mode, location)) ->
    (forall old_mode left right,
      authority_mode_dangerous old_mode ->
      In authority_flow_state
        (executing_authority_color_set CT h frame incoming)
        (old_mode, left) ->
      retained_mut_edge CT h' left right ->
      exists target_mode,
        authority_mode_dangerous target_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h frame incoming)
          (target_mode, right)) ->
    (forall old_mode left right,
      authority_mode_dangerous old_mode ->
      In authority_flow_state
        (executing_authority_color_set CT h frame incoming)
        (old_mode, left) ->
      mutable_edge CT h' right left ->
      exists target_mode,
        authority_mode_dangerous target_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h frame incoming)
          (target_mode, right)) ->
    executing_authority_colors_separated CT h' Z frame incoming.
Proof.
  intros CT h h' frame incoming Z Hseparated Howned Hforward Hbackward
    mode protected Hmode [seed [Hseed Hconnected]] Hprotected.
  set (old_colors := executing_authority_color_set CT h frame incoming).
  assert (Hclosed : forall old_source old_target,
      In authority_flow_state old_colors old_source ->
      phased_authority_frame_connected CT h frame old_source old_target ->
      In authority_flow_state old_colors old_target).
  { intros old_source old_target [origin [Horigin Hsource]] Hpath.
    exists origin. split; [exact Horigin|].
    eapply rt_trans; eauto. }
  assert (Hseed_covered : authority_state_covered old_colors seed).
  { destruct seed as [seed_mode seed_location]. simpl. intros Hseed_dangerous.
    inversion Hseed; subst.
    - exists seed_mode. split; [exact Hseed_dangerous|].
      unfold old_colors, executing_authority_color_set.
      exists (seed_mode, seed_location).
      split; [left; exact H|apply rt_refl].
    - destruct H as [location [Heq Hlocation]]. inversion Heq; subst.
      eapply Howned. exact Hlocation. }
  have Hcovered := phased_authority_frame_connected_preserves_coverage
    CT h h' frame old_colors seed (mode, protected) Hclosed Howned
    Hforward Hbackward Hseed_covered Hconnected Hmode.
  destruct Hcovered as [old_mode [Hold_mode Hold_color]].
  apply (Hseparated old_mode protected Hold_mode Hold_color Hprotected).
Qed.

Lemma executing_authority_owned_is_powered :
  forall CT h frame incoming location,
    frame_owned_location CT h frame location ->
    In authority_flow_state
      (executing_authority_color_set CT h frame incoming)
      (FlowPowered, location).
Proof.
  intros CT h frame incoming location Howned.
  exists (FlowPowered, location). split.
  - right. exists location. split; [reflexivity|exact Howned].
  - apply rt_refl.
Qed.

Lemma executing_authority_dangerous_retained :
  forall CT h frame incoming mode left right,
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT h frame incoming) (mode, left) ->
    retained_mut_edge CT h left right ->
    In authority_flow_state
      (executing_authority_color_set CT h frame incoming) (mode, right).
Proof.
  intros CT h frame incoming mode left right Hmode Hcolor Hedge.
  destruct Hmode as [Hmode | Hmode].
  - subst mode. destruct Hcolor as [seed [Hseed Hpath]].
    exists seed. split; [exact Hseed|].
    eapply rt_trans; [exact Hpath|].
    apply rt_step. apply phased_authority_retained. exact Hedge.
  - subst mode. destruct Hcolor as [seed [Hseed Hpath]].
    exists seed. split; [exact Hseed|].
    eapply rt_trans; [exact Hpath|].
    apply rt_step. apply phased_authority_prospective_retained. exact Hedge.
Qed.

Lemma executing_authority_dangerous_retained_reachable :
  forall CT h frame incoming mode left right,
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT h frame incoming) (mode, left) ->
    retained_mut_reachable CT h left right ->
    In authority_flow_state
      (executing_authority_color_set CT h frame incoming) (mode, right).
Proof.
  intros CT h frame incoming mode left right Hmode Hleft Hreachable.
  revert Hleft. induction Hreachable; intros Hleft_color.
  - exact Hleft_color.
  - eapply executing_authority_dangerous_retained.
    + exact Hmode.
    + apply IHHreachable. exact Hleft_color.
    + exact H.
Qed.

Lemma executing_authority_dangerous_reverse_rdm :
  forall CT h frame incoming mode left right,
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT h frame incoming) (mode, left) ->
    mutable_edge CT h right left ->
    In authority_flow_state
      (executing_authority_color_set CT h frame incoming)
      (FlowProspective, right).
Proof.
  intros CT h frame incoming mode left right Hmode Hcolor Hedge.
  destruct Hmode as [Hmode | Hmode].
  - subst mode. destruct Hcolor as [seed [Hseed Hpath]].
    exists seed. split; [exact Hseed|].
    eapply rt_trans; [exact Hpath|].
    apply rt_step. apply phased_authority_reverse_rdm. exact Hedge.
  - subst mode. destruct Hcolor as [seed [Hseed Hpath]].
    exists seed. split; [exact Hseed|].
    eapply rt_trans; [exact Hpath|].
    apply rt_step. apply phased_authority_prospective_rdm_backward.
    exact Hedge.
Qed.

Lemma executing_authority_dangerous_frame_join :
  forall CT h frame incoming mode left right,
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT h frame incoming) (mode, left) ->
    typed_root RDM frame.(frame_senv) frame.(frame_renv) left ->
    typed_root RDM frame.(frame_senv) frame.(frame_renv) right ->
    In authority_flow_state
      (executing_authority_color_set CT h frame incoming)
      (FlowProspective, right).
Proof.
  intros CT h frame incoming mode left right Hmode Hcolor Hleft Hright.
  destruct Hmode as [Hmode | Hmode].
  - subst mode. destruct Hcolor as [seed [Hseed Hpath]].
    exists seed. split; [exact Hseed|].
    eapply rt_trans; [exact Hpath|]. apply rt_step.
    eapply phased_authority_powered_frame_join; eauto.
  - subst mode. destruct Hcolor as [seed [Hseed Hpath]].
    exists seed. split; [exact Hseed|].
    eapply rt_trans; [exact Hpath|]. apply rt_step.
    eapply phased_authority_prospective_frame_join; eauto.
Qed.

(** The three endpoint shapes furnished by a well-typed write.  Mutable
    endpoints are already owned, immutable endpoints cannot be reached by an
    executing mutable authority color, and RDM endpoints are related by the
    phase-local prospective join. *)
Inductive authority_safe_field_endpoints
  (CT : class_table) (h : heap) (frame : watched_frame) (left right : Loc) :
  Prop :=
| authority_safe_field_mutable :
    frame_owned_location CT h frame left ->
    frame_owned_location CT h frame right ->
    authority_safe_field_endpoints CT h frame left right
| authority_safe_field_immutable :
    r_muttype h left = Some Imm_r ->
    r_muttype h right = Some Imm_r ->
    authority_safe_field_endpoints CT h frame left right
| authority_safe_field_rdm :
    typed_root RDM frame.(frame_senv) frame.(frame_renv) left ->
    typed_root RDM frame.(frame_senv) frame.(frame_renv) right ->
    authority_safe_field_endpoints CT h frame left right.

(** Boundary-local authority freshness.  A readonly-state body receives no
    direct mutable root from its caller.  Consequently every direct mutable
    root it later acquires, and every runtime-mutable RDM root, denotes a
    component allocated on the callee side of the tracked boundary.  This is
    stronger than the RDM-only helper above exactly where a nested call may
    adapt a fresh [Mut] actual to an RDM formal. *)
Definition mutable_authority_root
  (frame : watched_frame) (h : heap) (root : Loc) : Prop :=
  typed_root Mut frame.(frame_senv) frame.(frame_renv) root \/
  (typed_root RDM frame.(frame_senv) frame.(frame_renv) root /\
   r_muttype h root = Some Mut_r).

Lemma mutable_authority_root_runtime_mutable :
  forall CT h frame root,
    wf_r_config CT frame.(frame_senv) frame.(frame_renv) h ->
    authority_context_sound h frame.(frame_renv) frame.(frame_authority) ->
    mutable_authority_root frame h root ->
    r_muttype h root = Some Mut_r.
Proof.
  intros CT h frame root Hwf Hsound [Hmut | [Hrdm Hruntime]].
  - apply (frame_capability_root_runtime_mutable CT h frame root Hwf Hsound).
    destruct Hmut as [variable [T [Htype [Hvalue Hmut]]]].
    exists variable, T. repeat split; try assumption.
    unfold capability_in_context. left. exact Hmut.
  - exact Hruntime.
Qed.

(** Both powered capabilities and prospective runtime-mutable RDM roots
    follow retained [Mut_f] edges as well as RDM edges.  This deliberately
    matches [phased_authority_prospective_retained]: using only
    [mutable_reachable] here would leave the private freshness invariant too
    weak for the color semantics.  The two constructors remain distinct
    because only an RDM root under [Mut_r] frame authority is independently
    powered. *)
Inductive mutable_authority_reachable
  (CT : class_table) (h : heap) (frame : watched_frame) : Loc -> Loc -> Prop :=
| mutable_authority_reachable_capability : forall root target,
    frame_capability_root frame root ->
    r_muttype h root = Some Mut_r ->
    retained_mut_reachable CT h root target ->
    mutable_authority_reachable CT h frame root target
| mutable_authority_reachable_rdm : forall root target,
    typed_root RDM frame.(frame_senv) frame.(frame_renv) root ->
    r_muttype h root = Some Mut_r ->
    retained_mut_reachable CT h root target ->
    mutable_authority_reachable CT h frame root target.

Definition active_mutable_authority_components_after_cutoff
  (CT : class_table) (h : heap) (cutoff : Loc)
  (frame : watched_frame) : Prop :=
  forall root target,
    mutable_authority_reachable CT h frame root target ->
    cutoff <= target.

Definition live_mutable_authority_components_after_cutoff
  (CT : class_table) (h : heap) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary) : Prop :=
  forall frame root target,
    live_frame_member active stack frame ->
    mutable_authority_reachable CT h frame root target ->
    cutoff <= target.

Lemma live_mutable_authority_components_active :
  forall CT h cutoff active stack,
    live_mutable_authority_components_after_cutoff CT h cutoff active stack ->
    active_mutable_authority_components_after_cutoff CT h cutoff active.
Proof.
  intros CT h cutoff active stack Hlive root target Hreachable.
  eapply Hlive; eauto. constructor.
Qed.

Definition frame_rdm_root_set (frame : watched_frame) : Ensemble Loc :=
  fun root =>
    typed_root RDM frame.(frame_senv) frame.(frame_renv) root.

Lemma executing_authority_field_update_forward_covered :
  forall CT h frame incoming lx old field written old_mode left right,
    runtime_getObj h lx = Some old ->
    authority_colors_runtime_mutable h
      (executing_authority_color_set CT h frame incoming) ->
    authority_safe_field_endpoints CT h frame lx written ->
    authority_mode_dangerous old_mode ->
    In authority_flow_state
      (executing_authority_color_set CT h frame incoming) (old_mode, left) ->
    retained_mut_edge CT (update_field h lx field (Iot written)) left right ->
    exists target_mode,
      authority_mode_dangerous target_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h frame incoming)
        (target_mode, right).
Proof.
  intros CT h frame incoming lx old field written old_mode left right Hobj
    Hruntime Hendpoints Hmode Hleft Hedge.
  destruct (retained_edge_after_field_update CT h lx old field
    (Iot written) left right Hobj Hedge) as
    [Hold | [Heq_left [Heq_value Hnew]]].
  - exists old_mode. split; [exact Hmode|].
    eapply executing_authority_dangerous_retained; eauto.
  - injection Heq_value as Heq_right. subst left right.
    inversion Hendpoints; subst.
    + exists FlowPowered. split; [left; reflexivity|].
      eapply executing_authority_owned_is_powered; eauto.
    + have Hmut := Hruntime old_mode lx Hleft.
      rewrite H in Hmut. discriminate.
    + exists FlowProspective. split; [right; reflexivity|].
      eapply executing_authority_dangerous_frame_join; eauto.
Qed.

Lemma executing_authority_field_update_backward_covered :
  forall CT h frame incoming lx old field written old_mode left right,
    runtime_getObj h lx = Some old ->
    authority_colors_runtime_mutable h
      (executing_authority_color_set CT h frame incoming) ->
    authority_safe_field_endpoints CT h frame lx written ->
    authority_mode_dangerous old_mode ->
    In authority_flow_state
      (executing_authority_color_set CT h frame incoming) (old_mode, left) ->
    mutable_edge CT (update_field h lx field (Iot written)) right left ->
    exists target_mode,
      authority_mode_dangerous target_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h frame incoming)
        (target_mode, right).
Proof.
  intros CT h frame incoming lx old field written old_mode left right Hobj
    Hruntime Hendpoints Hmode Hleft Hedge.
  destruct (mutable_edge_after_field_update CT h lx old field
    (Iot written) right left Hobj Hedge) as
    [Hold | [Heq_right [Heq_value Hnew]]].
  - exists FlowProspective. split; [right; reflexivity|].
    eapply executing_authority_dangerous_reverse_rdm; eauto.
  - injection Heq_value as Heq_left. subst left right.
    inversion Hendpoints; subst.
    + exists FlowPowered. split; [left; reflexivity|].
      eapply executing_authority_owned_is_powered; eauto.
    + have Hmut := Hruntime old_mode written Hleft.
      rewrite H0 in Hmut. discriminate.
    + exists FlowProspective. split; [right; reflexivity|].
      eapply executing_authority_dangerous_frame_join; eauto.
Qed.

Lemma executing_authority_field_update_owned_covered :
  forall CT h frame incoming lx old field written location,
    runtime_getObj h lx = Some old ->
    authority_colors_runtime_mutable h
      (executing_authority_color_set CT h frame incoming) ->
    authority_safe_field_endpoints CT h frame lx written ->
    frame_owned_location CT (update_field h lx field (Iot written))
      frame location ->
    exists old_mode,
      authority_mode_dangerous old_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h frame incoming)
        (old_mode, location).
Proof.
  intros CT h frame incoming lx old field written location Hobj Hruntime
    Hendpoints [root [Hroot Hreachable]].
  destruct (retained_reachable_after_field_update CT h lx old field
    (Iot written) root location Hobj Hreachable) as
    [Hold | [written' [Heq_value [Hroot_lx Hwritten_location]]]].
  - exists FlowPowered. split; [left; reflexivity|].
    eapply executing_authority_dangerous_retained_reachable.
    + left. reflexivity.
    + apply executing_authority_owned_is_powered.
      exists root. split; [exact Hroot|constructor].
    + exact Hold.
  - injection Heq_value as <-.
    have Hroot_powered : In authority_flow_state
        (executing_authority_color_set CT h frame incoming)
        (FlowPowered, root).
    { apply executing_authority_owned_is_powered.
      exists root. split; [exact Hroot|constructor]. }
    have Hlx_powered : In authority_flow_state
        (executing_authority_color_set CT h frame incoming)
        (FlowPowered, lx).
    { eapply executing_authority_dangerous_retained_reachable.
      - left. reflexivity.
      - exact Hroot_powered.
      - exact Hroot_lx. }
    assert (Hwritten_dangerous : exists mode,
        authority_mode_dangerous mode /\
        In authority_flow_state
          (executing_authority_color_set CT h frame incoming)
          (mode, written)).
    { inversion Hendpoints; subst.
      - exists FlowPowered. split; [left; reflexivity|].
        eapply executing_authority_owned_is_powered; eauto.
      - have Hmut := Hruntime FlowPowered lx Hlx_powered.
        rewrite H in Hmut. discriminate.
      - exists FlowProspective. split; [right; reflexivity|].
        eapply executing_authority_dangerous_frame_join.
        + left. reflexivity.
        + exact Hlx_powered.
        + exact H.
        + exact H0. }
    destruct Hwritten_dangerous as [mode [Hmode Hwritten]].
    exists mode. split; [exact Hmode|].
    eapply executing_authority_dangerous_retained_reachable; eauto.
Qed.

Lemma executing_authority_colors_after_safe_field_update :
  forall CT h frame incoming Z lx old field written,
    runtime_getObj h lx = Some old ->
    authority_colors_runtime_mutable h
      (executing_authority_color_set CT h frame incoming) ->
    authority_safe_field_endpoints CT h frame lx written ->
    executing_authority_colors_separated CT h Z frame incoming ->
    executing_authority_colors_separated CT
      (update_field h lx field (Iot written)) Z frame incoming.
Proof.
  intros CT h frame incoming Z lx old field written Hobj Hruntime
    Hendpoints Hseparated.
  eapply executing_authority_colors_after_heap_change.
  - exact Hseparated.
  - intros location Howned.
    eapply executing_authority_field_update_owned_covered; eauto.
  - intros old_mode left right Hmode Hleft Hedge.
    eapply executing_authority_field_update_forward_covered; eauto.
  - intros old_mode left right Hmode Hleft Hedge.
    eapply executing_authority_field_update_backward_covered; eauto.
Qed.

(** Color-origin form of the preceding heap-change argument.  Unlike the
    separation wrapper, this lemma exposes the old dangerous color itself;
    it is the compositional body summary used at call return. *)
Lemma executing_authority_colors_after_heap_change_covered :
  forall CT h h' frame incoming,
    (forall location,
      frame_owned_location CT h' frame location ->
      exists old_mode,
        authority_mode_dangerous old_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h frame incoming)
          (old_mode, location)) ->
    (forall old_mode left right,
      authority_mode_dangerous old_mode ->
      In authority_flow_state
        (executing_authority_color_set CT h frame incoming)
        (old_mode, left) ->
      retained_mut_edge CT h' left right ->
      exists target_mode,
        authority_mode_dangerous target_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h frame incoming)
          (target_mode, right)) ->
    (forall old_mode left right,
      authority_mode_dangerous old_mode ->
      In authority_flow_state
        (executing_authority_color_set CT h frame incoming)
        (old_mode, left) ->
      mutable_edge CT h' right left ->
      exists target_mode,
        authority_mode_dangerous target_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h frame incoming)
          (target_mode, right)) ->
    forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT h' frame incoming)
        (mode, location) ->
      exists old_mode,
        authority_mode_dangerous old_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h frame incoming)
          (old_mode, location).
Proof.
  intros CT h h' frame incoming Howned Hforward Hbackward mode location
    Hmode [seed [Hseed Hconnected]].
  set (old_colors := executing_authority_color_set CT h frame incoming).
  assert (Hclosed : forall old_source old_target,
      In authority_flow_state old_colors old_source ->
      phased_authority_frame_connected CT h frame old_source old_target ->
      In authority_flow_state old_colors old_target).
  { intros old_source old_target [origin [Horigin Hsource]] Hpath.
    exists origin. split; [exact Horigin|].
    eapply rt_trans; eauto. }
  assert (Hseed_covered : authority_state_covered old_colors seed).
  { destruct seed as [seed_mode seed_location]. simpl. intros Hseed_mode.
    inversion Hseed; subst.
    - exists seed_mode. split; [exact Hseed_mode|].
      unfold old_colors, executing_authority_color_set.
      exists (seed_mode, seed_location). split;
        [left; exact H|apply rt_refl].
    - destruct H as [owned [Heq Hlocation]]. inversion Heq; subst.
      eapply Howned. exact Hlocation. }
  have Hcovered := phased_authority_frame_connected_preserves_coverage CT h
    h' frame old_colors seed (mode, location) Hclosed Howned Hforward
    Hbackward Hseed_covered Hconnected Hmode.
  exact Hcovered.
Qed.

Lemma executing_authority_colors_after_safe_field_update_covered :
  forall CT h frame incoming lx old field written,
    runtime_getObj h lx = Some old ->
    authority_colors_runtime_mutable h
      (executing_authority_color_set CT h frame incoming) ->
    authority_safe_field_endpoints CT h frame lx written ->
    forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT
          (update_field h lx field (Iot written)) frame incoming)
        (mode, location) ->
      exists old_mode,
        authority_mode_dangerous old_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h frame incoming)
          (old_mode, location).
Proof.
  intros CT h frame incoming lx old field written Hobj Hruntime Hendpoints.
  eapply executing_authority_colors_after_heap_change_covered.
  - intros location Howned.
    eapply executing_authority_field_update_owned_covered; eauto.
  - intros old_mode left right Hmode Hleft Hedge.
    eapply executing_authority_field_update_forward_covered; eauto.
  - intros old_mode left right Hmode Hleft Hedge.
    eapply executing_authority_field_update_backward_covered; eauto.
Qed.

Lemma executing_authority_colors_after_graph_reflection :
  forall CT h h' frame incoming Z,
    (forall location,
      frame_owned_location CT h' frame location ->
      frame_owned_location CT h frame location) ->
    (forall left right,
      retained_mut_edge CT h' left right ->
      retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right ->
      mutable_edge CT h left right) ->
    executing_authority_colors_separated CT h Z frame incoming ->
    executing_authority_colors_separated CT h' Z frame incoming.
Proof.
  intros CT h h' frame incoming Z Howned Hretained Hmutable Hseparated.
  eapply executing_authority_colors_after_heap_change.
  - exact Hseparated.
  - intros location Hlocation. exists FlowPowered.
    split; [left; reflexivity|]. apply executing_authority_owned_is_powered.
    apply Howned. exact Hlocation.
  - intros old_mode left right Hmode Hleft Hedge. exists old_mode.
    split; [exact Hmode|]. eapply executing_authority_dangerous_retained;
      eauto.
  - intros old_mode left right Hmode Hleft Hedge. exists FlowProspective.
    split; [right; reflexivity|].
    eapply executing_authority_dangerous_reverse_rdm; eauto.
Qed.

(** Color-origin counterpart of graph reflection.  This is used for
    transitions that change neither the active environment nor any edge
    visible to the authority graph. *)
Lemma executing_authority_colors_after_graph_reflection_covered :
  forall CT h h' frame incoming,
    (forall location,
      frame_owned_location CT h' frame location ->
      frame_owned_location CT h frame location) ->
    (forall left right,
      retained_mut_edge CT h' left right ->
      retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right ->
      mutable_edge CT h left right) ->
    forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT h' frame incoming)
        (mode, location) ->
      exists old_mode,
        authority_mode_dangerous old_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h frame incoming)
          (old_mode, location).
Proof.
  intros CT h h' frame incoming Howned Hretained Hmutable.
  eapply executing_authority_colors_after_heap_change_covered.
  - intros location Hlocation. exists FlowPowered.
    split; [left; reflexivity|]. apply executing_authority_owned_is_powered.
    apply Howned. exact Hlocation.
  - intros old_mode left right Hmode Hleft Hedge. exists old_mode.
    split; [exact Hmode|]. eapply executing_authority_dangerous_retained;
      eauto.
  - intros old_mode left right Hmode Hleft Hedge. exists FlowProspective.
    split; [right; reflexivity|].
    eapply executing_authority_dangerous_reverse_rdm; eauto.
Qed.

(** Erasing authority modes from a phase-local path yields an ordinary
    potential path in the same active frame.  Forget, mark, and promotion
    steps erase to reflexivity. *)
Lemma phased_authority_frame_step_projects_to_potential :
  forall CT h frame stack source target,
    phased_authority_frame_step CT h frame source target ->
    potential_connected CT h frame stack (snd source) (snd target).
Proof.
  intros CT h frame stack source target Hstep.
  inversion Hstep; subst; simpl.
  - apply rt_step. left. left. exact H.
  - apply rt_step. left. left. exact H.
  - apply rt_step. left. right. exact H.
  - apply rt_step. left. right. exact H.
  - apply rt_step. left. left. constructor. exact H.
  - apply rt_step. left. right. exact H.
  - apply rt_step. right. left. exists frame. split; [constructor|].
    split; [exact H|exact H0].
  - apply rt_step. right. left. exists frame. split; [constructor|].
    split; [exact H|exact H0].
  - apply rt_step. right. left. exists frame. split; [constructor|].
    split; [exact H|exact H0].
  - apply rt_refl.
  - apply rt_refl.
  - apply rt_refl.
  - apply rt_refl.
Qed.

Lemma phased_authority_frame_connected_projects_to_potential :
  forall CT h frame stack source target,
    phased_authority_frame_connected CT h frame source target ->
    potential_connected CT h frame stack (snd source) (snd target).
Proof.
  intros CT h frame stack source target Hconnected.
  induction Hconnected.
  - eapply phased_authority_frame_step_projects_to_potential; eauto.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma phased_authority_neutral_mutable_forward :
  forall CT h frame left right,
    mutable_reachable CT h left right ->
    phased_authority_frame_connected CT h frame
      (FlowNeutral, left) (FlowNeutral, right).
Proof.
  intros CT h frame left right Hreachable.
  induction Hreachable.
  - apply rt_refl.
  - eapply rt_trans; [exact IHHreachable|].
    apply rt_step. apply phased_authority_neutral_rdm_forward. exact H.
Qed.

Lemma phased_authority_neutral_mutable_reverse :
  forall CT h frame left right,
    mutable_reachable CT h left right ->
    phased_authority_frame_connected CT h frame
      (FlowNeutral, right) (FlowNeutral, left).
Proof.
  intros CT h frame left right Hreachable.
  induction Hreachable.
  - apply rt_refl.
  - eapply rt_trans.
    + apply rt_step. apply phased_authority_neutral_rdm_backward. exact H.
    + exact IHHreachable.
Qed.

Lemma phased_authority_prospective_mutable_forward :
  forall CT h frame left right,
    mutable_reachable CT h left right ->
    phased_authority_frame_connected CT h frame
      (FlowProspective, left) (FlowProspective, right).
Proof.
  intros CT h frame left right Hreachable.
  induction Hreachable.
  - apply rt_refl.
  - eapply rt_trans; [exact IHHreachable|].
    apply rt_step. apply phased_authority_prospective_retained.
    constructor. exact H.
Qed.

Lemma phased_authority_prospective_mutable_reverse :
  forall CT h frame left right,
    mutable_reachable CT h left right ->
    phased_authority_frame_connected CT h frame
      (FlowProspective, right) (FlowProspective, left).
Proof.
  intros CT h frame left right Hreachable.
  induction Hreachable.
  - apply rt_refl.
  - eapply rt_trans.
    + apply rt_step. apply phased_authority_prospective_rdm_backward.
      exact H.
    + exact IHHreachable.
Qed.

Lemma phased_authority_powered_mutable_reverse :
  forall CT h frame left right,
    mutable_reachable CT h left right ->
    phased_authority_frame_connected CT h frame
      (FlowPowered, right) (FlowProspective, left).
Proof.
  intros CT h frame left right Hreachable.
  induction Hreachable as [location | first middle last Hprefix IH Hedge].
  - apply rt_step. apply phased_authority_mark_prospective.
  - eapply rt_trans.
    + apply rt_step. apply phased_authority_reverse_rdm. exact Hedge.
    + eapply phased_authority_prospective_mutable_reverse. exact Hprefix.
Qed.

Lemma phased_authority_neutral_mutable_connected :
  forall CT h frame left right,
    mutable_connected CT h left right ->
    phased_authority_frame_connected CT h frame
      (FlowNeutral, left) (FlowNeutral, right).
Proof.
  intros CT h frame left right Hconnected.
  induction Hconnected.
  - apply rt_step. destruct H as [Hforward | Hbackward].
    + apply phased_authority_neutral_rdm_forward. exact Hforward.
    + apply phased_authority_neutral_rdm_backward. exact Hbackward.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma phased_authority_frame_step_after_descent_reflects :
  forall CT h authority old_senv old_renv new_senv new_renv source target,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame authority new_senv new_renv))
      (phase_frame_capability_set CT h
        (mk_watched_frame authority old_senv old_renv)) ->
    phased_authority_frame_step CT h
      (mk_watched_frame authority new_senv new_renv) source target ->
    phased_authority_frame_connected CT h
      (mk_watched_frame authority old_senv old_renv) source target.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv source target
    Hdescend Howned Hstep.
  inversion Hstep; subst.
  - apply rt_step. apply phased_authority_retained. exact H.
  - apply rt_step. apply phased_authority_prospective_retained. exact H.
  - apply rt_step. apply phased_authority_prospective_rdm_backward. exact H.
  - apply rt_step. apply phased_authority_reverse_rdm. exact H.
  - apply rt_step. apply phased_authority_neutral_rdm_forward. exact H.
  - apply rt_step. apply phased_authority_neutral_rdm_backward. exact H.
  - destruct (Hdescend left H) as
      [old_left [Hold_left Hleft_path]].
    destruct (Hdescend right H0) as
      [old_right [Hold_right Hright_path]].
    eapply rt_trans.
    + eapply phased_authority_powered_mutable_reverse. exact Hleft_path.
    + eapply rt_trans.
      * apply rt_step. eapply phased_authority_prospective_frame_join; eauto.
      * eapply phased_authority_prospective_mutable_forward.
        exact Hright_path.
  - destruct (Hdescend left H) as
      [old_left [Hold_left Hleft_path]].
    destruct (Hdescend right H0) as
      [old_right [Hold_right Hright_path]].
    eapply rt_trans.
    + eapply phased_authority_prospective_mutable_reverse. exact Hleft_path.
    + eapply rt_trans.
      * apply rt_step. eapply phased_authority_prospective_frame_join; eauto.
      * eapply phased_authority_prospective_mutable_forward.
        exact Hright_path.
  - destruct (Hdescend left H) as
      [old_left [Hold_left Hleft_path]].
    destruct (Hdescend right H0) as
      [old_right [Hold_right Hright_path]].
    eapply rt_trans.
    + eapply phased_authority_neutral_mutable_reverse. exact Hleft_path.
    + eapply rt_trans.
      * apply rt_step. eapply phased_authority_neutral_frame_join; eauto.
      * eapply phased_authority_neutral_mutable_forward. exact Hright_path.
  - apply rt_step. apply phased_authority_forget.
  - apply rt_step. apply phased_authority_prospective_forget.
  - apply rt_step. apply phased_authority_mark_prospective.
  - apply rt_step. apply phased_authority_promote. apply Howned. exact H.
Qed.

Lemma phased_authority_frame_connected_after_descent_reflects :
  forall CT h authority old_senv old_renv new_senv new_renv source target,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame authority new_senv new_renv))
      (phase_frame_capability_set CT h
        (mk_watched_frame authority old_senv old_renv)) ->
    phased_authority_frame_connected CT h
      (mk_watched_frame authority new_senv new_renv) source target ->
    phased_authority_frame_connected CT h
      (mk_watched_frame authority old_senv old_renv) source target.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv source target
    Hdescend Howned Hconnected.
  induction Hconnected.
  - eapply phased_authority_frame_step_after_descent_reflects; eauto.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma phased_authority_frame_closure_contains :
  forall CT h frame seeds,
    Included authority_flow_state seeds
      (phased_authority_frame_closure CT h frame seeds).
Proof.
  intros CT h frame seeds state Hstate.
  exists state. split; [exact Hstate|apply rt_refl].
Qed.

Inductive authority_flow_step
  (CT : class_table) (h : heap)
  (active : watched_frame) (stack : list watched_boundary) :
  authority_flow_state -> authority_flow_state -> Prop :=
| authority_flow_retained : forall left right,
    retained_mut_edge CT h left right ->
    authority_flow_step CT h active stack
      (FlowPowered, left) (FlowPowered, right)
| authority_flow_reverse_rdm : forall left right,
    mutable_edge CT h right left ->
    authority_flow_step CT h active stack
      (FlowPowered, left) (FlowNeutral, right)
| authority_flow_neutral_rdm_forward : forall left right,
    mutable_edge CT h left right ->
    authority_flow_step CT h active stack
      (FlowNeutral, left) (FlowNeutral, right)
| authority_flow_neutral_rdm_backward : forall left right,
    mutable_edge CT h right left ->
    authority_flow_step CT h active stack
      (FlowNeutral, left) (FlowNeutral, right)
| authority_flow_powered_frame : forall left right,
    potential_frame_edge active stack left right ->
    authority_flow_step CT h active stack
      (FlowPowered, left) (FlowNeutral, right)
| authority_flow_neutral_frame : forall left right,
    potential_frame_edge active stack left right ->
    authority_flow_step CT h active stack
      (FlowNeutral, left) (FlowNeutral, right)
| authority_flow_forget : forall location,
    authority_flow_step CT h active stack
      (FlowPowered, location) (FlowNeutral, location)
| authority_flow_promote : forall location,
    In Loc (live_capability_set CT h active stack) location ->
    authority_flow_step CT h active stack
      (FlowNeutral, location) (FlowPowered, location).

Definition authority_flow_connected
  (CT : class_table) (h : heap)
  (active : watched_frame) (stack : list watched_boundary) :
  authority_flow_state -> authority_flow_state -> Prop :=
  clos_refl_trans authority_flow_state
    (authority_flow_step CT h active stack).

Lemma authority_flow_step_projects_to_color :
  forall CT h active stack source target,
    authority_flow_step CT h active stack source target ->
    authority_color_connected CT h active stack
      (snd source) (snd target).
Proof.
  intros CT h active stack source target Hstep.
  inversion Hstep; subst; simpl.
  - apply rt_step. left. left. exact H.
  - apply rt_step. left. right. exact H.
  - apply rt_step. left. left. constructor. exact H.
  - apply rt_step. left. right. exact H.
  - apply rt_step. right. exact H.
  - apply rt_step. right. exact H.
  - apply rt_refl.
  - apply rt_refl.
Qed.

Lemma authority_flow_connected_projects_to_color :
  forall CT h active stack source target,
    authority_flow_connected CT h active stack source target ->
    authority_color_connected CT h active stack
      (snd source) (snd target).
Proof.
  intros CT h active stack source target Hconnected.
  induction Hconnected.
  - eapply authority_flow_step_projects_to_color; eauto.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma mutable_reachable_is_reverse_neutral_authority_flow :
  forall CT h active stack left right,
    mutable_reachable CT h left right ->
    authority_flow_connected CT h active stack
      (FlowNeutral, right) (FlowNeutral, left).
Proof.
  intros CT h active stack left right Hreachable.
  induction Hreachable.
  - apply rt_refl.
  - eapply rt_trans.
    + apply rt_step. apply authority_flow_neutral_rdm_backward. exact H.
    + exact IHHreachable.
Qed.

Definition live_boundary_cutoffs_valid
  (h : heap) (stack : list watched_boundary) : Prop :=
  Forall (fun boundary =>
    boundary.(boundary_entry_cutoff) <= dom h) stack.


Lemma live_boundary_cutoffs_valid_heap_growth :
  forall h h' stack,
    dom h <= dom h' ->
    live_boundary_cutoffs_valid h stack ->
    live_boundary_cutoffs_valid h' stack.
Proof.
  intros h h' stack Hgrowth Hvalid.
  induction Hvalid; constructor; auto. lia.
Qed.

(** The operational/history facts and the potential-component separation are
    kept together because both are needed at every recursive statement
    evaluation, including a method body. *)
Definition potential_live_history_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary) (h : heap) : Prop :=
  live_authority_history_state CT P Z cutoff active stack h /\
  potential_colors_separated CT h
    (live_capability_set CT h active stack) Z active stack /\
  live_boundary_cutoffs_valid h stack.

(** Final authority-sensitive staged state.  It needs neither a dispatch
    compatibility premise nor a public ownership hypothesis: powered and
    neutral colors are computed directly from the live execution stack. *)
Definition principled_phased_authority_live_history_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary)
  (incoming : Ensemble authority_flow_state) (h : heap) : Prop :=
  protected_zone_contains P Z /\
  state_is_confined P cutoff active.(frame_renv) h /\
  authority_colors_runtime_mutable h incoming /\
  executing_authority_colors_separated CT h Z active incoming /\
  live_frames_wf CT h active stack /\
  live_frames_authority_sound h active stack /\
  cutoff <= dom h /\
  protected_zone_before_cutoff Z cutoff /\
  live_stack_authorities_chain active.(frame_authority) stack /\
  live_boundary_cutoffs_valid h stack.

(** Frozen caller authority deliberately excludes [FlowNeutral].  Neutral
    flow remembers component identity after authority has been forgotten; a
    later promotion at a callee-owned location is independent callee
    authority and must not be attributed retroactively to the caller. *)
Inductive frozen_caller_authority_step
  (CT : class_table) (h : heap) (frame : watched_frame) :
  authority_flow_state -> authority_flow_state -> Prop :=
| frozen_caller_retained : forall left right,
    retained_mut_edge CT h left right ->
    frozen_caller_authority_step CT h frame
      (FlowPowered, left) (FlowPowered, right)
| frozen_caller_prospective_retained : forall left right,
    retained_mut_edge CT h left right ->
    frozen_caller_authority_step CT h frame
      (FlowProspective, left) (FlowProspective, right)
| frozen_caller_prospective_rdm_backward : forall left right,
    mutable_edge CT h right left ->
    frozen_caller_authority_step CT h frame
      (FlowProspective, left) (FlowProspective, right)
| frozen_caller_reverse_rdm : forall left right,
    mutable_edge CT h right left ->
    frozen_caller_authority_step CT h frame
      (FlowPowered, left) (FlowProspective, right)
| frozen_caller_powered_frame_join : forall left right,
    effective_frame_rdm_root frame left ->
    effective_frame_rdm_root frame right ->
    frozen_caller_authority_step CT h frame
      (FlowPowered, left) (FlowProspective, right)
| frozen_caller_prospective_frame_join : forall left right,
    effective_frame_rdm_root frame left ->
    effective_frame_rdm_root frame right ->
    frozen_caller_authority_step CT h frame
      (FlowProspective, left) (FlowProspective, right)
| frozen_caller_mark_prospective : forall location,
    frozen_caller_authority_step CT h frame
      (FlowPowered, location) (FlowProspective, location).

Definition frozen_caller_authority_connected
  (CT : class_table) (h : heap) (frame : watched_frame) :=
  clos_refl_trans authority_flow_state
    (frozen_caller_authority_step CT h frame).

Definition frozen_caller_authority_closure
  (CT : class_table) (h : heap) (frame : watched_frame)
  (seeds : Ensemble authority_flow_state) : Ensemble authority_flow_state :=
  fun state => exists seed,
    In authority_flow_state seeds seed /\
    frozen_caller_authority_connected CT h frame seed state.

(** Prospective authority rooted at every RDM variable that will become live
    again when [frame] resumes.  Its closure records not merely the roots but
    every location to which a pop-time frame join could subsequently carry
    authority through retained mutable fields. *)
Definition frame_resume_exposure_seeds
  (h : heap) (frame : watched_frame) : Ensemble authority_flow_state :=
  fun state => exists root,
    In Loc (frame_rdm_root_set frame) root /\
    r_muttype h root = Some Mut_r /\
    state = (FlowProspective, root).

Definition frame_resume_exposure_colors
  (CT : class_table) (h : heap) (frame : watched_frame) :
  Ensemble authority_flow_state :=
  frozen_caller_authority_closure CT h frame
    (frame_resume_exposure_seeds h frame).

(** The exact latent component that can be activated when an RDM root
    resumes.  Unlike [mutable_authority_reachable], this relation includes
    reverse RDM edges and RDM frame joins because both are genuine
    [FlowProspective] transitions.  It deliberately excludes powered-only
    transitions and therefore remains a proof-local description of latent
    authority rather than an executable capability. *)
Definition prospective_mutable_authority_reachable
  (CT : class_table) (h : heap) (frame : watched_frame)
  (root target : Loc) : Prop :=
  mutable_authority_root frame h root /\
  frozen_caller_authority_connected CT h frame
    (FlowProspective, root) (FlowProspective, target).

Definition prospective_location_covered_by_frame
  (CT : class_table) (h : heap) (frame : watched_frame)
  (location : Loc) : Prop :=
  exists root,
    mutable_authority_root frame h root /\
    frozen_caller_authority_connected CT h frame
      (FlowProspective, root) (FlowProspective, location).

Definition active_prospective_mutable_authority_components_after_cutoff
  (CT : class_table) (h : heap) (cutoff : Loc)
  (frame : watched_frame) : Prop :=
  forall root target,
    prospective_mutable_authority_reachable CT h frame root target ->
    cutoff <= target.

Definition live_prospective_mutable_authority_components_after_cutoff
  (CT : class_table) (h : heap) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary) : Prop :=
  forall frame root target,
    live_frame_member active stack frame ->
    prospective_mutable_authority_reachable CT h frame root target ->
    cutoff <= target.

Lemma live_prospective_mutable_authority_components_active :
  forall CT h cutoff active stack,
    live_prospective_mutable_authority_components_after_cutoff CT h cutoff
      active stack ->
    active_prospective_mutable_authority_components_after_cutoff CT h cutoff
      active.
Proof.
  intros CT h cutoff active stack Hcomponents root target Hreachable.
  eapply Hcomponents; [constructor|exact Hreachable].
Qed.

Definition dangerous_authority_colors
  (colors : Ensemble authority_flow_state) : Ensemble authority_flow_state :=
  fun state =>
    In authority_flow_state colors state /\
    authority_mode_dangerous (fst state).

Lemma frozen_caller_authority_closure_contains :
  forall CT h frame seeds,
    Included authority_flow_state seeds
      (frozen_caller_authority_closure CT h frame seeds).
Proof.
  intros CT h frame seeds state Hstate.
  exists state. split; [exact Hstate|apply rt_refl].
Qed.

Lemma frozen_caller_authority_closure_idempotent :
  forall CT h frame seeds,
    Same_set authority_flow_state
      (frozen_caller_authority_closure CT h frame
        (frozen_caller_authority_closure CT h frame seeds))
      (frozen_caller_authority_closure CT h frame seeds).
Proof.
  intros CT h frame seeds. split.
  - intros state [middle [[seed [Hseed Hfirst]] Hsecond]].
    exists seed. split; [exact Hseed|]. eapply rt_trans; eauto.
  - apply frozen_caller_authority_closure_contains.
Qed.

Lemma frozen_caller_authority_step_is_phased :
  forall CT h frame source target,
    frozen_caller_authority_step CT h frame source target ->
    phased_authority_frame_step CT h frame source target.
Proof.
  intros CT h frame source target Hstep. inversion Hstep; subst.
  - apply phased_authority_retained. exact H.
  - apply phased_authority_prospective_retained. exact H.
  - apply phased_authority_prospective_rdm_backward. exact H.
  - apply phased_authority_reverse_rdm. exact H.
  - eapply phased_authority_powered_frame_join; eauto.
  - eapply phased_authority_prospective_frame_join; eauto.
  - apply phased_authority_mark_prospective.
Qed.

Lemma frozen_caller_authority_connected_is_phased :
  forall CT h frame source target,
    frozen_caller_authority_connected CT h frame source target ->
    phased_authority_frame_connected CT h frame source target.
Proof.
  intros CT h frame source target Hconnected. induction Hconnected.
  - apply rt_step. apply frozen_caller_authority_step_is_phased. exact H.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma prospective_location_covered_by_frame_runtime_mutable :
  forall CT h frame location,
    wf_r_config CT frame.(frame_senv) frame.(frame_renv) h ->
    authority_context_sound h frame.(frame_renv) frame.(frame_authority) ->
    prospective_location_covered_by_frame CT h frame location ->
    r_muttype h location = Some Mut_r.
Proof.
  intros CT h frame location Hwf Hsound [root [Hroot Hpath]].
  have Hroot_runtime := mutable_authority_root_runtime_mutable CT h frame root
    Hwf Hsound Hroot.
  have Hphased := frozen_caller_authority_connected_is_phased CT h frame
    (FlowProspective, root) (FlowProspective, location) Hpath.
  exact (phased_authority_frame_connected_preserves_runtime_mutability CT h
    frame (FlowProspective, root) (FlowProspective, location) Mut_r Hwf
    Hphased Hroot_runtime).
Qed.

(** Proof-local provenance relative to the currently executing frame.  This
    definition is placed with the frozen graph because nested statement
    induction must preserve it long before the pop-specific derivation is
    constructed. *)
Definition frozen_authority_origin
  (CT : class_table) (h : heap) (frame : watched_frame)
  (incoming : Ensemble authority_flow_state)
  (state : authority_flow_state) : Prop :=
  exists seed,
    ((authority_mode_dangerous (fst seed) /\
       In authority_flow_state incoming seed) \/
     (exists anchor,
       seed = (FlowPowered, anchor) /\
       frame_owned_location CT h frame anchor)) /\
    frozen_caller_authority_connected CT h frame seed state.

Lemma channel_free_entry_frozen_step_reflects :
  forall CT h boundary old_frame source target,
    entry_ownership_channel_free boundary ->
    frozen_caller_authority_step CT h
      (mk_watched_frame
        (call_authority boundary.(boundary_caller).(frame_authority)
          boundary.(boundary_receiver_view))
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv)) source target ->
    frozen_caller_authority_step CT h old_frame source target.
Proof.
  intros CT h boundary old_frame source target [Hno_capability Hno_rdm]
    Hstep.
  inversion Hstep; subst.
  - apply frozen_caller_retained. exact H.
  - apply frozen_caller_prospective_retained. exact H.
  - apply frozen_caller_prospective_rdm_backward. exact H.
  - apply frozen_caller_reverse_rdm. exact H.
  - exfalso. exact (Hno_rdm left H).
  - exfalso. exact (Hno_rdm left H).
  - apply frozen_caller_mark_prospective.
Qed.

Lemma channel_free_entry_frozen_connected_reflects :
  forall CT h boundary old_frame source target,
    entry_ownership_channel_free boundary ->
    frozen_caller_authority_connected CT h
      (mk_watched_frame
        (call_authority boundary.(boundary_caller).(frame_authority)
          boundary.(boundary_receiver_view))
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv)) source target ->
    frozen_caller_authority_connected CT h old_frame source target.
Proof.
  intros CT h boundary old_frame source target Hfree Hconnected.
  induction Hconnected.
  - apply rt_step. eapply channel_free_entry_frozen_step_reflects; eauto.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

(** A caller color snapshot is proof-only state captured when a call suspends
    its caller.  Current execution colors advance through the active phase;
    latent resume exposure is always closed under the saved caller frame.
    Keeping that frame makes the exposure's graph interpretation stable when
    nested callees return. *)
Record frozen_caller_color_snapshot : Type := mk_frozen_caller_color_snapshot {
  frozen_snapshot_entry_colors : Ensemble authority_flow_state;
  frozen_snapshot_current_colors : Ensemble authority_flow_state;
  frozen_snapshot_entry_phase : Ensemble authority_flow_state;
  frozen_snapshot_phase_incoming : Ensemble authority_flow_state;
  frozen_snapshot_resume_rdm_roots : Ensemble Loc;
  frozen_snapshot_entry_resume_exposure : Ensemble authority_flow_state;
  frozen_snapshot_current_resume_exposure : Ensemble authority_flow_state;
  frozen_snapshot_resume_frame : watched_frame;
  (** Whether RDM denoted mutable authority in the suspended caller. *)
  frozen_snapshot_resume_authority : q_r
}.

Definition frozen_caller_snapshot_slot : Type :=
  option frozen_caller_color_snapshot.

(** A tracked slot is paired with its operational boundary and with the
    prefix of callee-side boundaries above it.  This alignment lets the
    private proof state state freshness only for frames executing on the
    callee side of that particular call; older caller frames are deliberately
    excluded. *)
Inductive frozen_snapshot_live_partition :
  list frozen_caller_snapshot_slot -> list watched_boundary ->
  frozen_caller_color_snapshot -> watched_boundary ->
  list watched_boundary -> list watched_boundary -> Prop :=
| frozen_snapshot_partition_here : forall snapshot snapshots boundary stack,
    frozen_snapshot_live_partition (Some snapshot :: snapshots)
      (boundary :: stack) snapshot boundary [] stack
| frozen_snapshot_partition_there : forall slot top snapshots stack snapshot
    boundary above below,
    frozen_snapshot_live_partition snapshots stack snapshot boundary
      above below ->
    frozen_snapshot_live_partition (slot :: snapshots) (top :: stack)
      snapshot boundary (top :: above) below.

Lemma frozen_snapshot_live_partition_is_live_call :
  forall snapshots stack snapshot boundary above below active,
    frozen_snapshot_live_partition snapshots stack snapshot boundary
      above below ->
    live_call_partition active stack boundary above below.
Proof.
  intros snapshots stack snapshot boundary above below active Hpartition.
  induction Hpartition.
  - constructor.
  - constructor. exact IHHpartition.
Qed.

Lemma frozen_snapshot_in_has_live_partition :
  forall snapshots stack snapshot,
    length snapshots = length stack ->
    List.In (Some snapshot) snapshots ->
    exists boundary above below,
      frozen_snapshot_live_partition snapshots stack snapshot boundary
        above below.
Proof.
  induction snapshots as [|slot snapshots IH]; intros stack snapshot Hlength
    Hin; [inversion Hin|].
  destruct stack as [|boundary stack]; [discriminate|].
  simpl in Hlength. injection Hlength as Htail_length.
  simpl in Hin. destruct Hin as [Hhead | Htail].
  - subst slot. exists boundary, ([] : list watched_boundary), stack.
    constructor.
  - destruct (IH stack snapshot Htail_length Htail) as
      [tracked_boundary [above [below Hpartition]]].
    exists tracked_boundary, (boundary :: above), below.
    constructor. exact Hpartition.
Qed.

(** The same tail-partition fact does not depend on the head slot being
    tracked.  This form is used when an intentionally untracked [None]
    boundary is popped while older tracked snapshots remain below it. *)
Lemma frozen_snapshot_in_tail_has_partition_below_slot :
  forall slot snapshots boundary stack snapshot,
    length (slot :: snapshots) = length (boundary :: stack) ->
    List.In (Some snapshot) snapshots ->
    exists tracked_boundary above below,
      frozen_snapshot_live_partition (slot :: snapshots)
        (boundary :: stack) snapshot tracked_boundary (boundary :: above)
        below.
Proof.
  intros slot snapshots boundary stack snapshot Haligned Hin.
  simpl in Haligned. injection Haligned as Htail_length.
  destruct (frozen_snapshot_in_has_live_partition snapshots stack snapshot
    Htail_length Hin) as [tracked_boundary [above [below Hpartition]]].
  exists tracked_boundary, above, below. constructor. exact Hpartition.
Qed.

Definition frozen_callee_side_mutable_components_after_boundaries
  (CT : class_table) (h : heap) (active : watched_frame)
  (snapshots : list frozen_caller_snapshot_slot)
  (stack : list watched_boundary) : Prop :=
  forall snapshot boundary above below,
    frozen_snapshot_live_partition snapshots stack snapshot boundary
      above below ->
    live_mutable_authority_components_after_cutoff CT h
      boundary.(boundary_entry_cutoff) active above.

(** Full prospective counterpart of the retained-direction partition above.
    This is the certificate consumed by the second-order exposure classifier:
    every latent component on a tracked boundary's callee side lies beyond
    that boundary's entry cutoff. *)
Definition frozen_callee_side_prospective_components_after_boundaries
  (CT : class_table) (h : heap) (active : watched_frame)
  (snapshots : list frozen_caller_snapshot_slot)
  (stack : list watched_boundary) : Prop :=
  forall snapshot boundary above below,
    frozen_snapshot_live_partition snapshots stack snapshot boundary
      above below ->
    live_prospective_mutable_authority_components_after_cutoff CT h
      boundary.(boundary_entry_cutoff) active above.

Lemma repeat_none_has_no_frozen_snapshot_partition :
  forall count stack snapshot boundary above below,
    ~ frozen_snapshot_live_partition
        (repeat (None : frozen_caller_snapshot_slot) count) stack
        snapshot boundary above below.
Proof.
  intros count. induction count as [|count IH]; intros stack snapshot boundary
    above below Hpartition.
  - inversion Hpartition.
  - simpl in Hpartition. inversion Hpartition; subst.
    eapply IH; eauto.
Qed.

(** Static snapshot metadata never changes while an active phase advances
    the two current color images.  The strengthened statement induction uses
    this relation to recover the exact call-entry roots and incoming colors
    after an arbitrarily long nested body evaluation. *)
Definition frozen_caller_snapshot_metadata_eq
  (new old : frozen_caller_color_snapshot) : Prop :=
  Same_set authority_flow_state new.(frozen_snapshot_entry_colors)
    old.(frozen_snapshot_entry_colors) /\
  Same_set authority_flow_state new.(frozen_snapshot_entry_phase)
    old.(frozen_snapshot_entry_phase) /\
  Same_set authority_flow_state new.(frozen_snapshot_phase_incoming)
    old.(frozen_snapshot_phase_incoming) /\
  Same_set Loc new.(frozen_snapshot_resume_rdm_roots)
    old.(frozen_snapshot_resume_rdm_roots) /\
  Same_set authority_flow_state new.(frozen_snapshot_entry_resume_exposure)
    old.(frozen_snapshot_entry_resume_exposure) /\
  new.(frozen_snapshot_resume_frame) = old.(frozen_snapshot_resume_frame) /\
  new.(frozen_snapshot_resume_authority) =
    old.(frozen_snapshot_resume_authority).

Definition frozen_caller_snapshot_slot_metadata_eq
  (new old : frozen_caller_snapshot_slot) : Prop :=
  match new, old with
  | Some new_snapshot, Some old_snapshot =>
      frozen_caller_snapshot_metadata_eq new_snapshot old_snapshot
  | None, None => True
  | _, _ => False
  end.

Definition frozen_caller_snapshot_list_metadata_eq
  (new old : list frozen_caller_snapshot_slot) : Prop :=
  Forall2 frozen_caller_snapshot_slot_metadata_eq new old.

(** Target snapshots use [phase_incoming] as a forward-only activation
    history.  All genuinely static metadata remains exact, but an older
    target may remember additional colors whenever one of its nested
    callees returns.  Ordinary snapshots and exceptional resume witnesses
    continue to use [frozen_caller_snapshot_metadata_eq]. *)
Definition frozen_target_snapshot_metadata_le
  (new old : frozen_caller_color_snapshot) : Prop :=
  Same_set authority_flow_state new.(frozen_snapshot_entry_colors)
    old.(frozen_snapshot_entry_colors) /\
  Same_set authority_flow_state new.(frozen_snapshot_entry_phase)
    old.(frozen_snapshot_entry_phase) /\
  Included authority_flow_state old.(frozen_snapshot_phase_incoming)
    new.(frozen_snapshot_phase_incoming) /\
  Same_set Loc new.(frozen_snapshot_resume_rdm_roots)
    old.(frozen_snapshot_resume_rdm_roots) /\
  Same_set authority_flow_state new.(frozen_snapshot_entry_resume_exposure)
    old.(frozen_snapshot_entry_resume_exposure) /\
  new.(frozen_snapshot_resume_frame) = old.(frozen_snapshot_resume_frame) /\
  new.(frozen_snapshot_resume_authority) =
    old.(frozen_snapshot_resume_authority).

Definition frozen_target_snapshot_slot_metadata_le
  (new old : frozen_caller_snapshot_slot) : Prop :=
  match new, old with
  | Some new_snapshot, Some old_snapshot =>
      frozen_target_snapshot_metadata_le new_snapshot old_snapshot
  | None, None => True
  | _, _ => False
  end.

Definition advance_frozen_caller_snapshot
  (CT : class_table) (h : heap) (active : watched_frame)
  (snapshot : frozen_caller_color_snapshot) :
  frozen_caller_color_snapshot :=
  mk_frozen_caller_color_snapshot
    snapshot.(frozen_snapshot_entry_colors)
    (frozen_caller_authority_closure CT h active
      snapshot.(frozen_snapshot_current_colors))
    snapshot.(frozen_snapshot_entry_phase)
    snapshot.(frozen_snapshot_phase_incoming)
    snapshot.(frozen_snapshot_resume_rdm_roots)
    snapshot.(frozen_snapshot_entry_resume_exposure)
    (frozen_caller_authority_closure CT h active
      snapshot.(frozen_snapshot_current_resume_exposure))
    snapshot.(frozen_snapshot_resume_frame)
    snapshot.(frozen_snapshot_resume_authority).

Definition advance_frozen_caller_snapshots
  (CT : class_table) (h : heap) (active : watched_frame)
  (snapshots : list frozen_caller_snapshot_slot) :
  list frozen_caller_snapshot_slot :=
  map (fun slot =>
    match slot with
    | Some snapshot =>
        Some (advance_frozen_caller_snapshot CT h active snapshot)
    | None => None
    end) snapshots.

Lemma advance_frozen_caller_snapshot_metadata_eq :
  forall CT h active snapshot,
    frozen_caller_snapshot_metadata_eq
      (advance_frozen_caller_snapshot CT h active snapshot) snapshot.
Proof.
  intros CT h active snapshot. unfold frozen_caller_snapshot_metadata_eq,
    advance_frozen_caller_snapshot. simpl. repeat split; try reflexivity;
    intros state Hstate; exact Hstate.
Qed.

(** Entering a tracked call first captures the caller's completed colors and
    then advances every tracked caller color through the new active frame.
    The map never inspects any suspended frame. *)
Definition enter_frozen_caller_snapshots
  (CT : class_table) (h : heap) (caller callee : watched_frame)
  (caller_colors : Ensemble authority_flow_state)
  (snapshots : list frozen_caller_snapshot_slot) :
  list frozen_caller_snapshot_slot :=
  Some (mk_frozen_caller_color_snapshot
    (frozen_caller_authority_closure CT h callee
      (dangerous_authority_colors caller_colors))
    (frozen_caller_authority_closure CT h callee
      (dangerous_authority_colors caller_colors))
    caller_colors
    caller_colors
    (frame_rdm_root_set caller)
    (frame_resume_exposure_colors CT h caller)
    (frozen_caller_authority_closure CT h callee
      (frame_resume_exposure_colors CT h caller))
    caller
    caller.(frame_authority)) ::
  advance_frozen_caller_snapshots CT h callee snapshots.

(** Dangerous colors carried for older suspended callers must also cross a
    nested call boundary.  The ordinary caller color set alone is not a
    compositional summary: an older frozen color can reach the nested
    return location even when that color is not independently exercisable
    by the immediate caller.  This proof-only union supplies the tracked
    head with exactly those additional seeds. *)
Definition frozen_caller_snapshot_current_color_union
  (snapshots : list frozen_caller_snapshot_slot) :
  Ensemble authority_flow_state :=
  fun state =>
    exists snapshot,
      List.In (Some snapshot) snapshots /\
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        state.

Definition nested_frozen_call_entry_seeds
  (caller_colors : Ensemble authority_flow_state)
  (snapshots : list frozen_caller_snapshot_slot) :
  Ensemble authority_flow_state :=
  Union authority_flow_state
    (dangerous_authority_colors caller_colors)
    (frozen_caller_snapshot_current_color_union snapshots).

(** Stack-compositional tracked head.  [caller_colors] remains the exact
    phase incoming set restored at pop; only the private frozen image is
    enlarged with older frozen provenance. *)
Definition nested_frozen_call_head
  (CT : class_table) (h : heap) (caller callee : watched_frame)
  (caller_colors : Ensemble authority_flow_state)
  (snapshots : list frozen_caller_snapshot_slot) :
  frozen_caller_color_snapshot :=
  mk_frozen_caller_color_snapshot
    (frozen_caller_authority_closure CT h callee
      (nested_frozen_call_entry_seeds caller_colors snapshots))
    (frozen_caller_authority_closure CT h callee
      (nested_frozen_call_entry_seeds caller_colors snapshots))
    caller_colors
    caller_colors
    (frame_rdm_root_set caller)
    (frame_resume_exposure_colors CT h caller)
    (frozen_caller_authority_closure CT h callee
      (frame_resume_exposure_colors CT h caller))
    caller
    caller.(frame_authority).

Lemma advance_frozen_snapshot_live_partition_reflects :
  forall CT h active snapshots stack new_snapshot boundary above below,
    frozen_snapshot_live_partition
      (advance_frozen_caller_snapshots CT h active snapshots) stack
      new_snapshot boundary above below ->
    exists old_snapshot,
      frozen_snapshot_live_partition snapshots stack old_snapshot boundary
        above below.
Proof.
  intros CT h active snapshots. induction snapshots as [|slot tail IH];
    intros stack new_snapshot boundary above below Hpartition.
  - inversion Hpartition.
  - destruct stack as [|top stack]; [inversion Hpartition|].
    unfold advance_frozen_caller_snapshots in Hpartition. simpl in Hpartition.
    destruct slot as [old_head|].
    + inversion Hpartition; subst.
      * exists old_head. constructor.
      * destruct (IH stack new_snapshot boundary above0 below H7) as
          [old_snapshot Hold].
        exists old_snapshot. constructor. exact Hold.
    + inversion Hpartition; subst.
      destruct (IH stack new_snapshot boundary above0 below H7) as
        [old_snapshot Hold].
      exists old_snapshot. constructor. exact Hold.
Qed.

(** Each tracked boundary summarizes all older tracked provenance below it.
    The relation is deliberately stated only over proof-local color images;
    it does not constrain programs or dispatch.  Dropping the head at pop
    preserves the tail relation definitionally. *)
Fixpoint frozen_caller_snapshots_nested_covered
  (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  match snapshots with
  | [] => True
  | None :: tail => frozen_caller_snapshots_nested_covered tail
  | Some head :: tail =>
      (forall older,
        List.In (Some older) tail ->
        Included authority_flow_state
          older.(frozen_snapshot_current_colors)
          head.(frozen_snapshot_current_colors)) /\
      frozen_caller_snapshots_nested_covered tail
  end.

(** Cross-boundary continuation certificate.  If a newer frozen phase has a
    dangerous color at a root that will resume in an older caller, then the
    older caller's entire potential RDM-join exposure is classified exactly
    as in its own pop rule: either that source was already present at the
    older entry, or every exposed target avoids the protected zone.  This is
    the conditional obligation that plain set inclusion cannot express. *)
Definition frozen_snapshot_resume_safe_against
  (Z : Ensemble Loc) (newer older : frozen_caller_color_snapshot) : Prop :=
  forall source_mode source,
    authority_mode_dangerous source_mode ->
    In authority_flow_state newer.(frozen_snapshot_current_colors)
      (source_mode, source) ->
    In Loc older.(frozen_snapshot_resume_rdm_roots) source ->
    (exists entry_mode,
      authority_mode_dangerous entry_mode /\
      In authority_flow_state older.(frozen_snapshot_entry_colors)
        (entry_mode, source)) \/
    (forall exposure_mode target,
      authority_mode_dangerous exposure_mode ->
      In authority_flow_state
        older.(frozen_snapshot_current_resume_exposure)
        (exposure_mode, target) ->
      ~ In Loc Z target).

Fixpoint frozen_caller_snapshots_nested_resume_safe
  (Z : Ensemble Loc) (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  match snapshots with
  | [] => True
  | None :: tail => frozen_caller_snapshots_nested_resume_safe Z tail
  | Some head :: tail =>
      (forall older,
        List.In (Some older) tail ->
        frozen_snapshot_resume_safe_against Z head older) /\
      frozen_caller_snapshots_nested_resume_safe Z tail
  end.

(** A newer suspended caller's latent resume exposure cannot coincide with
    a root captured for an older caller.  This is an age/provenance fact, not
    a semantic precondition: tracked call entry establishes it from the
    prospective-component cutoff invariant, and statement preservation
    transports it as private ghost state. *)
Definition frozen_snapshot_resume_exposure_disjoint_from
  (newer older : frozen_caller_color_snapshot) : Prop :=
  forall mode location,
    In authority_flow_state
      newer.(frozen_snapshot_current_resume_exposure) (mode, location) ->
    In Loc older.(frozen_snapshot_resume_rdm_roots) location ->
    False.

Fixpoint frozen_caller_snapshots_newer_resume_exposure_disjoint
  (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  match snapshots with
  | [] => True
  | None :: tail =>
      frozen_caller_snapshots_newer_resume_exposure_disjoint tail
  | Some head :: tail =>
      (forall older,
        List.In (Some older) tail ->
        frozen_snapshot_resume_exposure_disjoint_from head older) /\
      frozen_caller_snapshots_newer_resume_exposure_disjoint tail
  end.

(** Boundary-facing certificate for the phase that is executing now.  This
    differs from independent active authority: [completed] also contains
    inherited incoming colors.  It is maintained only by the private
    statement induction and is consumed when a tracked nested head freezes
    the immediate caller's completed colors. *)
Definition frozen_completed_colors_resume_safe
  (Z : Ensemble Loc) (completed : Ensemble authority_flow_state)
  (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  forall snapshot source_mode source,
    List.In (Some snapshot) snapshots ->
    authority_mode_dangerous source_mode ->
    In authority_flow_state completed (source_mode, source) ->
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
      ~ In Loc Z target).

Lemma repeat_none_completed_colors_resume_safe :
  forall Z completed count,
    frozen_completed_colors_resume_safe Z completed
      (repeat (None : frozen_caller_snapshot_slot) count).
Proof.
  intros Z completed count snapshot mode source Hsnapshot.
  apply repeat_spec in Hsnapshot. discriminate.
Qed.

Lemma repeat_none_snapshots_nested_resume_safe :
  forall Z count,
    frozen_caller_snapshots_nested_resume_safe Z
      (repeat (None : frozen_caller_snapshot_slot) count).
Proof.
  intros Z count. induction count; simpl; auto.
Qed.

Lemma frozen_caller_snapshot_closure_monotone :
  forall CT h active smaller larger,
    Included authority_flow_state smaller larger ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h active smaller)
      (frozen_caller_authority_closure CT h active larger).
Proof.
  intros CT h active smaller larger Hincluded state
    [seed [Hseed Hpath]].
  exists seed. split; [apply Hincluded; exact Hseed|exact Hpath].
Qed.

Lemma advance_frozen_caller_snapshots_nested_covered :
  forall CT h active snapshots,
    frozen_caller_snapshots_nested_covered snapshots ->
    frozen_caller_snapshots_nested_covered
      (advance_frozen_caller_snapshots CT h active snapshots).
Proof.
  intros CT h active snapshots. induction snapshots as [|slot tail IH];
    intros Hcovered; simpl in *; [exact I|].
  destruct slot as [head|].
  - destruct Hcovered as [Hhead Htail]. split.
    + intros older Holder.
      unfold advance_frozen_caller_snapshots in Holder. simpl in Holder.
      apply in_map_iff in Holder.
      destruct Holder as [old_slot [Heq Hold]].
      destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
      injection Heq as Heq. subst older. simpl.
      apply frozen_caller_snapshot_closure_monotone.
      eapply Hhead. exact Hold.
    + exact (IH Htail).
  - exact (IH Hcovered).
Qed.

(** Static age certificate paired with each suspended boundary.  It records
    that both the completed caller colors and every captured caller RDM root
    existed before the corresponding call began.  This is proof-only
    metadata used to separate a body-local fresh return component from old
    caller roots. *)
Definition frozen_snapshot_slot_before_boundary
  (slot : frozen_caller_snapshot_slot) (boundary : watched_boundary) : Prop :=
  match slot with
  | None => True
  | Some snapshot =>
      (forall mode location,
        In authority_flow_state snapshot.(frozen_snapshot_entry_phase)
          (mode, location) ->
        location < boundary.(boundary_entry_cutoff)) /\
      (forall root,
        In Loc snapshot.(frozen_snapshot_resume_rdm_roots) root ->
        root < boundary.(boundary_entry_cutoff))
  end.

Definition frozen_caller_snapshots_before_boundaries
  (snapshots : list frozen_caller_snapshot_slot)
  (stack : list watched_boundary) : Prop :=
  Forall2 frozen_snapshot_slot_before_boundary snapshots stack.

(** Every tracked boundary was created during the current public history
    interval.  Pre-existing operational boundaries carry [None], so this
    certificate is vacuous at public entry. *)
Definition frozen_snapshot_slot_boundary_after_cutoff
  (cutoff : Loc) (slot : frozen_caller_snapshot_slot)
  (boundary : watched_boundary) : Prop :=
  match slot with
  | None => True
  | Some _ => cutoff <= boundary.(boundary_entry_cutoff)
  end.

Definition frozen_snapshot_boundaries_after_cutoff
  (cutoff : Loc) (snapshots : list frozen_caller_snapshot_slot)
  (stack : list watched_boundary) : Prop :=
  Forall2 (frozen_snapshot_slot_boundary_after_cutoff cutoff) snapshots stack.

Lemma frozen_snapshot_partition_boundary_after_cutoff :
  forall cutoff snapshots stack snapshot boundary above below,
    frozen_snapshot_boundaries_after_cutoff cutoff snapshots stack ->
    frozen_snapshot_live_partition snapshots stack snapshot boundary above
      below ->
    cutoff <= boundary.(boundary_entry_cutoff).
Proof.
  intros cutoff snapshots stack snapshot boundary above below Hafter
    Hpartition.
  induction Hpartition.
  - inversion Hafter; subst. exact H2.
  - inversion Hafter; subst. eapply IHHpartition. exact H4.
Qed.

(** The same age argument does not depend on the immediate call being
    tracked.  In particular, an untracked call contributes a [None] slot,
    while every older snapshot still lies strictly below that slot. *)
Lemma head_slot_prospective_component_avoids_older_protected :
  forall CT h Z cutoff active slot snapshots boundary stack older root target,
    length (slot :: snapshots) = length (boundary :: stack) ->
    frozen_callee_side_prospective_components_after_boundaries CT h active
      (slot :: snapshots) (boundary :: stack) ->
    frozen_snapshot_boundaries_after_cutoff cutoff
      (slot :: snapshots) (boundary :: stack) ->
    protected_zone_before_cutoff Z cutoff ->
    List.In (Some older) snapshots ->
    prospective_mutable_authority_reachable CT h
      boundary.(boundary_caller) root target ->
    ~ In Loc Z target.
Proof.
  intros CT h Z cutoff active slot snapshots boundary stack older root target
    Haligned Hcomponents Hafter Hzone Hold Hreachable Hprotected.
  destruct (frozen_snapshot_in_tail_has_partition_below_slot slot snapshots
    boundary stack older Haligned Hold) as
    [older_boundary [above [below Hpartition]]].
  have Hcomponent_fresh : older_boundary.(boundary_entry_cutoff) <= target.
  { eapply Hcomponents with (snapshot := older)
      (above := boundary :: above) (below := below) (root := root).
    - exact Hpartition.
    - apply live_frame_suspended with (boundary := boundary). simpl. auto.
    - exact Hreachable. }
  have Hboundary_after : cutoff <= older_boundary.(boundary_entry_cutoff).
  { eapply frozen_snapshot_partition_boundary_after_cutoff; eauto. }
  have Hprotected_before := Hzone target Hprotected. lia.
Qed.

Lemma advance_frozen_caller_snapshots_before_boundaries :
  forall CT h active snapshots stack,
    frozen_caller_snapshots_before_boundaries snapshots stack ->
    frozen_caller_snapshots_before_boundaries
      (advance_frozen_caller_snapshots CT h active snapshots) stack.
Proof.
  intros CT h active snapshots stack Hbefore.
  induction Hbefore; constructor; [|exact IHHbefore].
  destruct x as [snapshot|]; simpl in *; [|exact I].
  destruct H as [Hcolors Hroots]. split; simpl.
  - exact Hcolors.
  - exact Hroots.
Qed.

(** There is exactly one proof slot per operational boundary.  A [None] slot
    denotes a pre-existing or untracked call.  Exact alignment makes pop
    compositional: it always removes the head slot, without guessing whether
    the top call was tracked. *)
Definition frozen_caller_snapshots_aligned
  (snapshots : list frozen_caller_snapshot_slot)
  (stack : list watched_boundary) : Prop :=
  length snapshots = length stack.

Definition frozen_caller_snapshots_runtime_mutable
  (h : heap) (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  forall snapshot,
    List.In (Some snapshot) snapshots ->
    authority_colors_runtime_mutable h
      snapshot.(frozen_snapshot_current_colors).

Definition frozen_caller_snapshots_closed
  (CT : class_table) (h : heap) (active : watched_frame)
  (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  forall snapshot,
    List.In (Some snapshot) snapshots ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h active
        snapshot.(frozen_snapshot_current_colors))
      snapshot.(frozen_snapshot_current_colors).

Definition frozen_caller_snapshots_retain_entry
  (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  forall snapshot,
    List.In (Some snapshot) snapshots ->
    Included authority_flow_state
      snapshot.(frozen_snapshot_entry_colors)
      snapshot.(frozen_snapshot_current_colors).

Definition frozen_caller_snapshots_dangerous
  (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  forall snapshot mode location,
    List.In (Some snapshot) snapshots ->
    In authority_flow_state
      snapshot.(frozen_snapshot_current_colors) (mode, location) ->
    authority_mode_dangerous mode.

Definition independent_active_authority_colors
  (CT : class_table) (h : heap) (active : watched_frame) :
  Ensemble authority_flow_state :=
  executing_authority_color_set CT h active
    (Empty_set authority_flow_state).

Lemma independent_active_authority_colors_in_executing :
  forall CT h active incoming,
    Included authority_flow_state
      (independent_active_authority_colors CT h active)
      (executing_authority_color_set CT h active incoming).
Proof.
  intros CT h active incoming state [seed [Hseed Hpath]].
  exists seed. split; [|exact Hpath].
  inversion Hseed; subst.
  - inversion H.
  - right. exact H.
Qed.

Lemma independent_active_authority_colors_frozen_closed :
  forall CT h active,
    Included authority_flow_state
      (frozen_caller_authority_closure CT h active
        (independent_active_authority_colors CT h active))
      (independent_active_authority_colors CT h active).
Proof.
  intros CT h active state [middle [Hmiddle Hpath]].
  destruct Hmiddle as [seed [Hseed Hprefix]].
  exists seed. split; [exact Hseed|].
  eapply rt_trans; [exact Hprefix|].
  eapply frozen_caller_authority_connected_is_phased. exact Hpath.
Qed.

(** Allocation-stable replacement for global frozen/active disjointness.
    If a frozen caller color is also independently exercisable by the active
    frame, it is enough to remember one captured caller RDM root that
    justifies that color.  The root-scoped resume certificate decides at pop
    whether the caller-entry case was already closed, or whether every
    exposed target avoids the protected zone. *)
Definition frozen_caller_snapshots_active_resume_origins
  (CT : class_table) (h : heap) (active : watched_frame)
  (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  forall snapshot snapshot_mode active_mode location,
    List.In (Some snapshot) snapshots ->
    authority_mode_dangerous snapshot_mode ->
    authority_mode_dangerous active_mode ->
    In authority_flow_state snapshot.(frozen_snapshot_current_colors)
      (snapshot_mode, location) ->
    (In authority_flow_state
       (independent_active_authority_colors CT h active)
       (active_mode, location) \/
     typed_root RDM active.(frame_senv) active.(frame_renv) location) ->
    exists root_mode root,
      authority_mode_dangerous root_mode /\
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (root_mode, root) /\
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) root.

Definition frozen_snapshot_resume_exposure_avoids
  (Z : Ensemble Loc) (snapshot : frozen_caller_color_snapshot) : Prop :=
  forall exposure_mode target,
    authority_mode_dangerous exposure_mode ->
    In authority_flow_state
      snapshot.(frozen_snapshot_current_resume_exposure)
      (exposure_mode, target) ->
    ~ In Loc Z target.

Definition frozen_target_colors_resume_phase_safe
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (colors : Ensemble authority_flow_state)
  (targets : list frozen_caller_snapshot_slot) : Prop :=
  forall target source_mode source,
    List.In (Some target) targets ->
    authority_mode_dangerous source_mode ->
    In authority_flow_state colors (source_mode, source) ->
    In Loc target.(frozen_snapshot_resume_rdm_roots) source ->
    (exists phase_mode,
      authority_mode_dangerous phase_mode /\
      In authority_flow_state target.(frozen_snapshot_phase_incoming)
        (phase_mode, source)) \/
    frozen_snapshot_resume_exposure_avoids Z target.

(** A saved resume exposure can become authority either from mutable
    class-bounded authority or from inherited phase authority already
    present at one of the suspended frame's RDM roots. *)
Definition frozen_snapshot_resume_activated
  (snapshot : frozen_caller_color_snapshot) : Prop :=
  snapshot.(frozen_snapshot_resume_authority) = Mut_r \/
  exists mode root,
    authority_mode_dangerous mode /\
    In authority_flow_state snapshot.(frozen_snapshot_phase_incoming)
      (mode, root) /\
    In Loc snapshot.(frozen_snapshot_resume_rdm_roots) root.

(** Inductive form of the overlap certificate.  A captured resume root is
    retained when one exists.  If a fresh return-time caller join creates an
    overlap for an older snapshot, the alternative records the exact fact
    needed by the later pop: every target exposed when that snapshot's caller
    resumes is already outside the protected zone. *)
Definition frozen_caller_snapshots_active_resume_justified
  (CT : class_table) (h : heap) (Z : Ensemble Loc) (active : watched_frame)
  (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  forall snapshot snapshot_mode active_mode location,
    List.In (Some snapshot) snapshots ->
    authority_mode_dangerous snapshot_mode ->
    authority_mode_dangerous active_mode ->
    In authority_flow_state snapshot.(frozen_snapshot_current_colors)
      (snapshot_mode, location) ->
    In Loc snapshot.(frozen_snapshot_resume_rdm_roots) location ->
    (In authority_flow_state
       (independent_active_authority_colors CT h active)
       (active_mode, location) \/
     typed_root RDM active.(frame_senv) active.(frame_renv) location) ->
    (exists root_mode root,
      authority_mode_dangerous root_mode /\
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (root_mode, root) /\
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) root) \/
    frozen_snapshot_resume_exposure_avoids Z snapshot.

Lemma frozen_active_resume_origins_imply_justified :
  forall CT h Z active snapshots,
    frozen_caller_snapshots_active_resume_origins CT h active snapshots ->
    frozen_caller_snapshots_active_resume_justified CT h Z active snapshots.
Proof.
  intros CT h Z active snapshots Horigins snapshot snapshot_mode active_mode
    location Hsnapshot Hsnapshot_mode Hactive_mode Hcolor Hroot Htrigger.
  left.
  exact (Horigins snapshot snapshot_mode active_mode location Hsnapshot
    Hsnapshot_mode Hactive_mode Hcolor Htrigger).
Qed.

(** The persistent safety fact carried by a frozen snapshot.  Caller and
    callee provenance may legitimately overlap at fresh locations; the
    theorem needs only that no dangerous frozen color reaches the protected
    zone. *)
Definition frozen_caller_snapshots_avoid_protected
  (Z : Ensemble Loc) (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  forall snapshot mode location,
    List.In (Some snapshot) snapshots ->
    authority_mode_dangerous mode ->
    In authority_flow_state snapshot.(frozen_snapshot_current_colors)
      (mode, location) ->
    ~ In Loc Z location.

(** Every captured resume root denotes an object in the current heap.  This
    fact is established from the caller's well-formed runtime environment at
    call entry and is monotone under heap growth. *)
Definition frozen_caller_snapshots_resume_roots_in_heap
  (h : heap) (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  forall snapshot root,
    List.In (Some snapshot) snapshots ->
    In Loc snapshot.(frozen_snapshot_resume_rdm_roots) root ->
    root < dom h.

Definition frozen_caller_snapshots_resume_exposures_wf
  (CT : class_table) (h : heap) (active : watched_frame)
  (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  (forall snapshot,
    List.In (Some snapshot) snapshots ->
    authority_colors_runtime_mutable h
      snapshot.(frozen_snapshot_current_resume_exposure)) /\
  (forall snapshot,
    List.In (Some snapshot) snapshots ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h active
        snapshot.(frozen_snapshot_current_resume_exposure))
      snapshot.(frozen_snapshot_current_resume_exposure)) /\
  (forall snapshot mode location,
    List.In (Some snapshot) snapshots ->
    In authority_flow_state
      snapshot.(frozen_snapshot_current_resume_exposure) (mode, location) ->
    authority_mode_dangerous mode) /\
  (forall snapshot,
    List.In (Some snapshot) snapshots ->
    Included authority_flow_state
      snapshot.(frozen_snapshot_entry_resume_exposure)
      snapshot.(frozen_snapshot_current_resume_exposure)) /\
  (forall snapshot root,
    List.In (Some snapshot) snapshots ->
    In Loc snapshot.(frozen_snapshot_resume_rdm_roots) root ->
    r_muttype h root = Some Mut_r ->
    In authority_flow_state
      snapshot.(frozen_snapshot_current_resume_exposure)
      (FlowProspective, root)).

(** Pop-sensitive provenance is required only when independent callee
    authority reaches an RDM root whose caller frame will resume.  The target
    condition ranges over the frozen prospective exposure of all resume
    roots, rather than just the roots themselves: after the pop-time join,
    authority may continue through retained mutable descendants. *)
Definition frozen_caller_snapshots_resume_roots_safe
  (CT : class_table) (h : heap) (Z : Ensemble Loc) (active : watched_frame)
  (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  forall snapshot active_mode source exposure_mode target,
    List.In (Some snapshot) snapshots ->
    authority_mode_dangerous active_mode ->
    In authority_flow_state
      (independent_active_authority_colors CT h active)
      (active_mode, source) ->
    In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
    authority_mode_dangerous exposure_mode ->
    In authority_flow_state
      snapshot.(frozen_snapshot_current_resume_exposure)
      (exposure_mode, target) ->
    ~ In Loc Z target.

(** Phase-stable pop certificate.  A frozen dangerous color that reaches a
    suspended caller's RDM root is either already present in that caller's
    entry colors, or every authority target exposed by resuming the caller is
    known to avoid the protected zone. *)
Definition frozen_caller_snapshots_resume_joins_safe
  (Z : Ensemble Loc) (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  forall snapshot source_mode source,
    List.In (Some snapshot) snapshots ->
    authority_mode_dangerous source_mode ->
    In authority_flow_state snapshot.(frozen_snapshot_current_colors)
      (source_mode, source) ->
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
      ~ In Loc Z target).

(** Root-scoped active-resume justification is derived, not assumed.  At a
    captured resume root, [resume_joins_safe] either supplies a caller-entry
    color, which [retain_entry] keeps in the current snapshot, or supplies
    exactly the protected-zone avoidance alternative required at pop. *)
Lemma frozen_resume_joins_and_retain_imply_active_resume_justified :
  forall CT h Z active snapshots,
    frozen_caller_snapshots_retain_entry snapshots ->
    frozen_caller_snapshots_resume_joins_safe Z snapshots ->
    frozen_caller_snapshots_active_resume_justified CT h Z active snapshots.
Proof.
  intros CT h Z active snapshots Hretain Hjoins snapshot snapshot_mode
    active_mode location Hsnapshot Hsnapshot_mode Hactive_mode Hcolor Hroot
    Htrigger.
  destruct (Hjoins snapshot snapshot_mode location Hsnapshot Hsnapshot_mode
    Hcolor Hroot) as [[entry_mode [Hentry_mode Hentry]] | Hsafe].
  - left. exists entry_mode, location. repeat split; try assumption.
    eapply Hretain; eauto.
  - right. exact Hsafe.
Qed.

(** Lockstep for the entry-derived branch of the pop certificate.  Once a
    dangerous caller-entry color reaches a captured RDM root, every color
    that resuming that caller could expose is already represented in the
    snapshot's current colors.  Both current sets are subsequently advanced
    through exactly the same active phases. *)
Definition frozen_caller_snapshots_entry_exposure_covered
  (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  forall snapshot source_mode source,
    List.In (Some snapshot) snapshots ->
    authority_mode_dangerous source_mode ->
    In authority_flow_state snapshot.(frozen_snapshot_entry_colors)
      (source_mode, source) ->
    In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
    Included authority_flow_state
      snapshot.(frozen_snapshot_current_resume_exposure)
      snapshot.(frozen_snapshot_current_colors).

(** The completed caller colors installed as the callee's incoming set are
    immutable snapshot metadata.  Their dangerous part remains represented
    in the phase-current frozen colors throughout the callee execution. *)
Definition frozen_caller_snapshots_cover_phase_incoming
  (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  forall snapshot mode location,
    List.In (Some snapshot) snapshots ->
    authority_mode_dangerous mode ->
    In authority_flow_state snapshot.(frozen_snapshot_phase_incoming)
      (mode, location) ->
    In authority_flow_state snapshot.(frozen_snapshot_current_colors)
      (mode, location).

Definition principled_frozen_authority_history_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary)
  (incoming : Ensemble authority_flow_state)
  (snapshots : list frozen_caller_snapshot_slot) (h : heap) : Prop :=
  principled_phased_authority_live_history_state CT P Z cutoff
    active stack incoming h /\
  frozen_caller_snapshots_aligned snapshots stack /\
  frozen_caller_snapshots_runtime_mutable h snapshots /\
  frozen_caller_snapshots_closed CT h active snapshots /\
  frozen_caller_snapshots_retain_entry snapshots /\
  frozen_caller_snapshots_dangerous snapshots /\
  frozen_caller_snapshots_avoid_protected Z snapshots /\
  frozen_caller_snapshots_resume_roots_in_heap h snapshots /\
  frozen_caller_snapshots_resume_exposures_wf CT h active snapshots /\
  frozen_caller_snapshots_resume_roots_safe CT h Z active snapshots /\
  frozen_caller_snapshots_resume_joins_safe Z snapshots /\
  frozen_caller_snapshots_entry_exposure_covered snapshots /\
  frozen_caller_snapshots_cover_phase_incoming snapshots.

Lemma nested_frozen_call_head_color_reflects_at_channel_free_entry :
  forall CT h boundary caller_colors snapshots state,
    let caller := boundary.(boundary_caller) in
    let callee := mk_watched_frame
      (call_authority caller.(frame_authority)
        boundary.(boundary_receiver_view))
      boundary.(boundary_callee_entry_senv)
      boundary.(boundary_callee_entry_renv) in
    entry_ownership_channel_free boundary ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h caller caller_colors)
      caller_colors ->
    frozen_caller_snapshots_closed CT h caller snapshots ->
    In authority_flow_state
      (nested_frozen_call_head CT h caller callee caller_colors snapshots)
        .(frozen_snapshot_current_colors) state ->
    In authority_flow_state caller_colors state \/
    exists snapshot,
      List.In (Some snapshot) snapshots /\
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        state.
Proof.
  intros CT h boundary caller_colors snapshots state caller callee Hfree
    Hcaller_closed Hsnapshots_closed Hstate.
  unfold nested_frozen_call_head in Hstate. simpl in Hstate.
  destruct Hstate as [seed [Hseed Hpath]].
  have Hcaller_path : frozen_caller_authority_connected CT h caller seed state.
  { unfold callee in Hpath.
    eapply channel_free_entry_frozen_connected_reflects; eauto. }
  inversion Hseed; subst.
  - left. eapply Hcaller_closed. exists seed. split.
    + exact (proj1 H).
    + exact Hcaller_path.
  - right. destruct H as [snapshot [Hsnapshot Hcolor]].
    exists snapshot. split; [exact Hsnapshot|].
    eapply Hsnapshots_closed; [exact Hsnapshot|].
    exists seed. split; [exact Hcolor|exact Hcaller_path].
Qed.

Lemma frozen_caller_snapshots_none_runtime_mutable :
  forall h count,
    frozen_caller_snapshots_runtime_mutable h (repeat None count).
Proof.
  intros h count snapshot Hsnapshot.
  apply repeat_spec in Hsnapshot. discriminate.
Qed.

Lemma frozen_caller_snapshots_none_closed :
  forall CT h active count,
    frozen_caller_snapshots_closed CT h active (repeat None count).
Proof.
  intros CT h active count snapshot Hsnapshot.
  apply repeat_spec in Hsnapshot. discriminate.
Qed.

Lemma frozen_caller_snapshots_none_retain_entry :
  forall count,
    frozen_caller_snapshots_retain_entry (repeat None count).
Proof.
  intros count snapshot Hsnapshot.
  apply repeat_spec in Hsnapshot. discriminate.
Qed.

Lemma frozen_caller_snapshots_none_dangerous :
  forall count,
    frozen_caller_snapshots_dangerous (repeat None count).
Proof.
  intros count snapshot mode location Hsnapshot.
  apply repeat_spec in Hsnapshot. discriminate.
Qed.

Lemma frozen_caller_snapshots_none_avoid_protected :
  forall Z count,
    frozen_caller_snapshots_avoid_protected Z (repeat None count).
Proof.
  intros Z count snapshot mode location Hsnapshot.
  apply repeat_spec in Hsnapshot. discriminate.
Qed.

Lemma frozen_caller_snapshots_none_resume_roots_safe :
  forall CT h Z active count,
    frozen_caller_snapshots_resume_roots_safe CT h Z active
      (repeat None count).
Proof.
  intros CT h Z active count snapshot mode source exposure_mode target
    Hsnapshot.
  apply repeat_spec in Hsnapshot. discriminate.
Qed.

Lemma frozen_caller_snapshots_none_resume_roots_in_heap :
  forall h count,
    frozen_caller_snapshots_resume_roots_in_heap h (repeat None count).
Proof.
  intros h count snapshot root Hsnapshot.
  apply repeat_spec in Hsnapshot. discriminate.
Qed.

Lemma frozen_caller_snapshots_none_resume_joins_safe :
  forall Z count,
    frozen_caller_snapshots_resume_joins_safe Z (repeat None count).
Proof.
  intros Z count snapshot mode source Hsnapshot.
  apply repeat_spec in Hsnapshot. discriminate.
Qed.

Lemma frozen_caller_snapshots_none_entry_exposure_covered :
  forall count,
    frozen_caller_snapshots_entry_exposure_covered (repeat None count).
Proof.
  intros count snapshot mode source Hsnapshot.
  apply repeat_spec in Hsnapshot. discriminate.
Qed.

Lemma frozen_caller_snapshots_none_cover_phase_incoming :
  forall count,
    frozen_caller_snapshots_cover_phase_incoming (repeat None count).
Proof.
  intros count snapshot mode location Hsnapshot.
  apply repeat_spec in Hsnapshot. discriminate.
Qed.

Lemma frozen_caller_snapshots_none_resume_exposures_wf :
  forall CT h active count,
    frozen_caller_snapshots_resume_exposures_wf CT h active
      (repeat None count).
Proof.
  intros CT h active count. repeat split; intros snapshot; intros.
  - apply repeat_spec in H. discriminate.
  - apply repeat_spec in H. discriminate.
  - apply repeat_spec in H. discriminate.
  - apply repeat_spec in H. discriminate.
  - apply repeat_spec in H. discriminate.
Qed.

Lemma frozen_caller_authority_step_preserves_dangerous :
  forall CT h frame source target,
    authority_mode_dangerous (fst source) ->
    frozen_caller_authority_step CT h frame source target ->
    authority_mode_dangerous (fst target).
Proof.
  intros CT h frame source target Hsource Hstep.
  inversion Hstep; subst; simpl.
  - left. reflexivity.
  - right. reflexivity.
  - right. reflexivity.
  - right. reflexivity.
  - right. reflexivity.
  - right. reflexivity.
  - right. reflexivity.
Qed.

Lemma frozen_caller_authority_connected_preserves_dangerous :
  forall CT h frame source target,
    authority_mode_dangerous (fst source) ->
    frozen_caller_authority_connected CT h frame source target ->
    authority_mode_dangerous (fst target).
Proof.
  intros CT h frame source target Hsource Hconnected.
  induction Hconnected.
  - eapply frozen_caller_authority_step_preserves_dangerous; eauto.
  - exact Hsource.
  - apply IHHconnected2. apply IHHconnected1. exact Hsource.
Qed.

Lemma dangerous_rdm_root_color_covers_frame_resume_exposure :
  forall CT h frame colors mode source,
    Included authority_flow_state
      (frozen_caller_authority_closure CT h frame colors) colors ->
    authority_mode_dangerous mode ->
    In authority_flow_state colors (mode, source) ->
    In Loc (frame_rdm_root_set frame) source ->
    Included authority_flow_state
      (frame_resume_exposure_colors CT h frame) colors.
Proof.
  intros CT h frame colors mode source Hclosed Hmode Hsource
    Hsource_root target [seed [Hseed Hpath]].
  destruct Hseed as [root [Hroot [Hruntime Heq]]].
  subst seed.
  apply Hclosed. exists (mode, source). split; [exact Hsource|].
  eapply rt_trans.
  - destruct Hmode as [-> | ->].
    + eapply rt_trans.
      * apply rt_step. apply frozen_caller_mark_prospective.
      * apply rt_step. eapply frozen_caller_prospective_frame_join; eauto.
    + apply rt_step. eapply frozen_caller_prospective_frame_join; eauto.
  - exact Hpath.
Qed.

Lemma frozen_caller_authority_closure_monotone :
  forall CT h frame left right,
    Included authority_flow_state left right ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h frame left)
      (frozen_caller_authority_closure CT h frame right).
Proof.
  intros CT h frame left right Hincluded state [seed [Hseed Hpath]].
  exists seed. split; [eapply Hincluded; exact Hseed|exact Hpath].
Qed.

Lemma advance_frozen_caller_snapshots_entry_exposure_covered :
  forall CT h active snapshots,
    frozen_caller_snapshots_entry_exposure_covered snapshots ->
    frozen_caller_snapshots_entry_exposure_covered
      (advance_frozen_caller_snapshots CT h active snapshots).
Proof.
  intros CT h active snapshots Hcovered snapshot source_mode source
    Hsnapshot Hsource_mode Hentry Hroot.
  unfold advance_frozen_caller_snapshots in Hsnapshot.
  apply in_map_iff in Hsnapshot.
  destruct Hsnapshot as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst snapshot. simpl in *.
  apply frozen_caller_authority_closure_monotone.
  eapply Hcovered; eauto.
Qed.

Lemma advance_frozen_caller_snapshots_cover_phase_incoming :
  forall CT h active snapshots,
    frozen_caller_snapshots_cover_phase_incoming snapshots ->
    frozen_caller_snapshots_cover_phase_incoming
      (advance_frozen_caller_snapshots CT h active snapshots).
Proof.
  intros CT h active snapshots Hcovered snapshot mode location Hsnapshot
    Hmode Hincoming.
  unfold advance_frozen_caller_snapshots in Hsnapshot.
  apply in_map_iff in Hsnapshot.
  destruct Hsnapshot as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst snapshot. simpl in *.
  apply frozen_caller_authority_closure_contains.
  eapply Hcovered; eauto.
Qed.

Lemma advance_frozen_caller_snapshot_dangerous :
  forall CT h active snapshot,
    (forall mode location,
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (mode, location) ->
      authority_mode_dangerous mode) ->
    forall mode location,
      In authority_flow_state
        (advance_frozen_caller_snapshot CT h active snapshot)
          .(frozen_snapshot_current_colors) (mode, location) ->
      authority_mode_dangerous mode.
Proof.
  intros CT h active snapshot Hdangerous mode location
    [seed [Hseed Hpath]].
  destruct seed as [seed_mode seed_location].
  have Hresult := frozen_caller_authority_connected_preserves_dangerous CT h
    active (seed_mode, seed_location) (mode, location)
    (Hdangerous seed_mode seed_location Hseed) Hpath.
  exact Hresult.
Qed.

Lemma advance_frozen_caller_snapshots_dangerous :
  forall CT h active snapshots,
    frozen_caller_snapshots_dangerous snapshots ->
    frozen_caller_snapshots_dangerous
      (advance_frozen_caller_snapshots CT h active snapshots).
Proof.
  intros CT h active snapshots Hdangerous snapshot mode location Hsnapshot
    Hcolor.
  unfold advance_frozen_caller_snapshots in Hsnapshot.
  apply in_map_iff in Hsnapshot.
  destruct Hsnapshot as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst snapshot.
  eapply advance_frozen_caller_snapshot_dangerous; [|exact Hcolor].
  intros old_mode old_location Hold_color.
  eapply Hdangerous; eauto.
Qed.

Lemma advance_frozen_caller_snapshot_closed :
  forall CT h active snapshot,
    Included authority_flow_state
      (frozen_caller_authority_closure CT h active
        (advance_frozen_caller_snapshot CT h active snapshot)
          .(frozen_snapshot_current_colors))
      (advance_frozen_caller_snapshot CT h active snapshot)
        .(frozen_snapshot_current_colors).
Proof.
  intros CT h active snapshot.
  unfold advance_frozen_caller_snapshot. simpl.
  exact (proj1
    (frozen_caller_authority_closure_idempotent CT h active
      snapshot.(frozen_snapshot_current_colors))).
Qed.

Lemma advance_frozen_caller_snapshot_retains_entry :
  forall CT h active snapshot,
    Included authority_flow_state
      snapshot.(frozen_snapshot_entry_colors)
      snapshot.(frozen_snapshot_current_colors) ->
    Included authority_flow_state
      (advance_frozen_caller_snapshot CT h active snapshot)
        .(frozen_snapshot_entry_colors)
      (advance_frozen_caller_snapshot CT h active snapshot)
        .(frozen_snapshot_current_colors).
Proof.
  intros CT h active snapshot Hretained state Hstate.
  unfold advance_frozen_caller_snapshot. simpl in *.
  eapply frozen_caller_authority_closure_contains.
  eapply Hretained. exact Hstate.
Qed.

Lemma advance_frozen_caller_snapshots_closed :
  forall CT h active snapshots,
    frozen_caller_snapshots_closed CT h active
      (advance_frozen_caller_snapshots CT h active snapshots).
Proof.
  intros CT h active snapshots snapshot Hsnapshot.
  unfold advance_frozen_caller_snapshots in Hsnapshot.
  apply in_map_iff in Hsnapshot.
  destruct Hsnapshot as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst snapshot.
  apply advance_frozen_caller_snapshot_closed.
Qed.

Lemma advance_frozen_caller_snapshots_retain_entry :
  forall CT h active snapshots,
    frozen_caller_snapshots_retain_entry snapshots ->
    frozen_caller_snapshots_retain_entry
      (advance_frozen_caller_snapshots CT h active snapshots).
Proof.
  intros CT h active snapshots Hretain snapshot Hsnapshot.
  unfold advance_frozen_caller_snapshots in Hsnapshot.
  apply in_map_iff in Hsnapshot.
  destruct Hsnapshot as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst snapshot.
  eapply advance_frozen_caller_snapshot_retains_entry.
  eapply Hretain. exact Hold.
Qed.

Lemma advance_frozen_caller_snapshot_runtime_mutable :
  forall CT h active snapshot,
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    authority_colors_runtime_mutable h snapshot ->
    authority_colors_runtime_mutable h
      (frozen_caller_authority_closure CT h active snapshot).
Proof.
  intros CT h active snapshot Hwf Hruntime mode location
    [seed [Hseed Hconnected]].
  destruct seed as [seed_mode seed_location].
  exact (phased_authority_frame_connected_preserves_runtime_mutability CT h
    active (seed_mode, seed_location) (mode, location) Mut_r Hwf
    (frozen_caller_authority_connected_is_phased CT h active
      (seed_mode, seed_location) (mode, location) Hconnected)
    (Hruntime seed_mode seed_location Hseed)).
Qed.

Lemma advance_frozen_caller_snapshots_runtime_mutable :
  forall CT h active snapshots,
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_runtime_mutable h
      (advance_frozen_caller_snapshots CT h active snapshots).
Proof.
  intros CT h active snapshots Hwf Hruntime snapshot Hsnapshot.
  unfold advance_frozen_caller_snapshots in Hsnapshot.
  apply in_map_iff in Hsnapshot.
  destruct Hsnapshot as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst snapshot.
  eapply advance_frozen_caller_snapshot_runtime_mutable; [exact Hwf|].
  eapply Hruntime. exact Hold.
Qed.

Lemma principled_phased_authority_starts_frozen :
  forall CT P Z cutoff active stack incoming h,
    principled_phased_authority_live_history_state CT P Z cutoff
      active stack incoming h ->
    principled_frozen_authority_history_state CT P Z cutoff
      active stack incoming (repeat None (length stack)) h.
Proof.
  intros CT P Z cutoff active stack incoming h Hstate.
  split; [exact Hstate|]. split.
  - unfold frozen_caller_snapshots_aligned. apply repeat_length.
  - split.
    + apply frozen_caller_snapshots_none_runtime_mutable.
    + split.
      * apply frozen_caller_snapshots_none_closed.
      * split.
        -- apply frozen_caller_snapshots_none_retain_entry.
        -- split.
           ++ apply frozen_caller_snapshots_none_dangerous.
           ++ split.
              ** apply frozen_caller_snapshots_none_avoid_protected.
              ** split.
                 --- apply frozen_caller_snapshots_none_resume_roots_in_heap.
                 --- split.
                     +++ apply frozen_caller_snapshots_none_resume_exposures_wf.
                     +++ split.
                         *** apply frozen_caller_snapshots_none_resume_roots_safe.
                         *** split.
                             ---- apply frozen_caller_snapshots_none_resume_joins_safe.
                             ---- split.
                                  ++++ apply frozen_caller_snapshots_none_entry_exposure_covered.
                                  ++++ apply frozen_caller_snapshots_none_cover_phase_incoming.
Qed.

Lemma potential_live_history_starts_principled_phased_authority :
  forall CT P Z cutoff active stack h,
    potential_live_history_state CT P Z cutoff active stack h ->
    principled_phased_authority_live_history_state CT P Z cutoff
      active stack (Empty_set authority_flow_state) h.
Proof.
  intros CT P Z cutoff active stack h [Hlive [Hpotential Hcutoffs]].
  destruct Hlive as
    [Hauthority [Hframes [Hsound [Hcutoff [Hzone Hchain]]]]].
  destruct Hauthority as [Hdirected [Hroots [Hactive_sound Hcomponents]]].
  destruct Hdirected as
    [Hcontains [Hzone_env [Hconfined [Hclosed [Hruntime
      [Hmut_roots Havoid]]]]]].
  refine (conj Hcontains (conj Hconfined (conj _ (conj _
    (conj Hframes (conj Hsound (conj Hcutoff
      (conj Hzone (conj Hchain Hcutoffs))))))))).
  - intros mode location Hempty. inversion Hempty.
  - intros mode protected Hmode Hcolor Hprotected.
    destruct Hcolor as [seed [Hseed Hpath]].
    inversion Hseed; subst.
    + inversion H.
    + destruct H as [root [Heq Howned]]. inversion Heq; subst.
      apply (Hpotential root protected).
      * apply frame_owned_location_iff_active_live in Howned.
        destruct Howned as
          [capability_root [[Hactive | [boundary [Hin _]]] Hreachable]].
        -- exists capability_root. split; [left; exact Hactive|].
           exact Hreachable.
        -- inversion Hin.
      * exact Hprotected.
      * exact (phased_authority_frame_connected_projects_to_potential CT h
          active stack (FlowPowered, root) (mode, protected) Hpath).
Qed.

Lemma potential_live_history_starts_principled_frozen_authority :
  forall CT P Z cutoff active stack h,
    potential_live_history_state CT P Z cutoff active stack h ->
    principled_frozen_authority_history_state CT P Z cutoff active stack
      (Empty_set authority_flow_state) (repeat None (length stack)) h.
Proof.
  intros CT P Z cutoff active stack h Hstate.
  apply principled_phased_authority_starts_frozen.
  apply potential_live_history_starts_principled_phased_authority.
  exact Hstate.
Qed.

(** Explicit-witness form used by the private statement induction.  Keeping
    [incoming] and [snapshots] visible internally is essential at nested call
    return: the induction preserves the incoming phase exactly and returns a
    metadata-equivalent snapshot list.  Both witnesses are existentially
    hidden again before the public theorem is concluded. *)
Definition private_frozen_statement_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary)
  (incoming : Ensemble authority_flow_state)
  (snapshots : list frozen_caller_snapshot_slot) (h : heap) : Prop :=
  principled_frozen_authority_history_state CT P Z cutoff active stack
    incoming snapshots h /\
  frozen_caller_snapshots_active_resume_justified CT h Z active snapshots /\
  frozen_caller_snapshots_before_boundaries snapshots stack /\
  frozen_caller_snapshots_nested_covered snapshots /\
  frozen_caller_snapshots_nested_resume_safe Z snapshots /\
  frozen_completed_colors_resume_safe Z
    (executing_authority_color_set CT h active incoming) snapshots.

Lemma repeat_none_snapshots_active_resume_origins :
  forall CT h active count,
    frozen_caller_snapshots_active_resume_origins CT h active
      (repeat None count).
Proof.
  intros CT h active count snapshot snapshot_mode active_mode location
    Hsnapshot. apply repeat_spec in Hsnapshot. discriminate.
Qed.

Lemma repeat_none_snapshots_before_boundaries :
  forall stack,
    frozen_caller_snapshots_before_boundaries
      (repeat (None : frozen_caller_snapshot_slot) (length stack)) stack.
Proof.
  intros stack. induction stack as [|boundary stack IH]; simpl.
  - constructor.
  - constructor; [exact I|exact IH].
Qed.

Lemma repeat_none_snapshots_nested_covered :
  forall count,
    frozen_caller_snapshots_nested_covered
      (repeat (None : frozen_caller_snapshot_slot) count).
Proof.
  intros count. induction count; simpl; auto.
Qed.

(** Final private induction package for nested channel-free calls.  The
    existing snapshot certificates describe authority provenance; this
    additional, stack-aligned conjunct describes the allocation age of the
    mutable components that can be passed through a later nested call.  It
    is vacuous for every boundary present at entry to the public theorem and
    therefore introduces no public assumption. *)
Definition private_fresh_frozen_statement_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary)
  (incoming : Ensemble authority_flow_state)
  (snapshots : list frozen_caller_snapshot_slot) (h : heap) : Prop :=
  private_frozen_statement_state CT P Z cutoff active stack incoming
    snapshots h /\
  frozen_callee_side_mutable_components_after_boundaries CT h active
    snapshots stack /\
  frozen_callee_side_prospective_components_after_boundaries CT h active
    snapshots stack /\
  frozen_snapshot_boundaries_after_cutoff cutoff snapshots stack.

Definition frozen_caller_snapshot_list_included
  (new old : list frozen_caller_snapshot_slot) : Prop :=
  forall new_snapshot,
    List.In (Some new_snapshot) new ->
    exists old_snapshot,
      List.In (Some old_snapshot) old /\
      Included authority_flow_state
        new_snapshot.(frozen_snapshot_current_colors)
        old_snapshot.(frozen_snapshot_current_colors).

Lemma advance_frozen_caller_snapshot_after_graph_reflection_included :
  forall CT h h' active snapshot,
    (forall left right,
      retained_mut_edge CT h' left right ->
      retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right ->
      mutable_edge CT h left right) ->
    (forall location,
      frame_owned_location CT h' active location ->
      frame_owned_location CT h active location) ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h active
        snapshot.(frozen_snapshot_current_colors))
      snapshot.(frozen_snapshot_current_colors) ->
    Included authority_flow_state
      (advance_frozen_caller_snapshot CT h' active snapshot)
        .(frozen_snapshot_current_colors)
      snapshot.(frozen_snapshot_current_colors).
Proof.
  intros CT h h' active snapshot Hretained Hmutable Howned Hclosed state
    [seed [Hseed Hpath]].
  assert (Hstep_reflect : forall source target,
      frozen_caller_authority_step CT h' active source target ->
      frozen_caller_authority_step CT h active source target).
  { intros source target Hstep. inversion Hstep; subst.
    - apply frozen_caller_retained. apply Hretained. exact H.
    - apply frozen_caller_prospective_retained.
      apply Hretained. exact H.
    - apply frozen_caller_prospective_rdm_backward.
      apply Hmutable. exact H.
    - apply frozen_caller_reverse_rdm. apply Hmutable. exact H.
    - eapply frozen_caller_powered_frame_join; eauto.
    - eapply frozen_caller_prospective_frame_join; eauto.
    - apply frozen_caller_mark_prospective. }
  apply Hclosed. exists seed. split; [exact Hseed|].
  induction Hpath.
  - apply rt_step. apply Hstep_reflect. exact H.
  - apply rt_refl.
  - have Hold_first := IHHpath1 Hseed.
    have Hmiddle : In authority_flow_state
        snapshot.(frozen_snapshot_current_colors) y.
    { apply Hclosed. exists x. split; assumption. }
    eapply rt_trans.
    + exact Hold_first.
    + exact (IHHpath2 Hmiddle).
Qed.

Lemma frozen_caller_closure_after_graph_reflection_included :
  forall CT h h' active colors,
    (forall left right,
      retained_mut_edge CT h' left right ->
      retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right ->
      mutable_edge CT h left right) ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h active colors) colors ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h' active colors) colors.
Proof.
  intros CT h h' active colors Hretained Hmutable Hclosed state
    [seed [Hseed Hpath]].
  assert (Hstep_reflect : forall source target,
      frozen_caller_authority_step CT h' active source target ->
      frozen_caller_authority_step CT h active source target).
  { intros source target Hstep. inversion Hstep; subst.
    - apply frozen_caller_retained. apply Hretained. exact H.
    - apply frozen_caller_prospective_retained.
      apply Hretained. exact H.
    - apply frozen_caller_prospective_rdm_backward.
      apply Hmutable. exact H.
    - apply frozen_caller_reverse_rdm. apply Hmutable. exact H.
    - eapply frozen_caller_powered_frame_join; eauto.
    - eapply frozen_caller_prospective_frame_join; eauto.
    - apply frozen_caller_mark_prospective. }
  apply Hclosed. exists seed. split; [exact Hseed|].
  induction Hpath.
  - apply rt_step. apply Hstep_reflect. exact H.
  - apply rt_refl.
  - have Hold_first := IHHpath1 Hseed.
    have Hmiddle : In authority_flow_state colors y.
    { apply Hclosed. exists x. split; assumption. }
    eapply rt_trans.
    + exact Hold_first.
    + exact (IHHpath2 Hmiddle).
Qed.

Lemma frozen_caller_connected_after_graph_reflection :
  forall CT old_h new_h frame source target,
    (forall left right,
      retained_mut_edge CT new_h left right ->
      retained_mut_edge CT old_h left right) ->
    (forall left right,
      mutable_edge CT new_h left right ->
      mutable_edge CT old_h left right) ->
    frozen_caller_authority_connected CT new_h frame source target ->
    frozen_caller_authority_connected CT old_h frame source target.
Proof.
  intros CT old_h new_h frame source target Hretained Hmutable Hpath.
  induction Hpath.
  - apply rt_step. inversion H; subst.
    + apply frozen_caller_retained. eauto.
    + apply frozen_caller_prospective_retained. eauto.
    + apply frozen_caller_prospective_rdm_backward. eauto.
    + apply frozen_caller_reverse_rdm. eauto.
    + eapply frozen_caller_powered_frame_join; eauto.
    + eapply frozen_caller_prospective_frame_join; eauto.
    + apply frozen_caller_mark_prospective.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma advance_frozen_caller_snapshots_after_graph_reflection_included :
  forall CT h h' active snapshots,
    (forall left right,
      retained_mut_edge CT h' left right ->
      retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right ->
      mutable_edge CT h left right) ->
    (forall location,
      frame_owned_location CT h' active location ->
      frame_owned_location CT h active location) ->
    frozen_caller_snapshots_closed CT h active snapshots ->
    frozen_caller_snapshot_list_included
      (advance_frozen_caller_snapshots CT h' active snapshots) snapshots.
Proof.
  intros CT h h' active snapshots Hretained Hmutable Howned Hclosed
    new_snapshot Hnew.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot.
  exists old_snapshot. split; [exact Hold|].
  eapply advance_frozen_caller_snapshot_after_graph_reflection_included;
    eauto.
Qed.

Lemma frozen_caller_snapshots_runtime_mutable_transport :
  forall h h' snapshots,
    (forall location, r_muttype h' location = r_muttype h location) ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_runtime_mutable h' snapshots.
Proof.
  intros h h' snapshots Hruntimes Hruntime snapshot Hsnapshot mode location
    Hcolor.
  rewrite Hruntimes. eapply Hruntime; eauto.
Qed.

Lemma principled_frozen_authority_after_graph_reflection :
  forall CT P Z cutoff active stack incoming snapshots h h',
    principled_frozen_authority_history_state CT P Z cutoff active stack
      incoming snapshots h ->
    principled_phased_authority_live_history_state CT P Z cutoff
      active stack incoming h' ->
    dom h <= dom h' ->
    (forall location, r_muttype h' location = r_muttype h location) ->
    (forall left right,
      retained_mut_edge CT h' left right ->
      retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right ->
      mutable_edge CT h left right) ->
    (forall location,
      frame_owned_location CT h' active location ->
      frame_owned_location CT h active location) ->
    principled_frozen_authority_history_state CT P Z cutoff active stack
      incoming (advance_frozen_caller_snapshots CT h' active snapshots) h'.
Proof.
  intros CT P Z cutoff active stack incoming snapshots h h'
    [Hold [Haligned [Hruntime [Hclosed
      [Hretain [Hdangerous [Havoid [Hroots [Hexposure
        [Hresume [Hjoins [Hentry_covered Hphase_covered]]]]]]]]]]]]
    Hpost Hdom Hruntimes Hretained Hmutable Howned.
  have Hincluded :=
    advance_frozen_caller_snapshots_after_graph_reflection_included CT h h'
      active snapshots Hretained Hmutable Howned Hclosed.
  split; [exact Hpost|]. split.
  - unfold frozen_caller_snapshots_aligned in *.
    unfold advance_frozen_caller_snapshots. rewrite length_map.
    exact Haligned.
  - split.
    + eapply advance_frozen_caller_snapshots_runtime_mutable.
      * exact (proj1 (proj1
           (proj2 (proj2 (proj2 (proj2 Hpost)))))).
      * eapply frozen_caller_snapshots_runtime_mutable_transport; eauto.
    + split.
      * apply advance_frozen_caller_snapshots_closed.
      * split.
        -- eapply advance_frozen_caller_snapshots_retain_entry. exact Hretain.
        -- split.
           ++ eapply advance_frozen_caller_snapshots_dangerous.
              exact Hdangerous.
           ++ split.
              ** intros new_snapshot mode location Hsnapshot Hmode Hcolor.
                 destruct (Hincluded new_snapshot Hsnapshot) as
                   [old_snapshot [Hold_snapshot Hcolors]].
                 eapply Havoid; [exact Hold_snapshot|exact Hmode|].
                 eapply Hcolors. exact Hcolor.
              ** split.
                 --- intros new_snapshot root Hsnapshot Hroot.
                     unfold advance_frozen_caller_snapshots in Hsnapshot.
                     apply in_map_iff in Hsnapshot.
                     destruct Hsnapshot as [old_slot [Heq Hold_slot]].
                     destruct old_slot as [old_snapshot|]; simpl in Heq;
                       [|discriminate].
                     injection Heq as Heq. subst new_snapshot. simpl in Hroot.
                     have Hold_root : root < dom h by
                       (eapply Hroots; eauto).
                     lia.
                 --- split.
                     +++ split.
                         *** intros new_snapshot Hsnapshot mode location Hcolor.
                             unfold advance_frozen_caller_snapshots in Hsnapshot.
                             apply in_map_iff in Hsnapshot.
                             destruct Hsnapshot as [old_slot [Heq Hold_slot]].
                             destruct old_slot as [old_snapshot|]; simpl in Heq;
                               [|discriminate].
                             injection Heq as Heq. subst new_snapshot. simpl in Hcolor.
                             eapply (advance_frozen_caller_snapshot_runtime_mutable
                               CT h' active
                               old_snapshot.(frozen_snapshot_current_resume_exposure)).
                             ---- exact (proj1 (proj1
                               (proj2 (proj2 (proj2 (proj2 Hpost)))))).
                             ---- intros old_mode old_location Hold_color.
                                  rewrite Hruntimes.
                                  eapply (proj1 Hexposure); eauto.
                             ---- exact Hcolor.
                         *** split.
                             ---- intros new_snapshot Hsnapshot.
                                  unfold advance_frozen_caller_snapshots in Hsnapshot.
                                  apply in_map_iff in Hsnapshot.
                                  destruct Hsnapshot as [old_slot [Heq Hold_slot]].
                                  destruct old_slot as [old_snapshot|]; simpl in Heq;
                                    [|discriminate].
                                  injection Heq as Heq. subst new_snapshot.
                                  simpl. exact (proj1
                                    (frozen_caller_authority_closure_idempotent
                                      CT h' active
                                      old_snapshot.(frozen_snapshot_current_resume_exposure))).
                             ---- split.
                                  ++++ intros new_snapshot mode location Hsnapshot Hcolor.
                                  unfold advance_frozen_caller_snapshots in Hsnapshot.
                                  apply in_map_iff in Hsnapshot.
                                  destruct Hsnapshot as [old_slot [Heq Hold_slot]].
                                  destruct old_slot as [old_snapshot|]; simpl in Heq;
                                    [|discriminate].
                                  injection Heq as Heq. subst new_snapshot. simpl in Hcolor.
                                  destruct Hcolor as [seed [Hseed Hpath]].
                                  destruct seed as [seed_mode seed_location].
                                  have Hseed_mode : authority_mode_dangerous seed_mode by
                                    (eapply (proj1 (proj2 (proj2 Hexposure))); eauto).
                                  have Hresult :=
                                    frozen_caller_authority_connected_preserves_dangerous
                                      CT h' active (seed_mode, seed_location)
                                      (mode, location) Hseed_mode Hpath.
                                  exact Hresult.
                                  ++++ split.
                                       ***** intros new_snapshot Hsnapshot state Hentry.
                                       unfold advance_frozen_caller_snapshots in Hsnapshot.
                                       apply in_map_iff in Hsnapshot.
                                       destruct Hsnapshot as [old_slot [Heq Hold_slot]].
                                       destruct old_slot as [old_snapshot|]; simpl in Heq;
                                         [|discriminate].
                                       injection Heq as Heq. subst new_snapshot. simpl in *.
                                       apply frozen_caller_authority_closure_contains.
                                            eapply (proj1 (proj2 (proj2
                                              (proj2 Hexposure)))); eauto.
                                       ***** intros new_snapshot root Hsnapshot
                                               Hroot Hroot_runtime.
                                            unfold advance_frozen_caller_snapshots
                                              in Hsnapshot.
                                            apply in_map_iff in Hsnapshot.
                                            destruct Hsnapshot as
                                              [old_slot [Heq Hold_slot]].
                                            destruct old_slot as [old_snapshot|];
                                              simpl in Heq; [|discriminate].
                                            injection Heq as Heq.
                                            subst new_snapshot. simpl in *.
                                            apply frozen_caller_authority_closure_contains.
                                            eapply (proj2 (proj2 (proj2
                                              (proj2 Hexposure)))); eauto.
                                            rewrite <- Hruntimes. exact Hroot_runtime.
                     +++ split.
                         *** intros new_snapshot active_mode source exposure_mode target
                           Hsnapshot Hactive_mode Hactive Hsource
                           Hexposure_mode Htarget Hprotected.
                         unfold advance_frozen_caller_snapshots in Hsnapshot.
                         apply in_map_iff in Hsnapshot.
                         destruct Hsnapshot as [old_slot [Heq Hold_slot]].
                         destruct old_slot as [old_snapshot|]; simpl in Heq;
                           [|discriminate].
                         injection Heq as Heq. subst new_snapshot. simpl in *.
                         destruct
                           (executing_authority_colors_after_graph_reflection_covered
                             CT h h' active (Empty_set authority_flow_state) Howned
                             Hretained Hmutable active_mode source Hactive_mode
                             Hactive) as [old_mode [Hold_mode Hold_active]].
                         have Hold_target : In authority_flow_state
                             old_snapshot.(frozen_snapshot_current_resume_exposure)
                             (exposure_mode, target).
                         { eapply frozen_caller_closure_after_graph_reflection_included;
                             [exact Hretained|exact Hmutable| |exact Htarget].
                           eapply (proj1 (proj2 Hexposure)); eauto. }
                         eapply Hresume with (snapshot := old_snapshot)
                           (active_mode := old_mode) (source := source)
                           (exposure_mode := exposure_mode); eauto.
                         *** split.
                             ---- intros new_snapshot source_mode source Hsnapshot
                               Hsource_mode Hsource_color Hsource_root.
                             unfold advance_frozen_caller_snapshots in Hsnapshot.
                             apply in_map_iff in Hsnapshot.
                             destruct Hsnapshot as [old_slot [Heq Hold_slot]].
                             destruct old_slot as [old_snapshot|]; simpl in Heq;
                               [|discriminate].
                             injection Heq as Heq. subst new_snapshot. simpl in *.
                             have Hold_source : In authority_flow_state
                                 old_snapshot.(frozen_snapshot_current_colors)
                                 (source_mode, source).
                             { eapply frozen_caller_closure_after_graph_reflection_included;
                                 [exact Hretained|exact Hmutable| |exact Hsource_color].
                               eapply Hclosed; eauto. }
                                  destruct (Hjoins old_snapshot source_mode source
                               Hold_slot Hsource_mode Hold_source Hsource_root) as
                               [[entry_mode [Hentry_mode Hentry]] | Hsafe].
                                  ++++ left. exists entry_mode. split; assumption.
                                  ++++ right. intros exposure_mode target
                                    Hexposure_mode Htarget Hprotected.
                                       apply (Hsafe exposure_mode target
                                    Hexposure_mode); [|exact Hprotected].
                                       eapply frozen_caller_closure_after_graph_reflection_included;
                                    [exact Hretained|exact Hmutable| |exact Htarget].
                                       eapply (proj1 (proj2 Hexposure)); eauto.
                             ---- split.
                                  ++++ apply advance_frozen_caller_snapshots_entry_exposure_covered.
                                       exact Hentry_covered.
                                  ++++ apply advance_frozen_caller_snapshots_cover_phase_incoming.
                                       exact Hphase_covered.
Qed.

Lemma frozen_caller_color_dangerous_retained :
  forall CT h frame colors mode left right,
    Included authority_flow_state
      (frozen_caller_authority_closure CT h frame colors) colors ->
    authority_mode_dangerous mode ->
    In authority_flow_state colors (mode, left) ->
    retained_mut_edge CT h left right ->
    In authority_flow_state colors (mode, right).
Proof.
  intros CT h frame colors mode left right Hclosed Hmode Hleft Hedge.
  apply Hclosed. exists (mode, left). split; [exact Hleft|].
  apply rt_step. destruct Hmode as [-> | ->].
  - apply frozen_caller_retained. exact Hedge.
  - apply frozen_caller_prospective_retained. exact Hedge.
Qed.

Lemma frozen_caller_color_dangerous_reverse_rdm :
  forall CT h frame colors mode left right,
    Included authority_flow_state
      (frozen_caller_authority_closure CT h frame colors) colors ->
    authority_mode_dangerous mode ->
    In authority_flow_state colors (mode, left) ->
    mutable_edge CT h right left ->
    In authority_flow_state colors (FlowProspective, right).
Proof.
  intros CT h frame colors mode left right Hclosed Hmode Hleft Hedge.
  apply Hclosed. exists (mode, left). split; [exact Hleft|].
  apply rt_step. destruct Hmode as [-> | ->].
  - apply frozen_caller_reverse_rdm. exact Hedge.
  - apply frozen_caller_prospective_rdm_backward. exact Hedge.
Qed.

Lemma frozen_caller_color_dangerous_frame_join :
  forall CT h frame colors mode left right,
    Included authority_flow_state
      (frozen_caller_authority_closure CT h frame colors) colors ->
    authority_mode_dangerous mode ->
    In authority_flow_state colors (mode, left) ->
    typed_root RDM frame.(frame_senv) frame.(frame_renv) left ->
    typed_root RDM frame.(frame_senv) frame.(frame_renv) right ->
    In authority_flow_state colors (FlowProspective, right).
Proof.
  intros CT h frame colors mode left right Hclosed Hmode Hleft
    Hleft_root Hright_root.
  apply Hclosed. exists (mode, left). split; [exact Hleft|].
  apply rt_step. destruct Hmode as [-> | ->].
  - eapply frozen_caller_powered_frame_join; eauto.
  - eapply frozen_caller_prospective_frame_join; eauto.
Qed.

Lemma frozen_caller_field_update_forward_covered :
  forall CT h frame colors lx old field written old_mode left right,
    runtime_getObj h lx = Some old ->
    authority_colors_runtime_mutable h colors ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h frame colors) colors ->
    (forall caller_mode active_mode location,
      authority_mode_dangerous caller_mode ->
      authority_mode_dangerous active_mode ->
      In authority_flow_state colors (caller_mode, location) ->
      ~ In authority_flow_state
          (independent_active_authority_colors CT h frame)
          (active_mode, location)) ->
    authority_safe_field_endpoints CT h frame lx written ->
    authority_mode_dangerous old_mode ->
    In authority_flow_state colors (old_mode, left) ->
    retained_mut_edge CT (update_field h lx field (Iot written)) left right ->
    exists target_mode,
      authority_mode_dangerous target_mode /\
      In authority_flow_state colors (target_mode, right).
Proof.
  intros CT h frame colors lx old field written old_mode left right Hobj
    Hruntime Hclosed Hseparated Hendpoints Hmode Hleft Hedge.
  destruct (retained_edge_after_field_update CT h lx old field
    (Iot written) left right Hobj Hedge) as
    [Hold | [Heq_left [Heq_value Hnew]]].
  - exists old_mode. split; [exact Hmode|].
    eapply frozen_caller_color_dangerous_retained; eauto.
  - injection Heq_value as Heq_right. subst left right.
    inversion Hendpoints; subst.
    + exfalso. eapply Hseparated with
        (caller_mode := old_mode) (active_mode := FlowPowered)
        (location := lx); eauto.
      * left. reflexivity.
      * apply executing_authority_owned_is_powered. exact H.
    + have Hmut := Hruntime old_mode lx Hleft.
      rewrite H in Hmut. discriminate.
    + exists FlowProspective. split; [right; reflexivity|].
      eapply frozen_caller_color_dangerous_frame_join; eauto.
Qed.

Lemma frozen_caller_field_update_backward_covered :
  forall CT h frame colors lx old field written old_mode left right,
    runtime_getObj h lx = Some old ->
    authority_colors_runtime_mutable h colors ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h frame colors) colors ->
    (forall caller_mode active_mode location,
      authority_mode_dangerous caller_mode ->
      authority_mode_dangerous active_mode ->
      In authority_flow_state colors (caller_mode, location) ->
      ~ In authority_flow_state
          (independent_active_authority_colors CT h frame)
          (active_mode, location)) ->
    authority_safe_field_endpoints CT h frame lx written ->
    authority_mode_dangerous old_mode ->
    In authority_flow_state colors (old_mode, left) ->
    mutable_edge CT (update_field h lx field (Iot written)) right left ->
    exists target_mode,
      authority_mode_dangerous target_mode /\
      In authority_flow_state colors (target_mode, right).
Proof.
  intros CT h frame colors lx old field written old_mode left right Hobj
    Hruntime Hclosed Hseparated Hendpoints Hmode Hleft Hedge.
  destruct (mutable_edge_after_field_update CT h lx old field
    (Iot written) right left Hobj Hedge) as
    [Hold | [Heq_right [Heq_value Hnew]]].
  - exists FlowProspective. split; [right; reflexivity|].
    eapply frozen_caller_color_dangerous_reverse_rdm; eauto.
  - injection Heq_value as Heq_left. subst left right.
    inversion Hendpoints; subst.
    + exfalso. eapply Hseparated with
        (caller_mode := old_mode) (active_mode := FlowPowered)
        (location := written); eauto.
      * left. reflexivity.
      * apply executing_authority_owned_is_powered. exact H0.
    + have Hmut := Hruntime old_mode written Hleft.
      rewrite H0 in Hmut. discriminate.
    + exists FlowProspective. split; [right; reflexivity|].
      eapply frozen_caller_color_dangerous_frame_join; eauto.
Qed.

Lemma frozen_caller_step_after_safe_field_update_covered :
  forall CT h frame colors lx old field written source target,
    runtime_getObj h lx = Some old ->
    authority_colors_runtime_mutable h colors ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h frame colors) colors ->
    (forall caller_mode active_mode location,
      authority_mode_dangerous caller_mode ->
      authority_mode_dangerous active_mode ->
      In authority_flow_state colors (caller_mode, location) ->
      ~ In authority_flow_state
          (independent_active_authority_colors CT h frame)
          (active_mode, location)) ->
    authority_safe_field_endpoints CT h frame lx written ->
    authority_state_covered colors source ->
    frozen_caller_authority_step CT
      (update_field h lx field (Iot written)) frame source target ->
    authority_state_covered colors target.
Proof.
  intros CT h frame colors lx old field written source target Hobj Hruntime
    Hclosed Hseparated Hendpoints Hsource Hstep Htarget_mode.
  inversion Hstep; subst; simpl in *.
  - destruct (Hsource (or_introl eq_refl)) as
      [old_mode [Hold_mode Hold_color]].
    eapply frozen_caller_field_update_forward_covered; eauto.
  - destruct (Hsource (or_intror eq_refl)) as
      [old_mode [Hold_mode Hold_color]].
    eapply frozen_caller_field_update_forward_covered; eauto.
  - destruct (Hsource (or_intror eq_refl)) as
      [old_mode [Hold_mode Hold_color]].
    eapply frozen_caller_field_update_backward_covered; eauto.
  - destruct (Hsource (or_introl eq_refl)) as
      [old_mode [Hold_mode Hold_color]].
    eapply frozen_caller_field_update_backward_covered; eauto.
  - destruct (Hsource (or_introl eq_refl)) as
      [old_mode [Hold_mode Hold_color]].
    exists FlowProspective. split; [right; reflexivity|].
    eapply frozen_caller_color_dangerous_frame_join; eauto.
  - destruct (Hsource (or_intror eq_refl)) as
      [old_mode [Hold_mode Hold_color]].
    exists FlowProspective. split; [right; reflexivity|].
    eapply frozen_caller_color_dangerous_frame_join; eauto.
  - destruct (Hsource (or_introl eq_refl)) as
      [old_mode [[-> | ->] Hold_color]].
    + exists FlowProspective. split; [right; reflexivity|].
      apply Hclosed. exists (FlowPowered, location).
      split; [exact Hold_color|].
      apply rt_step. apply frozen_caller_mark_prospective.
    + exists FlowProspective. split; [right; reflexivity|exact Hold_color].
Qed.

Definition frozen_authority_state_covered_by_old_or_active
  (old active : Ensemble authority_flow_state)
  (state : authority_flow_state) : Prop :=
  authority_mode_dangerous (fst state) ->
  (exists old_mode,
      authority_mode_dangerous old_mode /\
      In authority_flow_state old (old_mode, snd state)) \/
  (exists active_mode,
      authority_mode_dangerous active_mode /\
      In authority_flow_state active (active_mode, snd state)).

Definition frozen_caller_snapshot_list_covered_by_old_or_active
  (active : Ensemble authority_flow_state)
  (new old : list frozen_caller_snapshot_slot) : Prop :=
  forall new_snapshot,
    List.In (Some new_snapshot) new ->
    exists old_snapshot,
      List.In (Some old_snapshot) old /\
      forall mode location,
        authority_mode_dangerous mode ->
        In authority_flow_state
          new_snapshot.(frozen_snapshot_current_colors) (mode, location) ->
        (exists old_mode,
            authority_mode_dangerous old_mode /\
            In authority_flow_state
              old_snapshot.(frozen_snapshot_current_colors)
              (old_mode, location)) \/
        (exists active_mode,
            authority_mode_dangerous active_mode /\
            In authority_flow_state active (active_mode, location)).

Definition frozen_state_covered_by_old_or
  (snapshot : frozen_caller_color_snapshot) (fallback : Prop)
  (state : authority_flow_state) : Prop :=
  authority_mode_dangerous (fst state) ->
  (exists old_mode,
      authority_mode_dangerous old_mode /\
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (old_mode, snd state)) \/
  fallback.

Lemma frozen_caller_field_update_forward_covered_by_old_or_active :
  forall CT h frame colors lx old field written old_mode left right,
    runtime_getObj h lx = Some old ->
    authority_colors_runtime_mutable h colors ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h frame colors) colors ->
    authority_safe_field_endpoints CT h frame lx written ->
    authority_mode_dangerous old_mode ->
    In authority_flow_state colors (old_mode, left) ->
    retained_mut_edge CT (update_field h lx field (Iot written)) left right ->
    (exists target_mode,
        authority_mode_dangerous target_mode /\
        In authority_flow_state colors (target_mode, right)) \/
    (exists active_mode,
        authority_mode_dangerous active_mode /\
        In authority_flow_state
          (independent_active_authority_colors CT h frame)
          (active_mode, right)).
Proof.
  intros CT h frame colors lx old field written old_mode left right Hobj
    Hruntime Hclosed Hendpoints Hmode Hleft Hedge.
  destruct (retained_edge_after_field_update CT h lx old field
    (Iot written) left right Hobj Hedge) as
    [Hold | [Heq_left [Heq_value Hnew]]].
  - left. exists old_mode. split; [exact Hmode|].
    eapply frozen_caller_color_dangerous_retained; eauto.
  - injection Heq_value as Heq_right. subst left right.
    inversion Hendpoints; subst.
    + right. exists FlowPowered. split; [left; reflexivity|].
      unfold independent_active_authority_colors.
      apply executing_authority_owned_is_powered. exact H0.
    + have Hmut := Hruntime old_mode lx Hleft.
      rewrite H in Hmut. discriminate.
    + left. exists FlowProspective. split; [right; reflexivity|].
      eapply frozen_caller_color_dangerous_frame_join;
        eauto.
Qed.

Lemma frozen_caller_field_update_backward_covered_by_old_or_active :
  forall CT h frame colors lx old field written old_mode left right,
    runtime_getObj h lx = Some old ->
    authority_colors_runtime_mutable h colors ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h frame colors) colors ->
    authority_safe_field_endpoints CT h frame lx written ->
    authority_mode_dangerous old_mode ->
    In authority_flow_state colors (old_mode, left) ->
    mutable_edge CT (update_field h lx field (Iot written)) right left ->
    (exists target_mode,
        authority_mode_dangerous target_mode /\
        In authority_flow_state colors (target_mode, right)) \/
    (exists active_mode,
        authority_mode_dangerous active_mode /\
        In authority_flow_state
          (independent_active_authority_colors CT h frame)
          (active_mode, right)).
Proof.
  intros CT h frame colors lx old field written old_mode left right Hobj
    Hruntime Hclosed Hendpoints Hmode Hleft Hedge.
  destruct (mutable_edge_after_field_update CT h lx old field
    (Iot written) right left Hobj Hedge) as
    [Hold | [Heq_right [Heq_value Hnew]]].
  - left. exists FlowProspective. split; [right; reflexivity|].
    eapply frozen_caller_color_dangerous_reverse_rdm; eauto.
  - injection Heq_value as Heq_left. subst left right.
    inversion Hendpoints; subst.
    + right. exists FlowPowered. split; [left; reflexivity|].
      unfold independent_active_authority_colors.
      apply executing_authority_owned_is_powered. exact H.
    + have Hmut := Hruntime old_mode written Hleft.
      rewrite H0 in Hmut. discriminate.
    + left. exists FlowProspective. split; [right; reflexivity|].
      eapply frozen_caller_color_dangerous_frame_join;
        eauto.
Qed.

Lemma frozen_caller_step_after_safe_field_update_covered_by_old_or_active :
  forall CT h frame colors lx old field written source target,
    runtime_getObj h lx = Some old ->
    authority_colors_runtime_mutable h colors ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h frame colors) colors ->
    authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h frame) ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h frame
        (independent_active_authority_colors CT h frame))
      (independent_active_authority_colors CT h frame) ->
    authority_safe_field_endpoints CT h frame lx written ->
    frozen_authority_state_covered_by_old_or_active colors
      (independent_active_authority_colors CT h frame) source ->
    frozen_caller_authority_step CT
      (update_field h lx field (Iot written)) frame source target ->
    frozen_authority_state_covered_by_old_or_active colors
      (independent_active_authority_colors CT h frame) target.
Proof.
  intros CT h frame colors lx old field written source target Hobj Hruntime
    Hclosed Hactive_runtime Hactive_closed Hendpoints Hsource Hstep
    Htarget_mode.
  inversion Hstep; subst; simpl in *.
  - destruct (Hsource (or_introl eq_refl)) as
      [[old_mode [Hold_mode Hold_color]] |
       [active_mode [Hactive_mode Hactive_color]]].
    + eapply frozen_caller_field_update_forward_covered_by_old_or_active;
        eauto.
    + destruct (frozen_caller_field_update_forward_covered_by_old_or_active
        CT h frame (independent_active_authority_colors CT h frame) lx old
        field written active_mode left right Hobj Hactive_runtime
        Hactive_closed Hendpoints Hactive_mode Hactive_color H) as [Hcov|Hcov];
        right; exact Hcov.
  - destruct (Hsource (or_intror eq_refl)) as
      [[old_mode [Hold_mode Hold_color]] |
       [active_mode [Hactive_mode Hactive_color]]].
    + eapply frozen_caller_field_update_forward_covered_by_old_or_active;
        eauto.
    + destruct (frozen_caller_field_update_forward_covered_by_old_or_active
        CT h frame (independent_active_authority_colors CT h frame) lx old
        field written active_mode left right Hobj Hactive_runtime
        Hactive_closed Hendpoints Hactive_mode Hactive_color H) as [Hcov|Hcov];
        right; exact Hcov.
  - destruct (Hsource (or_intror eq_refl)) as
      [[old_mode [Hold_mode Hold_color]] |
       [active_mode [Hactive_mode Hactive_color]]].
    + eapply frozen_caller_field_update_backward_covered_by_old_or_active;
        eauto.
    + destruct (frozen_caller_field_update_backward_covered_by_old_or_active
        CT h frame (independent_active_authority_colors CT h frame) lx old
        field written active_mode left right Hobj Hactive_runtime
        Hactive_closed Hendpoints Hactive_mode Hactive_color H) as [Hcov|Hcov];
        right; exact Hcov.
  - destruct (Hsource (or_introl eq_refl)) as
      [[old_mode [Hold_mode Hold_color]] |
       [active_mode [Hactive_mode Hactive_color]]].
    + eapply frozen_caller_field_update_backward_covered_by_old_or_active;
        eauto.
    + destruct (frozen_caller_field_update_backward_covered_by_old_or_active
        CT h frame (independent_active_authority_colors CT h frame) lx old
        field written active_mode left right Hobj Hactive_runtime
        Hactive_closed Hendpoints Hactive_mode Hactive_color H) as [Hcov|Hcov];
        right; exact Hcov.
  - destruct (Hsource (or_introl eq_refl)) as
      [[old_mode [Hold_mode Hold_color]] |
       [active_mode [Hactive_mode Hactive_color]]].
    + left. exists FlowProspective. split; [right; reflexivity|].
      eapply frozen_caller_color_dangerous_frame_join;
        eauto.
    + right. exists FlowProspective. split; [right; reflexivity|].
      eapply executing_authority_dangerous_frame_join;
        eauto.
  - destruct (Hsource (or_intror eq_refl)) as
      [[old_mode [Hold_mode Hold_color]] |
       [active_mode [Hactive_mode Hactive_color]]].
    + left. exists FlowProspective. split; [right; reflexivity|].
      eapply frozen_caller_color_dangerous_frame_join;
        eauto.
    + right. exists FlowProspective. split; [right; reflexivity|].
      eapply executing_authority_dangerous_frame_join;
        eauto.
  - destruct (Hsource (or_introl eq_refl)) as
      [[old_mode [[-> | ->] Hold_color]] |
       [active_mode [[-> | ->] Hactive_color]]].
    + left. exists FlowProspective. split; [right; reflexivity|].
      apply Hclosed. exists (FlowPowered, location). split; [exact Hold_color|].
      apply rt_step. apply frozen_caller_mark_prospective.
    + left. exists FlowProspective. split; [right; reflexivity|exact Hold_color].
    + right. exists FlowProspective. split; [right; reflexivity|].
      unfold independent_active_authority_colors in *.
      destruct Hactive_color as [seed [Hseed Hpath]].
      exists seed. split; [exact Hseed|].
      eapply rt_trans; [exact Hpath|].
      apply rt_step. apply phased_authority_mark_prospective.
    + right. exists FlowProspective. split; [right; reflexivity|exact Hactive_color].
Qed.

Lemma frozen_caller_connected_after_safe_field_update_covered_by_old_or_active :
  forall CT h frame colors lx old field written source target,
    runtime_getObj h lx = Some old ->
    authority_colors_runtime_mutable h colors ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h frame colors) colors ->
    authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h frame) ->
    authority_safe_field_endpoints CT h frame lx written ->
    frozen_authority_state_covered_by_old_or_active colors
      (independent_active_authority_colors CT h frame) source ->
    frozen_caller_authority_connected CT
      (update_field h lx field (Iot written)) frame source target ->
    frozen_authority_state_covered_by_old_or_active colors
      (independent_active_authority_colors CT h frame) target.
Proof.
  intros CT h frame colors lx old field written source target Hobj Hruntime
    Hclosed Hactive_runtime Hendpoints Hsource Hconnected.
  induction Hconnected.
  - eapply frozen_caller_step_after_safe_field_update_covered_by_old_or_active;
      eauto using independent_active_authority_colors_frozen_closed.
  - exact Hsource.
  - apply IHHconnected2. apply IHHconnected1. exact Hsource.
Qed.

(** Closing a frozen caller snapshot together with the active frame cannot
    invent a third dangerous provenance.  Before promotion, all dangerous
    steps are part of the frozen closure; after promotion, the same location
    is independently powered by the active frame. *)
Lemma phased_step_with_frozen_incoming_covered_by_old_or_active :
  forall CT h frame colors source target,
    Included authority_flow_state
      (frozen_caller_authority_closure CT h frame colors) colors ->
    frozen_authority_state_covered_by_old_or_active colors
      (independent_active_authority_colors CT h frame) source ->
    phased_authority_frame_step CT h frame source target ->
    frozen_authority_state_covered_by_old_or_active colors
      (independent_active_authority_colors CT h frame) target.
Proof.
  intros CT h frame colors source target Hclosed Hsource Hstep Htarget_mode.
  inversion Hstep; subst; simpl in *.
  - destruct (Hsource (or_introl eq_refl)) as
      [[old_mode [Hold_mode Hold_color]] |
       [active_mode [Hactive_mode Hactive_color]]].
    + left. exists old_mode. split; [exact Hold_mode|].
      eapply frozen_caller_color_dangerous_retained; eauto.
    + right. exists active_mode. split; [exact Hactive_mode|].
      eapply executing_authority_dangerous_retained; eauto.
  - destruct (Hsource (or_intror eq_refl)) as
      [[old_mode [Hold_mode Hold_color]] |
       [active_mode [Hactive_mode Hactive_color]]].
    + left. exists old_mode. split; [exact Hold_mode|].
      eapply frozen_caller_color_dangerous_retained; eauto.
    + right. exists active_mode. split; [exact Hactive_mode|].
      eapply executing_authority_dangerous_retained; eauto.
  - destruct (Hsource (or_intror eq_refl)) as
      [[old_mode [Hold_mode Hold_color]] |
       [active_mode [Hactive_mode Hactive_color]]].
    + left. exists FlowProspective. split; [right; reflexivity|].
      eapply frozen_caller_color_dangerous_reverse_rdm; eauto.
    + right. exists FlowProspective. split; [right; reflexivity|].
      eapply executing_authority_dangerous_reverse_rdm; eauto.
  - destruct (Hsource (or_introl eq_refl)) as
      [[old_mode [Hold_mode Hold_color]] |
       [active_mode [Hactive_mode Hactive_color]]].
    + left. exists FlowProspective. split; [right; reflexivity|].
      eapply frozen_caller_color_dangerous_reverse_rdm; eauto.
    + right. exists FlowProspective. split; [right; reflexivity|].
      eapply executing_authority_dangerous_reverse_rdm; eauto.
  - destruct Htarget_mode as [Hbad | Hbad]; discriminate.
  - destruct Htarget_mode as [Hbad | Hbad]; discriminate.
  - destruct (Hsource (or_introl eq_refl)) as
      [[old_mode [Hold_mode Hold_color]] |
       [active_mode [Hactive_mode Hactive_color]]].
    + left. exists FlowProspective. split; [right; reflexivity|].
      eapply frozen_caller_color_dangerous_frame_join;
        eauto.
    + right. exists FlowProspective. split; [right; reflexivity|].
      eapply executing_authority_dangerous_frame_join;
        eauto.
  - destruct (Hsource (or_intror eq_refl)) as
      [[old_mode [Hold_mode Hold_color]] |
       [active_mode [Hactive_mode Hactive_color]]].
    + left. exists FlowProspective. split; [right; reflexivity|].
      eapply frozen_caller_color_dangerous_frame_join;
        eauto.
    + right. exists FlowProspective. split; [right; reflexivity|].
      eapply executing_authority_dangerous_frame_join;
        eauto.
  - destruct Htarget_mode as [Hbad | Hbad]; discriminate.
  - destruct Htarget_mode as [Hbad | Hbad]; discriminate.
  - destruct Htarget_mode as [Hbad | Hbad]; discriminate.
  - destruct (Hsource (or_introl eq_refl)) as
      [[old_mode [[-> | ->] Hold_color]] |
       [active_mode [[-> | ->] Hactive_color]]].
    + left. exists FlowProspective. split; [right; reflexivity|].
      apply Hclosed. exists (FlowPowered, location). split; [exact Hold_color|].
      apply rt_step. apply frozen_caller_mark_prospective.
    + left. exists FlowProspective. split; [right; reflexivity|exact Hold_color].
    + right. exists FlowProspective. split; [right; reflexivity|].
      unfold independent_active_authority_colors in *.
      destruct Hactive_color as [seed [Hseed Hpath]]. exists seed.
      split; [exact Hseed|]. eapply rt_trans; [exact Hpath|].
      apply rt_step. apply phased_authority_mark_prospective.
    + right. exists FlowProspective. split; [right; reflexivity|].
      exact Hactive_color.
  - right. exists FlowPowered. split; [left; reflexivity|].
    unfold independent_active_authority_colors.
    apply executing_authority_owned_is_powered. exact H.
Qed.

Lemma phased_connected_with_frozen_incoming_covered_by_old_or_active :
  forall CT h frame colors source target,
    Included authority_flow_state
      (frozen_caller_authority_closure CT h frame colors) colors ->
    frozen_authority_state_covered_by_old_or_active colors
      (independent_active_authority_colors CT h frame) source ->
    phased_authority_frame_connected CT h frame source target ->
    frozen_authority_state_covered_by_old_or_active colors
      (independent_active_authority_colors CT h frame) target.
Proof.
  intros CT h frame colors source target Hclosed Hsource Hconnected.
  induction Hconnected.
  - eapply phased_step_with_frozen_incoming_covered_by_old_or_active; eauto.
  - exact Hsource.
  - apply IHHconnected2. apply IHHconnected1. exact Hsource.
Qed.

Lemma executing_with_frozen_incoming_dangerous_covered_by_old_or_active :
  forall CT h frame colors mode location,
    Included authority_flow_state
      (frozen_caller_authority_closure CT h frame colors) colors ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT h frame colors) (mode, location) ->
    (exists old_mode,
        authority_mode_dangerous old_mode /\
        In authority_flow_state colors (old_mode, location)) \/
    (exists active_mode,
        authority_mode_dangerous active_mode /\
        In authority_flow_state
          (independent_active_authority_colors CT h frame)
          (active_mode, location)).
Proof.
  intros CT h frame colors mode location Hclosed Hmode
    [seed [Hseed Hpath]].
  have Hsource : frozen_authority_state_covered_by_old_or_active colors
      (independent_active_authority_colors CT h frame) seed.
  { destruct seed as [seed_mode seed_location]. simpl in *.
    intros Hseed_mode. inversion Hseed; subst.
    - left. exists seed_mode. split; assumption.
    - destruct H as [owned [Heq Howned]]. inversion Heq; subst.
      right. exists FlowPowered. split; [left; reflexivity|].
      unfold independent_active_authority_colors.
      exists (FlowPowered, owned). split.
      + right. exists owned. split; [reflexivity|exact Howned].
      + apply rt_refl. }
  have Hcovered :=
    phased_connected_with_frozen_incoming_covered_by_old_or_active CT h frame
      colors seed (mode, location) Hclosed Hsource Hpath.
  exact (Hcovered Hmode).
Qed.

Lemma advance_frozen_caller_snapshots_after_safe_field_update_covered_by_old_or_active :
  forall CT h frame snapshots lx old field written,
    runtime_getObj h lx = Some old ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_closed CT h frame snapshots ->
    authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h frame) ->
    authority_safe_field_endpoints CT h frame lx written ->
    frozen_caller_snapshot_list_covered_by_old_or_active
      (independent_active_authority_colors CT h frame)
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame snapshots)
      snapshots.
Proof.
  intros CT h frame snapshots lx old field written Hobj Hruntime Hclosed
    Hactive_runtime Hendpoints new_snapshot Hnew.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot.
  exists old_snapshot. split; [exact Hold|].
  intros mode location Hmode [seed [Hseed Hpath]].
  destruct seed as [seed_mode seed_location]. simpl in *.
  have Hsource : frozen_authority_state_covered_by_old_or_active
      old_snapshot.(frozen_snapshot_current_colors)
      (independent_active_authority_colors CT h frame)
      (seed_mode, seed_location).
  { intros Hseed_mode. left. exists seed_mode.
    split; [exact Hseed_mode|exact Hseed]. }
  have Hcovered :=
    frozen_caller_connected_after_safe_field_update_covered_by_old_or_active
      CT h frame old_snapshot.(frozen_snapshot_current_colors) lx old field
      written (seed_mode, seed_location) (mode, location) Hobj
      (Hruntime old_snapshot Hold)
      (Hclosed old_snapshot Hold) Hactive_runtime Hendpoints Hsource Hpath.
  exact (Hcovered Hmode).
Qed.

Lemma principled_frozen_authority_after_safe_field_update :
  forall CT P Z cutoff frame stack incoming snapshots h lx old field written,
    principled_frozen_authority_history_state CT P Z cutoff frame stack
      incoming snapshots h ->
    runtime_getObj h lx = Some old ->
    authority_safe_field_endpoints CT h frame lx written ->
    principled_phased_authority_live_history_state CT P Z cutoff frame stack
      incoming (update_field h lx field (Iot written)) ->
    principled_frozen_authority_history_state CT P Z cutoff frame stack
      incoming
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame snapshots)
      (update_field h lx field (Iot written)).
Proof.
  intros CT P Z cutoff frame stack incoming snapshots h lx old field written
    [Hold [Haligned [Hruntime [Hclosed
      [Hretain [Hdangerous [Havoid [Hroots [Hexposure
        [Hresume [Hjoins [Hentry_covered Hphase_covered]]]]]]]]]]]]
    Hobj Hendpoints Hpost.
  set (h' := update_field h lx field (Iot written)).
  set (snapshots' := advance_frozen_caller_snapshots CT h' frame snapshots).
  have Hactive_runtime : authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h frame).
  { unfold independent_active_authority_colors.
    eapply executing_authority_colors_runtime_mutable.
    - exact (proj1 (proj1
        (proj2 (proj2 (proj2 (proj2 Hold)))))).
    - exact (proj1 (proj1 (proj2
        (proj2 (proj2 (proj2 (proj2 Hold))))))).
    - intros mode location Hempty. inversion Hempty. }
  have Hcovered : frozen_caller_snapshot_list_covered_by_old_or_active
      (independent_active_authority_colors CT h frame) snapshots' snapshots.
  { unfold snapshots', h'.
    eapply
      advance_frozen_caller_snapshots_after_safe_field_update_covered_by_old_or_active;
      eauto. }
  have Hmain_separated :=
    proj1 (proj2 (proj2 (proj2 Hold))).
  split; [exact Hpost|]. split.
  - unfold snapshots', frozen_caller_snapshots_aligned,
      advance_frozen_caller_snapshots. rewrite length_map. exact Haligned.
  - split.
    + unfold snapshots', h'.
      eapply advance_frozen_caller_snapshots_runtime_mutable.
      * exact (proj1 (proj1
           (proj2 (proj2 (proj2 (proj2 Hpost)))))).
      * eapply frozen_caller_snapshots_runtime_mutable_transport.
        -- intros location. apply r_muttype_update_field_preserve.
        -- exact Hruntime.
    + split.
      * unfold snapshots'. apply advance_frozen_caller_snapshots_closed.
      * split.
        -- unfold snapshots'.
           eapply advance_frozen_caller_snapshots_retain_entry. exact Hretain.
        -- split.
           ++ unfold snapshots'.
              eapply advance_frozen_caller_snapshots_dangerous.
              exact Hdangerous.
           ++ split.
              ** intros new_snapshot mode location Hnew Hmode Hcolor Hprotected.
                 destruct (Hcovered new_snapshot Hnew) as
                   [old_snapshot [Hold_snapshot Hcolors]].
                 destruct (Hcolors mode location Hmode Hcolor) as
                   [[old_mode [Hold_mode Hold_color]] |
                    [active_mode [Hactive_mode Hactive_color]]].
                 --- exact (Havoid old_snapshot old_mode location Hold_snapshot
                      Hold_mode Hold_color Hprotected).
                 --- eapply Hmain_separated;
                       [exact Hactive_mode| |exact Hprotected].
                     eapply independent_active_authority_colors_in_executing.
                     exact Hactive_color.
              ** split.
                 --- intros new_snapshot root Hnew Hroot.
                     unfold snapshots', advance_frozen_caller_snapshots in Hnew.
                     apply in_map_iff in Hnew.
                     destruct Hnew as [old_slot [Heq Hold_slot]].
                     destruct old_slot as [old_snapshot|]; simpl in Heq;
                       [|discriminate].
                     injection Heq as Heq. subst new_snapshot. simpl in Hroot.
                     unfold h'. rewrite update_field_length.
                     eapply Hroots; eauto.
                 --- split.
                     +++ split.
                         *** intros new_snapshot Hnew mode location Hcolor.
                             unfold snapshots', advance_frozen_caller_snapshots in Hnew.
                             apply in_map_iff in Hnew.
                             destruct Hnew as [old_slot [Heq Hold_slot]].
                             destruct old_slot as [old_snapshot|]; simpl in Heq;
                               [|discriminate].
                             injection Heq as Heq. subst new_snapshot. simpl in Hcolor.
                             eapply (advance_frozen_caller_snapshot_runtime_mutable
                               CT h' frame
                               old_snapshot.(frozen_snapshot_current_resume_exposure)).
                             ---- exact (proj1 (proj1
                               (proj2 (proj2 (proj2 (proj2 Hpost)))))).
                             ---- intros old_mode old_location Hold_color.
                                  unfold h'. rewrite r_muttype_update_field_preserve.
                                  eapply (proj1 Hexposure); eauto.
                             ---- exact Hcolor.
                         *** split.
                             ---- intros new_snapshot Hnew.
                                  unfold snapshots', advance_frozen_caller_snapshots in Hnew.
                                  apply in_map_iff in Hnew.
                                  destruct Hnew as [old_slot [Heq Hold_slot]].
                                  destruct old_slot as [old_snapshot|]; simpl in Heq;
                                    [|discriminate].
                                  injection Heq as Heq. subst new_snapshot. simpl.
                                  exact (proj1
                                    (frozen_caller_authority_closure_idempotent
                                      CT h' frame
                                      old_snapshot.(frozen_snapshot_current_resume_exposure))).
                             ---- split.
                                  ++++ intros new_snapshot mode location Hnew Hcolor.
                                  unfold snapshots', advance_frozen_caller_snapshots in Hnew.
                                  apply in_map_iff in Hnew.
                                  destruct Hnew as [old_slot [Heq Hold_slot]].
                                  destruct old_slot as [old_snapshot|]; simpl in Heq;
                                    [|discriminate].
                                  injection Heq as Heq. subst new_snapshot. simpl in Hcolor.
                                  destruct Hcolor as [seed [Hseed Hpath]].
                                  destruct seed as [seed_mode seed_location].
                                  have Hseed_mode : authority_mode_dangerous seed_mode by
                                    (eapply (proj1 (proj2 (proj2 Hexposure))); eauto).
                                  exact
                                    (frozen_caller_authority_connected_preserves_dangerous
                                      CT h' frame (seed_mode, seed_location)
                                      (mode, location) Hseed_mode Hpath).
                                  ++++ split.
                                       ***** intros new_snapshot Hnew state Hentry.
                                       unfold snapshots', advance_frozen_caller_snapshots in Hnew.
                                       apply in_map_iff in Hnew.
                                       destruct Hnew as [old_slot [Heq Hold_slot]].
                                       destruct old_slot as [old_snapshot|]; simpl in Heq;
                                         [|discriminate].
                                       injection Heq as Heq. subst new_snapshot. simpl in *.
                                       apply frozen_caller_authority_closure_contains.
                                            eapply (proj1 (proj2 (proj2
                                              (proj2 Hexposure)))); eauto.
                                       ***** intros new_snapshot root Hnew
                                               Hroot Hroot_runtime.
                                            unfold snapshots',
                                              advance_frozen_caller_snapshots in Hnew.
                                            apply in_map_iff in Hnew.
                                            destruct Hnew as
                                              [old_slot [Heq Hold_slot]].
                                            destruct old_slot as [old_snapshot|];
                                              simpl in Heq; [|discriminate].
                                            injection Heq as Heq.
                                            subst new_snapshot. simpl in *.
                                            apply frozen_caller_authority_closure_contains.
                                            eapply (proj2 (proj2 (proj2
                                              (proj2 Hexposure)))); eauto.
                                            unfold h' in Hroot_runtime.
                                            rewrite r_muttype_update_field_preserve
                                              in Hroot_runtime.
                                            exact Hroot_runtime.
                     +++ split.
                         *** intros new_snapshot active_mode source exposure_mode target
                           Hnew Hactive_mode Hactive Hsource Hexposure_mode
                           Htarget Hprotected.
                         unfold snapshots', advance_frozen_caller_snapshots in Hnew.
                         apply in_map_iff in Hnew.
                         destruct Hnew as [old_slot [Heq Hold_slot]].
                         destruct old_slot as [old_snapshot|]; simpl in Heq;
                           [|discriminate].
                         injection Heq as Heq. subst new_snapshot. simpl in *.
                         destruct
                           (executing_authority_colors_after_safe_field_update_covered
                             CT h frame (Empty_set authority_flow_state) lx old field
                             written Hobj Hactive_runtime Hendpoints active_mode source
                             Hactive_mode Hactive) as
                           [old_mode [Hold_mode Hold_active]].
                         destruct Htarget as [seed [Hseed Hpath]].
                         destruct seed as [seed_mode seed_location].
                         have Hsource_covered :
                             frozen_authority_state_covered_by_old_or_active
                               old_snapshot.(frozen_snapshot_current_resume_exposure)
                               (independent_active_authority_colors CT h frame)
                               (seed_mode, seed_location).
                         { intros Hseed_mode. left. exists seed_mode.
                           split; assumption. }
                         have Htarget_covered :=
                           frozen_caller_connected_after_safe_field_update_covered_by_old_or_active
                             CT h frame
                             old_snapshot.(frozen_snapshot_current_resume_exposure)
                             lx old field written (seed_mode, seed_location)
                             (exposure_mode, target) Hobj
                             ((proj1 Hexposure) old_snapshot Hold_slot)
                             ((proj1 (proj2 Hexposure)) old_snapshot Hold_slot)
                             Hactive_runtime Hendpoints Hsource_covered Hpath.
                         destruct (Htarget_covered Hexposure_mode) as
                           [[old_exposure_mode [Hold_exposure_mode Hold_target]] |
                            [target_active_mode [Htarget_active_mode Htarget_active]]].
                         ---- eapply Hresume with (snapshot := old_snapshot)
                               (active_mode := old_mode) (source := source)
                               (exposure_mode := old_exposure_mode); eauto.
                         ---- eapply Hmain_separated;
                               [exact Htarget_active_mode| |exact Hprotected].
                             eapply independent_active_authority_colors_in_executing.
                             exact Htarget_active.
                         *** split.
                             ---- intros new_snapshot source_mode source Hnew
                               Hsource_mode Hsource_color Hsource_root.
                             unfold snapshots', advance_frozen_caller_snapshots in Hnew.
                             apply in_map_iff in Hnew.
                             destruct Hnew as [old_slot [Heq Hold_slot]].
                             destruct old_slot as [old_snapshot|]; simpl in Heq;
                               [|discriminate].
                             injection Heq as Heq. subst new_snapshot. simpl in *.
                                  destruct Hsource_color as [seed [Hseed Hpath]].
                                  destruct seed as [seed_mode seed_location].
                                  have Hseed_covered :
                                 frozen_authority_state_covered_by_old_or_active
                                   old_snapshot.(frozen_snapshot_current_colors)
                                   (independent_active_authority_colors CT h frame)
                                   (seed_mode, seed_location).
                                  { intros Hseed_mode. left. exists seed_mode.
                                    split; assumption. }
                                  have Hsource_covered :=
                               frozen_caller_connected_after_safe_field_update_covered_by_old_or_active
                                 CT h frame
                                 old_snapshot.(frozen_snapshot_current_colors)
                                 lx old field written (seed_mode, seed_location)
                                 (source_mode, source) Hobj
                                 (Hruntime old_snapshot Hold_slot)
                                 (Hclosed old_snapshot Hold_slot)
                                 Hactive_runtime Hendpoints Hseed_covered Hpath.
                                  assert (Hclassify_target : forall exposure_mode target,
                                 authority_mode_dangerous exposure_mode ->
                                 In authority_flow_state
                                   (frozen_caller_authority_closure CT h' frame
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
                                     (independent_active_authority_colors CT h frame)
                                     (target_active_mode, target))).
                                  { intros exposure_mode target Hexposure_mode
                                 [target_seed [Htarget_seed Htarget_path]].
                               destruct target_seed as
                                 [target_seed_mode target_seed_location].
                               have Htarget_seed_covered :
                                   frozen_authority_state_covered_by_old_or_active
                                     old_snapshot.(frozen_snapshot_current_resume_exposure)
                                     (independent_active_authority_colors CT h frame)
                                     (target_seed_mode, target_seed_location).
                               { intros Htarget_seed_mode. left.
                                 exists target_seed_mode. split; assumption. }
                               have Htarget_covered :=
                                 frozen_caller_connected_after_safe_field_update_covered_by_old_or_active
                                   CT h frame
                                   old_snapshot.(frozen_snapshot_current_resume_exposure)
                                   lx old field written
                                   (target_seed_mode, target_seed_location)
                                   (exposure_mode, target) Hobj
                                   ((proj1 Hexposure) old_snapshot Hold_slot)
                                   ((proj1 (proj2 Hexposure)) old_snapshot Hold_slot)
                                   Hactive_runtime Hendpoints Htarget_seed_covered
                                   Htarget_path.
                                    exact (Htarget_covered Hexposure_mode). }
                                  destruct (Hsource_covered Hsource_mode) as
                               [[old_source_mode [Hold_source_mode Hold_source]] |
                                [active_source_mode
                                  [Hactive_source_mode Hactive_source]]].
                                  ++++ destruct (Hjoins old_snapshot old_source_mode source
                                    Hold_slot Hold_source_mode Hold_source Hsource_root) as
                                    [[entry_mode [Hentry_mode Hentry]] | Hsafe].
                                       ***** left. exists entry_mode. split; assumption.
                                       ***** right. intros exposure_mode target
                                         Hexposure_mode Htarget Hprotected.
                                       destruct (Hclassify_target exposure_mode target
                                         Hexposure_mode Htarget) as
                                         [[old_exposure_mode
                                             [Hold_exposure_mode Hold_target]] |
                                          [target_active_mode
                                             [Htarget_active_mode Htarget_active]]].
                                            +++++ exact (Hsafe old_exposure_mode target
                                               Hold_exposure_mode Hold_target Hprotected).
                                            +++++ eapply Hmain_separated;
                                               [exact Htarget_active_mode| |exact Hprotected].
                                             eapply independent_active_authority_colors_in_executing.
                                             exact Htarget_active.
                                  ++++ right. intros exposure_mode target Hexposure_mode
                                    Htarget Hprotected.
                                  destruct (Hclassify_target exposure_mode target
                                    Hexposure_mode Htarget) as
                                    [[old_exposure_mode
                                        [Hold_exposure_mode Hold_target]] |
                                     [target_active_mode
                                        [Htarget_active_mode Htarget_active]]].
                                       ***** eapply Hresume with (snapshot := old_snapshot)
                                         (active_mode := active_source_mode)
                                         (source := source)
                                         (exposure_mode := old_exposure_mode); eauto.
                                       ***** eapply Hmain_separated;
                                         [exact Htarget_active_mode| |exact Hprotected].
                                       eapply independent_active_authority_colors_in_executing.
                                            exact Htarget_active.
                             ---- split.
                                  ++++ apply advance_frozen_caller_snapshots_entry_exposure_covered.
                                       exact Hentry_covered.
                                  ++++ apply advance_frozen_caller_snapshots_cover_phase_incoming.
                                       exact Hphase_covered.
Qed.

Lemma entry_ownership_channel_free_has_no_frame_owned_location :
  forall CT h boundary owned,
    entry_ownership_channel_free boundary ->
    ~ frame_owned_location CT h
        (mk_watched_frame
          (call_authority boundary.(boundary_caller).(frame_authority)
            boundary.(boundary_receiver_view))
          boundary.(boundary_callee_entry_senv)
          boundary.(boundary_callee_entry_renv)) owned.
Proof.
  intros CT h boundary owned [Hno_capability Hno_rdm]
    [root [Hroot Hreachable]].
  exact (Hno_capability root Hroot).
Qed.

Lemma channel_free_entry_has_no_independent_active_authority_color :
  forall CT h boundary state,
    entry_ownership_channel_free boundary ->
    ~ In authority_flow_state
        (independent_active_authority_colors CT h
          (mk_watched_frame
            (call_authority boundary.(boundary_caller).(frame_authority)
              boundary.(boundary_receiver_view))
            boundary.(boundary_callee_entry_senv)
            boundary.(boundary_callee_entry_renv))) state.
Proof.
  intros CT h boundary state Hfree [seed [Hseed Hpath]].
  inversion Hseed; subst.
  - inversion H.
  - destruct H as [location [Heq Howned]].
    eapply entry_ownership_channel_free_has_no_frame_owned_location;
      [exact Hfree|exact Howned].
Qed.

Lemma enter_frozen_caller_snapshots_aligned :
  forall CT h caller callee caller_colors snapshots boundary stack,
    frozen_caller_snapshots_aligned snapshots stack ->
    frozen_caller_snapshots_aligned
      (enter_frozen_caller_snapshots CT h caller callee caller_colors snapshots)
      (boundary :: stack).
Proof.
  intros CT h caller callee caller_colors snapshots boundary stack Haligned.
  unfold frozen_caller_snapshots_aligned in *.
  unfold enter_frozen_caller_snapshots,
    advance_frozen_caller_snapshots. simpl.
  f_equal. rewrite length_map. exact Haligned.
Qed.

Lemma frame_resume_exposure_colors_runtime_mutable :
  forall CT h frame,
    wf_r_config CT frame.(frame_senv) frame.(frame_renv) h ->
    authority_colors_runtime_mutable h
      (frame_resume_exposure_colors CT h frame).
Proof.
  intros CT h frame Hwf.
  unfold frame_resume_exposure_colors.
  eapply advance_frozen_caller_snapshot_runtime_mutable; [exact Hwf|].
  intros mode location [root [Hroot [Hruntime Heq]]].
  inversion Heq; subst. exact Hruntime.
Qed.

Lemma frozen_caller_authority_closure_dangerous :
  forall CT h frame colors,
    (forall mode location,
      In authority_flow_state colors (mode, location) ->
      authority_mode_dangerous mode) ->
    forall mode location,
      In authority_flow_state
        (frozen_caller_authority_closure CT h frame colors)
        (mode, location) ->
      authority_mode_dangerous mode.
Proof.
  intros CT h frame colors Hdangerous mode location
    [seed [Hseed Hpath]].
  destruct seed as [seed_mode seed_location].
  exact (frozen_caller_authority_connected_preserves_dangerous CT h frame
    (seed_mode, seed_location) (mode, location)
    (Hdangerous seed_mode seed_location Hseed) Hpath).
Qed.

Lemma frame_resume_exposure_colors_dangerous :
  forall CT h frame mode location,
    In authority_flow_state (frame_resume_exposure_colors CT h frame)
      (mode, location) ->
    authority_mode_dangerous mode.
Proof.
  intros CT h frame. unfold frame_resume_exposure_colors.
  eapply frozen_caller_authority_closure_dangerous.
  intros mode location [root [Hroot [Hruntime Heq]]].
  inversion Heq; subst. right. reflexivity.
Qed.

Lemma frame_resume_exposure_contains_mutable_rdm_root :
  forall CT h frame root,
    In Loc (frame_rdm_root_set frame) root ->
    r_muttype h root = Some Mut_r ->
    In authority_flow_state (frame_resume_exposure_colors CT h frame)
      (FlowProspective, root).
Proof.
  intros CT h frame root Hroot Hruntime.
  unfold frame_resume_exposure_colors.
  apply frozen_caller_authority_closure_contains.
  exists root. repeat split; assumption.
Qed.

Lemma tracked_snapshot_active_resume_exposure_avoids_protected :
  forall CT P Z cutoff active boundary stack incoming snapshot snapshots h
    active_mode source exposure_mode target,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some snapshot :: snapshots) h ->
    authority_mode_dangerous active_mode ->
    In authority_flow_state
      (independent_active_authority_colors CT h active)
      (active_mode, source) ->
    In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
    authority_mode_dangerous exposure_mode ->
    In authority_flow_state
      snapshot.(frozen_snapshot_current_resume_exposure)
      (exposure_mode, target) ->
    ~ In Loc Z target.
Proof.
  intros CT P Z cutoff active boundary stack incoming snapshot snapshots h
    active_mode source exposure_mode target
    [Hmain [Haligned [Hruntime [Hclosed [Hretain [Hdangerous
      [Havoid [Hroots [Hexposure
        [Hresume [Hjoins [Hentry_covered Hphase_covered]]]]]]]]]]]]
    Hactive_mode Hactive Hsource Hexposure_mode Htarget.
  eapply Hresume with (snapshot := snapshot) (active_mode := active_mode)
    (source := source) (exposure_mode := exposure_mode); eauto.
  simpl. left. reflexivity.
Qed.

Lemma tracked_snapshot_resume_exposure_avoids_protected :
  forall CT P Z cutoff active boundary stack incoming snapshot snapshots h
    source_mode source exposure_mode target,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some snapshot :: snapshots) h ->
    authority_mode_dangerous source_mode ->
    In authority_flow_state snapshot.(frozen_snapshot_current_colors)
      (source_mode, source) ->
    In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
    authority_mode_dangerous exposure_mode ->
    In authority_flow_state
      snapshot.(frozen_snapshot_current_resume_exposure)
      (exposure_mode, target) ->
    ~ In Loc Z target.
Proof.
  intros CT P Z cutoff active boundary stack incoming snapshot snapshots h
    source_mode source exposure_mode target
    [Hmain [Haligned [Hruntime [Hclosed [Hretain [Hdangerous
      [Havoid [Hroots [Hexposure
        [Hresume [Hjoins [Hentry_covered Hphase_covered]]]]]]]]]]]]
    Hsource_mode Hsource Hsource_root Hexposure_mode Htarget.
  have Hsnapshot : List.In (Some snapshot) (Some snapshot :: snapshots) by
    (simpl; left; reflexivity).
  destruct (Hjoins snapshot source_mode source Hsnapshot Hsource_mode
    Hsource Hsource_root) as
    [[entry_mode [Hentry_mode Hentry]] | Hsafe].
  - eapply Havoid with (snapshot := snapshot) (mode := exposure_mode).
    + exact Hsnapshot.
    + exact Hexposure_mode.
    + eapply (Hentry_covered snapshot entry_mode source Hsnapshot
        Hentry_mode Hentry Hsource_root). exact Htarget.
  - eapply Hsafe; eauto.
Qed.

Lemma retained_reachable_reflects_runtime_context_private :
  forall CT h source target runtime_q,
    wf_heap CT h ->
    retained_mut_reachable CT h source target ->
    r_muttype h target = Some runtime_q ->
    r_muttype h source = Some runtime_q.
Proof.
  intros CT h source target runtime_q Hheap Hreachable Htarget.
  induction Hreachable.
  - exact Htarget.
  - apply IHHreachable.
    eapply retained_edge_reflects_runtime_mutability; eauto.
Qed.

Lemma retained_reachable_preserves_runtime_context_private :
  forall CT h source target runtime_q,
    wf_heap CT h ->
    retained_mut_reachable CT h source target ->
    r_muttype h source = Some runtime_q ->
    r_muttype h target = Some runtime_q.
Proof.
  intros CT h source target runtime_q Hheap Hreachable Hsource.
  induction Hreachable.
  - exact Hsource.
  - have Hmiddle := IHHreachable Hsource.
    have Hedge_copy := H.
    destruct H.
    + eapply mutable_edge_preserves_runtime_mutability; eauto.
    + assert (runtime_q = Mut_r) by congruence. subst runtime_q.
      eapply retained_edge_preserves_runtime_mutability; eauto.
Qed.

Lemma active_mutable_authority_components_after_assignment :
  forall CT cutoff authority sGamma mt rGamma h x expression old value,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SVarAss x expression) sGamma ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma x = Some old ->
    eval_expr CT rGamma h expression value OK rGamma h ->
    active_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame authority sGamma rGamma) ->
    active_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame authority sGamma
        (update_r_env_value rGamma x value)).
Proof.
  intros CT cutoff authority sGamma mt rGamma h x expression old value Hwf
    Htyping Hscope Hvalue Heval Hold root target Hreachable.
  inversion Hreachable; subst.
  - destruct H as
      [variable [T [Htype [Hroot_value [Hmut | [Hrdm Hauthority]]]]]].
    + have Hnew_root : typed_root Mut sGamma
          (update_r_env_value rGamma x value) root.
      { exists variable, T. repeat split; assumption. }
      destruct (assignment_mut_root_has_old_ancestor CT sGamma mt rGamma h x
        expression old value Hwf Htyping Hscope Hvalue Heval root Hnew_root)
        as [old_root [Hold_root Hold_to_root]].
      have Hold_runtime : r_muttype h old_root = Some Mut_r.
      { eapply retained_reachable_reflects_runtime_context_private;
          [exact (proj1 (proj2 Hwf))|exact Hold_to_root|exact H0]. }
      eapply Hold with (root := old_root).
      apply mutable_authority_reachable_capability.
      * destruct Hold_root as
          [old_variable [old_T [Hold_type [Hold_value Hold_mut]]]].
        exists old_variable, old_T. repeat split; try assumption.
        unfold capability_in_context. left. exact Hold_mut.
      * exact Hold_runtime.
      * eapply retained_mut_reachable_transitive; eauto.
    + have Hnew_root : typed_root RDM sGamma
          (update_r_env_value rGamma x value) root.
      { exists variable, T. repeat split; assumption. }
      destruct (assignment_rdm_root_has_old_ancestor CT sGamma mt rGamma h x
        expression old value Hwf Htyping Hscope Hvalue Heval root Hnew_root)
        as [old_root [Hold_root Hold_to_root]].
      have Hroot_to_old : mutable_connected CT h root old_root.
      { eapply mutable_connected_sym.
        eapply mutable_reachable_connected. exact Hold_to_root. }
      have Hold_runtime : r_muttype h old_root = Some Mut_r.
      { eapply mutable_connected_preserves_runtime_mutability;
          [exact (proj1 (proj2 Hwf))|exact Hroot_to_old|exact H0]. }
      eapply Hold with (root := old_root).
      apply mutable_authority_reachable_capability.
      * destruct Hold_root as
          [old_variable [old_T [Hold_type [Hold_value Hold_rdm]]]].
        exists old_variable, old_T. repeat split; try assumption.
        unfold capability_in_context. right. split; assumption.
      * exact Hold_runtime.
      * eapply retained_mut_reachable_transitive.
        -- apply mutable_reachable_is_retained. exact Hold_to_root.
        -- exact H1.
  - destruct (assignment_rdm_root_has_old_ancestor CT sGamma mt rGamma h x
      expression old value Hwf Htyping Hscope Hvalue Heval root H) as
      [old_root [Hold_root Hold_to_root]].
    have Hroot_to_old : mutable_connected CT h root old_root.
    { eapply mutable_connected_sym.
      eapply mutable_reachable_connected. exact Hold_to_root. }
    have Hold_runtime : r_muttype h old_root = Some Mut_r.
    { eapply mutable_connected_preserves_runtime_mutability;
        [exact (proj1 (proj2 Hwf))|exact Hroot_to_old|exact H0]. }
    apply (Hold old_root target).
    apply mutable_authority_reachable_rdm; [exact Hold_root|exact Hold_runtime|].
    eapply retained_mut_reachable_transitive.
    + apply mutable_reachable_is_retained. exact Hold_to_root.
    + exact H1.
Qed.

Lemma live_mutable_authority_components_after_assignment :
  forall CT cutoff authority sGamma mt rGamma h stack x expression old value,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SVarAss x expression) sGamma ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma x = Some old ->
    eval_expr CT rGamma h expression value OK rGamma h ->
    live_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame authority sGamma rGamma) stack ->
    live_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame authority sGamma
        (update_r_env_value rGamma x value)) stack.
Proof.
  intros CT cutoff authority sGamma mt rGamma h stack x expression old value
    Hwf Htyping Hscope Hvalue Heval Hold frame root target Hlive Hreachable.
  inversion Hlive; subst.
  - have Hactive := active_mutable_authority_components_after_assignment CT
      cutoff authority sGamma mt rGamma h x expression old value Hwf Htyping
      Hscope Hvalue Heval
      (live_mutable_authority_components_active CT h cutoff
        (mk_watched_frame authority sGamma rGamma) stack Hold).
    eapply Hactive. exact Hreachable.
  - eapply Hold; eauto. constructor. exact H.
Qed.

Lemma active_mutable_authority_components_after_local :
  forall CT cutoff authority sGamma mt rGamma h T x sGamma',
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SLocal T x) sGamma' ->
    runtime_getVal rGamma x = None ->
    active_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame authority sGamma rGamma) ->
    active_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame authority sGamma'
        (set_vars rGamma (vars rGamma ++ [Null_a]))).
Proof.
  intros CT cutoff authority sGamma mt rGamma h T x sGamma' Hwf Htyping
    Hnone Hold root target Hreachable.
  inversion Htyping; subst.
  unfold wf_r_config in Hwf.
  destruct Hwf as [Hheap [Hreceiver [Hdom [Htypes [Hlength Hcorr]]]]].
  inversion Hreachable; subst.
  - destruct H as [variable [root_T [Htype [Hvalue Hcapability]]]].
    destruct (appended_null_nonnull_lookup_is_old sGamma rGamma T variable
      root_T root Hlength Htype Hvalue) as [Hold_type Hold_value].
    eapply Hold with (root := root).
    apply mutable_authority_reachable_capability.
    + exists variable, root_T. repeat split; assumption.
    + exact H0.
    + exact H1.
  - destruct H as [variable [root_T [Htype [Hvalue Hqualifier]]]].
    destruct (appended_null_nonnull_lookup_is_old sGamma rGamma T variable
      root_T root Hlength Htype Hvalue) as [Hold_type Hold_value].
    eapply Hold with (root := root).
    apply mutable_authority_reachable_rdm.
    + exists variable, root_T. repeat split; assumption.
    + exact H0.
    + exact H1.
Qed.

Lemma live_mutable_authority_components_after_local :
  forall CT cutoff authority sGamma mt rGamma h stack T x sGamma',
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SLocal T x) sGamma' ->
    runtime_getVal rGamma x = None ->
    live_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame authority sGamma rGamma) stack ->
    live_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame authority sGamma'
        (set_vars rGamma (vars rGamma ++ [Null_a]))) stack.
Proof.
  intros CT cutoff authority sGamma mt rGamma h stack T x sGamma' Hwf
    Htyping Hnone Hold frame root target Hlive Hreachable.
  inversion Hlive; subst.
  - have Hactive := active_mutable_authority_components_after_local CT cutoff
      authority sGamma mt rGamma h T x sGamma' Hwf Htyping Hnone
      (live_mutable_authority_components_active CT h cutoff
        (mk_watched_frame authority sGamma rGamma) stack Hold).
    eapply Hactive. exact Hreachable.
  - eapply Hold; eauto. constructor. exact H.
Qed.

(** Boundary-local freshness for the authority-flow graph after a typed
    field update.  Unlike the older RDM-only lemma, this follows the retained
    suffix used by both powered and prospective colors.  The proof is still
    entirely internal: the endpoint classification is derived from typing
    by the atomic statement wrapper. *)
Lemma live_mutable_authority_components_after_safe_field_update :
  forall CT cutoff frame stack h lx old field written,
    wf_r_config CT frame.(frame_senv) frame.(frame_renv) h ->
    authority_context_sound h frame.(frame_renv) frame.(frame_authority) ->
    live_mutable_authority_components_after_cutoff CT h cutoff frame stack ->
    runtime_getObj h lx = Some old ->
    authority_safe_field_endpoints CT h frame lx written ->
    live_mutable_authority_components_after_cutoff CT
      (update_field h lx field (Iot written)) cutoff frame stack.
Proof.
  intros CT cutoff frame stack h lx old field written Hwf Hsound Hold Hobj
    Hendpoints live root target Hlive Hreachable.
  have Hheap := proj1 (proj2 Hwf).
  inversion Hreachable; subst.
  - have Hroot_runtime_old : r_muttype h root = Some Mut_r.
    { rewrite r_muttype_update_field_preserve in H0. exact H0. }
    destruct (retained_reachable_after_field_update CT h lx old field
      (Iot written) root target Hobj H1) as
      [Hold_path | [new_written [Hvalue [Hroot_lx Hwritten_target]]]].
    + eapply Hold with (frame := live) (root := root).
      * exact Hlive.
      * apply mutable_authority_reachable_capability.
        -- exact H.
        -- exact Hroot_runtime_old.
        -- exact Hold_path.
    + injection Hvalue as <-.
      have Hlx_runtime : r_muttype h lx = Some Mut_r.
      { eapply retained_reachable_preserves_runtime_context_private;
          eauto. }
      have Hlx_fresh : cutoff <= lx.
      { eapply Hold with (frame := live) (root := root).
        - exact Hlive.
        - apply mutable_authority_reachable_capability.
          + exact H.
          + exact Hroot_runtime_old.
          + exact Hroot_lx. }
      inversion Hendpoints; subst.
      * destruct H3 as [owner [Howner Howner_written]].
        have Howner_runtime : r_muttype h owner = Some Mut_r.
        { eapply frame_capability_root_runtime_mutable; eauto. }
        eapply Hold with (frame := frame) (root := owner).
        -- constructor.
        -- apply mutable_authority_reachable_capability; try assumption.
           eapply retained_mut_reachable_transitive; eauto.
      * rewrite H2 in Hlx_runtime. discriminate.
      * have Hcontexts := active_rdm_roots_share_runtime_context CT
          frame.(frame_senv) frame.(frame_renv) h lx written Hwf
          H2 H3.
        destruct Hcontexts as [runtime_q [Hlx_context Hwritten_context]].
        rewrite Hlx_runtime in Hlx_context. injection Hlx_context as <-.
        eapply Hold with (frame := frame) (root := written).
        -- constructor.
        -- apply mutable_authority_reachable_rdm; assumption.
  - have Hroot_runtime_old : r_muttype h root = Some Mut_r.
    { rewrite r_muttype_update_field_preserve in H0. exact H0. }
    destruct (retained_reachable_after_field_update CT h lx old field
      (Iot written) root target Hobj H1) as
      [Hold_path | [new_written [Hvalue [Hroot_lx Hwritten_target]]]].
    + eapply Hold with (frame := live) (root := root).
      * exact Hlive.
      * apply mutable_authority_reachable_rdm.
        -- exact H.
        -- exact Hroot_runtime_old.
        -- exact Hold_path.
    + injection Hvalue as <-.
      have Hlx_runtime : r_muttype h lx = Some Mut_r.
      { eapply retained_reachable_preserves_runtime_context_private;
          eauto. }
      have Hlx_fresh : cutoff <= lx.
      { eapply Hold with (frame := live) (root := root).
        - exact Hlive.
        - apply mutable_authority_reachable_rdm.
          + exact H.
          + exact Hroot_runtime_old.
          + exact Hroot_lx. }
      inversion Hendpoints; subst.
      * destruct H3 as [owner [Howner Howner_written]].
        have Howner_runtime : r_muttype h owner = Some Mut_r.
        { eapply frame_capability_root_runtime_mutable; eauto. }
        eapply Hold with (frame := frame) (root := owner).
        -- constructor.
        -- apply mutable_authority_reachable_capability; try assumption.
           eapply retained_mut_reachable_transitive; eauto.
      * rewrite H2 in Hlx_runtime. discriminate.
      * have Hcontexts := active_rdm_roots_share_runtime_context CT
          frame.(frame_senv) frame.(frame_renv) h lx written Hwf
          H2 H3.
        destruct Hcontexts as [runtime_q [Hlx_context Hwritten_context]].
        rewrite Hlx_runtime in Hlx_context. injection Hlx_context as <-.
        eapply Hold with (frame := frame) (root := written).
        -- constructor.
        -- apply mutable_authority_reachable_rdm; assumption.
Qed.

Lemma retained_reachable_after_graph_reflection_private :
  forall CT h h' source target,
    (forall left right,
      retained_mut_edge CT h' left right ->
      retained_mut_edge CT h left right) ->
    retained_mut_reachable CT h' source target ->
    retained_mut_reachable CT h source target.
Proof.
  intros CT h h' source target Hedges Hreachable.
  induction Hreachable.
  - constructor.
  - eapply rmr_step; eauto.
Qed.

Lemma live_mutable_authority_components_after_graph_reflection :
  forall CT h h' cutoff active stack,
    (forall location, r_muttype h' location = r_muttype h location) ->
    (forall left right,
      retained_mut_edge CT h' left right ->
      retained_mut_edge CT h left right) ->
    live_mutable_authority_components_after_cutoff CT h cutoff active stack ->
    live_mutable_authority_components_after_cutoff CT h' cutoff active stack.
Proof.
  intros CT h h' cutoff active stack Hruntimes Hedges Hold frame root target
    Hlive Hreachable.
  inversion Hreachable; subst.
  - eapply Hold with (frame := frame) (root := root); [exact Hlive|].
    apply mutable_authority_reachable_capability.
    + exact H.
    + rewrite <- Hruntimes. exact H0.
    + eapply retained_reachable_after_graph_reflection_private; eauto.
  - eapply Hold with (frame := frame) (root := root); [exact Hlive|].
    apply mutable_authority_reachable_rdm.
    + exact H.
    + rewrite <- Hruntimes. exact H0.
    + eapply retained_reachable_after_graph_reflection_private; eauto.
Qed.

Lemma live_prospective_mutable_authority_components_after_graph_reflection :
  forall CT old_h new_h cutoff active stack,
    (forall location, r_muttype new_h location = r_muttype old_h location) ->
    (forall left right,
      retained_mut_edge CT new_h left right ->
      retained_mut_edge CT old_h left right) ->
    (forall left right,
      mutable_edge CT new_h left right ->
      mutable_edge CT old_h left right) ->
    live_prospective_mutable_authority_components_after_cutoff CT old_h cutoff
      active stack ->
    live_prospective_mutable_authority_components_after_cutoff CT new_h cutoff
      active stack.
Proof.
  intros CT old_h new_h cutoff active stack Hruntimes Hretained Hmutable Hold
    frame root target Hlive [Hroot Hpath].
  destruct Hroot as [Hmut | [Hrdm Hruntime]].
  - apply (Hold frame root target Hlive).
    split.
    + left. exact Hmut.
    + eapply frozen_caller_connected_after_graph_reflection; eauto.
  - apply (Hold frame root target Hlive).
    split.
    + right. split; [exact Hrdm|]. rewrite <- Hruntimes. exact Hruntime.
    + eapply frozen_caller_connected_after_graph_reflection; eauto.
Qed.

Lemma potential_frame_edge_symmetric :
  forall active stack left right,
    potential_frame_edge active stack left right ->
    potential_frame_edge active stack right left.
Proof.
  intros active stack left right [frame [Hlive [Hleft Hright]]].
  exists frame. repeat split; assumption.
Qed.

Lemma potential_return_edge_symmetric :
  forall h active stack left right,
    potential_return_edge h active stack left right ->
    potential_return_edge h active stack right left.
Proof.
  intros h active stack left right
    [callee [boundary [Hlive [Hview
      [Hcallee_return [Hruntime [Hroots | Hroots]]]]]]].
  - exists callee, boundary. repeat split; try assumption.
    + symmetry. exact Hruntime.
    + right. destruct Hroots as [Hleft Hright]. split; assumption.
  - exists callee, boundary. repeat split; try assumption.
    + symmetry. exact Hruntime.
    + left. destruct Hroots as [Hleft Hright]. split; assumption.
Qed.

Lemma staged_frame_connected_refl :
  forall CT h frame location,
    staged_frame_connected CT h frame location location.
Proof. intros. apply rt_refl. Qed.

Lemma staged_frame_connected_trans :
  forall CT h frame first middle last,
    staged_frame_connected CT h frame first middle ->
    staged_frame_connected CT h frame middle last ->
    staged_frame_connected CT h frame first last.
Proof. intros. eapply rt_trans; eauto. Qed.

Lemma mutable_reachable_is_staged_frame_connected :
  forall CT h frame left right,
    mutable_reachable CT h left right ->
    staged_frame_connected CT h frame left right.
Proof.
  intros CT h frame left right Hreachable.
  induction Hreachable.
  - apply rt_refl.
  - eapply rt_trans; [exact IHHreachable|].
    apply rt_step. left. left. constructor. exact H.
Qed.

Lemma mutable_reachable_is_reverse_staged_frame_connected :
  forall CT h frame left right,
    mutable_reachable CT h left right ->
    staged_frame_connected CT h frame right left.
Proof.
  intros CT h frame left right Hreachable.
  induction Hreachable.
  - apply rt_refl.
  - eapply rt_trans.
    + apply rt_step. left. right. exact H.
    + exact IHHreachable.
Qed.

Lemma retained_reachable_is_staged_frame_connected :
  forall CT h frame left right,
    retained_mut_reachable CT h left right ->
    staged_frame_connected CT h frame left right.
Proof.
  intros CT h frame left right Hreachable.
  induction Hreachable.
  - apply rt_refl.
  - eapply rt_trans; [exact IHHreachable|].
    apply rt_step. left. left. exact H.
Qed.

Lemma staged_frame_closure_contains :
  forall CT h frame seeds,
    Included Loc seeds (staged_frame_closure CT h frame seeds).
Proof.
  intros CT h frame seeds location Hlocation.
  exists location. split; [exact Hlocation|apply rt_refl].
Qed.

Lemma staged_frame_closure_monotone :
  forall CT h frame old new,
    Included Loc old new ->
    Included Loc
      (staged_frame_closure CT h frame old)
      (staged_frame_closure CT h frame new).
Proof.
  intros CT h frame old new Hincluded location
    [seed [Hseed Hconnected]].
  exists seed. split; [apply Hincluded; exact Hseed|exact Hconnected].
Qed.

Lemma staged_return_closure_monotone :
  forall h callee boundary old new,
    Included Loc old new ->
    Included Loc
      (staged_return_closure h callee boundary old)
      (staged_return_closure h callee boundary new).
Proof.
  intros h callee boundary old new Hincluded location
    [seed [Hseed Hconnected]].
  exists seed. split; [apply Hincluded; exact Hseed|exact Hconnected].
Qed.

Lemma layered_color_adjacent_symmetric :
  forall CT h active stack left right,
    layered_color_adjacent CT h active stack left right ->
    layered_color_adjacent CT h active stack right left.
Proof.
  intros CT h active stack left right
    [Hmutable | [Hframe | Hreturn]].
  - left. eapply mutable_adjacent_symmetric; eauto.
  - right. left. eapply potential_frame_edge_symmetric; eauto.
  - right. right. eapply potential_return_edge_symmetric; eauto.
Qed.

Lemma layered_color_connected_sym :
  forall CT h active stack left right,
    layered_color_connected CT h active stack left right ->
    layered_color_connected CT h active stack right left.
Proof.
  intros CT h active stack left right Hconnected.
  induction Hconnected.
  - apply rt_step. eapply layered_color_adjacent_symmetric; eauto.
  - apply rt_refl.
  - eapply rt_trans; [exact IHHconnected2|exact IHHconnected1].
Qed.

Lemma mutable_connected_is_layered_color_connected :
  forall CT h active stack left right,
    mutable_connected CT h left right ->
    layered_color_connected CT h active stack left right.
Proof.
  intros CT h active stack left right Hconnected.
  induction Hconnected.
  - apply rt_step. left. exact H.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma mutable_reachable_is_layered_color_connected :
  forall CT h active stack left right,
    mutable_reachable CT h left right ->
    layered_color_connected CT h active stack left right.
Proof.
  intros. eapply mutable_connected_is_layered_color_connected.
  eapply mutable_reachable_connected; eauto.
Qed.

Lemma potential_connected_refl :
  forall CT h active stack location,
    potential_connected CT h active stack location location.
Proof. intros. apply rt_refl. Qed.

Lemma potential_connected_trans :
  forall CT h active stack first middle last,
    potential_connected CT h active stack first middle ->
    potential_connected CT h active stack middle last ->
    potential_connected CT h active stack first last.
Proof. intros. eapply rt_trans; eauto. Qed.

Lemma authority_color_connected_trans :
  forall CT h active stack first middle last,
    authority_color_connected CT h active stack first middle ->
    authority_color_connected CT h active stack middle last ->
    authority_color_connected CT h active stack first last.
Proof. intros. eapply rt_trans; eauto. Qed.

Lemma authority_color_connected_is_potential_connected :
  forall CT h active stack left right,
    authority_color_connected CT h active stack left right ->
    potential_connected CT h active stack left right.
Proof.
  intros CT h active stack left right Hconnected.
  induction Hconnected.
  - apply rt_step. destruct H as [Hheap | Hframe].
    + left. exact Hheap.
    + right. left. exact Hframe.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma mutable_connected_is_authority_color_connected :
  forall CT h active stack left right,
    mutable_connected CT h left right ->
    authority_color_connected CT h active stack left right.
Proof.
  intros CT h active stack left right Hconnected.
  induction Hconnected.
  - apply rt_step. left.
    destruct H as [Hforward | Hbackward].
    + left. constructor. exact Hforward.
    + right. exact Hbackward.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma mutable_connected_is_potential_connected :
  forall CT h active stack left right,
    mutable_connected CT h left right ->
    potential_connected CT h active stack left right.
Proof.
  intros CT h active stack left right Hconnected.
  induction Hconnected.
  - apply rt_step. left. destruct H as [Hforward | Hbackward].
    + left. constructor. exact Hforward.
    + right. exact Hbackward.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma mutable_reachable_is_reverse_potential_connected :
  forall CT h active stack source target,
    mutable_reachable CT h source target ->
    potential_connected CT h active stack target source.
Proof.
  intros CT h active stack source target Hreachable.
  apply mutable_connected_is_potential_connected.
  apply mutable_connected_sym.
  eapply mutable_reachable_connected; eauto.
Qed.

Lemma retained_reachable_is_potential_connected :
  forall CT h active stack source target,
    retained_mut_reachable CT h source target ->
    potential_connected CT h active stack source target.
Proof.
  intros CT h active stack source target Hreachable.
  induction Hreachable.
  - apply rt_refl.
  - eapply rt_trans; [exact IHHreachable|].
    apply rt_step. left. left. exact H.
Qed.

Lemma live_frame_rdm_roots_potentially_connected :
  forall CT h active stack frame left right,
    live_frame_member active stack frame ->
    typed_root RDM frame.(frame_senv) frame.(frame_renv) left ->
    typed_root RDM frame.(frame_senv) frame.(frame_renv) right ->
    potential_connected CT h active stack left right.
Proof.
  intros CT h active stack frame left right Hlive Hleft Hright.
  apply rt_step. right. left. exists frame. split; [exact Hlive|].
  split; assumption.
Qed.

Lemma potential_return_edge_preserves_runtime_mutability :
  forall h active stack left right runtime_q,
    potential_return_edge h active stack left right ->
    r_muttype h left = Some runtime_q ->
    r_muttype h right = Some runtime_q.
Proof.
  intros h active stack left right runtime_q
    [callee [boundary
      [Hlive [Hview [Hcallee_return [Hruntime Hroots]]]]]] Hleft.
  rewrite <- Hruntime. exact Hleft.
Qed.

Lemma live_frame_member_wf :
  forall CT h active stack frame,
    live_frames_wf CT h active stack ->
    live_frame_member active stack frame ->
    wf_r_config CT frame.(frame_senv) frame.(frame_renv) h.
Proof.
  intros CT h active stack frame [Hactive Hstack] Hlive.
  inversion Hlive; subst.
  - exact Hactive.
  - apply Forall_forall with (x := boundary) in Hstack; assumption.
Qed.

Lemma live_frame_member_authority_sound :
  forall h active stack frame,
    live_frames_authority_sound h active stack ->
    live_frame_member active stack frame ->
    authority_context_sound h frame.(frame_renv) frame.(frame_authority).
Proof.
  intros h active stack frame [Hactive Hstack] Hlive.
  inversion Hlive; subst.
  - exact Hactive.
  - apply Forall_forall with (x := boundary) in Hstack; assumption.
Qed.

Lemma typed_rdm_root_has_runtime_context :
  forall CT sGamma rGamma h root,
    wf_r_config CT sGamma rGamma h ->
    typed_root RDM sGamma rGamma root ->
    exists runtime_q, r_muttype h root = Some runtime_q.
Proof.
  intros CT sGamma rGamma h root Hwf
    [variable [T [Htype [Hvalue Hrdm]]]].
  destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwf) as
    [receiver [runtime_q [Hreceiver [_ Hreceiver_runtime]]]].
  have Hwf_copy := Hwf.
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [_ [_ [_ Hcorr]]]]].
  have Hdom := Htype. apply static_getType_dom in Hdom.
  assert (Hthis : get_this_var_mapping (vars rGamma) = Some receiver).
  { unfold runtime_getVal in Hreceiver.
    unfold get_this_var_mapping. destruct (vars rGamma) as [|value values];
      simpl in Hreceiver; try discriminate.
    destruct value; try discriminate. injection Hreceiver as <-. reflexivity. }
  specialize (Hcorr receiver runtime_q Hthis Hreceiver_runtime variable
    Hdom T Htype).
  rewrite Hvalue in Hcorr.
  exists runtime_q. eapply rdm_typable_runtime_matches_context; eauto.
Qed.

Lemma typed_rdm_root_matches_receiver_runtime :
  forall CT sGamma rGamma h receiver runtime_q root,
    wf_r_config CT sGamma rGamma h ->
    runtime_getVal rGamma 0 = Some (Iot receiver) ->
    r_muttype h receiver = Some runtime_q ->
    typed_root RDM sGamma rGamma root ->
    r_muttype h root = Some runtime_q.
Proof.
  intros CT sGamma rGamma h receiver runtime_q root Hwf Hreceiver
    Hreceiver_runtime [variable [T [Htype [Hvalue Hrdm]]]].
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [_ [_ [_ Hcorr]]]]].
  have Hdom := Htype. apply static_getType_dom in Hdom.
  assert (Hthis : get_this_var_mapping (vars rGamma) = Some receiver).
  { unfold runtime_getVal in Hreceiver.
    unfold get_this_var_mapping. destruct (vars rGamma) as [|value values];
      simpl in Hreceiver; try discriminate.
    destruct value; try discriminate. injection Hreceiver as <-. reflexivity. }
  specialize (Hcorr receiver runtime_q Hthis Hreceiver_runtime variable
    Hdom T Htype).
  rewrite Hvalue in Hcorr.
  eapply rdm_typable_runtime_matches_context; eauto.
Qed.

Lemma potential_frame_edge_preserves_runtime_mutability :
  forall CT h active stack left right runtime_q,
    live_frames_wf CT h active stack ->
    potential_frame_edge active stack left right ->
    r_muttype h left = Some runtime_q ->
    r_muttype h right = Some runtime_q.
Proof.
  intros CT h active stack left right runtime_q Hframes
    [frame [Hlive [Hleft Hright]]] Hleft_runtime.
  have Hframe_wf := live_frame_member_wf CT h active stack frame Hframes Hlive.
  destruct (active_rdm_roots_share_runtime_context CT frame.(frame_senv)
    frame.(frame_renv) h left right Hframe_wf Hleft Hright) as
    [frame_context [Hleft_context Hright_context]].
  rewrite Hleft_runtime in Hleft_context. injection Hleft_context as <-.
  exact Hright_context.
Qed.

Lemma potential_adjacent_preserves_runtime_mutability :
  forall CT h active stack left right runtime_q,
    live_frames_wf CT h active stack ->
    wf_heap CT h ->
    potential_adjacent CT h active stack left right ->
    r_muttype h left = Some runtime_q ->
    r_muttype h right = Some runtime_q.
Proof.
  intros CT h active stack left right runtime_q Hframes Hheap
    [Hheap_edge | [Hframe_edge | Hreturn_edge]]
    Hleft_runtime.
  - destruct Hheap_edge as [Hforward | Hbackward].
    + eapply retained_edge_preserves_runtime_context; eauto.
    + eapply mutable_edge_reflects_runtime_mutability; eauto.
  - eapply potential_frame_edge_preserves_runtime_mutability; eauto.
  - eapply potential_return_edge_preserves_runtime_mutability; eauto.
Qed.

Lemma potential_connected_preserves_runtime_mutability :
  forall CT h active stack left right runtime_q,
    live_frames_wf CT h active stack ->
    wf_heap CT h ->
    potential_connected CT h active stack left right ->
    r_muttype h left = Some runtime_q ->
    r_muttype h right = Some runtime_q.
Proof.
  intros CT h active stack left right runtime_q Hframes Hheap Hconnected.
  induction Hconnected; intros Hruntime.
  - eapply potential_adjacent_preserves_runtime_mutability; eauto.
  - exact Hruntime.
  - apply IHHconnected2. apply IHHconnected1. exact Hruntime.
Qed.

Lemma authority_flow_step_preserves_runtime_mutability :
  forall CT h active stack source target runtime_q,
    live_frames_wf CT h active stack ->
    wf_heap CT h ->
    authority_flow_step CT h active stack source target ->
    r_muttype h (snd source) = Some runtime_q ->
    r_muttype h (snd target) = Some runtime_q.
Proof.
  intros CT h active stack source target runtime_q Hframes Hheap Hstep
    Hruntime.
  inversion Hstep; subst; simpl in *.
  - eapply retained_edge_preserves_runtime_context; eauto.
  - eapply mutable_edge_reflects_runtime_mutability; eauto.
  - eapply mutable_edge_preserves_runtime_mutability; eauto.
  - eapply mutable_edge_reflects_runtime_mutability; eauto.
  - eapply potential_frame_edge_preserves_runtime_mutability; eauto.
  - eapply potential_frame_edge_preserves_runtime_mutability; eauto.
  - exact Hruntime.
  - exact Hruntime.
Qed.

Lemma authority_flow_connected_preserves_runtime_mutability :
  forall CT h active stack source target runtime_q,
    live_frames_wf CT h active stack ->
    wf_heap CT h ->
    authority_flow_connected CT h active stack source target ->
    r_muttype h (snd source) = Some runtime_q ->
    r_muttype h (snd target) = Some runtime_q.
Proof.
  intros CT h active stack source target runtime_q Hframes Hheap Hconnected.
  induction Hconnected; intros Hruntime.
  - eapply authority_flow_step_preserves_runtime_mutability; eauto.
  - exact Hruntime.
  - apply IHHconnected2. apply IHHconnected1. exact Hruntime.
Qed.

Lemma potential_adjacent_reflects_runtime_mutability :
  forall CT h active stack left right runtime_q,
    live_frames_wf CT h active stack ->
    wf_heap CT h ->
    potential_adjacent CT h active stack left right ->
    r_muttype h right = Some runtime_q ->
    r_muttype h left = Some runtime_q.
Proof.
  intros CT h active stack left right runtime_q Hframes Hheap
    [Hheap_edge | [Hframe_edge | Hreturn_edge]]
    Hright_runtime.
  - destruct Hheap_edge as [Hforward | Hbackward].
    + eapply retained_edge_reflects_runtime_mutability; eauto.
    + eapply mutable_edge_preserves_runtime_mutability; eauto.
  - eapply potential_frame_edge_preserves_runtime_mutability; eauto.
    eapply potential_frame_edge_symmetric; eauto.
  - eapply potential_return_edge_preserves_runtime_mutability; eauto.
    eapply potential_return_edge_symmetric; eauto.
Qed.

Lemma potential_connected_reflects_runtime_mutability :
  forall CT h active stack left right runtime_q,
    live_frames_wf CT h active stack ->
    wf_heap CT h ->
    potential_connected CT h active stack left right ->
    r_muttype h right = Some runtime_q ->
    r_muttype h left = Some runtime_q.
Proof.
  intros CT h active stack left right runtime_q Hframes Hheap Hconnected.
  induction Hconnected; intros Hruntime.
  - eapply potential_adjacent_reflects_runtime_mutability; eauto.
  - exact Hruntime.
  - apply IHHconnected1. apply IHHconnected2. exact Hruntime.
Qed.

Lemma potential_colors_imply_live_frame_colors :
  forall CT h M Z active stack frame,
    potential_colors_separated CT h M Z active stack ->
    live_frame_member active stack frame ->
    watched_frame_colors CT h M Z frame.
Proof.
  intros CT h M Z active stack frame Hpotential Hlive
    capability_root zone_root Hcapability_root
    [capability [Hcapability Hcapability_connected]] Hzone_root
    [protected [Hprotected Hzone_connected]].
  apply (Hpotential capability protected Hcapability Hprotected).
  eapply potential_connected_trans.
  - eapply mutable_connected_is_potential_connected.
    eapply mutable_connected_sym. exact Hcapability_connected.
  - eapply potential_connected_trans.
    + eapply live_frame_rdm_roots_potentially_connected; eauto.
    + eapply mutable_connected_is_potential_connected. exact Hzone_connected.
Qed.

Lemma potential_colors_imply_active_colors :
  forall CT h M Z active stack,
    potential_colors_separated CT h M Z active stack ->
    watched_frame_colors CT h M Z active.
Proof.
  intros. eapply potential_colors_imply_live_frame_colors; eauto.
  constructor.
Qed.

Lemma potential_colors_imply_component_colors :
  forall CT h M Z active stack,
    potential_colors_separated CT h M Z active stack ->
    component_colors_separated CT h M Z.
Proof.
  intros CT h M Z active stack Hpotential capability protected
    Hcapability Hprotected Hconnected.
  apply (Hpotential capability protected Hcapability Hprotected).
  eapply mutable_connected_is_potential_connected; exact Hconnected.
Qed.

Lemma potential_connected_map_edges :
  forall CT1 h1 active1 stack1 CT2 h2 active2 stack2 left right,
    (forall edge_left edge_right,
      potential_adjacent CT1 h1 active1 stack1 edge_left edge_right ->
      potential_connected CT2 h2 active2 stack2 edge_left edge_right) ->
    potential_connected CT1 h1 active1 stack1 left right ->
    potential_connected CT2 h2 active2 stack2 left right.
Proof.
  intros CT1 h1 active1 stack1 CT2 h2 active2 stack2 left right
    Hedge Hconnected.
  induction Hconnected.
  - apply Hedge. exact H.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma mutable_reachable_is_potential_connected :
  forall CT h active stack source target,
    mutable_reachable CT h source target ->
    potential_connected CT h active stack source target.
Proof.
  intros CT h active stack source target Hreachable.
  apply mutable_connected_is_potential_connected.
  eapply mutable_reachable_connected; eauto.
Qed.

Lemma typed_mut_root_is_active_live_capability :
  forall CT h active stack root,
    typed_root Mut active.(frame_senv) active.(frame_renv) root ->
    In Loc (live_capability_set CT h active stack) root.
Proof.
  intros CT h active stack root
    [variable [T [Htype [Hvalue Hmut]]]].
  exists root. split.
  - left. exists variable, T. repeat split; try assumption.
    unfold capability_in_context. left. exact Hmut.
  - constructor.
Qed.

Lemma staged_frame_adjacent_after_descent_reflects :
  forall CT h authority old_senv old_renv new_senv new_renv left right,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    staged_frame_adjacent CT h
      (mk_watched_frame authority new_senv new_renv) left right ->
    staged_frame_connected CT h
      (mk_watched_frame authority old_senv old_renv) left right.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv left right
    Hdescend [Hheap | [Hleft Hright]].
  - apply rt_step. left. exact Hheap.
  - destruct (Hdescend left Hleft) as
      [old_left [Hold_left Hleft_reachable]].
    destruct (Hdescend right Hright) as
      [old_right [Hold_right Hright_reachable]].
    eapply staged_frame_connected_trans.
    + eapply mutable_reachable_is_reverse_staged_frame_connected.
      exact Hleft_reachable.
    + eapply staged_frame_connected_trans.
      * apply rt_step. right. split.
        -- exact Hold_left.
        -- exact Hold_right.
      * eapply mutable_reachable_is_staged_frame_connected.
        exact Hright_reachable.
Qed.

Lemma staged_frame_connected_after_descent_reflects :
  forall CT h authority old_senv old_renv new_senv new_renv left right,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    staged_frame_connected CT h
      (mk_watched_frame authority new_senv new_renv) left right ->
    staged_frame_connected CT h
      (mk_watched_frame authority old_senv old_renv) left right.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv left right
    Hdescend Hconnected.
  induction Hconnected.
  - eapply staged_frame_adjacent_after_descent_reflects; eauto.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma phased_authority_frame_closure_after_descent_included :
  forall CT h authority old_senv old_renv new_senv new_renv old_seeds
    new_seeds,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame authority new_senv new_renv))
      (phase_frame_capability_set CT h
        (mk_watched_frame authority old_senv old_renv)) ->
    Included authority_flow_state new_seeds old_seeds ->
    Included authority_flow_state
      (phased_authority_frame_closure CT h
        (mk_watched_frame authority new_senv new_renv) new_seeds)
      (phased_authority_frame_closure CT h
        (mk_watched_frame authority old_senv old_renv) old_seeds).
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv old_seeds
    new_seeds Hdescend Howned Hseeds state [seed [Hseed Hconnected]].
  exists seed. split; [apply Hseeds; exact Hseed|].
  eapply phased_authority_frame_connected_after_descent_reflects; eauto.
Qed.

(** Active-environment descent can discard authority paths but cannot create
    a new one.  Consequently every post-state color is literally an old
    color (with the same mode and location). *)
Lemma executing_authority_colors_after_active_descent_included :
  forall CT h authority old_senv old_renv new_senv new_renv incoming,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame authority new_senv new_renv))
      (phase_frame_capability_set CT h
        (mk_watched_frame authority old_senv old_renv)) ->
    Included authority_flow_state
      (executing_authority_color_set CT h
        (mk_watched_frame authority new_senv new_renv) incoming)
      (executing_authority_color_set CT h
        (mk_watched_frame authority old_senv old_renv) incoming).
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv incoming
    Hdescend Howned.
  unfold executing_authority_color_set.
  eapply phased_authority_frame_closure_after_descent_included; eauto.
  intros state Hstate. inversion Hstate; subst.
  - left. exact H.
  - right. destruct H as [location [Heq Hlocation]].
    exists location. split; [exact Heq|]. apply Howned. exact Hlocation.
Qed.

Lemma frozen_caller_prospective_retained_forward :
  forall CT h frame left right,
    retained_mut_reachable CT h left right ->
    frozen_caller_authority_connected CT h frame
      (FlowProspective, left) (FlowProspective, right).
Proof.
  intros CT h frame left right Hreachable. induction Hreachable.
  - apply rt_refl.
  - eapply rt_trans; [exact IHHreachable|].
    apply rt_step. apply frozen_caller_prospective_retained. exact H.
Qed.

Lemma frozen_caller_prospective_mutable_forward :
  forall CT h frame left right,
    mutable_reachable CT h left right ->
    frozen_caller_authority_connected CT h frame
      (FlowProspective, left) (FlowProspective, right).
Proof.
  intros CT h frame left right Hreachable. induction Hreachable.
  - apply rt_refl.
  - eapply rt_trans; [exact IHHreachable|]. apply rt_step.
    apply frozen_caller_prospective_retained. constructor. exact H.
Qed.

Lemma frozen_caller_prospective_mutable_reverse :
  forall CT h frame left right,
    mutable_reachable CT h left right ->
    frozen_caller_authority_connected CT h frame
      (FlowProspective, right) (FlowProspective, left).
Proof.
  intros CT h frame left right Hreachable. induction Hreachable.
  - apply rt_refl.
  - eapply rt_trans.
    + apply rt_step. apply frozen_caller_prospective_rdm_backward. exact H.
    + exact IHHreachable.
Qed.

Lemma frozen_caller_powered_mutable_reverse :
  forall CT h frame left right,
    mutable_reachable CT h left right ->
    frozen_caller_authority_connected CT h frame
      (FlowPowered, right) (FlowProspective, left).
Proof.
  intros CT h frame left right Hreachable. inversion Hreachable; subst.
  - apply rt_step. apply frozen_caller_mark_prospective.
  - eapply rt_trans.
    + apply rt_step. apply frozen_caller_reverse_rdm. exact H0.
    + eapply frozen_caller_prospective_mutable_reverse. exact H.
Qed.

(** Every frozen dangerous path has the same location projection when it is
    viewed prospectively.  This forgets whether the path initially carried
    powered authority; it does not add a transition to the operational
    semantics. *)
Lemma frozen_caller_connected_as_prospective :
  forall CT h frame source target,
    frozen_caller_authority_connected CT h frame source target ->
    frozen_caller_authority_connected CT h frame
      (FlowProspective, snd source) (FlowProspective, snd target).
Proof.
  intros CT h frame source target Hconnected.
  induction Hconnected.
  - inversion H; subst; simpl.
    + apply rt_step. apply frozen_caller_prospective_retained. exact H0.
    + apply rt_step. apply frozen_caller_prospective_retained. exact H0.
    + apply rt_step. apply frozen_caller_prospective_rdm_backward. exact H0.
    + apply rt_step. apply frozen_caller_prospective_rdm_backward. exact H0.
    + apply rt_step. eapply frozen_caller_prospective_frame_join; eauto.
    + apply rt_step. eapply frozen_caller_prospective_frame_join; eauto.
    + apply rt_refl.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma frozen_caller_step_after_descent_reflects :
  forall CT h authority old_senv old_renv new_senv new_renv source target,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    frozen_caller_authority_step CT h
      (mk_watched_frame authority new_senv new_renv) source target ->
    frozen_caller_authority_connected CT h
      (mk_watched_frame authority old_senv old_renv) source target.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv source target
    Hdescend Hstep. inversion Hstep; subst.
  - apply rt_step. apply frozen_caller_retained. exact H.
  - apply rt_step. apply frozen_caller_prospective_retained. exact H.
  - apply rt_step. apply frozen_caller_prospective_rdm_backward. exact H.
  - apply rt_step. apply frozen_caller_reverse_rdm. exact H.
  - destruct (Hdescend left H) as
      [old_left [Hold_left Hleft_path]].
    destruct (Hdescend right H0) as
      [old_right [Hold_right Hright_path]].
    eapply rt_trans.
    + eapply frozen_caller_powered_mutable_reverse. exact Hleft_path.
    + eapply rt_trans.
      * apply rt_step. eapply frozen_caller_prospective_frame_join; eauto.
      * eapply frozen_caller_prospective_mutable_forward. exact Hright_path.
  - destruct (Hdescend left H) as
      [old_left [Hold_left Hleft_path]].
    destruct (Hdescend right H0) as
      [old_right [Hold_right Hright_path]].
    eapply rt_trans.
    + eapply frozen_caller_prospective_mutable_reverse. exact Hleft_path.
    + eapply rt_trans.
      * apply rt_step. eapply frozen_caller_prospective_frame_join; eauto.
      * eapply frozen_caller_prospective_mutable_forward. exact Hright_path.
  - apply rt_step. apply frozen_caller_mark_prospective.
Qed.

Lemma frozen_caller_connected_after_descent_reflects :
  forall CT h authority old_senv old_renv new_senv new_renv source target,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    frozen_caller_authority_connected CT h
      (mk_watched_frame authority new_senv new_renv) source target ->
    frozen_caller_authority_connected CT h
      (mk_watched_frame authority old_senv old_renv) source target.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv source target
    Hdescend Hconnected. induction Hconnected.
  - eapply frozen_caller_step_after_descent_reflects; eauto.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma active_prospective_mutable_authority_components_after_descent :
  forall CT h cutoff authority old_senv old_renv new_senv new_renv,
    wf_r_config CT old_senv old_renv h ->
    authority_context_sound h old_renv authority ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame authority new_senv new_renv))
      (phase_frame_capability_set CT h
        (mk_watched_frame authority old_senv old_renv)) ->
    active_prospective_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame authority old_senv old_renv) ->
    active_prospective_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame authority new_senv new_renv).
Proof.
  intros CT h cutoff authority old_senv old_renv new_senv new_renv Hwf
    Hsound Hdescend Howned Hold root target
    [[Hmut | [Hrdm Hroot_runtime]] Hpath].
  - have Hnew_capability : frame_capability_root
        (mk_watched_frame authority new_senv new_renv) root.
    { destruct Hmut as [variable [T [Htype [Hvalue Hqualifier]]]].
      exists variable, T. repeat split; try assumption.
      unfold capability_in_context. left. exact Hqualifier. }
    have Hnew_owned : In Loc
        (phase_frame_capability_set CT h
      (mk_watched_frame authority new_senv new_renv)) root.
    { exists root. split; [exact Hnew_capability|constructor]. }
    have Hpath_old : frozen_caller_authority_connected CT h
        (mk_watched_frame authority old_senv old_renv)
        (FlowProspective, root) (FlowProspective, target).
    { eapply frozen_caller_connected_after_descent_reflects; eauto. }
    destruct (Howned root Hnew_owned) as
      [old_root [Hold_root Hold_reaches_root]].
    have Hold_runtime : r_muttype h old_root = Some Mut_r.
    { eapply frame_capability_root_runtime_mutable with
        (frame := mk_watched_frame authority old_senv old_renv).
      - exact Hwf.
      - exact Hsound.
      - exact Hold_root. }
    apply (Hold old_root target).
    split.
    + destruct Hold_root as
        [variable [T [Htype [Hvalue [Hold_mut | [Hold_rdm Hauthority]]]]]].
      * left. exists variable, T. repeat split; assumption.
      * right. split.
        -- exists variable, T. repeat split; assumption.
        -- exact Hold_runtime.
    + eapply rt_trans.
      * eapply frozen_caller_prospective_retained_forward.
        exact Hold_reaches_root.
      * exact Hpath_old.
  - destruct (Hdescend root Hrdm) as
      [old_root [Hold_root Hold_reaches_root]].
    have Hpath_old : frozen_caller_authority_connected CT h
        (mk_watched_frame authority old_senv old_renv)
        (FlowProspective, root) (FlowProspective, target).
    { eapply frozen_caller_connected_after_descent_reflects; eauto. }
    destruct (typed_rdm_root_has_runtime_context CT old_senv old_renv h
      old_root Hwf Hold_root) as [old_runtime Hold_runtime].
    have Hroot_context := mutable_reachable_preserves_runtime_mutability CT h
      old_root root old_runtime (proj1 (proj2 Hwf)) Hold_reaches_root
      Hold_runtime.
    rewrite Hroot_runtime in Hroot_context. injection Hroot_context as <-.
    eapply Hold with (root := old_root).
    split.
    + right. split; assumption.
    + eapply rt_trans.
      * eapply frozen_caller_prospective_mutable_forward.
        exact Hold_reaches_root.
      * exact Hpath_old.
Qed.

Lemma live_prospective_mutable_authority_components_after_active_descent :
  forall CT h cutoff authority old_senv old_renv new_senv new_renv stack,
    wf_r_config CT old_senv old_renv h ->
    authority_context_sound h old_renv authority ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame authority new_senv new_renv))
      (phase_frame_capability_set CT h
        (mk_watched_frame authority old_senv old_renv)) ->
    live_prospective_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame authority old_senv old_renv) stack ->
    live_prospective_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame authority new_senv new_renv) stack.
Proof.
  intros CT h cutoff authority old_senv old_renv new_senv new_renv stack Hwf
    Hsound Hdescend Howned Hold frame root target Hlive Hreachable.
  destruct Hlive as [|boundary Hin].
  - eapply active_prospective_mutable_authority_components_after_descent;
      eauto.
    eapply live_prospective_mutable_authority_components_active. exact Hold.
  - eapply Hold; [constructor; exact Hin|exact Hreachable].
Qed.

Lemma frozen_callee_side_prospective_components_after_active_descent :
  forall CT h authority old_senv old_renv new_senv new_renv snapshots stack,
    wf_r_config CT old_senv old_renv h ->
    authority_context_sound h old_renv authority ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame authority new_senv new_renv))
      (phase_frame_capability_set CT h
        (mk_watched_frame authority old_senv old_renv)) ->
    frozen_callee_side_prospective_components_after_boundaries CT h
      (mk_watched_frame authority old_senv old_renv) snapshots stack ->
    frozen_callee_side_prospective_components_after_boundaries CT h
      (mk_watched_frame authority new_senv new_renv)
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) snapshots) stack.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv snapshots stack
    Hwf Hsound Hdescend Howned Hold snapshot boundary above below Hpartition.
  destruct (advance_frozen_snapshot_live_partition_reflects CT h
    (mk_watched_frame authority new_senv new_renv) snapshots stack snapshot
    boundary above below Hpartition) as [old_snapshot Hold_partition].
  eapply live_prospective_mutable_authority_components_after_active_descent;
    eauto.
Qed.

Lemma advance_frozen_caller_snapshots_after_descent_included :
  forall CT h authority old_senv old_renv new_senv new_renv snapshots,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    frozen_caller_snapshots_closed CT h
      (mk_watched_frame authority old_senv old_renv) snapshots ->
    frozen_caller_snapshot_list_included
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) snapshots)
      snapshots.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv snapshots
    Hdescend Hclosed new_snapshot Hnew.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot.
  exists old_snapshot. split; [exact Hold|].
  intros state [seed [Hseed Hpath]].
  eapply Hclosed; [exact Hold|].
  exists seed. split; [exact Hseed|].
  eapply frozen_caller_connected_after_descent_reflects; eauto.
Qed.

Lemma frozen_caller_snapshots_nested_resume_safe_after_active_descent :
  forall CT h Z authority old_senv old_renv new_senv new_renv snapshots,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    frozen_caller_snapshots_closed CT h
      (mk_watched_frame authority old_senv old_renv) snapshots ->
    (forall snapshot,
      List.In (Some snapshot) snapshots ->
      Included authority_flow_state
        (frozen_caller_authority_closure CT h
          (mk_watched_frame authority old_senv old_renv)
          snapshot.(frozen_snapshot_current_resume_exposure))
        snapshot.(frozen_snapshot_current_resume_exposure)) ->
    frozen_caller_snapshots_nested_resume_safe Z snapshots ->
    frozen_caller_snapshots_nested_resume_safe Z
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) snapshots).
Proof.
  intros CT h Z authority old_senv old_renv new_senv new_renv snapshots
    Hdescend. induction snapshots as [|slot tail IH]; intros Hclosed Hexposure
    Hnested; simpl in *; [exact I|].
  destruct slot as [head|].
  - destruct Hnested as [Hhead Htail]. split.
    + intros new_older Hnew_older.
      unfold advance_frozen_caller_snapshots in Hnew_older.
      apply in_map_iff in Hnew_older.
      destruct Hnew_older as [old_slot [Heq Hold_slot]].
      destruct old_slot as [old_older|]; simpl in Heq; [|discriminate].
      injection Heq as Heq. subst new_older.
      intros source_mode source Hsource_mode Hsource Hsource_root.
      have Hold_source : In authority_flow_state
          head.(frozen_snapshot_current_colors) (source_mode, source).
      { eapply Hclosed; [simpl; auto|].
        destruct Hsource as [seed [Hseed Hpath]].
        exists seed. split; [exact Hseed|].
        eapply frozen_caller_connected_after_descent_reflects; eauto. }
      destruct (Hhead old_older Hold_slot source_mode source Hsource_mode
        Hold_source Hsource_root) as
        [[entry_mode [Hentry_mode Hentry]] | Hsafe].
      * left. exists entry_mode. split; assumption.
      * right. intros exposure_mode target Hexposure_mode Htarget.
        eapply Hsafe; [exact Hexposure_mode|].
        eapply Hexposure; [simpl; right; exact Hold_slot|].
        destruct Htarget as [seed [Hseed Hpath]].
        exists seed. split; [exact Hseed|].
        eapply frozen_caller_connected_after_descent_reflects; eauto.
    + eapply IH.
      * intros snapshot Hsnapshot. eapply Hclosed. simpl. right.
        exact Hsnapshot.
      * intros snapshot Hsnapshot. eapply Hexposure. simpl. right.
        exact Hsnapshot.
      * exact Htail.
  - eapply IH.
    + intros snapshot Hsnapshot. eapply Hclosed. simpl. right.
      exact Hsnapshot.
    + intros snapshot Hsnapshot. eapply Hexposure. simpl. right.
      exact Hsnapshot.
    + exact Hnested.
Qed.

Lemma frozen_completed_colors_resume_safe_after_active_descent :
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
    frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h
        (mk_watched_frame authority old_senv old_renv) incoming) snapshots ->
    frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h
        (mk_watched_frame authority new_senv new_renv) incoming)
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) snapshots).
Proof.
  intros CT h Z authority old_senv old_renv new_senv new_renv incoming
    snapshots Hdescend Howned Hexposure Hcompleted new_snapshot source_mode
    source Hnew Hsource_mode Hsource Hsource_root.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot. simpl in *.
  have Hold_source : In authority_flow_state
      (executing_authority_color_set CT h
        (mk_watched_frame authority old_senv old_renv) incoming)
      (source_mode, source).
  { eapply executing_authority_colors_after_active_descent_included; eauto. }
  destruct (Hcompleted old_snapshot source_mode source Hold Hsource_mode
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

(** Generic preservation rule for the pairwise nested resume certificate.
    A post-step color is classified either as the corresponding historical
    color or as a step-local exceptional provenance.  The exceptional class
    is required to be safe against the old resume exposures and against the
    protected zone.  Thus it is a private proof device, not a premise of the
    public preservation theorem. *)
Lemma frozen_caller_snapshots_nested_resume_safe_after_classified_advance :
  forall CT new_h Z new_active snapshots exceptional,
    frozen_caller_snapshots_nested_resume_safe Z snapshots ->
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
  intros CT new_h Z new_active snapshots exceptional Hnested Hresume Hactive_safe
    Hclassify_color Hclassify_exposure.
  induction snapshots as [|slot tail IH]; simpl in *; [exact I|].
  destruct slot as [head|].
  - destruct Hnested as [Hhead Htail]. split.
    + intros new_older Hnew_older.
      unfold advance_frozen_caller_snapshots in Hnew_older.
      apply in_map_iff in Hnew_older.
      destruct Hnew_older as [old_slot [Heq Hold_slot]].
      destruct old_slot as [old_older|]; simpl in Heq; [|discriminate].
      injection Heq as Heq. subst new_older.
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
      * right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
        destruct (Hclassify_exposure old_older exposure_mode target
          (ltac:(simpl; right; exact Hold_slot)) Hexposure_mode Htarget
          Hprotected) as
          [[old_exposure_mode [Hold_exposure_mode Hold_target]] |
           [active_target_mode [Hactive_target_mode Hactive_target]]].
        -- eapply Hresume with (snapshot := old_older)
             (active_mode := active_source_mode) (source := source)
             (exposure_mode := old_exposure_mode); eauto.
        -- eapply Hactive_safe; eauto.
    + apply IH.
      * exact Htail.
      * intros snapshot active_mode source exposure_mode target Hsnapshot.
        eapply Hresume. simpl. right. exact Hsnapshot.
      * intros snapshot older mode location Hsnapshot Holder.
        eapply Hclassify_color.
        -- simpl. right. exact Hsnapshot.
        -- simpl. right. exact Holder.
      * intros snapshot mode location Hsnapshot.
        eapply Hclassify_exposure. simpl. right. exact Hsnapshot.
  - apply IH.
    + exact Hnested.
    + intros snapshot active_mode source exposure_mode target Hsnapshot.
      eapply Hresume. simpl. right. exact Hsnapshot.
    + intros snapshot older mode location Hsnapshot Holder.
      eapply Hclassify_color.
      * simpl. right. exact Hsnapshot.
      * simpl. right. exact Holder.
    + intros snapshot mode location Hsnapshot.
      eapply Hclassify_exposure. simpl. right. exact Hsnapshot.
Qed.

Lemma frozen_caller_snapshots_nested_resume_safe_after_safe_field_update :
  forall CT h Z frame snapshots lx old field written,
    runtime_getObj h lx = Some old ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_closed CT h frame snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h frame snapshots ->
    authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h frame) ->
    authority_safe_field_endpoints CT h frame lx written ->
    frozen_caller_snapshots_nested_resume_safe Z snapshots ->
    frozen_caller_snapshots_resume_roots_safe CT h Z frame snapshots ->
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
  eapply frozen_caller_snapshots_nested_resume_safe_after_classified_advance
    with (exceptional := independent_active_authority_colors CT h frame).
  - exact Hnested.
  - exact Hresume.
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
  - intros snapshot mode location Hsnapshot Hmode
      [seed [Hseed Hpath]] _.
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

Lemma frozen_completed_colors_resume_safe_after_safe_field_update :
  forall CT h Z frame incoming snapshots lx old field written,
    runtime_getObj h lx = Some old ->
    authority_colors_runtime_mutable h
      (executing_authority_color_set CT h frame incoming) ->
    frozen_caller_snapshots_resume_exposures_wf CT h frame snapshots ->
    authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h frame) ->
    authority_safe_field_endpoints CT h frame lx written ->
    frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h frame incoming) snapshots ->
    (forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h frame)
        (active_mode, location) ->
      ~ In Loc Z location) ->
    frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT
        (update_field h lx field (Iot written)) frame incoming)
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame snapshots).
Proof.
  intros CT h Z frame incoming snapshots lx old field written Hobj
    Hcompleted_runtime Hexposure Hactive_runtime Hendpoints Hcompleted
    Hactive_safe new_snapshot source_mode source Hnew Hsource_mode Hsource
    Hsource_root.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot. simpl in *.
  destruct (executing_authority_colors_after_safe_field_update_covered CT h
    frame incoming lx old field written Hobj Hcompleted_runtime Hendpoints
    source_mode source Hsource_mode Hsource) as
    [old_source_mode [Hold_source_mode Hold_source]].
  destruct (Hcompleted old_snapshot old_source_mode source Hold
    Hold_source_mode Hold_source Hsource_root) as
    [[entry_mode [Hentry_mode Hentry]] | Hsafe].
  - left. exists entry_mode. split; assumption.
  - right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
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
    + exact (Hsafe old_target_mode target Hold_target_mode Hold_target
        Hprotected).
    + exact (Hactive_safe active_target_mode target Hactive_target_mode
        Hactive_target Hprotected).
Qed.

Lemma frozen_caller_snapshots_nested_resume_safe_after_graph_reflection :
  forall CT h h' Z active snapshots,
    (forall left right,
      retained_mut_edge CT h' left right -> retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right -> mutable_edge CT h left right) ->
    frozen_caller_snapshots_closed CT h active snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h active snapshots ->
    frozen_caller_snapshots_nested_resume_safe Z snapshots ->
    frozen_caller_snapshots_nested_resume_safe Z
      (advance_frozen_caller_snapshots CT h' active snapshots).
Proof.
  intros CT h h' Z active snapshots Hretained Hmutable Hclosed Hexposure
    Hnested.
  eapply frozen_caller_snapshots_nested_resume_safe_after_classified_advance
    with (exceptional := Empty_set authority_flow_state).
  - exact Hnested.
  - intros snapshot mode source exposure_mode target Hsnapshot Hmode Hempty.
    inversion Hempty.
  - intros mode location Hmode Hempty. inversion Hempty.
  - intros snapshot older mode location Hsnapshot Holder Hmode Hcolor Hroot.
    left. exists mode. split; [exact Hmode|].
    eapply frozen_caller_closure_after_graph_reflection_included; eauto.
  - intros snapshot mode location Hsnapshot Hmode Hcolor Hprotected.
    left. exists mode. split; [exact Hmode|].
    eapply frozen_caller_closure_after_graph_reflection_included; eauto.
    exact ((proj1 (proj2 Hexposure)) snapshot Hsnapshot).
Qed.

Lemma frozen_completed_colors_resume_safe_after_graph_reflection :
  forall CT h h' Z active incoming snapshots,
    (forall location,
      frame_owned_location CT h' active location ->
      frame_owned_location CT h active location) ->
    (forall left right,
      retained_mut_edge CT h' left right -> retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right -> mutable_edge CT h left right) ->
    frozen_caller_snapshots_resume_exposures_wf CT h active snapshots ->
    frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h active incoming) snapshots ->
    frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h' active incoming)
      (advance_frozen_caller_snapshots CT h' active snapshots).
Proof.
  intros CT h h' Z active incoming snapshots Howned Hretained Hmutable
    Hexposure Hcompleted new_snapshot source_mode source Hnew Hsource_mode
    Hsource Hsource_root.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot. simpl in *.
  destruct (executing_authority_colors_after_graph_reflection_covered CT h
    h' active incoming Howned Hretained Hmutable source_mode source
    Hsource_mode Hsource) as [old_source_mode [Hold_source_mode Hold_source]].
  destruct (Hcompleted old_snapshot old_source_mode source Hold
    Hold_source_mode Hold_source Hsource_root) as
    [[entry_mode [Hentry_mode Hentry]] | Hsafe].
  - left. exists entry_mode. split; assumption.
  - right. intros exposure_mode target Hexposure_mode Htarget.
    eapply Hsafe; [exact Hexposure_mode|].
    eapply frozen_caller_closure_after_graph_reflection_included;
      [exact Hretained|exact Hmutable| |exact Htarget].
    exact ((proj1 (proj2 Hexposure)) old_snapshot Hold).
Qed.

Lemma principled_frozen_authority_after_active_descent :
  forall CT P Z cutoff authority old_senv old_renv new_senv new_renv
    stack incoming snapshots h,
    principled_frozen_authority_history_state CT P Z cutoff
      (mk_watched_frame authority old_senv old_renv) stack incoming
      snapshots h ->
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame authority new_senv new_renv) stack incoming h ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame authority new_senv new_renv))
      (phase_frame_capability_set CT h
        (mk_watched_frame authority old_senv old_renv)) ->
    principled_frozen_authority_history_state CT P Z cutoff
      (mk_watched_frame authority new_senv new_renv) stack incoming
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) snapshots) h.
Proof.
  intros CT P Z cutoff authority old_senv old_renv new_senv new_renv
    stack incoming snapshots h
    [Hold [Haligned [Hruntime [Hclosed
      [Hretain [Hdangerous [Havoid [Hroots [Hexposure
        [Hresume [Hjoins [Hentry_covered Hphase_covered]]]]]]]]]]]]
    Hpost Hdescend Howned.
  set (old_frame := mk_watched_frame authority old_senv old_renv).
  set (new_frame := mk_watched_frame authority new_senv new_renv).
  set (snapshots' := advance_frozen_caller_snapshots CT h new_frame snapshots).
  have Hincluded : frozen_caller_snapshot_list_included snapshots' snapshots.
  { unfold snapshots', new_frame, old_frame in *.
    eapply advance_frozen_caller_snapshots_after_descent_included; eauto. }
  have Hactive_included : Included authority_flow_state
      (independent_active_authority_colors CT h new_frame)
      (independent_active_authority_colors CT h old_frame).
  { unfold independent_active_authority_colors, new_frame, old_frame.
    eapply executing_authority_colors_after_active_descent_included; eauto. }
  split; [exact Hpost|]. split.
  - unfold snapshots', frozen_caller_snapshots_aligned,
      advance_frozen_caller_snapshots. rewrite length_map. exact Haligned.
  - split.
    + unfold snapshots'. eapply advance_frozen_caller_snapshots_runtime_mutable.
      * exact (proj1 (proj1
           (proj2 (proj2 (proj2 (proj2 Hpost)))))).
      * exact Hruntime.
    + split.
      * unfold snapshots'. apply advance_frozen_caller_snapshots_closed.
      * split.
        -- unfold snapshots'.
           eapply advance_frozen_caller_snapshots_retain_entry. exact Hretain.
        -- split.
           ++ unfold snapshots'.
              eapply advance_frozen_caller_snapshots_dangerous.
              exact Hdangerous.
           ++ split.
              ** intros new_snapshot mode location Hnew Hmode Hcolor.
                 destruct (Hincluded new_snapshot Hnew) as
                   [old_snapshot [Hold_snapshot Hcolors]].
                 eapply Havoid; [exact Hold_snapshot|exact Hmode|].
                 eapply Hcolors. exact Hcolor.
              ** split.
                 --- intros new_snapshot root Hnew Hroot.
                     unfold snapshots', advance_frozen_caller_snapshots in Hnew.
                     apply in_map_iff in Hnew.
                     destruct Hnew as [old_slot [Heq Hold_slot]].
                     destruct old_slot as [old_snapshot|]; simpl in Heq;
                       [|discriminate].
                     injection Heq as Heq. subst new_snapshot. simpl in Hroot.
                     eapply Hroots; eauto.
                 --- split.
                     +++ split.
                         *** intros new_snapshot Hnew mode location Hcolor.
                             unfold snapshots', advance_frozen_caller_snapshots in Hnew.
                             apply in_map_iff in Hnew.
                             destruct Hnew as [old_slot [Heq Hold_slot]].
                             destruct old_slot as [old_snapshot|]; simpl in Heq;
                               [|discriminate].
                             injection Heq as Heq. subst new_snapshot. simpl in Hcolor.
                             eapply (advance_frozen_caller_snapshot_runtime_mutable
                               CT h new_frame
                               old_snapshot.(frozen_snapshot_current_resume_exposure)).
                             ---- exact (proj1 (proj1
                               (proj2 (proj2 (proj2 (proj2 Hpost)))))).
                             ---- eapply (proj1 Hexposure); eauto.
                             ---- exact Hcolor.
                         *** split.
                             ---- intros new_snapshot Hnew.
                                  unfold snapshots', advance_frozen_caller_snapshots in Hnew.
                                  apply in_map_iff in Hnew.
                                  destruct Hnew as [old_slot [Heq Hold_slot]].
                                  destruct old_slot as [old_snapshot|]; simpl in Heq;
                                    [|discriminate].
                                  injection Heq as Heq. subst new_snapshot. simpl.
                                  exact (proj1
                                    (frozen_caller_authority_closure_idempotent
                                      CT h new_frame
                                      old_snapshot.(frozen_snapshot_current_resume_exposure))).
                             ---- split.
                                  ++++ intros new_snapshot mode location Hnew Hcolor.
                                  unfold snapshots', advance_frozen_caller_snapshots in Hnew.
                                  apply in_map_iff in Hnew.
                                  destruct Hnew as [old_slot [Heq Hold_slot]].
                                  destruct old_slot as [old_snapshot|]; simpl in Heq;
                                    [|discriminate].
                                  injection Heq as Heq. subst new_snapshot. simpl in Hcolor.
                                  eapply frozen_caller_authority_closure_dangerous;
                                    [|exact Hcolor].
                                  intros old_mode old_location Hold_color.
                                  eapply (proj1 (proj2 (proj2 Hexposure))) with
                                    (snapshot := old_snapshot)
                                    (mode := old_mode) (location := old_location);
                                    eauto.
                                  ++++ split.
                                       ***** intros new_snapshot Hnew state Hentry.
                                       unfold snapshots', advance_frozen_caller_snapshots in Hnew.
                                       apply in_map_iff in Hnew.
                                       destruct Hnew as [old_slot [Heq Hold_slot]].
                                       destruct old_slot as [old_snapshot|]; simpl in Heq;
                                         [|discriminate].
                                       injection Heq as Heq. subst new_snapshot. simpl in *.
                                       apply frozen_caller_authority_closure_contains.
                                            eapply (proj1 (proj2 (proj2
                                              (proj2 Hexposure)))); eauto.
                                       ***** intros new_snapshot root Hnew
                                               Hroot Hroot_runtime.
                                            unfold snapshots',
                                              advance_frozen_caller_snapshots in Hnew.
                                            apply in_map_iff in Hnew.
                                            destruct Hnew as
                                              [old_slot [Heq Hold_slot]].
                                            destruct old_slot as [old_snapshot|];
                                              simpl in Heq; [|discriminate].
                                            injection Heq as Heq.
                                            subst new_snapshot. simpl in *.
                                            apply frozen_caller_authority_closure_contains.
                                            eapply (proj2 (proj2 (proj2
                                              (proj2 Hexposure)))); eauto.
                     +++ split.
                         *** intros new_snapshot active_mode source exposure_mode target
                           Hnew Hactive_mode Hactive Hsource Hexposure_mode
                           Htarget Hprotected.
                         unfold snapshots', advance_frozen_caller_snapshots in Hnew.
                         apply in_map_iff in Hnew.
                         destruct Hnew as [old_slot [Heq Hold_slot]].
                         destruct old_slot as [old_snapshot|]; simpl in Heq;
                           [|discriminate].
                         injection Heq as Heq. subst new_snapshot. simpl in *.
                         have Hold_target : In authority_flow_state
                             old_snapshot.(frozen_snapshot_current_resume_exposure)
                             (exposure_mode, target).
                         { eapply (proj1 (proj2 Hexposure)); [exact Hold_slot|].
                           destruct Htarget as [seed [Hseed Hpath]].
                           exists seed. split; [exact Hseed|].
                           unfold new_frame, old_frame in *.
                           eapply frozen_caller_connected_after_descent_reflects;
                             eauto. }
                         eapply Hresume with (snapshot := old_snapshot)
                           (active_mode := active_mode) (source := source)
                           (exposure_mode := exposure_mode); eauto.
                         *** split.
                             ---- intros new_snapshot source_mode source Hnew
                               Hsource_mode Hsource_color Hsource_root.
                             unfold snapshots', advance_frozen_caller_snapshots in Hnew.
                             apply in_map_iff in Hnew.
                             destruct Hnew as [old_slot [Heq Hold_slot]].
                             destruct old_slot as [old_snapshot|]; simpl in Heq;
                               [|discriminate].
                             injection Heq as Heq. subst new_snapshot. simpl in *.
                                  have Hold_source : In authority_flow_state
                                 old_snapshot.(frozen_snapshot_current_colors)
                                 (source_mode, source).
                                  { eapply Hclosed; [exact Hold_slot|].
                               destruct Hsource_color as [seed [Hseed Hpath]].
                               exists seed. split; [exact Hseed|].
                               unfold new_frame, old_frame in *.
                               eapply frozen_caller_connected_after_descent_reflects;
                                      eauto. }
                                  destruct (Hjoins old_snapshot source_mode source
                               Hold_slot Hsource_mode Hold_source Hsource_root) as
                               [[entry_mode [Hentry_mode Hentry]] | Hsafe].
                                  ++++ left. exists entry_mode. split; assumption.
                                  ++++ right. intros exposure_mode target
                                    Hexposure_mode Htarget Hprotected.
                                       apply (Hsafe exposure_mode target Hexposure_mode);
                                    [|exact Hprotected].
                                       eapply (proj1 (proj2 Hexposure));
                                         [exact Hold_slot|].
                                       destruct Htarget as [seed [Hseed Hpath]].
                                       exists seed. split; [exact Hseed|].
                                       unfold new_frame, old_frame in *.
                                       eapply frozen_caller_connected_after_descent_reflects;
                                         eauto.
                             ---- split.
                                  ++++ unfold snapshots'.
                                       apply advance_frozen_caller_snapshots_entry_exposure_covered.
                                       exact Hentry_covered.
                                  ++++ unfold snapshots'.
                                       apply advance_frozen_caller_snapshots_cover_phase_incoming.
                                       exact Hphase_covered.
Qed.

Lemma phased_authority_frame_step_after_graph_reflection :
  forall CT h h' frame source target,
    (forall left right,
      retained_mut_edge CT h' left right ->
      retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right ->
      mutable_edge CT h left right) ->
    (forall location,
      frame_owned_location CT h' frame location ->
      frame_owned_location CT h frame location) ->
    phased_authority_frame_step CT h' frame source target ->
    phased_authority_frame_step CT h frame source target.
Proof.
  intros CT h h' frame source target Hretained Hmutable Howned Hstep.
  inversion Hstep; subst.
  - apply phased_authority_retained. apply Hretained. exact H.
  - apply phased_authority_prospective_retained. apply Hretained. exact H.
  - apply phased_authority_prospective_rdm_backward. apply Hmutable. exact H.
  - apply phased_authority_reverse_rdm. apply Hmutable. exact H.
  - apply phased_authority_neutral_rdm_forward. apply Hmutable. exact H.
  - apply phased_authority_neutral_rdm_backward. apply Hmutable. exact H.
  - eapply phased_authority_powered_frame_join; eauto.
  - eapply phased_authority_prospective_frame_join; eauto.
  - eapply phased_authority_neutral_frame_join; eauto.
  - apply phased_authority_forget.
  - apply phased_authority_prospective_forget.
  - apply phased_authority_mark_prospective.
  - apply phased_authority_promote. apply Howned. exact H.
Qed.

Lemma phased_authority_return_step_after_graph_reflection :
  forall h h' callee boundary source target,
    (forall left right,
      staged_return_adjacent h' callee boundary left right ->
      staged_return_adjacent h callee boundary left right) ->
    phased_authority_return_step h' callee boundary source target ->
    phased_authority_return_step h callee boundary source target.
Proof.
  intros h h' callee boundary source target Hreturn Hstep.
  inversion Hstep; subst.
  - apply phased_authority_powered_return. apply Hreturn. exact H.
  - apply phased_authority_neutral_return. apply Hreturn. exact H.
  - apply phased_authority_return_forget.
Qed.

Lemma phased_authority_return_step_preserves_neutral :
  forall h callee boundary source target,
    fst source = FlowNeutral ->
    phased_authority_return_step h callee boundary source target ->
    fst target = FlowNeutral.
Proof.
  intros h callee boundary source target Hsource Hstep.
  inversion Hstep; subst; simpl in *; try reflexivity; discriminate.
Qed.

(** Updating one field adds at most the edge from the receiver to the written
    location, and—when the field is RDM—the corresponding reverse RDM step.
    Frame-local prospective joins are unchanged.  This normalization is the
    phase-sensitive analogue of [potential_connected_after_field_update]. *)
Lemma staged_frame_adjacent_after_field_update :
  forall CT h frame lx old field value left right,
    runtime_getObj h lx = Some old ->
    staged_frame_adjacent CT (update_field h lx field value) frame left right ->
    staged_frame_adjacent CT h frame left right \/
    exists written,
      value = Iot written /\
      ((left = lx /\ right = written) \/
       (left = written /\ right = lx)).
Proof.
  intros CT h frame lx old field value left right Hobj
    [[Hretained | Hreverse] | Hframe].
  - destruct (retained_edge_after_field_update CT h lx old field value
      left right Hobj Hretained) as
      [Hold | [Hsource [Hvalue Hnew]]].
    + left. left. left. exact Hold.
    + right. exists right. split; [exact Hvalue|]. left. split; auto.
  - destruct (mutable_edge_after_field_update CT h lx old field value
      right left Hobj Hreverse) as
      [Hold | [Hsource [Hvalue Hnew]]].
    + left. left. right. exact Hold.
    + right. exists left. split; [exact Hvalue|]. right. split; auto.
  - left. right. exact Hframe.
Qed.

(** If the active frame changes only by replacing each new RDM root with a
    root descending from the old frame, every new potential edge was already
    a potential path. Suspended-frame clique edges are unchanged. *)
Lemma potential_adjacent_after_active_descent_reflects :
  forall CT h authority old_senv old_renv new_senv new_renv stack left right,
    wf_r_config CT old_senv old_renv h ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    potential_adjacent CT h
      (mk_watched_frame authority new_senv new_renv) stack left right ->
    potential_connected CT h
      (mk_watched_frame authority old_senv old_renv) stack left right.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv stack left right
    Hwf Hdescend
    [Hheap | [[frame [Hlive [Hleft Hright]]] | Hreturn]].
  - apply rt_step. left. exact Hheap.
  - inversion Hlive; subst.
    + destruct (Hdescend left Hleft) as
        [old_left [Hold_left Hleft_reachable]].
      destruct (Hdescend right Hright) as
        [old_right [Hold_right Hright_reachable]].
      eapply potential_connected_trans.
      * eapply mutable_reachable_is_reverse_potential_connected; eauto.
      * eapply potential_connected_trans.
        -- eapply live_frame_rdm_roots_potentially_connected.
           ++ constructor.
           ++ exact Hold_left.
           ++ exact Hold_right.
        -- eapply mutable_reachable_is_potential_connected; eauto.
    + apply rt_step. right. left. exists boundary.(boundary_caller).
      split.
      * constructor. exact H.
      * split; assumption.
  - destruct Hreturn as
      [callee [boundary
        [Hboundary [Hview [Hcallee_return
          [Hruntime [Hroots | Hroots]]]]]]].
    + inversion Hboundary; subst.
      * destruct (Hdescend left (proj1 Hroots)) as
          [old_left [Hold_left Hleft_reachable]].
        destruct (typed_rdm_root_has_runtime_context CT old_senv old_renv h
          old_left Hwf Hold_left) as [runtime_q Hold_runtime].
        have Hleft_runtime := mutable_reachable_preserves_runtime_mutability
          CT h old_left left runtime_q (proj1 (proj2 Hwf)) Hleft_reachable
          Hold_runtime.
        assert (Hold_right_runtime :
          r_muttype h old_left = r_muttype h right).
        { rewrite Hold_runtime. rewrite <- Hruntime. symmetry.
          exact Hleft_runtime. }
        eapply potential_connected_trans.
        -- eapply mutable_reachable_is_reverse_potential_connected; eauto.
        -- apply rt_step. right. right. exists
             (mk_watched_frame authority old_senv old_renv), boundary.
           split; [constructor|]. split; [exact Hview|].
           split; [exact Hcallee_return|].
           split; [exact Hold_right_runtime|].
           left. split; [exact Hold_left|exact (proj2 Hroots)].
      * apply rt_step. right. right. exists callee, boundary.
        split; [constructor; exact H|]. split; [exact Hview|].
        split; [exact Hcallee_return|].
        split; [exact Hruntime|]. left. exact Hroots.
    + inversion Hboundary; subst.
      * destruct (Hdescend right (proj2 Hroots)) as
          [old_right [Hold_right Hright_reachable]].
        destruct (typed_rdm_root_has_runtime_context CT old_senv old_renv h
          old_right Hwf Hold_right) as [runtime_q Hold_runtime].
        have Hright_runtime := mutable_reachable_preserves_runtime_mutability
          CT h old_right right runtime_q (proj1 (proj2 Hwf)) Hright_reachable
          Hold_runtime.
        assert (Hleft_old_runtime :
          r_muttype h left = r_muttype h old_right).
        { rewrite Hruntime. rewrite Hright_runtime. symmetry.
          exact Hold_runtime. }
        eapply potential_connected_trans.
        -- apply rt_step. right. right. exists
             (mk_watched_frame authority old_senv old_renv), boundary.
           split; [constructor|]. split; [exact Hview|].
           split; [exact Hcallee_return|].
           split; [exact Hleft_old_runtime|].
           right. split; [exact (proj1 Hroots)|exact Hold_right].
        -- eapply mutable_reachable_is_potential_connected; eauto.
      * apply rt_step. right. right. exists callee, boundary.
        split; [constructor; exact H|]. split; [exact Hview|].
        split; [exact Hcallee_return|].
        split; [exact Hruntime|]. right. exact Hroots.
Qed.

Lemma potential_connected_after_active_descent_reflects_strong :
  forall CT h authority old_senv old_renv new_senv new_renv stack left right,
    wf_r_config CT old_senv old_renv h ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    potential_connected CT h
      (mk_watched_frame authority new_senv new_renv) stack left right ->
    potential_connected CT h
      (mk_watched_frame authority old_senv old_renv) stack left right.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv stack left right
    Hwf Hdescend Hconnected.
  eapply potential_connected_map_edges; [|exact Hconnected].
  intros edge_left edge_right Hedge.
  eapply potential_adjacent_after_active_descent_reflects; eauto.
Qed.

Lemma potential_connected_after_active_descent_reflects :
  forall CT h authority old_senv old_renv new_senv new_renv stack left right,
    wf_r_config CT old_senv old_renv h ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    potential_connected CT h
      (mk_watched_frame authority new_senv new_renv) stack left right ->
    potential_connected CT h
      (mk_watched_frame authority old_senv old_renv) stack left right \/
    exists anchor,
      In Loc (live_capability_set CT h
        (mk_watched_frame authority new_senv new_renv) stack) anchor /\
      potential_connected CT h
        (mk_watched_frame authority old_senv old_renv) stack anchor right.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv stack left right
    Hwf Hdescend Hconnected.
  left. eapply potential_connected_after_active_descent_reflects_strong;
    eauto.
Qed.

Lemma initial_potential_live_history :
  forall CT sGamma rGamma h,
    wf_r_config CT sGamma rGamma h ->
    env_respects_protected_set
      (reachable_locations_from_initial_env h rGamma) sGamma rGamma ->
    potential_live_history_state CT
      (reachable_locations_from_initial_env h rGamma)
      (reachable_locations_from_initial_env h rGamma)
      (dom h) (mk_watched_frame Imm_r sGamma rGamma) [] h.
Proof.
  intros CT sGamma rGamma h Hwf Henv.
  have Hinitial := initial_authority_component_history CT sGamma rGamma h
    Hwf Henv.
  have Hlive := initial_live_authority_history CT sGamma rGamma h Hwf Henv.
  split; [exact Hlive|].
  split.
  have Hempty := initial_live_capability_set_empty CT sGamma rGamma h
    (proj1 (proj2 Hinitial)).
  - intros capability protected Hcapability. exfalso.
    exact (Hempty capability Hcapability).
  - constructor.
Qed.
