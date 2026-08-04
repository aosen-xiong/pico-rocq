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

Definition phased_frame_powered_seeds
  (CT : class_table) (h : heap) (frame : watched_frame) :
  Ensemble authority_flow_state :=
  fun state => exists location,
    state = (FlowPowered, location) /\
    frame_owned_location CT h frame location.

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

Definition frozen_snapshot_resume_exposure_avoids
  (Z : Ensemble Loc) (snapshot : frozen_caller_color_snapshot) : Prop :=
  forall exposure_mode target,
    authority_mode_dangerous exposure_mode ->
    In authority_flow_state
      snapshot.(frozen_snapshot_current_resume_exposure)
      (exposure_mode, target) ->
    ~ In Loc Z target.

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
