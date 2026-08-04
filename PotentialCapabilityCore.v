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

Definition potential_colors_separated
  (CT : class_table) (h : heap) (M Z : Ensemble Loc)
  (active : watched_frame) (stack : list watched_boundary) : Prop :=
  forall capability protected,
    In Loc M capability ->
    In Loc Z protected ->
    ~ potential_connected CT h active stack capability protected.

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

Definition authority_mode_dangerous (mode : authority_flow_mode) : Prop :=
  mode = FlowPowered \/ mode = FlowProspective.

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

Definition independent_active_authority_colors
  (CT : class_table) (h : heap) (active : watched_frame) :
  Ensemble authority_flow_state :=
  executing_authority_color_set CT h active
    (Empty_set authority_flow_state).

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
