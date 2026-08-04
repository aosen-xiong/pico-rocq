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

Lemma live_capability_iff_live_frame_owned :
  forall CT h active stack location,
    In Loc (live_capability_set CT h active stack) location <->
    exists frame,
      live_frame_member active stack frame /\
      frame_owned_location CT h frame location.
Proof.
  intros CT h active stack location. split.
  - intros [root [[Hactive | [boundary [Hin Hsuspended]]] Hreach]].
    + exists active. split; [constructor|].
      exists root. split; assumption.
    + exists boundary.(boundary_caller). split.
      * constructor. exact Hin.
      * exists root. split; assumption.
  - intros [frame [Hlive [root [Hroot Hreach]]]].
    exists root. split; [|exact Hreach].
    inversion Hlive; subst.
    + left. exact Hroot.
    + right. exists boundary. split; assumption.
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

(** The suffix below a live boundary identifies the capabilities that survive
    after that call is popped. *)
Inductive live_call_context :
  watched_frame -> list watched_boundary ->
  watched_frame -> watched_boundary -> list watched_boundary -> Prop :=
| live_call_context_head : forall active boundary tail,
    live_call_context active (boundary :: tail) active boundary tail
| live_call_context_tail : forall active head tail callee boundary below,
    live_call_context head.(boundary_caller) tail callee boundary below ->
    live_call_context active (head :: tail) callee boundary below.

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

Lemma live_call_partition_above_frame_is_live :
  forall active stack boundary above below frame,
    live_call_partition active stack boundary above below ->
    live_frame_member active above frame ->
    live_frame_member active stack frame.
Proof.
  intros active stack boundary above below frame Hpartition Hlive.
  inversion Hlive; subst.
  - constructor.
  - constructor.
    rewrite (live_call_partition_stack_shape _ _ _ _ _ Hpartition).
    apply in_or_app. left. exact H.
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

Lemma live_call_partition_caller_capability_is_live :
  forall CT h active stack boundary above below location,
    live_call_partition active stack boundary above below ->
    In Loc
      (live_capability_set CT h boundary.(boundary_caller) below) location ->
    In Loc (live_capability_set CT h active stack) location.
Proof.
  intros CT h active stack boundary above below location Hpartition
    [root [Hroot Hreach]].
  exists root. split; [|exact Hreach].
  induction Hpartition.
  - destruct Hroot as [Hcaller | [older [Hin Holder]]].
    + right. exists boundary. split; [left; reflexivity|exact Hcaller].
    + right. exists older. split; [right; exact Hin|exact Holder].
  - have Hlifted := IHHpartition Hroot.
    destruct Hlifted as [Hactive | [older [Hin Holder]]].
    + left. exact Hactive.
    + right. exists older. split; [right; exact Hin|exact Holder].
Qed.

Lemma live_call_partition_above_capability_is_live :
  forall CT h active stack boundary above below location,
    live_call_partition active stack boundary above below ->
    In Loc (live_capability_set CT h active above) location ->
    In Loc (live_capability_set CT h active stack) location.
Proof.
  intros CT h active stack boundary above below location Hpartition
    Hlocation.
  apply live_capability_iff_live_frame_owned in Hlocation.
  destruct Hlocation as [frame [Hlive Howned]].
  apply live_capability_iff_live_frame_owned.
  exists frame. split.
  - eapply live_call_partition_above_frame_is_live; eauto.
  - exact Howned.
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

Lemma live_call_partition_caller_frames_wf :
  forall CT h active stack boundary above below,
    live_call_partition active stack boundary above below ->
    live_frames_wf CT h active stack ->
    live_frames_wf CT h boundary.(boundary_caller) below.
Proof.
  intros CT h active stack boundary above below Hpartition
    [Hactive Hstack].
  rewrite (live_call_partition_stack_shape _ _ _ _ _ Hpartition) in Hstack.
  apply Forall_app in Hstack.
  have Hboundary_tail := proj2 Hstack.
  split.
  - exact (Forall_inv Hboundary_tail).
  - exact (Forall_inv_tail Hboundary_tail).
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

Lemma live_call_partition_caller_frames_authority_sound :
  forall h active stack boundary above below,
    live_call_partition active stack boundary above below ->
    live_frames_authority_sound h active stack ->
    live_frames_authority_sound h boundary.(boundary_caller) below.
Proof.
  intros h active stack boundary above below Hpartition [Hactive Hstack].
  rewrite (live_call_partition_stack_shape _ _ _ _ _ Hpartition) in Hstack.
  apply Forall_app in Hstack.
  have Hboundary_tail := proj2 Hstack.
  split.
  - exact (Forall_inv Hboundary_tail).
  - exact (Forall_inv_tail Hboundary_tail).
Qed.

Lemma live_stack_authorities_chain_prefix :
  forall authority prefix suffix,
    live_stack_authorities_chain authority (prefix ++ suffix) ->
    live_stack_authorities_chain authority prefix.
Proof.
  intros authority prefix. revert authority.
  induction prefix as [|boundary prefix IH]; intros authority suffix Hchain.
  - exact I.
  - simpl in Hchain |- *. destruct Hchain as [Hhead Htail].
    split; [exact Hhead|].
    eapply IH. exact Htail.
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

Definition boundary_connected
  (CT : class_table) (h : heap)
  (active : watched_frame) (stack : list watched_boundary) :
  Loc -> Loc -> Prop :=
  clos_refl_trans Loc (boundary_adjacent CT h active stack).

Lemma potential_connected_is_boundary_connected :
  forall CT h active stack left right,
    potential_connected CT h active stack left right ->
    boundary_connected CT h active stack left right.
Proof.
  intros CT h active stack left right Hconnected.
  induction Hconnected.
  - apply rt_step. left. exact H.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

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

Definition layered_colors_separated
  (CT : class_table) (h : heap) (M Z : Ensemble Loc)
  (active : watched_frame) (stack : list watched_boundary) : Prop :=
  forall capability protected,
    In Loc M capability ->
    In Loc Z protected ->
    ~ layered_color_connected CT h active stack capability protected.

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

Definition staged_colors_separated
  (CT : class_table) (h : heap) (M Z : Ensemble Loc)
  (active : watched_frame) (stack : list watched_boundary) : Prop :=
  forall protected,
    In Loc (staged_live_color_set CT h active stack M) protected ->
    ~ In Loc Z protected.

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

Definition phased_live_color_set
  (CT : class_table) (h : heap) (active : watched_frame)
  (stack : list watched_boundary) : Ensemble Loc :=
  phased_live_color_set_from CT h active stack (Empty_set Loc).

Definition phased_colors_separated
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (active : watched_frame) (stack : list watched_boundary) : Prop :=
  forall protected,
    In Loc (phased_live_color_set CT h active stack) protected ->
    ~ In Loc Z protected.

Lemma phased_live_color_set_from_monotone :
  forall CT h active stack old new,
    Included Loc old new ->
    Included Loc
      (phased_live_color_set_from CT h active stack old)
      (phased_live_color_set_from CT h active stack new).
Proof.
  intros CT h active stack. revert active.
  induction stack as [|boundary tail IH];
    intros active old new Hincluded; simpl.
  - intros location [seed [Hseed Hconnected]].
    exists seed. split; [|exact Hconnected].
    inversion Hseed; subst.
    + left. apply Hincluded. exact H.
    + right. exact H.
  - eapply IH.
    intros location [seed [Hseed Hreturn]].
    exists seed. split; [|exact Hreturn].
    destruct Hseed as [frame_seed [Hframe_seed Hframe_path]].
    exists frame_seed. split; [|exact Hframe_path].
    inversion Hframe_seed; subst.
    + left. apply Hincluded. exact H.
    + right. exact H.
Qed.

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

Definition phased_authority_color_set
  (CT : class_table) (h : heap) (active : watched_frame)
  (stack : list watched_boundary) : Ensemble authority_flow_state :=
  phased_authority_color_set_from CT h active stack
    (Empty_set authority_flow_state).

Definition phased_authority_colors_separated
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (active : watched_frame) (stack : list watched_boundary) : Prop :=
  forall mode protected,
    (mode = FlowPowered \/ mode = FlowProspective) ->
    In authority_flow_state
      (phased_authority_color_set CT h active stack)
      (mode, protected) ->
    ~ In Loc Z protected.

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

(** The proof-local incoming authority is a genuine seed of the executing
    closure.  In particular, call entry never discards caller authority; it
    merely closes that authority under the callee's phase-local operations.
    This fact is used to restore the caller's original incoming set at pop
    time, without adding a saved-authority premise to any public theorem. *)
Lemma executing_authority_color_set_contains_incoming :
  forall CT h frame incoming,
    Included authority_flow_state incoming
      (executing_authority_color_set CT h frame incoming).
Proof.
  intros CT h frame incoming state Hstate.
  exists state. split.
  - left. exact Hstate.
  - apply rt_refl.
Qed.

(** After call entry, every completed caller color is part of the callee's
    incoming set and hence remains represented throughout callee execution. *)
Lemma executing_authority_color_set_contains_caller_colors :
  forall CT h caller callee incoming,
    Included authority_flow_state
      (executing_authority_color_set CT h caller incoming)
      (executing_authority_color_set CT h callee
        (executing_authority_color_set CT h caller incoming)).
Proof.
  intros CT h caller callee incoming state Hstate.
  apply executing_authority_color_set_contains_incoming. exact Hstate.
Qed.

Definition authority_mode_dangerous (mode : authority_flow_mode) : Prop :=
  mode = FlowPowered \/ mode = FlowProspective.

(** A compositional semantic summary for statement bodies.  Dangerous
    authority at a location that already existed at entry must have a
    dangerous representative in the entry phase.  Locations allocated by
    the body are intentionally outside the relation. *)
Definition executing_authority_old_colors_reflected
  (CT : class_table) (entry_h : heap) (entry_frame : watched_frame)
  (entry_incoming : Ensemble authority_flow_state)
  (final_h : heap) (final_frame : watched_frame)
  (final_incoming : Ensemble authority_flow_state) : Prop :=
  forall mode location,
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT final_h final_frame final_incoming)
      (mode, location) ->
    location < dom entry_h ->
    exists entry_mode,
      authority_mode_dangerous entry_mode /\
      In authority_flow_state
        (executing_authority_color_set CT entry_h entry_frame entry_incoming)
        (entry_mode, location).

Lemma executing_authority_old_colors_reflected_refl :
  forall CT h frame incoming,
    executing_authority_old_colors_reflected CT h frame incoming
      h frame incoming.
Proof.
  intros CT h frame incoming mode location Hmode Hcolor Hdom.
  exists mode. split; assumption.
Qed.

(** Flexible-call summary used by the final recursive induction.  Exact
    reflection is retained when available.  The additional alternative is
    semantically sufficient for preservation: a dangerous color that was
    materialized only through benign read-only overlap is certified outside
    the protected zone. *)
Definition executing_authority_old_colors_reflected_or_outside
  (CT : class_table) (Z : Ensemble Loc)
  (entry_h : heap) (entry_frame : watched_frame)
  (entry_incoming : Ensemble authority_flow_state)
  (final_h : heap) (final_frame : watched_frame)
  (final_incoming : Ensemble authority_flow_state) : Prop :=
  forall mode location,
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT final_h final_frame final_incoming)
      (mode, location) ->
    location < dom entry_h ->
    (exists entry_mode,
      authority_mode_dangerous entry_mode /\
      In authority_flow_state
        (executing_authority_color_set CT entry_h entry_frame entry_incoming)
        (entry_mode, location)) \/
    ~ In Loc Z location.

Lemma executing_authority_old_colors_reflected_implies_or_outside :
  forall CT Z h1 frame1 incoming1 h2 frame2 incoming2,
    executing_authority_old_colors_reflected CT h1 frame1 incoming1
      h2 frame2 incoming2 ->
    executing_authority_old_colors_reflected_or_outside CT Z
      h1 frame1 incoming1 h2 frame2 incoming2.
Proof.
  intros CT Z h1 frame1 incoming1 h2 frame2 incoming2 Hreflect mode
    location Hmode Hcolor Hold.
  left. eapply Hreflect; eauto.
Qed.

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

Lemma executing_authority_dangerous_mutable_connected :
  forall CT h frame incoming left right mode,
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT h frame incoming) (mode, left) ->
    mutable_connected CT h left right ->
    exists target_mode,
      authority_mode_dangerous target_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h frame incoming)
        (target_mode, right).
Proof.
  intros CT h frame incoming left right mode Hmode Hleft Hconnected.
  revert mode Hmode Hleft.
  induction Hconnected; intros mode Hmode Hleft.
  - destruct H as [Hforward | Hbackward].
    + exists mode. split; [exact Hmode|].
      eapply executing_authority_dangerous_retained; eauto.
      apply retained_edge_rdm. exact Hforward.
    + exists FlowProspective. split; [right; reflexivity|].
      eapply executing_authority_dangerous_reverse_rdm; eauto.
  - exists mode. split; assumption.
  - destruct (IHHconnected1 mode Hmode Hleft) as
      [middle_mode [Hmiddle_mode Hmiddle]].
    eapply IHHconnected2; eauto.
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

(** Auxiliary local invariant for the exceptional flexible-return proof.
    It is initialized when the dynamic entry frame has no RDM roots.  Only a
    runtime-mutable RDM component matters: immutable RDM components may
    legitimately include entry-heap objects but cannot carry the returned
    mutable authority.  The invariant is proof-local and does not occur in a
    public theorem. *)
Definition active_mutable_rdm_components_after_cutoff
  (CT : class_table) (h : heap) (cutoff : Loc)
  (frame : watched_frame) : Prop :=
  forall root target,
    typed_root RDM frame.(frame_senv) frame.(frame_renv) root ->
    r_muttype h root = Some Mut_r ->
    mutable_reachable CT h root target ->
    cutoff <= target.

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

Lemma mutable_authority_reachable_has_root :
  forall CT h frame root target,
    mutable_authority_reachable CT h frame root target ->
    mutable_authority_root frame h root.
Proof.
  intros CT h frame root target Hreachable. inversion Hreachable; subst.
  - destruct H as [variable [T [Htype [Hvalue Hcapability]]]].
    destruct Hcapability as [Hmut | [Hrdm Hauthority]].
    + left. exists variable, T. repeat split; assumption.
    + right. split.
      * exists variable, T. repeat split; assumption.
      * exact H0.
  - right. split; assumption.
Qed.

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

Lemma live_mutable_authority_components_push_without_active_authority :
  forall CT h cutoff caller stack callee boundary,
    boundary.(boundary_caller) = caller ->
    (forall root, ~ mutable_authority_root callee h root) ->
    live_mutable_authority_components_after_cutoff CT h cutoff caller stack ->
    live_mutable_authority_components_after_cutoff CT h cutoff callee
      (boundary :: stack).
Proof.
  intros CT h cutoff caller stack callee boundary Hcaller Hnone Hold frame
    root target Hlive Hreachable.
  inversion Hlive; subst.
  - exfalso. eapply Hnone.
    eapply mutable_authority_reachable_has_root. exact Hreachable.
  - destruct H as [Heq | Hin].
    + subst boundary0. eapply Hold; eauto. constructor.
    + eapply Hold; eauto. constructor. exact Hin.
Qed.

Lemma no_capability_or_rdm_root_has_no_mutable_authority_root :
  forall frame h,
    (forall root, ~ frame_capability_root frame root) ->
    (forall root,
      ~ typed_root RDM frame.(frame_senv) frame.(frame_renv) root) ->
    forall root, ~ mutable_authority_root frame h root.
Proof.
  intros frame h Hnone Hno_rdm root [Hmut | [Hrdm Hruntime]].
  - apply (Hnone root). destruct Hmut as
      [variable [T [Htype [Hvalue Hqualifier]]]].
    exists variable, T. repeat split; try assumption.
    unfold capability_in_context. left. exact Hqualifier.
  - exact (Hno_rdm root Hrdm).
Qed.

(** Call-compositional form of the proof-local freshness invariant.  It
    quantifies over the active frame and every suspended caller, because a
    nested call must retain the freshness fact established by its enclosing
    local evaluation.  This predicate is an internal induction hypothesis;
    it is not, and must not become, a premise of the public preservation
    theorem. *)
Definition live_mutable_rdm_components_after_cutoff
  (CT : class_table) (h : heap) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary) : Prop :=
  forall frame root target,
    live_frame_member active stack frame ->
    typed_root RDM frame.(frame_senv) frame.(frame_renv) root ->
    r_muttype h root = Some Mut_r ->
    mutable_reachable CT h root target ->
    cutoff <= target.

Lemma live_mutable_rdm_components_active :
  forall CT h cutoff active stack,
    live_mutable_rdm_components_after_cutoff CT h cutoff active stack ->
    active_mutable_rdm_components_after_cutoff CT h cutoff active.
Proof.
  intros CT h cutoff active stack Hlive root target Hroot Hruntime Hreachable.
  eapply Hlive; eauto. constructor.
Qed.

Lemma live_mutable_rdm_components_push_without_active_rdm :
  forall CT h cutoff caller stack callee boundary,
    boundary.(boundary_caller) = caller ->
    (forall root,
      ~ typed_root RDM callee.(frame_senv) callee.(frame_renv) root) ->
    live_mutable_rdm_components_after_cutoff CT h cutoff caller stack ->
    live_mutable_rdm_components_after_cutoff CT h cutoff
      callee (boundary :: stack).
Proof.
  intros CT h cutoff caller stack callee boundary Hcaller Hnone Hold frame
    root target Hlive Hroot Hruntime Hreachable.
  inversion Hlive; subst.
  - exfalso. exact (Hnone root Hroot).
  - destruct H as [Heq | Hin].
    + subst boundary0.
      eapply Hold; eauto. constructor.
    + eapply Hold; eauto. constructor. exact Hin.
Qed.

Definition frame_rdm_root_set (frame : watched_frame) : Ensemble Loc :=
  fun root =>
    typed_root RDM frame.(frame_senv) frame.(frame_renv) root.

(** Persistent, compositional form of the local component invariant.  A
    mutable component rooted at a current RDM variable is either wholly in
    the fresh suffix or is reachable from one of the fixed entry roots.
    [origins] remains fixed across sequential and nested evaluation. *)
Definition active_mutable_rdm_components_covered
  (CT : class_table) (h : heap) (cutoff : Loc)
  (origins : Ensemble Loc) (frame : watched_frame) : Prop :=
  forall root target,
    typed_root RDM frame.(frame_senv) frame.(frame_renv) root ->
    r_muttype h root = Some Mut_r ->
    mutable_reachable CT h root target ->
    cutoff <= target \/
    exists origin,
      In Loc origins origin /\
      mutable_reachable CT h origin target.

(** General no-publication summary.  The specialized cutoff invariant above
    is the empty-entry-root case.  In general, a final mutable RDM component
    may touch the old heap only through an RDM root already present in the
    entry frame.  This is a semantic result of statement evaluation, not a
    call or dispatch premise. *)
Definition active_mutable_rdm_components_have_entry_origin
  (CT : class_table) (entry_h : heap) (entry_frame : watched_frame)
  (final_h : heap) (final_frame : watched_frame) : Prop :=
  forall root target,
    typed_root RDM final_frame.(frame_senv) final_frame.(frame_renv) root ->
    r_muttype final_h root = Some Mut_r ->
    mutable_reachable CT final_h root target ->
    dom entry_h <= target \/
    exists entry_root,
      typed_root RDM entry_frame.(frame_senv) entry_frame.(frame_renv)
        entry_root /\
      mutable_reachable CT final_h entry_root target.

Lemma no_active_rdm_roots_have_old_mutable_components :
  forall CT h cutoff frame,
    (forall root,
      ~ typed_root RDM frame.(frame_senv) frame.(frame_renv) root) ->
    active_mutable_rdm_components_after_cutoff CT h cutoff frame.
Proof.
  intros CT h cutoff frame Hnone root target Hroot.
  exfalso. exact (Hnone root Hroot).
Qed.

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

Lemma phased_authority_powered_to_neutral_mutable_connected :
  forall CT h frame left right,
    mutable_connected CT h left right ->
    phased_authority_frame_connected CT h frame
      (FlowPowered, left) (FlowNeutral, right).
Proof.
  intros CT h frame left right Hconnected.
  eapply rt_trans.
  - apply rt_step. apply phased_authority_forget.
  - eapply phased_authority_neutral_mutable_connected. exact Hconnected.
Qed.

Lemma phased_authority_prospective_to_neutral_mutable_connected :
  forall CT h frame left right,
    mutable_connected CT h left right ->
    phased_authority_frame_connected CT h frame
      (FlowProspective, left) (FlowNeutral, right).
Proof.
  intros CT h frame left right Hconnected.
  eapply rt_trans.
  - apply rt_step. apply phased_authority_prospective_forget.
  - eapply phased_authority_neutral_mutable_connected. exact Hconnected.
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

Lemma phased_authority_frame_closure_monotone :
  forall CT h frame old new,
    Included authority_flow_state old new ->
    Included authority_flow_state
      (phased_authority_frame_closure CT h frame old)
      (phased_authority_frame_closure CT h frame new).
Proof.
  intros CT h frame old new Hincluded state [seed [Hseed Hconnected]].
  exists seed. split; [apply Hincluded; exact Hseed|exact Hconnected].
Qed.

Lemma phased_authority_frame_closure_idempotent :
  forall CT h frame seeds,
    Same_set authority_flow_state
      (phased_authority_frame_closure CT h frame
        (phased_authority_frame_closure CT h frame seeds))
      (phased_authority_frame_closure CT h frame seeds).
Proof.
  intros CT h frame seeds. split.
  - intros state [middle [[seed [Hseed Hseed_middle]] Hmiddle_state]].
    exists seed. split; [exact Hseed|]. eapply rt_trans; eauto.
  - eapply phased_authority_frame_closure_contains.
Qed.

Lemma phased_authority_frame_closure_extend :
  forall CT h frame seeds source target,
    In authority_flow_state
      (phased_authority_frame_closure CT h frame seeds) source ->
    phased_authority_frame_connected CT h frame source target ->
    In authority_flow_state
      (phased_authority_frame_closure CT h frame seeds) target.
Proof.
  intros CT h frame seeds source target
    [seed [Hseed Hseed_source]] Hsource_target.
  exists seed. split; [exact Hseed|]. eapply rt_trans; eauto.
Qed.

Lemma phased_authority_return_closure_contains :
  forall h callee boundary seeds,
    Included authority_flow_state seeds
      (phased_authority_return_closure h callee boundary seeds).
Proof.
  intros h callee boundary seeds state Hstate.
  exists state. split; [exact Hstate|apply rt_refl].
Qed.

Lemma phased_authority_return_closure_monotone :
  forall h callee boundary old new,
    Included authority_flow_state old new ->
    Included authority_flow_state
      (phased_authority_return_closure h callee boundary old)
      (phased_authority_return_closure h callee boundary new).
Proof.
  intros h callee boundary old new Hincluded state
    [seed [Hseed Hconnected]].
  exists seed. split; [apply Hincluded; exact Hseed|exact Hconnected].
Qed.

Lemma phased_authority_return_closure_extend :
  forall h callee boundary seeds source target,
    In authority_flow_state
      (phased_authority_return_closure h callee boundary seeds) source ->
    phased_authority_return_connected h callee boundary source target ->
    In authority_flow_state
      (phased_authority_return_closure h callee boundary seeds) target.
Proof.
  intros h callee boundary seeds source target
    [seed [Hseed Hseed_source]] Hsource_target.
  exists seed. split; [exact Hseed|]. eapply rt_trans; eauto.
Qed.

Lemma demote_authority_set_monotone :
  forall old new,
    Included authority_flow_state old new ->
    Included authority_flow_state
      (demote_authority_set old) (demote_authority_set new).
Proof.
  intros old new Hincluded state [mode [location [Hstate Heq]]].
  exists mode, location. split; [apply Hincluded; exact Hstate|exact Heq].
Qed.

Lemma phased_authority_return_connected_normal_form :
  forall h callee boundary source target,
    phased_authority_return_connected h callee boundary source target ->
    source = target \/
    (fst target = FlowNeutral /\
     staged_return_connected h callee boundary (snd source) (snd target)).
Proof.
  intros h callee boundary source target Hconnected.
  induction Hconnected.
  - right. inversion H; subst; simpl.
    + split; [reflexivity|]. apply rt_step. assumption.
    + split; [reflexivity|]. apply rt_step. assumption.
    + split; [reflexivity|]. apply rt_refl.
  - left. reflexivity.
  - destruct IHHconnected1 as [Hxy | [Hymode Hxy]];
      destruct IHHconnected2 as [Hyz | [Hzmode Hyz]].
    + left. congruence.
    + subst x. right. split; assumption.
    + subst z. right. split; assumption.
    + right. split; [exact Hzmode|].
      eapply rt_trans; eauto.
Qed.

Lemma phased_authority_color_set_from_monotone :
  forall CT h active stack old new,
    Included authority_flow_state old new ->
    Included authority_flow_state
      (phased_authority_color_set_from CT h active stack old)
      (phased_authority_color_set_from CT h active stack new).
Proof.
  intros CT h active stack. revert active.
  induction stack as [|boundary tail IH];
    intros active old new Hincluded; simpl.
  - eapply phased_authority_frame_closure_monotone.
    intros state Hstate. inversion Hstate; subst.
    + left. apply Hincluded. exact H.
    + right. exact H.
  - assert (Hframe : Included authority_flow_state
        (phased_authority_frame_closure CT h active
          (Union authority_flow_state old
            (phased_frame_powered_seeds CT h active)))
        (phased_authority_frame_closure CT h active
          (Union authority_flow_state new
            (phased_frame_powered_seeds CT h active)))).
    { eapply phased_authority_frame_closure_monotone.
      intros state Hstate. inversion Hstate; subst.
      - left. apply Hincluded. exact H.
      - right. exact H. }
    intros state Hstate. inversion Hstate; subst.
    + left. apply Hframe. exact H.
    + right. eapply IH; [|exact H].
      eapply phased_authority_return_closure_monotone.
      eapply demote_authority_set_monotone. exact Hframe.
Qed.

Lemma phased_authority_color_set_from_absorbs_active_frame :
  forall CT h active stack incoming,
    Included authority_flow_state
      (phased_authority_color_set_from CT h active stack
        (phased_authority_frame_closure CT h active
          (Union authority_flow_state incoming
            (phased_frame_powered_seeds CT h active))))
      (phased_authority_color_set_from CT h active stack incoming).
Proof.
  intros CT h active stack incoming.
  set (seeds := Union authority_flow_state incoming
    (phased_frame_powered_seeds CT h active)).
  set (closed := phased_authority_frame_closure CT h active seeds).
  assert (Hseed_closed : Included authority_flow_state
      (Union authority_flow_state closed
        (phased_frame_powered_seeds CT h active)) closed).
  { intros state Hstate. inversion Hstate; subst.
    - exact H.
    - unfold closed. eapply phased_authority_frame_closure_contains.
      unfold seeds. right. exact H. }
  assert (Hframe_absorb : Included authority_flow_state
      (phased_authority_frame_closure CT h active
        (Union authority_flow_state closed
          (phased_frame_powered_seeds CT h active))) closed).
  { unfold closed at 2.
    eapply phased_authority_frame_closure_monotone in Hseed_closed.
    intros state Hstate.
    have Htwice := Hseed_closed state Hstate.
    unfold closed in Htwice.
    exact (proj1 (phased_authority_frame_closure_idempotent CT h active seeds)
      state Htwice). }
  destruct stack as [|boundary tail]; simpl.
  - exact Hframe_absorb.
  - intros state Hstate. inversion Hstate; subst.
    + left. apply Hframe_absorb. exact H.
    + right. eapply phased_authority_color_set_from_monotone; [|exact H].
      eapply phased_authority_return_closure_monotone.
      eapply demote_authority_set_monotone. exact Hframe_absorb.
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

Definition pending_authority_reachable
  (CT : class_table) (h : heap)
  (active : watched_frame) (stack : list watched_boundary)
  (left right : Loc) : Prop :=
  authority_flow_connected CT h active stack
    (FlowPowered, left) (FlowPowered, right).

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

Lemma mutable_reachable_is_neutral_authority_flow :
  forall CT h active stack left right,
    mutable_reachable CT h left right ->
    authority_flow_connected CT h active stack
      (FlowNeutral, left) (FlowNeutral, right).
Proof.
  intros CT h active stack left right Hreachable.
  induction Hreachable.
  - apply rt_refl.
  - eapply rt_trans; [exact IHHreachable|].
    apply rt_step. constructor. exact H.
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

Lemma mutable_reachable_is_reverse_powered_authority_flow :
  forall CT h active stack left right,
    mutable_reachable CT h left right ->
    authority_flow_connected CT h active stack
      (FlowPowered, right) (FlowNeutral, left).
Proof.
  intros CT h active stack left right Hreachable.
  eapply rt_trans.
  - apply rt_step. apply authority_flow_forget.
  - eapply mutable_reachable_is_reverse_neutral_authority_flow.
    exact Hreachable.
Qed.

Definition authority_flow_state_live_or_neutral
  (CT : class_table) (h : heap)
  (active : watched_frame) (stack : list watched_boundary)
  (state : authority_flow_state) : Prop :=
  fst state = FlowNeutral \/
  In Loc (live_capability_set CT h active stack) (snd state).

Lemma authority_flow_step_preserves_live_or_neutral :
  forall CT h active stack source target,
    authority_flow_state_live_or_neutral CT h active stack source ->
    authority_flow_step CT h active stack source target ->
    authority_flow_state_live_or_neutral CT h active stack target.
Proof.
  intros CT h active stack source target Hsource Hstep.
  inversion Hstep; subst; simpl in *.
  - right. destruct Hsource as [Hbad | Hlive]; [discriminate|].
    eapply live_capability_set_retained_closed; eauto.
  - left. reflexivity.
  - left. reflexivity.
  - left. reflexivity.
  - left. reflexivity.
  - left. reflexivity.
  - left. reflexivity.
  - right. exact H.
Qed.

Lemma authority_flow_connected_preserves_live_or_neutral :
  forall CT h active stack source target,
    authority_flow_state_live_or_neutral CT h active stack source ->
    authority_flow_connected CT h active stack source target ->
    authority_flow_state_live_or_neutral CT h active stack target.
Proof.
  intros CT h active stack source target Hsource Hconnected.
  induction Hconnected.
  - eapply authority_flow_step_preserves_live_or_neutral; eauto.
  - exact Hsource.
  - apply IHHconnected2. apply IHHconnected1. exact Hsource.
Qed.

Definition authority_colors_separated
  (CT : class_table) (h : heap) (M Z : Ensemble Loc)
  (active : watched_frame) (stack : list watched_boundary) : Prop :=
  forall capability protected,
    In Loc M capability ->
    In Loc Z protected ->
    ~ authority_color_connected CT h active stack capability protected.

(** Transitional pending-call formulation.  The final formulation uses
    [pending_authority_reachable]; this authority-color version remains wired
    into the already-proved transition lemmas while the stateful call-entry
    normal form is completed. *)
Definition pending_call_authority_colors_separated
  (CT : class_table) (h : heap)
  (active : watched_frame) (stack : list watched_boundary) : Prop :=
  forall boundary above below capability owned,
    live_call_partition active stack boundary above below ->
    entry_ownership_channel_free boundary ->
    In Loc (live_capability_set CT h active above) owned ->
    In Loc
      (live_capability_set CT h boundary.(boundary_caller) below) capability ->
    ~ authority_color_connected CT h active stack capability owned.

(** Locations carrying actual mutable authority on the executing side of a
    pending call.  RDM roots are deliberately absent: a prospective RDM join
    enters neutral flow and becomes powered again only at a location that is
    independently in this live-capability set. *)
Definition pending_owned_authority_set
  (CT : class_table) (h : heap)
  (active : watched_frame) (stack : list watched_boundary) : Ensemble Loc :=
  live_capability_set CT h active stack.

Lemma pending_owned_authority_after_active_descent_included :
  forall CT h authority old_senv old_renv new_senv new_renv stack,
    Included Loc
      (live_capability_set CT h
        (mk_watched_frame authority new_senv new_renv) [])
      (live_capability_set CT h
        (mk_watched_frame authority old_senv old_renv) []) ->
    Included Loc
      (pending_owned_authority_set CT h
        (mk_watched_frame authority new_senv new_renv) stack)
      (pending_owned_authority_set CT h
        (mk_watched_frame authority old_senv old_renv) stack).
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv stack
    Hcapabilities location Hlive_capability.
  destruct Hlive_capability as [root [Hroot Hreachable]].
    destruct Hroot as [Hactive | [boundary [Hin Hsuspended]]].
    + have Hold_active : In Loc
          (live_capability_set CT h
            (mk_watched_frame authority old_senv old_renv) []) location.
      { apply Hcapabilities. exists root. split.
        - left. exact Hactive.
        - exact Hreachable. }
      destruct Hold_active as [old_root [Hold_root Hold_reachable]].
      exists old_root. split; [|exact Hold_reachable].
      destruct Hold_root as [Hold_active | [impossible [Hnone _]]].
      * left. exact Hold_active.
      * inversion Hnone.
    + exists root. split.
      * right. exists boundary. split; assumption.
      * exact Hreachable.
Qed.

Definition pending_call_stateful_authority_separated
  (CT : class_table) (h : heap)
  (active : watched_frame) (stack : list watched_boundary)
  (tracked_depth : nat) : Prop :=
  forall boundary above below capability owned,
    live_call_partition active stack boundary above below ->
    length above < tracked_depth ->
    entry_ownership_channel_free boundary ->
    In Loc (pending_owned_authority_set CT h active above) owned ->
    In Loc
      (live_capability_set CT h boundary.(boundary_caller) below) capability ->
    ~ pending_authority_reachable CT h active stack capability owned.

(** Caller-origin colors propagated inward through the currently executing
    call prefix.  Unlike [phased_authority_color_set_from], this construction
    adds no powered seeds from the callee-side frames: it answers exactly
    which authority originated below the pending boundary. *)
Fixpoint pending_caller_colors_through_prefix
  (CT : class_table) (h : heap) (active : watched_frame)
  (above : list watched_boundary)
  (caller_colors : Ensemble authority_flow_state) :
  Ensemble authority_flow_state :=
  match above with
  | [] => phased_authority_frame_closure CT h active caller_colors
  | head :: tail =>
      phased_authority_frame_closure CT h active
        (pending_caller_colors_through_prefix CT h
          head.(boundary_caller) tail caller_colors)
  end.

Definition pending_boundary_caller_color_set
  (CT : class_table) (h : heap) (active : watched_frame)
  (boundary : watched_boundary) (above below : list watched_boundary) :
  Ensemble authority_flow_state :=
  pending_caller_colors_through_prefix CT h active above
    (phased_authority_color_set CT h boundary.(boundary_caller) below).

(** Phase-aware two-color pending invariant.  Caller-originated powered or
    prospective authority must not overlap authority independently owned by
    the executing side of a tracked, ownership-channel-free boundary.
    Prospective colors are essential: an [RDM_f] write may materialize such
    a join into actual retained authority. *)
Definition pending_call_phased_authority_separated
  (CT : class_table) (h : heap)
  (active : watched_frame) (stack : list watched_boundary)
  (tracked_depth : nat) : Prop :=
  forall boundary above below owned mode,
    live_call_partition active stack boundary above below ->
    length above < tracked_depth ->
    entry_ownership_channel_free boundary ->
    In Loc (pending_owned_authority_set CT h active above) owned ->
    authority_mode_dangerous mode ->
    ~ In authority_flow_state
        (pending_boundary_caller_color_set CT h active boundary above below)
        (mode, owned).

Lemma entry_ownership_channel_free_has_no_owned_location :
  forall CT h boundary owned,
    entry_ownership_channel_free boundary ->
    ~ In Loc
        (pending_owned_authority_set CT h
          (mk_watched_frame
            (call_authority boundary.(boundary_caller).(frame_authority)
              boundary.(boundary_receiver_view))
            boundary.(boundary_callee_entry_senv)
            boundary.(boundary_callee_entry_renv)) []) owned.
Proof.
  intros CT h boundary owned [Hno_capability Hno_rdm]
    [root [[Hactive | [suspended [Hin _]]] Hreachable]].
  - exact (Hno_capability root Hactive).
  - inversion Hin.
Qed.

Lemma channel_free_entry_frame_step_reflects :
  forall CT h boundary old_frame source target,
    entry_ownership_channel_free boundary ->
    phased_authority_frame_step CT h
      (mk_watched_frame
        (call_authority boundary.(boundary_caller).(frame_authority)
          boundary.(boundary_receiver_view))
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv)) source target ->
    phased_authority_frame_step CT h old_frame source target.
Proof.
  intros CT h boundary old_frame source target [Hno_capability Hno_rdm]
    Hstep.
  inversion Hstep; subst.
  - apply phased_authority_retained. exact H.
  - apply phased_authority_prospective_retained. exact H.
  - apply phased_authority_prospective_rdm_backward. exact H.
  - apply phased_authority_reverse_rdm. exact H.
  - apply phased_authority_neutral_rdm_forward. exact H.
  - apply phased_authority_neutral_rdm_backward. exact H.
  - exfalso. exact (Hno_rdm left H).
  - exfalso. exact (Hno_rdm left H).
  - exfalso. exact (Hno_rdm left H).
  - apply phased_authority_forget.
  - apply phased_authority_prospective_forget.
  - apply phased_authority_mark_prospective.
  - exfalso.
    destruct H as [root [Hroot Hreachable]].
    exact (Hno_capability root Hroot).
Qed.

Lemma channel_free_entry_frame_connected_reflects :
  forall CT h boundary old_frame source target,
    entry_ownership_channel_free boundary ->
    phased_authority_frame_connected CT h
      (mk_watched_frame
        (call_authority boundary.(boundary_caller).(frame_authority)
          boundary.(boundary_receiver_view))
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv)) source target ->
    phased_authority_frame_connected CT h old_frame source target.
Proof.
  intros CT h boundary old_frame source target Hfree Hconnected.
  induction Hconnected.
  - apply rt_step. eapply channel_free_entry_frame_step_reflects; eauto.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma channel_free_entry_closure_absorbed_by_caller :
  forall CT h boundary caller_seeds state,
    entry_ownership_channel_free boundary ->
    In authority_flow_state
      (phased_authority_frame_closure CT h
        (mk_watched_frame
          (call_authority boundary.(boundary_caller).(frame_authority)
            boundary.(boundary_receiver_view))
          boundary.(boundary_callee_entry_senv)
          boundary.(boundary_callee_entry_renv))
        (phased_authority_frame_closure CT h
          boundary.(boundary_caller) caller_seeds)) state ->
    In authority_flow_state
      (phased_authority_frame_closure CT h
        boundary.(boundary_caller) caller_seeds) state.
Proof.
  intros CT h boundary caller_seeds state Hfree
    [middle [[seed [Hseed Hcaller_path]] Hentry_path]].
  exists seed. split; [exact Hseed|].
  eapply rt_trans; [exact Hcaller_path|].
  eapply channel_free_entry_frame_connected_reflects; eauto.
Qed.

Lemma channel_free_pending_prefix_push_included :
  forall CT h boundary above caller_colors,
    entry_ownership_channel_free boundary ->
    Included authority_flow_state
      (pending_caller_colors_through_prefix CT h
        (mk_watched_frame
          (call_authority boundary.(boundary_caller).(frame_authority)
            boundary.(boundary_receiver_view))
          boundary.(boundary_callee_entry_senv)
          boundary.(boundary_callee_entry_renv))
        (boundary :: above) caller_colors)
      (pending_caller_colors_through_prefix CT h
        boundary.(boundary_caller) above caller_colors).
Proof.
  intros CT h boundary above caller_colors Hfree state Hstate.
  simpl in Hstate.
  destruct above as [|head tail].
  - simpl. eapply channel_free_entry_closure_absorbed_by_caller; eauto.
  - simpl. eapply channel_free_entry_closure_absorbed_by_caller; eauto.
Qed.

Lemma authority_flow_step_after_graph_reflection :
  forall CT h h' active stack source target,
    (forall left right,
      retained_mut_edge CT h' left right ->
      retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right -> mutable_edge CT h left right) ->
    Included Loc
      (live_capability_set CT h' active stack)
      (live_capability_set CT h active stack) ->
    authority_flow_step CT h' active stack source target ->
    authority_flow_step CT h active stack source target.
Proof.
  intros CT h h' active stack source target Hretained Hmutable Hcapability
    Hstep.
  inversion Hstep; subst.
  - apply authority_flow_retained. apply Hretained. exact H.
  - apply authority_flow_reverse_rdm. apply Hmutable. exact H.
  - apply authority_flow_neutral_rdm_forward. apply Hmutable. exact H.
  - apply authority_flow_neutral_rdm_backward. apply Hmutable. exact H.
  - apply authority_flow_powered_frame. exact H.
  - apply authority_flow_neutral_frame. exact H.
  - apply authority_flow_forget.
  - apply authority_flow_promote. apply Hcapability. exact H.
Qed.

Lemma authority_flow_connected_after_graph_reflection :
  forall CT h h' active stack source target,
    (forall left right,
      retained_mut_edge CT h' left right ->
      retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right -> mutable_edge CT h left right) ->
    Included Loc
      (live_capability_set CT h' active stack)
      (live_capability_set CT h active stack) ->
    authority_flow_connected CT h' active stack source target ->
    authority_flow_connected CT h active stack source target.
Proof.
  intros CT h h' active stack source target Hretained Hmutable Hcapability
    Hconnected.
  induction Hconnected.
  - apply rt_step. eapply authority_flow_step_after_graph_reflection; eauto.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma pending_call_stateful_authority_after_graph_reflection :
  forall CT h h' active stack tracked_depth,
    (forall frame substack location,
      In Loc (live_capability_set CT h' frame substack) location ->
      In Loc (live_capability_set CT h frame substack) location) ->
    (forall left right,
      retained_mut_edge CT h' left right ->
      retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right -> mutable_edge CT h left right) ->
    pending_call_stateful_authority_separated CT h active stack
      tracked_depth ->
    pending_call_stateful_authority_separated CT h' active stack
      tracked_depth.
Proof.
  intros CT h h' active stack tracked_depth Hcapability Hretained Hmutable
    Hpending boundary above below capability owned Hpartition Htracked
    Hchannel_free Howned Hcaller Hreachable.
  apply (Hpending boundary above below capability owned Hpartition Htracked
    Hchannel_free
    (Hcapability active above owned Howned)
    (Hcapability boundary.(boundary_caller) below capability Hcaller)).
  eapply authority_flow_connected_after_graph_reflection; eauto.
  intros location Hlocation.
  eapply Hcapability. exact Hlocation.
Qed.

(** An ownership-channel-free call entry creates a genuine ownership boundary.
    Authority retained by the suspended caller must not flow into authority
    acquired locally by the callee.  The color relation is deliberately the
    directed potential graph itself.  In particular, merely naming an RDM
    root does not symmetrically color its inaccessible [Mut_f] descendants.
    RDM field writes merge colors transitionally according to the live
    capability side that owns their endpoints.

    Entries with a capability-bearing or RDM root are intentionally exempt:
    their shared authority is handled by the ordinary potential-color
    invariant and by the stored call-origin certificate.  This is a
    maintained execution color, not a dispatch premise. *)
Definition pending_call_ownership_colors_separated
  (CT : class_table) (h : heap)
  (active : watched_frame) (stack : list watched_boundary) : Prop :=
  forall boundary above below capability owned,
    live_call_partition active stack boundary above below ->
    entry_ownership_channel_free boundary ->
    In Loc (live_capability_set CT h active above) owned ->
    In Loc
      (live_capability_set CT h boundary.(boundary_caller) below) capability ->
    forall common,
      ~ (potential_connected CT h active stack capability common /\
         potential_connected CT h active stack owned common).

(** Depth-indexed form used by the private statement induction.  Boundaries
    already present when the public theorem is invoked are deliberately not
    assumed safe: depth zero tracks none.  Each recursively evaluated call
    pushes one tracked boundary. *)
Definition tracked_pending_call_ownership_colors_separated
  (CT : class_table) (h : heap)
  (active : watched_frame) (stack : list watched_boundary)
  (tracked_depth : nat) : Prop :=
  forall boundary above below capability owned,
    live_call_partition active stack boundary above below ->
    length above < tracked_depth ->
    entry_ownership_channel_free boundary ->
    In Loc (live_capability_set CT h active above) owned ->
    In Loc
      (live_capability_set CT h boundary.(boundary_caller) below) capability ->
    forall common,
      ~ (potential_connected CT h active stack capability common /\
         potential_connected CT h active stack owned common).

Lemma tracked_pending_call_ownership_zero :
  forall CT h active stack,
    tracked_pending_call_ownership_colors_separated CT h active stack 0.
Proof.
  intros CT h active stack boundary above below capability owned Hpartition
    Htracked. lia.
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

(** The layered history state is the authority-sensitive replacement for
    [potential_live_history_state].  It retains the same operational history
    and cutoff facts, but stores only the three coloring layers above rather
    than their unrestricted transitive closure through [Mut_f] edges. *)
Definition layered_live_history_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary) (h : heap) : Prop :=
  live_authority_history_state CT P Z cutoff active stack h /\
  layered_colors_separated CT h
    (live_capability_set CT h active stack) Z active stack /\
  live_boundary_cutoffs_valid h stack.

(** Final temporally staged invariant for flexible calls. *)
Definition staged_live_history_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary) (h : heap) : Prop :=
  live_authority_history_state CT P Z cutoff active stack h /\
  staged_colors_separated CT h
    (live_capability_set CT h active stack) Z active stack /\
  live_boundary_cutoffs_valid h stack.

(** Authority-sensitive flexible-call history: persistent frame joins are
    colored globally; call return remains a transition obligation. *)
Definition authority_color_live_history_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary) (h : heap) : Prop :=
  live_authority_history_state CT P Z cutoff active stack h /\
  authority_colors_separated CT h
    (live_capability_set CT h active stack) Z active stack /\
  live_boundary_cutoffs_valid h stack.

(** The final flexible-call invariant.  Persistent authority joins are
    tracked by [authority_color_live_history_state].  The second conjunct
    records the orthogonal ownership fact needed only for channel-free
    pending calls; it is established and preserved by execution rather than
    assumed by dispatch. *)
Definition principled_authority_color_live_history_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary)
  (tracked_depth : nat) (h : heap) : Prop :=
  authority_color_live_history_state CT P Z cutoff active stack h /\
  pending_call_stateful_authority_separated CT h active stack tracked_depth.

(** Final phase-correct state.  All additional obligations are maintained
    internally; in particular [tracked_depth] is initialized to zero by the
    public theorem and is not a public premise. *)
Definition principled_phased_live_history_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary)
  (tracked_depth : nat) (h : heap) : Prop :=
  live_authority_history_state CT P Z cutoff active stack h /\
  phased_colors_separated CT h Z active stack /\
  live_boundary_cutoffs_valid h stack /\
  pending_call_stateful_authority_separated CT h active stack tracked_depth.

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

(** Private induction package.  The phase component governs the currently
    executing frame; the tracked pending component remembers precisely the
    ownership boundaries whose callers will later resume.  Both indices are
    proof artifacts and are absent from the public preservation theorem. *)
Definition principled_complete_authority_history_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary)
  (incoming : Ensemble authority_flow_state) (tracked_depth : nat)
  (h : heap) : Prop :=
  principled_phased_authority_live_history_state CT P Z cutoff
    active stack incoming h /\
  pending_call_phased_authority_separated CT h active stack tracked_depth.

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

Lemma live_prospective_mutable_authority_components_push_without_active_root :
  forall CT h cutoff caller stack callee boundary,
    boundary.(boundary_caller) = caller ->
    (forall root, ~ mutable_authority_root callee h root) ->
    live_prospective_mutable_authority_components_after_cutoff CT h cutoff
      caller stack ->
    live_prospective_mutable_authority_components_after_cutoff CT h cutoff
      callee (boundary :: stack).
Proof.
  intros CT h cutoff caller stack callee boundary Hcaller Hnone Hold frame
    root target Hlive [Hroot Hpath].
  destruct Hlive as [|boundary0 Hin].
  - exfalso. exact (Hnone root Hroot).
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + subst boundary0. rewrite Hcaller in Hroot, Hpath.
      eapply Hold with (frame := caller) (root := root).
      * constructor.
      * unfold prospective_mutable_authority_reachable. exact (conj Hroot Hpath).
    + eapply Hold with (frame := boundary0.(boundary_caller)) (root := root).
      * constructor. exact Hin.
      * unfold prospective_mutable_authority_reachable. exact (conj Hroot Hpath).
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

Lemma executing_authority_color_set_frozen_closed :
  forall CT h frame incoming,
    Included authority_flow_state
      (frozen_caller_authority_closure CT h frame
        (executing_authority_color_set CT h frame incoming))
      (executing_authority_color_set CT h frame incoming).
Proof.
  intros CT h frame incoming state [middle [Hmiddle Hpath]].
  unfold executing_authority_color_set in *.
  eapply (proj1 (phased_authority_frame_closure_idempotent CT h frame
    (Union authority_flow_state incoming
      (phased_frame_powered_seeds CT h frame)))).
  exists middle. split; [exact Hmiddle|].
  eapply frozen_caller_authority_connected_is_phased. exact Hpath.
Qed.

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

Lemma frozen_snapshot_in_tail_has_partition_below_head :
  forall head snapshots boundary stack snapshot,
    length (Some head :: snapshots) = length (boundary :: stack) ->
    List.In (Some snapshot) snapshots ->
    exists tracked_boundary above below,
      frozen_snapshot_live_partition (Some head :: snapshots)
        (boundary :: stack) snapshot tracked_boundary (boundary :: above)
        below.
Proof.
  intros head snapshots boundary stack snapshot Haligned Hin.
  simpl in Haligned.
  injection Haligned as Htail_length.
  destruct (frozen_snapshot_in_has_live_partition snapshots stack snapshot
    Htail_length Hin) as [tracked_boundary [above [below Hpartition]]].
  exists tracked_boundary, above, below. constructor. exact Hpartition.
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

Lemma frozen_callee_side_components_at_tracked_head :
  forall CT h active snapshot snapshots boundary stack,
    frozen_callee_side_mutable_components_after_boundaries CT h active
      (Some snapshot :: snapshots) (boundary :: stack) ->
    active_mutable_authority_components_after_cutoff CT h
      boundary.(boundary_entry_cutoff) active.
Proof.
  intros CT h active snapshot snapshots boundary stack Hcomponents.
  unfold active_mutable_authority_components_after_cutoff.
  intros root target Hreachable.
  eapply Hcomponents with (snapshot := snapshot) (boundary := boundary)
    (above := []) (below := stack).
  - constructor.
  - constructor.
  - exact Hreachable.
Qed.

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

Lemma repeat_none_callee_side_components :
  forall CT h active stack,
    frozen_callee_side_mutable_components_after_boundaries CT h active
      (repeat None (length stack)) stack.
Proof.
  intros CT h active stack snapshot boundary above below Hpartition.
  exfalso. eapply repeat_none_has_no_frozen_snapshot_partition.
  exact Hpartition.
Qed.

Lemma repeat_none_callee_side_prospective_components :
  forall CT h active stack,
    frozen_callee_side_prospective_components_after_boundaries CT h active
      (repeat None (length stack)) stack.
Proof.
  intros CT h active stack snapshot boundary above below Hpartition.
  exfalso. eapply repeat_none_has_no_frozen_snapshot_partition.
  exact Hpartition.
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

Definition frozen_target_snapshot_list_metadata_le
  (new old : list frozen_caller_snapshot_slot) : Prop :=
  Forall2 frozen_target_snapshot_slot_metadata_le new old.

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

(** A target-only pop transition.  [actual] is the color set of the caller
    that really resumes.  It is accumulated in the target's activation
    history and in its current color image, after which the image is closed
    under the resumed caller.  Entry metadata and latent exposure metadata
    are preserved; the latter's current image merely advances through the
    resumed frame. *)
Definition activate_frozen_target_snapshot
  (CT : class_table) (h : heap) (caller : watched_frame)
  (actual : Ensemble authority_flow_state)
  (snapshot : frozen_caller_color_snapshot) :
  frozen_caller_color_snapshot :=
  mk_frozen_caller_color_snapshot
    snapshot.(frozen_snapshot_entry_colors)
    (frozen_caller_authority_closure CT h caller
      (Union authority_flow_state
        snapshot.(frozen_snapshot_current_colors) actual))
    snapshot.(frozen_snapshot_entry_phase)
    (Union authority_flow_state
      snapshot.(frozen_snapshot_phase_incoming) actual)
    snapshot.(frozen_snapshot_resume_rdm_roots)
    snapshot.(frozen_snapshot_entry_resume_exposure)
    (frozen_caller_authority_closure CT h caller
      snapshot.(frozen_snapshot_current_resume_exposure))
    snapshot.(frozen_snapshot_resume_frame)
    snapshot.(frozen_snapshot_resume_authority).

Definition activate_frozen_target_snapshots
  (CT : class_table) (h : heap) (caller : watched_frame)
  (actual : Ensemble authority_flow_state)
  (snapshots : list frozen_caller_snapshot_slot) :
  list frozen_caller_snapshot_slot :=
  map (fun slot =>
    match slot with
    | Some snapshot =>
        Some (activate_frozen_target_snapshot CT h caller actual snapshot)
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

Lemma advance_frozen_caller_snapshots_metadata_eq :
  forall CT h active snapshots,
    frozen_caller_snapshot_list_metadata_eq
      (advance_frozen_caller_snapshots CT h active snapshots) snapshots.
Proof.
  intros CT h active snapshots. induction snapshots as [|slot tail IH].
  - constructor.
  - unfold advance_frozen_caller_snapshots. simpl. constructor; [|exact IH].
    destruct slot as [snapshot|]; simpl; [|exact I].
    apply advance_frozen_caller_snapshot_metadata_eq.
Qed.

Lemma frozen_caller_snapshot_metadata_eq_target_le :
  forall new old,
    frozen_caller_snapshot_metadata_eq new old ->
    frozen_target_snapshot_metadata_le new old.
Proof.
  intros new old
    [Hentry [Hentry_phase [Hphase [Hroots
      [Hexposure [Hframe Hauthority]]]]]].
  unfold frozen_target_snapshot_metadata_le.
  exact (conj Hentry (conj Hentry_phase (conj (proj2 Hphase) (conj Hroots
    (conj Hexposure (conj Hframe Hauthority)))))).
Qed.

Lemma frozen_caller_snapshot_list_metadata_eq_target_le :
  forall new old,
    frozen_caller_snapshot_list_metadata_eq new old ->
    frozen_target_snapshot_list_metadata_le new old.
Proof.
  intros new old Hmetadata. induction Hmetadata; constructor; [|exact IHHmetadata].
  destruct x, y; simpl in *; try contradiction; [|exact I].
  eapply frozen_caller_snapshot_metadata_eq_target_le. exact H.
Qed.

Lemma activate_frozen_target_snapshot_metadata_le :
  forall CT h caller actual snapshot,
    frozen_target_snapshot_metadata_le
      (activate_frozen_target_snapshot CT h caller actual snapshot) snapshot.
Proof.
  intros CT h caller actual snapshot.
  unfold frozen_target_snapshot_metadata_le,
    activate_frozen_target_snapshot. simpl.
  repeat split; try reflexivity; try (intros state Hstate; exact Hstate).
  intros state Hstate. left. exact Hstate.
Qed.

Lemma frozen_target_snapshot_metadata_le_trans :
  forall newer middle older,
    frozen_target_snapshot_metadata_le newer middle ->
    frozen_target_snapshot_metadata_le middle older ->
    frozen_target_snapshot_metadata_le newer older.
Proof.
  intros newer middle older
    [Hentry1 [HentryPhase1 [Hphase1 [Hroots1
      [Hexposure1 [Hframe1 Hauthority1]]]]]]
    [Hentry2 [HentryPhase2 [Hphase2 [Hroots2
      [Hexposure2 [Hframe2 Hauthority2]]]]]].
  unfold frozen_target_snapshot_metadata_le.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - destruct Hentry1 as [Hentry1f Hentry1b].
    destruct Hentry2 as [Hentry2f Hentry2b].
    split; intros state Hstate; eauto.
  - destruct HentryPhase1 as [HentryPhase1f HentryPhase1b].
    destruct HentryPhase2 as [HentryPhase2f HentryPhase2b].
    split; intros state Hstate; eauto.
  - intros state Hstate. eauto.
  - destruct Hroots1 as [Hroots1f Hroots1b].
    destruct Hroots2 as [Hroots2f Hroots2b].
    split; intros root Hroot; eauto.
  - destruct Hexposure1 as [Hexposure1f Hexposure1b].
    destruct Hexposure2 as [Hexposure2f Hexposure2b].
    split; intros state Hstate; eauto.
  - congruence.
  - congruence.
Qed.

Lemma frozen_target_snapshot_list_metadata_le_trans :
  forall newer middle older,
    frozen_target_snapshot_list_metadata_le newer middle ->
    frozen_target_snapshot_list_metadata_le middle older ->
    frozen_target_snapshot_list_metadata_le newer older.
Proof.
  intros newer middle older Hnew Hmiddle.
  revert older Hmiddle. induction Hnew; intros older Hmiddle;
    inversion Hmiddle; subst; constructor.
  - destruct x, y, y0; simpl in *; try contradiction; [|exact I].
    eapply frozen_target_snapshot_metadata_le_trans; eauto.
  - eapply IHHnew. exact H4.
Qed.

Lemma frozen_caller_snapshot_metadata_eq_trans :
  forall newer middle older,
    frozen_caller_snapshot_metadata_eq newer middle ->
    frozen_caller_snapshot_metadata_eq middle older ->
    frozen_caller_snapshot_metadata_eq newer older.
Proof.
  intros newer middle older Hmetadata1 Hmetadata2.
  unfold frozen_caller_snapshot_metadata_eq in Hmetadata1, Hmetadata2 |-*.
  destruct Hmetadata1 as
    [Hentry1 [HentryPhase1 [Hphase1 [Hroots1
      [Hexposure1 [Hframe1 Hauthority1]]]]]].
  destruct Hmetadata2 as
    [Hentry2 [HentryPhase2 [Hphase2 [Hroots2
      [Hexposure2 [Hframe2 Hauthority2]]]]]].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - destruct Hentry1 as [Hforward1 Hback1].
    destruct Hentry2 as [Hforward2 Hback2]. split; intros state Hstate.
    + exact (Hforward2 state (Hforward1 state Hstate)).
    + exact (Hback1 state (Hback2 state Hstate)).
  - destruct HentryPhase1 as [Hforward1 Hback1].
    destruct HentryPhase2 as [Hforward2 Hback2]. split; intros state Hstate.
    + exact (Hforward2 state (Hforward1 state Hstate)).
    + exact (Hback1 state (Hback2 state Hstate)).
  - destruct Hphase1 as [Hforward1 Hback1].
    destruct Hphase2 as [Hforward2 Hback2]. split; intros state Hstate.
    + exact (Hforward2 state (Hforward1 state Hstate)).
    + exact (Hback1 state (Hback2 state Hstate)).
  - destruct Hroots1 as [Hforward1 Hback1].
    destruct Hroots2 as [Hforward2 Hback2]. split; intros root Hroot.
    + exact (Hforward2 root (Hforward1 root Hroot)).
    + exact (Hback1 root (Hback2 root Hroot)).
  - destruct Hexposure1 as [Hforward1 Hback1].
    destruct Hexposure2 as [Hforward2 Hback2]. split; intros state Hstate.
    + exact (Hforward2 state (Hforward1 state Hstate)).
    + exact (Hback1 state (Hback2 state Hstate)).
  - congruence.
  - congruence.
Qed.

Lemma frozen_caller_snapshot_list_metadata_eq_trans :
  forall newer middle older,
    frozen_caller_snapshot_list_metadata_eq newer middle ->
    frozen_caller_snapshot_list_metadata_eq middle older ->
    frozen_caller_snapshot_list_metadata_eq newer older.
Proof.
  intros newer middle older Hnew Hmiddle.
  revert older Hmiddle. induction Hnew; intros older Hmiddle;
    inversion Hmiddle; subst; constructor.
  - destruct x, y, y0; simpl in *; try contradiction; [|exact I].
    eapply frozen_caller_snapshot_metadata_eq_trans; eauto.
  - eapply IHHnew. exact H4.
Qed.

Lemma frozen_caller_snapshot_list_metadata_eq_head_some :
  forall final initial_snapshot initial_tail,
    frozen_caller_snapshot_list_metadata_eq final
      (Some initial_snapshot :: initial_tail) ->
    exists final_snapshot final_tail,
      final = Some final_snapshot :: final_tail /\
      frozen_caller_snapshot_metadata_eq final_snapshot initial_snapshot /\
      frozen_caller_snapshot_list_metadata_eq final_tail initial_tail.
Proof.
  intros final initial_snapshot initial_tail Hmetadata.
  destruct final as [|slot final_tail].
  - inversion Hmetadata.
  - inversion Hmetadata as [|a b l l' Hhead Htail]; subst.
    destruct slot as [final_snapshot|]; simpl in Hhead.
    + exists final_snapshot, final_tail. split; [reflexivity|].
      split; [exact Hhead|exact Htail].
    + contradiction.
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

Definition enter_nested_frozen_caller_snapshots
  (CT : class_table) (h : heap) (caller callee : watched_frame)
  (caller_colors : Ensemble authority_flow_state)
  (snapshots : list frozen_caller_snapshot_slot) :
  list frozen_caller_snapshot_slot :=
  Some (nested_frozen_call_head CT h caller callee caller_colors snapshots) ::
  advance_frozen_caller_snapshots CT h callee snapshots.

Lemma nested_frozen_head_metadata_recovers_phase_incoming :
  forall CT h caller callee caller_colors snapshots final_head,
    frozen_caller_snapshot_metadata_eq final_head
      (nested_frozen_call_head CT h caller callee caller_colors snapshots) ->
    Same_set authority_flow_state final_head.(frozen_snapshot_phase_incoming)
      caller_colors.
Proof.
  intros CT h caller callee caller_colors snapshots final_head Hmetadata.
  exact (proj1 (proj2 (proj2 Hmetadata))).
Qed.

Lemma nested_frozen_head_metadata_recovers_resume_roots :
  forall CT h caller callee caller_colors snapshots final_head,
    frozen_caller_snapshot_metadata_eq final_head
      (nested_frozen_call_head CT h caller callee caller_colors snapshots) ->
    Same_set Loc final_head.(frozen_snapshot_resume_rdm_roots)
      (frame_rdm_root_set caller).
Proof.
  intros CT h caller callee caller_colors snapshots final_head Hmetadata.
  exact (proj1 (proj2 (proj2 (proj2 Hmetadata)))).
Qed.

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

Lemma frozen_callee_side_components_enter_nested_without_authority :
  forall CT h caller callee caller_colors snapshots boundary stack,
    boundary.(boundary_caller) = caller ->
    (forall root, ~ mutable_authority_root callee h root) ->
    frozen_callee_side_mutable_components_after_boundaries CT h caller
      snapshots stack ->
    frozen_callee_side_mutable_components_after_boundaries CT h callee
      (enter_nested_frozen_caller_snapshots CT h caller callee caller_colors
        snapshots) (boundary :: stack).
Proof.
  intros CT h caller callee caller_colors snapshots boundary stack Hcaller
    Hnone Hold snapshot tracked_boundary above below Hpartition.
  unfold enter_nested_frozen_caller_snapshots in Hpartition.
  inversion Hpartition; subst.
  - intros frame root target Hframe Hreachable.
    inversion Hframe; subst.
    + exfalso. eapply Hnone.
      eapply mutable_authority_reachable_has_root. exact Hreachable.
    + inversion H.
  - destruct (advance_frozen_snapshot_live_partition_reflects CT h callee
      snapshots stack snapshot tracked_boundary above0 below H7) as
      [old_snapshot Hold_partition].
    have Hold_components := Hold old_snapshot tracked_boundary above0 below
      Hold_partition.
    eapply live_mutable_authority_components_push_without_active_authority
      with (caller := boundary.(boundary_caller)) (boundary := boundary);
      eauto.
Qed.

Lemma frozen_callee_side_prospective_components_enter_nested_without_authority :
  forall CT h caller callee caller_colors snapshots boundary stack,
    boundary.(boundary_caller) = caller ->
    (forall root, ~ mutable_authority_root callee h root) ->
    frozen_callee_side_prospective_components_after_boundaries CT h caller
      snapshots stack ->
    frozen_callee_side_prospective_components_after_boundaries CT h callee
      (enter_nested_frozen_caller_snapshots CT h caller callee caller_colors
        snapshots) (boundary :: stack).
Proof.
  intros CT h caller callee caller_colors snapshots boundary stack Hcaller
    Hnone Hold snapshot tracked_boundary above below Hpartition.
  unfold enter_nested_frozen_caller_snapshots in Hpartition.
  inversion Hpartition; subst.
  - intros frame root target Hframe [Hroot Hpath].
    inversion Hframe; subst.
    + exfalso. exact (Hnone root Hroot).
    + inversion H.
  - destruct (advance_frozen_snapshot_live_partition_reflects CT h callee
      snapshots stack snapshot tracked_boundary above0 below H7) as
      [old_snapshot Hold_partition].
    have Hold_components := Hold old_snapshot tracked_boundary above0 below
      Hold_partition.
    eapply live_prospective_mutable_authority_components_push_without_active_root
      with (caller := boundary.(boundary_caller)) (boundary := boundary);
      eauto.
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

Lemma repeat_none_snapshots_newer_resume_exposure_disjoint :
  forall count,
    frozen_caller_snapshots_newer_resume_exposure_disjoint
      (repeat (None : frozen_caller_snapshot_slot) count).
Proof.
  intros count. induction count; simpl; auto.
Qed.

Lemma frozen_caller_snapshots_newer_resume_exposure_disjoint_tail :
  forall head tail,
    frozen_caller_snapshots_newer_resume_exposure_disjoint (head :: tail) ->
    frozen_caller_snapshots_newer_resume_exposure_disjoint tail.
Proof.
  intros [snapshot|] tail Hdisjoint; simpl in *; tauto.
Qed.

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

Lemma frozen_caller_snapshots_nested_resume_safe_tail :
  forall Z head tail,
    frozen_caller_snapshots_nested_resume_safe Z (head :: tail) ->
    frozen_caller_snapshots_nested_resume_safe Z tail.
Proof.
  intros Z [snapshot|] tail Hsafe; simpl in Hsafe; tauto.
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

Lemma enter_nested_frozen_caller_snapshots_nested_covered :
  forall CT h caller callee caller_colors snapshots,
    frozen_caller_snapshots_nested_covered snapshots ->
    frozen_caller_snapshots_nested_covered
      (enter_nested_frozen_caller_snapshots CT h caller callee
        caller_colors snapshots).
Proof.
  intros CT h caller callee caller_colors snapshots Hcovered.
  unfold enter_nested_frozen_caller_snapshots. simpl. split.
  - intros older Holder.
    unfold advance_frozen_caller_snapshots in Holder.
    apply in_map_iff in Holder.
    destruct Holder as [slot [Heq Hslot]].
    destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as Heq. subst older. simpl.
    apply frozen_caller_snapshot_closure_monotone.
    intros state Hstate. right.
    exists old_snapshot. split; assumption.
  - apply advance_frozen_caller_snapshots_nested_covered. exact Hcovered.
Qed.

Lemma frozen_caller_snapshots_nested_covered_tail :
  forall head tail,
    frozen_caller_snapshots_nested_covered (head :: tail) ->
    frozen_caller_snapshots_nested_covered tail.
Proof.
  intros [snapshot|] tail Hcovered; simpl in Hcovered; tauto.
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

Lemma repeat_none_snapshot_boundaries_after_cutoff :
  forall cutoff stack,
    frozen_snapshot_boundaries_after_cutoff cutoff
      (repeat (None : frozen_caller_snapshot_slot) (length stack)) stack.
Proof.
  intros cutoff stack. induction stack; simpl.
  - constructor.
  - constructor; [exact I|exact IHstack].
Qed.

Lemma advance_snapshot_boundaries_after_cutoff :
  forall CT h active cutoff snapshots stack,
    frozen_snapshot_boundaries_after_cutoff cutoff snapshots stack ->
    frozen_snapshot_boundaries_after_cutoff cutoff
      (advance_frozen_caller_snapshots CT h active snapshots) stack.
Proof.
  intros CT h active cutoff snapshots stack Hafter.
  induction Hafter; constructor; [|exact IHHafter].
  destruct x; exact H.
Qed.

Lemma tracked_snapshot_boundaries_after_cutoff_push :
  forall CT h caller callee caller_colors cutoff snapshots boundary stack,
    cutoff <= boundary.(boundary_entry_cutoff) ->
    frozen_snapshot_boundaries_after_cutoff cutoff snapshots stack ->
    frozen_snapshot_boundaries_after_cutoff cutoff
      (enter_nested_frozen_caller_snapshots CT h caller callee caller_colors
        snapshots) (boundary :: stack).
Proof.
  intros CT h caller callee caller_colors cutoff snapshots boundary stack
    Hboundary Htail.
  unfold enter_nested_frozen_caller_snapshots. constructor; [exact Hboundary|].
  eapply advance_snapshot_boundaries_after_cutoff. exact Htail.
Qed.

Lemma snapshot_boundaries_after_cutoff_tail :
  forall cutoff head snapshots boundary stack,
    frozen_snapshot_boundaries_after_cutoff cutoff (head :: snapshots)
      (boundary :: stack) ->
    frozen_snapshot_boundaries_after_cutoff cutoff snapshots stack.
Proof.
  intros cutoff head snapshots boundary stack Hafter. inversion Hafter; subst.
  exact H4.
Qed.

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

Lemma tracked_head_prospective_component_avoids_older_protected :
  forall CT h Z cutoff active head snapshots boundary stack older root target,
    length (Some head :: snapshots) = length (boundary :: stack) ->
    frozen_callee_side_prospective_components_after_boundaries CT h active
      (Some head :: snapshots) (boundary :: stack) ->
    frozen_snapshot_boundaries_after_cutoff cutoff
      (Some head :: snapshots) (boundary :: stack) ->
    protected_zone_before_cutoff Z cutoff ->
    List.In (Some older) snapshots ->
    prospective_mutable_authority_reachable CT h
      boundary.(boundary_caller) root target ->
    ~ In Loc Z target.
Proof.
  intros CT h Z cutoff active head snapshots boundary stack older root target
    Haligned Hcomponents Hafter Hzone Hold Hreachable Hprotected.
  destruct (frozen_snapshot_in_tail_has_partition_below_head head snapshots
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

Lemma tracked_head_caller_component_avoids_protected :
  forall CT h Z cutoff active head snapshots boundary stack older root target,
    length (Some head :: snapshots) = length (boundary :: stack) ->
    frozen_callee_side_mutable_components_after_boundaries CT h active
      (Some head :: snapshots) (boundary :: stack) ->
    frozen_snapshot_boundaries_after_cutoff cutoff
      (Some head :: snapshots) (boundary :: stack) ->
    protected_zone_before_cutoff Z cutoff ->
    List.In (Some older) snapshots ->
    mutable_authority_reachable CT h boundary.(boundary_caller) root target ->
    ~ In Loc Z target.
Proof.
  intros CT h Z cutoff active head snapshots boundary stack older root target
    Haligned Hcomponents Hafter Hzone Hold Hreachable Hprotected.
  destruct (frozen_snapshot_in_tail_has_partition_below_head head snapshots
    boundary stack older Haligned Hold) as
    [older_boundary [above [below Hpartition]]].
  have Hcomponent_fresh : older_boundary.(boundary_entry_cutoff) <= target.
  { eapply Hcomponents with (snapshot := older) (above := boundary :: above)
      (below := below) (root := root).
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

Lemma frozen_snapshot_head_before_boundary :
  forall snapshot snapshots boundary stack,
    frozen_caller_snapshots_before_boundaries
      (Some snapshot :: snapshots) (boundary :: stack) ->
    (forall mode location,
      In authority_flow_state snapshot.(frozen_snapshot_entry_phase)
        (mode, location) ->
      location < boundary.(boundary_entry_cutoff)) /\
    (forall root,
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) root ->
      root < boundary.(boundary_entry_cutoff)) /\
    frozen_caller_snapshots_before_boundaries snapshots stack.
Proof.
  intros snapshot snapshots boundary stack Hbefore.
  inversion Hbefore as [|slot boundary' slots stack' Hhead Htail]; subst.
  simpl in Hhead. tauto.
Qed.

(** There is exactly one proof slot per operational boundary.  A [None] slot
    denotes a pre-existing or untracked call.  Exact alignment makes pop
    compositional: it always removes the head slot, without guessing whether
    the top call was tracked. *)
Definition frozen_caller_snapshots_aligned
  (snapshots : list frozen_caller_snapshot_slot)
  (stack : list watched_boundary) : Prop :=
  length snapshots = length stack.

(** Caller-originated dangerous colors may not coincide with authority owned
    independently by the executing frame.  This is an invariant over carried
    ghost data, not a premise on dispatch or on the public theorem. *)
Definition frozen_caller_snapshots_separated
  (CT : class_table) (h : heap) (active : watched_frame)
  (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  forall snapshot mode owned,
    List.In (Some snapshot) snapshots ->
    authority_mode_dangerous mode ->
    frame_owned_location CT h active owned ->
    ~ In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (mode, owned).

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

Definition frozen_caller_snapshots_independently_separated
  (CT : class_table) (h : heap) (active : watched_frame)
  (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  forall snapshot caller_mode active_mode location,
    List.In (Some snapshot) snapshots ->
    authority_mode_dangerous caller_mode ->
    authority_mode_dangerous active_mode ->
    In authority_flow_state
      snapshot.(frozen_snapshot_current_colors) (caller_mode, location) ->
    ~ In authority_flow_state
      (independent_active_authority_colors CT h active)
      (active_mode, location).

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

(** Target-policy authority is interpreted by the suspended caller that will
    resume, independently of whichever nested callee is currently active. *)
Definition frozen_snapshot_saved_resume_exposure
  (CT : class_table) (h : heap) (snapshot : frozen_caller_color_snapshot) :
  Ensemble authority_flow_state :=
  frozen_caller_authority_closure CT h
    snapshot.(frozen_snapshot_resume_frame)
    snapshot.(frozen_snapshot_entry_resume_exposure).

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

Fixpoint frozen_target_snapshots_nested_resume_phase_safe
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (targets : list frozen_caller_snapshot_slot) : Prop :=
  match targets with
  | [] => True
  | Some newer :: tail =>
      (frozen_snapshot_resume_activated newer ->
       frozen_target_colors_resume_phase_safe CT h Z
         newer.(frozen_snapshot_current_resume_exposure) tail) /\
      frozen_target_snapshots_nested_resume_phase_safe CT h Z tail
  | None :: tail =>
      frozen_target_snapshots_nested_resume_phase_safe CT h Z tail
  end.

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

(** Allocation-stable overlap certificate used by the final return
    classifier.  Unlike [frozen_caller_snapshots_active_resume_justified],
    the overlap location need not itself be a captured resume root.  A
    harmless fresh overlap is admitted: it either retains a captured caller
    origin, or records exactly that every target exposed on resume is outside
    the protected zone. *)
Definition frozen_caller_snapshots_active_overlap_justified
  (CT : class_table) (h : heap) (Z : Ensemble Loc) (active : watched_frame)
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
    (exists root_mode root,
      authority_mode_dangerous root_mode /\
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (root_mode, root) /\
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) root) \/
    frozen_snapshot_resume_exposure_avoids Z snapshot.

(** Compositional form carried by statement preservation.  Incoming caller
    authority is semantically live while the active frame executes and must
    therefore participate in the overlap invariant.  Unlike the active-only
    projection above, this definition is closed under call entry and return. *)
Definition frozen_caller_snapshots_executing_overlap_justified
  (CT : class_table) (h : heap) (Z : Ensemble Loc) (active : watched_frame)
  (incoming : Ensemble authority_flow_state)
  (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  forall snapshot snapshot_mode active_mode location,
    List.In (Some snapshot) snapshots ->
    authority_mode_dangerous snapshot_mode ->
    authority_mode_dangerous active_mode ->
    In authority_flow_state snapshot.(frozen_snapshot_current_colors)
      (snapshot_mode, location) ->
    (In authority_flow_state
       (executing_authority_color_set CT h active incoming)
       (active_mode, location) \/
     typed_root RDM active.(frame_senv) active.(frame_renv) location) ->
    (exists root_mode root,
      authority_mode_dangerous root_mode /\
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (root_mode, root) /\
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) root) \/
    frozen_snapshot_resume_exposure_avoids Z snapshot.

Lemma executing_overlap_justified_implies_active_overlap_justified :
  forall CT h Z active incoming snapshots,
    frozen_caller_snapshots_executing_overlap_justified CT h Z active incoming
      snapshots ->
    frozen_caller_snapshots_active_overlap_justified CT h Z active snapshots.
Proof.
  intros CT h Z active incoming snapshots Hoverlap snapshot snapshot_mode
    active_mode location Hsnapshot Hsnapshot_mode Hactive_mode Hcolor Htrigger.
  destruct Htrigger as [Hactive | Hrdm].
  - exact (Hoverlap snapshot snapshot_mode active_mode location Hsnapshot
      Hsnapshot_mode Hactive_mode Hcolor
      (or_introl (independent_active_authority_colors_in_executing CT h active
        incoming (active_mode, location) Hactive))).
  - exact (Hoverlap snapshot snapshot_mode active_mode location Hsnapshot
      Hsnapshot_mode Hactive_mode Hcolor (or_intror Hrdm)).
Qed.

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

(** Any frozen seed used to build a new nested head is safe against every
    older continuation.  If the seed comes from the target snapshot itself,
    or from a still older snapshot already summarized by it, use the target's
    own join certificate.  If it comes from a newer snapshot, use the
    pairwise certificate. *)
Lemma frozen_snapshot_current_color_union_resume_safe :
  forall Z snapshots target source_mode source,
    frozen_caller_snapshots_nested_covered snapshots ->
    frozen_caller_snapshots_nested_resume_safe Z snapshots ->
    frozen_caller_snapshots_resume_joins_safe Z snapshots ->
    List.In (Some target) snapshots ->
    authority_mode_dangerous source_mode ->
    In authority_flow_state
      (frozen_caller_snapshot_current_color_union snapshots)
      (source_mode, source) ->
    In Loc target.(frozen_snapshot_resume_rdm_roots) source ->
    (exists entry_mode,
      authority_mode_dangerous entry_mode /\
      In authority_flow_state target.(frozen_snapshot_entry_colors)
        (entry_mode, source)) \/
    (forall exposure_mode target_location,
      authority_mode_dangerous exposure_mode ->
      In authority_flow_state
        target.(frozen_snapshot_current_resume_exposure)
        (exposure_mode, target_location) ->
      ~ In Loc Z target_location).
Proof.
  intros Z snapshots. induction snapshots as [|slot tail IH];
    intros target source_mode source Hcovered Hnested Hjoins Htarget
      Hsource_mode [source_snapshot [Hsource_snapshot Hsource_color]]
      Hsource_root; simpl in *; [contradiction|].
  destruct slot as [head|].
  - destruct Hcovered as [Hhead_covered Htail_covered].
    destruct Hnested as [Hhead_safe Htail_safe].
    destruct Htarget as [Htarget_head | Htarget_tail].
    + injection Htarget_head as Heq. subst target.
      destruct Hsource_snapshot as [Hsource_head | Hsource_tail].
      * injection Hsource_head as Heq. subst source_snapshot.
        eapply Hjoins; [simpl; auto|exact Hsource_mode|exact Hsource_color|].
        exact Hsource_root.
      * eapply Hjoins; [simpl; auto|exact Hsource_mode| |exact Hsource_root].
        eapply Hhead_covered; eauto.
    + destruct Hsource_snapshot as [Hsource_head | Hsource_tail].
      * injection Hsource_head as Heq. subst source_snapshot.
        eapply Hhead_safe; eauto.
      * have Hjoins_tail : frozen_caller_snapshots_resume_joins_safe Z tail.
        { intros older mode location Holder Hmode Hcolor Hroot.
          exact (Hjoins older mode location (or_intror Holder) Hmode Hcolor
            Hroot). }
        exact (IH target source_mode source Htail_covered Htail_safe
          Hjoins_tail Htarget_tail Hsource_mode
          (ex_intro _ source_snapshot (conj Hsource_tail Hsource_color))
          Hsource_root).
  - have Hjoins_tail : frozen_caller_snapshots_resume_joins_safe Z tail.
    { intros older mode location Holder Hmode Hcolor Hroot.
      exact (Hjoins older mode location (or_intror Holder) Hmode Hcolor Hroot). }
    destruct Htarget as [Hbad | Htarget]; [discriminate|].
    destruct Hsource_snapshot as [Hbad | Hsource_snapshot]; [discriminate|].
    exact (IH target source_mode source Hcovered Hnested Hjoins_tail Htarget
      Hsource_mode
      (ex_intro _ source_snapshot (conj Hsource_snapshot Hsource_color))
      Hsource_root).
Qed.

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

Lemma nested_frozen_call_head_resume_safe_against_advanced_tail :
  forall CT h Z boundary caller_colors snapshots,
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
    frozen_caller_snapshots_nested_covered snapshots ->
    frozen_caller_snapshots_nested_resume_safe Z snapshots ->
    frozen_caller_snapshots_resume_joins_safe Z snapshots ->
    frozen_completed_colors_resume_safe Z caller_colors snapshots ->
    (forall old_snapshot exposure_mode target,
      List.In (Some old_snapshot) snapshots ->
      authority_mode_dangerous exposure_mode ->
      In authority_flow_state
        (frozen_caller_authority_closure CT h callee
          old_snapshot.(frozen_snapshot_current_resume_exposure))
        (exposure_mode, target) ->
      (forall old_mode,
        authority_mode_dangerous old_mode ->
        In authority_flow_state
          old_snapshot.(frozen_snapshot_current_resume_exposure)
          (old_mode, target) ->
        ~ In Loc Z target) ->
      ~ In Loc Z target) ->
    forall new_older,
      List.In (Some new_older)
        (advance_frozen_caller_snapshots CT h callee snapshots) ->
      frozen_snapshot_resume_safe_against Z
        (nested_frozen_call_head CT h caller callee caller_colors snapshots)
        new_older.
Proof.
  intros CT h Z boundary caller_colors snapshots caller callee Hfree
    Hcaller_closed Hsnapshots_closed Hcovered Hnested Hjoins Hcompleted
    Hlift new_older Hnew source_mode source Hsource_mode Hsource Hsource_root.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_older|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_older. simpl in *.
  have Hclassification :=
    nested_frozen_call_head_color_reflects_at_channel_free_entry CT h
      boundary caller_colors snapshots (source_mode, source) Hfree
      Hcaller_closed Hsnapshots_closed Hsource.
  destruct Hclassification as
    [Hcaller_source | [source_snapshot [Hsource_snapshot Hsnapshot_source]]].
  - destruct (Hcompleted old_older source_mode source Hold Hsource_mode
      Hcaller_source Hsource_root) as
      [[entry_mode [Hentry_mode Hentry]] | Hsafe].
    + left. exists entry_mode. split; assumption.
    + right. intros exposure_mode target Hexposure_mode Htarget.
      eapply Hlift; [exact Hold|exact Hexposure_mode|exact Htarget|].
      intros old_mode Hold_mode Hold_target. eapply Hsafe; eauto.
  - destruct (frozen_snapshot_current_color_union_resume_safe Z snapshots
      old_older source_mode source Hcovered Hnested Hjoins Hold Hsource_mode
      (ex_intro _ source_snapshot (conj Hsource_snapshot Hsnapshot_source))
      Hsource_root) as
      [[entry_mode [Hentry_mode Hentry]] | Hsafe].
    + left. exists entry_mode. split; assumption.
    + right. intros exposure_mode target Hexposure_mode Htarget.
      eapply Hlift; [exact Hold|exact Hexposure_mode|exact Htarget|].
      intros old_mode Hold_mode Hold_target. eapply Hsafe; eauto.
Qed.

Lemma nested_frozen_call_head_runtime_mutable :
  forall CT h boundary caller_colors snapshots,
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
    authority_colors_runtime_mutable h caller_colors ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_closed CT h caller snapshots ->
    authority_colors_runtime_mutable h
      (nested_frozen_call_head CT h caller callee caller_colors snapshots)
        .(frozen_snapshot_current_colors).
Proof.
  intros CT h boundary caller_colors snapshots caller callee Hfree
    Hcaller_closed Hcaller_runtime Hsnapshots_runtime Hsnapshots_closed mode
    location Hcolor.
  destruct (nested_frozen_call_head_color_reflects_at_channel_free_entry
    CT h boundary caller_colors snapshots (mode, location) Hfree
    Hcaller_closed Hsnapshots_closed Hcolor) as
    [Hcaller | [snapshot [Hsnapshot Hsnapshot_color]]].
  - eapply Hcaller_runtime. exact Hcaller.
  - eapply Hsnapshots_runtime; eauto.
Qed.

Lemma nested_frozen_call_head_closed :
  forall CT h caller callee caller_colors snapshots,
    Included authority_flow_state
      (frozen_caller_authority_closure CT h callee
        (nested_frozen_call_head CT h caller callee caller_colors snapshots)
          .(frozen_snapshot_current_colors))
      (nested_frozen_call_head CT h caller callee caller_colors snapshots)
        .(frozen_snapshot_current_colors).
Proof.
  intros CT h caller callee caller_colors snapshots.
  unfold nested_frozen_call_head. simpl.
  exact (proj1 (frozen_caller_authority_closure_idempotent CT h callee
    (nested_frozen_call_entry_seeds caller_colors snapshots))).
Qed.

Lemma nested_frozen_call_head_retains_entry :
  forall CT h caller callee caller_colors snapshots,
    Included authority_flow_state
      (nested_frozen_call_head CT h caller callee caller_colors snapshots)
        .(frozen_snapshot_entry_colors)
      (nested_frozen_call_head CT h caller callee caller_colors snapshots)
        .(frozen_snapshot_current_colors).
Proof.
  intros. unfold nested_frozen_call_head. simpl. intros state Hstate.
  exact Hstate.
Qed.

Lemma nested_frozen_call_head_avoids_protected :
  forall CT h Z boundary caller_colors snapshots mode location,
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
    (forall caller_mode caller_location,
      authority_mode_dangerous caller_mode ->
      In authority_flow_state caller_colors
        (caller_mode, caller_location) ->
      ~ In Loc Z caller_location) ->
    frozen_caller_snapshots_closed CT h caller snapshots ->
    frozen_caller_snapshots_avoid_protected Z snapshots ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (nested_frozen_call_head CT h caller callee caller_colors snapshots)
        .(frozen_snapshot_current_colors) (mode, location) ->
    ~ In Loc Z location.
Proof.
  intros CT h Z boundary caller_colors snapshots mode location caller callee
    Hfree Hcaller_closed Hcaller_separated Hsnapshots_closed Hsnapshots_avoid
    Hmode Hcolor.
  destruct (nested_frozen_call_head_color_reflects_at_channel_free_entry
    CT h boundary caller_colors snapshots (mode, location) Hfree
    Hcaller_closed Hsnapshots_closed Hcolor) as
    [Hcaller | [snapshot [Hsnapshot Hsnapshot_color]]].
  - eapply Hcaller_separated; eauto.
  - eapply Hsnapshots_avoid; eauto.
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

Lemma nested_frozen_call_head_dangerous :
  forall CT h caller callee caller_colors snapshots,
    frozen_caller_snapshots_dangerous snapshots ->
    forall mode location,
      In authority_flow_state
        (nested_frozen_call_head CT h caller callee caller_colors snapshots)
          .(frozen_snapshot_current_colors) (mode, location) ->
      authority_mode_dangerous mode.
Proof.
  intros CT h caller callee caller_colors snapshots Hsnapshots mode location
    Hcolor.
  unfold nested_frozen_call_head in Hcolor. simpl in Hcolor.
  destruct Hcolor as [seed [Hseed Hpath]].
  destruct seed as [seed_mode seed_location].
  have Hseed_dangerous : authority_mode_dangerous seed_mode.
  { inversion Hseed; subst.
    - exact (proj2 H).
    - destruct H as [snapshot [Hsnapshot Hsnapshot_color]].
      eapply Hsnapshots; eauto. }
  exact (frozen_caller_authority_connected_preserves_dangerous CT h callee
    (seed_mode, seed_location) (mode, location) Hseed_dangerous Hpath).
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

Lemma nested_frozen_call_head_entry_exposure_covered :
  forall CT h boundary caller_colors snapshots source_mode source,
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
    authority_mode_dangerous source_mode ->
    In authority_flow_state
      (nested_frozen_call_head CT h caller callee caller_colors snapshots)
        .(frozen_snapshot_entry_colors) (source_mode, source) ->
    In Loc (nested_frozen_call_head CT h caller callee caller_colors snapshots)
      .(frozen_snapshot_resume_rdm_roots) source ->
    Included authority_flow_state
      (nested_frozen_call_head CT h caller callee caller_colors snapshots)
        .(frozen_snapshot_current_resume_exposure)
      (nested_frozen_call_head CT h caller callee caller_colors snapshots)
        .(frozen_snapshot_current_colors).
Proof.
  intros CT h boundary caller_colors snapshots source_mode source caller
    callee Hfree Hcaller_closed Hsnapshots_closed Hsource_mode Hsource
    Hsource_root target Htarget.
  have Hclassification :=
    nested_frozen_call_head_color_reflects_at_channel_free_entry CT h
      boundary caller_colors snapshots (source_mode, source) Hfree
      Hcaller_closed Hsnapshots_closed Hsource.
  assert (Hexposure_seeded : forall state,
      In authority_flow_state (frame_resume_exposure_colors CT h caller) state ->
      In authority_flow_state
        (nested_frozen_call_entry_seeds caller_colors snapshots) state).
  { intros [state_mode state_location] Hstate. simpl in *.
    have Hstate_copy := Hstate.
    have Hstate_dangerous : authority_mode_dangerous state_mode.
    { destruct Hstate as [seed [Hseed Hstate_path]].
      destruct Hseed as [root [Hroot [Hruntime Heq]]].
      subst seed.
      exact (frozen_caller_authority_connected_preserves_dangerous CT h
        caller (FlowProspective, root) (state_mode, state_location)
        (or_intror eq_refl) Hstate_path). }
    destruct Hclassification as
      [Hcaller_source | [snapshot [Hsnapshot Hsnapshot_source]]].
    - left. split.
      + eapply dangerous_rdm_root_color_covers_frame_resume_exposure
          with (mode := source_mode) (source := source).
        * exact Hcaller_closed.
        * exact Hsource_mode.
        * exact Hcaller_source.
        * exact Hsource_root.
        * exact Hstate_copy.
      + exact Hstate_dangerous.
    - right. exists snapshot. split; [exact Hsnapshot|].
      eapply dangerous_rdm_root_color_covers_frame_resume_exposure
        with (mode := source_mode) (source := source).
      + exact (Hsnapshots_closed snapshot Hsnapshot).
      + exact Hsource_mode.
      + exact Hsnapshot_source.
      + exact Hsource_root.
      + exact Hstate_copy. }
  unfold nested_frozen_call_head in Htarget |- *. simpl in Htarget |- *.
  destruct Htarget as [middle [Hmiddle Hpath]].
  exists middle. split; [apply Hexposure_seeded; exact Hmiddle|exact Hpath].
Qed.

(** Replacing a tracked head leaves every older slot untouched.  Supplying
    the new head's singleton obligations is sufficient to reuse all tail
    facts from the established frozen state. *)
Lemma principled_frozen_authority_replace_head :
  forall CT P Z cutoff active boundary stack incoming old_head new_head tail h,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some old_head :: tail) h ->
    frozen_caller_snapshots_runtime_mutable h [Some new_head] ->
    frozen_caller_snapshots_closed CT h active [Some new_head] ->
    frozen_caller_snapshots_retain_entry [Some new_head] ->
    frozen_caller_snapshots_dangerous [Some new_head] ->
    frozen_caller_snapshots_avoid_protected Z [Some new_head] ->
    frozen_caller_snapshots_resume_roots_in_heap h [Some new_head] ->
    frozen_caller_snapshots_resume_exposures_wf CT h active [Some new_head] ->
    frozen_caller_snapshots_resume_roots_safe CT h Z active [Some new_head] ->
    frozen_caller_snapshots_resume_joins_safe Z [Some new_head] ->
    frozen_caller_snapshots_entry_exposure_covered [Some new_head] ->
    frozen_caller_snapshots_cover_phase_incoming [Some new_head] ->
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some new_head :: tail) h.
Proof.
  intros CT P Z cutoff active boundary stack incoming old_head new_head tail h
    [Hmain [Haligned [Hruntime [Hclosed [Hretain [Hdangerous [Havoid
      [Hroots [Hexposure [Hresume [Hjoins
        [Hentry Hphase]]]]]]]]]]]]
    Hnew_runtime Hnew_closed Hnew_retain Hnew_dangerous Hnew_avoid Hnew_roots
    Hnew_exposure Hnew_resume Hnew_joins Hnew_entry Hnew_phase.
  split; [exact Hmain|]. split.
  - unfold frozen_caller_snapshots_aligned in *. simpl in *. exact Haligned.
  - split.
    + intros snapshot Hsnapshot. simpl in Hsnapshot.
      destruct Hsnapshot as [Heq | Htail].
      * injection Heq as Heq. subst snapshot.
        eapply Hnew_runtime; simpl; auto.
      *
      eapply Hruntime. simpl. right. exact Htail.
    + split.
      * intros snapshot Hsnapshot. simpl in Hsnapshot.
        destruct Hsnapshot as [Heq | Htail].
        -- injection Heq as Heq. subst snapshot.
           eapply Hnew_closed; simpl; auto.
        --
        eapply Hclosed. simpl. right. exact Htail.
      * split.
        -- intros snapshot Hsnapshot. simpl in Hsnapshot.
           destruct Hsnapshot as [Heq | Htail].
           ++ injection Heq as Heq. subst snapshot.
              eapply Hnew_retain; simpl; auto.
           ++
           eapply Hretain. simpl. right. exact Htail.
        -- split.
           ++ intros snapshot mode location Hsnapshot Hcolor.
              simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
              ** injection Heq as Heq. subst snapshot.
                 eapply Hnew_dangerous; [simpl; auto|exact Hcolor].
              ** eapply Hdangerous; [simpl; right; exact Htail|exact Hcolor].
           ++ split.
              ** intros snapshot mode location Hsnapshot Hmode Hcolor.
                 simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
                 --- injection Heq as Heq. subst snapshot. eapply Hnew_avoid;
                       [simpl; auto|exact Hmode|exact Hcolor].
                 --- eapply Havoid;
                       [simpl; right; exact Htail|exact Hmode|exact Hcolor].
              ** split.
                 --- intros snapshot root Hsnapshot Hroot.
                     simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
                     +++ injection Heq as Heq. subst snapshot.
                         eapply Hnew_roots; [simpl; auto|exact Hroot].
                     +++ eapply Hroots; [simpl; right; exact Htail|exact Hroot].
                 --- split.
                     +++ destruct Hexposure as
                           [Hexposure_runtime [Hexposure_closed
                             [Hexposure_dangerous [Hexposure_entry
                               Hexposure_roots]]]].
                         destruct Hnew_exposure as
                           [Hnew_exposure_runtime [Hnew_exposure_closed
                             [Hnew_exposure_dangerous [Hnew_exposure_entry
                               Hnew_exposure_roots]]]].
                         split.
                         *** intros snapshot Hsnapshot. simpl in Hsnapshot.
                             destruct Hsnapshot as [Heq | Htail].
                             ---- injection Heq as Heq. subst snapshot.
                                  eapply Hnew_exposure_runtime; simpl; auto.
                             ---- eapply Hexposure_runtime.
                                  simpl; right; exact Htail.
                         *** split.
                             ---- intros snapshot Hsnapshot. simpl in Hsnapshot.
                                  destruct Hsnapshot as [Heq | Htail].
                                  ++++ injection Heq as Heq. subst snapshot.
                                       eapply Hnew_exposure_closed; simpl; auto.
                                  ++++ eapply Hexposure_closed.
                                       simpl; right; exact Htail.
                             ---- split.
                                  ++++ intros snapshot mode location Hsnapshot
                                         Hcolor. simpl in Hsnapshot.
                                       destruct Hsnapshot as [Heq | Htail].
                                       ***** injection Heq as Heq. subst snapshot.
                                             eapply Hnew_exposure_dangerous;
                                               [simpl; auto|exact Hcolor].
                                       ***** eapply Hexposure_dangerous;
                                               [simpl; right; exact Htail|
                                                exact Hcolor].
                                  ++++ split.
                                       ***** intros snapshot Hsnapshot state Hcolor.
                                             simpl in Hsnapshot.
                                             destruct Hsnapshot as [Heq | Htail].
                                             ----- injection Heq as Heq.
                                                   subst snapshot.
                                                   eapply Hnew_exposure_entry;
                                                     [simpl; auto|exact Hcolor].
                                             ----- eapply Hexposure_entry;
                                                     [simpl; right; exact Htail|
                                                      exact Hcolor].
                                       ***** intros snapshot root Hsnapshot
                                              Hroot Hroot_runtime.
                                             simpl in Hsnapshot.
                                             destruct Hsnapshot as [Heq | Htail].
                                             ----- injection Heq as Heq.
                                                   subst snapshot.
                                                   eapply Hnew_exposure_roots;
                                                     [simpl; auto|
                                                      exact Hroot|
                                                      exact Hroot_runtime].
                                             ----- eapply Hexposure_roots;
                                                     [simpl; right; exact Htail|
                                                      exact Hroot|
                                                      exact Hroot_runtime].
                     +++ split.
                         *** intros snapshot active_mode source exposure_mode
                               target Hsnapshot.
                             simpl in Hsnapshot.
                             destruct Hsnapshot as [Heq | Htail].
                             ---- injection Heq as Heq. subst snapshot.
                                  eapply Hnew_resume. simpl; auto.
                             ---- eapply Hresume. simpl; right; exact Htail.
                         *** split.
                             ---- intros snapshot source_mode source Hsnapshot.
                                  simpl in Hsnapshot.
                                  destruct Hsnapshot as [Heq | Htail].
                                  ++++ injection Heq as Heq. subst snapshot.
                                       eapply Hnew_joins. simpl; auto.
                                  ++++ eapply Hjoins. simpl; right; exact Htail.
                             ---- split.
                                  ++++ intros snapshot source_mode source Hsnapshot.
                                       simpl in Hsnapshot.
                                       destruct Hsnapshot as [Heq | Htail].
                                       ***** injection Heq as Heq. subst snapshot.
                                             eapply Hnew_entry. simpl; auto.
                                       ***** eapply Hentry. simpl; right; exact Htail.
                                  ++++ intros snapshot mode location Hsnapshot.
                                       simpl in Hsnapshot.
                                       destruct Hsnapshot as [Heq | Htail].
                                       ***** injection Heq as Heq. subst snapshot.
                                             eapply Hnew_phase. simpl; auto.
                                       ***** eapply Hphase. simpl; right; exact Htail.
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

(** Existential wrapper used by the strengthened statement induction.  Both
    witnesses are constructed from the original history-state premise, so
    exposing this wrapper internally does not strengthen the public theorem. *)
Definition frozen_flexible_live_history_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary) (h : heap) : Prop :=
  exists incoming snapshots,
    principled_frozen_authority_history_state CT P Z cutoff active stack
      incoming snapshots h.

Definition bounded_frozen_flexible_live_history_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary) (h : heap) : Prop :=
  exists incoming snapshots,
    principled_frozen_authority_history_state CT P Z cutoff active stack
      incoming snapshots h /\
    frozen_caller_snapshots_before_boundaries snapshots stack.

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

Lemma potential_live_history_starts_private_frozen_statement :
  forall CT P Z cutoff active stack h,
    potential_live_history_state CT P Z cutoff active stack h ->
    private_frozen_statement_state CT P Z cutoff active stack
      (Empty_set authority_flow_state)
      (repeat None (length stack)) h.
Proof.
  intros CT P Z cutoff active stack h Hstate. split.
  - apply potential_live_history_starts_principled_frozen_authority.
    exact Hstate.
  - split.
    + apply frozen_active_resume_origins_imply_justified.
      apply repeat_none_snapshots_active_resume_origins.
    + split.
      * apply repeat_none_snapshots_before_boundaries.
      * split.
        -- apply repeat_none_snapshots_nested_covered.
        -- split.
           ++ apply repeat_none_snapshots_nested_resume_safe.
           ++ apply repeat_none_completed_colors_resume_safe.
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

Lemma potential_live_history_starts_private_fresh_frozen_statement :
  forall CT P Z cutoff active stack h,
    potential_live_history_state CT P Z cutoff active stack h ->
    private_fresh_frozen_statement_state CT P Z cutoff active stack
      (Empty_set authority_flow_state)
      (repeat None (length stack)) h.
Proof.
  intros CT P Z cutoff active stack h Hstate. split.
  - apply potential_live_history_starts_private_frozen_statement.
    exact Hstate.
  - split.
    + apply repeat_none_callee_side_components.
    + split.
      * apply repeat_none_callee_side_prospective_components.
      * apply repeat_none_snapshot_boundaries_after_cutoff.
Qed.

(** Every retained target exposed from a captured immediate-caller RDM root
    is fresh relative to each older tracked boundary and therefore lies
    outside the protected zone.  This is the stack-aligned fact consumed by
    the second-order return classifier. *)
Lemma tracked_head_resume_component_avoids_older_protected :
  forall CT P Z cutoff active head snapshots boundary stack incoming h older
    root target,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (Some head :: snapshots) h ->
    Same_set Loc head.(frozen_snapshot_resume_rdm_roots)
      (frame_rdm_root_set boundary.(boundary_caller)) ->
    List.In (Some older) snapshots ->
    In Loc head.(frozen_snapshot_resume_rdm_roots) root ->
    r_muttype h root = Some Mut_r ->
    retained_mut_reachable CT h root target ->
    ~ In Loc Z target.
Proof.
  intros CT P Z cutoff active head snapshots boundary stack incoming h older
    root target [Hprivate [Hcomponents [_ Hafter]]] Hroots Hold Hroot Hruntime
    Hreachable.
  have Hfull := proj1 Hprivate.
  have Haligned := proj1 (proj2 Hfull).
  have Hmain := proj1 Hfull.
  have Hzone : protected_zone_before_cutoff Z cutoff :=
    proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain))))))).
  eapply (tracked_head_caller_component_avoids_protected CT h Z cutoff active
    head snapshots boundary stack older root target).
  - exact Haligned.
  - exact Hcomponents.
  - exact Hafter.
  - exact Hzone.
  - exact Hold.
  - apply mutable_authority_reachable_rdm.
    + eapply (proj1 Hroots). exact Hroot.
    + exact Hruntime.
    + exact Hreachable.
Qed.

Lemma private_head_slot_prospective_component_avoids_older_protected :
  forall CT P Z cutoff active slot snapshots boundary stack incoming h older
    root target,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (slot :: snapshots) h ->
    List.In (Some older) snapshots ->
    prospective_mutable_authority_reachable CT h
      boundary.(boundary_caller) root target ->
    ~ In Loc Z target.
Proof.
  intros CT P Z cutoff active slot snapshots boundary stack incoming h older
    root target [Hprivate [_ [Hprospective Hafter]]] Hold Hreachable.
  have Hfull := proj1 Hprivate.
  have Haligned := proj1 (proj2 Hfull).
  have Hmain := proj1 Hfull.
  have Hzone : protected_zone_before_cutoff Z cutoff :=
    proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain))))))).
  eapply head_slot_prospective_component_avoids_older_protected; eauto.
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

Lemma frozen_caller_snapshots_separated_weaken :
  forall CT h active old_snapshots new_snapshots,
    frozen_caller_snapshot_list_included new_snapshots old_snapshots ->
    frozen_caller_snapshots_separated CT h active old_snapshots ->
    frozen_caller_snapshots_separated CT h active new_snapshots.
Proof.
  intros CT h active old_snapshots new_snapshots Hincluded Hseparated
    snapshot mode owned Hsnapshot Hmode Howned Hcolor.
  destruct (Hincluded snapshot Hsnapshot) as
    [old_snapshot [Hold_snapshot Hcolors]].
  exact (Hseparated old_snapshot mode owned Hold_snapshot Hmode Howned
    (Hcolors (mode, owned) Hcolor)).
Qed.

Lemma frozen_caller_snapshots_separated_owned_weaken :
  forall CT h old_active new_active snapshots,
    Included Loc
      (frame_owned_location CT h new_active)
      (frame_owned_location CT h old_active) ->
    frozen_caller_snapshots_separated CT h old_active snapshots ->
    frozen_caller_snapshots_separated CT h new_active snapshots.
Proof.
  intros CT h old_active new_active snapshots Howned Hseparated
    snapshot mode owned Hsnapshot Hmode Hnew_owned Hcolor.
  exact (Hseparated snapshot mode owned Hsnapshot Hmode
    (Howned owned Hnew_owned) Hcolor).
Qed.

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

Lemma frozen_caller_snapshots_independently_separated_after_graph_reflection :
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
    frozen_caller_snapshots_independently_separated CT h active snapshots ->
    frozen_caller_snapshots_independently_separated CT h' active
      (advance_frozen_caller_snapshots CT h' active snapshots).
Proof.
  intros CT h h' active snapshots Hretained Hmutable Howned Hclosed
    Hseparated new_snapshot caller_mode active_mode location Hnew
    Hcaller_mode Hactive_mode Hcaller_color Hactive_color.
  have Hsnapshots :=
    advance_frozen_caller_snapshots_after_graph_reflection_included CT h h'
      active snapshots Hretained Hmutable Howned Hclosed.
  destruct (Hsnapshots new_snapshot Hnew) as
    [old_snapshot [Hold_snapshot Hcolors]].
  have Hactive_covered : exists old_active_mode,
      authority_mode_dangerous old_active_mode /\
      In authority_flow_state
        (independent_active_authority_colors CT h active)
        (old_active_mode, location).
  { unfold independent_active_authority_colors in *.
    eapply executing_authority_colors_after_heap_change_covered;
      [| | |exact Hactive_mode|exact Hactive_color].
    - intros owned Hnew_owned. exists FlowPowered.
      split; [left; reflexivity|].
      eapply executing_authority_owned_is_powered. apply Howned.
      exact Hnew_owned.
    - intros old_mode left right Hold_mode Hold_color Hedge.
      exists old_mode. split; [exact Hold_mode|].
      eapply executing_authority_dangerous_retained.
      + exact Hold_mode.
      + exact Hold_color.
      + apply Hretained. exact Hedge.
    - intros old_mode left right Hold_mode Hold_color Hedge.
      exists FlowProspective. split; [right; reflexivity|].
      eapply executing_authority_dangerous_reverse_rdm.
      + exact Hold_mode.
      + exact Hold_color.
      + apply Hmutable. exact Hedge. }
  destruct Hactive_covered as
    [old_active_mode [Hold_active_mode Hold_active_color]].
  exact (Hseparated old_snapshot caller_mode old_active_mode location
    Hold_snapshot Hcaller_mode Hold_active_mode
    (Hcolors (caller_mode, location) Hcaller_color) Hold_active_color).
Qed.

Lemma frozen_caller_snapshots_active_resume_origins_after_graph_reflection :
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
    frozen_caller_snapshots_active_resume_origins CT h active snapshots ->
    frozen_caller_snapshots_active_resume_origins CT h' active
      (advance_frozen_caller_snapshots CT h' active snapshots).
Proof.
  intros CT h h' active snapshots Hretained Hmutable Howned Hclosed
    Horigins new_snapshot snapshot_mode active_mode location Hnew
    Hsnapshot_mode Hactive_mode Hsnapshot_color Htrigger.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold_snapshot]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot. simpl in *.
  have Hcolors :=
    advance_frozen_caller_snapshot_after_graph_reflection_included CT h h'
      active old_snapshot Hretained Hmutable Howned
      (Hclosed old_snapshot Hold_snapshot).
  destruct Htrigger as [Hactive_color | Hrdm].
  - have Hactive_covered : exists old_active_mode,
        authority_mode_dangerous old_active_mode /\
        In authority_flow_state
          (independent_active_authority_colors CT h active)
          (old_active_mode, location).
    { unfold independent_active_authority_colors in *.
      eapply executing_authority_colors_after_heap_change_covered;
        [| | |exact Hactive_mode|exact Hactive_color].
      - intros owned Hnew_owned. exists FlowPowered.
        split; [left; reflexivity|].
        eapply executing_authority_owned_is_powered. apply Howned.
        exact Hnew_owned.
      - intros old_mode left right Hold_mode Hold_color Hedge.
        exists old_mode. split; [exact Hold_mode|].
        eapply executing_authority_dangerous_retained; eauto.
      - intros old_mode left right Hold_mode Hold_color Hedge.
        exists FlowProspective. split; [right; reflexivity|].
        eapply executing_authority_dangerous_reverse_rdm; eauto. }
    destruct Hactive_covered as
      [old_active_mode [Hold_active_mode Hold_active_color]].
    destruct (Horigins old_snapshot snapshot_mode old_active_mode location
      Hold_snapshot Hsnapshot_mode Hold_active_mode
      (Hcolors (snapshot_mode, location) Hsnapshot_color)
      (or_introl Hold_active_color)) as
      [root_mode [root [Hroot_mode [Hroot_color Hroot]]]].
    exists root_mode, root. split; [exact Hroot_mode|]. split.
    + apply frozen_caller_authority_closure_contains. exact Hroot_color.
    + exact Hroot.
  - destruct (Horigins old_snapshot snapshot_mode active_mode location
      Hold_snapshot Hsnapshot_mode Hactive_mode
      (Hcolors (snapshot_mode, location) Hsnapshot_color)
      (or_intror Hrdm)) as
      [root_mode [root [Hroot_mode [Hroot_color Hroot]]]].
    exists root_mode, root. split; [exact Hroot_mode|]. split.
    + apply frozen_caller_authority_closure_contains. exact Hroot_color.
    + exact Hroot.
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

Lemma frozen_caller_connected_after_safe_field_update_covered :
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
    frozen_caller_authority_connected CT
      (update_field h lx field (Iot written)) frame source target ->
    authority_state_covered colors target.
Proof.
  intros CT h frame colors lx old field written source target Hobj Hruntime
    Hclosed Hseparated Hendpoints Hsource Hconnected.
  induction Hconnected.
  - eapply frozen_caller_step_after_safe_field_update_covered; eauto.
  - exact Hsource.
  - apply IHHconnected2. apply IHHconnected1. exact Hsource.
Qed.

Lemma advance_frozen_caller_snapshot_after_safe_field_update_covered :
  forall CT h frame snapshot lx old field written,
    runtime_getObj h lx = Some old ->
    authority_colors_runtime_mutable h
      snapshot.(frozen_snapshot_current_colors) ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h frame
        snapshot.(frozen_snapshot_current_colors))
      snapshot.(frozen_snapshot_current_colors) ->
    (forall caller_mode active_mode location,
      authority_mode_dangerous caller_mode ->
      authority_mode_dangerous active_mode ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (caller_mode, location) ->
      ~ In authority_flow_state
          (independent_active_authority_colors CT h frame)
          (active_mode, location)) ->
    (forall mode location,
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (mode, location) ->
      authority_mode_dangerous mode) ->
    authority_safe_field_endpoints CT h frame lx written ->
    forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (advance_frozen_caller_snapshot CT
          (update_field h lx field (Iot written)) frame snapshot)
          .(frozen_snapshot_current_colors) (mode, location) ->
      exists old_mode,
        authority_mode_dangerous old_mode /\
        In authority_flow_state snapshot.(frozen_snapshot_current_colors)
          (old_mode, location).
Proof.
  intros CT h frame snapshot lx old field written Hobj Hruntime Hclosed
    Hseparated Hdangerous Hendpoints mode location Hmode
    [seed [Hseed Hpath]].
  destruct seed as [seed_mode seed_location].
  have Hseed_covered : authority_state_covered
      snapshot.(frozen_snapshot_current_colors)
      (seed_mode, seed_location).
  { intros Hseed_mode. exists seed_mode. split; [exact Hseed_mode|exact Hseed]. }
  have Hcovered := frozen_caller_connected_after_safe_field_update_covered
    CT h frame snapshot.(frozen_snapshot_current_colors) lx old field written
    (seed_mode, seed_location) (mode, location) Hobj Hruntime Hclosed
    Hseparated Hendpoints Hseed_covered Hpath.
  exact (Hcovered Hmode).
Qed.

Definition frozen_caller_snapshot_list_dangerous_covered
  (new old : list frozen_caller_snapshot_slot) : Prop :=
  forall new_snapshot,
    List.In (Some new_snapshot) new ->
    exists old_snapshot,
      List.In (Some old_snapshot) old /\
      forall mode location,
        authority_mode_dangerous mode ->
        In authority_flow_state
          new_snapshot.(frozen_snapshot_current_colors) (mode, location) ->
        exists old_mode,
          authority_mode_dangerous old_mode /\
          In authority_flow_state
            old_snapshot.(frozen_snapshot_current_colors)
            (old_mode, location).

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

Definition frozen_snapshot_has_resume_origin
  (snapshot : frozen_caller_color_snapshot) : Prop :=
  exists root_mode root,
    authority_mode_dangerous root_mode /\
    In authority_flow_state snapshot.(frozen_snapshot_current_colors)
      (root_mode, root) /\
    In Loc snapshot.(frozen_snapshot_resume_rdm_roots) root.

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

Lemma frozen_caller_step_after_safe_field_update_covered_by_old_or_origin :
  forall CT h frame snapshot fallback lx old field written source target,
    runtime_getObj h lx = Some old ->
    authority_colors_runtime_mutable h
      snapshot.(frozen_snapshot_current_colors) ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h frame
        snapshot.(frozen_snapshot_current_colors))
      snapshot.(frozen_snapshot_current_colors) ->
    authority_safe_field_endpoints CT h frame lx written ->
    (forall snapshot_mode active_mode location,
      authority_mode_dangerous snapshot_mode ->
      authority_mode_dangerous active_mode ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (snapshot_mode, location) ->
      (In authority_flow_state
         (independent_active_authority_colors CT h frame)
         (active_mode, location) \/
       typed_root RDM frame.(frame_senv) frame.(frame_renv) location) ->
      fallback) ->
    frozen_state_covered_by_old_or snapshot fallback source ->
    frozen_caller_authority_step CT
      (update_field h lx field (Iot written)) frame source target ->
    frozen_state_covered_by_old_or snapshot fallback target.
Proof.
  intros CT h frame snapshot fallback lx old field written source target Hobj
    Hruntime Hclosed Hendpoints Horigins Hsource Hstep Htarget_mode.
  inversion Hstep; subst; simpl in *.
  - destruct (Hsource (or_introl eq_refl)) as
      [[old_mode [Hold_mode Hold_color]] | Horigin];
      [|right; exact Horigin].
    destruct (retained_edge_after_field_update CT h lx old field
      (Iot written) left right Hobj H) as
      [Hold_edge | [Heq_left [Heq_value Hnew]]].
    + left. exists old_mode. split; [exact Hold_mode|].
      eapply frozen_caller_color_dangerous_retained; eauto.
    + injection Heq_value as Heq_right. subst left right.
      inversion Hendpoints; subst.
      * right. eapply Horigins with
          (snapshot_mode := old_mode) (active_mode := FlowPowered)
          (location := lx).
        -- exact Hold_mode.
        -- left. reflexivity.
        -- exact Hold_color.
        --
        left. unfold independent_active_authority_colors.
        apply executing_authority_owned_is_powered. exact H0.
      * have Hmut := Hruntime old_mode lx Hold_color.
        rewrite H0 in Hmut. discriminate.
      * left. exists FlowProspective. split; [right; reflexivity|].
        eapply frozen_caller_color_dangerous_frame_join;
          eauto.
  - destruct (Hsource (or_intror eq_refl)) as
      [[old_mode [Hold_mode Hold_color]] | Horigin];
      [|right; exact Horigin].
    destruct (retained_edge_after_field_update CT h lx old field
      (Iot written) left right Hobj H) as
      [Hold_edge | [Heq_left [Heq_value Hnew]]].
    + left. exists old_mode. split; [exact Hold_mode|].
      eapply frozen_caller_color_dangerous_retained; eauto.
    + injection Heq_value as Heq_right. subst left right.
      inversion Hendpoints; subst.
      * right. eapply Horigins with
          (snapshot_mode := old_mode) (active_mode := FlowPowered)
          (location := lx).
        -- exact Hold_mode.
        -- left. reflexivity.
        -- exact Hold_color.
        --
        left. unfold independent_active_authority_colors.
        apply executing_authority_owned_is_powered. exact H0.
      * have Hmut := Hruntime old_mode lx Hold_color.
        rewrite H0 in Hmut. discriminate.
      * left. exists FlowProspective. split; [right; reflexivity|].
        eapply frozen_caller_color_dangerous_frame_join;
          eauto.
  - destruct (Hsource (or_intror eq_refl)) as
      [[old_mode [Hold_mode Hold_color]] | Horigin];
      [|right; exact Horigin].
    destruct (mutable_edge_after_field_update CT h lx old field
      (Iot written) right left Hobj H) as
      [Hold_edge | [Heq_right [Heq_value Hnew]]].
    + left. exists FlowProspective. split; [right; reflexivity|].
      eapply frozen_caller_color_dangerous_reverse_rdm; eauto.
    + injection Heq_value as Heq_left. subst left right.
      inversion Hendpoints; subst.
      * right. eapply Horigins with
          (snapshot_mode := old_mode) (active_mode := FlowPowered)
          (location := written).
        -- exact Hold_mode.
        -- left. reflexivity.
        -- exact Hold_color.
        --
        left. unfold independent_active_authority_colors.
        apply executing_authority_owned_is_powered. exact H1.
      * have Hmut := Hruntime old_mode written Hold_color.
        rewrite H1 in Hmut. discriminate.
      * left. exists FlowProspective. split; [right; reflexivity|].
        eapply frozen_caller_color_dangerous_frame_join;
          eauto.
  - destruct (Hsource (or_introl eq_refl)) as
      [[old_mode [Hold_mode Hold_color]] | Horigin];
      [|right; exact Horigin].
    destruct (mutable_edge_after_field_update CT h lx old field
      (Iot written) right left Hobj H) as
      [Hold_edge | [Heq_right [Heq_value Hnew]]].
    + left. exists FlowProspective. split; [right; reflexivity|].
      eapply frozen_caller_color_dangerous_reverse_rdm; eauto.
    + injection Heq_value as Heq_left. subst left right.
      inversion Hendpoints; subst.
      * right. eapply Horigins with
          (snapshot_mode := old_mode) (active_mode := FlowPowered)
          (location := written).
        -- exact Hold_mode.
        -- left. reflexivity.
        -- exact Hold_color.
        --
        left. unfold independent_active_authority_colors.
        apply executing_authority_owned_is_powered. exact H1.
      * have Hmut := Hruntime old_mode written Hold_color.
        rewrite H1 in Hmut. discriminate.
      * left. exists FlowProspective. split; [right; reflexivity|].
        eapply frozen_caller_color_dangerous_frame_join;
          eauto.
  - destruct (Hsource (or_introl eq_refl)) as
      [[old_mode [Hold_mode Hold_color]] | Horigin];
      [|right; exact Horigin].
    left. exists FlowProspective. split; [right; reflexivity|].
    eapply frozen_caller_color_dangerous_frame_join;
      eauto.
  - destruct (Hsource (or_intror eq_refl)) as
      [[old_mode [Hold_mode Hold_color]] | Horigin];
      [|right; exact Horigin].
    left. exists FlowProspective. split; [right; reflexivity|].
    eapply frozen_caller_color_dangerous_frame_join;
      eauto.
  - destruct (Hsource (or_introl eq_refl)) as
      [[old_mode [Hold_mode Hold_color]] | Horigin];
      [|right; exact Horigin].
    left. exists FlowProspective. split; [right; reflexivity|].
    destruct Hold_mode as [-> | ->].
    + apply Hclosed. exists (FlowPowered, location).
      split; [exact Hold_color|]. apply rt_step.
      apply frozen_caller_mark_prospective.
    + exact Hold_color.
Qed.

Lemma frozen_caller_connected_after_safe_field_update_covered_by_old_or_origin :
  forall CT h frame snapshot fallback lx old field written source target,
    runtime_getObj h lx = Some old ->
    authority_colors_runtime_mutable h
      snapshot.(frozen_snapshot_current_colors) ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h frame
        snapshot.(frozen_snapshot_current_colors))
      snapshot.(frozen_snapshot_current_colors) ->
    authority_safe_field_endpoints CT h frame lx written ->
    (forall snapshot_mode active_mode location,
      authority_mode_dangerous snapshot_mode ->
      authority_mode_dangerous active_mode ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (snapshot_mode, location) ->
      (In authority_flow_state
         (independent_active_authority_colors CT h frame)
         (active_mode, location) \/
       typed_root RDM frame.(frame_senv) frame.(frame_renv) location) ->
      fallback) ->
    frozen_state_covered_by_old_or snapshot fallback source ->
    frozen_caller_authority_connected CT
      (update_field h lx field (Iot written)) frame source target ->
    frozen_state_covered_by_old_or snapshot fallback target.
Proof.
  intros CT h frame snapshot fallback lx old field written source target Hobj
    Hruntime Hclosed Hendpoints Horigins Hsource Hconnected.
  induction Hconnected.
  - eapply frozen_caller_step_after_safe_field_update_covered_by_old_or_origin;
      eauto.
  - exact Hsource.
  - apply IHHconnected2. apply IHHconnected1. exact Hsource.
Qed.

Lemma advance_frozen_caller_snapshot_after_safe_field_update_covered_by_old_or_origin :
  forall CT h frame snapshot fallback lx old field written,
    runtime_getObj h lx = Some old ->
    authority_colors_runtime_mutable h
      snapshot.(frozen_snapshot_current_colors) ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h frame
        snapshot.(frozen_snapshot_current_colors))
      snapshot.(frozen_snapshot_current_colors) ->
    authority_safe_field_endpoints CT h frame lx written ->
    (forall snapshot_mode active_mode location,
      authority_mode_dangerous snapshot_mode ->
      authority_mode_dangerous active_mode ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (snapshot_mode, location) ->
      (In authority_flow_state
         (independent_active_authority_colors CT h frame)
         (active_mode, location) \/
       typed_root RDM frame.(frame_senv) frame.(frame_renv) location) ->
      fallback) ->
    forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (advance_frozen_caller_snapshot CT
          (update_field h lx field (Iot written)) frame snapshot)
          .(frozen_snapshot_current_colors) (mode, location) ->
      (exists old_mode,
          authority_mode_dangerous old_mode /\
          In authority_flow_state snapshot.(frozen_snapshot_current_colors)
            (old_mode, location)) \/
      fallback.
Proof.
  intros CT h frame snapshot fallback lx old field written Hobj Hruntime Hclosed
    Hendpoints Horigins mode location Hmode [seed [Hseed Hpath]].
  destruct seed as [seed_mode seed_location].
  have Hsource : frozen_state_covered_by_old_or snapshot fallback
      (seed_mode, seed_location).
  { intros Hseed_mode. left. exists seed_mode. split; assumption. }
  have Hcovered :=
    frozen_caller_connected_after_safe_field_update_covered_by_old_or_origin
      CT h frame snapshot fallback lx old field written
      (seed_mode, seed_location)
      (mode, location) Hobj Hruntime Hclosed Hendpoints Horigins Hsource Hpath.
  exact (Hcovered Hmode).
Qed.

Lemma frozen_caller_snapshots_active_resume_origins_after_safe_field_update :
  forall CT h frame snapshots lx old field written,
    runtime_getObj h lx = Some old ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_closed CT h frame snapshots ->
    authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h frame) ->
    authority_safe_field_endpoints CT h frame lx written ->
    frozen_caller_snapshots_active_resume_origins CT h frame snapshots ->
    frozen_caller_snapshots_active_resume_origins CT
      (update_field h lx field (Iot written)) frame
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame snapshots).
Proof.
  intros CT h frame snapshots lx old field written Hobj Hruntime Hclosed
    Hactive_runtime Hendpoints Horigins new_snapshot snapshot_mode active_mode
    location Hnew Hsnapshot_mode Hactive_mode Hsnapshot_color Htrigger.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold_snapshot]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot. simpl in *.
  have Hcovered :=
    advance_frozen_caller_snapshot_after_safe_field_update_covered_by_old_or_origin
      CT h frame old_snapshot (frozen_snapshot_has_resume_origin old_snapshot)
      lx old field written Hobj
      (Hruntime old_snapshot Hold_snapshot)
      (Hclosed old_snapshot Hold_snapshot) Hendpoints
      (fun old_snapshot_mode old_active_mode old_location =>
        Horigins old_snapshot old_snapshot_mode old_active_mode old_location
          Hold_snapshot)
      snapshot_mode location Hsnapshot_mode Hsnapshot_color.
  destruct Hcovered as
    [[old_snapshot_mode [Hold_snapshot_mode Hold_snapshot_color]] | Horigin].
  - destruct Htrigger as [Hactive_color | Hrdm].
    + destruct (executing_authority_colors_after_safe_field_update_covered CT
        h frame (Empty_set authority_flow_state) lx old field written Hobj
        Hactive_runtime Hendpoints active_mode location Hactive_mode
        Hactive_color) as
        [old_active_mode [Hold_active_mode Hold_active_color]].
      destruct (Horigins old_snapshot old_snapshot_mode old_active_mode
        location Hold_snapshot Hold_snapshot_mode Hold_active_mode
        Hold_snapshot_color (or_introl Hold_active_color)) as
        [root_mode [root [Hroot_mode [Hroot_color Hroot]]]].
      exists root_mode, root. split; [exact Hroot_mode|]. split.
      * apply frozen_caller_authority_closure_contains. exact Hroot_color.
      * exact Hroot.
    + destruct (Horigins old_snapshot old_snapshot_mode active_mode location
        Hold_snapshot Hold_snapshot_mode Hactive_mode Hold_snapshot_color
        (or_intror Hrdm)) as
        [root_mode [root [Hroot_mode [Hroot_color Hroot]]]].
      exists root_mode, root. split; [exact Hroot_mode|]. split.
      * apply frozen_caller_authority_closure_contains. exact Hroot_color.
      * exact Hroot.
  - destruct Horigin as
      [root_mode [root [Hroot_mode [Hroot_color Hroot]]]].
    exists root_mode, root. split; [exact Hroot_mode|]. split.
    + apply frozen_caller_authority_closure_contains. exact Hroot_color.
    + exact Hroot.
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

Lemma advance_frozen_caller_snapshots_after_safe_field_update_covered :
  forall CT h frame snapshots lx old field written,
    runtime_getObj h lx = Some old ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_closed CT h frame snapshots ->
    frozen_caller_snapshots_independently_separated CT h frame snapshots ->
    frozen_caller_snapshots_dangerous snapshots ->
    authority_safe_field_endpoints CT h frame lx written ->
    frozen_caller_snapshot_list_dangerous_covered
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame snapshots)
      snapshots.
Proof.
  intros CT h frame snapshots lx old field written Hobj Hruntime Hclosed
    Hseparated Hdangerous Hendpoints new_snapshot Hnew.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot.
  exists old_snapshot. split; [exact Hold|].
  eapply advance_frozen_caller_snapshot_after_safe_field_update_covered.
  - exact Hobj.
  - eapply Hruntime. exact Hold.
  - eapply Hclosed. exact Hold.
  - intros caller_mode active_mode location Hcaller_mode Hactive_mode
      Hcaller_color Hactive_color.
    exact (Hseparated old_snapshot caller_mode active_mode location Hold
      Hcaller_mode Hactive_mode Hcaller_color Hactive_color).
  - intros mode location Hcolor. eapply Hdangerous; eauto.
  - exact Hendpoints.
Qed.

Lemma frozen_caller_snapshots_independently_separated_after_safe_field_update :
  forall CT h frame snapshots lx old field written,
    runtime_getObj h lx = Some old ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_closed CT h frame snapshots ->
    frozen_caller_snapshots_independently_separated CT h frame snapshots ->
    frozen_caller_snapshots_dangerous snapshots ->
    authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h frame) ->
    authority_safe_field_endpoints CT h frame lx written ->
    frozen_caller_snapshots_independently_separated CT
      (update_field h lx field (Iot written)) frame
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame snapshots).
Proof.
  intros CT h frame snapshots lx old field written Hobj Hruntime Hclosed
    Hseparated Hdangerous Hactive_runtime Hendpoints new_snapshot caller_mode
    active_mode location Hnew Hcaller_mode Hactive_mode Hcaller_color
    Hactive_color.
  have Hsnapshot_covered :=
    advance_frozen_caller_snapshots_after_safe_field_update_covered CT h frame
      snapshots lx old field written Hobj Hruntime Hclosed Hseparated
      Hdangerous Hendpoints.
  destruct (Hsnapshot_covered new_snapshot Hnew) as
    [old_snapshot [Hold_snapshot Hcolors]].
  destruct (Hcolors caller_mode location Hcaller_mode Hcaller_color) as
    [old_caller_mode [Hold_caller_mode Hold_caller_color]].
  have Hactive_covered := executing_authority_colors_after_safe_field_update_covered
    CT h frame (Empty_set authority_flow_state) lx old field written Hobj
    Hactive_runtime Hendpoints active_mode location Hactive_mode Hactive_color.
  destruct Hactive_covered as
    [old_active_mode [Hold_active_mode Hold_active_color]].
  exact (Hseparated old_snapshot old_caller_mode old_active_mode location
    Hold_snapshot Hold_caller_mode Hold_active_mode Hold_caller_color
    Hold_active_color).
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

Lemma channel_free_entry_has_active_resume_origins :
  forall CT h boundary snapshots,
    entry_ownership_channel_free boundary ->
    frozen_caller_snapshots_active_resume_origins CT h
      (mk_watched_frame
        (call_authority boundary.(boundary_caller).(frame_authority)
          boundary.(boundary_receiver_view))
        boundary.(boundary_callee_entry_senv)
      boundary.(boundary_callee_entry_renv)) snapshots.
Proof.
  intros CT h boundary snapshots Hfree snapshot snapshot_mode active_mode
    location Hsnapshot Hsnapshot_mode Hactive_mode Hsnapshot_color
    [Hactive_color | Hrdm].
  - exfalso.
    exact (channel_free_entry_has_no_independent_active_authority_color CT h
      boundary (active_mode, location) Hfree Hactive_color).
  - exfalso. exact ((proj2 Hfree) location Hrdm).
Qed.

Lemma frozen_caller_snapshots_aligned_push :
  forall slot snapshots boundary stack,
    frozen_caller_snapshots_aligned snapshots stack ->
    frozen_caller_snapshots_aligned
      (slot :: snapshots) (boundary :: stack).
Proof.
  intros slot snapshots boundary stack Haligned.
  unfold frozen_caller_snapshots_aligned in *. simpl. congruence.
Qed.

Lemma frozen_caller_snapshots_aligned_pop :
  forall slot snapshots boundary stack,
    frozen_caller_snapshots_aligned
      (slot :: snapshots) (boundary :: stack) ->
    frozen_caller_snapshots_aligned snapshots stack.
Proof.
  intros slot snapshots boundary stack Haligned.
  unfold frozen_caller_snapshots_aligned in *. simpl in Haligned. congruence.
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

Lemma enter_frozen_caller_snapshots_cover_phase_incoming :
  forall CT h caller callee caller_colors snapshots,
    frozen_caller_snapshots_cover_phase_incoming snapshots ->
    frozen_caller_snapshots_cover_phase_incoming
      (enter_frozen_caller_snapshots CT h caller callee caller_colors
        snapshots).
Proof.
  intros CT h caller callee caller_colors snapshots Hcovered snapshot mode
    location Hsnapshot Hmode Hincoming.
  unfold enter_frozen_caller_snapshots in Hsnapshot.
  simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
  - injection Heq as Heq. subst snapshot. simpl in *.
    apply frozen_caller_authority_closure_contains. split; assumption.
  - eapply (advance_frozen_caller_snapshots_cover_phase_incoming CT h callee
      snapshots Hcovered); eauto.
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

Lemma frame_resume_exposure_colors_in_executing_from_dangerous_rdm_root :
  forall CT h frame incoming source_mode source,
    authority_mode_dangerous source_mode ->
    In authority_flow_state
      (executing_authority_color_set CT h frame incoming)
      (source_mode, source) ->
    In Loc (frame_rdm_root_set frame) source ->
    Included authority_flow_state
      (frame_resume_exposure_colors CT h frame)
      (executing_authority_color_set CT h frame incoming).
Proof.
  intros CT h frame incoming source_mode source Hsource_mode Hsource
    Hsource_root target Htarget.
  destruct Htarget as [seed [Hseed Hpath]].
  destruct Hseed as [root [Hroot [Hruntime Heq]]].
  subst seed.
  have Hroot_color : In authority_flow_state
      (executing_authority_color_set CT h frame incoming)
      (FlowProspective, root).
  { eapply executing_authority_dangerous_frame_join; eauto. }
  destruct Hroot_color as [origin [Horigin Hprefix]].
  exists origin. split; [exact Horigin|].
  eapply rt_trans; [exact Hprefix|].
  eapply frozen_caller_authority_connected_is_phased. exact Hpath.
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

Lemma principled_frozen_authority_enter_untracked :
  forall CT P Z cutoff callee boundary stack h caller_colors snapshots,
    principled_phased_authority_live_history_state CT P Z cutoff
      callee (boundary :: stack) caller_colors h ->
    frozen_caller_snapshots_aligned snapshots stack ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_retain_entry snapshots ->
    frozen_caller_snapshots_dangerous snapshots ->
    frozen_caller_snapshots_avoid_protected Z
      (advance_frozen_caller_snapshots CT h callee snapshots) ->
    frozen_caller_snapshots_resume_roots_in_heap h
      (advance_frozen_caller_snapshots CT h callee snapshots) ->
    frozen_caller_snapshots_resume_exposures_wf CT h callee
      (advance_frozen_caller_snapshots CT h callee snapshots) ->
    frozen_caller_snapshots_resume_roots_safe CT h Z callee
      (advance_frozen_caller_snapshots CT h callee snapshots) ->
    frozen_caller_snapshots_resume_joins_safe Z
      (advance_frozen_caller_snapshots CT h callee snapshots) ->
    frozen_caller_snapshots_entry_exposure_covered
      (advance_frozen_caller_snapshots CT h callee snapshots) ->
    frozen_caller_snapshots_cover_phase_incoming
      (advance_frozen_caller_snapshots CT h callee snapshots) ->
    principled_frozen_authority_history_state CT P Z cutoff
      callee (boundary :: stack) caller_colors
      (None :: advance_frozen_caller_snapshots CT h callee snapshots) h.
Proof.
  intros CT P Z cutoff callee boundary stack h caller_colors snapshots
    Hstate Haligned Hruntime Hretain Hdangerous Havoid Hroots Hexposure
    Hresume Hjoin_safe Hentry_covered Hphase_covered.
  split; [exact Hstate|]. split.
  - apply frozen_caller_snapshots_aligned_push.
    unfold frozen_caller_snapshots_aligned,
      advance_frozen_caller_snapshots. rewrite length_map. exact Haligned.
  - split.
    + intros snapshot Hsnapshot. simpl in Hsnapshot.
      destruct Hsnapshot as [Hbad | Htail]; [discriminate|].
      eapply advance_frozen_caller_snapshots_runtime_mutable; eauto.
      exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hstate)))))).
    + split.
      * intros snapshot Hsnapshot. simpl in Hsnapshot.
        destruct Hsnapshot as [Hbad | Htail]; [discriminate|].
        eapply advance_frozen_caller_snapshots_closed. exact Htail.
      * split.
        -- intros snapshot Hsnapshot. simpl in Hsnapshot.
           destruct Hsnapshot as [Hbad | Htail]; [discriminate|].
           eapply advance_frozen_caller_snapshots_retain_entry; eauto.
        -- split.
           ++ intros snapshot mode location Hsnapshot Hcolor.
              simpl in Hsnapshot.
              destruct Hsnapshot as [Hbad | Htail]; [discriminate|].
              eapply advance_frozen_caller_snapshots_dangerous; eauto.
           ++ split.
              ** intros snapshot mode location Hsnapshot.
                 simpl in Hsnapshot.
                 destruct Hsnapshot as [Hbad | Htail]; [discriminate|].
                 eapply Havoid. exact Htail.
              ** split.
                 --- intros snapshot root Hsnapshot.
                     simpl in Hsnapshot.
                     destruct Hsnapshot as [Hbad | Htail]; [discriminate|].
                     eapply Hroots. exact Htail.
                 --- split.
                     +++ split.
                         *** intros snapshot Hsnapshot.
                             simpl in Hsnapshot.
                             destruct Hsnapshot as [Hbad | Htail]; [discriminate|].
                             eapply (proj1 Hexposure). exact Htail.
                         *** split.
                             ---- intros snapshot Hsnapshot.
                                  simpl in Hsnapshot.
                                  destruct Hsnapshot as [Hbad | Htail]; [discriminate|].
                                  eapply (proj1 (proj2 Hexposure)). exact Htail.
                             ---- split.
                                  ++++ intros snapshot mode location Hsnapshot.
                                       simpl in Hsnapshot.
                                       destruct Hsnapshot as [Hbad | Htail]; [discriminate|].
                                       eapply (proj1 (proj2 (proj2 Hexposure))). exact Htail.
                                  ++++ split.
                                       ***** intros snapshot Hsnapshot.
                                             simpl in Hsnapshot.
                                             destruct Hsnapshot as [Hbad | Htail];
                                               [discriminate|].
                                             eapply (proj1 (proj2 (proj2
                                               (proj2 Hexposure)))). exact Htail.
                                       ***** intros snapshot root Hsnapshot.
                                             simpl in Hsnapshot.
                                             destruct Hsnapshot as [Hbad | Htail];
                                               [discriminate|].
                                             eapply (proj2 (proj2 (proj2
                                               (proj2 Hexposure)))). exact Htail.
                     +++ split.
                         *** intros snapshot mode source exposure_mode target Hsnapshot.
                             simpl in Hsnapshot.
                             destruct Hsnapshot as [Hbad | Htail]; [discriminate|].
                             eapply Hresume. exact Htail.
                         *** split.
                             ---- intros snapshot mode source Hsnapshot.
                                  simpl in Hsnapshot.
                                  destruct Hsnapshot as [Hbad | Htail];
                                    [discriminate|].
                                  eapply Hjoin_safe. exact Htail.
                             ---- split.
                                  ++++ intros snapshot mode source Hsnapshot.
                                       simpl in Hsnapshot.
                                       destruct Hsnapshot as [Hbad | Htail];
                                         [discriminate|].
                                       eapply Hentry_covered. exact Htail.
                                  ++++ intros snapshot mode location Hsnapshot.
                                       simpl in Hsnapshot.
                                       destruct Hsnapshot as [Hbad | Htail];
                                         [discriminate|].
                                       eapply Hphase_covered. exact Htail.
Qed.

Lemma principled_frozen_authority_enter_channel_free :
  forall CT P Z cutoff boundary stack h caller_colors snapshots,
    let callee :=
      mk_watched_frame
        (call_authority boundary.(boundary_caller).(frame_authority)
          boundary.(boundary_receiver_view))
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv) in
    principled_phased_authority_live_history_state CT P Z cutoff
      callee (boundary :: stack) caller_colors h ->
    frozen_caller_snapshots_aligned snapshots stack ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_retain_entry snapshots ->
    frozen_caller_snapshots_dangerous snapshots ->
    authority_colors_runtime_mutable h caller_colors ->
    entry_ownership_channel_free boundary ->
    frozen_caller_snapshots_avoid_protected Z
      (advance_frozen_caller_snapshots CT h callee snapshots) ->
    frozen_caller_snapshots_resume_roots_in_heap h
      (advance_frozen_caller_snapshots CT h callee snapshots) ->
    frozen_caller_snapshots_resume_exposures_wf CT h callee
      (advance_frozen_caller_snapshots CT h callee snapshots) ->
    frozen_caller_snapshots_resume_roots_safe CT h Z callee
      (advance_frozen_caller_snapshots CT h callee snapshots) ->
    frozen_caller_snapshots_resume_joins_safe Z
      (advance_frozen_caller_snapshots CT h callee snapshots) ->
    frozen_caller_snapshots_entry_exposure_covered
      (enter_frozen_caller_snapshots CT h boundary.(boundary_caller) callee
        caller_colors snapshots) ->
    frozen_caller_snapshots_cover_phase_incoming
      (enter_frozen_caller_snapshots CT h boundary.(boundary_caller) callee
        caller_colors snapshots) ->
    principled_frozen_authority_history_state CT P Z cutoff
      callee (boundary :: stack) caller_colors
      (enter_frozen_caller_snapshots CT h boundary.(boundary_caller) callee
        caller_colors snapshots) h.
Proof.
  intros CT P Z cutoff boundary stack h caller_colors snapshots
    callee Hstate Haligned Hsnapshots_runtime Hsnapshots_retain
    Hsnapshots_dangerous Hcaller_runtime Hfree Htail_avoid Htail_roots
    Htail_exposure Htail_resume Htail_joins Hentry_covered Hphase_covered.
  split; [exact Hstate|]. split.
  - eapply enter_frozen_caller_snapshots_aligned. exact Haligned.
  - split.
    + unfold enter_frozen_caller_snapshots. intros snapshot Hsnapshot.
        simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
        -- injection Heq as Heq. subst snapshot.
           eapply advance_frozen_caller_snapshot_runtime_mutable.
           ++ exact (proj1 (proj1
                (proj2 (proj2 (proj2 (proj2 Hstate)))))).
           ++ intros mode location [Hcolor Hmode].
              eapply Hcaller_runtime. exact Hcolor.
        -- eapply advance_frozen_caller_snapshots_runtime_mutable.
           ++ exact (proj1 (proj1
                (proj2 (proj2 (proj2 (proj2 Hstate)))))).
           ++ exact Hsnapshots_runtime.
           ++ exact Htail.
    + split.
      * unfold enter_frozen_caller_snapshots. intros snapshot Hsnapshot.
           simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
           ++ injection Heq as Heq. subst snapshot.
              simpl. exact (proj1
                (frozen_caller_authority_closure_idempotent CT h callee
                  (dangerous_authority_colors caller_colors))).
           ++ eapply advance_frozen_caller_snapshots_closed. exact Htail.
      * split.
        -- unfold enter_frozen_caller_snapshots. intros snapshot Hsnapshot.
              simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
              ** injection Heq as Heq. subst snapshot. simpl.
                 intros state Hcolor. exact Hcolor.
              ** eapply advance_frozen_caller_snapshots_retain_entry.
                 --- exact Hsnapshots_retain.
                 --- exact Htail.
        -- split.
           ++ unfold enter_frozen_caller_snapshots.
                 intros snapshot mode location Hsnapshot Hcolor.
                 simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
                 --- injection Heq as Heq. subst snapshot. simpl in Hcolor.
                     destruct Hcolor as [seed [Hseed Hpath]].
                     destruct seed as [seed_mode seed_location].
                     exact
                       (frozen_caller_authority_connected_preserves_dangerous
                         CT h callee (seed_mode, seed_location)
                         (mode, location) (proj2 Hseed) Hpath).
                 --- eapply advance_frozen_caller_snapshots_dangerous.
                     +++ exact Hsnapshots_dangerous.
                     +++ exact Htail.
                     +++ exact Hcolor.
           ++ split.
              ** intros snapshot mode location Hsnapshot Hmode Hcolor
                   Hprotected.
                 unfold enter_frozen_caller_snapshots in Hsnapshot.
                 simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
                 --- injection Heq as Heq. subst snapshot. simpl in Hcolor.
                     destruct Hcolor as [seed [Hseed Hpath]].
                     destruct seed as [seed_mode seed_location].
                     have Hseparated :=
                       proj1 (proj2 (proj2 (proj2 Hstate))).
                     eapply Hseparated; [exact Hmode| |exact Hprotected].
                     exists (seed_mode, seed_location). split.
                     +++ left. exact (proj1 Hseed).
                     +++ eapply frozen_caller_authority_connected_is_phased.
                         exact Hpath.
                 --- eapply Htail_avoid; eauto.
              ** split.
                 --- intros snapshot root Hsnapshot Hroot.
                     unfold enter_frozen_caller_snapshots in Hsnapshot.
                     simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
                     +++ injection Heq as Heq. subst snapshot. simpl in Hroot.
                         unfold frame_rdm_root_set, typed_root in Hroot.
                         destruct Hroot as
                           [variable [T [Htype [Hvalue Hrdm]]]].
                         have Hframes := proj1
                           (proj2 (proj2 (proj2 (proj2 Hstate)))).
                         have Hcaller_wf := Forall_inv (proj2 Hframes).
                         eapply wf_config_value_dom; eauto.
                     +++ eapply Htail_roots; eauto.
                 --- split.
                     +++ split.
                         *** intros snapshot Hsnapshot mode location Hcolor.
                             unfold enter_frozen_caller_snapshots in Hsnapshot.
                             simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
                             ---- injection Heq as Heq. subst snapshot. simpl in Hcolor.
                                  eapply advance_frozen_caller_snapshot_runtime_mutable.
                                  ++++ exact (proj1 (proj1
                                    (proj2 (proj2 (proj2 (proj2 Hstate)))))).
                                  ++++ have Hframes := proj1
                                    (proj2 (proj2 (proj2 (proj2 Hstate)))).
                                       have Hcaller_wf := Forall_inv (proj2 Hframes).
                                       apply frame_resume_exposure_colors_runtime_mutable.
                                       exact Hcaller_wf.
                                  ++++ exact Hcolor.
                             ---- eapply (proj1 Htail_exposure); eauto.
                         *** split.
                             ---- intros snapshot Hsnapshot.
                                  unfold enter_frozen_caller_snapshots in Hsnapshot.
                                  simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
                                  ++++ injection Heq as Heq. subst snapshot. simpl.
                                       exact (proj1
                                         (frozen_caller_authority_closure_idempotent
                                           CT h callee
                                           (frame_resume_exposure_colors CT h
                                             boundary.(boundary_caller)))).
                                  ++++ eapply (proj1 (proj2 Htail_exposure)); eauto.
                             ---- split.
                                  ++++ intros snapshot mode location Hsnapshot Hcolor.
                                       unfold enter_frozen_caller_snapshots in Hsnapshot.
                                       simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
                                       ***** injection Heq as Heq. subst snapshot. simpl in Hcolor.
                                             eapply frozen_caller_authority_closure_dangerous;
                                               [|exact Hcolor].
                                             apply frame_resume_exposure_colors_dangerous.
                                       ***** eapply (proj1 (proj2 (proj2 Htail_exposure))); eauto.
                                  ++++ split.
                                       ***** intros snapshot Hsnapshot state Hentry.
                                       unfold enter_frozen_caller_snapshots in Hsnapshot.
                                       simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
                                       ----- injection Heq as Heq. subst snapshot. simpl in *.
                                             apply frozen_caller_authority_closure_contains.
                                             exact Hentry.
                                       ----- eapply (proj1 (proj2 (proj2
                                               (proj2 Htail_exposure)))); eauto.
                                       ***** intros snapshot root Hsnapshot
                                               Hroot Hroot_runtime.
                                             unfold enter_frozen_caller_snapshots
                                               in Hsnapshot.
                                             simpl in Hsnapshot.
                                             destruct Hsnapshot as [Heq | Htail].
                                             ----- injection Heq as Heq.
                                                   subst snapshot. simpl in *.
                                                   apply frozen_caller_authority_closure_contains.
                                                   eapply frame_resume_exposure_contains_mutable_rdm_root;
                                                     eauto.
                                             ----- eapply (proj2 (proj2 (proj2
                                                     (proj2 Htail_exposure))));
                                                     eauto.
                     +++ split.
                         *** intros snapshot mode source exposure_mode target Hsnapshot
                           Hmode Hactive Hsource Hexposure_mode Htarget.
                         unfold enter_frozen_caller_snapshots in Hsnapshot.
                         simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
                         ---- injection Heq as Heq. subst snapshot.
                             exfalso.
                             exact
                               (channel_free_entry_has_no_independent_active_authority_color
                                 CT h boundary (mode, source) Hfree Hactive).
                         ---- eapply Htail_resume with (snapshot := snapshot)
                               (active_mode := mode) (source := source)
                               (exposure_mode := exposure_mode) (target := target);
                               eauto.
                         *** split.
                             ---- intros snapshot source_mode source Hsnapshot
                               Hsource_mode Hsource_color Hsource_root.
                             unfold enter_frozen_caller_snapshots in Hsnapshot.
                             simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
                                  ++++ injection Heq as Heq. subst snapshot. simpl in *.
                                       left. exists source_mode. split; assumption.
                                  ++++ eapply Htail_joins; eauto.
                             ---- split; assumption.
Qed.

(** Channel-free tracked entry with a stack-compositional head.  The extra
    [caller_colors] closure fact is derived from the caller's executing
    color-set definition by the private call-entry wrapper. *)
Lemma principled_frozen_authority_enter_nested_channel_free :
  forall CT P Z cutoff boundary stack h caller_colors snapshots,
    let caller := boundary.(boundary_caller) in
    let callee := mk_watched_frame
      (call_authority caller.(frame_authority)
        boundary.(boundary_receiver_view))
      boundary.(boundary_callee_entry_senv)
      boundary.(boundary_callee_entry_renv) in
    principled_phased_authority_live_history_state CT P Z cutoff
      callee (boundary :: stack) caller_colors h ->
    frozen_caller_snapshots_aligned snapshots stack ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_closed CT h caller snapshots ->
    frozen_caller_snapshots_retain_entry snapshots ->
    frozen_caller_snapshots_dangerous snapshots ->
    frozen_caller_snapshots_avoid_protected Z snapshots ->
    authority_colors_runtime_mutable h caller_colors ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h caller caller_colors)
      caller_colors ->
    entry_ownership_channel_free boundary ->
    frozen_caller_snapshots_avoid_protected Z
      (advance_frozen_caller_snapshots CT h callee snapshots) ->
    frozen_caller_snapshots_resume_roots_in_heap h
      (advance_frozen_caller_snapshots CT h callee snapshots) ->
    frozen_caller_snapshots_resume_exposures_wf CT h callee
      (advance_frozen_caller_snapshots CT h callee snapshots) ->
    frozen_caller_snapshots_resume_roots_safe CT h Z callee
      (advance_frozen_caller_snapshots CT h callee snapshots) ->
    frozen_caller_snapshots_resume_joins_safe Z
      (advance_frozen_caller_snapshots CT h callee snapshots) ->
    frozen_caller_snapshots_entry_exposure_covered
      (enter_frozen_caller_snapshots CT h caller callee caller_colors
        snapshots) ->
    frozen_caller_snapshots_cover_phase_incoming
      (enter_frozen_caller_snapshots CT h caller callee caller_colors
        snapshots) ->
    principled_frozen_authority_history_state CT P Z cutoff callee
      (boundary :: stack) caller_colors
      (enter_nested_frozen_caller_snapshots CT h caller callee caller_colors
        snapshots) h.
Proof.
  intros CT P Z cutoff boundary stack h caller_colors snapshots caller callee
    Hstate Haligned Hsnapshots_runtime Hsnapshots_closed Hsnapshots_retain
    Hsnapshots_dangerous Hsnapshots_avoid Hcaller_runtime Hcaller_closed Hfree
    Htail_avoid Htail_roots Htail_exposure Htail_resume Htail_joins
    Hentry_covered Hphase_covered.
  have Hold := principled_frozen_authority_enter_channel_free CT P Z cutoff
    boundary stack h caller_colors snapshots Hstate Haligned
    Hsnapshots_runtime Hsnapshots_retain Hsnapshots_dangerous Hcaller_runtime
    Hfree Htail_avoid Htail_roots Htail_exposure Htail_resume Htail_joins
    Hentry_covered Hphase_covered.
  set (old_head := mk_frozen_caller_color_snapshot
    (frozen_caller_authority_closure CT h callee
      (dangerous_authority_colors caller_colors))
    (frozen_caller_authority_closure CT h callee
      (dangerous_authority_colors caller_colors))
    caller_colors
    caller_colors (frame_rdm_root_set caller)
    (frame_resume_exposure_colors CT h caller)
    (frozen_caller_authority_closure CT h callee
      (frame_resume_exposure_colors CT h caller))
    caller
    caller.(frame_authority)).
  set (new_head := nested_frozen_call_head CT h caller callee caller_colors
    snapshots).
  set (tail := advance_frozen_caller_snapshots CT h callee snapshots).
  change (principled_frozen_authority_history_state CT P Z cutoff callee
    (boundary :: stack) caller_colors (Some old_head :: tail) h) in Hold.
  have Hold_copy := Hold.
  destruct Hold_copy as
    (Hold_main & Hold_aligned & Hold_runtime & Hold_closed & Hold_retain &
      Hold_dangerous & Hold_avoid & Hold_roots & Hold_exposure & Hold_resume &
      Hold_joins & Hold_entry & Hold_phase).
  change (principled_frozen_authority_history_state CT P Z cutoff callee
    (boundary :: stack) caller_colors (Some new_head :: tail) h).
  eapply principled_frozen_authority_replace_head with (old_head := old_head).
  - exact Hold.
  - intros snapshot Hsnapshot. simpl in Hsnapshot.
    destruct Hsnapshot as [Heq | Hbad]; [|contradiction].
    injection Heq as Heq. subst snapshot. unfold new_head.
    eapply nested_frozen_call_head_runtime_mutable; eauto.
  - intros snapshot Hsnapshot. simpl in Hsnapshot.
    destruct Hsnapshot as [Heq | Hbad]; [|contradiction].
    injection Heq as Heq. subst snapshot. unfold new_head.
    apply nested_frozen_call_head_closed.
  - intros snapshot Hsnapshot. simpl in Hsnapshot.
    destruct Hsnapshot as [Heq | Hbad]; [|contradiction].
    injection Heq as Heq. subst snapshot. unfold new_head.
    apply nested_frozen_call_head_retains_entry.
  - intros snapshot mode location Hsnapshot Hcolor. simpl in Hsnapshot.
    destruct Hsnapshot as [Heq | Hbad]; [|contradiction].
    injection Heq as Heq. subst snapshot. unfold new_head.
    exact (nested_frozen_call_head_dangerous CT h caller callee caller_colors
      snapshots Hsnapshots_dangerous mode location Hcolor).
  - intros snapshot mode location Hsnapshot Hmode Hcolor. simpl in Hsnapshot.
    destruct Hsnapshot as [Heq | Hbad]; [|contradiction].
    injection Heq as Heq. subst snapshot. unfold new_head.
    eapply nested_frozen_call_head_avoids_protected.
    + exact Hfree.
    + exact Hcaller_closed.
    + intros caller_mode caller_location Hcaller_mode Hcaller_color.
      have Hseparated := proj1 (proj2 (proj2 (proj2 Hstate))).
      eapply Hseparated; [exact Hcaller_mode|].
      apply executing_authority_color_set_contains_incoming.
      exact Hcaller_color.
    + exact Hsnapshots_closed.
    + exact Hsnapshots_avoid.
    + exact Hmode.
    + exact Hcolor.
  - intros snapshot root Hsnapshot Hroot. simpl in Hsnapshot.
    destruct Hsnapshot as [Heq | Hbad]; [|contradiction].
    injection Heq as Heq. subst snapshot.
    unfold new_head, nested_frozen_call_head in Hroot. simpl in Hroot.
    unfold frame_rdm_root_set, typed_root in Hroot.
    destruct Hroot as [variable [T [Htype [Hvalue Hrdm]]]].
    have Hframes := proj1 (proj2 (proj2 (proj2 (proj2 Hstate)))).
    have Hcaller_wf := Forall_inv (proj2 Hframes).
    eapply wf_config_value_dom; eauto.
  - repeat split.
    + intros snapshot Hsnapshot mode location Hcolor. simpl in Hsnapshot.
      destruct Hsnapshot as [Heq | Hbad]; [|contradiction].
      injection Heq as Heq. subst snapshot.
      unfold new_head, nested_frozen_call_head in Hcolor. simpl in Hcolor.
      eapply advance_frozen_caller_snapshot_runtime_mutable.
      * exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hstate)))))).
      * have Hframes := proj1 (proj2 (proj2 (proj2 (proj2 Hstate)))).
        have Hcaller_wf := Forall_inv (proj2 Hframes).
        apply frame_resume_exposure_colors_runtime_mutable. exact Hcaller_wf.
      * exact Hcolor.
    + intros snapshot Hsnapshot. simpl in Hsnapshot.
      destruct Hsnapshot as [Heq | Hbad]; [|contradiction].
      injection Heq as Heq. subst snapshot.
      unfold new_head, nested_frozen_call_head. simpl.
      exact (proj1 (frozen_caller_authority_closure_idempotent CT h callee
        (frame_resume_exposure_colors CT h caller))).
    + intros snapshot mode location Hsnapshot Hcolor. simpl in Hsnapshot.
      destruct Hsnapshot as [Heq | Hbad]; [|contradiction].
      injection Heq as Heq. subst snapshot.
      unfold new_head, nested_frozen_call_head in Hcolor. simpl in Hcolor.
      eapply frozen_caller_authority_closure_dangerous;
        [|exact Hcolor].
      apply frame_resume_exposure_colors_dangerous.
    + intros snapshot Hsnapshot state Hcolor. simpl in Hsnapshot.
      destruct Hsnapshot as [Heq | Hbad]; [|contradiction].
      injection Heq as Heq. subst snapshot.
      unfold new_head, nested_frozen_call_head in *. simpl in *.
      apply frozen_caller_authority_closure_contains. exact Hcolor.
    + intros snapshot root Hsnapshot Hroot Hruntime.
      simpl in Hsnapshot.
      destruct Hsnapshot as [Heq | Hbad]; [|contradiction].
      injection Heq as Heq. subst snapshot.
      unfold new_head, nested_frozen_call_head in *. simpl in *.
      apply frozen_caller_authority_closure_contains.
      eapply frame_resume_exposure_contains_mutable_rdm_root; eauto.
  - intros snapshot active_mode source exposure_mode target Hsnapshot
      Hactive_mode Hactive Hsource Hexposure_mode Htarget.
    exfalso. exact
      (channel_free_entry_has_no_independent_active_authority_color CT h
        boundary (active_mode, source) Hfree Hactive).
  - intros snapshot source_mode source Hsnapshot Hsource_mode Hsource Hroot.
    simpl in Hsnapshot. destruct Hsnapshot as [Heq | Hbad]; [|contradiction].
    injection Heq as Heq. subst snapshot. left. exists source_mode.
    unfold new_head, nested_frozen_call_head in *. simpl in *. split; assumption.
  - intros snapshot source_mode source Hsnapshot Hsource_mode Hsource Hroot.
    simpl in Hsnapshot. destruct Hsnapshot as [Heq | Hbad]; [|contradiction].
    injection Heq as Heq. subst snapshot. unfold new_head.
    eapply nested_frozen_call_head_entry_exposure_covered; eauto.
  - intros snapshot mode location Hsnapshot Hmode Hincoming.
    simpl in Hsnapshot. destruct Hsnapshot as [Heq | Hbad]; [|contradiction].
    injection Heq as Heq. subst snapshot.
    unfold new_head, nested_frozen_call_head. simpl in *.
    apply frozen_caller_authority_closure_contains. left. split; assumption.
Qed.

(** Public-facing package for the directional preservation theorem.  The
    incoming authority color set is existentially hidden: callers provide
    one history-state premise, exactly as before, while the statement proof
    retains the witness through nested evaluations.  This changes no
    operational or typing premise and exposes no dispatch condition. *)
Definition flexible_live_history_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary) (h : heap) : Prop :=
  exists incoming,
    principled_phased_authority_live_history_state CT P Z cutoff
      active stack incoming h.

(** Proof-local strengthening used only while checking a flexible override
    body.  Keeping it separate from
    [principled_phased_authority_live_history_state] is deliberate: neither
    this component condition nor any equivalent obligation is a premise of
    the public statement-preservation theorem. *)
Definition principled_local_mutable_rdm_history_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary)
  (incoming : Ensemble authority_flow_state) (h : heap) : Prop :=
  principled_phased_authority_live_history_state CT P Z cutoff
    active stack incoming h /\
  active_mutable_rdm_components_after_cutoff CT h cutoff active.

(** Nested version of the preceding private package.  The stack-wide
    component fact is needed only by the strengthened statement induction;
    clients of the public theorem never construct or mention it. *)
Definition principled_live_mutable_rdm_history_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary)
  (incoming : Ensemble authority_flow_state) (h : heap) : Prop :=
  principled_phased_authority_live_history_state CT P Z cutoff
    active stack incoming h /\
  live_mutable_rdm_components_after_cutoff CT h cutoff active stack.

(** Private package for the exceptional channel-free flexible-return body.
    The ordinary frozen history tracks caller provenance, the stack-wide
    component invariant keeps runtime-mutable RDM components in the fresh
    suffix, and the final conjunct records the channel-free fact that frozen
    caller authority has not become independently owned by the active frame.
    This package is constructed after dispatch and is eliminated at pop; it
    is never a premise of a public theorem. *)
Definition principled_separated_frozen_mutable_rdm_history_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary)
  (incoming : Ensemble authority_flow_state)
  (snapshots : list frozen_caller_snapshot_slot) (h : heap) : Prop :=
  principled_frozen_authority_history_state CT P Z cutoff active stack
    incoming snapshots h /\
  live_mutable_rdm_components_after_cutoff CT h cutoff active stack /\
  frozen_caller_snapshots_independently_separated CT h active snapshots.

(** Allocation-stable exceptional-body package.  Unlike the older
    globally-disjoint package above, this records only the resume-root origin
    needed when a frozen color and independent active authority overlap.
    Harmless fresh overlap is admitted; the witness is consumed at pop and
    never appears in the public theorem. *)
Definition principled_root_scoped_frozen_mutable_rdm_history_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary)
  (incoming : Ensemble authority_flow_state)
  (snapshots : list frozen_caller_snapshot_slot) (h : heap) : Prop :=
  principled_frozen_authority_history_state CT P Z cutoff active stack
    incoming snapshots h /\
  live_mutable_rdm_components_after_cutoff CT h cutoff active stack /\
  frozen_caller_snapshots_active_resume_origins CT h active snapshots.

Lemma principled_phased_active_mut_root_not_in_protected_zone :
  forall CT P Z cutoff active stack incoming h root,
    principled_phased_authority_live_history_state CT P Z cutoff
      active stack incoming h ->
    typed_root Mut active.(frame_senv) active.(frame_renv) root ->
    ~ In Loc Z root.
Proof.
  intros CT P Z cutoff active stack incoming h root Hstate Hroot Hprotected.
  have Hseparated := proj1 (proj2 (proj2 (proj2 Hstate))).
  have Hcolored : In authority_flow_state
      (executing_authority_color_set CT h active incoming)
      (FlowPowered, root).
  { eapply executing_authority_owned_is_powered.
    exists root. split; [|constructor].
    destruct Hroot as [variable [T [Htype [Hvalue Hmut]]]].
    exists variable, T. repeat split; try assumption.
    unfold capability_in_context. left. exact Hmut. }
  exact (Hseparated FlowPowered root (or_introl eq_refl) Hcolored Hprotected).
Qed.

(** In a local run whose protected zone contains its whole entry-reachable
    set, a returned mutable root is necessarily allocated after the entry
    cutoff.  This is the freshness fact needed by the flexible RDM-to-Mut
    return case. *)
Lemma principled_phased_local_mut_root_is_fresh :
  forall CT P Z cutoff active stack incoming h variable T root,
    principled_phased_authority_live_history_state CT P Z cutoff
      active stack incoming h ->
    static_getType active.(frame_senv) variable = Some T ->
    runtime_getVal active.(frame_renv) variable = Some (Iot root) ->
    sqtype T = Mut ->
    cutoff <= root.
Proof.
  intros CT P Z cutoff active stack incoming h variable T root Hstate
    Htype Hvalue Hmut.
  have Hcontains := proj1 Hstate.
  have Hconfined := proj1 (proj2 Hstate).
  have Hnot_protected : ~ In Loc Z root.
  { eapply principled_phased_active_mut_root_not_in_protected_zone;
      [exact Hstate|].
    exists variable, T. repeat split; assumption. }
  destruct (proj1 Hconfined variable root Hvalue) as [HinP | Hfresh];
    [|exact Hfresh].
  exfalso. apply Hnot_protected. apply Hcontains. exact HinP.
Qed.

Lemma active_mutable_rdm_components_after_descent :
  forall CT h cutoff authority old_senv old_renv new_senv new_renv,
    wf_r_config CT old_senv old_renv h ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    active_mutable_rdm_components_after_cutoff CT h cutoff
      (mk_watched_frame authority old_senv old_renv) ->
    active_mutable_rdm_components_after_cutoff CT h cutoff
      (mk_watched_frame authority new_senv new_renv).
Proof.
  intros CT h cutoff authority old_senv old_renv new_senv new_renv Hwf
    Hdescend Hold root target Hroot Hroot_runtime Hroot_target.
  destruct (Hdescend root Hroot) as
    [old_root [Hold_root Hold_root_to_root]].
  have Hroot_to_old : mutable_connected CT h root old_root.
  { eapply mutable_connected_sym.
    eapply mutable_reachable_connected. exact Hold_root_to_root. }
  have Hold_root_runtime : r_muttype h old_root = Some Mut_r.
  { eapply mutable_connected_preserves_runtime_mutability;
      [exact (proj1 (proj2 Hwf))|exact Hroot_to_old|exact Hroot_runtime]. }
  eapply Hold with (root := old_root).
  - exact Hold_root.
  - exact Hold_root_runtime.
  - eapply mutable_reachable_trans; eauto.
Qed.

Lemma live_mutable_rdm_components_after_active_descent :
  forall CT h cutoff authority old_senv old_renv new_senv new_renv stack,
    wf_r_config CT old_senv old_renv h ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    live_mutable_rdm_components_after_cutoff CT h cutoff
      (mk_watched_frame authority old_senv old_renv) stack ->
    live_mutable_rdm_components_after_cutoff CT h cutoff
      (mk_watched_frame authority new_senv new_renv) stack.
Proof.
  intros CT h cutoff authority old_senv old_renv new_senv new_renv stack
    Hwf Hdescend Hold frame root target Hlive Hroot Hruntime Hreachable.
  inversion Hlive; subst.
  - have Hactive := active_mutable_rdm_components_after_descent CT h cutoff
      authority old_senv old_renv new_senv new_renv Hwf Hdescend
      (live_mutable_rdm_components_active CT h cutoff
        (mk_watched_frame authority old_senv old_renv) stack Hold).
    eapply Hactive; eauto.
  - eapply Hold; eauto. constructor. exact H.
Qed.

Lemma active_mutable_rdm_components_after_assignment :
  forall CT cutoff authority sGamma mt rGamma h x expression old value,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SVarAss x expression) sGamma ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma x = Some old ->
    eval_expr CT rGamma h expression value OK rGamma h ->
    active_mutable_rdm_components_after_cutoff CT h cutoff
      (mk_watched_frame authority sGamma rGamma) ->
    active_mutable_rdm_components_after_cutoff CT h cutoff
      (mk_watched_frame authority sGamma
        (update_r_env_value rGamma x value)).
Proof.
  intros CT cutoff authority sGamma mt rGamma h x expression old value Hwf
    Htyping Hscope Hvalue Heval Hcomponents.
  eapply active_mutable_rdm_components_after_descent; eauto.
  eapply rdm_roots_descend_after_assignment; eauto.
Qed.

Lemma active_mutable_rdm_components_after_local :
  forall CT cutoff authority sGamma mt rGamma h T x sGamma',
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SLocal T x) sGamma' ->
    runtime_getVal rGamma x = None ->
    active_mutable_rdm_components_after_cutoff CT h cutoff
      (mk_watched_frame authority sGamma rGamma) ->
    active_mutable_rdm_components_after_cutoff CT h cutoff
      (mk_watched_frame authority sGamma'
        (set_vars rGamma (vars rGamma ++ [Null_a]))).
Proof.
  intros CT cutoff authority sGamma mt rGamma h T x sGamma' Hwf Htyping
    Hnone Hcomponents.
  eapply active_mutable_rdm_components_after_descent; eauto.
  eapply rdm_roots_descend_after_local; eauto.
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

Lemma frozen_callee_side_components_after_assignment :
  forall CT h authority sGamma mt rGamma stack snapshots x expression old
    value,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SVarAss x expression) sGamma ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma x = Some old ->
    eval_expr CT rGamma h expression value OK rGamma h ->
    frozen_callee_side_mutable_components_after_boundaries CT h
      (mk_watched_frame authority sGamma rGamma) snapshots stack ->
    frozen_callee_side_mutable_components_after_boundaries CT h
      (mk_watched_frame authority sGamma
        (update_r_env_value rGamma x value))
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority sGamma
          (update_r_env_value rGamma x value)) snapshots) stack.
Proof.
  intros CT h authority sGamma mt rGamma stack snapshots x expression old
    value Hwf Htyping Hscope Hvalue Heval Hold snapshot boundary above below
    Hpartition.
  destruct (advance_frozen_snapshot_live_partition_reflects CT h
    (mk_watched_frame authority sGamma
      (update_r_env_value rGamma x value)) snapshots stack snapshot boundary
    above below Hpartition) as [old_snapshot Hold_partition].
  have Hold_components := Hold old_snapshot boundary above below
    Hold_partition.
  eapply live_mutable_authority_components_after_assignment; eauto.
Qed.

Lemma frozen_callee_side_components_after_local :
  forall CT h authority sGamma mt rGamma stack snapshots T x sGamma',
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SLocal T x) sGamma' ->
    runtime_getVal rGamma x = None ->
    frozen_callee_side_mutable_components_after_boundaries CT h
      (mk_watched_frame authority sGamma rGamma) snapshots stack ->
    frozen_callee_side_mutable_components_after_boundaries CT h
      (mk_watched_frame authority sGamma'
        (set_vars rGamma (vars rGamma ++ [Null_a])))
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority sGamma'
          (set_vars rGamma (vars rGamma ++ [Null_a]))) snapshots) stack.
Proof.
  intros CT h authority sGamma mt rGamma stack snapshots T x sGamma' Hwf
    Htyping Hnone Hold snapshot boundary above below Hpartition.
  destruct (advance_frozen_snapshot_live_partition_reflects CT h
    (mk_watched_frame authority sGamma'
      (set_vars rGamma (vars rGamma ++ [Null_a]))) snapshots stack snapshot
    boundary above below Hpartition) as [old_snapshot Hold_partition].
  have Hold_components := Hold old_snapshot boundary above below
    Hold_partition.
  eapply live_mutable_authority_components_after_local; eauto.
Qed.

(** Once an executing dangerous color is in the fresh region, following a
    directed RDM path cannot re-enter the protected entry region.  Heap
    confinement says that each such edge either stays fresh or enters [P];
    the latter alternative is excluded because [P] is contained in [Z] and
    the color closure follows the same directed RDM edge. *)
Lemma executing_authority_mutable_reachable_stays_after_cutoff :
  forall CT P Z cutoff frame stack incoming h mode root target,
    principled_phased_authority_live_history_state CT P Z cutoff
      frame stack incoming h ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT h frame incoming) (mode, root) ->
    cutoff <= root ->
    mutable_reachable CT h root target ->
    cutoff <= target.
Proof.
  intros CT P Z cutoff frame stack incoming h mode root target Hstate Hmode
    Hroot_color Hroot_fresh Hreachable.
  have Hcontains := proj1 Hstate.
  have Hconfined := proj1 (proj2 Hstate).
  have Hseparated := proj1 (proj2 (proj2 (proj2 Hstate))).
  induction Hreachable as
    [location | start middle finish Hprefix IH Hedge].
  - exact Hroot_fresh.
  - have Hmiddle_fresh := IH Hroot_color Hroot_fresh.
    have Hmiddle_color : In authority_flow_state
        (executing_authority_color_set CT h frame incoming) (mode, middle).
    { eapply executing_authority_dangerous_retained_reachable;
        [exact Hmode|exact Hroot_color|].
      eapply mutable_reachable_is_retained. exact Hprefix. }
    have Hfinish_color : In authority_flow_state
        (executing_authority_color_set CT h frame incoming) (mode, finish).
    { eapply executing_authority_dangerous_retained;
        [exact Hmode|exact Hmiddle_color|].
      constructor. exact Hedge. }
    have Hraw : raw_heap_edge h middle finish.
    { inversion Hedge; subst. exists o, f. split; assumption. }
    destruct (proj2 Hconfined middle finish (or_intror Hmiddle_fresh) Hraw)
      as [HinP | Hfinish_fresh]; [|exact Hfinish_fresh].
    exfalso.
    exact (Hseparated mode finish Hmode Hfinish_color
      (Hcontains finish HinP)).
Qed.

Lemma principled_phased_frame_owned_is_after_cutoff :
  forall CT P Z cutoff frame stack incoming h location,
    principled_phased_authority_live_history_state CT P Z cutoff
      frame stack incoming h ->
    frame_owned_location CT h frame location ->
    cutoff <= location.
Proof.
  intros CT P Z cutoff frame stack incoming h location Hstate Howned.
  have Hcontains := proj1 Hstate.
  have Hconfined := proj1 (proj2 Hstate).
  have Hseparated := proj1 (proj2 (proj2 (proj2 Hstate))).
  have Hcolored := executing_authority_owned_is_powered CT h frame incoming
    location Howned.
  have Hnot_zone : ~ In Loc Z location.
  { intros Hzone.
    exact (Hseparated FlowPowered location (or_introl eq_refl)
      Hcolored Hzone). }
  destruct Howned as [root [Hroot Hreachable]].
  have Hroot_confined : confined_loc P cutoff root.
  { destruct Hroot as
      [variable [T [Htype [Hvalue Hcapability]]]].
    eapply (proj1 Hconfined); eauto. }
  have Hlocation_confined : confined_loc P cutoff location.
  { clear Hroot Hcolored Hnot_zone.
    revert Hroot_confined.
    induction Hreachable as
      [root | root middle target Hprefix IH Hedge]; intros Hroot_confined.
    - exact Hroot_confined.
    - apply (proj2 Hconfined middle target (IH Hroot_confined)).
      inversion Hedge as
        [source destination Hrdm |
         source destination object field D field_def Hobject Hruntime
           Hfield Hbase Hdefinition Hmutability]; subst.
      + inversion Hrdm; subst. exists o, f. split; assumption.
      + exists object, field. split; assumption. }
  destruct Hlocation_confined as [HinP | Hfresh]; [|exact Hfresh].
  exfalso. apply Hnot_zone. apply Hcontains. exact HinP.
Qed.

Lemma mutable_reachable_after_field_update :
  forall CT h lx old field value root target,
    runtime_getObj h lx = Some old ->
    mutable_reachable CT (update_field h lx field value) root target ->
    mutable_reachable CT h root target \/
    exists written,
      value = Iot written /\
      mutable_reachable CT h root lx /\
      mutable_reachable CT h written target.
Proof.
  intros CT h lx old field value root target Hobj Hreachable.
  induction Hreachable as
    [root | root middle target Hprefix IH Hedge].
  - left. constructor.
  - destruct (mutable_edge_after_field_update CT h lx old field value
      middle target Hobj Hedge) as
      [Hold_edge | [Hmiddle [Hvalue Hnew_edge]]].
    + destruct IH as
        [Hold_prefix | [written [Hwritten [Hto_source Hsuffix]]]].
      * left. eapply mr_step; eauto.
      * right. exists written. repeat split; try assumption.
        eapply mr_step; eauto.
    + subst middle.
      destruct IH as
        [Hold_prefix | [written [Hwritten [Hto_source Hsuffix]]]].
      * right. exists target. repeat split; try assumption. constructor.
      * rewrite Hvalue in Hwritten. injection Hwritten as <-.
        right. exists target. repeat split; try assumption. constructor.
Qed.

Lemma active_mutable_rdm_components_after_safe_field_update :
  forall CT P Z cutoff frame stack incoming h lx old field written,
    principled_phased_authority_live_history_state CT P Z cutoff
      frame stack incoming h ->
    active_mutable_rdm_components_after_cutoff CT h cutoff frame ->
    runtime_getObj h lx = Some old ->
    authority_safe_field_endpoints CT h frame lx written ->
    active_mutable_rdm_components_after_cutoff CT
      (update_field h lx field (Iot written)) cutoff frame.
Proof.
  intros CT P Z cutoff frame stack incoming h lx old field written Hstate
    Hold Hobj Hendpoints root target Hroot Hroot_runtime Hreachable.
  have Hframes := proj1 (proj2 (proj2 (proj2 (proj2 Hstate)))).
  have Hwf := proj1 Hframes.
  have Hheap := proj1 (proj2 Hwf).
  have Hroot_runtime_old : r_muttype h root = Some Mut_r.
  { rewrite r_muttype_update_field_preserve in Hroot_runtime.
    exact Hroot_runtime. }
  destruct (mutable_reachable_after_field_update CT h lx old field
    (Iot written) root target Hobj Hreachable) as
    [Hold_path | [new_written [Hvalue [Hroot_lx Hwritten_target]]]].
  - eapply Hold; eauto.
  - injection Hvalue as <-.
    have Hlx_runtime : r_muttype h lx = Some Mut_r.
    { eapply mutable_reachable_preserves_runtime_mutability;
        [exact Hheap|exact Hroot_lx|exact Hroot_runtime_old]. }
    have Hlx_fresh : cutoff <= lx.
    { eapply Hold; eauto. }
    inversion Hendpoints; subst.
    + have Hwritten_fresh : cutoff <= written.
      { eapply principled_phased_frame_owned_is_after_cutoff; eauto. }
      have Hwritten_powered : In authority_flow_state
          (executing_authority_color_set CT h frame incoming)
          (FlowPowered, written).
      { eapply executing_authority_owned_is_powered. exact H0. }
      eapply executing_authority_mutable_reachable_stays_after_cutoff
        with (mode := FlowPowered) (root := written); eauto.
      left. reflexivity.
    + rewrite H in Hlx_runtime. discriminate.
    + have Hcontexts := active_rdm_roots_share_runtime_context CT
        frame.(frame_senv) frame.(frame_renv) h lx written Hwf
        H H0.
      destruct Hcontexts as [runtime_q [Hlx_context Hwritten_context]].
      rewrite Hlx_runtime in Hlx_context. injection Hlx_context as <-.
      eapply Hold with (root := written).
      * exact H0.
      * exact Hwritten_context.
      * exact Hwritten_target.
Qed.

Lemma live_mutable_rdm_components_after_safe_field_update :
  forall CT P Z cutoff frame stack incoming h lx old field written,
    principled_phased_authority_live_history_state CT P Z cutoff
      frame stack incoming h ->
    live_mutable_rdm_components_after_cutoff CT h cutoff frame stack ->
    runtime_getObj h lx = Some old ->
    authority_safe_field_endpoints CT h frame lx written ->
    live_mutable_rdm_components_after_cutoff CT
      (update_field h lx field (Iot written)) cutoff frame stack.
Proof.
  intros CT P Z cutoff frame stack incoming h lx old field written Hstate
    Hold Hobj Hendpoints live root target Hlive Hroot Hroot_runtime
    Hreachable.
  have Hframes := proj1 (proj2 (proj2 (proj2 (proj2 Hstate)))).
  have Hwf := proj1 Hframes.
  have Hheap := proj1 (proj2 Hwf).
  have Hroot_runtime_old : r_muttype h root = Some Mut_r.
  { rewrite r_muttype_update_field_preserve in Hroot_runtime.
    exact Hroot_runtime. }
  destruct (mutable_reachable_after_field_update CT h lx old field
    (Iot written) root target Hobj Hreachable) as
    [Hold_path | [new_written [Hvalue [Hroot_lx Hwritten_target]]]].
  - eapply Hold; eauto.
  - injection Hvalue as <-.
    have Hlx_runtime : r_muttype h lx = Some Mut_r.
    { eapply mutable_reachable_preserves_runtime_mutability;
        [exact Hheap|exact Hroot_lx|exact Hroot_runtime_old]. }
    have Hlx_fresh : cutoff <= lx.
    { eapply Hold; eauto. }
    inversion Hendpoints; subst.
    + have Hwritten_fresh : cutoff <= written.
      { eapply principled_phased_frame_owned_is_after_cutoff; eauto. }
      have Hwritten_powered : In authority_flow_state
          (executing_authority_color_set CT h frame incoming)
          (FlowPowered, written).
      { eapply executing_authority_owned_is_powered. exact H0. }
      eapply executing_authority_mutable_reachable_stays_after_cutoff
        with (mode := FlowPowered) (root := written); eauto.
      left. reflexivity.
    + rewrite H in Hlx_runtime. discriminate.
    + have Hcontexts := active_rdm_roots_share_runtime_context CT
        frame.(frame_senv) frame.(frame_renv) h lx written Hwf
        H H0.
      destruct Hcontexts as [runtime_q [Hlx_context Hwritten_context]].
      rewrite Hlx_runtime in Hlx_context. injection Hlx_context as <-.
      exact (Hold frame written target (live_frame_active frame stack)
        H0 Hwritten_context Hwritten_target).
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

Lemma frozen_callee_side_prospective_components_after_graph_reflection :
  forall CT old_h new_h active snapshots stack,
    (forall location, r_muttype new_h location = r_muttype old_h location) ->
    (forall left right,
      retained_mut_edge CT new_h left right ->
      retained_mut_edge CT old_h left right) ->
    (forall left right,
      mutable_edge CT new_h left right ->
      mutable_edge CT old_h left right) ->
    frozen_callee_side_prospective_components_after_boundaries CT old_h active
      snapshots stack ->
    frozen_callee_side_prospective_components_after_boundaries CT new_h active
      (advance_frozen_caller_snapshots CT new_h active snapshots) stack.
Proof.
  intros CT old_h new_h active snapshots stack Hruntimes Hretained Hmutable
    Hold snapshot boundary above below Hpartition.
  destruct (advance_frozen_snapshot_live_partition_reflects CT new_h active
    snapshots stack snapshot boundary above below Hpartition) as
    [old_snapshot Hold_partition].
  eapply live_prospective_mutable_authority_components_after_graph_reflection;
    eauto.
Qed.

Lemma frozen_callee_side_components_after_graph_reflection :
  forall CT h h' active snapshots stack,
    (forall location, r_muttype h' location = r_muttype h location) ->
    (forall left right,
      retained_mut_edge CT h' left right ->
      retained_mut_edge CT h left right) ->
    frozen_callee_side_mutable_components_after_boundaries CT h active
      snapshots stack ->
    frozen_callee_side_mutable_components_after_boundaries CT h' active
      (advance_frozen_caller_snapshots CT h' active snapshots) stack.
Proof.
  intros CT h h' active snapshots stack Hruntimes Hedges Hold snapshot
    boundary above below Hpartition.
  destruct (advance_frozen_snapshot_live_partition_reflects CT h' active
    snapshots stack snapshot boundary above below Hpartition) as
    [old_snapshot Hold_partition].
  have Hold_components := Hold old_snapshot boundary above below
    Hold_partition.
  eapply live_mutable_authority_components_after_graph_reflection; eauto.
Qed.

Lemma frozen_callee_side_components_after_safe_field_update :
  forall CT P Z cutoff frame stack incoming snapshots h lx old field written,
    principled_phased_authority_live_history_state CT P Z cutoff
      frame stack incoming h ->
    frozen_callee_side_mutable_components_after_boundaries CT h frame
      snapshots stack ->
    runtime_getObj h lx = Some old ->
    authority_safe_field_endpoints CT h frame lx written ->
    frozen_callee_side_mutable_components_after_boundaries CT
      (update_field h lx field (Iot written)) frame
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) frame snapshots) stack.
Proof.
  intros CT P Z cutoff frame stack incoming snapshots h lx old field written
    Hstate Hold Hobj Hendpoints snapshot boundary above below Hpartition.
  destruct (advance_frozen_snapshot_live_partition_reflects CT
    (update_field h lx field (Iot written)) frame snapshots stack snapshot
    boundary above below Hpartition) as [old_snapshot Hold_partition].
  have Hold_components := Hold old_snapshot boundary above below
    Hold_partition.
  have Hframes := proj1 (proj2 (proj2 (proj2 (proj2 Hstate)))).
  have Hwf := proj1 Hframes.
  have Hsound := proj1
    (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hstate)))))).
  eapply live_mutable_authority_components_after_safe_field_update; eauto.
Qed.

Lemma active_mutable_rdm_components_after_graph_reflection :
  forall CT h h' cutoff frame,
    (forall location, r_muttype h' location = r_muttype h location) ->
    (forall source target,
      mutable_edge CT h' source target ->
      mutable_edge CT h source target) ->
    active_mutable_rdm_components_after_cutoff CT h cutoff frame ->
    active_mutable_rdm_components_after_cutoff CT h' cutoff frame.
Proof.
  intros CT h h' cutoff frame Hruntimes Hedges Hold root target Hroot
    Hroot_runtime Hreachable.
  have Hroot_runtime_old : r_muttype h root = Some Mut_r.
  { rewrite <- Hruntimes. exact Hroot_runtime. }
  have Hreachable_old : mutable_reachable CT h root target.
  { induction Hreachable.
    - constructor.
    - eapply mr_step.
      + eapply IHHreachable; eauto.
      + apply Hedges. exact H. }
  eapply Hold; eauto.
Qed.

Lemma live_mutable_rdm_components_after_graph_reflection :
  forall CT h h' cutoff active stack,
    (forall location, r_muttype h' location = r_muttype h location) ->
    (forall source target,
      mutable_edge CT h' source target ->
      mutable_edge CT h source target) ->
    live_mutable_rdm_components_after_cutoff CT h cutoff active stack ->
    live_mutable_rdm_components_after_cutoff CT h' cutoff active stack.
Proof.
  intros CT h h' cutoff active stack Hruntimes Hedges Hold frame root target
    Hlive Hroot Hroot_runtime Hreachable.
  have Hroot_runtime_old : r_muttype h root = Some Mut_r.
  { rewrite <- Hruntimes. exact Hroot_runtime. }
  have Hreachable_old : mutable_reachable CT h root target.
  { induction Hreachable.
    - constructor.
    - eapply mr_step.
      + eapply IHHreachable; eauto.
      + apply Hedges. exact H. }
  eapply Hold; eauto.
Qed.

(** The complete invariant used by the flexible-override call proof.  The
    first conjunct is the established authority/color history; the second is
    the directional ownership fact for every pending call. *)
Definition principled_potential_live_history_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary) (h : heap) : Prop :=
  potential_live_history_state CT P Z cutoff active stack h /\
  pending_call_ownership_colors_separated CT h active stack.

(** Private, depth-indexed counterpart.  Unlike
    [principled_potential_live_history_state], it imposes no condition on
    boundaries that predate the current public preservation invocation. *)
Definition principled_tracked_potential_live_history_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary)
  (tracked_depth : nat) (h : heap) : Prop :=
  potential_live_history_state CT P Z cutoff active stack h /\
  tracked_pending_call_ownership_colors_separated CT h active stack
    tracked_depth.

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

Lemma staged_frame_adjacent_preserves_runtime_mutability :
  forall CT h frame left right runtime_q,
    wf_r_config CT frame.(frame_senv) frame.(frame_renv) h ->
    staged_frame_adjacent CT h frame left right ->
    r_muttype h left = Some runtime_q ->
    r_muttype h right = Some runtime_q.
Proof.
  intros CT h frame left right runtime_q Hwf
    [[Hretained | Hreverse] | [Hleft Hright]] Hruntime.
  - eapply retained_edge_preserves_runtime_context.
    + exact (proj1 (proj2 Hwf)).
    + exact Hretained.
    + exact Hruntime.
  - eapply mutable_edge_reflects_runtime_mutability.
    + exact (proj1 (proj2 Hwf)).
    + exact Hreverse.
    + exact Hruntime.
  - destruct (active_rdm_roots_share_runtime_context CT frame.(frame_senv)
      frame.(frame_renv) h left right Hwf Hleft Hright) as
      [context [Hleft_context Hright_context]].
    rewrite Hruntime in Hleft_context. injection Hleft_context as <-.
    exact Hright_context.
Qed.

Lemma staged_frame_connected_preserves_runtime_mutability :
  forall CT h frame left right runtime_q,
    wf_r_config CT frame.(frame_senv) frame.(frame_renv) h ->
    staged_frame_connected CT h frame left right ->
    r_muttype h left = Some runtime_q ->
    r_muttype h right = Some runtime_q.
Proof.
  intros CT h frame left right runtime_q Hwf Hconnected.
  induction Hconnected; intros Hruntime.
  - eapply staged_frame_adjacent_preserves_runtime_mutability; eauto.
  - exact Hruntime.
  - apply IHHconnected2. apply IHHconnected1. exact Hruntime.
Qed.

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

Lemma mutable_connected_is_staged_frame_connected :
  forall CT h frame left right,
    mutable_connected CT h left right ->
    staged_frame_connected CT h frame left right.
Proof.
  intros CT h frame left right Hconnected.
  induction Hconnected.
  - apply rt_step. left.
    destruct H as [Hforward | Hbackward].
    + left. constructor. exact Hforward.
    + right. exact Hbackward.
  - apply rt_refl.
  - eapply rt_trans; eauto.
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

Lemma staged_return_adjacent_symmetric :
  forall h callee boundary left right,
    staged_return_adjacent h callee boundary left right ->
    staged_return_adjacent h callee boundary right left.
Proof.
  intros h callee boundary left right
    [Hview [Hreturn [Hruntime [Hroots | Hroots]]]].
  - repeat split; try assumption.
    + symmetry. exact Hruntime.
    + right. split; [exact (proj2 Hroots)|exact (proj1 Hroots)].
  - repeat split; try assumption.
    + symmetry. exact Hruntime.
    + left. split; [exact (proj2 Hroots)|exact (proj1 Hroots)].
Qed.

Lemma staged_return_connected_preserves_runtime_mutability :
  forall h callee boundary left right runtime_q,
    staged_return_connected h callee boundary left right ->
    r_muttype h left = Some runtime_q ->
    r_muttype h right = Some runtime_q.
Proof.
  intros h callee boundary left right runtime_q Hconnected.
  induction Hconnected; intros Hleft.
  - destruct H as [_ [_ [Hruntime _]]].
    rewrite Hleft in Hruntime. symmetry. exact Hruntime.
  - exact Hleft.
  - apply IHHconnected2. apply IHHconnected1. exact Hleft.
Qed.

Lemma staged_return_connected_classifies :
  forall h callee boundary left right,
    staged_return_connected h callee boundary left right ->
    left = right \/
    (boundary.(boundary_receiver_view) = RDM /\
     boundary.(boundary_callee_return_qualifier) = RDM /\
     r_muttype h left = r_muttype h right /\
     staged_return_root callee boundary left /\
     staged_return_root callee boundary right).
Proof.
  intros h callee boundary left right Hconnected.
  induction Hconnected.
  - right. destruct H as
      [Hview [Hreturn [Hruntime [Hroots | Hroots]]]].
    + repeat split; try assumption.
      * left. exact (proj1 Hroots).
      * right. exact (proj2 Hroots).
    + repeat split; try assumption.
      * right. exact (proj1 Hroots).
      * left. exact (proj2 Hroots).
  - left. reflexivity.
  - destruct IHHconnected1 as [Hxy | Hxy];
      destruct IHHconnected2 as [Hyz | Hyz].
    + left. congruence.
    + subst x. right. exact Hyz.
    + subst z. right. exact Hxy.
    + right.
      destruct Hxy as
        [Hview [Hreturn [Hruntime_xy [Hx Hy]]]].
      destruct Hyz as
        [_ [_ [Hruntime_yz [_ Hz]]]].
      repeat split; try assumption.
      rewrite Hruntime_xy. exact Hruntime_yz.
Qed.

Lemma staged_frame_closure_contains :
  forall CT h frame seeds,
    Included Loc seeds (staged_frame_closure CT h frame seeds).
Proof.
  intros CT h frame seeds location Hlocation.
  exists location. split; [exact Hlocation|apply rt_refl].
Qed.

Lemma staged_return_closure_contains :
  forall h callee boundary seeds,
    Included Loc seeds (staged_return_closure h callee boundary seeds).
Proof.
  intros h callee boundary seeds location Hlocation.
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

Lemma staged_frame_closure_idempotent :
  forall CT h frame seeds,
    Same_set Loc
      (staged_frame_closure CT h frame
        (staged_frame_closure CT h frame seeds))
      (staged_frame_closure CT h frame seeds).
Proof.
  intros CT h frame seeds. split.
  - intros location [middle [[seed [Hseed Hseed_middle]]
      Hmiddle_location]].
    exists seed. split; [exact Hseed|].
    eapply staged_frame_connected_trans; eauto.
  - eapply staged_frame_closure_contains.
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

Lemma staged_live_color_set_monotone :
  forall CT h active stack old new,
    Included Loc old new ->
    Included Loc
      (staged_live_color_set CT h active stack old)
      (staged_live_color_set CT h active stack new).
Proof.
  intros CT h active stack. revert active.
  induction stack as [|boundary tail IH];
    intros active old new Hincluded location Hlocation; simpl in *.
  - eapply staged_frame_closure_monotone; eauto.
  - eapply (IH boundary.(boundary_caller)); [|exact Hlocation].
    eapply staged_return_closure_monotone.
    eapply staged_frame_closure_monotone.
    exact Hincluded.
Qed.

Lemma staged_live_color_set_absorbs_active_frame_closure :
  forall CT h active stack seeds,
    Included Loc
      (staged_live_color_set CT h active stack
        (staged_frame_closure CT h active seeds))
      (staged_live_color_set CT h active stack seeds).
Proof.
  intros CT h active stack seeds. destruct stack as [|boundary tail]; simpl.
  - intros location Hlocation.
    exact (proj1 (staged_frame_closure_idempotent CT h active seeds)
      location Hlocation).
  - eapply staged_live_color_set_monotone.
    eapply staged_return_closure_monotone.
    apply (proj1 (staged_frame_closure_idempotent CT h active seeds)).
Qed.

Lemma phased_live_color_set_from_absorbs_active_frame :
  forall CT h active stack incoming,
    Included Loc
      (phased_live_color_set_from CT h active stack
        (staged_frame_closure CT h active
          (Union Loc incoming (phase_frame_capability_set CT h active))))
      (phased_live_color_set_from CT h active stack incoming).
Proof.
  intros CT h active stack incoming.
  set (seeds := Union Loc incoming
    (phase_frame_capability_set CT h active)).
  set (closed := staged_frame_closure CT h active seeds).
  assert (Hseed_closed : Included Loc
      (Union Loc closed (phase_frame_capability_set CT h active)) closed).
  { intros location Hlocation. inversion Hlocation; subst.
    - exact H.
    - unfold closed. eapply staged_frame_closure_contains.
      unfold seeds. right. exact H. }
  assert (Hframe_absorb : Included Loc
      (staged_frame_closure CT h active
        (Union Loc closed (phase_frame_capability_set CT h active)))
      closed).
  { unfold closed at 2.
    eapply staged_frame_closure_monotone in Hseed_closed.
    intros location Hlocation.
    have Htwice := Hseed_closed location Hlocation.
    unfold closed in Htwice.
    exact (proj1 (staged_frame_closure_idempotent CT h active seeds)
      location Htwice). }
  destruct stack as [|boundary tail]; simpl.
  - exact Hframe_absorb.
  - eapply phased_live_color_set_from_monotone.
    eapply staged_return_closure_monotone.
    exact Hframe_absorb.
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

Lemma layered_color_connected_trans :
  forall CT h active stack left middle right,
    layered_color_connected CT h active stack left middle ->
    layered_color_connected CT h active stack middle right ->
    layered_color_connected CT h active stack left right.
Proof. intros. eapply rt_trans; eauto. Qed.

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

Lemma mutable_reachable_is_reverse_layered_color_connected :
  forall CT h active stack left right,
    mutable_reachable CT h left right ->
    layered_color_connected CT h active stack right left.
Proof.
  intros. eapply layered_color_connected_sym.
  eapply mutable_reachable_is_layered_color_connected; eauto.
Qed.

Lemma layered_color_connected_is_potential_connected :
  forall CT h active stack left right,
    layered_color_connected CT h active stack left right ->
    potential_connected CT h active stack left right.
Proof.
  intros CT h active stack left right Hconnected.
  induction Hconnected.
  - destruct H as [Hmutable | [Hframe | Hreturn]].
    + apply rt_step. left.
      destruct Hmutable as [Hforward | Hbackward].
      * left. constructor. exact Hforward.
      * right. exact Hbackward.
    + apply rt_step. right. left. exact Hframe.
    + apply rt_step. right. right. exact Hreturn.
  - apply rt_refl.
  - eapply rt_trans; eauto.
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

Lemma retained_reachable_is_authority_color_connected :
  forall CT h active stack left right,
    retained_mut_reachable CT h left right ->
    authority_color_connected CT h active stack left right.
Proof.
  intros CT h active stack left right Hreachable.
  induction Hreachable.
  - apply rt_refl.
  - eapply rt_trans; [exact IHHreachable|].
    apply rt_step. left. left. exact H.
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

Lemma live_frame_owned_locations_boundary_connected :
  forall CT h active stack frame left right,
    live_frame_member active stack frame ->
    frame_owned_location CT h frame left ->
    frame_owned_location CT h frame right ->
    boundary_connected CT h active stack left right.
Proof.
  intros CT h active stack frame left right Hlive Hleft Hright.
  apply rt_step. right. exists frame. repeat split; assumption.
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

Lemma layered_color_connected_preserves_runtime_mutability :
  forall CT h active stack left right runtime_q,
    live_frames_wf CT h active stack ->
    wf_heap CT h ->
    layered_color_connected CT h active stack left right ->
    r_muttype h left = Some runtime_q ->
    r_muttype h right = Some runtime_q.
Proof.
  intros CT h active stack left right runtime_q Hframes Hheap Hconnected.
  eapply potential_connected_preserves_runtime_mutability; eauto.
  eapply layered_color_connected_is_potential_connected; eauto.
Qed.

Lemma authority_color_connected_preserves_runtime_mutability :
  forall CT h active stack left right runtime_q,
    live_frames_wf CT h active stack ->
    wf_heap CT h ->
    authority_color_connected CT h active stack left right ->
    r_muttype h left = Some runtime_q ->
    r_muttype h right = Some runtime_q.
Proof.
  intros CT h active stack left right runtime_q Hframes Hheap Hconnected.
  eapply potential_connected_preserves_runtime_mutability; eauto.
  eapply authority_color_connected_is_potential_connected; eauto.
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

Lemma ownership_frame_edge_preserves_runtime_mutability :
  forall CT h active stack left right,
    live_frames_wf CT h active stack ->
    live_frames_authority_sound h active stack ->
    ownership_frame_edge CT h active stack left right ->
    r_muttype h left = Some Mut_r /\
    r_muttype h right = Some Mut_r.
Proof.
  intros CT h active stack left right Hframes Hsound
    [frame [Hlive [Hleft Hright]]].
  assert (Hleft_live :
      In Loc (live_capability_set CT h active stack) left).
  { destruct Hleft as [root [Hroot Hreach]].
    exists root. split; [|exact Hreach].
    inversion Hlive; subst.
    - left. exact Hroot.
    - right. exists boundary. split; assumption. }
  assert (Hright_live :
      In Loc (live_capability_set CT h active stack) right).
  { destruct Hright as [root [Hroot Hreach]].
    exists root. split; [|exact Hreach].
    inversion Hlive; subst.
    - left. exact Hroot.
    - right. exists boundary. split; assumption. }
  split;
    eapply live_capability_members_runtime_mutable; eauto.
Qed.

Lemma retained_reachable_preserves_runtime_context :
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
    + assert (runtime_q = Mut_r) by congruence.
      subst runtime_q.
      eapply retained_edge_preserves_runtime_mutability; eauto.
Qed.

Lemma retained_reachable_reflects_runtime_context :
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

Lemma retained_reachable_without_mutable_runtime_is_mutable_reachable :
  forall CT h root target,
    wf_heap CT h ->
    r_muttype h root <> Some Mut_r ->
    retained_mut_reachable CT h root target ->
    mutable_reachable CT h root target.
Proof.
  intros CT h root target Hheap Hroot_not_mut Hreachable.
  induction Hreachable.
  - constructor.
  - eapply mr_step.
    + apply IHHreachable. exact Hroot_not_mut.
    + inversion H; subst.
      * exact H0.
      * exfalso. apply Hroot_not_mut.
        eapply retained_reachable_reflects_runtime_context; eauto.
Qed.

Lemma boundary_connected_preserves_runtime_mutability :
  forall CT h active stack left right runtime_q,
    live_frames_wf CT h active stack ->
    live_frames_authority_sound h active stack ->
    wf_heap CT h ->
    boundary_connected CT h active stack left right ->
    r_muttype h left = Some runtime_q ->
    r_muttype h right = Some runtime_q.
Proof.
  intros CT h active stack left right runtime_q Hframes Hsound Hheap
    Hconnected.
  induction Hconnected; intros Hruntime.
  - destruct H as [Hpotential | Hownership].
    + eapply potential_adjacent_preserves_runtime_mutability; eauto.
    + destruct (ownership_frame_edge_preserves_runtime_mutability CT h
        active stack x y Hframes Hsound Hownership) as [Hx Hy].
      assert (runtime_q = Mut_r) by congruence. subst runtime_q. exact Hy.
  - exact Hruntime.
  - apply IHHconnected2. apply IHHconnected1. exact Hruntime.
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

Lemma layered_colors_imply_live_frame_colors :
  forall CT h M Z active stack frame,
    layered_colors_separated CT h M Z active stack ->
    live_frame_member active stack frame ->
    watched_frame_colors CT h M Z frame.
Proof.
  intros CT h M Z active stack frame Hlayers Hlive capability_root zone_root
    Hcapability_root
    [capability [Hcapability Hcapability_connected]] Hzone_root
    [protected [Hprotected Hzone_connected]].
  apply (Hlayers capability protected Hcapability Hprotected).
  eapply layered_color_connected_trans.
  - eapply mutable_connected_is_layered_color_connected.
    eapply mutable_connected_sym. exact Hcapability_connected.
  - eapply layered_color_connected_trans.
    + apply rt_step. right. left.
      exists frame. split; [exact Hlive|].
      split; [exact Hcapability_root|exact Hzone_root].
    + eapply mutable_connected_is_layered_color_connected.
      exact Hzone_connected.
Qed.

Lemma authority_colors_imply_component_colors :
  forall CT h M Z active stack,
    authority_colors_separated CT h M Z active stack ->
    component_colors_separated CT h M Z.
Proof.
  intros CT h M Z active stack Hcolors capability protected Hcapability
    Hprotected Hconnected.
  apply (Hcolors capability protected Hcapability Hprotected).
  eapply mutable_connected_is_authority_color_connected; eauto.
Qed.

Lemma authority_colors_imply_live_frame_colors :
  forall CT h M Z active stack frame,
    authority_colors_separated CT h M Z active stack ->
    live_frame_member active stack frame ->
    watched_frame_colors CT h M Z frame.
Proof.
  intros CT h M Z active stack frame Hcolors Hlive capability_root zone_root
    Hcapability_root
    [capability [Hcapability Hcapability_connected]] Hzone_root
    [protected [Hprotected Hzone_connected]].
  apply (Hcolors capability protected Hcapability Hprotected).
  eapply authority_color_connected_trans.
  - eapply mutable_connected_is_authority_color_connected.
    eapply mutable_connected_sym. exact Hcapability_connected.
  - eapply authority_color_connected_trans.
    + apply rt_step. right.
      exists frame. split; [exact Hlive|].
      split; [exact Hcapability_root|exact Hzone_root].
    + eapply mutable_connected_is_authority_color_connected.
      exact Hzone_connected.
Qed.

Lemma authority_colors_imply_active_colors :
  forall CT h M Z active stack,
    authority_colors_separated CT h M Z active stack ->
    watched_frame_colors CT h M Z active.
Proof.
  intros. eapply authority_colors_imply_live_frame_colors; eauto.
  constructor.
Qed.

Lemma potential_colors_imply_layered_colors :
  forall CT h M Z active stack,
    potential_colors_separated CT h M Z active stack ->
    layered_colors_separated CT h M Z active stack.
Proof.
  intros CT h M Z active stack Hpotential capability protected
    Hcapability Hprotected Hconnected.
  apply (Hpotential capability protected Hcapability Hprotected).
  assert (Hmap : forall left right,
    layered_color_connected CT h active stack left right ->
    potential_connected CT h active stack left right).
  { intros left right Hlayers. induction Hlayers.
    - destruct H as [Hmutable | [Hframe | Hreturn]].
      + eapply mutable_connected_is_potential_connected.
        apply rt_step. exact Hmutable.
      + apply rt_step. right. left. exact Hframe.
      + apply rt_step. right. right. exact Hreturn.
    - apply rt_refl.
    - eapply potential_connected_trans; eauto. }
  exact (Hmap capability protected Hconnected).
Qed.

Lemma potential_colors_imply_authority_colors :
  forall CT h M Z active stack,
    potential_colors_separated CT h M Z active stack ->
    authority_colors_separated CT h M Z active stack.
Proof.
  intros CT h M Z active stack Hpotential capability protected Hcapability
    Hprotected Hconnected.
  apply (Hpotential capability protected Hcapability Hprotected).
  eapply authority_color_connected_is_potential_connected; eauto.
Qed.

Lemma potential_history_implies_layered_history :
  forall CT P Z cutoff active stack h,
    potential_live_history_state CT P Z cutoff active stack h ->
    layered_live_history_state CT P Z cutoff active stack h.
Proof.
  intros CT P Z cutoff active stack h
    [Hlive [Hpotential Hcutoffs]].
  split; [exact Hlive|].
  split.
  - eapply potential_colors_imply_layered_colors; eauto.
  - exact Hcutoffs.
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

Lemma staged_frame_closure_after_descent_included :
  forall CT h authority old_senv old_renv new_senv new_renv old_seeds
    new_seeds,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc new_seeds old_seeds ->
    Included Loc
      (staged_frame_closure CT h
        (mk_watched_frame authority new_senv new_renv) new_seeds)
      (staged_frame_closure CT h
        (mk_watched_frame authority old_senv old_renv) old_seeds).
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv old_seeds
    new_seeds Hdescend Hincluded location [seed [Hseed Hconnected]].
  exists seed. split.
  - apply Hincluded. exact Hseed.
  - eapply staged_frame_connected_after_descent_reflects; eauto.
Qed.

Lemma staged_return_root_after_callee_descent_has_representative :
  forall CT h authority old_senv old_renv new_senv new_renv boundary root,
    wf_r_config CT old_senv old_renv h ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    staged_return_root
      (mk_watched_frame authority new_senv new_renv) boundary root ->
    exists representative,
      staged_return_root
        (mk_watched_frame authority old_senv old_renv) boundary
        representative /\
      mutable_connected CT h representative root /\
      r_muttype h representative = r_muttype h root.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv boundary root
    Hwf Hdescend [Hcallee | Hcaller].
  - destruct (Hdescend root Hcallee) as
      [old_root [Hold_root Hreachable]].
    exists old_root. split; [left; exact Hold_root|].
    split.
    + eapply mutable_reachable_connected; eauto.
    + destruct (typed_rdm_root_has_runtime_context CT old_senv old_renv h
        old_root Hwf Hold_root) as [runtime_q Hold_runtime].
      have Hroot_runtime := mutable_reachable_preserves_runtime_mutability
        CT h old_root root runtime_q (proj1 (proj2 Hwf)) Hreachable
        Hold_runtime.
      rewrite Hold_runtime. rewrite Hroot_runtime. reflexivity.
  - exists root. split; [right; exact Hcaller|].
    split; [apply mutable_connected_refl|reflexivity].
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

Lemma frozen_caller_powered_retained_forward :
  forall CT h frame left right,
    retained_mut_reachable CT h left right ->
    frozen_caller_authority_connected CT h frame
      (FlowPowered, left) (FlowPowered, right).
Proof.
  intros CT h frame left right Hreachable. induction Hreachable.
  - apply rt_refl.
  - eapply rt_trans; [exact IHHreachable|].
    apply rt_step. apply frozen_caller_retained. exact H.
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

Lemma frozen_callee_side_prospective_components_after_assignment :
  forall CT authority sGamma mt rGamma h snapshots stack x expression old
    value,
    wf_r_config CT sGamma rGamma h ->
    authority_context_sound h rGamma authority ->
    stmt_typing CT sGamma mt (SVarAss x expression) sGamma ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma x = Some old ->
    eval_expr CT rGamma h expression value OK rGamma h ->
    frozen_callee_side_prospective_components_after_boundaries CT h
      (mk_watched_frame authority sGamma rGamma) snapshots stack ->
    frozen_callee_side_prospective_components_after_boundaries CT h
      (mk_watched_frame authority sGamma
        (update_r_env_value rGamma x value))
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority sGamma
          (update_r_env_value rGamma x value)) snapshots) stack.
Proof.
  intros CT authority sGamma mt rGamma h snapshots stack x expression old
    value Hwf Hsound Htyping Hscope Hvalue Heval Hold.
  have Hdescend := rdm_roots_descend_after_assignment CT sGamma mt rGamma h
    x expression old value Hwf Htyping Hscope Hvalue Heval.
  have Howned : Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame authority sGamma
          (update_r_env_value rGamma x value)))
      (phase_frame_capability_set CT h
        (mk_watched_frame authority sGamma rGamma)).
  { intros location Hlocation.
    apply frame_owned_location_iff_active_live.
    eapply assignment_live_reachability_is_old with
      (mt := mt) (x := x) (e := expression) (old := old) (value := value)
      (stack := []); eauto.
    apply frame_owned_location_iff_active_live. exact Hlocation. }
  eapply frozen_callee_side_prospective_components_after_active_descent;
    eauto.
Qed.

Lemma frozen_callee_side_prospective_components_after_local :
  forall CT authority sGamma mt rGamma h snapshots stack T x sGamma',
    wf_r_config CT sGamma rGamma h ->
    authority_context_sound h rGamma authority ->
    stmt_typing CT sGamma mt (SLocal T x) sGamma' ->
    runtime_getVal rGamma x = None ->
    frozen_callee_side_prospective_components_after_boundaries CT h
      (mk_watched_frame authority sGamma rGamma) snapshots stack ->
    frozen_callee_side_prospective_components_after_boundaries CT h
      (mk_watched_frame authority sGamma'
        (set_vars rGamma (vars rGamma ++ [Null_a])))
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority sGamma'
          (set_vars rGamma (vars rGamma ++ [Null_a]))) snapshots) stack.
Proof.
  intros CT authority sGamma mt rGamma h snapshots stack T x sGamma' Hwf
    Hsound Htyping Hnone Hold.
  have Hdescend := rdm_roots_descend_after_local CT sGamma mt rGamma h T x
    sGamma' Hwf Htyping Hnone.
  have Howned : Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame authority sGamma'
          (set_vars rGamma (vars rGamma ++ [Null_a]))))
      (phase_frame_capability_set CT h
        (mk_watched_frame authority sGamma rGamma)).
  { intros location Hlocation.
    apply frame_owned_location_iff_active_live.
    eapply local_live_reachability_is_old with (stack := []); eauto.
    apply frame_owned_location_iff_active_live. exact Hlocation. }
  eapply frozen_callee_side_prospective_components_after_active_descent;
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

Lemma frozen_caller_snapshots_independently_separated_after_active_descent :
  forall CT h authority old_senv old_renv new_senv new_renv snapshots,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame authority new_senv new_renv))
      (phase_frame_capability_set CT h
        (mk_watched_frame authority old_senv old_renv)) ->
    frozen_caller_snapshots_closed CT h
      (mk_watched_frame authority old_senv old_renv) snapshots ->
    frozen_caller_snapshots_independently_separated CT h
      (mk_watched_frame authority old_senv old_renv) snapshots ->
    frozen_caller_snapshots_independently_separated CT h
      (mk_watched_frame authority new_senv new_renv)
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) snapshots).
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv snapshots
    Hdescend Howned Hclosed Hseparated new_snapshot caller_mode active_mode
    location Hnew Hcaller_mode Hactive_mode Hcaller_color Hactive_color.
  have Hsnapshots :=
    advance_frozen_caller_snapshots_after_descent_included CT h authority
      old_senv old_renv new_senv new_renv snapshots Hdescend Hclosed.
  destruct (Hsnapshots new_snapshot Hnew) as
    [old_snapshot [Hold_snapshot Hcolors]].
  have Hactive := executing_authority_colors_after_active_descent_included CT
    h authority old_senv old_renv new_senv new_renv
    (Empty_set authority_flow_state) Hdescend Howned.
  exact (Hseparated old_snapshot caller_mode active_mode location
    Hold_snapshot Hcaller_mode Hactive_mode
    (Hcolors (caller_mode, location) Hcaller_color)
    (Hactive (active_mode, location) Hactive_color)).
Qed.

Lemma frozen_caller_snapshots_active_resume_origins_after_active_descent :
  forall CT h authority old_senv old_renv new_senv new_renv snapshots,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame authority new_senv new_renv))
      (phase_frame_capability_set CT h
        (mk_watched_frame authority old_senv old_renv)) ->
    frozen_caller_snapshots_closed CT h
      (mk_watched_frame authority old_senv old_renv) snapshots ->
    frozen_caller_snapshots_active_resume_origins CT h
      (mk_watched_frame authority old_senv old_renv) snapshots ->
    frozen_caller_snapshots_active_resume_origins CT h
      (mk_watched_frame authority new_senv new_renv)
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) snapshots).
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv snapshots
    Hdescend Howned Hclosed Horigins new_snapshot snapshot_mode active_mode
    location Hnew Hsnapshot_mode Hactive_mode Hsnapshot_color Htrigger.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot. simpl in *.
  have Hold_snapshot_color : In authority_flow_state
      old_snapshot.(frozen_snapshot_current_colors)
      (snapshot_mode, location).
  { eapply Hclosed; [exact Hold|].
    destruct Hsnapshot_color as [seed [Hseed Hpath]].
    exists seed. split; [exact Hseed|].
    eapply frozen_caller_connected_after_descent_reflects; eauto. }
  destruct Htrigger as [Hactive_color | Hnew_rdm].
  - have Hactive := executing_authority_colors_after_active_descent_included CT
      h authority old_senv old_renv new_senv new_renv
      (Empty_set authority_flow_state) Hdescend Howned.
    destruct (Horigins old_snapshot snapshot_mode active_mode location Hold
      Hsnapshot_mode Hactive_mode Hold_snapshot_color
      (or_introl (Hactive (active_mode, location) Hactive_color))) as
      [root_mode [root [Hroot_mode [Hroot_color Hroot]]]].
    exists root_mode, root. split; [exact Hroot_mode|]. split.
    + apply frozen_caller_authority_closure_contains. exact Hroot_color.
    + exact Hroot.
  - destruct (Hdescend location Hnew_rdm) as
      [old_root [Hold_rdm Hroot_reachable]].
    have Hold_root_color : In authority_flow_state
        old_snapshot.(frozen_snapshot_current_colors)
        (FlowProspective, old_root).
    { eapply Hclosed; [exact Hold|]. exists (snapshot_mode, location).
      split; [exact Hold_snapshot_color|].
      destruct Hsnapshot_mode as [-> | ->].
      - eapply frozen_caller_powered_mutable_reverse. exact Hroot_reachable.
      - eapply frozen_caller_prospective_mutable_reverse.
        exact Hroot_reachable. }
    destruct (Horigins old_snapshot FlowProspective active_mode old_root Hold
      (or_intror eq_refl) Hactive_mode Hold_root_color
      (or_intror Hold_rdm)) as
      [root_mode [root [Hroot_mode [Hroot_color Hroot]]]].
    exists root_mode, root. split; [exact Hroot_mode|]. split.
    + apply frozen_caller_authority_closure_contains. exact Hroot_color.
    + exact Hroot.
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

Lemma principled_separated_frozen_mutable_rdm_after_active_descent :
  forall CT P Z cutoff authority old_senv old_renv new_senv new_renv
    stack incoming snapshots h,
    principled_separated_frozen_mutable_rdm_history_state CT P Z cutoff
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
    live_mutable_rdm_components_after_cutoff CT h cutoff
      (mk_watched_frame authority new_senv new_renv) stack ->
    principled_separated_frozen_mutable_rdm_history_state CT P Z cutoff
      (mk_watched_frame authority new_senv new_renv) stack incoming
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) snapshots) h.
Proof.
  intros CT P Z cutoff authority old_senv old_renv new_senv new_renv
    stack incoming snapshots h [Hfrozen [Hcomponents Hseparated]] Hpost
    Hdescend Howned Hpost_components.
  split.
  - eapply principled_frozen_authority_after_active_descent; eauto.
  - split; [exact Hpost_components|].
    eapply frozen_caller_snapshots_independently_separated_after_active_descent;
      eauto.
    exact (proj1 (proj2 (proj2 (proj2 Hfrozen)))).
Qed.

Lemma principled_root_scoped_frozen_mutable_rdm_after_active_descent :
  forall CT P Z cutoff authority old_senv old_renv new_senv new_renv
    stack incoming snapshots h,
    principled_root_scoped_frozen_mutable_rdm_history_state CT P Z cutoff
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
    live_mutable_rdm_components_after_cutoff CT h cutoff
      (mk_watched_frame authority new_senv new_renv) stack ->
    principled_root_scoped_frozen_mutable_rdm_history_state CT P Z cutoff
      (mk_watched_frame authority new_senv new_renv) stack incoming
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) snapshots) h.
Proof.
  intros CT P Z cutoff authority old_senv old_renv new_senv new_renv
    stack incoming snapshots h [Hfrozen [Hcomponents Horigins]] Hpost
    Hdescend Howned Hpost_components.
  split.
  - eapply principled_frozen_authority_after_active_descent; eauto.
  - split; [exact Hpost_components|].
    eapply frozen_caller_snapshots_active_resume_origins_after_active_descent;
      eauto.
    exact (proj1 (proj2 (proj2 (proj2 Hfrozen)))).
Qed.

Lemma pending_caller_colors_after_active_descent_included :
  forall CT h authority old_senv old_renv new_senv new_renv above
    caller_colors,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (live_capability_set CT h
        (mk_watched_frame authority new_senv new_renv) [])
      (live_capability_set CT h
        (mk_watched_frame authority old_senv old_renv) []) ->
    Included authority_flow_state
      (pending_caller_colors_through_prefix CT h
        (mk_watched_frame authority new_senv new_renv) above caller_colors)
      (pending_caller_colors_through_prefix CT h
        (mk_watched_frame authority old_senv old_renv) above caller_colors).
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv above
    caller_colors Hdescend Hcapabilities state Hstate.
  assert (Howned : Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame authority new_senv new_renv))
      (phase_frame_capability_set CT h
        (mk_watched_frame authority old_senv old_renv))).
  { intros location Hlocation.
    apply frame_owned_location_iff_active_live.
    apply Hcapabilities.
    apply frame_owned_location_iff_active_live. exact Hlocation. }
  destruct above as [|head tail]; simpl in *;
    eapply phased_authority_frame_closure_after_descent_included;
    eauto; intros seed Hseed; exact Hseed.
Qed.

Lemma pending_call_phased_authority_after_active_descent :
  forall CT h authority old_senv old_renv new_senv new_renv stack
    tracked_depth,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (live_capability_set CT h
        (mk_watched_frame authority new_senv new_renv) [])
      (live_capability_set CT h
        (mk_watched_frame authority old_senv old_renv) []) ->
    pending_call_phased_authority_separated CT h
      (mk_watched_frame authority old_senv old_renv) stack tracked_depth ->
    pending_call_phased_authority_separated CT h
      (mk_watched_frame authority new_senv new_renv) stack tracked_depth.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv stack
    tracked_depth Hdescend Hcapabilities Hpending boundary above below owned
    mode Hpartition Htracked Hfree Howned Hmode Hcolored.
  have Hpartition_old :
      live_call_partition
        (mk_watched_frame authority old_senv old_renv)
        stack boundary above below.
  { eapply live_call_partition_change_active. exact Hpartition. }
  have Howned_old :
      In Loc
        (pending_owned_authority_set CT h
          (mk_watched_frame authority old_senv old_renv) above) owned.
  { eapply pending_owned_authority_after_active_descent_included; eauto. }
  apply (Hpending boundary above below owned mode Hpartition_old Htracked
    Hfree Howned_old Hmode).
  unfold pending_boundary_caller_color_set in *.
  eapply pending_caller_colors_after_active_descent_included; eauto.
Qed.

Lemma phased_frame_closure_dangerous_rdm_join :
  forall CT h frame seeds mode left right,
    authority_mode_dangerous mode ->
    In authority_flow_state
      (phased_authority_frame_closure CT h frame seeds) (mode, left) ->
    typed_root RDM frame.(frame_senv) frame.(frame_renv) left ->
    typed_root RDM frame.(frame_senv) frame.(frame_renv) right ->
    In authority_flow_state
      (phased_authority_frame_closure CT h frame seeds)
      (FlowProspective, right).
Proof.
  intros CT h frame seeds mode left right Hmode
    [seed [Hseed Hconnected]] Hleft Hright.
  exists seed. split; [exact Hseed|].
  eapply rt_trans; [exact Hconnected|].
  apply rt_step.
  destruct Hmode as [-> | ->].
  - eapply phased_authority_powered_frame_join; eauto.
  - eapply phased_authority_prospective_frame_join; eauto.
Qed.

Lemma phased_frame_closure_dangerous_retained_reachable :
  forall CT h frame seeds mode left right,
    authority_mode_dangerous mode ->
    In authority_flow_state
      (phased_authority_frame_closure CT h frame seeds) (mode, left) ->
    retained_mut_reachable CT h left right ->
    In authority_flow_state
      (phased_authority_frame_closure CT h frame seeds) (mode, right).
Proof.
  intros CT h frame seeds mode left right Hmode
    [seed [Hseed Hconnected]] Hreachable.
  exists seed. split; [exact Hseed|].
  eapply rt_trans; [exact Hconnected|].
  clear Hconnected Hseed seed seeds.
  induction Hreachable.
  - apply rt_refl.
  - eapply rt_trans; [exact IHHreachable|].
    apply rt_step. destruct Hmode as [-> | ->].
    + apply phased_authority_retained. exact H.
    + apply phased_authority_prospective_retained. exact H.
Qed.

Lemma pending_boundary_caller_color_dangerous_rdm_join :
  forall CT h active boundary above below mode left right,
    authority_mode_dangerous mode ->
    In authority_flow_state
      (pending_boundary_caller_color_set CT h active boundary above below)
      (mode, left) ->
    effective_frame_rdm_root active left ->
    effective_frame_rdm_root active right ->
    In authority_flow_state
      (pending_boundary_caller_color_set CT h active boundary above below)
      (FlowProspective, right).
Proof.
  intros CT h active boundary above below mode left right Hmode Hcolor
    Hleft Hright.
  unfold pending_boundary_caller_color_set in *.
  destruct above as [|head tail]; simpl in *;
    eapply phased_frame_closure_dangerous_rdm_join; eauto.
Qed.

Lemma pending_boundary_caller_color_rdm_join_retained :
  forall CT h active boundary above below mode left right target,
    authority_mode_dangerous mode ->
    In authority_flow_state
      (pending_boundary_caller_color_set CT h active boundary above below)
      (mode, left) ->
    effective_frame_rdm_root active left ->
    effective_frame_rdm_root active right ->
    retained_mut_reachable CT h right target ->
    In authority_flow_state
      (pending_boundary_caller_color_set CT h active boundary above below)
      (FlowProspective, target).
Proof.
  intros CT h active boundary above below mode left right target
    Hmode Hcolor Hleft Hright Hreachable.
  have Hjoined := pending_boundary_caller_color_dangerous_rdm_join CT h
    active boundary above below mode left right Hmode Hcolor Hleft
    Hright.
  unfold pending_boundary_caller_color_set in *.
  destruct above as [|head tail]; simpl in *.
  - eapply phased_frame_closure_dangerous_retained_reachable;
      [right; reflexivity|exact Hjoined|exact Hreachable].
  - eapply phased_frame_closure_dangerous_retained_reachable;
      [right; reflexivity|exact Hjoined|exact Hreachable].
Qed.

Lemma callee_rdm_root_after_descent_has_runtime_representative :
  forall CT h old_senv old_renv new_senv new_renv root,
    wf_r_config CT old_senv old_renv h ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    typed_root RDM new_senv new_renv root ->
    exists representative,
      typed_root RDM old_senv old_renv representative /\
      mutable_connected CT h representative root /\
      r_muttype h representative = r_muttype h root.
Proof.
  intros CT h old_senv old_renv new_senv new_renv root Hwf Hdescend Hroot.
  destruct (Hdescend root Hroot) as
    [representative [Hrepresentative Hreachable]].
  exists representative. split; [exact Hrepresentative|]. split.
  - eapply mutable_reachable_connected. exact Hreachable.
  - destruct (typed_rdm_root_has_runtime_context CT old_senv old_renv h
      representative Hwf Hrepresentative) as [runtime_q Hrep_runtime].
    have Hroot_runtime := mutable_reachable_preserves_runtime_mutability CT h
      representative root runtime_q (proj1 (proj2 Hwf)) Hreachable
      Hrep_runtime.
    rewrite Hrep_runtime. rewrite Hroot_runtime. reflexivity.
Qed.

Lemma phased_authority_nontrivial_return_after_descent :
  forall CT h authority old_senv old_renv new_senv new_renv boundary
    old_seeds source_mode source target,
    wf_r_config CT old_senv old_renv h ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    boundary.(boundary_receiver_view) = RDM ->
    boundary.(boundary_callee_return_qualifier) = RDM ->
    r_muttype h source = r_muttype h target ->
    staged_return_root
      (mk_watched_frame authority new_senv new_renv) boundary source ->
    staged_return_root
      (mk_watched_frame authority new_senv new_renv) boundary target ->
    In authority_flow_state
      (phased_authority_frame_closure CT h
        (mk_watched_frame authority old_senv old_renv) old_seeds)
      (source_mode, source) ->
    In authority_flow_state
      (phased_authority_frame_closure CT h boundary.(boundary_caller)
        (phased_authority_return_closure h
          (mk_watched_frame authority old_senv old_renv) boundary
          (demote_authority_set
            (phased_authority_frame_closure CT h
              (mk_watched_frame authority old_senv old_renv) old_seeds))))
      (FlowNeutral, target).
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv boundary
    old_seeds source_mode source target Hwf Hdescend Hview Hreturn Hruntime
    [Hsource_callee | Hsource_caller]
    [Htarget_callee | Htarget_caller] Hsource_colored.
  all: try destruct
    (callee_rdm_root_after_descent_has_runtime_representative CT h
      old_senv old_renv new_senv new_renv source Hwf Hdescend
      Hsource_callee) as
      [source_rep [Hsource_rep [Hsource_component Hsource_runtime]]].
  all: try destruct
    (callee_rdm_root_after_descent_has_runtime_representative CT h
      old_senv old_renv new_senv new_renv target Hwf Hdescend
      Htarget_callee) as
      [target_rep [Htarget_rep [Htarget_component Htarget_runtime]]].
  all: try assert (Hsource_neutral : In authority_flow_state
      (phased_authority_frame_closure CT h
        (mk_watched_frame authority old_senv old_renv) old_seeds)
      (FlowNeutral, source_rep)).
  all: try (
    eapply phased_authority_frame_closure_extend;
    [exact Hsource_colored|]; destruct source_mode;
    [eapply phased_authority_powered_to_neutral_mutable_connected |
     eapply phased_authority_prospective_to_neutral_mutable_connected |
     eapply phased_authority_neutral_mutable_connected];
    eapply mutable_connected_sym; exact Hsource_component).
  - have Htarget_rep_colored : In authority_flow_state
        (phased_authority_frame_closure CT h
          (mk_watched_frame authority old_senv old_renv) old_seeds)
        (FlowNeutral, target_rep).
    { eapply phased_authority_frame_closure_extend; [exact Hsource_neutral|].
      apply rt_step. eapply phased_authority_neutral_frame_join.
      - exact Hsource_rep.
      - exact Htarget_rep. }
    eapply phased_authority_frame_closure_extend.
    + eapply phased_authority_frame_closure_contains.
      eapply phased_authority_return_closure_contains.
      exists FlowNeutral, target_rep. split;
        [exact Htarget_rep_colored|reflexivity].
    + eapply phased_authority_neutral_mutable_connected.
      exact Htarget_component.
  - have Hrep_runtime : r_muttype h source_rep = r_muttype h target.
    { rewrite Hsource_runtime. exact Hruntime. }
    have Hreturned : In authority_flow_state
        (phased_authority_return_closure h
          (mk_watched_frame authority old_senv old_renv) boundary
          (demote_authority_set
            (phased_authority_frame_closure CT h
              (mk_watched_frame authority old_senv old_renv) old_seeds)))
        (FlowNeutral, target).
    { eapply phased_authority_return_closure_extend.
      - eapply phased_authority_return_closure_contains.
        exists FlowNeutral, source_rep. split;
          [exact Hsource_neutral|reflexivity].
      - apply rt_step. apply phased_authority_neutral_return.
        repeat split; try assumption. left. split.
        + exact Hsource_rep.
        + exact Htarget_caller. }
    eapply phased_authority_frame_closure_contains. exact Hreturned.
  - have Hrep_runtime : r_muttype h source = r_muttype h target_rep.
    { rewrite Htarget_runtime. exact Hruntime. }
    have Hsource_neutral : In authority_flow_state
        (phased_authority_frame_closure CT h
          (mk_watched_frame authority old_senv old_renv) old_seeds)
        (FlowNeutral, source).
    { eapply phased_authority_frame_closure_extend;
        [exact Hsource_colored|].
      destruct source_mode.
      - apply rt_step. apply phased_authority_forget.
      - apply rt_step. apply phased_authority_prospective_forget.
      - apply rt_refl. }
    have Hreturned : In authority_flow_state
        (phased_authority_return_closure h
          (mk_watched_frame authority old_senv old_renv) boundary
          (demote_authority_set
            (phased_authority_frame_closure CT h
              (mk_watched_frame authority old_senv old_renv) old_seeds)))
        (FlowNeutral, target_rep).
    { eapply phased_authority_return_closure_extend.
      - eapply phased_authority_return_closure_contains.
        exists FlowNeutral, source. split;
          [exact Hsource_neutral|reflexivity].
      - apply rt_step. apply phased_authority_neutral_return.
        repeat split; try assumption. right. split.
        + exact Hsource_caller.
        + exact Htarget_rep. }
    eapply phased_authority_frame_closure_extend.
    + eapply phased_authority_frame_closure_contains. exact Hreturned.
    + eapply phased_authority_neutral_mutable_connected.
      exact Htarget_component.
  - have Hsource_neutral : In authority_flow_state
        (phased_authority_frame_closure CT h
          (mk_watched_frame authority old_senv old_renv) old_seeds)
        (FlowNeutral, source).
    { eapply phased_authority_frame_closure_extend;
        [exact Hsource_colored|].
      destruct source_mode.
      - apply rt_step. apply phased_authority_forget.
      - apply rt_step. apply phased_authority_prospective_forget.
      - apply rt_refl. }
    have Hreturned : In authority_flow_state
        (phased_authority_return_closure h
          (mk_watched_frame authority old_senv old_renv) boundary
          (demote_authority_set
            (phased_authority_frame_closure CT h
              (mk_watched_frame authority old_senv old_renv) old_seeds)))
        (FlowNeutral, source).
    { eapply phased_authority_return_closure_contains.
      exists FlowNeutral, source. split;
        [exact Hsource_neutral|reflexivity]. }
    eapply phased_authority_frame_closure_extend.
    + eapply phased_authority_frame_closure_contains. exact Hreturned.
    + apply rt_step. eapply phased_authority_neutral_frame_join; eauto.
  all: try assumption.
  all: try (split; assumption).
Qed.

Lemma phased_authority_call_phase_after_callee_descent_included :
  forall CT h authority old_senv old_renv new_senv new_renv boundary
    old_seeds new_seeds,
    wf_r_config CT old_senv old_renv h ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame authority new_senv new_renv))
      (phase_frame_capability_set CT h
        (mk_watched_frame authority old_senv old_renv)) ->
    Included authority_flow_state new_seeds old_seeds ->
    Included authority_flow_state
      (phased_authority_return_closure h
        (mk_watched_frame authority new_senv new_renv) boundary
        (demote_authority_set
          (phased_authority_frame_closure CT h
            (mk_watched_frame authority new_senv new_renv) new_seeds)))
      (phased_authority_frame_closure CT h boundary.(boundary_caller)
        (phased_authority_return_closure h
          (mk_watched_frame authority old_senv old_renv) boundary
          (demote_authority_set
            (phased_authority_frame_closure CT h
              (mk_watched_frame authority old_senv old_renv) old_seeds)))).
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv boundary
    old_seeds new_seeds Hwf Hdescend Howned Hseeds target
    [source [Hsource Hreturn_path]].
  destruct Hsource as
    [original_mode [source_location [Hsource_original Heq]]].
  subst source.
  have Hsource_old : In authority_flow_state
      (phased_authority_frame_closure CT h
        (mk_watched_frame authority old_senv old_renv) old_seeds)
      (original_mode, source_location).
  { eapply phased_authority_frame_closure_after_descent_included; eauto. }
  have Hsource_old_demoted : In authority_flow_state
      (demote_authority_set
        (phased_authority_frame_closure CT h
          (mk_watched_frame authority old_senv old_renv) old_seeds))
      (FlowNeutral, source_location).
  { exists original_mode, source_location. split;
      [exact Hsource_old|reflexivity]. }
  destruct (phased_authority_return_connected_normal_form h
    (mk_watched_frame authority new_senv new_renv) boundary
    (FlowNeutral, source_location) target Hreturn_path) as
    [Heq | [Htarget_neutral Hlocations]].
  - subst target. eapply phased_authority_frame_closure_contains.
    eapply phased_authority_return_closure_contains.
    exact Hsource_old_demoted.
  - destruct target as [target_mode target_location]. simpl in *.
    subst target_mode.
    destruct (staged_return_connected_classifies h
      (mk_watched_frame authority new_senv new_renv) boundary
      source_location target_location Hlocations) as [Heq | Hclass].
    + subst target_location.
      have Hneutral : In authority_flow_state
          (phased_authority_frame_closure CT h
            (mk_watched_frame authority old_senv old_renv) old_seeds)
          (FlowNeutral, source_location).
      { eapply phased_authority_frame_closure_extend;
          [exact Hsource_old|].
        destruct original_mode.
        - apply rt_step. apply phased_authority_forget.
        - apply rt_step. apply phased_authority_prospective_forget.
        - apply rt_refl. }
      eapply phased_authority_frame_closure_contains.
      eapply phased_authority_return_closure_contains.
      exists FlowNeutral, source_location. split;
        [exact Hneutral|reflexivity].
    + destruct Hclass as
        [Hview [Hcallee_return [Hruntime [Hsource_root Htarget_root]]]].
      eapply phased_authority_nontrivial_return_after_descent
        with (source_mode := original_mode); eauto.
Qed.

Lemma phased_authority_color_set_from_after_active_descent_included :
  forall CT h authority old_senv old_renv new_senv new_renv stack incoming,
    wf_r_config CT old_senv old_renv h ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (live_capability_set CT h
        (mk_watched_frame authority new_senv new_renv) [])
      (live_capability_set CT h
        (mk_watched_frame authority old_senv old_renv) []) ->
    Included authority_flow_state
      (phased_authority_color_set_from CT h
        (mk_watched_frame authority new_senv new_renv) stack incoming)
      (phased_authority_color_set_from CT h
        (mk_watched_frame authority old_senv old_renv) stack incoming).
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv stack incoming
    Hwf Hdescend Hcapabilities.
  set (old_frame := mk_watched_frame authority old_senv old_renv).
  set (new_frame := mk_watched_frame authority new_senv new_renv).
  assert (Howned : Included Loc
      (phase_frame_capability_set CT h new_frame)
      (phase_frame_capability_set CT h old_frame)).
  { intros location Hlocation.
    unfold phase_frame_capability_set in *.
    apply frame_owned_location_iff_active_live.
    apply Hcapabilities.
    apply frame_owned_location_iff_active_live. exact Hlocation. }
  assert (Hpowered : Included authority_flow_state
      (phased_frame_powered_seeds CT h new_frame)
      (phased_frame_powered_seeds CT h old_frame)).
  { intros state [location [Heq Hlocation]].
    exists location. split; [exact Heq|apply Howned; exact Hlocation]. }
  assert (Hseeds : Included authority_flow_state
      (Union authority_flow_state incoming
        (phased_frame_powered_seeds CT h new_frame))
      (Union authority_flow_state incoming
        (phased_frame_powered_seeds CT h old_frame))).
  { intros state Hstate. inversion Hstate; subst.
    - left. exact H.
    - right. apply Hpowered. exact H. }
  destruct stack as [|boundary tail]; simpl.
  - eapply phased_authority_frame_closure_after_descent_included; eauto.
  - set (new_return := phased_authority_return_closure h new_frame boundary
      (demote_authority_set
        (phased_authority_frame_closure CT h new_frame
          (Union authority_flow_state incoming
            (phased_frame_powered_seeds CT h new_frame))))).
    set (old_return := phased_authority_return_closure h old_frame boundary
      (demote_authority_set
        (phased_authority_frame_closure CT h old_frame
          (Union authority_flow_state incoming
            (phased_frame_powered_seeds CT h old_frame))))).
    assert (Hcall_phase : Included authority_flow_state new_return
      (phased_authority_frame_closure CT h boundary.(boundary_caller)
        old_return)).
    { unfold new_return, old_return, new_frame, old_frame.
      eapply phased_authority_call_phase_after_callee_descent_included;
        eauto. }
    assert (Hcall_phase_with_capabilities : Included authority_flow_state
      new_return
      (phased_authority_frame_closure CT h boundary.(boundary_caller)
        (Union authority_flow_state old_return
          (phased_frame_powered_seeds CT h
            boundary.(boundary_caller))))).
    { intros state Hstate.
      eapply phased_authority_frame_closure_monotone;
        [|apply Hcall_phase; exact Hstate].
      intros seed Hseed. left. exact Hseed. }
    intros state Hstate.
    inversion Hstate; subst.
    + left.
      eapply phased_authority_frame_closure_after_descent_included; eauto.
    + right.
      apply (phased_authority_color_set_from_absorbs_active_frame CT h
        boundary.(boundary_caller) tail old_return state).
      eapply phased_authority_color_set_from_monotone;
        [exact Hcall_phase_with_capabilities|exact H].
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

Lemma phased_authority_frame_connected_after_graph_reflection :
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
    phased_authority_frame_connected CT h' frame source target ->
    phased_authority_frame_connected CT h frame source target.
Proof.
  intros CT h h' frame source target Hretained Hmutable Howned Hconnected.
  induction Hconnected.
  - apply rt_step. eapply phased_authority_frame_step_after_graph_reflection;
      eauto.
  - apply rt_refl.
  - eapply rt_trans; eauto.
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

Lemma phased_authority_return_connected_after_graph_reflection :
  forall h h' callee boundary source target,
    (forall left right,
      staged_return_adjacent h' callee boundary left right ->
      staged_return_adjacent h callee boundary left right) ->
    phased_authority_return_connected h' callee boundary source target ->
    phased_authority_return_connected h callee boundary source target.
Proof.
  intros h h' callee boundary source target Hreturn Hconnected.
  induction Hconnected.
  - apply rt_step. eapply phased_authority_return_step_after_graph_reflection;
      eauto.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma phased_authority_color_set_from_after_graph_reflection :
  forall CT h h' active stack old_incoming new_incoming,
    Included authority_flow_state new_incoming old_incoming ->
    (forall frame location,
      frame_owned_location CT h' frame location ->
      frame_owned_location CT h frame location) ->
    (forall left right,
      retained_mut_edge CT h' left right ->
      retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right ->
      mutable_edge CT h left right) ->
    (forall callee boundary left right,
      staged_return_adjacent h' callee boundary left right ->
      staged_return_adjacent h callee boundary left right) ->
    Included authority_flow_state
      (phased_authority_color_set_from CT h' active stack new_incoming)
      (phased_authority_color_set_from CT h active stack old_incoming).
Proof.
  intros CT h h' active stack. revert active.
  induction stack as [|boundary tail IH];
    intros active old_incoming new_incoming Hincoming Howned Hretained
      Hmutable Hreturn; simpl.
  all: assert (Included authority_flow_state
      (phased_frame_powered_seeds CT h' active)
      (phased_frame_powered_seeds CT h active)) as Hpowered by
    (intros state [location [Heq Hlocation]]; exists location;
     split; [exact Heq|apply Howned; exact Hlocation]).
  all: assert (Included authority_flow_state
      (Union authority_flow_state new_incoming
        (phased_frame_powered_seeds CT h' active))
      (Union authority_flow_state old_incoming
        (phased_frame_powered_seeds CT h active))) as Hseeds by
    (intros state Hstate; inversion Hstate; subst;
     [left; apply Hincoming; exact H | right; apply Hpowered; exact H]).
  all: assert (Included authority_flow_state
      (phased_authority_frame_closure CT h' active
        (Union authority_flow_state new_incoming
          (phased_frame_powered_seeds CT h' active)))
      (phased_authority_frame_closure CT h active
        (Union authority_flow_state old_incoming
          (phased_frame_powered_seeds CT h active)))) as Hframe by
    (intros state [seed [Hseed Hconnected]]; exists seed;
     split; [apply Hseeds; exact Hseed|];
     eapply phased_authority_frame_connected_after_graph_reflection; eauto).
  - exact Hframe.
  - assert (Hreturned : Included authority_flow_state
        (phased_authority_return_closure h' active boundary
          (demote_authority_set
            (phased_authority_frame_closure CT h' active
              (Union authority_flow_state new_incoming
                (phased_frame_powered_seeds CT h' active)))))
        (phased_authority_return_closure h active boundary
          (demote_authority_set
            (phased_authority_frame_closure CT h active
              (Union authority_flow_state old_incoming
                (phased_frame_powered_seeds CT h active)))))).
    { intros returned [seed [Hseed Hconnected]]. exists seed. split.
      - eapply demote_authority_set_monotone;
          [exact Hframe|exact Hseed].
      - eapply phased_authority_return_connected_after_graph_reflection.
        + intros left right Hedge. eapply Hreturn; eauto.
        + exact Hconnected. }
    intros state Hstate. inversion Hstate; subst.
    + left. apply Hframe. exact H.
    + right. eapply IH; eauto.
Qed.

Lemma phased_authority_colors_after_graph_reflection :
  forall CT h h' active stack Z,
    (forall frame location,
      frame_owned_location CT h' frame location ->
      frame_owned_location CT h frame location) ->
    (forall left right,
      retained_mut_edge CT h' left right ->
      retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right ->
      mutable_edge CT h left right) ->
    (forall callee boundary left right,
      staged_return_adjacent h' callee boundary left right ->
      staged_return_adjacent h callee boundary left right) ->
    phased_authority_colors_separated CT h Z active stack ->
    phased_authority_colors_separated CT h' Z active stack.
Proof.
  intros CT h h' active stack Z Howned Hretained Hmutable Hreturn
    Hseparated mode protected Hmode Hcolored Hprotected.
  apply (Hseparated mode protected Hmode); [|exact Hprotected].
  unfold phased_authority_color_set in *.
  eapply phased_authority_color_set_from_after_graph_reflection; eauto.
  intros state Hempty. inversion Hempty.
Qed.

(** Caller-origin colors use the same phase-local closure as the executing
    colors, but deliberately add no callee-owned seeds.  Consequently a
    graph-reflecting heap change transports them pointwise through every
    frame in the pending prefix. *)
Lemma pending_caller_colors_through_prefix_after_graph_reflection :
  forall CT h h' active above old_caller_colors new_caller_colors,
    Included authority_flow_state new_caller_colors old_caller_colors ->
    (forall frame location,
      frame_owned_location CT h' frame location ->
      frame_owned_location CT h frame location) ->
    (forall left right,
      retained_mut_edge CT h' left right ->
      retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right ->
      mutable_edge CT h left right) ->
    Included authority_flow_state
      (pending_caller_colors_through_prefix CT h' active above
        new_caller_colors)
      (pending_caller_colors_through_prefix CT h active above
        old_caller_colors).
Proof.
  intros CT h h' active above. revert active.
  induction above as [|boundary tail IH];
    intros active old_caller_colors new_caller_colors Hincoming Howned
      Hretained Hmutable state [seed [Hseed Hconnected]]; simpl in *.
  - exists seed. split.
    + apply Hincoming. exact Hseed.
    + eapply phased_authority_frame_connected_after_graph_reflection;
        eauto.
  - exists seed. split.
    + eapply IH; eauto.
    + eapply phased_authority_frame_connected_after_graph_reflection;
        eauto.
Qed.

Lemma pending_boundary_caller_colors_after_graph_reflection :
  forall CT h h' active boundary above below,
    (forall frame location,
      frame_owned_location CT h' frame location ->
      frame_owned_location CT h frame location) ->
    (forall left right,
      retained_mut_edge CT h' left right ->
      retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right ->
      mutable_edge CT h left right) ->
    (forall callee call_boundary left right,
      staged_return_adjacent h' callee call_boundary left right ->
      staged_return_adjacent h callee call_boundary left right) ->
    Included authority_flow_state
      (pending_boundary_caller_color_set CT h' active boundary above below)
      (pending_boundary_caller_color_set CT h active boundary above below).
Proof.
  intros CT h h' active boundary above below Howned Hretained Hmutable
    Hreturn.
  unfold pending_boundary_caller_color_set.
  eapply pending_caller_colors_through_prefix_after_graph_reflection;
    eauto.
  unfold phased_authority_color_set.
  eapply phased_authority_color_set_from_after_graph_reflection; eauto.
  intros state Hempty. inversion Hempty.
Qed.

Lemma pending_call_phased_authority_after_graph_reflection :
  forall CT h h' active stack tracked_depth,
    (forall frame substack location,
      In Loc (live_capability_set CT h' frame substack) location ->
      In Loc (live_capability_set CT h frame substack) location) ->
    (forall left right,
      retained_mut_edge CT h' left right ->
      retained_mut_edge CT h left right) ->
    (forall left right,
      mutable_edge CT h' left right ->
      mutable_edge CT h left right) ->
    (forall callee boundary left right,
      staged_return_adjacent h' callee boundary left right ->
      staged_return_adjacent h callee boundary left right) ->
    pending_call_phased_authority_separated CT h active stack
      tracked_depth ->
    pending_call_phased_authority_separated CT h' active stack
      tracked_depth.
Proof.
  intros CT h h' active stack tracked_depth Hcapability Hretained Hmutable
    Hreturn Hpending boundary above below owned mode Hpartition Htracked
    Hfree Howned Hmode Hcolored.
  have Howned_old :
      In Loc (pending_owned_authority_set CT h active above) owned.
  { apply Hcapability. exact Howned. }
  apply (Hpending boundary above below owned mode Hpartition Htracked Hfree
    Howned_old Hmode).
  eapply pending_boundary_caller_colors_after_graph_reflection;
    [|exact Hretained|exact Hmutable|exact Hreturn|exact Hcolored].
  intros frame location Hframe_owned.
  apply frame_owned_location_iff_active_live.
  apply (Hcapability frame [] location).
  apply frame_owned_location_iff_active_live. exact Hframe_owned.
Qed.

Definition phased_state_owned_or_neutral
  (CT : class_table) (h : heap) (frame : watched_frame)
  (state : authority_flow_state) : Prop :=
  fst state = FlowNeutral \/ fst state = FlowProspective \/
    frame_owned_location CT h frame (snd state).

Lemma phased_authority_frame_step_preserves_owned_or_neutral :
  forall CT h frame source target,
    phased_state_owned_or_neutral CT h frame source ->
    phased_authority_frame_step CT h frame source target ->
    phased_state_owned_or_neutral CT h frame target.
Proof.
  intros CT h frame source target Hsource Hstep.
  inversion Hstep; subst; simpl in *.
  - right. right.
    destruct Hsource as [Hbad | [Hbad | Howned]]; try discriminate.
    destruct Howned as [root [Hroot Hreachable]].
    exists root. split; [exact Hroot|].
    eapply retained_mut_reachable_transitive; [exact Hreachable|].
    eapply rmr_step; [constructor|exact H].
  - right. left. reflexivity.
  - right. left. reflexivity.
  - right. left. reflexivity.
  - left. reflexivity.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. left. reflexivity.
  - left. reflexivity.
  - left. reflexivity.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. exact H.
Qed.

Lemma phased_authority_frame_connected_preserves_owned_or_neutral :
  forall CT h frame source target,
    phased_state_owned_or_neutral CT h frame source ->
    phased_authority_frame_connected CT h frame source target ->
    phased_state_owned_or_neutral CT h frame target.
Proof.
  intros CT h frame source target Hsource Hconnected.
  induction Hconnected.
  - eapply phased_authority_frame_step_preserves_owned_or_neutral; eauto.
  - exact Hsource.
  - apply IHHconnected2. apply IHHconnected1. exact Hsource.
Qed.

(** A demoted return cannot regain dangerous authority merely by crossing
    heap edges or RDM frame joins.  Its first non-neutral transition must be
    promotion at a capability independently owned by the resumed frame.
    The suffix is retained explicitly for the call-pop proof. *)
Lemma phased_authority_frame_connected_from_neutral_has_owned_promotion :
  forall CT h frame start target,
    phased_authority_frame_connected CT h frame
      (FlowNeutral, start) target ->
    fst target = FlowNeutral \/
    exists anchor,
      frame_owned_location CT h frame anchor /\
      phased_authority_frame_connected CT h frame
        (FlowPowered, anchor) target.
Proof.
  intros CT h frame start target Hconnected.
  remember (FlowNeutral, start) as source eqn:Hsource.
  revert start Hsource.
  induction Hconnected; intros start Hsource; subst.
  - inversion H; subst; simpl; try discriminate;
      try solve [left; reflexivity].
    right. eexists. split; [eassumption|apply rt_refl].
  - left. reflexivity.
  - destruct (IHHconnected1 start eq_refl) as
      [Hmiddle_neutral | [anchor [Howned Hanchor_middle]]].
    + destruct y as [middle_mode middle_location]. simpl in Hmiddle_neutral.
      subst middle_mode.
      eapply IHHconnected2. reflexivity.
    + right. exists anchor. split; [exact Howned|].
      eapply rt_trans; eauto.
Qed.

Lemma demote_authority_set_members_neutral :
  forall seeds state,
    In authority_flow_state (demote_authority_set seeds) state ->
    fst state = FlowNeutral.
Proof.
  intros seeds state [mode [location [Hseed Heq]]]. subst state. reflexivity.
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

Lemma phased_authority_return_connected_preserves_neutral :
  forall h callee boundary source target,
    fst source = FlowNeutral ->
    phased_authority_return_connected h callee boundary source target ->
    fst target = FlowNeutral.
Proof.
  intros h callee boundary source target Hsource Hconnected.
  induction Hconnected.
  - eapply phased_authority_return_step_preserves_neutral; eauto.
  - exact Hsource.
  - apply IHHconnected2. apply IHHconnected1. exact Hsource.
Qed.

Lemma phased_authority_return_from_demoted_is_neutral :
  forall h callee boundary seeds state,
    In authority_flow_state
      (phased_authority_return_closure h callee boundary
        (demote_authority_set seeds)) state ->
    fst state = FlowNeutral.
Proof.
  intros h callee boundary seeds state [seed [Hseed Hconnected]].
  eapply phased_authority_return_connected_preserves_neutral; [|exact Hconnected].
  eapply demote_authority_set_members_neutral. exact Hseed.
Qed.

Lemma returned_authority_dangerous_has_caller_owned_promotion :
  forall CT h callee boundary callee_colors caller mode location,
    authority_mode_dangerous mode ->
    In authority_flow_state
      (phased_authority_frame_closure CT h caller
        (phased_authority_return_closure h callee boundary
          (demote_authority_set callee_colors)))
      (mode, location) ->
    exists anchor,
      frame_owned_location CT h caller anchor /\
      phased_authority_frame_connected CT h caller
        (FlowPowered, anchor) (mode, location).
Proof.
  intros CT h callee boundary callee_colors caller mode location Hmode
    [seed [Hseed Hconnected]].
  have Hneutral := phased_authority_return_from_demoted_is_neutral h callee
    boundary callee_colors seed Hseed.
  destruct seed as [seed_mode seed_location]. simpl in Hneutral.
  subst seed_mode.
  destruct (phased_authority_frame_connected_from_neutral_has_owned_promotion
    CT h caller seed_location (mode, location) Hconnected) as
    [Htarget_neutral | [anchor [Howned Hsuffix]]].
  - simpl in Htarget_neutral.
    destruct Hmode as [-> | ->]; discriminate.
  - exists anchor. split; assumption.
Qed.

Lemma phased_authority_color_set_from_powered_has_live_frame :
  forall CT h active stack incoming location,
    (forall state,
      In authority_flow_state incoming state -> fst state = FlowNeutral) ->
    In authority_flow_state
      (phased_authority_color_set_from CT h active stack incoming)
      (FlowPowered, location) ->
    exists frame,
      live_frame_member active stack frame /\
      frame_owned_location CT h frame location.
Proof.
  intros CT h active stack. revert active.
  induction stack as [|boundary tail IH];
    intros active incoming location Hincoming Hcolored; simpl in Hcolored.
  - destruct Hcolored as [seed [Hseed Hconnected]].
    have Hseed_state : phased_state_owned_or_neutral CT h active seed.
    { inversion Hseed; subst.
      - left. apply Hincoming. exact H.
      - destruct H as [seed_location [Heq Howned]]. subst seed.
        right. right. exact Howned. }
    have Htarget := phased_authority_frame_connected_preserves_owned_or_neutral
      CT h active seed (FlowPowered, location) Hseed_state Hconnected.
    destruct Htarget as [Hbad | [Hbad | Howned]]; try discriminate.
    exists active. split; [constructor|exact Howned].
  - inversion Hcolored; subst.
    + destruct H as [seed [Hseed Hconnected]].
      have Hseed_state : phased_state_owned_or_neutral CT h active seed.
      { inversion Hseed as [seed' Hincoming_seed | seed' Hpowered_seed];
          subst seed'.
        - left. apply Hincoming. exact Hincoming_seed.
        - destruct Hpowered_seed as [seed_location [Heq Howned]]. subst seed.
          right. right. exact Howned. }
      have Htarget := phased_authority_frame_connected_preserves_owned_or_neutral
        CT h active seed (FlowPowered, location) Hseed_state Hconnected.
      destruct Htarget as [Hbad | [Hbad | Howned]]; try discriminate.
      exists active. split; [constructor|exact Howned].
    + destruct (IH boundary.(boundary_caller)
        (phased_authority_return_closure h active boundary
          (demote_authority_set
            (phased_authority_frame_closure CT h active
              (Union authority_flow_state incoming
                (phased_frame_powered_seeds CT h active)))))
        location) as [frame [Hlive Howned]].
      * intros state Hstate.
        eapply phased_authority_return_from_demoted_is_neutral. exact Hstate.
      * exact H.
      * exists frame. split.
        -- eapply live_frame_member_under_suspended_head. exact Hlive.
        -- exact Howned.
Qed.

Lemma phased_authority_active_owned_is_powered :
  forall CT h active stack incoming location,
    frame_owned_location CT h active location ->
    In authority_flow_state
      (phased_authority_color_set_from CT h active stack incoming)
      (FlowPowered, location).
Proof.
  intros CT h active stack incoming location Howned.
  destruct stack as [|boundary tail]; simpl.
  - eapply phased_authority_frame_closure_contains. right.
    exists location. split; [reflexivity|exact Howned].
  - left. eapply phased_authority_frame_closure_contains. right.
    exists location. split; [reflexivity|exact Howned].
Qed.

Lemma phased_authority_suspended_owned_is_powered :
  forall CT h active stack incoming boundary location,
    List.In boundary stack ->
    frame_owned_location CT h boundary.(boundary_caller) location ->
    In authority_flow_state
      (phased_authority_color_set_from CT h active stack incoming)
      (FlowPowered, location).
Proof.
  intros CT h active stack incoming. revert active incoming.
  induction stack as [|head tail IH];
    intros active incoming boundary location Hin Howned; [inversion Hin|].
  simpl. right. simpl in Hin. destruct Hin as [-> | Hin].
  - eapply phased_authority_active_owned_is_powered. exact Howned.
  - eapply IH; eauto.
Qed.

Lemma live_capability_is_phased_authority_powered :
  forall CT h active stack location,
    In Loc (live_capability_set CT h active stack) location ->
    In authority_flow_state
      (phased_authority_color_set CT h active stack)
      (FlowPowered, location).
Proof.
  intros CT h active stack location Hlive.
  apply live_capability_iff_live_frame_owned in Hlive.
  destruct Hlive as [frame [Hmember Howned]].
  inversion Hmember; subst.
  - unfold phased_authority_color_set.
    eapply phased_authority_active_owned_is_powered. exact Howned.
  - unfold phased_authority_color_set.
    eapply phased_authority_suspended_owned_is_powered; eauto.
Qed.

Lemma staged_call_phase_after_callee_descent_included :
  forall CT h authority old_senv old_renv new_senv new_renv boundary
    old_seeds new_seeds,
    wf_r_config CT old_senv old_renv h ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc new_seeds old_seeds ->
    Included Loc
      (staged_return_closure h
        (mk_watched_frame authority new_senv new_renv) boundary
        (staged_frame_closure CT h
          (mk_watched_frame authority new_senv new_renv) new_seeds))
      (staged_frame_closure CT h boundary.(boundary_caller)
        (staged_return_closure h
          (mk_watched_frame authority old_senv old_renv) boundary
          (staged_frame_closure CT h
            (mk_watched_frame authority old_senv old_renv) old_seeds))).
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv boundary
    old_seeds new_seeds Hwf Hdescend Hincluded location
    [seed [Hseed_new Hreturn]].
  have Hseed_old :
      In Loc
        (staged_frame_closure CT h
          (mk_watched_frame authority old_senv old_renv) old_seeds) seed.
  { eapply staged_frame_closure_after_descent_included; eauto. }
  destruct (staged_return_connected_classifies h
    (mk_watched_frame authority new_senv new_renv) boundary seed location
    Hreturn) as [Heq | Hclass].
  - subst location. exists seed. split.
    + eapply staged_return_closure_contains. exact Hseed_old.
    + apply rt_refl.
  - destruct Hclass as
      [Hview [Hcallee_return [Hseed_location
        [Hseed_root Hlocation_root]]]].
    destruct (staged_return_root_after_callee_descent_has_representative
      CT h authority old_senv old_renv new_senv new_renv boundary seed Hwf
      Hdescend Hseed_root) as
      [seed_rep [Hseed_rep_root [Hseed_component Hseed_rep_runtime]]].
    destruct (staged_return_root_after_callee_descent_has_representative
      CT h authority old_senv old_renv new_senv new_renv boundary location
      Hwf Hdescend Hlocation_root) as
      [location_rep
        [Hlocation_rep_root
          [Hlocation_component Hlocation_rep_runtime]]].
    have Hrepresentative_runtime :
        r_muttype h seed_rep = r_muttype h location_rep.
    { rewrite Hseed_rep_runtime. rewrite Hlocation_rep_runtime.
      exact Hseed_location. }
    have Hseed_rep_colored :
        In Loc
          (staged_frame_closure CT h
            (mk_watched_frame authority old_senv old_renv) old_seeds)
          seed_rep.
    { destruct Hseed_old as [origin [Horigin Horigin_seed]].
      exists origin. split; [exact Horigin|].
      eapply staged_frame_connected_trans; [exact Horigin_seed|].
      eapply mutable_connected_is_staged_frame_connected.
      eapply mutable_connected_sym. exact Hseed_component. }
    assert (Hlocation_rep_after_caller :
      In Loc
        (staged_frame_closure CT h boundary.(boundary_caller)
          (staged_return_closure h
            (mk_watched_frame authority old_senv old_renv) boundary
            (staged_frame_closure CT h
              (mk_watched_frame authority old_senv old_renv) old_seeds)))
        location_rep).
    {
      destruct Hseed_rep_root as [Hseed_callee | Hseed_caller];
        destruct Hlocation_rep_root as
          [Hlocation_callee | Hlocation_caller].
      - have Hlocation_before_return :
            In Loc
              (staged_frame_closure CT h
                (mk_watched_frame authority old_senv old_renv) old_seeds)
              location_rep.
        { destruct Hseed_rep_colored as
            [origin [Horigin Horigin_seed_rep]].
          exists origin. split; [exact Horigin|].
          eapply staged_frame_connected_trans;
            [exact Horigin_seed_rep|].
          apply rt_step. right. split;
            [exact Hseed_callee|exact Hlocation_callee]. }
        exists location_rep. split.
        + eapply staged_return_closure_contains.
          exact Hlocation_before_return.
        + apply rt_refl.
      - exists location_rep. split.
        + exists seed_rep. split; [exact Hseed_rep_colored|].
          apply rt_step. repeat split; try assumption.
          left. split; assumption.
        + apply rt_refl.
      - exists location_rep. split.
        + exists seed_rep. split; [exact Hseed_rep_colored|].
          apply rt_step. repeat split; try assumption.
          right. split; assumption.
        + apply rt_refl.
      - exists seed_rep. split.
        + eapply staged_return_closure_contains.
          exact Hseed_rep_colored.
        + apply rt_step. right. split;
            [exact Hseed_caller|exact Hlocation_caller].
    }
    destruct Hlocation_rep_after_caller as
      [caller_seed [Hcaller_seed Hcaller_path]].
    exists caller_seed. split; [exact Hcaller_seed|].
    eapply staged_frame_connected_trans; [exact Hcaller_path|].
    eapply mutable_connected_is_staged_frame_connected.
    exact Hlocation_component.
Qed.

Lemma staged_live_color_set_after_active_descent_included :
  forall CT h authority old_senv old_renv new_senv new_renv stack
    old_seeds new_seeds,
    wf_r_config CT old_senv old_renv h ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc new_seeds old_seeds ->
    Included Loc
      (staged_live_color_set CT h
        (mk_watched_frame authority new_senv new_renv) stack new_seeds)
      (staged_live_color_set CT h
        (mk_watched_frame authority old_senv old_renv) stack old_seeds).
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv stack
    old_seeds new_seeds Hwf Hdescend Hincluded.
  destruct stack as [|boundary tail]; simpl.
  - eapply staged_frame_closure_after_descent_included; eauto.
  - intros location Hlocation.
    eapply staged_live_color_set_absorbs_active_frame_closure.
    eapply staged_live_color_set_monotone; [|exact Hlocation].
    eapply staged_call_phase_after_callee_descent_included; eauto.
Qed.

Lemma phased_live_color_set_from_after_active_descent_included :
  forall CT h authority old_senv old_renv new_senv new_renv stack incoming,
    wf_r_config CT old_senv old_renv h ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (live_capability_set CT h
        (mk_watched_frame authority new_senv new_renv) [])
      (live_capability_set CT h
        (mk_watched_frame authority old_senv old_renv) []) ->
    Included Loc
      (phased_live_color_set_from CT h
        (mk_watched_frame authority new_senv new_renv) stack incoming)
      (phased_live_color_set_from CT h
        (mk_watched_frame authority old_senv old_renv) stack incoming).
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv stack incoming
    Hwf Hdescend Hcapabilities.
  set (old_frame := mk_watched_frame authority old_senv old_renv).
  set (new_frame := mk_watched_frame authority new_senv new_renv).
  assert (Howned : Included Loc
      (phase_frame_capability_set CT h new_frame)
      (phase_frame_capability_set CT h old_frame)).
  { intros location Hlocation.
    unfold phase_frame_capability_set in *.
    apply frame_owned_location_iff_active_live.
    apply Hcapabilities.
    apply frame_owned_location_iff_active_live. exact Hlocation. }
  assert (Hseeds : Included Loc
      (Union Loc incoming (phase_frame_capability_set CT h new_frame))
      (Union Loc incoming (phase_frame_capability_set CT h old_frame))).
  { intros location Hlocation. inversion Hlocation; subst.
    - left. exact H.
    - right. apply Howned. exact H. }
  destruct stack as [|boundary tail]; simpl.
  - eapply staged_frame_closure_after_descent_included; eauto.
  - set (new_return := staged_return_closure h new_frame boundary
      (staged_frame_closure CT h new_frame
        (Union Loc incoming (phase_frame_capability_set CT h new_frame)))).
    set (old_return := staged_return_closure h old_frame boundary
      (staged_frame_closure CT h old_frame
        (Union Loc incoming (phase_frame_capability_set CT h old_frame)))).
    assert (Hcall_phase : Included Loc new_return
      (staged_frame_closure CT h boundary.(boundary_caller) old_return)).
    { unfold new_return, old_return, new_frame, old_frame.
      eapply staged_call_phase_after_callee_descent_included; eauto. }
    assert (Hcall_phase_with_capabilities : Included Loc new_return
      (staged_frame_closure CT h boundary.(boundary_caller)
        (Union Loc old_return
          (phase_frame_capability_set CT h boundary.(boundary_caller))))).
    { intros location Hlocation.
      eapply staged_frame_closure_monotone; [|apply Hcall_phase; exact Hlocation].
      intros seed Hseed. left. exact Hseed. }
    intros location Hlocation.
    apply (phased_live_color_set_from_absorbs_active_frame CT h
      boundary.(boundary_caller) tail old_return location).
    eapply phased_live_color_set_from_monotone;
      [exact Hcall_phase_with_capabilities|exact Hlocation].
Qed.

Lemma phased_colors_after_active_descent :
  forall CT h authority old_senv old_renv new_senv new_renv stack
    (Z : Ensemble Loc),
    wf_r_config CT old_senv old_renv h ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (live_capability_set CT h
        (mk_watched_frame authority new_senv new_renv) [])
      (live_capability_set CT h
        (mk_watched_frame authority old_senv old_renv) []) ->
    phased_colors_separated CT h Z
      (mk_watched_frame authority old_senv old_renv) stack ->
    phased_colors_separated CT h Z
      (mk_watched_frame authority new_senv new_renv) stack.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv stack Z Hwf
    Hdescend Hincluded Hseparated protected Hcolored Hprotected.
  apply (Hseparated protected); [|exact Hprotected].
  unfold phased_live_color_set in *.
  eapply phased_live_color_set_from_after_active_descent_included; eauto.
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

Lemma staged_frame_connected_after_field_update :
  forall CT h frame lx old field value left right,
    runtime_getObj h lx = Some old ->
    staged_frame_connected CT (update_field h lx field value) frame left right ->
    staged_frame_connected CT h frame left right \/
    exists written,
      value = Iot written /\
      ((staged_frame_connected CT h frame left lx /\
        staged_frame_connected CT h frame written right) \/
       (staged_frame_connected CT h frame left written /\
        staged_frame_connected CT h frame lx right)).
Proof.
  intros CT h frame lx old field value left right Hobj Hconnected.
  induction Hconnected.
  - destruct (staged_frame_adjacent_after_field_update CT h frame lx old
      field value x y Hobj H) as
      [Hold | [written [Hvalue [[-> ->] | [-> ->]]]]].
    + left. apply rt_step. exact Hold.
    + right. exists written. split; [exact Hvalue|]. left. split;
        apply staged_frame_connected_refl.
    + right. exists written. split; [exact Hvalue|]. right. split;
        apply staged_frame_connected_refl.
  - left. apply staged_frame_connected_refl.
  - destruct IHHconnected1 as
      [Hxy | [written1 [Hvalue1 [[Hxlx Hwritten1y] |
        [Hxwritten1 Hlxy]]]]];
    destruct IHHconnected2 as
      [Hyz | [written2 [Hvalue2 [[Hylx Hwritten2z] |
        [Hywritten2 Hlxyz]]]]].
    + left. eapply staged_frame_connected_trans; eauto.
    + right. exists written2. split; [exact Hvalue2|]. left. split.
      * eapply staged_frame_connected_trans; eauto.
      * exact Hwritten2z.
    + right. exists written2. split; [exact Hvalue2|]. right. split.
      * eapply staged_frame_connected_trans; eauto.
      * exact Hlxyz.
    + right. exists written1. split; [exact Hvalue1|]. left. split.
      * exact Hxlx.
      * eapply staged_frame_connected_trans; eauto.
    + rewrite Hvalue1 in Hvalue2. injection Hvalue2 as <-.
      right. exists written1. split; [exact Hvalue1|]. left. split;
        assumption.
    + rewrite Hvalue1 in Hvalue2. injection Hvalue2 as <-.
      left. eapply staged_frame_connected_trans; [exact Hxlx|exact Hlxyz].
    + right. exists written1. split; [exact Hvalue1|]. right. split.
      * exact Hxwritten1.
      * eapply staged_frame_connected_trans; eauto.
    + rewrite Hvalue1 in Hvalue2. injection Hvalue2 as <-.
      left. eapply staged_frame_connected_trans;
        [exact Hxwritten1|exact Hwritten2z].
    + rewrite Hvalue1 in Hvalue2. injection Hvalue2 as <-.
      right. exists written1. split; [exact Hvalue1|]. right. split;
        assumption.
Qed.

Lemma staged_frame_connected_after_null_field_update_is_old :
  forall CT h frame lx old field left right,
    runtime_getObj h lx = Some old ->
    staged_frame_connected CT (update_field h lx field Null_a)
      frame left right ->
    staged_frame_connected CT h frame left right.
Proof.
  intros CT h frame lx old field left right Hobj Hconnected.
  destruct (staged_frame_connected_after_field_update CT h frame lx old
    field Null_a left right Hobj Hconnected) as
    [Hold | [written [Hvalue Hpaths]]].
  - exact Hold.
  - discriminate.
Qed.

Lemma staged_frame_connected_after_non_rdm_field_update_is_old :
  forall CT h frame lx old field value C fieldT left right,
    runtime_getObj h lx = Some old ->
    base_subtype CT (rctype (rt_type old)) C ->
    sf_def_rel CT C field fieldT ->
    mutability (ftype fieldT) <> RDM_f ->
    mutability (ftype fieldT) <> Mut_f ->
    staged_frame_connected CT (update_field h lx field value)
      frame left right ->
    staged_frame_connected CT h frame left right.
Proof.
  intros CT h frame lx old field value C fieldT left right Hobj Hbase
    Hfield Hnot_rdm Hnot_mut Hconnected.
  induction Hconnected.
  - destruct H as [[Hforward | Hbackward] | Hframe].
    + destruct (retained_edge_after_field_update CT h lx old field value
        x y Hobj Hforward) as [Hold | Hnew].
      * apply rt_step. left. left. exact Hold.
      * destruct Hnew as [Hsource [Hvalue [D [runtime_fd [Hruntime_base
          [Hruntime_field Hruntime_kind]]]]]].
        destruct Hruntime_kind as [Hruntime_rdm | Hruntime_mut].
        -- assert (runtime_fd = fieldT).
           { eapply field_defs_agree_at_runtime_subtype with
               (C := rctype (rt_type old)) (D1 := D) (D2 := C); eauto. }
           subst runtime_fd. contradiction.
        -- assert (runtime_fd = fieldT).
           { eapply field_defs_agree_at_runtime_subtype with
               (C := rctype (rt_type old)) (D1 := D) (D2 := C); eauto. }
           subst runtime_fd. contradiction.
    + destruct (mutable_edge_after_field_update CT h lx old field value
        y x Hobj Hbackward) as [Hold | Hnew].
      * apply rt_step. left. right. exact Hold.
      * destruct Hnew as [Hsource [Hvalue [D [runtime_fd [Hruntime_base
          [Hruntime_field Hruntime_rdm]]]]]].
        assert (runtime_fd = fieldT).
        { eapply field_defs_agree_at_runtime_subtype with
            (C := rctype (rt_type old)) (D1 := D) (D2 := C); eauto. }
        subst runtime_fd. contradiction.
    + apply rt_step. right. exact Hframe.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

(** If both endpoints of the only new edge are already colored seeds, any
    post-update path can restart at the endpoint after its last traversal of
    that edge.  Thus the update does not enlarge this phase's color set. *)
Lemma staged_frame_closure_after_colored_field_update_included :
  forall CT h frame seeds lx old field written,
    runtime_getObj h lx = Some old ->
    In Loc seeds lx ->
    In Loc seeds written ->
    Included Loc
      (staged_frame_closure CT (update_field h lx field (Iot written))
        frame seeds)
      (staged_frame_closure CT h frame seeds).
Proof.
  intros CT h frame seeds lx old field written Hobj Hlx Hwritten location
    [seed [Hseed Hpath]].
  destruct (staged_frame_connected_after_field_update CT h frame lx old
    field (Iot written) seed location Hobj Hpath) as
    [Hold | [written' [Hvalue [[Hseed_lx Hwritten_location] |
      [Hseed_written Hlx_location]]]]].
  - exists seed. split; assumption.
  - injection Hvalue as <-. exists written. split; assumption.
  - injection Hvalue as <-. exists lx. split; assumption.
Qed.

Lemma staged_frame_closure_members_runtime_mutable :
  forall CT h frame seeds,
    wf_r_config CT frame.(frame_senv) frame.(frame_renv) h ->
    (forall seed, In Loc seeds seed -> r_muttype h seed = Some Mut_r) ->
    forall location,
      In Loc (staged_frame_closure CT h frame seeds) location ->
      r_muttype h location = Some Mut_r.
Proof.
  intros CT h frame seeds Hwf Hseeds location
    [seed [Hseed Hconnected]].
  eapply staged_frame_connected_preserves_runtime_mutability; eauto.
Qed.

Lemma staged_return_closure_members_runtime_mutable :
  forall h callee boundary seeds,
    (forall seed, In Loc seeds seed -> r_muttype h seed = Some Mut_r) ->
    forall location,
      In Loc (staged_return_closure h callee boundary seeds) location ->
      r_muttype h location = Some Mut_r.
Proof.
  intros h callee boundary seeds Hseeds location
    [seed [Hseed Hconnected]].
  eapply staged_return_connected_preserves_runtime_mutability; eauto.
Qed.

Lemma staged_frame_closure_after_immutable_field_update_included :
  forall CT h frame old_seeds new_seeds lx old field written,
    runtime_getObj h lx = Some old ->
    wf_r_config CT frame.(frame_senv) frame.(frame_renv) h ->
    Included Loc new_seeds old_seeds ->
    (forall seed,
      In Loc new_seeds seed ->
      r_muttype (update_field h lx field (Iot written)) seed = Some Mut_r) ->
    r_muttype h lx = Some Imm_r ->
    r_muttype h written = Some Imm_r ->
    Included Loc
      (staged_frame_closure CT (update_field h lx field (Iot written))
        frame new_seeds)
      (staged_frame_closure CT h frame old_seeds).
Proof.
  intros CT h frame old_seeds new_seeds lx old field written Hobj Hwf
    Hseeds Hseed_runtime Hlx_immutable Hwritten_immutable location
    [seed [Hseed Hpath]].
  destruct (staged_frame_connected_after_field_update CT h frame lx old
    field (Iot written) seed location Hobj Hpath) as
    [Hold | [written' [Hvalue [[Hseed_lx Hwritten_location] |
      [Hseed_written Hlx_location]]]]].
  - exists seed. split; [apply Hseeds; exact Hseed|exact Hold].
  - injection Hvalue as <-.
    have Hseed_mut := Hseed_runtime seed Hseed.
    rewrite r_muttype_update_field_preserve in Hseed_mut.
    have Hlx_mut := staged_frame_connected_preserves_runtime_mutability CT h
      frame seed lx Mut_r Hwf Hseed_lx Hseed_mut.
    rewrite Hlx_immutable in Hlx_mut. discriminate.
  - injection Hvalue as <-.
    have Hseed_mut := Hseed_runtime seed Hseed.
    rewrite r_muttype_update_field_preserve in Hseed_mut.
    have Hwritten_mut :=
      staged_frame_connected_preserves_runtime_mutability CT h frame seed
        written Mut_r Hwf Hseed_written Hseed_mut.
    rewrite Hwritten_immutable in Hwritten_mut. discriminate.
Qed.

Lemma staged_return_connected_after_field_update_is_old :
  forall h callee boundary lx field value left right,
    staged_return_connected (update_field h lx field value)
      callee boundary left right ->
    staged_return_connected h callee boundary left right.
Proof.
  intros h callee boundary lx field value left right Hconnected.
  induction Hconnected.
  - apply rt_step.
    destruct H as [Hview [Hreturn [Hruntime Hroots]]].
    repeat split; try assumption.
    repeat rewrite r_muttype_update_field_preserve in Hruntime.
    exact Hruntime.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma staged_live_color_set_after_immutable_field_update_included :
  forall CT h active stack old_M new_M lx old field written,
    runtime_getObj h lx = Some old ->
    live_frames_wf CT h active stack ->
    live_frames_wf CT (update_field h lx field (Iot written)) active stack ->
    Included Loc new_M old_M ->
    (forall seed,
      In Loc new_M seed ->
      r_muttype (update_field h lx field (Iot written)) seed = Some Mut_r) ->
    r_muttype h lx = Some Imm_r ->
    r_muttype h written = Some Imm_r ->
    Included Loc
      (staged_live_color_set CT (update_field h lx field (Iot written))
        active stack new_M)
      (staged_live_color_set CT h active stack old_M).
Proof.
  intros CT h active stack. revert active.
  induction stack as [|boundary tail IH];
    intros active old_M new_M lx old field written Hobj Hframes_old
      Hframes_post HM Hnew_runtime Hlx_immutable Hwritten_immutable; simpl.
  - eapply staged_frame_closure_after_immutable_field_update_included;
      eauto. exact (proj1 Hframes_old).
  - destruct Hframes_old as [Hactive_old Hstack_old].
    destruct Hframes_post as [Hactive_post Hstack_post].
    set (post_frame := staged_frame_closure CT
      (update_field h lx field (Iot written)) active new_M).
    set (old_frame := staged_frame_closure CT h active old_M).
    set (post_return := staged_return_closure
      (update_field h lx field (Iot written)) active boundary post_frame).
    set (old_return := staged_return_closure h active boundary old_frame).
    assert (Hframe_included : Included Loc post_frame old_frame).
    { unfold post_frame, old_frame.
      eapply staged_frame_closure_after_immutable_field_update_included;
        eauto. }
    assert (Hpost_frame_runtime : forall location,
      In Loc post_frame location ->
      r_muttype (update_field h lx field (Iot written)) location =
        Some Mut_r).
    { unfold post_frame.
      eapply staged_frame_closure_members_runtime_mutable; eauto. }
    assert (Hreturn_included : Included Loc post_return old_return).
    { unfold post_return, old_return.
      intros location [seed [Hseed Hconnected]].
      exists seed. split.
      - apply Hframe_included. exact Hseed.
      - eapply staged_return_connected_after_field_update_is_old; eauto. }
    assert (Hpost_return_runtime : forall location,
      In Loc post_return location ->
      r_muttype (update_field h lx field (Iot written)) location =
        Some Mut_r).
    { unfold post_return.
      eapply staged_return_closure_members_runtime_mutable.
      exact Hpost_frame_runtime. }
    eapply IH.
    + exact Hobj.
    + split.
      * exact (Forall_inv Hstack_old).
      * exact (Forall_inv_tail Hstack_old).
    + split.
      * exact (Forall_inv Hstack_post).
      * exact (Forall_inv_tail Hstack_post).
    + exact Hreturn_included.
    + exact Hpost_return_runtime.
    + exact Hlx_immutable.
    + exact Hwritten_immutable.
Qed.

Lemma staged_return_closure_after_field_update_included :
  forall h callee boundary lx field value old_seeds new_seeds,
    Included Loc new_seeds old_seeds ->
    Included Loc
      (staged_return_closure (update_field h lx field value)
        callee boundary new_seeds)
      (staged_return_closure h callee boundary old_seeds).
Proof.
  intros h callee boundary lx field value old_seeds new_seeds Hseeds
    location [seed [Hseed Hconnected]].
  exists seed. split.
  - apply Hseeds. exact Hseed.
  - eapply staged_return_connected_after_field_update_is_old; eauto.
Qed.

Lemma staged_frame_closure_after_graph_reflection :
  forall CT h h' frame old_seeds new_seeds,
    Included Loc new_seeds old_seeds ->
    (forall left right,
      staged_frame_connected CT h' frame left right ->
      staged_frame_connected CT h frame left right) ->
    Included Loc
      (staged_frame_closure CT h' frame new_seeds)
      (staged_frame_closure CT h frame old_seeds).
Proof.
  intros CT h h' frame old_seeds new_seeds Hseeds Hgraph location
    [seed [Hseed Hconnected]].
  exists seed. split; [apply Hseeds; exact Hseed|].
  apply Hgraph. exact Hconnected.
Qed.

Lemma staged_return_closure_after_graph_reflection :
  forall h h' callee boundary old_seeds new_seeds,
    Included Loc new_seeds old_seeds ->
    (forall left right,
      staged_return_connected h' callee boundary left right ->
      staged_return_connected h callee boundary left right) ->
    Included Loc
      (staged_return_closure h' callee boundary new_seeds)
      (staged_return_closure h callee boundary old_seeds).
Proof.
  intros h h' callee boundary old_seeds new_seeds Hseeds Hgraph location
    [seed [Hseed Hconnected]].
  exists seed. split; [apply Hseeds; exact Hseed|].
  apply Hgraph. exact Hconnected.
Qed.

Lemma staged_live_color_set_after_graph_reflection :
  forall CT h h' active stack old_seeds new_seeds,
    Included Loc new_seeds old_seeds ->
    (forall frame left right,
      staged_frame_connected CT h' frame left right ->
      staged_frame_connected CT h frame left right) ->
    (forall callee boundary left right,
      staged_return_connected h' callee boundary left right ->
      staged_return_connected h callee boundary left right) ->
    Included Loc
      (staged_live_color_set CT h' active stack new_seeds)
      (staged_live_color_set CT h active stack old_seeds).
Proof.
  intros CT h h' active stack. revert active.
  induction stack as [|boundary tail IH];
    intros active old_seeds new_seeds Hseeds Hframe Hreturn; simpl.
  - eapply staged_frame_closure_after_graph_reflection; eauto.
  - eapply IH.
    + eapply staged_return_closure_after_graph_reflection.
      * eapply staged_frame_closure_after_graph_reflection; eauto.
      * intros left right Hconnected.
        eapply Hreturn; eauto.
    + exact Hframe.
    + exact Hreturn.
Qed.

Lemma phased_live_color_set_from_after_graph_reflection :
  forall CT h h' active stack old_incoming new_incoming,
    Included Loc new_incoming old_incoming ->
    (forall frame,
      Included Loc
        (phase_frame_capability_set CT h' frame)
        (phase_frame_capability_set CT h frame)) ->
    (forall frame left right,
      staged_frame_connected CT h' frame left right ->
      staged_frame_connected CT h frame left right) ->
    (forall callee boundary left right,
      staged_return_connected h' callee boundary left right ->
      staged_return_connected h callee boundary left right) ->
    Included Loc
      (phased_live_color_set_from CT h' active stack new_incoming)
      (phased_live_color_set_from CT h active stack old_incoming).
Proof.
  intros CT h h' active stack. revert active.
  induction stack as [|boundary tail IH];
    intros active old_incoming new_incoming Hincoming Howned Hframe Hreturn;
    simpl.
  - eapply staged_frame_closure_after_graph_reflection.
    + intros location Hlocation. inversion Hlocation; subst.
      * left. apply Hincoming. exact H.
      * right. apply Howned. exact H.
    + apply Hframe.
  - eapply IH.
    + eapply staged_return_closure_after_graph_reflection.
      * eapply staged_frame_closure_after_graph_reflection.
        -- intros location Hlocation. inversion Hlocation; subst.
           ++ left. apply Hincoming. exact H.
           ++ right. apply Howned. exact H.
        -- apply Hframe.
      * intros left right Hconnected. eapply Hreturn; eauto.
    + exact Howned.
    + exact Hframe.
    + exact Hreturn.
Qed.

Lemma phased_colors_after_graph_reflection :
  forall CT h h' active stack Z,
    (forall frame,
      Included Loc
        (phase_frame_capability_set CT h' frame)
        (phase_frame_capability_set CT h frame)) ->
    (forall frame left right,
      staged_frame_connected CT h' frame left right ->
      staged_frame_connected CT h frame left right) ->
    (forall callee boundary left right,
      staged_return_connected h' callee boundary left right ->
      staged_return_connected h callee boundary left right) ->
    phased_colors_separated CT h Z active stack ->
    phased_colors_separated CT h' Z active stack.
Proof.
  intros CT h h' active stack Z Howned Hframe Hreturn Hseparated
    protected Hcolored Hprotected.
  apply (Hseparated protected); [|exact Hprotected].
  unfold phased_live_color_set in *.
  eapply phased_live_color_set_from_after_graph_reflection; eauto.
  intros location Hempty. inversion Hempty.
Qed.

(** A typed mutable write has both endpoints in the initial live-color seed
    set.  Consequently the newly materialized edge is redundant not only in
    the active phase, but in each later caller phase: sequential frame and
    return closures retain their input seeds monotonically. *)
Lemma staged_live_color_set_after_colored_field_update_included :
  forall CT h active stack seeds lx old field written,
    runtime_getObj h lx = Some old ->
    In Loc seeds lx ->
    In Loc seeds written ->
    Included Loc
      (staged_live_color_set CT
        (update_field h lx field (Iot written)) active stack seeds)
      (staged_live_color_set CT h active stack seeds).
Proof.
  intros CT h active stack. revert active.
  induction stack as [|boundary tail IH];
    intros active seeds lx old field written Hobj Hlx Hwritten; simpl.
  - eapply staged_frame_closure_after_colored_field_update_included; eauto.
  - set (post_frame :=
      staged_frame_closure CT (update_field h lx field (Iot written))
        active seeds).
    set (old_frame := staged_frame_closure CT h active seeds).
    set (post_return := staged_return_closure
      (update_field h lx field (Iot written)) active boundary post_frame).
    set (old_return := staged_return_closure h active boundary old_frame).
    assert (Hpost_old : Included Loc post_return old_return).
    { unfold post_return, old_return.
      eapply staged_return_closure_after_field_update_included.
      unfold post_frame, old_frame.
      eapply staged_frame_closure_after_colored_field_update_included; eauto. }
    intros location Hlocation.
    eapply staged_live_color_set_monotone; [exact Hpost_old|].
    eapply IH; [exact Hobj| | |exact Hlocation].
    + unfold post_return, post_frame.
      eapply staged_return_closure_contains.
      eapply staged_frame_closure_contains. exact Hlx.
    + unfold post_return, post_frame.
      eapply staged_return_closure_contains.
      eapply staged_frame_closure_contains. exact Hwritten.
Qed.

Lemma authority_color_adjacent_after_active_descent_reflects :
  forall CT h authority old_senv old_renv new_senv new_renv stack left right,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    authority_color_adjacent CT h
      (mk_watched_frame authority new_senv new_renv) stack left right ->
    authority_color_connected CT h
      (mk_watched_frame authority old_senv old_renv) stack left right.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv stack left right
    Hdescend [Hheap | [frame [Hlive [Hleft Hright]]]].
  - apply rt_step. left. exact Hheap.
  - inversion Hlive; subst.
    + destruct (Hdescend left Hleft) as
        [old_left [Hold_left Hleft_reachable]].
      destruct (Hdescend right Hright) as
        [old_right [Hold_right Hright_reachable]].
      eapply authority_color_connected_trans.
      * eapply mutable_connected_is_authority_color_connected.
        eapply mutable_connected_sym.
        eapply mutable_reachable_connected. exact Hleft_reachable.
      * eapply authority_color_connected_trans.
        -- apply rt_step. right.
           exists (mk_watched_frame authority old_senv old_renv).
           split; [constructor|].
           split; [exact Hold_left|exact Hold_right].
        -- eapply mutable_connected_is_authority_color_connected.
           eapply mutable_reachable_connected. exact Hright_reachable.
    + apply rt_step. right. exists boundary.(boundary_caller).
      split; [constructor; exact H|].
      split; assumption.
Qed.

Lemma authority_color_connected_after_active_descent_reflects :
  forall CT h authority old_senv old_renv new_senv new_renv stack left right,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    authority_color_connected CT h
      (mk_watched_frame authority new_senv new_renv) stack left right ->
    authority_color_connected CT h
      (mk_watched_frame authority old_senv old_renv) stack left right.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv stack left right
    Hdescend Hconnected.
  induction Hconnected.
  - eapply authority_color_adjacent_after_active_descent_reflects; eauto.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma authority_flow_step_after_active_descent_reflects :
  forall CT h authority old_senv old_renv new_senv new_renv stack
    source target,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (live_capability_set CT h
        (mk_watched_frame authority new_senv new_renv) stack)
      (live_capability_set CT h
        (mk_watched_frame authority old_senv old_renv) stack) ->
    authority_flow_step CT h
      (mk_watched_frame authority new_senv new_renv) stack source target ->
    authority_flow_connected CT h
      (mk_watched_frame authority old_senv old_renv) stack source target.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv stack
    source target Hdescend Hcapabilities Hstep.
  inversion Hstep; subst.
  - apply rt_step. apply authority_flow_retained. exact H.
  - apply rt_step. apply authority_flow_reverse_rdm. exact H.
  - apply rt_step. apply authority_flow_neutral_rdm_forward. exact H.
  - apply rt_step. apply authority_flow_neutral_rdm_backward. exact H.
  - destruct H as [frame [Hlive [Hleft Hright]]].
    inversion Hlive; subst.
    + destruct (Hdescend left Hleft) as
        [old_left [Hold_left Hleft_reachable]].
      destruct (Hdescend right Hright) as
        [old_right [Hold_right Hright_reachable]].
      eapply rt_trans.
      * eapply mutable_reachable_is_reverse_powered_authority_flow.
        exact Hleft_reachable.
      * eapply rt_trans.
        -- apply rt_step. apply authority_flow_neutral_frame.
           exists (mk_watched_frame authority old_senv old_renv).
           split; [constructor|].
           split; [exact Hold_left|exact Hold_right].
        -- eapply mutable_reachable_is_neutral_authority_flow.
           exact Hright_reachable.
    + apply rt_step. apply authority_flow_powered_frame.
      exists boundary.(boundary_caller).
      split; [constructor; exact H|]. split; assumption.
  - destruct H as [frame [Hlive [Hleft Hright]]].
    inversion Hlive; subst.
    + destruct (Hdescend left Hleft) as
        [old_left [Hold_left Hleft_reachable]].
      destruct (Hdescend right Hright) as
        [old_right [Hold_right Hright_reachable]].
      eapply rt_trans.
      * eapply mutable_reachable_is_reverse_neutral_authority_flow.
        exact Hleft_reachable.
      * eapply rt_trans.
        -- apply rt_step. apply authority_flow_neutral_frame.
           exists (mk_watched_frame authority old_senv old_renv).
           split; [constructor|].
           split; [exact Hold_left|exact Hold_right].
        -- eapply mutable_reachable_is_neutral_authority_flow.
           exact Hright_reachable.
    + apply rt_step. apply authority_flow_neutral_frame.
      exists boundary.(boundary_caller).
      split; [constructor; exact H|]. split; assumption.
  - apply rt_step. apply authority_flow_forget.
  - apply rt_step. apply authority_flow_promote.
    apply Hcapabilities. exact H.
Qed.

Lemma authority_flow_connected_after_active_descent_reflects :
  forall CT h authority old_senv old_renv new_senv new_renv stack
    source target,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (live_capability_set CT h
        (mk_watched_frame authority new_senv new_renv) stack)
      (live_capability_set CT h
        (mk_watched_frame authority old_senv old_renv) stack) ->
    authority_flow_connected CT h
      (mk_watched_frame authority new_senv new_renv) stack source target ->
    authority_flow_connected CT h
      (mk_watched_frame authority old_senv old_renv) stack source target.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv stack
    source target Hdescend Hcapabilities Hconnected.
  induction Hconnected.
  - eapply authority_flow_step_after_active_descent_reflects; eauto.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

(** Intraprocedural root descent changes only the active frame.  Every edge
    of the new authority-sensitive color graph therefore reflects to a path
    in the old graph. *)
Lemma layered_color_adjacent_after_active_descent_reflects :
  forall CT h authority old_senv old_renv new_senv new_renv stack left right,
    wf_r_config CT old_senv old_renv h ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    layered_color_adjacent CT h
      (mk_watched_frame authority new_senv new_renv) stack left right ->
    layered_color_connected CT h
      (mk_watched_frame authority old_senv old_renv) stack left right.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv stack left right
    Hwf Hdescend [Hmutable | [Hframe | Hreturn]].
  - apply rt_step. left. exact Hmutable.
  - destruct Hframe as [frame [Hlive [Hleft Hright]]].
    inversion Hlive; subst.
    + destruct (Hdescend left Hleft) as
        [old_left [Hold_left Hleft_reachable]].
      destruct (Hdescend right Hright) as
        [old_right [Hold_right Hright_reachable]].
      eapply layered_color_connected_trans.
      * eapply mutable_reachable_is_reverse_layered_color_connected.
        exact Hleft_reachable.
      * eapply layered_color_connected_trans.
        -- apply rt_step. right. left.
           exists (mk_watched_frame authority old_senv old_renv).
           split; [apply live_frame_active|].
           split; [exact Hold_left|exact Hold_right].
        -- eapply mutable_reachable_is_layered_color_connected.
           exact Hright_reachable.
    + apply rt_step. right. left.
      exists boundary.(boundary_caller). repeat split; try assumption.
      constructor. exact H.
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
        eapply layered_color_connected_trans.
        -- eapply mutable_reachable_is_reverse_layered_color_connected.
           exact Hleft_reachable.
        -- apply rt_step. right. right.
           exists (mk_watched_frame authority old_senv old_renv), boundary.
           split; [constructor|]. split; [exact Hview|].
           split; [exact Hcallee_return|].
           split; [exact Hold_right_runtime|].
           left. split; [exact Hold_left|exact (proj2 Hroots)].
      * apply rt_step. right. right.
        exists callee, boundary. split.
        -- constructor. exact H.
        -- split; [exact Hview|]. split; [exact Hcallee_return|].
           split; [exact Hruntime|]. left. exact Hroots.
    + inversion Hboundary; subst.
      * destruct (Hdescend right (proj2 Hroots)) as
          [old_right [Hold_right Hright_reachable]].
        destruct (typed_rdm_root_has_runtime_context CT old_senv old_renv h
          old_right Hwf Hold_right) as [runtime_q Hold_runtime].
        have Hright_runtime := mutable_reachable_preserves_runtime_mutability
          CT h old_right right runtime_q (proj1 (proj2 Hwf))
          Hright_reachable Hold_runtime.
        assert (Hleft_old_runtime :
          r_muttype h left = r_muttype h old_right).
        { rewrite Hruntime. rewrite Hright_runtime. symmetry.
          exact Hold_runtime. }
        eapply layered_color_connected_trans.
        -- apply rt_step. right. right.
           exists (mk_watched_frame authority old_senv old_renv), boundary.
           split; [constructor|]. split; [exact Hview|].
           split; [exact Hcallee_return|].
           split; [exact Hleft_old_runtime|].
           right. split; [exact (proj1 Hroots)|exact Hold_right].
        -- eapply mutable_reachable_is_layered_color_connected.
           exact Hright_reachable.
      * apply rt_step. right. right.
        exists callee, boundary. split.
        -- constructor. exact H.
        -- split; [exact Hview|]. split; [exact Hcallee_return|].
           split; [exact Hruntime|]. right. exact Hroots.
Qed.

Lemma layered_color_connected_after_active_descent_reflects :
  forall CT h authority old_senv old_renv new_senv new_renv stack left right,
    wf_r_config CT old_senv old_renv h ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    layered_color_connected CT h
      (mk_watched_frame authority new_senv new_renv) stack left right ->
    layered_color_connected CT h
      (mk_watched_frame authority old_senv old_renv) stack left right.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv stack left right
    Hwf Hdescend Hconnected.
  induction Hconnected.
  - eapply layered_color_adjacent_after_active_descent_reflects; eauto.
  - apply rt_refl.
  - eapply rt_trans; eauto.
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

Lemma ownership_frame_edge_after_active_descent_reflects :
  forall CT h authority old_senv old_renv new_senv new_renv stack left right,
    Included Loc
      (live_capability_set CT h
        (mk_watched_frame authority new_senv new_renv) [])
      (live_capability_set CT h
        (mk_watched_frame authority old_senv old_renv) []) ->
    ownership_frame_edge CT h
      (mk_watched_frame authority new_senv new_renv) stack left right ->
    ownership_frame_edge CT h
      (mk_watched_frame authority old_senv old_renv) stack left right.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv stack left right
    Hincluded [frame [Hlive [Hleft Hright]]].
  inversion Hlive; subst.
  - exists (mk_watched_frame authority old_senv old_renv).
    split; [constructor|]. split;
      apply frame_owned_location_iff_active_live;
      apply Hincluded;
      apply frame_owned_location_iff_active_live;
      assumption.
  - exists boundary.(boundary_caller). split.
    + constructor. exact H.
    + split; assumption.
Qed.

Lemma active_live_capability_inclusion_lifts_stack :
  forall CT h old_active new_active stack,
    Included Loc
      (live_capability_set CT h new_active [])
      (live_capability_set CT h old_active []) ->
    Included Loc
      (live_capability_set CT h new_active stack)
      (live_capability_set CT h old_active stack).
Proof.
  intros CT h old_active new_active stack Hincluded location
    [root [[Hactive | Hsuspended] Hreachable]].
  - assert (Hnew : In Loc
      (live_capability_set CT h new_active []) location).
    { exists root. split; [left; exact Hactive|exact Hreachable]. }
    destruct (Hincluded location Hnew) as
      [old_root [[Hold_active | [boundary [Hin _]]] Hold_reachable]].
    + exists old_root. split; [left; exact Hold_active|exact Hold_reachable].
    + inversion Hin.
  - exists root. split; [right; exact Hsuspended|exact Hreachable].
Qed.

Lemma layered_colors_after_active_descent :
  forall CT h authority old_senv old_renv new_senv new_renv stack
    (Z : Ensemble Loc),
    wf_r_config CT old_senv old_renv h ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (live_capability_set CT h
        (mk_watched_frame authority new_senv new_renv) [])
      (live_capability_set CT h
        (mk_watched_frame authority old_senv old_renv) []) ->
    layered_colors_separated CT h
      (live_capability_set CT h
        (mk_watched_frame authority old_senv old_renv) stack)
      Z (mk_watched_frame authority old_senv old_renv) stack ->
    layered_colors_separated CT h
      (live_capability_set CT h
        (mk_watched_frame authority new_senv new_renv) stack)
      Z (mk_watched_frame authority new_senv new_renv) stack.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv stack Z Hwf
    Hdescend Hincluded Hseparated capability protected Hcapability
    Hprotected Hconnected.
  apply (Hseparated capability protected).
  - eapply active_live_capability_inclusion_lifts_stack; eauto.
  - exact Hprotected.
  - eapply layered_color_connected_after_active_descent_reflects; eauto.
Qed.

Lemma staged_colors_after_active_descent :
  forall CT h authority old_senv old_renv new_senv new_renv stack
    (Z : Ensemble Loc),
    wf_r_config CT old_senv old_renv h ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (live_capability_set CT h
        (mk_watched_frame authority new_senv new_renv) stack)
      (live_capability_set CT h
        (mk_watched_frame authority old_senv old_renv) stack) ->
    staged_colors_separated CT h
      (live_capability_set CT h
        (mk_watched_frame authority old_senv old_renv) stack)
      Z (mk_watched_frame authority old_senv old_renv) stack ->
    staged_colors_separated CT h
      (live_capability_set CT h
        (mk_watched_frame authority new_senv new_renv) stack)
      Z (mk_watched_frame authority new_senv new_renv) stack.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv stack Z Hwf
    Hdescend Hincluded Hseparated protected Hcolored Hprotected.
  apply (Hseparated protected).
  - eapply staged_live_color_set_after_active_descent_included; eauto.
  - exact Hprotected.
Qed.

Lemma authority_colors_after_active_descent :
  forall CT h authority old_senv old_renv new_senv new_renv stack
    (Z : Ensemble Loc),
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (live_capability_set CT h
        (mk_watched_frame authority new_senv new_renv) stack)
      (live_capability_set CT h
        (mk_watched_frame authority old_senv old_renv) stack) ->
    authority_colors_separated CT h
      (live_capability_set CT h
        (mk_watched_frame authority old_senv old_renv) stack)
      Z (mk_watched_frame authority old_senv old_renv) stack ->
    authority_colors_separated CT h
      (live_capability_set CT h
        (mk_watched_frame authority new_senv new_renv) stack)
      Z (mk_watched_frame authority new_senv new_renv) stack.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv stack Z
    Hdescend Hincluded Hseparated capability protected Hcapability Hprotected
    Hconnected.
  apply (Hseparated capability protected).
  - apply Hincluded. exact Hcapability.
  - exact Hprotected.
  - eapply authority_color_connected_after_active_descent_reflects; eauto.
Qed.

(** Replacing only the active frame by an RDM-descending frame preserves the
    pending-call ownership invariant.  Its conclusion deliberately lives in
    the suspended caller graph, which is unchanged by an intraprocedural
    assignment or local declaration. *)
Lemma pending_call_colors_after_active_descent :
  forall CT h authority old_senv old_renv new_senv new_renv stack,
    wf_r_config CT old_senv old_renv h ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (live_capability_set CT h
        (mk_watched_frame authority new_senv new_renv) [])
      (live_capability_set CT h
        (mk_watched_frame authority old_senv old_renv) []) ->
    pending_call_ownership_colors_separated CT h
      (mk_watched_frame authority old_senv old_renv) stack ->
    pending_call_ownership_colors_separated CT h
      (mk_watched_frame authority new_senv new_renv) stack.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv stack Hwf
    Hdescend Hcapabilities Hpending boundary above below capability owned
    Hpartition Hempty Howned Hcapability.
  have Hpartition_old :
      live_call_partition
        (mk_watched_frame authority old_senv old_renv)
        stack boundary above below.
  { eapply live_call_partition_change_active. exact Hpartition. }
  have Howned_old :
      In Loc
        (live_capability_set CT h
          (mk_watched_frame authority old_senv old_renv) above) owned.
  { eapply active_live_capability_inclusion_lifts_stack; eauto. }
  intros common [Hcapability_common Howned_common].
  apply (Hpending boundary above below capability owned Hpartition_old
    Hempty Howned_old Hcapability common).
  split;
    eapply potential_connected_after_active_descent_reflects_strong; eauto.
Qed.

Lemma tracked_pending_call_colors_after_active_descent :
  forall CT h authority old_senv old_renv new_senv new_renv stack
    tracked_depth,
    wf_r_config CT old_senv old_renv h ->
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (live_capability_set CT h
        (mk_watched_frame authority new_senv new_renv) [])
      (live_capability_set CT h
        (mk_watched_frame authority old_senv old_renv) []) ->
    tracked_pending_call_ownership_colors_separated CT h
      (mk_watched_frame authority old_senv old_renv) stack tracked_depth ->
    tracked_pending_call_ownership_colors_separated CT h
      (mk_watched_frame authority new_senv new_renv) stack tracked_depth.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv stack
    tracked_depth Hwf Hdescend Hcapabilities Hpending boundary above below
    capability owned Hpartition Htracked Hchannel_free Howned Hcapability.
  have Hpartition_old :
      live_call_partition
        (mk_watched_frame authority old_senv old_renv)
        stack boundary above below.
  { eapply live_call_partition_change_active. exact Hpartition. }
  have Howned_old :
      In Loc
        (live_capability_set CT h
          (mk_watched_frame authority old_senv old_renv) above) owned.
  { eapply active_live_capability_inclusion_lifts_stack; eauto. }
  intros common [Hcapability_common Howned_common].
  apply (Hpending boundary above below capability owned Hpartition_old
    Htracked Hchannel_free Howned_old Hcapability common).
  split;
    eapply potential_connected_after_active_descent_reflects_strong; eauto.
Qed.

Lemma pending_call_stateful_authority_after_active_descent :
  forall CT h authority old_senv old_renv new_senv new_renv stack
    tracked_depth,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    Included Loc
      (live_capability_set CT h
        (mk_watched_frame authority new_senv new_renv) [])
      (live_capability_set CT h
        (mk_watched_frame authority old_senv old_renv) []) ->
    pending_call_stateful_authority_separated CT h
      (mk_watched_frame authority old_senv old_renv) stack tracked_depth ->
    pending_call_stateful_authority_separated CT h
      (mk_watched_frame authority new_senv new_renv) stack tracked_depth.
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv stack
    tracked_depth Hdescend
    Hcapabilities Hpending boundary above below capability owned Hpartition
    Htracked Hchannel_free Howned Hcapability Hconnected.
  have Hpartition_old :
      live_call_partition
        (mk_watched_frame authority old_senv old_renv)
        stack boundary above below.
  { eapply live_call_partition_change_active. exact Hpartition. }
  have Howned_old :
      In Loc
        (pending_owned_authority_set CT h
          (mk_watched_frame authority old_senv old_renv) above) owned.
  { eapply pending_owned_authority_after_active_descent_included; eauto. }
  apply (Hpending boundary above below capability owned Hpartition_old
    Htracked Hchannel_free Howned_old Hcapability).
  eapply authority_flow_connected_after_active_descent_reflects;
    [exact Hdescend| |exact Hconnected].
  intros location Hlocation.
  eapply active_live_capability_inclusion_lifts_stack;
    [exact Hcapabilities|exact Hlocation].
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

Lemma initial_authority_color_live_history :
  forall CT sGamma rGamma h,
    wf_r_config CT sGamma rGamma h ->
    env_respects_protected_set
      (reachable_locations_from_initial_env h rGamma) sGamma rGamma ->
    authority_color_live_history_state CT
      (reachable_locations_from_initial_env h rGamma)
      (reachable_locations_from_initial_env h rGamma)
      (dom h) (mk_watched_frame Imm_r sGamma rGamma) [] h.
Proof.
  intros CT sGamma rGamma h Hwf Henv.
  destruct (initial_potential_live_history CT sGamma rGamma h Hwf Henv) as
    [Hlive [Hpotential Hcutoffs]].
  split; [exact Hlive|]. split; [|exact Hcutoffs].
  eapply potential_colors_imply_authority_colors; eauto.
Qed.

Lemma initial_principled_phased_authority_live_history :
  forall CT sGamma rGamma h,
    wf_r_config CT sGamma rGamma h ->
    env_respects_protected_set
      (reachable_locations_from_initial_env h rGamma) sGamma rGamma ->
    principled_phased_authority_live_history_state CT
      (reachable_locations_from_initial_env h rGamma)
      (reachable_locations_from_initial_env h rGamma)
      (dom h) (mk_watched_frame Imm_r sGamma rGamma) []
      (Empty_set authority_flow_state) h.
Proof.
  intros CT sGamma rGamma h Hwf Henv.
  have Hinitial := initial_authority_component_history CT sGamma rGamma h
    Hwf Henv.
  have Hlive := initial_live_authority_history CT sGamma rGamma h Hwf Henv.
  have Hempty := initial_live_capability_set_empty CT sGamma rGamma h
    (proj1 (proj2 Hinitial)).
  destruct Hlive as
    [[Hdirected Hauthority] [Hframes [Hsound [Hcutoff [Hzone Hchain]]]]].
  destruct Hdirected as
    [Hcontains [Hzone_env [Hconfined Hdirected_tail]]].
  refine (conj Hcontains (conj Hconfined _)).
  refine (conj _ _).
  - intros mode location Hnone. inversion Hnone.
  - refine (conj _ (conj Hframes (conj Hsound (conj Hcutoff
      (conj Hzone (conj Hchain _)))))).
    + intros mode protected Hmode Hcolored.
    unfold executing_authority_color_set in Hcolored.
    destruct Hcolored as [seed [Hseed Hconnected]].
    inversion Hseed as [state Hincoming | state Hpowered]; subst.
      * inversion Hincoming.
      * destruct Hpowered as [location [Heq Howned]]. subst seed.
        exfalso. apply (Hempty location).
        apply frame_owned_location_iff_active_live. exact Howned.
    + constructor.
Qed.
