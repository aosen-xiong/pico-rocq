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
    boundary.  Unlike authority roots, RDM roots do not themselves grant
    mutation authority; they identify components that a future typed field
    write in that frame may join. *)
Inductive live_frame_member
  (active : watched_frame) (stack : list watched_boundary) :
  watched_frame -> Prop :=
| live_frame_active : live_frame_member active stack active
| live_frame_suspended : forall boundary,
    List.In boundary stack ->
    live_frame_member active stack boundary.(boundary_caller).

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
    view.  Such a return can put any callee RDM value into an RDM destination
    of the suspended caller.  This proof-only edge records that latent future
    connection while the body is still executing.  The runtime-context
    equality is semantic evidence that the two RDM roots can coexist in the
    same caller frame after return. *)
Definition potential_return_edge
  (h : heap) (active : watched_frame) (stack : list watched_boundary)
  (left right : Loc) : Prop :=
  exists callee boundary,
    live_call_boundary active stack callee boundary /\
    boundary.(boundary_receiver_view) = RDM /\
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
  (retained_mut_edge CT h left right \/ mutable_edge CT h right left) \/
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

(** The operational/history facts and the potential-component separation are
    kept together because both are needed at every recursive statement
    evaluation, including a method body. *)
Definition potential_live_history_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary) (h : heap) : Prop :=
  live_authority_history_state CT P Z cutoff active stack h /\
  potential_colors_separated CT h
    (live_capability_set CT h active stack) Z active stack.

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
    [callee [boundary [Hlive [Hview [Hruntime [Hroots | Hroots]]]]]].
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
  apply rt_step. right. left. exists frame. repeat split; assumption.
Qed.

Lemma potential_return_edge_preserves_runtime_mutability :
  forall h active stack left right runtime_q,
    potential_return_edge h active stack left right ->
    r_muttype h left = Some runtime_q ->
    r_muttype h right = Some runtime_q.
Proof.
  intros h active stack left right runtime_q
    [callee [boundary [Hlive [Hview [Hruntime Hroots]]]]] Hleft.
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
    [Hheap_edge | [Hframe_edge | Hreturn_edge]] Hleft_runtime.
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
    [Hheap_edge | [Hframe_edge | Hreturn_edge]] Hright_runtime.
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
    Hwf Hdescend [Hheap | [[frame [Hlive [Hleft Hright]]] | Hreturn]].
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
      repeat split; try assumption. constructor. exact H.
  - destruct Hreturn as
      [callee [boundary [Hboundary [Hview [Hruntime [Hroots | Hroots]]]]]].
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
           split; [exact Hold_right_runtime|].
           left. split; [exact Hold_left|exact (proj2 Hroots)].
      * apply rt_step. right. right. exists callee, boundary.
        split; [constructor; exact H|]. split; [exact Hview|].
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
           split; [exact Hleft_old_runtime|].
           right. split; [exact (proj1 Hroots)|exact Hold_right].
        -- eapply mutable_reachable_is_potential_connected; eauto.
      * apply rt_step. right. right. exists callee, boundary.
        split; [constructor; exact H|]. split; [exact Hview|].
        split; [exact Hruntime|]. right. exact Hroots.
Qed.

Lemma potential_connected_after_active_descent_reflects :
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
  have Hempty := initial_live_capability_set_empty CT sGamma rGamma h
    (proj1 (proj2 Hinitial)).
  intros capability protected Hcapability. exfalso.
  exact (Hempty capability Hcapability).
Qed.

Lemma potential_history_after_assignment :
  forall CT P Z cutoff authority sGamma mt rGamma h stack x e old value,
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack h ->
    stmt_typing CT sGamma mt (SVarAss x e) sGamma ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma x = Some old ->
    eval_expr CT rGamma h e value OK rGamma h ->
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma
        (update_r_env_value rGamma x value)) stack h.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack x e old value
    [Hlive Hpotential] Htyping Hscope Hx Heval.
  have Hlive_post := live_history_after_assignment CT P Z cutoff authority
    sGamma mt rGamma h stack x e old value Hlive Htyping Hscope Hx Heval.
  split; [exact Hlive_post|].
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 Hlive)).
  have Hdescend := rdm_roots_descend_after_assignment CT sGamma mt
    rGamma h x e old value Hwf Htyping Hscope Hx Heval.
  intros capability protected Hcapability Hprotected Hconnected.
  apply (Hpotential capability protected).
  - eapply assignment_live_reachability_is_old; eauto.
  - exact Hprotected.
  - eapply potential_connected_after_active_descent_reflects; eauto.
Qed.

Lemma potential_history_after_local :
  forall CT P Z cutoff authority sGamma mt rGamma h stack T x sGamma',
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack h ->
    stmt_typing CT sGamma mt (SLocal T x) sGamma' ->
    runtime_getVal rGamma x = None ->
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma'
        (set_vars rGamma (vars rGamma ++ [Null_a]))) stack h.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack T x sGamma'
    [Hlive Hpotential] Htyping Hnone.
  have Hlive_post := live_history_after_local CT P Z cutoff authority
    sGamma mt rGamma h stack T x sGamma' Hlive Htyping Hnone.
  split; [exact Hlive_post|].
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 Hlive)).
  have Hdescend := rdm_roots_descend_after_local CT sGamma mt rGamma h
    T x sGamma' Hwf Htyping Hnone.
  intros capability protected Hcapability Hprotected Hconnected.
  apply (Hpotential capability protected).
  - eapply local_live_reachability_is_old; eauto.
  - exact Hprotected.
  - eapply potential_connected_after_active_descent_reflects; eauto.
Qed.

Lemma potential_adjacent_after_field_update :
  forall CT h active stack lx old field value left right,
    runtime_getObj h lx = Some old ->
    potential_adjacent CT (update_field h lx field value)
      active stack left right ->
    potential_adjacent CT h active stack left right \/
    exists written,
      value = Iot written /\
      ((left = lx /\ right = written) \/
       (left = written /\ right = lx)).
Proof.
  intros CT h active stack lx old field value left right Hobj
    [Hheap | [Hframe | Hreturn]].
  - destruct Hheap as [Hforward | Hbackward].
    + destruct (retained_edge_after_field_update CT h lx old field value
        left right Hobj Hforward) as [Hold | [Hsource [Hvalue Hnew]]].
      * left. left. left. exact Hold.
      * right. exists right. split; [exact Hvalue|]. left. split; auto.
    + destruct (mutable_edge_after_field_update CT h lx old field value
        right left Hobj Hbackward) as [Hold | [Hsource [Hvalue Hnew]]].
      * left. left. right. exact Hold.
      * right. exists left. split; [exact Hvalue|]. right. split; auto.
  - left. right. left. exact Hframe.
  - left. right. right.
    destruct Hreturn as
      [callee [boundary [Hlive [Hview [Hruntime Hroots]]]]].
    exists callee, boundary. split; [exact Hlive|]. split; [exact Hview|].
    split; [|exact Hroots].
    repeat rewrite r_muttype_update_field_preserve in Hruntime.
    exact Hruntime.
Qed.

Lemma potential_return_edge_after_field_update_is_old :
  forall h active stack lx field value left right,
    potential_return_edge (update_field h lx field value)
      active stack left right ->
    potential_return_edge h active stack left right.
Proof.
  intros h active stack lx field value left right
    [callee [boundary [Hlive [Hview [Hruntime Hroots]]]]].
  exists callee, boundary. split; [exact Hlive|]. split; [exact Hview|].
  split; [|exact Hroots].
  repeat rewrite r_muttype_update_field_preserve in Hruntime.
  exact Hruntime.
Qed.

(** A field update adds at most one directed potential edge; the two cases
    below record whether a path traverses that edge forward or backward. This is the
    potential-graph analogue of [mutable_connected_after_field_update] and is
    the normalization used by the typed field-write preservation proof. *)
Lemma potential_connected_after_field_update :
  forall CT h active stack lx old field value left right,
    runtime_getObj h lx = Some old ->
    potential_connected CT (update_field h lx field value)
      active stack left right ->
    potential_connected CT h active stack left right \/
    exists written,
      value = Iot written /\
      ((potential_connected CT h active stack left lx /\
        potential_connected CT h active stack written right) \/
       (potential_connected CT h active stack left written /\
        potential_connected CT h active stack lx right)).
Proof.
  intros CT h active stack lx old field value left right Hobj Hconnected.
  induction Hconnected.
  - destruct (potential_adjacent_after_field_update CT h active stack lx old
      field value x y Hobj H) as
      [Hold | [written [Hvalue [[-> ->] | [-> ->]]]]].
    + left. apply rt_step. exact Hold.
    + right. exists written. split; [exact Hvalue|]. left. split;
        apply potential_connected_refl.
    + right. exists written. split; [exact Hvalue|]. right. split;
        apply potential_connected_refl.
  - left. apply potential_connected_refl.
  - destruct IHHconnected1 as
      [Hxy | [written1 [Hvalue1 [[Hxlx Hwritten1y] |
        [Hxwritten1 Hlxy]]]]];
    destruct IHHconnected2 as
      [Hyz | [written2 [Hvalue2 [[Hylx Hwritten2z] |
        [Hywritten2 Hlxyz]]]]].
    + left. eapply potential_connected_trans; eauto.
    + right. exists written2. split; [exact Hvalue2|]. left. split.
      * eapply potential_connected_trans; eauto.
      * exact Hwritten2z.
    + right. exists written2. split; [exact Hvalue2|]. right. split.
      * eapply potential_connected_trans; eauto.
      * exact Hlxyz.
    + right. exists written1. split; [exact Hvalue1|]. left. split.
      * exact Hxlx.
      * eapply potential_connected_trans; eauto.
    + rewrite Hvalue1 in Hvalue2. injection Hvalue2 as <-.
      right. exists written1. split; [exact Hvalue1|]. left. split;
        assumption.
    + rewrite Hvalue1 in Hvalue2. injection Hvalue2 as <-.
      left. eapply potential_connected_trans; [exact Hxlx|exact Hlxyz].
    + right. exists written1. split; [exact Hvalue1|]. right. split.
      * exact Hxwritten1.
      * eapply potential_connected_trans; eauto.
    + rewrite Hvalue1 in Hvalue2. injection Hvalue2 as <-.
      left. eapply potential_connected_trans;
        [exact Hxwritten1|exact Hwritten2z].
    + rewrite Hvalue1 in Hvalue2. injection Hvalue2 as <-.
      right. exists written1. split; [exact Hvalue1|]. right. split;
        assumption.
Qed.

Lemma potential_connected_after_non_rdm_field_update_is_old :
  forall CT h active stack lx old field value C fieldT left right,
    runtime_getObj h lx = Some old ->
    base_subtype CT (rctype (rt_type old)) C ->
    sf_def_rel CT C field fieldT ->
    mutability (ftype fieldT) <> RDM_f ->
    mutability (ftype fieldT) <> Mut_f ->
    potential_connected CT (update_field h lx field value)
      active stack left right ->
    potential_connected CT h active stack left right.
Proof.
  intros CT h active stack lx old field value C fieldT left right Hobj
    Hbase Hfield Hnot_rdm Hnot_mut Hconnected.
  eapply potential_connected_map_edges; [|exact Hconnected].
  intros edge_left edge_right [Hheap | [Hframe | Hreturn]].
  - apply rt_step. left. destruct Hheap as [Hforward | Hbackward].
    + left. destruct (retained_edge_after_field_update CT h lx old field value
        edge_left edge_right Hobj Hforward) as
        [Hold | [Hsource [Hvalue [D [runtime_fd [Hruntime_base
          [Hruntime_field [Hruntime_rdm | Hruntime_mut]]]]]]]].
      * exact Hold.
      * assert (runtime_fd = fieldT).
        { eapply field_defs_agree_at_runtime_subtype with
            (C := rctype (rt_type old)) (D1 := D) (D2 := C); eauto. }
        subst runtime_fd. contradiction.
      * assert (runtime_fd = fieldT).
        { eapply field_defs_agree_at_runtime_subtype with
            (C := rctype (rt_type old)) (D1 := D) (D2 := C); eauto. }
        subst runtime_fd. contradiction.
    + right. destruct (mutable_edge_after_field_update CT h lx old field value
        edge_right edge_left Hobj Hbackward) as
        [Hold | [Hsource [Hvalue [D [runtime_fd [Hruntime_base
          [Hruntime_field Hruntime_rdm]]]]]]].
      * exact Hold.
      * assert (runtime_fd = fieldT).
        { eapply field_defs_agree_at_runtime_subtype with
            (C := rctype (rt_type old)) (D1 := D) (D2 := C); eauto. }
        subst runtime_fd. contradiction.
  - apply rt_step. right. left. exact Hframe.
  - apply rt_step. right. right.
    eapply potential_return_edge_after_field_update_is_old; eauto.
Qed.

Lemma potential_connected_after_null_field_update_is_old :
  forall CT h active stack lx old field left right,
    runtime_getObj h lx = Some old ->
    potential_connected CT (update_field h lx field Null_a)
      active stack left right ->
    potential_connected CT h active stack left right.
Proof.
  intros CT h active stack lx old field left right Hobj Hconnected.
  eapply potential_connected_map_edges; [|exact Hconnected].
  intros edge_left edge_right [Hheap | [Hframe | Hreturn]].
  - destruct Hheap as [Hforward | Hbackward].
    + destruct (retained_edge_after_field_update CT h lx old field Null_a
        edge_left edge_right Hobj Hforward) as
        [Hold | [Hsource [Hvalue Hnew]]].
      * apply rt_step. left. left. exact Hold.
      * discriminate.
    + destruct (mutable_edge_after_field_update CT h lx old field Null_a
        edge_right edge_left Hobj Hbackward) as
        [Hold | [Hsource [Hvalue Hnew]]].
      * apply rt_step. left. right. exact Hold.
      * discriminate.
  - apply rt_step. right. left. exact Hframe.
  - apply rt_step. right. right.
    eapply potential_return_edge_after_field_update_is_old; eauto.
Qed.

Lemma live_capability_after_non_rdm_field_update_is_old :
  forall CT h active stack lx old field value C fieldT location,
    runtime_getObj h lx = Some old ->
    base_subtype CT (rctype (rt_type old)) C ->
    sf_def_rel CT C field fieldT ->
    mutability (ftype fieldT) <> RDM_f ->
    mutability (ftype fieldT) <> Mut_f ->
    live_capability_reachable CT (update_field h lx field value)
      active stack location ->
    live_capability_reachable CT h active stack location.
Proof.
  intros CT h active stack lx old field value C fieldT location Hobj
    Hbase Hfield Hnot_rdm Hnot_mut [root [Hroot Hreachable]].
  exists root. split; [exact Hroot|].
  induction Hreachable.
  - constructor.
  - eapply rmr_step.
    + exact (IHHreachable Hroot).
    + destruct (retained_edge_after_field_update CT h lx old field value
        l2 l3 Hobj H) as [Hold | [Hsource [Hvalue
          [D [runtime_fd [Hruntime_base [Hruntime_field Hruntime_q]]]]]]].
      * exact Hold.
      * assert (runtime_fd = fieldT).
        { eapply field_defs_agree_at_runtime_subtype with
            (C := rctype (rt_type old)) (D1 := D) (D2 := C); eauto. }
        subst runtime_fd. destruct Hruntime_q; contradiction.
Qed.

Lemma live_capability_after_null_field_update_is_old :
  forall CT h active stack lx old field location,
    runtime_getObj h lx = Some old ->
    live_capability_reachable CT (update_field h lx field Null_a)
      active stack location ->
    live_capability_reachable CT h active stack location.
Proof.
  intros CT h active stack lx old field location Hobj
    [root [Hroot Hreachable]].
  destruct (retained_reachable_after_field_update CT h lx old field Null_a
    root location Hobj Hreachable) as
    [Hold | [written [Hvalue _]]].
  - exists root. split; assumption.
  - discriminate.
Qed.

Lemma potential_colors_after_graph_reflection :
  forall CT h h' active stack M M' Z,
    Included Loc M' M ->
    (forall left right,
      potential_connected CT h' active stack left right ->
      potential_connected CT h active stack left right) ->
    potential_colors_separated CT h M Z active stack ->
    potential_colors_separated CT h' M' Z active stack.
Proof.
  intros CT h h' active stack M M' Z HM Hgraph Hseparated
    capability protected Hcapability Hprotected Hconnected.
  apply (Hseparated capability protected (HM capability Hcapability)
    Hprotected).
  apply Hgraph. exact Hconnected.
Qed.

Lemma typed_mut_root_is_live_capability :
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

Lemma typed_rdm_root_is_live_under_mut_authority :
  forall CT h sGamma rGamma stack root,
    typed_root RDM sGamma rGamma root ->
    In Loc
      (live_capability_set CT h
        (mk_watched_frame Mut_r sGamma rGamma) stack) root.
Proof.
  intros CT h sGamma rGamma stack root
    [variable [T [Htype [Hvalue Hrdm]]]].
  exists root. split.
  - left. exists variable, T. repeat split; try assumption.
    unfold capability_in_context. right. split; [exact Hrdm|reflexivity].
  - constructor.
Qed.

Lemma typed_imm_root_runtime_immutable :
  forall CT sGamma rGamma h root,
    wf_r_config CT sGamma rGamma h ->
    typed_root Imm sGamma rGamma root ->
    r_muttype h root = Some Imm_r.
Proof.
  intros CT sGamma rGamma h root Hwf
    [variable [T [Htype [Hvalue Himm]]]].
  destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwf) as
    [receiver [context [Hreceiver [_ Hcontext]]]].
  have Hwf_copy := Hwf.
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [_ [_ [_ Hcorrespondence]]]]].
  have Hvariable_dom := Htype. apply static_getType_dom in Hvariable_dom.
  specialize (Hcorrespondence receiver context Hreceiver Hcontext variable
    Hvariable_dom T Htype).
  rewrite Hvalue in Hcorrespondence.
  unfold wf_r_typable, r_type in Hcorrespondence.
  destruct (runtime_getObj h root) as [object|] eqn:Hobject;
    try contradiction.
  destruct Hcorrespondence as [_ Hqualifier].
  unfold qualifier_typable_context, vpa_mutability_runtime in Hqualifier.
  rewrite Himm in Hqualifier.
  unfold r_muttype. rewrite Hobject. simpl.
  destruct (rqtype (rt_type object)).
  - destruct context; contradiction.
  - reflexivity.
Qed.

Lemma potential_connected_after_field_update_if_edge_redundant :
  forall CT h active stack lx old field written left right,
    runtime_getObj h lx = Some old ->
    potential_connected CT h active stack lx written ->
    potential_connected CT h active stack written lx ->
    potential_connected CT (update_field h lx field (Iot written))
      active stack left right ->
    potential_connected CT h active stack left right.
Proof.
  intros CT h active stack lx old field written left right Hobj
    Hforward Hbackward Hconnected.
  destruct (potential_connected_after_field_update CT h active stack lx old
    field (Iot written) left right Hobj Hconnected) as
    [Hold | [new_written [Hvalue [[Hleft_lx Hwritten_right] |
      [Hleft_written Hlx_right]]]]].
  - exact Hold.
  - injection Hvalue as <-. eapply potential_connected_trans.
    + exact Hleft_lx.
    + eapply potential_connected_trans; [exact Hforward|exact Hwritten_right].
  - injection Hvalue as <-. eapply potential_connected_trans.
    + exact Hleft_written.
    + eapply potential_connected_trans.
      * exact Hbackward.
      * exact Hlx_right.
Qed.

Lemma live_capability_after_redundant_field_update_has_old_potential_origin :
  forall CT h active stack lx old field written location,
    runtime_getObj h lx = Some old ->
    potential_connected CT h active stack lx written ->
    potential_connected CT h active stack written lx ->
    In Loc
      (live_capability_set CT (update_field h lx field (Iot written))
        active stack) location ->
    exists old_capability,
      In Loc (live_capability_set CT h active stack) old_capability /\
      potential_connected CT h active stack old_capability location.
Proof.
  intros CT h active stack lx old field written location Hobj Hforward Hbackward
    [root [Hroot Hreachable]].
  exists root. split.
  - exists root. split; [exact Hroot|constructor].
  - eapply potential_connected_after_field_update_if_edge_redundant;
      [exact Hobj|exact Hforward|exact Hbackward|].
    eapply retained_reachable_is_potential_connected; eauto.
Qed.

Lemma potential_colors_after_redundant_field_update :
  forall CT h active stack lx old field written M' M Z,
    runtime_getObj h lx = Some old ->
    potential_connected CT h active stack lx written ->
    potential_connected CT h active stack written lx ->
    (forall location,
      In Loc M' location ->
      exists old_capability,
        In Loc M old_capability /\
        potential_connected CT h active stack old_capability location) ->
    potential_colors_separated CT h M Z active stack ->
    potential_colors_separated CT
      (update_field h lx field (Iot written)) M' Z active stack.
Proof.
  intros CT h active stack lx old field written M' M Z Hobj Hforward Hbackward
    Horigin Hseparated capability protected Hcapability Hprotected
    Hconnected.
  destruct (Horigin capability Hcapability) as
    [old_capability [Hold_capability Hold_to_capability]].
  apply (Hseparated old_capability protected Hold_capability Hprotected).
  eapply potential_connected_trans; [exact Hold_to_capability|].
  eapply potential_connected_after_field_update_if_edge_redundant; eauto.
Qed.

Lemma potential_colors_after_m_colored_field_update :
  forall CT h active stack lx old field written M' M Z,
    runtime_getObj h lx = Some old ->
    Included Loc M' M ->
    In Loc M lx ->
    In Loc M written ->
    potential_colors_separated CT h M Z active stack ->
    potential_colors_separated CT
      (update_field h lx field (Iot written)) M' Z active stack.
Proof.
  intros CT h active stack lx old field written M' M Z Hobj HM Hlx
    Hwritten Hseparated capability protected Hcapability Hprotected
    Hconnected.
  destruct (potential_connected_after_field_update CT h active stack lx old
    field (Iot written) capability protected Hobj Hconnected) as
    [Hold | [new_written [Hvalue [[Hcap_lx Hwritten_protected] |
      [Hcap_written Hlx_protected]]]]].
  - exact (Hseparated capability protected (HM capability Hcapability)
      Hprotected Hold).
  - injection Hvalue as <-.
    exact (Hseparated written protected Hwritten Hprotected
      Hwritten_protected).
  - injection Hvalue as <-.
    exact (Hseparated lx protected Hlx Hprotected Hlx_protected).
Qed.

Lemma live_capability_after_immutable_source_field_update_is_old :
  forall CT h active stack lx old field written location,
    live_frames_wf CT h active stack ->
    live_frames_authority_sound h active stack ->
    runtime_getObj h lx = Some old ->
    r_muttype h lx = Some Imm_r ->
    In Loc
      (live_capability_set CT (update_field h lx field (Iot written))
        active stack) location ->
    In Loc (live_capability_set CT h active stack) location.
Proof.
  intros CT h active stack lx old field written location Hframes Hsound
    Hobj Hlx_immutable [root [Hroot Hreachable]].
  destruct (retained_reachable_after_field_update CT h lx old field
    (Iot written) root location Hobj Hreachable) as
    [Hold | [new_written [Hvalue [Hroot_lx Hwritten_location]]]].
  - exists root. split; assumption.
  - have Hroot_live : In Loc (live_capability_set CT h active stack) root.
    { exists root. split; [exact Hroot|constructor]. }
    have Hroot_runtime := live_capability_members_runtime_mutable CT h active
      stack Hframes Hsound root Hroot_live.
    have Hheap_wf : wf_heap CT h := proj1 (proj2 (proj1 Hframes)).
    have Hlx_runtime := retained_reachable_preserves_runtime_mutability CT h
      root lx Hheap_wf Hroot_lx Hroot_runtime.
    rewrite Hlx_immutable in Hlx_runtime. discriminate.
Qed.

Lemma potential_colors_after_immutable_field_update :
  forall CT h active stack lx old field written Z,
    live_frames_wf CT h active stack ->
    live_frames_authority_sound h active stack ->
    runtime_getObj h lx = Some old ->
    r_muttype h lx = Some Imm_r ->
    r_muttype h written = Some Imm_r ->
    potential_colors_separated CT h
      (live_capability_set CT h active stack) Z active stack ->
    potential_colors_separated CT
      (update_field h lx field (Iot written))
      (live_capability_set CT (update_field h lx field (Iot written))
        active stack) Z active stack.
Proof.
  intros CT h active stack lx old field written Z Hframes Hsound Hobj
    Hlx_immutable Hwritten_immutable Hseparated capability protected
    Hcapability Hprotected Hconnected.
  have Hcapability_old :=
    live_capability_after_immutable_source_field_update_is_old CT h active
      stack lx old field written capability Hframes Hsound Hobj
      Hlx_immutable Hcapability.
  destruct (potential_connected_after_field_update CT h active stack lx old
    field (Iot written) capability protected Hobj Hconnected) as
    [Hold | [new_written [Hvalue [[Hcap_lx Hwritten_protected] |
      [Hcap_written Hlx_protected]]]]].
  - exact (Hseparated capability protected Hcapability_old Hprotected Hold).
  - injection Hvalue as <-.
    have Hcapability_runtime := live_capability_members_runtime_mutable CT h
      active stack Hframes Hsound capability Hcapability_old.
    have Hheap_wf : wf_heap CT h := proj1 (proj2 (proj1 Hframes)).
    have Hlx_runtime := potential_connected_preserves_runtime_mutability CT h
      active stack capability lx Mut_r Hframes Hheap_wf Hcap_lx
      Hcapability_runtime.
    rewrite Hlx_immutable in Hlx_runtime. discriminate.
  - injection Hvalue as <-.
    have Hcapability_runtime := live_capability_members_runtime_mutable CT h
      active stack Hframes Hsound capability Hcapability_old.
    have Hheap_wf : wf_heap CT h := proj1 (proj2 (proj1 Hframes)).
    have Hwritten_runtime :=
      potential_connected_preserves_runtime_mutability CT h active stack
        capability written Mut_r Hframes Hheap_wf Hcap_written
        Hcapability_runtime.
    rewrite Hwritten_immutable in Hwritten_runtime. discriminate.
Qed.

(** The potential invariant supplies exactly the fact that the standalone live
    history cannot establish when a field write grows the live capability set:
    every newly live location remains disjoint from the protected zone. *)
Lemma live_history_after_field_write_given_potential :
  forall CT P Z cutoff authority sGamma mt rGamma h stack x field y
    sGamma' rGamma' h',
    live_authority_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack h ->
    stmt_typing CT sGamma mt (SFldWrite x field y) sGamma' ->
    readonly_state_method_scope mt ->
    eval_stmt CT rGamma h (SFldWrite x field y) OK rGamma' h' ->
    potential_colors_separated CT h'
      (live_capability_set CT h'
        (mk_watched_frame authority sGamma' rGamma') stack) Z
      (mk_watched_frame authority sGamma' rGamma') stack ->
    live_authority_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma' rGamma') stack h'.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack x field y
    sGamma' rGamma' h' Hlive Htyping Hscope Heval Hpotential.
  assert (HsGamma : sGamma' = sGamma) by
    (inversion Htyping; reflexivity).
  assert (HrGamma : rGamma' = rGamma) by
    (inversion Heval; reflexivity).
  subst sGamma' rGamma'.
  destruct Hlive as
    [Hauthority [[Hwf Hstack_wf]
      [[Hsound Hstack_sound] [Hcutoff [Hzone_bound Hchain]]]]].
  destruct (authority_history_after_field_write CT P Z
    (live_capability_set CT h
      (mk_watched_frame authority sGamma rGamma) stack)
    cutoff authority sGamma mt rGamma h x field y rGamma h' sGamma Hwf
    Hauthority Htyping Hscope Heval) as [Mbig [Hcontains_old Hbig]].
  destruct Hbig as
    [[[Hcontains [Hzone [Hconfined [Hclosed_big [Hruntime_big
      [Hmutroots_big [Havoid_big Hrdm_big]]]]]]]
      [Hcomponents_big Hactive_big]] [Hroots_big Hcontext]].
  have Hpost_wf := preservation_pico CT sGamma mt rGamma h
    (SFldWrite x field y) rGamma h' sGamma Hwf Htyping Heval.
  have Hheap' : wf_heap CT h' := proj1 (proj2 Hpost_wf).
  have Htypes : preserves_old_runtime_types h h'.
  { inversion Heval; subst. apply field_update_preserves_old_runtime_types. }
  destruct (live_frames_preserved_by_runtime_types CT h h'
    (mk_watched_frame authority sGamma rGamma) stack
    (conj Hwf Hstack_wf) (conj Hsound Hstack_sound) Hheap' Htypes) as
    [Hframes_wf Hframes_sound].
  have Hclosed := live_capability_set_forward_closed CT h'
    (mk_watched_frame authority sGamma rGamma) stack.
  have Hruntime := live_capability_members_runtime_mutable CT h'
    (mk_watched_frame authority sGamma rGamma) stack
    Hframes_wf Hframes_sound.
  have Hroots := active_authority_roots_are_live CT h'
    (mk_watched_frame authority sGamma rGamma) stack.
  have Hcomponents := potential_colors_imply_component_colors CT h'
    (live_capability_set CT h'
      (mk_watched_frame authority sGamma rGamma) stack) Z
    (mk_watched_frame authority sGamma rGamma) stack Hpotential.
  have Hactive := potential_colors_imply_active_colors CT h'
    (live_capability_set CT h'
      (mk_watched_frame authority sGamma rGamma) stack) Z
    (mk_watched_frame authority sGamma rGamma) stack Hpotential.
  have Hrdm := active_component_colors_imply_rdm_separation CT h'
    (live_capability_set CT h'
      (mk_watched_frame authority sGamma rGamma) stack) Z sGamma rGamma Hactive.
  assert (Havoid : forall location,
      In Loc (live_capability_set CT h'
        (mk_watched_frame authority sGamma rGamma) stack) location ->
      ~ In Loc Z location).
  { intros location Hlocation Hprotected.
    apply (Hpotential location location Hlocation Hprotected).
    apply potential_connected_refl. }
  split.
  - split.
    + split.
      * refine (conj Hcontains (conj Hzone (conj Hconfined
          (conj Hclosed (conj Hruntime (conj _ (conj Havoid Hrdm))))))).
        intros root [variable [T [Htype [Hvalue Hmut]]]].
        apply Hroots. exists variable, T. repeat split; try assumption.
        unfold capability_in_context. left. exact Hmut.
      * split; assumption.
    + split; assumption.
  - split; [exact Hframes_wf|].
    split; [exact Hframes_sound|]. split.
    + destruct Htypes as [Hdom _]. lia.
    + split; assumption.
Qed.

Lemma potential_history_after_field_write :
  forall CT P Z cutoff authority sGamma mt rGamma h stack x field y
    sGamma' rGamma' h',
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack h ->
    stmt_typing CT sGamma mt (SFldWrite x field y) sGamma' ->
    readonly_state_method_scope mt ->
    eval_stmt CT rGamma h (SFldWrite x field y) OK rGamma' h' ->
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma' rGamma') stack h'.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack x field y
    sGamma' rGamma' h' [Hlive Hpotential] Htyping Hscope Heval.
  assert (HsGamma : sGamma' = sGamma) by
    (inversion Htyping; reflexivity).
  assert (HrGamma : rGamma' = rGamma) by
    (inversion Heval; reflexivity).
  subst sGamma' rGamma'.
  assert (Hpotential_post : potential_colors_separated CT h'
      (live_capability_set CT h'
        (mk_watched_frame authority sGamma rGamma) stack) Z
      (mk_watched_frame authority sGamma rGamma) stack).
  {
  have Hframes : live_frames_wf CT h
      (mk_watched_frame authority sGamma rGamma) stack :=
    proj1 (proj2 Hlive).
  have Hsound : live_frames_authority_sound h
      (mk_watched_frame authority sGamma rGamma) stack :=
    proj1 (proj2 (proj2 Hlive)).
  have Hwf : wf_r_config CT sGamma rGamma h := proj1 Hframes.
  inversion Heval; subst.
  destruct val_y as [|written].
  - eapply potential_colors_after_graph_reflection
      with (M := live_capability_set CT h
        (mk_watched_frame authority sGamma rGamma) stack).
    + intros location Hlocation.
      eapply live_capability_after_null_field_update_is_old; eauto.
    + intros left right Hconnected.
      eapply potential_connected_after_null_field_update_is_old; eauto.
    + exact Hpotential.
  - destruct (typed_field_write_runtime_field_agreement CT sGamma mt rGamma
      h x field y loc_x o sGamma Hwf Htyping Hval_x Hobj) as
      [Tx [fieldT [Hgetx [Hfield_definition Hruntime_base]]]].
    destruct (mutability (ftype fieldT)) eqn:Hfield_mutability.
    + destruct (typed_runtime_mut_field_write_subtyping CT sGamma mt rGamma
        h x field y loc_x o (sctype Tx) fieldT sGamma Hwf Htyping Hscope
        Hval_x Hobj Hruntime_base Hfield_definition Hfield_mutability) as
        [Tx' [Ty [Hgetx' [Hgety Hsub]]]].
      destruct (safe_mut_write_endpoint_qualifiers CT sGamma rGamma h x y
        loc_x written Tx' Ty (f_base_type (ftype fieldT)) Hwf Hgetx' Hgety
        Hval_x Hval_y Hsub) as [Hreceiver_mut Hvalue_mut].
      have Hloc_x_live : In Loc
          (live_capability_set CT h
            (mk_watched_frame authority sGamma rGamma) stack) loc_x.
      { eapply typed_mut_root_is_live_capability.
        exists x, Tx'. repeat split; assumption. }
      have Hwritten_live : In Loc
          (live_capability_set CT h
            (mk_watched_frame authority sGamma rGamma) stack) written.
      { eapply typed_mut_root_is_live_capability.
        exists y, Ty. repeat split; assumption. }
      eapply potential_colors_after_m_colored_field_update
        with (M := live_capability_set CT h
          (mk_watched_frame authority sGamma rGamma) stack).
      * exact Hobj.
      * intros location Hlocation.
        eapply live_capability_reachable_after_field_update_if_written_live;
          [exact Hobj| |exact Hlocation].
        intros candidate Hcandidate. injection Hcandidate as <-.
        exact Hwritten_live.
      * exact Hloc_x_live.
      * exact Hwritten_live.
      * exact Hpotential.
    + eapply potential_colors_after_graph_reflection
        with (M := live_capability_set CT h
          (mk_watched_frame authority sGamma rGamma) stack).
      * intros location Hlocation.
        eapply live_capability_after_non_rdm_field_update_is_old
          with (C := sctype Tx) (fieldT := fieldT); eauto; discriminate.
      * intros left right Hconnected.
        eapply potential_connected_after_non_rdm_field_update_is_old
          with (C := sctype Tx) (fieldT := fieldT); eauto; discriminate.
      * exact Hpotential.
    + destruct (typed_runtime_rdm_field_write_subtyping CT sGamma mt rGamma
        h x field y loc_x o (sctype Tx) fieldT sGamma Hwf Htyping Hscope
        Hval_x Hobj Hruntime_base Hfield_definition Hfield_mutability) as
        [Tx' [Ty [Hgetx' [Hgety Hsub]]]].
      have Hendpoint_shapes := safe_rdm_write_endpoint_qualifiers CT sGamma
        rGamma h x y loc_x written Tx' Ty
        (f_base_type (ftype fieldT)) Hwf Hgetx' Hgety Hval_x Hval_y Hsub.
      destruct Hendpoint_shapes as
        [[Hreceiver_mut Hvalue_mut] |
          [[Hreceiver_imm Hvalue_imm] | [Hreceiver_rdm Hvalue_rdm]]].
      * have Hloc_x_live : In Loc
          (live_capability_set CT h
            (mk_watched_frame authority sGamma rGamma) stack) loc_x.
        { eapply typed_mut_root_is_live_capability.
          exists x, Tx'. repeat split; assumption. }
        have Hwritten_live : In Loc
          (live_capability_set CT h
            (mk_watched_frame authority sGamma rGamma) stack) written.
        { eapply typed_mut_root_is_live_capability.
          exists y, Ty. repeat split; assumption. }
        eapply potential_colors_after_m_colored_field_update
          with (M := live_capability_set CT h
            (mk_watched_frame authority sGamma rGamma) stack).
        -- exact Hobj.
        -- intros location Hlocation.
           eapply live_capability_reachable_after_field_update_if_written_live;
             [exact Hobj| |exact Hlocation].
           intros candidate Hcandidate. injection Hcandidate as <-.
           exact Hwritten_live.
        -- exact Hloc_x_live.
        -- exact Hwritten_live.
        -- exact Hpotential.
      * have Hloc_x_immutable : r_muttype h loc_x = Some Imm_r.
        { eapply typed_imm_root_runtime_immutable; [exact Hwf|].
          exists x, Tx'. repeat split; assumption. }
        have Hwritten_immutable : r_muttype h written = Some Imm_r.
        { eapply typed_imm_root_runtime_immutable; [exact Hwf|].
          exists y, Ty. repeat split; assumption. }
        eapply potential_colors_after_immutable_field_update; eauto.
	      * have Hredundant : potential_connected CT h
          (mk_watched_frame authority sGamma rGamma) stack loc_x written.
        { eapply live_frame_rdm_roots_potentially_connected
            with (frame := mk_watched_frame authority sGamma rGamma).
          - constructor.
          - exists x, Tx'. repeat split; assumption.
	          - exists y, Ty. repeat split; assumption. }
	        have Hredundant_reverse : potential_connected CT h
	          (mk_watched_frame authority sGamma rGamma) stack written loc_x.
	        { eapply live_frame_rdm_roots_potentially_connected
	            with (frame := mk_watched_frame authority sGamma rGamma).
	          - constructor.
	          - exists y, Ty. repeat split; assumption.
	          - exists x, Tx'. repeat split; assumption. }
	        eapply potential_colors_after_redundant_field_update
          with (M := live_capability_set CT h
            (mk_watched_frame authority sGamma rGamma) stack).
        -- exact Hobj.
	        -- exact Hredundant.
	        -- exact Hredundant_reverse.
	        -- intros location Hlocation.
           eapply live_capability_after_redundant_field_update_has_old_potential_origin;
             eauto.
        -- exact Hpotential.
    + eapply potential_colors_after_graph_reflection
        with (M := live_capability_set CT h
          (mk_watched_frame authority sGamma rGamma) stack).
      * intros location Hlocation.
        eapply live_capability_after_non_rdm_field_update_is_old
          with (C := sctype Tx) (fieldT := fieldT); eauto; discriminate.
      * intros left right Hconnected.
        eapply potential_connected_after_non_rdm_field_update_is_old
          with (C := sctype Tx) (fieldT := fieldT); eauto; discriminate.
      * exact Hpotential.
  }
  split.
  - eapply live_history_after_field_write_given_potential; eauto.
  - exact Hpotential_post.
Qed.

(** At an RDM-view call, a fresh callee RDM result may later be installed in
    the suspended caller.  Besides ordinary active-frame creation roots, the
    allocation normal form must therefore include an immediate suspended-caller
    RDM root as an anchor. *)
Definition immediate_rdm_caller_root
  (h : heap) (active : watched_frame) (stack : list watched_boundary)
  (root : Loc) : Prop :=
  exists boundary tail,
    stack = boundary :: tail /\
    boundary.(boundary_receiver_view) = RDM /\
    typed_root RDM boundary.(boundary_caller).(frame_senv)
      boundary.(boundary_caller).(frame_renv) root /\
    (forall active_root,
      typed_root RDM active.(frame_senv) active.(frame_renv) active_root ->
      r_muttype h active_root = r_muttype h root).

(** An attachment to a freshly allocated component is represented by the
    fresh location, an old active creation-view root, or (only for RDM
    creation) an immediate suspended-caller RDM root, followed by an old
    potential path. *)
Definition potential_new_attachment
  (CT : class_table) (h : heap) (active : watched_frame)
  (stack : list watched_boundary) (qc : q_c) (root : Loc) : Prop :=
  exists anchor,
    (anchor = dom h \/
     typed_root (qc2q qc) active.(frame_senv) active.(frame_renv) anchor \/
     typed_root Mut active.(frame_senv) active.(frame_renv) anchor \/
     (qc = RDM_c /\ immediate_rdm_caller_root h active stack anchor)) /\
    potential_connected CT h active stack anchor root.

(** The dual, direction-sensitive provenance used at the left endpoint of a
    path that crosses a freshly allocated object.  Unlike
    [potential_new_attachment], the old creation anchor is reached *from* the
    endpoint.  Keeping the two directions separate is essential once explicit
    [Mut] fields are forward-only. *)
Definition potential_new_entry
  (CT : class_table) (h : heap) (active : watched_frame)
  (stack : list watched_boundary) (qc : q_c) (root : Loc) : Prop :=
  exists anchor,
    (anchor = dom h \/
     typed_root (qc2q qc) active.(frame_senv) active.(frame_renv) anchor \/
     (qc = RDM_c /\ immediate_rdm_caller_root h active stack anchor)) /\
    potential_connected CT h active stack root anchor.

Lemma potential_new_entry_fresh :
  forall CT h active stack qc,
    potential_new_entry CT h active stack qc (dom h).
Proof.
  intros. exists (dom h). split; [left; reflexivity|apply rt_refl].
Qed.

Lemma potential_new_entry_typed_root :
  forall CT h active stack qc root,
    typed_root (qc2q qc) active.(frame_senv) active.(frame_renv) root ->
    potential_new_entry CT h active stack qc root.
Proof.
  intros. exists root. split; [right; left; assumption|apply rt_refl].
Qed.

Lemma potential_new_entry_caller_rdm_root :
  forall CT h active stack root,
    immediate_rdm_caller_root h active stack root ->
    potential_new_entry CT h active stack RDM_c root.
Proof.
  intros CT h active stack root Hcaller. exists root. split.
	  - exact (or_intror (or_intror (conj eq_refl Hcaller))).
  - apply rt_refl.
Qed.

Lemma potential_new_attachment_fresh :
  forall CT h active stack qc,
    potential_new_attachment CT h active stack qc (dom h).
Proof.
  intros. exists (dom h). split; [left; reflexivity|apply rt_refl].
Qed.

Lemma potential_new_attachment_typed_root :
  forall CT h active stack qc root,
    typed_root (qc2q qc) active.(frame_senv) active.(frame_renv) root ->
    potential_new_attachment CT h active stack qc root.
Proof.
  intros. exists root. split; [right; left; assumption|apply rt_refl].
Qed.

Lemma potential_new_attachment_mut_root :
  forall CT h active stack qc root,
    typed_root Mut active.(frame_senv) active.(frame_renv) root ->
    potential_new_attachment CT h active stack qc root.
Proof.
  intros. exists root. split; [right; right; left; assumption|apply rt_refl].
Qed.

Lemma potential_new_attachment_caller_rdm_root :
  forall CT h active stack root,
    immediate_rdm_caller_root h active stack root ->
    potential_new_attachment CT h active stack RDM_c root.
Proof.
  intros. exists root. split.
  - right. right. right. split; [reflexivity|assumption].
  - apply rt_refl.
Qed.

Lemma immediate_rdm_caller_root_live_under_mut_authority :
  forall CT h sGamma rGamma stack root,
    live_stack_authorities_chain Mut_r stack ->
    immediate_rdm_caller_root h
      (mk_watched_frame Mut_r sGamma rGamma) stack root ->
    In Loc (live_capability_set CT h
      (mk_watched_frame Mut_r sGamma rGamma) stack) root.
Proof.
  intros CT h sGamma rGamma stack root Hchain
    [boundary [tail [Hstack [Hview [Hroot Hcompat]]]]].
  subst stack. simpl in Hchain. destruct Hchain as [Hauthority Htail].
  rewrite Hview in Hauthority. simpl in Hauthority.
  exists root. split.
  - right. exists boundary. split; [left; reflexivity|].
    destruct Hroot as [variable [T [Htype [Hvalue Hrdm]]]].
    exists variable, T. repeat split; try assumption.
    unfold capability_in_context. right. split; [exact Hrdm|].
    symmetry. exact Hauthority.
  - constructor.
Qed.

Lemma active_and_immediate_rdm_roots_potentially_connected :
  forall CT h active stack active_root caller_root,
    typed_root RDM active.(frame_senv) active.(frame_renv) active_root ->
    immediate_rdm_caller_root h active stack caller_root ->
    potential_connected CT h active stack active_root caller_root.
Proof.
  intros CT h active stack active_root caller_root Hactive
    [boundary [tail [Hstack [Hview [Hcaller Hcompat]]]]].
  subst stack. apply rt_step. right. right. exists active, boundary.
  split; [constructor|]. split; [exact Hview|].
  split; [apply Hcompat; exact Hactive|].
  left. split; assumption.
Qed.

Lemma immediate_and_active_rdm_roots_potentially_connected :
  forall CT h active stack caller_root active_root,
    immediate_rdm_caller_root h active stack caller_root ->
    typed_root RDM active.(frame_senv) active.(frame_renv) active_root ->
    potential_connected CT h active stack caller_root active_root.
Proof.
  intros CT h active stack caller_root active_root
    [boundary [tail [Hstack [Hview [Hcaller Hcompat]]]]] Hactive.
  subst stack. apply rt_step. right. right. exists active, boundary.
  split; [constructor|]. split; [exact Hview|].
  split; [symmetry; apply Hcompat; exact Hactive|].
  right. split; assumption.
Qed.

Lemma immediate_rdm_caller_roots_potentially_connected :
  forall CT h active stack left right,
    immediate_rdm_caller_root h active stack left ->
    immediate_rdm_caller_root h active stack right ->
    potential_connected CT h active stack left right.
Proof.
  intros CT h active stack left right
    [left_boundary [left_tail [Hleft_stack [Hleft_view
      [Hleft_root Hleft_compat]]]]]
    [right_boundary [right_tail [Hright_stack [Hright_view
      [Hright_root Hright_compat]]]]].
  subst stack. injection Hright_stack as Hboundary_eq Htail_eq.
  subst right_boundary right_tail.
  eapply live_frame_rdm_roots_potentially_connected with
    (frame := left_boundary.(boundary_caller)).
  - constructor. left. reflexivity.
  - exact Hleft_root.
  - exact Hright_root.
Qed.

Lemma immediate_rdm_caller_root_dom :
  forall CT h active stack root,
    live_frames_wf CT h active stack ->
    immediate_rdm_caller_root h active stack root ->
    root < dom h.
Proof.
  intros CT h active stack root Hframes
    [boundary [tail [Hstack [Hview [Hroot Hcompat]]]]].
  subst stack.
  assert (Hcaller_live : live_frame_member active (boundary :: tail)
      boundary.(boundary_caller)).
  { constructor. left. reflexivity. }
  have Hcaller_wf := live_frame_member_wf CT h active (boundary :: tail)
    boundary.(boundary_caller) Hframes Hcaller_live.
  destruct Hroot as [variable [T [Htype [Hvalue Hrdm]]]].
  eapply wf_config_value_dom; eauto.
Qed.

Lemma rdm_creation_anchors_potentially_connected :
  forall CT h active stack left right,
    (typed_root RDM active.(frame_senv) active.(frame_renv) left \/
     immediate_rdm_caller_root h active stack left) ->
    (typed_root RDM active.(frame_senv) active.(frame_renv) right \/
     immediate_rdm_caller_root h active stack right) ->
    potential_connected CT h active stack left right.
Proof.
  intros CT h active stack left right [Hleft | Hleft] [Hright | Hright].
  - eapply live_frame_rdm_roots_potentially_connected with (frame := active).
    + constructor.
    + exact Hleft.
    + exact Hright.
  - eapply active_and_immediate_rdm_roots_potentially_connected; eauto.
  - eapply immediate_and_active_rdm_roots_potentially_connected; eauto.
  - eapply immediate_rdm_caller_roots_potentially_connected; eauto.
Qed.

Lemma potential_new_attachment_transport :
  forall CT h active stack qc first second,
    potential_new_attachment CT h active stack qc first ->
    potential_connected CT h active stack first second ->
    potential_new_attachment CT h active stack qc second.
Proof.
  intros CT h active stack qc first second
    [anchor [Hanchor Hanchor_first]] Hfirst_second.
  exists anchor. split; [exact Hanchor|].
  eapply potential_connected_trans; eauto.
Qed.

Lemma potential_new_entry_transport :
  forall CT h active stack qc first second,
    potential_connected CT h active stack first second ->
    potential_new_entry CT h active stack qc second ->
    potential_new_entry CT h active stack qc first.
Proof.
  intros CT h active stack qc first second Hfirst_second
    [anchor [Hanchor Hsecond_anchor]].
  exists anchor. split; [exact Hanchor|].
  eapply potential_connected_trans; eauto.
Qed.


Lemma fresh_retained_edge_target_is_potential_attachment :
  forall CT sGamma mt rGamma h x qc C args sGamma' vals qruntime
    authority stack target,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    retained_mut_edge CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) (dom h) target ->
    potential_new_attachment CT h
      (mk_watched_frame authority sGamma rGamma) stack qc target.
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' vals qruntime
    authority stack target Hwf Htyping Hvals Hedge.
  destruct (retained_edge_after_append CT h
    (mkObj (mkruntime_type qruntime C) vals) (dom h) target Hedge) as
    [Hold | [Hfresh [field [D [fdef [Hfield [Hsub [Hfd
      [Hrdm | Hmut]]]]]]]]].
  - inversion Hold as [? ? Hrdm_edge | ? ? oldobj ? ? ? Hobj]; subst.
    + inversion Hrdm_edge as [? ? oldobj ? ? ? Hobj].
      apply runtime_getObj_dom in Hobj. lia.
    + apply runtime_getObj_dom in Hobj. lia.
  - assert (HfdC : sf_def_rel CT C field fdef).
    { eapply field_inheritance_subtyping; eauto. }
    have Hroot := new_creation_rdm_field_target_has_creation_root
      CT sGamma mt rGamma h x qc C args sGamma' vals field fdef target
      Hwf Htyping Hvals Hfield HfdC Hrdm.
    eapply potential_new_attachment_typed_root; exact Hroot.
  - assert (HfdC : sf_def_rel CT C field fdef).
    { eapply field_inheritance_subtyping; eauto. }
    have Hroot := new_creation_mut_field_target_has_mut_root
      CT sGamma mt rGamma h x qc C args sGamma' vals field fdef target
      Hwf Htyping Hvals Hfield HfdC Hmut.
    eapply potential_new_attachment_mut_root; exact Hroot.
Qed.

Lemma fresh_mutable_edge_target_is_potential_entry :
  forall CT sGamma mt rGamma h x qc C args sGamma' vals qruntime
    authority stack target,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    mutable_edge CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) (dom h) target ->
    potential_new_entry CT h
      (mk_watched_frame authority sGamma rGamma) stack qc target.
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' vals qruntime
    authority stack target Hwf Htyping Hvals Hedge.
  destruct (mutable_edge_after_append CT h
    (mkObj (mkruntime_type qruntime C) vals) (dom h) target Hedge) as
    [Hold | [Hfresh [field [D [fieldT [Hfield [Hbase [Hdef Hrdm]]]]]]]].
  - inversion Hold as [? ? oldobj ? ? ? Hobj].
    apply runtime_getObj_dom in Hobj. lia.
	  - assert (HdefC : sf_def_rel CT C field fieldT).
	    { eapply field_inheritance_subtyping; eauto. }
	    have Hroot := new_creation_rdm_field_target_has_creation_root
	      CT sGamma mt rGamma h x qc C args sGamma' vals field
	      fieldT target Hwf Htyping Hvals Hfield HdefC Hrdm.
    eapply potential_new_entry_typed_root; exact Hroot.
Qed.

Lemma potential_adjacent_after_new :
  forall CT sGamma mt rGamma h x qc C args sGamma' vals qruntime
    authority stack left right,
    wf_r_config CT sGamma rGamma h ->
    live_frames_wf CT h
      (mk_watched_frame authority sGamma rGamma) stack ->
    (qc = RDM_c -> exists receiver,
      runtime_getVal rGamma 0 = Some (Iot receiver) /\
      r_muttype h receiver = Some qruntime) ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    potential_adjacent CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h)))) stack left right ->
    potential_connected CT h
      (mk_watched_frame authority sGamma rGamma) stack left right \/
    (potential_new_entry CT h
       (mk_watched_frame authority sGamma rGamma) stack qc left /\
     potential_new_attachment CT h
       (mk_watched_frame authority sGamma rGamma) stack qc right).
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' vals qruntime
    authority stack left right Hwf Hframes Hrdm_runtime Htyping Hvals
    [Hheap | [Hframe | Hreturn]].
  - destruct Hheap as [Hforward | Hbackward].
    + destruct (retained_edge_after_append CT h
        (mkObj (mkruntime_type qruntime C) vals) left right Hforward) as
        [Hold | [Hfresh Hnew]].
      * left. apply rt_step. left. left. exact Hold.
      * subst left. right. split.
        -- apply potential_new_entry_fresh.
        -- eapply fresh_retained_edge_target_is_potential_attachment; eauto.
    + destruct (mutable_edge_after_append CT h
        (mkObj (mkruntime_type qruntime C) vals) right left Hbackward) as
        [Hold | [Hfresh Hnew]].
      * left. apply rt_step. left. right. exact Hold.
	      * subst right. right. split.
	        -- eapply fresh_mutable_edge_target_is_potential_entry; eauto.
	        -- apply potential_new_attachment_fresh.
  - destruct Hframe as [frame [Hlive [Hleft Hright]]].
    inversion Hlive; subst.
    + destruct (new_active_rdm_root_origin CT sGamma mt rGamma h x qc C
        args sGamma' left Hwf Htyping Hleft) as
        [Hleft_old | [Hleft_fresh Hleft_qc]];
      destruct (new_active_rdm_root_origin CT sGamma mt rGamma h x qc C
        args sGamma' right Hwf Htyping Hright) as
        [Hright_old | [Hright_fresh Hright_qc]].
      * left. eapply live_frame_rdm_roots_potentially_connected
          with (frame := mk_watched_frame authority sGamma rGamma).
        -- constructor.
        -- exact Hleft_old.
        -- exact Hright_old.
      * subst qc. right. split.
	        -- apply potential_new_entry_typed_root. exact Hleft_old.
        -- subst right. apply potential_new_attachment_fresh.
      * subst qc. right. split.
	        -- subst left. apply potential_new_entry_fresh.
        -- apply potential_new_attachment_typed_root. exact Hright_old.
      * right. split.
	        -- subst left. apply potential_new_entry_fresh.
        -- subst right. apply potential_new_attachment_fresh.
    + left. apply rt_step. right. left. exists boundary.(boundary_caller).
      repeat split; try assumption. constructor. exact H.
  - destruct Hreturn as
      [callee [boundary [Hboundary [Hview [Hruntime [Hroots | Hroots]]]]]].
    + inversion Hboundary; subst.
      * destruct (new_active_rdm_root_origin CT sGamma mt rGamma h x qc C
          args sGamma' left Hwf Htyping (proj1 Hroots)) as
          [Hleft_old | [Hleft_fresh Hleft_qc]].
        -- have Hleft_dom : left < dom h.
           { destruct Hleft_old as
               [variable [T [Htype [Hvalue Hrdm]]]].
             eapply wf_config_value_dom; eauto. }
           assert (Hcaller_live : live_frame_member
             (mk_watched_frame authority sGamma rGamma) (boundary :: tail)
             boundary.(boundary_caller)).
           { constructor. simpl. auto. }
           have Hcaller_wf := live_frame_member_wf CT h
             (mk_watched_frame authority sGamma rGamma) (boundary :: tail)
             boundary.(boundary_caller) Hframes Hcaller_live.
           destruct (proj2 Hroots) as
             [variable [T [Htype [Hvalue Hrdm]]]].
           have Hright_dom : right < dom h :=
             wf_config_value_dom CT _ _ h variable right Hcaller_wf Hvalue.
           rewrite (r_muttype_app_preserve_old h
             (mkObj (mkruntime_type qruntime C) vals) left Hleft_dom) in Hruntime.
           rewrite (r_muttype_app_preserve_old h
             (mkObj (mkruntime_type qruntime C) vals) right Hright_dom) in Hruntime.
           left. apply rt_step. right. right.
           exists (mk_watched_frame authority sGamma rGamma), boundary.
           split; [constructor|]. split; [exact Hview|].
           split; [exact Hruntime|]. left. split.
           ++ exact Hleft_old.
           ++ exists variable, T. repeat split; assumption.
        -- subst left. subst qc. right. split.
	           ++ apply potential_new_entry_fresh.
	           ++ apply potential_new_attachment_caller_rdm_root.
              exists boundary, tail. split; [reflexivity|].
              split; [exact Hview|]. split; [exact (proj2 Hroots)|].
              intros active_root Hactive_root.
              destruct (Hrdm_runtime eq_refl) as
                [receiver [Hreceiver Hreceiver_runtime]].
              have Hactive_runtime := typed_rdm_root_matches_receiver_runtime
                CT sGamma rGamma h receiver qruntime active_root Hwf Hreceiver
                Hreceiver_runtime Hactive_root.
              assert (Hcaller_live : live_frame_member
                (mk_watched_frame authority sGamma rGamma) (boundary :: tail)
                boundary.(boundary_caller)).
              { constructor. simpl. auto. }
              have Hcaller_wf := live_frame_member_wf CT h
                (mk_watched_frame authority sGamma rGamma) (boundary :: tail)
                boundary.(boundary_caller) Hframes Hcaller_live.
              destruct (proj2 Hroots) as
                [variable [T [Htype [Hvalue Hrdm]]]].
              have Hright_dom : right < dom h := wf_config_value_dom CT _ _ h
                variable right Hcaller_wf Hvalue.
              assert (Hfresh_runtime : r_muttype
                (h ++ [mkObj (mkruntime_type qruntime C) vals]) (dom h) =
                Some qruntime).
              { unfold r_muttype, r_type. rewrite runtime_getObj_last.
                reflexivity. }
              rewrite Hfresh_runtime in Hruntime.
              rewrite (r_muttype_app_preserve_old h
                (mkObj (mkruntime_type qruntime C) vals) right Hright_dom)
                in Hruntime.
              rewrite Hactive_runtime. rewrite Hruntime. reflexivity.
      * have Hcallee_live := live_call_boundary_callee_is_live _ _ _ _ H.
        have Hcaller_live := live_call_boundary_caller_is_live _ _ _ _ H.
        have Hcallee_wf := live_frame_member_wf CT h
          (mk_watched_frame authority sGamma rGamma) (head :: tail)
          callee Hframes (live_frame_member_under_suspended_head
            (mk_watched_frame authority sGamma rGamma) head tail callee
            Hcallee_live).
        have Hcaller_wf := live_frame_member_wf CT h
          (mk_watched_frame authority sGamma rGamma) (head :: tail)
          boundary.(boundary_caller) Hframes
          (live_frame_member_under_suspended_head
            (mk_watched_frame authority sGamma rGamma) head tail
            boundary.(boundary_caller) Hcaller_live).
        destruct (proj1 Hroots) as
          [left_var [left_T [Hleft_type [Hleft_value Hleft_rdm]]]].
        destruct (proj2 Hroots) as
          [right_var [right_T [Hright_type [Hright_value Hright_rdm]]]].
        have Hleft_dom : left < dom h := wf_config_value_dom CT _ _ h
          left_var left Hcallee_wf Hleft_value.
        have Hright_dom : right < dom h := wf_config_value_dom CT _ _ h
          right_var right Hcaller_wf Hright_value.
        rewrite (r_muttype_app_preserve_old h
          (mkObj (mkruntime_type qruntime C) vals) left Hleft_dom) in Hruntime.
        rewrite (r_muttype_app_preserve_old h
          (mkObj (mkruntime_type qruntime C) vals) right Hright_dom) in Hruntime.
        left. apply rt_step. right. right. exists callee, boundary.
        split; [constructor; exact H|]. split; [exact Hview|].
        split; [exact Hruntime|]. left. split.
        -- exists left_var, left_T. repeat split; assumption.
        -- exists right_var, right_T. repeat split; assumption.
    + inversion Hboundary; subst.
      * destruct (new_active_rdm_root_origin CT sGamma mt rGamma h x qc C
          args sGamma' right Hwf Htyping (proj2 Hroots)) as
          [Hright_old | [Hright_fresh Hright_qc]].
        -- have Hright_dom : right < dom h.
           { destruct Hright_old as
               [variable [T [Htype [Hvalue Hrdm]]]].
             eapply wf_config_value_dom; eauto. }
           assert (Hcaller_live : live_frame_member
             (mk_watched_frame authority sGamma rGamma) (boundary :: tail)
             boundary.(boundary_caller)).
           { constructor. simpl. auto. }
           have Hcaller_wf := live_frame_member_wf CT h
             (mk_watched_frame authority sGamma rGamma) (boundary :: tail)
             boundary.(boundary_caller) Hframes Hcaller_live.
           destruct (proj1 Hroots) as
             [variable [T [Htype [Hvalue Hrdm]]]].
           have Hleft_dom : left < dom h :=
             wf_config_value_dom CT _ _ h variable left Hcaller_wf Hvalue.
           rewrite (r_muttype_app_preserve_old h
             (mkObj (mkruntime_type qruntime C) vals) left Hleft_dom) in Hruntime.
           rewrite (r_muttype_app_preserve_old h
             (mkObj (mkruntime_type qruntime C) vals) right Hright_dom) in Hruntime.
           left. apply rt_step. right. right.
           exists (mk_watched_frame authority sGamma rGamma), boundary.
           split; [constructor|]. split; [exact Hview|].
           split; [exact Hruntime|]. right. split.
           ++ exists variable, T. repeat split; assumption.
           ++ exact Hright_old.
        -- subst right. subst qc. right. split.
	           ++ apply potential_new_entry_caller_rdm_root.
              exists boundary, tail. split; [reflexivity|].
              split; [exact Hview|]. split; [exact (proj1 Hroots)|].
              intros active_root Hactive_root.
              destruct (Hrdm_runtime eq_refl) as
                [receiver [Hreceiver Hreceiver_runtime]].
              have Hactive_runtime := typed_rdm_root_matches_receiver_runtime
                CT sGamma rGamma h receiver qruntime active_root Hwf Hreceiver
                Hreceiver_runtime Hactive_root.
              assert (Hcaller_live : live_frame_member
                (mk_watched_frame authority sGamma rGamma) (boundary :: tail)
                boundary.(boundary_caller)).
              { constructor. simpl. auto. }
              have Hcaller_wf := live_frame_member_wf CT h
                (mk_watched_frame authority sGamma rGamma) (boundary :: tail)
                boundary.(boundary_caller) Hframes Hcaller_live.
              destruct (proj1 Hroots) as
                [variable [T [Htype [Hvalue Hrdm]]]].
              have Hleft_dom : left < dom h := wf_config_value_dom CT _ _ h
                variable left Hcaller_wf Hvalue.
              assert (Hfresh_runtime : r_muttype
                (h ++ [mkObj (mkruntime_type qruntime C) vals]) (dom h) =
                Some qruntime).
              { unfold r_muttype, r_type. rewrite runtime_getObj_last.
                reflexivity. }
              rewrite Hfresh_runtime in Hruntime.
              rewrite (r_muttype_app_preserve_old h
                (mkObj (mkruntime_type qruntime C) vals) left Hleft_dom)
                in Hruntime.
              rewrite Hactive_runtime. rewrite Hruntime. reflexivity.
           ++ apply potential_new_attachment_fresh.
      * have Hcallee_live := live_call_boundary_callee_is_live _ _ _ _ H.
        have Hcaller_live := live_call_boundary_caller_is_live _ _ _ _ H.
        have Hcallee_wf := live_frame_member_wf CT h
          (mk_watched_frame authority sGamma rGamma) (head :: tail) callee
          Hframes (live_frame_member_under_suspended_head
            (mk_watched_frame authority sGamma rGamma) head tail callee
            Hcallee_live).
        have Hcaller_wf := live_frame_member_wf CT h
          (mk_watched_frame authority sGamma rGamma) (head :: tail)
          boundary.(boundary_caller) Hframes
          (live_frame_member_under_suspended_head
            (mk_watched_frame authority sGamma rGamma) head tail
            boundary.(boundary_caller) Hcaller_live).
        destruct (proj1 Hroots) as
          [left_var [left_T [Hleft_type [Hleft_value Hleft_rdm]]]].
        destruct (proj2 Hroots) as
          [right_var [right_T [Hright_type [Hright_value Hright_rdm]]]].
        have Hleft_dom : left < dom h := wf_config_value_dom CT _ _ h
          left_var left Hcaller_wf Hleft_value.
        have Hright_dom : right < dom h := wf_config_value_dom CT _ _ h
          right_var right Hcallee_wf Hright_value.
        rewrite (r_muttype_app_preserve_old h
          (mkObj (mkruntime_type qruntime C) vals) left Hleft_dom) in Hruntime.
        rewrite (r_muttype_app_preserve_old h
          (mkObj (mkruntime_type qruntime C) vals) right Hright_dom) in Hruntime.
        left. apply rt_step. right. right. exists callee, boundary.
        split; [constructor; exact H|]. split; [exact Hview|].
        split; [exact Hruntime|]. right. split.
        -- exists left_var, left_T. repeat split; assumption.
        -- exists right_var, right_T. repeat split; assumption.
Qed.

Lemma potential_connected_after_new :
  forall CT sGamma mt rGamma h x qc C args sGamma' vals qruntime
    authority stack left right,
    wf_r_config CT sGamma rGamma h ->
    live_frames_wf CT h
      (mk_watched_frame authority sGamma rGamma) stack ->
    (qc = RDM_c -> exists receiver,
      runtime_getVal rGamma 0 = Some (Iot receiver) /\
      r_muttype h receiver = Some qruntime) ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    potential_connected CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h)))) stack left right ->
    potential_connected CT h
      (mk_watched_frame authority sGamma rGamma) stack left right \/
    (potential_new_entry CT h
       (mk_watched_frame authority sGamma rGamma) stack qc left /\
     potential_new_attachment CT h
       (mk_watched_frame authority sGamma rGamma) stack qc right).
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' vals qruntime
    authority stack left right Hwf Hframes Hrdm_runtime Htyping Hvals
    Hconnected.
  induction Hconnected.
  - destruct (potential_adjacent_after_new CT sGamma mt rGamma h x qc C args
      sGamma' vals qruntime authority stack x0 y Hwf Hframes Hrdm_runtime
      Htyping Hvals H) as [Hold | [Hleft Hright]].
    + left. exact Hold.
    + right. split; assumption.
  - left. apply rt_refl.
  - destruct IHHconnected1 as [Hxy | [Hentry_x Hattach_y]];
      destruct IHHconnected2 as [Hyz | [Hentry_y Hattach_z]].
    + left. eapply potential_connected_trans; eauto.
    + right. split.
      * eapply potential_new_entry_transport; eauto.
      * exact Hattach_z.
    + right. split.
      * exact Hentry_x.
      * eapply potential_new_attachment_transport; eauto.
    + right. split; assumption.
Qed.

Lemma potential_adjacent_left_dom :
  forall CT h active stack left right,
    live_frames_wf CT h active stack ->
    potential_adjacent CT h active stack left right ->
    left < dom h.
Proof.
  intros CT h active stack left right Hframes
    [Hheap | [Hframe | Hreturn]].
  - have Hheap_wf : wf_heap CT h := proj1 (proj2 (proj1 Hframes)).
    destruct Hheap as [Hforward | Hbackward].
    + inversion Hforward as
        [? ? Hrdm_edge | ? ? object field D fieldT Hobject Hsource_mut
          Hfield Hbase Hfield_definition Hmut]; subst.
      * inversion Hrdm_edge as
          [? ? object field D fieldT Hobject Hfield Hbase Hfield_definition
            Hrdm]; subst.
        apply runtime_getObj_dom in Hobject. exact Hobject.
      * apply runtime_getObj_dom in Hobject. exact Hobject.
	    + eapply mutable_edge_target_dom; eauto.
  - destruct Hframe as [frame [Hlive [Hleft Hright]]].
    have Hframe_wf := live_frame_member_wf CT h active stack frame Hframes
      Hlive.
    destruct Hleft as [variable [T [Htype [Hvalue Hrdm]]]].
    eapply wf_config_value_dom; eauto.
  - destruct Hreturn as
      [callee [boundary [Hlive [Hview [Hruntime [Hroots | Hroots]]]]]].
    + have Hcallee_live := live_call_boundary_callee_is_live _ _ _ _ Hlive.
      have Hcallee_wf := live_frame_member_wf CT h active stack callee Hframes
        Hcallee_live.
      destruct (proj1 Hroots) as
        [variable [T [Htype [Hvalue Hrdm]]]].
      eapply wf_config_value_dom; eauto.
    + have Hcaller_live := live_call_boundary_caller_is_live _ _ _ _ Hlive.
      have Hcaller_wf := live_frame_member_wf CT h active stack
        boundary.(boundary_caller) Hframes Hcaller_live.
      destruct (proj1 Hroots) as
        [variable [T [Htype [Hvalue Hrdm]]]].
      eapply wf_config_value_dom; eauto.
Qed.

Lemma potential_connected_left_dom_from_right :
  forall CT h active stack left right,
    live_frames_wf CT h active stack ->
    potential_connected CT h active stack left right ->
    right < dom h ->
    left < dom h.
Proof.
  intros CT h active stack left right Hframes Hconnected.
  induction Hconnected; intros Hright_dom.
  - eapply potential_adjacent_left_dom; eauto.
  - exact Hright_dom.
  - apply IHHconnected1. apply IHHconnected2. exact Hright_dom.
Qed.

Lemma potential_connected_from_fresh_is_fresh :
  forall CT h active stack target,
    live_frames_wf CT h active stack ->
    potential_connected CT h active stack (dom h) target ->
    target = dom h.
Proof.
  intros CT h active stack target Hframes Hconnected.
  remember (dom h) as fresh eqn:Hfresh in Hconnected |- *.
  induction Hconnected.
  - subst x. have Hdom := potential_adjacent_left_dom CT h active stack
      (dom h) y Hframes H. lia.
  - reflexivity.
  - have Hyx := IHHconnected1 Hfresh.
    assert (Hydom : y = dom h).
    { rewrite Hyx. exact Hfresh. }
    have Hzy := IHHconnected2 Hydom.
    rewrite Hzy. rewrite Hyx. reflexivity.
Qed.

Lemma potential_adjacent_right_dom :
  forall CT h active stack left right,
    live_frames_wf CT h active stack ->
    potential_adjacent CT h active stack left right ->
    right < dom h.
Proof.
  intros CT h active stack left right Hframes
    [Hheap | [Hframe | Hreturn]].
  - have Hheap_wf : wf_heap CT h := proj1 (proj2 (proj1 Hframes)).
    destruct Hheap as [Hforward | Hbackward].
    + eapply retained_edge_target_dom; eauto.
    + inversion Hbackward as
        [? ? object field D fieldT Hobject Hfield Hbase Hdefinition Hrdm];
        subst.
      apply runtime_getObj_dom in Hobject. exact Hobject.
  - destruct Hframe as [frame [Hlive [Hleft Hright]]].
    have Hframe_wf := live_frame_member_wf CT h active stack frame Hframes
      Hlive.
    destruct Hright as [variable [T [Htype [Hvalue Hrdm]]]].
    eapply wf_config_value_dom; eauto.
  - destruct Hreturn as
      [callee [boundary [Hlive [Hview [Hruntime [Hroots | Hroots]]]]]].
    + have Hcaller_live := live_call_boundary_caller_is_live _ _ _ _ Hlive.
      have Hcaller_wf := live_frame_member_wf CT h active stack
        boundary.(boundary_caller) Hframes Hcaller_live.
      destruct (proj2 Hroots) as
        [variable [T [Htype [Hvalue Hrdm]]]].
      eapply wf_config_value_dom; eauto.
    + have Hcallee_live := live_call_boundary_callee_is_live _ _ _ _ Hlive.
      have Hcallee_wf := live_frame_member_wf CT h active stack callee Hframes
        Hcallee_live.
      destruct (proj2 Hroots) as
        [variable [T [Htype [Hvalue Hrdm]]]].
      eapply wf_config_value_dom; eauto.
Qed.

Lemma potential_connected_to_fresh_is_fresh :
  forall CT h active stack source,
    live_frames_wf CT h active stack ->
    potential_connected CT h active stack source (dom h) ->
    source = dom h.
Proof.
  intros CT h active stack source Hframes Hconnected.
  remember (dom h) as fresh eqn:Hfresh in Hconnected |- *.
  induction Hconnected.
  - subst y. have Hdom := potential_adjacent_right_dom CT h active stack
      x (dom h) Hframes H. lia.
  - reflexivity.
  - have Hzy := IHHconnected2 Hfresh.
    assert (Hydom : y = dom h).
    { rewrite Hzy. exact Hfresh. }
    have Hyx := IHHconnected1 Hydom.
    etransitivity; [exact Hyx|exact Hzy].
Qed.

Lemma potential_new_attachment_to_old_has_typed_anchor :
  forall CT h active stack qc root,
    live_frames_wf CT h active stack ->
    root < dom h ->
    potential_new_attachment CT h active stack qc root ->
    exists anchor,
      (typed_root (qc2q qc) active.(frame_senv) active.(frame_renv) anchor \/
       typed_root Mut active.(frame_senv) active.(frame_renv) anchor \/
       (qc = RDM_c /\ immediate_rdm_caller_root h active stack anchor)) /\
      potential_connected CT h active stack anchor root.
Proof.
  intros CT h active stack qc root Hframes Hroot
    [anchor [[Hfresh | [Htyped | [Hmut | Hcaller]]] Hconnected]].
  - subst anchor.
    have Hroot_fresh := potential_connected_from_fresh_is_fresh CT h active
      stack root Hframes Hconnected.
    subst root. lia.
  - exists anchor. split; [left; exact Htyped|exact Hconnected].
  - exists anchor. split; [right; left; exact Hmut|exact Hconnected].
  - exists anchor. split; [right; right; exact Hcaller|exact Hconnected].
Qed.

Lemma fresh_live_after_rdm_new_implies_mut_authority :
  forall CT sGamma mt rGamma h x C args sGamma' vals qruntime authority
    stack,
    wf_r_config CT sGamma rGamma h ->
    live_frames_wf CT h
      (mk_watched_frame authority sGamma rGamma) stack ->
    stmt_typing CT sGamma mt (SNew x RDM_c C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    In Loc
      (live_capability_set CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) stack)
      (dom h) ->
    authority = Mut_r.
Proof.
  intros CT sGamma mt rGamma h x C args sGamma' vals qruntime authority
    stack Hwf Hframes Htyping Hvals
    [root [[Hactive_root | [boundary [Hin Hboundary_root]]] Hreachable]].
  - destruct Hactive_root as
      [variable [T [Htype [Hvalue Hcapability]]]].
    destruct Hcapability as [Hmut | [Hrdm Hauthority]].
    + assert (Hroot : typed_root Mut sGamma'
          (update_r_env_value rGamma x (Iot (dom h))) root).
      { exists variable, T. repeat split; assumption. }
      destruct (new_typed_root_origin CT sGamma mt rGamma h x RDM_c C args
        sGamma' Mut root Hwf Htyping Hroot) as
        [Hold_root | [Hfresh [Tx [Hgetx Htx_mut]]]].
      * destruct Hold_root as
          [old_variable [OldT [Hold_type [Hold_value Hold_mut]]]].
        have Hroot_dom := wf_config_value_dom CT sGamma rGamma h
          old_variable root Hwf Hold_value.
        have Hheap_wf : wf_heap CT h := proj1 (proj2 Hwf).
        destruct (retained_reachable_from_old_after_append CT h
          (mkObj (mkruntime_type qruntime C) vals) root (dom h) Hheap_wf
          Hroot_dom Hreachable) as [Hfresh_dom _]. lia.
      * have Hcreation := new_mut_result_requires_mut_creation CT sGamma mt x
          RDM_c C args sGamma' Tx Htyping.
        assert (HsGamma : sGamma' = sGamma) by
          (inversion Htyping; reflexivity).
        specialize (Hcreation (ltac:(rewrite HsGamma; exact Hgetx)) Htx_mut).
        discriminate.
    + assert (Hroot : typed_root RDM sGamma'
          (update_r_env_value rGamma x (Iot (dom h))) root).
      { exists variable, T. repeat split; assumption. }
      destruct (new_typed_root_origin CT sGamma mt rGamma h x RDM_c C args
        sGamma' RDM root Hwf Htyping Hroot) as
        [Hold_root | [Hfresh Hfresh_root]].
      * destruct Hold_root as
          [old_variable [OldT [Hold_type [Hold_value Hold_rdm]]]].
        have Hroot_dom := wf_config_value_dom CT sGamma rGamma h
          old_variable root Hwf Hold_value.
        have Hheap_wf : wf_heap CT h := proj1 (proj2 Hwf).
        destruct (retained_reachable_from_old_after_append CT h
          (mkObj (mkruntime_type qruntime C) vals) root (dom h) Hheap_wf
          Hroot_dom Hreachable) as [Hfresh_dom _]. lia.
      * exact Hauthority.
  - have Hstack_wf := proj2 Hframes.
    apply Forall_forall with (x := boundary) in Hstack_wf;
      [|exact Hin].
    have Hroot_dom := frame_capability_root_dom CT h
      boundary.(boundary_caller) root Hstack_wf Hboundary_root.
    have Hheap_wf : wf_heap CT h := proj1 (proj2 Hwf).
    destruct (retained_reachable_from_old_after_append CT h
      (mkObj (mkruntime_type qruntime C) vals) root (dom h) Hheap_wf
      Hroot_dom Hreachable) as [Hfresh_dom _]. lia.
Qed.

Lemma potential_history_after_new :
  forall CT P Z cutoff authority sGamma mt rGamma h stack x qc C args
    sGamma' rGamma' h',
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    eval_stmt CT rGamma h (SNew x qc C args) OK rGamma' h' ->
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma' rGamma') stack h'.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack x qc C args
    sGamma' rGamma' h' [Hlive Hpotential] Htyping Heval.
  have Hlive_post := live_history_after_new CT P Z cutoff authority sGamma mt
    rGamma h stack x qc C args sGamma' rGamma' h' Hlive Htyping Heval.
  split; [exact Hlive_post|].
  destruct Hlive as
    [Hhistory [Hframes [Hsound [Hcutoff [Hzone_bound Hauthority_chain]]]]].
  have Hwf : wf_r_config CT sGamma rGamma h := proj1 Hframes.
  inversion Heval; subst.
  assert (Hupdate :
      set_vars rGamma (update x (Iot (dom h)) (vars rGamma)) =
      update_r_env_value rGamma x (Iot (dom h))).
  { destruct rGamma. reflexivity. }
  rewrite Hupdate in Hlive_post |- *.
  match goal with
  | |- potential_colors_separated _
      (h ++ [mkObj (mkruntime_type ?runtime_q C) vals]) _ _ _ _ =>
      set (new_runtime := runtime_q) in *
  end.
  have Hpost_frames : live_frames_wf CT
      (h ++ [mkObj (mkruntime_type new_runtime C) vals])
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h)))) stack :=
    proj1 (proj2 Hlive_post).
  have Hpost_sound : live_frames_authority_sound
      (h ++ [mkObj (mkruntime_type new_runtime C) vals])
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h)))) stack :=
    proj1 (proj2 (proj2 Hlive_post)).
  assert (Hrdm_runtime : qc = RDM_c -> exists receiver,
      runtime_getVal rGamma 0 = Some (Iot receiver) /\
      r_muttype h receiver = Some new_runtime).
  { intros Hqc. subst qc. exists l1. split; [exact Hthis|].
    unfold new_runtime. destruct qthisr; simpl in *; exact Hmut. }
  intros capability protected Hcapability Hprotected Hconnected.
  have Hprotected_old : protected < dom h.
  { have Hbound := Hzone_bound protected Hprotected. lia. }
  destruct (potential_connected_after_new CT sGamma mt rGamma h x qc C
    args sGamma' vals new_runtime authority stack capability protected Hwf
	    Hframes Hrdm_runtime Htyping Hargs Hconnected) as
	    [Hold_connected | [Hcapability_entry Hprotected_attachment]].
  - have Hcapability_old : capability < dom h.
    { eapply potential_connected_left_dom_from_right; eauto. }
    have Hcapability_pre : In Loc
        (live_capability_set CT h
          (mk_watched_frame authority sGamma rGamma) stack) capability.
    { eapply new_live_reachability_to_old_location_has_old_origin
        with (mt := mt) (x := x) (qc := qc) (C := C) (args := args)
          (sGamma' := sGamma') (vals := vals) (qruntime := new_runtime);
        eauto. }
    exact (Hpotential capability protected Hcapability_pre Hprotected
      Hold_connected).
	  - destruct (potential_new_attachment_to_old_has_typed_anchor CT h
      (mk_watched_frame authority sGamma rGamma) stack qc protected Hframes
	      Hprotected_old Hprotected_attachment) as
	      [zone_anchor [Hzone_anchor Hzone_connected]].
	    have Hheap_wf : wf_heap CT h := proj1 (proj2 Hwf).
	    have Hcapability_runtime_post : r_muttype
	        (h ++ [mkObj (mkruntime_type new_runtime C) vals]) capability =
	        Some Mut_r.
	    { eapply live_capability_members_runtime_mutable; eauto. }
	    have Hprotected_runtime_post : r_muttype
	        (h ++ [mkObj (mkruntime_type new_runtime C) vals]) protected =
	        Some Mut_r.
	    { eapply potential_connected_preserves_runtime_mutability; eauto.
	      exact (proj1 (proj2 (proj1 Hpost_frames))). }
	    have Hprotected_runtime : r_muttype h protected = Some Mut_r.
	    { rewrite (r_muttype_app_preserve_old h
	        (mkObj (mkruntime_type new_runtime C) vals) protected Hprotected_old)
	        in Hprotected_runtime_post.
	      exact Hprotected_runtime_post. }
	    have Hzone_runtime : r_muttype h zone_anchor = Some Mut_r.
	    { eapply potential_connected_reflects_runtime_mutability; eauto. }
	    destruct qc.
	    + destruct Hzone_anchor as
	        [Hzone_anchor | [Hzone_anchor | [Himpossible Hcaller]]];
	        [| |discriminate].
	      * simpl in Hzone_anchor.
	      have Hzone_capability : In Loc
          (live_capability_set CT h
            (mk_watched_frame authority sGamma rGamma) stack) zone_anchor.
      { eapply typed_mut_root_is_live_capability; eauto. }
	      exact (Hpotential zone_anchor protected Hzone_capability Hprotected
	        Hzone_connected).
	      * have Hzone_capability : In Loc
	          (live_capability_set CT h
	            (mk_watched_frame authority sGamma rGamma) stack) zone_anchor.
	        { eapply typed_mut_root_is_live_capability; eauto. }
	        exact (Hpotential zone_anchor protected Hzone_capability Hprotected
	          Hzone_connected).
	    + destruct Hzone_anchor as
	        [Hzone_imm | [Hzone_mut | [Himpossible Hcaller]]].
	      * simpl in Hzone_imm.
	        have Hzone_immutable := typed_imm_root_runtime_immutable CT sGamma
	          rGamma h zone_anchor Hwf Hzone_imm.
	        rewrite Hzone_immutable in Hzone_runtime. discriminate.
	      * have Hzone_capability : In Loc
	          (live_capability_set CT h
	            (mk_watched_frame authority sGamma rGamma) stack) zone_anchor.
	        { eapply typed_mut_root_is_live_capability; eauto. }
	        exact (Hpotential zone_anchor protected Hzone_capability Hprotected
	          Hzone_connected).
	      * discriminate.
	    + simpl in Hzone_anchor.
	      assert (Hzone_case :
	        (typed_root RDM sGamma rGamma zone_anchor \/
	         immediate_rdm_caller_root h
	           (mk_watched_frame authority sGamma rGamma) stack zone_anchor) \/
	        In Loc (live_capability_set CT h
	          (mk_watched_frame authority sGamma rGamma) stack) zone_anchor).
	      { destruct Hzone_anchor as
	          [Hzone_active | [Hzone_mut | [Hzone_qc Hzone_caller]]].
	        - left. left. exact Hzone_active.
	        - right. eapply typed_mut_root_is_live_capability; eauto.
	        - left. right. exact Hzone_caller. }
	      destruct Hzone_case as [Hzone_creation | Hzone_capability].
	      2: exact (Hpotential zone_anchor protected Hzone_capability Hprotected
	        Hzone_connected).
	      destruct Hcapability_entry as
        [capability_anchor
          [[Hcapability_anchor_fresh | [Hcapability_anchor_active |
            [Hcapability_qc Hcapability_anchor_caller]]]
            Hanchor_connected]].
      * subst capability_anchor.
	        have Hcapability_fresh := potential_connected_to_fresh_is_fresh CT h
          (mk_watched_frame authority sGamma rGamma) stack capability Hframes
          Hanchor_connected.
        subst capability.
        have Hauthority_mut := fresh_live_after_rdm_new_implies_mut_authority
          CT sGamma mt rGamma h x C args sGamma' vals new_runtime authority
          stack Hwf Hframes Htyping Hargs Hcapability.
        subst authority.
        have Hzone_capability : In Loc
            (live_capability_set CT h
              (mk_watched_frame Mut_r sGamma rGamma) stack) zone_anchor.
        { destruct Hzone_creation as [Hzone_active | Hzone_caller].
          - eapply typed_rdm_root_is_live_under_mut_authority; eauto.
          - eapply immediate_rdm_caller_root_live_under_mut_authority; eauto. }
        exact (Hpotential zone_anchor protected Hzone_capability Hprotected
          Hzone_connected).
      * have Hcapability_anchor_dom : capability_anchor < dom h.
        { destruct Hcapability_anchor_active as
            [variable [T [Htype [Hvalue Hrdm]]]].
          eapply wf_config_value_dom; eauto. }
        have Hcapability_old : capability < dom h.
        { eapply potential_connected_left_dom_from_right.
          - exact Hframes.
	          - exact Hanchor_connected.
          - exact Hcapability_anchor_dom. }
        have Hcapability_pre : In Loc
            (live_capability_set CT h
              (mk_watched_frame authority sGamma rGamma) stack) capability.
        { eapply new_live_reachability_to_old_location_has_old_origin
            with (mt := mt) (x := x) (qc := RDM_c) (C := C)
              (args := args) (sGamma' := sGamma') (vals := vals)
              (qruntime := new_runtime); eauto. }
        apply (Hpotential capability protected Hcapability_pre Hprotected).
        eapply potential_connected_trans.
	        -- exact Hanchor_connected.
        -- eapply potential_connected_trans.
           ++ eapply rdm_creation_anchors_potentially_connected.
              ** left. exact Hcapability_anchor_active.
              ** exact Hzone_creation.
           ++ exact Hzone_connected.
      * have Hcapability_anchor_dom : capability_anchor < dom h.
        { eapply immediate_rdm_caller_root_dom; eauto. }
        have Hcapability_old : capability < dom h.
        { eapply potential_connected_left_dom_from_right.
          - exact Hframes.
	          - exact Hanchor_connected.
          - exact Hcapability_anchor_dom. }
        have Hcapability_pre : In Loc
            (live_capability_set CT h
              (mk_watched_frame authority sGamma rGamma) stack) capability.
        { eapply new_live_reachability_to_old_location_has_old_origin
            with (mt := mt) (x := x) (qc := RDM_c) (C := C)
              (args := args) (sGamma' := sGamma') (vals := vals)
              (qruntime := new_runtime); eauto. }
        apply (Hpotential capability protected Hcapability_pre Hprotected).
        eapply potential_connected_trans.
	        -- exact Hanchor_connected.
        -- eapply potential_connected_trans.
           ++ eapply rdm_creation_anchors_potentially_connected.
              ** right. exact Hcapability_anchor_caller.
              ** exact Hzone_creation.
           ++ exact Hzone_connected.
Qed.

Definition boundary_view_anchor
  (boundary : watched_boundary) (root : Loc) : Prop :=
  match boundary.(boundary_receiver_view) with
  | Mut => typed_root Mut
      boundary.(boundary_caller).(frame_senv)
      boundary.(boundary_caller).(frame_renv) root
  | Imm => typed_root Imm
      boundary.(boundary_caller).(frame_senv)
      boundary.(boundary_caller).(frame_renv) root
  | RDM => typed_root RDM
      boundary.(boundary_caller).(frame_senv)
      boundary.(boundary_caller).(frame_renv) root
  | RO | Lost | Bot => False
  end.

Definition boundary_view_attachment
  (CT : class_table) (h : heap) (boundary : watched_boundary)
  (stack : list watched_boundary) (root : Loc) : Prop :=
  exists anchor,
    boundary_view_anchor boundary anchor /\
    potential_connected CT h boundary.(boundary_caller) stack anchor root.

Definition boundary_view_entry
  (CT : class_table) (h : heap) (boundary : watched_boundary)
  (stack : list watched_boundary) (root : Loc) : Prop :=
  exists anchor,
    boundary_view_anchor boundary anchor /\
    potential_connected CT h boundary.(boundary_caller) stack root anchor.

Lemma boundary_view_attachment_root :
  forall CT h boundary stack root,
    boundary_view_anchor boundary root ->
    boundary_view_attachment CT h boundary stack root.
Proof.
  intros. exists root. split; [assumption|apply rt_refl].
Qed.

Lemma boundary_view_entry_root :
  forall CT h boundary stack root,
    boundary_view_anchor boundary root ->
    boundary_view_entry CT h boundary stack root.
Proof.
  intros. exists root. split; [assumption|apply rt_refl].
Qed.

Lemma boundary_view_attachment_transport :
  forall CT h boundary stack first second,
    boundary_view_attachment CT h boundary stack first ->
    potential_connected CT h boundary.(boundary_caller) stack first second ->
    boundary_view_attachment CT h boundary stack second.
Proof.
  intros CT h boundary stack first second
    [anchor [Hanchor Hanchor_first]] Hfirst_second.
  exists anchor. split; [exact Hanchor|].
  eapply potential_connected_trans; eauto.
Qed.

Lemma boundary_view_entry_transport :
  forall CT h boundary stack first second,
    potential_connected CT h boundary.(boundary_caller) stack first second ->
    boundary_view_entry CT h boundary stack second ->
    boundary_view_entry CT h boundary stack first.
Proof.
  intros CT h boundary stack first second Hfirst_second
    [anchor [Hanchor Hsecond_anchor]].
  exists anchor. split; [exact Hanchor|].
  eapply potential_connected_trans; eauto.
Qed.

Lemma readonly_boundary_roots_equal :
  forall boundary left right,
    boundary.(boundary_receiver_view) = RO ->
    typed_root RDM boundary.(boundary_callee_entry_senv)
      boundary.(boundary_callee_entry_renv) left ->
    typed_root RDM boundary.(boundary_callee_entry_senv)
      boundary.(boundary_callee_entry_renv) right ->
    left = right.
Proof.
  intros boundary left right Hview Hleft Hright.
  have Hleft_origin := boundary_entry_rdm_root_by_view boundary left Hleft.
  have Hright_origin := boundary_entry_rdm_root_by_view boundary right Hright.
  rewrite Hview in Hleft_origin, Hright_origin.
  destruct Hleft_origin as
    [left_receiver [Hleft_receiver [Hleft_eq Hleft_root]]].
  destruct Hright_origin as
    [right_receiver [Hright_receiver [Hright_eq Hright_root]]].
  rewrite Hleft_receiver in Hright_receiver.
  injection Hright_receiver as <-. congruence.
Qed.

Lemma potential_adjacent_after_call_push :
  forall CT h boundary stack callee_authority left right,
    potential_adjacent CT h
      (mk_watched_frame callee_authority
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv))
      (boundary :: stack) left right ->
    potential_connected CT h boundary.(boundary_caller) stack left right \/
    (boundary_view_entry CT h boundary stack left /\
     boundary_view_attachment CT h boundary stack right).
Proof.
  intros CT h boundary stack callee_authority left right
    [Hheap | [Hframe | Hreturn]].
  - left. apply rt_step. left. exact Hheap.
  - destruct Hframe as [frame [Hlive [Hleft Hright]]].
    inversion Hlive; subst.
    + have Hleft_origin := boundary_entry_rdm_root_by_view boundary left Hleft.
      have Hright_origin := boundary_entry_rdm_root_by_view boundary right Hright.
      destruct boundary.(boundary_receiver_view) eqn:Hview;
        simpl in Hleft_origin, Hright_origin.
      * right. split.
        -- apply boundary_view_entry_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
        -- apply boundary_view_attachment_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
      * right. split.
        -- apply boundary_view_entry_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
        -- apply boundary_view_attachment_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
      * right. split.
        -- apply boundary_view_entry_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
        -- apply boundary_view_attachment_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
      * left. have Heq := readonly_boundary_roots_equal boundary left right
          Hview Hleft Hright. subst right. apply rt_refl.
      * contradiction.
      * contradiction.
    + simpl in H.
      destruct H as [Htop | Htail].
      * subst boundary0. left. eapply live_frame_rdm_roots_potentially_connected
          with (frame := boundary.(boundary_caller)).
        -- constructor.
        -- exact Hleft.
        -- exact Hright.
      * left. apply rt_step. right. left. exists boundary0.(boundary_caller).
        repeat split; try assumption. constructor. exact Htail.
  - destruct Hreturn as
      [callee [return_boundary
        [Hlive [Hview [Hruntime [Hroots | Hroots]]]]]].
    + inversion Hlive; subst.
      * have Horigin := boundary_entry_rdm_root_by_view return_boundary left
          (proj1 Hroots).
        rewrite Hview in Horigin. simpl in Horigin.
        left. eapply live_frame_rdm_roots_potentially_connected with
          (frame := return_boundary.(boundary_caller)).
        -- constructor.
        -- exact Horigin.
        -- exact (proj2 Hroots).
      * left. apply rt_step. right. right. exists callee, return_boundary.
        split.
        { match goal with
          | Htail : live_call_boundary _ _ _ _ |- _ => exact Htail
          end. }
        split; [exact Hview|].
        split; [exact Hruntime|]. left. exact Hroots.
    + inversion Hlive; subst.
      * have Horigin := boundary_entry_rdm_root_by_view return_boundary right
          (proj2 Hroots).
        rewrite Hview in Horigin. simpl in Horigin.
        left. eapply live_frame_rdm_roots_potentially_connected with
          (frame := return_boundary.(boundary_caller)).
        -- constructor.
        -- exact (proj1 Hroots).
        -- exact Horigin.
      * left. apply rt_step. right. right. exists callee, return_boundary.
        split.
        { match goal with
          | Htail : live_call_boundary _ _ _ _ |- _ => exact Htail
          end. }
        split; [exact Hview|].
        split; [exact Hruntime|]. right. exact Hroots.
Qed.

Lemma potential_connected_after_call_push :
  forall CT h boundary stack callee_authority left right,
    potential_connected CT h
      (mk_watched_frame callee_authority
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv))
      (boundary :: stack) left right ->
    potential_connected CT h boundary.(boundary_caller) stack left right \/
    (boundary_view_entry CT h boundary stack left /\
     boundary_view_attachment CT h boundary stack right).
Proof.
  intros CT h boundary stack callee_authority left right Hconnected.
  induction Hconnected.
  - eapply potential_adjacent_after_call_push; eauto.
  - left. apply rt_refl.
  - destruct IHHconnected1 as [Hxy | [Hentry_x Hattach_y]];
      destruct IHHconnected2 as [Hyz | [Hentry_y Hattach_z]].
    + left. eapply potential_connected_trans; eauto.
    + right. split.
      * eapply boundary_view_entry_transport; eauto.
      * exact Hattach_z.
    + right. split.
      * exact Hentry_x.
      * eapply boundary_view_attachment_transport; eauto.
    + right. split; assumption.
Qed.

Lemma potential_history_enter_call :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack
    x method y args sGamma' vals ly cy runtime_mdef Ty,
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    exists origins,
      potential_live_history_state CT P Z cutoff
        (mk_watched_frame
          (call_authority caller_authority (sqtype Ty))
          (mreceiver (msignature runtime_mdef) ::
            mparams (msignature runtime_mdef))
          (mkr_env (Iot ly :: vals)))
        (mk_watched_boundary
          (mk_watched_frame caller_authority sGamma rGamma)
          (mreceiver (msignature runtime_mdef) ::
            mparams (msignature runtime_mdef))
          (mkr_env (Iot ly :: vals)) (sqtype Ty) origins :: stack) h.
Proof.
  intros CT P Z cutoff caller_authority sGamma mt rGamma h stack
    x method y args sGamma' vals ly cy runtime_mdef Ty
    [Hlive Hpotential] Htyping Hscope Hgety Hvalue Hbase Hfind Hargs.
  destruct (live_history_enter_call CT P Z cutoff caller_authority sGamma mt
    rGamma h stack x method y args sGamma' vals ly cy runtime_mdef Ty Hlive
    Htyping Hscope Hgety Hvalue Hbase Hfind Hargs) as
    [origins Hlive_post].
  exists origins. split; [exact Hlive_post|].
  set (caller := mk_watched_frame caller_authority sGamma rGamma).
  set (callee_senv := mreceiver (msignature runtime_mdef) ::
    mparams (msignature runtime_mdef)).
  set (callee_renv := mkr_env (Iot ly :: vals)).
  set (boundary := mk_watched_boundary caller callee_senv callee_renv
    (sqtype Ty) origins).
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 Hlive)).
  have Hframes : live_frames_wf CT h caller stack.
  { unfold caller. exact (proj1 (proj2 Hlive)). }
  have Hsound : live_frames_authority_sound h caller stack.
  { unfold caller. exact (proj1 (proj2 (proj2 Hlive))). }
  intros capability protected Hcapability Hprotected Hconnected.
  have Hcapability_old : In Loc
      (live_capability_set CT h caller stack) capability.
  { unfold boundary, caller, callee_senv, callee_renv in Hcapability |- *.
    apply (proj1 (call_push_live_reachability_equivalent CT caller_authority
      sGamma mt rGamma h x method y args sGamma' vals ly cy runtime_mdef Ty
      origins stack capability Hwf Htyping Hscope Hgety Hvalue Hbase Hfind
      Hargs)).
    exact Hcapability. }
  destruct (potential_connected_after_call_push CT h boundary stack
    (call_authority caller_authority (sqtype Ty)) capability protected
    Hconnected) as
    [Hold_connected | [Hcapability_entry Hprotected_attachment]].
  - unfold caller in Hcapability_old, Hold_connected, Hframes, Hsound |- *.
    exact (Hpotential capability protected Hcapability_old Hprotected
      Hold_connected).
  - destruct (sqtype Ty) eqn:Hview.
    + destruct Hprotected_attachment as
        [zone_anchor [Hzone_anchor Hzone_connected]].
      unfold boundary_view_anchor in Hzone_anchor.
      unfold boundary in Hzone_anchor, Hzone_connected. simpl in *.
      have Hzone_capability : In Loc
          (live_capability_set CT h caller stack) zone_anchor.
      { unfold caller. eapply typed_mut_root_is_live_capability; eauto. }
      unfold caller in Hzone_capability, Hzone_connected.
      exact (Hpotential zone_anchor protected Hzone_capability Hprotected
        Hzone_connected).
    + destruct Hcapability_entry as
        [capability_anchor [Hcapability_anchor Hanchor_connected]].
      unfold boundary_view_anchor in Hcapability_anchor.
      unfold boundary in Hcapability_anchor, Hanchor_connected. simpl in *.
      have Hcapability_runtime := live_capability_members_runtime_mutable CT h
        caller stack Hframes Hsound capability Hcapability_old.
      have Hanchor_immutable := typed_imm_root_runtime_immutable CT sGamma
        rGamma h capability_anchor Hwf Hcapability_anchor.
      have Hheap_wf : wf_heap CT h := proj1 (proj2 Hwf).
      have Hanchor_runtime := potential_connected_preserves_runtime_mutability
        CT h caller stack capability capability_anchor Mut_r Hframes Hheap_wf
        Hanchor_connected Hcapability_runtime.
      rewrite Hanchor_immutable in Hanchor_runtime. discriminate.
    + destruct Hcapability_entry as
        [capability_anchor [Hcapability_anchor Hcapability_connected]].
      destruct Hprotected_attachment as
        [zone_anchor [Hzone_anchor Hzone_connected]].
      unfold boundary_view_anchor in Hcapability_anchor, Hzone_anchor.
      unfold boundary in Hcapability_anchor, Hzone_anchor,
        Hcapability_connected, Hzone_connected. simpl in *.
      unfold caller in Hcapability_old, Hcapability_connected, Hzone_connected.
      apply (Hpotential capability protected Hcapability_old Hprotected).
      eapply potential_connected_trans.
	      * exact Hcapability_connected.
      * eapply potential_connected_trans.
        -- eapply live_frame_rdm_roots_potentially_connected
             with (frame := mk_watched_frame caller_authority sGamma rGamma).
           ++ constructor.
           ++ exact Hcapability_anchor.
           ++ exact Hzone_anchor.
        -- exact Hzone_connected.
    + destruct Hcapability_entry as
        [anchor [Hanchor Hanchor_connected]].
      unfold boundary_view_anchor in Hanchor.
      unfold boundary in Hanchor. simpl in Hanchor.
      contradiction.
    + destruct Hcapability_entry as
        [anchor [Hanchor Hanchor_connected]].
      unfold boundary_view_anchor in Hanchor.
      unfold boundary in Hanchor. simpl in Hanchor.
      contradiction.
    + destruct Hcapability_entry as
        [anchor [Hanchor Hanchor_connected]].
      unfold boundary_view_anchor in Hanchor.
      unfold boundary in Hanchor. simpl in Hanchor.
      contradiction.
Qed.

(** A non-null result stored in an RDM caller destination can only arise from
    an RDM body result viewed through an RDM receiver. *)
Lemma safe_call_rdm_result_reflects_to_body_return :
  forall receiver_q body_return_q declared_return_q result_q,
    q_subtype body_return_q declared_return_q ->
    q_subtype (vpa_mutability_qq_readonly_state receiver_q declared_return_q)
      result_q ->
    receiver_q <> Bot ->
    body_return_q <> Bot ->
    result_q = RDM ->
    receiver_q = RDM /\ body_return_q = RDM.
Proof.
  intros receiver_q body_return_q declared_return_q result_q Hbody Hresult
    Hreceiver_nonbottom Hbody_nonbottom Hresult_rdm.
  subst result_q.
  destruct receiver_q, body_return_q, declared_return_q; simpl in *;
    try contradiction;
    repeat match goal with
    | H : q_subtype _ _ |- _ => inversion H; subst; clear H
    end;
    try solve [split; reflexivity | contradiction | congruence].
Qed.

Lemma caller_post_rdm_root_origin :
  forall CT caller_senv caller_renv h destination destination_type
    return_location root,
    wf_r_config CT caller_senv caller_renv h ->
    static_getType caller_senv destination = Some destination_type ->
    typed_root RDM caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) root ->
    typed_root RDM caller_senv caller_renv root \/
    (root = return_location /\ sqtype destination_type = RDM).
Proof.
  intros CT caller_senv caller_renv h destination destination_type
    return_location root Hwf Hdestination
    [variable [T [Htype [Hvalue Hrdm]]]].
  destruct (Nat.eq_dec variable destination) as [Heq | Hneq].
  - subst variable. rewrite Hdestination in Htype. injection Htype as <-.
    have Hdestination_dom := Hdestination.
    apply static_getType_dom in Hdestination_dom.
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [_ [_ [Hlength Hcorr]]]]].
    assert (Hruntime_dom : destination < dom (vars caller_renv)) by lia.
    have Hupdated := runtime_getVal_update_same caller_renv destination
      (Iot return_location) Hruntime_dom.
    rewrite Hupdated in Hvalue. injection Hvalue as <-.
    right. split; [reflexivity|exact Hrdm].
  - have Hunchanged := runtime_getVal_update_diff caller_renv destination
      variable (Iot return_location).
    assert (Hdestination_variable : destination <> variable) by congruence.
    specialize (Hunchanged Hdestination_variable).
    rewrite Hunchanged in Hvalue.
    left. exists variable, T. repeat split; assumption.
Qed.

Lemma caller_post_rdm_root_reflects_before_pop :
  forall CT caller_senv caller_renv h destination destination_type receiver
    receiver_location receiver_type callee_senv callee_renv return_var
    body_return_type declared_return_type return_location root,
    wf_r_config CT caller_senv caller_renv h ->
    static_getType caller_senv destination = Some destination_type ->
    static_getType caller_senv receiver = Some receiver_type ->
    runtime_getVal caller_renv receiver = Some (Iot receiver_location) ->
    wf_r_config CT callee_senv callee_renv h ->
    static_getType callee_senv return_var = Some body_return_type ->
    runtime_getVal callee_renv return_var = Some (Iot return_location) ->
    qualified_type_subtype CT body_return_type declared_return_type ->
    qualified_type_subtype CT
      (vpa_mutability_tt_readonly_state receiver_type declared_return_type)
      destination_type ->
    typed_root RDM caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) root ->
    typed_root RDM caller_senv caller_renv root \/
    (sqtype receiver_type = RDM /\
     typed_root RDM callee_senv callee_renv root).
Proof.
  intros CT caller_senv caller_renv h destination destination_type receiver
    receiver_location receiver_type callee_senv callee_renv return_var
    body_return_type declared_return_type return_location root Hcaller_wf
    Hdestination Hreceiver_type Hreceiver_value Hcallee_wf Hreturn_type
    Hreturn_value Hbody_sub Hresult_sub Hroot.
  destruct (caller_post_rdm_root_origin CT caller_senv caller_renv h
    destination destination_type return_location root Hcaller_wf Hdestination
    Hroot) as [Hold | [Hroot_return Hdestination_rdm]].
  - left. exact Hold.
  - right. subst root.
    have Hreceiver_nonbottom : sqtype receiver_type <> Bot.
    { eapply (wf_config_nonnull_variable_not_bot CT caller_senv caller_renv h
        receiver receiver_type receiver_location); eauto. }
    have Hreturn_nonbottom : sqtype body_return_type <> Bot.
    { eapply (wf_config_nonnull_variable_not_bot CT callee_senv callee_renv h
        return_var body_return_type return_location); eauto. }
    destruct (safe_call_rdm_result_reflects_to_body_return
      (sqtype receiver_type) (sqtype body_return_type)
      (sqtype declared_return_type) (sqtype destination_type)
      (qualified_type_subtype_q_subtype CT body_return_type
        declared_return_type Hbody_sub)
      (ltac:(rewrite <- sq_vpa_tt_eq_qq_readonly_state;
        exact (qualified_type_subtype_q_subtype CT
          (vpa_mutability_tt_readonly_state receiver_type declared_return_type)
          destination_type Hresult_sub)))
      Hreceiver_nonbottom Hreturn_nonbottom Hdestination_rdm) as
      [Hreceiver_rdm Hbody_rdm].
    split; [exact Hreceiver_rdm|].
    exists return_var, body_return_type. repeat split; assumption.
Qed.

Lemma potential_adjacent_after_call_pop_reflects :
  forall CT h caller_authority caller_senv caller_renv stack destination
    destination_type receiver receiver_location receiver_type entry_senv
    entry_renv origins callee_senv callee_renv return_var body_return_type
    declared_return_type return_location left right,
    wf_r_config CT caller_senv caller_renv h ->
    destination <> 0 ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    static_getType caller_senv destination = Some destination_type ->
    static_getType caller_senv receiver = Some receiver_type ->
    runtime_getVal caller_renv receiver = Some (Iot receiver_location) ->
    wf_r_config CT callee_senv callee_renv h ->
    static_getType callee_senv return_var = Some body_return_type ->
    runtime_getVal callee_renv return_var = Some (Iot return_location) ->
    qualified_type_subtype CT body_return_type declared_return_type ->
    qualified_type_subtype CT
      (vpa_mutability_tt_readonly_state receiver_type declared_return_type)
      destination_type ->
    potential_adjacent CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      stack left right ->
    potential_connected CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type) origins :: stack)
      left right.
Proof.
  intros CT h caller_authority caller_senv caller_renv stack destination
    destination_type receiver receiver_location receiver_type entry_senv
    entry_renv origins callee_senv callee_renv return_var body_return_type
    declared_return_type return_location left right Hcaller_wf
    Hdestination_not_receiver Hcaller_post_wf Hdestination Hreceiver_type Hreceiver_value
    Hcallee_wf Hreturn_type
    Hreturn_value Hbody_sub Hresult_sub [Hheap | [Hframe | Hreturn]].
  - apply rt_step. left. exact Hheap.
  - destruct Hframe as [frame [Hlive [Hleft Hright]]].
    inversion Hlive; subst.
    + destruct (caller_post_rdm_root_reflects_before_pop CT caller_senv
        caller_renv h destination destination_type receiver receiver_location
        receiver_type callee_senv callee_renv return_var body_return_type
        declared_return_type return_location left Hcaller_wf Hdestination
        Hreceiver_type Hreceiver_value Hcallee_wf Hreturn_type Hreturn_value
        Hbody_sub Hresult_sub Hleft) as [Hleft_old | [Hview_left Hleft_body]];
      destruct (caller_post_rdm_root_reflects_before_pop CT caller_senv
        caller_renv h destination destination_type receiver receiver_location
        receiver_type callee_senv callee_renv return_var body_return_type
        declared_return_type return_location right Hcaller_wf Hdestination
        Hreceiver_type Hreceiver_value Hcallee_wf Hreturn_type Hreturn_value
        Hbody_sub Hresult_sub Hright) as
        [Hright_old | [Hview_right Hright_body]].
      * eapply live_frame_rdm_roots_potentially_connected with
          (frame := mk_watched_frame caller_authority caller_senv caller_renv).
        -- apply live_frame_suspended with
             (boundary := mk_watched_boundary
               (mk_watched_frame caller_authority caller_senv caller_renv)
               entry_senv entry_renv (sqtype receiver_type) origins).
           left. reflexivity.
        -- exact Hleft_old.
        -- exact Hright_old.
      * destruct (active_rdm_roots_share_runtime_context CT caller_senv
          (update_r_env_value caller_renv destination (Iot return_location))
          h left right Hcaller_post_wf Hleft Hright) as
          [runtime_q [Hleft_runtime Hright_runtime]].
        apply rt_step. right. right.
        exists (mk_watched_frame
          (call_authority caller_authority (sqtype receiver_type))
          callee_senv callee_renv),
          (mk_watched_boundary
            (mk_watched_frame caller_authority caller_senv caller_renv)
            entry_senv entry_renv (sqtype receiver_type) origins).
        split; [constructor|]. split; [simpl; exact Hview_right|].
        split.
        -- rewrite Hleft_runtime. rewrite Hright_runtime. reflexivity.
        -- right. split; [exact Hleft_old|exact Hright_body].
      * destruct (active_rdm_roots_share_runtime_context CT caller_senv
          (update_r_env_value caller_renv destination (Iot return_location))
          h left right Hcaller_post_wf Hleft Hright) as
          [runtime_q [Hleft_runtime Hright_runtime]].
        apply rt_step. right. right.
        exists (mk_watched_frame
          (call_authority caller_authority (sqtype receiver_type))
          callee_senv callee_renv),
          (mk_watched_boundary
            (mk_watched_frame caller_authority caller_senv caller_renv)
            entry_senv entry_renv (sqtype receiver_type) origins).
        split; [constructor|]. split; [simpl; exact Hview_left|].
        split.
        -- rewrite Hleft_runtime. rewrite Hright_runtime. reflexivity.
        -- left. split; [exact Hleft_body|exact Hright_old].
      * eapply live_frame_rdm_roots_potentially_connected with
          (frame := mk_watched_frame
            (call_authority caller_authority (sqtype receiver_type))
            callee_senv callee_renv).
        -- constructor.
        -- exact Hleft_body.
        -- exact Hright_body.
    + apply rt_step. right. left. exists boundary.(boundary_caller).
      split.
      * apply live_frame_suspended with (boundary := boundary).
        right. exact H.
      * split; assumption.
  - destruct Hreturn as
      [return_callee [return_boundary
        [Hlive [Hview [Hruntime Hroots]]]]].
    inversion Hlive; subst.
    + destruct Hroots as [Hroots | Hroots].
      * destruct (caller_post_rdm_root_reflects_before_pop CT caller_senv
          caller_renv h destination destination_type receiver receiver_location
          receiver_type callee_senv callee_renv return_var body_return_type
          declared_return_type return_location left Hcaller_wf Hdestination
          Hreceiver_type Hreceiver_value Hcallee_wf Hreturn_type Hreturn_value
          Hbody_sub Hresult_sub (proj1 Hroots)) as
          [Hleft_old | [Hreceiver_rdm Hleft_body]].
        -- apply rt_step. right. right. exists
             (mk_watched_frame caller_authority caller_senv caller_renv),
             return_boundary.
           split; [constructor; constructor|]. split; [exact Hview|].
           split; [exact Hruntime|]. left. split;
             [exact Hleft_old|exact (proj2 Hroots)].
        -- assert (Hcaller_receiver_root :
             typed_root RDM caller_senv caller_renv receiver_location).
           { exists receiver, receiver_type. repeat split; assumption. }
           destruct (extract_receiver_from_wf_config CT caller_senv caller_renv
             h Hcaller_wf) as
             [this [runtime_q [Hthis [Hthis_dom Hthis_runtime]]]].
           have Hthis_value := get_this_var_mapping_runtime_getVal caller_renv
             this Hthis.
           have Hpost_this_value := runtime_getVal_update_diff caller_renv
             destination 0 (Iot return_location) Hdestination_not_receiver.
           rewrite Hthis_value in Hpost_this_value.
           have Hleft_runtime := typed_rdm_root_matches_receiver_runtime CT
             caller_senv
             (update_r_env_value caller_renv destination (Iot return_location))
             h this runtime_q left Hcaller_post_wf Hpost_this_value Hthis_runtime
             (proj1 Hroots).
           have Hreceiver_runtime := typed_rdm_root_matches_receiver_runtime CT
             caller_senv caller_renv h this runtime_q receiver_location
             Hcaller_wf Hthis_value Hthis_runtime Hcaller_receiver_root.
           eapply potential_connected_trans.
           ++ apply rt_step. right. right. exists
                (mk_watched_frame
                  (call_authority caller_authority (sqtype receiver_type))
                  callee_senv callee_renv),
                (mk_watched_boundary
                  (mk_watched_frame caller_authority caller_senv caller_renv)
                  entry_senv entry_renv (sqtype receiver_type) origins).
              split; [constructor|]. split; [simpl; exact Hreceiver_rdm|].
              split.
              ** transitivity (Some runtime_q).
                 --- exact Hleft_runtime.
                 --- symmetry. exact Hreceiver_runtime.
              ** left. split; [exact Hleft_body|exact Hcaller_receiver_root].
           ++ apply rt_step. right. right. exists
                (mk_watched_frame caller_authority caller_senv caller_renv),
                return_boundary.
              split; [constructor; constructor|]. split; [exact Hview|].
              split.
              ** rewrite Hreceiver_runtime. rewrite <- Hruntime.
                 symmetry. exact Hleft_runtime.
              ** left. split;
                   [exact Hcaller_receiver_root|exact (proj2 Hroots)].
      * destruct (caller_post_rdm_root_reflects_before_pop CT caller_senv
          caller_renv h destination destination_type receiver receiver_location
          receiver_type callee_senv callee_renv return_var body_return_type
          declared_return_type return_location right Hcaller_wf Hdestination
          Hreceiver_type Hreceiver_value Hcallee_wf Hreturn_type Hreturn_value
          Hbody_sub Hresult_sub (proj2 Hroots)) as
          [Hright_old | [Hreceiver_rdm Hright_body]].
        -- apply rt_step. right. right. exists
             (mk_watched_frame caller_authority caller_senv caller_renv),
             return_boundary.
           split; [constructor; constructor|]. split; [exact Hview|].
           split; [exact Hruntime|]. right. split;
             [exact (proj1 Hroots)|exact Hright_old].
        -- assert (Hcaller_receiver_root :
             typed_root RDM caller_senv caller_renv receiver_location).
           { exists receiver, receiver_type. repeat split; assumption. }
           destruct (extract_receiver_from_wf_config CT caller_senv caller_renv
             h Hcaller_wf) as
             [this [runtime_q [Hthis [Hthis_dom Hthis_runtime]]]].
           have Hthis_value := get_this_var_mapping_runtime_getVal caller_renv
             this Hthis.
           have Hpost_this_value := runtime_getVal_update_diff caller_renv
             destination 0 (Iot return_location) Hdestination_not_receiver.
           rewrite Hthis_value in Hpost_this_value.
           have Hright_runtime := typed_rdm_root_matches_receiver_runtime CT
             caller_senv
             (update_r_env_value caller_renv destination (Iot return_location))
             h this runtime_q right Hcaller_post_wf Hpost_this_value Hthis_runtime
             (proj2 Hroots).
           have Hreceiver_runtime := typed_rdm_root_matches_receiver_runtime CT
             caller_senv caller_renv h this runtime_q receiver_location
             Hcaller_wf Hthis_value Hthis_runtime Hcaller_receiver_root.
           eapply potential_connected_trans.
           ++ apply rt_step. right. right. exists
                (mk_watched_frame caller_authority caller_senv caller_renv),
                return_boundary.
              split; [constructor; constructor|]. split; [exact Hview|].
              split.
              ** transitivity (Some runtime_q).
                 --- rewrite Hruntime. exact Hright_runtime.
                 --- symmetry. exact Hreceiver_runtime.
              ** right. split;
                   [exact (proj1 Hroots)|exact Hcaller_receiver_root].
           ++ apply rt_step. right. right. exists
                (mk_watched_frame
                  (call_authority caller_authority (sqtype receiver_type))
                  callee_senv callee_renv),
                (mk_watched_boundary
                  (mk_watched_frame caller_authority caller_senv caller_renv)
                  entry_senv entry_renv (sqtype receiver_type) origins).
              split; [constructor|]. split; [simpl; exact Hreceiver_rdm|].
              split.
              ** transitivity (Some runtime_q).
                 --- exact Hreceiver_runtime.
                 --- symmetry. exact Hright_runtime.
              ** right. split;
                   [exact Hcaller_receiver_root|exact Hright_body].
    + apply rt_step. right. right. exists return_callee, return_boundary.
      split; [constructor; constructor; exact H|].
      split; [exact Hview|]. split; assumption.
Qed.

Lemma potential_connected_after_call_pop_reflects :
  forall CT h caller_authority caller_senv caller_renv stack destination
    destination_type receiver receiver_location receiver_type entry_senv
    entry_renv origins callee_senv callee_renv return_var body_return_type
    declared_return_type return_location left right,
    wf_r_config CT caller_senv caller_renv h ->
    destination <> 0 ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    static_getType caller_senv destination = Some destination_type ->
    static_getType caller_senv receiver = Some receiver_type ->
    runtime_getVal caller_renv receiver = Some (Iot receiver_location) ->
    wf_r_config CT callee_senv callee_renv h ->
    static_getType callee_senv return_var = Some body_return_type ->
    runtime_getVal callee_renv return_var = Some (Iot return_location) ->
    qualified_type_subtype CT body_return_type declared_return_type ->
    qualified_type_subtype CT
      (vpa_mutability_tt_readonly_state receiver_type declared_return_type)
      destination_type ->
    potential_connected CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      stack left right ->
    potential_connected CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type) origins :: stack)
      left right.
Proof.
  intros CT h caller_authority caller_senv caller_renv stack destination
    destination_type receiver receiver_location receiver_type entry_senv
    entry_renv origins callee_senv callee_renv return_var body_return_type
    declared_return_type return_location left right Hcaller_wf
    Hdestination_not_receiver Hcaller_post_wf Hdestination Hreceiver_type Hreceiver_value
    Hcallee_wf Hreturn_type
    Hreturn_value Hbody_sub Hresult_sub Hconnected.
  eapply potential_connected_map_edges; [|exact Hconnected].
  intros edge_left edge_right Hedge.
  eapply potential_adjacent_after_call_pop_reflects; eauto.
Qed.

Lemma potential_history_leave_call :
  forall CT P Z cutoff caller_authority caller_senv caller_renv caller_h stack
    destination destination_type receiver receiver_location receiver_type
    entry_senv entry_renv origins callee_senv callee_renv callee_h return_var
    body_return_type declared_return_type return_location,
    zone_env_safe Z caller_senv caller_renv ->
    env_is_confined P cutoff caller_renv ->
    wf_r_config CT caller_senv caller_renv caller_h ->
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    static_getType caller_senv receiver = Some receiver_type ->
    runtime_getVal caller_renv receiver = Some (Iot receiver_location) ->
    static_getType callee_senv return_var = Some body_return_type ->
    runtime_getVal callee_renv return_var = Some (Iot return_location) ->
    qualified_type_subtype CT body_return_type declared_return_type ->
    qualified_type_subtype CT
      (vpa_mutability_tt_readonly_state receiver_type declared_return_type)
      destination_type ->
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type) origins :: stack) callee_h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location))
      callee_h ->
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      stack callee_h.
Proof.
  intros CT P Z cutoff caller_authority caller_senv caller_renv caller_h stack
    destination destination_type receiver receiver_location receiver_type
    entry_senv entry_renv origins callee_senv callee_renv callee_h return_var
    body_return_type declared_return_type return_location Hcaller_zone
    Hcaller_confined Hcaller_wf Hdestination_not_receiver Hdestination_type
    Hreceiver_type Hreceiver_value Hreturn_type Hreturn_value Hbody_sub
    Hresult_sub [Hlive Hpotential] Hcaller_post_wf.
  set (callee_frame := mk_watched_frame
    (call_authority caller_authority (sqtype receiver_type))
    callee_senv callee_renv).
  set (caller_boundary := mk_watched_boundary
    (mk_watched_frame caller_authority caller_senv caller_renv)
    entry_senv entry_renv (sqtype receiver_type) origins).
  set (caller_post := mk_watched_frame caller_authority caller_senv
    (update_r_env_value caller_renv destination (Iot return_location))).
  have Hpre_frames : live_frames_wf CT callee_h callee_frame
      (caller_boundary :: stack) := proj1 (proj2 Hlive).
  have Hcallee_wf : wf_r_config CT callee_senv callee_renv callee_h :=
    proj1 Hpre_frames.
  have Hcaller_current_wf : wf_r_config CT caller_senv caller_renv callee_h.
  { have Hcaller_boundary_wf := Forall_inv (proj2 Hpre_frames).
    change (wf_r_config CT caller_senv caller_renv callee_h)
      in Hcaller_boundary_wf.
    exact Hcaller_boundary_wf. }
  set (Mpre := live_capability_set CT callee_h callee_frame
    (caller_boundary :: stack)).
  assert (Hpost_separated_pre :
    potential_colors_separated CT callee_h Mpre Z caller_post stack).
  { intros capability protected Hcapability Hprotected Hconnected.
    apply (Hpotential capability protected Hcapability Hprotected).
    unfold caller_post, callee_frame, caller_boundary in *.
    eapply potential_connected_after_call_pop_reflects; eauto. }
  have Hcaller_colors : watched_frame_colors CT callee_h Mpre Z caller_post.
  { eapply potential_colors_imply_active_colors; eauto. }
  have Hlive_post := live_history_leave_call_given_caller_colors CT P Z cutoff
    caller_authority caller_senv caller_renv caller_h stack destination
    destination_type receiver receiver_location receiver_type entry_senv
    entry_renv origins callee_senv callee_renv callee_h return_var
    body_return_type declared_return_type return_location Hcaller_zone
    Hcaller_confined Hcaller_wf Hdestination_not_receiver Hdestination_type
    Hreceiver_type Hreceiver_value Hreturn_type Hreturn_value Hbody_sub
    Hresult_sub Hlive Hcaller_post_wf
    (ltac:(unfold caller_post, Mpre in Hcaller_colors; exact Hcaller_colors)).
  split; [exact Hlive_post|].
  intros capability protected Hcapability Hprotected Hconnected.
  apply (Hpost_separated_pre capability protected).
  - unfold Mpre, caller_post, callee_frame, caller_boundary.
    eapply call_return_live_reachability_reflects_before_pop with
      (caller_h := caller_h) (destination_type := destination_type)
      (receiver := receiver) (receiver_location := receiver_location)
      (receiver_type := receiver_type) (entry_senv := entry_senv)
      (entry_renv := entry_renv) (origins := origins)
      (callee_senv := callee_senv) (callee_renv := callee_renv)
      (return_var := return_var) (body_return_type := body_return_type)
      (declared_return_type := declared_return_type)
      (return_location := return_location); eauto.
  - exact Hprotected.
  - exact Hconnected.
Qed.

Lemma caller_null_rdm_roots_descend :
  forall CT caller_senv caller_renv h destination destination_type,
    wf_r_config CT caller_senv caller_renv h ->
    static_getType caller_senv destination = Some destination_type ->
    rdm_roots_descend_from CT h caller_senv caller_renv caller_senv
      (update_r_env_value caller_renv destination Null_a).
Proof.
  intros CT caller_senv caller_renv h destination destination_type Hwf
    Hdestination root [variable [T [Htype [Hvalue Hrdm]]]].
  destruct (Nat.eq_dec variable destination) as [Heq | Hneq].
  - subst variable.
    have Hdestination_dom := Hdestination.
    apply static_getType_dom in Hdestination_dom.
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [_ [_ [Hlength Hcorr]]]]].
    assert (Hruntime_dom : destination < dom (vars caller_renv)) by lia.
    have Hupdated := runtime_getVal_update_same caller_renv destination
      Null_a Hruntime_dom.
    rewrite Hupdated in Hvalue. discriminate.
  - have Hunchanged := runtime_getVal_update_diff caller_renv destination
      variable Null_a.
    assert (Hdestination_variable : destination <> variable) by congruence.
    specialize (Hunchanged Hdestination_variable).
    rewrite Hunchanged in Hvalue.
    exists root. split.
    + exists variable, T. repeat split; assumption.
    + constructor.
Qed.

Lemma potential_adjacent_before_call_pop_included :
  forall CT h caller_frame stack callee_frame entry_senv entry_renv
    receiver_view origins left right,
    potential_adjacent CT h caller_frame stack left right ->
    potential_adjacent CT h callee_frame
      (mk_watched_boundary caller_frame entry_senv entry_renv receiver_view
        origins :: stack) left right.
Proof.
  intros CT h caller_frame stack callee_frame entry_senv entry_renv
    receiver_view origins left right [Hheap | [Hframe | Hreturn]].
  - left. exact Hheap.
  - right. left. destruct Hframe as [frame [Hlive [Hleft Hright]]].
    exists frame. split.
    + inversion Hlive; subst.
      * apply live_frame_suspended with
          (boundary := mk_watched_boundary frame entry_senv entry_renv
            receiver_view origins).
        left. reflexivity.
      * apply live_frame_suspended with (boundary := boundary).
        right. exact H.
    + split; assumption.
  - right. right.
    destruct Hreturn as
      [return_callee [return_boundary
        [Hlive [Hview [Hruntime Hroots]]]]].
    exists return_callee, return_boundary. split.
    + constructor. exact Hlive.
    + split; [exact Hview|]. split; assumption.
Qed.

Lemma potential_connected_before_call_pop_included :
  forall CT h caller_frame stack callee_frame entry_senv entry_renv
    receiver_view origins left right,
    potential_connected CT h caller_frame stack left right ->
    potential_connected CT h callee_frame
      (mk_watched_boundary caller_frame entry_senv entry_renv receiver_view
        origins :: stack) left right.
Proof.
  intros CT h caller_frame stack callee_frame entry_senv entry_renv
    receiver_view origins left right Hconnected.
  eapply potential_connected_map_edges; [|exact Hconnected].
  intros edge_left edge_right Hedge. apply rt_step.
  eapply potential_adjacent_before_call_pop_included; eauto.
Qed.

Lemma potential_history_leave_call_null :
  forall CT P Z cutoff caller_authority caller_senv caller_renv caller_h stack
    destination destination_type receiver_type entry_senv entry_renv origins
    callee_senv callee_renv callee_h,
    zone_env_safe Z caller_senv caller_renv ->
    env_is_confined P cutoff caller_renv ->
    wf_r_config CT caller_senv caller_renv caller_h ->
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type) origins :: stack) callee_h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination Null_a) callee_h ->
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination Null_a)) stack callee_h.
Proof.
  intros CT P Z cutoff caller_authority caller_senv caller_renv caller_h stack
    destination destination_type receiver_type entry_senv entry_renv origins
    callee_senv callee_renv callee_h Hcaller_zone Hcaller_env Hcaller_wf
    Hdestination_not_receiver Hdestination_type [Hlive Hpotential]
    Hcaller_post_wf.
  set (callee_frame := mk_watched_frame
    (call_authority caller_authority (sqtype receiver_type))
    callee_senv callee_renv).
  set (caller_boundary := mk_watched_boundary
    (mk_watched_frame caller_authority caller_senv caller_renv)
    entry_senv entry_renv (sqtype receiver_type) origins).
  set (caller_old := mk_watched_frame caller_authority caller_senv caller_renv).
  set (caller_post := mk_watched_frame caller_authority caller_senv
    (update_r_env_value caller_renv destination Null_a)).
  have Hpre_frames : live_frames_wf CT callee_h callee_frame
      (caller_boundary :: stack) := proj1 (proj2 Hlive).
  have Hcaller_current_wf : wf_r_config CT caller_senv caller_renv callee_h.
  { have Hcaller_boundary_wf := Forall_inv (proj2 Hpre_frames).
    change (wf_r_config CT caller_senv caller_renv callee_h)
      in Hcaller_boundary_wf.
    exact Hcaller_boundary_wf. }
  have Hdescend := caller_null_rdm_roots_descend CT caller_senv caller_renv
    callee_h destination destination_type Hcaller_current_wf Hdestination_type.
  set (Mpre := live_capability_set CT callee_h callee_frame
    (caller_boundary :: stack)).
  assert (Hpost_separated_pre :
    potential_colors_separated CT callee_h Mpre Z caller_post stack).
  { intros capability protected Hcapability Hprotected Hconnected.
    apply (Hpotential capability protected Hcapability Hprotected).
    have Hold_connected : potential_connected CT callee_h caller_old stack
        capability protected.
    { unfold caller_old, caller_post.
      eapply potential_connected_after_active_descent_reflects; eauto. }
    unfold callee_frame, caller_boundary, caller_old in *.
    eapply potential_connected_before_call_pop_included; eauto. }
  have Hcaller_colors : watched_frame_colors CT callee_h Mpre Z caller_post.
  { eapply potential_colors_imply_active_colors; eauto. }
  have Hlive_post := live_history_leave_call_null_given_caller_colors CT P Z
    cutoff caller_authority caller_senv caller_renv caller_h stack destination
    destination_type receiver_type entry_senv entry_renv origins callee_senv
    callee_renv callee_h Hcaller_zone Hcaller_env Hcaller_wf
    Hdestination_not_receiver Hdestination_type Hlive Hcaller_post_wf
    (ltac:(unfold caller_post, Mpre in Hcaller_colors; exact Hcaller_colors)).
  split; [exact Hlive_post|].
  intros capability protected Hcapability Hprotected Hconnected.
  apply (Hpost_separated_pre capability protected).
  - unfold Mpre, caller_post, callee_frame, caller_boundary.
    eapply call_return_null_live_reachability_reflects_before_pop with
      (caller_h := caller_h) (destination_type := destination_type); eauto.
  - exact Hprotected.
  - exact Hconnected.
Qed.

Lemma safe_typed_call_target_method_safe :
  forall CT sGamma mt rGamma h x method y args sGamma' ly cy runtime_mdef,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    readonly_state_method_scope (mscope (msignature runtime_mdef)).
Proof.
  intros CT sGamma mt rGamma h x method y args sGamma' ly cy runtime_mdef
    Hwf Htyping Hsafe Hvalue Hbase Hfind.
  inversion Htyping; subst.
  - destruct Hsafe as [Hrs | Hts]; subst mt;
      destruct Hscope as [Has | [Hcs Hcallee]]; discriminate.
  - have Hsignature : msignature runtime_mdef = msignature mdef.
    { eapply runtime_call_signature_agrees; eauto. }
    rewrite Hsignature.
    eapply readonly_state_submethod; eauto.
Qed.

Lemma safe_typed_call_static_result :
  forall CT sGamma mt rGamma h x method y args sGamma' ly cy runtime_mdef,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    exists destination_type receiver_type,
      sGamma' = sGamma /\
      x <> 0 /\
      static_getType sGamma x = Some destination_type /\
      static_getType sGamma y = Some receiver_type /\
      qualified_type_subtype CT
        (vpa_mutability_tt_readonly_state receiver_type
          (mret (msignature runtime_mdef))) destination_type.
Proof.
  intros CT sGamma mt rGamma h x method y args sGamma' ly cy runtime_mdef
    Hwf Htyping Hsafe Hvalue Hbase Hfind.
  inversion Htyping; subst.
  - destruct Hsafe as [Hrs | Hts]; subst mt;
      destruct Hscope as [Has | [Hcs Hcallee]]; discriminate.
  - have Hsignature : msignature runtime_mdef = msignature mdef.
    { eapply runtime_call_signature_agrees; eauto. }
    exists Tx, Ty. repeat split; try assumption.
    rewrite Hsignature. exact Hret_sub.
Qed.

Theorem successful_stmt_preserves_potential_history :
  forall P CT rGamma h statement rGamma' h',
    eval_stmt CT rGamma h statement OK rGamma' h' ->
    forall sGamma mt sGamma' authority stack Z cutoff,
      potential_live_history_state CT P Z cutoff
        (mk_watched_frame authority sGamma rGamma) stack h ->
      stmt_typing CT sGamma mt statement sGamma' ->
      readonly_state_method_scope mt ->
      potential_live_history_state CT P Z cutoff
        (mk_watched_frame authority sGamma' rGamma') stack h'.
Proof.
  intros P CT rGamma h statement rGamma' h' Heval.
  have Heval_copy := Heval.
  dependent induction Heval;
    intros sGamma mt sGamma' authority stack Z cutoff Hstate Htyping Hsafe.
  - inversion Htyping; subst. exact Hstate.
  - eapply potential_history_after_local; eauto.
  - inversion Htyping; subst.
    assert (Hupdate :
      set_vars rΓ (update x v2 (vars rΓ)) = update_r_env_value rΓ x v2).
    { destruct rΓ. reflexivity. }
    rewrite Hupdate.
    eapply potential_history_after_assignment with
      (CT := CT) (P := P) (Z := Z) (cutoff := cutoff)
      (authority := authority) (mt := mt)
      (rGamma := rΓ) (h := h) (stack := stack)
      (x := x) (e := e) (old := v1) (value := v2).
    + exact Hstate.
    + exact Htyping.
    + exact Hsafe.
    + exact Hval.
    + exact Heval.
  - eapply potential_history_after_field_write.
    + exact Hstate.
    + exact Htyping.
    + exact Hsafe.
    + exact Heval_copy.
  - eapply potential_history_after_new; eauto.
  - destruct Hfind as [Hfind_method Hbody_definition].
    subst mbody. subst mstmt. subst mret. subst rΓ'. subst rΓ'''.
    have Hcaller_wf : wf_r_config CT sGamma rΓ h :=
      proj1 (proj1 (proj2 (proj1 Hstate))).
    destruct (safe_typed_call_static_result CT sGamma mt rΓ h x m y zs
      sGamma' ly cy mdef Hcaller_wf Htyping Hsafe Hval_y Hbase Hfind_method)
      as [destination_type [receiver_type
        [HsGamma [Hdestination_not_receiver [Hdestination_type
          [Hreceiver_type Hresult_sub]]]]]].
    subst sGamma'.
    have Hcallee_safe := safe_typed_call_target_method_safe CT sGamma mt rΓ
      h x m y zs sGamma ly cy mdef Hcaller_wf Htyping Hsafe Hval_y Hbase
      Hfind_method.
    destruct (typed_call_target CT sGamma mt rΓ h x m y zs sGamma vals ly
      cy mdef Hcaller_wf Htyping Hval_y Hbase Hfind_method Hargs) as
      [declaring_class [declaring_def [body_end
        [Hruntime_sub [Hdeclaring_class [Hmethod_member
          [Hmethod_wf [Hbody_typing Hcallee_initial_wf]]]]]]]].
    unfold wf_method in Hmethod_wf. simpl in Hmethod_wf.
    destruct Hmethod_wf as
      [_ [method_end [body_return_type
        [Hmethod_body_typing [Hreturn_dom
          [Hreturn_type [Hbody_sub Hoverriding]]]]]]].
    destruct (potential_history_enter_call CT P Z cutoff authority sGamma mt
      rΓ h stack x m y zs sGamma vals ly cy mdef receiver_type Hstate
      Htyping Hsafe Hreceiver_type Hval_y Hbase Hfind_method Hargs) as
      [origins Hentry].
    have Hbody_post := IHHeval eq_refl Heval
      (mreceiver (msignature mdef) :: mparams (msignature mdef))
      (mscope (msignature mdef)) method_end
      (call_authority authority (sqtype receiver_type))
      (mk_watched_boundary
        (mk_watched_frame authority sGamma rΓ)
        (mreceiver (msignature mdef) :: mparams (msignature mdef))
        (mkr_env (Iot ly :: vals)) (sqtype receiver_type) origins :: stack)
      Z cutoff Hentry Hmethod_body_typing Hcallee_safe.
    have Hlive_start := proj1 Hstate.
    have Hauthority_start := proj1 Hlive_start.
    have Hcomponent_start := proj1 Hauthority_start.
    have Hforward_start := proj1 Hcomponent_start.
    have Hcaller_zone : zone_env_safe Z sGamma rΓ :=
      proj1 (proj2 Hforward_start).
    have Hcaller_env : env_is_confined P cutoff rΓ :=
      proj1 (proj1 (proj2 (proj2 Hforward_start))).
    have Hcaller_final_wf := preservation_pico CT sGamma mt rΓ h
      (SCall x m y zs) (set_vars rΓ (update x retval (vars rΓ))) h' sGamma
      Hcaller_wf Htyping Heval_copy.
    assert (Hupdate : set_vars rΓ (update x retval (vars rΓ)) =
        update_r_env_value rΓ x retval).
    { destruct rΓ. reflexivity. }
    rewrite Hupdate in Hcaller_final_wf |- *.
    destruct retval as [|return_location].
    + eapply potential_history_leave_call_null with
        (caller_h := h) (destination_type := destination_type)
        (receiver_type := receiver_type)
        (entry_senv := mreceiver (msignature mdef) ::
          mparams (msignature mdef))
        (entry_renv := mkr_env (Iot ly :: vals))
        (origins := origins) (callee_senv := method_end)
        (callee_renv := rΓ'') (callee_h := h'); eauto.
    + eapply potential_history_leave_call with
        (caller_h := h) (destination_type := destination_type)
        (receiver := y) (receiver_location := ly)
        (receiver_type := receiver_type)
        (entry_senv := mreceiver (msignature mdef) ::
          mparams (msignature mdef))
        (entry_renv := mkr_env (Iot ly :: vals))
        (origins := origins) (callee_senv := method_end)
        (callee_renv := rΓ'') (callee_h := h')
        (return_var := mreturn (mbody mdef))
        (body_return_type := body_return_type)
        (declared_return_type := mret (msignature mdef))
        (return_location := return_location); eauto.
  - inversion Htyping; subst.
    eapply (IHHeval2 eq_refl Heval2).
    + eapply (IHHeval1 eq_refl Heval1); eauto.
    + exact Htype2.
    + exact Hsafe.
Qed.
