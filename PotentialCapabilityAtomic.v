Require Import Syntax Notations Helpers Typing Subtyping Bigstep.
Require Import ViewpointAdaptation Properties Preservation ReadonlyHelper.
Require Import Reachability MutableCapability ComponentColoring.
Require Import ExecutionConfinement ProtectionHistory ForwardCapabilityHistory.
Require Import AuthorityCapability AuthorityHistory WatchedFrames
  LiveCapabilityStack.
Require Export PotentialCapabilityCore.
From Stdlib Require Import List Sets.Ensembles Relations.Relation_Operators
  Program.Equality.
Import ListNotations.

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
    [Hlive [Hpotential Hcutoffs]] Htyping Hscope Hx Heval.
  have Hlive_post := live_history_after_assignment CT P Z cutoff authority
    sGamma mt rGamma h stack x e old value Hlive Htyping Hscope Hx Heval.
  split; [exact Hlive_post|].
  split; [|exact Hcutoffs].
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 Hlive)).
  have Hdescend := rdm_roots_descend_after_assignment CT sGamma mt
    rGamma h x e old value Hwf Htyping Hscope Hx Heval.
  intros capability protected Hcapability Hprotected Hconnected.
  destruct (potential_connected_after_active_descent_reflects CT h authority
    sGamma rGamma sGamma (update_r_env_value rGamma x value) stack
    capability protected Hwf Hdescend Hconnected) as
    [Hreflected | [anchor [Hanchor_live Hanchor_path]]].
  - apply (Hpotential capability protected).
    + eapply assignment_live_reachability_is_old; eauto.
    + exact Hprotected.
    + exact Hreflected.
  - apply (Hpotential anchor protected).
    + eapply assignment_live_reachability_is_old; eauto.
    + exact Hprotected.
    + exact Hanchor_path.
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
    [Hlive [Hpotential Hcutoffs]] Htyping Hnone.
  have Hlive_post := live_history_after_local CT P Z cutoff authority
    sGamma mt rGamma h stack T x sGamma' Hlive Htyping Hnone.
  split; [exact Hlive_post|].
  split; [|exact Hcutoffs].
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 Hlive)).
  have Hdescend := rdm_roots_descend_after_local CT sGamma mt rGamma h
    T x sGamma' Hwf Htyping Hnone.
  intros capability protected Hcapability Hprotected Hconnected.
  destruct (potential_connected_after_active_descent_reflects CT h authority
    sGamma rGamma sGamma'
    (set_vars rGamma (vars rGamma ++ [Null_a])) stack
    capability protected Hwf Hdescend Hconnected) as
    [Hreflected | [anchor [Hanchor_live Hanchor_path]]].
  - apply (Hpotential capability protected).
    + eapply local_live_reachability_is_old; eauto.
    + exact Hprotected.
    + exact Hreflected.
  - apply (Hpotential anchor protected).
    + eapply local_live_reachability_is_old; eauto.
    + exact Hprotected.
    + exact Hanchor_path.
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
      [callee [boundary
        [Hlive [Hview [Hcallee_return [Hruntime Hroots]]]]]].
    exists callee, boundary. split; [exact Hlive|].
    split; [exact Hview|].
    split; [exact Hcallee_return|].
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
    [callee [boundary
      [Hlive [Hview [Hcallee_return [Hruntime Hroots]]]]]].
  exists callee, boundary. split; [exact Hlive|].
  split; [exact Hview|].
  split; [exact Hcallee_return|].
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

Lemma mutable_edge_after_non_rdm_field_update_is_old :
  forall CT h lx old field value C fieldT left right,
    runtime_getObj h lx = Some old ->
    base_subtype CT (rctype (rt_type old)) C ->
    sf_def_rel CT C field fieldT ->
    mutability (ftype fieldT) <> RDM_f ->
    mutable_edge CT (update_field h lx field value) left right ->
    mutable_edge CT h left right.
Proof.
  intros CT h lx old field value C fieldT left right Hobj Hbase Hfield
    Hnot_rdm Hedge.
  destruct (mutable_edge_after_field_update CT h lx old field value
    left right Hobj Hedge) as [Hold | Hnew]; [exact Hold|].
  destruct Hnew as [Hsource [Hvalue [D [runtime_fd [Hruntime_base
    [Hruntime_field Hruntime_rdm]]]]]].
  assert (runtime_fd = fieldT).
  { eapply field_defs_agree_at_runtime_subtype with
      (C := rctype (rt_type old)) (D1 := D) (D2 := C); eauto. }
  subst runtime_fd. contradiction.
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

(*
The following generic heap-change transport belonged to the discarded
symmetric ownership-color graph.  The directed pending-call invariant is
preserved by statement-specific transition lemmas instead.

Lemma pending_call_colors_after_heap_change :
  forall CT h h' active stack,
    pending_call_ownership_colors_separated CT h active stack ->
    (forall left right,
      boundary_connected CT h' active stack left right ->
      boundary_connected CT h active stack left right) ->
    (forall frame location,
      live_frame_member active stack frame ->
      frame_owned_location CT h' frame location ->
      exists anchor,
        frame_owned_location CT h frame anchor /\
        boundary_connected CT h active stack location anchor /\
        boundary_connected CT h active stack anchor location) ->
    pending_call_ownership_colors_separated CT h' active stack.
Proof.
  intros CT h h' active stack Hpending Hgraph Horigin boundary above below
    capability owned Hpartition Hchannel_free Howned Hcapability Hconnected.
  apply live_capability_iff_live_frame_owned in Howned.
  destruct Howned as [owned_frame [Howned_frame_live Howned_frame]].
  have Howned_frame_live_global :
      live_frame_member active stack owned_frame.
  { eapply live_call_partition_above_frame_is_live; eauto. }
  destruct (Horigin owned_frame owned Howned_frame_live_global
    Howned_frame) as
    [owned_anchor
      [Howned_anchor [Howned_to_anchor Hanchor_to_owned]]].
  have Howned_anchor_live :
      In Loc (live_capability_set CT h active above) owned_anchor.
  { apply live_capability_iff_live_frame_owned.
    exists owned_frame. split; assumption. }
  apply live_capability_iff_live_frame_owned in Hcapability.
  destruct Hcapability as
    [capability_frame [Hcapability_frame_live Hcapability_frame]].
  have Hcapability_frame_live_global :
      live_frame_member active stack capability_frame.
  { eapply live_call_partition_below_frame_is_live; eauto. }
  destruct (Horigin capability_frame capability
    Hcapability_frame_live_global Hcapability_frame) as
    [capability_anchor
      [Hcapability_anchor
        [Hcapability_to_anchor Hanchor_to_capability]]].
  have Hcapability_anchor_live :
      In Loc
        (live_capability_set CT h boundary.(boundary_caller) below)
        capability_anchor.
  { apply live_capability_iff_live_frame_owned.
    exists capability_frame. split; assumption. }
  apply (Hpending boundary above below capability_anchor owned_anchor
    Hpartition Hchannel_free Howned_anchor_live Hcapability_anchor_live).
  eapply rt_trans; [exact Hanchor_to_capability|].
  eapply rt_trans.
  - eapply Hgraph. exact Hconnected.
  - exact Howned_to_anchor.
Qed.

Lemma boundary_connected_after_graph_and_ownership_reflection :
  forall CT h h' active stack left right,
    (forall edge_left edge_right,
      potential_connected CT h' active stack edge_left edge_right ->
      potential_connected CT h active stack edge_left edge_right) ->
    (forall frame location,
      frame_owned_location CT h' frame location ->
      frame_owned_location CT h frame location) ->
    boundary_connected CT h' active stack left right ->
    boundary_connected CT h active stack left right.
Proof.
  intros CT h h' active stack left right Hpotential Howned Hconnected.
  induction Hconnected.
  - destruct H as [Hedge | [frame [Hlive [Hleft Hright]]]].
    + apply potential_connected_is_boundary_connected.
      apply Hpotential. apply rt_step. exact Hedge.
    + apply rt_step. right. exists frame. repeat split; eauto.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma pending_call_colors_after_null_field_update :
  forall CT h active stack lx old field,
    runtime_getObj h lx = Some old ->
    pending_call_ownership_colors_separated CT h active stack ->
    pending_call_ownership_colors_separated CT
      (update_field h lx field Null_a) active stack.
Proof.
  intros CT h active stack lx old field Hobj Hpending.
  eapply pending_call_colors_after_heap_change; [exact Hpending| |].
  - intros left right Hconnected.
    eapply boundary_connected_after_graph_and_ownership_reflection
      with (h' := update_field h lx field Null_a).
    + intros edge_left edge_right Hedge.
      eapply potential_connected_after_null_field_update_is_old; eauto.
    + intros frame location Howned.
      eapply frame_owned_after_null_field_update_is_old; eauto.
    + exact Hconnected.
  - intros frame location Hlive Howned.
    exists location. repeat split.
    + eapply frame_owned_after_null_field_update_is_old; eauto.
    + apply rt_refl.
    + apply rt_refl.
Qed.

Lemma pending_call_colors_after_non_rdm_field_update :
  forall CT h active stack lx old field value C fieldT,
    runtime_getObj h lx = Some old ->
    base_subtype CT (rctype (rt_type old)) C ->
    sf_def_rel CT C field fieldT ->
    mutability (ftype fieldT) <> RDM_f ->
    mutability (ftype fieldT) <> Mut_f ->
    pending_call_ownership_colors_separated CT h active stack ->
    pending_call_ownership_colors_separated CT
      (update_field h lx field value) active stack.
Proof.
  intros CT h active stack lx old field value C fieldT Hobj Hbase Hfield
    Hnot_rdm Hnot_mut Hpending.
  eapply pending_call_colors_after_heap_change; [exact Hpending| |].
  - intros left right Hconnected.
    eapply boundary_connected_after_graph_and_ownership_reflection
      with (h' := update_field h lx field value).
    + intros edge_left edge_right Hedge.
      eapply potential_connected_after_non_rdm_field_update_is_old
        with (C := C) (fieldT := fieldT); eauto.
    + intros frame location Howned.
      eapply frame_owned_after_non_rdm_field_update_is_old
        with (C := C) (fieldT := fieldT); eauto.
    + exact Hconnected.
  - intros frame location Hlive Howned.
    exists location. repeat split.
    + eapply frame_owned_after_non_rdm_field_update_is_old
        with (C := C) (fieldT := fieldT); eauto.
    + apply rt_refl.
    + apply rt_refl.
Qed.
*)

(*
The discarded heap-only join-region experiment used to start here.  It
symmetrically colored [Mut_f] descendants of RDM roots even when those roots
carried no authority in the current frame.  Keep the proof text temporarily
while the authority-sensitive replacement is completed; it is deliberately
outside the Rocq development.

Lemma actual_rdm_join_after_active_owned_field_update_has_boundary_origin :
  forall CT h active stack lx old field written left right,
    runtime_getObj h lx = Some old ->
    frame_owned_location CT h active lx ->
    frame_owned_location CT h active written ->
    actual_rdm_join_edge
      CT (update_field h lx field (Iot written)) left right ->
    boundary_connected CT h active stack left right.
Proof.
  intros CT h active stack lx old field written left right Hobj
    Hlx_owned Hwritten_owned
    [left_root [right_root
      [Hdifferent [Hroots [Hleft Hright]]]]].
  destruct (mutable_connected_after_field_update CT h lx old field
    (Iot written) left_root right_root Hobj Hroots) as
    [Hroots_old |
      [new_written [Hwritten_value
        [[Hleft_root_lx Hwritten_right_root] |
         [Hleft_root_written Hlx_right_root]]]]];
  destruct (retained_reachable_after_field_update CT h lx old field
    (Iot written) left_root left Hobj Hleft) as
    [Hleft_old |
      [new_written_left
        [Hwritten_left_value [Hleft_root_lx' Hwritten_left]]]];
  destruct (retained_reachable_after_field_update CT h lx old field
    (Iot written) right_root right Hobj Hright) as
    [Hright_old |
      [new_written_right
        [Hwritten_right_value [Hright_root_lx Hwritten_right]]]].
  - eapply actual_rdm_join_is_boundary_connected.
    exists left_root, right_root. repeat split; assumption.
  - injection Hwritten_right_value as <-.
    have Hleft_lx : boundary_connected CT h active stack left lx.
    { eapply actual_rdm_join_is_boundary_connected.
      exists left_root, right_root. repeat split; assumption. }
    destruct (component_region_connects_to_owned_anchor CT h active stack
      active written written right (ltac:(constructor)) Hwritten_owned
      (mutable_connected_refl CT h written) Hwritten_right)
      as [Hright_to_written Hwritten_to_right].
    eapply rt_trans; [exact Hleft_lx|].
    eapply rt_trans.
    + eapply live_frame_owned_locations_boundary_connected
        with (frame := active).
      * constructor.
      * exact Hlx_owned.
      * exact Hwritten_owned.
    + exact Hwritten_to_right.
  - injection Hwritten_left_value as <-.
    destruct (component_region_connects_to_owned_anchor CT h active stack
      active written written left (ltac:(constructor)) Hwritten_owned
      (mutable_connected_refl CT h written) Hwritten_left)
      as [Hleft_to_written Hwritten_to_left].
    have Hlx_right : boundary_connected CT h active stack lx right.
    { eapply actual_rdm_join_is_boundary_connected.
      exists left_root, right_root. repeat split; assumption. }
    eapply rt_trans; [exact Hleft_to_written|].
    eapply rt_trans.
    + eapply live_frame_owned_locations_boundary_connected
        with (frame := active).
      * constructor.
      * exact Hwritten_owned.
      * exact Hlx_owned.
    + exact Hlx_right.
  - injection Hwritten_left_value as <-.
    injection Hwritten_right_value as <-.
    eapply owned_anchors_connect_component_regions
      with (frame := active) (left_root := written)
        (left_anchor := written) (right_root := written)
        (right_anchor := written).
    + constructor.
    + exact Hwritten_owned.
    + exact Hwritten_owned.
    + apply mutable_connected_refl.
    + exact Hwritten_left.
    + apply mutable_connected_refl.
    + exact Hwritten_right.
  - injection Hwritten_value as <-.
    eapply owned_anchors_connect_component_regions
      with (frame := active) (left_root := left_root)
        (left_anchor := lx) (right_root := right_root)
        (right_anchor := written).
    + constructor.
    + exact Hlx_owned.
    + exact Hwritten_owned.
    + exact Hleft_root_lx.
    + exact Hleft_old.
    + eapply mutable_connected_sym. exact Hwritten_right_root.
    + exact Hright_old.
  - injection Hwritten_value as <-.
    injection Hwritten_right_value as <-.
    eapply owned_anchors_connect_component_regions
      with (frame := active) (left_root := left_root)
        (left_anchor := lx) (right_root := written)
        (right_anchor := written).
    + constructor.
    + exact Hlx_owned.
    + exact Hwritten_owned.
    + exact Hleft_root_lx.
    + exact Hleft_old.
    + apply mutable_connected_refl.
    + exact Hwritten_right.
  - injection Hwritten_value as <-.
    injection Hwritten_left_value as <-.
    eapply owned_anchors_connect_component_regions
      with (frame := active) (left_root := written)
        (left_anchor := written) (right_root := right_root)
        (right_anchor := written).
    + constructor.
    + exact Hwritten_owned.
    + exact Hwritten_owned.
    + apply mutable_connected_refl.
    + exact Hwritten_left.
    + eapply mutable_connected_sym. exact Hwritten_right_root.
    + exact Hright_old.
  - injection Hwritten_value as <-.
    injection Hwritten_left_value as <-.
    injection Hwritten_right_value as <-.
    eapply owned_anchors_connect_component_regions
      with (frame := active) (left_root := written)
        (left_anchor := written) (right_root := written)
        (right_anchor := written).
    + constructor.
    + exact Hwritten_owned.
    + exact Hwritten_owned.
    + apply mutable_connected_refl.
    + exact Hwritten_left.
    + apply mutable_connected_refl.
    + exact Hwritten_right.
  - injection Hwritten_value as <-.
    eapply owned_anchors_connect_component_regions
      with (frame := active) (left_root := left_root)
        (left_anchor := written) (right_root := right_root)
        (right_anchor := lx).
    + constructor.
    + exact Hwritten_owned.
    + exact Hlx_owned.
    + exact Hleft_root_written.
    + exact Hleft_old.
    + eapply mutable_connected_sym. exact Hlx_right_root.
    + exact Hright_old.
  - injection Hwritten_value as <-.
    injection Hwritten_right_value as <-.
    eapply owned_anchors_connect_component_regions
      with (frame := active) (left_root := left_root)
        (left_anchor := written) (right_root := written)
        (right_anchor := written).
    + constructor.
    + exact Hwritten_owned.
    + exact Hwritten_owned.
    + exact Hleft_root_written.
    + exact Hleft_old.
    + apply mutable_connected_refl.
    + exact Hwritten_right.
  - injection Hwritten_value as <-.
    injection Hwritten_left_value as <-.
    eapply owned_anchors_connect_component_regions
      with (frame := active) (left_root := written)
        (left_anchor := written) (right_root := right_root)
        (right_anchor := lx).
    + constructor.
    + exact Hwritten_owned.
    + exact Hlx_owned.
    + apply mutable_connected_refl.
    + exact Hwritten_left.
    + eapply mutable_connected_sym. exact Hlx_right_root.
    + exact Hright_old.
  - injection Hwritten_value as <-.
    injection Hwritten_left_value as <-.
    injection Hwritten_right_value as <-.
    eapply owned_anchors_connect_component_regions
      with (frame := active) (left_root := written)
        (left_anchor := written) (right_root := written)
        (right_anchor := written).
    + constructor.
    + exact Hwritten_owned.
    + exact Hwritten_owned.
    + apply mutable_connected_refl.
    + exact Hwritten_left.
    + apply mutable_connected_refl.
    + exact Hwritten_right.
Qed.

Lemma actual_rdm_join_after_immutable_field_update_is_old_at_mutable_endpoint :
  forall CT h lx old field written left right,
    wf_heap CT h ->
    wf_heap CT (update_field h lx field (Iot written)) ->
    runtime_getObj h lx = Some old ->
    r_muttype h lx = Some Imm_r ->
    r_muttype h written = Some Imm_r ->
    r_muttype (update_field h lx field (Iot written)) left = Some Mut_r ->
    actual_rdm_join_edge
      CT (update_field h lx field (Iot written)) left right ->
    actual_rdm_join_edge CT h left right.
Proof.
  intros CT h lx old field written left right Hheap Hheap_post
    Hobj Hlx_imm Hwritten_imm Hleft_mut
    [left_root [right_root
      [Hdifferent [Hroots [Hleft Hright]]]]].
  destruct (mutable_connected_after_field_update CT h lx old field
    (Iot written) left_root right_root Hobj Hroots) as
    [Hroots_old |
      [new_written [Hwritten_value
        [[Hleft_root_lx Hwritten_right_root] |
         [Hleft_root_written Hlx_right_root]]]]];
  destruct (retained_reachable_after_field_update CT h lx old field
    (Iot written) left_root left Hobj Hleft) as
    [Hleft_old |
      [new_written_left
        [Hwritten_left_value [Hleft_root_lx' Hwritten_left]]]].
  - destruct (retained_reachable_after_field_update CT h lx old field
      (Iot written) right_root right Hobj Hright) as
      [Hright_old |
        [new_written_right
          [Hwritten_right_value [Hright_root_lx Hwritten_right]]]].
    + exists left_root, right_root. repeat split; assumption.
    + have Hright_root_imm :
          r_muttype h right_root = Some Imm_r.
      { eapply retained_reachable_reflects_runtime_context; eauto. }
      have Hleft_root_imm :
          r_muttype h left_root = Some Imm_r.
      { eapply mutable_connected_preserves_runtime_mutability.
        - exact Hheap.
        - eapply mutable_connected_sym. exact Hroots_old.
        - exact Hright_root_imm. }
      have Hleft_imm : r_muttype h left = Some Imm_r.
      { eapply retained_reachable_preserves_runtime_context; eauto. }
      rewrite r_muttype_update_field_preserve in Hleft_mut.
      congruence.
  - injection Hwritten_left_value as <-.
    have Hleft_imm : r_muttype h left = Some Imm_r.
    { eapply retained_reachable_preserves_runtime_context;
        [exact Hheap|exact Hwritten_left|exact Hwritten_imm]. }
    rewrite r_muttype_update_field_preserve in Hleft_mut.
    congruence.
  - have Hleft_root_imm :
        r_muttype h left_root = Some Imm_r.
    { eapply mutable_connected_preserves_runtime_mutability.
      - exact Hheap.
      - eapply mutable_connected_sym. exact Hleft_root_lx.
      - exact Hlx_imm. }
    have Hleft_imm : r_muttype h left = Some Imm_r.
    { eapply retained_reachable_preserves_runtime_context; eauto. }
    rewrite r_muttype_update_field_preserve in Hleft_mut.
    congruence.
  - injection Hwritten_left_value as <-.
    have Hleft_imm : r_muttype h left = Some Imm_r.
    { eapply retained_reachable_preserves_runtime_context;
        [exact Hheap|exact Hwritten_left|exact Hwritten_imm]. }
    rewrite r_muttype_update_field_preserve in Hleft_mut.
    congruence.
  - injection Hwritten_value as <-.
    have Hleft_root_imm :
        r_muttype h left_root = Some Imm_r.
    { eapply mutable_connected_preserves_runtime_mutability.
      - exact Hheap.
      - eapply mutable_connected_sym. exact Hleft_root_written.
      - exact Hwritten_imm. }
    have Hleft_imm : r_muttype h left = Some Imm_r.
    { eapply retained_reachable_preserves_runtime_context; eauto. }
    rewrite r_muttype_update_field_preserve in Hleft_mut.
    congruence.
  - injection Hwritten_left_value as <-.
    have Hleft_imm : r_muttype h left = Some Imm_r.
    { eapply retained_reachable_preserves_runtime_context;
        [exact Hheap|exact Hwritten_left|exact Hwritten_imm]. }
    rewrite r_muttype_update_field_preserve in Hleft_mut.
    congruence.
Qed.
*)

(*
These two wrappers target the discarded symmetric boundary graph.  Directed
field-transition preservation is proved below from endpoint color cases.

Lemma pending_call_colors_after_active_owned_field_update :
  forall CT h active stack lx old field written,
    runtime_getObj h lx = Some old ->
    frame_owned_location CT h active lx ->
    frame_owned_location CT h active written ->
    pending_call_ownership_colors_separated CT h active stack ->
    pending_call_ownership_colors_separated CT
      (update_field h lx field (Iot written)) active stack.
Proof.
  intros CT h active stack lx old field written Hobj Hlx_owned
    Hwritten_owned Hpending.
  eapply pending_call_colors_after_heap_change; [exact Hpending| |].
  - intros left right Hconnected.
    eapply boundary_connected_after_active_owned_field_update_is_old; eauto.
  - intros frame location Hlive Howned.
    eapply frame_owned_after_active_owned_field_update_has_boundary_origin;
      eauto.
Qed.

Lemma pending_call_colors_after_immutable_field_update :
  forall CT h active stack lx old field written,
    wf_heap CT h ->
    wf_heap CT (update_field h lx field (Iot written)) ->
    live_frames_wf CT h active stack ->
    live_frames_authority_sound h active stack ->
    live_frames_wf CT (update_field h lx field (Iot written)) active stack ->
    live_frames_authority_sound
      (update_field h lx field (Iot written)) active stack ->
    runtime_getObj h lx = Some old ->
    r_muttype h lx = Some Imm_r ->
    r_muttype h written = Some Imm_r ->
    potential_connected CT h active stack lx written ->
    potential_connected CT h active stack written lx ->
    pending_call_ownership_colors_separated CT h active stack ->
    pending_call_ownership_colors_separated CT
      (update_field h lx field (Iot written)) active stack.
Proof.
  intros CT h active stack lx old field written Hheap Hheap_post Hframes
    Hsound Hframes_post Hsound_post Hobj Hlx_imm Hwritten_imm
    Hlx_written Hwritten_lx Hpending boundary above below capability owned
    Hpartition Hchannel_free Howned Hcapability Hconnected.
  have Hcapability_global :
      In Loc
        (live_capability_set CT
          (update_field h lx field (Iot written)) active stack)
        capability.
  { eapply live_call_partition_caller_capability_is_live; eauto. }
  have Hcapability_mut :
      r_muttype (update_field h lx field (Iot written)) capability =
        Some Mut_r.
  { eapply live_capability_members_runtime_mutable; eauto. }
  have Hconnected_old :
      boundary_connected CT h active stack capability owned.
  { eapply
      boundary_connected_after_immutable_field_update_is_old_at_mutable_root;
      eauto. }
  have Howned_old :
      In Loc (live_capability_set CT h active above) owned.
  { apply live_capability_iff_live_frame_owned in Howned.
    destruct Howned as [frame [Hlive Hframe_owned]].
    apply live_capability_iff_live_frame_owned.
    exists frame. split; [exact Hlive|].
    eapply frame_owned_after_nonmutable_source_field_update_is_old.
    - exact Hheap.
    - exact Hframes.
    - exact Hsound.
    - exact Hobj.
    - congruence.
    - eapply live_call_partition_above_frame_is_live; eauto.
    - exact Hframe_owned. }
  have Hcapability_old :
      In Loc
        (live_capability_set CT h boundary.(boundary_caller) below)
        capability.
  { apply live_capability_iff_live_frame_owned in Hcapability.
    destruct Hcapability as [frame [Hlive Hframe_owned]].
    apply live_capability_iff_live_frame_owned.
    exists frame. split; [exact Hlive|].
    eapply frame_owned_after_nonmutable_source_field_update_is_old.
    - exact Hheap.
    - exact Hframes.
    - exact Hsound.
    - exact Hobj.
    - congruence.
    - eapply live_call_partition_below_frame_is_live; eauto.
    - exact Hframe_owned. }
  eapply Hpending; eauto.
Qed.
*)

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
Lemma live_history_after_field_write_given_colors :
  forall CT P Z cutoff authority sGamma mt rGamma h stack x field y
    sGamma' rGamma' h',
    live_authority_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack h ->
    stmt_typing CT sGamma mt (SFldWrite x field y) sGamma' ->
    readonly_state_method_scope mt ->
    eval_stmt CT rGamma h (SFldWrite x field y) OK rGamma' h' ->
    component_colors_separated CT h'
      (live_capability_set CT h'
        (mk_watched_frame authority sGamma' rGamma') stack) Z ->
    watched_frame_colors CT h'
      (live_capability_set CT h'
        (mk_watched_frame authority sGamma' rGamma') stack) Z
      (mk_watched_frame authority sGamma' rGamma') ->
    (forall location,
      In Loc (live_capability_set CT h'
        (mk_watched_frame authority sGamma' rGamma') stack) location ->
      ~ In Loc Z location) ->
    live_authority_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma' rGamma') stack h'.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack x field y
    sGamma' rGamma' h' Hlive Htyping Hscope Heval Hcomponents Hactive Havoid.
  assert (HsGamma : sGamma' = sGamma) by
    (inversion Htyping; reflexivity).
  assert (HrGamma : rGamma' = rGamma) by
    (inversion Heval; reflexivity).
  subst sGamma' rGamma'.
  destruct Hlive as
    [[Hdirected [Hauthority_roots [Hcontext Hauthority_colors]]]
      [[Hwf Hstack_wf]
      [[Hsound Hstack_sound] [Hcutoff [Hzone_bound Hchain]]]]].
  destruct Hdirected as
    [Hcontains [Hzone [Hconfined [Hclosed_old [Hruntime_old
      [Hmutroots_old Havoid_old]]]]]].
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
  have Hconfined' : state_is_confined P cutoff rGamma h'.
  { destruct Hconfined as [Hconfenv Hconfheap].
    split; [exact Hconfenv|].
    intros source target Hsource Hedge.
    inversion Heval; subst.
    destruct (raw_edge_after_update h loc_x o field val_y source target
      Hobj Hedge) as [Holdedge | [-> Hnewvalue]].
    - eapply Hconfheap; eauto.
    - rewrite Hnewvalue in Hval_y. eapply Hconfenv; eauto. }
  split.
  - split.
    + refine (conj Hcontains (conj Hzone (conj Hconfined'
        (conj Hclosed (conj Hruntime (conj _ Havoid)))))).
      intros root [variable [T [Htype [Hvalue Hmut]]]].
      apply Hroots. exists variable, T. repeat split; try assumption.
      unfold capability_in_context. left. exact Hmut.
    + split; [exact Hroots|].
      split; [exact (proj1 Hframes_sound)|].
      split; [exact Hcomponents|exact Hactive].
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
    sGamma' rGamma' h' [Hlive [Hpotential Hcutoffs]]
    Htyping Hscope Heval.
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
  - eapply live_history_after_field_write_given_colors; eauto.
    + eapply potential_colors_imply_component_colors; eauto.
    + eapply potential_colors_imply_active_colors; eauto.
    + intros location Hlocation Hprotected.
      apply (Hpotential_post location location Hlocation Hprotected).
      apply rt_refl.
  - split; [exact Hpotential_post|].
    eapply live_boundary_cutoffs_valid_heap_growth; [|exact Hcutoffs].
    eapply eval_stmt_preserves_heap_domain_simple; exact Heval.
Qed.

(** At an RDM-view call whose dynamic signature actually returns RDM, a fresh
    callee RDM result may later be installed in the suspended caller.  Besides
    ordinary active-frame creation roots, the allocation normal form must
    therefore include an immediate suspended-caller RDM root as an anchor. *)
Definition immediate_rdm_caller_root
  (h : heap) (active : watched_frame) (stack : list watched_boundary)
  (root : Loc) : Prop :=
  exists boundary tail,
    stack = boundary :: tail /\
    boundary.(boundary_receiver_view) = RDM /\
    boundary.(boundary_callee_return_qualifier) = RDM /\
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
    [boundary [tail [Hstack [Hview [Hcallee_return [Hroot Hcompat]]]]]].
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
    [boundary [tail
      [Hstack [Hview [Hcallee_return [Hcaller Hcompat]]]]]].
  subst stack. apply rt_step. right. right. exists active, boundary.
  split; [constructor|]. split; [exact Hview|].
  split; [exact Hcallee_return|].
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
    [boundary [tail
      [Hstack [Hview [Hcallee_return [Hcaller Hcompat]]]]]] Hactive.
  subst stack. apply rt_step. right. right. exists active, boundary.
  split; [constructor|]. split; [exact Hview|].
  split; [exact Hcallee_return|].
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
      [Hleft_return [Hleft_root Hleft_compat]]]]]]
    [right_boundary [right_tail [Hright_stack [Hright_view
      [Hright_return [Hright_root Hright_compat]]]]]].
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
    [boundary [tail
      [Hstack [Hview [Hcallee_return [Hroot Hcompat]]]]]].
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

Lemma fresh_mutable_edge_target_has_creation_root :
  forall CT sGamma mt rGamma h x qc C args sGamma' vals qruntime target,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    mutable_edge CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) (dom h) target ->
    typed_root (qc2q qc) sGamma rGamma target.
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' vals qruntime target
    Hwf Htyping Hvals Hedge.
  destruct (mutable_edge_after_append CT h
    (mkObj (mkruntime_type qruntime C) vals) (dom h) target Hedge) as
    [Hold | [Hfresh [field [D [fieldT
      [Hfield [Hbase [Hdef Hrdm]]]]]]]].
  - inversion Hold as [? ? oldobj ? ? ? Hobj].
    apply runtime_getObj_dom in Hobj. lia.
  - assert (HdefC : sf_def_rel CT C field fieldT).
    { eapply field_inheritance_subtyping; eauto. }
    eapply new_creation_rdm_field_target_has_creation_root; eauto.
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
  - destruct Hframe as
      [frame [Hlive [Hleft Hright]]].
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
      [callee [boundary
        [Hboundary [Hview [Hcallee_return
          [Hruntime [Hroots | Hroots]]]]]]].
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
           split; [exact Hcallee_return|].
           split; [exact Hruntime|]. left. split.
           ++ exact Hleft_old.
           ++ exists variable, T. repeat split; assumption.
        -- subst left. subst qc. right. split.
	           ++ apply potential_new_entry_fresh.
	           ++ apply potential_new_attachment_caller_rdm_root.
              exists boundary, tail. split; [reflexivity|].
              split; [exact Hview|]. split; [exact Hcallee_return|].
              split; [exact (proj2 Hroots)|].
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
        split; [exact Hcallee_return|].
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
           split; [exact Hcallee_return|].
           split; [exact Hruntime|]. right. split.
           ++ exists variable, T. repeat split; assumption.
           ++ exact Hright_old.
        -- subst right. subst qc. right. split.
	           ++ apply potential_new_entry_caller_rdm_root.
              exists boundary, tail. split; [reflexivity|].
              split; [exact Hview|]. split; [exact Hcallee_return|].
              split; [exact (proj1 Hroots)|].
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
        split; [exact Hcallee_return|].
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
  - destruct Hframe as
      [frame [Hlive [Hleft Hright]]].
    have Hframe_wf := live_frame_member_wf CT h active stack frame Hframes
      Hlive.
    destruct Hleft as [variable [T [Htype [Hvalue Hrdm]]]].
    eapply wf_config_value_dom; eauto.
  - destruct Hreturn as
      [callee [boundary
        [Hlive [Hview [Hcallee_return
          [Hruntime [Hroots | Hroots]]]]]]].
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
  - destruct Hframe as
      [frame [Hlive [Hleft Hright]]].
    have Hframe_wf := live_frame_member_wf CT h active stack frame Hframes
      Hlive.
    destruct Hright as [variable [T [Htype [Hvalue Hrdm]]]].
    eapply wf_config_value_dom; eauto.
  - destruct Hreturn as
      [callee [boundary
        [Hlive [Hview [Hcallee_return
          [Hruntime [Hroots | Hroots]]]]]]].
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

(** Allocation is the only statement that introduces a location not present
    in the pre-state color set.  A dangerous color at that fresh location is
    justified either by a mutable creation, or by an RDM creation joined to
    an old colored RDM root.  This is ghost evidence used only by the
    allocation proof. *)
Definition allocation_fresh_authorized
  (CT : class_table) (h : heap) (frame : watched_frame)
  (old_colors : Ensemble authority_flow_state) (qc : q_c) : Prop :=
  qc = Mut_c \/
  (qc = RDM_c /\
    (frame.(frame_authority) = Mut_r \/
     exists mode anchor,
       authority_mode_dangerous mode /\
       In authority_flow_state old_colors (mode, anchor) /\
       typed_root RDM frame.(frame_senv) frame.(frame_renv) anchor)).

Definition allocation_authority_state_covered
  (CT : class_table) (h : heap)
  (old_colors : Ensemble authority_flow_state) (qc : q_c)
  (frame : watched_frame) (state : authority_flow_state) : Prop :=
  authority_mode_dangerous (fst state) ->
  (exists old_mode,
      authority_mode_dangerous old_mode /\
      In authority_flow_state old_colors (old_mode, snd state)) \/
  (snd state = dom h /\
   allocation_fresh_authorized CT h frame old_colors qc).

Lemma executing_authority_typed_mut_root_is_powered :
  forall CT h frame incoming location,
    typed_root Mut frame.(frame_senv) frame.(frame_renv) location ->
    In authority_flow_state
      (executing_authority_color_set CT h frame incoming)
      (FlowPowered, location).
Proof.
  intros CT h frame incoming location Hroot.
  apply executing_authority_owned_is_powered.
  apply frame_owned_location_iff_active_live.
  eapply typed_mut_root_is_live_capability. exact Hroot.
Qed.

Lemma executing_authority_typed_rdm_root_under_mut_is_powered :
  forall CT h sGamma rGamma incoming location,
    typed_root RDM sGamma rGamma location ->
    In authority_flow_state
      (executing_authority_color_set CT h
        (mk_watched_frame Mut_r sGamma rGamma) incoming)
      (FlowPowered, location).
Proof.
  intros CT h sGamma rGamma incoming location Hroot.
  apply executing_authority_owned_is_powered.
  apply frame_owned_location_iff_active_live.
  eapply typed_rdm_root_is_live_under_mut_authority. exact Hroot.
Qed.

Lemma allocation_creation_root_is_old_colored :
  forall CT h frame incoming qc location,
    allocation_fresh_authorized CT h frame
      (executing_authority_color_set CT h frame incoming) qc ->
    typed_root (qc2q qc) frame.(frame_senv) frame.(frame_renv) location ->
    exists mode,
      authority_mode_dangerous mode /\
      In authority_flow_state
        (executing_authority_color_set CT h frame incoming)
        (mode, location).
Proof.
  intros CT h frame incoming qc location Hauthorized Hroot.
  destruct Hauthorized as [Hmut | [Hrdm Hauthorized]].
  - subst qc. exists FlowPowered. split; [left; reflexivity|].
    eapply executing_authority_typed_mut_root_is_powered. exact Hroot.
  - subst qc. simpl in Hroot.
    destruct Hauthorized as [Hauthority | [mode [anchor
      [Hmode [Hcolor Hanchor]]]]].
    + destruct frame as [authority sGamma rGamma]. simpl in *.
      subst authority. exists FlowPowered. split; [left; reflexivity|].
      eapply executing_authority_typed_rdm_root_under_mut_is_powered.
      exact Hroot.
    + exists FlowProspective. split; [right; reflexivity|].
      eapply executing_authority_dangerous_frame_join; eauto.
Qed.

Lemma r_muttype_some_dom :
  forall h location runtime_q,
    r_muttype h location = Some runtime_q ->
    location < dom h.
Proof.
  intros h location runtime_q Hruntime.
  unfold r_muttype in Hruntime.
  destruct (runtime_getObj h location) as [object|] eqn:Hobject;
    [apply runtime_getObj_dom in Hobject; exact Hobject|discriminate].
Qed.

Lemma allocation_typed_mut_root_is_old_colored :
  forall CT h frame incoming location,
    typed_root Mut frame.(frame_senv) frame.(frame_renv) location ->
    exists mode,
      authority_mode_dangerous mode /\
      In authority_flow_state
        (executing_authority_color_set CT h frame incoming)
        (mode, location).
Proof.
  intros. exists FlowPowered. split; [left; reflexivity|].
  eapply executing_authority_typed_mut_root_is_powered; eauto.
Qed.

Lemma allocation_fresh_retained_target_is_old_colored :
  forall CT sGamma mt rGamma h x qc C args sGamma' vals qruntime
    authority incoming target,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    allocation_fresh_authorized CT h
      (mk_watched_frame authority sGamma rGamma)
      (executing_authority_color_set CT h
        (mk_watched_frame authority sGamma rGamma) incoming) qc ->
    retained_mut_edge CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) (dom h) target ->
    exists mode,
      authority_mode_dangerous mode /\
      In authority_flow_state
        (executing_authority_color_set CT h
          (mk_watched_frame authority sGamma rGamma) incoming)
        (mode, target).
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' vals qruntime
    authority incoming target Hwf Htyping Hvals Hauthorized Hedge.
  destruct (retained_edge_after_append CT h
    (mkObj (mkruntime_type qruntime C) vals) (dom h) target Hedge) as
    [Hold | [Hfresh [field [D [fieldT [Hfield [Hbase [Hdefinition
      [Hrdm | Hmut]]]]]]]]].
  - inversion Hold as [? ? Hrdm_edge | ? ? object ? ? ? Hobject]; subst.
    + inversion Hrdm_edge as [? ? object ? ? ? Hobject].
      apply runtime_getObj_dom in Hobject. lia.
    + apply runtime_getObj_dom in Hobject. lia.
  - assert (Hdefinition_C : sf_def_rel CT C field fieldT).
    { eapply field_inheritance_subtyping; eauto. }
    have Hroot := new_creation_rdm_field_target_has_creation_root
      CT sGamma mt rGamma h x qc C args sGamma' vals field fieldT target
      Hwf Htyping Hvals Hfield Hdefinition_C Hrdm.
    eapply allocation_creation_root_is_old_colored; eauto.
  - assert (Hdefinition_C : sf_def_rel CT C field fieldT).
    { eapply field_inheritance_subtyping; eauto. }
    have Hroot := new_creation_mut_field_target_has_mut_root
      CT sGamma mt rGamma h x qc C args sGamma' vals field fieldT target
      Hwf Htyping Hvals Hfield Hdefinition_C Hmut.
    eapply allocation_typed_mut_root_is_old_colored; eauto.
Qed.

Lemma allocation_old_color_is_not_fresh :
  forall CT h frame incoming mode location,
    authority_colors_runtime_mutable h
      (executing_authority_color_set CT h frame incoming) ->
    In authority_flow_state
      (executing_authority_color_set CT h frame incoming) (mode, location) ->
    location <> dom h.
Proof.
  intros CT h frame incoming mode location Hruntime Hcolor Heq.
  have Hdom := r_muttype_some_dom h location Mut_r
    (Hruntime mode location Hcolor).
  lia.
Qed.

Lemma allocation_fresh_authorized_from_rdm_color :
  forall CT h frame incoming mode anchor,
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT h frame incoming) (mode, anchor) ->
    typed_root RDM frame.(frame_senv) frame.(frame_renv) anchor ->
    allocation_fresh_authorized CT h frame
      (executing_authority_color_set CT h frame incoming) RDM_c.
Proof.
  intros. right. split; [reflexivity|]. right.
  exists mode, anchor. repeat split; assumption.
Qed.

Lemma allocation_retained_step_preserves_coverage :
  forall CT sGamma mt rGamma h x qc C args sGamma' vals qruntime
    authority incoming mode left right,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    authority_colors_runtime_mutable h
      (executing_authority_color_set CT h
        (mk_watched_frame authority sGamma rGamma) incoming) ->
    authority_mode_dangerous mode ->
    allocation_authority_state_covered CT h
      (executing_authority_color_set CT h
        (mk_watched_frame authority sGamma rGamma) incoming)
      qc (mk_watched_frame authority sGamma rGamma) (mode, left) ->
    retained_mut_edge CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) left right ->
    allocation_authority_state_covered CT h
      (executing_authority_color_set CT h
        (mk_watched_frame authority sGamma rGamma) incoming)
      qc (mk_watched_frame authority sGamma rGamma) (mode, right).
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' vals qruntime
    authority incoming mode left right Hwf Htyping Hvals Hold_runtime Hmode
    Hcovered Hedge _.
  destruct (Hcovered Hmode) as
    [[old_mode [Hold_mode Hold_color]] | [Hleft_fresh Hauthorized]].
  - destruct (retained_edge_after_append CT h
      (mkObj (mkruntime_type qruntime C) vals) left right Hedge) as
      [Hold_edge | [Hsource Hnew]].
    + left. exists old_mode. split; [exact Hold_mode|].
      eapply executing_authority_dangerous_retained; eauto.
    + subst left. exfalso.
      eapply allocation_old_color_is_not_fresh; eauto.
  - simpl in Hleft_fresh. subst left. left.
    eapply allocation_fresh_retained_target_is_old_colored; eauto.
Qed.

Lemma allocation_reverse_rdm_step_preserves_coverage :
  forall CT sGamma mt rGamma h x qc C args sGamma' vals qruntime
    authority incoming mode left right,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    authority_colors_runtime_mutable h
      (executing_authority_color_set CT h
        (mk_watched_frame authority sGamma rGamma) incoming) ->
    authority_mode_dangerous mode ->
    allocation_authority_state_covered CT h
      (executing_authority_color_set CT h
        (mk_watched_frame authority sGamma rGamma) incoming)
      qc (mk_watched_frame authority sGamma rGamma) (mode, left) ->
    mutable_edge CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) right left ->
    allocation_authority_state_covered CT h
      (executing_authority_color_set CT h
        (mk_watched_frame authority sGamma rGamma) incoming)
      qc (mk_watched_frame authority sGamma rGamma)
      (FlowProspective, right).
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' vals qruntime
    authority incoming mode left right Hwf Htyping Hvals Hold_runtime Hmode
    Hcovered Hedge _. simpl.
  destruct (Hcovered Hmode) as
    [[old_mode [Hold_mode Hold_color]] | [Hleft_fresh Hauthorized]].
  - destruct (mutable_edge_after_append CT h
      (mkObj (mkruntime_type qruntime C) vals) right left Hedge) as
      [Hold_edge | [Hright_fresh Hnew]].
    + left. exists FlowProspective. split; [right; reflexivity|].
      eapply executing_authority_dangerous_reverse_rdm; eauto.
    + right. split; [exact Hright_fresh|].
      have Hroot := fresh_mutable_edge_target_has_creation_root CT sGamma mt
        rGamma h x qc C args sGamma' vals qruntime left Hwf Htyping Hvals.
      assert (Hedge_fresh : mutable_edge CT
          (h ++ [mkObj (mkruntime_type qruntime C) vals]) (dom h) left).
      { rewrite <- Hright_fresh. exact Hedge. }
      specialize (Hroot Hedge_fresh).
      destruct qc.
      * left. reflexivity.
      * simpl in Hroot.
        have Himmutable := typed_imm_root_runtime_immutable CT sGamma rGamma
          h left Hwf Hroot.
        have Hmutable := Hold_runtime old_mode left Hold_color.
        congruence.
      * eapply allocation_fresh_authorized_from_rdm_color; eauto.
  - simpl in Hleft_fresh. subst left.
    destruct (mutable_edge_after_append CT h
      (mkObj (mkruntime_type qruntime C) vals) right (dom h) Hedge) as
      [Hold_edge | [Hright_fresh Hnew]].
    + have Hdom := mutable_edge_target_dom CT h right (dom h)
        (proj1 (proj2 Hwf)) Hold_edge. lia.
    + have Hroot := fresh_mutable_edge_target_has_creation_root CT sGamma mt
        rGamma h x qc C args sGamma' vals qruntime (dom h) Hwf Htyping
        Hvals.
      subst right. specialize (Hroot Hedge).
      destruct Hroot as [variable [T [Htype [Hvalue Hqualifier]]]].
      have Hdom := wf_config_value_dom CT sGamma rGamma h variable (dom h)
        Hwf Hvalue. lia.
Qed.

Lemma allocation_frame_join_preserves_coverage :
  forall CT sGamma mt rGamma h x qc C args sGamma'
    authority incoming mode left right,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    authority_colors_runtime_mutable h
      (executing_authority_color_set CT h
        (mk_watched_frame authority sGamma rGamma) incoming) ->
    authority_mode_dangerous mode ->
    allocation_authority_state_covered CT h
      (executing_authority_color_set CT h
        (mk_watched_frame authority sGamma rGamma) incoming)
      qc (mk_watched_frame authority sGamma rGamma) (mode, left) ->
    typed_root RDM sGamma'
      (update_r_env_value rGamma x (Iot (dom h))) left ->
    typed_root RDM sGamma'
      (update_r_env_value rGamma x (Iot (dom h))) right ->
    allocation_authority_state_covered CT h
      (executing_authority_color_set CT h
        (mk_watched_frame authority sGamma rGamma) incoming)
      qc (mk_watched_frame authority sGamma rGamma)
      (FlowProspective, right).
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' authority incoming mode
    left right Hwf Htyping Hold_runtime Hmode Hcovered Hleft_root Hright_root
    _. simpl.
  destruct (new_active_rdm_root_origin CT sGamma mt rGamma h x qc C args
    sGamma' left Hwf Htyping Hleft_root) as
    [Hleft_old | [Hleft_fresh Hleft_qc]];
  destruct (new_active_rdm_root_origin CT sGamma mt rGamma h x qc C args
    sGamma' right Hwf Htyping Hright_root) as
    [Hright_old | [Hright_fresh Hright_qc]].
  - destruct (Hcovered Hmode) as
      [[old_mode [Hold_mode Hold_color]] | [Hsource_fresh Hauthorized]].
    + left. exists FlowProspective. split; [right; reflexivity|].
      eapply executing_authority_dangerous_frame_join; eauto.
    + simpl in Hsource_fresh. subst left.
      destruct Hleft_old as [variable [T [Htype [Hvalue Hrdm]]]].
      have Hdom := wf_config_value_dom CT sGamma rGamma h variable (dom h)
        Hwf Hvalue. lia.
  - subst right qc. right. split; [reflexivity|].
    destruct (Hcovered Hmode) as
      [[old_mode [Hold_mode Hold_color]] | [Hsource_fresh Hauthorized]].
    + exact (allocation_fresh_authorized_from_rdm_color CT h
        (mk_watched_frame authority sGamma rGamma) incoming old_mode left
        Hold_mode Hold_color Hleft_old).
    + simpl in Hsource_fresh. subst left.
      destruct Hleft_old as [variable [T [Htype [Hvalue Hrdm]]]].
      have Hdom := wf_config_value_dom CT sGamma rGamma h variable (dom h)
        Hwf Hvalue. lia.
  - destruct (Hcovered Hmode) as
      [[old_mode [Hold_mode Hold_color]] | [Hsource_fresh Hauthorized]].
    + subst left. exfalso.
      eapply allocation_old_color_is_not_fresh; eauto.
    + subst qc. left.
      eapply allocation_creation_root_is_old_colored; eauto.
  - subst left right qc. right. split; [reflexivity|].
    destruct (Hcovered Hmode) as
      [[old_mode [Hold_mode Hold_color]] | [Hsource_fresh Hauthorized]].
    + exfalso. eapply allocation_old_color_is_not_fresh; eauto.
    + exact Hauthorized.
Qed.

Lemma allocation_promote_preserves_coverage :
  forall CT sGamma mt rGamma h x qc C args sGamma' vals qreceiver qruntime
    authority incoming location,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    vpa_mutability_object_creation qreceiver qc = qruntime ->
    r_muttype
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) location = Some Mut_r ->
    frame_owned_location CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h)))) location ->
    allocation_authority_state_covered CT h
      (executing_authority_color_set CT h
        (mk_watched_frame authority sGamma rGamma) incoming)
      qc (mk_watched_frame authority sGamma rGamma)
      (FlowPowered, location).
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' vals qreceiver qruntime
    authority incoming location Hwf Htyping Hvals Hadapt Hruntime Howned _.
  have Horigin := new_live_reachability_after_new_has_origin CT authority
    sGamma mt rGamma h [] x qc C args sGamma' vals qruntime location Hwf
    (conj Hwf (Forall_nil _)) Htyping Hvals.
  apply frame_owned_location_iff_active_live in Howned.
  specialize (Horigin Howned).
  destruct Horigin as [Hfresh | Hold].
  - right. split; [exact Hfresh|]. subst location.
    destruct qc.
    + left. reflexivity.
    + destruct qreceiver; simpl in Hadapt; subst qruntime;
        unfold r_muttype in Hruntime;
        rewrite runtime_getObj_last in Hruntime; simpl in Hruntime;
        discriminate.
    + right. split; [reflexivity|]. left.
      have Hauthority := fresh_live_after_rdm_new_implies_mut_authority CT
        sGamma mt rGamma h x C args sGamma' vals qruntime authority [] Hwf
        (conj Hwf (Forall_nil _)) Htyping Hvals Howned.
      exact Hauthority.
  - left. exists FlowPowered. split; [left; reflexivity|].
    apply executing_authority_owned_is_powered.
    apply frame_owned_location_iff_active_live. exact Hold.
Qed.

Lemma allocation_frame_step_preserves_coverage :
  forall CT sGamma mt rGamma h x qc C args sGamma' vals qreceiver qruntime
    authority incoming source target,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    vpa_mutability_object_creation qreceiver qc = qruntime ->
    authority_colors_runtime_mutable h
      (executing_authority_color_set CT h
        (mk_watched_frame authority sGamma rGamma) incoming) ->
    authority_colors_runtime_mutable
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (executing_authority_color_set CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) incoming) ->
    In authority_flow_state
      (executing_authority_color_set CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) incoming) source ->
    allocation_authority_state_covered CT h
      (executing_authority_color_set CT h
        (mk_watched_frame authority sGamma rGamma) incoming)
      qc (mk_watched_frame authority sGamma rGamma) source ->
    phased_authority_frame_step CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h)))) source target ->
    allocation_authority_state_covered CT h
      (executing_authority_color_set CT h
        (mk_watched_frame authority sGamma rGamma) incoming)
      qc (mk_watched_frame authority sGamma rGamma) target.
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' vals qreceiver qruntime
    authority incoming source target Hwf Htyping Hvals Hadapt Hold_runtime
    Hpost_runtime Hsource_color Hsource_covered Hstep.
  have Htarget_color : In authority_flow_state
      (executing_authority_color_set CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) incoming) target.
  { destruct Hsource_color as [seed [Hseed Hpath]]. exists seed.
    split; [exact Hseed|]. eapply rt_trans; [exact Hpath|].
    apply rt_step. exact Hstep. }
  destruct target as [target_mode target_location].
  have Htarget_runtime := Hpost_runtime target_mode target_location
    Htarget_color.
  inversion Hstep; subst; simpl in *.
  - eapply allocation_retained_step_preserves_coverage; eauto.
    left. reflexivity.
  - eapply allocation_retained_step_preserves_coverage; eauto.
    right. reflexivity.
  - eapply allocation_reverse_rdm_step_preserves_coverage; eauto.
    right. reflexivity.
  - eapply allocation_reverse_rdm_step_preserves_coverage; eauto.
    left. reflexivity.
  - intros Hdangerous. destruct Hdangerous as [Hbad | Hbad]; discriminate.
  - intros Hdangerous. destruct Hdangerous as [Hbad | Hbad]; discriminate.
  - eapply allocation_frame_join_preserves_coverage; eauto.
    left. reflexivity.
  - eapply allocation_frame_join_preserves_coverage; eauto.
    right. reflexivity.
  - intros Hdangerous. destruct Hdangerous as [Hbad | Hbad]; discriminate.
  - intros Hdangerous. destruct Hdangerous as [Hbad | Hbad]; discriminate.
  - intros Hdangerous. destruct Hdangerous as [Hbad | Hbad]; discriminate.
  - intros Hdangerous.
    apply Hsource_covered. left. reflexivity.
  - eapply allocation_promote_preserves_coverage; eauto.
Qed.

Lemma allocation_frame_connected_preserves_coverage :
  forall CT sGamma mt rGamma h x qc C args sGamma' vals qreceiver qruntime
    authority incoming source target,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    vpa_mutability_object_creation qreceiver qc = qruntime ->
    authority_colors_runtime_mutable h
      (executing_authority_color_set CT h
        (mk_watched_frame authority sGamma rGamma) incoming) ->
    authority_colors_runtime_mutable
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (executing_authority_color_set CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) incoming) ->
    In authority_flow_state
      (executing_authority_color_set CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) incoming) source ->
    allocation_authority_state_covered CT h
      (executing_authority_color_set CT h
        (mk_watched_frame authority sGamma rGamma) incoming)
      qc (mk_watched_frame authority sGamma rGamma) source ->
    phased_authority_frame_connected CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h)))) source target ->
    allocation_authority_state_covered CT h
      (executing_authority_color_set CT h
        (mk_watched_frame authority sGamma rGamma) incoming)
      qc (mk_watched_frame authority sGamma rGamma) target.
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' vals qreceiver qruntime
    authority incoming source target Hwf Htyping Hvals Hadapt Hold_runtime
    Hpost_runtime Hsource_color Hsource_covered Hconnected.
  induction Hconnected.
  - eapply allocation_frame_step_preserves_coverage; eauto.
  - exact Hsource_covered.
  - assert (Hmiddle_color : In authority_flow_state
        (executing_authority_color_set CT
          (h ++ [mkObj (mkruntime_type qruntime C) vals])
          (mk_watched_frame authority sGamma'
            (update_r_env_value rGamma x (Iot (dom h)))) incoming) y).
    { destruct Hsource_color as [seed [Hseed Hpath]]. exists seed.
      split; [exact Hseed|]. eapply rt_trans; eauto. }
    have Hmiddle_covered :=
      IHHconnected1 Hsource_color Hsource_covered.
    exact (IHHconnected2 Hmiddle_color Hmiddle_covered).
Qed.

(** Allocation preserves the origin of every dangerous color at an old
    location.  The only alternative admitted by allocation coverage is the
    newly allocated location [dom h], which the strict bound excludes. *)
Lemma executing_authority_colors_after_new_covered :
  forall CT sGamma mt rGamma h x qc C args sGamma' vals
    qreceiver qruntime authority incoming,
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
    forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT
          (h ++ [mkObj (mkruntime_type qruntime C) vals])
          (mk_watched_frame authority sGamma'
            (update_r_env_value rGamma x (Iot (dom h)))) incoming)
        (mode, location) ->
      location < dom h ->
      exists old_mode,
        authority_mode_dangerous old_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h
            (mk_watched_frame authority sGamma rGamma) incoming)
          (old_mode, location).
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' vals qreceiver qruntime
    authority incoming Hwf Hpost_wf Hsound Hpost_sound Hincoming_runtime
    Htyping Hvals Hadapt mode location Hmode
    [seed [Hseed Hconnected]] Hlocation_old.
  have Hold_runtime : authority_colors_runtime_mutable h
      (executing_authority_color_set CT h
        (mk_watched_frame authority sGamma rGamma) incoming).
  { eapply executing_authority_colors_runtime_mutable; eauto. }
  have Hincoming_post : authority_colors_runtime_mutable
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) incoming.
  { intros incoming_mode incoming_location Hcolor.
    have Hruntime := Hincoming_runtime incoming_mode incoming_location Hcolor.
    have Hdom := r_muttype_some_dom h incoming_location Mut_r Hruntime.
    rewrite r_muttype_app_preserve_old; assumption. }
  have Hpost_runtime : authority_colors_runtime_mutable
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (executing_authority_color_set CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) incoming).
  { eapply executing_authority_colors_runtime_mutable; eauto. }
  assert (Hseed_covered : allocation_authority_state_covered CT h
      (executing_authority_color_set CT h
        (mk_watched_frame authority sGamma rGamma) incoming)
      qc (mk_watched_frame authority sGamma rGamma) seed).
  { destruct seed as [seed_mode seed_location]. simpl.
    intros Hseed_mode. inversion Hseed; subst.
    - left. exists seed_mode. split; [exact Hseed_mode|].
      exists (seed_mode, seed_location). split.
      + left. exact H.
      + apply rt_refl.
    - destruct H as [owned [Heq Howned]]. inversion Heq; subst.
      eapply allocation_promote_preserves_coverage; eauto.
      eapply Hpost_runtime. exists (FlowPowered, owned).
      split.
      + right. exists owned. split; [reflexivity|exact Howned].
      + apply rt_refl. }
  have Hseed_color : In authority_flow_state
      (executing_authority_color_set CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) incoming) seed.
  { exists seed. split; [exact Hseed|apply rt_refl]. }
  have Hcovered := allocation_frame_connected_preserves_coverage CT sGamma
    mt rGamma h x qc C args sGamma' vals qreceiver qruntime authority
    incoming seed (mode, location) Hwf Htyping Hvals Hadapt Hold_runtime
    Hpost_runtime Hseed_color Hseed_covered Hconnected Hmode.
  destruct Hcovered as
    [[old_mode [Hold_mode Hold_color]] | [Hfresh Hauthorized]].
  - exists old_mode. split; assumption.
  - simpl in Hfresh. subst location. lia.
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
    frozen_caller_snapshots_resume_roots_safe CT h Z
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
  intros CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qreceiver qruntime authority snapshots Hwf Hpost_wf Hsound Hpost_sound
    Htyping Hvals Hadapt Hcutoff Hzone Hruntime Hclosed Hroots Hexposure
    Hnested Hresume Hactive_safe.
  set (old_frame := mk_watched_frame authority sGamma rGamma).
  set (new_h := h ++ [mkObj (mkruntime_type qruntime C) vals]).
  set (new_frame := mk_watched_frame authority sGamma'
    (update_r_env_value rGamma x (Iot (dom h)))).
  eapply frozen_caller_snapshots_nested_resume_safe_after_classified_advance
    with (exceptional := independent_active_authority_colors CT h old_frame).
  - exact Hnested.
  - exact Hresume.
  - exact Hactive_safe.
  - intros snapshot older mode location Hsnapshot Holder Hmode Hcolor Hroot.
    have Hlocation_old : location < dom h.
    { unfold old_frame in Hroots. eapply Hroots; eauto. }
    have Hpost_color : In authority_flow_state
        (executing_authority_color_set CT new_h new_frame
          snapshot.(frozen_snapshot_current_colors)) (mode, location).
    { destruct Hcolor as [seed [Hseed Hpath]]. exists seed.
      split; [left; exact Hseed|].
      eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
    destruct (executing_authority_colors_after_new_covered CT sGamma mt
      rGamma h x qc C args sGamma' vals qreceiver qruntime authority
      snapshot.(frozen_snapshot_current_colors) Hwf Hpost_wf Hsound
      Hpost_sound (Hruntime snapshot Hsnapshot) Htyping Hvals Hadapt mode
      location Hmode Hpost_color Hlocation_old) as
      [old_mode [Hold_mode Hold_color]].
    unfold old_frame.
    eapply executing_with_frozen_incoming_dangerous_covered_by_old_or_active;
      eauto.
  - intros snapshot mode location Hsnapshot Hmode Hcolor Hprotected.
    have Hlocation_old : location < dom h.
    { have Hbefore := Hzone location Hprotected. lia. }
    have Hpost_color : In authority_flow_state
        (executing_authority_color_set CT new_h new_frame
          snapshot.(frozen_snapshot_current_resume_exposure))
        (mode, location).
    { destruct Hcolor as [seed [Hseed Hpath]]. exists seed.
      split; [left; exact Hseed|].
      eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
    destruct (executing_authority_colors_after_new_covered CT sGamma mt
      rGamma h x qc C args sGamma' vals qreceiver qruntime authority
      snapshot.(frozen_snapshot_current_resume_exposure) Hwf Hpost_wf Hsound
      Hpost_sound ((proj1 Hexposure) snapshot Hsnapshot) Htyping Hvals Hadapt
      mode location Hmode Hpost_color Hlocation_old) as
      [old_mode [Hold_mode Hold_color]].
    unfold old_frame.
    eapply executing_with_frozen_incoming_dangerous_covered_by_old_or_active.
    + exact ((proj1 (proj2 Hexposure)) snapshot Hsnapshot).
    + exact Hold_mode.
    + exact Hold_color.
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
  intros CT Z cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qreceiver qruntime authority incoming snapshots Hwf Hpost_wf Hsound
    Hpost_sound Hincoming_runtime Htyping Hvals Hadapt Hcutoff Hzone Hroots
    Hexposure Hcompleted Hactive_safe new_snapshot source_mode source Hnew
    Hsource_mode Hsource Hsource_root.
  set (old_frame := mk_watched_frame authority sGamma rGamma).
  set (new_h := h ++ [mkObj (mkruntime_type qruntime C) vals]).
  set (new_frame := mk_watched_frame authority sGamma'
    (update_r_env_value rGamma x (Iot (dom h)))).
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot. simpl in *.
  have Hsource_old : source < dom h by
    (unfold old_frame in Hroots; eapply Hroots; eauto).
  destruct (executing_authority_colors_after_new_covered CT sGamma mt
    rGamma h x qc C args sGamma' vals qreceiver qruntime authority incoming
    Hwf Hpost_wf Hsound Hpost_sound Hincoming_runtime Htyping Hvals Hadapt
    source_mode source Hsource_mode Hsource Hsource_old) as
    [old_source_mode [Hold_source_mode Hold_source]].
  unfold old_frame in Hcompleted.
  destruct (Hcompleted old_snapshot old_source_mode source Hold
    Hold_source_mode Hold_source Hsource_root) as
    [[entry_mode [Hentry_mode Hentry]] | Hsafe].
  - left. exists entry_mode. split; assumption.
  - right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
    have Htarget_old : target < dom h.
    { have Hbefore := Hzone target Hprotected. lia. }
    have Hpost_target : In authority_flow_state
        (executing_authority_color_set CT new_h new_frame
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
      CT h old_frame old_snapshot.(frozen_snapshot_current_resume_exposure)
      old_target_mode target ((proj1 (proj2 Hexposure)) old_snapshot Hold)
      Hold_target_mode Hold_target) as
      [[snapshot_target_mode [Hsnapshot_target_mode Hsnapshot_target]] |
       [active_target_mode [Hactive_target_mode Hactive_target]]].
    + exact (Hsafe snapshot_target_mode target Hsnapshot_target_mode
        Hsnapshot_target Hprotected).
    + exact (Hactive_safe active_target_mode target Hactive_target_mode
        Hactive_target Hprotected).
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
    sGamma' rGamma' h' [Hlive [Hpotential Hcutoffs]] Htyping Heval.
  have Hcomponent : component_forward_history_state CT P Z
      (live_capability_set CT h
        (mk_watched_frame authority sGamma rGamma) stack)
      cutoff sGamma rGamma h.
  { eapply mutable_authority_component_history
      with (authority := authority).
    exact (proj1 Hlive). }
  have Hlive_post := live_history_after_new CT P Z cutoff authority sGamma mt
    rGamma h stack x qc C args sGamma' rGamma' h' Hlive Hcomponent Htyping
    Heval.
  split; [exact Hlive_post|].
  split.
  destruct Hlive as
    [Hhistory [Hframes [Hsound [Hcutoff [Hzone_bound Hauthority_chain]]]]].
  have Hwf : wf_r_config CT sGamma rGamma h := proj1 Hframes.
  inversion Heval; subst.
  assert (Hupdate :
      set_vars rGamma (update x (Iot (dom h)) (vars rGamma)) =
      update_r_env_value rGamma x (Iot (dom h))).
  { destruct rGamma. reflexivity. }
  rewrite Hupdate in Hlive_post |- *.
  { match goal with
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
  }
  { eapply live_boundary_cutoffs_valid_heap_growth; [|exact Hcutoffs].
    eapply eval_stmt_preserves_heap_domain_simple; exact Heval.
  }
Qed.

Lemma fresh_retained_edge_target_has_creation_authority_root :
  forall CT sGamma mt rGamma h x qc C args sGamma' vals qruntime target,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    retained_mut_edge CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) (dom h) target ->
    typed_root (qc2q qc) sGamma rGamma target \/
    typed_root Mut sGamma rGamma target.
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' vals qruntime target
    Hwf Htyping Hvals Hedge.
  destruct (retained_edge_after_append CT h
    (mkObj (mkruntime_type qruntime C) vals) (dom h) target Hedge) as
    [Hold | [Hfresh [field [D [fieldT [Hfield [Hbase [Hdefinition
      [Hrdm | Hmut]]]]]]]]].
  - inversion Hold as [? ? Hrdm_edge | ? ? object ? ? ? Hobject]; subst.
    + inversion Hrdm_edge as [? ? object ? ? ? Hobject].
      apply runtime_getObj_dom in Hobject. lia.
    + apply runtime_getObj_dom in Hobject. lia.
  - left. assert (Hdefinition_C : sf_def_rel CT C field fieldT).
    { eapply field_inheritance_subtyping; eauto. }
    eapply new_creation_rdm_field_target_has_creation_root; eauto.
  - right. assert (Hdefinition_C : sf_def_rel CT C field fieldT).
    { eapply field_inheritance_subtyping; eauto. }
    eapply new_creation_mut_field_target_has_mut_root; eauto.
Qed.

Definition allocation_prospective_location_covered
  (CT : class_table) (h : heap) (frame : watched_frame)
  (location : Loc) : Prop :=
  location = dom h \/
  prospective_location_covered_by_frame CT h frame location.

Lemma active_allocation_prospective_step_covered :
  forall CT authority sGamma mt rGamma h x qc C args sGamma' vals qruntime
    source target,
    wf_r_config CT sGamma rGamma h ->
    authority_context_sound h rGamma authority ->
    wf_r_config CT sGamma'
      (update_r_env_value rGamma x (Iot (dom h)))
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    r_muttype (h ++ [mkObj (mkruntime_type qruntime C) vals]) source =
      Some Mut_r ->
    r_muttype (h ++ [mkObj (mkruntime_type qruntime C) vals]) target =
      Some Mut_r ->
    allocation_prospective_location_covered CT h
      (mk_watched_frame authority sGamma rGamma) source ->
    frozen_caller_authority_step CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h))))
      (FlowProspective, source) (FlowProspective, target) ->
    allocation_prospective_location_covered CT h
      (mk_watched_frame authority sGamma rGamma) target.
Proof.
  intros CT authority sGamma mt rGamma h x qc C args sGamma' vals qruntime
    source target Hwf Hsound Hpost_wf Htyping Hvals Hsource_runtime
    Htarget_runtime Hsource Hstep.
  inversion Hstep; subst.
  - destruct (retained_edge_after_append CT h
      (mkObj (mkruntime_type qruntime C) vals) source target H1) as
      [Hold_edge | [Hsource_fresh Hnew_edge]].
    + destruct Hsource as [Hfresh | [root [Hroot Hpath]]].
      * subst source. exfalso.
        inversion Hold_edge as
          [edge_source edge_target Hrdm |
           edge_source edge_target object field D field_def Hobject]; subst.
        -- inversion Hrdm as
             [rdm_source rdm_target object field D field_def Hobject].
           apply runtime_getObj_dom in Hobject. lia.
        -- apply runtime_getObj_dom in Hobject. lia.
      * right. exists root. split; [exact Hroot|].
        eapply rt_trans; [exact Hpath|]. apply rt_step.
        apply frozen_caller_prospective_retained. exact Hold_edge.
    + subst source.
      have Horigin := fresh_retained_edge_target_has_creation_authority_root
        CT sGamma mt rGamma h x qc C args sGamma' vals qruntime target Hwf
        Htyping Hvals H1.
      have Htarget_old_runtime : r_muttype h target = Some Mut_r.
      { destruct Horigin as [Hcreation | Hmut];
          destruct Hcreation as
            [variable [T [Htype [Hvalue Hqualifier]]]] ||
          destruct Hmut as [variable [T [Htype [Hvalue Hqualifier]]]];
          have Htarget_dom := wf_config_value_dom CT sGamma rGamma h variable
            target Hwf Hvalue;
          eapply r_muttype_app_preserve_old_Some; eauto. }
      right. exists target. split; [|apply rt_refl].
      destruct Horigin as [Hcreation | Hmut].
      * destruct qc; simpl in Hcreation.
        -- left. exact Hcreation.
        -- have Himmutable := typed_imm_root_runtime_immutable CT sGamma
             rGamma h target Hwf Hcreation. congruence.
        -- right. split; assumption.
      * left. exact Hmut.
  - destruct (mutable_edge_after_append CT h
      (mkObj (mkruntime_type qruntime C) vals) target source H1) as
      [Hold_edge | [Htarget_fresh Hnew_edge]].
    + destruct Hsource as [Hfresh | [root [Hroot Hpath]]].
      * subst source.
        have Hsource_dom := mutable_edge_target_dom CT h target (dom h)
          (proj1 (proj2 Hwf)) Hold_edge. lia.
      * right. exists root. split; [exact Hroot|].
        eapply rt_trans; [exact Hpath|]. apply rt_step.
        apply frozen_caller_prospective_rdm_backward. exact Hold_edge.
    + left. exact Htarget_fresh.
  - destruct (new_active_rdm_root_origin CT sGamma mt rGamma h x qc C args
      sGamma' target Hwf Htyping H2) as
      [Hold_root | [Htarget_fresh Hcreation]].
    + right. exists target. split; [|apply rt_refl].
      right. split; [exact Hold_root|].
      destruct Hold_root as [variable [T [Htype [Hvalue Hrdm]]]].
      have Htarget_dom := wf_config_value_dom CT sGamma rGamma h variable
        target Hwf Hvalue.
      eapply r_muttype_app_preserve_old_Some; eauto.
    + left. exact Htarget_fresh.
Qed.

Definition active_allocation_prospective_state_covered
  (CT : class_table) (h post_h : heap) (frame : watched_frame)
  (state : authority_flow_state) : Prop :=
  fst state = FlowProspective /\
  r_muttype post_h (snd state) = Some Mut_r /\
  allocation_prospective_location_covered CT h frame (snd state).

Definition suspended_allocation_component_covered
  (CT : class_table) (h : heap) (suspended active : watched_frame)
  (location : Loc) : Prop :=
  prospective_location_covered_by_frame CT h suspended location \/
  prospective_location_covered_by_frame CT h active location.

Definition suspended_allocation_location_covered
  (CT : class_table) (h : heap) (suspended active : watched_frame)
  (location : Loc) : Prop :=
  location = dom h \/
  suspended_allocation_component_covered CT h suspended active location.
