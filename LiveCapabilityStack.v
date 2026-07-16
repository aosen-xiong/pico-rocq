Require Import Syntax Notations Helpers Typing Subtyping Bigstep.
Require Import ViewpointAdaptation Properties Preservation ReadonlyHelper.
Require Import Reachability MutableCapability AuthorityCapability
  ComponentColoring.
Require Import ExecutionConfinement ProtectionHistory ForwardCapabilityHistory
  AuthorityHistory WatchedFrames.
Require Import CallFrameWellformed.
From Stdlib Require Import List Sets.Ensembles.
Import ListNotations.

(** Live capabilities are derived from variables that still occur in an
    active or suspended frame. *)
Definition frame_capability_root
  (frame : watched_frame) (root : Loc) : Prop :=
  exists x T,
    static_getType frame.(frame_senv) x = Some T /\
    runtime_getVal frame.(frame_renv) x = Some (Iot root) /\
    capability_in_context frame.(frame_authority) (sqtype T).

Definition boundary_capability_root
  (boundary : watched_boundary) (root : Loc) : Prop :=
  frame_capability_root boundary.(boundary_caller) root.

Definition live_capability_root
  (active : watched_frame) (stack : list watched_boundary)
  (root : Loc) : Prop :=
  frame_capability_root active root \/
  exists boundary,
    List.In boundary stack /\ boundary_capability_root boundary root.

Definition live_capability_reachable
  (CT : class_table) (h : heap)
  (active : watched_frame) (stack : list watched_boundary)
  (location : Loc) : Prop :=
  exists root,
    live_capability_root active stack root /\
    mutable_reachable CT h root location.

Definition live_frames_wf
  (CT : class_table) (h : heap)
  (active : watched_frame) (stack : list watched_boundary) : Prop :=
  wf_r_config CT active.(frame_senv) active.(frame_renv) h /\
  Forall (fun boundary =>
    wf_r_config CT boundary.(boundary_caller).(frame_senv)
      boundary.(boundary_caller).(frame_renv) h) stack.

Definition live_frames_authority_sound
  (h : heap) (active : watched_frame)
  (stack : list watched_boundary) : Prop :=
  authority_context_sound h active.(frame_renv) active.(frame_authority) /\
  Forall (fun boundary =>
    authority_context_sound h
      boundary.(boundary_caller).(frame_renv)
      boundary.(boundary_caller).(frame_authority)) stack.

Definition live_capability_set
  (CT : class_table) (h : heap)
  (active : watched_frame) (stack : list watched_boundary) : Ensemble Loc :=
  fun location => live_capability_reachable CT h active stack location.

Definition protected_zone_before_cutoff
  (Z : Ensemble Loc) (cutoff : Loc) : Prop :=
  forall location, In Loc Z location -> location < cutoff.

Fixpoint live_stack_authorities_chain
  (active_authority : q_r) (stack : list watched_boundary) : Prop :=
  match stack with
  | [] => True
  | boundary :: tail =>
      active_authority =
        call_authority boundary.(boundary_caller).(frame_authority)
          boundary.(boundary_receiver_view) /\
      live_stack_authorities_chain
        boundary.(boundary_caller).(frame_authority) tail
  end.

Definition live_authority_history_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary) (h : heap) : Prop :=
  authority_component_history_state CT P Z
    (live_capability_set CT h active stack) cutoff
    active.(frame_authority) active.(frame_senv) active.(frame_renv) h /\
  live_frames_wf CT h active stack /\
  live_frames_authority_sound h active stack /\
  cutoff <= dom h /\
  protected_zone_before_cutoff Z cutoff /\
  live_stack_authorities_chain active.(frame_authority) stack.

Lemma mutable_reachable_transitive :
  forall CT h l1 l2 l3,
    mutable_reachable CT h l1 l2 ->
    mutable_reachable CT h l2 l3 ->
    mutable_reachable CT h l1 l3.
Proof.
  intros CT h l1 l2 l3 H12 H23.
  revert l1 H12.
  induction H23 as [l | start middle finish Hprefix IH Hedge]; intros.
  - exact H12.
  - eapply mr_step.
    + exact (IH l1 H12).
    + exact Hedge.
Qed.

Lemma live_capability_reachable_trans :
  forall CT h active stack root location,
    live_capability_reachable CT h active stack root ->
    mutable_reachable CT h root location ->
    live_capability_reachable CT h active stack location.
Proof.
  intros CT h active stack root location
    [origin [Hlive Hreach1]] Hreach2.
  exists origin. split; [exact Hlive|].
  eapply mutable_reachable_transitive; eauto.
Qed.

Lemma frame_capability_root_runtime_mutable :
  forall CT h frame root,
    wf_r_config CT frame.(frame_senv) frame.(frame_renv) h ->
    authority_context_sound h frame.(frame_renv) frame.(frame_authority) ->
    frame_capability_root frame root ->
    r_muttype h root = Some Mut_r.
Proof.
  intros CT h [authority sGamma rGamma] root Hwf Hsound
    [x [T [Htype [Hvalue Hcapability]]]]. simpl in *.
  destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwf)
    as [this [qcontext [Hthis [_ Hqcontext]]]].
  have Hwf_copy := Hwf.
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [_ [_ [_ Hcorr]]]]].
  have Hdom := Htype. apply static_getType_dom in Hdom.
  specialize (Hcorr this qcontext Hthis Hqcontext x Hdom T Htype).
  rewrite Hvalue in Hcorr.
  destruct Hcapability as [Hmut | [Hrdm Hauthority]].
  - unfold wf_r_typable, r_type in Hcorr.
    destruct (runtime_getObj h root) as [object|] eqn:Hobj;
      try contradiction.
    destruct Hcorr as [_ Hqualifier].
    unfold qualifier_typable_context, vpa_mutability_rs in Hqualifier.
    rewrite Hmut in Hqualifier.
    unfold r_muttype. rewrite Hobj. simpl.
    destruct (rqtype (rt_type object)), qcontext;
      try contradiction; reflexivity.
  - subst authority.
    have Hroot_context := rdm_typable_runtime_matches_context
      CT rGamma h root T qcontext Hcorr Hrdm.
    destruct (Hsound eq_refl) as
      [authority_this [Hauthority_this Hauthority_runtime]].
    rewrite Hthis in Hauthority_this. injection Hauthority_this as <-.
    rewrite Hqcontext in Hauthority_runtime.
    injection Hauthority_runtime as <-. exact Hroot_context.
Qed.

Lemma frame_capability_root_dom :
  forall CT h frame root,
    wf_r_config CT frame.(frame_senv) frame.(frame_renv) h ->
    frame_capability_root frame root ->
    root < dom h.
Proof.
  intros CT h frame root Hwf
    [x [T [_ [Hvalue _]]]].
  eapply wf_config_value_dom; eauto.
Qed.

Lemma live_capability_members_runtime_mutable :
  forall CT h active stack,
    live_frames_wf CT h active stack ->
    live_frames_authority_sound h active stack ->
    mutable_members_runtime_mut h
      (live_capability_set CT h active stack).
Proof.
  intros CT h active stack [Hactive_wf Hstack_wf]
    [Hactive_sound Hstack_sound] location
    [root [[Hactive_root | [boundary [Hin Hboundary_root]]] Hreach]].
  - have Hroot_runtime := frame_capability_root_runtime_mutable
      CT h active root Hactive_wf Hactive_sound Hactive_root.
    eapply mutable_reachable_preserves_runtime_mutability; eauto.
    exact (proj1 (proj2 Hactive_wf)).
  - apply Forall_forall with (x := boundary) in Hstack_wf; [|exact Hin].
    apply Forall_forall with (x := boundary) in Hstack_sound; [|exact Hin].
    have Hroot_runtime := frame_capability_root_runtime_mutable
      CT h boundary.(boundary_caller) root Hstack_wf Hstack_sound
      Hboundary_root.
    eapply mutable_reachable_preserves_runtime_mutability; eauto.
    exact (proj1 (proj2 Hactive_wf)).
Qed.

Lemma live_capability_set_forward_closed :
  forall CT h active stack,
    mutable_heap_closed CT h (live_capability_set CT h active stack).
Proof.
  intros CT h active stack source target Hsource Hedge.
  eapply live_capability_reachable_trans; [exact Hsource|].
  eapply mr_step; [constructor|exact Hedge].
Qed.

Lemma active_authority_roots_are_live :
  forall CT h active stack,
    authority_env_roots_in active.(frame_authority)
      (live_capability_set CT h active stack)
      active.(frame_senv) active.(frame_renv).
Proof.
  intros CT h active stack root Hroot.
  exists root. split.
  - left. exact Hroot.
  - constructor.
Qed.

Lemma initial_live_capability_set_empty :
  forall CT sGamma rGamma h,
    authority_env_roots_in Imm_r (Empty_set Loc) sGamma rGamma ->
    forall location,
      ~ In Loc (live_capability_set CT h
        (mk_watched_frame Imm_r sGamma rGamma) []) location.
Proof.
  intros CT sGamma rGamma h Hroots location
    [root [[Hactive | Hstack] Hreach]].
    + destruct (Hroots root Hactive).
    + destruct Hstack as [boundary [Hin _]]. inversion Hin.
Qed.

Lemma authority_component_history_shrink_before_initialization :
  forall CT P Z Mbig Msmall cutoff authority sGamma rGamma h,
    authority_component_history_state CT P Z Mbig cutoff authority
      sGamma rGamma h ->
    Included Loc Msmall Mbig ->
    mutable_heap_closed CT h Msmall ->
    mutable_members_runtime_mut h Msmall ->
    authority_env_roots_in authority Msmall sGamma rGamma ->
    authority_component_history_state CT P Z Msmall cutoff authority
      sGamma rGamma h.
Proof.
  intros CT P Z Mbig Msmall cutoff authority sGamma rGamma h
    [[[Hcontains [Hzone [Hconfined [Hclosed_big [Hruntime_big
      [Hmutroots_big [Havoid Hrdm]]]]]]]
      [Hcomponents Hactive]] [Hauthority_roots Hcontext]]
    Hincluded Hclosed Hruntime Hroots.
  split.
  - split.
    + refine (conj Hcontains (conj Hzone (conj Hconfined
        (conj Hclosed (conj Hruntime (conj _ (conj _ _))))))).
      * intros root [x [T [Htype [Hvalue Hmut]]]].
        apply Hroots. exists x, T. repeat split; try assumption.
        unfold capability_in_context. left. exact Hmut.
      * intros location Hin. apply Havoid. apply Hincluded. exact Hin.
      * intros capability_root zone_root
          [Hcaproot [capability [Hcapreach Hcapability]]]
          [Hzoneroot [protected [Hzonereach Hprotected]]].
        eapply Hrdm.
        -- split; [exact Hcaproot|]. exists capability.
           split; [exact Hcapreach|]. apply Hincluded. exact Hcapability.
        -- split; [exact Hzoneroot|]. exists protected. split; assumption.
    + split.
      * intros capability protected Hcapability Hprotected Hconnected.
        eapply Hcomponents; [apply Hincluded; exact Hcapability| |]; eauto.
      * intros capability_root zone_root Hcaproot
          [capability [Hcapability Hcapconnected]] Hzoneroot Hzonetouch.
        eapply Hactive with (capability_root := capability_root)
          (zone_root := zone_root); eauto.
        exists capability. split; [apply Hincluded; exact Hcapability|].
        exact Hcapconnected.
  - split; assumption.
Qed.

Lemma initial_live_authority_history :
  forall CT sGamma rGamma h,
    wf_r_config CT sGamma rGamma h ->
    env_respects_protected_set
      (reachable_locations_from_initial_env CT h rGamma) sGamma rGamma ->
    live_authority_history_state CT
      (reachable_locations_from_initial_env CT h rGamma)
      (reachable_locations_from_initial_env CT h rGamma)
      (dom h) (mk_watched_frame Imm_r sGamma rGamma) [] h.
Proof.
  intros CT sGamma rGamma h Hwf Henv.
  have Hinitial := initial_authority_component_history CT sGamma rGamma h
    Hwf Henv.
  have Hempty := initial_live_capability_set_empty CT sGamma rGamma h
    (proj1 (proj2 Hinitial)).
  have Hcomponent : authority_component_history_state CT
      (reachable_locations_from_initial_env CT h rGamma)
      (reachable_locations_from_initial_env CT h rGamma)
      (live_capability_set CT h
        (mk_watched_frame Imm_r sGamma rGamma) [])
      (dom h) Imm_r sGamma rGamma h.
  { eapply authority_component_history_shrink_before_initialization
      with (Mbig := Empty_set Loc); eauto.
    - intros location Hlocation. exfalso. exact (Hempty location Hlocation).
    - intros source target Hsource. exfalso. exact (Hempty source Hsource).
    - intros location Hlocation. exfalso. exact (Hempty location Hlocation).
    - intros root Hroot. exfalso.
      destruct ((proj1 (proj2 Hinitial)) root Hroot). }
  unfold live_authority_history_state.
  split; [exact Hcomponent|].
  split; [split; [exact Hwf|constructor]|].
  split.
  - split.
    + intros Hbad. discriminate.
    + constructor.
  - split; [lia|]. split.
    + intros location Hin.
      eapply reachable_locations_from_initial_env_dom; eauto.
    + simpl. exact I.
Qed.

Lemma authority_component_history_shrink :
  forall CT P Z Mbig Msmall cutoff authority sGamma rGamma h,
    authority_component_history_state CT P Z Mbig cutoff authority
      sGamma rGamma h ->
    Included Loc Msmall Mbig ->
    mutable_heap_closed CT h Msmall ->
    mutable_members_runtime_mut h Msmall ->
    authority_env_roots_in authority Msmall sGamma rGamma ->
    authority_component_history_state CT P Z Msmall cutoff authority
      sGamma rGamma h.
Proof.
  intros CT P Z Mbig Msmall cutoff authority sGamma rGamma h
    [[[Hcontains [Hzone [Hconfined [Hclosed_big [Hruntime_big
      [Hmutroots_big [Havoid Hrdm]]]]]]]
      [Hcomponents Hactive]] [Hauthority_roots Hcontext]]
    Hincluded Hclosed Hruntime Hroots.
  split.
  - split.
    + refine (conj Hcontains (conj Hzone (conj Hconfined
        (conj Hclosed (conj Hruntime (conj _ (conj _ _))))))).
      * intros root [x [T [Htype [Hvalue Hmut]]]].
        apply Hroots. exists x, T. repeat split; try assumption.
        unfold capability_in_context. left. exact Hmut.
      * intros location Hin. apply Havoid. apply Hincluded. exact Hin.
      * intros capability_root zone_root
          [Hcaproot [capability [Hcapreach Hcapability]]]
          [Hzoneroot [protected [Hzonereach Hprotected]]].
        eapply Hrdm.
        -- split; [exact Hcaproot|]. exists capability.
           split; [exact Hcapreach|]. apply Hincluded. exact Hcapability.
        -- split; [exact Hzoneroot|]. exists protected. split; assumption.
    + split.
      * intros capability protected Hcapability Hprotected Hconnected.
        eapply Hcomponents; [apply Hincluded; exact Hcapability| |]; eauto.
      * intros capability_root zone_root Hcaproot
          [capability [Hcapability Hcapconnected]] Hzoneroot Hzonetouch.
        eapply Hactive with (capability_root := capability_root)
          (zone_root := zone_root); eauto.
        exists capability. split; [apply Hincluded; exact Hcapability|].
        exact Hcapconnected.
  - split; assumption.
Qed.

(** The heap-wide part of a history is independent of the currently active
    frame.  Reactivating a suspended caller therefore needs only the caller's
    environment facts, root inclusion, authority soundness, and its RDM color
    condition; all heap closure and separation facts are reused. *)
Lemma authority_component_history_reframe :
  forall CT P Z M cutoff source_authority source_senv source_renv
    target_authority target_senv target_renv h,
    authority_component_history_state CT P Z M cutoff source_authority
      source_senv source_renv h ->
    zone_env_safe Z target_senv target_renv ->
    env_is_confined P cutoff target_renv ->
    authority_env_roots_in target_authority M target_senv target_renv ->
    authority_context_sound h target_renv target_authority ->
    active_rdm_component_colors_separated CT h M Z target_senv target_renv ->
    authority_component_history_state CT P Z M cutoff target_authority
      target_senv target_renv h.
Proof.
  intros CT P Z M cutoff source_authority source_senv source_renv
    target_authority target_senv target_renv h
    [[[Hcontains [Hsource_zone [[Hsource_env Hheap_confined]
      [Hclosed [Hruntime [Hsource_mut_roots [Havoid Hsource_rdm]]]]]]]
      [Hcomponents Hsource_active]] [Hsource_roots Hsource_sound]]
    Htarget_zone Htarget_env Htarget_roots Htarget_sound Htarget_active.
  split.
  - split.
    + refine (conj Hcontains (conj Htarget_zone
        (conj (conj Htarget_env Hheap_confined)
          (conj Hclosed (conj Hruntime (conj _ (conj Havoid _))))))).
      * intros root Hmutroot. apply Htarget_roots.
        destruct Hmutroot as [x [T [Htype [Hvalue Hmut]]]].
        exists x, T. repeat split; try assumption.
        unfold capability_in_context. left. exact Hmut.
      * intros capability_root zone_root
          [Hcaproot [capability [Hcapreach Hcapability]]]
          [Hzoneroot [protected [Hzonereach Hprotected]]].
        eapply Htarget_active with
          (capability_root := capability_root) (zone_root := zone_root);
          try exact Hcaproot; try exact Hzoneroot.
        -- exists capability. split; [exact Hcapability|].
           eapply mutable_reachable_connected; eauto.
        -- exists protected. split; [exact Hprotected|].
           eapply mutable_reachable_connected; eauto.
    + split; [exact Hcomponents|exact Htarget_active].
  - split; assumption.
Qed.

Definition preserves_old_runtime_types (h h' : heap) : Prop :=
  dom h <= dom h' /\
  forall location,
    location < dom h -> r_type h' location = r_type h location.

Lemma preserved_r_type_preserves_r_muttype :
  forall h h' location,
    r_type h' location = r_type h location ->
    r_muttype h' location = r_muttype h location.
Proof.
  intros h h' location Htype.
  unfold r_type, r_muttype in *.
  destruct (runtime_getObj h' location) as [new_object|] eqn:Hnew;
  destruct (runtime_getObj h location) as [old_object|] eqn:Hold;
  simpl in *; try discriminate; try reflexivity.
  injection Htype as Hruntime_type. rewrite Hruntime_type. reflexivity.
Qed.

Lemma wf_r_config_preserved_by_runtime_types :
  forall CT sGamma rGamma h h',
    wf_r_config CT sGamma rGamma h ->
    wf_heap CT h' ->
    preserves_old_runtime_types h h' ->
    wf_r_config CT sGamma rGamma h'.
Proof.
  intros CT sGamma rGamma h h'
    [Hclass [Hheap [Hrenv [Hsenv [Hlength Hcorr]]]]] Hheap'
    [Hdom Htypes].
  destruct Hrenv as [Hnonempty [[receiver [Hreceiver Hreceiver_dom]] Hvalues]].
  refine (conj Hclass (conj Hheap' (conj _
    (conj Hsenv (conj Hlength _))))).
  - split; [exact Hnonempty|]. split.
    + exists receiver. split; [exact Hreceiver|lia].
    + eapply Forall_impl; [|exact Hvalues].
      intros entry Hentry. destruct entry as [|location|n].
      * exact I.
      * destruct (runtime_getObj h location) as [old_object|] eqn:Hold;
          try contradiction.
        have Hlocation_dom := Hold. apply runtime_getObj_dom in Hlocation_dom.
        have Htype := Htypes location Hlocation_dom.
        unfold r_type in Htype. rewrite Hold in Htype.
        destruct (runtime_getObj h' location); simpl in *;
          try discriminate; exact I.
      * exact I.
  - intros this qcontext Hthis Hthis_mut i Hi sqt Hsqt.
    assert (Hthis_eq : this = receiver) by congruence. subst this.
    have Hreceiver_type := Htypes receiver Hreceiver_dom.
    have Hmut_eq := preserved_r_type_preserves_r_muttype h h' receiver
      Hreceiver_type.
    rewrite Hmut_eq in Hthis_mut.
    have Hentry := Hcorr receiver qcontext Hreceiver Hthis_mut i Hi sqt Hsqt.
    destruct (runtime_getVal rGamma i) as [entry|] eqn:Hvalue;
      [|exact Hentry].
    destruct entry as [|location|n].
    + exact I.
    + unfold wf_r_typable in Hentry |- *.
      destruct (r_type h location) as [runtime_type|] eqn:Holdtype;
        try contradiction.
      have Hlocation_dom : location < dom h.
      { unfold r_type in Holdtype.
        destruct (runtime_getObj h location) as [object|] eqn:Hobject;
          try discriminate.
        apply runtime_getObj_dom in Hobject. exact Hobject. }
      rewrite (Htypes location Hlocation_dom).
      rewrite Holdtype. exact Hentry.
    + exact Hentry.
Qed.

Lemma field_update_preserves_old_runtime_types :
  forall h source field value,
    preserves_old_runtime_types h (update_field h source field value).
Proof.
  intros h source field value. split.
  - unfold update_field.
    destruct (runtime_getObj h source); simpl; rewrite ?update_length; lia.
  - intros location Hlocation.
    unfold r_type, update_field.
    destruct (runtime_getObj h source) as [source_object|] eqn:Hsource;
      [|reflexivity].
    destruct (Nat.eq_dec location source) as [->|Hneq].
    + have Hsame := runtime_getObj_update_same h source
        (set_fields_map source_object
          (update field value (fields_map source_object))) Hlocation.
      rewrite Hsame. rewrite Hsource. reflexivity.
    + have Hdiff := runtime_getObj_update_diff h source location
        (set_fields_map source_object
          (update field value (fields_map source_object)))
        (not_eq_sym Hneq).
      rewrite Hdiff. reflexivity.
Qed.

Lemma heap_append_preserves_old_runtime_types :
  forall h new_object,
    preserves_old_runtime_types h (h ++ [new_object]).
Proof.
  intros h new_object. split.
  - rewrite length_app. simpl. lia.
  - intros location Hlocation. unfold r_type.
    rewrite <- (runtime_getObj_app_left_equal h new_object location Hlocation).
    reflexivity.
Qed.

Lemma authority_context_sound_preserved_by_runtime_types :
  forall h h' rGamma authority,
    authority_context_sound h rGamma authority ->
    preserves_old_runtime_types h h' ->
    authority_context_sound h' rGamma authority.
Proof.
  intros h h' rGamma authority Hsound [Hdom Htypes] Hauthority.
  destruct (Hsound Hauthority) as [receiver [Hreceiver Hruntime]].
  exists receiver. split; [exact Hreceiver|].
  have Hruntime_copy := Hruntime.
  unfold r_muttype in Hruntime_copy.
  destruct (runtime_getObj h receiver) as [object|] eqn:Hobject;
    try discriminate.
  have Hreceiver_dom := Hobject. apply runtime_getObj_dom in Hreceiver_dom.
  have Htype := Htypes receiver Hreceiver_dom.
  have Hmut := preserved_r_type_preserves_r_muttype h h' receiver Htype.
  rewrite Hmut. exact Hruntime.
Qed.

Lemma live_frames_preserved_by_runtime_types :
  forall CT h h' active stack,
    live_frames_wf CT h active stack ->
    live_frames_authority_sound h active stack ->
    wf_heap CT h' ->
    preserves_old_runtime_types h h' ->
    live_frames_wf CT h' active stack /\
    live_frames_authority_sound h' active stack.
Proof.
  intros CT h h' active stack [Hactive_wf Hstack_wf]
    [Hactive_sound Hstack_sound] Hheap Htypes.
  split.
  - split.
    + eapply wf_r_config_preserved_by_runtime_types;
        [exact Hactive_wf|exact Hheap|exact Htypes].
    + eapply Forall_impl; [|exact Hstack_wf].
      intros boundary Hframe.
      eapply wf_r_config_preserved_by_runtime_types;
        [exact Hframe|exact Hheap|exact Htypes].
  - split.
    + eapply authority_context_sound_preserved_by_runtime_types;
        [exact Hactive_sound|exact Htypes].
    + eapply Forall_impl; [|exact Hstack_sound].
      intros boundary Hframe.
      eapply authority_context_sound_preserved_by_runtime_types;
        [exact Hframe|exact Htypes].
Qed.

Lemma live_capability_set_in_closed_superset :
  forall CT h h' active stack M,
    Included Loc (live_capability_set CT h active stack) M ->
    mutable_heap_closed CT h' M ->
    Included Loc (live_capability_set CT h' active stack) M.
Proof.
  intros CT h h' active stack M Hincluded Hclosed location
    [root [Hroot Hreach]].
  eapply mutable_heap_closed_reachable; [exact Hclosed|exact Hreach|].
  apply Hincluded. exists root. split; [exact Hroot|constructor].
Qed.

Lemma live_capability_set_after_active_change_in_superset :
  forall CT h h' old_active new_active stack M,
    Included Loc (live_capability_set CT h old_active stack) M ->
    authority_env_roots_in new_active.(frame_authority) M
      new_active.(frame_senv) new_active.(frame_renv) ->
    mutable_heap_closed CT h' M ->
    Included Loc (live_capability_set CT h' new_active stack) M.
Proof.
  intros CT h h' old_active new_active stack M Hold Hactive Hclosed location
    [root [Hlive Hreach]].
  eapply mutable_heap_closed_reachable; [exact Hclosed|exact Hreach|].
  destruct Hlive as [Hnew_root | [boundary [Hin Hboundary_root]]].
  - apply Hactive. exact Hnew_root.
  - apply Hold. exists root. split.
    + right. exists boundary. split; assumption.
    + constructor.
Qed.

(** A capability-bearing callee root is an actual capability root in the
    caller.  This is the call-boundary fact needed to push a continuation
    frame without inventing authority. *)
Lemma safe_call_callee_capability_root_reflects_to_caller :
  forall CT caller_authority sGamma mt rGamma h x y m args sGamma'
    vals ly cy runtime_mdef Ty root,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x y m args) sGamma' ->
    safe_readonly_method_type mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    frame_capability_root
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals))) root ->
    frame_capability_root
      (mk_watched_frame caller_authority sGamma rGamma) root.
Proof.
  intros CT caller_authority sGamma mt rGamma h x y m args sGamma'
    vals ly cy runtime_mdef Ty root Hwf Htyping Hscope Hgety Hval Hbase
    Hfind Hargs [z [T [Htype [Hrootval Hcap]]]].
  destruct Hcap as [Hmut | [Hrdm Hcallee_authority]].
  - exfalso. eapply safe_call_callee_has_no_mut_root with
      (CT := CT) (sGamma := sGamma) (mt := mt) (rGamma := rGamma)
      (h := h) (x := x) (m := m) (y := y) (args := args)
      (sGamma' := sGamma') (vals := vals) (ly := ly) (cy := cy)
      (runtime_mdef := runtime_mdef) (root := root); eauto.
    exists z, T. repeat split; assumption.
  - assert (Hrootrdm : typed_root RDM
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) root).
    { exists z, T. repeat split; assumption. }
    destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x y m
      args sGamma' vals ly cy runtime_mdef root Hwf Htyping Hscope Hval Hbase
      Hfind Hargs Hrootrdm) as
      [[Ty0 [Hgety0 [Hshape Hcallerroot]]] |
       [Ty0 [Hgety0 [Hro Hroot]]]].
    + assert (Ty0 = Ty) by congruence. subst Ty0.
      destruct Hcallerroot as
        [caller_var [CallerT [Hcaller_type [Hcaller_val Hcaller_qual]]]].
      exists caller_var, CallerT. repeat split; try assumption.
      rewrite Hcaller_qual.
      apply (safe_call_receiver_authority_reflects
        caller_authority (sqtype Ty)).
      * eapply wf_config_nonnull_variable_not_bot; eauto.
      * unfold capability_in_context. right. split.
        -- reflexivity.
        -- exact Hcallee_authority.
    + assert (Ty0 = Ty) by congruence. subst Ty0.
      rewrite Hro in Hcallee_authority. discriminate.
Qed.

Lemma call_push_preserves_live_capability_roots :
  forall CT caller_authority sGamma mt rGamma h x y m args sGamma'
    vals ly cy runtime_mdef Ty origins stack root,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x y m args) sGamma' ->
    safe_readonly_method_type mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    live_capability_root
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals)))
      (mk_watched_boundary
        (mk_watched_frame caller_authority sGamma rGamma)
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals)) (sqtype Ty) origins :: stack) root ->
    live_capability_root
      (mk_watched_frame caller_authority sGamma rGamma) stack root.
Proof.
  intros CT caller_authority sGamma mt rGamma h x y m args sGamma'
    vals ly cy runtime_mdef Ty origins stack root Hwf Htyping Hscope Hgety
    Hval Hbase Hfind Hargs [Hactive | [boundary [Hin Hboundary]]].
  - left. eapply safe_call_callee_capability_root_reflects_to_caller; eauto.
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + subst boundary. left. exact Hboundary.
    + right. exists boundary. split; assumption.
Qed.

Lemma caller_roots_remain_live_after_call_push :
  forall caller_authority sGamma rGamma entry_senv entry_renv receiver_view origins
    callee stack root,
    live_capability_root
      (mk_watched_frame caller_authority sGamma rGamma) stack root ->
    live_capability_root callee
      (mk_watched_boundary
        (mk_watched_frame caller_authority sGamma rGamma)
        entry_senv entry_renv receiver_view origins :: stack) root.
Proof.
  intros * [Hactive | [boundary [Hin Hboundary]]].
  - right. eexists. split; [left; reflexivity|exact Hactive].
  - right. exists boundary. split; [right; exact Hin|exact Hboundary].
Qed.

Lemma call_push_live_reachability_equivalent :
  forall CT caller_authority sGamma mt rGamma h x y m args sGamma'
    vals ly cy runtime_mdef Ty origins stack location,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x y m args) sGamma' ->
    safe_readonly_method_type mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    (live_capability_reachable CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals)))
      (mk_watched_boundary
        (mk_watched_frame caller_authority sGamma rGamma)
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals)) (sqtype Ty) origins :: stack) location <->
     live_capability_reachable CT h
      (mk_watched_frame caller_authority sGamma rGamma) stack location).
Proof.
  intros CT caller_authority sGamma mt rGamma h x y m args sGamma'
    vals ly cy runtime_mdef Ty origins stack location Hwf Htyping Hscope
    Hgety Hval Hbase Hfind Hargs. split.
  - intros [root [Hroot Hreach]]. exists root. split; [|exact Hreach].
    eapply call_push_preserves_live_capability_roots; eauto.
  - intros [root [Hroot Hreach]]. exists root. split; [|exact Hreach].
    eapply caller_roots_remain_live_after_call_push; eauto.
Qed.

(** A successful safe call cannot manufacture authority at return.  If the
    destination type is capability-bearing in the caller, then the method
    body's (non-bottom) return type is capability-bearing under the authority
    transferred to the callee. *)
Lemma safe_call_result_capability_reflects_to_body_return :
  forall caller_authority receiver_q body_return_q declared_return_q result_q,
    q_subtype body_return_q declared_return_q ->
    q_subtype
      (vpa_mutability_qq_safe_ro receiver_q declared_return_q) result_q ->
    receiver_q <> Bot ->
    body_return_q <> Bot ->
    capability_in_context caller_authority result_q ->
    capability_in_context
      (call_authority caller_authority receiver_q) body_return_q.
Proof.
  intros caller_authority receiver_q body_return_q declared_return_q result_q
    Hbody_sub Hresult_sub Hreceiver_nonbottom Hreturn_nonbottom
    Hresult_capability.
  destruct caller_authority, receiver_q, body_return_q, declared_return_q,
    result_q; simpl in *; try contradiction;
    repeat match goal with
    | H : q_subtype _ _ |- _ => inversion H; subst; clear H
    end;
    unfold capability_in_context in *; try solve [intuition congruence].
Qed.

Lemma safe_call_return_destination_is_safe :
  forall caller_authority receiver_q body_return_q declared_return_q result_q,
    q_subtype body_return_q declared_return_q ->
    q_subtype
      (vpa_mutability_qq_safe_ro receiver_q declared_return_q) result_q ->
    receiver_q <> Bot ->
    body_return_q <> Bot ->
    is_safe_mode body_return_q ->
    ~ capability_in_context
      (call_authority caller_authority receiver_q) body_return_q ->
    is_safe_mode result_q.
Proof.
  intros caller_authority receiver_q body_return_q declared_return_q result_q
    Hbody_sub Hresult_sub Hreceiver_nonbottom Hreturn_nonbottom Hreturn_safe
    Hreturn_not_capability.
  destruct caller_authority, receiver_q, body_return_q, declared_return_q,
    result_q; simpl in *; try contradiction;
    repeat match goal with
    | H : q_subtype _ _ |- _ => inversion H; subst; clear H
    end;
    unfold is_safe_mode, capability_in_context in *;
    try solve [intuition congruence].
Qed.

(** The qualifier reflection above lifts to runtime frames: a non-null return
    value assigned to a capability-bearing caller destination is an active
    capability root in the final callee frame. *)
Lemma safe_call_return_value_is_callee_capability_root :
  forall CT caller_authority caller_senv caller_renv caller_h
    receiver receiver_location receiver_type destination_type
    callee_senv callee_renv callee_h return_var body_return_type
    declared_return_type return_location,
    wf_r_config CT caller_senv caller_renv caller_h ->
    static_getType caller_senv receiver = Some receiver_type ->
    runtime_getVal caller_renv receiver = Some (Iot receiver_location) ->
    wf_r_config CT callee_senv callee_renv callee_h ->
    static_getType callee_senv return_var = Some body_return_type ->
    runtime_getVal callee_renv return_var = Some (Iot return_location) ->
    qualified_type_subtype CT body_return_type declared_return_type ->
    qualified_type_subtype CT
      (vpa_mutability_tt_safe_ro receiver_type declared_return_type)
      destination_type ->
    capability_in_context caller_authority (sqtype destination_type) ->
    frame_capability_root
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv) return_location.
Proof.
  intros CT caller_authority caller_senv caller_renv caller_h receiver
    receiver_location receiver_type destination_type callee_senv callee_renv
    callee_h return_var body_return_type declared_return_type return_location
    Hcaller_wf Hreceiver_type Hreceiver_value Hcallee_wf Hreturn_type
    Hreturn_value Hbody_sub Hresult_sub Hresult_capability.
  exists return_var, body_return_type. repeat split; try assumption.
  eapply safe_call_result_capability_reflects_to_body_return.
  - exact (qualified_type_subtype_q_subtype CT body_return_type
      declared_return_type Hbody_sub).
  - rewrite <- sq_vpa_tt_eq_qq_safe_ro.
    exact (qualified_type_subtype_q_subtype CT
      (vpa_mutability_tt_safe_ro receiver_type declared_return_type)
      destination_type Hresult_sub).
  - eapply (wf_config_nonnull_variable_not_bot CT caller_senv caller_renv
      caller_h receiver receiver_type receiver_location); eauto.
  - eapply (wf_config_nonnull_variable_not_bot CT callee_senv callee_renv
      callee_h return_var body_return_type return_location); eauto.
  - exact Hresult_capability.
Qed.

(** Returning a value into the caller preserves the caller's protected-zone
    typing.  The only subtle qualifier case is an RDM return adapted through a
    mutable receiver; that case would be a callee capability in [M], which the
    history proves cannot point into [Z]. *)
Lemma call_return_preserves_zone_env_safe :
  forall CT P Z M cutoff caller_authority caller_senv caller_renv caller_h
    destination destination_type receiver receiver_location receiver_type
    callee_senv callee_renv callee_h return_var body_return_type
    declared_return_type return_location,
    zone_env_safe Z caller_senv caller_renv ->
    wf_r_config CT caller_senv caller_renv caller_h ->
    static_getType caller_senv destination = Some destination_type ->
    static_getType caller_senv receiver = Some receiver_type ->
    runtime_getVal caller_renv receiver = Some (Iot receiver_location) ->
    wf_r_config CT callee_senv callee_renv callee_h ->
    static_getType callee_senv return_var = Some body_return_type ->
    runtime_getVal callee_renv return_var = Some (Iot return_location) ->
    qualified_type_subtype CT body_return_type declared_return_type ->
    qualified_type_subtype CT
      (vpa_mutability_tt_safe_ro receiver_type declared_return_type)
      destination_type ->
    authority_component_history_state CT P Z M cutoff
      (call_authority caller_authority (sqtype receiver_type))
      callee_senv callee_renv callee_h ->
    zone_env_safe Z caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)).
Proof.
  intros CT P Z M cutoff caller_authority caller_senv caller_renv caller_h
    destination destination_type receiver receiver_location receiver_type
    callee_senv callee_renv callee_h return_var body_return_type
    declared_return_type return_location Hcaller_zone Hcaller_wf
    Hdestination_type Hreceiver_type Hreceiver_value Hcallee_wf Hreturn_type
    Hreturn_value Hbody_sub Hresult_sub
    [[[Hcontains [Hcallee_zone [Hconfined [Hclosed [Hruntime
      [Hmutroots [Havoid Hrdm]]]]]]] [Hcomponents Hactive]]
      [Hroots Hsound]].
  intros variable location variable_type Hvariable_type Hvariable_value
    Hlocation_zone.
  destruct (Nat.eq_dec variable destination) as [->|Hneq].
  - assert (Hdestination_dom : destination < dom (vars caller_renv)).
    { apply static_getType_dom in Hdestination_type.
      unfold wf_r_config in Hcaller_wf.
      destruct Hcaller_wf as [_ [_ [_ [_ [Hlength _]]]]]. lia. }
    have Hupdated := runtime_getVal_update_same caller_renv destination
      (Iot return_location) Hdestination_dom.
    rewrite Hupdated in Hvariable_value. injection Hvariable_value as <-.
    rewrite Hdestination_type in Hvariable_type.
    injection Hvariable_type as <-.
    have Hreturn_safe : is_safe_mode (sqtype body_return_type).
    { eapply Hcallee_zone; eauto. }
    have Hreceiver_nonbottom : sqtype receiver_type <> Bot.
    { eapply (wf_config_nonnull_variable_not_bot CT caller_senv caller_renv
        caller_h receiver receiver_type receiver_location); eauto. }
    have Hreturn_nonbottom : sqtype body_return_type <> Bot.
    { eapply (wf_config_nonnull_variable_not_bot CT callee_senv callee_renv
        callee_h return_var body_return_type return_location); eauto. }
    apply (safe_call_return_destination_is_safe caller_authority
      (sqtype receiver_type) (sqtype body_return_type)
      (sqtype declared_return_type) (sqtype destination_type)).
    + exact (qualified_type_subtype_q_subtype CT body_return_type
        declared_return_type Hbody_sub).
    + rewrite <- sq_vpa_tt_eq_qq_safe_ro.
      exact (qualified_type_subtype_q_subtype CT
        (vpa_mutability_tt_safe_ro receiver_type declared_return_type)
        destination_type Hresult_sub).
    + exact Hreceiver_nonbottom.
    + exact Hreturn_nonbottom.
    + exact Hreturn_safe.
    + intros Hreturn_capability.
      have Hreturn_in_M : In Loc M return_location.
      { apply Hroots. exists return_var, body_return_type.
        repeat split; assumption. }
      exact (Havoid return_location Hreturn_in_M Hlocation_zone).
  - have Hunchanged := runtime_getVal_update_diff caller_renv destination
      variable (Iot return_location).
    assert (Hneq' : destination <> variable) by congruence.
    specialize (Hunchanged Hneq'). rewrite Hunchanged in Hvariable_value.
    eapply Hcaller_zone; eauto.
Qed.

Lemma call_return_preserves_env_confinement :
  forall P cutoff caller_renv callee_renv destination return_var
    return_location,
    env_is_confined P cutoff caller_renv ->
    env_is_confined P cutoff callee_renv ->
    runtime_getVal callee_renv return_var = Some (Iot return_location) ->
    env_is_confined P cutoff
      (update_r_env_value caller_renv destination (Iot return_location)).
Proof.
  intros P cutoff caller_renv callee_renv destination return_var
    return_location Hcaller Hcallee Hreturn.
  eapply env_confined_update; [exact Hcaller|].
  eapply Hcallee; eauto.
Qed.

Lemma authority_context_sound_after_nonreceiver_update :
  forall h rGamma authority destination value,
    authority_context_sound h rGamma authority ->
    destination <> 0 ->
    authority_context_sound h
      (update_r_env_value rGamma destination value) authority.
Proof.
  intros h rGamma authority destination value Hsound Hnot_receiver
    Hmutable_authority.
  destruct (Hsound Hmutable_authority) as
    [receiver [Hreceiver Hreceiver_mutable]].
  exists receiver. split; [|exact Hreceiver_mutable].
  unfold update_r_env_value. destruct rGamma; simpl in *.
  rewrite get_this_var_mapping_update_nonzero; assumption.
Qed.

(** Popping a successful call cannot expose a new capability root.  Unchanged
    caller roots are represented by the suspended caller boundary; the only
    changed root is the destination, whose value is reflected to the callee's
    return variable by the preceding lemma. *)
Lemma call_return_live_root_reflects_before_pop :
  forall CT caller_authority caller_senv caller_renv caller_h
    stack destination destination_type receiver receiver_location receiver_type
    entry_senv entry_renv origins callee_senv callee_renv callee_h
    return_var body_return_type declared_return_type return_location root,
    wf_r_config CT caller_senv caller_renv caller_h ->
    static_getType caller_senv destination = Some destination_type ->
    static_getType caller_senv receiver = Some receiver_type ->
    runtime_getVal caller_renv receiver = Some (Iot receiver_location) ->
    wf_r_config CT callee_senv callee_renv callee_h ->
    static_getType callee_senv return_var = Some body_return_type ->
    runtime_getVal callee_renv return_var = Some (Iot return_location) ->
    qualified_type_subtype CT body_return_type declared_return_type ->
    qualified_type_subtype CT
      (vpa_mutability_tt_safe_ro receiver_type declared_return_type)
      destination_type ->
    live_capability_root
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      stack root ->
    live_capability_root
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type) origins :: stack) root.
Proof.
  intros CT caller_authority caller_senv caller_renv caller_h stack
    destination destination_type receiver receiver_location receiver_type
    entry_senv entry_renv origins callee_senv callee_renv callee_h return_var
    body_return_type declared_return_type return_location root Hcaller_wf
    Hdestination_type Hreceiver_type Hreceiver_value Hcallee_wf Hreturn_type
    Hreturn_value Hbody_sub Hresult_sub
    [Hactive | [boundary [Hin Hboundary_root]]].
  - destruct Hactive as
      [variable [variable_type [Hvariable_type [Hvariable_value Hcapability]]]].
    destruct (Nat.eq_dec variable destination) as [->|Hneq].
    + assert (Hdestination_dom : destination < dom (vars caller_renv)).
      { apply static_getType_dom in Hdestination_type.
        unfold wf_r_config in Hcaller_wf.
        destruct Hcaller_wf as [_ [_ [_ [_ [Hlength _]]]]]. lia. }
      have Hupdated := runtime_getVal_update_same caller_renv destination
        (Iot return_location) Hdestination_dom.
      rewrite Hupdated in Hvariable_value.
      injection Hvariable_value as <-.
      rewrite Hdestination_type in Hvariable_type.
      injection Hvariable_type as <-.
      left. exact (safe_call_return_value_is_callee_capability_root CT
        caller_authority caller_senv caller_renv caller_h receiver
        receiver_location receiver_type destination_type callee_senv
        callee_renv callee_h return_var body_return_type declared_return_type
        return_location Hcaller_wf Hreceiver_type Hreceiver_value Hcallee_wf
        Hreturn_type Hreturn_value Hbody_sub Hresult_sub Hcapability).
    + have Hunchanged := runtime_getVal_update_diff caller_renv destination
        variable (Iot return_location).
      assert (Hneq' : destination <> variable) by congruence.
      specialize (Hunchanged Hneq').
      rewrite Hunchanged in Hvariable_value.
      right. exists (mk_watched_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type) origins). split.
      * left. reflexivity.
      * exists variable, variable_type. repeat split; assumption.
  - right. exists boundary. split; [right; exact Hin|exact Hboundary_root].
Qed.

Lemma call_return_live_reachability_reflects_before_pop :
  forall CT caller_authority caller_senv caller_renv caller_h
    stack destination destination_type receiver receiver_location receiver_type
    entry_senv entry_renv origins callee_senv callee_renv callee_h
    return_var body_return_type declared_return_type return_location location,
    wf_r_config CT caller_senv caller_renv caller_h ->
    static_getType caller_senv destination = Some destination_type ->
    static_getType caller_senv receiver = Some receiver_type ->
    runtime_getVal caller_renv receiver = Some (Iot receiver_location) ->
    wf_r_config CT callee_senv callee_renv callee_h ->
    static_getType callee_senv return_var = Some body_return_type ->
    runtime_getVal callee_renv return_var = Some (Iot return_location) ->
    qualified_type_subtype CT body_return_type declared_return_type ->
    qualified_type_subtype CT
      (vpa_mutability_tt_safe_ro receiver_type declared_return_type)
      destination_type ->
    live_capability_reachable CT callee_h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      stack location ->
    live_capability_reachable CT callee_h
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type) origins :: stack) location.
Proof.
  intros * Hcaller_wf Hdestination_type Hreceiver_type Hreceiver_value
    Hcallee_wf Hreturn_type Hreturn_value Hbody_sub Hresult_sub
    [root [Hroot Hreach]].
  exists root. split; [|exact Hreach].
  eapply call_return_live_root_reflects_before_pop with
    (caller_h := caller_h) (callee_h := callee_h)
    (destination_type := destination_type)
    (receiver_location := receiver_location)
    (receiver_type := receiver_type)
    (body_return_type := body_return_type)
    (declared_return_type := declared_return_type)
    (return_location := return_location); eauto.
Qed.

(** All call-return bookkeeping except preservation of the suspended caller's
    RDM color condition.  Keeping that condition explicit identifies the sole
    PICO-specific body-summary obligation; no theorem-strength premise is
    hidden in environment or capability transfer. *)
Lemma live_history_leave_call_given_caller_colors :
  forall CT P Z cutoff caller_authority caller_senv caller_renv caller_h stack
    destination destination_type receiver receiver_location receiver_type
    entry_senv entry_renv origins callee_senv callee_renv callee_h
    return_var body_return_type declared_return_type return_location,
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
      (vpa_mutability_tt_safe_ro receiver_type declared_return_type)
      destination_type ->
    live_authority_history_state CT P Z cutoff
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type) origins :: stack) callee_h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location))
      callee_h ->
    active_rdm_component_colors_separated CT callee_h
      (live_capability_set CT callee_h
        (mk_watched_frame
          (call_authority caller_authority (sqtype receiver_type))
          callee_senv callee_renv)
        (mk_watched_boundary
          (mk_watched_frame caller_authority caller_senv caller_renv)
          entry_senv entry_renv (sqtype receiver_type) origins :: stack)) Z caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) ->
    live_authority_history_state CT P Z cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      stack callee_h.
Proof.
  intros CT P Z cutoff caller_authority caller_senv caller_renv caller_h stack
    destination destination_type receiver receiver_location receiver_type
    entry_senv entry_renv origins callee_senv callee_renv callee_h return_var
    body_return_type declared_return_type return_location Hcaller_zone
    Hcaller_env Hcaller_wf Hdestination_not_receiver Hdestination_type
    Hreceiver_type Hreceiver_value Hreturn_type Hreturn_value Hbody_sub
    Hresult_sub
    [Hcallee_history [[Hcallee_wf Hboundary_wf]
      [[Hcallee_sound Hboundary_sound]
        [Hcutoff [Hzone_bound Hauthority_chain]]]]]
    Hcaller_post_wf Hcaller_colors.
  set (callee_frame := mk_watched_frame
    (call_authority caller_authority (sqtype receiver_type))
    callee_senv callee_renv).
  set (caller_boundary := mk_watched_boundary
    (mk_watched_frame caller_authority caller_senv caller_renv)
    entry_senv entry_renv (sqtype receiver_type) origins).
  set (caller_post := mk_watched_frame caller_authority caller_senv
    (update_r_env_value caller_renv destination (Iot return_location))).
  simpl in Hauthority_chain.
  destruct Hauthority_chain as [Hcurrent_authority Htail_authority_chain].
  set (Mbig := live_capability_set CT callee_h callee_frame
    (caller_boundary :: stack)).
  set (Msmall := live_capability_set CT callee_h caller_post stack).
  have Hcaller_old_sound : authority_context_sound callee_h caller_renv
      caller_authority := Forall_inv Hboundary_sound.
  have Hcaller_post_sound := authority_context_sound_after_nonreceiver_update
    callee_h caller_renv caller_authority destination (Iot return_location)
    Hcaller_old_sound Hdestination_not_receiver.
  have Htail_wf : Forall (fun boundary =>
      wf_r_config CT boundary.(boundary_caller).(frame_senv)
        boundary.(boundary_caller).(frame_renv) callee_h) stack :=
    Forall_inv_tail Hboundary_wf.
  have Htail_sound : Forall (fun boundary =>
      authority_context_sound callee_h
        boundary.(boundary_caller).(frame_renv)
        boundary.(boundary_caller).(frame_authority)) stack :=
    Forall_inv_tail Hboundary_sound.
  assert (Hpost_frames_wf : live_frames_wf CT callee_h caller_post stack).
  { split; [exact Hcaller_post_wf|exact Htail_wf]. }
  assert (Hpost_frames_sound :
      live_frames_authority_sound callee_h caller_post stack).
  { split; [exact Hcaller_post_sound|exact Htail_sound]. }
  assert (Hincluded : Included Loc Msmall Mbig).
  { intros location Hlocation. subst Msmall Mbig caller_post callee_frame
      caller_boundary.
    eapply call_return_live_reachability_reflects_before_pop with
      (caller_h := caller_h) (destination_type := destination_type)
      (receiver_location := receiver_location)
      (receiver_type := receiver_type)
      (body_return_type := body_return_type)
      (declared_return_type := declared_return_type)
      (return_location := return_location); eauto. }
  assert (Htarget_zone : zone_env_safe Z caller_senv
      (update_r_env_value caller_renv destination (Iot return_location))).
  { eapply call_return_preserves_zone_env_safe with
      (P := P) (M := Mbig) (cutoff := cutoff)
      (caller_authority := caller_authority) (caller_h := caller_h)
      (receiver := receiver) (receiver_location := receiver_location)
      (callee_senv := callee_senv) (callee_renv := callee_renv)
      (callee_h := callee_h) (return_var := return_var)
      (body_return_type := body_return_type)
      (declared_return_type := declared_return_type); eauto. }
  assert (Hcallee_env : env_is_confined P cutoff callee_renv).
  { destruct Hcallee_history as
      [[[? [? [[Henv ?] ?]]] ?] ?]. exact Henv. }
  have Htarget_env := call_return_preserves_env_confinement P cutoff
    caller_renv callee_renv destination return_var return_location Hcaller_env
    Hcallee_env Hreturn_value.
  assert (Htarget_roots : authority_env_roots_in caller_authority Mbig
      caller_senv
      (update_r_env_value caller_renv destination (Iot return_location))).
  { intros root Hroot. apply Hincluded.
    exists root. split; [left; exact Hroot|constructor]. }
  have Hreframed := authority_component_history_reframe CT P Z Mbig cutoff
    (call_authority caller_authority (sqtype receiver_type)) callee_senv
    callee_renv caller_authority caller_senv
    (update_r_env_value caller_renv destination (Iot return_location))
    callee_h Hcallee_history Htarget_zone Htarget_env Htarget_roots
    Hcaller_post_sound Hcaller_colors.
  have Hclosed := live_capability_set_forward_closed CT callee_h caller_post
    stack.
  have Hruntime := live_capability_members_runtime_mutable CT callee_h
    caller_post stack Hpost_frames_wf Hpost_frames_sound.
  have Hroots := active_authority_roots_are_live CT callee_h caller_post stack.
  have Hsmall := authority_component_history_shrink CT P Z Mbig Msmall cutoff
    caller_authority caller_senv
    (update_r_env_value caller_renv destination (Iot return_location))
    callee_h Hreframed Hincluded Hclosed Hruntime Hroots.
  split; [exact Hsmall|]. split; [exact Hpost_frames_wf|].
  split; [exact Hpost_frames_sound|]. split; [exact Hcutoff|].
  split; assumption.
Qed.

Lemma call_return_nonlocation_live_root_reflects_before_pop :
  forall CT caller_authority caller_senv caller_renv caller_h stack
    destination destination_type receiver_type entry_senv entry_renv origins
    callee_senv callee_renv return_value root,
    (forall location, return_value <> Iot location) ->
    wf_r_config CT caller_senv caller_renv caller_h ->
    static_getType caller_senv destination = Some destination_type ->
    live_capability_root
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination return_value)) stack root ->
    live_capability_root
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type) origins :: stack) root.
Proof.
  intros CT caller_authority caller_senv caller_renv caller_h stack
    destination destination_type receiver_type entry_senv entry_renv origins
    callee_senv callee_renv return_value root Hnonlocation Hcaller_wf Hdestination
    [Hactive | [boundary [Hin Hboundary_root]]].
  - destruct Hactive as
      [variable [T [Htype [Hvalue Hcapability]]]].
    destruct (Nat.eq_dec variable destination) as [Heq | Hneq].
    + subst variable.
      have Hdestination_dom := Hdestination.
      apply static_getType_dom in Hdestination_dom.
      unfold wf_r_config in Hcaller_wf.
      destruct Hcaller_wf as [_ [_ [_ [_ [Hlength Hcorr]]]]].
      assert (Hruntime_dom : destination < dom (vars caller_renv)) by lia.
      have Hupdated := runtime_getVal_update_same caller_renv destination
        return_value Hruntime_dom.
      rewrite Hupdated in Hvalue. injection Hvalue as Hbad.
      exfalso. exact (Hnonlocation root Hbad).
    + have Hunchanged := runtime_getVal_update_diff caller_renv destination
        variable return_value.
      assert (Hdestination_variable : destination <> variable) by congruence.
      specialize (Hunchanged Hdestination_variable).
      rewrite Hunchanged in Hvalue.
      right. exists (mk_watched_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type) origins).
      split; [left; reflexivity|].
      exists variable, T. repeat split; assumption.
  - right. exists boundary. split; [right; exact Hin|exact Hboundary_root].
Qed.

Lemma call_return_nonlocation_live_reachability_reflects_before_pop :
  forall CT h caller_authority caller_senv caller_renv caller_h stack
    destination destination_type receiver_type entry_senv entry_renv origins
    callee_senv callee_renv return_value location,
    (forall target, return_value <> Iot target) ->
    wf_r_config CT caller_senv caller_renv caller_h ->
    static_getType caller_senv destination = Some destination_type ->
    live_capability_reachable CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination return_value)) stack location ->
    live_capability_reachable CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type) origins :: stack)
      location.
Proof.
  intros CT h caller_authority caller_senv caller_renv caller_h stack
    destination destination_type receiver_type entry_senv entry_renv origins
    callee_senv callee_renv return_value location Hnonlocation Hcaller_wf Hdestination
    [root [Hroot Hreach]].
  exists root. split; [|exact Hreach].
  eapply call_return_nonlocation_live_root_reflects_before_pop; eauto.
Qed.

Lemma zone_env_safe_after_nonlocation_update :
  forall CT Z caller_senv caller_renv caller_h destination destination_type
    return_value,
    (forall location, return_value <> Iot location) ->
    zone_env_safe Z caller_senv caller_renv ->
    wf_r_config CT caller_senv caller_renv caller_h ->
    static_getType caller_senv destination = Some destination_type ->
    zone_env_safe Z caller_senv
      (update_r_env_value caller_renv destination return_value).
Proof.
  intros CT Z caller_senv caller_renv caller_h destination destination_type
    return_value Hnonlocation Hzone Hwf Hdestination variable location
    variable_type Hvariable_type
    Hvariable_value Hlocation_zone.
  destruct (Nat.eq_dec variable destination) as [Heq | Hneq].
  - subst variable.
    have Hdestination_dom := Hdestination.
    apply static_getType_dom in Hdestination_dom.
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [_ [_ [Hlength Hcorr]]]]].
    assert (Hruntime_dom : destination < dom (vars caller_renv)) by lia.
    have Hupdated := runtime_getVal_update_same caller_renv destination
      return_value Hruntime_dom.
    rewrite Hupdated in Hvariable_value. injection Hvariable_value as Hbad.
    exfalso. exact (Hnonlocation location Hbad).
  - have Hunchanged := runtime_getVal_update_diff caller_renv destination
      variable return_value.
    assert (Hdestination_variable : destination <> variable) by congruence.
    specialize (Hunchanged Hdestination_variable).
    rewrite Hunchanged in Hvariable_value.
    eapply Hzone; eauto.
Qed.

Lemma live_history_leave_call_nonlocation_given_caller_colors :
  forall CT P Z cutoff caller_authority caller_senv caller_renv caller_h stack
    destination destination_type receiver_type entry_senv entry_renv origins
    callee_senv callee_renv callee_h return_value,
    (forall location, return_value <> Iot location) ->
    zone_env_safe Z caller_senv caller_renv ->
    env_is_confined P cutoff caller_renv ->
    wf_r_config CT caller_senv caller_renv caller_h ->
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    live_authority_history_state CT P Z cutoff
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type) origins :: stack) callee_h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination return_value) callee_h ->
    active_rdm_component_colors_separated CT callee_h
      (live_capability_set CT callee_h
        (mk_watched_frame
          (call_authority caller_authority (sqtype receiver_type))
          callee_senv callee_renv)
        (mk_watched_boundary
          (mk_watched_frame caller_authority caller_senv caller_renv)
          entry_senv entry_renv (sqtype receiver_type) origins :: stack)) Z
      caller_senv (update_r_env_value caller_renv destination return_value) ->
    live_authority_history_state CT P Z cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination return_value)) stack callee_h.
Proof.
  intros CT P Z cutoff caller_authority caller_senv caller_renv caller_h stack
    destination destination_type receiver_type entry_senv entry_renv origins
    callee_senv callee_renv callee_h return_value Hnonlocation Hcaller_zone
    Hcaller_env Hcaller_wf
    Hdestination_not_receiver Hdestination_type
    [Hcallee_history [[Hcallee_wf Hboundary_wf]
      [[Hcallee_sound Hboundary_sound]
        [Hcutoff [Hzone_bound Hauthority_chain]]]]]
    Hcaller_post_wf Hcaller_colors.
  set (callee_frame := mk_watched_frame
    (call_authority caller_authority (sqtype receiver_type))
    callee_senv callee_renv).
  set (caller_boundary := mk_watched_boundary
    (mk_watched_frame caller_authority caller_senv caller_renv)
    entry_senv entry_renv (sqtype receiver_type) origins).
  set (caller_post := mk_watched_frame caller_authority caller_senv
    (update_r_env_value caller_renv destination return_value)).
  simpl in Hauthority_chain.
  destruct Hauthority_chain as [Hcurrent_authority Htail_authority_chain].
  set (Mbig := live_capability_set CT callee_h callee_frame
    (caller_boundary :: stack)).
  set (Msmall := live_capability_set CT callee_h caller_post stack).
  have Hcaller_old_sound : authority_context_sound callee_h caller_renv
      caller_authority := Forall_inv Hboundary_sound.
  have Hcaller_post_sound := authority_context_sound_after_nonreceiver_update
    callee_h caller_renv caller_authority destination return_value
    Hcaller_old_sound Hdestination_not_receiver.
  have Htail_wf : Forall (fun boundary =>
      wf_r_config CT boundary.(boundary_caller).(frame_senv)
        boundary.(boundary_caller).(frame_renv) callee_h) stack :=
    Forall_inv_tail Hboundary_wf.
  have Htail_sound : Forall (fun boundary =>
      authority_context_sound callee_h
        boundary.(boundary_caller).(frame_renv)
        boundary.(boundary_caller).(frame_authority)) stack :=
    Forall_inv_tail Hboundary_sound.
  assert (Hpost_frames_wf : live_frames_wf CT callee_h caller_post stack).
  { split; [exact Hcaller_post_wf|exact Htail_wf]. }
  assert (Hpost_frames_sound :
      live_frames_authority_sound callee_h caller_post stack).
  { split; [exact Hcaller_post_sound|exact Htail_sound]. }
  assert (Hincluded : Included Loc Msmall Mbig).
  { intros location Hlocation. subst Msmall Mbig caller_post callee_frame
      caller_boundary.
    eapply call_return_nonlocation_live_reachability_reflects_before_pop with
      (caller_h := caller_h) (destination_type := destination_type); eauto. }
  assert (Htarget_zone : zone_env_safe Z caller_senv
      (update_r_env_value caller_renv destination return_value)).
  { eapply zone_env_safe_after_nonlocation_update; eauto. }
  have Htarget_env : env_is_confined P cutoff
      (update_r_env_value caller_renv destination return_value).
  { eapply env_confined_update; [exact Hcaller_env|].
    destruct return_value; try exact I.
    exfalso. eapply Hnonlocation. reflexivity. }
  assert (Htarget_roots : authority_env_roots_in caller_authority Mbig
      caller_senv (update_r_env_value caller_renv destination return_value)).
  { intros root Hroot. apply Hincluded.
    exists root. split; [left; exact Hroot|constructor]. }
  have Hreframed := authority_component_history_reframe CT P Z Mbig cutoff
    (call_authority caller_authority (sqtype receiver_type)) callee_senv
    callee_renv caller_authority caller_senv
    (update_r_env_value caller_renv destination return_value) callee_h
    Hcallee_history Htarget_zone Htarget_env Htarget_roots
    Hcaller_post_sound Hcaller_colors.
  have Hclosed := live_capability_set_forward_closed CT callee_h caller_post
    stack.
  have Hruntime := live_capability_members_runtime_mutable CT callee_h
    caller_post stack Hpost_frames_wf Hpost_frames_sound.
  have Hroots := active_authority_roots_are_live CT callee_h caller_post stack.
  have Hsmall := authority_component_history_shrink CT P Z Mbig Msmall cutoff
    caller_authority caller_senv
    (update_r_env_value caller_renv destination return_value) callee_h Hreframed
    Hincluded Hclosed Hruntime Hroots.
  split; [exact Hsmall|]. split; [exact Hpost_frames_wf|].
  split; [exact Hpost_frames_sound|]. split; [exact Hcutoff|].
  split; assumption.
Qed.

Lemma assignment_capability_root_has_live_origin :
  forall CT authority sGamma mt rGamma h stack x e old value root,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SVarAss x e) sGamma ->
    safe_readonly_method_type mt ->
    runtime_getVal rGamma x = Some old ->
    eval_expr OK CT rGamma h e value OK rGamma h ->
    frame_capability_root
      (mk_watched_frame authority sGamma
        (update_r_env_value rGamma x value)) root ->
    exists old_root,
      live_capability_root
        (mk_watched_frame authority sGamma rGamma) stack old_root /\
      mutable_reachable CT h old_root root.
Proof.
  intros CT authority sGamma mt rGamma h stack x e old value root Hwf
    Htyping Hscope Hx Heval
    [z [T [Htype [Hvalue Hcapability]]]].
  destruct Hcapability as [Hmut | [Hrdm Hauthority]].
  - assert (Hroot : typed_root Mut sGamma
      (update_r_env_value rGamma x value) root).
    { exists z, T. repeat split; assumption. }
    destruct (assignment_mut_root_has_old_ancestor CT sGamma mt rGamma h
      x e old value Hwf Htyping Hscope Hx Heval root Hroot) as
      [old_root [[old_var [OldT [Holdtype [Holdvalue Holdmut]]]] Hreach]].
    exists old_root. split; [left|exact Hreach].
    exists old_var, OldT. repeat split; try assumption.
    unfold capability_in_context. left. exact Holdmut.
  - assert (Hroot : typed_root RDM sGamma
      (update_r_env_value rGamma x value) root).
    { exists z, T. repeat split; assumption. }
    destruct (assignment_rdm_root_has_old_ancestor CT sGamma mt rGamma h
      x e old value Hwf Htyping Hscope Hx Heval root Hroot) as
      [old_root [[old_var [OldT [Holdtype [Holdvalue Holdrdm]]]] Hreach]].
    exists old_root. split; [left|exact Hreach].
    exists old_var, OldT. repeat split; try assumption.
    unfold capability_in_context. right. split; assumption.
Qed.

Lemma assignment_live_reachability_is_old :
  forall CT authority sGamma mt rGamma h stack x e old value location,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SVarAss x e) sGamma ->
    safe_readonly_method_type mt ->
    runtime_getVal rGamma x = Some old ->
    eval_expr OK CT rGamma h e value OK rGamma h ->
    live_capability_reachable CT h
      (mk_watched_frame authority sGamma
        (update_r_env_value rGamma x value)) stack location ->
    live_capability_reachable CT h
      (mk_watched_frame authority sGamma rGamma) stack location.
Proof.
  intros CT authority sGamma mt rGamma h stack x e old value location
    Hwf Htyping Hscope Hx Heval [root [[Hactive | Hsuspended] Hreach]].
  - destruct (assignment_capability_root_has_live_origin CT authority
      sGamma mt rGamma h stack x e old value root Hwf Htyping Hscope Hx
      Heval Hactive) as [old_root [Hlive Holdreach]].
    exists old_root. split; [exact Hlive|].
    eapply mutable_reachable_transitive; eauto.
  - exists root. split; [right; exact Hsuspended|exact Hreach].
Qed.

Lemma local_capability_root_is_old :
  forall CT authority sGamma mt rGamma h T x sGamma' root,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SLocal T x) sGamma' ->
    runtime_getVal rGamma x = None ->
    frame_capability_root
      (mk_watched_frame authority sGamma'
        (set_vars rGamma (vars rGamma ++ [default_value T]))) root ->
    frame_capability_root
      (mk_watched_frame authority sGamma rGamma) root.
Proof.
  intros CT authority sGamma mt rGamma h T x sGamma' root Hwf Htyping
    Hnone [y [Ty [Htype [Hvalue Hcapability]]]].
  inversion Htyping; subst.
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [_ [_ [Hlength _]]]]].
  destruct (appended_nonlocation_lookup_is_old sGamma rGamma T
    (default_value T) y Ty root (default_value_not_location T)
    Hlength Htype Hvalue) as [Holdtype Holdvalue].
  exists y, Ty. repeat split; assumption.
Qed.

Lemma local_live_reachability_is_old :
  forall CT authority sGamma mt rGamma h T x sGamma' stack location,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SLocal T x) sGamma' ->
    runtime_getVal rGamma x = None ->
    live_capability_reachable CT h
      (mk_watched_frame authority sGamma'
        (set_vars rGamma (vars rGamma ++ [default_value T]))) stack location ->
    live_capability_reachable CT h
      (mk_watched_frame authority sGamma rGamma) stack location.
Proof.
  intros CT authority sGamma mt rGamma h T x sGamma' stack location Hwf
    Htyping Hnone [root [[Hactive | Hsuspended] Hreach]].
  - exists root. split; [left|exact Hreach].
    eapply local_capability_root_is_old; eauto.
  - exists root. split; [right; exact Hsuspended|exact Hreach].
Qed.

(** Backward provenance for the ordinary field-update case. Updating an RDM
    edge cannot manufacture live authority when its non-null target was
    already live before the update. The complementary typed field-write case,
    in which the target was not live, is excluded from the protected zone by
    call-boundary origin information. *)
Lemma live_capability_reachable_after_field_update_if_written_live :
  forall CT h active stack lx old field value location,
    runtime_getObj h lx = Some old ->
    (forall written,
      value = Iot written ->
      live_capability_reachable CT h active stack written) ->
    live_capability_reachable CT (update_field h lx field value)
      active stack location ->
    live_capability_reachable CT h active stack location.
Proof.
  intros CT h active stack lx old field value location Hobj Hwritten
    [root [Hroot Hreach]].
  destruct (mutable_reachable_after_field_update CT h lx old field value
    root location Hobj Hreach) as
    [Hold | [written [Hvalue [Hroot_source Hwritten_location]]]].
  - exists root. split; assumption.
  - destruct (Hwritten written Hvalue) as
      [written_root [Hwritten_root Hwritten_reach]].
    exists written_root. split; [exact Hwritten_root|].
    eapply mutable_reachable_transitive; eauto.
Qed.

(** An allocation may introduce a fresh live root, but every old location
    reachable from that root has an old root of the same capability
    qualifier.  This is the allocation analogue of roDOT's backward mutable-
    reachability lemma. *)
Lemma new_live_reachability_to_old_location_has_old_origin :
  forall CT authority sGamma mt rGamma h stack x qc C args sGamma' vals
    qruntime location,
    wf_r_config CT sGamma rGamma h ->
    live_frames_wf CT h
      (mk_watched_frame authority sGamma rGamma) stack ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    location < dom h ->
    live_capability_reachable CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (mk_watched_frame authority sGamma'
        (update_r_env_value rGamma x (Iot (dom h)))) stack location ->
    live_capability_reachable CT h
      (mk_watched_frame authority sGamma rGamma) stack location.
Proof.
  intros CT authority sGamma mt rGamma h stack x qc C args sGamma' vals
    qruntime location Hwf [Hactive_wf Hstack_wf] Htyping Hvals Hlocation_old
    [root [[Hactive_root | [boundary [Hin Hboundary_root]]] Hreach]].
  - destruct Hactive_root as
      [variable [T [Htype [Hvalue Hcapability]]]].
    destruct Hcapability as [Hmut | [Hrdm Hauthority]].
    + assert (Hroot : typed_root Mut sGamma'
        (update_r_env_value rGamma x (Iot (dom h))) root).
      { exists variable, T. repeat split; assumption. }
      destruct (new_mutable_component_origin CT sGamma mt rGamma h x qc C
        args sGamma' vals qruntime root location Hwf Htyping Hvals Hroot
        Hreach) as [Hfresh | [old_root [Holdroot Holdreach]]].
      * subst location. lia.
      * exists old_root. split.
        -- left. destruct Holdroot as
             [old_variable [OldT [Holdtype [Holdvalue Holdmut]]]].
           exists old_variable, OldT. repeat split; try assumption.
           unfold capability_in_context. left. exact Holdmut.
        -- exact Holdreach.
    + assert (Hroot : typed_root RDM sGamma'
        (update_r_env_value rGamma x (Iot (dom h))) root).
      { exists variable, T. repeat split; assumption. }
      destruct (new_rdm_component_origin CT sGamma mt rGamma h x qc C args
        sGamma' vals qruntime root location Hwf Htyping Hvals Hroot Hreach)
        as [Hfresh | [old_root [Holdroot Holdreach]]].
      * subst location. lia.
      * exists old_root. split.
        -- left. destruct Holdroot as
             [old_variable [OldT [Holdtype [Holdvalue Holdrdm]]]].
           exists old_variable, OldT. repeat split; try assumption.
           unfold capability_in_context. right. split; assumption.
        -- exact Holdreach.
  - apply Forall_forall with (x := boundary) in Hstack_wf; [|exact Hin].
    have Hroot_old : root < dom h.
    { eapply frame_capability_root_dom; eauto. }
    destruct (mutable_reachable_from_old_after_append CT h
      (mkObj (mkruntime_type qruntime C) vals) root location
      (proj1 (proj2 Hwf)) Hroot_old Hreach) as [_ Holdreach].
    exists root. split.
    + right. exists boundary. split; assumption.
    + exact Holdreach.
Qed.

Lemma live_history_after_assignment :
  forall CT P Z cutoff authority sGamma mt rGamma h stack x e old value,
    live_authority_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack h ->
    stmt_typing CT sGamma mt (SVarAss x e) sGamma ->
    safe_readonly_method_type mt ->
    runtime_getVal rGamma x = Some old ->
    eval_expr OK CT rGamma h e value OK rGamma h ->
    live_authority_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma
        (update_r_env_value rGamma x value)) stack h.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack x e old value
    [Hhistory [[Hwf Hstack_wf]
      [[Hsound Hstack_sound] [Hcutoff [Hzone_bound Hauthority_chain]]]]]
    Htyping Hscope Hx Heval.
  have Hbig := authority_history_after_assignment CT P Z
    (live_capability_set CT h
      (mk_watched_frame authority sGamma rGamma) stack)
    cutoff authority sGamma mt rGamma h x e old value Hwf Hhistory
    Htyping Hscope Hx Heval.
  assert (Hupdate :
      set_vars rGamma (update x value (vars rGamma)) =
      update_r_env_value rGamma x value).
  { destruct rGamma. reflexivity. }
  assert (Hstmt : eval_stmt OK CT rGamma h (SVarAss x e) OK
      (update_r_env_value rGamma x value) h).
  { rewrite <- Hupdate. eapply SBS_Assign with (v1 := old); eauto. }
  have Hpost_wf := preservation_pico CT sGamma mt rGamma h
    (SVarAss x e) (update_r_env_value rGamma x value) h sGamma Hwf
    Htyping Hstmt.
  assert (Hframes_wf : live_frames_wf CT h
      (mk_watched_frame authority sGamma
        (update_r_env_value rGamma x value)) stack).
  { split; assumption. }
  assert (Hframes_sound : live_frames_authority_sound h
      (mk_watched_frame authority sGamma
        (update_r_env_value rGamma x value)) stack).
  { split.
    - exact (proj2 (proj2 Hbig)).
    - exact Hstack_sound. }
  have Hincluded : Included Loc
      (live_capability_set CT h
        (mk_watched_frame authority sGamma
          (update_r_env_value rGamma x value)) stack)
      (live_capability_set CT h
        (mk_watched_frame authority sGamma rGamma) stack).
  { intros location Hlocation.
    eapply assignment_live_reachability_is_old; eauto. }
  have Hclosed := live_capability_set_forward_closed CT h
    (mk_watched_frame authority sGamma
      (update_r_env_value rGamma x value)) stack.
  have Hruntime := live_capability_members_runtime_mutable CT h
    (mk_watched_frame authority sGamma
      (update_r_env_value rGamma x value)) stack Hframes_wf Hframes_sound.
  have Hroots := active_authority_roots_are_live CT h
    (mk_watched_frame authority sGamma
      (update_r_env_value rGamma x value)) stack.
  have Hsmall := authority_component_history_shrink CT P Z
    (live_capability_set CT h
      (mk_watched_frame authority sGamma rGamma) stack)
    (live_capability_set CT h
      (mk_watched_frame authority sGamma
        (update_r_env_value rGamma x value)) stack)
    cutoff authority sGamma (update_r_env_value rGamma x value) h
    Hbig Hincluded Hclosed Hruntime Hroots.
  split; [exact Hsmall|]. split; [exact Hframes_wf|].
  split; [exact Hframes_sound|]. split; [exact Hcutoff|].
  split; assumption.
Qed.

Lemma live_history_after_local :
  forall CT P Z cutoff authority sGamma mt rGamma h stack T x sGamma',
    live_authority_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack h ->
    stmt_typing CT sGamma mt (SLocal T x) sGamma' ->
    runtime_getVal rGamma x = None ->
    live_authority_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma'
        (set_vars rGamma (vars rGamma ++ [default_value T]))) stack h.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack T x sGamma'
    [Hhistory [[Hwf Hstack_wf]
      [[Hsound Hstack_sound] [Hcutoff [Hzone_bound Hauthority_chain]]]]]
    Htyping Hnone.
  have Hbig := authority_history_after_local CT P Z
    (live_capability_set CT h
      (mk_watched_frame authority sGamma rGamma) stack)
    cutoff authority sGamma mt rGamma h T x sGamma' Hwf Hhistory
    Htyping Hnone.
  have Hstmt : eval_stmt OK CT rGamma h (SLocal T x) OK
      (set_vars rGamma (vars rGamma ++ [default_value T])) h.
  { apply SBS_Local. exact Hnone. }
  have Hpost_wf := preservation_pico CT sGamma mt rGamma h
    (SLocal T x) (set_vars rGamma (vars rGamma ++ [default_value T])) h sGamma'
    Hwf Htyping Hstmt.
  assert (Hframes_wf : live_frames_wf CT h
      (mk_watched_frame authority sGamma'
        (set_vars rGamma (vars rGamma ++ [default_value T]))) stack).
  { split; assumption. }
  assert (Hframes_sound : live_frames_authority_sound h
      (mk_watched_frame authority sGamma'
        (set_vars rGamma (vars rGamma ++ [default_value T]))) stack).
  { split.
    - exact (proj2 (proj2 Hbig)).
    - exact Hstack_sound. }
  have Hincluded : Included Loc
      (live_capability_set CT h
        (mk_watched_frame authority sGamma'
          (set_vars rGamma (vars rGamma ++ [default_value T]))) stack)
      (live_capability_set CT h
        (mk_watched_frame authority sGamma rGamma) stack).
  { intros location Hlocation.
    eapply local_live_reachability_is_old; eauto. }
  have Hclosed := live_capability_set_forward_closed CT h
      (mk_watched_frame authority sGamma'
      (set_vars rGamma (vars rGamma ++ [default_value T]))) stack.
  have Hruntime := live_capability_members_runtime_mutable CT h
      (mk_watched_frame authority sGamma'
      (set_vars rGamma (vars rGamma ++ [default_value T]))) stack
    Hframes_wf Hframes_sound.
  have Hroots := active_authority_roots_are_live CT h
      (mk_watched_frame authority sGamma'
      (set_vars rGamma (vars rGamma ++ [default_value T]))) stack.
  have Hsmall := authority_component_history_shrink CT P Z
    (live_capability_set CT h
      (mk_watched_frame authority sGamma rGamma) stack)
    (live_capability_set CT h
        (mk_watched_frame authority sGamma'
        (set_vars rGamma (vars rGamma ++ [default_value T]))) stack)
    cutoff authority sGamma'
    (set_vars rGamma (vars rGamma ++ [default_value T])) h
    Hbig Hincluded Hclosed Hruntime Hroots.
  split; [exact Hsmall|]. split; [exact Hframes_wf|].
  split; [exact Hframes_sound|]. split; [exact Hcutoff|].
  split; assumption.
Qed.

Lemma live_history_after_field_write :
  forall CT P Z cutoff authority sGamma mt rGamma h stack x f y
    sGamma' rGamma' h',
    live_authority_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack h ->
    stmt_typing CT sGamma mt (SFldWrite x f y) sGamma' ->
    safe_readonly_method_type mt ->
    eval_stmt OK CT rGamma h (SFldWrite x f y) OK rGamma' h' ->
    live_authority_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma' rGamma') stack h'.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack x f y
    sGamma' rGamma' h'
    [Hhistory [[Hwf Hstack_wf]
      [[Hsound Hstack_sound] [Hcutoff [Hzone_bound Hauthority_chain]]]]]
    Htyping Hscope Heval.
  assert (HsGamma : sGamma' = sGamma) by
    (inversion Htyping; reflexivity).
  assert (HrGamma : rGamma' = rGamma) by
    (inversion Heval; reflexivity).
  subst sGamma' rGamma'.
  destruct (authority_history_after_field_write CT P Z
    (live_capability_set CT h
      (mk_watched_frame authority sGamma rGamma) stack)
    cutoff authority sGamma mt rGamma h x f y rGamma h' sGamma Hwf
    Hhistory Htyping Hscope Heval) as [Mbig [Hcontains Hbig]].
  have Hpost_wf := preservation_pico CT sGamma mt rGamma h
    (SFldWrite x f y) rGamma h' sGamma Hwf Htyping Heval.
  have Hheap' : wf_heap CT h' := proj1 (proj2 Hpost_wf).
  have Htypes : preserves_old_runtime_types h h'.
  { inversion Heval; subst. apply field_update_preserves_old_runtime_types. }
  destruct (live_frames_preserved_by_runtime_types CT h h'
    (mk_watched_frame authority sGamma rGamma) stack
    (conj Hwf Hstack_wf) (conj Hsound Hstack_sound) Hheap' Htypes) as
    [Hframes_wf Hframes_sound].
  have Hincluded : Included Loc
      (live_capability_set CT h'
        (mk_watched_frame authority sGamma rGamma) stack) Mbig.
  { eapply live_capability_set_in_closed_superset.
    - exact Hcontains.
    - exact (proj1 (proj2 (proj2 (proj2 (proj1 (proj1 Hbig)))))). }
  have Hclosed := live_capability_set_forward_closed CT h'
    (mk_watched_frame authority sGamma rGamma) stack.
  have Hruntime := live_capability_members_runtime_mutable CT h'
    (mk_watched_frame authority sGamma rGamma) stack
    Hframes_wf Hframes_sound.
  have Hroots := active_authority_roots_are_live CT h'
    (mk_watched_frame authority sGamma rGamma) stack.
  have Hsmall := authority_component_history_shrink CT P Z Mbig
    (live_capability_set CT h'
      (mk_watched_frame authority sGamma rGamma) stack)
    cutoff authority sGamma rGamma h' Hbig Hincluded Hclosed Hruntime Hroots.
  split; [exact Hsmall|]. split; [exact Hframes_wf|].
  split; [exact Hframes_sound|]. split.
  - destruct Htypes as [Hdom _]. lia.
  - split; assumption.
Qed.

Lemma live_history_after_new :
  forall CT P Z cutoff authority sGamma mt rGamma h stack x qc C args
    sGamma' rGamma' h',
    live_authority_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    eval_stmt OK CT rGamma h (SNew x qc C args) OK rGamma' h' ->
    live_authority_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma' rGamma') stack h'.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack x qc C args
    sGamma' rGamma' h'
    [Hhistory [[Hwf Hstack_wf]
      [[Hsound Hstack_sound] [Hcutoff [Hzone_bound Hauthority_chain]]]]]
    Htyping Heval.
  assert (Hfresh_zone : ~ In Loc Z (dom h)).
  { intros Hin. have Hbound := Hzone_bound (dom h) Hin. lia. }
  destruct (authority_history_after_new CT P Z
    (live_capability_set CT h
      (mk_watched_frame authority sGamma rGamma) stack)
    cutoff authority sGamma mt rGamma h x qc C args rGamma' h' sGamma'
    Hwf Hhistory Htyping Hcutoff Hfresh_zone Heval) as
    [Mbig [Hcontains Hbig]].
  have Hpost_wf := preservation_pico CT sGamma mt rGamma h
    (SNew x qc C args) rGamma' h' sGamma' Hwf Htyping Heval.
  have Hheap' : wf_heap CT h' := proj1 (proj2 Hpost_wf).
  have Htypes : preserves_old_runtime_types h h'.
  { inversion Heval; subst. apply heap_append_preserves_old_runtime_types. }
  destruct (live_frames_preserved_by_runtime_types CT h h'
    (mk_watched_frame authority sGamma rGamma) stack
    (conj Hwf Hstack_wf) (conj Hsound Hstack_sound) Hheap' Htypes) as
    [[Hold_active_wf Hpost_stack_wf]
      [Hold_active_sound Hpost_stack_sound]].
  have Hpost_sound : authority_context_sound h' rGamma' authority :=
    proj2 (proj2 Hbig).
  assert (Hframes_wf : live_frames_wf CT h'
      (mk_watched_frame authority sGamma' rGamma') stack).
  { split; assumption. }
  assert (Hframes_sound : live_frames_authority_sound h'
      (mk_watched_frame authority sGamma' rGamma') stack).
  { split; assumption. }
  have Hroots_big : authority_env_roots_in authority Mbig
      sGamma' rGamma' := proj1 (proj2 Hbig).
  have Hclosed_big : mutable_heap_closed CT h' Mbig :=
    proj1 (proj2 (proj2 (proj2 (proj1 (proj1 Hbig))))).
  have Hincluded : Included Loc
      (live_capability_set CT h'
        (mk_watched_frame authority sGamma' rGamma') stack) Mbig.
  { eapply live_capability_set_after_active_change_in_superset.
    - exact Hcontains.
    - exact Hroots_big.
    - exact Hclosed_big. }
  have Hclosed := live_capability_set_forward_closed CT h'
    (mk_watched_frame authority sGamma' rGamma') stack.
  have Hruntime := live_capability_members_runtime_mutable CT h'
    (mk_watched_frame authority sGamma' rGamma') stack
    Hframes_wf Hframes_sound.
  have Hroots := active_authority_roots_are_live CT h'
    (mk_watched_frame authority sGamma' rGamma') stack.
  have Hsmall := authority_component_history_shrink CT P Z Mbig
    (live_capability_set CT h'
      (mk_watched_frame authority sGamma' rGamma') stack)
    cutoff authority sGamma' rGamma' h' Hbig Hincluded Hclosed Hruntime
    Hroots.
  split; [exact Hsmall|]. split; [exact Hframes_wf|].
  split; [exact Hframes_sound|]. split.
  - destruct Htypes as [Hdom _]. lia.
  - split; assumption.
Qed.

Lemma live_history_enter_call :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack
    x y m args sGamma' vals ly cy runtime_mdef Ty,
    live_authority_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack h ->
    stmt_typing CT sGamma mt (SCall x y m args) sGamma' ->
    safe_readonly_method_type mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    exists origins,
      live_authority_history_state CT P Z cutoff
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
    x y m args sGamma' vals ly cy runtime_mdef Ty
    [Hhistory [[Hwf Hstack_wf]
      [[Hsound Hstack_sound] [Hcutoff [Hzone_bound Hauthority_chain]]]]]
    Htyping Hscope Hgety Hval Hbase Hfind Hargs.
  set (callee_senv := mreceiver (msignature runtime_mdef) ::
    mparams (msignature runtime_mdef)).
  set (callee_renv := mkr_env (Iot ly :: vals)).
  destruct (typed_call_target CT sGamma mt rGamma h x y m args sGamma'
    vals ly cy runtime_mdef Hwf Htyping Hval Hbase Hfind Hargs) as
    [declaring_class [declaring_def [body_sGamma
      [_ [_ [_ [_ [_ Hcallee_wf]]]]]]]].
  set (origins := safe_call_rdm_roots_reflect_through_view CT sGamma mt
    rGamma h x y m args sGamma' vals ly cy runtime_mdef Ty Hwf Htyping
    Hscope Hgety Hval Hbase Hfind Hargs).
  exists origins.
  have Hcallee_history := authority_history_enter_call CT P Z
    (live_capability_set CT h
      (mk_watched_frame caller_authority sGamma rGamma) stack)
    cutoff caller_authority sGamma mt rGamma h x y m args sGamma' vals ly
    cy runtime_mdef Ty Hwf Hhistory Htyping Hscope Hgety Hval Hbase Hfind
    Hargs.
  assert (Hcallee_wf' : wf_r_config CT callee_senv callee_renv h).
  { subst callee_senv callee_renv. exact Hcallee_wf. }
  have Hcallee_sound : authority_context_sound h callee_renv
      (call_authority caller_authority (sqtype Ty)).
  { subst callee_renv. exact (proj2 (proj2 Hcallee_history)). }
  set (caller_boundary := mk_watched_boundary
    (mk_watched_frame caller_authority sGamma rGamma)
    callee_senv callee_renv (sqtype Ty) origins).
  have Hcallee_frames : live_frames_wf CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty)) callee_senv callee_renv)
      (caller_boundary :: stack).
  { split; [exact Hcallee_wf'|]. constructor; [exact Hwf|exact Hstack_wf]. }
  have Hcallee_sounds : live_frames_authority_sound h
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty)) callee_senv callee_renv)
      (caller_boundary :: stack).
  { split; [exact Hcallee_sound|].
    constructor; [exact Hsound|exact Hstack_sound]. }
  have Hpost_history : authority_component_history_state CT P Z
      (live_capability_set CT h
        (mk_watched_frame
          (call_authority caller_authority (sqtype Ty))
          callee_senv callee_renv)
        (caller_boundary :: stack)) cutoff
      (call_authority caller_authority (sqtype Ty))
      callee_senv callee_renv h.
  { eapply authority_component_history_shrink with
      (Mbig := live_capability_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) stack).
    - exact Hcallee_history.
    - intros location Hlocation.
      subst caller_boundary callee_senv callee_renv origins.
      apply (proj1 (call_push_live_reachability_equivalent CT
        caller_authority sGamma mt rGamma h x y m args sGamma' vals ly cy
        runtime_mdef Ty
        (safe_call_rdm_roots_reflect_through_view CT sGamma mt rGamma h x y m
          args sGamma' vals ly cy runtime_mdef Ty Hwf Htyping Hscope Hgety
          Hval Hbase Hfind Hargs) stack location Hwf Htyping Hscope Hgety Hval
          Hbase Hfind Hargs)).
      exact Hlocation.
    - apply live_capability_set_forward_closed.
    - eapply live_capability_members_runtime_mutable; eauto.
    - exact (active_authority_roots_are_live CT h
        (mk_watched_frame
          (call_authority caller_authority (sqtype Ty))
          callee_senv callee_renv) (caller_boundary :: stack)). }
  split; [exact Hpost_history|].
  split.
  - split; [exact Hcallee_wf|]. constructor; [exact Hwf|exact Hstack_wf].
  - split.
    + split; [exact Hcallee_sound|].
      constructor; [exact Hsound|exact Hstack_sound].
    + split; [exact Hcutoff|]. split; [exact Hzone_bound|].
      simpl. split; [reflexivity|exact Hauthority_chain].
Qed.
