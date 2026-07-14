Require Import Syntax Notations Helpers Typing Subtyping Bigstep.
Require Import ViewpointAdaptation Properties Preservation ReadonlyHelper.
Require Import Reachability MutableCapability ExecutionConfinement ProtectionHistory.
Require Import ComponentColoring.
From Stdlib Require Import List Lia Sets.Ensembles.
Import ListNotations.

(** A forward capability set records every location currently reachable from a
    static [Mut] root, including roots retained by suspended callers. It is not
    backward closed: a fresh RDM object that points into the set need not
    itself carry mutable authority. *)
Definition env_mut_roots_in
  (M : Ensemble Loc) (sGamma : s_env) (rGamma : r_env) : Prop :=
  forall root, typed_root Mut sGamma rGamma root -> In Loc M root.

Definition rdm_root_reaches_set
  (CT : class_table) (h : heap) (S : Ensemble Loc)
  (sGamma : s_env) (rGamma : r_env) (root : Loc) : Prop :=
  typed_root RDM sGamma rGamma root /\
  exists target,
    mutable_reachable CT h root target /\ In Loc S target.

Definition rdm_root_reaches_zone := rdm_root_reaches_set.

(** The two forbidden colors are an active RDM root already carrying a
    retained mutable capability, and an active RDM root whose RDM component
    reaches the protected zone.  Keeping both out of one frame prevents a
    field write from joining the retained capability set to the zone. *)
Definition rdm_capability_zone_separated
  (CT : class_table) (h : heap) (M Z : Ensemble Loc)
  (sGamma : s_env) (rGamma : r_env) : Prop :=
  forall capability_root zone_root,
    rdm_root_reaches_set CT h M sGamma rGamma capability_root ->
    rdm_root_reaches_zone CT h Z sGamma rGamma zone_root ->
    False.

Definition forward_history_state
  (CT : class_table) (P Z M : Ensemble Loc) (cutoff : Loc)
  (sGamma : s_env) (rGamma : r_env) (h : heap) : Prop :=
  protected_zone_contains P Z /\
  zone_env_safe Z sGamma rGamma /\
  state_is_confined P cutoff rGamma h /\
  mutable_heap_closed CT h M /\
  mutable_members_runtime_mut h M /\
  env_mut_roots_in M sGamma rGamma /\
  (forall l, In Loc M l -> ~ In Loc Z l) /\
  rdm_capability_zone_separated CT h M Z sGamma rGamma.

Definition component_forward_history_state
  (CT : class_table) (P Z M : Ensemble Loc) (cutoff : Loc)
  (sGamma : s_env) (rGamma : r_env) (h : heap) : Prop :=
  forward_history_state CT P Z M cutoff sGamma rGamma h /\
  component_colors_separated CT h M Z /\
  active_rdm_component_colors_separated CT h M Z sGamma rGamma.

Definition extend_capability_after_write
  (CT : class_table) (h : heap) (M : Ensemble Loc)
  (source : Loc) (old : Obj) (field : var) (value : value) : Ensemble Loc :=
  fun l => In Loc M l \/
    exists target D fdef,
      value = Iot target /\ In Loc M source /\
      base_subtype CT (rctype (rt_type old)) D /\
      sf_def_rel CT D field fdef /\
      mutability (ftype fdef) = RDM_f /\
      mutable_reachable CT (update_field h source field value) target l.

(** Allocation grants fresh authority only for an explicitly mutable creation.
    In particular, a runtime-mutable [RDM_c] allocation under a readonly call
    frame is not itself evidence of mutable authority. *)
Definition extend_capability_after_new
  (M : Ensemble Loc) (qc : q_c) (fresh : Loc) : Ensemble Loc :=
  fun l => In Loc M l \/ (qc = Mut_c /\ l = fresh).

Lemma capability_new_extension_contains_old :
  forall M qc fresh,
    Included Loc M (extend_capability_after_new M qc fresh).
Proof. intros M qc fresh l Hin. left. exact Hin. Qed.

Lemma capability_extension_contains_old :
  forall CT h M source old field value,
    Included Loc M
      (extend_capability_after_write CT h M source old field value).
Proof. intros CT h M source old field value l Hin. left. exact Hin. Qed.

Lemma capability_extension_closed_after_write :
  forall CT h M source old field value,
    runtime_getObj h source = Some old ->
    mutable_heap_closed CT h M ->
    mutable_heap_closed CT (update_field h source field value)
      (extend_capability_after_write CT h M source old field value).
Proof.
  intros CT h M source old field value Hobj Hclosed l l'
    [Hinold | [target [D [fdef
      [Hvalue [Hsourcem [Hsub [Hfd [Hrdm Hreach]]]]]]]]] Hedge.
  - destruct (mutable_edge_after_field_update CT h source old field value l l'
      Hobj Hedge) as [Holdedge | [-> [Hwritten Hnewedge]]].
    + left. eapply Hclosed; eauto.
    + destruct Hnewedge as [D [fdef [Hsub [Hfd Hrdm]]]].
      right. exists l', D, fdef. repeat split; try assumption. constructor.
  - right. exists target, D, fdef. repeat split; try assumption.
    eapply mr_step; eauto.
Qed.

Lemma capability_extension_runtime_mut_after_write :
  forall CT h M source old field oldvalue value,
    wf_heap CT h ->
    wf_heap CT (update_field h source field value) ->
    runtime_getObj h source = Some old ->
    getVal old.(fields_map) field = Some oldvalue ->
    mutable_members_runtime_mut h M ->
    mutable_members_runtime_mut (update_field h source field value)
      (extend_capability_after_write CT h M source old field value).
Proof.
  intros CT h M source old field oldvalue value Hwf Hwf' Hobj Holdfield
    Hruntime l [Hinold | [target [D [fdef
      [Hvalue [Hsourcem [Hsub [Hfd [Hrdm Hreach]]]]]]]]].
  - rewrite r_muttype_update_field_preserve. apply Hruntime. exact Hinold.
  - subst value.
    have Hsource_runtime := Hruntime source Hsourcem.
    have Hedge := written_rdm_field_is_mutable_edge CT h source old field
      oldvalue target D fdef Hobj Holdfield Hsub Hfd Hrdm.
    have Htarget_runtime := mutable_edge_preserves_runtime_mutability CT
      (update_field h source field (Iot target)) source target Mut_r Hwf' Hedge.
    rewrite r_muttype_update_field_preserve in Htarget_runtime.
    specialize (Htarget_runtime Hsource_runtime).
    rewrite r_muttype_update_field_preserve in Htarget_runtime.
    eapply mutable_reachable_preserves_runtime_mutability
      with (source := target) (qruntime := Mut_r); eauto.
    rewrite r_muttype_update_field_preserve. exact Htarget_runtime.
Qed.

Lemma mutable_heap_closed_reachable :
  forall CT h M source target,
    mutable_heap_closed CT h M ->
    mutable_reachable CT h source target ->
    In Loc M source ->
    In Loc M target.
Proof.
  intros CT h M source target Hclosed Hreach Hsource.
  induction Hreach; [exact Hsource|].
  eapply Hclosed.
  - apply IHHreach. exact Hsource.
  - exact H.
Qed.

Lemma initial_forward_history :
  forall CT sGamma rGamma h,
    wf_r_config CT sGamma rGamma h ->
    env_respects_protected_set
      (reachable_locations_from_initial_env CT h rGamma) sGamma rGamma ->
    forward_history_state CT
      (reachable_locations_from_initial_env CT h rGamma)
      (reachable_locations_from_initial_env CT h rGamma)
      (Empty_set Loc) (dom h) sGamma rGamma h.
Proof.
  intros CT sGamma rGamma h Hwf Henv.
  refine (conj (fun l Hin => Hin)
    (conj Henv (conj (initial_state_is_confined CT sGamma rGamma h Hwf)
      (conj _ (conj _ (conj _ (conj _ _))))))).
  - intros source target Hin. contradiction.
  - intros l Hin. contradiction.
  - intros root [x [T [Htype [Hval Hmut]]]].
    assert (HinP : In Loc
      (reachable_locations_from_initial_env CT h rGamma) root).
    { exists x, root. split; [exact Hval|].
      apply rch_heap. eapply wf_config_value_dom; eauto. }
    have Hsafe := Henv x root T Htype Hval HinP.
    rewrite Hmut in Hsafe. unfold is_safe_mode in Hsafe.
    intuition discriminate.
  - intros l Hin. contradiction.
  - intros capability_root zone_root Hcapability Hzone.
    destruct Hcapability as [_ [target [_ HinM]]]. contradiction.
Qed.

Lemma initial_component_forward_history :
  forall CT sGamma rGamma h,
    wf_r_config CT sGamma rGamma h ->
    env_respects_protected_set
      (reachable_locations_from_initial_env CT h rGamma) sGamma rGamma ->
    component_forward_history_state CT
      (reachable_locations_from_initial_env CT h rGamma)
      (reachable_locations_from_initial_env CT h rGamma)
      (Empty_set Loc) (dom h) sGamma rGamma h.
Proof.
  intros CT sGamma rGamma h Hwf Henv. split.
  - eapply initial_forward_history; eauto.
  - split.
    + intros capability protected Hinempty. contradiction.
    + intros capability_root zone_root Hcaproot
        [member [Hinempty Hconnected]]. contradiction.
Qed.

Lemma safe_call_callee_rdm_root_origin :
  forall CT sGamma mt rGamma h x m y args sGamma'
    vals ly cy runtime_mdef root,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x m y args) sGamma' ->
    safe_readonly_method_type mt ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    typed_root RDM
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) root ->
    (exists Ty,
      static_getType sGamma y = Some Ty /\
      (sqtype Ty = Mut \/ sqtype Ty = Imm \/ sqtype Ty = RDM) /\
      typed_root (sqtype Ty) sGamma rGamma root) \/
    (exists Ty,
      static_getType sGamma y = Some Ty /\
      sqtype Ty = RO /\ root = ly).
Proof.
  intros CT sGamma mt rGamma h x m y args sGamma' vals ly cy runtime_mdef
    root Hwf Htyping Hsafe_scope Hval_y Hbase Hfind Hargs
    [z [T [Htype [Hval Hrdm]]]].
  inversion Htyping; subst.
  - exfalso. destruct Hscope as [-> | [-> _]];
      destruct Hsafe_scope; congruence.
  - assert (Hsignature : msignature runtime_mdef = msignature mdef).
    { eapply runtime_call_signature_agrees; eauto. }
    rewrite Hsignature in Htype. clear Hsignature.
    destruct z as [|i].
    + simpl in Htype, Hval. injection Htype as <-. injection Hval as <-.
      destruct Hrcv_sub as [Hordinary | [Hreadonly [Hformal_rdm Hbase_sub]]].
      * left. exists Ty. split; [exact Hget_y|]. split.
        -- apply qualified_type_subtype_q_subtype in Hordinary.
           unfold vpa_mutability_tt_safe_ro in Hordinary.
           rewrite Hrdm in Hordinary. simpl in Hordinary.
           have Hnotbot := wf_config_nonnull_variable_not_bot
             CT _ rGamma h y Ty ly Hwf Hget_y Hval_y.
           destruct (sqtype Ty) eqn:Hactual.
           all: simpl in Hordinary; try solve_q_subtype_wrong; try auto.
           all: try (inversion Hordinary; subst; congruence).
        -- exists y, Ty. repeat split; assumption.
      * right. exists Ty. repeat split; assumption.
    + simpl in Htype, Hval.
      assert (Hi : i < length (mparams (msignature mdef))).
      { have Htype_dom := Htype. apply static_getType_dom in Htype_dom.
        exact Htype_dom. }
      have Harg_lengths := Forall2_length Harg_sub.
      assert (Hi_args : i < length argtypes) by lia.
      destruct (nth_error_Some_exists argtypes i Hi_args) as [Targ HTarg].
      have Hsub_i := Harg_sub.
      eapply Forall2_nth_error with (i := i) (a := Targ) (b := T) in Hsub_i;
        [|exact HTarg|exact Htype].
      destruct (static_getType_list_nth_zs _ args argtypes i Targ
        Hget_args HTarg) as [arg [Harg_index Harg_type]].
      destruct (runtime_lookup_list_nth_zs rGamma args vals i (Iot root)
        Hargs Hval) as [arg' [Harg'_index Harg_val]].
      rewrite Harg_index in Harg'_index. injection Harg'_index as <-.
      left. exists Ty. split; [exact Hget_y|]. split.
      2: { exists arg, Targ. repeat split; try assumption.
           apply qualified_type_subtype_q_subtype in Hsub_i.
           unfold vpa_mutability_tt_safe_ro in Hsub_i.
           rewrite Hrdm in Hsub_i. simpl in Hsub_i.
           have Hnotbot := wf_config_nonnull_variable_not_bot
             CT _ rGamma h arg Targ root Hwf Harg_type Harg_val.
           destruct (sqtype Ty) eqn:Hreceiver; simpl in Hsub_i;
           destruct (sqtype Targ) eqn:Hactual;
             try solve_q_subtype_wrong; try reflexivity;
             try (exfalso; apply Hnotbot; exact Hactual);
             inversion Hsub_i; subst; congruence. }
      apply qualified_type_subtype_q_subtype in Hsub_i.
      unfold vpa_mutability_tt_safe_ro in Hsub_i.
      rewrite Hrdm in Hsub_i. simpl in Hsub_i.
      have Hnotbot := wf_config_nonnull_variable_not_bot
        CT _ rGamma h arg Targ root Hwf Harg_type Harg_val.
      destruct (sqtype Ty) eqn:Hreceiver; simpl in Hsub_i;
      destruct (sqtype Targ) eqn:Hactual;
        try solve_q_subtype_wrong; auto;
        try (exfalso; apply Hnotbot; exact Hactual);
        inversion Hsub_i; subst; congruence.
Qed.

Lemma immutable_root_cannot_touch_capability_component :
  forall CT h M sGamma rGamma root,
    wf_r_config CT sGamma rGamma h ->
    mutable_members_runtime_mut h M ->
    typed_root Imm sGamma rGamma root ->
    component_touches CT h M root ->
    False.
Proof.
  intros CT h M sGamma rGamma root Hwf Hruntime
    [x [T [Htype [Hval Himm]]]] [member [HinM Hconnected]].
  destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwf)
    as [this [qcontext [Hthis [_ Hqcontext]]]].
  have Hwf_copy := Hwf.
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [Hwfheap [_ [_ [_ Hcorr]]]]].
  have Hxdom := Htype. apply static_getType_dom in Hxdom.
  specialize (Hcorr this qcontext Hthis Hqcontext x Hxdom T Htype).
  rewrite Hval in Hcorr.
  have Hmember_runtime := Hruntime member HinM.
  have Hroot_runtime := mutable_connected_preserves_runtime_mutability
    CT h member root Mut_r Hwfheap
    (mutable_connected_sym CT h root member Hconnected) Hmember_runtime.
  eapply runtime_mut_typable_not_imm; eauto.
Qed.

Lemma active_rdm_roots_share_runtime_context :
  forall CT sGamma rGamma h root1 root2,
    wf_r_config CT sGamma rGamma h ->
    typed_root RDM sGamma rGamma root1 ->
    typed_root RDM sGamma rGamma root2 ->
    exists qcontext,
      r_muttype h root1 = Some qcontext /\
      r_muttype h root2 = Some qcontext.
Proof.
  intros CT sGamma rGamma h root1 root2 Hwf
    [x1 [T1 [Htype1 [Hval1 Hrdm1]]]]
    [x2 [T2 [Htype2 [Hval2 Hrdm2]]]].
  destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwf)
    as [this [qcontext [Hthis [_ Hqcontext]]]].
  have Hwf_copy := Hwf.
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [_ [_ [_ Hcorr]]]]].
  have Hdom1 := Htype1. apply static_getType_dom in Hdom1.
  have Hdom2 := Htype2. apply static_getType_dom in Hdom2.
  have Htyp1 := Hcorr this qcontext Hthis Hqcontext x1 Hdom1 T1 Htype1.
  have Htyp2 := Hcorr this qcontext Hthis Hqcontext x2 Hdom2 T2 Htype2.
  rewrite Hval1 in Htyp1. rewrite Hval2 in Htyp2.
  exists qcontext. split.
  - eapply rdm_typable_runtime_matches_context; eauto.
  - eapply rdm_typable_runtime_matches_context; eauto.
Qed.

Lemma active_capability_rdm_excludes_immutable_endpoint :
  forall CT h M sGamma rGamma capability_root other_root endpoint,
    wf_r_config CT sGamma rGamma h ->
    mutable_members_runtime_mut h M ->
    typed_root RDM sGamma rGamma capability_root ->
    component_touches CT h M capability_root ->
    typed_root RDM sGamma rGamma other_root ->
    mutable_connected CT h other_root endpoint ->
    typed_root Imm sGamma rGamma endpoint ->
    False.
Proof.
  intros CT h M sGamma rGamma capability_root other_root endpoint Hwf
    Hruntime Hcaproot [member [HinM Hcap_member]] Hother Hother_endpoint
    [x [T [Htype [Hval Himm]]]].
  have Hwf_copy := Hwf.
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [Hwfheap [_ [_ [_ Hcorr]]]]].
  have Hmember_runtime := Hruntime member HinM.
  have Hcap_runtime := mutable_connected_preserves_runtime_mutability
    CT h member capability_root Mut_r Hwfheap
    (mutable_connected_sym CT h capability_root member Hcap_member)
    Hmember_runtime.
  destruct (active_rdm_roots_share_runtime_context CT sGamma rGamma h
    capability_root other_root Hwf_copy Hcaproot Hother) as
    [qcontext [Hcap_context Hother_context]].
  rewrite Hcap_runtime in Hcap_context. injection Hcap_context as <-.
  have Hendpoint_runtime := mutable_connected_preserves_runtime_mutability
    CT h other_root endpoint Mut_r Hwfheap Hother_endpoint Hother_context.
  destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwf_copy)
    as [this [actual_context [Hthis [_ Hactual_context]]]].
  unfold wf_r_config in Hwf_copy.
  destruct Hwf_copy as [_ [_ [_ [_ [_ Hcorr_copy]]]]].
  have Hxdom := Htype. apply static_getType_dom in Hxdom.
  specialize (Hcorr_copy this actual_context Hthis Hactual_context
    x Hxdom T Htype).
  rewrite Hval in Hcorr_copy.
  eapply runtime_mut_typable_not_imm; eauto.
Qed.

Lemma safe_call_callee_active_component_colors :
  forall CT P Z M cutoff sGamma mt rGamma h x m y args sGamma'
    vals ly cy runtime_mdef,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x m y args) sGamma' ->
    safe_readonly_method_type mt ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    active_rdm_component_colors_separated CT h M Z
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)).
Proof.
  intros CT P Z M cutoff sGamma mt rGamma h x m y args sGamma' vals ly cy
    runtime_mdef Hwf Htyping Hscope
    [[Hcontains [Henv [Hconfined [Hclosed [Hruntime
      [Hmutroots [Havoid Holdcolors]]]]]]]
      [Hcomponents Hactive]]
    Hval_y Hbase Hfind Hargs capability_root zone_root Hcaproot Hcapability
    Hzoneroot Hzone.
  destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x m y
    args sGamma' vals ly cy runtime_mdef capability_root Hwf Htyping Hscope
    Hval_y Hbase Hfind Hargs Hcaproot) as
    [[Tcap [Hreceiver_cap [Hcapqual Hcaporigin]]] |
     [Tcap [Hreceiver_cap [Hcapro Hcaproot_eq]]]].
  - destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x m y
      args sGamma' vals ly cy runtime_mdef zone_root Hwf Htyping Hscope
      Hval_y Hbase Hfind Hargs Hzoneroot) as
      [[Tzone [Hreceiver_zone [Hzonequal Hzoneorigin]]] |
       [Tzone [Hreceiver_zone [Hzonero Hzoneroot_eq]]]].
    + rewrite Hreceiver_cap in Hreceiver_zone. injection Hreceiver_zone as <-.
      destruct Hcapqual as [Hmut | [Himm | Hrdm]].
      * rewrite Hmut in Hzoneorigin.
        eapply separated_components_cannot_touch_both with (root := zone_root).
        -- exact Hcomponents.
        -- destruct Hzoneorigin as [z [T [Htype [Hval Hqual]]]].
           exists zone_root. split.
           ++ apply Hmutroots. exists z, T. repeat split; assumption.
           ++ apply mutable_connected_refl.
        -- exact Hzone.
      * rewrite Himm in Hcaporigin.
        eapply immutable_root_cannot_touch_capability_component
          with (root := capability_root); eauto.
      * rewrite Hrdm in Hcaporigin, Hzoneorigin.
        eapply Hactive with (capability_root := capability_root)
          (zone_root := zone_root); eauto.
    + rewrite Hreceiver_cap in Hreceiver_zone. injection Hreceiver_zone as <-.
      rewrite Hzonero in Hcapqual.
      destruct Hcapqual as [Hbad | [Hbad | Hbad]]; discriminate.
  - destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x m y
      args sGamma' vals ly cy runtime_mdef zone_root Hwf Htyping Hscope
      Hval_y Hbase Hfind Hargs Hzoneroot) as
      [[Tzone [Hreceiver_zone [Hzonequal Hzoneorigin]]] |
       [Tzone [Hreceiver_zone [Hzonero Hzoneroot_eq]]]].
    + rewrite Hreceiver_cap in Hreceiver_zone. injection Hreceiver_zone as <-.
      rewrite Hcapro in Hzonequal.
      destruct Hzonequal as [Hbad | [Hbad | Hbad]]; discriminate.
    + subst capability_root zone_root.
      eapply separated_components_cannot_touch_both with (root := ly); eauto.
Qed.

Lemma safe_call_callee_component_forward_history :
  forall CT P Z M cutoff sGamma mt rGamma h x m y args sGamma'
    vals ly cy runtime_mdef,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x m y args) sGamma' ->
    safe_readonly_method_type mt ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    component_forward_history_state CT P Z M cutoff
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) h.
Proof.
  intros CT P Z M cutoff sGamma mt rGamma h x m y args sGamma' vals ly cy
    runtime_mdef Hwf Htyping Hscope Hstate Hval_y Hbase Hfind Hargs.
  have Hactive' := safe_call_callee_active_component_colors CT P Z M cutoff
    sGamma mt rGamma h x m y args sGamma' vals ly cy runtime_mdef Hwf
    Htyping Hscope Hstate Hval_y Hbase Hfind Hargs.
  destruct Hstate as
    [[Hcontains [Henv [Hconfined [Hclosed [Hruntime
      [Hmutroots [Havoid Holdcolors]]]]]]]
      [Hcomponents Hactive]].
  split.
  - refine (conj Hcontains (conj _ (conj _ (conj Hclosed
      (conj Hruntime (conj _ (conj Havoid _))))))).
    + eapply safe_call_callee_zone_env; eauto.
    + eapply call_callee_operationally_confined; eauto.
    + intros root Hroot. exfalso.
      eapply safe_call_callee_has_no_mut_root; eauto.
    + intros capability_root zone_root
        [Hcaproot [capability [Hcapreach Hcapability]]]
        [Hzoneroot [protected [Hzonereach Hprotected]]].
      eapply Hactive' with (capability_root := capability_root)
        (zone_root := zone_root).
      * exact Hcaproot.
      * exists capability. split; [exact Hcapability|].
        eapply mutable_reachable_connected; exact Hcapreach.
      * exact Hzoneroot.
      * exists protected. split; [exact Hprotected|].
        eapply mutable_reachable_connected; exact Hzonereach.
  - split; [exact Hcomponents|exact Hactive'].
Qed.

Lemma forward_expression_into_zone_has_safe_type :
  forall P Z M cutoff CT sGamma mt rGamma h e l T,
    wf_r_config CT sGamma rGamma h ->
    forward_history_state CT P Z M cutoff sGamma rGamma h ->
    eval_expr OK P CT rGamma h e (Iot l) OK P rGamma h ->
    expr_has_type CT sGamma mt e T ->
    safe_readonly_method_type mt ->
    In Loc Z l ->
    is_safe_mode (sqtype T).
Proof.
  intros P Z M cutoff CT sGamma mt rGamma h e l T Hwf
    [Hcontains [Henv [Hconfined [Hclosed [Hruntime
      [Hmutroots [Havoid Hcolors]]]]]]] Heval Htyping Hscope HinZ.
  inversion Heval; subst.
  - inversion Htyping; subst.
    destruct (sqtype T) eqn:Hq; unfold is_safe_mode; auto.
    + exfalso. apply (Havoid l).
      * apply Hmutroots. exists x, T. repeat split; assumption.
      * exact HinZ.
    + exfalso.
      destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwf)
        as [this [qcontext [Hthis [_ Hqcontext]]]].
      unfold wf_r_config in Hwf.
      destruct Hwf as [_ [_ [_ [_ [_ Hcorr]]]]].
      have Hxdom := Hget. apply static_getType_dom in Hxdom.
      specialize (Hcorr this qcontext Hthis Hqcontext x Hxdom T Hget).
      rewrite Hval in Hcorr.
      eapply typable_nonnull_not_bot; eauto.
  - inversion Htyping; subst.
    + exfalso. destruct Hmt; subst; destruct Hscope; congruence.
    + destruct (sqtype T0) eqn:Hreceiver;
        destruct (mutability (ftype fDef)) eqn:Hfieldq;
        simpl; unfold is_safe_mode; auto.
      * exfalso. apply (Havoid l).
        -- eapply Hclosed.
          ++ apply Hmutroots. exists x, T0.
             split; [exact Hget_x|]. split; [exact Hval|exact Hreceiver].
          ++ eapply runtime_static_rdm_edge; eauto.
        -- exact HinZ.
      * exfalso.
        destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwf)
          as [this [qcontext [Hthis [_ Hqcontext]]]].
        unfold wf_r_config in Hwf.
        destruct Hwf as [_ [_ [_ [_ [_ Hcorr]]]]].
        have Hxdom := Hget_x. apply static_getType_dom in Hxdom.
        specialize (Hcorr this qcontext Hthis Hqcontext x Hxdom T0 Hget_x).
        rewrite Hval in Hcorr.
        eapply typable_nonnull_not_bot; eauto.
Qed.

Lemma safe_rdm_write_component_colors_cannot_cross :
  forall CT P Z M cutoff h sGamma rGamma x y lx ly Tx Ty Ctarget,
    wf_r_config CT sGamma rGamma h ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    static_getType sGamma x = Some Tx ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma x = Some (Iot lx) ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    qualified_type_subtype CT Ty
      (Build_qualified_type
        (vpa_mutability_stype_fld_safe_ro (sqtype Tx) RDM_f) Ctarget) ->
    (component_touches CT h M lx ->
      component_touches CT h Z ly -> False) /\
    (component_touches CT h Z lx ->
      component_touches CT h M ly -> False).
Proof.
  intros CT P Z M cutoff h sGamma rGamma x y lx ly Tx Ty Ctarget Hwf
    [[Hcontains [Henv [Hconfined [Hclosed [Hruntime
      [Hmutroots [Havoid Holdcolors]]]]]]]
      [Hcomponents Hactivecolors]]
    Hgetx Hgety Hvalx Hvaly Hsub.
  destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwf)
    as [this [qcontext [Hthis [_ Hqcontext]]]].
  have Hwf_copy := Hwf.
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [_ [_ [_ Hcorr]]]]].
  have Hxdom := Hgetx. apply static_getType_dom in Hxdom.
  have Hydom := Hgety. apply static_getType_dom in Hydom.
  have Hxtyp := Hcorr this qcontext Hthis Hqcontext x Hxdom Tx Hgetx.
  have Hytyp := Hcorr this qcontext Hthis Hqcontext y Hydom Ty Hgety.
  rewrite Hvalx in Hxtyp. rewrite Hvaly in Hytyp.
  have Hxnotbot := typable_nonnull_not_bot CT rGamma h lx Tx qcontext Hxtyp.
  have Hynotbot := typable_nonnull_not_bot CT rGamma h ly Ty qcontext Hytyp.
  apply qualified_type_subtype_q_subtype in Hsub.
  destruct (sqtype Tx) eqn:Hqx.
  - destruct (sqtype Ty) eqn:Hqy; simpl in Hsub;
      try solve_q_subtype_wrong.
    + assert (HlxM : In Loc M lx).
      { apply Hmutroots. exists x, Tx. repeat split; assumption. }
      assert (HlyM : In Loc M ly).
      { apply Hmutroots. exists y, Ty. repeat split; assumption. }
      split.
      * intros _ HlyZ.
        eapply separated_components_cannot_touch_both with (root := ly); eauto.
        exists ly. split; [exact HlyM|apply mutable_connected_refl].
      * intros HlxZ _.
        eapply separated_components_cannot_touch_both with (root := lx); eauto.
        exists lx. split; [exact HlxM|apply mutable_connected_refl].
    + exfalso. apply Hynotbot. reflexivity.
  - split.
    + intros HlxM _.
      eapply immutable_root_cannot_touch_capability_component
        with (root := lx).
      * exact Hwf_copy.
      * exact Hruntime.
      * exists x, Tx. repeat split; assumption.
      * exact HlxM.
    + destruct (sqtype Ty) eqn:Hqy; simpl in Hsub;
        try solve_q_subtype_wrong.
      * intros _ HlyM.
        eapply immutable_root_cannot_touch_capability_component
          with (root := ly).
        -- exact Hwf_copy.
        -- exact Hruntime.
        -- exists y, Ty. repeat split; assumption.
        -- exact HlyM.
      * exfalso. apply Hynotbot. reflexivity.
  - destruct (sqtype Ty) eqn:Hqy; simpl in Hsub;
      try solve_q_subtype_wrong.
    + split.
      * intros HlxM HlyZ.
        eapply Hactivecolors with (capability_root := lx) (zone_root := ly).
        -- exists x, Tx. repeat split; assumption.
        -- exact HlxM.
        -- exists y, Ty. repeat split; assumption.
        -- exact HlyZ.
      * intros HlxZ HlyM.
        eapply Hactivecolors with (capability_root := ly) (zone_root := lx).
        -- exists y, Ty. repeat split; assumption.
        -- exact HlyM.
        -- exists x, Tx. repeat split; assumption.
        -- exact HlxZ.
    + exfalso. apply Hynotbot. reflexivity.
  - destruct (sqtype Ty) eqn:Hqy; simpl in Hsub;
      try solve_q_subtype_wrong; exfalso; apply Hynotbot; reflexivity.
  - destruct (sqtype Ty) eqn:Hqy; simpl in Hsub;
      try solve_q_subtype_wrong; exfalso; apply Hynotbot; reflexivity.
  - exfalso. apply Hxnotbot. reflexivity.
Qed.

Lemma typed_runtime_rdm_field_write_subtyping :
  forall CT sGamma mt rGamma h x f y lx old D runtime_fd sGamma',
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SFldWrite x f y) sGamma' ->
    safe_readonly_method_type mt ->
    runtime_getVal rGamma x = Some (Iot lx) ->
    runtime_getObj h lx = Some old ->
    base_subtype CT (rctype (rt_type old)) D ->
    sf_def_rel CT D f runtime_fd ->
    mutability (ftype runtime_fd) = RDM_f ->
    exists Tx Ty,
      static_getType sGamma x = Some Tx /\
      static_getType sGamma y = Some Ty /\
      qualified_type_subtype CT Ty
        (Build_qualified_type
          (vpa_mutability_stype_fld_safe_ro (sqtype Tx) RDM_f)
          (f_base_type (ftype runtime_fd))).
Proof.
  intros CT sGamma mt rGamma h x f y lx old D runtime_fd sGamma' Hwf
    Htyping Hscope Hvalx Hobj Hruntime_sub Hruntime_fd Hruntime_rdm.
  inversion Htyping; subst.
  - exfalso. destruct Hscope; congruence.
  - exfalso. destruct Hscope; congruence.
  - assert (Hbase : base_subtype CT (rctype (rt_type old)) (sctype Tx)).
    { destruct (extract_receiver_from_wf_config CT _ rGamma h Hwf)
        as [thisloc [qcontext [Hrthis [_ Hrcontext]]]].
      unfold wf_r_config in Hwf.
      destruct Hwf as [_ [_ [_ [_ [_ Hcorr]]]]].
      have Hxdom := Hget_x. apply static_getType_dom in Hxdom.
      specialize (Hcorr thisloc qcontext Hrthis Hrcontext x Hxdom Tx Hget_x).
      rewrite Hvalx in Hcorr.
      unfold wf_r_typable, r_type in Hcorr. rewrite Hobj in Hcorr.
      exact (proj1 Hcorr). }
    assert (runtime_fd = fieldT).
    { eapply field_defs_agree_at_runtime_subtype with
        (C := rctype (rt_type old)) (D1 := D) (D2 := sctype Tx); eauto. }
    subst runtime_fd. exists Tx, Ty. repeat split; try assumption.
    rewrite Hruntime_rdm in Hsub. exact Hsub.
  - assert (Hbase : base_subtype CT (rctype (rt_type old)) (sctype Tx)).
    { destruct (extract_receiver_from_wf_config CT _ rGamma h Hwf)
        as [thisloc [qcontext [Hrthis [_ Hrcontext]]]].
      unfold wf_r_config in Hwf.
      destruct Hwf as [_ [_ [_ [_ [_ Hcorr]]]]].
      have Hxdom := Hget_x. apply static_getType_dom in Hxdom.
      specialize (Hcorr thisloc qcontext Hrthis Hrcontext x Hxdom Tx Hget_x).
      rewrite Hvalx in Hcorr.
      unfold wf_r_typable, r_type in Hcorr. rewrite Hobj in Hcorr.
      exact (proj1 Hcorr). }
    assert (runtime_fd = fieldT).
    { eapply field_defs_agree_at_runtime_subtype with
        (C := rctype (rt_type old)) (D1 := D) (D2 := sctype Tx); eauto. }
    subst runtime_fd. exists Tx, Ty. repeat split; try assumption.
    rewrite Hruntime_rdm in Hsub. exact Hsub.
Qed.

(** A successful non-null write to an RDM field in a safe scope has one of
    three homogeneous endpoint shapes.  In particular, RO and Lost aliases
    cannot be used to manufacture an RDM edge: their adapted field type is
    Lost, and no non-bottom run-time value has a subtype of Lost. *)
Lemma safe_rdm_write_endpoint_qualifiers :
  forall CT sGamma rGamma h x y lx ly Tx Ty Ctarget,
    wf_r_config CT sGamma rGamma h ->
    static_getType sGamma x = Some Tx ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma x = Some (Iot lx) ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    qualified_type_subtype CT Ty
      (Build_qualified_type
        (vpa_mutability_stype_fld_safe_ro (sqtype Tx) RDM_f) Ctarget) ->
    (sqtype Tx = Mut /\ sqtype Ty = Mut) \/
    (sqtype Tx = Imm /\ sqtype Ty = Imm) \/
    (sqtype Tx = RDM /\ sqtype Ty = RDM).
Proof.
  intros CT sGamma rGamma h x y lx ly Tx Ty Ctarget Hwf Hgetx Hgety
    Hvalx Hvaly Hsub.
  destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwf)
    as [receiver [qcontext [Hreceiver [Hreceiver_dom Hcontext]]]].
  have Hwf_copy := Hwf.
  unfold wf_r_config in Hwf.
  destruct Hwf as [Hclasses [Hheap [Hrenv [Hsenv [Hlength Hcorr]]]]].
  have Hxdom := Hgetx. apply static_getType_dom in Hxdom.
  have Hydom := Hgety. apply static_getType_dom in Hydom.
  have Hxtyp := Hcorr receiver qcontext Hreceiver Hcontext x Hxdom Tx Hgetx.
  have Hytyp := Hcorr receiver qcontext Hreceiver Hcontext y Hydom Ty Hgety.
  rewrite Hvalx in Hxtyp. rewrite Hvaly in Hytyp.
  have Hxnotbot := typable_nonnull_not_bot CT rGamma h lx Tx qcontext Hxtyp.
  have Hynotbot := typable_nonnull_not_bot CT rGamma h ly Ty qcontext Hytyp.
  apply qualified_type_subtype_q_subtype in Hsub.
  destruct (sqtype Tx) eqn:Hqx;
    destruct (sqtype Ty) eqn:Hqy;
    simpl in Hsub.
  all: try solve_q_subtype_wrong.
  all: try (exfalso; apply Hxnotbot; reflexivity).
  all: try (exfalso; apply Hynotbot; reflexivity).
  - left. split; reflexivity.
  - right. left. split; reflexivity.
  - right. right. split; reflexivity.
Qed.

Lemma typed_field_write_runtime_field_agreement :
  forall CT sGamma mt rGamma h x f y lx old sGamma',
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SFldWrite x f y) sGamma' ->
    runtime_getVal rGamma x = Some (Iot lx) ->
    runtime_getObj h lx = Some old ->
    exists Tx fieldT,
      static_getType sGamma x = Some Tx /\
      sf_def_rel CT (sctype Tx) f fieldT /\
      base_subtype CT (rctype (rt_type old)) (sctype Tx).
Proof.
  intros CT sGamma mt rGamma h x f y lx old sGamma' Hwf Htyping Hvalx Hobj.
  inversion Htyping; subst.
  all: exists Tx, fieldT; repeat split; try assumption.
  all: destruct (extract_receiver_from_wf_config CT _ rGamma h Hwf)
    as [thisloc [qcontext [Hrthis [_ Hrcontext]]]].
  all: unfold wf_r_config in Hwf.
  all: destruct Hwf as [_ [_ [_ [_ [_ Hcorr]]]]].
  all: have Hxdom := Hget_x; apply static_getType_dom in Hxdom.
  all: specialize (Hcorr thisloc qcontext Hrthis Hrcontext x Hxdom Tx Hget_x).
  all: rewrite Hvalx in Hcorr.
  all: unfold wf_r_typable, r_type in Hcorr; rewrite Hobj in Hcorr.
  all: exact (proj1 Hcorr).
Qed.

Lemma component_colors_after_typed_rdm_field_update_existing_set :
  forall CT P Z M cutoff sGamma mt rGamma h x f y lx old value
    D runtime_fd sGamma',
    wf_r_config CT sGamma rGamma h ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SFldWrite x f y) sGamma' ->
    safe_readonly_method_type mt ->
    runtime_getVal rGamma x = Some (Iot lx) ->
    runtime_getVal rGamma y = Some value ->
    runtime_getObj h lx = Some old ->
    base_subtype CT (rctype (rt_type old)) D ->
    sf_def_rel CT D f runtime_fd ->
    mutability (ftype runtime_fd) = RDM_f ->
    component_colors_separated CT (update_field h lx f value) M Z.
Proof.
  intros CT P Z M cutoff sGamma mt rGamma h x f y lx old value D
    runtime_fd sGamma' Hwf Hstate Htyping Hscope Hvalx Hvaly Hobj
    Hruntime_sub Hruntime_fd Hruntime_rdm.
  destruct (typed_runtime_rdm_field_write_subtyping CT sGamma mt rGamma h
    x f y lx old D runtime_fd sGamma' Hwf Htyping Hscope Hvalx Hobj
    Hruntime_sub Hruntime_fd Hruntime_rdm) as
    [Tx [Ty [Hgetx [Hgety Hsub]]]].
  destruct Hstate as [Hforward [Hcomponents Hactive]].
  eapply component_colors_after_field_update_existing_sets.
  - exact Hobj.
  - exact Hcomponents.
  - intros written Hvalue HlxM HwrittenZ.
    have Hvaly_written := Hvaly. rewrite Hvalue in Hvaly_written.
    have Hcross := safe_rdm_write_component_colors_cannot_cross
      CT P Z M cutoff h sGamma rGamma x y lx written Tx Ty
      (f_base_type (ftype runtime_fd)) Hwf
      (conj Hforward (conj Hcomponents Hactive)) Hgetx Hgety Hvalx
      Hvaly_written Hsub.
    exact (proj1 Hcross HlxM HwrittenZ).
  - intros written Hvalue HlxZ HwrittenM.
    have Hvaly_written := Hvaly. rewrite Hvalue in Hvaly_written.
    have Hcross := safe_rdm_write_component_colors_cannot_cross
      CT P Z M cutoff h sGamma rGamma x y lx written Tx Ty
      (f_base_type (ftype runtime_fd)) Hwf
      (conj Hforward (conj Hcomponents Hactive)) Hgetx Hgety Hvalx
      Hvaly_written Hsub.
    exact (proj2 Hcross HlxZ HwrittenM).
Qed.

Lemma component_colors_after_typed_field_update_existing_set :
  forall CT P Z M cutoff sGamma mt rGamma h x f y lx old value sGamma',
    wf_r_config CT sGamma rGamma h ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SFldWrite x f y) sGamma' ->
    safe_readonly_method_type mt ->
    runtime_getVal rGamma x = Some (Iot lx) ->
    runtime_getVal rGamma y = Some value ->
    runtime_getObj h lx = Some old ->
    component_colors_separated CT (update_field h lx f value) M Z.
Proof.
  intros CT P Z M cutoff sGamma mt rGamma h x f y lx old value sGamma'
    Hwf Hstate Htyping Hscope Hvalx Hvaly Hobj.
  destruct (typed_field_write_runtime_field_agreement CT sGamma mt rGamma h
    x f y lx old sGamma' Hwf Htyping Hvalx Hobj) as
    [Tx [fieldT [Hgetx [Hfield Hbase]]]].
  destruct (mutability (ftype fieldT)) eqn:Hfieldq.
  - eapply component_colors_after_non_rdm_field_update
      with (C := sctype Tx) (fieldT := fieldT).
    + exact Hobj.
    + exact Hbase.
    + exact Hfield.
    + intro Hbad. rewrite Hfieldq in Hbad. discriminate.
    + exact (proj1 (proj2 Hstate)).
  - eapply component_colors_after_non_rdm_field_update
      with (C := sctype Tx) (fieldT := fieldT).
    + exact Hobj.
    + exact Hbase.
    + exact Hfield.
    + intro Hbad. rewrite Hfieldq in Hbad. discriminate.
    + exact (proj1 (proj2 Hstate)).
  - eapply component_colors_after_typed_rdm_field_update_existing_set
      with (D := sctype Tx) (runtime_fd := fieldT); eauto.
  - eapply component_colors_after_non_rdm_field_update
      with (C := sctype Tx) (fieldT := fieldT).
    + exact Hobj.
    + exact Hbase.
    + exact Hfield.
    + intro Hbad. rewrite Hfieldq in Hbad. discriminate.
    + exact (proj1 (proj2 Hstate)).
Qed.

Lemma capability_extension_after_typed_write_avoids_zone :
  forall CT P Z M cutoff sGamma mt rGamma h x f y lx old oldvalue value sGamma',
    wf_r_config CT sGamma rGamma h ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SFldWrite x f y) sGamma' ->
    safe_readonly_method_type mt ->
    runtime_getVal rGamma x = Some (Iot lx) ->
    runtime_getVal rGamma y = Some value ->
    runtime_getObj h lx = Some old ->
    getVal old.(fields_map) f = Some oldvalue ->
    forall protected,
      In Loc
        (extend_capability_after_write CT h M lx old f value) protected ->
      ~ In Loc Z protected.
Proof.
  intros CT P Z M cutoff sGamma mt rGamma h x f y lx old oldvalue value
    sGamma' Hwf Hstate Htyping Hscope Hvalx Hvaly Hobj Holdfield protected
    [HinM | [ly [D [runtime_fd [Hvalue [HsourceM
      [Hruntime_sub [Hruntime_fd [Hruntime_rdm Hreach]]]]]]]]] HinZ.
  - destruct Hstate as
      [[Hcontains [Henv [Hconfined [Hclosed [Hruntime
        [Hmutroots [Havoid Hcolors]]]]]]] Hcomponentfacts].
    eapply Havoid; eauto.
  - have Hcomponents := component_colors_after_typed_rdm_field_update_existing_set
      CT P Z M cutoff sGamma mt rGamma h x f y lx old value D runtime_fd
      sGamma' Hwf Hstate Htyping Hscope Hvalx Hvaly Hobj Hruntime_sub
      Hruntime_fd Hruntime_rdm.
    subst value.
    have Hnewedge := written_rdm_field_is_mutable_edge CT h lx old f
      oldvalue ly D runtime_fd Hobj Holdfield Hruntime_sub Hruntime_fd
      Hruntime_rdm.
    apply (Hcomponents lx protected HsourceM HinZ).
    eapply mutable_connected_trans.
    + eapply mutable_connected_step; exact Hnewedge.
    + eapply mutable_reachable_connected; exact Hreach.
Qed.

Lemma component_colors_after_typed_field_write_extension :
  forall CT P Z M cutoff sGamma mt rGamma h x f y lx old oldvalue value
    sGamma',
    wf_r_config CT sGamma rGamma h ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SFldWrite x f y) sGamma' ->
    safe_readonly_method_type mt ->
    runtime_getVal rGamma x = Some (Iot lx) ->
    runtime_getVal rGamma y = Some value ->
    runtime_getObj h lx = Some old ->
    getVal old.(fields_map) f = Some oldvalue ->
    component_colors_separated CT (update_field h lx f value)
      (extend_capability_after_write CT h M lx old f value) Z.
Proof.
  intros CT P Z M cutoff sGamma mt rGamma h x f y lx old oldvalue value
    sGamma' Hwf Hstate Htyping Hscope Hvalx Hvaly Hobj Holdfield.
  have Hexisting := component_colors_after_typed_field_update_existing_set
    CT P Z M cutoff sGamma mt rGamma h x f y lx old value sGamma'
    Hwf Hstate Htyping Hscope Hvalx Hvaly Hobj.
  intros capability protected
    [Hcapability | [target [D [runtime_fd [Hvalue [HsourceM
      [Hruntime_sub [Hruntime_fd [Hruntime_rdm Hreach]]]]]]]]]
    Hprotected Hconnected.
  - exact (Hexisting capability protected Hcapability Hprotected Hconnected).
  - subst value.
    have Hnewedge := written_rdm_field_is_mutable_edge CT h lx old f
      oldvalue target D runtime_fd Hobj Holdfield Hruntime_sub Hruntime_fd
      Hruntime_rdm.
    apply (Hexisting lx protected HsourceM Hprotected).
    eapply mutable_connected_trans.
    + eapply mutable_connected_trans.
      * eapply mutable_connected_step; exact Hnewedge.
      * eapply mutable_reachable_connected; exact Hreach.
    + exact Hconnected.
Qed.

Lemma component_touch_extension_reduces_to_old_capability_set :
  forall CT h M source old oldvalue field value root,
    runtime_getObj h source = Some old ->
    getVal old.(fields_map) field = Some oldvalue ->
    component_touches CT (update_field h source field value)
      (extend_capability_after_write CT h M source old field value) root ->
    component_touches CT (update_field h source field value) M root.
Proof.
  intros CT h M source old oldvalue field value root Hobj Holdfield
    [member [[HinM | [target [D [runtime_fd [Hvalue [HsourceM
      [Hruntime_sub [Hruntime_fd [Hruntime_rdm Hreach]]]]]]]]]
      Hroot_member]].
  - exists member. split; assumption.
  - subst value. exists source. split; [exact HsourceM|].
    have Hnewedge := written_rdm_field_is_mutable_edge CT h source old field
      oldvalue target D runtime_fd Hobj Holdfield Hruntime_sub Hruntime_fd
      Hruntime_rdm.
    eapply mutable_connected_trans; [exact Hroot_member|].
    eapply mutable_connected_sym.
    eapply mutable_connected_trans.
    + eapply mutable_connected_step; exact Hnewedge.
    + eapply mutable_reachable_connected; exact Hreach.
Qed.

Lemma non_rdm_capability_extension_is_old :
  forall CT h M source old field value C fieldT,
    base_subtype CT (rctype (rt_type old)) C ->
    sf_def_rel CT C field fieldT ->
    mutability (ftype fieldT) <> RDM_f ->
    Included Loc
      (extend_capability_after_write CT h M source old field value) M.
Proof.
  intros CT h M source old field value C fieldT Hbase Hfield Hnotrdm
    member [HinM | [target [D [runtime_fd [Hvalue [HsourceM
      [Hruntime_base [Hruntime_field [Hruntime_rdm Hreach]]]]]]]]].
  - exact HinM.
  - assert (runtime_fd = fieldT).
    { eapply field_defs_agree_at_runtime_subtype with
        (C := rctype (rt_type old)) (D1 := D) (D2 := C); eauto. }
    subst runtime_fd. contradiction.
Qed.

Lemma active_rdm_colors_after_typed_non_rdm_field_write :
  forall CT P Z M cutoff sGamma mt rGamma h x f y lx old value sGamma'
    Tx fieldT,
    wf_r_config CT sGamma rGamma h ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SFldWrite x f y) sGamma' ->
    runtime_getVal rGamma x = Some (Iot lx) ->
    runtime_getObj h lx = Some old ->
    static_getType sGamma x = Some Tx ->
    sf_def_rel CT (sctype Tx) f fieldT ->
    base_subtype CT (rctype (rt_type old)) (sctype Tx) ->
    mutability (ftype fieldT) <> RDM_f ->
    active_rdm_component_colors_separated CT (update_field h lx f value)
      (extend_capability_after_write CT h M lx old f value) Z
      sGamma' rGamma.
Proof.
  intros CT P Z M cutoff sGamma mt rGamma h x f y lx old value sGamma'
    Tx fieldT Hwf [Hforward [Hcomponents Hactive]] Htyping Hvalx Hobj
    Hgetx Hfield Hbase Hnotrdm.
  assert (HsGamma : sGamma' = sGamma) by (inversion Htyping; reflexivity).
  subst sGamma'.
  have Hextension := non_rdm_capability_extension_is_old CT h M lx old f
    value (sctype Tx) fieldT Hbase Hfield Hnotrdm.
  intros capability_root zone_root Hcaproot
    [capability [Hcapability Hcapconnected]] Hzoneroot
    [protected [Hprotected Hzoneconnected]].
  apply (Hactive capability_root zone_root Hcaproot).
  - exists capability. split; [apply Hextension; exact Hcapability|].
    eapply mutable_connected_after_non_rdm_field_update_is_old; eauto.
  - exact Hzoneroot.
  - exists protected. split; [exact Hprotected|].
    eapply mutable_connected_after_non_rdm_field_update_is_old; eauto.
Qed.

Lemma null_capability_extension_is_old :
  forall CT h M source old field,
    Included Loc
      (extend_capability_after_write CT h M source old field Null_a) M.
Proof.
  intros CT h M source old field member
    [HinM | [target [D [runtime_fd [Hvalue Hrest]]]]].
  - exact HinM.
  - discriminate.
Qed.

Lemma active_rdm_colors_after_null_field_write :
  forall CT P Z M cutoff sGamma rGamma h lx old f sGamma',
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    sGamma' = sGamma ->
    runtime_getObj h lx = Some old ->
    active_rdm_component_colors_separated CT
      (update_field h lx f Null_a)
      (extend_capability_after_write CT h M lx old f Null_a) Z
      sGamma' rGamma.
Proof.
  intros CT P Z M cutoff sGamma rGamma h lx old f sGamma'
    [Hforward [Hcomponents Hactive]] -> Hobj.
  intros capability_root zone_root Hcaproot
    [capability [Hcapability Hcapconnected]] Hzoneroot
    [protected [Hprotected Hzoneconnected]].
  apply (Hactive capability_root zone_root Hcaproot).
  - exists capability; split;
    [exact (null_capability_extension_is_old CT h M lx old f capability
      Hcapability)|];
    eapply mutable_connected_after_null_field_update_is_old; eauto.
  - exact Hzoneroot.
  - exists protected; split; [exact Hprotected|];
    eapply mutable_connected_after_null_field_update_is_old; eauto.
Qed.

Lemma old_active_capability_blocks_new_zone_bridge :
  forall CT P Z M cutoff h sGamma rGamma x y lx ly Tx Ty Ctarget
    capability_root zone_root,
    wf_r_config CT sGamma rGamma h ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    static_getType sGamma x = Some Tx ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma x = Some (Iot lx) ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    qualified_type_subtype CT Ty
      (Build_qualified_type
        (vpa_mutability_stype_fld_safe_ro (sqtype Tx) RDM_f) Ctarget) ->
    typed_root RDM sGamma rGamma capability_root ->
    component_touches CT h M capability_root ->
    typed_root RDM sGamma rGamma zone_root ->
    ((mutable_connected CT h zone_root lx /\
        component_touches CT h Z ly) \/
     (mutable_connected CT h zone_root ly /\
        component_touches CT h Z lx)) ->
    False.
Proof.
  intros CT P Z M cutoff h sGamma rGamma x y lx ly Tx Ty Ctarget
    capability_root zone_root Hwf
    [[Hcontains [Henv [Hconfined [Hclosed [Hruntime
      [Hmutroots [Havoid Holdcolors]]]]]]]
      [Hcomponents Hactive]]
    Hgetx Hgety Hvalx Hvaly Hsub Hcaproot HcapM Hzoneroot Hbridge.
  destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwf)
    as [this [qcontext [Hthis [_ Hqcontext]]]].
  have Hwf_copy := Hwf.
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [_ [_ [_ Hcorr]]]]].
  have Hxdom := Hgetx. apply static_getType_dom in Hxdom.
  have Hydom := Hgety. apply static_getType_dom in Hydom.
  have Hxtyp := Hcorr this qcontext Hthis Hqcontext x Hxdom Tx Hgetx.
  have Hytyp := Hcorr this qcontext Hthis Hqcontext y Hydom Ty Hgety.
  rewrite Hvalx in Hxtyp. rewrite Hvaly in Hytyp.
  have Hxnotbot := typable_nonnull_not_bot CT rGamma h lx Tx qcontext Hxtyp.
  have Hynotbot := typable_nonnull_not_bot CT rGamma h ly Ty qcontext Hytyp.
  apply qualified_type_subtype_q_subtype in Hsub.
  destruct (sqtype Tx) eqn:Hqx.
  - destruct (sqtype Ty) eqn:Hqy; simpl in Hsub;
      try solve_q_subtype_wrong.
    + have HlxM : In Loc M lx.
      { apply Hmutroots. exists x, Tx. repeat split; assumption. }
      have HlyM : In Loc M ly.
      { apply Hmutroots. exists y, Ty. repeat split; assumption. }
      destruct Hbridge as [[Hzone_lx HlyZ] | [Hzone_ly HlxZ]].
      * eapply separated_components_cannot_touch_both with (root := ly); eauto.
        exists ly. split; [exact HlyM|apply mutable_connected_refl].
      * eapply separated_components_cannot_touch_both with (root := lx); eauto.
        exists lx. split; [exact HlxM|apply mutable_connected_refl].
    + exfalso. apply Hynotbot. reflexivity.
  - destruct (sqtype Ty) eqn:Hqy; simpl in Hsub;
      try solve_q_subtype_wrong.
    + destruct Hbridge as [[Hzone_lx HlyZ] | [Hzone_ly HlxZ]].
      * eapply active_capability_rdm_excludes_immutable_endpoint
          with (capability_root := capability_root) (other_root := zone_root)
            (endpoint := lx); eauto.
        exists x, Tx. repeat split; assumption.
      * eapply active_capability_rdm_excludes_immutable_endpoint
          with (capability_root := capability_root) (other_root := zone_root)
            (endpoint := ly); eauto.
        exists y, Ty. repeat split; assumption.
    + exfalso. apply Hynotbot. reflexivity.
  - destruct (sqtype Ty) eqn:Hqy; simpl in Hsub;
      try solve_q_subtype_wrong.
    + destruct Hbridge as [[Hzone_lx HlyZ] | [Hzone_ly HlxZ]].
      * eapply Hactive with (capability_root := capability_root)
          (zone_root := ly); eauto.
        exists y, Ty. repeat split; assumption.
      * eapply Hactive with (capability_root := capability_root)
          (zone_root := lx); eauto.
        exists x, Tx. repeat split; assumption.
    + exfalso. apply Hynotbot. reflexivity.
  - destruct (sqtype Ty) eqn:Hqy; simpl in Hsub;
      try solve_q_subtype_wrong; exfalso; apply Hynotbot; reflexivity.
  - destruct (sqtype Ty) eqn:Hqy; simpl in Hsub;
      try solve_q_subtype_wrong; exfalso; apply Hynotbot; reflexivity.
  - exfalso. apply Hxnotbot. reflexivity.
Qed.

Lemma new_capability_bridge_blocks_old_active_zone :
  forall CT P Z M cutoff h sGamma rGamma x y lx ly Tx Ty Ctarget
    capability_root zone_root,
    wf_r_config CT sGamma rGamma h ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    static_getType sGamma x = Some Tx ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma x = Some (Iot lx) ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    qualified_type_subtype CT Ty
      (Build_qualified_type
        (vpa_mutability_stype_fld_safe_ro (sqtype Tx) RDM_f) Ctarget) ->
    typed_root RDM sGamma rGamma capability_root ->
    typed_root RDM sGamma rGamma zone_root ->
    component_touches CT h Z zone_root ->
    ((mutable_connected CT h capability_root lx /\
        component_touches CT h M ly) \/
     (mutable_connected CT h capability_root ly /\
        component_touches CT h M lx)) ->
    False.
Proof.
  intros CT P Z M cutoff h sGamma rGamma x y lx ly Tx Ty Ctarget
    capability_root zone_root Hwf
    [[Hcontains [Henv [Hconfined [Hclosed [Hruntime
      [Hmutroots [Havoid Holdcolors]]]]]]]
      [Hcomponents Hactive]]
    Hgetx Hgety Hvalx Hvaly Hsub Hcaproot Hzoneroot HzoneZ Hbridge.
  destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwf)
    as [this [qcontext [Hthis [_ Hqcontext]]]].
  have Hwf_copy := Hwf.
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [_ [_ [_ Hcorr]]]]].
  have Hxdom := Hgetx. apply static_getType_dom in Hxdom.
  have Hydom := Hgety. apply static_getType_dom in Hydom.
  have Hxtyp := Hcorr this qcontext Hthis Hqcontext x Hxdom Tx Hgetx.
  have Hytyp := Hcorr this qcontext Hthis Hqcontext y Hydom Ty Hgety.
  rewrite Hvalx in Hxtyp. rewrite Hvaly in Hytyp.
  have Hxnotbot := typable_nonnull_not_bot CT rGamma h lx Tx qcontext Hxtyp.
  have Hynotbot := typable_nonnull_not_bot CT rGamma h ly Ty qcontext Hytyp.
  apply qualified_type_subtype_q_subtype in Hsub.
  destruct (sqtype Tx) eqn:Hqx.
  - destruct (sqtype Ty) eqn:Hqy; simpl in Hsub;
      try solve_q_subtype_wrong.
    + have HlxM : In Loc M lx.
      { apply Hmutroots. exists x, Tx. repeat split; assumption. }
      have HlyM : In Loc M ly.
      { apply Hmutroots. exists y, Ty. repeat split; assumption. }
      eapply Hactive with (capability_root := capability_root)
        (zone_root := zone_root); eauto.
      destruct Hbridge as [[Hcap_lx Hly_component] |
        [Hcap_ly Hlx_component]].
      * exists lx. split; [exact HlxM|exact Hcap_lx].
      * exists ly. split; [exact HlyM|exact Hcap_ly].
    + exfalso. apply Hynotbot. reflexivity.
  - destruct (sqtype Ty) eqn:Hqy; simpl in Hsub;
      try solve_q_subtype_wrong.
    + destruct Hbridge as [[Hcap_lx HlyM] | [Hcap_ly HlxM]].
      * eapply immutable_root_cannot_touch_capability_component
          with (root := ly).
        -- exact Hwf_copy.
        -- exact Hruntime.
        -- exists y, Ty. repeat split; assumption.
        -- exact HlyM.
      * eapply immutable_root_cannot_touch_capability_component
          with (root := lx).
        -- exact Hwf_copy.
        -- exact Hruntime.
        -- exists x, Tx. repeat split; assumption.
        -- exact HlxM.
    + exfalso. apply Hynotbot. reflexivity.
  - destruct (sqtype Ty) eqn:Hqy; simpl in Hsub;
      try solve_q_subtype_wrong.
    + destruct Hbridge as [[Hcap_lx HlyM] | [Hcap_ly HlxM]].
      * eapply Hactive with (capability_root := ly) (zone_root := zone_root).
        -- exists y, Ty. repeat split; assumption.
        -- exact HlyM.
        -- exact Hzoneroot.
        -- exact HzoneZ.
      * eapply Hactive with (capability_root := lx) (zone_root := zone_root).
        -- exists x, Tx. repeat split; assumption.
        -- exact HlxM.
        -- exact Hzoneroot.
        -- exact HzoneZ.
    + exfalso. apply Hynotbot. reflexivity.
  - destruct (sqtype Ty) eqn:Hqy; simpl in Hsub;
      try solve_q_subtype_wrong; exfalso; apply Hynotbot; reflexivity.
  - destruct (sqtype Ty) eqn:Hqy; simpl in Hsub;
      try solve_q_subtype_wrong; exfalso; apply Hynotbot; reflexivity.
  - exfalso. apply Hxnotbot. reflexivity.
Qed.

Lemma active_rdm_colors_after_typed_rdm_field_write :
  forall CT P Z M cutoff sGamma mt rGamma h x f y lx ly old oldvalue
    D runtime_fd sGamma',
    wf_r_config CT sGamma rGamma h ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SFldWrite x f y) sGamma' ->
    safe_readonly_method_type mt ->
    runtime_getVal rGamma x = Some (Iot lx) ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    runtime_getObj h lx = Some old ->
    getVal old.(fields_map) f = Some oldvalue ->
    base_subtype CT (rctype (rt_type old)) D ->
    sf_def_rel CT D f runtime_fd ->
    mutability (ftype runtime_fd) = RDM_f ->
    active_rdm_component_colors_separated CT
      (update_field h lx f (Iot ly))
      (extend_capability_after_write CT h M lx old f (Iot ly)) Z
      sGamma' rGamma.
Proof.
  intros CT P Z M cutoff sGamma mt rGamma h x f y lx ly old oldvalue
    D runtime_fd sGamma' Hwf Hstate Htyping Hscope Hvalx Hvaly Hobj
    Holdfield Hruntime_sub Hruntime_field Hruntime_rdm.
  assert (HsGamma : sGamma' = sGamma) by (inversion Htyping; reflexivity).
  subst sGamma'.
  destruct (typed_runtime_rdm_field_write_subtyping CT sGamma mt rGamma h
    x f y lx old D runtime_fd sGamma Hwf Htyping Hscope Hvalx Hobj
    Hruntime_sub Hruntime_field Hruntime_rdm) as
    [Tx [Ty [Hgetx [Hgety Hsub]]]].
  have Hcomponents := proj1 (proj2 Hstate).
  have Hactive := proj2 (proj2 Hstate).
  have Hcross := safe_rdm_write_component_colors_cannot_cross
    CT P Z M cutoff h sGamma rGamma x y lx ly Tx Ty
    (f_base_type (ftype runtime_fd)) Hwf Hstate Hgetx Hgety Hvalx Hvaly Hsub.
  intros capability_root zone_root Hcaproot Hcapability Hzoneroot Hzone.
  have Hcapability_old :=
    component_touch_extension_reduces_to_old_capability_set CT h M lx old
      oldvalue f (Iot ly) capability_root Hobj Holdfield Hcapability.
  destruct (component_touch_after_field_update_origin CT h lx old f
    (Iot ly) M capability_root Hobj Hcapability_old) as
    [Hcap_old | [written_cap [Hwritten_cap Hcap_bridge]]].
  - destruct (component_touch_after_field_update_origin CT h lx old f
      (Iot ly) Z zone_root Hobj Hzone) as
      [Hzone_old | [written_zone [Hwritten_zone Hzone_bridge]]].
    + exact (Hactive capability_root zone_root Hcaproot Hcap_old
        Hzoneroot Hzone_old).
    + injection Hwritten_zone as <-.
      eapply old_active_capability_blocks_new_zone_bridge
        with (x := x) (y := y) (lx := lx) (ly := ly)
          (Tx := Tx) (Ty := Ty)
          (Ctarget := f_base_type (ftype runtime_fd)).
      * exact Hwf.
      * exact Hstate.
      * exact Hgetx.
      * exact Hgety.
      * exact Hvalx.
      * exact Hvaly.
      * exact Hsub.
      * exact Hcaproot.
      * exact Hcap_old.
      * exact Hzoneroot.
      * exact Hzone_bridge.
  - injection Hwritten_cap as <-.
    destruct (component_touch_after_field_update_origin CT h lx old f
      (Iot ly) Z zone_root Hobj Hzone) as
      [Hzone_old | [written_zone [Hwritten_zone Hzone_bridge]]].
    + eapply new_capability_bridge_blocks_old_active_zone
        with (x := x) (y := y) (lx := lx) (ly := ly)
          (Tx := Tx) (Ty := Ty)
          (Ctarget := f_base_type (ftype runtime_fd)).
      * exact Hwf.
      * exact Hstate.
      * exact Hgetx.
      * exact Hgety.
      * exact Hvalx.
      * exact Hvaly.
      * exact Hsub.
      * exact Hcaproot.
      * exact Hzoneroot.
      * exact Hzone_old.
      * exact Hcap_bridge.
    + injection Hwritten_zone as <-.
      destruct Hcap_bridge as [[Hcap_lx HlyM] | [Hcap_ly HlxM]];
        destruct Hzone_bridge as [[Hzone_lx HlyZ] | [Hzone_ly HlxZ]].
      * eapply separated_components_cannot_touch_both
          with (root := ly); eauto.
      * exact (proj2 Hcross HlxZ HlyM).
      * exact (proj1 Hcross HlxM HlyZ).
      * eapply separated_components_cannot_touch_both
          with (root := lx); eauto.
Qed.

Lemma active_rdm_colors_after_typed_field_write :
  forall CT P Z M cutoff sGamma mt rGamma h x f y lx old oldvalue value
    sGamma',
    wf_r_config CT sGamma rGamma h ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SFldWrite x f y) sGamma' ->
    safe_readonly_method_type mt ->
    runtime_getVal rGamma x = Some (Iot lx) ->
    runtime_getVal rGamma y = Some value ->
    runtime_getObj h lx = Some old ->
    getVal old.(fields_map) f = Some oldvalue ->
    active_rdm_component_colors_separated CT
      (update_field h lx f value)
      (extend_capability_after_write CT h M lx old f value) Z
      sGamma' rGamma.
Proof.
  intros CT P Z M cutoff sGamma mt rGamma h x f y lx old oldvalue value
    sGamma' Hwf Hstate Htyping Hscope Hvalx Hvaly Hobj Holdfield.
  destruct value as [|ly].
  - eapply active_rdm_colors_after_null_field_write.
    + exact Hstate.
    + inversion Htyping; reflexivity.
    + exact Hobj.
  - destruct (typed_field_write_runtime_field_agreement CT sGamma mt rGamma
      h x f y lx old sGamma' Hwf Htyping Hvalx Hobj) as
      [Tx [fieldT [Hgetx [Hfield Hbase]]]].
    destruct (mutability (ftype fieldT)) eqn:Hfieldq.
    + eapply active_rdm_colors_after_typed_non_rdm_field_write
        with (Tx := Tx) (fieldT := fieldT); eauto.
    + eapply active_rdm_colors_after_typed_non_rdm_field_write
        with (Tx := Tx) (fieldT := fieldT); eauto.
    + eapply active_rdm_colors_after_typed_rdm_field_write
        with (D := sctype Tx) (runtime_fd := fieldT); eauto.
    + eapply active_rdm_colors_after_typed_non_rdm_field_write
        with (Tx := Tx) (fieldT := fieldT); eauto.
Qed.

Lemma active_component_colors_imply_rdm_separation :
  forall CT h M Z sGamma rGamma,
    active_rdm_component_colors_separated CT h M Z sGamma rGamma ->
    rdm_capability_zone_separated CT h M Z sGamma rGamma.
Proof.
  intros CT h M Z sGamma rGamma Hactive capability_root zone_root
    [Hcaproot [capability [Hcapreach Hcapability]]]
    [Hzoneroot [protected [Hzonereach Hprotected]]].
  eapply Hactive with (capability_root := capability_root)
    (zone_root := zone_root).
  - exact Hcaproot.
  - exists capability. split; [exact Hcapability|].
    eapply mutable_reachable_connected; exact Hcapreach.
  - exact Hzoneroot.
  - exists protected. split; [exact Hprotected|].
    eapply mutable_reachable_connected; exact Hzonereach.
Qed.

Lemma component_forward_history_after_field_write :
  forall CT P Z M cutoff sGamma mt rGamma h x f y rGamma' h' sGamma',
    wf_r_config CT sGamma rGamma h ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SFldWrite x f y) sGamma' ->
    safe_readonly_method_type mt ->
    eval_stmt OK P CT rGamma h (SFldWrite x f y) OK P rGamma' h' ->
    exists M',
      Included Loc M M' /\
      component_forward_history_state CT P Z M' cutoff sGamma' rGamma' h'.
Proof.
  intros CT P Z M cutoff sGamma mt rGamma h x f y rGamma' h' sGamma'
    Hwf Hstate Htyping Hscope Heval.
  assert (HrGamma : rGamma' = rGamma) by (inversion Heval; reflexivity).
  subst rGamma'.
  have Hwf' := preservation_fldwrite_ok P CT sGamma mt rGamma h x f y h'
    sGamma' Hwf Htyping Heval.
  inversion Heval; subst.
  exists (extend_capability_after_write CT h M loc_x o f val_y).
  split; [apply capability_extension_contains_old|].
  assert (HsGamma : sGamma' = sGamma) by (inversion Htyping; reflexivity).
  subst sGamma'.
  have Hcomponents' := component_colors_after_typed_field_write_extension
    CT P Z M cutoff sGamma mt rGamma h x f y loc_x o vf val_y sGamma
    Hwf Hstate Htyping Hscope Hval_x Hval_y Hobj Hfield.
  have Hactive' := active_rdm_colors_after_typed_field_write
    CT P Z M cutoff sGamma mt rGamma h x f y loc_x o vf val_y sGamma
    Hwf Hstate Htyping Hscope Hval_x Hval_y Hobj Hfield.
  have Havoid' := capability_extension_after_typed_write_avoids_zone
    CT P Z M cutoff sGamma mt rGamma h x f y loc_x o vf val_y sGamma
    Hwf Hstate Htyping Hscope Hval_x Hval_y Hobj Hfield.
  destruct Hstate as
    [[Hcontains [Henv [[Hconfenv Hconfheap] [Hclosed [Hruntime
      [Hmutroots [Havoid Holdcolors]]]]]]]
      [Hcomponents Hactive]].
  have Hwf_old := Hwf.
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [Hwfheap _]].
  unfold wf_r_config in Hwf'.
  destruct Hwf' as [_ [Hwfheap' _]].
  have Hclosed' := capability_extension_closed_after_write CT h M loc_x o f
    val_y Hobj Hclosed.
  have Hruntime' := capability_extension_runtime_mut_after_write CT h M loc_x
    o f vf val_y Hwfheap Hwfheap' Hobj Hfield Hruntime.
  have Hcolors' := active_component_colors_imply_rdm_separation CT
    (update_field h loc_x f val_y)
    (extend_capability_after_write CT h M loc_x o f val_y) Z
    sGamma rGamma Hactive'.
  split.
  - refine (conj Hcontains (conj Henv (conj _ (conj Hclosed'
      (conj Hruntime' (conj _ (conj Havoid' Hcolors'))))))).
    + split; [exact Hconfenv|].
      intros source target Hsource Hedge.
      destruct (raw_edge_after_update h loc_x o f val_y source target Hobj Hedge)
        as [Holdedge | [-> Hnewvalue]].
      * eapply Hconfheap; eauto.
      * rewrite Hnewvalue in Hval_y. eapply Hconfenv; eauto.
    + intros root Hroot. apply capability_extension_contains_old.
      apply Hmutroots. exact Hroot.
  - split; assumption.
Qed.

Lemma fresh_attachment_has_creation_root :
  forall CT sGamma mt rGamma h x qc C args sGamma' vals qruntime root,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    fresh_component_attachment CT h
      (mkObj (mkruntime_type qruntime C) vals) root ->
    root = dom h \/
    exists target,
      typed_root (qc2q qc) sGamma rGamma target /\
      mutable_connected CT h target root.
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' vals qruntime root
    Hwf Htyping Hvals [Hfresh | [field [D [fdef [target
      [Hfield [Hsub [Hfd [Hrdm Hconnected]]]]]]]]].
  - left. exact Hfresh.
  - right. exists target. split; [|exact Hconnected].
    assert (HfdC : sf_def_rel CT C field fdef).
    { eapply field_inheritance_subtyping; eauto. }
    eapply new_creation_rdm_field_target_has_creation_root; eauto.
Qed.

Lemma component_colors_after_new_existing_sets :
  forall CT P Z M cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qruntime,
    wf_r_config CT sGamma rGamma h ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    ~ In Loc Z (dom h) ->
    component_colors_separated CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) M Z.
Proof.
  intros CT P Z M cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qruntime Hwf Hstate Htyping Hvals HfreshZ capability protected
    Hcapability Hprotected Hconnected.
  destruct Hstate as
    [[Hcontains [Henv [Hconfined [Hclosed [Hruntime
      [Hmutroots [Havoid Holdcolors]]]]]]]
      [Hcomponents Hactive]].
  have Hwfheap : wf_heap CT h.
  { unfold wf_r_config in Hwf. tauto. }
  destruct (mutable_connected_after_append_components CT h
    (mkObj (mkruntime_type qruntime C) vals) capability protected Hwfheap
    Hconnected) as [Hold | [Hcapattach Hzoneattach]].
  - exact (Hcomponents capability protected Hcapability Hprotected Hold).
  - destruct (fresh_attachment_has_creation_root CT sGamma mt rGamma h x qc
      C args sGamma' vals qruntime capability Hwf Htyping Hvals Hcapattach)
      as [Hcapfresh | [caproot [Hcaproot Hcapconnected]]].
    + subst capability. exfalso.
      eapply old_mutable_member_not_fresh; eauto.
    + destruct (fresh_attachment_has_creation_root CT sGamma mt rGamma h x
        qc C args sGamma' vals qruntime protected Hwf Htyping Hvals
        Hzoneattach) as [Hzonefresh | [zoneroot [Hzoneroot Hzoneconnected]]].
      * subst protected. contradiction.
      * destruct qc.
        -- simpl in Hcaproot, Hzoneroot.
           apply (Hcomponents zoneroot protected).
           ++ apply Hmutroots. exact Hzoneroot.
           ++ exact Hprotected.
           ++ exact Hzoneconnected.
        -- simpl in Hcaproot, Hzoneroot.
           eapply immutable_root_cannot_touch_capability_component
             with (root := caproot).
           ++ exact Hwf.
           ++ exact Hruntime.
           ++ exact Hcaproot.
           ++ exists capability. split; [exact Hcapability|].
              exact Hcapconnected.
        -- simpl in Hcaproot, Hzoneroot.
           eapply Hactive with (capability_root := caproot)
             (zone_root := zoneroot).
           ++ exact Hcaproot.
           ++ exists capability. split; assumption.
           ++ exact Hzoneroot.
           ++ exists protected. split; assumption.
Qed.

Lemma component_colors_after_new_extension :
  forall CT P Z M cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qruntime,
    wf_r_config CT sGamma rGamma h ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    ~ In Loc Z (dom h) ->
    component_colors_separated CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (extend_capability_after_new M qc (dom h)) Z.
Proof.
  intros CT P Z M cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qruntime Hwf Hstate Htyping Hvals HfreshZ capability protected
    [Hcapability | [Hmutcreation Hcapfresh]] Hprotected Hconnected.
  - have Hexisting := component_colors_after_new_existing_sets CT P Z M
      cutoff sGamma mt rGamma h x qc C args sGamma' vals qruntime Hwf
      Hstate Htyping Hvals HfreshZ.
    exact (Hexisting capability protected Hcapability Hprotected Hconnected).
  - subst qc capability. simpl in *.
    have Hwfheap : wf_heap CT h.
    { unfold wf_r_config in Hwf. tauto. }
    destruct (mutable_connected_after_append_components CT h
      (mkObj (mkruntime_type qruntime C) vals) (dom h) protected Hwfheap
      Hconnected) as [Hold | [Hfreshattach Hzoneattach]].
    + have Hprotectedfresh := old_component_reaching_fresh_is_fresh CT h
        protected Hwfheap (mutable_connected_sym CT h (dom h) protected Hold).
      subst protected. contradiction.
    + destruct (fresh_attachment_has_creation_root CT sGamma mt rGamma h x
        Mut_c C args sGamma' vals qruntime protected Hwf Htyping Hvals
        Hzoneattach) as [Hzonefresh | [zoneroot [Hzoneroot Hzoneconnected]]].
      * subst protected. contradiction.
      * simpl in Hzoneroot.
        destruct Hstate as
          [[Hcontains [Henv [Hconfined [Hclosed [Hruntime
            [Hmutroots [Havoid Holdcolors]]]]]]]
            [Hcomponents Hactive]].
        apply (Hcomponents zoneroot protected).
        -- apply Hmutroots. exact Hzoneroot.
        -- exact Hprotected.
        -- exact Hzoneconnected.
Qed.

Lemma capability_new_extension_closed :
  forall CT P Z M cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qruntime,
    wf_r_config CT sGamma rGamma h ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    mutable_heap_closed CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (extend_capability_after_new M qc (dom h)).
Proof.
  intros CT P Z M cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qruntime Hwf Hstate Htyping Hvals source target
    [HsourceM | [Hmutcreation Hsourcefresh]] Hedge.
  - destruct Hstate as
      [[Hcontains [Henv [Hconfined [Hclosed [Hruntime
        [Hmutroots [Havoid Holdcolors]]]]]]] Hcolors].
    destruct (mutable_edge_after_append CT h
      (mkObj (mkruntime_type qruntime C) vals) source target Hedge)
      as [Holdedge | [Hfresh Hnewedge]].
    + left. eapply Hclosed; eauto.
    + subst source. exfalso. eapply old_mutable_member_not_fresh; eauto.
  - subst qc source.
    destruct Hstate as
      [[Hcontains [Henv [Hconfined [Hclosed [Hruntime
        [Hmutroots [Havoid Holdcolors]]]]]]] Hcolors].
    destruct (mutable_edge_after_append CT h
      (mkObj (mkruntime_type qruntime C) vals) (dom h) target Hedge)
      as [Holdedge | [Hfresh [field [D [fdef [Hfield [Hsub
        [Hfd Hrdm]]]]]]]].
    + inversion Holdedge as [? ? old oldfield oldD oldfdef Hobj Hvalue
        Holdsub Holdfd Holdrdm]; subst.
      apply runtime_getObj_dom in Hobj. lia.
    + left. apply Hmutroots.
      assert (HfdC : sf_def_rel CT C field fdef).
      { eapply field_inheritance_subtyping; eauto. }
      exact (new_creation_rdm_field_target_has_creation_root CT sGamma mt
        rGamma h x Mut_c C args sGamma' vals field fdef target Hwf Htyping
        Hvals Hfield HfdC Hrdm).
Qed.

Lemma capability_new_extension_runtime_mutable :
  forall h M rGamma qc C vals qthis qruntime this,
    mutable_members_runtime_mut h M ->
    runtime_getVal rGamma 0 = Some (Iot this) ->
    r_muttype h this = Some qthis ->
    vpa_mutability_object_creation qthis qc = qruntime ->
    mutable_members_runtime_mut
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (extend_capability_after_new M qc (dom h)).
Proof.
  intros h M rGamma qc C vals qthis qruntime this Hruntime Hthis Hqthis
    Hadapt location [Hold | [Hmutcreation Hfresh]].
  - specialize (Hruntime location Hold).
    unfold r_muttype, r_type in *.
    destruct (runtime_getObj h location) as [old|] eqn:Hobj;
      try discriminate.
    have Hlocation := Hobj. apply runtime_getObj_dom in Hlocation.
    erewrite runtime_getObj_last2; [|exact Hlocation].
    rewrite Hobj. exact Hruntime.
  - subst qc location. unfold r_muttype, r_type.
    rewrite runtime_getObj_last. simpl.
    destruct qthis; simpl in Hadapt; subst qruntime; reflexivity.
Qed.

Lemma env_mut_roots_after_new_in_extension :
  forall CT P Z M cutoff sGamma mt rGamma h x qc C args sGamma',
    wf_r_config CT sGamma rGamma h ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    env_mut_roots_in (extend_capability_after_new M qc (dom h)) sGamma'
      (update_r_env_value rGamma x (Iot (dom h))).
Proof.
  intros CT P Z M cutoff sGamma mt rGamma h x qc C args sGamma' Hwf
    [[Hcontains [Henv [Hconfined [Hclosed [Hruntime
      [Hmutroots [Havoid Holdcolors]]]]]]] Hcolors]
    Htyping root Hroot.
  destruct (new_typed_root_origin CT sGamma mt rGamma h x qc C args
    sGamma' Mut root Hwf Htyping Hroot) as
    [Holdroot | [Hfresh [Tx [Hgetx Hmut]]]].
  - left. apply Hmutroots. exact Holdroot.
  - right. split; [|exact Hfresh].
    have Hcreation := new_mut_result_requires_mut_creation CT sGamma mt x qc
      C args sGamma' Tx Htyping.
    assert (HsGamma : sGamma' = sGamma) by (inversion Htyping; reflexivity).
    specialize (Hcreation (ltac:(rewrite HsGamma; exact Hgetx)) Hmut).
    destruct qc; simpl in Hcreation; try discriminate; reflexivity.
Qed.

Lemma capability_new_extension_avoids_zone :
  forall M Z qc fresh,
    (forall location, In Loc M location -> ~ In Loc Z location) ->
    ~ In Loc Z fresh ->
    forall location,
      In Loc (extend_capability_after_new M qc fresh) location ->
      ~ In Loc Z location.
Proof.
  intros M Z qc fresh Havoid Hfresh location
    [Hold | [Hmutcreation ->]].
  - apply Havoid. exact Hold.
  - exact Hfresh.
Qed.

Lemma component_touch_after_new_old_set_origin :
  forall CT sGamma mt rGamma h x qc C args sGamma' vals qruntime S root,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    ~ In Loc S (dom h) ->
    component_touches CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) S root ->
    root = dom h \/
    component_touches CT h S root \/
    exists root_target member_target,
      typed_root (qc2q qc) sGamma rGamma root_target /\
      typed_root (qc2q qc) sGamma rGamma member_target /\
      mutable_connected CT h root_target root /\
      component_touches CT h S member_target.
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' vals qruntime S root
    Hwf Htyping Hvals HfreshS [member [Hmember Hconnected]].
  have Hwfheap : wf_heap CT h.
  { unfold wf_r_config in Hwf. tauto. }
  destruct (mutable_connected_after_append_components CT h
    (mkObj (mkruntime_type qruntime C) vals) root member Hwfheap Hconnected)
    as [Hold | [Hrootattach Hmemberattach]].
  - right. left. exists member. split; assumption.
  - destruct (fresh_attachment_has_creation_root CT sGamma mt rGamma h x qc
      C args sGamma' vals qruntime root Hwf Htyping Hvals Hrootattach)
      as [Hrootfresh | [root_target [Hroot_target Hrootconnected]]].
    + left. exact Hrootfresh.
    + destruct (fresh_attachment_has_creation_root CT sGamma mt rGamma h x
        qc C args sGamma' vals qruntime member Hwf Htyping Hvals
        Hmemberattach) as
        [Hmemberfresh | [member_target [Hmember_target Hmemberconnected]]].
      * subst member. contradiction.
      * right. right. exists root_target, member_target. repeat split;
          try assumption.
        exists member. split; assumption.
Qed.

Lemma new_active_rdm_root_origin :
  forall CT sGamma mt rGamma h x qc C args sGamma' root,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    typed_root RDM sGamma'
      (update_r_env_value rGamma x (Iot (dom h))) root ->
    typed_root RDM sGamma rGamma root \/
    (root = dom h /\ qc = RDM_c).
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' root Hwf Htyping
    Hroot.
  destruct (new_typed_root_origin CT sGamma mt rGamma h x qc C args
    sGamma' RDM root Hwf Htyping Hroot) as
    [Hold | [Hfresh [Tx [Hgetx Hrdm]]]].
  - left. exact Hold.
  - right. split; [exact Hfresh|].
    have Hcreation := new_rdm_result_requires_rdm_creation CT sGamma mt x qc
      C args sGamma' Tx Htyping.
    assert (HsGamma : sGamma' = sGamma) by (inversion Htyping; reflexivity).
    specialize (Hcreation (ltac:(rewrite HsGamma; exact Hgetx)) Hrdm).
    destruct qc; simpl in Hcreation; try discriminate; reflexivity.
Qed.

Lemma fresh_component_touches_old_set_has_creation_root :
  forall CT sGamma mt rGamma h x qc C args sGamma' vals qruntime S,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    ~ In Loc S (dom h) ->
    component_touches CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) S (dom h) ->
    exists target,
      typed_root (qc2q qc) sGamma rGamma target /\
      component_touches CT h S target.
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' vals qruntime S Hwf
    Htyping Hvals HfreshS [member [Hmember Hconnected]].
  have Hwfheap : wf_heap CT h.
  { unfold wf_r_config in Hwf. tauto. }
  destruct (mutable_connected_after_append_components CT h
    (mkObj (mkruntime_type qruntime C) vals) (dom h) member Hwfheap
    Hconnected) as [Hold | [Hfreshattach Hmemberattach]].
  - have Hmemberfresh := old_component_reaching_fresh_is_fresh CT h member
      Hwfheap (mutable_connected_sym CT h (dom h) member Hold).
    subst member. contradiction.
  - destruct (fresh_attachment_has_creation_root CT sGamma mt rGamma h x qc
      C args sGamma' vals qruntime member Hwf Htyping Hvals Hmemberattach)
      as [Hmemberfresh | [target [Htarget Htarget_member]]].
    + subst member. contradiction.
    + exists target. split; [exact Htarget|].
      exists member. split; assumption.
Qed.

Lemma active_rdm_capability_after_new_has_old_origin :
  forall CT P Z M cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qruntime root,
    wf_r_config CT sGamma rGamma h ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    typed_root RDM sGamma'
      (update_r_env_value rGamma x (Iot (dom h))) root ->
    component_touches CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (extend_capability_after_new M qc (dom h)) root ->
    exists old_root,
      typed_root RDM sGamma rGamma old_root /\
      component_touches CT h M old_root.
Proof.
  intros CT P Z M cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qruntime root Hwf Hstate Htyping Hvals Hroot Htouch.
  have Hwfheap : wf_heap CT h.
  { unfold wf_r_config in Hwf. tauto. }
  have HfreshM : ~ In Loc M (dom h).
  { destruct Hstate as
      [[Hcontains [Henv [Hconfined [Hclosed [Hruntime Hrest]]]]] Hcolors].
    eapply old_mutable_member_not_fresh; exact Hruntime. }
  destruct Htouch as
    [member [[HmemberM | [Hmutcreation Hmemberfresh]] Hconnected]].
  - have Htouch : component_touches CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) M root.
    { exists member. split; assumption. }
    destruct (component_touch_after_new_old_set_origin CT sGamma mt rGamma h
      x qc C args sGamma' vals qruntime M root Hwf Htyping Hvals HfreshM
      Htouch) as
      [Hrootfresh | [Holdtouch | [root_target [member_target
        [Hroot_target [Hmember_target [Htarget_root Hmember_touch]]]]]]].
    + destruct (new_active_rdm_root_origin CT sGamma mt rGamma h x qc C args
        sGamma' root Hwf Htyping Hroot) as [Holdroot | [Hfresh Hqcrdm]].
      * destruct Holdroot as [z [T [Htype [Hval Hrdm]]]].
        have Hdom := wf_config_value_dom CT sGamma rGamma h z root Hwf Hval.
        subst root. lia.
      * subst root qc. simpl in *.
        destruct (fresh_component_touches_old_set_has_creation_root CT sGamma
          mt rGamma h x RDM_c C args sGamma' vals qruntime M Hwf Htyping
          Hvals HfreshM Htouch) as [target [Htarget HtargetM]].
        exists target. split; assumption.
    + destruct (new_active_rdm_root_origin CT sGamma mt rGamma h x qc C args
        sGamma' root Hwf Htyping Hroot) as [Holdroot | [Hfresh Hqcrdm]].
      * exists root. split; assumption.
      * subst root.
        destruct Holdtouch as [old_member [Holdmember Holdconnected]].
        have Hmemberfresh := old_component_reaching_fresh_is_fresh CT h
          old_member Hwfheap
          (mutable_connected_sym CT h (dom h) old_member Holdconnected).
        subst old_member. contradiction.
    + destruct Hstate as
        [[Hcontains [Henv [Hconfined [Hclosed [Hruntime
          [Hmutroots [Havoid Holdcolors]]]]]]]
          [Hcomponents Hactive]].
      destruct qc.
      * simpl in Hroot_target, Hmember_target.
        destruct (new_active_rdm_root_origin CT sGamma mt rGamma h x Mut_c C
          args sGamma' root Hwf Htyping Hroot) as
          [Holdroot | [Hfresh Hbad]]; [|discriminate].
        exists root. split; [exact Holdroot|].
        exists root_target. split.
        -- apply Hmutroots. exact Hroot_target.
        -- eapply mutable_connected_sym; exact Htarget_root.
      * simpl in Hroot_target, Hmember_target.
        exfalso. eapply immutable_root_cannot_touch_capability_component
          with (root := member_target).
        -- exact Hwf.
        -- exact Hruntime.
        -- exact Hmember_target.
        -- exact Hmember_touch.
      * simpl in Hroot_target, Hmember_target.
        exists member_target. split; assumption.
  - subst qc member. simpl in *.
    destruct (new_active_rdm_root_origin CT sGamma mt rGamma h x Mut_c C
      args sGamma' root Hwf Htyping Hroot) as
      [Holdroot | [Hrootfresh Hbad]]; [|discriminate].
    destruct (mutable_connected_after_append_components CT h
      (mkObj (mkruntime_type qruntime C) vals) root (dom h) Hwfheap
      Hconnected) as [Holdconnected | [Hrootattach Hfreshattach]].
    + have Hrootfresh := old_component_reaching_fresh_is_fresh CT h root
        Hwfheap Holdconnected.
      destruct Holdroot as [z [T [Htype [Hval Hrdm]]]].
      have Hdom := wf_config_value_dom CT sGamma rGamma h z root Hwf Hval.
      subst root. lia.
    + destruct (fresh_attachment_has_creation_root CT sGamma mt rGamma h x
        Mut_c C args sGamma' vals qruntime root Hwf Htyping Hvals Hrootattach)
        as [Hrootfresh | [target [Htarget Htarget_root]]].
      * destruct Holdroot as [z [T [Htype [Hval Hrdm]]]].
        have Hdom := wf_config_value_dom CT sGamma rGamma h z root Hwf Hval.
        subst root. lia.
      * destruct Hstate as
          [[Hcontains [Henv [Hconfined [Hclosed [Hruntime
            [Hmutroots [Havoid Holdcolors]]]]]]] Hcolors].
        simpl in Htarget.
        exists root. split; [exact Holdroot|].
        exists target. split.
        -- apply Hmutroots. exact Htarget.
        -- eapply mutable_connected_sym; exact Htarget_root.
Qed.

Lemma active_rdm_zone_after_new_has_old_origin :
  forall CT P Z M cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qruntime capability_root zone_root,
    wf_r_config CT sGamma rGamma h ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    ~ In Loc Z (dom h) ->
    typed_root RDM sGamma rGamma capability_root ->
    component_touches CT h M capability_root ->
    typed_root RDM sGamma'
      (update_r_env_value rGamma x (Iot (dom h))) zone_root ->
    component_touches CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) Z zone_root ->
    exists old_zone_root,
      typed_root RDM sGamma rGamma old_zone_root /\
      component_touches CT h Z old_zone_root.
Proof.
  intros CT P Z M cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qruntime capability_root zone_root Hwf Hstate Htyping Hvals HfreshZ
    Hcaproot Hcapability Hzoneroot Hzone.
  have Hwfheap : wf_heap CT h.
  { unfold wf_r_config in Hwf. tauto. }
  destruct (component_touch_after_new_old_set_origin CT sGamma mt rGamma h
    x qc C args sGamma' vals qruntime Z zone_root Hwf Htyping Hvals
    HfreshZ Hzone) as
    [Hzonefresh | [Holdzone | [root_target [member_target
      [Hroot_target [Hmember_target [Htarget_zone Hmember_zone]]]]]]].
  - destruct (new_active_rdm_root_origin CT sGamma mt rGamma h x qc C args
      sGamma' zone_root Hwf Htyping Hzoneroot) as
      [Holdroot | [Hfresh Hqcrdm]].
    + destruct Holdroot as [z [T [Htype [Hval Hrdm]]]].
      have Hdom := wf_config_value_dom CT sGamma rGamma h z zone_root Hwf Hval.
      subst zone_root. lia.
    + subst zone_root qc. simpl in *.
      destruct (fresh_component_touches_old_set_has_creation_root CT sGamma
        mt rGamma h x RDM_c C args sGamma' vals qruntime Z Hwf Htyping
        Hvals HfreshZ Hzone) as [target [Htarget HtargetZ]].
      exists target. split; assumption.
  - destruct (new_active_rdm_root_origin CT sGamma mt rGamma h x qc C args
      sGamma' zone_root Hwf Htyping Hzoneroot) as
      [Holdroot | [Hfresh Hqcrdm]].
    + exists zone_root. split; assumption.
    + subst zone_root.
      destruct Holdzone as [member [Hmember Hmember_fresh]].
      have Hmemberfresh := old_component_reaching_fresh_is_fresh CT h member
        Hwfheap (mutable_connected_sym CT h (dom h) member Hmember_fresh).
      subst member. contradiction.
  - destruct Hstate as
      [[Hcontains [Henv [Hconfined [Hclosed [Hruntime
        [Hmutroots [Havoid Holdcolors]]]]]]]
        [Hcomponents Hactive]].
    destruct qc.
    + simpl in Hroot_target, Hmember_target.
      exfalso. eapply separated_components_cannot_touch_both
        with (root := member_target).
      * exact Hcomponents.
      * exists member_target. split.
        -- apply Hmutroots. exact Hmember_target.
        -- apply mutable_connected_refl.
      * exact Hmember_zone.
    + simpl in Hroot_target, Hmember_target.
      destruct (new_active_rdm_root_origin CT sGamma mt rGamma h x Imm_c C
        args sGamma' zone_root Hwf Htyping Hzoneroot) as
        [Holdzone | [Hfresh Hbad]]; [|discriminate].
      exfalso.
      eapply active_capability_rdm_excludes_immutable_endpoint
        with (capability_root := capability_root) (other_root := zone_root)
          (endpoint := root_target).
      * exact Hwf.
      * exact Hruntime.
      * exact Hcaproot.
      * exact Hcapability.
      * exact Holdzone.
      * eapply mutable_connected_sym; exact Htarget_zone.
      * exact Hroot_target.
    + simpl in Hroot_target, Hmember_target.
      exists member_target. split; assumption.
Qed.

Lemma active_rdm_colors_after_new :
  forall CT P Z M cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qruntime,
    wf_r_config CT sGamma rGamma h ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    ~ In Loc Z (dom h) ->
    active_rdm_component_colors_separated CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (extend_capability_after_new M qc (dom h)) Z sGamma'
      (update_r_env_value rGamma x (Iot (dom h))).
Proof.
  intros CT P Z M cutoff sGamma mt rGamma h x qc C args sGamma' vals
    qruntime Hwf Hstate Htyping Hvals HfreshZ capability_root zone_root
    Hcaproot Hcapability Hzoneroot Hzone.
  destruct (active_rdm_capability_after_new_has_old_origin CT P Z M cutoff
    sGamma mt rGamma h x qc C args sGamma' vals qruntime capability_root
    Hwf Hstate Htyping Hvals Hcaproot Hcapability) as
    [old_capability [Holdcaproot Holdcapability]].
  destruct (active_rdm_zone_after_new_has_old_origin CT P Z M cutoff sGamma
    mt rGamma h x qc C args sGamma' vals qruntime old_capability zone_root
    Hwf Hstate Htyping Hvals HfreshZ Holdcaproot Holdcapability Hzoneroot
    Hzone) as [old_zone [Holdzoneroot Holdzone]].
  exact (proj2 (proj2 Hstate) old_capability old_zone Holdcaproot
    Holdcapability Holdzoneroot Holdzone).
Qed.

Lemma component_forward_history_after_new :
  forall CT P Z M cutoff sGamma mt rGamma h x qc C args rGamma' h'
    sGamma',
    wf_r_config CT sGamma rGamma h ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    cutoff <= dom h ->
    ~ In Loc Z (dom h) ->
    eval_stmt OK P CT rGamma h (SNew x qc C args) OK P rGamma' h' ->
    exists M',
      Included Loc M M' /\
      component_forward_history_state CT P Z M' cutoff sGamma' rGamma' h'.
Proof.
  intros CT P Z M cutoff sGamma mt rGamma h x qc C args rGamma' h'
    sGamma' Hwf Hstate Htyping Hcutoff HfreshZ Heval.
  have Hwf' := preservation_new_ok P CT sGamma mt rGamma h x qc C args
    rGamma' h' sGamma' Hwf Htyping Heval.
  inversion Heval; subst.
  assert (HsGamma : sGamma' = sGamma) by (inversion Htyping; reflexivity).
  subst sGamma'.
  set (qruntime := vpa_mutability_object_creation qthisr qc).
  set (newobj := mkObj (mkruntime_type qruntime C) vals).
  assert (Hnewobj :
    mkObj (mkruntime_type (vpa_mutability_object_creation qthisr qc) C) vals
      = newobj) by reflexivity.
  assert (Hnewenv :
    set_vars rGamma (update x (Iot (dom h)) (vars rGamma)) =
      update_r_env_value rGamma x (Iot (dom h))) by
    (destruct rGamma; reflexivity).
  rewrite Hnewobj in Hwf'. rewrite Hnewenv in Hwf'.
  rewrite Hnewenv.
  exists (extend_capability_after_new M qc (dom h)).
  split; [apply capability_new_extension_contains_old|].
  have Hcomponents' := component_colors_after_new_extension CT P Z M cutoff
    sGamma mt rGamma h x qc C args sGamma vals qruntime Hwf Hstate Htyping
    Hargs HfreshZ.
  have Hactive' := active_rdm_colors_after_new CT P Z M cutoff sGamma mt
    rGamma h x qc C args sGamma vals qruntime Hwf Hstate Htyping Hargs
    HfreshZ.
  have Hclosed' := capability_new_extension_closed CT P Z M cutoff sGamma mt
    rGamma h x qc C args sGamma vals qruntime Hwf Hstate Htyping Hargs.
  destruct Hstate as
    [[Hcontains [Hzone [[Hconfenv Hconfheap] [Hclosed [Hruntime
      [Hmutroots [Havoid Holdcolors]]]]]]]
      [Hcomponents Hactive]].
  have Hruntime' := capability_new_extension_runtime_mutable h M rGamma qc C
    vals qthisr qruntime l1 Hruntime Hthis Hmut
      (ltac:(unfold qruntime; reflexivity)).
  have Hmutroots' := env_mut_roots_after_new_in_extension CT P Z M cutoff
    sGamma mt rGamma h x qc C args sGamma Hwf
    (conj (conj Hcontains (conj Hzone (conj (conj Hconfenv Hconfheap)
      (conj Hclosed (conj Hruntime (conj Hmutroots
        (conj Havoid Holdcolors))))))) (conj Hcomponents Hactive)) Htyping.
  have Havoid' := capability_new_extension_avoids_zone M Z qc (dom h)
    Havoid HfreshZ.
  have Hcolors' := active_component_colors_imply_rdm_separation CT
    (h ++ [newobj]) (extend_capability_after_new M qc (dom h)) Z
    sGamma (update_r_env_value rGamma x (Iot (dom h))) Hactive'.
  assert (Hxdom : x < dom (vars rGamma)).
  { inversion Htyping; subst. apply static_getType_dom in Hget_x.
    unfold wf_r_config in Hwf. destruct Hwf as [_ [_ [_ [_ [Hlength _]]]]].
    lia. }
  split.
  - refine (conj Hcontains (conj _ (conj _ (conj Hclosed'
      (conj Hruntime' (conj Hmutroots' (conj Havoid' Hcolors'))))))).
    + intros z l T Htype Hval HinZ.
      destruct (Nat.eq_dec z x) as [->|Hneq].
      * rewrite runtime_getVal_update_same in Hval; auto.
        injection Hval as <-. contradiction.
      * rewrite runtime_getVal_update_diff in Hval; auto.
        eapply Hzone; eauto.
    + split.
      * apply env_confined_update; [exact Hconfenv|].
        right. exact Hcutoff.
      * intros source target Hsource Hedge.
        destruct (raw_edge_after_append h newobj source target Hedge)
          as [Holdedge | [Hsourcefresh [field Hfield]]].
        -- eapply Hconfheap; eauto.
        -- subst source. unfold newobj in Hfield. simpl in Hfield.
           exact (env_confined_lookup_list P cutoff rGamma args vals Hconfenv
             Hargs field target Hfield).
  - split; assumption.
Qed.

Lemma forward_history_after_assignment :
  forall CT P Z M cutoff sGamma mt rGamma h x e old value,
    wf_r_config CT sGamma rGamma h ->
    forward_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SVarAss x e) sGamma ->
    safe_readonly_method_type mt ->
    runtime_getVal rGamma x = Some old ->
    eval_expr OK P CT rGamma h e value OK P rGamma h ->
    forward_history_state CT P Z M cutoff sGamma
      (update_r_env_value rGamma x value) h.
Proof.
  intros CT P Z M cutoff sGamma mt rGamma h x e old value Hwf Hstate
    Htyping Hscope Hx Heval.
  destruct Hstate as
    [Hcontains [Henv [[Hconfenv Hconfheap] [Hclosed [Hruntime
      [Hmutroots [Havoid Hcolors]]]]]]].
  inversion Htyping; subst.
  assert (Hxdom : x < dom (vars rGamma)).
  { apply static_getType_dom in Hget_x.
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [_ [_ [Hlength _]]]]]. lia. }
  refine (conj Hcontains (conj _ (conj _ (conj Hclosed
    (conj Hruntime (conj _ (conj Havoid _))))))).
  - intros z l Tz Htype_z Hval_z HinZ.
    destruct (Nat.eq_dec z x) as [->|Hneq].
    + rewrite Hget_x in Htype_z. injection Htype_z as <-.
      destruct value as [|result].
      * rewrite runtime_getVal_update_same in Hval_z; auto. discriminate.
      * rewrite runtime_getVal_update_same in Hval_z; auto.
        injection Hval_z as <-.
        have Hsafe_result := forward_expression_into_zone_has_safe_type
          P Z M cutoff CT sGamma mt rGamma h e result Te Hwf
          (conj Hcontains (conj Henv (conj (conj Hconfenv Hconfheap)
            (conj Hclosed (conj Hruntime
              (conj Hmutroots (conj Havoid Hcolors)))))))
          Heval Htype_e Hscope HinZ.
        eapply subtype_safe_implies_safe; eauto.
    + rewrite runtime_getVal_update_diff in Hval_z; auto.
      eapply Henv; eauto.
  - split; [|exact Hconfheap].
    apply env_confined_update; [exact Hconfenv|].
    destruct value as [|result]; [trivial|].
    eapply eval_expr_preserves_confinement; eauto. split; assumption.
  - intros root Hroot.
    destruct (assignment_mut_root_has_old_ancestor P CT sGamma mt rGamma h
      x e old value Hwf Htyping Hscope Hx Heval root Hroot)
      as [old_root [Holdroot Holdreach]].
    eapply mutable_heap_closed_reachable with (source := old_root).
    + exact Hclosed.
    + exact Holdreach.
    + apply Hmutroots. exact Holdroot.
  - intros capability_root zone_root
      [Hcaproot [cap_target [Hcapreach HcapM]]]
      [Hzoneroot [zone_target [Hzonereach HzoneZ]]].
    destruct (assignment_rdm_root_has_old_ancestor P CT sGamma mt rGamma h
      x e old value Hwf Htyping Hscope Hx Heval capability_root Hcaproot)
      as [old_cap [Holdcap Hcap_prefix]].
    destruct (assignment_rdm_root_has_old_ancestor P CT sGamma mt rGamma h
      x e old value Hwf Htyping Hscope Hx Heval zone_root Hzoneroot)
      as [old_zone [Holdzone Hzone_prefix]].
    eapply Hcolors with (capability_root := old_cap) (zone_root := old_zone).
    + split; [exact Holdcap|]. exists cap_target. split; [|exact HcapM].
      eapply mutable_reachable_trans; eauto.
    + split; [exact Holdzone|]. exists zone_target. split; [|exact HzoneZ].
      eapply mutable_reachable_trans; eauto.
Qed.

Lemma forward_history_after_local :
  forall CT P Z M cutoff sGamma mt rGamma h T x sGamma',
    wf_r_config CT sGamma rGamma h ->
    forward_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SLocal T x) sGamma' ->
    runtime_getVal rGamma x = None ->
    forward_history_state CT P Z M cutoff sGamma'
      (set_vars rGamma (vars rGamma ++ [Null_a])) h.
Proof.
  intros CT P Z M cutoff sGamma mt rGamma h T x sGamma' Hwf Hstate
    Htyping Hrnone.
  inversion Htyping; subst.
  destruct Hstate as
    [Hcontains [Henv [[Hconfenv Hconfheap] [Hclosed [Hruntime
      [Hmutroots [Havoid Hcolors]]]]]]].
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [_ [_ [Hlength _]]]]].
  refine (conj Hcontains (conj _ (conj _ (conj Hclosed
    (conj Hruntime (conj _ (conj Havoid _))))))).
  - intros y l Ty Htype Hval HinZ.
    destruct (appended_null_nonnull_lookup_is_old sGamma rGamma T y Ty l
      Hlength Htype Hval) as [Holdtype Holdval].
    eapply Henv; eauto.
  - split; [|exact Hconfheap].
    intros y l Hval.
    destruct (Nat.eq_dec y (dom (vars rGamma))) as [->|Hneq].
    + rewrite runtime_getVal_last in Hval. discriminate.
    + assert (Hy : y < dom (vars rGamma)).
      { apply runtime_getVal_dom in Hval. simpl in Hval.
        rewrite length_app in Hval. simpl in Hval. lia. }
      rewrite runtime_getVal_last2 in Hval; auto. eapply Hconfenv; eauto.
  - intros root [y [Ty [Htype [Hval Hmut]]]].
    destruct (appended_null_nonnull_lookup_is_old sGamma rGamma T y Ty root
      Hlength Htype Hval) as [Holdtype Holdval].
    apply Hmutroots. exists y, Ty. repeat split; assumption.
  - intros capability_root zone_root
      [[yc [Tc [Htypec [Hvalc Hrdmc]]]] [cap_target [Hcapreach HcapM]]]
      [[yz [Tz [Htypez [Hvalz Hrdmz]]]] [zone_target [Hzonereach HzoneZ]]].
    destruct (appended_null_nonnull_lookup_is_old sGamma rGamma T yc Tc
      capability_root Hlength Htypec Hvalc) as [Holdtypec Holdvalc].
    destruct (appended_null_nonnull_lookup_is_old sGamma rGamma T yz Tz
      zone_root Hlength Htypez Hvalz) as [Holdtypez Holdvalz].
    eapply Hcolors with (capability_root := capability_root)
      (zone_root := zone_root).
    + split.
      * exists yc, Tc. repeat split; assumption.
      * exists cap_target. split; assumption.
    + split.
      * exists yz, Tz. repeat split; assumption.
      * exists zone_target. split; assumption.
Qed.

Lemma component_forward_history_after_assignment :
  forall CT P Z M cutoff sGamma mt rGamma h x e old value,
    wf_r_config CT sGamma rGamma h ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SVarAss x e) sGamma ->
    safe_readonly_method_type mt ->
    runtime_getVal rGamma x = Some old ->
    eval_expr OK P CT rGamma h e value OK P rGamma h ->
    component_forward_history_state CT P Z M cutoff sGamma
      (update_r_env_value rGamma x value) h.
Proof.
  intros CT P Z M cutoff sGamma mt rGamma h x e old value Hwf
    [Hforward [Hcomponents Hactive]] Htyping Hscope Hx Heval.
  split.
  - eapply forward_history_after_assignment; eauto.
  - split; [exact Hcomponents|].
    intros capability_root zone_root Hcaproot Hcapcomponent
      Hzoneroot Hzonecomponent.
    destruct (assignment_rdm_root_has_old_ancestor P CT sGamma mt rGamma h
      x e old value Hwf Htyping Hscope Hx Heval capability_root Hcaproot)
      as [old_capability [Holdcapability Hcapability_prefix]].
    destruct (assignment_rdm_root_has_old_ancestor P CT sGamma mt rGamma h
      x e old value Hwf Htyping Hscope Hx Heval zone_root Hzoneroot)
      as [old_zone [Holdzone Hzone_prefix]].
    eapply Hactive with (capability_root := old_capability)
      (zone_root := old_zone).
    + exact Holdcapability.
    + destruct Hcapcomponent as [member [HinM Hcapability_member]].
      exists member. split; [exact HinM|].
      eapply mutable_connected_trans.
      * eapply mutable_reachable_connected; exact Hcapability_prefix.
      * exact Hcapability_member.
    + exact Holdzone.
    + destruct Hzonecomponent as [member [HinZ Hzone_member]].
      exists member. split; [exact HinZ|].
      eapply mutable_connected_trans.
      * eapply mutable_reachable_connected; exact Hzone_prefix.
      * exact Hzone_member.
Qed.

Lemma component_forward_history_after_local :
  forall CT P Z M cutoff sGamma mt rGamma h T x sGamma',
    wf_r_config CT sGamma rGamma h ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SLocal T x) sGamma' ->
    runtime_getVal rGamma x = None ->
    component_forward_history_state CT P Z M cutoff sGamma'
      (set_vars rGamma (vars rGamma ++ [Null_a])) h.
Proof.
  intros CT P Z M cutoff sGamma mt rGamma h T x sGamma' Hwf
    [Hforward [Hcomponents Hactive]] Htyping Hrnone.
  split.
  - eapply forward_history_after_local; eauto.
  - split; [exact Hcomponents|].
    inversion Htyping; subst.
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [_ [_ [Hlength _]]]]].
    intros capability_root zone_root
      [yc [Tc [Htypec [Hvalc Hrdmc]]]] Hcapcomponent
      [yz [Tz [Htypez [Hvalz Hrdmz]]]] Hzonecomponent.
    destruct (appended_null_nonnull_lookup_is_old sGamma rGamma T yc Tc
      capability_root Hlength Htypec Hvalc) as [Holdtypec Holdvalc].
    destruct (appended_null_nonnull_lookup_is_old sGamma rGamma T yz Tz
      zone_root Hlength Htypez Hvalz) as [Holdtypez Holdvalz].
    eapply Hactive with (capability_root := capability_root)
      (zone_root := zone_root).
    + exists yc, Tc. repeat split; assumption.
    + exact Hcapcomponent.
    + exists yz, Tz. repeat split; assumption.
    + exact Hzonecomponent.
Qed.
