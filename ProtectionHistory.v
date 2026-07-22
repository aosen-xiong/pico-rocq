Require Import Syntax Notations Helpers Typing Subtyping Bigstep.
Require Import ViewpointAdaptation Properties Preservation ReadonlyHelper.
Require Import Reachability MutableCapability ExecutionConfinement.
From Stdlib Require Import List Lia Sets.Ensembles.
Import ListNotations.

(** [Z] is a proof-only zone that contains the paper-level protected set [P]
    and may grow with freshly allocated objects.  Backward closure says that
    an execution-reachable source of an RDM edge joins the zone whenever its
    target is already in the zone.  This is precisely the direction needed to
    rule out a mutable field read into [P]. *)
Definition protected_zone_contains
  (P Z : Ensemble Loc) : Prop :=
  Included Loc P Z.

Definition zone_env_safe
  (Z : Ensemble Loc) (sGamma : s_env) (rGamma : r_env) : Prop :=
  env_respects_protected_set Z sGamma rGamma.

Definition typed_root
  (qualifier : q) (sGamma : s_env) (rGamma : r_env) (root : Loc) : Prop :=
  exists x T,
    static_getType sGamma x = Some T /\
    runtime_getVal rGamma x = Some (Iot root) /\
    sqtype T = qualifier.

Lemma safe_call_callee_zone_env :
  forall CT Z sGamma mt rGamma h x m y args sGamma'
    vals ly cy runtime_mdef,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x m y args) sGamma' ->
    readonly_state_method_scope mt ->
    zone_env_safe Z sGamma rGamma ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    zone_env_safe Z
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)).
Proof.
  intros CT Z sGamma mt rGamma h x m y args sGamma' vals ly cy runtime_mdef
    Hwf Htyping Hsafe_scope Henv Hval_y Hbase Hfind_runtime Hargs.
  inversion Htyping; subst.
  - exfalso. destruct Hscope as [-> | [-> _]];
      destruct Hsafe_scope; congruence.
  - assert (Hsignature : msignature runtime_mdef = msignature mdef).
    { eapply runtime_call_signature_agrees; eauto. }
    rewrite Hsignature.
    intros z l T Htype Hval HinZ.
    destruct z as [|i].
    + simpl in Htype, Hval. injection Htype as <-. injection Hval as <-.
      have Hactual_safe := Henv y ly Ty Hget_y Hval_y HinZ.
      destruct Hrcv_sub as [Hordinary | [_ [Hformal_rdm _]]].
      * eapply adapted_subtype_safe_implies_safe; eauto.
      * rewrite Hformal_rdm. unfold is_nonmutable_qualifier. auto.
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
      destruct (runtime_lookup_list_nth_zs rGamma args vals i (Iot l)
        Hargs Hval) as [arg' [Harg'_index Harg_val]].
      rewrite Harg_index in Harg'_index. injection Harg'_index as <-.
      have Hactual_safe := Henv arg l Targ Harg_type Harg_val HinZ.
      eapply adapted_subtype_safe_implies_safe; eauto.
Qed.

Lemma call_callee_operationally_confined :
  forall P cutoff rGamma h y args vals ly,
    state_is_confined P cutoff rGamma h ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    runtime_lookup_list rGamma args = Some vals ->
    state_is_confined P cutoff (mkr_env (Iot ly :: vals)) h.
Proof.
  intros P cutoff rGamma h y args vals ly [Henv Hheap] Hreceiver Hargs.
  split; [|exact Hheap].
  intros i l Hval. destruct i as [|i].
  - simpl in Hval. injection Hval as <-. eapply Henv; eauto.
  - simpl in Hval.
    exact (env_confined_lookup_list P cutoff rGamma args vals
      Henv Hargs i l Hval).
Qed.

Lemma wf_config_nonnull_variable_not_bot :
  forall CT sGamma rGamma h x T l,
    wf_r_config CT sGamma rGamma h ->
    static_getType sGamma x = Some T ->
    runtime_getVal rGamma x = Some (Iot l) ->
    sqtype T <> Bot.
Proof.
  intros CT sGamma rGamma h x T l Hwf Htype Hval.
  destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwf)
    as [this [qcontext [Hthis [_ Hqcontext]]]].
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [_ [_ [_ Hcorr]]]]].
  have Hxdom := Htype. apply static_getType_dom in Hxdom.
  specialize (Hcorr this qcontext Hthis Hqcontext x Hxdom T Htype).
  rewrite Hval in Hcorr. eapply typable_nonnull_not_bot; eauto.
Qed.

Lemma safe_call_callee_mut_variable_origin :
  forall CT sGamma mt rGamma h x m y args sGamma'
    vals ly cy runtime_mdef z T l,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x m y args) sGamma' ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    static_getType
      (mreceiver (msignature runtime_mdef) :: mparams (msignature runtime_mdef))
      z = Some T ->
    runtime_getVal (mkr_env (Iot ly :: vals)) z = Some (Iot l) ->
    sqtype T = Mut ->
    typed_root Mut sGamma rGamma l.
Proof.
  intros CT sGamma mt rGamma h x m y args sGamma' vals ly cy runtime_mdef
    z T l Hwf Htyping Hsafe_scope Hval_y Hbase Hfind_runtime Hargs
    Htype Hval Hmut.
  inversion Htyping; subst.
  - exfalso. destruct Hscope as [-> | [-> _]];
      destruct Hsafe_scope; congruence.
  - assert (Hsignature : msignature runtime_mdef = msignature mdef).
    { eapply runtime_call_signature_agrees; eauto. }
    rewrite Hsignature in Htype. clear Hsignature.
    destruct z as [|i].
    + simpl in Htype, Hval. injection Htype as <-. injection Hval as <-.
      destruct Hrcv_sub as [Hordinary | [_ [Hformal_rdm _]]].
      * apply qualified_type_subtype_q_subtype in Hordinary.
        unfold vpa_mutability_tt_readonly_state in Hordinary.
        rewrite Hmut in Hordinary. simpl in Hordinary.
        have Hnotbot := wf_config_nonnull_variable_not_bot
          CT _ rGamma h y Ty ly Hwf Hget_y Hval_y.
        destruct (sqtype Ty) eqn:Hq; simpl in Hordinary;
          try solve [inversion Hordinary; subst; congruence];
          try solve [exists y, Ty; repeat split; assumption];
          exfalso; apply Hnotbot; exact Hq.
      * rewrite Hformal_rdm in Hmut. discriminate.
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
      destruct (runtime_lookup_list_nth_zs rGamma args vals i (Iot l)
        Hargs Hval) as [arg' [Harg'_index Harg_val]].
      rewrite Harg_index in Harg'_index. injection Harg'_index as <-.
      apply qualified_type_subtype_q_subtype in Hsub_i.
      unfold vpa_mutability_tt_readonly_state in Hsub_i.
      rewrite Hmut in Hsub_i. simpl in Hsub_i.
      have Hnotbot := wf_config_nonnull_variable_not_bot
        CT _ rGamma h arg Targ l Hwf Harg_type Harg_val.
      destruct (sqtype Ty); simpl in Hsub_i;
      destruct (sqtype Targ) eqn:Hq;
        try solve [inversion Hsub_i; subst; congruence];
        try solve [exists arg, Targ; repeat split; assumption];
        exfalso; apply Hnotbot; exact Hq.
Qed.

Lemma safe_call_callee_mut_root_origin :
  forall CT sGamma mt rGamma h x m y args sGamma'
    vals ly cy runtime_mdef root,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x m y args) sGamma' ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    typed_root Mut
      (mreceiver (msignature runtime_mdef) :: mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) root ->
    typed_root Mut sGamma rGamma root.
Proof.
  intros CT sGamma mt rGamma h x m y args sGamma' vals ly cy runtime_mdef
    root Hwf Htyping Hscope Hval_y Hbase Hfind Hargs
    [z [T [Htype [Hval Hmut]]]].
  eapply safe_call_callee_mut_variable_origin; eauto.
Qed.

Lemma appended_null_nonnull_lookup_is_old :
  forall sGamma rGamma Tnew x Tx l,
    dom sGamma = dom (vars rGamma) ->
    static_getType (sGamma ++ [Tnew]) x = Some Tx ->
    runtime_getVal (set_vars rGamma (vars rGamma ++ [Null_a])) x =
      Some (Iot l) ->
    static_getType sGamma x = Some Tx /\
    runtime_getVal rGamma x = Some (Iot l).
Proof.
  intros sGamma rGamma Tnew x Tx l Hlength Htype Hval.
  have Htype_extended := Htype.
  have Hval_extended := Hval.
  assert (Hxextended : x < S (dom (vars rGamma))).
  { apply runtime_getVal_dom in Hval. simpl in Hval.
    rewrite length_app in Hval. simpl in Hval. lia. }
  assert (Hxold : x < dom (vars rGamma)).
  { destruct (Nat.eq_dec x (dom (vars rGamma))) as [->|Hneq].
    - rewrite runtime_getVal_last in Hval_extended. discriminate.
    - lia. }
  split.
  - change (nth_error sGamma x = Some Tx).
    change (nth_error (sGamma ++ [Tnew]) x = Some Tx) in Htype_extended.
    assert (Hxs : x < length sGamma) by lia.
    have Happ := nth_error_app1 sGamma [Tnew] Hxs.
    rewrite Happ in Htype_extended. exact Htype_extended.
  - have Hsame := runtime_getVal_last2 rGamma x Null_a Hxold.
    exact (eq_trans (eq_sym Hsame) Hval_extended).
Qed.

Lemma mut_expression_result_has_mutable_root :
  forall CT sGamma mt rGamma h e l T,
    wf_r_config CT sGamma rGamma h ->
    eval_expr CT rGamma h e (Iot l) OK rGamma h ->
    expr_has_type CT sGamma mt e T ->
    readonly_state_method_scope mt ->
    sqtype T = Mut ->
    exists root,
      typed_root Mut sGamma rGamma root /\
      retained_mut_reachable CT h root l.
Proof.
  intros CT sGamma mt rGamma h e l T Hwf Heval Htyping Hscope Hmut.
  inversion Heval; subst.
  - inversion Htyping; subst.
    exists l. split.
    + exists x, T. repeat split; assumption.
    + constructor.
  - inversion Htyping; subst.
    + exfalso. destruct Hmt; subst; destruct Hscope; congruence.
    + simpl in Hmut.
      assert (Hshape : sqtype T0 = Mut /\
        (mutability (ftype fDef) = RDM_f \/
         mutability (ftype fDef) = Mut_f)).
      { destruct (sqtype T0); destruct (mutability (ftype fDef));
          simpl in Hmut; try discriminate; auto. }
      destruct Hshape as [Hreceiver [Hrdm | Hmut_field]].
      exists v. split.
      * exists x, T0. repeat split; assumption.
      * eapply rmr_step; [constructor|].
        constructor. eapply runtime_static_rdm_edge; eauto.
      * exists v. split.
        -- exists x, T0. repeat split; assumption.
        -- eapply rmr_step; [constructor|].
           eapply runtime_static_mut_field_edge; eauto.
Qed.

Lemma rdm_expression_result_has_rdm_root :
  forall CT sGamma mt rGamma h e l T,
    wf_r_config CT sGamma rGamma h ->
    eval_expr CT rGamma h e (Iot l) OK rGamma h ->
    expr_has_type CT sGamma mt e T ->
    readonly_state_method_scope mt ->
    sqtype T = RDM ->
    exists root,
      typed_root RDM sGamma rGamma root /\
      mutable_reachable CT h root l.
Proof.
  intros CT sGamma mt rGamma h e l T Hwf Heval Htyping Hscope Hrdm_result.
  inversion Heval; subst.
  - inversion Htyping; subst.
    exists l. split.
    + exists x, T. repeat split; assumption.
    + constructor.
  - inversion Htyping; subst.
    + exfalso. destruct Hmt; subst; destruct Hscope; congruence.
    + simpl in Hrdm_result.
      assert (Hshape : sqtype T0 = RDM /\ mutability (ftype fDef) = RDM_f).
      { destruct (sqtype T0); destruct (mutability (ftype fDef));
          simpl in Hrdm_result; try discriminate; auto. }
      destruct Hshape as [Hreceiver Hrdm].
      assert (Hedge : mutable_edge CT h v l).
      { eapply runtime_static_rdm_edge; eauto. }
      exists v. split.
      * exists x, T0. repeat split; assumption.
      * eapply mr_step; [constructor|exact Hedge].
Qed.

Lemma mutable_reachable_trans :
  forall CT h l1 l2 l3,
    mutable_reachable CT h l1 l2 ->
    mutable_reachable CT h l2 l3 ->
    mutable_reachable CT h l1 l3.
Proof.
  intros CT h l1 l2 l3 H12 H23.
  induction H23.
  - exact H12.
  - exact (@mr_step CT h l1 l2 l3 (IHmutable_reachable H12) H).
Qed.

Lemma nonnull_subtype_to_rdm_is_rdm :
  forall CT h l T1 T2 qcontext,
    wf_r_typable CT h l T1 qcontext ->
    qualified_type_subtype CT T1 T2 ->
    sqtype T2 = RDM ->
    sqtype T1 = RDM.
Proof.
  intros CT h l T1 T2 qcontext Htyp Hsub Hrdm.
  apply qualified_type_subtype_q_subtype in Hsub.
  rewrite Hrdm in Hsub.
  inversion Hsub; subst; auto.
  exfalso. eapply typable_nonnull_not_bot; eauto.
Qed.

Lemma mutable_edge_preserves_runtime_mutability :
  forall CT h source target qruntime,
    wf_heap CT h ->
    mutable_edge CT h source target ->
    r_muttype h source = Some qruntime ->
    r_muttype h target = Some qruntime.
Proof.
  intros CT h source target qruntime Hwf Hedge Hsource_mut.
  inversion Hedge as [? ? o f D fdef Hobj Hfield Hsub Hfd Hrdm]; subst.
  have Hsource_dom := Hobj. apply runtime_getObj_dom in Hsource_dom.
  specialize (Hwf source Hsource_dom).
  unfold wf_obj in Hwf. rewrite Hobj in Hwf.
  destruct Hwf as [_ [field_defs [Hcollect [Hlength Hvalues]]]].
  assert (Hfdom : f < dom field_defs).
  { rewrite <- Hlength. apply getVal_dom in Hfield. exact Hfield. }
  destruct (nth_error_Some_exists field_defs f Hfdom) as [runtime_fd Hruntime_fd].
  have Hvalue_typed := Hvalues.
  unfold getVal in Hfield.
  eapply Forall2_nth_error with (i := f) (a := Iot target)
    (b := runtime_fd) in Hvalue_typed;
    [|exact Hfield|exact Hruntime_fd].
  simpl in Hvalue_typed.
  assert (Hruntime_lookup : sf_def_rel CT (rctype (rt_type o)) f runtime_fd).
  { unfold sf_def_rel. econstructor; eauto. }
  assert (Hdeclared_lookup : sf_def_rel CT (rctype (rt_type o)) f fdef).
  { eapply field_inheritance_subtyping; eauto. }
  assert (runtime_fd = fdef).
  { eapply field_lookup_deterministic_rel; eauto. }
  subst runtime_fd. rewrite Hrdm in Hvalue_typed.
  destruct (runtime_getObj h target) as [target_obj|] eqn:Htarget_obj;
    try contradiction.
  destruct Hvalue_typed as [target_type [Htarget_type [Hbase Hqualifier]]].
  unfold r_muttype, r_type in *.
  rewrite Hobj in Hsource_mut. simpl in Hsource_mut.
  rewrite Htarget_obj in Htarget_type. injection Htarget_type as <-.
  rewrite Htarget_obj. simpl.
  destruct (rqtype (rt_type o)); destruct (rqtype (rt_type target_obj));
    simpl in Hsource_mut, Hqualifier |- *; try congruence.
  all: contradiction.
Qed.

Lemma retained_edge_preserves_runtime_mutability :
  forall CT h source target,
    wf_heap CT h ->
    retained_mut_edge CT h source target ->
    r_muttype h source = Some Mut_r ->
    r_muttype h target = Some Mut_r.
Proof.
  intros CT h source target Hwf Hedge Hsource_mut.
  inversion Hedge as [l l' Hrdm_edge | l l' o f D fdef
    Hobj Hedge_source_mut Hfield Hsub Hfd Hmut]; subst.
  - eapply mutable_edge_preserves_runtime_mutability; eauto.
  - have Hsource_dom := Hobj. apply runtime_getObj_dom in Hsource_dom.
    specialize (Hwf source Hsource_dom).
    unfold wf_obj in Hwf. rewrite Hobj in Hwf.
    destruct Hwf as [_ [field_defs [Hcollect [Hlength Hvalues]]]].
    assert (Hfdom : f < dom field_defs).
    { rewrite <- Hlength. apply getVal_dom in Hfield. exact Hfield. }
    destruct (nth_error_Some_exists field_defs f Hfdom) as
      [runtime_fd Hruntime_fd].
    have Hvalue_typed := Hvalues.
    unfold getVal in Hfield.
    eapply Forall2_nth_error with (i := f) (a := Iot target)
      (b := runtime_fd) in Hvalue_typed;
      [|exact Hfield|exact Hruntime_fd].
    simpl in Hvalue_typed.
    assert (Hruntime_lookup :
      sf_def_rel CT (rctype (rt_type o)) f runtime_fd).
    { unfold sf_def_rel. econstructor; eauto. }
    assert (Hdeclared_lookup :
      sf_def_rel CT (rctype (rt_type o)) f fdef).
    { eapply field_inheritance_subtyping; eauto. }
    assert (runtime_fd = fdef).
    { eapply field_lookup_deterministic_rel; eauto. }
    subst runtime_fd. rewrite Hmut in Hvalue_typed.
    destruct (runtime_getObj h target) as [target_obj|] eqn:Htarget_obj;
      try contradiction.
    destruct Hvalue_typed as [target_type [Htarget_type [Hbase Hqualifier]]].
    unfold r_muttype, r_type in *.
    rewrite Htarget_obj in Htarget_type. injection Htarget_type as <-.
    rewrite Htarget_obj. simpl.
    rewrite Hobj in Hsource_mut. simpl in Hsource_mut.
    destruct (rqtype (rt_type o)); destruct (rqtype (rt_type target_obj));
      simpl in Hsource_mut, Hqualifier |- *; try congruence.
    all: contradiction.
Qed.

Lemma retained_edge_preserves_runtime_context :
  forall CT h source target runtime_q,
    wf_heap CT h ->
    retained_mut_edge CT h source target ->
    r_muttype h source = Some runtime_q ->
    r_muttype h target = Some runtime_q.
Proof.
  intros CT h source target runtime_q Hwf Hedge Hsource_runtime.
  inversion Hedge as [l l' Hrdm_edge | l l' o f D fdef
    Hobj Hsource_mut Hfield Hsub Hfd Hmut]; subst.
  - eapply mutable_edge_preserves_runtime_mutability; eauto.
  - rewrite Hsource_mut in Hsource_runtime. injection Hsource_runtime as <-.
    eapply retained_edge_preserves_runtime_mutability; eauto.
Qed.

Lemma retained_reachable_preserves_runtime_mutability :
  forall CT h source target,
    wf_heap CT h ->
    retained_mut_reachable CT h source target ->
    r_muttype h source = Some Mut_r ->
    r_muttype h target = Some Mut_r.
Proof.
  intros CT h source target Hwf Hreach Hsource.
  induction Hreach.
  - exact Hsource.
  - eapply retained_edge_preserves_runtime_mutability; eauto.
Qed.

Lemma mutable_edge_reflects_runtime_mutability :
  forall CT h source target qruntime,
    wf_heap CT h ->
    mutable_edge CT h source target ->
    r_muttype h target = Some qruntime ->
    r_muttype h source = Some qruntime.
Proof.
  intros CT h source target qruntime Hwf Hedge Htarget.
  inversion Hedge as [? ? o f D fdef Hobj Hfield Hsub Hfd Hrdm]; subst.
  unfold r_muttype, r_type. rewrite Hobj. simpl.
  destruct (rqtype (rt_type o)) eqn:Hsourceq.
  - assert (Hsource : r_muttype h source = Some Mut_r).
    { unfold r_muttype. rewrite Hobj. simpl. rewrite Hsourceq. reflexivity. }
    have Hforward := mutable_edge_preserves_runtime_mutability
      CT h source target Mut_r Hwf Hedge Hsource.
    rewrite Htarget in Hforward.
    injection Hforward as <-. reflexivity.
  - assert (Hsource : r_muttype h source = Some Imm_r).
    { unfold r_muttype. rewrite Hobj. simpl. rewrite Hsourceq. reflexivity. }
    have Hforward := mutable_edge_preserves_runtime_mutability
      CT h source target Imm_r Hwf Hedge Hsource.
    rewrite Htarget in Hforward.
    injection Hforward as <-. reflexivity.
Qed.

Lemma retained_edge_reflects_runtime_mutability :
  forall CT h source target runtime_q,
    wf_heap CT h ->
    retained_mut_edge CT h source target ->
    r_muttype h target = Some runtime_q ->
    r_muttype h source = Some runtime_q.
Proof.
  intros CT h source target runtime_q Hwf Hedge Htarget_runtime.
  inversion Hedge as [l l' Hrdm_edge | l l' o f D fdef
    Hobj Hsource_mut Hfield Hsub Hfd Hmut]; subst.
  - eapply mutable_edge_reflects_runtime_mutability; eauto.
  - have Htarget_mut := retained_edge_preserves_runtime_mutability CT h
      source target Hwf Hedge Hsource_mut.
    rewrite Htarget_runtime in Htarget_mut.
    inversion Htarget_mut; subst runtime_q.
    exact Hsource_mut.
Qed.

Lemma mutable_reachable_preserves_runtime_mutability :
  forall CT h source target qruntime,
    wf_heap CT h ->
    mutable_reachable CT h source target ->
    r_muttype h source = Some qruntime ->
    r_muttype h target = Some qruntime.
Proof.
  intros CT h source target qruntime Hwf Hreach Hsource.
  induction Hreach.
  - exact Hsource.
  - eapply mutable_edge_preserves_runtime_mutability; eauto.
Qed.

Lemma new_typed_root_origin :
  forall CT sGamma mt rGamma h x qc C args sGamma' qualifier root,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    typed_root qualifier sGamma'
      (update_r_env_value rGamma x (Iot (dom h))) root ->
    typed_root qualifier sGamma rGamma root \/
    (root = dom h /\ exists Tx,
      static_getType sGamma x = Some Tx /\ sqtype Tx = qualifier).
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' qualifier root Hwf
    Htyping [z [Tz [Htype_z [Hval_z Hqual_z]]]].
  inversion Htyping; subst sGamma'.
  assert (Hxdom : x < dom (vars rGamma)).
  { apply static_getType_dom in Hget_x.
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [_ [_ [Hlength _]]]]]. lia. }
  destruct (Nat.eq_dec z x) as [->|Hneq].
  - rewrite Hget_x in Htype_z. injection Htype_z as <-.
    rewrite runtime_getVal_update_same in Hval_z; auto.
    injection Hval_z as <-. right. split; [reflexivity|].
    exists Tx. repeat split; assumption.
  - rewrite runtime_getVal_update_diff in Hval_z; auto.
    left. exists z, Tz. repeat split; assumption.
Qed.

Lemma new_mut_result_requires_mut_creation :
  forall CT sGamma mt x qc C args sGamma' Tx,
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    static_getType sGamma' x = Some Tx ->
    sqtype Tx = Mut ->
    qc2q qc = Mut.
Proof.
  intros CT sGamma mt x qc C args sGamma' Tx Htyping Hget Hmut.
  inversion Htyping; subst sGamma'.
  rewrite Hget_x in Hget. injection Hget as <-.
  apply qualified_type_subtype_q_subtype in Hresult_sub.
  rewrite Hmut in Hresult_sub. simpl in Hresult_sub.
  destruct qc; inversion Hresult_sub; reflexivity.
Qed.

Lemma new_rdm_result_requires_rdm_creation :
  forall CT sGamma mt x qc C args sGamma' Tx,
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    static_getType sGamma' x = Some Tx ->
    sqtype Tx = RDM ->
    qc2q qc = RDM.
Proof.
  intros CT sGamma mt x qc C args sGamma' Tx Htyping Hget Hrdm.
  inversion Htyping; subst sGamma'.
  rewrite Hget_x in Hget. injection Hget as <-.
  apply qualified_type_subtype_q_subtype in Hresult_sub.
  rewrite Hrdm in Hresult_sub. simpl in Hresult_sub.
  destruct qc; inversion Hresult_sub; reflexivity.
Qed.

Lemma new_creation_rdm_field_target_has_creation_root :
  forall CT sGamma mt rGamma h x qc C args sGamma' vals f fdef target,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    getVal vals f = Some (Iot target) ->
    sf_def_rel CT C f fdef ->
    mutability (ftype fdef) = RDM_f ->
    typed_root (qc2q qc) sGamma rGamma target.
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' vals f fdef target
    Hwf Htyping Hvals Hfield Hfd Hrdm.
  inversion Htyping; subst sGamma'.
  have Hwfcopy := Hwf.
  unfold wf_r_config in Hwf.
  destruct Hwf as [Hwfct [Hwfheap [Hwfrenv [Hwfsenv [Hlenenv Hcorr]]]]].
  assert (Hctorwf : wf_constructor CT C consig).
  { eapply constructor_lookup_wf.
    - exact Hwfct.
    - eapply constructor_sig_lookup_dom. exact Hconsig.
    - exact Hconsig. }
  unfold wf_constructor in Hctorwf.
  destruct Hctorwf as [Hctorbound [Hparamswf [field_defs
    [Hcollect [Hlenfields Hparamfields]]]]].
  unfold sf_def_rel in Hfd.
  inversion Hfd as [? ? lookup_fields ? ? Hcollect_lookup Hgetfd]; subst.
  assert (lookup_fields = field_defs).
  { eapply collect_fields_deterministic_rel; eauto. }
  subst lookup_fields.
  unfold getVal in Hfield.
  assert (Hfdom : f < dom field_defs).
  { apply gget_dom in Hgetfd. exact Hgetfd. }
  destruct (nth_error_Some_exists (cparams consig) f
    (ltac:(rewrite Hlenfields; exact Hfdom))) as [paramT HparamT].
  assert (Hargdom : f < dom argtypes).
  { have Harglen := Forall2_length Harg_sub.
    rewrite Harglen. rewrite length_map. rewrite Hlenfields. exact Hfdom. }
  destruct (nth_error_Some_exists argtypes f Hargdom) as [argT HargT].
  assert (Hadapt_param :
    nth_error (map (vpa_mutability_constructor_param qc) (cparams consig)) f =
    Some (vpa_mutability_constructor_param qc paramT)).
  { rewrite nth_error_map. rewrite HparamT. reflexivity. }
  have HArgSubtype := Harg_sub.
  eapply Forall2_nth_error with (i := f) (a := argT)
    (b := vpa_mutability_constructor_param qc paramT) in HArgSubtype;
    [|exact HargT|exact Hadapt_param].
  have HParamField := Hparamfields.
  eapply Forall2_nth_error with (i := f) (a := paramT) (b := fdef)
    in HParamField; [|exact HparamT|exact Hgetfd].
  destruct (static_getType_list_nth_zs sGamma args argtypes f argT
    Hget_args HargT) as [arg [Harg_index Harg_static]].
  destruct (runtime_lookup_list_nth_zs rGamma args vals f (Iot target)
    Hvals Hfield) as [arg' [Harg'_index Harg_runtime]].
  rewrite Harg_index in Harg'_index. injection Harg'_index as <-.
  destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwfcopy)
    as [this [qcontext [Hrthis [_ Hqcontext]]]].
  assert (Harg_index_dom : arg < dom sGamma).
  { apply static_getType_dom in Harg_static. exact Harg_static. }
  specialize (Hcorr this qcontext Hrthis Hqcontext arg Harg_index_dom argT
    Harg_static).
  rewrite Harg_runtime in Hcorr.
  have Hnotbot := typable_nonnull_not_bot CT h target argT qcontext Hcorr.
  apply qualified_type_subtype_q_subtype in HArgSubtype.
  apply qualified_type_subtype_q_subtype in HParamField.
  simpl in HArgSubtype, HParamField.
  rewrite Hrdm in HParamField. simpl in HParamField.
  assert (Hargcreation : sqtype argT = qc2q qc).
  { unfold vpa_mutability_constructor_param, vpa_mutability_qq_abstract_state
      in HArgSubtype.
    unfold vpa_mutability_constructor_fld in HParamField.
    unfold vpa_mutability_bound, qc2q in Hqc.
    destruct qc; destruct qcontext; destruct (cqualifier consig);
      destruct paramT as [qparam cparam]; destruct qparam;
      destruct argT as [qarg carg]; destruct qarg;
      simpl in Hqc, HArgSubtype, HParamField, Hnotbot |- *;
      try solve_q_subtype_wrong; try contradiction; try discriminate;
      reflexivity. }
  exists arg, argT. repeat split; assumption.
Qed.

Lemma new_creation_mut_field_target_has_mut_root :
  forall CT sGamma mt rGamma h x qc C args sGamma' vals f fdef target,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    getVal vals f = Some (Iot target) ->
    sf_def_rel CT C f fdef ->
    mutability (ftype fdef) = Mut_f ->
    typed_root Mut sGamma rGamma target.
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' vals f fdef target
    Hwf Htyping Hvals Hfield Hfd Hmut.
  inversion Htyping; subst sGamma'.
  have Hwfcopy := Hwf.
  unfold wf_r_config in Hwf.
  destruct Hwf as [Hwfct [Hwfheap [Hwfrenv [Hwfsenv [Hlenenv Hcorr]]]]].
  assert (Hctorwf : wf_constructor CT C consig).
  { eapply constructor_lookup_wf.
    - exact Hwfct.
    - eapply constructor_sig_lookup_dom. exact Hconsig.
    - exact Hconsig. }
  unfold wf_constructor in Hctorwf.
  destruct Hctorwf as [Hctorbound [Hparamswf [field_defs
    [Hcollect [Hlenfields Hparamfields]]]]].
  unfold sf_def_rel in Hfd.
  inversion Hfd as [? ? lookup_fields ? ? Hcollect_lookup Hgetfd]; subst.
  assert (lookup_fields = field_defs).
  { eapply collect_fields_deterministic_rel; eauto. }
  subst lookup_fields.
  unfold getVal in Hfield.
  assert (Hfdom : f < dom field_defs).
  { apply gget_dom in Hgetfd. exact Hgetfd. }
  destruct (nth_error_Some_exists (cparams consig) f
    (ltac:(rewrite Hlenfields; exact Hfdom))) as [paramT HparamT].
  assert (Hargdom : f < dom argtypes).
  { have Harglen := Forall2_length Harg_sub.
    rewrite Harglen. rewrite length_map. rewrite Hlenfields. exact Hfdom. }
  destruct (nth_error_Some_exists argtypes f Hargdom) as [argT HargT].
  assert (Hadapt_param :
    nth_error (map (vpa_mutability_constructor_param qc) (cparams consig)) f =
    Some (vpa_mutability_constructor_param qc paramT)).
  { rewrite nth_error_map. rewrite HparamT. reflexivity. }
  have HArgSubtype := Harg_sub.
  eapply Forall2_nth_error with (i := f) (a := argT)
    (b := vpa_mutability_constructor_param qc paramT) in HArgSubtype;
    [|exact HargT|exact Hadapt_param].
  have HParamField := Hparamfields.
  eapply Forall2_nth_error with (i := f) (a := paramT) (b := fdef)
    in HParamField; [|exact HparamT|exact Hgetfd].
  destruct (static_getType_list_nth_zs sGamma args argtypes f argT
    Hget_args HargT) as [arg [Harg_index Harg_static]].
  destruct (runtime_lookup_list_nth_zs rGamma args vals f (Iot target)
    Hvals Hfield) as [arg' [Harg'_index Harg_runtime]].
  rewrite Harg_index in Harg'_index. injection Harg'_index as <-.
  destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwfcopy)
    as [this [qcontext [Hrthis [_ Hqcontext]]]].
  have Harg_index_dom := Harg_static. apply static_getType_dom in Harg_index_dom.
  specialize (Hcorr this qcontext Hrthis Hqcontext arg Harg_index_dom argT
    Harg_static).
  rewrite Harg_runtime in Hcorr.
  have Hnotbot := typable_nonnull_not_bot CT h target argT qcontext Hcorr.
  apply qualified_type_subtype_q_subtype in HArgSubtype.
  apply qualified_type_subtype_q_subtype in HParamField.
  simpl in HArgSubtype, HParamField.
  rewrite Hmut in HParamField. simpl in HParamField.
  assert (Hargmut : sqtype argT = Mut).
  { unfold vpa_mutability_constructor_param, vpa_mutability_qq_abstract_state
      in HArgSubtype.
    unfold vpa_mutability_constructor_fld in HParamField.
    unfold vpa_mutability_bound, qc2q in Hqc.
    destruct qc; destruct qcontext; destruct (cqualifier consig);
      destruct paramT as [qparam cparam]; destruct qparam;
      destruct argT as [qarg carg]; destruct qarg;
      simpl in Hqc, HArgSubtype, HParamField, Hnotbot |- *;
      try solve_q_subtype_wrong; try contradiction; try discriminate;
      reflexivity. }
  exists arg, argT. repeat split; assumption.
Qed.

Lemma fresh_retained_reachable_has_old_mut_ancestor :
  forall CT sGamma mt rGamma h x qc C args sGamma' vals freshrt target,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    qc2q qc = Mut ->
    retained_mut_reachable CT
      (h ++ [mkObj (mkruntime_type freshrt C) vals]) (dom h) target ->
    target = dom h \/
    exists old_root,
      typed_root Mut sGamma rGamma old_root /\
      retained_mut_reachable CT h old_root target.
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' vals freshrt target
    Hwf Htyping Hvals Hqcmut Hreach.
  remember (dom h) as fresh eqn:Hfresh in Hreach.
  induction Hreach as [fresh|fresh middle target Hprefix IH Hedge].
  - left. exact Hfresh.
  - destruct (retained_edge_after_append CT h
      (mkObj (mkruntime_type freshrt C) vals) middle target Hedge)
      as [Holdedge | [Hmiddle [field [D [fd [Hfield [Hsub [Hfd
        [Hrdm | Hmut]]]]]]]]].
    + destruct (IH Hfresh) as [Hmiddle | [old_root [Holdroot Holdpath]]].
      * exfalso. subst middle.
        inversion Holdedge as [? ? Hrdmedge | ? ? oldobj ? ? ? Hobj]; subst.
        -- inversion Hrdmedge as [? ? oldobj ? ? ? Hobj].
           apply runtime_getObj_dom in Hobj. lia.
        -- apply runtime_getObj_dom in Hobj. lia.
      * right. exists old_root. split; [exact Holdroot|].
        eapply rmr_step; eauto.
    + subst middle. right. exists target. split.
      * assert (HfdC : sf_def_rel CT C field fd).
        { eapply field_inheritance_subtyping; eauto. }
        have Hroot := new_creation_rdm_field_target_has_creation_root
          CT sGamma mt rGamma h x qc C args sGamma' vals field fd target
          Hwf Htyping Hvals Hfield HfdC Hrdm.
        rewrite Hqcmut in Hroot. exact Hroot.
      * constructor.
    + subst middle. right. exists target. split.
      * assert (HfdC : sf_def_rel CT C field fd).
        { eapply field_inheritance_subtyping; eauto. }
        eapply new_creation_mut_field_target_has_mut_root; eauto.
      * constructor.
Qed.

Lemma fresh_retained_reachable_has_old_authority_ancestor :
  forall CT sGamma mt rGamma h x qc C args sGamma' vals freshrt target
    authority,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    capability_in_context authority (qc2q qc) ->
    retained_mut_reachable CT
      (h ++ [mkObj (mkruntime_type freshrt C) vals]) (dom h) target ->
    target = dom h \/
    exists old_root,
      ((typed_root (qc2q qc) sGamma rGamma old_root /\
        capability_in_context authority (qc2q qc)) \/
       typed_root Mut sGamma rGamma old_root) /\
      retained_mut_reachable CT h old_root target.
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' vals freshrt target
    authority Hwf Htyping Hvals Hqccap Hreach.
  remember (dom h) as fresh eqn:Hfresh in Hreach.
  induction Hreach as [fresh|fresh middle target Hprefix IH Hedge].
  - left. exact Hfresh.
  - destruct (retained_edge_after_append CT h
      (mkObj (mkruntime_type freshrt C) vals) middle target Hedge)
      as [Holdedge | [Hmiddle [field [D [fd [Hfield [Hsub [Hfd
        [Hrdm | Hmut]]]]]]]]].
    + destruct (IH Hfresh) as [Hmiddle | [old_root [Holdroot Holdpath]]].
      * exfalso. subst middle.
        inversion Holdedge as [? ? Hrdmedge | ? ? oldobj ? ? ? Hobj]; subst.
        -- inversion Hrdmedge as [? ? oldobj ? ? ? Hobj].
           apply runtime_getObj_dom in Hobj. lia.
        -- apply runtime_getObj_dom in Hobj. lia.
      * right. exists old_root. split; [exact Holdroot|].
        eapply rmr_step; eauto.
    + subst middle. right. exists target. split.
      * left. split; [|exact Hqccap].
        assert (HfdC : sf_def_rel CT C field fd).
        { eapply field_inheritance_subtyping; eauto. }
        eapply new_creation_rdm_field_target_has_creation_root; eauto.
      * constructor.
    + subst middle. right. exists target. split.
      * right. assert (HfdC : sf_def_rel CT C field fd).
        { eapply field_inheritance_subtyping; eauto. }
        eapply new_creation_mut_field_target_has_mut_root; eauto.
      * constructor.
Qed.


Lemma new_retained_mutable_origin :
  forall CT sGamma mt rGamma h x qc C args sGamma' vals freshrt root target,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    typed_root Mut sGamma'
      (update_r_env_value rGamma x (Iot (dom h))) root ->
    retained_mut_reachable CT
      (h ++ [mkObj (mkruntime_type freshrt C) vals]) root target ->
    target = dom h \/
    exists old_root,
      typed_root Mut sGamma rGamma old_root /\
      retained_mut_reachable CT h old_root target.
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' vals freshrt root target
    Hwf Htyping Hvals Hroot Hreach.
  destruct (new_typed_root_origin CT sGamma mt rGamma h x qc C args sGamma'
    Mut root Hwf Htyping Hroot)
    as [Holdroot | [Hfresh [Tx [Hgetx Hmut]]]].
  - assert (Hrootdom : root < dom h).
    { destruct Holdroot as [z [T [Htype [Hval Hq]]]].
      eapply wf_config_value_dom; eauto. }
    destruct (retained_reachable_from_old_after_append CT h
      (mkObj (mkruntime_type freshrt C) vals) root target
      (ltac:(unfold wf_r_config in Hwf; tauto)) Hrootdom Hreach)
      as [Htargetdom Holdreach].
    right. exists root. split; assumption.
  - subst root.
    assert (HsGamma : sGamma' = sGamma) by (inversion Htyping; reflexivity).
    assert (Hgetx' : static_getType sGamma' x = Some Tx).
    { rewrite HsGamma. exact Hgetx. }
    have Hqcmut := new_mut_result_requires_mut_creation CT sGamma mt x qc C
      args sGamma' Tx Htyping Hgetx' Hmut.
    eapply fresh_retained_reachable_has_old_mut_ancestor; eauto.
Qed.


Lemma assignment_mut_root_has_old_ancestor :
  forall CT sGamma mt rGamma h x e old value,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SVarAss x e) sGamma ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma x = Some old ->
    eval_expr CT rGamma h e value OK rGamma h ->
    forall root,
      typed_root Mut sGamma (update_r_env_value rGamma x value) root ->
      exists old_root,
        typed_root Mut sGamma rGamma old_root /\
        retained_mut_reachable CT h old_root root.
Proof.
  intros CT sGamma mt rGamma h x e old value Hwf Htyping Hscope Hx Heval root
    [z [Tz [Htype_z [Hval_z Hmut_z]]]].
  inversion Htyping; subst.
  destruct (Nat.eq_dec z x) as [->|Hneq].
  - rewrite Hget_x in Htype_z. injection Htype_z as <-.
    assert (Hxdom : x < dom (vars rGamma)).
    { apply static_getType_dom in Hget_x.
      unfold wf_r_config in Hwf.
      destruct Hwf as [_ [_ [_ [_ [Hlength _]]]]]. lia. }
    destruct value as [|l].
    + have Hsame := runtime_getVal_update_same rGamma x Null_a Hxdom.
      rewrite Hsame in Hval_z. discriminate.
    + have Hsame := runtime_getVal_update_same rGamma x (Iot l) Hxdom.
      rewrite Hsame in Hval_z. injection Hval_z as <-.
      destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwf)
        as [this [qcontext [Hrthis [_ Hqcontext]]]].
      have Htypable := expr_eval_preservation CT sGamma mt rGamma h e
        (Iot l) rGamma h Te this qcontext Hrthis Hqcontext Hwf Htype_e Heval.
      have Hmut_e := nonnull_subtype_to_mut_is_mut
        CT h l Te Tx qcontext Htypable Hsub Hmut_z.
      eapply mut_expression_result_has_mutable_root; eauto.
  - rewrite runtime_getVal_update_diff in Hval_z; auto.
    exists root. split.
    + exists z, Tz. repeat split; assumption.
    + constructor.
Qed.

Lemma assignment_rdm_root_has_old_ancestor :
  forall CT sGamma mt rGamma h x e old value,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SVarAss x e) sGamma ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma x = Some old ->
    eval_expr CT rGamma h e value OK rGamma h ->
    forall root,
      typed_root RDM sGamma (update_r_env_value rGamma x value) root ->
      exists old_root,
        typed_root RDM sGamma rGamma old_root /\
        mutable_reachable CT h old_root root.
Proof.
  intros CT sGamma mt rGamma h x e old value Hwf Htyping Hscope Hx Heval root
    [z [Tz [Htype_z [Hval_z Hrdm_z]]]].
  inversion Htyping; subst.
  destruct (Nat.eq_dec z x) as [->|Hneq].
  - rewrite Hget_x in Htype_z. injection Htype_z as <-.
    assert (Hxdom : x < dom (vars rGamma)).
    { apply static_getType_dom in Hget_x.
      unfold wf_r_config in Hwf.
      destruct Hwf as [_ [_ [_ [_ [Hlength _]]]]]. lia. }
    destruct value as [|l].
    + have Hsame := runtime_getVal_update_same rGamma x Null_a Hxdom.
      rewrite Hsame in Hval_z. discriminate.
    + have Hsame := runtime_getVal_update_same rGamma x (Iot l) Hxdom.
      rewrite Hsame in Hval_z. injection Hval_z as <-.
      destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwf)
        as [this [qcontext [Hrthis [_ Hqcontext]]]].
      have Htypable := expr_eval_preservation CT sGamma mt rGamma h e
        (Iot l) rGamma h Te this qcontext Hrthis Hqcontext Hwf Htype_e Heval.
      have Hrdm_e := nonnull_subtype_to_rdm_is_rdm
        CT h l Te Tx qcontext Htypable Hsub Hrdm_z.
      eapply rdm_expression_result_has_rdm_root; eauto.
  - rewrite runtime_getVal_update_diff in Hval_z; auto.
    exists root. split.
    + exists z, Tz. repeat split; assumption.
    + constructor.
Qed.
