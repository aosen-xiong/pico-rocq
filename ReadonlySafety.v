Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation.
Require Import Properties DeepImmutability Reachability Preservation ReadonlyHelper ReadonlyNoMutation.
Require Import CallFrameWellformed.
From Stdlib Require Import List.
From Stdlib Require String.
Import ListNotations.

Lemma readonly_pico_field_write_with_end :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ' l C vals vals' f qt readonlyx anyf rhs anyrq
    (Hstmt : stmt = (SFldWrite readonlyx anyf rhs))
    (Hstatic_type : static_getType sΓ readonlyx = Some qt)
    (Hqt_ro : sqtype qt = RO)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Hmtype: safe_readonly_method_type mt)
    (Heval : eval_stmt OK CT rΓ h stmt OK rΓ' h')
    (Hget_readonly : runtime_getVal rΓ readonlyx = Some (Iot l))
    (Hobj_before : runtime_getObj h l = Some (mkObj (mkruntime_type anyrq C) vals))
    (Hobj_after : runtime_getObj h' l = Some (mkObj (mkruntime_type anyrq C) vals'))
    (Hassign : sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA),
    nth_error vals f = nth_error vals' f.
Proof.
  intros.
  (* Subst the statement form *)
  subst stmt.

  (* Invert the evaluation to get heap update details *)
  inversion Heval; subst.

  (* Invert typing to get field write constraints *)
  inversion Htyping; subst.
  -
    exfalso; apply (proj1 Hmtype); reflexivity.
  -
    exfalso; apply (proj2 Hmtype); reflexivity.
  -
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hclasstable [_ [Hrenv [_ [_ Htypable]]]]].
    assert (Hreadonly_dom : readonlyx < dom sΓ').
    {
      apply static_getType_dom in Hstatic_type.
      exact Hstatic_type.
    }
    rewrite Hget_readonly in Hval_x.
    inversion Hval_x.
    subst l.
    unfold wf_renv in Hrenv.
    destruct Hrenv as [_ [Hreceiver _]].
    destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
    assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
    {
      eapply receiver_mutability_exists_from_bound; eauto.
    }
    destruct HOutterReceiverMutability as [qcontext Hqcontext].
    (* Apply correspondence to get wf_r_typable *)
    specialize (Htypable iot qcontext Hget_iot Hqcontext readonlyx Hreadonly_dom qt Hstatic_type).
    rewrite Hget_readonly in Htypable.
    unfold wf_r_typable in Htypable.
    unfold r_type in Htypable.
    rewrite Hobj in Htypable.
    destruct Htypable as [base qualifier].
    rewrite Hobj in Hobj_before.
    injection Hobj_before as Hobject_eq.
    subst o.
    simpl in base.
    rewrite Hstatic_type in Hget_x. inversion Hget_x. subst Tx.
    destruct (base_subtype_from_ref CT C (sbase qt) base) as
      [D [Hstatic_base Hclass]].
    rewrite Href in Hstatic_base. injection Hstatic_base as <-.

    (* Use the fact that Final/RDA fields are protected from modification *)
    destruct Hassign as [Hfinal | Hrda].
    --
      unfold vpa_assignability in Hassignable.
      destruct a0 eqn: Haeqn; try easy.
      assert (Hneq: anyf <> f).
      {
        intro Heq.
        subst anyf.
        assert (Heq_assign : Final = Assignable).
        {
          eapply sf_assignability_consistent_subtype;
            [exact Hclasstable | exact Hclass | exact Hfinal | exact Hassign_rel].
        }
        discriminate.
      }
      unfold update_field in Hobj_after.
      rewrite Hobj in Hobj_after.
      simpl in Hobj_after.
      unfold update_field in Hobj_after.
      simpl in Hobj_after.
      assert (Hdom: loc_x < dom h).
      {
        apply runtime_getObj_dom in Hobj.
        exact Hobj.
      }
      rewrite runtime_getObj_update_same in Hobj_after; auto.
      inversion Hobj_after; subst.
      simpl.
      symmetry.
      apply update_diff.
      exact Hneq.
      unfold vpa_assignability in Hassignable.
      rewrite Hqt_ro in Hassignable; easy.
      rewrite Hqt_ro in Hassignable; easy.
    -- (* RDA case: RDA fields cannot be written *)
      unfold vpa_assignability in Hassignable.
      destruct a0 eqn: Haeqn; try easy.
      assert (Hneq: anyf <> f).
      {
        intro Heq.
        subst anyf.
        assert (Heq_assign : RDA = Assignable).
        {
          eapply sf_assignability_consistent_subtype;
            [exact Hclasstable | exact Hclass | exact Hrda | exact Hassign_rel].
        }
        discriminate.
      }
      unfold update_field in Hobj_after.
      rewrite Hobj in Hobj_after.
      simpl in Hobj_after.
      unfold update_field in Hobj_after.
      simpl in Hobj_after.
      assert (Hdom: loc_x < dom h).
      {
        apply runtime_getObj_dom in Hobj.
        exact Hobj.
      }
      rewrite runtime_getObj_update_same in Hobj_after; auto.
      inversion Hobj_after; subst.
      simpl.
      symmetry.
      apply update_diff.
      exact Hneq.
      rewrite Hqt_ro in Hassignable; easy.
      rewrite Hqt_ro in Hassignable; easy.
  -
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hclasstable [_ [Hrenv [_ [_ Htypable]]]]].
    assert (Hreadonly_dom : readonlyx < dom sΓ').
    {
      apply static_getType_dom in Hstatic_type.
      exact Hstatic_type.
    }
    rewrite Hget_readonly in Hval_x.
    inversion Hval_x.
    subst l.
    unfold wf_renv in Hrenv.
    destruct Hrenv as [_ [Hreceiver _]].
    destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
    assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
    {
      eapply receiver_mutability_exists_from_bound; eauto.
    }
    destruct HOutterReceiverMutability as [qcontext Hqcontext].
    (* Apply correspondence to get wf_r_typable *)
    specialize (Htypable iot qcontext Hget_iot Hqcontext readonlyx Hreadonly_dom qt Hstatic_type).
    rewrite Hget_readonly in Htypable.
    unfold wf_r_typable in Htypable.
    unfold r_type in Htypable.
    rewrite Hobj in Htypable.
    destruct Htypable as [base qualifier].
    rewrite Hobj in Hobj_before.
    injection Hobj_before as Hobject_eq.
    subst o.
    simpl in base.
    rewrite Hstatic_type in Hget_x. inversion Hget_x. subst Tx.
    destruct (base_subtype_from_ref CT C (sbase qt) base) as
      [D [Hstatic_base Hclass]].
    rewrite Href in Hstatic_base. injection Hstatic_base as <-.

    (* Use the fact that Final/RDA fields are protected from modification *)
    destruct Hassign as [Hfinal | Hrda].
    --
      unfold vpa_assignability in Hassignable.
      destruct a0 eqn: Haeqn; try easy.
      assert (Hneq: anyf <> f).
      {
        intro Heq.
        subst anyf.
        assert (Heq_assign : Final = Assignable).
        {
          eapply sf_assignability_consistent_subtype;
            [exact Hclasstable | exact Hclass | exact Hfinal | exact Hassign_rel].
        }
        discriminate.
      }
      unfold update_field in Hobj_after.
      rewrite Hobj in Hobj_after.
      simpl in Hobj_after.
      unfold update_field in Hobj_after.
      simpl in Hobj_after.
      assert (Hdom: loc_x < dom h).
      {
        apply runtime_getObj_dom in Hobj.
        exact Hobj.
      }
      rewrite runtime_getObj_update_same in Hobj_after; auto.
      inversion Hobj_after; subst.
      simpl.
      symmetry.
      apply update_diff.
      exact Hneq.
      unfold vpa_assignability in Hassignable.
      rewrite Hqt_ro in Hassignable; easy.
      rewrite Hqt_ro in Hassignable; easy.
    -- (* RDA case: RDA fields cannot be written *)
      unfold vpa_assignability in Hassignable.
      destruct a0 eqn: Haeqn; try easy.
      assert (Hneq: anyf <> f).
      {
        intro Heq.
        subst anyf.
        assert (Heq_assign : RDA = Assignable).
        {
          eapply sf_assignability_consistent_subtype;
            [exact Hclasstable | exact Hclass | exact Hrda | exact Hassign_rel].
        }
        discriminate.
      }
      unfold update_field in Hobj_after.
      rewrite Hobj in Hobj_after.
      simpl in Hobj_after.
      unfold update_field in Hobj_after.
      simpl in Hobj_after.
      assert (Hdom: loc_x < dom h).
      {
        apply runtime_getObj_dom in Hobj.
        exact Hobj.
      }
      rewrite runtime_getObj_update_same in Hobj_after; auto.
      inversion Hobj_after; subst.
      simpl.
      symmetry.
      apply update_diff.
      exact Hneq.
      rewrite Hqt_ro in Hassignable; easy.
      rewrite Hqt_ro in Hassignable; easy.
Qed.

(* Paper-facing form: evaluation itself preserves the object's runtime type,
   so callers need not supply the final-heap object as a premise. *)
Theorem readonly_pico_field_write :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ' l C vals f qt readonlyx anyf rhs anyrq
    (Hstmt : stmt = (SFldWrite readonlyx anyf rhs))
    (Hstatic_type : static_getType sΓ readonlyx = Some qt)
    (Hqt_ro : sqtype qt = RO)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Hmtype : safe_readonly_method_type mt)
    (Heval : eval_stmt OK CT rΓ h stmt OK rΓ' h')
    (Hget_readonly : runtime_getVal rΓ readonlyx = Some (Iot l))
    (Hobj_before : runtime_getObj h l = Some (mkObj (mkruntime_type anyrq C) vals))
    (Hassign : sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA),
    exists vals',
      runtime_getObj h' l = Some (mkObj (mkruntime_type anyrq C) vals') /\
      nth_error vals f = nth_error vals' f.
Proof.
  intros CT sΓ mt rΓ h stmt rΓ' h' sΓ' l C vals f
    qt readonlyx anyf rhs anyrq Hstmt Hstatic_type Hqt_ro Hwf Htyping
    Hmtype Heval Hget_readonly Hobj_before Hassign.
  destruct (runtime_preserves_r_type_heap CT rΓ h l
    (mkruntime_type anyrq C) h' vals stmt rΓ' Hobj_before Heval)
    as [vals' Hobj_after].
  exists vals'. split; [exact Hobj_after|].
  eapply readonly_pico_field_write_with_end; eauto.
Qed.

Definition all_params_safe (msig : method_sig) : Prop :=
  is_safe_mode (sqtype (mreceiver msig)) /\
  Forall (fun T => is_safe_mode (sqtype T)) (mparams msig).

Lemma callee_frame_respects_protected_set :
  forall CT h ly vals msig
    (Hwf : wf_r_config CT
      (mreceiver msig :: mparams msig) (mkr_env (Iot ly :: vals)) h)
    (Hsafe : all_params_safe msig),
    env_respects_protected_set
      (reachable_locations_from_initial_env CT h (mkr_env (Iot ly :: vals)))
      (mreceiver msig :: mparams msig) (mkr_env (Iot ly :: vals)).
Proof.
  intros CT h ly vals msig Hwf [Hreceiver_safe Hparams_safe].
  eapply confinement_from_all_readonly_env; eauto.
  intros index T Hlookup.
  unfold static_getType in Hlookup.
  destruct index as [|index].
  - simpl in Hlookup. injection Hlookup as <-. exact Hreceiver_safe.
  - simpl in Hlookup.
    eapply Forall_nth_error in Hparams_safe; eauto.
Qed.

Definition reachable_locations_from_vals
  (CT : class_table) (h : heap) (vals : list value) : Ensembles.Ensemble Loc :=
  fun l_target =>
    exists l_root,
      In (Iot l_root) vals /\
      reachable h l_root l_target.

Lemma reachable_locations_subset_reachable_from_method_frame :
  forall CT h ly vals,
    let rΓmethodinit := {| vars := Iot ly :: vals |} in
    Ensembles.Included Loc
      (reachable_locations_from_vals CT h (Iot ly :: vals))
      (reachable_locations_from_initial_env CT h rΓmethodinit).
Proof.
  intros CT h ly vals rΓmethodinit l Hin.
  unfold reachable_locations_from_vals in Hin.
  destruct Hin as [l_root [Hin_list Hreach]].
  unfold reachable_locations_from_initial_env.
  (* l_root is in (Iot ly :: vals), so either l_root = ly or l_root is in vals *)
  destruct Hin_list as [Heq | Hin_vals].
  - (* Case: Iot l_root = Iot ly *)
    inversion Heq; subst l_root.
    exists 0, ly.
    split.
    -- unfold runtime_getVal. simpl. reflexivity.
    -- exact Hreach.
  - (* Case: Iot l_root in vals *)
    (* Find which variable in vals contains this *)
    have Hin_runtime : exists idx, nth_error vals idx = Some (Iot l_root).
    {
      apply In_nth_error in Hin_vals.
      exact Hin_vals.
    }
    destruct Hin_runtime as [idx Hnth_vals].
    exists (S idx), l_root.
    split.
    -- unfold runtime_getVal. simpl. exact Hnth_vals.
    -- exact Hreach.
Qed.

Lemma readonly_method_call_preserves_arguments_with_end :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ' x y mindex Ty Crecv mdef zs vals ly
         loc_arg C anyrq vals_arg vals_arg' f
    (Hstmt : stmt = (SCall x y mindex zs))
    (Hstatic_type : static_getType sΓ y = Some Ty)
    (Href : sbase Ty = TRef Crecv)
    (Hmethod_lookup : FindMethodWithName CT Crecv mindex mdef)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Hmtype: safe_readonly_method_type mt)
    (Heval : eval_stmt OK CT rΓ h stmt OK rΓ' h')
    (Hget_y : runtime_getVal rΓ y = Some (Iot ly))
    (Hget_zs : runtime_lookup_list rΓ zs = Some vals)
    (HinP: Ensembles.In Loc (reachable_locations_from_vals CT h (Iot ly :: vals)) loc_arg)
    (Harg_obj : runtime_getObj h loc_arg = Some (mkObj (mkruntime_type anyrq C) vals_arg))
    (Harg_obj' : runtime_getObj h' loc_arg = Some (mkObj (mkruntime_type anyrq C) vals_arg'))
    (Hassign : sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA)
    (Hall_readonly : all_params_safe (msignature mdef)),
    nth_error vals_arg f = nth_error vals_arg' f.
  Proof.
  intros.
  subst stmt.
  inversion Heval; subst; try discriminate.
  have Heqy: ly = ly0.
  {
    rewrite Hval_y in Hget_y.
    inversion Hget_y; reflexivity.
  }
  subst ly0.
  have Heqzs : vals = vals0.
  {
    rewrite Hargs in Hget_zs.
    inversion Hget_zs; reflexivity.
  }
  subst vals0.
  inversion Htyping; subst.
  exfalso. destruct Hscope as [Hscope | [Hscope _]]; subst;
    [apply (proj1 Hmtype) | apply (proj2 Hmtype)]; reflexivity.
  rename sΓ' into sΓ.
  rewrite Hget_y0 in Hstatic_type.
  inversion Hstatic_type; subst Ty0.

  have Hmdefeq: mdef1 = mdef.
  {
    unfold wf_r_config in Hwf.
    destruct Hwf as [HClassTable _].
    unfold wf_senv in Hwf0.
    destruct Hwf0 as [Hwf0 Hwftypeuse].
    eapply find_overriding_method_deterministic; eauto.
    eapply Forall_nth_error in Hwftypeuse; eauto.
    rewrite Href in Hwftypeuse.
    unfold wf_stypeuse in Hwftypeuse.
    destruct (bound CT Crecv) eqn: Hbound.
    - unfold bound in Hbound.
      destruct (find_class CT Crecv) eqn:Hfindclass; [|discriminate].
      apply find_class_dom in Hfindclass; auto.
    - contradiction.
  }
  subst mdef1.
  rename mdef into mdef1.
  rename mdef0 into mdef.
  rename Ty into Ty_call.

  have Hwfcopy := Hwf.
  unfold wf_r_config in Hwf.
  destruct Hwf as [Hclasstable [Hheap [Hrenv [Hsenv [_ Htypable]]]]].
  destruct Hfind as [mdeflookup getmbody].
  remember (msignature mdef) as msig.
  inversion mdeflookup; revert getmbody; subst; intro getmbody.
  +
    assert (Hwfmethod: wf_method CT cy mdef).
    {
      eapply method_lookup_wf_class; eauto.
      eapply r_basetype_in_dom; eauto.
      unfold gget_method in Hget_method.
      apply find_some in Hget_method.
      destruct Hget_method as [Hmethod_in _].
      exact Hmethod_in.
    }
    unfold wf_method in Hwfmethod;
    destruct Hwfmethod as [_ [sΓmethodend [mbodyreturntype [Hmethodbody_typing [HmethodReturnBound [HmethodReturnType [HmethodReturnSubtype HMethodoverride]]]]]]];
    remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit;
    remember {| vars := Iot ly :: vals |} as rΓmethodinit;
    remember (set_vars rΓ (update x retval (vars rΓ))) as rΓ'''.
    remember (mreceiver (msignature mdef)) as Ty.
    assert (Hframe_sig : msignature mdef = msignature mdef1).
    { eapply runtime_call_signature_agrees; eauto. }
    assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
    {
      rewrite HeqsΓmethodinit.
      rewrite HeqTy.
      rewrite HeqrΓmethodinit.
      eapply callee_frame_wf_rs_ts; eauto.
      all: rewrite Hframe_sig; assumption.
    }

    eapply deep_readonly_preservation with (stmt := (mbody_stmt mbody)) (sΓ' := sΓmethodend) (mt:=(mtype (msignature mdef))); eauto.
    assert (HenvImpliesEnvRespect :
      env_respects_protected_set
        (reachable_locations_from_initial_env CT h rΓmethodinit)
        sΓmethodinit rΓmethodinit).
    {
      have Hwf_frame := Hwf_method_frame.
      rewrite HeqsΓmethodinit in Hwf_frame.
      rewrite HeqTy in Hwf_frame.
      rewrite HeqrΓmethodinit in Hwf_frame.
      rewrite HeqsΓmethodinit.
      rewrite HeqTy.
      rewrite HeqrΓmethodinit.
      eapply callee_frame_respects_protected_set.
      exact Hwf_frame.
      rewrite Hframe_sig. exact Hall_readonly.
    }
    exact HenvImpliesEnvRespect.
    rewrite getmbody; auto.
    rewrite Hframe_sig; split; assumption.
    have Hsubset := reachable_locations_subset_reachable_from_method_frame CT h ly vals.
    rewrite <- HeqrΓmethodinit in Hsubset.
    unfold Ensembles.Included in Hsubset.
    exact (Hsubset loc_arg HinP).
  +
    assert (Hwfmethod: exists D ddef, class_subtype CT cy D /\ find_class CT D = Some ddef /\ In mdef (methods (body ddef)) /\ wf_method CT D mdef).
    {
      eapply method_lookup_in_wellformed_inherited; eauto.
      eapply r_basetype_in_dom; eauto.
    }
    destruct Hwfmethod as [D Hwfmethod].
    destruct Hwfmethod as [ddef Hwfmethod].
    destruct Hwfmethod as [Hbasecyd [HfindD [HmdefinD Hwfmethod]]].

    unfold wf_method in Hwfmethod;
    destruct Hwfmethod as [_ [sΓmethodend [mbodyreturntype [Hmethodbody_typing [HmethodReturnBound [HmethodReturnType [HmethodReturnSubtype HMethodoverride]]]]]]];
    remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit;
    remember {| vars := Iot ly :: vals |} as rΓmethodinit;
    remember (set_vars rΓ (update x retval (vars rΓ))) as rΓ'''.
    remember (mreceiver (msignature mdef)) as Ty.
    assert (Hframe_sig : msignature mdef = msignature mdef1).
    { eapply runtime_call_signature_agrees; eauto. }
    assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
    {
      rewrite HeqsΓmethodinit.
      rewrite HeqTy.
      rewrite HeqrΓmethodinit.
      eapply callee_frame_wf_rs_ts; eauto.
      all: rewrite Hframe_sig; assumption.
    }
    eapply deep_readonly_preservation with (stmt := (mbody_stmt mbody)) (sΓ' := sΓmethodend) (mt:=(mtype (msignature mdef))); eauto.
    assert (HenvImpliesEnvRespect :
      env_respects_protected_set
        (reachable_locations_from_initial_env CT h rΓmethodinit)
        sΓmethodinit rΓmethodinit).
    {
      have Hwf_frame := Hwf_method_frame.
      rewrite HeqsΓmethodinit in Hwf_frame.
      rewrite HeqTy in Hwf_frame.
      rewrite HeqrΓmethodinit in Hwf_frame.
      rewrite HeqsΓmethodinit.
      rewrite HeqTy.
      rewrite HeqrΓmethodinit.
      eapply callee_frame_respects_protected_set.
      exact Hwf_frame.
      rewrite Hframe_sig. exact Hall_readonly.
    }
    exact HenvImpliesEnvRespect.
    rewrite getmbody; auto.
    rewrite Hframe_sig; split; assumption.
    have Hsubset := reachable_locations_subset_reachable_from_method_frame CT h ly vals.
    rewrite <- HeqrΓmethodinit in Hsubset.
    unfold Ensembles.Included in Hsubset.
    exact (Hsubset loc_arg HinP).
  all: eauto.
Qed.

(** Public RS guarantee with final-object existence and runtime type derived
    from the successful call evaluation. *)
Theorem readonly_method_call_preserves_arguments :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ' x y mindex Ty Crecv mdef zs vals ly
         loc_arg C anyrq vals_arg f
    (Hstmt : stmt = (SCall x y mindex zs))
    (Hstatic_type : static_getType sΓ y = Some Ty)
    (Href : sbase Ty = TRef Crecv)
    (Hmethod_lookup : FindMethodWithName CT Crecv mindex mdef)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Hmtype: safe_readonly_method_type mt)
    (Heval : eval_stmt OK CT rΓ h stmt OK rΓ' h')
    (Hget_y : runtime_getVal rΓ y = Some (Iot ly))
    (Hget_zs : runtime_lookup_list rΓ zs = Some vals)
    (HinP: Ensembles.In Loc (reachable_locations_from_vals CT h (Iot ly :: vals)) loc_arg)
    (Harg_obj : runtime_getObj h loc_arg = Some (mkObj (mkruntime_type anyrq C) vals_arg))
    (Hassign : sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA)
    (Hall_readonly : all_params_safe (msignature mdef)),
    exists vals_arg',
      runtime_getObj h' loc_arg = Some (mkObj (mkruntime_type anyrq C) vals_arg') /\
      nth_error vals_arg f = nth_error vals_arg' f.
Proof.
  intros CT sΓ mt rΓ h stmt rΓ' h' sΓ' x y mindex Ty Crecv mdef zs vals ly
    loc_arg C anyrq vals_arg f Hstmt Hstatic_type Href Hmethod_lookup Hwf Htyping
    Hmtype Heval Hget_y Hget_zs HinP Harg_obj Hassign Hall_readonly.
  destruct (runtime_preserves_r_type_heap CT rΓ h loc_arg
    (mkruntime_type anyrq C) h' vals_arg stmt rΓ' Harg_obj Heval)
    as [vals_arg' Harg_obj'].
  exists vals_arg'. split; [exact Harg_obj'|].
  eapply readonly_method_call_preserves_arguments_with_end; eauto.
Qed.
