Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation.
Require Import Properties DeepImmutability Reachability Preservation ReadonlyHelper ReadonlyConfinement ReadonlyNoMutation.
From Stdlib Require Import List.
From Stdlib Require String.
Import ListNotations.
From RecordUpdate Require Import RecordUpdate.

Theorem readonly_pico_field_write :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ' l C vals vals' f qt readonlyx anyf rhs anyrq
    (Hstmt : stmt = (SFldWrite readonlyx anyf rhs))
    (Hstatic_type : static_getType sΓ readonlyx = Some qt)
    (Hqt_ro : sqtype qt = RO)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Hmtype: mt <> AbstractImm)
    (Heval : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h')
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
    exfalso; apply Hmtype; reflexivity.
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
    inversion Hobj_before.
    rewrite H1 in base.
    simpl in base.

    (* Use the fact that Final/RDA fields are protected from modification *)
    destruct Hassign as [Hfinal | Hrda].
    --  
      rewrite Hstatic_type in Hget_x.
      inversion Hget_x.
      subst Tx.
      (* rewrite Hstatic_type in H16. *)
      unfold vpa_assignability in Hassignable.
      destruct a0 eqn: Haeqn; try easy.
      assert (Hneq: anyf <> f).
      {
        intro Heq.
        subst anyf.
        assert (Heq_assign : Final = Assignable).
        {
          eapply sf_assignability_consistent_subtype; [exact Hclasstable | exact base | exact Hfinal | exact Hassign_rel].
        }
        discriminate.
      }
      injection Hobj_before as Hvals_eq.
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
      rewrite Hstatic_type in Hget_x.
      inversion Hget_x.
      subst Tx.
      unfold vpa_assignability in Hassignable.
      destruct a0 eqn: Haeqn; try easy.
      assert (Hneq: anyf <> f).
      {
        intro Heq.
        subst anyf.
        assert (Heq_assign : RDA = Assignable).
        {
          eapply sf_assignability_consistent_subtype; [exact Hclasstable | exact base | exact Hrda | exact Hassign_rel].
        }
        discriminate.
      }
      injection Hobj_before as Hvals_eq.
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
    inversion Hobj_before.
    rewrite H1 in base.
    simpl in base.

    (* Use the fact that Final/RDA fields are protected from modification *)
    destruct Hassign as [Hfinal | Hrda].
    --  
      rewrite Hstatic_type in Hget_x.
      inversion Hget_x.
      subst Tx.
      (* rewrite Hstatic_type in H16. *)
      unfold vpa_assignability in Hassignable.
      destruct a0 eqn: Haeqn; try easy.
      assert (Hneq: anyf <> f).
      {
        intro Heq.
        subst anyf.
        assert (Heq_assign : Final = Assignable).
        {
          eapply sf_assignability_consistent_subtype; [exact Hclasstable | exact base | exact Hfinal | exact Hassign_rel].
        }
        discriminate.
      }
      injection Hobj_before as Hvals_eq.
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
      rewrite Hstatic_type in Hget_x.
      inversion Hget_x.
      subst Tx.
      unfold vpa_assignability in Hassignable.
      destruct a0 eqn: Haeqn; try easy.
      assert (Hneq: anyf <> f).
      {
        intro Heq.
        subst anyf.
        assert (Heq_assign : RDA = Assignable).
        {
          eapply sf_assignability_consistent_subtype; [exact Hclasstable | exact base | exact Hrda | exact Hassign_rel].
        }
        discriminate.
      }
      injection Hobj_before as Hvals_eq.
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

Definition all_params_safe (msig : method_sig) : Prop :=
  is_safe_mode (sqtype (mreceiver msig)) /\
  Forall (fun T => is_safe_mode (sqtype T)) (mparams msig).

Definition reachable_locations_from_vals
  (CT : class_table) (h : heap) (vals : list value) : Ensembles.Ensemble Loc :=
  fun l_target => 
    exists l_root,
      In (Iot l_root) vals /\
      reachable h l_root l_target.

Definition protected_locations_from_vals
  (CT : class_table) (h : heap) (vals : list value) : Ensembles.Ensemble Loc :=
  fun l_target => 
    exists l_root,
      In (Iot l_root) vals /\
      reachable_abs CT h l_root l_target.

Lemma reachable_abs_implies_reachable :
  forall CT h l_src l_dst
    (Hreach : reachable_abs CT h l_src l_dst),
    reachable h l_src l_dst.
Proof.
  intros CT h l_src l_dst Hreach.
  induction Hreach.
  - (* Base case: reachable_abs_heap *)
    apply rch_heap; exact Hdom.
  - (* Step case: reachable_abs_step *)
    eapply rch_step; eauto.
  - (* Trans case *)
    eapply rch_trans; eauto.
Qed.

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

Lemma protected_locations_subset_reachable_from_method_frame :
  forall CT h ly vals,
    let rΓmethodinit := {| vars := Iot ly :: vals |} in
    Ensembles.Included Loc
      (protected_locations_from_vals CT h (Iot ly :: vals))
      (reachable_locations_from_initial_env CT h rΓmethodinit).
Proof.
  intros CT h ly vals rΓmethodinit l Hin.
  unfold protected_locations_from_vals in Hin.
  destruct Hin as [l_root [Hin_list Hreach]].
  unfold reachable_locations_from_initial_env.
  (* l_root is in (Iot ly :: vals), so either l_root = ly or l_root is in vals *)
  destruct Hin_list as [Heq | Hin_vals].
  - (* Case: Iot l_root = Iot ly *)
    inversion Heq; subst l_root.
    exists 0, ly.
    split.
    -- unfold runtime_getVal. simpl. reflexivity.
    -- exact (reachable_abs_implies_reachable CT h ly l Hreach).
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
    -- exact (reachable_abs_implies_reachable CT h l_root l Hreach).
Qed.

Theorem readonly_method_call_preserves_arguments :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ' x y mindex Ty mdef zs anyC vals ly 
         loc_arg C anyrq vals_arg vals_arg' f
    (Hstmt : stmt = (SCall x mindex y zs))
    (HTy : Ty = Build_qualified_type RO anyC)
    (Hstatic_type : static_getType sΓ y = Some Ty)
    (Hmethod_lookup : FindMethodWithName CT (sctype Ty) mindex mdef)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Hmtype: mt <> AbstractImm)
    (Heval : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h')
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
  exfalso; apply Hmtype; reflexivity.
  rename sΓ' into sΓ.
  have HTy: Ty = {| sqtype := RO; sctype := anyC |}.
  {
    rewrite Hget_y0 in Hstatic_type.
    inversion Hstatic_type.
    reflexivity.
  }

  have Hmdefeq: mdef1 = mdef.
  {
    rewrite <- HTy in Hmethod_lookup.
    unfold wf_r_config in Hwf.
    destruct Hwf as [HClassTable _].
    unfold wf_senv in Hwf0.
    destruct Hwf0 as [Hwf0 Hwftypeuse].
    eapply find_overriding_method_deterministic; eauto.
    eapply Forall_nth_error in Hwftypeuse; eauto.
    unfold wf_stypeuse in Hwftypeuse.
    destruct (bound CT (sctype Ty)) eqn: Hbound.
    unfold bound in Hbound.
    destruct (find_class CT (sctype Ty)) eqn:Hfindclass; [|discriminate].
    apply find_class_dom in Hfindclass; auto.
    easy.
  }
  subst mdef1.
  rename mdef into mdef1.
  rename mdef0 into mdef.

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
    destruct Hwfmethod as [sΓmethodend [mbodyreturntype [Hmethodbody_typing [HmethodReturnBound [HmethodReturnType [HmethodReturnSubtype HMethodoverride]]]]]];
    remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit;
    remember {| vars := Iot ly :: vals |} as rΓmethodinit;
    remember (rΓ <| vars := update x retval (vars rΓ) |>) as rΓ'''.
    remember {| sqtype := RO; sctype := anyC |} as Ty. 
    assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
    {
      (* Method inner config wellformed.*)
        have Hclass := Hclasstable.
        unfold  wf_class_table in Hclass.
        destruct Hclass as [Hclass [Hobjexist [Hotherclasses Hcname_consistent]]].
        repeat split.
        exact Hclass.
        exact Hobjexist.
        exact Hotherclasses.
        apply Hcname_consistent.
        apply Hcname_consistent.
        exact Hheap.
        rewrite HeqrΓmethodinit.
        simpl.
        lia.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
        exists ly.
        split.
        rewrite HeqrΓmethodinit.
        simpl.
        reflexivity.
        unfold runtime_getVal in Hval_y.
        eapply Forall_nth_error in Hallvals; eauto.
        simpl in Hallvals.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjly; [|contradiction].
        apply runtime_getObj_dom in Hobjly.
        exact Hobjly.

        (* Inner runtime env is wellformed *)
        rewrite HeqrΓmethodinit.
        simpl.
        constructor.
        simpl.
        unfold runtime_getVal in Hval_y.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [_ Hallvals]].
        eapply Forall_nth_error in Hallvals; eauto.
        simpl in Hallvals.
        exact Hallvals.
        eapply runtime_lookup_list_preserves_wf_values with (zs := zs) (vals0:=vals); eauto.

        (* Inner Static Environment's length is more than 0 *)
        rewrite HeqsΓmethodinit.
        simpl.
        lia.

        (* Inner static env's elements are wellformed typeuse *)
        rewrite HeqsΓmethodinit.
        constructor.

        (* Receiver type is well-formed *)
        eapply method_sig_wf_receiver_by_find; eauto.
        assert (Hcydom: cy < dom CT). {
            eapply find_class_dom; eauto.
        }
        exact Hcydom.
        eapply method_sig_wf_parameters_by_find; eauto.
        assert (Hcydom: cy < dom CT). {
            eapply find_class_dom; eauto.
        }
        exact Hcydom.

        apply static_getType_list_preserves_length in Hget_args.
        apply runtime_lookup_list_preserves_length in Hargs.
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        simpl.
        f_equal.
        apply Forall2_length in Harg_sub.
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in Hget_y0.
          exact Hget_y0.
        }
        assert (HOutterReceiverAddr: exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
        {
          eapply get_this_exists_from_wf_r_config; eauto.
        }
        destruct HOutterReceiverAddr as [lOutterReceiver HOutterReceiverAddr].
        assert (HOutterReceiverMutability: exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
        {
          eapply receiver_mutability_exists_wf_renv; eauto.
        }
        destruct HOutterReceiverMutability as [OutterReceiverMutability HOutterReceiverMutabilityType].
        have Hcorr := Htypable.
        have Hcorrcopy := Hcorr.
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty Hget_y0).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in Hbase.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection Hbase as Hcy_eq.
        subst cy.
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot _]].
        unfold get_this_var_mapping.
        unfold gget in Hget_iot.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].

        unfold r_type in Hcorr.
        rewrite Hval_y in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
        assert (Hmsigeq : msignature mdef = msignature mdef1).
        {
          eapply method_signature_consistent_subtype with (C := rc_obj) (D := sctype Ty) (m := mindex); eauto.
        }
        rewrite Hmsigeq.
        rewrite Hargs.
        rewrite <- Harg_sub.
        exact Hget_args.

        (* Correspondence holds for inner environment *)
        intros ι qinner HreceiverAddr Hqcontext i Hi sqt Hnth.
        rewrite HeqsΓmethodinit in Hnth, Hi.
        rewrite HeqrΓmethodinit.
        simpl in *.
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in Hget_y0.
          exact Hget_y0.
        }
        assert (HOutterReceiverAddr: exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
        {
          eapply get_this_exists_from_wf_r_config; eauto.
        }
        destruct HOutterReceiverAddr as [lOutterReceiver HOutterReceiverAddr].
        assert (HOutterReceiverMutability: exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
        {
          eapply receiver_mutability_exists_wf_renv; eauto.
        }
        destruct HOutterReceiverMutability as [OutterReceiverMutability HOutterReceiverMutabilityType].
        have Hcorr := Htypable.
        have Hcorrcopy := Hcorr.
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty Hget_y0).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in Hbase.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection Hbase as Hcy_eq.
        subst cy.
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        have Hrenvcopy := Hrenv.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot _]].
        unfold get_this_var_mapping.
        unfold gget in Hget_iot.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].

        unfold r_type in Hcorr.
        rewrite Hval_y in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
        
        assert (Hmsigeq: msignature mdef = msignature mdef1).
        {
          eapply method_signature_consistent_subtype with (C := rc_obj) (D := sctype Ty) (m := mindex); eauto.
        }
        destruct i as [|i'].

        (* Reciever index - 0 *)
        simpl in Hnth.
        injection Hnth as Hsqt_eq.
        subst sqt.
        simpl.
        unfold wf_r_typable.
        unfold r_type.

        rewrite Hobjy.
        simpl.
        split.

        (* Base type subtyping *)
        rewrite Hmsigeq.
        destruct Hrcv_sub as [Hrcv_sub | Hrcv_sub].
        apply qualified_type_subtype_base_subtype in Hrcv_sub.
        rewrite (vpa_mutabilty_tt_sctype_safe_ro Ty (mreceiver (msignature mdef1))) in Hrcv_sub.
        eapply base_trans; eauto.
        destruct Hrcv_sub as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
        eapply base_trans; eauto.

        (* Qualifier typbility *)
        1: 
        {
          destruct Hrcv_sub as [Hrcv_sub | Hrcv_sub].
          1:{
            apply qualified_type_subtype_q_subtype in Hrcv_sub.
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            apply get_this_qualified_type_nth_error in Hthis.
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            specialize (Hcorrcopy 0 Hsenvdom Tthis Hthis).
            rewrite <- Hvars in HOutterReceiverAddr.
            apply get_this_var_mapping_runtime_getVal in HOutterReceiverAddr.
            rewrite HOutterReceiverAddr in Hcorrcopy.
            unfold wf_r_typable in Hcorrcopy.
            unfold r_type in Hcorrcopy.
            destruct (runtime_getObj h lOutterReceiver) as [outterreceiverobj|] eqn:Houtterobj; [|easy].
            destruct Hcorrcopy as [_ Houtter_qualifier_typable].

            assert (rqtype (rt_type outterreceiverobj) = OutterReceiverMutability).
            {
              unfold r_muttype in HOutterReceiverMutabilityType.
              rewrite Houtterobj in HOutterReceiverMutabilityType.
              simpl in HOutterReceiverMutabilityType.
              inversion HOutterReceiverMutabilityType; subst OutterReceiverMutability.
              reflexivity.
            }
            subst OutterReceiverMutability.

            assert (ly = ι). 
            {
              rewrite HeqrΓmethodinit in HreceiverAddr.
              unfold get_this_var_mapping in HreceiverAddr.
              simpl in HreceiverAddr.
              inversion HreceiverAddr; reflexivity.
            }
            subst ι.

            assert (Hmut_ly : r_muttype h ly = Some rq_obj).
            {
              unfold r_muttype.
              rewrite Hobjy.
              simpl.
              reflexivity.
            }

            assert (rq_obj = qinner).
            {
              rewrite Hmut_ly in Hqcontext.
              inversion Hqcontext; subst qinner.
              reflexivity.
            }
            subst rq_obj.

            unfold qualifier_typable_context.
            unfold qualifier_typable_context in HyQualifierTypablility.
            unfold qualifier_typable_context in Houtter_qualifier_typable.
            unfold vpa_mutabilty_rs.
            unfold vpa_mutabilty_rs in HyQualifierTypablility.
            unfold vpa_mutabilty_rs in Houtter_qualifier_typable.
            unfold vpa_mutabilty_tt_safe_ro in Hrcv_sub.
            rewrite <- Hmsigeq in Hrcv_sub.

            destruct qinner eqn:HInnerReceiverMutability;
            destruct (sqtype (mreceiver (msignature mdef))) eqn:HMethodReceiverDeclaredType;
            try trivial.
            all: destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            destruct (sqtype Ty) eqn:HTyStaticMutability;
            try trivial.
            all: destruct (sqtype Tthis) eqn:HTthisStaticMutability;
            try rewrite HTyStaticMutability in Hrcv_sub;
            simpl in Hrcv_sub;
            try rewrite HMethodReceiverDeclaredType in Hrcv_sub;
            try inversion Hrcv_sub; try trivial.
            all: try inversion Hrcv_sub; try easy.
          }
          1:{
            destruct Hrcv_sub as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            apply get_this_qualified_type_nth_error in Hthis.
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            specialize (Hcorrcopy 0 Hsenvdom Tthis Hthis).
            rewrite <- Hvars in HOutterReceiverAddr.
            apply get_this_var_mapping_runtime_getVal in HOutterReceiverAddr.
            rewrite HOutterReceiverAddr in Hcorrcopy.
            unfold wf_r_typable in Hcorrcopy.
            unfold r_type in Hcorrcopy.
            destruct (runtime_getObj h lOutterReceiver) as [outterreceiverobj|] eqn:Houtterobj; [|easy].
            destruct Hcorrcopy as [_ Houtter_qualifier_typable].

            assert (rqtype (rt_type outterreceiverobj) = OutterReceiverMutability).
            {
              unfold r_muttype in HOutterReceiverMutabilityType.
              rewrite Houtterobj in HOutterReceiverMutabilityType.
              simpl in HOutterReceiverMutabilityType.
              inversion HOutterReceiverMutabilityType; subst OutterReceiverMutability.
              reflexivity.
            }
            subst OutterReceiverMutability.

            assert (ly = ι). 
            {
              rewrite HeqrΓmethodinit in HreceiverAddr.
              unfold get_this_var_mapping in HreceiverAddr.
              simpl in HreceiverAddr.
              inversion HreceiverAddr; reflexivity.
            }
            subst ι.

            assert (Hmut_ly : r_muttype h ly = Some rq_obj).
            {
              unfold r_muttype.
              rewrite Hobjy.
              simpl.
              reflexivity.
            }

            assert (rq_obj = qinner).
            {
              rewrite Hmut_ly in Hqcontext.
              inversion Hqcontext; subst qinner.
              reflexivity.
            }
            subst rq_obj.

            unfold qualifier_typable_context.
            unfold qualifier_typable_context in HyQualifierTypablility.
            unfold qualifier_typable_context in Houtter_qualifier_typable.
            unfold vpa_mutabilty_rs.
            unfold vpa_mutabilty_rs in HyQualifierTypablility.
            unfold vpa_mutabilty_rs in Houtter_qualifier_typable.
            rewrite <- Hmsigeq in HReceiverDeclearedQualifier.

            rewrite HReceiverDeclearedQualifier.
            destruct qinner eqn:HInnerReceiverMutability;
            try trivial.
          }
        }

        (* -------------------------------------------------- *)
        (* Other index - > 1 *)
        unfold runtime_getVal.
        simpl.
        destruct (nth_error vals i') as [v|] eqn:Hval_i.
          - (* Parameter i' exists *)
            destruct v as [|loc]; [trivial|].
            assert (Hi'_bound : i' < List.length argtypes).
            {
              apply Forall2_length in Harg_sub.
              simpl in Hi.
              simpl in Hnth.
              rewrite Hmsigeq in Hnth.
              rewrite Harg_sub.
              apply nth_error_Some.
              intros Hnone.
              rewrite Hnth in Hnone.
              discriminate.
            }
            assert (Harg_type : exists argtype, nth_error argtypes i' = Some argtype).
            {
              apply nth_error_Some_exists.
              exact Hi'_bound.
            }
            assert (loc < dom h).
            {
              assert (Hvals_wf :
              Forall
                (fun v =>
                  match v with
                  | Null_a => True
                  | Iot loc =>
                      match runtime_getObj h loc with
                      | Some _ => True
                      | None => False
                      end
                  end) vals).
              {
                eapply runtime_lookup_list_preserves_wf_values; eauto.
              }
              eapply Forall_nth_error in Hvals_wf; eauto.
              simpl in Hvals_wf.
              destruct (runtime_getObj h loc) as [argobj|] eqn:Hargobjloc; [|contradiction].
              apply runtime_getObj_dom in Hargobjloc.
              exact Hargobjloc.
            }
            destruct Harg_type as [argtype Hargtype].
            unfold wf_r_typable.
            unfold r_type.
            destruct (runtime_getObj h loc) as [argobj|] eqn:Hargobjloc; [|apply runtime_getObj_not_dom in Hargobjloc; lia].
            assert (HargtypeFromsEnv :
              exists iArgInSenv,
                nth_error sΓ iArgInSenv = Some argtype
            /\ nth_error zs i' = Some iArgInSenv).
            {
              destruct (static_getType_list_nth_zs sΓ zs argtypes i' argtype Hget_args Hargtype)
                as [j [Hzs_j Hst_j]].
              exists j.
              split.
              - (* from static_getType to nth_error sΓ' *)
                unfold static_getType in Hst_j; exact Hst_j.
              - (* keep the zs fact *)
                exact Hzs_j.
            }
            destruct HargtypeFromsEnv as [iArgInSenv [HargtypeFromsEnv Hzs_iArg]].

            assert (Hi'dom : iArgInSenv < dom sΓ).
            {
              apply nth_error_Some.
              rewrite HargtypeFromsEnv; discriminate.
            }
            assert (HargtypeFromrEnv :
                      nth_error (vars rΓ) iArgInSenv = Some (Iot loc)).
            {
              destruct (runtime_lookup_list_nth_zs rΓ zs vals i' (Iot loc) Hargs Hval_i)
                as [j [Hzs_j Hget_j]].
              assert (HiEq : iArgInSenv = j).
              {
                (* zs[i'] = Some iArgInSenv and zs[i'] = Some j ⇒ iArgInSenv = j *)
                rewrite Hzs_iArg in Hzs_j.
                inversion Hzs_j; reflexivity.
              }
              subst iArgInSenv.
              unfold runtime_getVal in Hget_j.
              exact Hget_j.
            }
            have Hcorrcopy_2 := Hcorrcopy.
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType iArgInSenv Hi'dom argtype HargtypeFromsEnv).
            unfold runtime_getVal in Hcorrcopy.
            rewrite HargtypeFromrEnv in Hcorrcopy.
            unfold wf_r_typable in Hcorrcopy.
            unfold r_type in Hcorrcopy.
            rewrite Hargobjloc in Hcorrcopy.
            destruct Hcorrcopy as [Harg_basesubtype Harg_qualifiertypability].
            split.

            (* base subtype *)
            rewrite nth_error_cons_succ in Hnth.
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in Harg_sub; eauto.
            apply qualified_type_subtype_base_subtype in Harg_sub.
            rewrite (vpa_mutabilty_tt_sctype_safe_ro Ty sqt) in Harg_sub.
            eapply base_trans; eauto.

            (* Qualifier Typability *)
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in Harg_sub; eauto.
            apply qualified_type_subtype_q_subtype in Harg_sub.
            rewrite sq_vpa_tt_eq_qq_safe_ro in Harg_sub.
            specialize (Hcorrcopy_2 lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            apply get_this_qualified_type_nth_error in Hthis.
            specialize (Hcorrcopy_2 0 Hsenvdom Tthis Hthis).
            rewrite <- Hvars in Hget_iot.
            apply get_this_var_mapping_runtime_getVal in Hget_iot.
            rewrite Hget_iot in Hcorrcopy_2.
            unfold wf_r_typable in Hcorrcopy_2.
            unfold r_type in Hcorrcopy_2.
            destruct (runtime_getObj h iot) as [outterreceiverobj|] eqn:Houtterobj; [|easy].
            destruct Hcorrcopy_2 as [_ HOutterReceiverQualifierTypablility].
            assert (rqtype (rt_type outterreceiverobj) = OutterReceiverMutability).
            {
              clear - Houtterobj HOutterReceiverMutabilityType HOutterReceiverAddr Hget_iot Hvars.
              rewrite <- Hvars in HOutterReceiverAddr.
              apply get_this_var_mapping_runtime_getVal in HOutterReceiverAddr.
              rewrite Hget_iot in HOutterReceiverAddr.
              inversion HOutterReceiverAddr; subst lOutterReceiver.
              unfold r_muttype in HOutterReceiverMutabilityType.
              rewrite Houtterobj in HOutterReceiverMutabilityType.
              simpl in HOutterReceiverMutabilityType.
              inversion HOutterReceiverMutabilityType; reflexivity.
            }
            subst OutterReceiverMutability.
            assert (ι = ly).
            {
              unfold get_this_var_mapping in HreceiverAddr.
              rewrite HeqrΓmethodinit in HreceiverAddr.
              simpl in HreceiverAddr.
              inversion HreceiverAddr; reflexivity.
            }
            subst ι.
            assert(rq_obj = qinner).
            {
              unfold r_muttype in Hqcontext.
              rewrite Hobjy in Hqcontext.
              simpl in Hqcontext.
              inversion Hqcontext.
              easy.
            }
            subst rq_obj.
            clear - Harg_sub Harg_qualifiertypability HyQualifierTypablility HOutterReceiverQualifierTypablility Ty.

            destruct (rqtype (rt_type argobj)) eqn:Hargobjmutability; move Hargobjmutability at bottom;
            destruct (sqtype sqt) eqn:HParameterStaticDeclearedMutability; move HParameterStaticDeclearedMutability at bottom;
            destruct qinner eqn:HInnerReceiverMutability; move HInnerReceiverMutability at bottom;
            try solve_qualifier_typable_correct_concrete.

            all: destruct (sqtype Ty) eqn:HTyStaticMutability;
            destruct (sqtype argtype) eqn:HArgTypeStaticMutability;
            simpl in Harg_sub;
            try solve_q_subtype_wrong.

            all: 
            destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            try solve_qualifier_typable_wrong_concrete.

          - (* Parameter i' doesn't exist - contradiction *)
            exfalso.
            apply nth_error_None in Hval_i.
            apply runtime_lookup_list_preserves_length in Hargs.
            apply static_getType_list_preserves_length in Hget_args.
            apply Forall2_length in Harg_sub.
            rewrite Hargs in Hval_i.
            rewrite <- Hget_args in Hval_i.
            rewrite Harg_sub in Hval_i.
            simpl in Hi.
            simpl in Hnth.
            rewrite <- Hmsigeq in Hval_i.
            lia.
    }

    eapply deep_readonly_preservation with (stmt := (mbody_stmt mbody)) (sΓ' := sΓmethodend) (mt:=(mtype (msignature mdef))); eauto.
    assert (HenvImpliesEnvRespect: env_respects_protected_set (reachable_locations_from_initial_env CT h rΓmethodinit) sΓmethodinit rΓmethodinit).
    {
      eapply confinement_from_all_readonly_env; eauto.
      assert (Hy_dom : y < dom sΓ).
      {
        apply static_getType_dom in Hget_y0.
        exact Hget_y0.
      }
      assert (HOutterReceiverAddr: exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
      {
        eapply get_this_exists_from_wf_r_config; eauto.
      }
      destruct HOutterReceiverAddr as [lOutterReceiver HOutterReceiverAddr].
      assert (HOutterReceiverMutability: exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
      {
        eapply receiver_mutability_exists_wf_renv; eauto.
      }
      destruct HOutterReceiverMutability as [OutterReceiverMutability HOutterReceiverMutabilityType].
      have Hcorr := Htypable.
      have Hcorrcopy := Hcorr.
      specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty Hget_y0).
      unfold wf_r_typable in Hcorr.
      unfold r_basetype in Hbase.
      unfold r_type.
      destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
      injection Hbase as Hcy_eq.
      subst cy.
      destruct obj as [rt_obj fields_obj].
      destruct rt_obj as [rq_obj rc_obj].

      unfold wf_renv in Hrenv.
      destruct Hrenv as [_ [Hreceiver _]].
      destruct Hreceiver as [iot [Hget_iot _]].
      unfold get_this_var_mapping.
      unfold gget in Hget_iot.
      destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].

      unfold r_type in Hcorr.
      rewrite Hval_y in Hcorr.
      rewrite Hobjy in Hcorr.
      simpl in Hcorr.
      destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
      assert (Hmsigeq: msignature mdef = msignature mdef1).
      {
        eapply method_signature_consistent_subtype with (C := rc_obj) (D := sctype Ty) (m := mindex); eauto.
      }
      intros y0 T Hlookup_s.
      unfold static_getType in Hlookup_s.
      simpl in Hlookup_s.
      rewrite HeqsΓmethodinit in Hlookup_s.
      simpl in Hlookup_s.
      destruct y0 as [|y0'].
      - (* Case: y0 = 0 (receiver) *)
        simpl in Hlookup_s.
        injection Hlookup_s as <-.
        unfold all_params_safe in Hall_readonly.
        destruct Hall_readonly as [Hreceiver_safe _].
        rewrite Hmsigeq.
        exact Hreceiver_safe.
      - (* Case: y0 = S y0' (a parameter) *)
        simpl in Hlookup_s.
        unfold all_params_safe in Hall_readonly.
        destruct Hall_readonly as [_ Hall_params].
        rewrite Hmsigeq in Hlookup_s.
        eapply Forall_nth_error in Hall_params; eauto.
    }
    exact HenvImpliesEnvRespect.
    rewrite getmbody; auto.
    assert (Hy_dom : y < dom sΓ).
    {
      apply static_getType_dom in Hget_y0.
      exact Hget_y0.
    }
    assert (HOutterReceiverAddr: exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
    {
      eapply get_this_exists_from_wf_r_config; eauto.
    }
    destruct HOutterReceiverAddr as [lOutterReceiver HOutterReceiverAddr].
    assert (HOutterReceiverMutability: exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
    {
      eapply receiver_mutability_exists_wf_renv; eauto.
    }
    destruct HOutterReceiverMutability as [OutterReceiverMutability HOutterReceiverMutabilityType].
    have Hcorr := Htypable.
    have Hcorrcopy := Hcorr.
    specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty Hget_y0).
    unfold wf_r_typable in Hcorr.
    unfold r_basetype in Hbase.
    unfold r_type.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
    injection Hbase as Hcy_eq.
    subst cy.
    destruct obj as [rt_obj fields_obj].
    destruct rt_obj as [rq_obj rc_obj].

    unfold wf_renv in Hrenv.
    destruct Hrenv as [_ [Hreceiver _]].
    destruct Hreceiver as [iot [Hget_iot _]].
    unfold get_this_var_mapping.
    unfold gget in Hget_iot.
    destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].

    unfold r_type in Hcorr.
    rewrite Hval_y in Hcorr.
    rewrite Hobjy in Hcorr.
    simpl in Hcorr.
    destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
    assert (Hmsigeq:msignature mdef = msignature mdef1).
    {
      eapply method_signature_consistent_subtype with (C := rc_obj) (D := sctype Ty) (m := mindex); eauto.
    }
    rewrite Hmsigeq; exact Hmt_not_abs.
    have Hsubset := reachable_locations_subset_reachable_from_method_frame CT h ly vals.
    rewrite <- HeqrΓmethodinit in Hsubset.
    unfold Ensembles.Included in Hsubset.
    exact (Hsubset loc_arg HinP).
  +
    assert (Hwfmethod: exists D ddef, base_subtype CT cy D /\ find_class CT D = Some ddef /\ In mdef (methods (body ddef)) /\ wf_method CT D mdef).
    {
      eapply method_lookup_in_wellformed_inherited; eauto.
      eapply r_basetype_in_dom; eauto.
    }
    destruct Hwfmethod as [D Hwfmethod].
    destruct Hwfmethod as [ddef Hwfmethod].
    destruct Hwfmethod as [Hbasecyd [HfindD [HmdefinD Hwfmethod]]].

    unfold wf_method in Hwfmethod;
    destruct Hwfmethod as [sΓmethodend [mbodyreturntype [Hmethodbody_typing [HmethodReturnBound [HmethodReturnType [HmethodReturnSubtype HMethodoverride]]]]]];
    remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit;
    remember {| vars := Iot ly :: vals |} as rΓmethodinit;
    remember (rΓ <| vars := update x retval (vars rΓ) |>) as rΓ'''.
    remember {| sqtype := RO; sctype := anyC |} as Ty. 
    assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
    {
      (* Method inner config wellformed.*)
        have Hclass := Hclasstable.
        unfold  wf_class_table in Hclass.
        destruct Hclass as [Hclass [Hobjexist [Hotherclasses Hcname_consistent]]].
        repeat split.
        exact Hclass.
        exact Hobjexist.
        exact Hotherclasses.
        apply Hcname_consistent.
        apply Hcname_consistent.
        exact Hheap.
        rewrite HeqrΓmethodinit.
        simpl.
        lia.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
        exists ly.
        split.
        rewrite HeqrΓmethodinit.
        simpl.
        reflexivity.
        unfold runtime_getVal in Hval_y.
        eapply Forall_nth_error in Hallvals; eauto.
        simpl in Hallvals.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjly; [|contradiction].
        apply runtime_getObj_dom in Hobjly.
        exact Hobjly.

        (* Inner runtime env is wellformed *)
        rewrite HeqrΓmethodinit.
        simpl.
        constructor.
        simpl.
        unfold runtime_getVal in Hval_y.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [_ Hallvals]].
        eapply Forall_nth_error in Hallvals; eauto.
        simpl in Hallvals.
        exact Hallvals.
        eapply runtime_lookup_list_preserves_wf_values with (zs:= zs) (vals0:=vals); eauto.

        (* Inner Static Environment's length is more than 0 *)
        rewrite HeqsΓmethodinit.
        simpl.
        lia.

        (* Inner static env's elements are wellformed typeuse *)
        rewrite HeqsΓmethodinit.
        constructor.

        (* Receiver type is well-formed *)
        eapply method_sig_wf_receiver_by_find; eauto.
        (* assert (Hcydom: cy < dom CT). {
            eapply find_class_dom; eauto.
        }
        exact Hcydom. *)
        assert (Hparentdom: parent < dom CT). {
          assert (cy < dom CT). {
            eapply find_class_dom; eauto.
          }
          assert (parent < cy). {
            eapply parent_implies_strict_ordering with (C:= cy) (D:=parent); eauto.
          }
          lia.
        }
        exact Hparentdom. 
        eapply method_sig_wf_parameters_by_find; eauto.
        assert (Hparentdom: parent < dom CT). {
          assert (cy < dom CT). {
            eapply find_class_dom; eauto.
          }
          assert (parent < cy). {
            eapply parent_implies_strict_ordering with (C:= cy) (D:=parent); eauto.
          }
          lia.
        }
        exact Hparentdom. 
        apply static_getType_list_preserves_length in Hget_args.
        apply runtime_lookup_list_preserves_length in Hargs.
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        simpl.
        f_equal.
        apply Forall2_length in Harg_sub.
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in Hget_y0.
          exact Hget_y0.
        }
        assert (HOutterReceiverAddr: exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
        {
          eapply get_this_exists_from_wf_r_config; eauto.

        }
        destruct HOutterReceiverAddr as [lOutterReceiver HOutterReceiverAddr].
        assert (HOutterReceiverMutability: exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
        {
          eapply receiver_mutability_exists_wf_renv; eauto.
        }
        destruct HOutterReceiverMutability as [OutterReceiverMutability HOutterReceiverMutabilityType].
        have Hcorr := Htypable.
        have Hcorrcopy := Hcorr.
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty Hget_y0).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in Hbase.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection Hbase as Hcy_eq.
        subst cy.
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot _]].
        unfold get_this_var_mapping.
        unfold gget in Hget_iot.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].

        unfold r_type in Hcorr.
        rewrite Hval_y in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
        assert (Hmsigeq : msignature mdef = msignature mdef1).
        {
          eapply method_signature_consistent_subtype with (C := rc_obj) (D := sctype Ty) (m := mindex); eauto.
        }
        rewrite Hmsigeq.
        rewrite Hargs.
        rewrite <- Harg_sub.
        exact Hget_args.

        (* Correspondence holds for inner environment *)
        intros ι qinner HreceiverAddr Hqcontext i Hi sqt Hnth.
        rewrite HeqsΓmethodinit in Hnth, Hi.
        rewrite HeqrΓmethodinit.
        simpl in *.
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in Hget_y0.
          exact Hget_y0.
        }
        assert (HOutterReceiverAddr: exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
        {
          eapply get_this_exists_from_wf_r_config; eauto.
        }
        destruct HOutterReceiverAddr as [lOutterReceiver HOutterReceiverAddr].
        assert (HOutterReceiverMutability: exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
        {
          eapply receiver_mutability_exists_wf_renv; eauto.
        }
        destruct HOutterReceiverMutability as [OutterReceiverMutability HOutterReceiverMutabilityType].
        have Hcorr := Htypable.
        have Hcorrcopy := Hcorr.
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty Hget_y0).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in Hbase.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection Hbase as Hcy_eq.
        subst cy.
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        have Hrenvcopy := Hrenv.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot _]].
        unfold get_this_var_mapping.
        unfold gget in Hget_iot.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].

        unfold r_type in Hcorr.
        rewrite Hval_y in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
        
        assert (Hmsigeq: msignature mdef = msignature mdef1).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        destruct i as [|i'].

        (* Reciever index - 0 *)
        simpl in Hnth.
        injection Hnth as Hsqt_eq.
        subst sqt.
        simpl.
        unfold wf_r_typable.
        unfold r_type.

        rewrite Hobjy.
        simpl.
        split.

        (* Base type subtyping *)
        rewrite Hmsigeq.
        destruct Hrcv_sub as [Hrcv_sub | Hrcv_sub].
        apply qualified_type_subtype_base_subtype in Hrcv_sub.
        (* rewrite (vpa_mutabilty_tt_sctype Tthis Ty) in Hrcv_sub. *)
        rewrite (vpa_mutabilty_tt_sctype_safe_ro Ty (mreceiver (msignature mdef1))) in Hrcv_sub.
        eapply base_trans; eauto.
        destruct Hrcv_sub as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
        eapply base_trans; eauto.

        (* Qualifier typbility *)
        1: 
        {
          destruct Hrcv_sub as [Hrcv_sub | Hrcv_sub].
          1:{
            apply qualified_type_subtype_q_subtype in Hrcv_sub.
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            apply get_this_qualified_type_nth_error in Hthis.
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            specialize (Hcorrcopy 0 Hsenvdom Tthis Hthis).
            rewrite <- Hvars in HOutterReceiverAddr.
            apply get_this_var_mapping_runtime_getVal in HOutterReceiverAddr.
            rewrite HOutterReceiverAddr in Hcorrcopy.
            unfold wf_r_typable in Hcorrcopy.
            unfold r_type in Hcorrcopy.
            destruct (runtime_getObj h lOutterReceiver) as [outterreceiverobj|] eqn:Houtterobj; [|easy].
            destruct Hcorrcopy as [_ Houtter_qualifier_typable].

            assert (rqtype (rt_type outterreceiverobj) = OutterReceiverMutability).
            {
              unfold r_muttype in HOutterReceiverMutabilityType.
              rewrite Houtterobj in HOutterReceiverMutabilityType.
              simpl in HOutterReceiverMutabilityType.
              inversion HOutterReceiverMutabilityType; subst OutterReceiverMutability.
              reflexivity.
            }
            subst OutterReceiverMutability.

            assert (ly = ι). 
            {
              rewrite HeqrΓmethodinit in HreceiverAddr.
              unfold get_this_var_mapping in HreceiverAddr.
              simpl in HreceiverAddr.
              inversion HreceiverAddr; reflexivity.
            }
            subst ι.

            assert (Hmut_ly : r_muttype h ly = Some rq_obj).
            {
              unfold r_muttype.
              rewrite Hobjy.
              simpl.
              reflexivity.
            }

            assert (rq_obj = qinner).
            {
              rewrite Hmut_ly in Hqcontext.
              inversion Hqcontext; subst qinner.
              reflexivity.
            }
            subst rq_obj.

            unfold qualifier_typable_context.
            unfold qualifier_typable_context in HyQualifierTypablility.
            unfold qualifier_typable_context in Houtter_qualifier_typable.
            unfold vpa_mutabilty_rs.
            unfold vpa_mutabilty_rs in HyQualifierTypablility.
            unfold vpa_mutabilty_rs in Houtter_qualifier_typable.
            unfold vpa_mutabilty_tt_safe_ro in Hrcv_sub.
            rewrite <- Hmsigeq in Hrcv_sub.

            destruct qinner eqn:HInnerReceiverMutability;
            destruct (sqtype (mreceiver (msignature mdef))) eqn:HMethodReceiverDeclaredType;
            try trivial.
            all: destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            destruct (sqtype Ty) eqn:HTyStaticMutability;
            try trivial.
            all: destruct (sqtype Tthis) eqn:HTthisStaticMutability;
            try rewrite HTyStaticMutability in Hrcv_sub;
            simpl in Hrcv_sub;
            try rewrite HMethodReceiverDeclaredType in Hrcv_sub;
            try inversion Hrcv_sub; try trivial.
            all: try inversion Hrcv_sub; try easy.
          }
          1:{
            destruct Hrcv_sub as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            apply get_this_qualified_type_nth_error in Hthis.
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            specialize (Hcorrcopy 0 Hsenvdom Tthis Hthis).
            rewrite <- Hvars in HOutterReceiverAddr.
            apply get_this_var_mapping_runtime_getVal in HOutterReceiverAddr.
            rewrite HOutterReceiverAddr in Hcorrcopy.
            unfold wf_r_typable in Hcorrcopy.
            unfold r_type in Hcorrcopy.
            destruct (runtime_getObj h lOutterReceiver) as [outterreceiverobj|] eqn:Houtterobj; [|easy].
            destruct Hcorrcopy as [_ Houtter_qualifier_typable].

            assert (rqtype (rt_type outterreceiverobj) = OutterReceiverMutability).
            {
              unfold r_muttype in HOutterReceiverMutabilityType.
              rewrite Houtterobj in HOutterReceiverMutabilityType.
              simpl in HOutterReceiverMutabilityType.
              inversion HOutterReceiverMutabilityType; subst OutterReceiverMutability.
              reflexivity.
            }
            subst OutterReceiverMutability.

            assert (ly = ι). 
            {
              rewrite HeqrΓmethodinit in HreceiverAddr.
              unfold get_this_var_mapping in HreceiverAddr.
              simpl in HreceiverAddr.
              inversion HreceiverAddr; reflexivity.
            }
            subst ι.

            assert (Hmut_ly : r_muttype h ly = Some rq_obj).
            {
              unfold r_muttype.
              rewrite Hobjy.
              simpl.
              reflexivity.
            }

            assert (rq_obj = qinner).
            {
              rewrite Hmut_ly in Hqcontext.
              inversion Hqcontext; subst qinner.
              reflexivity.
            }
            subst rq_obj.

            unfold qualifier_typable_context.
            unfold qualifier_typable_context in HyQualifierTypablility.
            unfold qualifier_typable_context in Houtter_qualifier_typable.
            unfold vpa_mutabilty_rs.
            unfold vpa_mutabilty_rs in HyQualifierTypablility.
            unfold vpa_mutabilty_rs in Houtter_qualifier_typable.
            rewrite <- Hmsigeq in HReceiverDeclearedQualifier.
            rewrite HReceiverDeclearedQualifier;
            destruct qinner eqn:HInnerReceiverMutability;
            try trivial.
          }
        }
        (* clear_dups. amazing.... *)

  (* -------------------------------------------------- *)
  (* Other index - > 1 *)
        unfold runtime_getVal.
        simpl.
        destruct (nth_error vals i') as [v|] eqn:Hval_i.
          - (* Parameter i' exists *)
            destruct v as [|loc]; [trivial|].
            (* Use Hrcv_sub to get the subtyping relationship *)
            assert (Hi'_bound : i' < List.length argtypes).
            {
              apply Forall2_length in Harg_sub.
              simpl in Hi.
              simpl in Hnth.
              rewrite Hmsigeq in Hnth.
              rewrite Harg_sub.
              apply nth_error_Some.
              intros Hnone.
              rewrite Hnth in Hnone.
              discriminate.
            }
            assert (Harg_type : exists argtype, nth_error argtypes i' = Some argtype).
            {
              apply nth_error_Some_exists.
              exact Hi'_bound.
            }
            assert (loc < dom h).
            {
              assert (Hvals_wf :
              Forall
                (fun v =>
                  match v with
                  | Null_a => True
                  | Iot loc =>
                      match runtime_getObj h loc with
                      | Some _ => True
                      | None => False
                      end
                  end) vals).
              {
                eapply runtime_lookup_list_preserves_wf_values; eauto.
              }
              eapply Forall_nth_error in Hvals_wf; eauto.
              simpl in Hvals_wf.
              destruct (runtime_getObj h loc) as [argobj|] eqn:Hargobjloc; [|contradiction].
              apply runtime_getObj_dom in Hargobjloc.
              exact Hargobjloc.
            }
            destruct Harg_type as [argtype Hargtype].
            unfold wf_r_typable.
            unfold r_type.
            destruct (runtime_getObj h loc) as [argobj|] eqn:Hargobjloc; [|apply runtime_getObj_not_dom in Hargobjloc; lia].
            assert (HargtypeFromsEnv :
              exists iArgInSenv,
                nth_error sΓ iArgInSenv = Some argtype
            /\ nth_error zs i' = Some iArgInSenv).
            {
              destruct (static_getType_list_nth_zs sΓ zs argtypes i' argtype Hget_args Hargtype)
                as [j [Hzs_j Hst_j]].
              exists j.
              split.
              - (* from static_getType to nth_error sΓ' *)
                unfold static_getType in Hst_j; exact Hst_j.
              - (* keep the zs fact *)
                exact Hzs_j.
            }
            destruct HargtypeFromsEnv as [iArgInSenv [HargtypeFromsEnv Hzs_iArg]].

            assert (Hi'dom : iArgInSenv < dom sΓ).
            {
              apply nth_error_Some.
              rewrite HargtypeFromsEnv; discriminate.
            }
            assert (HargtypeFromrEnv :
                      nth_error (vars rΓ) iArgInSenv = Some (Iot loc)).
            {
              destruct (runtime_lookup_list_nth_zs rΓ zs vals i' (Iot loc) Hargs Hval_i)
                as [j [Hzs_j Hget_j]].
              assert (HiEq : iArgInSenv = j).
              {
                (* zs[i'] = Some iArgInSenv and zs[i'] = Some j ⇒ iArgInSenv = j *)
                rewrite Hzs_iArg in Hzs_j.
                inversion Hzs_j; reflexivity.
              }
              subst iArgInSenv.
              unfold runtime_getVal in Hget_j.
              exact Hget_j.
            }
            have Hcorrcopy_2 := Hcorrcopy.
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType iArgInSenv Hi'dom argtype HargtypeFromsEnv).
            unfold runtime_getVal in Hcorrcopy.
            rewrite HargtypeFromrEnv in Hcorrcopy.
            unfold wf_r_typable in Hcorrcopy.
            unfold r_type in Hcorrcopy.
            rewrite Hargobjloc in Hcorrcopy.
            destruct Hcorrcopy as [Harg_basesubtype Harg_qualifiertypability].
            split.

            (* base subtype *)
            rewrite nth_error_cons_succ in Hnth.
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in Harg_sub; eauto.
            apply qualified_type_subtype_base_subtype in Harg_sub.
            rewrite (vpa_mutabilty_tt_sctype_safe_ro Ty sqt) in Harg_sub.
            eapply base_trans; eauto.

            (* Qualifier Typability *)
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in Harg_sub; eauto.
            apply qualified_type_subtype_q_subtype in Harg_sub.
            rewrite sq_vpa_tt_eq_qq_safe_ro in Harg_sub.
            specialize (Hcorrcopy_2 lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            apply get_this_qualified_type_nth_error in Hthis.
            specialize (Hcorrcopy_2 0 Hsenvdom Tthis Hthis).
            rewrite <- Hvars in Hget_iot.
            apply get_this_var_mapping_runtime_getVal in Hget_iot.
            rewrite Hget_iot in Hcorrcopy_2.
            unfold wf_r_typable in Hcorrcopy_2.
            unfold r_type in Hcorrcopy_2.
            destruct (runtime_getObj h iot) as [outterreceiverobj|] eqn:Houtterobj; [|easy].
            destruct Hcorrcopy_2 as [_ HOutterReceiverQualifierTypablility].
            assert (rqtype (rt_type outterreceiverobj) = OutterReceiverMutability).
            {
              clear - Houtterobj HOutterReceiverMutabilityType HOutterReceiverAddr Hget_iot Hvars.
              rewrite <- Hvars in HOutterReceiverAddr.
              apply get_this_var_mapping_runtime_getVal in HOutterReceiverAddr.
              rewrite Hget_iot in HOutterReceiverAddr.
              inversion HOutterReceiverAddr; subst lOutterReceiver.
              unfold r_muttype in HOutterReceiverMutabilityType.
              rewrite Houtterobj in HOutterReceiverMutabilityType.
              simpl in HOutterReceiverMutabilityType.
              inversion HOutterReceiverMutabilityType; reflexivity.
            }
            subst OutterReceiverMutability.
            assert (ι = ly).
            {
              unfold get_this_var_mapping in HreceiverAddr.
              rewrite HeqrΓmethodinit in HreceiverAddr.
              simpl in HreceiverAddr.
              inversion HreceiverAddr; reflexivity.
            }
            subst ι.
            assert(rq_obj = qinner).
            {
              unfold r_muttype in Hqcontext.
              rewrite Hobjy in Hqcontext.
              simpl in Hqcontext.
              inversion Hqcontext.
              easy.
            }
            subst rq_obj.
            clear - Harg_sub Harg_qualifiertypability HyQualifierTypablility HOutterReceiverQualifierTypablility.

            destruct (rqtype (rt_type argobj)) eqn:Hargobjmutability; move Hargobjmutability at bottom;
            destruct (sqtype sqt) eqn:HParameterStaticDeclearedMutability; move HParameterStaticDeclearedMutability at bottom;
            destruct qinner eqn:HInnerReceiverMutability; move HInnerReceiverMutability at bottom;
            try solve_qualifier_typable_correct_concrete.

            all: destruct (sqtype Ty) eqn:HTyStaticMutability;
            destruct (sqtype argtype) eqn:HArgTypeStaticMutability;
            simpl in Harg_sub;
            try solve_q_subtype_wrong.

            all: 
            destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            try solve_qualifier_typable_wrong_concrete.

          - (* Parameter i' doesn't exist - contradiction *)
            exfalso.
            apply nth_error_None in Hval_i.
            apply runtime_lookup_list_preserves_length in Hargs.
            apply static_getType_list_preserves_length in Hget_args.
            apply Forall2_length in Harg_sub.
            rewrite Hargs in Hval_i.
            rewrite <- Hget_args in Hval_i.
            rewrite Harg_sub in Hval_i.
            simpl in Hi.
            simpl in Hnth.
            rewrite <- Hmsigeq in Hval_i.
            lia.
    }
    eapply deep_readonly_preservation with (stmt := (mbody_stmt mbody)) (sΓ' := sΓmethodend) (mt:=(mtype (msignature mdef))); eauto.
    assert (HenvImpliesEnvRespect: env_respects_protected_set (reachable_locations_from_initial_env CT h rΓmethodinit) sΓmethodinit rΓmethodinit).
    {
      eapply confinement_from_all_readonly_env; eauto.
      assert (Hy_dom : y < dom sΓ).
      {
        apply static_getType_dom in Hget_y0.
        exact Hget_y0.
      }
      assert (HOutterReceiverAddr: exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
      {
        eapply get_this_exists_from_wf_r_config; eauto.
      }
      destruct HOutterReceiverAddr as [lOutterReceiver HOutterReceiverAddr].
      assert (HOutterReceiverMutability: exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
      {
        eapply receiver_mutability_exists_wf_renv; eauto.
      }
      destruct HOutterReceiverMutability as [OutterReceiverMutability HOutterReceiverMutabilityType].
      have Hcorr := Htypable.
      have Hcorrcopy := Hcorr.
      specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty Hget_y0).
      unfold wf_r_typable in Hcorr.
      unfold r_basetype in Hbase.
      unfold r_type.
      destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
      injection Hbase as Hcy_eq.
      subst cy.
      destruct obj as [rt_obj fields_obj].
      destruct rt_obj as [rq_obj rc_obj].

      unfold wf_renv in Hrenv.
      destruct Hrenv as [_ [Hreceiver _]].
      destruct Hreceiver as [iot [Hget_iot _]].
      unfold get_this_var_mapping.
      unfold gget in Hget_iot.
      destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].

      unfold r_type in Hcorr.
      rewrite Hval_y in Hcorr.
      rewrite Hobjy in Hcorr.
      simpl in Hcorr.
      destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
      assert (Hmsigeq: msignature mdef = msignature mdef1).
      {
        eapply method_signature_consistent_subtype with (C := rc_obj) (D := sctype Ty) (m := mindex); eauto.
      }
      intros y0 T Hlookup_s.
      unfold static_getType in Hlookup_s.
      simpl in Hlookup_s.
      rewrite HeqsΓmethodinit in Hlookup_s.
      simpl in Hlookup_s.
      destruct y0 as [|y0'].
      - (* Case: y0 = 0 (receiver) *)
        simpl in Hlookup_s.
        injection Hlookup_s as <-.
        unfold all_params_safe in Hall_readonly.
        destruct Hall_readonly as [Hreceiver_safe _].
        rewrite Hmsigeq.
        exact Hreceiver_safe.
      - (* Case: y0 = S y0' (a parameter) *)
        simpl in Hlookup_s.
        unfold all_params_safe in Hall_readonly.
        destruct Hall_readonly as [_ Hall_params].
        rewrite Hmsigeq in Hlookup_s.
        eapply Forall_nth_error in Hall_params; eauto.
    }
    exact HenvImpliesEnvRespect.
    rewrite getmbody; auto.
    assert (Hy_dom : y < dom sΓ).
    {
      apply static_getType_dom in Hget_y0.
      exact Hget_y0.
    }
    assert (HOutterReceiverAddr: exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
    {
      eapply get_this_exists_from_wf_r_config; eauto.
    }
    destruct HOutterReceiverAddr as [lOutterReceiver HOutterReceiverAddr].
    assert (HOutterReceiverMutability: exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
    {
      eapply receiver_mutability_exists_wf_renv; eauto.
    }
    destruct HOutterReceiverMutability as [OutterReceiverMutability HOutterReceiverMutabilityType].
    have Hcorr := Htypable.
    have Hcorrcopy := Hcorr.
    specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty Hget_y0).
    unfold wf_r_typable in Hcorr.
    unfold r_basetype in Hbase.
    unfold r_type.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
    injection Hbase as Hcy_eq.
    subst cy.
    destruct obj as [rt_obj fields_obj].
    destruct rt_obj as [rq_obj rc_obj].

    unfold wf_renv in Hrenv.
    destruct Hrenv as [_ [Hreceiver _]].
    destruct Hreceiver as [iot [Hget_iot _]].
    unfold get_this_var_mapping.
    unfold gget in Hget_iot.
    destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].

    unfold r_type in Hcorr.
    rewrite Hval_y in Hcorr.
    rewrite Hobjy in Hcorr.
    simpl in Hcorr.
    destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
    assert (Hmsigeq:msignature mdef = msignature mdef1).
    {
      eapply method_signature_consistent_subtype with (C := rc_obj) (D := sctype Ty) (m := mindex); eauto.
    }
    rewrite Hmsigeq; exact Hmt_not_abs.
    have Hsubset := reachable_locations_subset_reachable_from_method_frame CT h ly vals.
    rewrite <- HeqrΓmethodinit in Hsubset.
    unfold Ensembles.Included in Hsubset.
    exact (Hsubset loc_arg HinP).
  all: eauto.
Qed.
