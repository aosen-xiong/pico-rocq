Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation Properties.

From Stdlib Require Import List.
From Stdlib Require String.
Import ListNotations.

(* ------------------------------------------------------------- *)
Lemma callee_frame_wf_rs_ts :
  forall CT sΓ' rΓ h y m zs vals ly cy mdef mdef0 Ty argtypes Tthis
    (Hwf : wf_r_config CT sΓ' rΓ h)
    (Hval_y : runtime_getVal rΓ y = Some (Iot ly))
    (Hbase : r_basetype h ly = Some cy)
    (mdeflookup : FindMethodWithName CT cy m mdef)
    (Hfind_m : FindMethodWithName CT (sctype Ty) m mdef0)
    (Hget_y : static_getType sΓ' y = Some Ty)
    (Hget_args : static_getType_list sΓ' zs = Some argtypes)
    (Hthis : get_this_qualified_type sΓ' = Some Tthis)
    (Hargs : runtime_lookup_list rΓ zs = Some vals)
    (Hrcv_sub :
      qualified_type_subtype CT Ty
        (vpa_mutability_tt_safe_ro Ty (mreceiver (msignature mdef))) \/
      (sqtype Ty = RO /\ sqtype (mreceiver (msignature mdef)) = RDM /\
       base_subtype CT (sctype Ty) (sctype (mreceiver (msignature mdef)))))
    (Harg_sub :
      Forall2
        (fun arg T => qualified_type_subtype CT arg
          (vpa_mutability_tt_safe_ro Ty T))
        argtypes (mparams (msignature mdef))),
    wf_r_config CT
      (mreceiver (msignature mdef) :: mparams (msignature mdef))
      (mkr_env (Iot ly :: vals)) h.
Proof.
  intros CT sΓ' rΓ h y m zs vals ly cy mdef mdef0 Ty argtypes Tthis
    Hwf Hval_y Hbase mdeflookup Hfind_m Hget_y Hget_args Hthis Hargs
    Hrcv_sub Harg_sub.
  assert (Hmsigeq : msignature mdef = msignature mdef0).
  { eapply runtime_call_signature_agrees; eauto. }
  have Hwfcopy := Hwf.
  unfold wf_r_config in Hwf.
  destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
  remember (mreceiver (msignature mdef) :: mparams (msignature mdef))
    as sΓmethodinit.
  remember (mkr_env (Iot ly :: vals)) as rΓmethodinit.
  destruct (r_muttype h ly) eqn:Hinnerthis.
  2:{
    unfold r_muttype in Hinnerthis.
    unfold r_basetype in Hbase.
    destruct (runtime_getObj h ly); discriminate.
  }
 (* Method inner config wellformed.*)
  split; [exact Hclass|].
  repeat split.
  -
    exact Hheap.
  -
    rewrite HeqrΓmethodinit.
    simpl.
    lia.
  -
    unfold wf_renv in Hrenv.
    destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
    exists ly.
    split.
    --
    rewrite HeqrΓmethodinit.
    simpl.
    reflexivity.
    --
    unfold runtime_getVal in Hval_y.
    destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
    injection Hval_y as H1_eq.
    subst v.
    eapply Forall_nth_error in Hallvals; eauto.
    simpl in Hallvals.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjly; [|contradiction].
    apply runtime_getObj_dom in Hobjly.
    exact Hobjly.

  - (* Inner runtime env is wellformed*)
    rewrite HeqrΓmethodinit.
    simpl.
    constructor.
    simpl.
    unfold runtime_getVal in Hval_y.
    destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
    injection Hval_y as H1_eq.
    subst v.
    unfold runtime_getVal in Hnth_y.
    unfold wf_renv in Hrenv.
    destruct Hrenv as [_ [_ Hallvals]].
    eapply Forall_nth_error in Hallvals; eauto.
    simpl in Hallvals.
    exact Hallvals.
    eapply runtime_lookup_list_preserves_wf_values; eauto.
  -
    rewrite HeqsΓmethodinit.
    simpl.
    lia.

  - (* Inner static env's elements are wellformed typeuse *)
    rewrite HeqsΓmethodinit.
    constructor.
    subst.

    --  (* Receiver type is well-formed *)
    eapply method_sig_wf_receiver_by_find; eauto.
    unfold r_basetype in Hbase.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
    injection Hbase as H2_eq.
    destruct obj as [rt_obj fields_obj].
    destruct rt_obj as [rq_obj rc_obj].
    simpl.
    unfold wf_heap in Hheap.
    assert (Hly_dom : ly < dom h) by (apply runtime_getObj_dom in Hobjy; exact Hobjy).
    specialize (Hheap ly Hly_dom).
    unfold wf_obj in Hheap.
    rewrite Hobjy in Hheap.
    destruct Hheap as [Hwf_rtypeuse _].
    unfold wf_rtypeuse in Hwf_rtypeuse.
    simpl in Hwf_rtypeuse.
    destruct (bound CT rc_obj) as [class_def|] eqn:Hbound.
    subst cy.
    simpl.
    destruct Hwf_rtypeuse as [Hwf_rtypeuse _].
    exact Hwf_rtypeuse.
    contradiction.
    --
      eapply method_sig_wf_parameters_by_find; eauto.
      unfold r_basetype in Hbase.
      destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
      injection Hbase as H2_eq.
      subst cy.
      destruct obj as [rt_obj fields_obj].
      destruct rt_obj as [rq_obj rc_obj].
      simpl.
      unfold wf_heap in Hheap.
      assert (Hly_dom : ly < dom h) by (apply runtime_getObj_dom in Hobjy; exact Hobjy).
      specialize (Hheap ly Hly_dom).
      unfold wf_obj in Hheap.
      rewrite Hobjy in Hheap.
      destruct Hheap as [Hwf_rtypeuse _].
      unfold wf_rtypeuse in Hwf_rtypeuse.
      simpl in Hwf_rtypeuse.
      destruct (bound CT rc_obj) as [class_def|] eqn:Hbound.
      simpl.
      destruct Hwf_rtypeuse as [Hwf_rtypeuse _].
      exact Hwf_rtypeuse.
      contradiction.
  -
    apply static_getType_list_preserves_length in Hget_args.
    apply runtime_lookup_list_preserves_length in Hargs.
    rewrite HeqsΓmethodinit.
    rewrite HeqrΓmethodinit.
    simpl.
    f_equal.
    apply Forall2_length in Harg_sub.
    rewrite <- Hargs in Hget_args.
    rewrite <- Hget_args.
    rewrite Harg_sub.
    rewrite Hmsigeq.
    reflexivity.
  -
  assert (Hy_dom : y < dom sΓ').
  {
    apply static_getType_dom in Hget_y.
    exact Hget_y.
  }
  unfold wf_renv in Hrenv.
  destruct Hrenv as [OutterDom [OutterReceiver OutterCorrespond]].
  destruct OutterReceiver as [OutterReceiverAddr OutterReceiver].
  destruct OutterReceiver as [OutterReceiverGetAddr OutterReceiverAddrBound].
  assert (H5 : exists qrout, r_muttype h OutterReceiverAddr = Some qrout).
  {
    unfold r_muttype.
    destruct (runtime_getObj h OutterReceiverAddr) eqn: Hobjaddr.
    2:{
      apply runtime_getObj_not_dom in Hobjaddr.
      lia.
    }
    eexists.
    reflexivity.
  }

  destruct H5 as [qrout H5].
  assert (Hmethod_this_addr : get_this_var_mapping (vars rΓmethodinit) = Some ly).
  {
    unfold get_this_var_mapping.
    rewrite HeqrΓmethodinit.
    simpl.
    auto.
  }
  assert (Hytypable: wf_r_typable CT rΓ h ly Ty qrout).
  {
    eapply correspondence_to_typable; eauto.
    specialize (Hcorr OutterReceiverAddr qrout OutterReceiverGetAddr H5).
    exact Hcorr.
  }
  intros ι qcontext getThisAddr getqcontext i Hi sqt Hnth.
  rewrite HeqsΓmethodinit in Hnth, Hi.
  rewrite HeqrΓmethodinit.
  simpl in *.
  destruct i as [|i'].
  -- (* Reciever *)
    simpl in Hnth.
    injection Hnth as Hsqt_eq.
    subst sqt.
    simpl.
    unfold wf_r_typable.
    unfold r_type.
    destruct (runtime_getObj h ly) as [objy|] eqn:Hobj_ly.
    2:{
      unfold r_basetype in Hbase.
      rewrite Hobj_ly in Hbase.
      discriminate.
    }
    (* Get the runtime type *)
    destruct (r_muttype h ly) as [qy|] eqn:Hq_ly.
    2:{
      unfold r_muttype in Hq_ly.
      rewrite Hobj_ly in Hq_ly.
      discriminate.
    }
    split.
    ---
      unfold wf_r_typable in Hytypable.
      unfold r_basetype in Hbase.
      unfold r_type.
      rewrite Hobj_ly in Hbase.
      injection Hbase as Hcy_eq.
      subst cy.
      destruct objy as [rt_obj fields_obj].
      destruct rt_obj as [rq_obj rc_obj].
      destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].

      unfold r_type in Hytypable.
      rewrite Hobj_ly in Hytypable.
      simpl in Hytypable.
      destruct Hytypable as [Hsubtype _].
      simpl in Hobj_ly.
      (* receiver base type subtype *)
      destruct Hrcv_sub as [Hrcv_sub | H24Special].
      ----
        apply qualified_type_subtype_base_subtype in Hrcv_sub.
        rewrite (vpa_mutability_tt_sctype_safe_ro Ty (mreceiver (msignature mdef))) in Hrcv_sub.
        eapply base_trans; eauto.
        ----
          destruct H24Special as [HReceiverQualifier HBasetype].
          destruct HBasetype as [HReceiverDeclaredQualifier HBasetype].
          eapply base_trans; eauto.

  ---
  (* receiver qualifier type subtype preserved *)
  destruct Hrcv_sub as [Hrcv_sub | H24Special].
  apply qualified_type_subtype_q_subtype in Hrcv_sub.
  ----
    have Hcorrcopy := Hcorr.
    specialize (Hcorr OutterReceiverAddr qrout OutterReceiverGetAddr H5).
    unfold static_getType in Hget_y.
    specialize (Hcorr y Hy_dom Ty Hget_y).
    unfold wf_r_typable in Hcorr.
    rewrite Hval_y in Hcorr.
    unfold r_type in Hcorr.
    rewrite Hobj_ly in Hcorr.
    destruct Hcorr as [_ HInnerReceiverQualifier].

    specialize (Hcorrcopy OutterReceiverAddr qrout OutterReceiverGetAddr H5).
    unfold wf_senv in Hsenv.
    destruct Hsenv as [Hsenvdom _].
    apply get_this_qualified_type_nth_error in Hthis.
    specialize (Hcorrcopy 0 Hsenvdom Tthis Hthis).
    apply get_this_var_mapping_runtime_getVal in OutterReceiverGetAddr.
    rewrite OutterReceiverGetAddr in Hcorrcopy.
    unfold wf_r_typable in Hcorrcopy.
    unfold r_type in Hcorrcopy.
    unfold r_muttype in H5.
    destruct (runtime_getObj h OutterReceiverAddr) as [outterreceiverobj|] eqn:Houtterobj; [|discriminate].
    inversion H5; subst qrout.
    destruct Hcorrcopy as [_ Houtterqualifier].
    rewrite sq_vpa_tt_eq_qq_safe_ro in Hrcv_sub.
    assert (ly = ι).
    {
      rewrite Hmethod_this_addr in getThisAddr.
      inversion getThisAddr; subst; reflexivity.
    }
    subst ι.
    assert ((rqtype (rt_type objy)) = qcontext).
    {
      unfold r_muttype in getqcontext.
      rewrite Hobj_ly in getqcontext.
      simpl in getqcontext.
      inversion getqcontext; subst qcontext.
      reflexivity.
    }
    subst qcontext.
    clear - Houtterqualifier HInnerReceiverQualifier Hrcv_sub.
    destruct (rqtype (rt_type objy)) eqn:Hrqtq;
    destruct (sqtype (mreceiver (msignature mdef))) eqn:Hreceiverq;
    try solve_qualifier_typable_correct_concrete.
    all: destruct (sqtype Ty) eqn:Htyq;
    simpl in Hrcv_sub;
    try solve_q_subtype_wrong.
    all:
    destruct (rqtype (rt_type outterreceiverobj)) eqn:Hrqtoutter;
    try solve_qualifier_typable_wrong_concrete.
  ---- (* The special case *)
    destruct H24Special as [HReceiverQualifier HBasetype].
    destruct HBasetype as [HReceiverDeclaredQualifier HBasetype].
    rewrite HReceiverDeclaredQualifier.

    have Hcorrcopy := Hcorr.
    specialize (Hcorr OutterReceiverAddr qrout OutterReceiverGetAddr H5).
    unfold static_getType in Hget_y.
    specialize (Hcorr y Hy_dom Ty Hget_y).
    unfold wf_r_typable in Hcorr.
    rewrite Hval_y in Hcorr.
    unfold r_type in Hcorr.
    rewrite Hobj_ly in Hcorr.
    destruct Hcorr as [_ HInnerReceiverQualifier].

    specialize (Hcorrcopy OutterReceiverAddr qrout OutterReceiverGetAddr H5).
    unfold wf_senv in Hsenv.
    destruct Hsenv as [Hsenvdom _].
    apply get_this_qualified_type_nth_error in Hthis.
    specialize (Hcorrcopy 0 Hsenvdom Tthis Hthis).
    apply get_this_var_mapping_runtime_getVal in OutterReceiverGetAddr.
    rewrite OutterReceiverGetAddr in Hcorrcopy.
    unfold wf_r_typable in Hcorrcopy.
    unfold r_type in Hcorrcopy.
    unfold r_muttype in H5.
    destruct (runtime_getObj h OutterReceiverAddr) as [outterreceiverobj|] eqn:Houtterobj; [|discriminate].
    inversion H5; subst qrout.
    destruct Hcorrcopy as [_ Houtterqualifier].
    assert (ly = ι).
    {
    rewrite Hmethod_this_addr in getThisAddr.
      inversion getThisAddr; subst; reflexivity.
    }
    subst ι.
    assert ((rqtype (rt_type objy)) = qcontext).
    {
      unfold r_muttype in getqcontext.
      rewrite Hobj_ly in getqcontext.
      simpl in getqcontext.
      inversion getqcontext; subst qcontext.
      reflexivity.
    }
    subst qcontext.
    clear - Houtterqualifier HInnerReceiverQualifier HReceiverQualifier HReceiverDeclaredQualifier.
    destruct (rqtype (rt_type objy)) eqn:Hrqtq;
    destruct (sqtype (mreceiver (msignature mdef))) eqn:Hreceiverq;
    try solve_qualifier_typable_correct_concrete.
    --  (* -------------------------------------------------- *)
  (* apply qualified_type_subtype_q_subtype in Hrcv_sub. *)
  rewrite Hmethod_this_addr in getThisAddr.
  inversion getThisAddr; subst.
  destruct (runtime_getObj h ι) as [objι|] eqn:Hobj_ι.
  2:{
    unfold r_basetype in Hbase.
    rewrite Hobj_ι in Hbase.
    discriminate.
  }
  simpl.
  have Hcorrcopy := Hcorr.
  have Hcorrcopy2 := Hcorr.
  specialize (Hcorr OutterReceiverAddr qrout OutterReceiverGetAddr H5).
  unfold static_getType in Hget_y.
  specialize (Hcorr y Hy_dom Ty Hget_y).
  unfold wf_r_typable in Hcorr.
  rewrite Hval_y in Hcorr.
  unfold r_type in Hcorr.
  rewrite Hobj_ι in Hcorr.
  destruct Hcorr as [_ HInnerReceiverQualifier].

  specialize (Hcorrcopy OutterReceiverAddr qrout OutterReceiverGetAddr H5).
  unfold wf_senv in Hsenv.
  destruct Hsenv as [Hsenvdom _].
  apply get_this_qualified_type_nth_error in Hthis.
  specialize (Hcorrcopy 0 Hsenvdom Tthis Hthis).
  have OutterReceiverGetAddr_copy := OutterReceiverGetAddr.
  have H5_copy := H5.
  apply get_this_var_mapping_runtime_getVal in OutterReceiverGetAddr.
  rewrite OutterReceiverGetAddr in Hcorrcopy.
  unfold wf_r_typable in Hcorrcopy.
  unfold r_type in Hcorrcopy.
  unfold r_muttype in H5.
  destruct (runtime_getObj h OutterReceiverAddr) as [outterreceiverobj|] eqn:Houtterobj; [|discriminate].
  destruct Hcorrcopy as [_ Houtterqualifier].

  unfold runtime_getVal.
  simpl.
  destruct (nth_error vals i') as [v|] eqn:Hval_i.
  --- (* Parameter i' exists *)
    destruct v as [|loc]; [trivial|].
    (* Use Hret_sub to get the subtyping relationship *)
    assert (Hi'_bound : i' < List.length argtypes).
    {
      apply Forall2_length in Harg_sub.
      simpl in Hi.
      simpl in Hnth.
      assert (Hi_mparams : i' < dom (mparams (msignature mdef))).
      { apply nth_error_Some. rewrite Hnth. discriminate. }
      rewrite <- Harg_sub in Hi_mparams.
      exact Hi_mparams.
    }
    assert (Harg_type : exists argtype, nth_error argtypes i' = Some argtype).
    {
      apply nth_error_Some_exists.
      exact Hi'_bound.
    }
    destruct Harg_type as [argtype Hargtype].
    eapply Forall2_nth_error in Harg_sub; eauto.
    unfold wf_r_typable.
    unfold r_type.
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
        unfold wf_r_config in Hwfcopy.
        destruct Hwfcopy as [_ [_ [Hrenv [_ _]]]].
        eapply runtime_lookup_list_preserves_wf_values; eauto.
      }
      eapply Forall_nth_error in Hvals_wf; eauto.
      simpl in Hvals_wf.
      destruct (runtime_getObj h loc) as [obj_loc|] eqn:Hobj_loc; [|contradiction].
      apply runtime_getObj_dom in Hobj_loc.
      exact Hobj_loc.
    }
    destruct (runtime_getObj h loc) as [obj_loc|] eqn:Hobj_loc.
    2:{apply runtime_getObj_not_dom in Hobj_loc. lia. }
    assert (HargtypeFromsEnv :
      exists iArgInSenv,
        nth_error sΓ' iArgInSenv = Some argtype
    /\ nth_error zs i' = Some iArgInSenv).
    {
      destruct (static_getType_list_nth_zs sΓ' zs argtypes i' argtype Hget_args Hargtype)
        as [j [Hzs_j Hst_j]].
      exists j.
      split.
      - (* from static_getType to nth_error sΓ' *)
        unfold static_getType in Hst_j; exact Hst_j.
      - (* keep the zs fact *)
        exact Hzs_j.
    }
    destruct HargtypeFromsEnv as [iArgInSenv [HargtypeFromsEnv Hzs_iArg]].

    assert (Hi'dom : iArgInSenv < dom sΓ').
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
    specialize (Hcorrcopy2 OutterReceiverAddr qrout OutterReceiverGetAddr_copy H5_copy).
    specialize (Hcorrcopy2 iArgInSenv Hi'dom argtype HargtypeFromsEnv).
    unfold runtime_getVal in Hcorrcopy2.
    rewrite HargtypeFromrEnv in Hcorrcopy2.
    unfold wf_r_typable in Hcorrcopy2.
    unfold r_type in Hcorrcopy2.
    rewrite Hobj_loc in Hcorrcopy2.
    destruct Hcorrcopy2 as [Harg_base_subtype Harg_qual_subtype].
    split.

    (* Base type subtype *)
    apply qualified_type_subtype_base_subtype in Harg_sub.
    rewrite (vpa_mutability_tt_sctype_safe_ro Ty) in Harg_sub.
    eapply base_trans; eauto.

    (* Quliafier type correspondence *)
    assert (Hqcontext_eq: qcontext = rqtype (rt_type objι)).
    {
      unfold r_muttype in getqcontext.
      rewrite Hobj_ι in getqcontext.
      inversion getqcontext; subst qcontext.
      reflexivity.
    }
    subst qcontext.
    assert (HOutterReceiverRuntimeMutabilityEq: qrout = rqtype (rt_type outterreceiverobj)).
    {
      inversion H5; subst; reflexivity.
    }
    subst qrout.
    apply qualified_type_subtype_q_subtype in Harg_sub.
    destruct Hrcv_sub as [Hrcv_sub | H24Special].
    ----
      apply qualified_type_subtype_q_subtype in Hrcv_sub.
      clear - Harg_qual_subtype Houtterqualifier HInnerReceiverQualifier Harg_sub.
      rewrite sq_vpa_tt_eq_qq_safe_ro in Harg_sub.
      destruct (rqtype (rt_type obj_loc)) eqn:HArgMutability;
      destruct (rqtype (rt_type objι)) eqn:HInnerReceiverMutability;
      destruct (sqtype sqt) eqn:HParameterStaticDeclearedMutability;
      try solve_qualifier_typable_correct_concrete.
      all:
      destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
      destruct (sqtype Ty) eqn:HyStaticMutability;
      try solve_qualifier_typable_wrong_concrete.
      all:
      destruct (sqtype argtype) eqn:Hargqtype;
      try solve_qualifier_typable_wrong_concrete.

      all: destruct (sqtype Tthis) eqn:HOutterReceiverStaticMutability;
      simpl in Harg_sub;
      try solve_qualifier_typable_wrong_concrete;
      try solve_q_subtype_wrong.
    ----
      destruct H24Special as [HReceiverQualifier HBasetype].
      destruct HBasetype as [HReceiverDeclaredQualifier HBasetype].
      clear - Harg_qual_subtype Houtterqualifier HInnerReceiverQualifier Harg_sub.
      rewrite sq_vpa_tt_eq_qq_safe_ro in Harg_sub.
      destruct (rqtype (rt_type obj_loc)) eqn:HArgMutability;
      destruct (rqtype (rt_type objι)) eqn:HInnerReceiverMutability;
      destruct (sqtype sqt) eqn:HParameterStaticDeclearedMutability;
      try solve_qualifier_typable_correct_concrete.
      all:
      destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
      destruct (sqtype Ty) eqn:HyStaticMutability;
      try solve_qualifier_typable_wrong_concrete.
      all:
      destruct (sqtype argtype) eqn:Hargqtype;
      try solve_qualifier_typable_wrong_concrete.

      all: destruct (sqtype Tthis) eqn:HOutterReceiverStaticMutability;
      simpl in Harg_sub;
      try solve_qualifier_typable_wrong_concrete;
      try solve_q_subtype_wrong.

  --- (* Parameter i' doesn't exist - contradiction *)
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
    lia.

Qed.


Lemma callee_frame_wf_abs :
  forall CT sΓ' rΓ h y m zs vals ly cy mdef mdef0 Ty argtypes Tthis
    (Hwf : wf_r_config CT sΓ' rΓ h)
    (Hval_y : runtime_getVal rΓ y = Some (Iot ly))
    (Hbase : r_basetype h ly = Some cy)
    (mdeflookup : FindMethodWithName CT cy m mdef)
    (Hfind_m : FindMethodWithName CT (sctype Ty) m mdef0)
    (Hget_y : static_getType sΓ' y = Some Ty)
    (Hget_args : static_getType_list sΓ' zs = Some argtypes)
    (Hthis : get_this_qualified_type sΓ' = Some Tthis)
    (Hargs : runtime_lookup_list rΓ zs = Some vals)
    (Hrcv_sub :
      qualified_type_subtype CT Ty
        (vpa_mutability_tt_abs_imm Ty (mreceiver (msignature mdef))) \/
      (sqtype Ty = RO /\ sqtype (mreceiver (msignature mdef)) = RDM /\
       base_subtype CT (sctype Ty) (sctype (mreceiver (msignature mdef)))))
    (Harg_sub :
      Forall2
        (fun arg T => qualified_type_subtype CT arg
          (vpa_mutability_tt_abs_imm Ty T))
        argtypes (mparams (msignature mdef))),
    wf_r_config CT
      (mreceiver (msignature mdef) :: mparams (msignature mdef))
      (mkr_env (Iot ly :: vals)) h.
Proof.
  intros CT sΓ' rΓ h y m zs vals ly cy mdef mdef0 Ty argtypes Tthis
    Hwf Hval_y Hbase mdeflookup Hfind_m Hget_y Hget_args Hthis Hargs
    Hrcv_sub Harg_sub.
  assert (Hmsigeq : msignature mdef = msignature mdef0).
  { eapply runtime_call_signature_agrees; eauto. }
  have Hwfcopy := Hwf.
  unfold wf_r_config in Hwf.
  destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
  remember (mreceiver (msignature mdef) :: mparams (msignature mdef))
    as sΓmethodinit.
  remember (mkr_env (Iot ly :: vals)) as rΓmethodinit.
  destruct (r_muttype h ly) eqn:Hinnerthis.
  2:{
    unfold r_muttype in Hinnerthis.
    unfold r_basetype in Hbase.
    destruct (runtime_getObj h ly); discriminate.
  }
 (* Method inner config wellformed.*)
  split; [exact Hclass|].
  repeat split.
  -
    exact Hheap.
  -
    rewrite HeqrΓmethodinit.
    simpl.
    lia.
  -
    unfold wf_renv in Hrenv.
    destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
    exists ly.
    split.
    --
      rewrite HeqrΓmethodinit.
      simpl.
      reflexivity.
    --
      unfold runtime_getVal in Hval_y.
      destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
      injection Hval_y as H1_eq.
      subst v.
      eapply Forall_nth_error in Hallvals; eauto.
      simpl in Hallvals.
      destruct (runtime_getObj h ly) as [obj|] eqn:Hobjly; [|contradiction].
      apply runtime_getObj_dom in Hobjly.
      exact Hobjly.

  - (* Inner runtime env is wellformed*)
    rewrite HeqrΓmethodinit.
    simpl.
    constructor.
    simpl.
    unfold runtime_getVal in Hval_y.
    destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
    injection Hval_y as H1_eq.
    subst v.
    unfold runtime_getVal in Hnth_y.
    unfold wf_renv in Hrenv.
    destruct Hrenv as [_ [_ Hallvals]].
    eapply Forall_nth_error in Hallvals; eauto.
    simpl in Hallvals.
    exact Hallvals.
    eapply runtime_lookup_list_preserves_wf_values; eauto.
  -
    rewrite HeqsΓmethodinit.
    simpl.
    lia.

  - (* Inner static env's elements are wellformed typeuse *)
    rewrite HeqsΓmethodinit.
    constructor.
    subst.

    --  (* Receiver type is well-formed *)
      eapply method_sig_wf_receiver_by_find; eauto.
      unfold r_basetype in Hbase.
      destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
      injection Hbase as H2_eq.
      destruct obj as [rt_obj fields_obj].
      destruct rt_obj as [rq_obj rc_obj].
      simpl.
      unfold wf_heap in Hheap.
      assert (Hly_dom : ly < dom h) by (apply runtime_getObj_dom in Hobjy; exact Hobjy).
      specialize (Hheap ly Hly_dom).
      unfold wf_obj in Hheap.
      rewrite Hobjy in Hheap.
      destruct Hheap as [Hwf_rtypeuse _].
      unfold wf_rtypeuse in Hwf_rtypeuse.
      simpl in Hwf_rtypeuse.
      destruct (bound CT rc_obj) as [class_def|] eqn:Hbound.
      subst cy.
      simpl.
      destruct Hwf_rtypeuse as [Hwf_rtypeuse _].
      exact Hwf_rtypeuse.
      contradiction.
    --
      eapply method_sig_wf_parameters_by_find; eauto.
      unfold r_basetype in Hbase.
      destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
      injection Hbase as H2_eq.
      subst cy.
      destruct obj as [rt_obj fields_obj].
      destruct rt_obj as [rq_obj rc_obj].
      simpl.
      unfold wf_heap in Hheap.
      assert (Hly_dom : ly < dom h) by (apply runtime_getObj_dom in Hobjy; exact Hobjy).
      specialize (Hheap ly Hly_dom).
      unfold wf_obj in Hheap.
      rewrite Hobjy in Hheap.
      destruct Hheap as [Hwf_rtypeuse _].
      unfold wf_rtypeuse in Hwf_rtypeuse.
      simpl in Hwf_rtypeuse.
      destruct (bound CT rc_obj) as [class_def|] eqn:Hbound.
      simpl.
      destruct Hwf_rtypeuse as [Hwf_rtypeuse _].
      exact Hwf_rtypeuse.
      contradiction.
  -
    apply static_getType_list_preserves_length in Hget_args.
    apply runtime_lookup_list_preserves_length in Hargs.
    rewrite HeqsΓmethodinit.
    rewrite HeqrΓmethodinit.
    simpl.
    f_equal.
    apply Forall2_length in Harg_sub.
    rewrite <- Hargs in Hget_args.
    rewrite <- Hget_args.
    rewrite Harg_sub.
    rewrite Hmsigeq.
    reflexivity.
  -
  assert (Hy_dom : y < dom sΓ').
  {
    apply static_getType_dom in Hget_y.
    exact Hget_y.
  }
  unfold wf_renv in Hrenv.
  destruct Hrenv as [OutterDom [OutterReceiver OutterCorrespond]].
  destruct OutterReceiver as [OutterReceiverAddr OutterReceiver].
  destruct OutterReceiver as [OutterReceiverGetAddr OutterReceiverAddrBound].
  assert (H5 : exists qrout, r_muttype h OutterReceiverAddr = Some qrout).
  {
    unfold r_muttype.
    destruct (runtime_getObj h OutterReceiverAddr) eqn: Hobjaddr.
    2:{
      apply runtime_getObj_not_dom in Hobjaddr.
      lia.
    }
    eexists.
    reflexivity.
  }

  destruct H5 as [qrout H5].
  assert (Hmethod_this_addr : get_this_var_mapping (vars rΓmethodinit) = Some ly).
  {
    unfold get_this_var_mapping.
    rewrite HeqrΓmethodinit.
    simpl.
    auto.
  }
  assert (Hytypable: wf_r_typable CT rΓ h ly Ty qrout).
  {
    eapply correspondence_to_typable; eauto.
    specialize (Hcorr OutterReceiverAddr qrout OutterReceiverGetAddr H5).
    exact Hcorr.
  }
  intros ι qcontext getThisAddr getqcontext i Hi sqt Hnth.
  rewrite HeqsΓmethodinit in Hnth, Hi.
  rewrite HeqrΓmethodinit.
  simpl in *.
  destruct i as [|i'].
  -- (* Reciever *)
    simpl in Hnth.
    injection Hnth as Hsqt_eq.
    subst sqt.
    simpl.
    unfold wf_r_typable.
    unfold r_type.
    destruct (runtime_getObj h ly) as [objy|] eqn:Hobj_ly.
    2:{
      unfold r_basetype in Hbase.
      rewrite Hobj_ly in Hbase.
      discriminate.
    }
    (* Get the runtime type *)
    destruct (r_muttype h ly) as [qy|] eqn:Hq_ly.
    2:{
      unfold r_muttype in Hq_ly.
      rewrite Hobj_ly in Hq_ly.
      discriminate.
    }
    split.
    ---
      unfold wf_r_typable in Hytypable.
      unfold r_basetype in Hbase.
      unfold r_type.
      rewrite Hobj_ly in Hbase.
      injection Hbase as Hcy_eq.
      subst cy.
      destruct objy as [rt_obj fields_obj].
      destruct rt_obj as [rq_obj rc_obj].
      destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].

      unfold r_type in Hytypable.
      rewrite Hobj_ly in Hytypable.
      simpl in Hytypable.
      destruct Hytypable as [Hsubtype _].
      simpl in Hobj_ly.
      (* receiver base type subtype *)
      destruct Hrcv_sub as [Hrcv_sub | H24Special].
      ----
        apply qualified_type_subtype_base_subtype in Hrcv_sub.
        rewrite (vpa_mutability_tt_sctype_abs_imm Ty (mreceiver (msignature mdef))) in Hrcv_sub.
        eapply base_trans; eauto.
      ----
        destruct H24Special as [HReceiverQualifier HBasetype].
        destruct HBasetype as [HReceiverDeclaredQualifier HBasetype].
        eapply base_trans; eauto.
  ---
  (* receiver qualifier type subtype preserved *)
  destruct Hrcv_sub as [Hrcv_sub | H24Special].
  apply qualified_type_subtype_q_subtype in Hrcv_sub.
  ----
    have Hcorrcopy := Hcorr.
    specialize (Hcorr OutterReceiverAddr qrout OutterReceiverGetAddr H5).
    unfold static_getType in Hget_y.
    specialize (Hcorr y Hy_dom Ty Hget_y).
    unfold wf_r_typable in Hcorr.
    rewrite Hval_y in Hcorr.
    unfold r_type in Hcorr.
    rewrite Hobj_ly in Hcorr.
    destruct Hcorr as [_ HInnerReceiverQualifier].

    specialize (Hcorrcopy OutterReceiverAddr qrout OutterReceiverGetAddr H5).
    unfold wf_senv in Hsenv.
    destruct Hsenv as [Hsenvdom _].
    apply get_this_qualified_type_nth_error in Hthis.
    specialize (Hcorrcopy 0 Hsenvdom Tthis Hthis).
    apply get_this_var_mapping_runtime_getVal in OutterReceiverGetAddr.
    rewrite OutterReceiverGetAddr in Hcorrcopy.
    unfold wf_r_typable in Hcorrcopy.
    unfold r_type in Hcorrcopy.
    unfold r_muttype in H5.
    destruct (runtime_getObj h OutterReceiverAddr) as [outterreceiverobj|] eqn:Houtterobj; [|discriminate].
    inversion H5; subst qrout.
    destruct Hcorrcopy as [_ Houtterqualifier].
    rewrite sq_vpa_tt_eq_qq_abs_imm in Hrcv_sub.
    assert (ly = ι).
    {
      rewrite Hmethod_this_addr in getThisAddr.
      inversion getThisAddr; subst; reflexivity.
    }
    subst ι.
    assert ((rqtype (rt_type objy)) = qcontext).
    {
      unfold r_muttype in getqcontext.
      rewrite Hobj_ly in getqcontext.
      simpl in getqcontext.
      inversion getqcontext; subst qcontext.
      reflexivity.
    }
    subst qcontext.
    clear - Houtterqualifier HInnerReceiverQualifier Hrcv_sub.
    destruct (rqtype (rt_type objy)) eqn:Hrqtq;
    destruct (sqtype (mreceiver (msignature mdef))) eqn:Hreceiverq;
    try solve_qualifier_typable_correct_concrete.
    all: destruct (sqtype Ty) eqn:Htyq;
    simpl in Hrcv_sub;
    try solve_q_subtype_wrong.
    all:
    destruct (rqtype (rt_type outterreceiverobj)) eqn:Hrqtoutter;
    try solve_qualifier_typable_wrong_concrete.
  ---- (* The special case *)
    destruct H24Special as [HReceiverQualifier HBasetype].
    destruct HBasetype as [HReceiverDeclaredQualifier HBasetype].
    rewrite HReceiverDeclaredQualifier.

    have Hcorrcopy := Hcorr.
    specialize (Hcorr OutterReceiverAddr qrout OutterReceiverGetAddr H5).
    unfold static_getType in Hget_y.
    specialize (Hcorr y Hy_dom Ty Hget_y).
    unfold wf_r_typable in Hcorr.
    rewrite Hval_y in Hcorr.
    unfold r_type in Hcorr.
    rewrite Hobj_ly in Hcorr.
    destruct Hcorr as [_ HInnerReceiverQualifier].

    specialize (Hcorrcopy OutterReceiverAddr qrout OutterReceiverGetAddr H5).
    unfold wf_senv in Hsenv.
    destruct Hsenv as [Hsenvdom _].
    apply get_this_qualified_type_nth_error in Hthis.
    specialize (Hcorrcopy 0 Hsenvdom Tthis Hthis).
    apply get_this_var_mapping_runtime_getVal in OutterReceiverGetAddr.
    rewrite OutterReceiverGetAddr in Hcorrcopy.
    unfold wf_r_typable in Hcorrcopy.
    unfold r_type in Hcorrcopy.
    unfold r_muttype in H5.
    destruct (runtime_getObj h OutterReceiverAddr) as [outterreceiverobj|] eqn:Houtterobj; [|discriminate].
    inversion H5; subst qrout.
    destruct Hcorrcopy as [_ Houtterqualifier].
    assert (ly = ι).
    {
    rewrite Hmethod_this_addr in getThisAddr.
      inversion getThisAddr; subst; reflexivity.
    }
    subst ι.
    assert ((rqtype (rt_type objy)) = qcontext).
    {
      unfold r_muttype in getqcontext.
      rewrite Hobj_ly in getqcontext.
      simpl in getqcontext.
      inversion getqcontext; subst qcontext.
      reflexivity.
    }
    subst qcontext.
    clear - Houtterqualifier HInnerReceiverQualifier HReceiverQualifier HReceiverDeclaredQualifier.
    destruct (rqtype (rt_type objy)) eqn:Hrqtq;
    destruct (sqtype (mreceiver (msignature mdef))) eqn:Hreceiverq;
    try solve_qualifier_typable_correct_concrete.
    --  (* -------------------------------------------------- *)
  (* apply qualified_type_subtype_q_subtype in Hrcv_sub. *)
  rewrite Hmethod_this_addr in getThisAddr.
  inversion getThisAddr; subst.
  destruct (runtime_getObj h ι) as [objι|] eqn:Hobj_ι.
  2:{
    unfold r_basetype in Hbase.
    rewrite Hobj_ι in Hbase.
    discriminate.
  }
  simpl.
  have Hcorrcopy := Hcorr.
  have Hcorrcopy2 := Hcorr.
  specialize (Hcorr OutterReceiverAddr qrout OutterReceiverGetAddr H5).
  unfold static_getType in Hget_y.
  specialize (Hcorr y Hy_dom Ty Hget_y).
  unfold wf_r_typable in Hcorr.
  rewrite Hval_y in Hcorr.
  unfold r_type in Hcorr.
  rewrite Hobj_ι in Hcorr.
  destruct Hcorr as [_ HInnerReceiverQualifier].

  specialize (Hcorrcopy OutterReceiverAddr qrout OutterReceiverGetAddr H5).
  unfold wf_senv in Hsenv.
  destruct Hsenv as [Hsenvdom _].
  apply get_this_qualified_type_nth_error in Hthis.
  specialize (Hcorrcopy 0 Hsenvdom Tthis Hthis).
  have OutterReceiverGetAddr_copy := OutterReceiverGetAddr.
  have H5_copy := H5.
  apply get_this_var_mapping_runtime_getVal in OutterReceiverGetAddr.
  rewrite OutterReceiverGetAddr in Hcorrcopy.
  unfold wf_r_typable in Hcorrcopy.
  unfold r_type in Hcorrcopy.
  unfold r_muttype in H5.
  destruct (runtime_getObj h OutterReceiverAddr) as [outterreceiverobj|] eqn:Houtterobj; [|discriminate].
  destruct Hcorrcopy as [_ Houtterqualifier].

  unfold runtime_getVal.
  simpl.
  destruct (nth_error vals i') as [v|] eqn:Hval_i.
  --- (* Parameter i' exists *)
    destruct v as [|loc]; [trivial|].
    (* Use Hret_sub to get the subtyping relationship *)
    assert (Hi'_bound : i' < List.length argtypes).
    {
      apply Forall2_length in Harg_sub.
      simpl in Hi.
      simpl in Hnth.
      assert (Hi_mparams : i' < dom (mparams (msignature mdef))).
      { apply nth_error_Some. rewrite Hnth. discriminate. }
      rewrite <- Harg_sub in Hi_mparams.
      exact Hi_mparams.
    }
    assert (Harg_type : exists argtype, nth_error argtypes i' = Some argtype).
    {
      apply nth_error_Some_exists.
      exact Hi'_bound.
    }
    destruct Harg_type as [argtype Hargtype].
    eapply Forall2_nth_error in Harg_sub; eauto.
    unfold wf_r_typable.
    unfold r_type.
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
        unfold wf_r_config in Hwfcopy.
        destruct Hwfcopy as [_ [_ [Hrenv [_ _]]]].
        eapply runtime_lookup_list_preserves_wf_values; eauto.
      }
      eapply Forall_nth_error in Hvals_wf; eauto.
      simpl in Hvals_wf.
      destruct (runtime_getObj h loc) as [obj_loc|] eqn:Hobj_loc; [|contradiction].
      apply runtime_getObj_dom in Hobj_loc.
      exact Hobj_loc.
    }
    destruct (runtime_getObj h loc) as [obj_loc|] eqn:Hobj_loc.
    2:{apply runtime_getObj_not_dom in Hobj_loc. lia. }
    assert (HargtypeFromsEnv :
      exists iArgInSenv,
        nth_error sΓ' iArgInSenv = Some argtype
    /\ nth_error zs i' = Some iArgInSenv).
    {
      destruct (static_getType_list_nth_zs sΓ' zs argtypes i' argtype Hget_args Hargtype)
        as [j [Hzs_j Hst_j]].
      exists j.
      split.
      - (* from static_getType to nth_error sΓ' *)
        unfold static_getType in Hst_j; exact Hst_j.
      - (* keep the zs fact *)
        exact Hzs_j.
    }
    destruct HargtypeFromsEnv as [iArgInSenv [HargtypeFromsEnv Hzs_iArg]].

    assert (Hi'dom : iArgInSenv < dom sΓ').
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
    specialize (Hcorrcopy2 OutterReceiverAddr qrout OutterReceiverGetAddr_copy H5_copy).
    specialize (Hcorrcopy2 iArgInSenv Hi'dom argtype HargtypeFromsEnv).
    unfold runtime_getVal in Hcorrcopy2.
    rewrite HargtypeFromrEnv in Hcorrcopy2.
    unfold wf_r_typable in Hcorrcopy2.
    unfold r_type in Hcorrcopy2.
    rewrite Hobj_loc in Hcorrcopy2.
    destruct Hcorrcopy2 as [Harg_base_subtype Harg_qual_subtype].
    split.

    (* Base type subtype *)
    apply qualified_type_subtype_base_subtype in Harg_sub.
    rewrite (vpa_mutability_tt_sctype_abs_imm Ty) in Harg_sub.
    eapply base_trans; eauto.

    (* Quliafier type correspondence *)
    assert (Hqcontext_eq: qcontext = rqtype (rt_type objι)).
    {
      unfold r_muttype in getqcontext.
      rewrite Hobj_ι in getqcontext.
      inversion getqcontext; subst qcontext.
      reflexivity.
    }
    subst qcontext.
    assert (HOutterReceiverRuntimeMutabilityEq: qrout = rqtype (rt_type outterreceiverobj)).
    {
      inversion H5; subst; reflexivity.
    }
    subst qrout.
    apply qualified_type_subtype_q_subtype in Harg_sub.
    destruct Hrcv_sub as [Hrcv_sub | H24Special].
    ----
      apply qualified_type_subtype_q_subtype in Hrcv_sub.
      clear - Harg_qual_subtype Houtterqualifier HInnerReceiverQualifier Harg_sub.
      rewrite sq_vpa_tt_eq_qq_abs_imm in Harg_sub.
      destruct (rqtype (rt_type obj_loc)) eqn:HArgMutability;
      destruct (rqtype (rt_type objι)) eqn:HInnerReceiverMutability;
      destruct (sqtype sqt) eqn:HParameterStaticDeclearedMutability;
      try solve_qualifier_typable_correct_concrete.
      all:
      destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
      destruct (sqtype Ty) eqn:HyStaticMutability;
      try solve_qualifier_typable_wrong_concrete.
      all:
      destruct (sqtype argtype) eqn:Hargqtype;
      try solve_qualifier_typable_wrong_concrete.

      all: destruct (sqtype Tthis) eqn:HOutterReceiverStaticMutability;
      simpl in Harg_sub;
      try solve_qualifier_typable_wrong_concrete;
      try solve_q_subtype_wrong.
    ----
      destruct H24Special as [HReceiverQualifier HBasetype].
      destruct HBasetype as [HReceiverDeclaredQualifier HBasetype].
      clear - Harg_qual_subtype Houtterqualifier HInnerReceiverQualifier Harg_sub.
      rewrite sq_vpa_tt_eq_qq_abs_imm in Harg_sub.
      destruct (rqtype (rt_type obj_loc)) eqn:HArgMutability;
      destruct (rqtype (rt_type objι)) eqn:HInnerReceiverMutability;
      destruct (sqtype sqt) eqn:HParameterStaticDeclearedMutability;
      try solve_qualifier_typable_correct_concrete.
      all:
      destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
      destruct (sqtype Ty) eqn:HyStaticMutability;
      try solve_qualifier_typable_wrong_concrete.
      all:
      destruct (sqtype argtype) eqn:Hargqtype;
      try solve_qualifier_typable_wrong_concrete.

      all: destruct (sqtype Tthis) eqn:HOutterReceiverStaticMutability;
      simpl in Harg_sub;
      try solve_qualifier_typable_wrong_concrete;
      try solve_q_subtype_wrong.

  --- (* Parameter i' doesn't exist - contradiction *)
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
    lia.

Qed.

(** A typed call initializes the dynamically selected method with a
    well-formed runtime frame, and that method body has the corresponding
    typing derivation. *)
Lemma typed_call_has_wf_callee_frame :
  forall CT sΓ mt rΓ h x m y zs sΓ' vals ly cy mdef
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt (SCall x m y zs) sΓ')
    (Hval_y : runtime_getVal rΓ y = Some (Iot ly))
    (Hbase : r_basetype h ly = Some cy)
    (Hfind : FindMethodWithName CT cy m mdef)
    (Hargs : runtime_lookup_list rΓ zs = Some vals),
    exists sΓbody',
      stmt_typing CT
        (mreceiver (msignature mdef) :: mparams (msignature mdef))
        (mtype (msignature mdef))
        (mbody_stmt (mbody mdef)) sΓbody' /\
      wf_r_config CT
        (mreceiver (msignature mdef) :: mparams (msignature mdef))
        (mkr_env (Iot ly :: vals)) h.
Proof.
  intros CT sΓ mt rΓ h x m y zs sΓ' vals ly cy mdef
    Hwf Htyping Hval_y Hbase Hfind Hargs.
  have Hwf_ct : wf_class_table CT.
  { unfold wf_r_config in Hwf. exact (proj1 Hwf). }
  have Hwf_heap : wf_heap CT h.
  { unfold wf_r_config in Hwf. exact (proj1 (proj2 Hwf)). }
  have Hcy_dom : cy < dom CT.
  { eapply r_basetype_in_dom; eauto. }
  destruct (method_body_well_typed_by_find CT cy m mdef Hwf_ct Hcy_dom Hfind)
    as [sΓbody' Hbody].
  exists sΓbody'.
  split; [exact Hbody|].
  inversion Htyping; subst.
  - assert (Hsig : msignature mdef = msignature mdef0).
    { eapply runtime_call_signature_agrees; eauto. }
    rewrite <- Hsig in Hrcv_sub, Harg_sub.
    eapply callee_frame_wf_abs; eauto.
  - assert (Hsig : msignature mdef = msignature mdef0).
    { eapply runtime_call_signature_agrees; eauto. }
    rewrite <- Hsig in Hrcv_sub, Harg_sub.
    eapply callee_frame_wf_rs_ts; eauto.
Qed.

(** Collect all facts about the dynamically selected target of a typed call.
    In particular, clients do not need to distinguish a method declared in
    the receiver class from one inherited from an ancestor. *)
Lemma typed_call_target :
  forall CT sΓ mt rΓ h x m y zs sΓ' vals ly cy mdef
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt (SCall x m y zs) sΓ')
    (Hval_y : runtime_getVal rΓ y = Some (Iot ly))
    (Hbase : r_basetype h ly = Some cy)
    (Hfind : FindMethodWithName CT cy m mdef)
    (Hargs : runtime_lookup_list rΓ zs = Some vals),
    exists D ddef sΓbody',
      base_subtype CT cy D /\
      find_class CT D = Some ddef /\
      In mdef (methods (body ddef)) /\
      wf_method CT D mdef /\
      stmt_typing CT
        (mreceiver (msignature mdef) :: mparams (msignature mdef))
        (mtype (msignature mdef))
        (mbody_stmt (mbody mdef)) sΓbody' /\
      wf_r_config CT
        (mreceiver (msignature mdef) :: mparams (msignature mdef))
        (mkr_env (Iot ly :: vals)) h.
Proof.
  intros CT sΓ mt rΓ h x m y zs sΓ' vals ly cy mdef
    Hwf Htyping Hval_y Hbase Hfind Hargs.
  have Hwf_ct : wf_class_table CT.
  { unfold wf_r_config in Hwf. exact (proj1 Hwf). }
  have Hwf_heap : wf_heap CT h.
  { unfold wf_r_config in Hwf. exact (proj1 (proj2 Hwf)). }
  have Hcy_dom : cy < dom CT.
  { eapply r_basetype_in_dom; eauto. }
  destruct (method_lookup_in_wellformed_inherited CT cy m mdef
              Hwf_ct Hcy_dom Hfind)
    as [D [ddef [Hsub [Hfind_D [Hin Hwf_method]]]]].
  destruct (typed_call_has_wf_callee_frame CT sΓ mt rΓ h x m y zs
              sΓ' vals ly cy mdef Hwf Htyping Hval_y Hbase Hfind Hargs)
    as [sΓbody' [Hbody Hframe]].
  exists D, ddef, sΓbody'.
  exact (conj Hsub
    (conj Hfind_D
      (conj Hin
        (conj Hwf_method
          (conj Hbody Hframe))))).
Qed.

(* Soundness properties for PICO *)
Theorem preservation_pico :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ'
    (Hwf     : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Heval   : eval_stmt OK CT rΓ h stmt OK rΓ' h'),
    wf_r_config CT sΓ' rΓ' h'.
Proof.
  intros CT sΓ mt rΓ h stmt rΓ' h' sΓ' Hwf Htyping Heval.
  generalize dependent sΓ.
  generalize dependent sΓ'.
  generalize dependent mt.
  remember OK as ok.
  have Heval_copy := Heval.
  induction Heval; intros; try (discriminate; inversion Htyping; subst; exact Hwf).
  6:
    {
      have Htyping_copy := Htyping.
      inversion Htyping; subst.
      -
      destruct Hfind as [mdeflookup getmbody].
      remember (msignature mdef) as msig.
      have mdeflookupcopy := mdeflookup.
      have Hwfcopy := Hwf.
      unfold wf_r_config in Hwf.
      destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
      inversion mdeflookup; revert getmbody; subst; intro getmbody.
      assert (H2 : wf_method CT cy mdef).
      {
        eapply method_lookup_wf_class; eauto.
        eapply r_basetype_in_dom; eauto.
        unfold gget_method in Hget_method.
        apply find_some in Hget_method.
        destruct Hget_method as [Hmethod_in _].
        exact Hmethod_in.
      }
      destruct H2 as [_ [sΓmethodend [mrettype Htyping_method]]].
      destruct Htyping_method as [Htyping_method Hmethodret].
      rewrite <- getmbody in Htyping_method.
      remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit.
      remember {| vars := Iot ly :: vals |} as rΓmethodinit.
      destruct (r_muttype h ly) eqn: Hinnerthis.
      2:{
        unfold r_muttype in Hinnerthis.
        unfold r_basetype in Hbase.
        destruct (runtime_getObj h ly).
        discriminate Hinnerthis.
        discriminate Hbase.
      }
      remember (set_vars rΓ (update x retval (vars rΓ))) as rΓ'''.

      assert (Hmsigeq: msignature mdef = msignature mdef0).
      {
        assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in Hget_y.
          exact Hget_y.
        }
        unfold wf_renv in Hrenv.
        destruct Hrenv as [OutterDom [OutterReceiver OutterCorrespond]].
        destruct OutterReceiver as [OutterReceiverAddr OutterReceiver].
        destruct OutterReceiver as [OutterReceiverGetAddr OutterReceiverAddrBound].
        assert (H5 : exists qrout, r_muttype h OutterReceiverAddr = Some qrout).
        {
          eapply receiver_mutability_exists_from_bound.
          exact OutterReceiverAddrBound.
        }

        destruct H5 as [qrout H5].
        assert (Hmethod_this_addr : get_this_var_mapping (vars rΓmethodinit) = Some ly).
        {
          unfold get_this_var_mapping.
          rewrite HeqrΓmethodinit.
          simpl.
          auto.
        }
        assert (Hytypable: wf_r_typable CT rΓ h ly Ty qrout). {
          eapply correspondence_to_typable; eauto.
          specialize (Hcorr OutterReceiverAddr qrout OutterReceiverGetAddr H5).
          exact Hcorr.
        }

        (* Extract subtyping from wf_r_typable *)
        unfold wf_r_typable in Hytypable.
        unfold r_basetype in Hbase.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection Hbase as Hcy_eq.
        subst cy.
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].
        unfold get_this_var_mapping.

        unfold r_type in Hytypable.
        rewrite Hobjy in Hytypable.
        simpl in Hytypable.
        destruct Hytypable as [Hsubtype _].
        eapply method_signature_consistent_subtype; eauto.
      }
      rewrite <- Hmsigeq in Hrcv_sub.
      rewrite <- Hmsigeq in Hret_sub.
      rewrite <- Hmsigeq in Harg_sub.
      assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
      {
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        eapply callee_frame_wf_abs; eauto.
      }
      assert (H5 : wf_r_config CT sΓmethodend rΓ'' h').
      {
        eapply IHHeval with (sΓ := sΓmethodinit) (sΓ' := sΓmethodend); eauto.
      }

      {
        (* Method call resulting config is wellformed *)
        have H5copy := H5.
        unfold wf_r_config.
        unfold wf_r_config in H5.
        destruct H5 as [_ [Hheapinit [Hrenvinit [Hsenvinit [Hleninit Hcorrinit]]]]].
        have Hrenvcopy := Hrenv.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [HrEnvLen [Hreceiver Hrenvval]].
        split; [exact Hclass|].
        repeat split.
        exact Hheapinit.
        rewrite HeqrΓ'''.
        simpl.
        rewrite update_length.
        simpl.
        lia.
        destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
        exists iot.
        split.
        rewrite HeqrΓ'''.
        simpl.
        unfold gget in *.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
        discriminate Hget_iot.
        unfold get_this_var_mapping in Hget_iot.
        (* injection Hget_iot as Hv0_eq. *)
        (* subst v0. *)
        unfold update.
        destruct x as [|x'].
        easy.
        simpl.
        destruct v0 as [|loc]; [trivial|].
        exact Hget_iot.
        (* rewrite <- getmbody in Htyping_method. *)
	        have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓmethodinit h (mbody_stmt mbody) rΓ'' h' Heval.
        lia.

        (* Outter runtime env is wellformed*)
        rewrite HeqrΓ'''.
        simpl.
        eapply Forall_update; eauto.
        eapply Forall_impl; [|exact Hrenvval].
        intros v Hv.
        destruct v as [|loc]; [trivial|].
        destruct (runtime_getObj h loc) as [obj|] eqn:Hobjloc; [|contradiction].
        (* rewrite <- getmbody in Htyping_method. *)
	        have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓmethodinit h (mbody_stmt mbody) rΓ'' h' Heval.
        assert (Hloc_dom : loc < dom h) by (apply runtime_getObj_dom in Hobjloc; exact Hobjloc).
        assert (Hloc_dom' : loc < dom h') by lia.
        destruct (runtime_getObj h' loc) as [obj'|] eqn:Hobj'.
        trivial.
        exfalso. apply runtime_getObj_not_dom in Hobj'. lia.
        unfold runtime_getVal in Hretval.
        destruct retval as [|loc]; [trivial|].
        unfold wf_renv in Hrenvinit.
        destruct Hrenvinit as [_ [_ Hrenv_wf]].
        eapply Forall_nth_error in Hrenv_wf; eauto.
        simpl in Hrenv_wf.
        destruct (runtime_getObj h' loc) as [obj|] eqn:Hobjloc; [trivial|].
        contradiction.
        apply static_getType_dom in Hget_x.
        rewrite Hlen in Hget_x.
        exact Hget_x.

        (* Length constraint *)
        rewrite Hlen.
        exact HrEnvLen.

        (* Type use is wellformed *)
        unfold wf_senv in Hsenv.
        destruct Hsenv as [Hsenvpdom Hsenvptypeuse].
        exact Hsenvptypeuse.

        (* Length constraint *)
        rewrite Hlen.
        rewrite HeqrΓ'''.
        simpl.
        rewrite update_length.
        easy.

        (* Correspondence holds for resulting variable environment *)
        intros ι qcontext HreceiverAddr Hqcontext i Hi sqt Hnth.
        destruct (Nat.eq_dec i x) as [Heq | Hneq].
        - (* Case: i = x (updated variable) *)
          subst i.
          rewrite HeqrΓ'''.
          simpl.
          unfold runtime_getVal.
          rewrite update_same.
          + apply static_getType_dom in Hget_x.
            rewrite Hlen in Hget_x.
            exact Hget_x.
          + (* Show wf_r_typable for retval *)
            assert (Hnth_x : nth_error sΓ' x = Some Tx).
            {
              unfold static_getType in Hget_x.
              exact Hget_x.
            }
            rewrite Hnth_x in Hnth.
            injection Hnth as Hsqt_eq.
            subst sqt.
            (* Use the fact that retval is well-typed from method return *)
            unfold runtime_getVal in Hretval.
            destruct retval as [|loc]; [trivial|].
            assert (Hret_dom : mreturn (Syntax.mbody mdef) < dom (vars rΓ'')).
            {
              apply nth_error_Some.
              rewrite <- getmbody.
              rewrite Hretval.
              discriminate.
            }
            rewrite <- Hleninit in Hret_dom.
            assert (wf_class_table CT). {
              unfold wf_r_config in H5copy.
              destruct H5copy as [Hclass1 _].
              exact Hclass1.
            }
            destruct Hmethodret as [Hmbodyretvar_dom [Hnth_mbodyret Hsubtype_ret]].
            have Hcorr_copy := Hcorr.
            destruct Hreceiver as [recv_iot [Hget_recv_iot Hrecv_iot_dom]].
            assert (HreceiverAddrInit : get_this_var_mapping (vars rΓ'') = Some ly).
            {
              eapply eval_stmt_preserves_receiver_addr_typed; eauto.
              unfold get_this_var_mapping.
              rewrite HeqrΓmethodinit.
              simpl.
              reflexivity.
            }
            assert (HInnerReceiverEndFrame : r_muttype h' ly = Some q).
            {
              eapply eval_stmt_preserves_r_muttype; eauto.
              unfold r_muttype in Hinnerthis.
              destruct (runtime_getObj h ly) as [innerthisobj|] eqn:Hinnerobj; [|discriminate].
              apply runtime_getObj_dom in Hinnerobj.
              exact Hinnerobj.
            }
            have Hcorrinit_copy := Hcorrinit.
            specialize (Hcorrinit ly q HreceiverAddrInit HInnerReceiverEndFrame (mreturn (Syntax.mbody mdef)) Hret_dom mrettype Hnth_mbodyret).
            destruct (runtime_getVal rΓ'' (mreturn (Syntax.mbody mdef))) eqn: Hmet_val; [|easy].
            destruct v.
            2:{
              assert (Hy_dom : y < dom sΓ').
              {
                apply static_getType_dom in Hget_y.
                exact Hget_y.
              }
              assert (Houtter_receiver_exists : exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
              {
                eapply get_this_exists_from_wf_r_config; eauto.
              }
              destruct Houtter_receiver_exists as [lOutterReceiver HOutterReceiverAddr].
              assert (Houtter_mutability_exists : exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
              {
                eapply receiver_mutability_exists_wf_renv with (CT:=CT); eauto.
              }
              destruct Houtter_mutability_exists as [OutterReceiverMutability HOutterReceiverMutabilityType].

              have Hcorrcopy := Hcorr.
              specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty Hget_y).
              unfold wf_r_typable in Hcorr.
              unfold r_basetype in Hbase.
              unfold r_type.
              destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
              injection Hbase as Hcy_eq.
              subst cy.
              destruct obj as [rt_obj fields_obj].
              destruct rt_obj as [rq_obj rc_obj].

              unfold r_type in Hcorr.
              rewrite Hval_y in Hcorr.
              rewrite Hobjy in Hcorr.
              simpl in Hcorr.
              destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
              unfold runtime_getVal in Hmet_val.
              rewrite getmbody in Hretval.
              rewrite Hmet_val in Hretval.
              inversion Hretval.
              unfold wf_r_typable.
              unfold r_type.
              unfold runtime_getObj.
              subst loc.
              unfold wf_r_typable in Hcorrinit.
              unfold r_type in Hcorrinit.
              unfold runtime_getObj in Hcorrinit.
              destruct (nth_error h' l) eqn: Hobjh'; [|easy].
              destruct Hcorrinit as [Hrorettypebase Hrorettypequalifier].
              split.

              (* Base type subtyping *)
              destruct Hsubtype_ret as [Hsubtype_ret Hmethodoveride].
              apply qualified_type_subtype_base_subtype in Hsubtype_ret.
              apply qualified_type_subtype_base_subtype in Hret_sub.
              (* rewrite (vpa_mutability_tt_sctype Tthis Tx) in H22. *)
              (* rewrite (vpa_mutability_tt Ty (mret (msignature mdef0))) in H22. *)
              rewrite (vpa_mutability_tt_sctype_abs_imm Ty (mret (msignature mdef))) in Hret_sub.
              (* rewrite (vpa_mutability_tt_sctype (mreceiver (msignature mdef)) mrettype) in Hsubtype_ret.
              rewrite (vpa_mutability_tt_sctype (mreceiver (msignature mdef)) (mret (msignature mdef))) in Hsubtype_ret. *)
              (* rewrite <- Hmsigeq in Harg_sub. *)
              eapply base_trans; eauto.
              eapply base_trans; eauto.

              (* Qualfier typability *)
              assert(HOutterReceiverAddrInit: get_this_var_mapping (vars rΓ) = Some ι).
              {
                eapply eval_stmt_preserves_receiver_addr_typed_backwards; eauto.
              }

              assert (HOutterReceiverMutabilityInit: r_muttype h ι = Some qcontext).
              {
                eapply eval_stmt_preserves_r_muttype_backwards; eauto.
              }

              rename q into qinner.
              rename qcontext into qoutter.
              assert(lOutterReceiver = ι). {
                rewrite HOutterReceiverAddrInit in HOutterReceiverAddr.
                inversion HOutterReceiverAddr; reflexivity.
              }
              subst ι.
              assert(OutterReceiverMutability = qoutter). {
                rewrite HOutterReceiverMutabilityType in HOutterReceiverMutabilityInit.
                inversion HOutterReceiverMutabilityInit; reflexivity.
              }
              subst qoutter.
              assert (rq_obj = qinner). {
                unfold r_muttype in Hinnerthis.
                rewrite Hobjy in Hinnerthis.
                simpl in Hinnerthis.
                inversion Hinnerthis; subst qinner.
                reflexivity.
              }
              subst rq_obj.

              specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddrInit HOutterReceiverMutabilityInit).
              specialize (Hcorr_copy lOutterReceiver OutterReceiverMutability HOutterReceiverAddrInit HOutterReceiverMutabilityInit).
              apply get_this_qualified_type_nth_error in Hthis.
              unfold wf_senv in Hsenv.
              destruct Hsenv as [Hsenvdom _].
              specialize (Hcorrcopy 0 Hsenvdom Tthis Hthis).
              apply get_this_var_mapping_runtime_getVal in HOutterReceiverAddrInit.
              rewrite HOutterReceiverAddrInit in Hcorrcopy.
              unfold wf_r_typable in Hcorrcopy.
              unfold r_type in Hcorrcopy.
              unfold r_muttype in HOutterReceiverMutabilityType.
              destruct (runtime_getObj h lOutterReceiver) as [outterreceiverobj|] eqn:Houtterobj; [|discriminate].
              destruct Hcorrcopy as [_ HOutterReceiverQualifierTypablility].

              assert (Hx_dom : x < dom sΓ').
              {
                apply static_getType_dom in Hget_x.
                exact Hget_x.
              }

              destruct Hsubtype_ret as [Hsubtype_ret _].
              apply qualified_type_subtype_q_subtype in Hsubtype_ret.
              move Hsubtype_ret at bottom.
              apply qualified_type_subtype_q_subtype in Hret_sub.
              move Hret_sub at bottom.
              destruct Hrcv_sub as [Hrcv_sub | H24Special].
              1:{
                apply qualified_type_subtype_q_subtype in Hrcv_sub.
                move Hrcv_sub at bottom.
                rewrite Hmsigeq in Hsubtype_ret.
                move HyQualifierTypablility at bottom.

                clear IHHeval.
                inversion HOutterReceiverMutabilityType; subst OutterReceiverMutability.
                subst.
                rewrite sq_vpa_tt_eq_qq_abs_imm in Hrcv_sub.
                rewrite sq_vpa_tt_eq_qq_abs_imm in Hret_sub.
                rewrite <- Hmsigeq in Hsubtype_ret.
                clear - Hsubtype_ret Hret_sub Hrcv_sub HyQualifierTypablility HOutterReceiverQualifierTypablility Hrorettypequalifier.
                destruct (rqtype (rt_type o)) eqn:HretObjectMutability; move HretObjectMutability at bottom;
                destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverRuntimeMutability; move HOutterReceiverRuntimeMutability at bottom;
                destruct (sqtype Tx) eqn:HTxStaticMutability; move HTxStaticMutability at bottom;
                try solve_qualifier_typable_correct_concrete.
                all:
                destruct (sqtype Ty) eqn:HTyStaticMutability; move HTyStaticMutability at bottom;
                destruct (sqtype (mreceiver (msignature mdef))) eqn: HMethodReceiverDeclaredType;
                simpl in Hrcv_sub;
                try solve_q_subtype_wrong.
                all:
                destruct (sqtype (mret (msignature mdef))) eqn:HMethodDeclaredReturnType;
                simpl in Hret_sub;
                try solve_q_subtype_wrong.
                all:
                destruct (sqtype mrettype) eqn:HMethodReturnType; move HMethodReturnType at bottom;
                simpl in Hsubtype_ret;
                try solve_q_subtype_wrong.
                all:
                destruct qinner eqn:HInnerReceiverRuntimeMutability; move HInnerReceiverRuntimeMutability at bottom;
                try solve_qualifier_typable_wrong_concrete.
              }
              1:{
                destruct H24Special as [HReceiverQualifier HBasetype].
                destruct HBasetype as [HReceiverDeclaredQualifier HBasetype].
                rewrite Hmsigeq in Hsubtype_ret.
                move HyQualifierTypablility at bottom.

                clear IHHeval.
                inversion HOutterReceiverMutabilityType; subst OutterReceiverMutability.
                subst.
                rewrite sq_vpa_tt_eq_qq_abs_imm in Hret_sub.
                rewrite <- Hmsigeq in Hsubtype_ret.

                clear - Hsubtype_ret Hret_sub HReceiverQualifier HReceiverDeclaredQualifier HyQualifierTypablility HOutterReceiverQualifierTypablility Hrorettypequalifier.
                destruct (rqtype (rt_type o)) eqn:HretObjectMutability; move HretObjectMutability at bottom;
                destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverRuntimeMutability; move HOutterReceiverRuntimeMutability at bottom;
                destruct (sqtype Tx) eqn:HTxStaticMutability; move HTxStaticMutability at bottom;
                try solve_qualifier_typable_correct_concrete.
                all:
                destruct (sqtype Ty) eqn:HTyStaticMutability; move HTyStaticMutability at bottom;
                destruct (sqtype (mreceiver (msignature mdef))) eqn: HMethodReceiverDeclaredType;
                try solve_q_subtype_wrong.
                all:
                destruct (sqtype (mret (msignature mdef))) eqn:HMethodDeclaredReturnType;
                simpl in Hret_sub;
                try solve_q_subtype_wrong.
                all:
                destruct (sqtype mrettype) eqn:HMethodReturnType; move HMethodReturnType at bottom;
                simpl in Hsubtype_ret;
                try solve_q_subtype_wrong.
                all:
                destruct qinner eqn:HInnerReceiverRuntimeMutability; move HInnerReceiverRuntimeMutability at bottom;
                try solve_qualifier_typable_wrong_concrete.
              }
            }
            unfold runtime_getVal in Hmet_val.
            rewrite getmbody in Hretval.
            rewrite Hretval in Hmet_val.
            easy.
        - (* Case: i ≠ x (unchanged variable) *)
          rewrite HeqrΓ'''.
          simpl.
          unfold runtime_getVal.
          rewrite update_diff; [symmetry; exact Hneq|].
          destruct Hreceiver as [outterreceiveriot [Hget_outter_iot Houtter_iot_dom]].
          assert (HoutreceiverMutabilityType: exists qrout, r_muttype h outterreceiveriot = Some qrout).
          {
            eapply receiver_mutability_exists_from_bound; eauto.
          }
          destruct HoutreceiverMutabilityType as [qrout HoutreceiverMutabilityType].
          specialize (Hcorr outterreceiveriot qrout Hget_outter_iot HoutreceiverMutabilityType i Hi sqt Hnth).
          unfold runtime_getVal in Hcorr.
          destruct (nth_error (vars rΓ) i) as [v|] eqn:Hgetval; [|exact Hcorr].
          destruct v as [|loc]; [trivial|].
          (* Need to show wf_r_typable is preserved when changing runtime environment and heap *)
          unfold wf_r_typable in Hcorr |- *.
          destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
          assert (Hrtype_preserved : r_type h' loc = Some rqt).
          {
            eapply eval_stmt_preserves_r_type; eauto.
            unfold r_type in Hrtype.
            destruct (runtime_getObj h loc) as [obj|] eqn:Hobjloc; [|discriminate].
            apply runtime_getObj_dom in Hobjloc.
            exact Hobjloc.
          }
          {
            unfold update.
            destruct x as [|x'].
            contradiction Hneq.
            easy.
            simpl.
            rewrite Hrtype_preserved.
            assert (outterreceiveriot = ι).
            {
              eapply eval_stmt_preserves_receiver_addr_eq_loc' with (rΓ:=rΓ)(rΓ':=rΓ''')(h':=h'); eauto.
            }
            subst ι.
            assert (HOutterReceiverMutabilityInit: r_muttype h outterreceiveriot = Some qcontext).
            {
              eapply eval_stmt_preserves_r_muttype_backwards; eauto.
            }
            rewrite HOutterReceiverMutabilityInit in HoutreceiverMutabilityType.
            inversion HoutreceiverMutabilityType; subst qrout.
            exact Hcorr.
          }
      }
      assert (H2 : exists D ddef, base_subtype CT cy D /\ find_class CT D = Some ddef /\ In mdef (methods (body ddef)) /\ wf_method CT D mdef).
      {
        eapply method_lookup_in_wellformed_inherited; eauto.
        eapply r_basetype_in_dom; eauto.
      }
      destruct H2 as [D H2].
      destruct H2 as [ddef H2].
      destruct H2 as [Hbasecyd [HfindD [HmdefinD H2]]].

      destruct H2 as [_ [sΓmethodend [mrettype Htyping_method]]].
      destruct Htyping_method as [Htyping_method Hmethodret].
      rewrite <- getmbody in Htyping_method.
      remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit.
      remember {| vars := Iot ly :: vals |} as rΓmethodinit.
      remember (set_vars rΓ (update x retval (vars rΓ))) as rΓ'''.
      assert (Hframe_sig : msignature mdef = msignature mdef0).
      { eapply runtime_call_signature_agrees; eauto. }
      assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
      {
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        eapply callee_frame_wf_abs; eauto.
        all: rewrite Hframe_sig; assumption.
      }
      assert (H8 : wf_r_config CT sΓmethodend rΓ'' h').
      {
        eapply IHHeval with (sΓ := sΓmethodinit) (sΓ' := sΓmethodend); eauto.
      }

      { (* Method call resulting config is wellformed *)
        have H8copy := H8.
        unfold wf_r_config.
        unfold wf_r_config in H8.
        destruct H8 as [_ [Hheapinit [Hrenvinit [Hsenvinit [Hleninit Hcorrinit]]]]].
        unfold wf_renv in Hrenv.
        destruct Hrenv as [HrEnvLen [Hreceiver Hrenvval]].
        split; [exact Hclass|].
        repeat split.
        exact Hheapinit.
        rewrite HeqrΓ'''.
        simpl.
        rewrite update_length.
        simpl.
        lia.

        destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
        exists iot.
        split.
        rewrite HeqrΓ'''.
        simpl.
        unfold gget in *.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
        discriminate Hget_iot.
        (* injection Hget_iot as Hv0_eq. *)
        (* subst v0. *)
        unfold update.
        destruct x as [|x'].
        easy.
        simpl.
        destruct v0 as [|loc]; [trivial|].
        unfold get_this_var_mapping in Hget_iot.
        exact Hget_iot.

        (* length constraint *)
	        have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓmethodinit h (mbody_stmt mbody) rΓ'' h' Heval.
        lia.

        (* Outter runtime env is wellformed*)
        rewrite HeqrΓ'''.
        simpl.
        eapply Forall_update; eauto.
        eapply Forall_impl; [|exact Hrenvval].
        intros v Hv.
        destruct v as [|loc]; [trivial|].
        destruct (runtime_getObj h loc) as [obj|] eqn:Hobjloc; [|contradiction].
        (* rewrite <- getmbody in Htyping_method. *)
	        have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓmethodinit h (mbody_stmt mbody) rΓ'' h' Heval.
        assert (Hloc_dom : loc < dom h) by (apply runtime_getObj_dom in Hobjloc; exact Hobjloc).
        assert (Hloc_dom' : loc < dom h') by lia.
        destruct (runtime_getObj h' loc) as [obj'|] eqn:Hobj'.
        trivial.
        exfalso. apply runtime_getObj_not_dom in Hobj'. lia.
        unfold runtime_getVal in Hretval.
        destruct retval as [|loc]; [trivial|].
        unfold wf_renv in Hrenvinit.
        destruct Hrenvinit as [_ [_ Hrenv_wf]].
        eapply Forall_nth_error in Hrenv_wf; eauto.
        simpl in Hrenv_wf.
        destruct (runtime_getObj h' loc) as [obj|] eqn:Hobjloc; [trivial|].
        contradiction.
        apply static_getType_dom in Hget_x.
        rewrite Hlen in Hget_x.
        exact Hget_x.

        rewrite Hlen.
        exact HrEnvLen.
        unfold wf_senv in Hsenv.
        destruct Hsenv as [Hsenvpdom Hsenvptypeuse].
        exact Hsenvptypeuse.

        rewrite Hlen.
        rewrite HeqrΓ'''.
        simpl.
        rewrite update_length.
        easy.

        intros ι qoutter HOutterReceiverAddr HOutterReceiverMutability i Hi sqt Hnth.
        destruct (Nat.eq_dec i x) as [Heq | Hneq].
        - (* Case: i = x (updated variable) *)
          subst i.
          rewrite HeqrΓ'''.
          simpl.
          unfold runtime_getVal.
          rewrite update_same.
          + apply static_getType_dom in Hget_x.
            rewrite Hlen in Hget_x.
            exact Hget_x.
          + (* Show wf_r_typable for retval *)
            assert (Hnth_x : nth_error sΓ' x = Some Tx).
            {
              unfold static_getType in Hget_x.
              exact Hget_x.
            }
            rewrite Hnth_x in Hnth.
            injection Hnth as Hsqt_eq.
            subst sqt.
            (* Use the fact that retval is well-typed from method return *)
            unfold runtime_getVal in Hretval.
            destruct retval as [|loc]; [trivial|].
            assert (Hret_dom : mreturn (Syntax.mbody mdef) < dom (vars rΓ'')).
            {
              apply nth_error_Some.
              rewrite <- getmbody.
              rewrite Hretval.
              discriminate.
            }
            rewrite <- Hleninit in Hret_dom.
            assert (wf_class_table CT). {
              unfold wf_r_config in H8copy.
              destruct H8copy as [Hclass1 _].
              exact Hclass1.
            }
            destruct Hmethodret as [Hmbodyretvar_dom [Hnth_mbodyret Hsubtype_ret]].
            have Hcorr_copy := Hcorr.

            assert (HInnerReceiverAddr: get_this_var_mapping (vars rΓ'') = Some ly).
            {
              eapply eval_stmt_preserves_receiver_addr_typed with (rΓ:=rΓmethodinit)(rΓ':=rΓ''); eauto.
              unfold get_this_var_mapping.
              rewrite HeqrΓmethodinit.
              simpl.
              reflexivity.
            }
            assert (HInnerReceiverMutability: exists InnerReceiverMutability, r_muttype h' ly = Some InnerReceiverMutability).
            {
              eapply receiver_mutability_exists_from_bound; eauto.
              unfold r_basetype in Hbase.
              destruct (runtime_getObj h ly) as [objly|] eqn:Hobj; [|discriminate].
              apply runtime_getObj_dom in Hobj.
              assert (dom h <= dom h'). {
                eapply eval_stmt_preserves_heap_domain_simple; eauto.
              }
              lia.
            }
            assert (HOutterReceiverAddrInit: get_this_var_mapping (vars rΓ) = Some ι).
            {
              eapply eval_stmt_preserves_receiver_addr_typed_backwards; eauto.
            }
            destruct Hreceiver as [outterreceiveinitriot [Hget_outter_iot Houtter_iot_dom]].
            assert (outterreceiveinitriot = ι).
            {
              eapply eval_stmt_preserves_receiver_addr_eq_loc' with (rΓ:=rΓ)(rΓ':=rΓ''')(h':=h'); eauto.
            }
            assert (HOutterReceiverMutabilityInit: r_muttype h outterreceiveinitriot = Some qoutter).
            {
              eapply eval_stmt_preserves_r_muttype_backwards; eauto.
            }
            subst ι.
            destruct HInnerReceiverMutability as [InnerReceiverMutability HInnerReceiverMutability].
            specialize (Hcorrinit ly InnerReceiverMutability HInnerReceiverAddr HInnerReceiverMutability).
            specialize (Hcorrinit (mreturn (Syntax.mbody mdef)) Hret_dom mrettype Hnth_mbodyret).
            unfold wf_r_typable.
            unfold r_type.
            destruct (runtime_getObj h' loc) as [retobj|] eqn:HReturnObject.
            2:{
              unfold runtime_getVal in Hcorrinit.
              rewrite getmbody in Hretval.
              rewrite Hretval in Hcorrinit.
              unfold wf_r_typable in Hcorrinit.
              unfold r_type in Hcorrinit.
              rewrite HReturnObject in Hcorrinit.
              easy.
            }
            specialize (Hcorr outterreceiveinitriot qoutter Hget_outter_iot HOutterReceiverMutabilityInit).
            have H14copy := Hget_y.
            apply static_getType_dom in Hget_y.
            specialize (Hcorr y Hget_y Ty H14copy).
            rewrite Hval_y in Hcorr.
            unfold wf_r_typable in Hcorr; unfold r_type in Hcorr.
            destruct (runtime_getObj h ly) as [objly|] eqn:Hobj; [|contradiction].
            destruct Hcorr as [HyBasetype HyQualifierTypability].
            assert (rctype (rt_type objly) = cy).
            {
              unfold r_basetype in Hbase.
              rewrite Hobj in Hbase.
              simpl in Hbase.
              inversion Hbase; subst cy.
              reflexivity.
            }
            subst cy.
            assert (Hmsigeq: msignature mdef = msignature mdef0).
            {
              eapply method_signature_consistent_subtype; eauto.
            }
            rewrite Hleninit in Hmbodyretvar_dom.
            destruct (runtime_getVal rΓ'' (mreturn (Syntax.mbody mdef))) eqn: Hmet_val; [|easy].
            destruct v.
            2:{
              unfold runtime_getVal in Hmet_val.
              rewrite getmbody in Hretval.
              rewrite Hmet_val in Hretval.
              inversion Hretval.
              unfold wf_r_typable.
              unfold r_type.
              unfold runtime_getObj.
              subst loc.
              unfold wf_r_typable in Hcorrinit.
              unfold r_type in Hcorrinit.
              unfold runtime_getObj in Hcorrinit.
              destruct (nth_error h' l) eqn: Hobjh'; [|contradiction].
              assert (o = retobj).
              {
                unfold runtime_getObj in HReturnObject.
                rewrite Hobjh' in HReturnObject.
                inversion HReturnObject; subst retobj.
                reflexivity.
              }
              subst o.
              destruct Hcorrinit as [Hrorettypebase Hrorettypequalifier].
              destruct Hsubtype_ret as [Hsubtype_ret Hmethodoveride].

              split.
              (* Base type subtyping *)
              apply qualified_type_subtype_base_subtype in Hret_sub.
              rewrite (vpa_mutability_tt_sctype_abs_imm Ty (mret (msignature mdef0))) in Hret_sub.
              rewrite Hmsigeq in Hsubtype_ret.
              apply qualified_type_subtype_base_subtype in Hsubtype_ret.
              eapply base_trans; eauto.
              eapply base_trans; eauto.

              (* Qualifier Typability *)
              move Hrorettypequalifier at bottom.
              apply qualified_type_subtype_q_subtype in Hret_sub.
              move Hret_sub at bottom.
              move Hcorr_copy at bottom.
              specialize (Hcorr_copy outterreceiveinitriot qoutter Hget_outter_iot HOutterReceiverMutabilityInit).
              unfold wf_senv in Hsenv.
              destruct Hsenv as [Hsenvdom _].
              apply get_this_qualified_type_nth_error in Hthis.
              specialize (Hcorr_copy 0 Hsenvdom Tthis Hthis).
              apply get_this_var_mapping_runtime_getVal in Hget_outter_iot.
              rewrite Hget_outter_iot in Hcorr_copy.
              unfold wf_r_typable in Hcorr_copy.
              unfold r_type in Hcorr_copy.
              destruct (runtime_getObj h outterreceiveinitriot) as [outterreceiverobj|] eqn:Houtterobj; [|easy].
              destruct Hcorr_copy as [_ Houtter_qualifier_typable].
              assert (rqtype (rt_type outterreceiverobj) = qoutter).
              {
                unfold r_muttype in HOutterReceiverMutabilityInit.
                rewrite Houtterobj in HOutterReceiverMutabilityInit.
                simpl in HOutterReceiverMutabilityInit.
                inversion HOutterReceiverMutabilityInit; subst qoutter.
                reflexivity.
              }
              subst qoutter.
              assert (rqtype (rt_type objly) = InnerReceiverMutability).
              {
                assert (Hinner_mut_initial : r_muttype h ly = Some InnerReceiverMutability).
                {
                  eapply eval_stmt_preserves_r_muttype_backwards; eauto.
                  apply runtime_getObj_dom in Hobj.
                  lia.
                }
                unfold r_muttype in Hinner_mut_initial.
                rewrite Hobj in Hinner_mut_initial.
                simpl in Hinner_mut_initial.
                inversion Hinner_mut_initial; subst InnerReceiverMutability.
                reflexivity.
              }
              subst InnerReceiverMutability.
              move Hsubtype_ret at bottom.
              move Hrcv_sub at bottom.
              apply qualified_type_subtype_q_subtype in Hsubtype_ret.
              destruct Hrcv_sub as [Hrcv_sub | H24Special].
              1:{
                apply qualified_type_subtype_q_subtype in Hrcv_sub.
                rewrite <- Hmsigeq in Hret_sub.
                rewrite <- Hmsigeq in Hrcv_sub.

                clear - Hrorettypequalifier Hret_sub Houtter_qualifier_typable Hsubtype_ret Hrcv_sub HyQualifierTypability.
                rewrite sq_vpa_tt_eq_qq_abs_imm in Hret_sub.
                rewrite sq_vpa_tt_eq_qq_abs_imm in Hrcv_sub.
                destruct (rqtype (rt_type retobj)) eqn:Hrorettypemutability; move Hrorettypequalifier at bottom;
                destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutabilityValue; move HOutterReceiverMutabilityValue at bottom;
                destruct (sqtype Tx) eqn:HTxStaticMutability; move HTxStaticMutability at bottom;
                try solve_qualifier_typable_correct_concrete.

                all:
                destruct ((sqtype (mreceiver (msignature mdef)))) eqn:HMethodReceiverDeclaredType;
                destruct (sqtype Ty) eqn:HTyStaticMutability;
                simpl in Hrcv_sub;
                try solve_q_subtype_wrong.

                all:
                destruct (sqtype (mret (msignature mdef))) eqn:HMethodRetDeclaredType;
                simpl in Hret_sub;
                try solve_q_subtype_wrong.

                all:
                destruct (sqtype mrettype) eqn: HMethodRetType;
                simpl in Hsubtype_ret;
                try solve_q_subtype_wrong.

                all:
                destruct (rqtype (rt_type objly)) eqn:HInnerReceiverMutabilityValue;
                try solve_qualifier_typable_wrong_concrete.
              }
              1:{
                destruct H24Special as [HReceiverQualifier HBasetype].
                destruct HBasetype as [HReceiverDeclaredQualifier HBasetype].
                rewrite <- Hmsigeq in Hret_sub.
                rewrite <- Hmsigeq in HReceiverDeclaredQualifier.

                clear - Hrorettypequalifier Hret_sub Houtter_qualifier_typable Hsubtype_ret HReceiverDeclaredQualifier HBasetype HyQualifierTypability.
                rewrite sq_vpa_tt_eq_qq_abs_imm in Hret_sub.
                destruct (rqtype (rt_type retobj)) eqn:Hrorettypemutability; move Hrorettypequalifier at bottom;
                destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutabilityValue; move HOutterReceiverMutabilityValue at bottom;
                destruct (sqtype Tx) eqn:HTxStaticMutability; move HTxStaticMutability at bottom;
                try solve_qualifier_typable_correct_concrete.

                all:
                destruct ((sqtype (mreceiver (msignature mdef)))) eqn:HMethodReceiverDeclaredType;
                destruct (sqtype Ty) eqn:HTyStaticMutability;
                try solve_q_subtype_wrong.

                all:
                destruct (sqtype (mret (msignature mdef))) eqn:HMethodRetDeclaredType;
                simpl in Hret_sub;
                try solve_q_subtype_wrong.

                all:
                destruct (sqtype mrettype) eqn: HMethodRetType;
                simpl in Hsubtype_ret;
                try solve_q_subtype_wrong.

                all:
                destruct (rqtype (rt_type objly)) eqn:HInnerReceiverMutabilityValue;
                try solve_qualifier_typable_wrong_concrete.
              }
            }
            unfold runtime_getVal in Hmet_val.
            rewrite getmbody in Hretval.
            rewrite Hretval in Hmet_val.
            easy.
        - (* Case: i ≠ x (unchanged variable) *)
          rewrite HeqrΓ'''.
          simpl.
          unfold runtime_getVal.
          rewrite update_diff; [symmetry; exact Hneq|].
          destruct Hreceiver as [outterreceiveinitriot [Hget_outter_iot Houtter_iot_dom]].
          assert (outterreceiveinitriot = ι).
          {
            eapply eval_stmt_preserves_receiver_addr_eq_loc' with (rΓ:=rΓ)(rΓ':=rΓ''')(h':=h'); eauto.
          }
          subst ι.
          assert (HOutterReceiverMutabilityInit: r_muttype h outterreceiveinitriot = Some qoutter).
          {
            eapply eval_stmt_preserves_r_muttype_backwards; eauto.
          }
          specialize (Hcorr outterreceiveinitriot qoutter Hget_outter_iot HOutterReceiverMutabilityInit i Hi sqt Hnth).
          unfold runtime_getVal in Hcorr.
          destruct (nth_error (vars rΓ) i) as [v|] eqn:Hgetval; [|exact Hcorr].
          destruct v as [|loc]; [trivial|].
          (* Need to show wf_r_typable is preserved when changing runtime environment and heap *)
          unfold wf_r_typable in Hcorr |- *.
          destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
          assert (Hrtype_preserved : r_type h' loc = Some rqt).
          {
            eapply eval_stmt_preserves_r_type; eauto.
            unfold r_type in Hrtype.
            destruct (runtime_getObj h loc) as [obj|] eqn:Hobjloc; [|discriminate].
            apply runtime_getObj_dom in Hobjloc.
            exact Hobjloc.
          }
          {
            unfold update.
            destruct x as [|x'].
            contradiction Hneq.
            easy.
            simpl.
            rewrite Hrtype_preserved.
            exact Hcorr.
          }
      }
      -
      destruct Hfind as [mdeflookup getmbody].
      remember (msignature mdef) as msig.
      have mdeflookupcopy := mdeflookup.
      have Hwfcopy := Hwf.
      unfold wf_r_config in Hwf.
      destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
      inversion mdeflookup; revert getmbody; subst; intro getmbody.
      assert (H2 : wf_method CT cy mdef).
      {
        eapply method_lookup_wf_class; eauto.
        eapply r_basetype_in_dom; eauto.
        unfold gget_method in Hget_method.
        apply find_some in Hget_method.
        destruct Hget_method as [Hmethod_in _].
        exact Hmethod_in.
      }
      destruct H2 as [_ [sΓmethodend [mrettype Htyping_method]]].
      destruct Htyping_method as [Htyping_method Hmethodret].
      rewrite <- getmbody in Htyping_method.
      remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit.
      remember {| vars := Iot ly :: vals |} as rΓmethodinit.
      destruct (r_muttype h ly) eqn: Hinnerthis.
      2:{
        unfold r_muttype in Hinnerthis.
        unfold r_basetype in Hbase.
        destruct (runtime_getObj h ly).
        discriminate Hinnerthis.
        discriminate Hbase.
      }
      remember (set_vars rΓ (update x retval (vars rΓ))) as rΓ'''.

      assert (Hmsigeq: msignature mdef = msignature mdef0).
      {
        assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in Hget_y.
          exact Hget_y.
        }
        unfold wf_renv in Hrenv.
        destruct Hrenv as [OutterDom [OutterReceiver OutterCorrespond]].
        destruct OutterReceiver as [OutterReceiverAddr OutterReceiver].
        destruct OutterReceiver as [OutterReceiverGetAddr OutterReceiverAddrBound].
        assert (H5 : exists qrout, r_muttype h OutterReceiverAddr = Some qrout).
        {
          eapply receiver_mutability_exists_from_bound.
          exact OutterReceiverAddrBound.
        }

        destruct H5 as [qrout H5].
        assert (Hmethod_this_addr : get_this_var_mapping (vars rΓmethodinit) = Some ly).
        {
          unfold get_this_var_mapping.
          rewrite HeqrΓmethodinit.
          simpl.
          auto.
        }
        assert (Hytypable: wf_r_typable CT rΓ h ly Ty qrout). {
          eapply correspondence_to_typable; eauto.
          specialize (Hcorr OutterReceiverAddr qrout OutterReceiverGetAddr H5).
          exact Hcorr.
        }

        (* Extract subtyping from wf_r_typable *)
        unfold wf_r_typable in Hytypable.
        unfold r_basetype in Hbase.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection Hbase as Hcy_eq.
        subst cy.
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].
        unfold get_this_var_mapping.

        unfold r_type in Hytypable.
        rewrite Hobjy in Hytypable.
        simpl in Hytypable.
        destruct Hytypable as [Hsubtype _].
        eapply method_signature_consistent_subtype; eauto.
      }
      rewrite <- Hmsigeq in Hret_sub.
      rewrite <- Hmsigeq in Hrcv_sub.
      rewrite <- Hmsigeq in Harg_sub.
      assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
      {
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        eapply callee_frame_wf_rs_ts; eauto.
      }
      assert (H5 : wf_r_config CT sΓmethodend rΓ'' h').
      {
        eapply IHHeval with (sΓ := sΓmethodinit) (sΓ' := sΓmethodend); eauto.
      }

      {
        (* Method call resulting config is wellformed *)
        have H5copy := H5.
        unfold wf_r_config.
        unfold wf_r_config in H5.
        destruct H5 as [_ [Hheapinit [Hrenvinit [Hsenvinit [Hleninit Hcorrinit]]]]].
        have Hrenvcopy := Hrenv.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [HrEnvLen [Hreceiver Hrenvval]].
        split; [exact Hclass|].
        repeat split.
        exact Hheapinit.
        rewrite HeqrΓ'''.
        simpl.
        rewrite update_length.
        simpl.
        lia.
        destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
        exists iot.
        split.
        rewrite HeqrΓ'''.
        simpl.
        unfold gget in *.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
        discriminate Hget_iot.
        unfold get_this_var_mapping in Hget_iot.
        (* injection Hget_iot as Hv0_eq. *)
        (* subst v0. *)
        unfold update.
        destruct x as [|x'].
        easy.
        simpl.
        destruct v0 as [|loc]; [trivial|].
        exact Hget_iot.
        (* rewrite <- getmbody in Htyping_method. *)
	        have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓmethodinit h (mbody_stmt mbody) rΓ'' h' Heval.
        lia.

        (* Outter runtime env is wellformed*)
        rewrite HeqrΓ'''.
        simpl.
        eapply Forall_update; eauto.
        eapply Forall_impl; [|exact Hrenvval].
        intros v Hv.
        destruct v as [|loc]; [trivial|].
        destruct (runtime_getObj h loc) as [obj|] eqn:Hobjloc; [|contradiction].
        (* rewrite <- getmbody in Htyping_method. *)
	        have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓmethodinit h (mbody_stmt mbody) rΓ'' h' Heval.
        assert (Hloc_dom : loc < dom h) by (apply runtime_getObj_dom in Hobjloc; exact Hobjloc).
        assert (Hloc_dom' : loc < dom h') by lia.
        destruct (runtime_getObj h' loc) as [obj'|] eqn:Hobj'.
        trivial.
        exfalso. apply runtime_getObj_not_dom in Hobj'. lia.
        unfold runtime_getVal in Hretval.
        destruct retval as [|loc]; [trivial|].
        unfold wf_renv in Hrenvinit.
        destruct Hrenvinit as [_ [_ Hrenv_wf]].
        eapply Forall_nth_error in Hrenv_wf; eauto.
        simpl in Hrenv_wf.
        destruct (runtime_getObj h' loc) as [obj|] eqn:Hobjloc; [trivial|].
        contradiction.
        apply static_getType_dom in Hget_x.
        rewrite Hlen in Hget_x.
        exact Hget_x.

        (* Length constraint *)
        rewrite Hlen.
        exact HrEnvLen.

        (* Type use is wellformed *)
        unfold wf_senv in Hsenv.
        destruct Hsenv as [Hsenvpdom Hsenvptypeuse].
        exact Hsenvptypeuse.

        (* Length constraint *)
        rewrite Hlen.
        rewrite HeqrΓ'''.
        simpl.
        rewrite update_length.
        easy.

        (* Correspondence holds for resulting variable environment *)
        intros ι qcontext HreceiverAddr Hqcontext i Hi sqt Hnth.
        destruct (Nat.eq_dec i x) as [Heq | Hneq].
        - (* Case: i = x (updated variable) *)
          subst i.
          rewrite HeqrΓ'''.
          simpl.
          unfold runtime_getVal.
          rewrite update_same.
          + apply static_getType_dom in Hget_x.
            rewrite Hlen in Hget_x.
            exact Hget_x.
          + (* Show wf_r_typable for retval *)
            assert (Hnth_x : nth_error sΓ' x = Some Tx).
            {
              unfold static_getType in Hget_x.
              exact Hget_x.
            }
            rewrite Hnth_x in Hnth.
            injection Hnth as Hsqt_eq.
            subst sqt.
            (* Use the fact that retval is well-typed from method return *)
            unfold runtime_getVal in Hretval.
            destruct retval as [|loc]; [trivial|].
            assert (Hret_dom : mreturn (Syntax.mbody mdef) < dom (vars rΓ'')).
            {
              apply nth_error_Some.
              rewrite <- getmbody.
              rewrite Hretval.
              discriminate.
            }
            rewrite <- Hleninit in Hret_dom.
            assert (wf_class_table CT). {
              unfold wf_r_config in H5copy.
              destruct H5copy as [Hclass1 _].
              exact Hclass1.
            }
            destruct Hmethodret as [Hmbodyretvar_dom [Hnth_mbodyret Hsubtype_ret]].
            have Hcorr_copy := Hcorr.
            destruct Hreceiver as [recv_iot [Hget_recv_iot Hrecv_iot_dom]].
            assert (HreceiverAddrInit : get_this_var_mapping (vars rΓ'') = Some ly).
            {
              eapply eval_stmt_preserves_receiver_addr_typed; eauto.
              unfold get_this_var_mapping.
              rewrite HeqrΓmethodinit.
              easy.
            }
            assert (HInnerReceiverEndFrame : r_muttype h' ly = Some q).
            {
              eapply eval_stmt_preserves_r_muttype; eauto.
              unfold r_muttype in Hinnerthis.
              destruct (runtime_getObj h ly) as [innerthisobj|] eqn:Hinnerobj; [|discriminate].
              apply runtime_getObj_dom in Hinnerobj.
              exact Hinnerobj.
            }
            have Hcorrinit_copy := Hcorrinit.
            specialize (Hcorrinit ly q HreceiverAddrInit HInnerReceiverEndFrame (mreturn (Syntax.mbody mdef)) Hret_dom mrettype Hnth_mbodyret).
            destruct (runtime_getVal rΓ'' (mreturn (Syntax.mbody mdef))) eqn: Hmet_val; [|easy].
            destruct v.
            2:{
              assert (Hy_dom : y < dom sΓ').
              {
                apply static_getType_dom in Hget_y.
                exact Hget_y.
              }
              assert (Houtter_receiver_exists : exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
              {
                eapply get_this_exists_from_wf_r_config; eauto.
              }
              destruct Houtter_receiver_exists as [lOutterReceiver HOutterReceiverAddr].
              assert (Houtter_mutability_exists : exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
              {
                eapply receiver_mutability_exists_wf_renv with (CT:=CT); eauto.
              }
              destruct Houtter_mutability_exists as [OutterReceiverMutability HOutterReceiverMutabilityType].

              have Hcorrcopy := Hcorr.
              specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty Hget_y).
              unfold wf_r_typable in Hcorr.
              unfold r_basetype in Hbase.
              unfold r_type.
              destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
              injection Hbase as Hcy_eq.
              subst cy.
              destruct obj as [rt_obj fields_obj].
              destruct rt_obj as [rq_obj rc_obj].

              unfold r_type in Hcorr.
              rewrite Hval_y in Hcorr.
              rewrite Hobjy in Hcorr.
              simpl in Hcorr.
              destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
              unfold runtime_getVal in Hmet_val.
              rewrite getmbody in Hretval.
              rewrite Hmet_val in Hretval.
              inversion Hretval.
              unfold wf_r_typable.
              unfold r_type.
              unfold runtime_getObj.
              subst loc.
              unfold wf_r_typable in Hcorrinit.
              unfold r_type in Hcorrinit.
              unfold runtime_getObj in Hcorrinit.
              destruct (nth_error h' l) eqn: Hobjh'; [|easy].
              destruct Hcorrinit as [Hrorettypebase Hrorettypequalifier].
              split.

              (* Base type subtyping *)
              destruct Hsubtype_ret as [Hsubtype_ret Hmethodoveride].
              apply qualified_type_subtype_base_subtype in Hsubtype_ret.
              apply qualified_type_subtype_base_subtype in Hret_sub.
              (* rewrite (vpa_mutability_tt_sctype Tthis Tx) in H22. *)
              (* rewrite (vpa_mutability_tt Ty (mret (msignature mdef0))) in H22. *)
              rewrite (vpa_mutability_tt_sctype_safe_ro Ty (mret (msignature mdef))) in Hret_sub.
              (* rewrite (vpa_mutability_tt_sctype (mreceiver (msignature mdef)) mrettype) in Hsubtype_ret.
              rewrite (vpa_mutability_tt_sctype (mreceiver (msignature mdef)) (mret (msignature mdef))) in Hsubtype_ret. *)
              (* rewrite <- Hmsigeq in Harg_sub. *)
              eapply base_trans; eauto.
              eapply base_trans; eauto.

              (* Qualfier typability *)
              assert(HOutterReceiverAddrInit: get_this_var_mapping (vars rΓ) = Some ι).
              {
                eapply eval_stmt_preserves_receiver_addr_typed_backwards; eauto.
              }

              assert (HOutterReceiverMutabilityInit: r_muttype h ι = Some qcontext).
              {
                eapply eval_stmt_preserves_r_muttype_backwards; eauto.
              }

              rename q into qinner.
              rename qcontext into qoutter.
              assert(lOutterReceiver = ι). {
                rewrite HOutterReceiverAddrInit in HOutterReceiverAddr.
                inversion HOutterReceiverAddr; reflexivity.
              }
              subst ι.
              assert(OutterReceiverMutability = qoutter). {
                rewrite HOutterReceiverMutabilityType in HOutterReceiverMutabilityInit.
                inversion HOutterReceiverMutabilityInit; reflexivity.
              }
              subst qoutter.
              assert (rq_obj = qinner). {
                unfold r_muttype in Hinnerthis.
                rewrite Hobjy in Hinnerthis.
                simpl in Hinnerthis.
                inversion Hinnerthis; subst qinner.
                reflexivity.
              }
              subst rq_obj.

              specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddrInit HOutterReceiverMutabilityInit).
              specialize (Hcorr_copy lOutterReceiver OutterReceiverMutability HOutterReceiverAddrInit HOutterReceiverMutabilityInit).
              apply get_this_qualified_type_nth_error in Hthis.
              unfold wf_senv in Hsenv.
              destruct Hsenv as [Hsenvdom _].
              specialize (Hcorrcopy 0 Hsenvdom Tthis Hthis).
              apply get_this_var_mapping_runtime_getVal in HOutterReceiverAddrInit.
              rewrite HOutterReceiverAddrInit in Hcorrcopy.
              unfold wf_r_typable in Hcorrcopy.
              unfold r_type in Hcorrcopy.
              unfold r_muttype in HOutterReceiverMutabilityType.
              destruct (runtime_getObj h lOutterReceiver) as [outterreceiverobj|] eqn:Houtterobj; [|discriminate].
              destruct Hcorrcopy as [_ HOutterReceiverQualifierTypablility].

              assert (Hx_dom : x < dom sΓ').
              {
                apply static_getType_dom in Hget_x.
                exact Hget_x.
              }

              destruct Hsubtype_ret as [Hsubtype_ret _].
              apply qualified_type_subtype_q_subtype in Hsubtype_ret.
              move Hsubtype_ret at bottom.
              apply qualified_type_subtype_q_subtype in Hret_sub.
              move Hret_sub at bottom.
              destruct Hrcv_sub as [Hrcv_sub | H24Special].
              1:{
                apply qualified_type_subtype_q_subtype in Hrcv_sub.
                move Hrcv_sub at bottom.
                rewrite Hmsigeq in Hsubtype_ret.
                move HyQualifierTypablility at bottom.

                clear IHHeval.
                inversion HOutterReceiverMutabilityType; subst OutterReceiverMutability.
                subst.
                rewrite sq_vpa_tt_eq_qq_safe_ro in Hrcv_sub.
                rewrite sq_vpa_tt_eq_qq_safe_ro in Hret_sub.
                rewrite <- Hmsigeq in Hsubtype_ret.
                clear - Hsubtype_ret Hret_sub Hrcv_sub HyQualifierTypablility HOutterReceiverQualifierTypablility Hrorettypequalifier.
                destruct (rqtype (rt_type o)) eqn:HretObjectMutability; move HretObjectMutability at bottom;
                destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverRuntimeMutability; move HOutterReceiverRuntimeMutability at bottom;
                destruct (sqtype Tx) eqn:HTxStaticMutability; move HTxStaticMutability at bottom;
                try solve_qualifier_typable_correct_concrete.
                all:
                destruct (sqtype Ty) eqn:HTyStaticMutability; move HTyStaticMutability at bottom;
                destruct (sqtype (mreceiver (msignature mdef))) eqn: HMethodReceiverDeclaredType;
                simpl in Hrcv_sub;
                try solve_q_subtype_wrong.
                all:
                destruct (sqtype (mret (msignature mdef))) eqn:HMethodDeclaredReturnType;
                simpl in Hret_sub;
                try solve_q_subtype_wrong.
                all:
                destruct (sqtype mrettype) eqn:HMethodReturnType; move HMethodReturnType at bottom;
                simpl in Hsubtype_ret;
                try solve_q_subtype_wrong.
                all:
                destruct qinner eqn:HInnerReceiverRuntimeMutability; move HInnerReceiverRuntimeMutability at bottom;
                try solve_qualifier_typable_wrong_concrete.
              }
              1:{
                destruct H24Special as [HReceiverQualifier HBasetype].
                destruct HBasetype as [HReceiverDeclaredQualifier HBasetype].
                rewrite Hmsigeq in Hsubtype_ret.
                move HyQualifierTypablility at bottom.

                clear IHHeval.
                inversion HOutterReceiverMutabilityType; subst OutterReceiverMutability.
                subst.
                rewrite sq_vpa_tt_eq_qq_safe_ro in Hret_sub.
                rewrite <- Hmsigeq in Hsubtype_ret.

                clear - Hsubtype_ret Hret_sub HReceiverQualifier HReceiverDeclaredQualifier HyQualifierTypablility HOutterReceiverQualifierTypablility Hrorettypequalifier.
                destruct (rqtype (rt_type o)) eqn:HretObjectMutability; move HretObjectMutability at bottom;
                destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverRuntimeMutability; move HOutterReceiverRuntimeMutability at bottom;
                destruct (sqtype Tx) eqn:HTxStaticMutability; move HTxStaticMutability at bottom;
                try solve_qualifier_typable_correct_concrete.
                all:
                destruct (sqtype Ty) eqn:HTyStaticMutability; move HTyStaticMutability at bottom;
                destruct (sqtype (mreceiver (msignature mdef))) eqn: HMethodReceiverDeclaredType;
                try solve_q_subtype_wrong.
                all:
                destruct (sqtype (mret (msignature mdef))) eqn:HMethodDeclaredReturnType;
                simpl in Hret_sub;
                try solve_q_subtype_wrong.
                all:
                destruct (sqtype mrettype) eqn:HMethodReturnType; move HMethodReturnType at bottom;
                simpl in Hsubtype_ret;
                try solve_q_subtype_wrong.
                all:
                destruct qinner eqn:HInnerReceiverRuntimeMutability; move HInnerReceiverRuntimeMutability at bottom;
                try solve_qualifier_typable_wrong_concrete.
              }
            }
            unfold runtime_getVal in Hmet_val.
            rewrite getmbody in Hretval.
            rewrite Hretval in Hmet_val.
            easy.
        - (* Case: i ≠ x (unchanged variable) *)
          rewrite HeqrΓ'''.
          simpl.
          unfold runtime_getVal.
          rewrite update_diff; [symmetry; exact Hneq|].
          destruct Hreceiver as [outterreceiveriot [Hget_outter_iot Houtter_iot_dom]].
          assert (HoutreceiverMutabilityType: exists qrout, r_muttype h outterreceiveriot = Some qrout).
          {
            eapply receiver_mutability_exists_from_bound; eauto.
          }
          destruct HoutreceiverMutabilityType as [qrout HoutreceiverMutabilityType].
          specialize (Hcorr outterreceiveriot qrout Hget_outter_iot HoutreceiverMutabilityType i Hi sqt Hnth).
          unfold runtime_getVal in Hcorr.
          destruct (nth_error (vars rΓ) i) as [v|] eqn:Hgetval; [|exact Hcorr].
          destruct v as [|loc]; [trivial|].
          (* Need to show wf_r_typable is preserved when changing runtime environment and heap *)
          unfold wf_r_typable in Hcorr |- *.
          destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
          assert (Hrtype_preserved : r_type h' loc = Some rqt).
          {
            eapply eval_stmt_preserves_r_type; eauto.
            unfold r_type in Hrtype.
            destruct (runtime_getObj h loc) as [obj|] eqn:Hobjloc; [|discriminate].
            apply runtime_getObj_dom in Hobjloc.
            exact Hobjloc.
          }
          {
            unfold update.
            destruct x as [|x'].
            contradiction Hneq.
            easy.
            simpl.
            rewrite Hrtype_preserved.
            assert (outterreceiveriot = ι).
            {
              eapply eval_stmt_preserves_receiver_addr_eq_loc' with (rΓ:=rΓ)(rΓ':=rΓ''')(h':=h'); eauto.
            }
            subst ι.
            assert (HOutterReceiverMutabilityInit: r_muttype h outterreceiveriot = Some qcontext).
            {
              eapply eval_stmt_preserves_r_muttype_backwards; eauto.
            }
            rewrite HOutterReceiverMutabilityInit in HoutreceiverMutabilityType.
            inversion HoutreceiverMutabilityType; subst qrout.
            exact Hcorr.
          }
      }
      assert (H2 : exists D ddef, base_subtype CT cy D /\ find_class CT D = Some ddef /\ In mdef (methods (body ddef)) /\ wf_method CT D mdef).
      {
        eapply method_lookup_in_wellformed_inherited; eauto.
        eapply r_basetype_in_dom; eauto.
      }
      destruct H2 as [D H2].
      destruct H2 as [ddef H2].
      destruct H2 as [Hbasecyd [HfindD [HmdefinD H2]]].

      destruct H2 as [_ [sΓmethodend [mrettype Htyping_method]]].
      destruct Htyping_method as [Htyping_method Hmethodret].
      rewrite <- getmbody in Htyping_method.
      remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit.
      remember {| vars := Iot ly :: vals |} as rΓmethodinit.
      remember (set_vars rΓ (update x retval (vars rΓ))) as rΓ'''.
      assert (Hframe_sig : msignature mdef = msignature mdef0).
      { eapply runtime_call_signature_agrees; eauto. }
      assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
      {
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        eapply callee_frame_wf_rs_ts; eauto.
        all: rewrite Hframe_sig; assumption.
      }
      assert (H8 : wf_r_config CT sΓmethodend rΓ'' h').
      {
        eapply IHHeval with (sΓ := sΓmethodinit) (sΓ' := sΓmethodend); eauto.
      }

      { (* Method call resulting config is wellformed *)
        have H8copy := H8.
        unfold wf_r_config.
        unfold wf_r_config in H8.
        destruct H8 as [_ [Hheapinit [Hrenvinit [Hsenvinit [Hleninit Hcorrinit]]]]].
        unfold wf_renv in Hrenv.
        destruct Hrenv as [HrEnvLen [Hreceiver Hrenvval]].
        split; [exact Hclass|].
        repeat split.
        exact Hheapinit.
        rewrite HeqrΓ'''.
        simpl.
        rewrite update_length.
        simpl.
        lia.

        destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
        exists iot.
        split.
        rewrite HeqrΓ'''.
        simpl.
        unfold gget in *.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
        discriminate Hget_iot.
        (* injection Hget_iot as Hv0_eq. *)
        (* subst v0. *)
        unfold update.
        destruct x as [|x'].
        easy.
        simpl.
        destruct v0 as [|loc]; [trivial|].
        unfold get_this_var_mapping in Hget_iot.
        exact Hget_iot.

        (* length constraint *)
	        have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓmethodinit h (mbody_stmt mbody) rΓ'' h' Heval.
        lia.

        (* Outter runtime env is wellformed*)
        rewrite HeqrΓ'''.
        simpl.
        eapply Forall_update; eauto.
        eapply Forall_impl; [|exact Hrenvval].
        intros v Hv.
        destruct v as [|loc]; [trivial|].
        destruct (runtime_getObj h loc) as [obj|] eqn:Hobjloc; [|contradiction].
        (* rewrite <- getmbody in Htyping_method. *)
	        have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓmethodinit h (mbody_stmt mbody) rΓ'' h' Heval.
        assert (Hloc_dom : loc < dom h) by (apply runtime_getObj_dom in Hobjloc; exact Hobjloc).
        assert (Hloc_dom' : loc < dom h') by lia.
        destruct (runtime_getObj h' loc) as [obj'|] eqn:Hobj'.
        trivial.
        exfalso. apply runtime_getObj_not_dom in Hobj'. lia.
        unfold runtime_getVal in Hretval.
        destruct retval as [|loc]; [trivial|].
        unfold wf_renv in Hrenvinit.
        destruct Hrenvinit as [_ [_ Hrenv_wf]].
        eapply Forall_nth_error in Hrenv_wf; eauto.
        simpl in Hrenv_wf.
        destruct (runtime_getObj h' loc) as [obj|] eqn:Hobjloc; [trivial|].
        contradiction.
        apply static_getType_dom in Hget_x.
        rewrite Hlen in Hget_x.
        exact Hget_x.

        rewrite Hlen.
        exact HrEnvLen.
        unfold wf_senv in Hsenv.
        destruct Hsenv as [Hsenvpdom Hsenvptypeuse].
        exact Hsenvptypeuse.

        rewrite Hlen.
        rewrite HeqrΓ'''.
        simpl.
        rewrite update_length.
        easy.

        intros ι qoutter HOutterReceiverAddr HOutterReceiverMutability i Hi sqt Hnth.
        destruct (Nat.eq_dec i x) as [Heq | Hneq].
        - (* Case: i = x (updated variable) *)
          subst i.
          rewrite HeqrΓ'''.
          simpl.
          unfold runtime_getVal.
          rewrite update_same.
          + apply static_getType_dom in Hget_x.
            rewrite Hlen in Hget_x.
            exact Hget_x.
          + (* Show wf_r_typable for retval *)
            assert (Hnth_x : nth_error sΓ' x = Some Tx).
            {
              unfold static_getType in Hget_x.
              exact Hget_x.
            }
            rewrite Hnth_x in Hnth.
            injection Hnth as Hsqt_eq.
            subst sqt.
            (* Use the fact that retval is well-typed from method return *)
            unfold runtime_getVal in Hretval.
            destruct retval as [|loc]; [trivial|].
            assert (Hret_dom : mreturn (Syntax.mbody mdef) < dom (vars rΓ'')).
            {
              apply nth_error_Some.
              rewrite <- getmbody.
              rewrite Hretval.
              discriminate.
            }
            rewrite <- Hleninit in Hret_dom.
            assert (wf_class_table CT). {
              unfold wf_r_config in H8copy.
              destruct H8copy as [Hclass1 _].
              exact Hclass1.
            }
            destruct Hmethodret as [Hmbodyretvar_dom [Hnth_mbodyret Hsubtype_ret]].
            have Hcorr_copy := Hcorr.

            assert (HInnerReceiverAddr: get_this_var_mapping (vars rΓ'') = Some ly).
            {
              eapply eval_stmt_preserves_receiver_addr_typed with (rΓ:=rΓmethodinit)(rΓ':=rΓ''); eauto.
              unfold get_this_var_mapping.
              rewrite HeqrΓmethodinit.
              simpl.
              reflexivity.
            }
            assert (HInnerReceiverMutability: exists InnerReceiverMutability, r_muttype h' ly = Some InnerReceiverMutability).
            {
              eapply receiver_mutability_exists_from_bound; eauto.
              unfold r_basetype in Hbase.
              destruct (runtime_getObj h ly) as [objly|] eqn:Hobj; [|discriminate].
              apply runtime_getObj_dom in Hobj.
              assert (dom h <= dom h'). {
                eapply eval_stmt_preserves_heap_domain_simple; eauto.
              }
              lia.
            }
            assert (HOutterReceiverAddrInit: get_this_var_mapping (vars rΓ) = Some ι).
            {
              eapply eval_stmt_preserves_receiver_addr_typed_backwards; eauto.
            }
            destruct Hreceiver as [outterreceiveinitriot [Hget_outter_iot Houtter_iot_dom]].
            assert (outterreceiveinitriot = ι).
            {
              eapply eval_stmt_preserves_receiver_addr_eq_loc' with (rΓ:=rΓ)(rΓ':=rΓ''')(h':=h'); eauto.
            }
            assert (HOutterReceiverMutabilityInit: r_muttype h outterreceiveinitriot = Some qoutter).
            {
              eapply eval_stmt_preserves_r_muttype_backwards; eauto.
            }
            subst ι.
            destruct HInnerReceiverMutability as [InnerReceiverMutability HInnerReceiverMutability].
            specialize (Hcorrinit ly InnerReceiverMutability HInnerReceiverAddr HInnerReceiverMutability).
            specialize (Hcorrinit (mreturn (Syntax.mbody mdef)) Hret_dom mrettype Hnth_mbodyret).
            unfold wf_r_typable.
            unfold r_type.
            destruct (runtime_getObj h' loc) as [retobj|] eqn:HReturnObject.
            2:{
              unfold runtime_getVal in Hcorrinit.
              rewrite getmbody in Hretval.
              rewrite Hretval in Hcorrinit.
              unfold wf_r_typable in Hcorrinit.
              unfold r_type in Hcorrinit.
              rewrite HReturnObject in Hcorrinit.
              easy.
            }
            specialize (Hcorr outterreceiveinitriot qoutter Hget_outter_iot HOutterReceiverMutabilityInit).
            have H14copy := Hget_y.
            apply static_getType_dom in Hget_y.
            specialize (Hcorr y Hget_y Ty H14copy).
            rewrite Hval_y in Hcorr.
            unfold wf_r_typable in Hcorr; unfold r_type in Hcorr.
            destruct (runtime_getObj h ly) as [objly|] eqn:Hobj; [|contradiction].
            destruct Hcorr as [HyBasetype HyQualifierTypability].
            assert (rctype (rt_type objly) = cy).
            {
              unfold r_basetype in Hbase.
              rewrite Hobj in Hbase.
              simpl in Hbase.
              inversion Hbase; subst cy.
              reflexivity.
            }
            subst cy.
            assert (Hmsigeq: msignature mdef = msignature mdef0).
            {
              eapply method_signature_consistent_subtype; eauto.
            }
            rewrite Hleninit in Hmbodyretvar_dom.
            destruct (runtime_getVal rΓ'' (mreturn (Syntax.mbody mdef))) eqn: Hmet_val; [|easy].
            destruct v.
            2:{
              unfold runtime_getVal in Hmet_val.
              rewrite getmbody in Hretval.
              rewrite Hmet_val in Hretval.
              inversion Hretval.
              unfold wf_r_typable.
              unfold r_type.
              unfold runtime_getObj.
              subst loc.
              unfold wf_r_typable in Hcorrinit.
              unfold r_type in Hcorrinit.
              unfold runtime_getObj in Hcorrinit.
              destruct (nth_error h' l) eqn: Hobjh'; [|contradiction].
              assert (o = retobj).
              {
                unfold runtime_getObj in HReturnObject.
                rewrite Hobjh' in HReturnObject.
                inversion HReturnObject; subst retobj.
                reflexivity.
              }
              subst o.
              destruct Hcorrinit as [Hrorettypebase Hrorettypequalifier].
              destruct Hsubtype_ret as [Hsubtype_ret Hmethodoveride].

              split.
              (* Base type subtyping *)
              apply qualified_type_subtype_base_subtype in Hret_sub.
              rewrite (vpa_mutability_tt_sctype_safe_ro Ty (mret (msignature mdef0))) in Hret_sub.
              rewrite Hmsigeq in Hsubtype_ret.
              apply qualified_type_subtype_base_subtype in Hsubtype_ret.
              eapply base_trans; eauto.
              eapply base_trans; eauto.

              (* Qualifier Typability *)
              move Hrorettypequalifier at bottom.
              apply qualified_type_subtype_q_subtype in Hret_sub.
              move Hret_sub at bottom.
              move Hcorr_copy at bottom.
              specialize (Hcorr_copy outterreceiveinitriot qoutter Hget_outter_iot HOutterReceiverMutabilityInit).
              unfold wf_senv in Hsenv.
              destruct Hsenv as [Hsenvdom _].
              apply get_this_qualified_type_nth_error in Hthis.
              specialize (Hcorr_copy 0 Hsenvdom Tthis Hthis).
              apply get_this_var_mapping_runtime_getVal in Hget_outter_iot.
              rewrite Hget_outter_iot in Hcorr_copy.
              unfold wf_r_typable in Hcorr_copy.
              unfold r_type in Hcorr_copy.
              destruct (runtime_getObj h outterreceiveinitriot) as [outterreceiverobj|] eqn:Houtterobj; [|easy].
              destruct Hcorr_copy as [_ Houtter_qualifier_typable].
              assert (rqtype (rt_type outterreceiverobj) = qoutter).
              {
                unfold r_muttype in HOutterReceiverMutabilityInit.
                rewrite Houtterobj in HOutterReceiverMutabilityInit.
                simpl in HOutterReceiverMutabilityInit.
                inversion HOutterReceiverMutabilityInit; subst qoutter.
                reflexivity.
              }
              subst qoutter.
              assert (rqtype (rt_type objly) = InnerReceiverMutability).
              {
                assert (Hinner_mut_initial : r_muttype h ly = Some InnerReceiverMutability).
                {
                  eapply eval_stmt_preserves_r_muttype_backwards; eauto.
                  apply runtime_getObj_dom in Hobj.
                  lia.
                }
                unfold r_muttype in Hinner_mut_initial.
                rewrite Hobj in Hinner_mut_initial.
                simpl in Hinner_mut_initial.
                inversion Hinner_mut_initial; subst InnerReceiverMutability.
                reflexivity.
              }
              subst InnerReceiverMutability.
              move Hsubtype_ret at bottom.
              move Hrcv_sub at bottom.
              apply qualified_type_subtype_q_subtype in Hsubtype_ret.
              destruct Hrcv_sub as [Hrcv_sub | H24Special].
              1:{
                apply qualified_type_subtype_q_subtype in Hrcv_sub.
                rewrite <- Hmsigeq in Hret_sub.
                rewrite <- Hmsigeq in Hrcv_sub.

                clear - Hrorettypequalifier Hret_sub Houtter_qualifier_typable Hsubtype_ret Hrcv_sub HyQualifierTypability.
                rewrite sq_vpa_tt_eq_qq_safe_ro in Hret_sub.
                rewrite sq_vpa_tt_eq_qq_safe_ro in Hrcv_sub.
                destruct (rqtype (rt_type retobj)) eqn:Hrorettypemutability; move Hrorettypequalifier at bottom;
                destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutabilityValue; move HOutterReceiverMutabilityValue at bottom;
                destruct (sqtype Tx) eqn:HTxStaticMutability; move HTxStaticMutability at bottom;
                try solve_qualifier_typable_correct_concrete.

                all:
                destruct ((sqtype (mreceiver (msignature mdef)))) eqn:HMethodReceiverDeclaredType;
                destruct (sqtype Ty) eqn:HTyStaticMutability;
                simpl in Hrcv_sub;
                try solve_q_subtype_wrong.

                all:
                destruct (sqtype (mret (msignature mdef))) eqn:HMethodRetDeclaredType;
                simpl in Hret_sub;
                try solve_q_subtype_wrong.

                all:
                destruct (sqtype mrettype) eqn: HMethodRetType;
                simpl in Hsubtype_ret;
                try solve_q_subtype_wrong.

                all:
                destruct (rqtype (rt_type objly)) eqn:HInnerReceiverMutabilityValue;
                try solve_qualifier_typable_wrong_concrete.
              }
              1:{
                destruct H24Special as [HReceiverQualifier HBasetype].
                destruct HBasetype as [HReceiverDeclaredQualifier HBasetype].
                rewrite <- Hmsigeq in Hret_sub.
                rewrite <- Hmsigeq in HReceiverDeclaredQualifier.

                clear - Hrorettypequalifier Hret_sub Houtter_qualifier_typable Hsubtype_ret HReceiverDeclaredQualifier HBasetype HyQualifierTypability.
                rewrite sq_vpa_tt_eq_qq_safe_ro in Hret_sub.
                destruct (rqtype (rt_type retobj)) eqn:Hrorettypemutability; move Hrorettypequalifier at bottom;
                destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutabilityValue; move HOutterReceiverMutabilityValue at bottom;
                destruct (sqtype Tx) eqn:HTxStaticMutability; move HTxStaticMutability at bottom;
                try solve_qualifier_typable_correct_concrete.

                all:
                destruct ((sqtype (mreceiver (msignature mdef)))) eqn:HMethodReceiverDeclaredType;
                destruct (sqtype Ty) eqn:HTyStaticMutability;
                try solve_q_subtype_wrong.

                all:
                destruct (sqtype (mret (msignature mdef))) eqn:HMethodRetDeclaredType;
                simpl in Hret_sub;
                try solve_q_subtype_wrong.

                all:
                destruct (sqtype mrettype) eqn: HMethodRetType;
                simpl in Hsubtype_ret;
                try solve_q_subtype_wrong.

                all:
                destruct (rqtype (rt_type objly)) eqn:HInnerReceiverMutabilityValue;
                try solve_qualifier_typable_wrong_concrete.
              }
            }
            unfold runtime_getVal in Hmet_val.
            rewrite getmbody in Hretval.
            rewrite Hretval in Hmet_val.
            easy.
        - (* Case: i ≠ x (unchanged variable) *)
          rewrite HeqrΓ'''.
          simpl.
          unfold runtime_getVal.
          rewrite update_diff; [symmetry; exact Hneq|].
          destruct Hreceiver as [outterreceiveinitriot [Hget_outter_iot Houtter_iot_dom]].
          assert (outterreceiveinitriot = ι).
          {
            eapply eval_stmt_preserves_receiver_addr_eq_loc' with (rΓ:=rΓ)(rΓ':=rΓ''')(h':=h'); eauto.
          }
          subst ι.
          assert (HOutterReceiverMutabilityInit: r_muttype h outterreceiveinitriot = Some qoutter).
          {
            eapply eval_stmt_preserves_r_muttype_backwards; eauto.
          }
          specialize (Hcorr outterreceiveinitriot qoutter Hget_outter_iot HOutterReceiverMutabilityInit i Hi sqt Hnth).
          unfold runtime_getVal in Hcorr.
          destruct (nth_error (vars rΓ) i) as [v|] eqn:Hgetval; [|exact Hcorr].
          destruct v as [|loc]; [trivial|].
          (* Need to show wf_r_typable is preserved when changing runtime environment and heap *)
          unfold wf_r_typable in Hcorr |- *.
          destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
          assert (Hrtype_preserved : r_type h' loc = Some rqt).
          {
            eapply eval_stmt_preserves_r_type; eauto.
            unfold r_type in Hrtype.
            destruct (runtime_getObj h loc) as [obj|] eqn:Hobjloc; [|discriminate].
            apply runtime_getObj_dom in Hobjloc.
            exact Hobjloc.
          }
          {
            unfold update.
            destruct x as [|x'].
            contradiction Hneq.
            easy.
            simpl.
            rewrite Hrtype_preserved.
            exact Hcorr.
          }
      }
    }
  - (* Case: stmt = Skip *)
    eapply preservation_skip; eauto.
  - (* Case: stmt = Local *)
    eapply preservation_local_ok; eauto.
  - (* Case: stmt = VarAss *)
    eapply preservation_varass_ok; eauto.
  - (* Case: stmt = FldWrite *)
    eapply preservation_fldwrite_ok; eauto.
  - (* Case: stmt = New *)
    eapply preservation_new_ok; eauto.
  - (* Case: stmt = Seq *)
    intros. inversion Htyping; subst.
    specialize (IHHeval1 eq_refl Heval1 mt sΓ'0 sΓ Hwf Htype1) as IH1.
    specialize (IHHeval2 eq_refl Heval2 mt sΓ' sΓ'0 IH1 Htype2) as IH2.
    exact IH2.
Qed.

Notation "l [ i ]" := (nth_error l i) (at level 50).
