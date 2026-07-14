Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation Properties Preservation.

From Stdlib Require Import List.
From Stdlib Require String.
Import ListNotations.

(* ------------------------------------------------------------- *)
Lemma callee_frame_wf_rs_ts :
  forall CT sΓ' rΓ h y m zs vals ly cy mdef mdef0 Ty C argtypes Tthis
    (Hwf : wf_r_config CT sΓ' rΓ h)
    (Hval_y : runtime_getVal rΓ y = Some (Iot ly))
    (Hbase : r_basetype h ly = Some cy)
    (mdeflookup : FindMethodWithName CT cy m mdef)
    (Href : sbase Ty = TRef C)
    (Hfind_m : FindMethodWithName CT C m mdef0)
    (Hget_y : static_getType sΓ' y = Some Ty)
    (Hget_args : static_getType_list sΓ' zs = Some argtypes)
    (Hthis : get_this_qualified_type sΓ' = Some Tthis)
    (Hargs : runtime_lookup_list rΓ zs = Some vals)
    (Hrcv_sub :
      qualified_type_subtype CT Ty
        (vpa_mutability_tt_safe_ro Ty (mreceiver (msignature mdef))) \/
      (sqtype Ty = RO /\ sqtype (mreceiver (msignature mdef)) = RDM /\
       base_subtype CT (sbase Ty) (sbase (mreceiver (msignature mdef)))))
    (Harg_sub :
      Forall2
        (fun arg T => qualified_type_subtype CT arg
          (vpa_mutability_tt_safe_ro Ty T))
        argtypes (mparams (msignature mdef))),
    wf_r_config CT
      (mreceiver (msignature mdef) :: mparams (msignature mdef))
      (mkr_env (Iot ly :: vals)) h.
Proof.
  intros CT sΓ' rΓ h y m zs vals ly cy mdef mdef0 Ty C argtypes Tthis
    Hwf Hval_y Hbase mdeflookup Href Hfind_m Hget_y Hget_args Hthis Hargs
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
        rewrite (vpa_mutability_tt_sbase_safe_ro Ty (mreceiver (msignature mdef))) in Hrcv_sub.
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
    destruct v as [|loc|n]; try trivial.
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
          | Int _ => True
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
    rewrite (vpa_mutability_tt_sbase_safe_ro Ty) in Harg_sub.
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

    ---- eapply call_int_arg_base_safe_ro with
        (Ty := Ty) (mdef := mdef)
        (argtypes := argtypes) (zs := zs) (vals := vals)
        (i := i') (n := n); eauto.

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
  forall CT sΓ' rΓ h y m zs vals ly cy mdef mdef0 Ty C argtypes Tthis
    (Hwf : wf_r_config CT sΓ' rΓ h)
    (Hval_y : runtime_getVal rΓ y = Some (Iot ly))
    (Hbase : r_basetype h ly = Some cy)
    (mdeflookup : FindMethodWithName CT cy m mdef)
    (Href : sbase Ty = TRef C)
    (Hfind_m : FindMethodWithName CT C m mdef0)
    (Hget_y : static_getType sΓ' y = Some Ty)
    (Hget_args : static_getType_list sΓ' zs = Some argtypes)
    (Hthis : get_this_qualified_type sΓ' = Some Tthis)
    (Hargs : runtime_lookup_list rΓ zs = Some vals)
    (Hrcv_sub :
      qualified_type_subtype CT Ty
        (vpa_mutability_tt_abs_imm Ty (mreceiver (msignature mdef))) \/
      (sqtype Ty = RO /\ sqtype (mreceiver (msignature mdef)) = RDM /\
       base_subtype CT (sbase Ty) (sbase (mreceiver (msignature mdef)))))
    (Harg_sub :
      Forall2
        (fun arg T => qualified_type_subtype CT arg
          (vpa_mutability_tt_abs_imm Ty T))
        argtypes (mparams (msignature mdef))),
    wf_r_config CT
      (mreceiver (msignature mdef) :: mparams (msignature mdef))
      (mkr_env (Iot ly :: vals)) h.
Proof.
  intros CT sΓ' rΓ h y m zs vals ly cy mdef mdef0 Ty C argtypes Tthis
    Hwf Hval_y Hbase mdeflookup Href Hfind_m Hget_y Hget_args Hthis Hargs
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
        rewrite (vpa_mutability_tt_sbase_abs_imm Ty (mreceiver (msignature mdef))) in Hrcv_sub.
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
    destruct v as [|loc|n]; try trivial.
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
          | Int _ => True
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
    rewrite (vpa_mutability_tt_sbase_abs_imm Ty) in Harg_sub.
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

    ---- assert (Harg_sub_static :
           Forall2
             (fun arg T => qualified_type_subtype CT arg
               (vpa_mutability_tt_abs_imm Ty T))
             argtypes (mparams (msignature mdef0))).
         { rewrite <- Hmsigeq. exact Harg_sub. }
         refine (@call_int_arg_base_abs CT sΓ' rΓ h zs vals argtypes Ty
          mdef mdef0 i' sqt n OutterReceiverAddr qrout Harg_sub_static Hget_args
          Hargs Hval_i _ Hmsigeq OutterReceiverGetAddr_copy H5_copy
          Hcorrcopy2).
         simpl. exact Hnth.

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
  forall CT sΓ mt rΓ h x y m zs sΓ' vals ly cy mdef
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt (SCall x y m zs) sΓ')
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
  intros CT sΓ mt rΓ h x y m zs sΓ' vals ly cy mdef
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
    { eapply runtime_call_signature_agrees with (C := C); eauto. }
    rewrite <- Hsig in Hrcv_sub, Harg_sub.
    eapply callee_frame_wf_abs; eauto.
  - assert (Hsig : msignature mdef = msignature mdef0).
    { eapply runtime_call_signature_agrees with (C := C); eauto. }
    rewrite <- Hsig in Hrcv_sub, Harg_sub.
    eapply callee_frame_wf_rs_ts; eauto.
Qed.

(** Collect all facts about the dynamically selected target of a typed call.
    In particular, clients do not need to distinguish a method declared in
    the receiver class from one inherited from an ancestor. *)
Lemma typed_call_target :
  forall CT sΓ mt rΓ h x y m zs sΓ' vals ly cy mdef
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt (SCall x y m zs) sΓ')
    (Hval_y : runtime_getVal rΓ y = Some (Iot ly))
    (Hbase : r_basetype h ly = Some cy)
    (Hfind : FindMethodWithName CT cy m mdef)
    (Hargs : runtime_lookup_list rΓ zs = Some vals),
    exists D ddef sΓbody',
      class_subtype CT cy D /\
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
  intros CT sΓ mt rΓ h x y m zs sΓ' vals ly cy mdef
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
  destruct (typed_call_has_wf_callee_frame CT sΓ mt rΓ h x y m zs
              sΓ' vals ly cy mdef Hwf Htyping Hval_y Hbase Hfind Hargs)
    as [sΓbody' [Hbody Hframe]].
  exists D, ddef, sΓbody'.
  exact (conj Hsub
    (conj Hfind_D
      (conj Hin
        (conj Hwf_method
          (conj Hbody Hframe))))).
Qed.
