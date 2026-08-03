Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation Properties.

From Stdlib Require Import List.
From Stdlib Require String.
Import ListNotations.

(* ------------------------------------------------------------- *)
Lemma call_arguments_subtype_runtime :
  forall (adapt : qualified_type -> qualified_type -> qualified_type)
    CT Ty argtypes static_params runtime_params,
    Forall2
      (fun arg static_param =>
        qualified_type_subtype CT arg (adapt Ty static_param))
      argtypes static_params ->
    Forall2
      (fun static_param runtime_param =>
        qualified_type_subtype CT
          (adapt Ty static_param) (adapt Ty runtime_param))
      static_params runtime_params ->
    Forall2
      (fun arg runtime_param =>
        qualified_type_subtype CT arg (adapt Ty runtime_param))
      argtypes runtime_params.
Proof.
  intros adapt CT Ty argtypes static_params runtime_params
    Hargs Hparams.
  eapply (Forall2_trans
    (fun arg static_param =>
      qualified_type_subtype CT arg (adapt Ty static_param))
    (fun static_param runtime_param =>
      qualified_type_subtype CT
        (adapt Ty static_param) (adapt Ty runtime_param))
    (fun arg runtime_param =>
      qualified_type_subtype CT arg (adapt Ty runtime_param))).
  - intros. eapply qtype_trans; eauto.
  - exact Hargs.
  - exact Hparams.
Qed.

Lemma callee_frame_wf_rs_ts :
  forall CT sΓ' rΓ h y m zs vals ly cy mdef Ty argtypes Tthis
    (Hwf : wf_r_config CT sΓ' rΓ h)
    (Hval_y : runtime_getVal rΓ y = Some (Iot ly))
    (Hbase : r_basetype h ly = Some cy)
    (Hfind_m : FindMethodWithName CT (sctype Ty) m mdef)
    (Hget_y : static_getType sΓ' y = Some Ty)
    (Hget_args : static_getType_list sΓ' zs = Some argtypes)
    (Hthis : get_this_qualified_type sΓ' = Some Tthis)
    (Hargs : runtime_lookup_list rΓ zs = Some vals)
    (Hrcv_sub :
      qualified_type_subtype CT Ty
        (vpa_mutability_tt_readonly_state Ty (mreceiver (msignature mdef))))
    (Harg_sub :
      Forall2
        (fun arg T => qualified_type_subtype CT arg
          (vpa_mutability_tt_readonly_state Ty T))
        argtypes (mparams (msignature mdef))),
    wf_r_config CT
      (mreceiver (msignature mdef) :: mparams (msignature mdef))
      (mkr_env (Iot ly :: vals)) h.
Proof.
  intros CT sΓ' rΓ h y m zs vals ly cy mdef Ty argtypes Tthis
    Hwf Hval_y Hbase Hfind_m Hget_y Hget_args Hthis Hargs
    Hrcv_sub Harg_sub.
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
    eapply senv_var_domain; eauto.
    --
      eapply method_sig_wf_parameters_by_find; eauto.
      eapply senv_var_domain; eauto.
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
  assert (Hytypable: wf_r_typable CT h ly Ty qrout).
  {
    eapply correspondence_to_typable with (ι := OutterReceiverAddr).
    - exact OutterReceiverGetAddr.
    - exact H5.
    - exact (Hcorr OutterReceiverAddr qrout OutterReceiverGetAddr H5).
    - exact Hy_dom.
    - exact Hget_y.
    - exact Hval_y.
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
      apply qualified_type_subtype_base_subtype in Hrcv_sub.
      rewrite (vpa_mutability_tt_sctype_readonly_state Ty
        (mreceiver (msignature mdef))) in Hrcv_sub.
      eapply base_trans; [exact Hsubtype|exact Hrcv_sub].

  ---
  (* receiver qualifier type subtype preserved *)
  apply qualified_type_subtype_q_subtype in Hrcv_sub.
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
    rewrite sq_vpa_tt_eq_qq_readonly_state in Hrcv_sub.
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
    rewrite (vpa_mutability_tt_sctype_readonly_state Ty) in Harg_sub.
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
    apply qualified_type_subtype_q_subtype in Hrcv_sub.
    clear - Harg_qual_subtype Houtterqualifier HInnerReceiverQualifier Harg_sub.
    rewrite sq_vpa_tt_eq_qq_readonly_state in Harg_sub.
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
  forall CT sΓ' rΓ h y m zs vals ly cy mdef Ty argtypes Tthis
    (Hwf : wf_r_config CT sΓ' rΓ h)
    (Hval_y : runtime_getVal rΓ y = Some (Iot ly))
    (Hbase : r_basetype h ly = Some cy)
    (Hfind_m : FindMethodWithName CT (sctype Ty) m mdef)
    (Hget_y : static_getType sΓ' y = Some Ty)
    (Hget_args : static_getType_list sΓ' zs = Some argtypes)
    (Hthis : get_this_qualified_type sΓ' = Some Tthis)
    (Hargs : runtime_lookup_list rΓ zs = Some vals)
    (Hrcv_sub :
      qualified_type_subtype CT Ty
        (vpa_mutability_tt_abstract_state Ty (mreceiver (msignature mdef))))
    (Harg_sub :
      Forall2
        (fun arg T => qualified_type_subtype CT arg
          (vpa_mutability_tt_abstract_state Ty T))
        argtypes (mparams (msignature mdef))),
    wf_r_config CT
      (mreceiver (msignature mdef) :: mparams (msignature mdef))
      (mkr_env (Iot ly :: vals)) h.
Proof.
  intros CT sΓ' rΓ h y m zs vals ly cy mdef Ty argtypes Tthis
    Hwf Hval_y Hbase Hfind_m Hget_y Hget_args Hthis Hargs
    Hrcv_sub Harg_sub.
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
      eapply senv_var_domain; eauto.
    --
      eapply method_sig_wf_parameters_by_find; eauto.
      eapply senv_var_domain; eauto.
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
  assert (Hytypable: wf_r_typable CT h ly Ty qrout).
  {
    eapply correspondence_to_typable with (ι := OutterReceiverAddr).
    - exact OutterReceiverGetAddr.
    - exact H5.
    - exact (Hcorr OutterReceiverAddr qrout OutterReceiverGetAddr H5).
    - exact Hy_dom.
    - exact Hget_y.
    - exact Hval_y.
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
      apply qualified_type_subtype_base_subtype in Hrcv_sub.
      rewrite (vpa_mutability_tt_sctype_abstract_state Ty
        (mreceiver (msignature mdef))) in Hrcv_sub.
      eapply base_trans; [exact Hsubtype|exact Hrcv_sub].
  ---
  (* receiver qualifier type subtype preserved *)
  apply qualified_type_subtype_q_subtype in Hrcv_sub.
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
    rewrite sq_vpa_tt_eq_qq_abstract_state in Hrcv_sub.
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
    rewrite (vpa_mutability_tt_sctype_abstract_state Ty) in Harg_sub.
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
    apply qualified_type_subtype_q_subtype in Hrcv_sub.
    clear - Harg_qual_subtype Houtterqualifier HInnerReceiverQualifier Harg_sub.
    rewrite sq_vpa_tt_eq_qq_abstract_state in Harg_sub.
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
        (mscope (msignature mdef))
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
  - have Hstatic_frame :
      wf_r_config CT
        (mreceiver (msignature mdef0) :: mparams (msignature mdef0))
        (mkr_env (Iot ly :: vals)) h.
    { eapply callee_frame_wf_abs; eauto. }
    have Hrefine :
      method_signature_refinement CT
        (msignature mdef) (msignature mdef0).
    { eapply runtime_call_signature_refines.
      - exact Hwf.
      - exact Hget_y.
      - exact Hval_y.
      - exact Hbase.
      - exact Hfind.
      - exact Hfind_m. }
    destruct (method_lookup_in_wellformed_inherited
      CT cy m mdef Hwf_ct Hcy_dom Hfind)
      as [D [ddef [Hruntime_receiver [_ [_ Hwf_runtime]]]]].
    unfold wf_method in Hwf_runtime; simpl in Hwf_runtime.
    destruct Hwf_runtime as
      [_ [sΓD [retD [_ [_ [_ [_ [_ [Hreceiver_D _]]]]]]]]].
    have Hruntime_receiver' :
      base_subtype CT cy (sctype (mreceiver (msignature mdef))).
    { rewrite Hreceiver_D. exact Hruntime_receiver. }
    eapply refinement_preserves_callee_frame; eauto.
  - have Hstatic_frame :
      wf_r_config CT
        (mreceiver (msignature mdef0) :: mparams (msignature mdef0))
        (mkr_env (Iot ly :: vals)) h.
    { eapply callee_frame_wf_rs_ts; eauto. }
    have Hrefine :
      method_signature_refinement CT
        (msignature mdef) (msignature mdef0).
    { eapply runtime_call_signature_refines.
      - exact Hwf.
      - exact Hget_y.
      - exact Hval_y.
      - exact Hbase.
      - exact Hfind.
      - exact Hfind_m. }
    destruct (method_lookup_in_wellformed_inherited
      CT cy m mdef Hwf_ct Hcy_dom Hfind)
      as [D [ddef [Hruntime_receiver [_ [_ Hwf_runtime]]]]].
    unfold wf_method in Hwf_runtime; simpl in Hwf_runtime.
    destruct Hwf_runtime as
      [_ [sΓD [retD [_ [_ [_ [_ [_ [Hreceiver_D _]]]]]]]]].
    have Hruntime_receiver' :
      base_subtype CT cy (sctype (mreceiver (msignature mdef))).
    { rewrite Hreceiver_D. exact Hruntime_receiver. }
    eapply refinement_preserves_callee_frame; eauto.
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
        (mscope (msignature mdef))
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

(** A call made from a readonly/transitive scope can only dispatch to a
    method whose well-formed signature contains no mutable roots.  The fact
    is established at method declaration time, not as an operational
    dispatch premise. *)
Lemma typed_safe_call_runtime_no_mutable_roots :
  forall CT sΓ mt rΓ h x m y zs sΓ' ly cy runtime_mdef,
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ mt (SCall x m y zs) sΓ' ->
    readonly_state_method_scope mt ->
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m runtime_mdef ->
    signature_has_no_mutable_roots (msignature runtime_mdef).
Proof.
  intros CT sΓ mt rΓ h x m y zs sΓ' ly cy runtime_mdef
    Hwf Htyping Hsafe_scope Hval_y Hbase Hfind_runtime.
  have Hclass : wf_class_table CT.
  { unfold wf_r_config in Hwf. exact (proj1 Hwf). }
  have Hcy_dom : cy < dom CT.
  {
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [Hheap _]].
    eapply r_basetype_in_dom; eauto.
  }
  destruct (method_lookup_in_wellformed_inherited
    CT cy m runtime_mdef Hclass Hcy_dom Hfind_runtime)
    as [D [ddef [Hsub [HfindD [HinD Hwf_runtime]]]]].
  inversion Htyping; subst.
  - exfalso.
    destruct Hscope as [-> | [-> _]];
      destruct Hsafe_scope; congruence.
  - apply (wf_method_readonly_roots CT D runtime_mdef Hwf_runtime).
    have Hscope_eq :
      mscope (msignature runtime_mdef) = mscope (msignature mdef).
    { eapply runtime_call_scope_eq; eauto. }
    rewrite Hscope_eq.
    unfold readonly_state_method_scope.
    destruct (mscope (msignature mdef));
      try contradiction; auto.
Qed.

(* Soundness properties for PICO *)
Theorem preservation_pico :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ'
    (Hwf     : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Heval   : eval_stmt CT rΓ h stmt OK rΓ' h'),
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
      have Hwf_runtime_method := H2.
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

      assert (Hrefine :
        method_signature_refinement CT
          (msignature mdef) (msignature mdef0)).
      {
        eapply runtime_call_signature_refines; eauto.
      }
      assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
      {
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        destruct (typed_call_has_wf_callee_frame
          CT _ _ rΓ h x m y zs _ vals ly cy mdef
          Hwfcopy Htyping_copy Hval_y Hbase mdeflookupcopy Hargs)
          as [sΓbody' [_ Hframe]].
        exact Hframe.
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
              unfold runtime_getVal in Hmet_val.
              rewrite getmbody in Hretval.
              rewrite Hmet_val in Hretval.
              inversion Hretval.
              subst loc.
              assert (HOutterReceiverAddrInit :
                get_this_var_mapping (vars rΓ) = Some ι).
              {
                eapply eval_stmt_preserves_receiver_addr_typed_backwards; eauto.
              }
              assert (HOutterReceiverMutabilityInit :
                r_muttype h ι = Some qcontext).
              {
                eapply eval_stmt_preserves_r_muttype_backwards; eauto.
              }
              have Htarget_initial :=
                Hcorr_copy ι qcontext HOutterReceiverAddrInit
                  HOutterReceiverMutabilityInit y Hy_dom Ty Hget_y.
              rewrite Hval_y in Htarget_initial.
              destruct (r_type h ly) as [target_runtime_type|]
                eqn:Htarget_type.
              2:{
                unfold r_type, r_basetype in Htarget_type, Hbase.
                destruct (runtime_getObj h ly); discriminate.
              }
              assert (Htarget_type_preserved :
                r_type h' ly = Some target_runtime_type).
              {
                eapply eval_stmt_preserves_r_type; eauto.
                unfold r_basetype in Hbase.
                destruct (runtime_getObj h ly) as [target_obj|] eqn:Htarget_obj;
                  [eapply runtime_getObj_dom; eauto | discriminate].
              }
              have Htarget_final :
                wf_r_typable CT h' ly Ty qcontext.
              {
                unfold wf_r_typable in Htarget_initial |- *.
                rewrite Htarget_type in Htarget_initial.
                rewrite Htarget_type_preserved.
                exact Htarget_initial.
              }
              have Hdynamic_result :
                wf_r_typable CT h' l (mret (msignature mdef)) q.
              {
                eapply wf_r_typable_subtype; eauto.
                exact (proj1 Hsubtype_ret).
              }
              assert (Hbase_final : r_basetype h' ly = Some cy).
              {
                unfold r_type in Htarget_type, Htarget_type_preserved.
                unfold r_basetype in Hbase |- *.
                destruct (runtime_getObj h ly) as [[[target_q target_c] fs]|]
                  eqn:Htarget_obj; [|discriminate].
                simpl in Hbase, Htarget_type.
                injection Hbase as <-.
                injection Htarget_type as <-.
                destruct (runtime_getObj h' ly) as [[[target_q' target_c'] fs']|]
                  eqn:Htarget_obj'; [|discriminate].
                simpl in Htarget_type_preserved |- *.
                injection Htarget_type_preserved as -> ->.
                reflexivity.
              }
              have Hruntime_receiver :
                base_subtype CT cy (sctype (mreceiver (msignature mdef))).
              {
                rewrite (wf_method_receiver_class CT cy mdef Hwf_runtime_method).
                apply base_refl.
                eapply r_basetype_in_dom; eauto.
              }
              eapply refinement_preserves_call_result_abstract; eauto.
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

      have Hwf_runtime_method := H2.
      destruct H2 as [_ [sΓmethodend [mrettype Htyping_method]]].
      destruct Htyping_method as [Htyping_method Hmethodret].
      rewrite <- getmbody in Htyping_method.
      remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit.
      remember {| vars := Iot ly :: vals |} as rΓmethodinit.
      remember (set_vars rΓ (update x retval (vars rΓ))) as rΓ'''.
      destruct (r_muttype h ly) as [q|] eqn:Hinnerthis.
      2:{
        unfold r_muttype, r_basetype in Hinnerthis, Hbase.
        destruct (runtime_getObj h ly); discriminate.
      }
      assert (Hrefine :
        method_signature_refinement CT
          (msignature mdef) (msignature mdef0)).
      {
        eapply runtime_call_signature_refines; eauto.
      }
      assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
      {
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        destruct (typed_call_has_wf_callee_frame
          CT _ _ rΓ h x m y zs _ vals ly cy mdef
          Hwfcopy Htyping_copy Hval_y Hbase mdeflookupcopy Hargs)
          as [sΓbody' [_ Hframe]].
        exact Hframe.
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
            destruct Hreceiver as
              [outterreceiveinitriot [Hget_outter_iot Houtter_iot_dom]].
            assert (HInnerReceiverAddr :
              get_this_var_mapping (vars rΓ'') = Some ly).
            {
              eapply eval_stmt_preserves_receiver_addr_typed; eauto.
              unfold get_this_var_mapping.
              rewrite HeqrΓmethodinit.
              reflexivity.
            }
            assert (HInnerReceiverMutability :
              r_muttype h' ly = Some q).
            {
              eapply eval_stmt_preserves_r_muttype; eauto.
              unfold r_basetype in Hbase.
              destruct (runtime_getObj h ly) as [objly|] eqn:Hobj;
                [eapply runtime_getObj_dom; eauto | discriminate].
            }
            specialize (Hcorrinit ly q HInnerReceiverAddr
              HInnerReceiverMutability (mreturn (Syntax.mbody mdef))
              Hret_dom mrettype Hnth_mbodyret).
            destruct (runtime_getVal rΓ'' (mreturn (Syntax.mbody mdef))) eqn: Hmet_val; [|easy].
            destruct v.
            2:{
              unfold runtime_getVal in Hmet_val.
              rewrite getmbody in Hretval.
              rewrite Hmet_val in Hretval.
              inversion Hretval.
              subst loc.
              assert (HOutterReceiverAddrInit :
                get_this_var_mapping (vars rΓ) = Some ι).
              {
                eapply eval_stmt_preserves_receiver_addr_typed_backwards; eauto.
              }
              assert (HOutterReceiverMutabilityInit :
                r_muttype h ι = Some qoutter).
              {
                eapply eval_stmt_preserves_r_muttype_backwards; eauto.
              }
              have Htarget_initial :=
                Hcorr_copy ι qoutter HOutterReceiverAddrInit
                  HOutterReceiverMutabilityInit y
                  (static_getType_dom _ _ _ Hget_y) Ty Hget_y.
              rewrite Hval_y in Htarget_initial.
              destruct (r_type h ly) as [target_runtime_type|]
                eqn:Htarget_type.
              2:{
                unfold r_type, r_basetype in Htarget_type, Hbase.
                destruct (runtime_getObj h ly); discriminate.
              }
              assert (Htarget_type_preserved :
                r_type h' ly = Some target_runtime_type).
              {
                eapply eval_stmt_preserves_r_type; eauto.
                unfold r_basetype in Hbase.
                destruct (runtime_getObj h ly) as [target_obj|]
                  eqn:Htarget_obj;
                  [eapply runtime_getObj_dom; eauto | discriminate].
              }
              have Htarget_final :
                wf_r_typable CT h' ly Ty qoutter.
              {
                unfold wf_r_typable in Htarget_initial |- *.
                rewrite Htarget_type in Htarget_initial.
                rewrite Htarget_type_preserved.
                exact Htarget_initial.
              }
              have Hdynamic_result :
                wf_r_typable CT h' l (mret (msignature mdef)) q.
              {
                eapply wf_r_typable_subtype; eauto.
                exact (proj1 Hsubtype_ret).
              }
              assert (Hbase_final : r_basetype h' ly = Some cy).
              {
                unfold r_type in Htarget_type, Htarget_type_preserved.
                unfold r_basetype in Hbase |- *.
                destruct (runtime_getObj h ly) as [[[target_q target_c] fs]|]
                  eqn:Htarget_obj; [|discriminate].
                simpl in Hbase, Htarget_type.
                injection Hbase as <-.
                injection Htarget_type as <-.
                destruct (runtime_getObj h' ly) as [[[target_q' target_c'] fs']|]
                  eqn:Htarget_obj'; [|discriminate].
                simpl in Htarget_type_preserved |- *.
                injection Htarget_type_preserved as -> ->.
                reflexivity.
              }
              have Hruntime_receiver :
                base_subtype CT cy (sctype (mreceiver (msignature mdef))).
              {
                rewrite (wf_method_receiver_class CT D mdef
                  Hwf_runtime_method).
                eapply base_trans; eauto.
                apply base_refl.
                eapply base_subtype_domain; eauto.
              }
              eapply refinement_preserves_call_result_abstract; eauto.
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
      have Hwf_runtime_method := H2.
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

      assert (Hrefine :
        method_signature_refinement CT
          (msignature mdef) (msignature mdef0)).
      {
        eapply runtime_call_signature_refines; eauto.
      }
      assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
      {
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        destruct (typed_call_has_wf_callee_frame
          CT _ _ rΓ h x m y zs _ vals ly cy mdef
          Hwfcopy Htyping_copy Hval_y Hbase mdeflookupcopy Hargs)
          as [sΓbody' [_ Hframe]].
        exact Hframe.
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
              unfold runtime_getVal in Hmet_val.
              rewrite getmbody in Hretval.
              rewrite Hmet_val in Hretval.
              inversion Hretval.
              subst loc.
              assert (HOutterReceiverAddrInit :
                get_this_var_mapping (vars rΓ) = Some ι).
              {
                eapply eval_stmt_preserves_receiver_addr_typed_backwards; eauto.
              }
              assert (HOutterReceiverMutabilityInit :
                r_muttype h ι = Some qcontext).
              {
                eapply eval_stmt_preserves_r_muttype_backwards; eauto.
              }
              have Htarget_initial :=
                Hcorr_copy ι qcontext HOutterReceiverAddrInit
                  HOutterReceiverMutabilityInit y Hy_dom Ty Hget_y.
              rewrite Hval_y in Htarget_initial.
              destruct (r_type h ly) as [target_runtime_type|]
                eqn:Htarget_type.
              2:{
                unfold r_type, r_basetype in Htarget_type, Hbase.
                destruct (runtime_getObj h ly); discriminate.
              }
              assert (Htarget_type_preserved :
                r_type h' ly = Some target_runtime_type).
              {
                eapply eval_stmt_preserves_r_type; eauto.
                unfold r_basetype in Hbase.
                destruct (runtime_getObj h ly) as [target_obj|]
                  eqn:Htarget_obj;
                  [eapply runtime_getObj_dom; eauto | discriminate].
              }
              have Htarget_final :
                wf_r_typable CT h' ly Ty qcontext.
              {
                unfold wf_r_typable in Htarget_initial |- *.
                rewrite Htarget_type in Htarget_initial.
                rewrite Htarget_type_preserved.
                exact Htarget_initial.
              }
              have Hdynamic_result :
                wf_r_typable CT h' l (mret (msignature mdef)) q.
              {
                eapply wf_r_typable_subtype; eauto.
                exact (proj1 Hsubtype_ret).
              }
              assert (Hbase_final : r_basetype h' ly = Some cy).
              {
                unfold r_type in Htarget_type, Htarget_type_preserved.
                unfold r_basetype in Hbase |- *.
                destruct (runtime_getObj h ly) as [[[target_q target_c] fs]|]
                  eqn:Htarget_obj; [|discriminate].
                simpl in Hbase, Htarget_type.
                injection Hbase as <-.
                injection Htarget_type as <-.
                destruct (runtime_getObj h' ly) as [[[target_q' target_c'] fs']|]
                  eqn:Htarget_obj'; [|discriminate].
                simpl in Htarget_type_preserved |- *.
                injection Htarget_type_preserved as -> ->.
                reflexivity.
              }
              have Hruntime_receiver :
                base_subtype CT cy (sctype (mreceiver (msignature mdef))).
              {
                rewrite (wf_method_receiver_class CT cy mdef Hwf_runtime_method).
                apply base_refl.
                eapply r_basetype_in_dom; eauto.
              }
              eapply refinement_preserves_call_result_readonly; eauto.
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

      have Hwf_runtime_method := H2.
      destruct H2 as [_ [sΓmethodend [mrettype Htyping_method]]].
      destruct Htyping_method as [Htyping_method Hmethodret].
      rewrite <- getmbody in Htyping_method.
      remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit.
      remember {| vars := Iot ly :: vals |} as rΓmethodinit.
      remember (set_vars rΓ (update x retval (vars rΓ))) as rΓ'''.
      destruct (r_muttype h ly) as [q|] eqn:Hinnerthis.
      2:{
        unfold r_muttype, r_basetype in Hinnerthis, Hbase.
        destruct (runtime_getObj h ly); discriminate.
      }
      assert (Hrefine :
        method_signature_refinement CT
          (msignature mdef) (msignature mdef0)).
      {
        eapply runtime_call_signature_refines; eauto.
      }
      assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
      {
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        destruct (typed_call_has_wf_callee_frame
          CT _ _ rΓ h x m y zs _ vals ly cy mdef
          Hwfcopy Htyping_copy Hval_y Hbase mdeflookupcopy Hargs)
          as [sΓbody' [_ Hframe]].
        exact Hframe.
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
            destruct Hreceiver as
              [outterreceiveinitriot [Hget_outter_iot Houtter_iot_dom]].
            assert (HInnerReceiverAddr :
              get_this_var_mapping (vars rΓ'') = Some ly).
            {
              eapply eval_stmt_preserves_receiver_addr_typed; eauto.
              unfold get_this_var_mapping.
              rewrite HeqrΓmethodinit.
              reflexivity.
            }
            assert (HInnerReceiverMutability :
              r_muttype h' ly = Some q).
            {
              eapply eval_stmt_preserves_r_muttype; eauto.
              unfold r_basetype in Hbase.
              destruct (runtime_getObj h ly) as [objly|] eqn:Hobj;
                [eapply runtime_getObj_dom; eauto | discriminate].
            }
            specialize (Hcorrinit ly q HInnerReceiverAddr
              HInnerReceiverMutability (mreturn (Syntax.mbody mdef))
              Hret_dom mrettype Hnth_mbodyret).
            destruct (runtime_getVal rΓ'' (mreturn (Syntax.mbody mdef))) eqn: Hmet_val; [|easy].
            destruct v.
            2:{
              unfold runtime_getVal in Hmet_val.
              rewrite getmbody in Hretval.
              rewrite Hmet_val in Hretval.
              inversion Hretval.
              subst loc.
              assert (HOutterReceiverAddrInit :
                get_this_var_mapping (vars rΓ) = Some ι).
              {
                eapply eval_stmt_preserves_receiver_addr_typed_backwards; eauto.
              }
              assert (HOutterReceiverMutabilityInit :
                r_muttype h ι = Some qoutter).
              {
                eapply eval_stmt_preserves_r_muttype_backwards; eauto.
              }
              have Htarget_initial :=
                Hcorr_copy ι qoutter HOutterReceiverAddrInit
                  HOutterReceiverMutabilityInit y
                  (static_getType_dom _ _ _ Hget_y) Ty Hget_y.
              rewrite Hval_y in Htarget_initial.
              destruct (r_type h ly) as [target_runtime_type|]
                eqn:Htarget_type.
              2:{
                unfold r_type, r_basetype in Htarget_type, Hbase.
                destruct (runtime_getObj h ly); discriminate.
              }
              assert (Htarget_type_preserved :
                r_type h' ly = Some target_runtime_type).
              {
                eapply eval_stmt_preserves_r_type; eauto.
                unfold r_basetype in Hbase.
                destruct (runtime_getObj h ly) as [target_obj|]
                  eqn:Htarget_obj;
                  [eapply runtime_getObj_dom; eauto | discriminate].
              }
              have Htarget_final :
                wf_r_typable CT h' ly Ty qoutter.
              {
                unfold wf_r_typable in Htarget_initial |- *.
                rewrite Htarget_type in Htarget_initial.
                rewrite Htarget_type_preserved.
                exact Htarget_initial.
              }
              have Hdynamic_result :
                wf_r_typable CT h' l (mret (msignature mdef)) q.
              {
                eapply wf_r_typable_subtype; eauto.
                exact (proj1 Hsubtype_ret).
              }
              assert (Hbase_final : r_basetype h' ly = Some cy).
              {
                unfold r_type in Htarget_type, Htarget_type_preserved.
                unfold r_basetype in Hbase |- *.
                destruct (runtime_getObj h ly) as [[[target_q target_c] fs]|]
                  eqn:Htarget_obj; [|discriminate].
                simpl in Hbase, Htarget_type.
                injection Hbase as <-.
                injection Htarget_type as <-.
                destruct (runtime_getObj h' ly) as [[[target_q' target_c'] fs']|]
                  eqn:Htarget_obj'; [|discriminate].
                simpl in Htarget_type_preserved |- *.
                injection Htarget_type_preserved as -> ->.
                reflexivity.
              }
              have Hruntime_receiver :
                base_subtype CT cy (sctype (mreceiver (msignature mdef))).
              {
                rewrite (wf_method_receiver_class CT D mdef
                  Hwf_runtime_method).
                eapply base_trans; eauto.
                apply base_refl.
                eapply base_subtype_domain; eauto.
              }
              eapply refinement_preserves_call_result_readonly; eauto.
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
