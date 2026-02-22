From Stdlib Require Import List.
From Stdlib Require String.
Import ListNotations.
From RecordUpdate Require Import RecordUpdate.

Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation Properties Reachability Preservation.

Definition LocSet      : Type := Ensembles.Ensemble Loc.

Lemma vpa_assingability_concret_imm_assign_cases: forall q a,
  vpa_assignability_concret_imm q a = Assignable ->
  (a = Assignable) \/
  (q = Mut /\ a = RDA).
Proof.
  intros q a Hvpa.
  unfold vpa_assignability_concret_imm in Hvpa.
  destruct q, a; simpl in Hvpa; try discriminate; auto.
Qed.

Theorem shallow_immutability_pico :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ' l C vals vals' f,
    l < dom h ->
    runtime_getObj h l = Some (mkObj (mkruntime_type Imm_r C) vals) ->
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ mt stmt sΓ' -> 
    eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h' ->
    runtime_getObj h' l = Some (mkObj (mkruntime_type Imm_r C) vals') ->
    sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA ->
    nth_error vals f = nth_error vals' f.
Proof.
  intros. remember OK as ok.
  generalize dependent sΓ.
  generalize dependent sΓ'.
  generalize dependent mt.
  generalize dependent vals. generalize dependent vals'.
  induction H3; try discriminate.
  - (* Skip *) 
   intros. inversion H2. subst.
   rewrite H0 in H4. injection H4; auto.
   intro H_eq.
   rewrite H_eq.
   reflexivity.
  - (* Local *) 
  intros. inversion H3. subst.
  rewrite H1 in H4. injection H4; auto.
  intro H_eq.
  rewrite H_eq.
  reflexivity.
  - (* VarAss *) 
  intros. inversion H6. subst.
  rewrite H2 in H4. injection H4; auto.
  intro H_eq.
  rewrite H_eq.
  reflexivity.
  - (* FldWrite *) 
  {
    intros.
    destruct (Nat.eq_dec l loc_x) as [Heq_l | Hneq_l].
    - (* Case: l = lx (same object being written to) *)
      subst l.
      (* Extract the object type from H0 and H6 *)
      rewrite H7 in H1.
      injection H1 as H1_eq.
      subst o.
      (* Now we have an immutable object, but can_assign returned true *)
      (* This should be impossible for Final/RDA fields on immutable objects *)
      destruct (Nat.eq_dec f f0) as [Heq_f | Hneq_f].
      + (* Case: f = f0 (same field being written) *)
        subst f.
        (* Show contradiction: can_assign should be false for immutable Final/RDA fields *)
        exfalso.
        unfold wf_r_config in H8.
        destruct H8 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
        assert (Hx_bound : x < dom sΓ) by (apply runtime_getVal_dom in H0; rewrite <- Hlen in H0; exact H0).
        inversion H9; subst.
        --
          unfold wf_renv in Hrenv.
          destruct Hrenv as [HrEnvLen [Hreceiver _]].
          destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
          assert (exists qcontext, r_muttype h iot = Some qcontext).
          {
            eapply receiver_mutability_exists_from_bound; eauto.
          }
          destruct H1 as [qcontext Hqcontext].
          specialize (Hcorr iot qcontext Hget_iot Hqcontext x Hx_bound Tx H12).
          rewrite H0 in Hcorr.
          unfold wf_r_typable in Hcorr.
          destruct (r_type h loc_x) as [rqt|] eqn:Hrtype; [|contradiction].
          unfold r_type in Hrtype.
          rewrite H7 in Hrtype.
          simpl in Hrtype.
          injection Hrtype as Hrtype_eq.
          destruct Hcorr as [Hbase_sub Htypable].
          destruct H5 as [Hffinal | HfRDA].
          have Hrctype_eq : rctype rqt = C by (rewrite <- Hrtype_eq; reflexivity).
          subst C.
          assert (Heq : Final = a).
          {
            eapply sf_assignability_consistent_subtype with (f := f0) (C := rctype rqt) (D := sctype Tx); eauto.
          }
          apply vpa_assingability_assign_cases in H22.
          destruct H22 as [HAassignable | HARDA ].
          ---
          rewrite HAassignable in Heq.
          discriminate.
          ---
          destruct HARDA as [_ HFinalRDA].
          rewrite HFinalRDA in Heq.
          discriminate.
          ---
          apply vpa_assingability_assign_cases in H22.
          destruct H22 as [HAassignable | HARDA ].
          have Hrctype_eq : rctype rqt = C by (rewrite <- Hrtype_eq; reflexivity).
          rewrite HAassignable in H19.
          subst C.
          assert (RDA = Assignable). {
            eapply sf_assignability_consistent_subtype with (f := f0) (C := rctype rqt) (D := sctype Tx); eauto.
          }
          discriminate.
          destruct HARDA as [HsqtypeMut _].
          unfold qualifier_typable_context in Htypable.
          unfold vpa_mutabilty_rs in Htypable.
          have Hrqtype_eq : rqtype rqt = Imm_r by (rewrite <- Hrtype_eq; reflexivity).
          rewrite Hrqtype_eq in Htypable.
          rewrite HsqtypeMut in Htypable.
          destruct qcontext;
          easy.
        --
          unfold wf_renv in Hrenv.
          destruct Hrenv as [HrEnvLen [Hreceiver _]].
          destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
          assert (exists qcontext, r_muttype h iot = Some qcontext).
          {
            eapply receiver_mutability_exists_from_bound; eauto.
          }
          destruct H1 as [qcontext Hqcontext].
          specialize (Hcorr iot qcontext Hget_iot Hqcontext x Hx_bound Tx H12).
          rewrite H0 in Hcorr.
          unfold wf_r_typable in Hcorr.
          destruct (r_type h loc_x) as [rqt|] eqn:Hrtype; [|contradiction].
          unfold r_type in Hrtype.
          rewrite H7 in Hrtype.
          simpl in Hrtype.
          injection Hrtype as Hrtype_eq.
          destruct Hcorr as [Hbase_sub Htypable].
          destruct H5 as [Hffinal | HfRDA].
          have Hrctype_eq : rctype rqt = C by (rewrite <- Hrtype_eq; reflexivity).
          subst C.
          assert (Heq : Final = a).
          {
            eapply sf_assignability_consistent_subtype with (f := f0) (C := rctype rqt) (D := sctype Tx); eauto.
          }
          apply vpa_assingability_assign_cases in H22.
          destruct H22 as [HAassignable | HARDA ].
          ---
          rewrite HAassignable in Heq.
          discriminate.
          ---
          destruct HARDA as [_ HFinalRDA].
          rewrite HFinalRDA in Heq.
          discriminate.
          ---
          apply vpa_assingability_assign_cases in H22.
          destruct H22 as [HAassignable | HARDA ].
          have Hrctype_eq : rctype rqt = C by (rewrite <- Hrtype_eq; reflexivity).
          rewrite HAassignable in H19.
          subst C.
          assert (RDA = Assignable). {
            eapply sf_assignability_consistent_subtype with (f := f0) (C := rctype rqt) (D := sctype Tx); eauto.
          }
          discriminate.
          destruct HARDA as [HsqtypeMut _].
          unfold qualifier_typable_context in Htypable.
          unfold vpa_mutabilty_rs in Htypable.
          have Hrqtype_eq : rqtype rqt = Imm_r by (rewrite <- Hrtype_eq; reflexivity).
          rewrite Hrqtype_eq in Htypable.
          rewrite HsqtypeMut in Htypable.
          destruct qcontext;
          easy.
        --unfold wf_renv in Hrenv.
          destruct Hrenv as [HrEnvLen [Hreceiver _]].
          destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
          assert (exists qcontext, r_muttype h iot = Some qcontext).
          {
            eapply receiver_mutability_exists_from_bound; eauto.
          }
          destruct H1 as [qcontext Hqcontext].
          specialize (Hcorr iot qcontext Hget_iot Hqcontext x Hx_bound Tx H12).
          rewrite H0 in Hcorr.
          unfold wf_r_typable in Hcorr.
          destruct (r_type h loc_x) as [rqt|] eqn:Hrtype; [|contradiction].
          unfold r_type in Hrtype.
          rewrite H7 in Hrtype.
          simpl in Hrtype.
          injection Hrtype as Hrtype_eq.
          destruct Hcorr as [Hbase_sub Htypable].
          destruct H5 as [Hffinal | HfRDA].
          have Hrctype_eq : rctype rqt = C by (rewrite <- Hrtype_eq; reflexivity).
          subst C.
          assert (Heq : Final = a).
          {
            eapply sf_assignability_consistent_subtype with (f := f0) (C := rctype rqt) (D := sctype Tx); eauto.
          }
          apply vpa_assingability_concret_imm_assign_cases in H22.
          destruct H22 as [HAassignable | HARDA ].
          ---
          rewrite HAassignable in Heq.
          discriminate.
          ---
          destruct HARDA as [_ HFinalRDA].
          rewrite HFinalRDA in Heq.
          discriminate.
          ---
          apply vpa_assingability_concret_imm_assign_cases in H22.
          destruct H22 as [HAassignable | HARDA ].
          have Hrctype_eq : rctype rqt = C by (rewrite <- Hrtype_eq; reflexivity).
          rewrite HAassignable in H19.
          subst C.
          assert (RDA = Assignable). {
            eapply sf_assignability_consistent_subtype with (f := f0) (C := rctype rqt) (D := sctype Tx); eauto.
          }
          discriminate.
          destruct HARDA as [HsqtypeMut _].
          unfold qualifier_typable_context in Htypable.
          unfold vpa_mutabilty_rs in Htypable.
          have Hrqtype_eq : rqtype rqt = Imm_r by (rewrite <- Hrtype_eq; reflexivity).
          rewrite Hrqtype_eq in Htypable.
          rewrite HsqtypeMut in Htypable.
          destruct qcontext;
          easy.  
        + 
        assert (Hvals_eq : vals' = [f0 ↦ val_y] (vals)).
        { 
          (* Use the definition of update_field and the fact that h' contains the updated object *)
          unfold update_field in H4.
          rewrite H7 in H4.
          rewrite H4 in H6.
          unfold runtime_getObj in H6.
          (* Apply update_same to get the updated object *)
          assert (Hget_same : nth_error (update loc_x {| rt_type := {| rqtype := Imm_r; rctype := C |}; fields_map := [f0 ↦ val_y] (vals) |} h) loc_x = 
                              Some {| rt_type := {| rqtype := Imm_r; rctype := C |}; fields_map := [f0 ↦ val_y] (vals) |}).
          {
            apply update_same.
            exact H.
          }
          rewrite Hget_same in H6.
          injection H6 as H6_eq.
          symmetry. exact H6_eq.
        }
        rewrite Hvals_eq.
        unfold getVal.
        rewrite update_diff.
        symmetry. exact Hneq_f.
        reflexivity.
    -
    assert (Hl_unchanged : runtime_getObj h' l = runtime_getObj h l).
    {
      unfold update_field in H4.
      rewrite H1 in H4.
      rewrite H4.
      unfold runtime_getObj.
      apply update_diff.
      easy.
    }
    rewrite H7 in Hl_unchanged.
    rewrite Hl_unchanged in H6.
    injection H6 as H6_eq.
    rewrite <- H6_eq.
    reflexivity.
  }
  - (* New *) (* h' = h ++ [new_obj], so l < dom h means same object *)
  intros.
  inversion H11; subst.
  (* Since l < dom h, the object at location l is unchanged *)
  unfold runtime_getObj in H8.
  rewrite List.nth_error_app1 in H8; auto.
  unfold runtime_getObj in H9.
  rewrite H9 in H8.
  injection H8; intros; subst.
  reflexivity.
  - (* Call *) (* Similar to other non-mutating cases *) 
  intros.
  revert H13.
  inversion H14.
  -- 
  revert H20.
  subst.
  intro H20.
  intro H13.
  destruct H2 as [mdeflookup getmbody].
  remember (msignature mdef) as msig.
  have mdeflookupcopy := mdeflookup.
  apply method_body_well_typed_by_find in mdeflookup; auto.
  destruct mdeflookup as [sΓmethodend Htyping_method].
  remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit.
  apply IHeval_stmt with (mt:=(mtype (msignature mdef)))(sΓ' := sΓmethodend)(sΓ := sΓmethodinit). 1-9: auto.
  remember {| vars := Iot ly :: vals |} as rΓmethodinit.
  destruct (r_muttype h ly) eqn: Hinnerthis.
  2:{
    unfold r_muttype in Hinnerthis.
    unfold r_basetype in H1.
    destruct (runtime_getObj h ly).
    discriminate Hinnerthis.
    discriminate H1.
  }
  assert (Hwf_method_frame : wf_r_config CT sΓmethodinit 
                                    rΓmethodinit h ).
  {
    have Hwf_copy := H13.
    unfold wf_r_config in H13.
    destruct H13 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    have Hclasstable := Hclass.
    destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
    repeat split.
    exact Hclass.
    exact Hobj.
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
    unfold runtime_getVal in H0.
    destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
    injection H0 as H_eq.
    subst v.
    eapply Forall_nth_error in Hallvals; eauto.
    simpl in Hallvals.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjly; [|contradiction].
    apply runtime_getObj_dom in Hobjly.

    exact Hobjly.
    rewrite HeqrΓmethodinit.
    simpl.
    constructor.
    simpl.
    unfold runtime_getVal in H0.
    destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
    injection H0 as H_eq.
    subst v.
    unfold runtime_getVal in Hnth_y.
    unfold wf_renv in Hrenv.
    destruct Hrenv as [_ [_ Hallvals]].
    eapply Forall_nth_error in Hallvals; eauto.
    simpl in Hallvals.
    exact Hallvals.
    eapply runtime_lookup_list_preserves_wf_values; eauto.

    rewrite HeqsΓmethodinit.
    simpl.
    lia.

    (* Inner static env's elements are wellformed typeuse *)
    rewrite HeqsΓmethodinit.
    constructor.
    (* Receiver type is well-formed *)
    eapply method_sig_wf_receiver_by_find; eauto.
    unfold r_basetype in H1.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
    injection H1 as H0_eq.
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
    destruct Hwf_rtypeuse as [Hwf_rtypeuse _].
    exact Hwf_rtypeuse.
    contradiction.

    eapply method_sig_wf_parameters_by_find; eauto.
    unfold r_basetype in H1.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
    injection H1 as H0_eq.
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
    destruct Hwf_rtypeuse as [Hwf_rtypeuse _].
    exact Hwf_rtypeuse.
    contradiction.

    apply static_getType_list_preserves_length in H21.
    apply runtime_lookup_list_preserves_length in H6.
    rewrite HeqsΓmethodinit.
    simpl.
    f_equal.
    apply Forall2_length in H31.
    rewrite <- Heqmsig.
    assert (Hy_dom : y < dom sΓ').
    {
      apply static_getType_dom in H20.
      exact H20.
    }

    unfold wf_renv in Hrenv.
    destruct Hrenv as [_ [Hreceiver _]].
    destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
    assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
    {
      eapply receiver_mutability_exists_from_bound; eauto.
    }
    destruct HOutterReceiverMutability as [qcontext Hqcontext].
    (* Apply correspondence to get wf_r_typable *)
    specialize (Hcorr iot qcontext Hget_iot Hqcontext y Hy_dom Ty H20).
    rewrite H0 in Hcorr.

    (* Extract subtyping from wf_r_typable *)
    unfold wf_r_typable in Hcorr.
    unfold r_basetype in H1.
    unfold r_type.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
    injection H1 as Hcy_eq.
    subst cy.
    destruct obj as [rt_obj fields_obj].
    destruct rt_obj as [rq_obj rc_obj].

    unfold r_type in Hcorr.
    rewrite Hobjy in Hcorr.
    simpl in Hcorr.
    destruct Hcorr as [Hsubtype _].
    rewrite <- H6 in H21.
    rewrite HeqrΓmethodinit.
    simpl.
    f_equal.
    rewrite <- H21.
    rewrite Heqmsig.
    rewrite H31.
    simpl in mdeflookupcopy.
    assert (msignature mdef = msignature mdef0).
    {
      eapply method_signature_consistent_subtype; eauto.
    }
    rewrite <- H1 in H29.
    rewrite <- H1 in H30.
    rewrite <- H1 in H31.
    rewrite H1.
    reflexivity.

    (* Typable! *)
    intros lInnerRecevier qinner HgetInnerReceiverAddr HgetInnerReceiverMutability i Hi sqt Hnth. 
      rewrite HeqsΓmethodinit in Hnth, Hi.
      rewrite HeqrΓmethodinit.
      simpl in *.
      destruct i as [|i'].
      (* Reciever *)
      simpl in Hnth.
      injection Hnth as Hsqt_eq.
      subst sqt.
      simpl.
      unfold wf_r_typable.
      unfold r_type.
      destruct (runtime_getObj h ly) as [objy|] eqn:Hobj_ly.
      2:{
        unfold r_basetype in H1.
        rewrite Hobj_ly in H1.
        discriminate.
      }

      assert (Hy_dom : y < dom sΓ').
      {
        apply static_getType_dom in H20.
        exact H20.
      }

      unfold wf_renv in Hrenv.
      destruct Hrenv as [_ [Hreceiver _]].
      destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
      assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
      {
        eapply receiver_mutability_exists_from_bound; eauto.
      }
      destruct HOutterReceiverMutability as [qoutter Hqoutter].
      (* Apply correspondence to get wf_r_typable *)
      specialize (Hcorr iot qoutter Hget_iot Hqoutter y Hy_dom Ty H20).
      unfold wf_r_typable in Hcorr.
      unfold r_basetype in H1.
      unfold r_type.
      destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
      destruct obj as [rt_obj fields_obj].
      destruct rt_obj as [rq_obj rc_obj].

      unfold r_type in Hcorr.
      rewrite H0 in Hcorr.
      rewrite Hobjy in Hcorr.
      simpl in Hcorr.
      destruct Hcorr as [Hsubtype Hqualifier].
      simpl in Hobj_ly.
      injection Hobj_ly as Hobjy_eq.

      simpl in H1.
      inversion H1.
      rewrite <- H3 in mdeflookupcopy.
      assert (Hsigeq: msignature mdef = msignature mdef0).
      {
        eapply method_signature_consistent_subtype; eauto.
      }

      split.
      - 
      destruct H30 as [H30 | H30].
        +
          apply qualified_type_subtype_base_subtype in H30.
          rewrite (vpa_mutabilty_tt_sctype_abs_imm Ty (mreceiver (msignature mdef0))) in H30.
          rewrite <- Hsigeq in H29.
          rewrite <- Hsigeq in H30.
          rewrite <- Hsigeq in H31.
          subst objy.
          simpl.
          eapply base_trans; eauto.
        +
          destruct H30 as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
          rewrite <- Hsigeq in H29.
          rewrite <- Hsigeq in HBaseSubtype.
          rewrite <- Hsigeq in H31.
          subst objy.
          simpl.
          eapply base_trans; eauto. 
      -
      destruct H30 as [H30 | H30].
      +
        apply qualified_type_subtype_q_subtype in H30.
        rewrite sq_vpa_tt_eq_qq_abs_imm in H30.
        rewrite <- Hsigeq in H29.
        rewrite <- Hsigeq in H30.
        rewrite <- Hsigeq in H31.
        rewrite <- Hobjy_eq.
        simpl.
        assert (Hrq_eq : rq_obj = q).
        {
          unfold r_muttype in Hinnerthis.
          rewrite Hobjy in Hinnerthis.
          simpl in Hinnerthis.
          inversion Hinnerthis; reflexivity.
        }
        subst q.
        assert (rq_obj = qinner).
        {
          rewrite HeqrΓmethodinit in HgetInnerReceiverAddr.
          simpl in HgetInnerReceiverAddr.
          inversion HgetInnerReceiverAddr; subst lInnerRecevier.
          clear HgetInnerReceiverAddr.

          (* Now both inner-this facts are about loc = ly *)
          rewrite Hinnerthis in HgetInnerReceiverMutability.
          inversion HgetInnerReceiverMutability; subst qinner.
          clear HgetInnerReceiverMutability.

          (* From Hobjy_eq we know objy has rqtype = rq_obj *)
          subst objy.
          simpl in *.
          reflexivity.
        }
        subst rq_obj.
        clear - H30 Hqualifier.
        destruct qinner eqn:Hqinner;
        destruct ((sqtype (mreceiver (msignature mdef)))) eqn:HMethodReceiverDeclaredType;
        try solve_qualifier_typable_correct_concrete.

        all:
        destruct (sqtype Ty) eqn:HTyStaticMutability;
        simpl in H30;
        try solve_q_subtype_wrong.

        all:
        destruct qoutter eqn:Hqoutter;
        try solve_qualifier_typable_wrong_concrete.
      +
        destruct H30 as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
        rewrite <- Hsigeq in H29.
        rewrite <- Hsigeq in HReceiverDeclearedQualifier.
        rewrite <- Hsigeq in H31.
        rewrite <- Hobjy_eq.
        simpl.
        assert (Hrq_eq : rq_obj = q).
        {
          unfold r_muttype in Hinnerthis.
          rewrite Hobjy in Hinnerthis.
          simpl in Hinnerthis.
          inversion Hinnerthis; reflexivity.
        }
        subst q.
        assert (rq_obj = qinner).
        {
          rewrite HeqrΓmethodinit in HgetInnerReceiverAddr.
          simpl in HgetInnerReceiverAddr.
          inversion HgetInnerReceiverAddr; subst lInnerRecevier.
          clear HgetInnerReceiverAddr.

          (* Now both inner-this facts are about loc = ly *)
          rewrite Hinnerthis in HgetInnerReceiverMutability.
          inversion HgetInnerReceiverMutability; subst qinner.
          clear HgetInnerReceiverMutability.

          (* From Hobjy_eq we know objy has rqtype = rq_obj *)
          subst objy.
          simpl in *.
          reflexivity.
        }
        subst rq_obj.
        clear -  HTyqualifier HReceiverDeclearedQualifier Hqualifier.
        rewrite HTyqualifier in Hqualifier.
        destruct qinner eqn:Hqinner;
        destruct ((sqtype (mreceiver (msignature mdef)))) eqn:HMethodReceiverDeclaredType;
        try solve_qualifier_typable_correct_concrete.

        all:
        destruct qoutter eqn:Hqoutter;
        try solve_qualifier_typable_wrong_concrete.
        all: try easy.

(* -------------------------------------------------- *)
      -
      destruct H30 as [H30 | H30].
      1:{
        apply qualified_type_subtype_q_subtype in H30.
        assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H20.
          exact H20.
        }
        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
        assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
        {
          eapply receiver_mutability_exists_from_bound; eauto.
        }
        destruct HOutterReceiverMutability as [qoutter Hqoutter].
        (* Apply correspondence to get wf_r_typable *)
        specialize (Hcorr iot qoutter Hget_iot Hqoutter y Hy_dom Ty H20).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H1.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        unfold r_type in Hcorr.
        rewrite H0 in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct Hcorr as [Hsubtype Hqualifier].

        simpl in mdeflookupcopy.
        simpl in H1.
        inversion H1.
        rewrite <- H3 in mdeflookupcopy.
        assert (Hsigeq: msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        rewrite <- Hsigeq in H29.
        rewrite <- Hsigeq in H30.
        rewrite <- Hsigeq in H31.

        simpl.
        unfold runtime_getVal.
        simpl.
        destruct (nth_error vals i') as [v|] eqn:Hval_i.
        + (* Parameter i' exists *)
          destruct v as [|loc]; [trivial|].
          assert (Hi'_bound : i' < List.length argtypes).
          {
            apply Forall2_length in H31.
            simpl in Hi.
            simpl in Hnth.
            lia.
          }
          assert (Harg_type : exists argtype, nth_error argtypes i' = Some argtype).
          {
            apply nth_error_Some_exists.
            exact Hi'_bound.
          }
          destruct Harg_type as [argtype Hargtype].
          eapply runtime_lookup_list_preserves_typing with (CT:= CT) (h:=h)in H6; eauto.
          eapply Forall2_nth_error in H6; eauto.
          eapply Forall2_nth_error in H31; eauto.
          simpl in H6.
          unfold wf_r_typable.
          unfold wf_r_typable in H6.
          destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
          destruct H6 as [Hsubtype_param Htypable_param].
          split.
          *
          apply qualified_type_subtype_base_subtype in H31.
          rewrite (vpa_mutabilty_tt_sctype_abs_imm Ty sqt) in H31.
          eapply base_trans; eauto.
          *
          apply qualified_type_subtype_q_subtype in H31.
          rewrite sq_vpa_tt_eq_qq_abs_imm in H31.
          assert (rq_obj = q).
          {
            unfold r_muttype in Hinnerthis.
            rewrite Hobjy in Hinnerthis.
            simpl in Hinnerthis.
            inversion Hinnerthis; reflexivity.
          }
          subst q.
          assert (rq_obj = qinner).
          {
            rewrite HeqrΓmethodinit in HgetInnerReceiverAddr.
            simpl in HgetInnerReceiverAddr.
            inversion HgetInnerReceiverAddr; subst lInnerRecevier.
            clear HgetInnerReceiverAddr.

            (* Now both inner-this facts are about loc = ly *)
            rewrite Hinnerthis in HgetInnerReceiverMutability.
            inversion HgetInnerReceiverMutability; subst qinner.
            clear HgetInnerReceiverMutability.
            reflexivity.
          }
          subst rq_obj.
          clear - H31 Htypable_param Hqualifier.
          destruct qinner eqn:Hqinner;
          destruct (sqtype sqt) eqn:HTxStaticMutability;
          destruct (rqtype rqt) eqn:Hrqtype;
          try solve_qualifier_typable_correct_concrete.
          all:
          destruct (sqtype Ty) eqn:HTyStaticMutability;
          destruct (sqtype argtype) eqn:Hargtype_static;
          simpl in H31;
          try solve_q_subtype_wrong.
          all:
          destruct qoutter eqn:Hqoutter;
          try solve_qualifier_typable_wrong_concrete.
        + (* Parameter i' doesn't exist - contradiction *)
          exfalso.
          apply nth_error_None in Hval_i.
          apply runtime_lookup_list_preserves_length in H6.
          apply static_getType_list_preserves_length in H21.
          apply Forall2_length in H31.
          rewrite H6 in Hval_i.
          rewrite <- H21 in Hval_i.
          rewrite H31 in Hval_i.
          simpl in Hi.
          simpl in Hnth.
          simpl in Hnth.
          lia.
        }
        1:{
          destruct H30 as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
          assert (Hy_dom : y < dom sΓ').
          {
            apply static_getType_dom in H20.
            exact H20.
          }
          unfold wf_renv in Hrenv.
          destruct Hrenv as [_ [Hreceiver _]].
          destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
          assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
          {
            eapply receiver_mutability_exists_from_bound; eauto.
          }
          destruct HOutterReceiverMutability as [qoutter Hqoutter].
          (* Apply correspondence to get wf_r_typable *)
          specialize (Hcorr iot qoutter Hget_iot Hqoutter y Hy_dom Ty H20).
          unfold wf_r_typable in Hcorr.
          unfold r_basetype in H1.
          unfold r_type.
          destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
          destruct obj as [rt_obj fields_obj].
          destruct rt_obj as [rq_obj rc_obj].

          unfold r_type in Hcorr.
          rewrite H0 in Hcorr.
          rewrite Hobjy in Hcorr.
          simpl in Hcorr.
          destruct Hcorr as [Hsubtype Hqualifier].

          simpl in mdeflookupcopy.
          simpl in H1.
          inversion H1.
          rewrite <- H3 in mdeflookupcopy.
          assert (Hsigeq: msignature mdef = msignature mdef0).
          {
            eapply method_signature_consistent_subtype; eauto.
          }
          rewrite <- Hsigeq in H29.
          rewrite <- Hsigeq in HReceiverDeclearedQualifier.
          rewrite <- Hsigeq in H31.

          simpl.
          unfold runtime_getVal.
          simpl.
          destruct (nth_error vals i') as [v|] eqn:Hval_i.
          + (* Parameter i' exists *)
            destruct v as [|loc]; [trivial|].
            assert (Hi'_bound : i' < List.length argtypes).
            {
              apply Forall2_length in H31.
              simpl in Hi.
              simpl in Hnth.
              lia.
            }
            assert (Harg_type : exists argtype, nth_error argtypes i' = Some argtype).
            {
              apply nth_error_Some_exists.
              exact Hi'_bound.
            }
            destruct Harg_type as [argtype Hargtype].
            eapply runtime_lookup_list_preserves_typing with (CT:= CT) (h:=h)in H6; eauto.
            eapply Forall2_nth_error in H6; eauto.
            eapply Forall2_nth_error in H31; eauto.
            simpl in H6.
            unfold wf_r_typable.
            unfold wf_r_typable in H6.
            destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
            destruct H6 as [Hsubtype_param Htypable_param].
            split.
            *
            apply qualified_type_subtype_base_subtype in H31.
            rewrite (vpa_mutabilty_tt_sctype_abs_imm Ty sqt) in H31.
            eapply base_trans; eauto.
            *
            apply qualified_type_subtype_q_subtype in H31.
            rewrite sq_vpa_tt_eq_qq_abs_imm in H31.
            assert (rq_obj = q).
            {
              unfold r_muttype in Hinnerthis.
              rewrite Hobjy in Hinnerthis.
              simpl in Hinnerthis.
              inversion Hinnerthis; reflexivity.
            }
            subst q.
            assert (rq_obj = qinner).
            {
              rewrite HeqrΓmethodinit in HgetInnerReceiverAddr.
              simpl in HgetInnerReceiverAddr.
              inversion HgetInnerReceiverAddr; subst lInnerRecevier.
              clear HgetInnerReceiverAddr.

              (* Now both inner-this facts are about loc = ly *)
              rewrite Hinnerthis in HgetInnerReceiverMutability.
              inversion HgetInnerReceiverMutability; subst qinner.
              clear HgetInnerReceiverMutability.
              reflexivity.
            }
            subst rq_obj.
            clear - H31 Htypable_param Hqualifier.
            destruct qinner eqn:Hqinner;
            destruct (sqtype sqt) eqn:HTxStaticMutability;
            destruct (rqtype rqt) eqn:Hrqtype;
            try solve_qualifier_typable_correct_concrete.
            all:
            destruct (sqtype Ty) eqn:HTyStaticMutability;
            destruct (sqtype argtype) eqn:Hargtype_static;
            simpl in H31;
            try solve_q_subtype_wrong.
            all:
            destruct qoutter eqn:Hqoutter;
            try solve_qualifier_typable_wrong_concrete.
          + (* Parameter i' doesn't exist - contradiction *)
            exfalso.
            apply nth_error_None in Hval_i.
            apply runtime_lookup_list_preserves_length in H6.
            apply static_getType_list_preserves_length in H21.
            apply Forall2_length in H31.
            rewrite H6 in Hval_i.
            rewrite <- H21 in Hval_i.
            rewrite H31 in Hval_i.
            simpl in Hi.
            simpl in Hnth.
            simpl in Hnth.
            lia.
        }
    }
    exact Hwf_method_frame.
    rewrite getmbody.
    exact Htyping_method.
    unfold wf_r_config in H13.
    destruct H13 as [Hwf_classtable _].
    exact Hwf_classtable.
    unfold r_basetype in H1.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
    injection H1 as H0_eq.
    subst cy.
    destruct obj as [rt_obj fields_obj].
    destruct rt_obj as [rq_obj rc_obj].
    simpl.
    destruct H13 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    unfold wf_heap in Hheap.
    assert (Hly_dom : ly < dom h) by (apply runtime_getObj_dom in Hobjy; exact Hobjy).
    specialize (Hheap ly Hly_dom).
    unfold wf_obj in Hheap.
    rewrite Hobjy in Hheap.
    destruct Hheap as [Hwf_rtypeuse _].
    unfold wf_rtypeuse in Hwf_rtypeuse.
    simpl in Hwf_rtypeuse.
    destruct (bound CT rc_obj) as [class_def|] eqn:Hbound.
    destruct Hwf_rtypeuse as [Hwf_rtypeuse _].
    exact Hwf_rtypeuse.
    contradiction.
    --
    revert H20.
  subst.
  intro H20.
  intro H13.
  destruct H2 as [mdeflookup getmbody].
  remember (msignature mdef) as msig.
  have mdeflookupcopy := mdeflookup.
  apply method_body_well_typed_by_find in mdeflookup; auto.
  destruct mdeflookup as [sΓmethodend Htyping_method].
  remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit.
  apply IHeval_stmt with (mt:=(mtype (msignature mdef)))(sΓ' := sΓmethodend)(sΓ := sΓmethodinit). 1-9: auto.
  remember {| vars := Iot ly :: vals |} as rΓmethodinit.
  destruct (r_muttype h ly) eqn: Hinnerthis.
  2:{
    unfold r_muttype in Hinnerthis.
    unfold r_basetype in H1.
    destruct (runtime_getObj h ly).
    discriminate Hinnerthis.
    discriminate H1.
  }
  assert (Hwf_method_frame : wf_r_config CT sΓmethodinit 
                                    rΓmethodinit h ).
  {
    have Hwf_copy := H13.
    unfold wf_r_config in H13.
    destruct H13 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    have Hclasstable := Hclass.
    destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
    repeat split.
    exact Hclass.
    exact Hobj.
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
    unfold runtime_getVal in H0.
    destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
    injection H0 as H_eq.
    subst v.
    eapply Forall_nth_error in Hallvals; eauto.
    simpl in Hallvals.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjly; [|contradiction].
    apply runtime_getObj_dom in Hobjly.

    exact Hobjly.
    rewrite HeqrΓmethodinit.
    simpl.
    constructor.
    simpl.
    unfold runtime_getVal in H0.
    destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
    injection H0 as H_eq.
    subst v.
    unfold runtime_getVal in Hnth_y.
    unfold wf_renv in Hrenv.
    destruct Hrenv as [_ [_ Hallvals]].
    eapply Forall_nth_error in Hallvals; eauto.
    simpl in Hallvals.
    exact Hallvals.
    eapply runtime_lookup_list_preserves_wf_values; eauto.

    rewrite HeqsΓmethodinit.
    simpl.
    lia.

    (* Inner static env's elements are wellformed typeuse *)
    rewrite HeqsΓmethodinit.
    constructor.
    (* Receiver type is well-formed *)
    eapply method_sig_wf_receiver_by_find; eauto.
    unfold r_basetype in H1.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
    injection H1 as H0_eq.
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
    destruct Hwf_rtypeuse as [Hwf_rtypeuse _].
    exact Hwf_rtypeuse.
    contradiction.

    eapply method_sig_wf_parameters_by_find; eauto.
    unfold r_basetype in H1.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
    injection H1 as H0_eq.
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
    destruct Hwf_rtypeuse as [Hwf_rtypeuse _].
    exact Hwf_rtypeuse.
    contradiction.

    apply static_getType_list_preserves_length in H21.
    apply runtime_lookup_list_preserves_length in H6.
    rewrite HeqsΓmethodinit.
    simpl.
    f_equal.
    apply Forall2_length in H32.
    rewrite <- Heqmsig.
    assert (Hy_dom : y < dom sΓ').
    {
      apply static_getType_dom in H20.
      exact H20.
    }

    unfold wf_renv in Hrenv.
    destruct Hrenv as [_ [Hreceiver _]].
    destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
    assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
    {
      eapply receiver_mutability_exists_from_bound; eauto.
    }
    destruct HOutterReceiverMutability as [qcontext Hqcontext].
    (* Apply correspondence to get wf_r_typable *)
    specialize (Hcorr iot qcontext Hget_iot Hqcontext y Hy_dom Ty H20).
    rewrite H0 in Hcorr.

    (* Extract subtyping from wf_r_typable *)
    unfold wf_r_typable in Hcorr.
    unfold r_basetype in H1.
    unfold r_type.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
    injection H1 as Hcy_eq.
    subst cy.
    destruct obj as [rt_obj fields_obj].
    destruct rt_obj as [rq_obj rc_obj].

    unfold r_type in Hcorr.
    rewrite Hobjy in Hcorr.
    simpl in Hcorr.
    destruct Hcorr as [Hsubtype _].
    rewrite <- H6 in H21.
    rewrite HeqrΓmethodinit.
    simpl.
    f_equal.
    rewrite <- H21.
    rewrite Heqmsig.
    rewrite H32.
    simpl in mdeflookupcopy.
    assert (msignature mdef = msignature mdef0).
    {
      eapply method_signature_consistent_subtype; eauto.
    }
    rewrite <- H1 in H26.
    rewrite <- H1 in H30.
    rewrite <- H1 in H32.
    rewrite H1.
    reflexivity.

    (* Typable! *)
    intros lInnerRecevier qinner HgetInnerReceiverAddr HgetInnerReceiverMutability i Hi sqt Hnth. 
      rewrite HeqsΓmethodinit in Hnth, Hi.
      rewrite HeqrΓmethodinit.
      simpl in *.
      destruct i as [|i'].
      (* Reciever *)
      simpl in Hnth.
      injection Hnth as Hsqt_eq.
      subst sqt.
      simpl.
      unfold wf_r_typable.
      unfold r_type.
      destruct (runtime_getObj h ly) as [objy|] eqn:Hobj_ly.
      2:{
        unfold r_basetype in H1.
        rewrite Hobj_ly in H1.
        discriminate.
      }

      assert (Hy_dom : y < dom sΓ').
      {
        apply static_getType_dom in H20.
        exact H20.
      }

      unfold wf_renv in Hrenv.
      destruct Hrenv as [_ [Hreceiver _]].
      destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
      assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
      {
        eapply receiver_mutability_exists_from_bound; eauto.
      }
      destruct HOutterReceiverMutability as [qoutter Hqoutter].
      (* Apply correspondence to get wf_r_typable *)
      specialize (Hcorr iot qoutter Hget_iot Hqoutter y Hy_dom Ty H20).
      unfold wf_r_typable in Hcorr.
      unfold r_basetype in H1.
      unfold r_type.
      destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
      destruct obj as [rt_obj fields_obj].
      destruct rt_obj as [rq_obj rc_obj].

      unfold r_type in Hcorr.
      rewrite H0 in Hcorr.
      rewrite Hobjy in Hcorr.
      simpl in Hcorr.
      destruct Hcorr as [Hsubtype Hqualifier].
      simpl in Hobj_ly.
      injection Hobj_ly as Hobjy_eq.

      simpl in H1.
      inversion H1.
      rewrite <- H3 in mdeflookupcopy.
      assert (Hsigeq: msignature mdef = msignature mdef0).
      {
        eapply method_signature_consistent_subtype; eauto.
      }

      split.
      - 
      destruct H30 as [H30 | H30].
        +
          apply qualified_type_subtype_base_subtype in H30.
          rewrite (vpa_mutabilty_tt_sctype_safe_ro Ty (mreceiver (msignature mdef0))) in H30.
          rewrite <- Hsigeq in H26.
          rewrite <- Hsigeq in H30.
          rewrite <- Hsigeq in H32.
          subst objy.
          simpl.
          eapply base_trans; eauto.
        +
          destruct H30 as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
          rewrite <- Hsigeq in H26.
          rewrite <- Hsigeq in HBaseSubtype.
          rewrite <- Hsigeq in H32.
          subst objy.
          simpl.
          eapply base_trans; eauto. 
      -
      destruct H30 as [H30 | H30].
      +
        apply qualified_type_subtype_q_subtype in H30.
        rewrite sq_vpa_tt_eq_qq_safe_ro in H30.
        rewrite <- Hsigeq in H26.
        rewrite <- Hsigeq in H30.
        rewrite <- Hsigeq in H32.
        rewrite <- Hobjy_eq.
        simpl.
        assert (Hrq_eq : rq_obj = q).
        {
          unfold r_muttype in Hinnerthis.
          rewrite Hobjy in Hinnerthis.
          simpl in Hinnerthis.
          inversion Hinnerthis; reflexivity.
        }
        subst q.
        assert (rq_obj = qinner).
        {
          rewrite HeqrΓmethodinit in HgetInnerReceiverAddr.
          simpl in HgetInnerReceiverAddr.
          inversion HgetInnerReceiverAddr; subst lInnerRecevier.
          clear HgetInnerReceiverAddr.

          (* Now both inner-this facts are about loc = ly *)
          rewrite Hinnerthis in HgetInnerReceiverMutability.
          inversion HgetInnerReceiverMutability; subst qinner.
          clear HgetInnerReceiverMutability.

          (* From Hobjy_eq we know objy has rqtype = rq_obj *)
          subst objy.
          simpl in *.
          reflexivity.
        }
        subst rq_obj.
        clear - H30 Hqualifier.
        destruct qinner eqn:Hqinner;
        destruct ((sqtype (mreceiver (msignature mdef)))) eqn:HMethodReceiverDeclaredType;
        try solve_qualifier_typable_correct_concrete.

        all:
        destruct (sqtype Ty) eqn:HTyStaticMutability;
        simpl in H30;
        try solve_q_subtype_wrong.

        all:
        destruct qoutter eqn:Hqoutter;
        try solve_qualifier_typable_wrong_concrete.
      +
        destruct H30 as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
        rewrite <- Hsigeq in H26.
        rewrite <- Hsigeq in HReceiverDeclearedQualifier.
        rewrite <- Hsigeq in H32.
        rewrite <- Hobjy_eq.
        simpl.
        assert (Hrq_eq : rq_obj = q).
        {
          unfold r_muttype in Hinnerthis.
          rewrite Hobjy in Hinnerthis.
          simpl in Hinnerthis.
          inversion Hinnerthis; reflexivity.
        }
        subst q.
        assert (rq_obj = qinner).
        {
          rewrite HeqrΓmethodinit in HgetInnerReceiverAddr.
          simpl in HgetInnerReceiverAddr.
          inversion HgetInnerReceiverAddr; subst lInnerRecevier.
          clear HgetInnerReceiverAddr.

          (* Now both inner-this facts are about loc = ly *)
          rewrite Hinnerthis in HgetInnerReceiverMutability.
          inversion HgetInnerReceiverMutability; subst qinner.
          clear HgetInnerReceiverMutability.

          (* From Hobjy_eq we know objy has rqtype = rq_obj *)
          subst objy.
          simpl in *.
          reflexivity.
        }
        subst rq_obj.
        clear -  HTyqualifier HReceiverDeclearedQualifier Hqualifier.
        rewrite HTyqualifier in Hqualifier.
        destruct qinner eqn:Hqinner;
        destruct ((sqtype (mreceiver (msignature mdef)))) eqn:HMethodReceiverDeclaredType;
        try solve_qualifier_typable_correct_concrete.

        all:
        destruct qoutter eqn:Hqoutter;
        try solve_qualifier_typable_wrong_concrete.
        all: try easy.

(* -------------------------------------------------- *)
      -
      destruct H30 as [H30 | H30].
      1:{
        apply qualified_type_subtype_q_subtype in H30.
        assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H20.
          exact H20.
        }
        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
        assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
        {
          eapply receiver_mutability_exists_from_bound; eauto.
        }
        destruct HOutterReceiverMutability as [qoutter Hqoutter].
        (* Apply correspondence to get wf_r_typable *)
        specialize (Hcorr iot qoutter Hget_iot Hqoutter y Hy_dom Ty H20).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H1.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        unfold r_type in Hcorr.
        rewrite H0 in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct Hcorr as [Hsubtype Hqualifier].

        simpl in mdeflookupcopy.
        simpl in H1.
        inversion H1.
        rewrite <- H3 in mdeflookupcopy.
        assert (Hsigeq: msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        rewrite <- Hsigeq in H26.
        rewrite <- Hsigeq in H30.
        rewrite <- Hsigeq in H32.

        simpl.
        unfold runtime_getVal.
        simpl.
        destruct (nth_error vals i') as [v|] eqn:Hval_i.
        + (* Parameter i' exists *)
          destruct v as [|loc]; [trivial|].
          assert (Hi'_bound : i' < List.length argtypes).
          {
            apply Forall2_length in H32.
            simpl in Hi.
            simpl in Hnth.
            lia.
          }
          assert (Harg_type : exists argtype, nth_error argtypes i' = Some argtype).
          {
            apply nth_error_Some_exists.
            exact Hi'_bound.
          }
          destruct Harg_type as [argtype Hargtype].
          eapply runtime_lookup_list_preserves_typing with (CT:= CT) (h:=h)in H6; eauto.
          eapply Forall2_nth_error in H6; eauto.
          eapply Forall2_nth_error in H32; eauto.
          simpl in H6.
          unfold wf_r_typable.
          unfold wf_r_typable in H6.
          destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
          destruct H6 as [Hsubtype_param Htypable_param].
          split.
          *
          apply qualified_type_subtype_base_subtype in H32.
          rewrite (vpa_mutabilty_tt_sctype_safe_ro Ty sqt) in H32.
          eapply base_trans; eauto.
          *
          apply qualified_type_subtype_q_subtype in H32.
          rewrite sq_vpa_tt_eq_qq_safe_ro in H32.
          assert (rq_obj = q).
          {
            unfold r_muttype in Hinnerthis.
            rewrite Hobjy in Hinnerthis.
            simpl in Hinnerthis.
            inversion Hinnerthis; reflexivity.
          }
          subst q.
          assert (rq_obj = qinner).
          {
            rewrite HeqrΓmethodinit in HgetInnerReceiverAddr.
            simpl in HgetInnerReceiverAddr.
            inversion HgetInnerReceiverAddr; subst lInnerRecevier.
            clear HgetInnerReceiverAddr.

            (* Now both inner-this facts are about loc = ly *)
            rewrite Hinnerthis in HgetInnerReceiverMutability.
            inversion HgetInnerReceiverMutability; subst qinner.
            clear HgetInnerReceiverMutability.
            reflexivity.
          }
          subst rq_obj.
          clear - H32 Htypable_param Hqualifier.
          destruct qinner eqn:Hqinner;
          destruct (sqtype sqt) eqn:HTxStaticMutability;
          destruct (rqtype rqt) eqn:Hrqtype;
          try solve_qualifier_typable_correct_concrete.
          all:
          destruct (sqtype Ty) eqn:HTyStaticMutability;
          destruct (sqtype argtype) eqn:Hargtype_static;
          simpl in H32;
          try solve_q_subtype_wrong.
          all:
          destruct qoutter eqn:Hqoutter;
          try solve_qualifier_typable_wrong_concrete.
        + (* Parameter i' doesn't exist - contradiction *)
          exfalso.
          apply nth_error_None in Hval_i.
          apply runtime_lookup_list_preserves_length in H6.
          apply static_getType_list_preserves_length in H21.
          apply Forall2_length in H32.
          rewrite H6 in Hval_i.
          rewrite <- H21 in Hval_i.
          rewrite H32 in Hval_i.
          simpl in Hi.
          simpl in Hnth.
          simpl in Hnth.
          lia.
        }
        1:{
          destruct H30 as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
          assert (Hy_dom : y < dom sΓ').
          {
            apply static_getType_dom in H20.
            exact H20.
          }
          unfold wf_renv in Hrenv.
          destruct Hrenv as [_ [Hreceiver _]].
          destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
          assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
          {
            eapply receiver_mutability_exists_from_bound; eauto.
          }
          destruct HOutterReceiverMutability as [qoutter Hqoutter].
          (* Apply correspondence to get wf_r_typable *)
          specialize (Hcorr iot qoutter Hget_iot Hqoutter y Hy_dom Ty H20).
          unfold wf_r_typable in Hcorr.
          unfold r_basetype in H1.
          unfold r_type.
          destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
          destruct obj as [rt_obj fields_obj].
          destruct rt_obj as [rq_obj rc_obj].

          unfold r_type in Hcorr.
          rewrite H0 in Hcorr.
          rewrite Hobjy in Hcorr.
          simpl in Hcorr.
          destruct Hcorr as [Hsubtype Hqualifier].

          simpl in mdeflookupcopy.
          simpl in H1.
          inversion H1.
          rewrite <- H3 in mdeflookupcopy.
          assert (Hsigeq: msignature mdef = msignature mdef0).
          {
            eapply method_signature_consistent_subtype; eauto.
          }
          rewrite <- Hsigeq in H26.
          rewrite <- Hsigeq in HReceiverDeclearedQualifier.
          rewrite <- Hsigeq in H32.

          simpl.
          unfold runtime_getVal.
          simpl.
          destruct (nth_error vals i') as [v|] eqn:Hval_i.
          + (* Parameter i' exists *)
            destruct v as [|loc]; [trivial|].
            assert (Hi'_bound : i' < List.length argtypes).
            {
              apply Forall2_length in H32.
              simpl in Hi.
              simpl in Hnth.
              lia.
            }
            assert (Harg_type : exists argtype, nth_error argtypes i' = Some argtype).
            {
              apply nth_error_Some_exists.
              exact Hi'_bound.
            }
            destruct Harg_type as [argtype Hargtype].
            eapply runtime_lookup_list_preserves_typing with (CT:= CT) (h:=h)in H6; eauto.
            eapply Forall2_nth_error in H6; eauto.
            eapply Forall2_nth_error in H32; eauto.
            simpl in H6.
            unfold wf_r_typable.
            unfold wf_r_typable in H6.
            destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
            destruct H6 as [Hsubtype_param Htypable_param].
            split.
            *
            apply qualified_type_subtype_base_subtype in H32.
            rewrite (vpa_mutabilty_tt_sctype_safe_ro Ty sqt) in H32.
            eapply base_trans; eauto.
            *
            apply qualified_type_subtype_q_subtype in H32.
            rewrite sq_vpa_tt_eq_qq_safe_ro in H32.
            assert (rq_obj = q).
            {
              unfold r_muttype in Hinnerthis.
              rewrite Hobjy in Hinnerthis.
              simpl in Hinnerthis.
              inversion Hinnerthis; reflexivity.
            }
            subst q.
            assert (rq_obj = qinner).
            {
              rewrite HeqrΓmethodinit in HgetInnerReceiverAddr.
              simpl in HgetInnerReceiverAddr.
              inversion HgetInnerReceiverAddr; subst lInnerRecevier.
              clear HgetInnerReceiverAddr.

              (* Now both inner-this facts are about loc = ly *)
              rewrite Hinnerthis in HgetInnerReceiverMutability.
              inversion HgetInnerReceiverMutability; subst qinner.
              clear HgetInnerReceiverMutability.
              reflexivity.
            }
            subst rq_obj.
            clear - H32 Htypable_param Hqualifier.
            destruct qinner eqn:Hqinner;
            destruct (sqtype sqt) eqn:HTxStaticMutability;
            destruct (rqtype rqt) eqn:Hrqtype;
            try solve_qualifier_typable_correct_concrete.
            all:
            destruct (sqtype Ty) eqn:HTyStaticMutability;
            destruct (sqtype argtype) eqn:Hargtype_static;
            simpl in H32;
            try solve_q_subtype_wrong.
            all:
            destruct qoutter eqn:Hqoutter;
            try solve_qualifier_typable_wrong_concrete.
          + (* Parameter i' doesn't exist - contradiction *)
            exfalso.
            apply nth_error_None in Hval_i.
            apply runtime_lookup_list_preserves_length in H6.
            apply static_getType_list_preserves_length in H21.
            apply Forall2_length in H32.
            rewrite H6 in Hval_i.
            rewrite <- H21 in Hval_i.
            rewrite H32 in Hval_i.
            simpl in Hi.
            simpl in Hnth.
            simpl in Hnth.
            lia.
        }
    }
    exact Hwf_method_frame.
    rewrite getmbody.
    exact Htyping_method.
    unfold wf_r_config in H13.
    destruct H13 as [Hwf_classtable _].
    exact Hwf_classtable.
    unfold r_basetype in H1.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
    injection H1 as H0_eq.
    subst cy.
    destruct obj as [rt_obj fields_obj].
    destruct rt_obj as [rq_obj rc_obj].
    simpl.
    destruct H13 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    unfold wf_heap in Hheap.
    assert (Hly_dom : ly < dom h) by (apply runtime_getObj_dom in Hobjy; exact Hobjy).
    specialize (Hheap ly Hly_dom).
    unfold wf_obj in Hheap.
    rewrite Hobjy in Hheap.
    destruct Hheap as [Hwf_rtypeuse _].
    unfold wf_rtypeuse in Hwf_rtypeuse.
    simpl in Hwf_rtypeuse.
    destruct (bound CT rc_obj) as [class_def|] eqn:Hbound.
    destruct Hwf_rtypeuse as [Hwf_rtypeuse _].
    exact Hwf_rtypeuse.
    contradiction.
  -  (* Seq *) (* Apply IH transitively *)
  intros. inversion H2; subst. 
  specialize (eval_stmt_preserves_heap_domain_simple CT rΓ h s1 rΓ' h' H3_) as Hh'.
  assert (l < dom h') by lia. 
  specialize (runtime_getObj_Some h' l H3) as [C' [values' Hh'some]].
  specialize (runtime_preserves_r_type_heap CT rΓ h l ({| rqtype := Imm_r; rctype := C |})
  h' vals s1 rΓ' H0 H3_) as [vals1 Hrtype]. 
  rewrite Hrtype in Hh'some; inversion Hh'some; subst.
  specialize (IHeval_stmt1 H Heqok H5 values' Hrtype vals H0 mt sΓ'0 sΓ H1 H11). 
  specialize (preservation_pico CT sΓ mt rΓ h s1 rΓ' h' sΓ'0 H1 H11 H3_) as Hwf'.
  specialize (IHeval_stmt2 H3 Heqok H5 vals' H4 values' Hrtype mt sΓ' sΓ'0 Hwf' H13). 
  rewrite IHeval_stmt2 in IHeval_stmt1; auto.
Qed.

Lemma imm_step_preserves_imm :
  forall CT sΓ rΓ h l0 C vals l1 k
         (Hwf   : wf_r_config CT sΓ rΓ h)
         (HgetObj  : runtime_getObj h l0 = Some (mkObj (mkruntime_type Imm_r C) vals))
         (Hl1dom  : l1 < dom h)
         (Hnth  : nth_error vals k = Some (Iot l1))
         (HFieldmut  : sf_mutability_rel CT C k RDM_f \/ sf_mutability_rel CT C k Imm_f),
         exists C' vals',
            runtime_getObj h l1 =
              Some (mkObj (mkruntime_type Imm_r C') vals').
Proof.
  intros.
  unfold wf_r_config in Hwf.
  destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen _]]]]].
  unfold wf_heap in Hheap.
  have HgetObjCopy := HgetObj.
  apply runtime_getObj_dom in HgetObjCopy.
  specialize (Hheap l0 HgetObjCopy).
  unfold wf_obj in Hheap.
  rewrite HgetObj in Hheap.
  destruct Hheap as [_ [field_defs [Hfields [Hdom_fields Hforall2]]]].
  assert (Hfield_k : exists fdef : field_def, nth_error field_defs k = Some fdef).
  {
    simpl in Hdom_fields.
    assert (Hk_dom : k < dom vals) by (apply nth_error_Some; rewrite Hnth; discriminate).
    rewrite Hdom_fields in Hk_dom.
    apply nth_error_Some_exists in Hk_dom.
    destruct Hk_dom as [fdef Hfdef].
    exists fdef. exact Hfdef.
  }
  destruct Hfield_k as [fdef Hfdef].
  eapply Forall2_nth_error_prop in Hforall2; eauto.
  simpl in Hforall2.
  destruct (runtime_getObj h l1) eqn:HgetObj_l1; try (exfalso; lia).
  destruct Hforall2 as [rqt [Hrtype [_ Hqual]]].
  destruct HFieldmut as [Hrdm | Himm].
  - (* RDM case *)
    simpl in Hfields.
    unfold sf_mutability_rel in Hrdm.
    destruct Hrdm as [fdef1 [HFieldLookup HFieldMut]].
    assert (fdef1 = fdef).
    {
      clear - HFieldLookup Hfdef Hfields.
      inversion HFieldLookup; subst.
      assert (fields = field_defs) by (eapply collect_fields_deterministic_rel; eauto); subst.
      unfold gget in H0.
      rewrite Hfdef in H0.
      inversion H0; reflexivity.
    }
    subst fdef1.
    rewrite HFieldMut in Hqual.
    unfold qualifier_typable_heap in Hqual.
    destruct (rqtype rqt) eqn:Hrqt; try easy.
    assert (o.(rt_type) = rqt).
    {
      unfold r_type in Hrtype.
      rewrite HgetObj_l1 in Hrtype.
      inversion Hrtype; reflexivity.
    }
    subst rqt.
    destruct o as [rqt vals'].
    exists (rctype rqt), vals'.
    f_equal.
    destruct rqt.
    simpl in Hrqt.
    rewrite Hrqt.
    reflexivity.
  - (* Imm case *)
    simpl in Hfields.
    unfold sf_mutability_rel in Himm.
    destruct Himm as [fdef1 [HFieldLookup HFieldMut]].
    assert (fdef1 = fdef).
    {
      clear - HFieldLookup Hfdef Hfields.
      inversion HFieldLookup; subst.
      assert (fields = field_defs) by (eapply collect_fields_deterministic_rel; eauto); subst.
      unfold gget in H0.
      rewrite Hfdef in H0.
      inversion H0; reflexivity.
    }
    subst fdef1.
    rewrite HFieldMut in Hqual.
    unfold qualifier_typable_heap in Hqual.
    destruct (rqtype rqt) eqn:Hrqt; try easy.
    assert (o.(rt_type) = rqt).
    {
      unfold r_type in Hrtype.
      rewrite HgetObj_l1 in Hrtype.
      inversion Hrtype; reflexivity.
    }
    subst rqt.
    destruct o as [rqt vals'].
    exists (rctype rqt), vals'.
    f_equal.
    destruct rqt.
    simpl in Hrqt.
    rewrite Hrqt.
    reflexivity.
Qed.

Lemma reachable_abs_from_imm_points_to_imm :
  forall CT sΓ rΓ h l0 C0 vals0 l1
         (Hwf   : wf_r_config CT sΓ rΓ h)
         (Himm  : runtime_getObj h l0 = Some (mkObj (mkruntime_type Imm_r C0) vals0))
         (Hrch  : reachable_abs CT h l0 l1),
          exists C' vals',
            runtime_getObj h l1 =
              Some (mkObj (mkruntime_type Imm_r C') vals').
Proof.
  intros.
  remember l0 as l_root eqn:Heq.
  revert l0 C0 vals0 Himm Heq.
  induction Hrch as
    [l Hdom
    |l0 l1 f any C vals k Hdom1 Hget Hf
    |l0 l1 l2 Hr01 IH01 Hr12 IH12
    ]; intros l_root C_root vals_root Himm' Heq'; subst.

  - (* reachable_abs_heap: l1 = l_root *)
    exists C_root, vals_root. assumption.

  - (* reachable_abs_step: l0 -> l1 by RDM/Imm field *)
    (* Key: show l1 is Imm_r using a step lemma *)
    eapply imm_step_preserves_imm; eauto.

  - (* reachable_abs_trans: l0 -> l1 -> l2 *)
    (* First, l1 is Imm_r by IH01 *)
    destruct (IH01 l_root C_root vals_root Himm' eq_refl) as [C1 [vals1 Himm1]].
    (* Now l1 is immutable: runtime_getObj h l1 = Some (mkObj (mkruntime_type Imm_r C1) vals1) *)
    destruct (IH12 l1 C1 vals1 Himm1 eq_refl) as [C2 [vals2 Himm2]].
    (* Now l2 is immutable *)
    exists C2, vals2.
    exact Himm2.
Qed.

(* All reachable objects in the abstract state from immutable root object are immutable *)
Lemma protected_locset_all_imm :
  forall CT sΓ rΓ h root C0 vals0 l
         (Hwf : wf_r_config CT sΓ rΓ h)
         (Himm : runtime_getObj h root = Some (mkObj (mkruntime_type Imm_r C0) vals0))
         (Hin : protected_locset CT h root l),
    exists C' vals',
      runtime_getObj h l = Some (mkObj (mkruntime_type Imm_r C') vals').
Proof.
  intros.
  unfold protected_locset in Hin.
  eapply reachable_abs_from_imm_points_to_imm; eauto.
Qed.

Theorem deep_immutability_pico :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ' root C0 vals0 l C qr vals vals' f
         (Hdom : root < dom h)
         (Himm_root : runtime_getObj h root = Some (mkObj (mkruntime_type Imm_r C0) vals0))
         (Hreach : reachable_abs CT h root l)
         (Hwf : wf_r_config CT sΓ rΓ h)
         (Htyping : stmt_typing CT sΓ mt stmt sΓ')
         (Heval : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h')
         (Hobj : runtime_getObj h l = Some (mkObj (mkruntime_type qr C) vals))
         (Hobj' : runtime_getObj h' l = Some (mkObj (mkruntime_type qr C) vals'))
         (Hprotected : sf_assignability_rel CT C f Final \/ 
                       sf_assignability_rel CT C f RDA),
    nth_error vals f = nth_error vals' f.
Proof.
  intros.
  eapply protected_locset_all_imm in Hreach; eauto.
  destruct Hreach as [C' [vals'' Himm_l]].
  eapply shallow_immutability_pico with (l := l); eauto.
  apply runtime_getObj_dom in Hobj. exact Hobj.
Qed.
