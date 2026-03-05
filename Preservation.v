Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation Properties.

From Stdlib Require Import List.
From Stdlib Require String.
Import ListNotations.
From RecordUpdate Require Import RecordUpdate.

(* ------------------------------------------------------------- *)
(* Soundness properties for PICO *)
Theorem preservation_pico :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ',
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ mt stmt sΓ' -> 
    eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h' -> 
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
      destruct H1 as [mdeflookup getmbody].
      remember (msignature mdef) as msig.
      have mdeflookupcopy := mdeflookup.
      have Hwfcopy := Hwf.
      unfold wf_r_config in Hwf.
      destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
      inversion mdeflookup; revert getmbody; subst; intro getmbody.
      assert (wf_method CT cy mdef).
      {
        eapply method_lookup_wf_class; eauto.
        eapply r_basetype_in_dom; eauto.
        unfold gget_method in H3.
        apply find_some in H3.
        destruct H3.
        exact H2.
      }
      inversion H2; subst.
      destruct H5 as [mrettype Htyping_method].
      destruct Htyping_method as [Htyping_method Hmethodret].
      remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit.
      remember {| vars := Iot ly :: vals |} as rΓmethodinit.
      destruct (r_muttype h ly) eqn: Hinnerthis.
      2:{
        unfold r_muttype in Hinnerthis.
        unfold r_basetype in H0.
        destruct (runtime_getObj h ly).
        discriminate Hinnerthis.
        discriminate H0.
      }
      remember (rΓ <| vars := update x retval (vars rΓ) |>) as rΓ'''.
      
      assert (Hmsigeq: msignature mdef = msignature mdef0).
      {
        assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H14.
          exact H14.
        }
        unfold wf_renv in Hrenv.
        destruct Hrenv as [OutterDom [OutterReceiver OutterCorrespond]].
        destruct OutterReceiver as [OutterReceiverAddr OutterReceiver].
        destruct OutterReceiver as [OutterReceiverGetAddr OutterReceiverAddrBound].
        assert (exists qrout, r_muttype h OutterReceiverAddr = Some qrout).
        {
          eapply receiver_mutability_exists_from_bound.
          exact OutterReceiverAddrBound.
        }
        
        destruct H5 as [qrout H5].
        assert (get_this_var_mapping (vars rΓmethodinit) = Some ly).
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
        unfold r_basetype in H0.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H0 as Hcy_eq.
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
      rewrite <- Hmsigeq in H24.
      rewrite <- Hmsigeq in H23.
      rewrite <- Hmsigeq in H25.
      assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
      { (* Method inner config wellformed.*)
        have Hclasstable := Hclass.
        unfold  wf_class_table in Hclass.
        destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
        repeat split.
        -
          exact Hclass.
        -
          exact Hobj.
        -
          exact Hotherclasses.
        -
          apply Hcname_consistent.
        - 
          apply Hcname_consistent.
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
          unfold runtime_getVal in H.
          destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
          injection H as H1_eq.
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
          unfold runtime_getVal in H.
          destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
          injection H as H1_eq.
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
          unfold r_basetype in H0.
          destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
          injection H0 as H2_eq.
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
            unfold r_basetype in H0.
            destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
            injection H0 as H2_eq.
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
          apply static_getType_list_preserves_length in H15.
          apply runtime_lookup_list_preserves_length in H4.
          rewrite HeqsΓmethodinit.
          rewrite HeqrΓmethodinit.
          simpl.
          f_equal.
          apply Forall2_length in H25.
          
          
          rewrite <- H4 in H15.
          rewrite <- H15.
          rewrite H25.
          rewrite Hmsigeq.
          reflexivity.
        -
        assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H14.
          exact H14.
        }
        unfold wf_renv in Hrenv.
        destruct Hrenv as [OutterDom [OutterReceiver OutterCorrespond]].
        destruct OutterReceiver as [OutterReceiverAddr OutterReceiver].
        destruct OutterReceiver as [OutterReceiverGetAddr OutterReceiverAddrBound].
        assert (exists qrout, r_muttype h OutterReceiverAddr = Some qrout).
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
        assert (get_this_var_mapping (vars rΓmethodinit) = Some ly).
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
            unfold r_basetype in H0.
            rewrite Hobj_ly in H0.
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
            unfold r_basetype in H0.
            unfold r_type.
            rewrite Hobj_ly in H0.
            injection H0 as Hcy_eq.
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
            destruct H24 as [H24 | H24Special].
            ----
              apply qualified_type_subtype_base_subtype in H24.
              rewrite (vpa_mutabilty_tt_sctype_abs_imm Ty (mreceiver (msignature mdef))) in H24.
              eapply base_trans; eauto.
              ----
                destruct H24Special as [HReceiverQualifier HBasetype].
                destruct HBasetype as [HReceiverDeclaredQualifier HBasetype].
                eapply base_trans; eauto.

        ---
        (* receiver qualifier type subtype preserved *)
        destruct H24 as [H24 | H24Special].
        apply qualified_type_subtype_q_subtype in H24.
        ----
          have Hcorrcopy := Hcorr.
          specialize (Hcorr OutterReceiverAddr qrout OutterReceiverGetAddr H5).
          unfold static_getType in H14.
          specialize (Hcorr y Hy_dom Ty H14).
          unfold wf_r_typable in Hcorr.
          rewrite H in Hcorr.
          unfold r_type in Hcorr.
          rewrite Hobj_ly in Hcorr.
          destruct Hcorr as [_ HInnerReceiverQualifier].

          specialize (Hcorrcopy OutterReceiverAddr qrout OutterReceiverGetAddr H5).
          unfold wf_senv in Hsenv.
          destruct Hsenv as [Hsenvdom _].
          apply get_this_qualified_type_nth_error in H16.
          specialize (Hcorrcopy 0 Hsenvdom Tthis H16).
          apply get_this_var_mapping_runtime_getVal in OutterReceiverGetAddr.
          rewrite OutterReceiverGetAddr in Hcorrcopy.
          unfold wf_r_typable in Hcorrcopy.
          unfold r_type in Hcorrcopy.
          unfold r_muttype in H5.
          destruct (runtime_getObj h OutterReceiverAddr) as [outterreceiverobj|] eqn:Houtterobj; [|discriminate].
          inversion H5; subst qrout.
          destruct Hcorrcopy as [_ Houtterqualifier].
          rewrite sq_vpa_tt_eq_qq_abs_imm in H24.
          assert (ly = ι).
          {
            rewrite H7 in getThisAddr.
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
          clear - Houtterqualifier HInnerReceiverQualifier H24.
          destruct (rqtype (rt_type objy)) eqn:Hrqtq;
          destruct (sqtype (mreceiver (msignature mdef))) eqn:Hreceiverq;
          try solve_qualifier_typable_correct_concrete.
          all: destruct (sqtype Ty) eqn:Htyq;
          simpl in H24;
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
          unfold static_getType in H14.
          specialize (Hcorr y Hy_dom Ty H14).
          unfold wf_r_typable in Hcorr.
          rewrite H in Hcorr.
          unfold r_type in Hcorr.
          rewrite Hobj_ly in Hcorr.
          destruct Hcorr as [_ HInnerReceiverQualifier].

          specialize (Hcorrcopy OutterReceiverAddr qrout OutterReceiverGetAddr H5).
          unfold wf_senv in Hsenv.
          destruct Hsenv as [Hsenvdom _].
          apply get_this_qualified_type_nth_error in H16.
          specialize (Hcorrcopy 0 Hsenvdom Tthis H16).
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
            rewrite H7 in getThisAddr.
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
        (* apply qualified_type_subtype_q_subtype in H24. *)
        rewrite H7 in getThisAddr.
        inversion getThisAddr; subst.
        destruct (runtime_getObj h ι) as [objι|] eqn:Hobj_ι.
        2:{
          unfold r_basetype in H0.
          rewrite Hobj_ι in H0.
          discriminate.
        }
        simpl.
        have Hcorrcopy := Hcorr.
        have Hcorrcopy2 := Hcorr.
        specialize (Hcorr OutterReceiverAddr qrout OutterReceiverGetAddr H5).
        unfold static_getType in H14.
        specialize (Hcorr y Hy_dom Ty H14).
        unfold wf_r_typable in Hcorr.
        rewrite H in Hcorr.
        unfold r_type in Hcorr.
        rewrite Hobj_ι in Hcorr.
        destruct Hcorr as [_ HInnerReceiverQualifier].

        specialize (Hcorrcopy OutterReceiverAddr qrout OutterReceiverGetAddr H5).
        unfold wf_senv in Hsenv.
        destruct Hsenv as [Hsenvdom _].
        apply get_this_qualified_type_nth_error in H16.
        specialize (Hcorrcopy 0 Hsenvdom Tthis H16).
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
          (* Use H23 to get the subtyping relationship *)
          assert (Hi'_bound : i' < List.length argtypes).
          {
            apply Forall2_length in H25.
            simpl in Hi.
            simpl in Hnth.
            assert (Hi_mparams : i' < dom (mparams (msignature mdef))).
            { apply nth_error_Some. rewrite Hnth. discriminate. }
            rewrite <- H25 in Hi_mparams.
            exact Hi_mparams.
          }
          assert (Harg_type : exists argtype, nth_error argtypes i' = Some argtype).
          {
            apply nth_error_Some_exists.
            exact Hi'_bound.
          }
          destruct Harg_type as [argtype Hargtype].
          eapply Forall2_nth_error in H25; eauto.
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
            destruct (static_getType_list_nth_zs sΓ' zs argtypes i' argtype H15 Hargtype)
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
            destruct (runtime_lookup_list_nth_zs rΓ zs vals i' (Iot loc) H4 Hval_i)
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
          apply qualified_type_subtype_base_subtype in H25.
          rewrite (vpa_mutabilty_tt_sctype_abs_imm Ty) in H25.
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
          apply qualified_type_subtype_q_subtype in H25.
          destruct H24 as [H24 | H24Special].
          ----
            apply qualified_type_subtype_q_subtype in H24.
            clear - Harg_qual_subtype Houtterqualifier HInnerReceiverQualifier H25.
            rewrite sq_vpa_tt_eq_qq_abs_imm in H25.
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
            simpl in H25;
            try solve_qualifier_typable_wrong_concrete;
            try solve_q_subtype_wrong.
          ----
            destruct H24Special as [HReceiverQualifier HBasetype].
            destruct HBasetype as [HReceiverDeclaredQualifier HBasetype].
            clear - Harg_qual_subtype Houtterqualifier HInnerReceiverQualifier H25.
            rewrite sq_vpa_tt_eq_qq_abs_imm in H25.
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
            simpl in H25;
            try solve_qualifier_typable_wrong_concrete;
            try solve_q_subtype_wrong.
          
        --- (* Parameter i' doesn't exist - contradiction *)
          exfalso.
          apply nth_error_None in Hval_i.
          apply runtime_lookup_list_preserves_length in H4.
          apply static_getType_list_preserves_length in H15.
          apply Forall2_length in H25.
          rewrite H4 in Hval_i.
          rewrite <- H15 in Hval_i.
          rewrite H25 in Hval_i.
          simpl in Hi.
          simpl in Hnth.
          lia.
      }
      rename x0 into sΓmethodend.
      assert (wf_r_config CT sΓmethodend rΓ'' h'). 
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
        destruct Hclass as [Hclass_ [Hobj_ [Hcname_consistent_ Hfind_consistent_]]].
        repeat split.
        exact Hclass_.
        exact Hobj_.
        apply Hcname_consistent_.
        apply Hfind_consistent_.
        apply Hfind_consistent_.
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
        have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓmethodinit h (mbody_stmt (mbody mdef)) rΓ'' h' Heval.
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
        have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓmethodinit h (mbody_stmt (mbody mdef)) rΓ'' h' Heval.
        assert (Hloc_dom : loc < dom h) by (apply runtime_getObj_dom in Hobjloc; exact Hobjloc).
        assert (Hloc_dom' : loc < dom h') by lia.
        destruct (runtime_getObj h' loc) as [obj'|] eqn:Hobj'.
        trivial.
        exfalso. apply runtime_getObj_not_dom in Hobj'. lia.
        unfold runtime_getVal in H6.
        destruct retval as [|loc]; [trivial|].
        unfold wf_renv in Hrenvinit.
        destruct Hrenvinit as [_ [_ Hrenv_wf]].
        eapply Forall_nth_error in Hrenv_wf; eauto.
        simpl in Hrenv_wf.
        destruct (runtime_getObj h' loc) as [obj|] eqn:Hobjloc; [trivial|].
        contradiction.
        apply static_getType_dom in H13.
        rewrite Hlen in H13.
        exact H13.

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
          + apply static_getType_dom in H13.
            rewrite Hlen in H13.
            exact H13.
          + (* Show wf_r_typable for retval *)
            assert (Hnth_x : nth_error sΓ' x = Some Tx).
            {
              unfold static_getType in H13.
              exact H13.
            }
            rewrite Hnth_x in Hnth.
            injection Hnth as Hsqt_eq.
            subst sqt.
            (* Use the fact that retval is well-typed from method return *)
            unfold runtime_getVal in H6.
            destruct retval as [|loc]; [trivial|].
            assert (Hret_dom : mreturn (mbody mdef) < dom (vars rΓ'')).
            {
              apply nth_error_Some.
              rewrite H6.
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
            specialize (Hcorrinit ly q HreceiverAddrInit HInnerReceiverEndFrame (mreturn (mbody mdef)) Hret_dom mrettype Hnth_mbodyret).
            destruct (runtime_getVal rΓ'' (mreturn (mbody mdef))) eqn: Hmet_val; [|easy].
            destruct v.
            2:{
              assert (Hy_dom : y < dom sΓ').
              {
                apply static_getType_dom in H14.
                exact H14.
              }
              assert (exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
              {
                eapply get_this_exists_from_wf_r_config; eauto.
              }
              destruct H7 as [lOutterReceiver HOutterReceiverAddr].
              assert (exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
              {
                eapply receiver_mutability_exists_wf_renv with (CT:=CT); eauto.
              }
              destruct H7 as [OutterReceiverMutability HOutterReceiverMutabilityType].

              have Hcorrcopy := Hcorr.
              specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H14).
              unfold wf_r_typable in Hcorr.
              unfold r_basetype in H0.
              unfold r_type.
              destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
              injection H0 as Hcy_eq.
              subst cy.
              destruct obj as [rt_obj fields_obj].
              destruct rt_obj as [rq_obj rc_obj].

              unfold r_type in Hcorr.
              rewrite H in Hcorr.
              rewrite Hobjy in Hcorr.
              simpl in Hcorr.
              destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
              unfold runtime_getVal in Hmet_val.
              rewrite Hmet_val in H6.
              inversion H6.
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
              apply qualified_type_subtype_base_subtype in H23.
              (* rewrite (vpa_mutabilty_tt_sctype Tthis Tx) in H22. *)
              (* rewrite (vpa_mutabilty_tt Ty (mret (msignature mdef0))) in H22. *)
              rewrite (vpa_mutabilty_tt_sctype_abs_imm Ty (mret (msignature mdef))) in H23.
              (* rewrite (vpa_mutabilty_tt_sctype (mreceiver (msignature mdef)) mrettype) in Hsubtype_ret.
              rewrite (vpa_mutabilty_tt_sctype (mreceiver (msignature mdef)) (mret (msignature mdef))) in Hsubtype_ret. *)
              (* rewrite <- Hmsigeq in H25. *)
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
              apply get_this_qualified_type_nth_error in H16.
              unfold wf_senv in Hsenv.
              destruct Hsenv as [Hsenvdom _].
              specialize (Hcorrcopy 0 Hsenvdom Tthis H16).
              apply get_this_var_mapping_runtime_getVal in HOutterReceiverAddrInit.
              rewrite HOutterReceiverAddrInit in Hcorrcopy.
              unfold wf_r_typable in Hcorrcopy.
              unfold r_type in Hcorrcopy.
              unfold r_muttype in HOutterReceiverMutabilityType.
              destruct (runtime_getObj h lOutterReceiver) as [outterreceiverobj|] eqn:Houtterobj; [|discriminate].
              destruct Hcorrcopy as [_ HOutterReceiverQualifierTypablility].

              assert (Hx_dom : x < dom sΓ').
              {
                apply static_getType_dom in H13.
                exact H13.
              }

              destruct Hsubtype_ret as [Hsubtype_ret _].
              apply qualified_type_subtype_q_subtype in Hsubtype_ret.
              move Hsubtype_ret at bottom.
              apply qualified_type_subtype_q_subtype in H23.
              move H23 at bottom.
              destruct H24 as [H24 | H24Special].
              1:{
                apply qualified_type_subtype_q_subtype in H24.
                move H24 at bottom.
                rewrite Hmsigeq in Hsubtype_ret.
                move HyQualifierTypablility at bottom.

                clear IHHeval.
                inversion HOutterReceiverMutabilityType; subst OutterReceiverMutability.
                subst.
                rewrite sq_vpa_tt_eq_qq_abs_imm in H24.
                rewrite sq_vpa_tt_eq_qq_abs_imm in H23.
                rewrite <- Hmsigeq in Hsubtype_ret.
                clear - Hsubtype_ret H23 H24 HyQualifierTypablility HOutterReceiverQualifierTypablility Hrorettypequalifier.
                destruct (rqtype (rt_type o)) eqn:HretObjectMutability; move HretObjectMutability at bottom;
                destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverRuntimeMutability; move HOutterReceiverRuntimeMutability at bottom;
                destruct (sqtype Tx) eqn:HTxStaticMutability; move HTxStaticMutability at bottom;
                try solve_qualifier_typable_correct_concrete.
                all:
                destruct (sqtype Ty) eqn:HTyStaticMutability; move HTyStaticMutability at bottom;
                destruct (sqtype (mreceiver (msignature mdef))) eqn: HMethodReceiverDeclaredType;
                simpl in H24;
                try solve_q_subtype_wrong.
                all:
                destruct (sqtype (mret (msignature mdef))) eqn:HMethodDeclaredReturnType;
                simpl in H23;
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
                rewrite sq_vpa_tt_eq_qq_abs_imm in H23.
                rewrite <- Hmsigeq in Hsubtype_ret.

                clear - Hsubtype_ret H23 HReceiverQualifier HReceiverDeclaredQualifier HyQualifierTypablility HOutterReceiverQualifierTypablility Hrorettypequalifier.
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
                simpl in H23;
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
            rewrite H6 in Hmet_val.
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
      assert (exists D ddef, base_subtype CT cy D /\ find_class CT D = Some ddef /\ In mdef (methods (body ddef)) /\ wf_method CT D mdef).
      {
        eapply method_lookup_in_wellformed_inherited; eauto.
        eapply r_basetype_in_dom; eauto.
      }
      destruct H2 as [D H2].
      destruct H2 as [ddef H2].
      destruct H2 as [Hbasecyd [HfindD [HmdefinD H2]]].

      inversion H2; subst.
      destruct H8 as [mrettype Htyping_method].
      destruct Htyping_method as [Htyping_method Hmethodret].
      remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit.
      remember {| vars := Iot ly :: vals |} as rΓmethodinit.
      remember (rΓ <| vars := update x retval (vars rΓ) |>) as rΓ'''.
      assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
      { 
        (* Method inner config wellformed.*)
        have Hclasstable := Hclass.
        unfold  wf_class_table in Hclass.
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
        unfold runtime_getVal in H.
        destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
        injection H as H1_eq.
        subst v.
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
        unfold runtime_getVal in H.
        destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
        injection H as H1_eq.
        subst v.
        unfold runtime_getVal in Hnth_y.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [_ Hallvals]].
        eapply Forall_nth_error in Hallvals; eauto.
        simpl in Hallvals.
        exact Hallvals.
        eapply runtime_lookup_list_preserves_wf_values; eauto.

        (* Inner Static Environment's length is more than 0 *)
        rewrite HeqsΓmethodinit.
        simpl.
        lia.

        (* Inner static env's elements are wellformed typeuse *)
        rewrite HeqsΓmethodinit.
        constructor.
        subst.
        assert (parent < dom CT). {
          assert (cy < dom CT). {
            eapply find_class_dom; eauto.
          }
          assert (parent < cy). {
            eapply parent_implies_strict_ordering with (C:= cy) (D:=parent); eauto.
          }
          lia.
        }

        (* Receiver type is well-formed *)
        eapply method_sig_wf_receiver_by_find; eauto.
        assert (parent < dom CT). {
          assert (cy < dom CT). {
            eapply find_class_dom; eauto.
          }
          assert (parent < cy). {
            eapply parent_implies_strict_ordering with (C:= cy) (D:=parent); eauto.
          }
          lia.
        }
        eapply method_sig_wf_parameters_by_find; eauto.

        apply static_getType_list_preserves_length in H15.
        apply runtime_lookup_list_preserves_length in H4.
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        simpl.
        f_equal.
        apply Forall2_length in H25.
        assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H14.
          exact H14.
        }
        assert (exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
        {
          eapply get_this_exists_from_wf_r_config; eauto.
        }
        destruct H8 as [lOutterReceiver HOutterReceiverAddr].
        assert (exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
        {
          eapply receiver_mutability_exists_wf_renv; eauto.
        }
        destruct H8 as [OutterReceiverMutability HOutterReceiverMutabilityType].

        have Hcorrcopy := Hcorr.
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H14).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H0.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H0 as Hcy_eq.
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
        rewrite H in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
        assert (msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        rewrite H0.
        rewrite H4.
        rewrite <- H25.
        exact H15.

        (* Correspondence holds for inner environment *)
        intros ι qinner HreceiverAddr Hqcontext i Hi sqt Hnth.
        rewrite HeqsΓmethodinit in Hnth, Hi.
        rewrite HeqrΓmethodinit.
        simpl in *.
        assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H14.
          exact H14.
        }
        assert (exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
        {
          eapply get_this_exists_from_wf_r_config; eauto.
        }
        destruct H8 as [lOutterReceiver HOutterReceiverAddr].
        assert (exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
        {
          eapply receiver_mutability_exists_wf_renv; eauto.
        }
        destruct H8 as [OutterReceiverMutability HOutterReceiverMutabilityType].

        have Hcorrcopy := Hcorr.
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H14).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H0.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H0 as Hcy_eq.
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
        rewrite H in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
        
        assert (Hmsigeq: msignature mdef = msignature mdef0).
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
        destruct H24 as [H24 | H24Special].
        1:
        {
          apply qualified_type_subtype_base_subtype in H24.
          rewrite (vpa_mutabilty_tt_sctype_abs_imm Ty (mreceiver (msignature mdef0))) in H24.
          eapply base_trans; eauto.
        }
        1:{
          destruct H24Special as [HReceiverQualifier HBasetype].
          destruct HBasetype as [HReceiverDeclaredQualifier HBasetype].
          eapply base_trans; eauto.
        }

        (* Qualifier typbility *)
        1: 
        {
          destruct H24 as [H24 | H24Special].
          1:{
            apply qualified_type_subtype_q_subtype in H24.
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            apply get_this_qualified_type_nth_error in H16.
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            specialize (Hcorrcopy 0 Hsenvdom Tthis H16).
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

            assert (r_muttype h ly = Some rq_obj).
            {
              unfold r_muttype.
              rewrite Hobjy.
              simpl.
              reflexivity.
            }

            assert (rq_obj = qinner).
            {
              rewrite H0 in Hqcontext.
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
            unfold vpa_mutabilty_tt_abs_imm in H24.
            rewrite <- Hmsigeq in H24.

            destruct qinner eqn:HInnerReceiverMutability;
            destruct (sqtype (mreceiver (msignature mdef))) eqn:HMethodReceiverDeclaredType;
            try trivial.
            all: destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            destruct (sqtype Ty) eqn:HTyStaticMutability;
            try trivial.
            all: destruct (sqtype Tthis) eqn:HTthisStaticMutability;
            try rewrite HTyStaticMutability in H24;
            simpl in H24;
            try rewrite HMethodReceiverDeclaredType in H24;
            try inversion H24; try trivial.
            all: try inversion H24; try easy.
          }
          1:{
            destruct H24Special as [HReceiverQualifier HBasetype].
            destruct HBasetype as [HReceiverDeclaredQualifier HBasetype].
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            apply get_this_qualified_type_nth_error in H16.
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            specialize (Hcorrcopy 0 Hsenvdom Tthis H16).
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

            assert (r_muttype h ly = Some rq_obj).
            {
              unfold r_muttype.
              rewrite Hobjy.
              simpl.
              reflexivity.
            }

            assert (rq_obj = qinner).
            {
              rewrite H0 in Hqcontext.
              inversion Hqcontext; subst qinner.
              reflexivity.
            }
            subst rq_obj.
            rewrite Hmsigeq.

            unfold qualifier_typable_context.
            unfold qualifier_typable_context in HyQualifierTypablility.
            unfold qualifier_typable_context in Houtter_qualifier_typable.
            unfold vpa_mutabilty_rs.
            unfold vpa_mutabilty_rs in HyQualifierTypablility.
            unfold vpa_mutabilty_rs in Houtter_qualifier_typable.

            destruct qinner eqn:HInnerReceiverMutability;
            destruct (sqtype (mreceiver (msignature mdef0))) eqn:HMethodReceiverDeclaredType;
            try trivial.
            all: destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            destruct (sqtype Ty) eqn:HTyStaticMutability;
            try trivial.
            all: destruct (sqtype Tthis) eqn:HTthisStaticMutability; try trivial.
            all: try easy.
          }
        }

        (* -------------------------------------------------- *)
        (* Other index - > 1 *)
        apply qualified_type_subtype_q_subtype in H23.
        unfold runtime_getVal.
        simpl.
        destruct (nth_error vals i') as [v|] eqn:Hval_i.
          - (* Parameter i' exists *)
            destruct v as [|loc]; [trivial|].
            (* Use H23 to get the subtyping relationship *)
            assert (Hi'_bound : i' < List.length argtypes).
            {
              apply Forall2_length in H25.
              simpl in Hi.
              simpl in Hnth.
              rewrite Hmsigeq in Hnth.
              rewrite H25.
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
                nth_error sΓ' iArgInSenv = Some argtype
            /\ nth_error zs i' = Some iArgInSenv).
            {
              destruct (static_getType_list_nth_zs sΓ' zs argtypes i' argtype H15 Hargtype)
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
              destruct (runtime_lookup_list_nth_zs rΓ zs vals i' (Iot loc) H4 Hval_i)
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
            eapply Forall2_nth_error in H25; eauto.
            apply qualified_type_subtype_base_subtype in H25.
            rewrite (vpa_mutabilty_tt_sctype_abs_imm Ty sqt) in H25.
            eapply base_trans; eauto.

            (* Qualifier Typability *)
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in H25; eauto.
            apply qualified_type_subtype_q_subtype in H25.
            rewrite sq_vpa_tt_eq_qq_abs_imm in H25.
            specialize (Hcorrcopy_2 lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            apply get_this_qualified_type_nth_error in H16.
            specialize (Hcorrcopy_2 0 Hsenvdom Tthis H16).
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
            clear - H25 Harg_qualifiertypability HyQualifierTypablility HOutterReceiverQualifierTypablility.

            destruct (rqtype (rt_type argobj)) eqn:Hargobjmutability; move Hargobjmutability at bottom;
            destruct (sqtype sqt) eqn:HParameterStaticDeclearedMutability; move HParameterStaticDeclearedMutability at bottom;
            destruct qinner eqn:HInnerReceiverMutability; move HInnerReceiverMutability at bottom;
            try solve_qualifier_typable_correct_concrete.

            all: destruct (sqtype Ty) eqn:HTyStaticMutability;
            destruct (sqtype argtype) eqn:HArgTypeStaticMutability;
            simpl in H25;
            try solve_q_subtype_wrong.

            all: 
            destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            try solve_qualifier_typable_wrong_concrete.

          - (* Parameter i' doesn't exist - contradiction *)
            exfalso.
            apply nth_error_None in Hval_i.
            apply runtime_lookup_list_preserves_length in H4.
            apply static_getType_list_preserves_length in H15.
            apply Forall2_length in H25.
            rewrite H4 in Hval_i.
            rewrite <- H15 in Hval_i.
            rewrite H25 in Hval_i.
            simpl in Hi.
            simpl in Hnth.
            rewrite <- Hmsigeq in Hval_i.
            lia.
      }
      rename x0 into sΓmethodend.
      assert (wf_r_config CT sΓmethodend rΓ'' h'). 
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
        destruct Hclass as [Hclass_ [Hobj_ [Hcname_consistent_ Hfind_consistent_]]].
        repeat split.
        exact Hclass_.
        exact Hobj_.
        apply Hcname_consistent_.
        apply Hfind_consistent_.
        apply Hfind_consistent_.
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
        have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓmethodinit h (mbody_stmt (mbody mdef)) rΓ'' h' Heval.
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
        have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓmethodinit h (mbody_stmt (mbody mdef)) rΓ'' h' Heval.
        assert (Hloc_dom : loc < dom h) by (apply runtime_getObj_dom in Hobjloc; exact Hobjloc).
        assert (Hloc_dom' : loc < dom h') by lia.
        destruct (runtime_getObj h' loc) as [obj'|] eqn:Hobj'.
        trivial.
        exfalso. apply runtime_getObj_not_dom in Hobj'. lia.
        unfold runtime_getVal in H6.
        destruct retval as [|loc]; [trivial|].
        unfold wf_renv in Hrenvinit.
        destruct Hrenvinit as [_ [_ Hrenv_wf]].
        eapply Forall_nth_error in Hrenv_wf; eauto.
        simpl in Hrenv_wf.
        destruct (runtime_getObj h' loc) as [obj|] eqn:Hobjloc; [trivial|].
        contradiction.
        apply static_getType_dom in H13.
        rewrite Hlen in H13.
        exact H13.

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
          + apply static_getType_dom in H13.
            rewrite Hlen in H13.
            exact H13.
          + (* Show wf_r_typable for retval *)
            assert (Hnth_x : nth_error sΓ' x = Some Tx).
            {
              unfold static_getType in H13.
              exact H13.
            }
            rewrite Hnth_x in Hnth.
            injection Hnth as Hsqt_eq.
            subst sqt.
            (* Use the fact that retval is well-typed from method return *)
            unfold runtime_getVal in H6.
            destruct retval as [|loc]; [trivial|].
            assert (Hret_dom : mreturn (mbody mdef) < dom (vars rΓ'')).
            {
              apply nth_error_Some.
              rewrite H6.
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
              easy.
            }
            assert (HInnerReceiverMutability: exists InnerReceiverMutability, r_muttype h' ly = Some InnerReceiverMutability).
            {
              eapply receiver_mutability_exists_from_bound; eauto.
              unfold r_basetype in H0.
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
            specialize (Hcorrinit (mreturn (mbody mdef)) Hret_dom mrettype Hnth_mbodyret).
            unfold wf_r_typable.
            unfold r_type.
            destruct (runtime_getObj h' loc) as [retobj|] eqn:HReturnObject.
            2:{
              unfold runtime_getVal in Hcorrinit.
              rewrite H6 in Hcorrinit.
              unfold wf_r_typable in Hcorrinit.
              unfold r_type in Hcorrinit.
              rewrite HReturnObject in Hcorrinit.
              easy.
            }
            specialize (Hcorr outterreceiveinitriot qoutter Hget_outter_iot HOutterReceiverMutabilityInit).
            have H14copy := H14.
            apply static_getType_dom in H14.
            specialize (Hcorr y H14 Ty H14copy).
            rewrite H in Hcorr.
            unfold wf_r_typable in Hcorr; unfold r_type in Hcorr.
            destruct (runtime_getObj h ly) as [objly|] eqn:Hobj; [|contradiction].
            destruct Hcorr as [HyBasetype HyQualifierTypability].
            assert (rctype (rt_type objly) = cy).
            {
              unfold r_basetype in H0.
              rewrite Hobj in H0.
              simpl in H0.
              inversion H0; subst cy.
              reflexivity.
            }
            subst cy.
            assert (Hmsigeq: msignature mdef = msignature mdef0).
            {
              eapply method_signature_consistent_subtype; eauto.
            }
            rewrite Hleninit in Hmbodyretvar_dom.
            destruct (runtime_getVal rΓ'' (mreturn (mbody mdef))) eqn: Hmet_val; [|easy].
            destruct v.
            2:{
              unfold runtime_getVal in Hmet_val.
              rewrite Hmet_val in H6.
              inversion H6.
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
              apply qualified_type_subtype_base_subtype in H23.
              rewrite (vpa_mutabilty_tt_sctype_abs_imm Ty (mret (msignature mdef0))) in H23.
              rewrite Hmsigeq in Hsubtype_ret.
              apply qualified_type_subtype_base_subtype in Hsubtype_ret.
              eapply base_trans; eauto.
              eapply base_trans; eauto.

              (* Qualifier Typability *)
              move Hrorettypequalifier at bottom.
              apply qualified_type_subtype_q_subtype in H23.
              move H23 at bottom.
              move Hcorr_copy at bottom.
              specialize (Hcorr_copy outterreceiveinitriot qoutter Hget_outter_iot HOutterReceiverMutabilityInit).
              unfold wf_senv in Hsenv.
              destruct Hsenv as [Hsenvdom _].
              apply get_this_qualified_type_nth_error in H16.
              specialize (Hcorr_copy 0 Hsenvdom Tthis H16).
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
                assert (r_muttype h ly = Some InnerReceiverMutability).
                {
                  eapply eval_stmt_preserves_r_muttype_backwards; eauto.
                  apply runtime_getObj_dom in Hobj.
                  lia.
                }
                unfold r_muttype in H9.
                rewrite Hobj in H9.
                simpl in H9.
                inversion H9; subst InnerReceiverMutability.
                reflexivity.
              }
              subst InnerReceiverMutability.
              move Hsubtype_ret at bottom.
              move H24 at bottom.
              apply qualified_type_subtype_q_subtype in Hsubtype_ret.
              destruct H24 as [H24 | H24Special].
              1:{
                apply qualified_type_subtype_q_subtype in H24.
                rewrite <- Hmsigeq in H23.
                rewrite <- Hmsigeq in H24.

                clear - Hrorettypequalifier H23 Houtter_qualifier_typable Hsubtype_ret H24 HyQualifierTypability.
                rewrite sq_vpa_tt_eq_qq_abs_imm in H23.
                rewrite sq_vpa_tt_eq_qq_abs_imm in H24.
                destruct (rqtype (rt_type retobj)) eqn:Hrorettypemutability; move Hrorettypequalifier at bottom;
                destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutabilityValue; move HOutterReceiverMutabilityValue at bottom;
                destruct (sqtype Tx) eqn:HTxStaticMutability; move HTxStaticMutability at bottom;
                try solve_qualifier_typable_correct_concrete.

                all:
                destruct ((sqtype (mreceiver (msignature mdef)))) eqn:HMethodReceiverDeclaredType;
                destruct (sqtype Ty) eqn:HTyStaticMutability;
                simpl in H24;
                try solve_q_subtype_wrong.
                
                all:
                destruct (sqtype (mret (msignature mdef))) eqn:HMethodRetDeclaredType;
                simpl in H23;
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
                rewrite <- Hmsigeq in H23.
                rewrite <- Hmsigeq in HReceiverDeclaredQualifier.

                clear - Hrorettypequalifier H23 Houtter_qualifier_typable Hsubtype_ret HReceiverDeclaredQualifier HBasetype HyQualifierTypability.
                rewrite sq_vpa_tt_eq_qq_abs_imm in H23.
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
                simpl in H23;
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
            rewrite H6 in Hmet_val.
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
      destruct H1 as [mdeflookup getmbody].
      remember (msignature mdef) as msig.
      have mdeflookupcopy := mdeflookup.
      have Hwfcopy := Hwf.
      unfold wf_r_config in Hwf.
      destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
      inversion mdeflookup; revert getmbody; subst; intro getmbody.
      assert (wf_method CT cy mdef).
      {
        eapply method_lookup_wf_class; eauto.
        eapply r_basetype_in_dom; eauto.
        unfold gget_method in H3.
        apply find_some in H3.
        destruct H3.
        exact H2.
      }
      inversion H2; subst.
      destruct H5 as [mrettype Htyping_method].
      destruct Htyping_method as [Htyping_method Hmethodret].
      remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit.
      remember {| vars := Iot ly :: vals |} as rΓmethodinit.
      destruct (r_muttype h ly) eqn: Hinnerthis.
      2:{
        unfold r_muttype in Hinnerthis.
        unfold r_basetype in H0.
        destruct (runtime_getObj h ly).
        discriminate Hinnerthis.
        discriminate H0.
      }
      remember (rΓ <| vars := update x retval (vars rΓ) |>) as rΓ'''.
      
      assert (Hmsigeq: msignature mdef = msignature mdef0).
      {
        assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H14.
          exact H14.
        }
        unfold wf_renv in Hrenv.
        destruct Hrenv as [OutterDom [OutterReceiver OutterCorrespond]].
        destruct OutterReceiver as [OutterReceiverAddr OutterReceiver].
        destruct OutterReceiver as [OutterReceiverGetAddr OutterReceiverAddrBound].
        assert (exists qrout, r_muttype h OutterReceiverAddr = Some qrout).
        {
          eapply receiver_mutability_exists_from_bound.
          exact OutterReceiverAddrBound.
        }
        
        destruct H5 as [qrout H5].
        assert (get_this_var_mapping (vars rΓmethodinit) = Some ly).
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
        unfold r_basetype in H0.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H0 as Hcy_eq.
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
      rewrite <- Hmsigeq in H20.
      rewrite <- Hmsigeq in H24.
      rewrite <- Hmsigeq in H26.
      assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
      { (* Method inner config wellformed.*)
        have Hclasstable := Hclass.
        unfold  wf_class_table in Hclass.
        destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
        repeat split.
        -
          exact Hclass.
        -
          exact Hobj.
        -
          exact Hotherclasses.
        -
          apply Hcname_consistent.
        - 
          apply Hcname_consistent.
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
          unfold runtime_getVal in H.
          destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
          injection H as H1_eq.
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
          unfold runtime_getVal in H.
          destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
          injection H as H1_eq.
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
          unfold r_basetype in H0.
          destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
          injection H0 as H2_eq.
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
            unfold r_basetype in H0.
            destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
            injection H0 as H2_eq.
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
          apply static_getType_list_preserves_length in H15.
          apply runtime_lookup_list_preserves_length in H4.
          rewrite HeqsΓmethodinit.
          rewrite HeqrΓmethodinit.
          simpl.
          f_equal.
          apply Forall2_length in H26.
          rewrite <- H4 in H15.
          rewrite <- H15.
          rewrite H26.
          rewrite Hmsigeq.
          reflexivity.
        -
        assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H14.
          exact H14.
        }
        unfold wf_renv in Hrenv.
        destruct Hrenv as [OutterDom [OutterReceiver OutterCorrespond]].
        destruct OutterReceiver as [OutterReceiverAddr OutterReceiver].
        destruct OutterReceiver as [OutterReceiverGetAddr OutterReceiverAddrBound].
        assert (exists qrout, r_muttype h OutterReceiverAddr = Some qrout).
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
        assert (get_this_var_mapping (vars rΓmethodinit) = Some ly).
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
            unfold r_basetype in H0.
            rewrite Hobj_ly in H0.
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
            unfold r_basetype in H0.
            unfold r_type.
            rewrite Hobj_ly in H0.
            injection H0 as Hcy_eq.
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
            destruct H24 as [H24 | H24Special].
            ----
              apply qualified_type_subtype_base_subtype in H24.
              rewrite (vpa_mutabilty_tt_sctype_safe_ro Ty (mreceiver (msignature mdef))) in H24.
              eapply base_trans; eauto.
              ----
                destruct H24Special as [HReceiverQualifier HBasetype].
                destruct HBasetype as [HReceiverDeclaredQualifier HBasetype].
                eapply base_trans; eauto.

        ---
        (* receiver qualifier type subtype preserved *)
        destruct H24 as [H24 | H24Special].
        apply qualified_type_subtype_q_subtype in H24.
        ----
          have Hcorrcopy := Hcorr.
          specialize (Hcorr OutterReceiverAddr qrout OutterReceiverGetAddr H5).
          unfold static_getType in H14.
          specialize (Hcorr y Hy_dom Ty H14).
          unfold wf_r_typable in Hcorr.
          rewrite H in Hcorr.
          unfold r_type in Hcorr.
          rewrite Hobj_ly in Hcorr.
          destruct Hcorr as [_ HInnerReceiverQualifier].

          specialize (Hcorrcopy OutterReceiverAddr qrout OutterReceiverGetAddr H5).
          unfold wf_senv in Hsenv.
          destruct Hsenv as [Hsenvdom _].
          apply get_this_qualified_type_nth_error in H16.
          specialize (Hcorrcopy 0 Hsenvdom Tthis H16).
          apply get_this_var_mapping_runtime_getVal in OutterReceiverGetAddr.
          rewrite OutterReceiverGetAddr in Hcorrcopy.
          unfold wf_r_typable in Hcorrcopy.
          unfold r_type in Hcorrcopy.
          unfold r_muttype in H5.
          destruct (runtime_getObj h OutterReceiverAddr) as [outterreceiverobj|] eqn:Houtterobj; [|discriminate].
          inversion H5; subst qrout.
          destruct Hcorrcopy as [_ Houtterqualifier].
          rewrite sq_vpa_tt_eq_qq_safe_ro in H24.
          assert (ly = ι).
          {
            rewrite H7 in getThisAddr.
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
          clear - Houtterqualifier HInnerReceiverQualifier H24.
          destruct (rqtype (rt_type objy)) eqn:Hrqtq;
          destruct (sqtype (mreceiver (msignature mdef))) eqn:Hreceiverq;
          try solve_qualifier_typable_correct_concrete.
          all: destruct (sqtype Ty) eqn:Htyq;
          simpl in H24;
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
          unfold static_getType in H14.
          specialize (Hcorr y Hy_dom Ty H14).
          unfold wf_r_typable in Hcorr.
          rewrite H in Hcorr.
          unfold r_type in Hcorr.
          rewrite Hobj_ly in Hcorr.
          destruct Hcorr as [_ HInnerReceiverQualifier].

          specialize (Hcorrcopy OutterReceiverAddr qrout OutterReceiverGetAddr H5).
          unfold wf_senv in Hsenv.
          destruct Hsenv as [Hsenvdom _].
          apply get_this_qualified_type_nth_error in H16.
          specialize (Hcorrcopy 0 Hsenvdom Tthis H16).
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
            rewrite H7 in getThisAddr.
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
        (* apply qualified_type_subtype_q_subtype in H24. *)
        rewrite H7 in getThisAddr.
        inversion getThisAddr; subst.
        destruct (runtime_getObj h ι) as [objι|] eqn:Hobj_ι.
        2:{
          unfold r_basetype in H0.
          rewrite Hobj_ι in H0.
          discriminate.
        }
        simpl.
        have Hcorrcopy := Hcorr.
        have Hcorrcopy2 := Hcorr.
        specialize (Hcorr OutterReceiverAddr qrout OutterReceiverGetAddr H5).
        unfold static_getType in H14.
        specialize (Hcorr y Hy_dom Ty H14).
        unfold wf_r_typable in Hcorr.
        rewrite H in Hcorr.
        unfold r_type in Hcorr.
        rewrite Hobj_ι in Hcorr.
        destruct Hcorr as [_ HInnerReceiverQualifier].

        specialize (Hcorrcopy OutterReceiverAddr qrout OutterReceiverGetAddr H5).
        unfold wf_senv in Hsenv.
        destruct Hsenv as [Hsenvdom _].
        apply get_this_qualified_type_nth_error in H16.
        specialize (Hcorrcopy 0 Hsenvdom Tthis H16).
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
          (* Use H23 to get the subtyping relationship *)
          assert (Hi'_bound : i' < List.length argtypes).
          {
            apply Forall2_length in H26.
            simpl in Hi.
            simpl in Hnth.
            assert (Hi_mparams : i' < dom (mparams (msignature mdef))).
            { apply nth_error_Some. rewrite Hnth. discriminate. }
            rewrite <- H26 in Hi_mparams.
            exact Hi_mparams.
          }
          assert (Harg_type : exists argtype, nth_error argtypes i' = Some argtype).
          {
            apply nth_error_Some_exists.
            exact Hi'_bound.
          }
          destruct Harg_type as [argtype Hargtype].
          eapply Forall2_nth_error in H26; eauto.
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
            destruct (static_getType_list_nth_zs sΓ' zs argtypes i' argtype H15 Hargtype)
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
            destruct (runtime_lookup_list_nth_zs rΓ zs vals i' (Iot loc) H4 Hval_i)
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
          apply qualified_type_subtype_base_subtype in H26.
          rewrite (vpa_mutabilty_tt_sctype_safe_ro Ty) in H26.
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
          apply qualified_type_subtype_q_subtype in H26.
          destruct H24 as [H24 | H24Special].
          ----
            apply qualified_type_subtype_q_subtype in H24.
            clear - Harg_qual_subtype Houtterqualifier HInnerReceiverQualifier H26.
            rewrite sq_vpa_tt_eq_qq_safe_ro in H26.
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
            simpl in H26;
            try solve_qualifier_typable_wrong_concrete;
            try solve_q_subtype_wrong.
          ----
            destruct H24Special as [HReceiverQualifier HBasetype].
            destruct HBasetype as [HReceiverDeclaredQualifier HBasetype].
            clear - Harg_qual_subtype Houtterqualifier HInnerReceiverQualifier H26.
            rewrite sq_vpa_tt_eq_qq_safe_ro in H26.
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
            simpl in H26;
            try solve_qualifier_typable_wrong_concrete;
            try solve_q_subtype_wrong.
          
        --- (* Parameter i' doesn't exist - contradiction *)
          exfalso.
          apply nth_error_None in Hval_i.
          apply runtime_lookup_list_preserves_length in H4.
          apply static_getType_list_preserves_length in H15.
          apply Forall2_length in H26.
          rewrite H4 in Hval_i.
          rewrite <- H15 in Hval_i.
          rewrite H26 in Hval_i.
          simpl in Hi.
          simpl in Hnth.
          lia.
      }
      rename x0 into sΓmethodend.
      assert (wf_r_config CT sΓmethodend rΓ'' h'). 
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
        destruct Hclass as [Hclass_ [Hobj_ [Hcname_consistent_ Hfind_consistent_]]].
        repeat split.
        exact Hclass_.
        exact Hobj_.
        apply Hcname_consistent_.
        apply Hfind_consistent_.
        apply Hfind_consistent_.
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
        have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓmethodinit h (mbody_stmt (mbody mdef)) rΓ'' h' Heval.
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
        have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓmethodinit h (mbody_stmt (mbody mdef)) rΓ'' h' Heval.
        assert (Hloc_dom : loc < dom h) by (apply runtime_getObj_dom in Hobjloc; exact Hobjloc).
        assert (Hloc_dom' : loc < dom h') by lia.
        destruct (runtime_getObj h' loc) as [obj'|] eqn:Hobj'.
        trivial.
        exfalso. apply runtime_getObj_not_dom in Hobj'. lia.
        unfold runtime_getVal in H6.
        destruct retval as [|loc]; [trivial|].
        unfold wf_renv in Hrenvinit.
        destruct Hrenvinit as [_ [_ Hrenv_wf]].
        eapply Forall_nth_error in Hrenv_wf; eauto.
        simpl in Hrenv_wf.
        destruct (runtime_getObj h' loc) as [obj|] eqn:Hobjloc; [trivial|].
        contradiction.
        apply static_getType_dom in H13.
        rewrite Hlen in H13.
        exact H13.

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
          + apply static_getType_dom in H13.
            rewrite Hlen in H13.
            exact H13.
          + (* Show wf_r_typable for retval *)
            assert (Hnth_x : nth_error sΓ' x = Some Tx).
            {
              unfold static_getType in H13.
              exact H13.
            }
            rewrite Hnth_x in Hnth.
            injection Hnth as Hsqt_eq.
            subst sqt.
            (* Use the fact that retval is well-typed from method return *)
            unfold runtime_getVal in H6.
            destruct retval as [|loc]; [trivial|].
            assert (Hret_dom : mreturn (mbody mdef) < dom (vars rΓ'')).
            {
              apply nth_error_Some.
              rewrite H6.
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
            specialize (Hcorrinit ly q HreceiverAddrInit HInnerReceiverEndFrame (mreturn (mbody mdef)) Hret_dom mrettype Hnth_mbodyret).
            destruct (runtime_getVal rΓ'' (mreturn (mbody mdef))) eqn: Hmet_val; [|easy].
            destruct v.
            2:{
              assert (Hy_dom : y < dom sΓ').
              {
                apply static_getType_dom in H14.
                exact H14.
              }
              assert (exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
              {
                eapply get_this_exists_from_wf_r_config; eauto.
              }
              destruct H7 as [lOutterReceiver HOutterReceiverAddr].
              assert (exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
              {
                eapply receiver_mutability_exists_wf_renv with (CT:=CT); eauto.
              }
              destruct H7 as [OutterReceiverMutability HOutterReceiverMutabilityType].

              have Hcorrcopy := Hcorr.
              specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H14).
              unfold wf_r_typable in Hcorr.
              unfold r_basetype in H0.
              unfold r_type.
              destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
              injection H0 as Hcy_eq.
              subst cy.
              destruct obj as [rt_obj fields_obj].
              destruct rt_obj as [rq_obj rc_obj].

              unfold r_type in Hcorr.
              rewrite H in Hcorr.
              rewrite Hobjy in Hcorr.
              simpl in Hcorr.
              destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
              unfold runtime_getVal in Hmet_val.
              rewrite Hmet_val in H6.
              inversion H6.
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
              apply qualified_type_subtype_base_subtype in H20.
              (* rewrite (vpa_mutabilty_tt_sctype Tthis Tx) in H22. *)
              (* rewrite (vpa_mutabilty_tt Ty (mret (msignature mdef0))) in H22. *)
              rewrite (vpa_mutabilty_tt_sctype_safe_ro Ty (mret (msignature mdef))) in H20.
              (* rewrite (vpa_mutabilty_tt_sctype (mreceiver (msignature mdef)) mrettype) in Hsubtype_ret.
              rewrite (vpa_mutabilty_tt_sctype (mreceiver (msignature mdef)) (mret (msignature mdef))) in Hsubtype_ret. *)
              (* rewrite <- Hmsigeq in H25. *)
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
              apply get_this_qualified_type_nth_error in H16.
              unfold wf_senv in Hsenv.
              destruct Hsenv as [Hsenvdom _].
              specialize (Hcorrcopy 0 Hsenvdom Tthis H16).
              apply get_this_var_mapping_runtime_getVal in HOutterReceiverAddrInit.
              rewrite HOutterReceiverAddrInit in Hcorrcopy.
              unfold wf_r_typable in Hcorrcopy.
              unfold r_type in Hcorrcopy.
              unfold r_muttype in HOutterReceiverMutabilityType.
              destruct (runtime_getObj h lOutterReceiver) as [outterreceiverobj|] eqn:Houtterobj; [|discriminate].
              destruct Hcorrcopy as [_ HOutterReceiverQualifierTypablility].

              assert (Hx_dom : x < dom sΓ').
              {
                apply static_getType_dom in H13.
                exact H13.
              }

              destruct Hsubtype_ret as [Hsubtype_ret _].
              apply qualified_type_subtype_q_subtype in Hsubtype_ret.
              move Hsubtype_ret at bottom.
              apply qualified_type_subtype_q_subtype in H20.
              move H20 at bottom.
              destruct H24 as [H24 | H24Special].
              1:{
                apply qualified_type_subtype_q_subtype in H24.
                move H24 at bottom.
                rewrite Hmsigeq in Hsubtype_ret.
                move HyQualifierTypablility at bottom.

                clear IHHeval.
                inversion HOutterReceiverMutabilityType; subst OutterReceiverMutability.
                subst.
                rewrite sq_vpa_tt_eq_qq_safe_ro in H24.
                rewrite sq_vpa_tt_eq_qq_safe_ro in H20.
                rewrite <- Hmsigeq in Hsubtype_ret.
                clear - Hsubtype_ret H20 H24 HyQualifierTypablility HOutterReceiverQualifierTypablility Hrorettypequalifier.
                destruct (rqtype (rt_type o)) eqn:HretObjectMutability; move HretObjectMutability at bottom;
                destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverRuntimeMutability; move HOutterReceiverRuntimeMutability at bottom;
                destruct (sqtype Tx) eqn:HTxStaticMutability; move HTxStaticMutability at bottom;
                try solve_qualifier_typable_correct_concrete.
                all:
                destruct (sqtype Ty) eqn:HTyStaticMutability; move HTyStaticMutability at bottom;
                destruct (sqtype (mreceiver (msignature mdef))) eqn: HMethodReceiverDeclaredType;
                simpl in H24;
                try solve_q_subtype_wrong.
                all:
                destruct (sqtype (mret (msignature mdef))) eqn:HMethodDeclaredReturnType;
                simpl in H20;
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
                rewrite sq_vpa_tt_eq_qq_safe_ro in H20.
                rewrite <- Hmsigeq in Hsubtype_ret.

                clear - Hsubtype_ret H20 HReceiverQualifier HReceiverDeclaredQualifier HyQualifierTypablility HOutterReceiverQualifierTypablility Hrorettypequalifier.
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
                simpl in H20;
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
            rewrite H6 in Hmet_val.
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
      assert (exists D ddef, base_subtype CT cy D /\ find_class CT D = Some ddef /\ In mdef (methods (body ddef)) /\ wf_method CT D mdef).
      {
        eapply method_lookup_in_wellformed_inherited; eauto.
        eapply r_basetype_in_dom; eauto.
      }
      destruct H2 as [D H2].
      destruct H2 as [ddef H2].
      destruct H2 as [Hbasecyd [HfindD [HmdefinD H2]]].

      inversion H2; subst.
      destruct H8 as [mrettype Htyping_method].
      destruct Htyping_method as [Htyping_method Hmethodret].
      remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit.
      remember {| vars := Iot ly :: vals |} as rΓmethodinit.
      remember (rΓ <| vars := update x retval (vars rΓ) |>) as rΓ'''.
      assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
      { 
        (* Method inner config wellformed.*)
        have Hclasstable := Hclass.
        unfold  wf_class_table in Hclass. 
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
        unfold runtime_getVal in H.
        destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
        injection H as H1_eq.
        subst v.
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
        unfold runtime_getVal in H.
        destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
        injection H as H1_eq.
        subst v.
        unfold runtime_getVal in Hnth_y.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [_ Hallvals]].
        eapply Forall_nth_error in Hallvals; eauto.
        simpl in Hallvals.
        exact Hallvals.
        eapply runtime_lookup_list_preserves_wf_values; eauto.

        (* Inner Static Environment's length is more than 0 *)
        rewrite HeqsΓmethodinit.
        simpl.
        lia.

        (* Inner static env's elements are wellformed typeuse *)
        rewrite HeqsΓmethodinit.
        constructor.
        subst.
        assert (parent < dom CT). {
          assert (cy < dom CT). {
            eapply find_class_dom; eauto.
          }
          assert (parent < cy). {
            eapply parent_implies_strict_ordering with (C:= cy) (D:=parent); eauto.
          }
          lia.
        }

        (* Receiver type is well-formed *)
        eapply method_sig_wf_receiver_by_find; eauto.
        assert (parent < dom CT). {
          assert (cy < dom CT). {
            eapply find_class_dom; eauto.
          }
          assert (parent < cy). {
            eapply parent_implies_strict_ordering with (C:= cy) (D:=parent); eauto.
          }
          lia.
        }
        eapply method_sig_wf_parameters_by_find; eauto.

        apply static_getType_list_preserves_length in H15.
        apply runtime_lookup_list_preserves_length in H4.
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        simpl.
        f_equal.
        apply Forall2_length in H26.
        assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H14.
          exact H14.
        }
        assert (exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
        {
          eapply get_this_exists_from_wf_r_config; eauto.
        }
        destruct H8 as [lOutterReceiver HOutterReceiverAddr].
        assert (exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
        {
          eapply receiver_mutability_exists_wf_renv; eauto.
        }
        destruct H8 as [OutterReceiverMutability HOutterReceiverMutabilityType].

        have Hcorrcopy := Hcorr.
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H14).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H0.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H0 as Hcy_eq.
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
        rewrite H in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
        assert (msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        rewrite H0.
        rewrite H4.
        rewrite <- H26.
        exact H15.

        (* Correspondence holds for inner environment *)
        intros ι qinner HreceiverAddr Hqcontext i Hi sqt Hnth.
        rewrite HeqsΓmethodinit in Hnth, Hi.
        rewrite HeqrΓmethodinit.
        simpl in *.
        assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H14.
          exact H14.
        }
        assert (exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
        {
          eapply get_this_exists_from_wf_r_config; eauto.
        }
        destruct H8 as [lOutterReceiver HOutterReceiverAddr].
        assert (exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
        {
          eapply receiver_mutability_exists_wf_renv; eauto.
        }
        destruct H8 as [OutterReceiverMutability HOutterReceiverMutabilityType].

        have Hcorrcopy := Hcorr.
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H14).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H0.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H0 as Hcy_eq.
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
        rewrite H in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
        
        assert (Hmsigeq: msignature mdef = msignature mdef0).
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
        destruct H24 as [H24 | H24Special].
        1:
        {
          apply qualified_type_subtype_base_subtype in H24.
          rewrite (vpa_mutabilty_tt_sctype_safe_ro Ty (mreceiver (msignature mdef0))) in H24.
          eapply base_trans; eauto.
        }
        1:{
          destruct H24Special as [HReceiverQualifier HBasetype].
          destruct HBasetype as [HReceiverDeclaredQualifier HBasetype].
          eapply base_trans; eauto.
        }

        (* Qualifier typbility *)
        1: 
        {
          destruct H24 as [H24 | H24Special].
          1:{
            apply qualified_type_subtype_q_subtype in H24.
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            apply get_this_qualified_type_nth_error in H16.
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            specialize (Hcorrcopy 0 Hsenvdom Tthis H16).
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

            assert (r_muttype h ly = Some rq_obj).
            {
              unfold r_muttype.
              rewrite Hobjy.
              simpl.
              reflexivity.
            }

            assert (rq_obj = qinner).
            {
              rewrite H0 in Hqcontext.
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
            unfold vpa_mutabilty_tt_safe_ro in H24.
            rewrite <- Hmsigeq in H24.

            destruct qinner eqn:HInnerReceiverMutability;
            destruct (sqtype (mreceiver (msignature mdef))) eqn:HMethodReceiverDeclaredType;
            try trivial.
            all: destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            destruct (sqtype Ty) eqn:HTyStaticMutability;
            try trivial.
            all: destruct (sqtype Tthis) eqn:HTthisStaticMutability;
            try rewrite HTyStaticMutability in H24;
            simpl in H24;
            try rewrite HMethodReceiverDeclaredType in H24;
            try inversion H24; try trivial.
            all: try inversion H24; try easy.
          }
          1:{
            destruct H24Special as [HReceiverQualifier HBasetype].
            destruct HBasetype as [HReceiverDeclaredQualifier HBasetype].
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            apply get_this_qualified_type_nth_error in H16.
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            specialize (Hcorrcopy 0 Hsenvdom Tthis H16).
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

            assert (r_muttype h ly = Some rq_obj).
            {
              unfold r_muttype.
              rewrite Hobjy.
              simpl.
              reflexivity.
            }

            assert (rq_obj = qinner).
            {
              rewrite H0 in Hqcontext.
              inversion Hqcontext; subst qinner.
              reflexivity.
            }
            subst rq_obj.
            rewrite Hmsigeq.

            unfold qualifier_typable_context.
            unfold qualifier_typable_context in HyQualifierTypablility.
            unfold qualifier_typable_context in Houtter_qualifier_typable.
            unfold vpa_mutabilty_rs.
            unfold vpa_mutabilty_rs in HyQualifierTypablility.
            unfold vpa_mutabilty_rs in Houtter_qualifier_typable.

            destruct qinner eqn:HInnerReceiverMutability;
            destruct (sqtype (mreceiver (msignature mdef0))) eqn:HMethodReceiverDeclaredType;
            try trivial.
            all: destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            destruct (sqtype Ty) eqn:HTyStaticMutability;
            try trivial.
            all: destruct (sqtype Tthis) eqn:HTthisStaticMutability; try trivial.
            all: try easy.
          }
        }

        (* -------------------------------------------------- *)
        (* Other index - > 1 *)
        apply qualified_type_subtype_q_subtype in H20.
        unfold runtime_getVal.
        simpl.
        destruct (nth_error vals i') as [v|] eqn:Hval_i.
          - (* Parameter i' exists *)
            destruct v as [|loc]; [trivial|].
            (* Use H23 to get the subtyping relationship *)
            assert (Hi'_bound : i' < List.length argtypes).
            {
              apply Forall2_length in H26.
              simpl in Hi.
              simpl in Hnth.
              rewrite Hmsigeq in Hnth.
              rewrite H26.
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
                nth_error sΓ' iArgInSenv = Some argtype
            /\ nth_error zs i' = Some iArgInSenv).
            {
              destruct (static_getType_list_nth_zs sΓ' zs argtypes i' argtype H15 Hargtype)
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
              destruct (runtime_lookup_list_nth_zs rΓ zs vals i' (Iot loc) H4 Hval_i)
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
            eapply Forall2_nth_error in H26; eauto.
            apply qualified_type_subtype_base_subtype in H26.
            rewrite (vpa_mutabilty_tt_sctype_safe_ro Ty sqt) in H26.
            eapply base_trans; eauto.

            (* Qualifier Typability *)
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in H26; eauto.
            apply qualified_type_subtype_q_subtype in H26.
            rewrite sq_vpa_tt_eq_qq_safe_ro in H26.
            specialize (Hcorrcopy_2 lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            apply get_this_qualified_type_nth_error in H16.
            specialize (Hcorrcopy_2 0 Hsenvdom Tthis H16).
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
            clear - H26 Harg_qualifiertypability HyQualifierTypablility HOutterReceiverQualifierTypablility.

            destruct (rqtype (rt_type argobj)) eqn:Hargobjmutability; move Hargobjmutability at bottom;
            destruct (sqtype sqt) eqn:HParameterStaticDeclearedMutability; move HParameterStaticDeclearedMutability at bottom;
            destruct qinner eqn:HInnerReceiverMutability; move HInnerReceiverMutability at bottom;
            try solve_qualifier_typable_correct_concrete.

            all: destruct (sqtype Ty) eqn:HTyStaticMutability;
            destruct (sqtype argtype) eqn:HArgTypeStaticMutability;
            simpl in H26;
            try solve_q_subtype_wrong.

            all: 
            destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            try solve_qualifier_typable_wrong_concrete.

          - (* Parameter i' doesn't exist - contradiction *)
            exfalso.
            apply nth_error_None in Hval_i.
            apply runtime_lookup_list_preserves_length in H4.
            apply static_getType_list_preserves_length in H15.
            apply Forall2_length in H26.
            rewrite H4 in Hval_i.
            rewrite <- H15 in Hval_i.
            rewrite H26 in Hval_i.
            simpl in Hi.
            simpl in Hnth.
            rewrite <- Hmsigeq in Hval_i.
            lia.
      }
      rename x0 into sΓmethodend.
      assert (wf_r_config CT sΓmethodend rΓ'' h'). 
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
        destruct Hclass as [Hclass_ [Hobj_ [Hcname_consistent_ Hfind_consistent_]]].
        repeat split.
        exact Hclass_.
        exact Hobj_.
        apply Hcname_consistent_.
        apply Hfind_consistent_.
        apply Hfind_consistent_.
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
        have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓmethodinit h (mbody_stmt (mbody mdef)) rΓ'' h' Heval.
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
        have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓmethodinit h (mbody_stmt (mbody mdef)) rΓ'' h' Heval.
        assert (Hloc_dom : loc < dom h) by (apply runtime_getObj_dom in Hobjloc; exact Hobjloc).
        assert (Hloc_dom' : loc < dom h') by lia.
        destruct (runtime_getObj h' loc) as [obj'|] eqn:Hobj'.
        trivial.
        exfalso. apply runtime_getObj_not_dom in Hobj'. lia.
        unfold runtime_getVal in H6.
        destruct retval as [|loc]; [trivial|].
        unfold wf_renv in Hrenvinit.
        destruct Hrenvinit as [_ [_ Hrenv_wf]].
        eapply Forall_nth_error in Hrenv_wf; eauto.
        simpl in Hrenv_wf.
        destruct (runtime_getObj h' loc) as [obj|] eqn:Hobjloc; [trivial|].
        contradiction.
        apply static_getType_dom in H13.
        rewrite Hlen in H13.
        exact H13.

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
          + apply static_getType_dom in H13.
            rewrite Hlen in H13.
            exact H13.
          + (* Show wf_r_typable for retval *)
            assert (Hnth_x : nth_error sΓ' x = Some Tx).
            {
              unfold static_getType in H13.
              exact H13.
            }
            rewrite Hnth_x in Hnth.
            injection Hnth as Hsqt_eq.
            subst sqt.
            (* Use the fact that retval is well-typed from method return *)
            unfold runtime_getVal in H6.
            destruct retval as [|loc]; [trivial|].
            assert (Hret_dom : mreturn (mbody mdef) < dom (vars rΓ'')).
            {
              apply nth_error_Some.
              rewrite H6.
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
              easy.
            }
            assert (HInnerReceiverMutability: exists InnerReceiverMutability, r_muttype h' ly = Some InnerReceiverMutability).
            {
              eapply receiver_mutability_exists_from_bound; eauto.
              unfold r_basetype in H0.
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
            specialize (Hcorrinit (mreturn (mbody mdef)) Hret_dom mrettype Hnth_mbodyret).
            unfold wf_r_typable.
            unfold r_type.
            destruct (runtime_getObj h' loc) as [retobj|] eqn:HReturnObject.
            2:{
              unfold runtime_getVal in Hcorrinit.
              rewrite H6 in Hcorrinit.
              unfold wf_r_typable in Hcorrinit.
              unfold r_type in Hcorrinit.
              rewrite HReturnObject in Hcorrinit.
              easy.
            }
            specialize (Hcorr outterreceiveinitriot qoutter Hget_outter_iot HOutterReceiverMutabilityInit).
            have H14copy := H14.
            apply static_getType_dom in H14.
            specialize (Hcorr y H14 Ty H14copy).
            rewrite H in Hcorr.
            unfold wf_r_typable in Hcorr; unfold r_type in Hcorr.
            destruct (runtime_getObj h ly) as [objly|] eqn:Hobj; [|contradiction].
            destruct Hcorr as [HyBasetype HyQualifierTypability].
            assert (rctype (rt_type objly) = cy).
            {
              unfold r_basetype in H0.
              rewrite Hobj in H0.
              simpl in H0.
              inversion H0; subst cy.
              reflexivity.
            }
            subst cy.
            assert (Hmsigeq: msignature mdef = msignature mdef0).
            {
              eapply method_signature_consistent_subtype; eauto.
            }
            rewrite Hleninit in Hmbodyretvar_dom.
            destruct (runtime_getVal rΓ'' (mreturn (mbody mdef))) eqn: Hmet_val; [|easy].
            destruct v.
            2:{
              unfold runtime_getVal in Hmet_val.
              rewrite Hmet_val in H6.
              inversion H6.
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
              apply qualified_type_subtype_base_subtype in H20.
              rewrite (vpa_mutabilty_tt_sctype_safe_ro Ty (mret (msignature mdef0))) in H20.
              rewrite Hmsigeq in Hsubtype_ret.
              apply qualified_type_subtype_base_subtype in Hsubtype_ret.
              eapply base_trans; eauto.
              eapply base_trans; eauto.

              (* Qualifier Typability *)
              move Hrorettypequalifier at bottom.
              apply qualified_type_subtype_q_subtype in H20.
              move H20 at bottom.
              move Hcorr_copy at bottom.
              specialize (Hcorr_copy outterreceiveinitriot qoutter Hget_outter_iot HOutterReceiverMutabilityInit).
              unfold wf_senv in Hsenv.
              destruct Hsenv as [Hsenvdom _].
              apply get_this_qualified_type_nth_error in H16.
              specialize (Hcorr_copy 0 Hsenvdom Tthis H16).
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
                assert (r_muttype h ly = Some InnerReceiverMutability).
                {
                  eapply eval_stmt_preserves_r_muttype_backwards; eauto.
                  apply runtime_getObj_dom in Hobj.
                  lia.
                }
                unfold r_muttype in H9.
                rewrite Hobj in H9.
                simpl in H9.
                inversion H9; subst InnerReceiverMutability.
                reflexivity.
              }
              subst InnerReceiverMutability.
              move Hsubtype_ret at bottom.
              move H24 at bottom.
              apply qualified_type_subtype_q_subtype in Hsubtype_ret.
              destruct H24 as [H24 | H24Special].
              1:{
                apply qualified_type_subtype_q_subtype in H24.
                rewrite <- Hmsigeq in H20.
                rewrite <- Hmsigeq in H24.

                clear - Hrorettypequalifier H20 Houtter_qualifier_typable Hsubtype_ret H24 HyQualifierTypability.
                rewrite sq_vpa_tt_eq_qq_safe_ro in H20.
                rewrite sq_vpa_tt_eq_qq_safe_ro in H24.
                destruct (rqtype (rt_type retobj)) eqn:Hrorettypemutability; move Hrorettypequalifier at bottom;
                destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutabilityValue; move HOutterReceiverMutabilityValue at bottom;
                destruct (sqtype Tx) eqn:HTxStaticMutability; move HTxStaticMutability at bottom;
                try solve_qualifier_typable_correct_concrete.

                all:
                destruct ((sqtype (mreceiver (msignature mdef)))) eqn:HMethodReceiverDeclaredType;
                destruct (sqtype Ty) eqn:HTyStaticMutability;
                simpl in H24;
                try solve_q_subtype_wrong.
                
                all:
                destruct (sqtype (mret (msignature mdef))) eqn:HMethodRetDeclaredType;
                simpl in H20;
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
                rewrite <- Hmsigeq in H20.
                rewrite <- Hmsigeq in HReceiverDeclaredQualifier.

                clear - Hrorettypequalifier H20 Houtter_qualifier_typable Hsubtype_ret HReceiverDeclaredQualifier HBasetype HyQualifierTypability.
                rewrite sq_vpa_tt_eq_qq_safe_ro in H20.
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
                simpl in H20;
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
            rewrite H6 in Hmet_val.
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
    specialize (IHHeval1 eq_refl Heval1 mt sΓ'0 sΓ Hwf H5) as IH1.
    specialize (IHHeval2 eq_refl Heval2 mt sΓ' sΓ'0 IH1 H7) as IH2.
    exact IH2.
Qed.

Notation "l [ i ]" := (nth_error l i) (at level 50).