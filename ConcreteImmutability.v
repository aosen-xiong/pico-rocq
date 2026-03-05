Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation.
Require Import Properties DeepImmutability Reachability Preservation ReadonlyHelper ReadonlyConfinement ReadonlyNoMutation ReadonlySafety.
From Stdlib Require Import List.
From Stdlib Require String.
Import ListNotations.
From RecordUpdate Require Import RecordUpdate.

Lemma deep_concrete_immutability_preservation: 
  forall CT sΓ rΓ h stmt rΓ' h' sΓ' l C anyrq vals vals' f
    (Hconfined : env_respects_protected_set (reachable_locations_from_initial_env CT h rΓ) sΓ rΓ)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ ConcreteImm stmt sΓ')
    (Heval : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h')
    (Hlocalset : Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) l)
    (Hobj : runtime_getObj h l = Some (mkObj (mkruntime_type anyrq C) vals))
    (Hobj' : runtime_getObj h' l = Some (mkObj (mkruntime_type anyrq C) vals')),
  nth_error vals f = nth_error vals' f.
Proof.
  intros.
  remember OK as ok.
  generalize dependent sΓ.
  generalize dependent sΓ'.
  generalize dependent vals. 
  generalize dependent vals'.
  induction Heval; intros; subst; try discriminate.
  - (* Skip *) 
    rewrite Hobj in Hobj'.
    inversion Hobj'; subst.
    reflexivity.
  - (* Local *)
    rewrite Hobj in Hobj'.
    inversion Hobj'; subst.
    reflexivity.
  - (* VarAss *)
    rewrite Hobj in Hobj'.
    inversion Hobj'; subst.
    reflexivity.
  - (* FldWrite *)
    + (* Protected objects unchanged *)
    {
    (* intros l C anyrq vals vals' Hin Hobj Hobj' f0 Hprotected.   *)
    destruct (Nat.eq_dec loc_x l) as [Halias | Hno_alias].
    -
      subst loc_x.
      destruct (Nat.eq_dec f f0) as [Heq_f | Hneq_f].
      + (* Same field case: contradiction *)
        subst f0.
        inversion Htyping; subst.
        unfold env_respects_protected_set in Hconfined.
        have Hx_safe := mut_var_cannot_point_to_P sΓ' rΓ x Tx l (reachable_locations_from_initial_env CT h rΓ) H7 H Hconfined Hlocalset.
        
        (* Case on assignability *)
        apply vpa_assingability_assign_cases_concret_imm in H16.
        unfold wf_r_config in Hwf.
        destruct Hwf as [Hclasstable [_[Hrenv [_ [_ Htypable]]]]].
        unfold wf_renv in Hrenv.
        (* try destruct (extract_receiver_from_wf_config CT sΓ rΓ h Hwf) as [iot [qcontext [Hget_iot[Hiot_dom Hqcontext]]]]. *)
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
        assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
        {
          eapply receiver_mutability_exists_from_bound; eauto.
        }
        destruct HOutterReceiverMutability as [qcontext Hqcontext].
        specialize (Htypable iot qcontext Hget_iot Hqcontext x).
        have H7copy := H7.
        apply static_getType_dom in H7.
        unfold static_getType in H7copy.
        specialize (Htypable H7 Tx H7copy).
        rewrite H in Htypable.
        unfold wf_r_typable in Htypable.
        unfold r_type in Htypable.
        rewrite Hobj in Htypable.
        destruct Htypable as [base qualifier].
        simpl in base.
        destruct H16 as [[Hx_mut Ha_assignable] | [Hx_mut Ha_rda]].
        ++ (* Case: a = Assignable *)
          rewrite Hx_mut in Hx_safe.
          exfalso; apply Hx_safe; reflexivity.
        ++ (* Case: sqtype Tx = Mut ∧ a = RDA *)
          exfalso.
          apply Hx_safe.
          exact Hx_mut.
      + (* Different field case: trivial *)
        unfold update_field in Hobj'.
        rewrite H0 in Hobj'.
        simpl in Hobj'.

        (* Extract the domain bound for l *)
        assert (Hdom : l < dom h).
        {
          apply runtime_getObj_dom in H0.
          exact H0.
        }

        (* After update_field, the object at l has fields updated at f0 *)
        rewrite runtime_getObj_update_same in Hobj'; auto.

        injection Hobj' as _ Hvals'_eq.
        rewrite H0 in Hobj.
        injection Hobj as Hvals_eq.

        (* vals' is just vals with f0 updated, so f is unchanged *)
        rewrite <- Hvals'_eq.
        rewrite update_diff.
        --
         symmetry; exact Hneq_f.
        -- 
        assert (Hfields : fields_map o = vals).
        {
          rewrite Hvals_eq.
          reflexivity.
        }
        rewrite Hfields.
        reflexivity.
    -
      (* No aliasing case: trivial *)
      unfold update_field in Hobj'.
      have Heq : runtime_getObj 
        (match runtime_getObj h loc_x with
        | Some o => [loc_x ↦ o <| fields_map := update f0 val_y (fields_map o) |>] h
        | None => h
        end) l = runtime_getObj h l.
      {
        destruct (runtime_getObj h loc_x).
        - apply runtime_getObj_update_diff; auto.
        - reflexivity.
      }
      rewrite Heq in Hobj'.
      rewrite Hobj in Hobj'.
      inversion Hobj'.
      reflexivity.
    }
  - (* New *)
    (* intros l C anyrq vals0 vals' Hin Hobj Hobj' f Hprotected. *)
    unfold protected_locset in Hlocalset.

    (* Extract l < dom h from reachable_abs *)
    assert(Hl_old : l < dom h).
    {
      apply runtime_getObj_dom in Hobj.
      exact Hobj.
    }
    
    rewrite runtime_getObj_last2 in Hobj'; auto.
  - (* Call *)
    inversion Htyping; subst sΓ'; subst.
    have Hwfcopy := Hwf.
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hclasstable [Hheap [Hrenv [Hsenv [_ Htypable]]]]].
    unfold env_respects_protected_set in *.
    specialize (IHHeval (eq_refl)).
    destruct H1 as [mdeflookup getmbody].
    remember (msignature mdef) as msig.
    inversion mdeflookup; revert getmbody; subst; intro getmbody.
    assert (Hwfmethod: wf_method CT cy mdef).
    {
      eapply method_lookup_wf_class; eauto.
      eapply r_basetype_in_dom; eauto.
      unfold gget_method in H3.
      apply find_some in H3.
      destruct H3.
      exact H2.
    }
    unfold wf_method in Hwfmethod;
    destruct Hwfmethod as [sΓmethodend [mbodyreturntype [Hmethodbody_typing [HmethodReturnBound [HmethodReturnType [HmethodReturnSubtype HMethodoverride]]]]]];
    remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit;
    remember {| vars := Iot ly :: vals |} as rΓmethodinit;
    remember (rΓ <| vars := update x retval (vars rΓ) |>) as rΓ'''.
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

        apply static_getType_list_preserves_length in H11.
        apply runtime_lookup_list_preserves_length in H4.
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        simpl.
        f_equal.
        apply Forall2_length in H22.
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H10.
          exact H10.
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
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H10).
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
        rewrite <- H22.
        exact H11.

        (* Correspondence holds for inner environment *)
        intros ι qinner HreceiverAddr Hqcontext i Hi sqt Hnth.
        rewrite HeqsΓmethodinit in Hnth, Hi.
        rewrite HeqrΓmethodinit.
        simpl in *.
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H10.
          exact H10.
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
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H10).
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
        destruct H20 as [H20 | H20].
        apply qualified_type_subtype_base_subtype in H20.
        (* rewrite (vpa_mutabilty_tt_sctype Tthis Ty) in H23. *)
        rewrite (vpa_mutabilty_tt_sctype_safe_ro Ty (mreceiver (msignature mdef0))) in H20.
        eapply base_trans; eauto.
        destruct H20 as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
        eapply base_trans; eauto.

        (* Qualifier typbility *)
        1: 
        {
          destruct H20 as [H20 | H20].
          1:{
            apply qualified_type_subtype_q_subtype in H20.
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            apply get_this_qualified_type_nth_error in H12.
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            specialize (Hcorrcopy 0 Hsenvdom Tthis H12).
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
            unfold vpa_mutabilty_tt_safe_ro in H20.
            rewrite <- Hmsigeq in H20.

            destruct qinner eqn:HInnerReceiverMutability;
            destruct (sqtype (mreceiver (msignature mdef))) eqn:HMethodReceiverDeclaredType;
            try trivial.
            all: destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            destruct (sqtype Ty) eqn:HTyStaticMutability;
            try trivial.
            all: destruct (sqtype Tthis) eqn:HTthisStaticMutability;
            try rewrite HTyStaticMutability in H20;
            simpl in H20;
            try rewrite HMethodReceiverDeclaredType in H20;
            try inversion H20; try trivial.
            all: try inversion H20; try easy.
          }
          1:{
            destruct H20 as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            apply get_this_qualified_type_nth_error in H12.
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            specialize (Hcorrcopy 0 Hsenvdom Tthis H12).
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
            rewrite <- Hmsigeq in HReceiverDeclearedQualifier.
            rewrite HReceiverDeclearedQualifier.

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
            (* Use H23 to get the subtyping relationship *)
            assert (Hi'_bound : i' < List.length argtypes).
            {
              apply Forall2_length in H22.
              simpl in Hi.
              simpl in Hnth.
              rewrite Hmsigeq in Hnth.
              rewrite H22.
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
              destruct (static_getType_list_nth_zs sΓ zs argtypes i' argtype H11 Hargtype)
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
            eapply Forall2_nth_error in H22; eauto.
            apply qualified_type_subtype_base_subtype in H22.
            rewrite (vpa_mutabilty_tt_sctype_safe_ro Ty sqt) in H22.
            eapply base_trans; eauto.

            (* Qualifier Typability *)
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in H22; eauto.
            apply qualified_type_subtype_q_subtype in H22.
            rewrite sq_vpa_tt_eq_qq_safe_ro in H22.
            specialize (Hcorrcopy_2 lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            apply get_this_qualified_type_nth_error in H12.
            specialize (Hcorrcopy_2 0 Hsenvdom Tthis H12).
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
            clear - H22 Harg_qualifiertypability HyQualifierTypablility HOutterReceiverQualifierTypablility.

            destruct (rqtype (rt_type argobj)) eqn:Hargobjmutability; move Hargobjmutability at bottom;
            destruct (sqtype sqt) eqn:HParameterStaticDeclearedMutability; move HParameterStaticDeclearedMutability at bottom;
            destruct qinner eqn:HInnerReceiverMutability; move HInnerReceiverMutability at bottom;
            try solve_qualifier_typable_correct_concrete.

            all: destruct (sqtype Ty) eqn:HTyStaticMutability;
            destruct (sqtype argtype) eqn:HArgTypeStaticMutability;
            simpl in H22;
            try solve_q_subtype_wrong.

            all: 
            destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            try solve_qualifier_typable_wrong_concrete.

          - (* Parameter i' doesn't exist - contradiction *)
            exfalso.
            apply nth_error_None in Hval_i.
            apply runtime_lookup_list_preserves_length in H4.
            apply static_getType_list_preserves_length in H11.
            apply Forall2_length in H22.
            rewrite H4 in Hval_i.
            rewrite <- H11 in Hval_i.
            rewrite H22 in Hval_i.
            simpl in Hi.
            simpl in Hnth.
            rewrite <- Hmsigeq in Hval_i.
            lia.
    }
    destruct (classic (Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓmethodinit) l)) as [Hlocalset' | Hnot_reachable].
    2:
    {
      have Hunchanged : vals0 = vals'.
      {
        eapply stmt_preserves_unreachable_objects; eauto.
      }
      subst vals'.
      reflexivity.
    }
    assert (HenvInvariant: env_respects_protected_set (reachable_locations_from_initial_env CT h rΓmethodinit)
    sΓmethodinit rΓmethodinit).
    {
      unfold env_respects_protected_set.
      intros z l_z Tz Hlookup_s Hlookup_r Hin_P.
      rewrite HeqsΓmethodinit in Hlookup_s.
      rewrite HeqrΓmethodinit in Hlookup_r.
      unfold static_getType in Hlookup_s.
      unfold runtime_getVal in Hlookup_r.
      simpl in Hlookup_s, Hlookup_r.
      destruct z as [| z'].
      - simpl in Hlookup_s, Hlookup_r.
      injection Hlookup_s as <-. injection Hlookup_r as <-.
      unfold is_safe_mode.
      have Hin_P_orig : Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) ly.
      {
        unfold reachable_locations_from_initial_env.
        exists y, ly.
        split.
        - exact H.  (* runtime_getVal rΓ y = Some (Iot ly) *)
        - apply rch_heap.
          apply reachable_locations_from_initial_env_dom in Hin_P; auto.
      }
      have Hty_safe : is_safe_mode (sqtype Ty).
      {
        unfold env_respects_protected_set in Hconfined.
        specialize (Hconfined y ly Ty H10 H Hin_P_orig).
        exact Hconfined.
      }
      unfold is_safe_mode in Hty_safe.
      unfold vpa_mutabilty_tt_safe_ro.
      assert (Hy_dom : y < dom sΓ).
      {
        apply static_getType_dom in H10.
        exact H10.
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
      specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H10).
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
      clear - Hmsigeq Hty_safe H20.
      destruct H20 as [H20 | H20].
      apply qualified_type_subtype_q_subtype in H20.
      rewrite Hmsigeq.
      unfold vpa_mutabilty_tt_safe_ro in H20.
      destruct Hty_safe as [HRd | [HLost | [HRDM| HImm] ]].
      + (* Case: sqtype Ty = Rd *)
        rewrite HRd in H20.
        destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
        simpl in H20.
        all: try solve_q_subtype_wrong.
        all: try solve solve_safe_mode.
        try rewrite HMethodReceiverDeclaredType in H20; try solve_q_subtype_wrong.
      + (* Case: sqtype Ty = Lost *)
        rewrite HLost in H20.
        destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
        simpl in H20.
        all: try solve_q_subtype_wrong.
        all: try solve solve_safe_mode.
        try rewrite HMethodReceiverDeclaredType in H20; try solve_q_subtype_wrong.
      + (* Case: sqtype Ty = RDM *)
        rewrite HRDM in H20.
        destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
        simpl in H20.
        all: try solve_q_subtype_wrong.
        all: try solve solve_safe_mode.
        try rewrite HMethodReceiverDeclaredType in H20; try solve_q_subtype_wrong.
      + (* Case: sqtype Ty = Imm *)
        rewrite HImm in H20.
        destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
        simpl in H20.
        all: try solve_q_subtype_wrong.
        all: try solve solve_safe_mode.
        try rewrite HMethodReceiverDeclaredType in H20; try solve_q_subtype_wrong.  
      + 
        destruct H20 as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
        rewrite <- Hmsigeq in HReceiverDeclearedQualifier.
        right; right; left; exact HReceiverDeclearedQualifier.
      -
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H10.
          exact H10.
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
        specialize (Htypable iot qoutter Hget_iot Hqoutter y Hy_dom Ty H10).
        unfold wf_r_typable in Htypable.
        unfold r_basetype in H1.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy.
        2:{
          unfold r_basetype in H0.
          rewrite Hobjy in H0.
          discriminate.
        }
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        unfold r_type in Htypable.
        rewrite H in Htypable.
        rewrite Hobjy in Htypable.
        simpl in Htypable.
        destruct Htypable as [Hsubtype Hqualifier].
        simpl in Hobjy.

        simpl in H1.
        inversion H1.
        assert (Hrc_obj_eq: rc_obj = cy).
        {
          unfold r_basetype in H0.
          rewrite Hobjy in H0.
          inversion H0.
          easy.
        }
        subst rc_obj.
        assert (Hsigeq: msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        have Hnth_param_type : nth_error (mparams (msignature mdef)) z' = Some Tz.
        {
          simpl in Hlookup_s.
          easy.
        }

        have Hnth_param_val : nth_error vals z' = Some (Iot l_z).
        {
          simpl in Hlookup_r.
          easy.
        }
        assert (Hi'_bound : z' < List.length argtypes).
        {
          apply Forall2_length in H22.
          rewrite <- Hsigeq in H22.
          assert (H_bound_params : z' < dom (mparams (msignature mdef))).
          {
            apply nth_error_Some. (* Converts "index < len" to "lookup <> None" *)
            rewrite Hnth_param_type.   (* lookup is Some Tz *)
            discriminate.         (* Some <> None *)
          }

          (* 2. Convert to bound for argtypes using the equality *)
          rewrite <- H22 in H_bound_params. (* Replace length of params with length of argtypes *)

          (* 3. Solve the goal *)
          exact H_bound_params.
        }

        have Hnth_arg: exists T_arg, nth_error argtypes z' = Some T_arg.
        {
          apply nth_error_Some_exists.
          exact Hi'_bound.
        }

        destruct Hnth_arg as [T_arg Hnth_arg].
        eapply Forall2_nth_error with (i := z') (a := T_arg) (b := Tz) in H22; [|auto|rewrite <- Hsigeq; exact Hnth_param_type].
        unfold env_respects_protected_set in Hconfined.
        apply adapated_subtype_safe_implies_safe in H22; auto.

        have HargtypeFromsEnv :
          exists z_outter,
            static_getType sΓ z_outter = Some T_arg /\
            nth_error zs z' = Some z_outter.
        {
          destruct (static_getType_list_nth_zs sΓ zs argtypes z' T_arg H11 Hnth_arg)
            as [j [Hzs_j Hst_j]].
          exists j.
          split.
          - unfold static_getType. exact Hst_j.
          - exact Hzs_j.
        }

        destruct HargtypeFromsEnv as [z_outter [HgetZ_type Hzs_z_outter]].

        have HgetZ_val : runtime_getVal rΓ z_outter = Some (Iot l_z).
        {
          destruct (runtime_lookup_list_nth_zs rΓ zs vals z' (Iot l_z) H4 Hnth_param_val)
            as [j [Hzs_j Hget_j]].
          assert (HzEq : z_outter = j) by (
            rewrite Hzs_z_outter in Hzs_j;
            inversion Hzs_j; reflexivity
          ).
          subst j.
          exact Hget_j.
        }
        have Hin_P_orig : Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) l_z.
        {
          unfold reachable_locations_from_initial_env.
          exists z_outter, l_z.
          split.
          - exact HgetZ_val.  (* runtime_getVal rΓ y = Some (Iot ly) *)
          - apply rch_heap.
            apply reachable_locations_from_initial_env_dom in Hin_P; auto.
        }
        specialize (Hconfined z_outter l_z T_arg HgetZ_type HgetZ_val Hin_P_orig); auto.
    }
    {
      rewrite <- getmbody in Hmethodbody_typing.
      assert (Hy_dom : y < dom sΓ).
      {
        apply static_getType_dom in H10.
        exact H10.
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
      specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H10).
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

      rewrite Hmsigeq in Hmethodbody_typing.
      destruct (mtype (msignature mdef0)).
      exfalso; apply H15; reflexivity.
      inversion H24; subst.
      specialize (IHHeval Hlocalset' vals' Hobj' vals0 Hobj sΓmethodend sΓmethodinit).
      specialize (IHHeval HenvInvariant Hwf_method_frame).
      specialize (IHHeval Hmethodbody_typing); auto.
    }
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
        apply static_getType_list_preserves_length in H11.
        apply runtime_lookup_list_preserves_length in H4.
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        simpl.
        f_equal.
        apply Forall2_length in H22.
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H10.
          exact H10.
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
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H10).
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
        rewrite <- H22.
        exact H11.

        (* Correspondence holds for inner environment *)
        intros ι qinner HreceiverAddr Hqcontext i Hi sqt Hnth.
        rewrite HeqsΓmethodinit in Hnth, Hi.
        rewrite HeqrΓmethodinit.
        simpl in *.
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H10.
          exact H10.
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
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H10).
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
        destruct H20 as [H20 | H20].
        apply qualified_type_subtype_base_subtype in H20.
        (* rewrite (vpa_mutabilty_tt_sctype Tthis Ty) in H23. *)
        rewrite (vpa_mutabilty_tt_sctype_safe_ro Ty (mreceiver (msignature mdef0))) in H20.
        eapply base_trans; eauto.
        destruct H20 as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
        eapply base_trans; eauto.

        (* Qualifier typbility *)
        1: 
        {
          destruct H20 as [H20 | H20].
          1:{
            apply qualified_type_subtype_q_subtype in H20.
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            apply get_this_qualified_type_nth_error in H12.
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            specialize (Hcorrcopy 0 Hsenvdom Tthis H12).
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
            unfold vpa_mutabilty_tt_safe_ro in H20.
            rewrite <- Hmsigeq in H20.

            destruct qinner eqn:HInnerReceiverMutability;
            destruct (sqtype (mreceiver (msignature mdef))) eqn:HMethodReceiverDeclaredType;
            try trivial.
            all: destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            destruct (sqtype Ty) eqn:HTyStaticMutability;
            try trivial.
            all: destruct (sqtype Tthis) eqn:HTthisStaticMutability;
            try rewrite HTyStaticMutability in H20;
            simpl in H20;
            try rewrite HMethodReceiverDeclaredType in H20;
            try inversion H20; try trivial.
            all: try inversion H20; try easy.
          }
          1:{
            destruct H20 as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            apply get_this_qualified_type_nth_error in H12.
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            specialize (Hcorrcopy 0 Hsenvdom Tthis H12).
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
            rewrite <- Hmsigeq in HReceiverDeclearedQualifier.
            rewrite HReceiverDeclearedQualifier.
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
            (* Use H23 to get the subtyping relationship *)
            assert (Hi'_bound : i' < List.length argtypes).
            {
              apply Forall2_length in H22.
              simpl in Hi.
              simpl in Hnth.
              rewrite Hmsigeq in Hnth.
              rewrite H22.
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
              destruct (static_getType_list_nth_zs sΓ zs argtypes i' argtype H11 Hargtype)
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
            eapply Forall2_nth_error in H22; eauto.
            apply qualified_type_subtype_base_subtype in H22.
            rewrite (vpa_mutabilty_tt_sctype_safe_ro Ty sqt) in H22.
            eapply base_trans; eauto.

            (* Qualifier Typability *)
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in H22; eauto.
            apply qualified_type_subtype_q_subtype in H22.
            rewrite sq_vpa_tt_eq_qq_safe_ro in H22.
            specialize (Hcorrcopy_2 lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            apply get_this_qualified_type_nth_error in H12.
            specialize (Hcorrcopy_2 0 Hsenvdom Tthis H12).
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
            clear - H22 Harg_qualifiertypability HyQualifierTypablility HOutterReceiverQualifierTypablility.

            destruct (rqtype (rt_type argobj)) eqn:Hargobjmutability; move Hargobjmutability at bottom;
            destruct (sqtype sqt) eqn:HParameterStaticDeclearedMutability; move HParameterStaticDeclearedMutability at bottom;
            destruct qinner eqn:HInnerReceiverMutability; move HInnerReceiverMutability at bottom;
            try solve_qualifier_typable_correct_concrete.

            all: destruct (sqtype Ty) eqn:HTyStaticMutability;
            destruct (sqtype argtype) eqn:HArgTypeStaticMutability;
            simpl in H22;
            try solve_q_subtype_wrong.

            all: 
            destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            try solve_qualifier_typable_wrong_concrete.

          - (* Parameter i' doesn't exist - contradiction *)
            exfalso.
            apply nth_error_None in Hval_i.
            apply runtime_lookup_list_preserves_length in H4.
            apply static_getType_list_preserves_length in H11.
            apply Forall2_length in H22.
            rewrite H4 in Hval_i.
            rewrite <- H11 in Hval_i.
            rewrite H22 in Hval_i.
            simpl in Hi.
            simpl in Hnth.
            rewrite <- Hmsigeq in Hval_i.
            lia.
    }
    destruct (classic (Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓmethodinit) l)) as [Hlocalset' | Hnot_reachable].
    2:
    {
      have Hunchanged : vals0 = vals'.
      {
        eapply stmt_preserves_unreachable_objects; eauto.
      }
      subst vals'.
      reflexivity.
    }
    assert (HenvInvariant: env_respects_protected_set (reachable_locations_from_initial_env CT h rΓmethodinit)
    sΓmethodinit rΓmethodinit).
    {
      unfold env_respects_protected_set.
      intros z l_z Tz Hlookup_s Hlookup_r Hin_P.
      rewrite HeqsΓmethodinit in Hlookup_s.
      rewrite HeqrΓmethodinit in Hlookup_r.
      unfold static_getType in Hlookup_s.
      unfold runtime_getVal in Hlookup_r.
      simpl in Hlookup_s, Hlookup_r.
      destruct z as [| z'].
      - simpl in Hlookup_s, Hlookup_r.
      injection Hlookup_s as <-. injection Hlookup_r as <-.
      unfold is_safe_mode.
      have Hin_P_orig : Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) ly.
      {
        unfold reachable_locations_from_initial_env.
        exists y, ly.
        split.
        - exact H.  (* runtime_getVal rΓ y = Some (Iot ly) *)
        - apply rch_heap.
          apply reachable_locations_from_initial_env_dom in Hin_P; auto.
      }
      have Hty_safe : is_safe_mode (sqtype Ty).
      {
        unfold env_respects_protected_set in Hconfined.
        specialize (Hconfined y ly Ty H10 H Hin_P_orig).
        exact Hconfined.
      }
      unfold is_safe_mode in Hty_safe.
      unfold vpa_mutabilty_tt_safe_ro.
      assert (Hy_dom : y < dom sΓ).
      {
        apply static_getType_dom in H10.
        exact H10.
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
      specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H10).
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
      clear - Hmsigeq Hty_safe H20.
      destruct H20 as [H20 | H20].
      apply qualified_type_subtype_q_subtype in H20.
      rewrite Hmsigeq.
      unfold vpa_mutabilty_tt_safe_ro in H20.
      destruct Hty_safe as [HRd | [HLost | [HRDM| HImm] ]].
      + (* Case: sqtype Ty = Rd *)
        rewrite HRd in H20.
        destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
        simpl in H20.
        all: try solve_q_subtype_wrong.
        all: try solve solve_safe_mode.
        try rewrite HMethodReceiverDeclaredType in H20; try solve_q_subtype_wrong.
      + (* Case: sqtype Ty = Lost *)
        rewrite HLost in H20.
        destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
        simpl in H20.
        all: try solve_q_subtype_wrong.
        all: try solve solve_safe_mode.
        try rewrite HMethodReceiverDeclaredType in H20; try solve_q_subtype_wrong.
      + (* Case: sqtype Ty = RDM *)
        rewrite HRDM in H20.
        destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
        simpl in H20.
        all: try solve_q_subtype_wrong.
        all: try solve solve_safe_mode.
        try rewrite HMethodReceiverDeclaredType in H20; try solve_q_subtype_wrong.
      + (* Case: sqtype Ty = Imm *)
        rewrite HImm in H20.
        destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
        simpl in H20.
        all: try solve_q_subtype_wrong.
        all: try solve solve_safe_mode.
        try rewrite HMethodReceiverDeclaredType in H20; try solve_q_subtype_wrong.  
      + 
        destruct H20 as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
        rewrite <- Hmsigeq in HReceiverDeclearedQualifier.
        right; right; left; exact HReceiverDeclearedQualifier.
      -
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H10.
          exact H10.
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
        specialize (Htypable iot qoutter Hget_iot Hqoutter y Hy_dom Ty H10).
        unfold wf_r_typable in Htypable.
        unfold r_basetype in H1.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy.
        2:{
          unfold r_basetype in H0.
          rewrite Hobjy in H0.
          discriminate.
        }
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        unfold r_type in Htypable.
        rewrite H in Htypable.
        rewrite Hobjy in Htypable.
        simpl in Htypable.
        destruct Htypable as [Hsubtype Hqualifier].
        simpl in Hobjy.

        simpl in H1.
        inversion H1.
        assert (Hrc_obj_eq: rc_obj = cy).
        {
          unfold r_basetype in H0.
          rewrite Hobjy in H0.
          inversion H0.
          easy.
        }
        subst rc_obj.
        assert (Hsigeq: msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        have Hnth_param_type : nth_error (mparams (msignature mdef)) z' = Some Tz.
        {
          simpl in Hlookup_s.
          easy.
        }

        have Hnth_param_val : nth_error vals z' = Some (Iot l_z).
        {
          simpl in Hlookup_r.
          easy.
        }
        assert (Hi'_bound : z' < List.length argtypes).
        {
          apply Forall2_length in H22.
          rewrite <- Hsigeq in H22.
          assert (H_bound_params : z' < dom (mparams (msignature mdef))).
          {
            apply nth_error_Some. (* Converts "index < len" to "lookup <> None" *)
            rewrite Hnth_param_type.   (* lookup is Some Tz *)
            discriminate.         (* Some <> None *)
          }

          (* 2. Convert to bound for argtypes using the equality *)
          rewrite <- H22 in H_bound_params. (* Replace length of params with length of argtypes *)

          (* 3. Solve the goal *)
          exact H_bound_params.
        }

        have Hnth_arg: exists T_arg, nth_error argtypes z' = Some T_arg.
        {
          apply nth_error_Some_exists.
          exact Hi'_bound.
        }

        destruct Hnth_arg as [T_arg Hnth_arg].
        eapply Forall2_nth_error with (i := z') (a := T_arg) (b := Tz) in H22; [|auto|rewrite <- Hsigeq; exact Hnth_param_type].
        (* apply qualified_type_subtype_q_subtype in H20. *)
        unfold env_respects_protected_set in Hconfined.
        apply adapated_subtype_safe_implies_safe in H22; auto.

        have HargtypeFromsEnv :
          exists z_outter,
            static_getType sΓ z_outter = Some T_arg /\
            nth_error zs z' = Some z_outter.
        {
          destruct (static_getType_list_nth_zs sΓ zs argtypes z' T_arg H11 Hnth_arg)
            as [j [Hzs_j Hst_j]].
          exists j.
          split.
          - unfold static_getType. exact Hst_j.
          - exact Hzs_j.
        }

        destruct HargtypeFromsEnv as [z_outter [HgetZ_type Hzs_z_outter]].

        have HgetZ_val : runtime_getVal rΓ z_outter = Some (Iot l_z).
        {
          destruct (runtime_lookup_list_nth_zs rΓ zs vals z' (Iot l_z) H4 Hnth_param_val)
            as [j [Hzs_j Hget_j]].
          assert (HzEq : z_outter = j) by (
            rewrite Hzs_z_outter in Hzs_j;
            inversion Hzs_j; reflexivity
          ).
          subst j.
          exact Hget_j.
        }
        have Hin_P_orig : Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) l_z.
        {
          unfold reachable_locations_from_initial_env.
          exists z_outter, l_z.
          split.
          - exact HgetZ_val.  (* runtime_getVal rΓ y = Some (Iot ly) *)
          - apply rch_heap.
            apply reachable_locations_from_initial_env_dom in Hin_P; auto.
        }
        specialize (Hconfined z_outter l_z T_arg HgetZ_type HgetZ_val Hin_P_orig); auto.
    }
    {
      rewrite <- getmbody in Hmethodbody_typing.
      assert (Hy_dom : y < dom sΓ).
      {
        apply static_getType_dom in H10.
        exact H10.
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
      specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H10).
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

      rewrite Hmsigeq in Hmethodbody_typing.
      destruct (mtype (msignature mdef0)).
      exfalso; apply H15; reflexivity.
      inversion H24; subst.
      specialize (IHHeval Hlocalset' vals' Hobj' vals0 Hobj sΓmethodend sΓmethodinit).
      specialize (IHHeval HenvInvariant Hwf_method_frame).
      specialize (IHHeval Hmethodbody_typing); auto.
    }
  - (* Seq *)
    inversion Htyping; subst.
    rename sΓ' into  sΓ''.
    rename sΓ'0 into sΓ'.
    
    (* Extract wellformedness for intermediate state using preservation_pico *)
    have Hwf' : wf_r_config CT sΓ' rΓ' h'.
    {
      eapply preservation_pico; eauto.
    }

    assert (Hconfined_intermediate: env_respects_protected_set (reachable_locations_from_initial_env CT h rΓ) sΓ' rΓ').
    {
      eapply stmt_preserves_confinement; eauto.
      easy.
    }

    specialize (eval_stmt_preserves_heap_domain_simple CT rΓ h s1 rΓ' h' Heval1) as Hh'.
    assert (Hldomh': l < dom h') by (apply runtime_getObj_dom in Hobj; lia).
    specialize (runtime_getObj_Some h' l Hldomh') as [T [values' Hh'some]].
    specialize (runtime_preserves_r_type_heap CT rΓ h l ({| rqtype := anyrq; rctype := C |})
    h' vals s1 rΓ' Hobj Heval1) as [vals1 Hrtype].
    rewrite Hrtype in Hh'some; inversion Hh'some; subst.
    specialize (IHHeval1 eq_refl Hlocalset values' Hrtype vals Hobj sΓ' sΓ Hconfined Hwf H5).
    specialize (IHHeval2 eq_refl Hlocalset vals' Hobj' values' Hrtype sΓ'' sΓ' Hconfined_intermediate Hwf' H7).
    rewrite IHHeval2 in IHHeval1; auto.
Qed.

Theorem ConcreteImmutability :
  forall CT sΓ rΓ h stmt rΓ' h' sΓ' x y mindex Ty mdef zs anyC vals ly 
         loc_arg C anyrq vals_arg vals_arg' f
    (Hstmt : stmt = (SCall x mindex y zs))
    (HTy : Ty = Build_qualified_type RO anyC)
    (Hstatic_type : static_getType sΓ y = Some Ty)
    (Hmethod_lookup : FindMethodWithName CT (sctype Ty) mindex mdef)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ ConcreteImm stmt sΓ')
    (Heval : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h')
    (Hget_y : runtime_getVal rΓ y = Some (Iot ly))
    (Hget_zs : runtime_lookup_list rΓ zs = Some vals)
    (HinP: Ensembles.In Loc (reachable_locations_from_vals CT h (Iot ly :: vals)) loc_arg)
    (Harg_obj : runtime_getObj h loc_arg = Some (mkObj (mkruntime_type anyrq C) vals_arg))
    (Harg_obj' : runtime_getObj h' loc_arg = Some (mkObj (mkruntime_type anyrq C) vals_arg'))
    (Hall_readonly : all_params_safe (msignature mdef)),
    nth_error vals_arg f = nth_error vals_arg' f.
Proof.
  intros.
  inversion Heval; subst; try discriminate.
  inversion H14; subst.
  have Heqy: ly = ly0.
  {
    rewrite H0 in Hget_y.
    inversion Hget_y; reflexivity.
  }
  subst ly0.
  have Heqzs : vals = vals0.
  {
    rewrite H5 in Hget_zs.
    inversion Hget_zs; reflexivity.
  }
  subst vals0.
  inversion Htyping; subst.
  rename sΓ' into sΓ.
  have HTy: Ty = {| sqtype := RO; sctype := anyC |}.
  {
    rewrite H12 in Hstatic_type.
    inversion Hstatic_type.
    reflexivity.
  }

  have Hmdefeq: mdef1 = mdef.
  {
    rewrite <- HTy in Hmethod_lookup.
    unfold wf_r_config in Hwf.
    destruct Hwf as [HClassTable _].
    unfold wf_senv in H10.
    destruct H10 as [H10 Hwftypeuse].
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
  destruct H2 as [mdeflookup getmbody].
  remember (msignature mdef) as msig.
  inversion mdeflookup; revert getmbody; subst; intro getmbody.
  +
    assert (Hwfmethod: wf_method CT cy mdef).
    {
      eapply method_lookup_wf_class; eauto.
      eapply r_basetype_in_dom; eauto.
      unfold gget_method in H4.
      apply find_some in H4.
      destruct H4.
      exact H3.
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
        unfold runtime_getVal in H.
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

        apply static_getType_list_preserves_length in H13.
        apply runtime_lookup_list_preserves_length in H5.
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        simpl.
        f_equal.
        apply Forall2_length in H25.
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H12.
          exact H12.
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
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H12).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H1.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H1 as Hcy_eq.
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
        rewrite H0 in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
        assert (msignature mdef = msignature mdef1).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        rewrite H1.
        rewrite H5.
        rewrite <- H25.
        exact H13.

        (* Correspondence holds for inner environment *)
        intros ι qinner HreceiverAddr Hqcontext i Hi sqt Hnth.
        rewrite HeqsΓmethodinit in Hnth, Hi.
        rewrite HeqrΓmethodinit.
        simpl in *.
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H12.
          exact H12.
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
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H12).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H1.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H1 as Hcy_eq.
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
        rewrite H0 in Hcorr.
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
        destruct H23 as [H23 | H23].
        apply qualified_type_subtype_base_subtype in H23.
        rewrite (vpa_mutabilty_tt_sctype_safe_ro Ty (mreceiver (msignature mdef1))) in H23.
        eapply base_trans; eauto.
        destruct H23 as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
        eapply base_trans; eauto.

        (* Qualifier typbility *)
        1: 
        {
          destruct H23 as [H23 | H23].
          1:{
            apply qualified_type_subtype_q_subtype in H23.
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            apply get_this_qualified_type_nth_error in H15.
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            specialize (Hcorrcopy 0 Hsenvdom Tthis H15).
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
              rewrite H1 in Hqcontext.
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
            unfold vpa_mutabilty_tt_safe_ro in H23.
            rewrite <- Hmsigeq in H23.

            destruct qinner eqn:HInnerReceiverMutability;
            destruct (sqtype (mreceiver (msignature mdef))) eqn:HMethodReceiverDeclaredType;
            try trivial.
            all: destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            destruct (sqtype Ty) eqn:HTyStaticMutability;
            try trivial.
            all: destruct (sqtype Tthis) eqn:HTthisStaticMutability;
            try rewrite HTyStaticMutability in H23;
            simpl in H23;
            try rewrite HMethodReceiverDeclaredType in H23;
            try inversion H23; try trivial.
            all: try inversion H23; try easy.
          }
          1:{
            destruct H23 as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            apply get_this_qualified_type_nth_error in H15.
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            specialize (Hcorrcopy 0 Hsenvdom Tthis H15).
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
              rewrite H1 in Hqcontext.
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
                nth_error sΓ iArgInSenv = Some argtype
            /\ nth_error zs i' = Some iArgInSenv).
            {
              destruct (static_getType_list_nth_zs sΓ zs argtypes i' argtype H13 Hargtype)
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
              destruct (runtime_lookup_list_nth_zs rΓ zs vals i' (Iot loc) H5 Hval_i)
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
            rewrite (vpa_mutabilty_tt_sctype_safe_ro Ty sqt) in H25.
            eapply base_trans; eauto.

            (* Qualifier Typability *)
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in H25; eauto.
            apply qualified_type_subtype_q_subtype in H25.
            rewrite sq_vpa_tt_eq_qq_safe_ro in H25.
            specialize (Hcorrcopy_2 lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            apply get_this_qualified_type_nth_error in H15.
            specialize (Hcorrcopy_2 0 Hsenvdom Tthis H15).
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
            clear - H25 Harg_qualifiertypability HyQualifierTypablility HOutterReceiverQualifierTypablility Ty.

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
            apply runtime_lookup_list_preserves_length in H5.
            apply static_getType_list_preserves_length in H13.
            apply Forall2_length in H25.
            rewrite H5 in Hval_i.
            rewrite <- H13 in Hval_i.
            rewrite H25 in Hval_i.
            simpl in Hi.
            simpl in Hnth.
            rewrite <- Hmsigeq in Hval_i.
            lia.
    }

    eapply deep_concrete_immutability_preservation with (stmt := (mbody_stmt mbody)) (sΓ' := sΓmethodend); eauto.
    assert (HenvImpliesEnvRespect: env_respects_protected_set (reachable_locations_from_initial_env CT h rΓmethodinit) sΓmethodinit rΓmethodinit).
    {
      eapply confinement_from_all_readonly_env; eauto.
      assert (Hy_dom : y < dom sΓ).
      {
        apply static_getType_dom in H12.
        exact H12.
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
      specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H12).
      unfold wf_r_typable in Hcorr.
      unfold r_basetype in H1.
      unfold r_type.
      destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
      injection H1 as Hcy_eq.
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
      rewrite H0 in Hcorr.
      rewrite Hobjy in Hcorr.
      simpl in Hcorr.
      destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
      assert (Hmsigeq: msignature mdef = msignature mdef1).
      {
        eapply method_signature_consistent_subtype; eauto.
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
      apply static_getType_dom in H12.
      exact H12.
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
    specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H12).
    unfold wf_r_typable in Hcorr.
    unfold r_basetype in H1.
    unfold r_type.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
    injection H1 as Hcy_eq.
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
    rewrite H0 in Hcorr.
    rewrite Hobjy in Hcorr.
    simpl in Hcorr.
    destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
    assert (Hmsigeq:msignature mdef = msignature mdef1).
    {
      eapply method_signature_consistent_subtype; eauto.
    }
    rewrite <- Hmsigeq in H27.
    destruct (mtype (msignature mdef)).
    inversion H27; subst.
    inversion H27; subst.
    exact Hmethodbody_typing.
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
        unfold runtime_getVal in H.
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
        apply static_getType_list_preserves_length in H13.
        apply runtime_lookup_list_preserves_length in H5.
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        simpl.
        f_equal.
        apply Forall2_length in H25.
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H12.
          exact H12.
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
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H12).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H1.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H1 as Hcy_eq.
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
        rewrite H0 in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
        assert (msignature mdef = msignature mdef1).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        rewrite H1.
        rewrite H5.
        rewrite <- H25.
        exact H13.

        (* Correspondence holds for inner environment *)
        intros ι qinner HreceiverAddr Hqcontext i Hi sqt Hnth.
        rewrite HeqsΓmethodinit in Hnth, Hi.
        rewrite HeqrΓmethodinit.
        simpl in *.
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H12.
          exact H12.
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
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H12).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H1.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H1 as Hcy_eq.
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
        rewrite H0 in Hcorr.
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
        destruct H23 as [H23 | H23].
        apply qualified_type_subtype_base_subtype in H23.
        (* rewrite (vpa_mutabilty_tt_sctype Tthis Ty) in H23. *)
        rewrite (vpa_mutabilty_tt_sctype_safe_ro Ty (mreceiver (msignature mdef1))) in H23.
        eapply base_trans; eauto.
        destruct H23 as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
        eapply base_trans; eauto.

        (* Qualifier typbility *)
        1: 
        {
          destruct H23 as [H23 | H23].
          1:{
            apply qualified_type_subtype_q_subtype in H23.
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            apply get_this_qualified_type_nth_error in H15.
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            specialize (Hcorrcopy 0 Hsenvdom Tthis H15).
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
              rewrite H1 in Hqcontext.
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
            unfold vpa_mutabilty_tt_safe_ro in H23.
            rewrite <- Hmsigeq in H23.

            destruct qinner eqn:HInnerReceiverMutability;
            destruct (sqtype (mreceiver (msignature mdef))) eqn:HMethodReceiverDeclaredType;
            try trivial.
            all: destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            destruct (sqtype Ty) eqn:HTyStaticMutability;
            try trivial.
            all: destruct (sqtype Tthis) eqn:HTthisStaticMutability;
            try rewrite HTyStaticMutability in H23;
            simpl in H23;
            try rewrite HMethodReceiverDeclaredType in H23;
            try inversion H23; try trivial.
            all: try inversion H23; try easy.
          }
          1:{
            destruct H23 as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            apply get_this_qualified_type_nth_error in H15.
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            specialize (Hcorrcopy 0 Hsenvdom Tthis H15).
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
              rewrite H1 in Hqcontext.
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
                nth_error sΓ iArgInSenv = Some argtype
            /\ nth_error zs i' = Some iArgInSenv).
            {
              destruct (static_getType_list_nth_zs sΓ zs argtypes i' argtype H13 Hargtype)
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
              destruct (runtime_lookup_list_nth_zs rΓ zs vals i' (Iot loc) H5 Hval_i)
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
            rewrite (vpa_mutabilty_tt_sctype_safe_ro Ty sqt) in H25.
            eapply base_trans; eauto.

            (* Qualifier Typability *)
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in H25; eauto.
            apply qualified_type_subtype_q_subtype in H25.
            rewrite sq_vpa_tt_eq_qq_safe_ro in H25.
            specialize (Hcorrcopy_2 lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            apply get_this_qualified_type_nth_error in H15.
            specialize (Hcorrcopy_2 0 Hsenvdom Tthis H15).
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
            apply runtime_lookup_list_preserves_length in H5.
            apply static_getType_list_preserves_length in H13.
            apply Forall2_length in H25.
            rewrite H5 in Hval_i.
            rewrite <- H13 in Hval_i.
            rewrite H25 in Hval_i.
            simpl in Hi.
            simpl in Hnth.
            rewrite <- Hmsigeq in Hval_i.
            lia.
    }
    eapply deep_concrete_immutability_preservation with (stmt := (mbody_stmt mbody)) (sΓ' := sΓmethodend); eauto.
    assert (HenvImpliesEnvRespect: env_respects_protected_set (reachable_locations_from_initial_env CT h rΓmethodinit) sΓmethodinit rΓmethodinit).
    {
      eapply confinement_from_all_readonly_env; eauto.
      assert (Hy_dom : y < dom sΓ).
      {
        apply static_getType_dom in H12.
        exact H12.
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
      specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H12).
      unfold wf_r_typable in Hcorr.
      unfold r_basetype in H1.
      unfold r_type.
      destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
      injection H1 as Hcy_eq.
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
      rewrite H0 in Hcorr.
      rewrite Hobjy in Hcorr.
      simpl in Hcorr.
      destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
      assert (Hmsigeq: msignature mdef = msignature mdef1).
      {
        eapply method_signature_consistent_subtype; eauto.
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
      apply static_getType_dom in H12.
      exact H12.
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
    specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H12).
    unfold wf_r_typable in Hcorr.
    unfold r_basetype in H1.
    unfold r_type.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
    injection H1 as Hcy_eq.
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
    rewrite H0 in Hcorr.
    rewrite Hobjy in Hcorr.
    simpl in Hcorr.
    destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
    assert (Hmsigeq:msignature mdef = msignature mdef1).
    {
      eapply method_signature_consistent_subtype; eauto.
    }
    rewrite <- Hmsigeq in H27.
    destruct (mtype (msignature mdef)).
    inversion H27; subst.
    inversion H27; subst.
    exact Hmethodbody_typing.
    have Hsubset := reachable_locations_subset_reachable_from_method_frame CT h ly vals.
    rewrite <- HeqrΓmethodinit in Hsubset.
    unfold Ensembles.Included in Hsubset.
    exact (Hsubset loc_arg HinP).
Qed.