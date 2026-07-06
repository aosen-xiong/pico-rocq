Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation Properties DeepImmutability Reachability Preservation ReadonlyHelper.
From Stdlib Require Import List.
From Stdlib Require String.
Import ListNotations.

Lemma stmt_preserves_confinement :
  forall CT sΓ mt rΓ h stmt sΓ' rΓ' h'
    (Hconfined : env_respects_protected_set (reachable_locations_from_initial_env CT h rΓ) sΓ rΓ)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Hmtype: mt <> AbstractImm)
    (Heval : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h'),
  env_respects_protected_set (reachable_locations_from_initial_env CT h rΓ) sΓ' rΓ'.
Proof.
  intros.
  remember OK as ok.
  generalize dependent sΓ.
  generalize dependent sΓ'.
  generalize dependent mt.
  have Heval_copy := Heval.
  induction Heval; intros; subst; try discriminate.
  7:
  {
    inversion Htyping; subst.
    rename sΓ' into sΓ''.
    rename sΓ'0 into sΓ'.

    (* Apply IH1 *)
	    pose proof (IHHeval1 eq_refl Heval1 mt Hmtype sΓ' sΓ Hconfined Hwf Htype1) as Henv1.

    (* Get wellformedness for intermediate state *)
	    pose proof (preservation_pico _ _ _ _ _ _ _ _ _ Hwf Htype1 Heval1) as Hwf'.

    (* assert (Hdom_root' : l_root < dom h').
    {
      apply eval_stmt_preserves_heap_domain_simple in Heval1; eauto.
      lia.
    } *)

    assert (Hconf_for_ih2 : env_respects_protected_set (reachable_locations_from_initial_env CT h rΓ) sΓ' rΓ').
    {
      eapply IHHeval1; eauto.
    }

    eapply IHHeval2; eauto.
  }
  - (* skip *)
    inversion Htyping; subst.
    exact Hconfined.
  - (* local *)
    inversion Htyping; subst.
    unfold env_respects_protected_set in *.
    (* destruct Hconfined as [Henv_respects Hheap_respects]. *)
    (* split. *)
    *
      unfold env_respects_protected_set.
      intros y l_y Ty Hlookup_s Hlookup_r Hin_P.
      destruct (Nat.eq_dec x y); subst.
      --
	        assert (Hy_eq : y = dom sΓ).
        {
          apply static_getType_dom in Hlookup_s.
	          match goal with
	          | Hstatic_none : static_getType sΓ y = None |- _ =>
	              apply static_getType_not_dom in Hstatic_none
	          end.
	          rewrite length_app in Hlookup_s; simpl in Hlookup_s. (* dom (sΓ++[T]) = S (dom sΓ) *)
	          match goal with
	          | Hstatic_none : y >= dom sΓ |- _ => lia
	          end.
        }
	        rewrite Hy_eq in Hlookup_s.
        destruct Hwf as [_ [_ [_ [_ [Hlen _]]]]]. (* gives dom sΓ = dom (vars rΓ) *)
	        rewrite Hy_eq in Hlookup_r.                  (* y = dom sΓ *)
        rewrite Hlen in Hlookup_r.                (* now y = dom (vars rΓ) *)
        rewrite runtime_getVal_last in Hlookup_r. (* yields Some Null_a *)
        discriminate.
      --

        assert (H_bound : y < dom sΓ).
        {
          (* Use the lookup success in the extended list *)
          apply static_getType_dom in Hlookup_s.
          rewrite length_app in Hlookup_s.
          simpl in Hlookup_s.
	          assert (H_x_idx : x = dom sΓ). 
	          {
	            match goal with
	            | Hstatic_none : static_getType sΓ x = None,
	              Hstatic_x : static_getType (sΓ ++ [T]) x = Some T |- _ =>
	                apply static_getType_not_dom in Hstatic_none;
	                apply static_getType_dom in Hstatic_x;
	                rewrite length_app in Hstatic_x; simpl in Hstatic_x;
	                lia
	            end.
	          }
          
          (* With x = length sΓ and x <> y, we know y < length sΓ *)
          lia. 
        }

        assert (Hlookup_s_old : static_getType sΓ y = Some Ty).
        {
          unfold static_getType in *.
          rewrite nth_error_app1 in Hlookup_s; auto.
        }

        assert (Hlookup_r_old : runtime_getVal rΓ y = Some (Iot l_y)).
        {
          unfold runtime_getVal in *.
          rewrite nth_error_app1 in Hlookup_r; auto.
          destruct Hwf as [_ [_ [_ [_ [Hlen _]]]]]. (* gives dom sΓ = dom (vars rΓ) *)
          rewrite Hlen in H_bound.                (* now y = dom (vars rΓ) *)
          auto.
        }

        unfold env_respects_protected_set in Hconfined.
        exact (Hconfined y l_y Ty Hlookup_s_old Hlookup_r_old Hin_P).
  - (* var assign *)
    + (* Invariant preserved *)
      inversion Htyping; subst.
      have Hconfined_copy := Hconfined.
      unfold env_respects_protected_set.
      unfold env_respects_protected_set in Hconfined.
      (* destruct Hconfined as [Henv_respects Hheap_respects]. *)
      rename sΓ' into sΓ.
      *
        unfold env_respects_protected_set.
        intros y l_y Ty Hlookup_s Hlookup_r Hin_P.
        unfold runtime_getVal in Hlookup_r.
        simpl in Hlookup_r.
        destruct (Nat.eq_dec y x) as [Heq_y | Hneq_y].
        -- (* y = x *)
        subst y.
	        rewrite Hget_x in Hlookup_s.
	        inversion Hlookup_s; subst Ty.
	        apply runtime_getVal_dom in Hval.
	        rewrite update_same in Hlookup_r; auto.
        injection Hlookup_r as Heq_v2.
        subst v2.
        assert (Hsafe_e : is_safe_mode (sqtype Te)).
        {
          eapply expr_eval_to_protected_implies_safe_type; eauto.
        }
        eapply subtype_safe_implies_safe; eauto.
        -- (* y <> x *)
        rewrite update_diff in Hlookup_r; auto.
        unfold env_respects_protected_set in Hconfined.
        exact (Hconfined y l_y Ty Hlookup_s Hlookup_r Hin_P).
 
    - (* Invariant preserved *)
      inversion Htyping; subst sΓ'; subst.
      unfold env_respects_protected_set in *.
      exact Hconfined.
      unfold env_respects_protected_set in *.
      exact Hconfined.
      unfold env_respects_protected_set in *.
      exact Hconfined.
    - (* Invariant preserved *)
      inversion Htyping; subst sΓ'; subst.
      unfold env_respects_protected_set in *.
      intros y l_y Ty Hlookup_s Hlookup_r Hin_P.
	      assert (Hupdate_env : (set_vars rΓ (update x (Iot dom h) (vars rΓ))) = update_r_env_value rΓ x (Iot (dom h))).
      {
        destruct rΓ.
        reflexivity.
      }
	      rewrite Hupdate_env in Hlookup_r.
      destruct (Nat.eq_dec x y); subst.
      -- (* y = x *)
      rewrite runtime_getVal_update_same in Hlookup_r; auto.
      apply static_getType_dom in Hlookup_s.
      unfold wf_r_config in Hwf.
      destruct Hwf as [_ [_[_ [_ [Hlen _]]]]].
      rewrite Hlen in Hlookup_s.
      exact Hlookup_s.
      unfold protected_locset in Hin_P.
      apply reachable_locations_from_initial_env_dom in Hin_P.
      inversion Hlookup_r; subst l_y.
      lia.
      -- (* y <> x *)
      rewrite runtime_getVal_update_diff in Hlookup_r; auto.
      eapply Hconfined; eauto.
  - (* call *)
    inversion Htyping; subst sΓ'; subst.
    exfalso; apply Hmtype; reflexivity.
    have Hwfcopy := Hwf.
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hclasstable [Hheap [Hrenv [Hsenv [Henv_len Htypable]]]]].
    unfold env_respects_protected_set in *.
    specialize (IHHeval (eq_refl)).
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
    remember (set_vars rΓ (update x retval (vars rΓ))) as rΓ'''.
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
        destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
        injection Hval_y as H1_eq.
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
          apply static_getType_dom in Hget_y.
          exact Hget_y.
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
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty Hget_y).
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
	        assert (Hmsigeq : msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype with (C := rc_obj) (D := sctype Ty) (m := m); eauto.
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
          apply static_getType_dom in Hget_y.
          exact Hget_y.
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
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty Hget_y).
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
        destruct Hrcv_sub as [Hrcv_sub | Hrcv_sub].
        apply qualified_type_subtype_base_subtype in Hrcv_sub.
        rewrite (vpa_mutability_tt_sctype_safe_ro Ty (mreceiver (msignature mdef0))) in Hrcv_sub.
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

	            assert (Hinner_mut_at_ly : r_muttype h ly = Some rq_obj).
            {
              unfold r_muttype.
              rewrite Hobjy.
              simpl.
              reflexivity.
            }

            assert (rq_obj = qinner).
            {
	              rewrite Hinner_mut_at_ly in Hqcontext.
              inversion Hqcontext; subst qinner.
              reflexivity.
            }
            subst rq_obj.

            unfold qualifier_typable_context.
            unfold qualifier_typable_context in HyQualifierTypablility.
            unfold qualifier_typable_context in Houtter_qualifier_typable.
            unfold vpa_mutability_rs.
            unfold vpa_mutability_rs in HyQualifierTypablility.
            unfold vpa_mutability_rs in Houtter_qualifier_typable.
            unfold vpa_mutability_tt_safe_ro in Hrcv_sub.
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

	            assert (Hinner_mut_at_ly : r_muttype h ly = Some rq_obj).
            {
              unfold r_muttype.
              rewrite Hobjy.
              simpl.
              reflexivity.
            }

            assert (rq_obj = qinner).
            {
	              rewrite Hinner_mut_at_ly in Hqcontext.
              inversion Hqcontext; subst qinner.
              reflexivity.
            }
            subst rq_obj.

            unfold qualifier_typable_context.
            unfold qualifier_typable_context in HyQualifierTypablility.
            unfold qualifier_typable_context in Houtter_qualifier_typable.
            unfold vpa_mutability_rs.
            unfold vpa_mutability_rs in HyQualifierTypablility.
            unfold vpa_mutability_rs in Houtter_qualifier_typable.
            rewrite <- Hmsigeq in HReceiverDeclearedQualifier.

            destruct qinner eqn:HInnerReceiverMutability;
            destruct (sqtype (mreceiver (msignature mdef))) eqn:HMethodReceiverDeclaredType;
            try trivial.
            all: destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            try trivial.
            all: destruct (sqtype Tthis) eqn:HTthisStaticMutability;
            try easy.
          }
        }
        (* clear_dups. amazing.... *)

  (* -------------------------------------------------- *)
  (* Other index - > 1 *)
        (* apply qualified_type_subtype_q_subtype in H1. *)
        unfold runtime_getVal.
        simpl.
        destruct (nth_error vals i') as [v|] eqn:Hval_i.
          - (* Parameter i' exists *)
            destruct v as [|loc|n]; [trivial| | trivial].
            (* Use Hmethod_case to get the subtyping relationship *)
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
                  | Int _ => True
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
            rewrite (vpa_mutability_tt_sctype_safe_ro Ty sqt) in Harg_sub.
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
	        - exact Hval_y.  (* runtime_getVal rΓ y = Some (Iot ly) *)
        - apply rch_heap.
          apply reachable_locations_from_initial_env_dom in Hin_P; auto.
      }
      have Hty_safe : is_safe_mode (sqtype Ty).
      {
        unfold env_respects_protected_set in Hconfined.
	        specialize (Hconfined y ly Ty Hget_y Hval_y Hin_P_orig).
        exact Hconfined.
      }
      unfold is_safe_mode in Hty_safe.
      unfold vpa_mutability_tt_safe_ro.
      assert (Hy_dom : y < dom sΓ).
      {
        apply static_getType_dom in Hget_y.
        exact Hget_y.
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
      specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty Hget_y).
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
      
      assert (Hmsigeq: msignature mdef = msignature mdef0).
      {
        eapply method_signature_consistent_subtype; eauto.
      }
      clear - Hmsigeq Hty_safe Hrcv_sub.
      destruct Hrcv_sub as [Hrcv_sub | Hrcv_sub].
      apply qualified_type_subtype_q_subtype in Hrcv_sub.
      rewrite Hmsigeq.
      unfold vpa_mutability_tt_safe_ro in Hrcv_sub.
      destruct Hty_safe as [HRd | [HLost| [HRDM | HImm]]].
      + (* Case: sqtype Ty = Rd *)
        rewrite HRd in Hrcv_sub.
        destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
        simpl in Hrcv_sub.
        all: try solve_q_subtype_wrong.
        all: try solve solve_safe_mode.
        try rewrite HMethodReceiverDeclaredType in Hrcv_sub; try solve_q_subtype_wrong.
      + (* Case: sqtype Ty = Lost *)
        rewrite HLost in Hrcv_sub.
        destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
        simpl in Hrcv_sub.
        all: try solve_q_subtype_wrong.
        all: try solve solve_safe_mode.
        try rewrite HMethodReceiverDeclaredType in Hrcv_sub; try solve_q_subtype_wrong.
      + (* Case: sqtype Ty = RDM *)
        rewrite HRDM in Hrcv_sub.
        destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
        simpl in Hrcv_sub.
        all: try solve_q_subtype_wrong.
        all: try solve solve_safe_mode.
        try rewrite HMethodReceiverDeclaredType in Hrcv_sub; try solve_q_subtype_wrong.
      + (* Case: sqtype Ty = Imm *)
        rewrite HImm in Hrcv_sub.
        destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
        simpl in Hrcv_sub.
        all: try solve_q_subtype_wrong.
        all: try solve solve_safe_mode.
        try rewrite HMethodReceiverDeclaredType in Hrcv_sub; try solve_q_subtype_wrong.
      +
        destruct Hrcv_sub as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
        rewrite <- Hmsigeq in HReceiverDeclearedQualifier.
        right; right; auto.
      -
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in Hget_y.
          exact Hget_y.
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
        specialize (Htypable iot qoutter Hget_iot Hqoutter y Hy_dom Ty Hget_y).
        unfold wf_r_typable in Htypable.
        unfold r_basetype in Hbase.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection Hbase as Hcy_eq.
        subst cy.
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        unfold r_type in Htypable.
        rewrite Hval_y in Htypable.
        rewrite Hobjy in Htypable.
        simpl in Htypable.
        destruct Htypable as [Hsubtype Hqualifier].
        simpl in Hobjy.
        assert (Hsigeq: msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype with (C := rc_obj) (D := sctype Ty) (m := m).
          - exact Hclasstable.
          - exact Hsubtype.
          - exact mdeflookup.
          - exact Hfind_m.
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
          apply Forall2_length in Harg_sub.
          rewrite <- Hsigeq in Harg_sub.
          assert (H_bound_params : z' < dom (mparams (msignature mdef))).
          {
            apply nth_error_Some. (* Converts "index < len" to "lookup <> None" *)
            rewrite Hnth_param_type.   (* lookup is Some Tz *)
            discriminate.         (* Some <> None *)
          }

          (* 2. Convert to bound for argtypes using the equality *)
          rewrite <- Harg_sub in H_bound_params. (* Replace length of params with length of argtypes *)

          (* 3. Solve the goal *)
          exact H_bound_params.
        }

        have Hnth_arg: exists T_arg, nth_error argtypes z' = Some T_arg.
        {
          apply nth_error_Some_exists.
          exact Hi'_bound.
        }

        destruct Hnth_arg as [T_arg Hnth_arg].
        eapply Forall2_nth_error with (i := z') (a := T_arg) (b := Tz) in Harg_sub; [|auto|rewrite <- Hsigeq; exact Hnth_param_type].
        (* apply qualified_type_subtype_q_subtype in Hreceiver_sub. *)
        unfold env_respects_protected_set in Hconfined.
        apply adapated_subtype_safe_implies_safe in Harg_sub; auto.

        have HargtypeFromsEnv :
          exists z_outter,
            static_getType sΓ z_outter = Some T_arg /\
            nth_error zs z' = Some z_outter.
        {
          destruct (static_getType_list_nth_zs sΓ zs argtypes z' T_arg Hget_args Hnth_arg)
            as [j [Hzs_j Hst_j]].
          exists j.
          split.
          - unfold static_getType. exact Hst_j.
          - exact Hzs_j.
        }

        destruct HargtypeFromsEnv as [z_outter [HgetZ_type Hzs_z_outter]].

        have HgetZ_val : runtime_getVal rΓ z_outter = Some (Iot l_z).
        {
          destruct (runtime_lookup_list_nth_zs rΓ zs vals z' (Iot l_z) Hargs Hnth_param_val)
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
    rewrite <- getmbody in Hmethodbody_typing.
    assert (Hy_dom : y < dom sΓ).
    {
      apply static_getType_dom in Hget_y.
      exact Hget_y.
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
    specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty Hget_y).
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
    
    assert (Hmsigeq: msignature mdef = msignature mdef0).
    {
      eapply method_signature_consistent_subtype; eauto.
    }

    rewrite Hmsigeq in Hmethodbody_typing.
    have H15 : ConcreteImm <> AbstractImm.
      discriminate.
    have H26 : ConcreteImm <> AbstractImm.
      discriminate.
    destruct (mtype (msignature mdef0)).
    exfalso; exact (Hmt_not_abs eq_refl).
    have H23 : SafeRO <> AbstractImm.
    discriminate.
    have H24 := Hmt_sub.
    destruct mt;
    try solve [exfalso; apply H23; reflexivity].
    specialize (IHHeval Heval SafeRO H23 sΓmethodend sΓmethodinit).
    specialize (IHHeval HenvInvariant Hwf_method_frame).
    specialize (IHHeval Hmethodbody_typing).
      assert (Henv_respects'': env_respects_protected_set (reachable_locations_from_initial_env CT h rΓ) sΓ rΓ''' ).
      {
        rewrite HeqrΓ'''.
        unfold env_respects_protected_set.
        intros z l_z T_z Hlookup_s Hlookup_r Hin_P.
        destruct (Nat.eq_dec x z); subst.
        -- (* CASE: z = x (New Variable) *)
          assert (T_z = Tx). 
          {
            rewrite Hget_x in Hlookup_s. 
            injection Hlookup_s as H_eq_T. subst T_z.
            reflexivity.
          }
          subst T_z.
          unfold env_respects_protected_set in IHHeval.
          have HGetMethodReturnType: static_getType sΓmethodend (mreturn (Syntax.mbody mdef)) = Some mbodyreturntype.
          {
            unfold static_getType; auto.
          }
          rewrite <- Hvars in Hlookup_r.
          have Hdom_z : z < dom (vars rΓ). 
          { 
            apply runtime_getVal_dom in Hlookup_r.
            rewrite update_length in Hlookup_r.
            exact Hlookup_r.
          }
          have Hlookup_r_copy := Hlookup_r.
          unfold runtime_getVal in Hlookup_r.
          rewrite update_same in Hlookup_r.
          lia.
          inversion Hlookup_r; subst.

          have Hin_P_inner: Ensembles.In Loc (reachable_locations_from_initial_env CT h
          {| vars := Iot ly :: vals |}) l_z.
          {
            eapply reachable_return_implies_reachable_args; eauto.
            apply reachable_locations_from_initial_env_dom in Hin_P; auto. (* This is not provable, need a lot changes *)
          }
          specialize (IHHeval (mreturn (Syntax.mbody mdef)) l_z mbodyreturntype HGetMethodReturnType Hretval Hin_P_inner).
          have Hsafe_ret : is_safe_mode (sqtype (mret (msignature mdef0))).
          {
            rewrite Hmsigeq in HmethodReturnSubtype.
            apply subtype_safe_implies_safe in HmethodReturnSubtype; auto.
          }
          assert (HlyInP: Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) ly).
          {
            unfold reachable_locations_from_initial_env.
            exists y, ly.
            split; auto.
            apply rch_heap.
            apply runtime_getObj_dom in Hobjy; auto.
          }
          specialize (Hconfined y ly Ty Hget_y Hval_y HlyInP).
          have Hsafe_ty : is_safe_mode (sqtype Ty) := Hconfined.
          have Hsafe_tx : is_safe_mode (sqtype Tx).
          {
            exact (subtype_safe_implies_safe_adapted CT (mret (msignature mdef0)) Ty Tx
              Hret_sub Hsafe_ret Hsafe_ty).
          }
          exact Hsafe_tx.
        -- (* CASE: z <> x (Old Variables) *)
          assert (Hupdate_env : (set_vars rΓ (update x retval (vars rΓ))) = update_r_env_value rΓ x retval).
          {
            destruct rΓ.
            reflexivity.
          }
          rewrite <- Hvars in Hlookup_r.
          rewrite Hupdate_env in Hlookup_r.
          rewrite runtime_getVal_update_diff in Hlookup_r; auto.
          eapply Hconfined; eauto.
      }
      exact Henv_respects''.
      specialize (IHHeval Heval SafeRO H23 sΓmethodend sΓmethodinit);
      specialize (IHHeval HenvInvariant Hwf_method_frame);
      specialize (IHHeval Hmethodbody_typing);
      assert (Henv_respects'': env_respects_protected_set (reachable_locations_from_initial_env CT h rΓ) sΓ rΓ''' ).
      {
        rewrite HeqrΓ'''.
        unfold env_respects_protected_set.
        intros z l_z T_z Hlookup_s Hlookup_r Hin_P.
        destruct (Nat.eq_dec x z); subst.
        -- (* CASE: z = x (New Variable) *)
          assert (T_z = Tx). 
          {
            rewrite Hget_x in Hlookup_s. 
            injection Hlookup_s as H_eq_T. subst T_z.
            reflexivity.
          }
          subst T_z.
          unfold env_respects_protected_set in IHHeval.
          have HGetMethodReturnType: static_getType sΓmethodend (mreturn (Syntax.mbody mdef)) = Some mbodyreturntype.
          {
            unfold static_getType; auto.
          }
          rewrite <- Hvars in Hlookup_r.
          have Hdom_z : z < dom (vars rΓ). 
          { 
            apply runtime_getVal_dom in Hlookup_r.
            rewrite update_length in Hlookup_r.
            exact Hlookup_r.
          }
          have Hlookup_r_copy := Hlookup_r.
          unfold runtime_getVal in Hlookup_r.
          rewrite update_same in Hlookup_r.
          lia.
          inversion Hlookup_r; subst.

          have Hin_P_inner: Ensembles.In Loc (reachable_locations_from_initial_env CT h
          {| vars := Iot ly :: vals |}) l_z.
          {
            eapply reachable_return_implies_reachable_args; eauto.
            apply reachable_locations_from_initial_env_dom in Hin_P; auto. (* This is not provable, need a lot changes *)
          }
          specialize (IHHeval (mreturn (Syntax.mbody mdef)) l_z mbodyreturntype HGetMethodReturnType Hretval Hin_P_inner).
          have Hsafe_ret : is_safe_mode (sqtype (mret (msignature mdef0))).
          {
            rewrite Hmsigeq in HmethodReturnSubtype.
            apply subtype_safe_implies_safe in HmethodReturnSubtype; auto.
          }
          assert (HlyInP: Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) ly).
          {
            unfold reachable_locations_from_initial_env.
            exists y, ly.
            split; auto.
            apply rch_heap.
            apply runtime_getObj_dom in Hobjy; auto.
          }
          specialize (Hconfined y ly Ty Hget_y Hval_y HlyInP).
          have Hsafe_ty : is_safe_mode (sqtype Ty) := Hconfined.
          have Hsafe_tx : is_safe_mode (sqtype Tx).
          {
            exact (subtype_safe_implies_safe_adapted CT (mret (msignature mdef0)) Ty Tx
              Hret_sub Hsafe_ret Hsafe_ty).
          }
          exact Hsafe_tx.
        -- (* CASE: z <> x (Old Variables) *)
          assert (Hupdate_env : (set_vars rΓ (update x retval (vars rΓ))) = update_r_env_value rΓ x retval).
          {
            destruct rΓ.
            reflexivity.
          }
          rewrite <- Hvars in Hlookup_r.
          rewrite Hupdate_env in Hlookup_r.
          rewrite runtime_getVal_update_diff in Hlookup_r; auto.
          eapply Hconfined; eauto.
      }
      exact Henv_respects''.
    specialize (IHHeval Heval SafeRO H23 sΓmethodend sΓmethodinit).
    specialize (IHHeval HenvInvariant Hwf_method_frame).
    specialize (IHHeval Hmethodbody_typing).
    assert (Henv_respects'': env_respects_protected_set (reachable_locations_from_initial_env CT h rΓ) sΓ rΓ''' ).
    {
      rewrite HeqrΓ'''.
      unfold env_respects_protected_set.
      intros z l_z T_z Hlookup_s Hlookup_r Hin_P.
      destruct (Nat.eq_dec x z); subst.
      -- (* CASE: z = x (New Variable) *)
        assert (T_z = Tx). 
        {
          rewrite Hget_x in Hlookup_s. 
          injection Hlookup_s as H_eq_T. subst T_z.
          reflexivity.
        }
        subst T_z.
        unfold env_respects_protected_set in IHHeval.
        have HGetMethodReturnType: static_getType sΓmethodend (mreturn (Syntax.mbody mdef)) = Some mbodyreturntype.
        {
          unfold static_getType; auto.
        }
        rewrite <- Hvars in Hlookup_r.
        have Hdom_z : z < dom (vars rΓ). 
        { 
          apply runtime_getVal_dom in Hlookup_r.
          rewrite update_length in Hlookup_r.
          exact Hlookup_r.
        }
        have Hlookup_r_copy := Hlookup_r.
        unfold runtime_getVal in Hlookup_r.
        rewrite update_same in Hlookup_r.
        lia.
        inversion Hlookup_r; subst.

        have Hin_P_inner: Ensembles.In Loc (reachable_locations_from_initial_env CT h
        {| vars := Iot ly :: vals |}) l_z.
        {
          eapply reachable_return_implies_reachable_args; eauto.
          apply reachable_locations_from_initial_env_dom in Hin_P; auto. (* This is not provable, need a lot changes *)
        }
        specialize (IHHeval (mreturn (Syntax.mbody mdef)) l_z mbodyreturntype HGetMethodReturnType Hretval Hin_P_inner).
          have Hsafe_ret : is_safe_mode (sqtype (mret (msignature mdef0))).
          {
            rewrite Hmsigeq in HmethodReturnSubtype.
            apply subtype_safe_implies_safe in HmethodReturnSubtype; auto.
          }
        assert (HlyInP: Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) ly).
        {
          unfold reachable_locations_from_initial_env.
          exists y, ly.
          split; auto.
          apply rch_heap.
          apply runtime_getObj_dom in Hobjy; auto.
        }
        specialize (Hconfined y ly Ty Hget_y Hval_y HlyInP).
        have Hsafe_ty : is_safe_mode (sqtype Ty) := Hconfined.
        have Hsafe_tx : is_safe_mode (sqtype Tx).
        {
          exact (subtype_safe_implies_safe_adapted CT (mret (msignature mdef0)) Ty Tx
            Hret_sub Hsafe_ret Hsafe_ty).
        }
        exact Hsafe_tx.
      -- (* CASE: z <> x (Old Variables) *)
        assert (Hupdate_env : (set_vars rΓ (update x retval (vars rΓ))) = update_r_env_value rΓ x retval).
        {
          destruct rΓ.
          reflexivity.
        }
        rewrite <- Hvars in Hlookup_r.
        rewrite Hupdate_env in Hlookup_r.
        rewrite runtime_getVal_update_diff in Hlookup_r; auto.
        eapply Hconfined; eauto.
    }
    exact Henv_respects''.
    specialize (IHHeval Heval ConcreteImm H26 sΓmethodend sΓmethodinit).
    specialize (IHHeval HenvInvariant Hwf_method_frame).
    specialize (IHHeval Hmethodbody_typing).
    assert (Henv_respects'': env_respects_protected_set (reachable_locations_from_initial_env CT h rΓ) sΓ rΓ''' ).
    {
      rewrite HeqrΓ'''.
      unfold env_respects_protected_set.
      intros z l_z T_z Hlookup_s Hlookup_r Hin_P.
      destruct (Nat.eq_dec x z); subst.
      -- (* CASE: z = x (New Variable) *)
        assert (T_z = Tx). 
        {
          rewrite Hget_x in Hlookup_s. 
          injection Hlookup_s as H_eq_T. subst T_z.
          reflexivity.
        }
        subst T_z.
        unfold env_respects_protected_set in IHHeval.
        have HGetMethodReturnType: static_getType sΓmethodend (mreturn (Syntax.mbody mdef)) = Some mbodyreturntype.
        {
          unfold static_getType; auto.
        }
        rewrite <- Hvars in Hlookup_r.
        have Hdom_z : z < dom (vars rΓ). 
        { 
          apply runtime_getVal_dom in Hlookup_r.
          rewrite update_length in Hlookup_r.
          exact Hlookup_r.
        }
        have Hlookup_r_copy := Hlookup_r.
        unfold runtime_getVal in Hlookup_r.
        rewrite update_same in Hlookup_r.
        lia.
        inversion Hlookup_r; subst.

        have Hin_P_inner: Ensembles.In Loc (reachable_locations_from_initial_env CT h
        {| vars := Iot ly :: vals |}) l_z.
        {
          eapply reachable_return_implies_reachable_args; eauto.
          apply reachable_locations_from_initial_env_dom in Hin_P; auto. (* This is not provable, need a lot changes *)
        }
        specialize (IHHeval (mreturn (Syntax.mbody mdef)) l_z mbodyreturntype HGetMethodReturnType Hretval Hin_P_inner).
          have Hsafe_ret : is_safe_mode (sqtype (mret (msignature mdef0))).
          {
            rewrite Hmsigeq in HmethodReturnSubtype.
            apply subtype_safe_implies_safe in HmethodReturnSubtype; auto.
          }
        assert (HlyInP: Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) ly).
        {
          unfold reachable_locations_from_initial_env.
          exists y, ly.
          split; auto.
          apply rch_heap.
          apply runtime_getObj_dom in Hobjy; auto.
        }
        specialize (Hconfined y ly Ty Hget_y Hval_y HlyInP).
        have Hsafe_ty : is_safe_mode (sqtype Ty) := Hconfined.
        have Hsafe_tx : is_safe_mode (sqtype Tx).
        {
          exact (subtype_safe_implies_safe_adapted CT (mret (msignature mdef0)) Ty Tx
            Hret_sub Hsafe_ret Hsafe_ty).
        }
        exact Hsafe_tx.
      -- (* CASE: z <> x (Old Variables) *)
        assert (Hupdate_env : (set_vars rΓ (update x retval (vars rΓ))) = update_r_env_value rΓ x retval).
        {
          destruct rΓ.
          reflexivity.
        }
        rewrite <- Hvars in Hlookup_r.
        rewrite Hupdate_env in Hlookup_r.
        rewrite runtime_getVal_update_diff in Hlookup_r; auto.
        eapply Hconfined; eauto.
    }
    exact Henv_respects''.
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
    remember (set_vars rΓ (update x retval (vars rΓ))) as rΓ'''.
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
        destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
        injection Hval_y as H1_eq.
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

        (* Inner Static Environment's length is more than 0 *)
        rewrite HeqsΓmethodinit.
        simpl.
        lia.

        (* Inner static env's elements are wellformed typeuse *)
        rewrite HeqsΓmethodinit.
        constructor.

        (* Receiver type is well-formed *)
        eapply method_sig_wf_receiver_by_find; eauto.
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
          apply static_getType_dom in Hget_y.
          exact Hget_y.
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
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty Hget_y).
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
        assert (Hmsigeq : msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
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
          apply static_getType_dom in Hget_y.
          exact Hget_y.
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
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty Hget_y).
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
        destruct Hrcv_sub as [Hrcv_sub | Hrcv_sub].
        apply qualified_type_subtype_base_subtype in Hrcv_sub.
        (* rewrite (vpa_mutability_tt_sctype Tthis Ty) in Hmethod_case. *)
        rewrite (vpa_mutability_tt_sctype_safe_ro Ty (mreceiver (msignature mdef0))) in Hrcv_sub.
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

            assert (Hqcontext0 : r_muttype h ly = Some rq_obj).
            {
              unfold r_muttype.
              rewrite Hobjy.
              simpl.
              reflexivity.
            }

            assert (rq_obj = qinner).
            {
              rewrite Hqcontext0 in Hqcontext.
              inversion Hqcontext; subst qinner.
              reflexivity.
            }
            subst rq_obj.

            unfold qualifier_typable_context.
            unfold qualifier_typable_context in HyQualifierTypablility.
            unfold qualifier_typable_context in Houtter_qualifier_typable.
            unfold vpa_mutability_rs.
            unfold vpa_mutability_rs in HyQualifierTypablility.
            unfold vpa_mutability_rs in Houtter_qualifier_typable.
            unfold vpa_mutability_tt_safe_ro in Hrcv_sub.
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

            assert (Hqcontext0 : r_muttype h ly = Some rq_obj).
            {
              unfold r_muttype.
              rewrite Hobjy.
              simpl.
              reflexivity.
            }

            assert (rq_obj = qinner).
            {
              rewrite Hqcontext0 in Hqcontext.
              inversion Hqcontext; subst qinner.
              reflexivity.
            }
            subst rq_obj.

            unfold qualifier_typable_context.
            unfold qualifier_typable_context in HyQualifierTypablility.
            unfold qualifier_typable_context in Houtter_qualifier_typable.
            unfold vpa_mutability_rs.
            unfold vpa_mutability_rs in HyQualifierTypablility.
            unfold vpa_mutability_rs in Houtter_qualifier_typable.
            rewrite <- Hmsigeq in HReceiverDeclearedQualifier.

            destruct qinner eqn:HInnerReceiverMutability;
            destruct (sqtype (mreceiver (msignature mdef))) eqn:HMethodReceiverDeclaredType;
            try trivial.
            all: destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            destruct (sqtype Ty) eqn:HTyStaticMutability;
            try trivial.
            all: destruct (sqtype Tthis) eqn:HTthisStaticMutability;
            try easy.
          }
        }

  (* -------------------------------------------------- *)
  (* Other index - > 1 *)
        unfold runtime_getVal.
        simpl.
        destruct (nth_error vals i') as [v|] eqn:Hval_i.
          - (* Parameter i' exists *)
            destruct v as [|loc|n]; [trivial| | trivial].
            (* Use Hmethod_case to get the subtyping relationship *)
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
                  | Int _ => True
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
            rewrite (vpa_mutability_tt_sctype_safe_ro Ty sqt) in Harg_sub.
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
    (* specialize (IHHeval Heval sΓmethodend sΓmethodinit). *)
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
        - exact Hval_y.  (* runtime_getVal rΓ y = Some (Iot ly) *)
        - apply rch_heap.
          apply reachable_locations_from_initial_env_dom in Hin_P; auto.
      }
      have Hty_safe : is_safe_mode (sqtype Ty).
      {
        unfold env_respects_protected_set in Hconfined.
        specialize (Hconfined y ly Ty Hget_y Hval_y Hin_P_orig).
        exact Hconfined.
      }
      unfold is_safe_mode in Hty_safe.
      unfold vpa_mutability_tt_safe_ro.
      assert (Hy_dom : y < dom sΓ).
      {
        apply static_getType_dom in Hget_y.
        exact Hget_y.
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
      specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty Hget_y).
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
      
      assert (Hmsigeq: msignature mdef = msignature mdef0).
      {
        eapply method_signature_consistent_subtype; eauto.
      }
      destruct Hrcv_sub as [Hrcv_sub | Hrcv_sub].
      clear - Hmsigeq Hty_safe Hrcv_sub.
      rewrite Hmsigeq.
      unfold vpa_mutability_tt_safe_ro in Hrcv_sub.
      apply qualified_type_subtype_q_subtype in Hrcv_sub.
      destruct Hty_safe as [HRd | [HLost | [HRDM | HImm]]].
      + (* Case: sqtype Ty = Rd *)
        rewrite HRd in Hrcv_sub.
        destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
        simpl in Hrcv_sub.
        all: try solve_q_subtype_wrong.
        all: try solve solve_safe_mode.
        try rewrite HMethodReceiverDeclaredType in Hrcv_sub; try solve_q_subtype_wrong.
      + (* Case: sqtype Ty = Lost *)
        rewrite HLost in Hrcv_sub.
        destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
        simpl in Hrcv_sub.
        all: try solve_q_subtype_wrong.
        all: try solve solve_safe_mode.
        try rewrite HMethodReceiverDeclaredType in Hrcv_sub; try solve_q_subtype_wrong.
      + (* Case: sqtype Ty = RDM *)
        rewrite HRDM in Hrcv_sub.
        destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
        simpl in Hrcv_sub.
        all: try solve_q_subtype_wrong.
        all: try solve solve_safe_mode.
        try rewrite HMethodReceiverDeclaredType in Hrcv_sub; try solve_q_subtype_wrong.
      + (* Case: sqtype Ty = Imm *)
        rewrite HImm in Hrcv_sub.
        destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
        simpl in Hrcv_sub.
        all: try solve_q_subtype_wrong.
        all: try solve solve_safe_mode.
        try rewrite HMethodReceiverDeclaredType in Hrcv_sub; try solve_q_subtype_wrong.
      +
        destruct Hrcv_sub as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
        rewrite <- Hmsigeq in HReceiverDeclearedQualifier.
        right; right; auto.
      -
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in Hget_y.
          exact Hget_y.
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
        specialize (Htypable iot qoutter Hget_iot Hqoutter y Hy_dom Ty Hget_y).
        unfold wf_r_typable in Htypable.
        have Hrc_base := Hbase.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy.
        2:{
          unfold r_basetype in Hrc_base.
          rewrite Hobjy in Hrc_base.
          discriminate.
        }
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        unfold r_type in Htypable.
        rewrite Hval_y in Htypable.
        rewrite Hobjy in Htypable.
        simpl in Htypable.
        destruct Htypable as [Hsubtype Hqualifier].
        simpl in Hobjy.
        unfold r_basetype in Hrc_base.
        rewrite Hobjy in Hrc_base.
        simpl in Hrc_base.
        injection Hrc_base as Hrc_obj_eq.
        subst rc_obj.

        assert (Hsigeq: msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype with (C := cy) (D := sctype Ty) (m := m).
          - exact Hclasstable.
          - exact Hsubtype.
          - exact mdeflookup.
          - exact Hfind_m.
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
          apply Forall2_length in Harg_sub.
          rewrite <- Hsigeq in Harg_sub.
          assert (H_bound_params : z' < dom (mparams (msignature mdef))).
          {
            apply nth_error_Some. (* Converts "index < len" to "lookup <> None" *)
            rewrite Hnth_param_type.   (* lookup is Some Tz *)
            discriminate.         (* Some <> None *)
          }

          (* 2. Convert to bound for argtypes using the equality *)
          rewrite <- Harg_sub in H_bound_params. (* Replace length of params with length of argtypes *)

          (* 3. Solve the goal *)
          exact H_bound_params.
        }

        have Hnth_arg: exists T_arg, nth_error argtypes z' = Some T_arg.
        {
          apply nth_error_Some_exists.
          exact Hi'_bound.
        }

        destruct Hnth_arg as [T_arg Hnth_arg].
        eapply Forall2_nth_error with (i := z') (a := T_arg) (b := Tz) in Harg_sub; [|auto|rewrite <- Hsigeq; exact Hnth_param_type].
        (* apply qualified_type_subtype_q_subtype in Hreceiver_sub. *)
        unfold env_respects_protected_set in Hconfined.
        apply adapated_subtype_safe_implies_safe in Harg_sub; auto.

        have HargtypeFromsEnv :
          exists z_outter,
            static_getType sΓ z_outter = Some T_arg /\
            nth_error zs z' = Some z_outter.
        {
          destruct (static_getType_list_nth_zs sΓ zs argtypes z' T_arg Hget_args Hnth_arg)
            as [j [Hzs_j Hst_j]].
          exists j.
          split.
          - unfold static_getType. exact Hst_j.
          - exact Hzs_j.
        }

        destruct HargtypeFromsEnv as [z_outter [HgetZ_type Hzs_z_outter]].

        have HgetZ_val : runtime_getVal rΓ z_outter = Some (Iot l_z).
        {
          destruct (runtime_lookup_list_nth_zs rΓ zs vals z' (Iot l_z) Hargs Hnth_param_val)
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
    assert (Hy_dom : y < dom sΓ).
    {
      apply static_getType_dom in Hget_y.
      exact Hget_y.
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
    specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty Hget_y).
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
    
    assert (Hmsigeq: msignature mdef = msignature mdef0).
    {
      eapply method_signature_consistent_subtype; eauto.
    }

    rewrite <- getmbody in Hmethodbody_typing.
    rewrite Hmsigeq in Hmethodbody_typing.
	    destruct (mtype (msignature mdef0)) eqn:Hcallee_mtype.
	    ++ exfalso; exact (Hmt_not_abs eq_refl).
	    ++ have H23 : SafeRO <> AbstractImm.
	      discriminate.
	      destruct mt eqn:Hcaller_mtype.
	      +++ exfalso; exact (Hmtype eq_refl).
	      +++ specialize (IHHeval Heval SafeRO H23 sΓmethodend sΓmethodinit).
    specialize (IHHeval HenvInvariant Hwf_method_frame).
    specialize (IHHeval Hmethodbody_typing).
    assert (Henv_respects'': env_respects_protected_set (reachable_locations_from_initial_env CT h rΓ) sΓ rΓ''' ).
    {
      rewrite HeqrΓ'''.
      intros z l_z T_z Hlookup_s Hlookup_r Hin_P.
      destruct (Nat.eq_dec x z) eqn: Heqxz.
        --- (* CASE: z = x (New Variable) *)
        subst z.
        assert (T_z = Tx). 
        {
          rewrite Hget_x in Hlookup_s. 
          injection Hlookup_s as H_eq_T. subst T_z.
          reflexivity.
        }
        subst T_z.
        unfold env_respects_protected_set in IHHeval.
        have HGetMethodReturnType: static_getType sΓmethodend (mreturn (Syntax.mbody mdef)) = Some mbodyreturntype.
        {
          unfold static_getType; auto.
        }
        rewrite getmbody in Hretval.
        have Hlookup_r_copy := Hlookup_r.
        rewrite <- Hvars in Hlookup_r.
        have Hdom_x : x < dom (vars rΓ). 
        { 
          apply runtime_getVal_dom in Hlookup_r.
          rewrite update_length in Hlookup_r.
          exact Hlookup_r.
        }
        rewrite <- HeqrΓ''' in Hlookup_r_copy.
        unfold runtime_getVal in Hlookup_r.
        rewrite update_same in Hlookup_r. lia.   (* or by exact Hdom_x *)
        inversion Hlookup_r; subst.
        have Hin_P_inner: Ensembles.In Loc (reachable_locations_from_initial_env CT h
        {| vars := Iot ly :: vals |}) l_z.
        {
          have Hdom_l_z : l_z < dom h.
          {
            apply reachable_locations_from_initial_env_dom in Hin_P; auto.
          }
          eapply reachable_return_implies_reachable_args; eauto.
        }
        specialize (IHHeval (mreturn (Syntax.mbody mdef)) l_z mbodyreturntype HGetMethodReturnType Hretval Hin_P_inner).
        have Hsafe_ret : is_safe_mode (sqtype (mret (msignature mdef0))).
        {
          rewrite Hmsigeq in HmethodReturnSubtype.
          apply subtype_safe_implies_safe in HmethodReturnSubtype; auto.
        }
        assert (HlyInP: Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) ly).
        {
          unfold reachable_locations_from_initial_env.
          exists y, ly.
          split; auto.
          apply rch_heap.
          apply runtime_getObj_dom in Hobjy; auto.
        }
        specialize (Hconfined y ly Ty Hget_y Hval_y HlyInP).
        have Hsafe_ty : is_safe_mode (sqtype Ty) := Hconfined.
        have Hsafe_tx : is_safe_mode (sqtype Tx).
        {
          exact (subtype_safe_implies_safe_adapted CT (mret (msignature mdef0)) Ty Tx
            Hret_sub Hsafe_ret Hsafe_ty).
        }
        exact Hsafe_tx.
        --- (* CASE: z <> x (Old Variables) *)
        rewrite <- Hvars in Hlookup_r.
        assert (Hupdate_env : (set_vars rΓ (update x retval (vars rΓ))) = update_r_env_value rΓ x retval).
        {
          destruct rΓ.
          reflexivity.
        }
        rewrite Hupdate_env in Hlookup_r.
        rewrite runtime_getVal_update_diff in Hlookup_r; auto.
        eapply Hconfined; eauto.
    }
	    exact Henv_respects''.
	      +++ inversion Hmt_sub.
	    ++ have H26 : ConcreteImm <> AbstractImm.
	      discriminate.
	      destruct mt eqn:Hcaller_mtype.
		      +++ exfalso; exact (Hmtype eq_refl).
		      +++ specialize (IHHeval Heval ConcreteImm H26 sΓmethodend sΓmethodinit).
    specialize (IHHeval HenvInvariant Hwf_method_frame).
    specialize (IHHeval Hmethodbody_typing).
    assert (Henv_respects'': env_respects_protected_set (reachable_locations_from_initial_env CT h rΓ) sΓ rΓ''' ).
    {
      rewrite HeqrΓ'''.
      intros z l_z T_z Hlookup_s Hlookup_r Hin_P.
      destruct (Nat.eq_dec x z) eqn: Heqxz.
        --- (* CASE: z = x (New Variable) *)
        subst z.
        assert (T_z = Tx). 
        {
          rewrite Hget_x in Hlookup_s. 
          injection Hlookup_s as H_eq_T. subst T_z.
          reflexivity.
        }
        subst T_z.
        unfold env_respects_protected_set in IHHeval.
        have HGetMethodReturnType: static_getType sΓmethodend (mreturn (Syntax.mbody mdef)) = Some mbodyreturntype.
        {
          unfold static_getType; auto.
        }
        rewrite getmbody in Hretval.
        have Hlookup_r_copy := Hlookup_r.
        rewrite <- Hvars in Hlookup_r.
        have Hdom_x : x < dom (vars rΓ). 
        { 
          apply runtime_getVal_dom in Hlookup_r.
          rewrite update_length in Hlookup_r.
          exact Hlookup_r.
        }
        rewrite <- HeqrΓ''' in Hlookup_r_copy.
        unfold runtime_getVal in Hlookup_r.
        rewrite update_same in Hlookup_r. lia.   (* or by exact Hdom_x *)
        inversion Hlookup_r; subst.
        have Hin_P_inner: Ensembles.In Loc (reachable_locations_from_initial_env CT h
        {| vars := Iot ly :: vals |}) l_z.
        {
          have Hdom_l_z : l_z < dom h.
          {
            apply reachable_locations_from_initial_env_dom in Hin_P; auto.
          }
          eapply reachable_return_implies_reachable_args; eauto.
        }
        specialize (IHHeval (mreturn (Syntax.mbody mdef)) l_z mbodyreturntype HGetMethodReturnType Hretval Hin_P_inner).
        have Hsafe_ret : is_safe_mode (sqtype (mret (msignature mdef0))).
        {
          rewrite Hmsigeq in HmethodReturnSubtype.
          apply subtype_safe_implies_safe in HmethodReturnSubtype; auto.
        }
        assert (HlyInP: Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) ly).
        {
          unfold reachable_locations_from_initial_env.
          exists y, ly.
          split; auto.
          apply rch_heap.
          apply runtime_getObj_dom in Hobjy; auto.
        }
        specialize (Hconfined y ly Ty Hget_y Hval_y HlyInP).
        have Hsafe_ty : is_safe_mode (sqtype Ty) := Hconfined.
        have Hsafe_tx : is_safe_mode (sqtype Tx).
        {
          exact (subtype_safe_implies_safe_adapted CT (mret (msignature mdef0)) Ty Tx
            Hret_sub Hsafe_ret Hsafe_ty).
        }
        exact Hsafe_tx.
        --- (* CASE: z <> x (Old Variables) *)
        rewrite <- Hvars in Hlookup_r.
        assert (Hupdate_env : (set_vars rΓ (update x retval (vars rΓ))) = update_r_env_value rΓ x retval).
        {
          destruct rΓ.
          reflexivity.
        }
        rewrite Hupdate_env in Hlookup_r.
        rewrite runtime_getVal_update_diff in Hlookup_r; auto.
        eapply Hconfined; eauto.
    }
	    exact Henv_respects''.
		      +++ specialize (IHHeval Heval ConcreteImm H26 sΓmethodend sΓmethodinit).
    specialize (IHHeval HenvInvariant Hwf_method_frame).
    specialize (IHHeval Hmethodbody_typing).
    assert (Henv_respects'': env_respects_protected_set (reachable_locations_from_initial_env CT h rΓ) sΓ rΓ''' ).
    {
      rewrite HeqrΓ'''.
      intros z l_z T_z Hlookup_s Hlookup_r Hin_P.
      destruct (Nat.eq_dec x z) eqn: Heqxz.
        --- (* CASE: z = x (New Variable) *)
        subst z.
        assert (T_z = Tx). 
        {
          rewrite Hget_x in Hlookup_s. 
          injection Hlookup_s as H_eq_T. subst T_z.
          reflexivity.
        }
        subst T_z.
        unfold env_respects_protected_set in IHHeval.
        have HGetMethodReturnType: static_getType sΓmethodend (mreturn (Syntax.mbody mdef)) = Some mbodyreturntype.
        {
          unfold static_getType; auto.
        }
        rewrite getmbody in Hretval.
        have Hlookup_r_copy := Hlookup_r.
        rewrite <- Hvars in Hlookup_r.
        have Hdom_x : x < dom (vars rΓ). 
        { 
          apply runtime_getVal_dom in Hlookup_r.
          rewrite update_length in Hlookup_r.
          exact Hlookup_r.
        }
        rewrite <- HeqrΓ''' in Hlookup_r_copy.
        unfold runtime_getVal in Hlookup_r.
        rewrite update_same in Hlookup_r. lia.   (* or by exact Hdom_x *)
        inversion Hlookup_r; subst.
        have Hin_P_inner: Ensembles.In Loc (reachable_locations_from_initial_env CT h
        {| vars := Iot ly :: vals |}) l_z.
        {
          have Hdom_l_z : l_z < dom h.
          {
            apply reachable_locations_from_initial_env_dom in Hin_P; auto.
          }
          eapply reachable_return_implies_reachable_args; eauto.
        }
        specialize (IHHeval (mreturn (Syntax.mbody mdef)) l_z mbodyreturntype HGetMethodReturnType Hretval Hin_P_inner).
        have Hsafe_ret : is_safe_mode (sqtype (mret (msignature mdef0))).
        {
          rewrite Hmsigeq in HmethodReturnSubtype.
          apply subtype_safe_implies_safe in HmethodReturnSubtype; auto.
        }
        assert (HlyInP: Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) ly).
        {
          unfold reachable_locations_from_initial_env.
          exists y, ly.
          split; auto.
          apply rch_heap.
          apply runtime_getObj_dom in Hobjy; auto.
        }
        specialize (Hconfined y ly Ty Hget_y Hval_y HlyInP).
        have Hsafe_ty : is_safe_mode (sqtype Ty) := Hconfined.
        have Hsafe_tx : is_safe_mode (sqtype Tx).
        {
          exact (subtype_safe_implies_safe_adapted CT (mret (msignature mdef0)) Ty Tx
            Hret_sub Hsafe_ret Hsafe_ty).
        }
        exact Hsafe_tx.
        --- (* CASE: z <> x (Old Variables) *)
        rewrite <- Hvars in Hlookup_r.
        assert (Hupdate_env : (set_vars rΓ (update x retval (vars rΓ))) = update_r_env_value rΓ x retval).
        {
          destruct rΓ.
          reflexivity.
        }
        rewrite Hupdate_env in Hlookup_r.
        rewrite runtime_getVal_update_diff in Hlookup_r; auto.
        eapply Hconfined; eauto.
    }
    exact Henv_respects''.
Qed.
