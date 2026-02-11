Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation.
Require Import Properties DeepImmutability Reachability.
Require Import ReadonlyReachability.
From Stdlib Require Import List.
From Stdlib Require String.
Import ListNotations.
From RecordUpdate Require Import RecordUpdate.

Lemma stmt_preserves_confinement :
  forall CT sΓ rΓ h stmt sΓ' rΓ' h'
    (Hconfined : env_respects_protected_set (reachable_locations_from_initial_env CT h rΓ) sΓ rΓ)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ stmt sΓ')
    (Heval : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) true CT rΓ h stmt OK true (reachable_locations_from_initial_env CT h rΓ) rΓ' h'),
  env_respects_protected_set (reachable_locations_from_initial_env CT h rΓ) sΓ' rΓ'.
Proof.
  intros.
  remember OK as ok.
  remember true as TouchNonMutOnly.
  generalize dependent sΓ.
  generalize dependent sΓ'.
  have Heval_copy := Heval.
  induction Heval; intros; subst; try discriminate.
  7:
  {
    inversion Htyping; subst.
    rename sΓ' into sΓ''.
    rename sΓ'0 into sΓ'.

    (* Get wellformedness for intermediate state *)
    pose proof (preservation_pico _ _ _ _ _ _ _ _ _ _ Hwf H4 Heval1) as Hwf'.

    have HtrueVal': TouchNonMutOnly' = true.
    eapply eval_stmt_did_not_touch_abs_start_with_true; eauto.

    rewrite HtrueVal' in Heval1.

    have HtrueVal: TouchNonMutOnly = true.
    eapply eval_stmt_did_not_touch_abs_start_with_true with (stmt:=s1) (sΓ:=sΓ) (sΓ':=sΓ'); eauto.

    subst TouchNonMutOnly'.
    subst TouchNonMutOnly.
    (* Apply IH1 *)
    pose proof (IHHeval1 eq_refl eq_refl Heval1 sΓ' sΓ Hconfined Hwf H4) as Henv1.

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
        assert (y = dom sΓ).
        {
          apply static_getType_dom in Hlookup_s.
          apply static_getType_not_dom in H4.
          rewrite length_app in Hlookup_s; simpl in Hlookup_s. (* dom (sΓ++[T]) = S (dom sΓ) *)
          lia.
        }
        rewrite H0 in Hlookup_s.
        destruct Hwf as [_ [_ [_ [_ [Hlen _]]]]]. (* gives dom sΓ = dom (vars rΓ) *)
        rewrite H0 in Hlookup_r.                  (* y = dom sΓ *)
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
            inversion Htyping; subst.
            apply static_getType_not_dom in H4.
            apply static_getType_dom in H9.
            rewrite length_app in H9; simpl in H9.
            lia.
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
    (* split.
    + reflexivity. *)
    + (* Invariant preserved *)
      inversion Htyping; subst.
      have Hconfined_copy := Hconfined.
      unfold env_respects_protected_set.
      unfold env_respects_protected_set in Hconfined.
      (* destruct Hconfined as [Henv_respects Hheap_respects]. *)
      rename sΓ' into sΓ.
      (* split. *)
      *
        unfold env_respects_protected_set.
        intros y l_y Ty Hlookup_s Hlookup_r Hin_P.
        unfold runtime_getVal in Hlookup_r.
        simpl in Hlookup_r.
        destruct (Nat.eq_dec y x) as [Heq_y | Hneq_y].
        -- (* y = x *)
        subst y.
        rewrite H9 in Hlookup_s.
        inversion Hlookup_s; subst Ty.
        apply runtime_getVal_dom in H.
        rewrite update_same in Hlookup_r; auto.
        injection Hlookup_r as Heq_v2.
        subst v2.
        have HtrueVal: TouchNonMutOnly = true.
        eapply eval_expr_did_not_touch_abs_start_with_true; eauto.
        rewrite HtrueVal in H0.
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
    - (* Invariant preserved *)
      inversion Htyping; subst sΓ'; subst.
      unfold env_respects_protected_set in *.
      intros y l_y Ty Hlookup_s Hlookup_r Hin_P.
      assert (rΓ <| vars := update x (Iot dom h) (vars rΓ) |> = update_r_env_value rΓ x (Iot (dom h))).
      {
        destruct rΓ.
        reflexivity.
      }
      rewrite H2 in Hlookup_r.
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
    have Hwfcopy := Hwf.
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hclasstable [Hheap [Hrenv [Hsenv [Henv_len Htypable]]]]].
    unfold env_respects_protected_set in *.
    specialize (IHHeval (eq_refl)).
    destruct H1 as [mdeflookup getmbody].
    remember (msignature mdef) as msig.
    inversion mdeflookup; revert getmbody; subst; intro getmbody.
    +
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

        apply static_getType_list_preserves_length in H11.
        apply runtime_lookup_list_preserves_length in H4.
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        simpl.
        f_equal.
        apply Forall2_length in H20.
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
        rewrite <- H20.
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
        apply qualified_type_subtype_base_subtype in H19.
        (* rewrite (vpa_mutabilty_tt_sctype Tthis Ty) in H23. *)
        rewrite (vpa_mutabilty_tt_sctype Ty (mreceiver (msignature mdef0))) in H19.
        eapply base_trans; eauto.

        (* Qualifier typbility *)
        1: 
        {
          apply qualified_type_subtype_q_subtype in H19.
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
          unfold vpa_mutabilty_tt in H19.
          rewrite <- Hmsigeq in H19.

          destruct qinner eqn:HInnerReceiverMutability;
          destruct (sqtype (mreceiver (msignature mdef))) eqn:HMethodReceiverDeclaredType;
          try trivial.
          all: destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
          destruct (sqtype Ty) eqn:HTyStaticMutability;
          try trivial.
          all: destruct (sqtype Tthis) eqn:HTthisStaticMutability;
          try rewrite HTyStaticMutability in H19;
          simpl in H19;
          try rewrite HMethodReceiverDeclaredType in H19;
          try inversion H19; try trivial.
          all: try inversion H19; try easy.
        }
        (* clear_dups. amazing.... *)

  (* -------------------------------------------------- *)
  (* Other index - > 1 *)
        apply qualified_type_subtype_q_subtype in H18.
        unfold runtime_getVal.
        simpl.
        destruct (nth_error vals i') as [v|] eqn:Hval_i.
          - (* Parameter i' exists *)
            destruct v as [|loc]; [trivial|].
            (* Use H23 to get the subtyping relationship *)
            assert (Hi'_bound : i' < List.length argtypes).
            {
              apply Forall2_length in H20.
              simpl in Hi.
              simpl in Hnth.
              rewrite Hmsigeq in Hnth.
              rewrite H20.
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
            eapply Forall2_nth_error in H20; eauto.
            apply qualified_type_subtype_base_subtype in H20.
            rewrite (vpa_mutabilty_tt_sctype Ty sqt) in H20.
            eapply base_trans; eauto.

            (* Qualifier Typability *)
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in H20; eauto.
            apply qualified_type_subtype_q_subtype in H20.
            rewrite sq_vpa_tt_eq_qq in H20.
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
            clear - H20 Harg_qualifiertypability HyQualifierTypablility HOutterReceiverQualifierTypablility.

            destruct (rqtype (rt_type argobj)) eqn:Hargobjmutability; move Hargobjmutability at bottom;
            destruct (sqtype sqt) eqn:HParameterStaticDeclearedMutability; move HParameterStaticDeclearedMutability at bottom;
            destruct qinner eqn:HInnerReceiverMutability; move HInnerReceiverMutability at bottom;
            try solve_qualifier_typable_correct_concrete.

            all: destruct (sqtype Ty) eqn:HTyStaticMutability;
            destruct (sqtype argtype) eqn:HArgTypeStaticMutability;
            simpl in H20;
            try solve_q_subtype_wrong.

            all: 
            destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            try solve_qualifier_typable_wrong_concrete.

          - (* Parameter i' doesn't exist - contradiction *)
            exfalso.
            apply nth_error_None in Hval_i.
            apply runtime_lookup_list_preserves_length in H4.
            apply static_getType_list_preserves_length in H11.
            apply Forall2_length in H20.
            rewrite H4 in Hval_i.
            rewrite <- H11 in Hval_i.
            rewrite H20 in Hval_i.
            simpl in Hi.
            simpl in Hnth.
            rewrite <- Hmsigeq in Hval_i.
            lia.
    }
    have HtrueVal: TouchNonMutOnly = true.
    rewrite getmbody in Heval.
    eapply eval_stmt_did_not_touch_abs_start_with_true with (P:=(reachable_locations_from_initial_env CT h rΓmethodinit)) (rΓ':=rΓ'')(h':=h'); eauto.
    rewrite HtrueVal in Heval.
    specialize (IHHeval eq_refl Heval sΓmethodend sΓmethodinit).
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
      unfold vpa_mutabilty_tt.
      apply qualified_type_subtype_q_subtype in H19.
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
      clear - Hmsigeq Hty_safe H19.
      rewrite Hmsigeq.
      unfold vpa_mutabilty_tt in H19.
      destruct Hty_safe as [Hrd | [Hlost| [Himm| HRDM]]].
      + (* Case: sqtype Ty = Rd *)
        rewrite Hrd in H19.
        destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
        try rewrite HMethodReceiverDeclaredType in H19;
        simpl in H19.
        all: inversion H19; try easy.
        all: left; reflexivity.
      + (* Case: sqtype Ty = Lost *)
        rewrite Hlost in H19.
        destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
        try rewrite HMethodReceiverDeclaredType in H19;
        simpl in H19.
        all: inversion H19; try easy.
        all: left; reflexivity.
      + (* Case: sqtype Ty = Imm *)
        rewrite Himm in H19.
        destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
        try rewrite HMethodReceiverDeclaredType in H19;
        simpl in H19.
        all: inversion H19; try easy.
        right; right; left; reflexivity.
        right; right; right; reflexivity.
        left; reflexivity.
      + (* Case: sqtype Ty = RDM *)  
        rewrite HRDM in H19.
        destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
        try rewrite HMethodReceiverDeclaredType in H19;
        simpl in H19.
        all: inversion H19; try easy.
        right; right; right; reflexivity.
        left; reflexivity.
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
          apply Forall2_length in H20.
          rewrite <- Hsigeq in H20.
          assert (H_bound_params : z' < dom (mparams (msignature mdef))).
          {
            apply nth_error_Some. (* Converts "index < len" to "lookup <> None" *)
            rewrite Hnth_param_type.   (* lookup is Some Tz *)
            discriminate.         (* Some <> None *)
          }

          (* 2. Convert to bound for argtypes using the equality *)
          rewrite <- H20 in H_bound_params. (* Replace length of params with length of argtypes *)

          (* 3. Solve the goal *)
          exact H_bound_params.
        }

        have Hnth_arg: exists T_arg, nth_error argtypes z' = Some T_arg.
        {
          apply nth_error_Some_exists.
          exact Hi'_bound.
        }

        destruct Hnth_arg as [T_arg Hnth_arg].
        eapply Forall2_nth_error with (i := z') (a := T_arg) (b := Tz) in H20; [|auto|rewrite <- Hsigeq; exact Hnth_param_type].
        (* apply qualified_type_subtype_q_subtype in H20. *)
        unfold env_respects_protected_set in Hconfined.
        apply adapated_subtype_safe_implies_safe in H20; auto.

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
    specialize (IHHeval HenvInvariant Hwf_method_frame).
    rewrite <- getmbody in Hmethodbody_typing.
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
          rewrite H9 in Hlookup_s. 
          injection Hlookup_s as H_eq_T. subst T_z.
          reflexivity.
        }
        subst T_z.
        unfold env_respects_protected_set in IHHeval.
        have HGetMethodReturnType: static_getType sΓmethodend (mreturn (Syntax.mbody mdef)) = Some mbodyreturntype.
        {
          unfold static_getType; auto.
        }
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H10.
          exact H10.
        }
        (* eapply protected_loc_has_safe_type; eauto.  *)

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
        have Hdom_z : z < dom (vars rΓ). 
        { 
          apply runtime_getVal_dom in Hlookup_r.
          rewrite update_length in Hlookup_r.
          exact Hlookup_r.
        }
        have Hlookup_r_copy := Hlookup_r.
        unfold runtime_getVal in Hlookup_r.
        rewrite update_same in Hlookup_r. lia.   (* or by exact Hdom_x *)
        inversion Hlookup_r; subst.

        have Hin_P_inner: Ensembles.In Loc (reachable_locations_from_initial_env CT h
        {| vars := Iot ly :: vals |}) l_z.
        {
          eapply reachable_return_implies_reachable_args; eauto.
          apply reachable_locations_from_initial_env_dom in Hin_P; auto. (* This is not provable, need a lot changes *)
        }
        specialize (IHHeval (mreturn (Syntax.mbody mdef)) l_z mbodyreturntype HGetMethodReturnType H6 Hin_P_inner).
        rewrite <- Hsigeq in H18.
        apply subtype_safe_implies_safe in HmethodReturnSubtype; auto.
        assert (HlyInP: Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) ly).
        {
          unfold reachable_locations_from_initial_env.
          exists y, ly.
          split; auto.
          apply rch_heap.
          apply runtime_getObj_dom in Hobjy; auto.
        }
        specialize (Hconfined y ly Ty H10 H HlyInP).
        apply subtype_safe_implies_safe_adapted in H18; auto.
      -- (* CASE: z <> x (Old Variables) *)
      (* Just use the original invariant *)
      assert (rΓ <| vars := update x retval (vars rΓ) |> = update_r_env_value rΓ x retval).
      {
        destruct rΓ.
        reflexivity.
      }
      rewrite H2 in Hlookup_r.
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
        apply static_getType_list_preserves_length in H11.
        apply runtime_lookup_list_preserves_length in H4.
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        simpl.
        f_equal.
        apply Forall2_length in H20.
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
        rewrite <- H20.
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
        apply qualified_type_subtype_base_subtype in H19.
        (* rewrite (vpa_mutabilty_tt_sctype Tthis Ty) in H23. *)
        rewrite (vpa_mutabilty_tt_sctype Ty (mreceiver (msignature mdef0))) in H19.
        eapply base_trans; eauto.

        (* Qualifier typbility *)
        1: 
        {
          apply qualified_type_subtype_q_subtype in H19.
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
          unfold vpa_mutabilty_tt in H19.
          rewrite <- Hmsigeq in H19.

          destruct qinner eqn:HInnerReceiverMutability;
          destruct (sqtype (mreceiver (msignature mdef))) eqn:HMethodReceiverDeclaredType;
          try trivial.
          all: destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
          destruct (sqtype Ty) eqn:HTyStaticMutability;
          try trivial.
          all: destruct (sqtype Tthis) eqn:HTthisStaticMutability;
          try rewrite HTyStaticMutability in H19;
          simpl in H19;
          try rewrite HMethodReceiverDeclaredType in H19;
          try inversion H19; try trivial.
          all: try inversion H19; try easy.
        }
        (* clear_dups. amazing.... *)

  (* -------------------------------------------------- *)
  (* Other index - > 1 *)
        apply qualified_type_subtype_q_subtype in H18.
        unfold runtime_getVal.
        simpl.
        destruct (nth_error vals i') as [v|] eqn:Hval_i.
          - (* Parameter i' exists *)
            destruct v as [|loc]; [trivial|].
            (* Use H23 to get the subtyping relationship *)
            assert (Hi'_bound : i' < List.length argtypes).
            {
              apply Forall2_length in H20.
              simpl in Hi.
              simpl in Hnth.
              rewrite Hmsigeq in Hnth.
              rewrite H20.
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
            eapply Forall2_nth_error in H20; eauto.
            apply qualified_type_subtype_base_subtype in H20.
            rewrite (vpa_mutabilty_tt_sctype Ty sqt) in H20.
            eapply base_trans; eauto.

            (* Qualifier Typability *)
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in H20; eauto.
            apply qualified_type_subtype_q_subtype in H20.
            rewrite sq_vpa_tt_eq_qq in H20.
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
            clear - H20 Harg_qualifiertypability HyQualifierTypablility HOutterReceiverQualifierTypablility.

            destruct (rqtype (rt_type argobj)) eqn:Hargobjmutability; move Hargobjmutability at bottom;
            destruct (sqtype sqt) eqn:HParameterStaticDeclearedMutability; move HParameterStaticDeclearedMutability at bottom;
            destruct qinner eqn:HInnerReceiverMutability; move HInnerReceiverMutability at bottom;
            try solve_qualifier_typable_correct_concrete.

            all: destruct (sqtype Ty) eqn:HTyStaticMutability;
            destruct (sqtype argtype) eqn:HArgTypeStaticMutability;
            simpl in H20;
            try solve_q_subtype_wrong.

            all: 
            destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            try solve_qualifier_typable_wrong_concrete.

          - (* Parameter i' doesn't exist - contradiction *)
            exfalso.
            apply nth_error_None in Hval_i.
            apply runtime_lookup_list_preserves_length in H4.
            apply static_getType_list_preserves_length in H11.
            apply Forall2_length in H20.
            rewrite H4 in Hval_i.
            rewrite <- H11 in Hval_i.
            rewrite H20 in Hval_i.
            simpl in Hi.
            simpl in Hnth.
            rewrite <- Hmsigeq in Hval_i.
            lia.
    }
    have HtrueVal: TouchNonMutOnly = true.
    rewrite getmbody in Heval.
    eapply eval_stmt_did_not_touch_abs_start_with_true with (P:=(reachable_locations_from_initial_env CT h rΓmethodinit)) (rΓ':=rΓ'')(h':=h'); eauto.
    rewrite HtrueVal in Heval.
    specialize (IHHeval eq_refl Heval sΓmethodend sΓmethodinit).
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
      unfold vpa_mutabilty_tt.
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
      clear - Hmsigeq Hty_safe H19.
      rewrite Hmsigeq.
      unfold vpa_mutabilty_tt in H19.
      apply qualified_type_subtype_q_subtype in H19.
      destruct Hty_safe as [Hrd | [Hlost| [Himm| HRDM]]].
      + (* Case: sqtype Ty = Rd *)
        rewrite Hrd in H19.
        destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
        try rewrite HMethodReceiverDeclaredType in H19;
        simpl in H19.
        all: inversion H19; try easy.
        all: left; reflexivity.
      + (* Case: sqtype Ty = Lost *)
        rewrite Hlost in H19.
        destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
        try rewrite HMethodReceiverDeclaredType in H19;
        simpl in H19.
        all: inversion H19; try easy.
        all: left; reflexivity.
      + (* Case: sqtype Ty = Imm *)
        rewrite Himm in H19.
        destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
        try rewrite HMethodReceiverDeclaredType in H19;
        simpl in H19.
        all: inversion H19; try easy.
        right; right; left; reflexivity.
        right; right; right; reflexivity.
        left; reflexivity.
      + (* Case: sqtype Ty = RDM *)  
        rewrite HRDM in H19.
        destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
        try rewrite HMethodReceiverDeclaredType in H19;
        simpl in H19.
        all: inversion H19; try easy.
        right; right; right; reflexivity.
        left; reflexivity.
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
          apply Forall2_length in H20.
          rewrite <- Hsigeq in H20.
          assert (H_bound_params : z' < dom (mparams (msignature mdef))).
          {
            apply nth_error_Some. (* Converts "index < len" to "lookup <> None" *)
            rewrite Hnth_param_type.   (* lookup is Some Tz *)
            discriminate.         (* Some <> None *)
          }

          (* 2. Convert to bound for argtypes using the equality *)
          rewrite <- H20 in H_bound_params. (* Replace length of params with length of argtypes *)

          (* 3. Solve the goal *)
          exact H_bound_params.
        }

        have Hnth_arg: exists T_arg, nth_error argtypes z' = Some T_arg.
        {
          apply nth_error_Some_exists.
          exact Hi'_bound.
        }

        destruct Hnth_arg as [T_arg Hnth_arg].
        eapply Forall2_nth_error with (i := z') (a := T_arg) (b := Tz) in H20; [|auto|rewrite <- Hsigeq; exact Hnth_param_type].
        (* apply qualified_type_subtype_q_subtype in H20. *)
        unfold env_respects_protected_set in Hconfined.
        apply adapated_subtype_safe_implies_safe in H20; auto.

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
    specialize (IHHeval HenvInvariant Hwf_method_frame).
    rewrite <- getmbody in Hmethodbody_typing.
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
          rewrite H9 in Hlookup_s. 
          injection Hlookup_s as H_eq_T. subst T_z.
          reflexivity.
        }
        subst T_z.
        unfold env_respects_protected_set in IHHeval.
        have HGetMethodReturnType: static_getType sΓmethodend (mreturn (Syntax.mbody mdef)) = Some mbodyreturntype.
        {
          unfold static_getType; auto.
        }
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
        rewrite getmbody in H6.
        have Hdom_x : x < dom (vars rΓ). 
        { 
          apply runtime_getVal_dom in Hlookup_r.
          rewrite update_length in Hlookup_r.
          exact Hlookup_r.
        }
        have Hlookup_r_copy := Hlookup_r.
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
        specialize (IHHeval (mreturn (Syntax.mbody mdef)) l_z mbodyreturntype HGetMethodReturnType H6 Hin_P_inner).
        rewrite <- Hsigeq in H18.
        apply subtype_safe_implies_safe in HmethodReturnSubtype; auto.
        assert (HlyInP: Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) ly).
        {
          unfold reachable_locations_from_initial_env.
          exists y, ly.
          split; auto.
          apply rch_heap.
          apply runtime_getObj_dom in Hobjy; auto.
        }
        specialize (Hconfined y ly Ty H10 H HlyInP).
        apply subtype_safe_implies_safe_adapted in H18; auto.
        --- (* CASE: z <> x (Old Variables) *)
        (* Just use the original invariant *)
        assert (rΓ <| vars := update x retval (vars rΓ) |> = update_r_env_value rΓ x retval).
        {
          destruct rΓ.
          reflexivity.
        }
        rewrite H2 in Hlookup_r.
        rewrite runtime_getVal_update_diff in Hlookup_r; auto.
        eapply Hconfined; eauto.
    }
    exact Henv_respects''.
Qed.