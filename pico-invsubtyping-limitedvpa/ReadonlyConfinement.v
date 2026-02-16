Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation.
Require Import Properties DeepImmutability Reachability.
Require Import ReadonlyReachability.
From Stdlib Require Import List.
From Stdlib Require String.
Import ListNotations.
From RecordUpdate Require Import RecordUpdate.

(* TODO: move this to all where helper should located *)

Lemma wf_config_has_static_env_dom_greater_than_zero :
  forall CT sΓ rΓ h
    (Hwf : wf_r_config CT sΓ rΓ h),
  dom sΓ > 0.
Proof.
  intros.
  destruct Hwf as [_ [_ [_ [Hsenv [_ _]]]]].
  unfold wf_senv in Hsenv.
  lia.
Qed.

Lemma wf_config_has_runtime_env_dom_greater_than_zero :
  forall CT sΓ rΓ h
    (Hwf : wf_r_config CT sΓ rΓ h),
  dom (vars rΓ) > 0.
Proof.
  intros.
  destruct Hwf as [_ [_ [_ [Hsenv [Henv_len _]]]]].
  unfold wf_senv in Hsenv.
  lia.
Qed.

Lemma receiver_addr_in_protection_set :
  forall CT rΓ h lthis
    (Hdom : lthis < dom h)
    (Hlthis: runtime_getVal rΓ 0 = Some (Iot lthis)),
  Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) lthis.
Proof.
  intros.
  unfold reachable_locations_from_initial_env.
  exists 0, lthis.
  split; auto.
  apply rch_heap; auto.
Qed.

Lemma confined_env_implies_receiver_safe :
  forall CT sΓ rΓ h Tthis lthis
    (Hconfined : env_respects_protected_set (reachable_locations_from_initial_env CT h rΓ) sΓ rΓ)
    (Hdom : lthis < dom h)
    (HTthis: get_this_qualified_type sΓ = Some Tthis)
    (Hlthis: runtime_getVal rΓ 0 = Some (Iot lthis)),
  is_safe_mode_adapted Tthis Tthis.
Proof.
  intros.
  unfold env_respects_protected_set in Hconfined.
  have HinP: Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) lthis by (apply receiver_addr_in_protection_set; auto).
  specialize (Hconfined _ _ Tthis Tthis HTthis HTthis Hlthis HinP).
  exact Hconfined.
Qed.

Ltac solve_safe_mode :=
  match goal with
  (* If the goal is a disjunction, try the left side. If that fails, try the right side. *)
  | |- ?A \/ ?B => (left; solve_safe_mode) || (right; solve_safe_mode)
  
  (* Base Case 1: The branch is a trivial equality (e.g., RO = RO) *)
  | |- ?X = ?X => reflexivity
  
  (* Base Case 2: The branch exactly matches a hypothesis in the current context *)
  | |- _ => assumption
  end.

Lemma stmt_preserves_confinement :
  forall CT sΓ rΓ h stmt sΓ' rΓ' h'
    (Hconfined : env_respects_protected_set (reachable_locations_from_initial_env CT h rΓ) sΓ rΓ)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT retain_nonabs_method sΓ stmt sΓ')
    (Heval : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h'),
  env_respects_protected_set (reachable_locations_from_initial_env CT h rΓ) sΓ' rΓ'.
Proof.
  intros.
  remember OK as ok.
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
    pose proof (preservation_pico _ _ _ _ _ _ _ _ _ Hwf H5 Heval1) as Hwf'.

    (* eapply eval_stmt_did_not_touch_abs_start_with_true; eauto. *)

    (* rewrite HtrueVal' in Heval1. *)

    (* have HtrueVal:  = true. *)
    (* eapply eval_stmt_did_not_touch_abs_start_with_true with (stmt:=s1) (sΓ:=sΓ) (sΓ':=sΓ'); eauto. *)

    subst .
    subst .
    (* Apply IH1 *)
    pose proof (IHHeval1 eq_refl Heval1 sΓ' sΓ Hconfined Hwf H5) as Henv1.

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
    *
      unfold env_respects_protected_set.
      intros y l_y Tthis Ty HTthis Hlookup_s Hlookup_r Hin_P.
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
            apply static_getType_dom in H10.
            rewrite length_app in H10; simpl in H10.
            lia.
          }
          
          (* With x = length sΓ and x <> y, we know y < length sΓ *)
          lia.
        }

        assert (HTthis_old: static_getType sΓ 0 = Some Tthis).
        {
          unfold get_this_qualified_type in HTthis.
          unfold static_getType in HTthis.
          rewrite nth_error_app1 in HTthis; auto.
          eapply wf_config_has_static_env_dom_greater_than_zero in Hwf; eauto.
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
        exact (Hconfined y l_y Tthis Ty HTthis_old Hlookup_s_old Hlookup_r_old Hin_P).
  - (* var assign *)
    inversion Htyping; subst.
    have Hconfined_copy := Hconfined.
    unfold env_respects_protected_set.
    unfold env_respects_protected_set in Hconfined.
    rename sΓ' into sΓ.
    *
      intros y l_y Tthis' Ty HTthis Hlookup_s Hlookup_r Hin_P.
      rewrite H5 in HTthis.
      inversion HTthis; subst Tthis'.
      destruct (extract_receiver_from_wf_config CT sΓ rΓ h Hwf) as [iot [qcontext [Hget_iot[Hiot_dom Hqcontext]]]].
      unfold runtime_getVal in Hlookup_r.
      simpl in Hlookup_r.
      destruct (Nat.eq_dec y x) as [Heq_y | Hneq_y].
      -- (* y = x *)
        subst y.
        rewrite H10 in Hlookup_s.
        inversion Hlookup_s; subst Ty.
        apply runtime_getVal_dom in H.
        rewrite update_same in Hlookup_r; auto.
        injection Hlookup_r as Heq_v2.
        subst v2.
        (* have HtrueVal:  = true.
        eapply eval_expr_did_not_touch_abs_start_with_true; eauto. *)
        (* rewrite HtrueVal in H0. *)
        assert (Hsafe_expr : is_safe_mode_adapted Tthis Te).
        {
          eapply expr_eval_to_protected_implies_safe_type; eauto.
        }
        (* TODO: redefine get_this_var_mapping *)
        eapply subtype_safe_implies_safe; eauto.
        eapply confined_env_implies_receiver_safe; eauto.
        unfold runtime_getVal.
        unfold get_this_var_mapping in Hget_iot.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].
        unfold nth_error.
        destruct v0 as [|loc]; [discriminate|].
        inversion Hget_iot; subst iot.
        reflexivity.
      -- (* y <> x *)
        rewrite update_diff in Hlookup_r; auto.
        unfold env_respects_protected_set in Hconfined.
        exact (Hconfined y l_y Tthis Ty H5 Hlookup_s Hlookup_r Hin_P).
  - (* Field Write *)
    inversion Htyping; subst sΓ'; subst.
    unfold env_respects_protected_set in *.
    exact Hconfined.
  - (* New Object *)
    inversion Htyping; subst sΓ'; subst.
    unfold env_respects_protected_set in *.
    intros y l_y Tthis' Ty HTthis' Hlookup_s Hlookup_r Hin_P.
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
        apply Forall2_length in H21.
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
        rewrite <- H21.
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
        apply qualified_type_subtype_base_subtype in H20.
        (* rewrite (vpa_mutabilty_tt_sctype Tthis Ty) in H23. *)
        rewrite (vpa_mutabilty_tt_sctype Ty (mreceiver (msignature mdef0))) in H20.
        eapply base_trans; eauto.

        (* Qualifier typbility *)
        1: 
        {
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
          unfold vpa_mutabilty_tt in H20.
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
              apply Forall2_length in H21.
              simpl in Hi.
              simpl in Hnth.
              rewrite Hmsigeq in Hnth.
              rewrite H21.
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
            eapply Forall2_nth_error in H21; eauto.
            apply qualified_type_subtype_base_subtype in H21.
            rewrite (vpa_mutabilty_tt_sctype Ty sqt) in H21.
            eapply base_trans; eauto.

            (* Qualifier Typability *)
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in H21; eauto.
            apply qualified_type_subtype_q_subtype in H21.
            rewrite sq_vpa_tt_eq_qq in H21.
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
            clear - H21 Harg_qualifiertypability HyQualifierTypablility HOutterReceiverQualifierTypablility.

            destruct (rqtype (rt_type argobj)) eqn:Hargobjmutability; move Hargobjmutability at bottom;
            destruct (sqtype sqt) eqn:HParameterStaticDeclearedMutability; move HParameterStaticDeclearedMutability at bottom;
            destruct qinner eqn:HInnerReceiverMutability; move HInnerReceiverMutability at bottom;
            try solve_qualifier_typable_correct_concrete.

            all: destruct (sqtype Ty) eqn:HTyStaticMutability;
            destruct (sqtype argtype) eqn:HArgTypeStaticMutability;
            simpl in H21;
            try solve_q_subtype_wrong.

            all: 
            destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            try solve_qualifier_typable_wrong_concrete.

          - (* Parameter i' doesn't exist - contradiction *)
            exfalso.
            apply nth_error_None in Hval_i.
            apply runtime_lookup_list_preserves_length in H4.
            apply static_getType_list_preserves_length in H11.
            apply Forall2_length in H21.
            rewrite H4 in Hval_i.
            rewrite <- H11 in Hval_i.
            rewrite H21 in Hval_i.
            simpl in Hi.
            simpl in Hnth.
            rewrite <- Hmsigeq in Hval_i.
            lia.
    }
    (* have HtrueVal:  = true. *)
    rewrite getmbody in Heval.
    (* eapply eval_stmt_did_not_touch_abs_start_with_true with (P:=(reachable_locations_from_initial_env CT h rΓmethodinit)) (rΓ':=rΓ'')(h':=h'); eauto. *)
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
    rewrite <- Hmsigeq in H14.
    rewrite H14 in Hmethodbody_typing.
    rewrite <- getmbody in Heval.
    specialize (IHHeval Heval sΓmethodend sΓmethodinit).
    assert (HenvInvariant: env_respects_protected_set (reachable_locations_from_initial_env CT h rΓmethodinit)
    sΓmethodinit rΓmethodinit).
    {
      unfold env_respects_protected_set.
      intros z l_z Tthisinner Tz HTthisInner Hlookup_s Hlookup_r Hin_P.
      rewrite HeqsΓmethodinit in Hlookup_s.
      rewrite HeqrΓmethodinit in Hlookup_r.
      unfold static_getType in Hlookup_s.
      unfold runtime_getVal in Hlookup_r.
      simpl in Hlookup_s, Hlookup_r.
      destruct z as [| z'].
      -
        simpl in Hlookup_s, Hlookup_r.
        injection Hlookup_s as <-. injection Hlookup_r as <-.
        unfold is_safe_mode_adapted.
        have Hin_P_orig : Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) ly.
        {
          unfold reachable_locations_from_initial_env.
          exists y, ly.
          split.
          - exact H.  (* runtime_getVal rΓ y = Some (Iot ly) *)
          - apply rch_heap.
            apply reachable_locations_from_initial_env_dom in Hin_P; auto.
        }
        have Hty_safe : is_safe_mode_adapted Tthis Ty.
        {
          unfold env_respects_protected_set in Hconfined.
          specialize (Hconfined y ly Tthis Ty H12 H10 H Hin_P_orig).
          exact Hconfined.
        }
        unfold is_safe_mode_adapted in Hty_safe.
        unfold vpa_mutabilty_tt.
        have Habs_subtype: abs_subtype Ty.(sabs) (vpa_mutabilty_tt Ty (mreceiver (msignature mdef0))).(sabs) by (eapply qualified_type_subtype_abs_subtype; eauto).
        apply qualified_type_subtype_q_subtype in H20.
        (* assert (Hy_dom : y < dom sΓ).
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
        } *)
        rewrite HeqsΓmethodinit in HTthisInner.
        unfold get_this_qualified_type in HTthisInner.
        unfold static_getType in HTthisInner.
        simpl in HTthisInner.
        inversion HTthisInner; subst.
        clear - Hmsigeq Hty_safe H20 Habs_subtype.
        rewrite Hmsigeq.
        unfold vpa_mutabilty_tt in *.
        destruct Hty_safe as [Hrd | [Hlost| [Himm| [HRDM | Hnonabs]]]].
        + (* Case: sqtype Ty = Rd *)
          destruct (sqtype Tthis) eqn: HTthisStaticMutability;
          destruct (sqtype Ty) eqn: HTyStaticMutability;
          simpl in Hrd;
          try discriminate Hrd.
          all: destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
          try rewrite HMethodReceiverDeclaredType in H20;
          simpl in H20.
          all: inversion H20; try easy.
          all: destruct (mreceiver (msignature mdef)) eqn: HTthisInnerStaticMutability; simpl.
          all: left; reflexivity.
        + (* Case: sqtype Ty = Lost *)
          destruct (sqtype Tthis) eqn: HTthisStaticMutability;
          destruct (sqtype Ty) eqn: HTyStaticMutability;
          simpl in Hlost;
          try discriminate Hlost.
          all: destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
          try rewrite HMethodReceiverDeclaredType in H20;
          simpl in H20.
          all: inversion H20; try easy.
          all: destruct (mreceiver (msignature mdef)) eqn: HTthisInnerStaticMutability; simpl.
          1, 4, 9, 12, 15, 18: right; left; reflexivity.
          2, 4, 6, 8, 10, 12, 14: left; reflexivity.
          all: right; right; right; left; reflexivity.
        + (* Case: sqtype Ty = Imm *)
          destruct (sqtype Tthis) eqn: HTthisStaticMutability;
          destruct (sqtype Ty) eqn: HTyStaticMutability;
          simpl in Himm;
          try discriminate Himm.
          all: destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
          try rewrite HMethodReceiverDeclaredType in H20;
          simpl in H20.
          all: inversion H20; try easy.
          all: destruct (mreceiver (msignature mdef)) eqn: HTthisInnerStaticMutability; simpl.
          4, 7: right; right; right; left; reflexivity.
          all: left; reflexivity.
        + (* Case: sqtype Ty = RDM *)  
          destruct (sqtype Tthis) eqn: HTthisStaticMutability;
          destruct (sqtype Ty) eqn: HTyStaticMutability;
          simpl in HRDM;
          try discriminate HRDM.
          all: destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
          try rewrite HMethodReceiverDeclaredType in H20;
          simpl in H20.
          all: inversion H20; try easy.
          all: destruct (mreceiver (msignature mdef)) eqn: HTthisInnerStaticMutability; simpl.
          1: right; right; right; left; reflexivity.
          left; reflexivity.
        + (* Case: sabs Ty = Nonabs*)
          destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
          destruct (sabs (mreceiver (msignature mdef0))) eqn:HMethodReceiverIsAbs;
          simpl.
          1, 3, 5, 7, 9, 11: right; right; right; right; reflexivity.
          2: right; left; reflexivity.
          2: right; right; right; left; reflexivity.
          2: left; reflexivity.
          2: right; right; left; reflexivity.
          all: destruct (sqtype Ty) eqn:HTyStaticMutability;
          try rewrite HMethodReceiverDeclaredType in H20;
          simpl in H20.
          all: inversion H20; try easy.
          all: destruct (sabs Ty) eqn:HTyAbs; simpl in Habs_subtype; try discriminate.
          all: try inversion Habs_subtype; try easy.
      -
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
          apply Forall2_length in H21.
          rewrite <- Hmsigeq in H21.
          assert (H_bound_params : z' < dom (mparams (msignature mdef))).
          {
            apply nth_error_Some. (* Converts "index < len" to "lookup <> None" *)
            rewrite Hnth_param_type.   (* lookup is Some Tz *)
            discriminate.         (* Some <> None *)
          }

          (* 2. Convert to bound for argtypes using the equality *)
          rewrite <- H21 in H_bound_params. (* Replace length of params with length of argtypes *)

          (* 3. Solve the goal *)
          exact H_bound_params.
        }

        have Hnth_arg: exists T_arg, nth_error argtypes z' = Some T_arg.
        {
          apply nth_error_Some_exists.
          exact Hi'_bound.
        }

        destruct Hnth_arg as [T_arg Hnth_arg].
        eapply Forall2_nth_error with (i := z') (a := T_arg) (b := Tz) in H21; [|auto|rewrite <- Hmsigeq; exact Hnth_param_type].
        rewrite HeqsΓmethodinit in HTthisInner.
        unfold get_this_qualified_type in HTthisInner.
        unfold static_getType in HTthisInner.
        simpl in HTthisInner.
        inversion HTthisInner; subst.
        rewrite Hmsigeq.
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
        have Hconfined_copy := Hconfined.
        specialize (Hconfined z_outter l_z Tthis T_arg H12 HgetZ_type HgetZ_val Hin_P_orig).
        (* have HlyInP: Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) ly.
        {
          unfold reachable_locations_from_initial_env.
          exists y, ly.
          split; auto.
          apply rch_heap.
          apply reachable_locations_from_initial_env_dom in Hin_P; auto.
          apply runtime_getObj_dom in Hobjy; auto.
        } *)
        (* specialize (Hconfined_copy y ly Tthis Ty H12 H10 H HlyInP); auto. *)
        (* eapply subtype_safe_implies_safe in H21. *)
        clear - H21 H20 Hconfined.
        have Habs1: abs_subtype T_arg.(sabs) (vpa_mutabilty_tt Ty Tz).(sabs).
        {
          eapply qualified_type_subtype_abs_subtype in H21; eauto.
        }
        apply qualified_type_subtype_q_subtype in H21.
        have Habs2: abs_subtype Ty.(sabs) (vpa_mutabilty_tt Ty (mreceiver (msignature mdef0))).(sabs).
        {
          eapply qualified_type_subtype_abs_subtype in H20; eauto.
        }
        apply qualified_type_subtype_q_subtype in H20.
        unfold is_safe_mode_adapted in *.
        unfold vpa_mutabilty_tt in *.
        destruct (sqtype Ty) eqn:HTyStaticMutability;
        destruct (sqtype (mreceiver (msignature mdef0))) eqn:HMethodReceiverDeclaredType;
        simpl in *.
        all: destruct (sqtype Tz) eqn:HTzStaticMutability; try solve_q_subtype_wrong.
        all: try solve [solve_safe_mode].
        all:
        destruct (sqtype Tthis) eqn:HTthisStaticMutability;
        destruct (sqtype T_arg) eqn:HTargStaticMutability.
        all: try solve_q_subtype_wrong.
        all: try solve [solve_safe_mode].
        all: destruct (sabs Tz) eqn:HTzAbs; try solve [solve_safe_mode].
        all: destruct Hconfined as [Hrd | [Hlost| [Himm| [HRDM | Hnonabs]]]];
        try discriminate Hrd; try discriminate Hlost; try discriminate Himm; try discriminate HRDM.
        all: rewrite Hnonabs in Habs1; try inversion Habs1; subst; auto.
    }
    specialize (IHHeval HenvInvariant Hwf_method_frame).
    rewrite <- getmbody in Hmethodbody_typing.
    specialize (IHHeval Hmethodbody_typing).
    assert (Henv_respects'': env_respects_protected_set (reachable_locations_from_initial_env CT h rΓ) sΓ rΓ''' ).
    {
      rewrite HeqrΓ'''.
      unfold env_respects_protected_set.
      intros z l_z Tthis' T_z HTthis Hlookup_s Hlookup_r Hin_P.
      rewrite H12 in HTthis.
      inversion HTthis; subst Tthis'.
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
        have Hdom_z : z < dom (vars rΓ). 
        { 
          apply runtime_getVal_dom in Hlookup_r.
          rewrite update_length in Hlookup_r.
          rewrite Hvars.
          exact Hlookup_r.
        }
        have Hlookup_r_copy := Hlookup_r.
        unfold runtime_getVal in Hlookup_r.
        rewrite update_same in Hlookup_r. rewrite <- Hvars. lia.   (* or by exact Hdom_x *)
        inversion Hlookup_r; subst.

        have Hin_P_inner: Ensembles.In Loc (reachable_locations_from_initial_env CT h
        {| vars := Iot ly :: vals |}) l_z.
        {
          eapply reachable_return_implies_reachable_args; eauto.
          apply reachable_locations_from_initial_env_dom in Hin_P; auto. (* This is not provable, need a lot changes *)
        }
        have HgetReceverEndingFrame: get_this_qualified_type sΓmethodend = Some (mreceiver (msignature mdef)).
        {
          admit.
        }
        have HgetReceiverAddrEndingFrame: runtime_getVal rΓ'' 0 = Some (Iot ly).
        {
          admit.
        }
        assert (HlyInPinner: Ensembles.In Loc (reachable_locations_from_initial_env CT h {| vars := Iot ly :: vals |}) ly).
        {
          eapply reachable_return_implies_reachable_args; eauto.
          apply reachable_locations_from_initial_env_dom in Hin_P; auto.
          apply runtime_getObj_dom in Hobjy; auto.
        }
        have IHHeval_copy := IHHeval.
        specialize (IHHeval (mreturn (Syntax.mbody mdef)) l_z (mreceiver (msignature mdef)) mbodyreturntype HgetReceverEndingFrame HGetMethodReturnType H6 Hin_P_inner).
        specialize (IHHeval_copy 0 ly (mreceiver (msignature mdef)) (mreceiver (msignature mdef)) HgetReceverEndingFrame HgetReceverEndingFrame HgetReceiverAddrEndingFrame HlyInPinner).
        rewrite <- Hmsigeq in H18.
        
        (* have Hconfined_copy := Hconfined.
        unfold env_respects_protected_set in HenvInvariant.
        specialize (HenvInvariant ). *)
        rewrite <- Hmsigeq in H20.
        have test: is_safe_mode_adapted Tthis Tthis.
        {
          admit.
        }
        have HlyInP: Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) ly.
        {
          unfold reachable_locations_from_initial_env.
          exists y, ly.
          split; auto.
          apply rch_heap.
          apply reachable_locations_from_initial_env_dom in Hin_P; auto.
          apply runtime_getObj_dom in Hobjy; auto.
        }
        specialize (Hconfined y ly Tthis Ty H12 H10 H HlyInP).
        (* eapply subtype_safe_implies_safe_adapted in H18; eauto. *)
        (* specialize (Hconfined 0 lOutterReceiver Tthis Tthis H12 H12 HOutterReceiverAddr ) *)
        clear - IHHeval IHHeval_copy H18 H20 HmethodReturnSubtype Hconfined.
        have Habs1: abs_subtype (vpa_mutabilty_tt Ty (mret (msignature mdef))).(sabs) Tx.(sabs).
        {
          eapply qualified_type_subtype_abs_subtype in H18; eauto.
        }
        apply qualified_type_subtype_q_subtype in H18.
        have Habs2: abs_subtype Ty.(sabs) (vpa_mutabilty_tt Ty (mreceiver (msignature mdef))).(sabs).
        {
          eapply qualified_type_subtype_abs_subtype in H20; eauto.
        }
        apply qualified_type_subtype_q_subtype in H20.
        have Habs3: abs_subtype mbodyreturntype.(sabs) (mret (msignature mdef)).(sabs).
        {
          eapply qualified_type_subtype_abs_subtype in HmethodReturnSubtype; eauto.
        }
        apply qualified_type_subtype_q_subtype in HmethodReturnSubtype.
        unfold is_safe_mode_adapted in *.
        unfold vpa_mutabilty_tt in *.
        simpl in *.
        have Habs: abs_subtype (sabs mbodyreturntype) (sabs Tx).
        {
          eapply abs_subtype_trans; eauto.
        }
        (* clear Habs1 Habs2 Habs3. *)
        destruct (sqtype Tthis) eqn:HTthisStaticMutability;
        destruct (sqtype Tx) eqn:HTxStaticMutability;
        simpl; try solve [solve_safe_mode].
        all: 
        destruct (sabs Tx) eqn:HTxAbs; try solve [solve_safe_mode].
        all: exfalso.
        all: 
        destruct (sqtype (mreceiver (msignature mdef))) eqn:HMethodReceiverDeclaredType.
        all: destruct (sqtype Ty) eqn:HTyStaticMutability; try solve_q_subtype_wrong.
        all: destruct (sqtype (mret (msignature mdef))) eqn:HMethodReturnDeclaredType;
        try solve_q_subtype_wrong.
        all: destruct (sqtype mbodyreturntype) eqn:HMethodReturnStaticDeclaredMutability;
        try solve_q_subtype_wrong.
        all: destruct Hconfined as [Hrd | [Hlost| [Himm| [HRDM | Hnonabs]]]];
        try discriminate Hrd; try discriminate Hlost; try discriminate Himm; try discriminate HRDM.
        all: destruct IHHeval as [Hrd' | [Hlost'| [Himm'| [HRDM' | Hnonabs']]]];
        try discriminate Hrd'; try discriminate Hlost'; try discriminate Himm'; try discriminate HRDM'.
        all: destruct IHHeval_copy as [Hrd'' | [Hlost''| [Himm''| [HRDM'' | Hnonabs'']]]];
        try discriminate Hrd''; try discriminate Hlost''; try discriminate Himm''; try discriminate HRDM''.
        all: try rewrite Hnonabs in Habs2.
        all: try rewrite Hnonabs' in Habs.
        all: try inversion Habs; subst; auto.
        all: clear Habs.
        all: 
        try rewrite Hnonabs'' in Habs3;
        try rewrite Hnonabs'' in Habs;
        try discriminate Hnonabs.
        5, 10, 15, 20, 25, 30, 35, 40, 45, 50, 55, 60, 65, 70: rewrite Hnonabs in Habs; inversion Habs; subst; auto.
        (* all: clear Habs. *)
        all: destruct IHHeval_copy as [Hrd' | [Hlost'| [Himm'| [HRDM' | Hnonabs']]]].

        all: destruct (sqtype Ty) eqn:HTyStaticMutability;
        try discriminate Hrd';
        try discriminate Hlost';
        try discriminate Himm';
        try discriminate HRDM';
        try solve_q_subtype_wrong.
        try discriminate Hrd;
        try discriminate Hlost;
        try discriminate Himm;
        try discriminate HRDM.

         
        
        
        
        all: destruct (sqtype (mreceiver (msignature mdef))) eqn:HMethodReceiverDeclaredType;
        
        try simpl in Hrd; 
        
        
        all:
         
        all: destruct 
        
        all:
        eapply subtype_safe_implies_safe_adapted; eauto.
        (* specialize (Hconfined y ly Ty H10 H HlyInP). *)
        rewrite <- Hmsigeq in H20.
        rewrite <- Hmsigeq in H21.
        apply subtype_safe_implies_safe_adapted in H18; auto.
        all: admit.
      -- (* CASE: z <> x (Old Variables) *)
      (* Just use the original invariant *)
      assert (rΓ <| vars := update x retval (vars rΓ) |> = update_r_env_value rΓ x retval).
      {
        destruct rΓ.
        reflexivity.
      }
      rewrite Hvars in H0.
      rewrite H0 in Hlookup_r.
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
        apply Forall2_length in H21.
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
        rewrite <- H21.
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
        apply qualified_type_subtype_base_subtype in H20.
        (* rewrite (vpa_mutabilty_tt_sctype Tthis Ty) in H23. *)
        rewrite (vpa_mutabilty_tt_sctype Ty (mreceiver (msignature mdef0))) in H20.
        eapply base_trans; eauto.

        (* Qualifier typbility *)
        1: 
        {
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
          unfold vpa_mutabilty_tt in H20.
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
              apply Forall2_length in H21.
              simpl in Hi.
              simpl in Hnth.
              rewrite Hmsigeq in Hnth.
              rewrite H21.
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
            eapply Forall2_nth_error in H21; eauto.
            apply qualified_type_subtype_base_subtype in H21.
            rewrite (vpa_mutabilty_tt_sctype Ty sqt) in H21.
            eapply base_trans; eauto.

            (* Qualifier Typability *)
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in H21; eauto.
            apply qualified_type_subtype_q_subtype in H21.
            rewrite sq_vpa_tt_eq_qq in H21.
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
            clear - H21 Harg_qualifiertypability HyQualifierTypablility HOutterReceiverQualifierTypablility.

            destruct (rqtype (rt_type argobj)) eqn:Hargobjmutability; move Hargobjmutability at bottom;
            destruct (sqtype sqt) eqn:HParameterStaticDeclearedMutability; move HParameterStaticDeclearedMutability at bottom;
            destruct qinner eqn:HInnerReceiverMutability; move HInnerReceiverMutability at bottom;
            try solve_qualifier_typable_correct_concrete.

            all: destruct (sqtype Ty) eqn:HTyStaticMutability;
            destruct (sqtype argtype) eqn:HArgTypeStaticMutability;
            simpl in H21;
            try solve_q_subtype_wrong.

            all: 
            destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            try solve_qualifier_typable_wrong_concrete.

          - (* Parameter i' doesn't exist - contradiction *)
            exfalso.
            apply nth_error_None in Hval_i.
            apply runtime_lookup_list_preserves_length in H4.
            apply static_getType_list_preserves_length in H11.
            apply Forall2_length in H21.
            rewrite H4 in Hval_i.
            rewrite <- H11 in Hval_i.
            rewrite H21 in Hval_i.
            simpl in Hi.
            simpl in Hnth.
            rewrite <- Hmsigeq in Hval_i.
            lia.
    }
    (* have HtrueVal:  = true.
    rewrite getmbody in Heval.
    eapply eval_stmt_did_not_touch_abs_start_with_true with (P:=(reachable_locations_from_initial_env CT h rΓmethodinit)) (rΓ':=rΓ'')(h':=h'); eauto. *)
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
    rewrite <- Hmsigeq in H14.
    rewrite H14 in Hmethodbody_typing.
    (* exact Hmethodbody_typing. *)
    (* rewrite HtrueVal in Heval. *)
    specialize (IHHeval Heval sΓmethodend sΓmethodinit).
    assert (HenvInvariant: env_respects_protected_set (reachable_locations_from_initial_env CT h rΓmethodinit)
    sΓmethodinit rΓmethodinit).
    {
      unfold env_respects_protected_set.
      intros z l_z TthisInner Tz HTthisInner Hlookup_s Hlookup_r Hin_P.
      rewrite HeqsΓmethodinit in Hlookup_s.
      rewrite HeqrΓmethodinit in Hlookup_r.
      unfold static_getType in Hlookup_s.
      unfold runtime_getVal in Hlookup_r.
      simpl in Hlookup_s, Hlookup_r.
      destruct z as [| z'].
      -
        simpl in Hlookup_s, Hlookup_r.
        injection Hlookup_s as <-. injection Hlookup_r as <-.
        unfold is_safe_mode_adapted.
        have Hin_P_orig : Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) ly.
        {
          unfold reachable_locations_from_initial_env.
          exists y, ly.
          split.
          - exact H.  (* runtime_getVal rΓ y = Some (Iot ly) *)
          - apply rch_heap.
            apply reachable_locations_from_initial_env_dom in Hin_P; auto.
        }
        have Hty_safe : is_safe_mode_adapted Tthis Ty.
        {
          unfold env_respects_protected_set in Hconfined.
          specialize (Hconfined y ly Tthis Ty H12 H10 H Hin_P_orig).
          exact Hconfined.
        }
        unfold is_safe_mode_adapted in Hty_safe.
        unfold vpa_mutabilty_tt.
        have Habs_subtype: abs_subtype Ty.(sabs) (vpa_mutabilty_tt Ty (mreceiver (msignature mdef0))).(sabs) by (eapply qualified_type_subtype_abs_subtype; eauto).
        apply qualified_type_subtype_q_subtype in H20.
        rewrite HeqsΓmethodinit in HTthisInner.
        unfold get_this_qualified_type in HTthisInner.
        unfold static_getType in HTthisInner.
        simpl in HTthisInner.
        inversion HTthisInner; subst.
        clear - Hmsigeq Hty_safe H20 Habs_subtype.
        rewrite Hmsigeq.
        unfold vpa_mutabilty_tt in *.
        destruct Hty_safe as [Hrd | [Hlost| [Himm| [HRDM | Hnonabs]]]].
        + (* Case: sqtype Ty = Rd *)
          destruct (sqtype Tthis) eqn: HTthisStaticMutability;
          destruct (sqtype Ty) eqn: HTyStaticMutability;
          simpl in Hrd;
          try discriminate Hrd.
          all: destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
          try rewrite HMethodReceiverDeclaredType in H20;
          simpl in H20.
          all: inversion H20; try easy.
          all: destruct (mreceiver (msignature mdef)) eqn: HTthisInnerStaticMutability; simpl.
          all: left; reflexivity.
        + (* Case: sqtype Ty = Lost *)
          destruct (sqtype Tthis) eqn: HTthisStaticMutability;
          destruct (sqtype Ty) eqn: HTyStaticMutability;
          simpl in Hlost;
          try discriminate Hlost.
          all: destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
          try rewrite HMethodReceiverDeclaredType in H20;
          simpl in H20.
          all: inversion H20; try easy.
          all: destruct (mreceiver (msignature mdef)) eqn: HTthisInnerStaticMutability; simpl.
          1, 4, 9, 12, 15, 18: right; left; reflexivity.
          2, 4, 6, 8, 10, 12, 14: left; reflexivity.
          all: right; right; right; left; reflexivity.
        + (* Case: sqtype Ty = Imm *)
          destruct (sqtype Tthis) eqn: HTthisStaticMutability;
          destruct (sqtype Ty) eqn: HTyStaticMutability;
          simpl in Himm;
          try discriminate Himm.
          all: destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
          try rewrite HMethodReceiverDeclaredType in H20;
          simpl in H20.
          all: inversion H20; try easy.
          all: destruct (mreceiver (msignature mdef)) eqn: HTthisInnerStaticMutability; simpl.
          4, 7: right; right; right; left; reflexivity.
          all: left; reflexivity.
        + (* Case: sqtype Ty = RDM *)  
          destruct (sqtype Tthis) eqn: HTthisStaticMutability;
          destruct (sqtype Ty) eqn: HTyStaticMutability;
          simpl in HRDM;
          try discriminate HRDM.
          all: destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
          try rewrite HMethodReceiverDeclaredType in H20;
          simpl in H20.
          all: inversion H20; try easy.
          all: destruct (mreceiver (msignature mdef)) eqn: HTthisInnerStaticMutability; simpl.
          1: right; right; right; left; reflexivity.
          left; reflexivity.
        + (* Case: sabs Ty = Nonabs*)
          destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
          destruct (sabs (mreceiver (msignature mdef0))) eqn:HMethodReceiverIsAbs;
          simpl.
          1, 3, 5, 7, 9, 11: right; right; right; right; reflexivity.
          2: right; left; reflexivity.
          2: right; right; right; left; reflexivity.
          2: left; reflexivity.
          2: right; right; left; reflexivity.
          all: destruct (sqtype Ty) eqn:HTyStaticMutability;
          try rewrite HMethodReceiverDeclaredType in H20;
          simpl in H20.
          all: inversion H20; try easy.
          all: destruct (sabs Ty) eqn:HTyAbs; simpl in Habs_subtype; try discriminate.
          all: try inversion Habs_subtype; try easy.
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
          apply Forall2_length in H21.
          rewrite <- Hsigeq in H21.
          assert (H_bound_params : z' < dom (mparams (msignature mdef))).
          {
            apply nth_error_Some. (* Converts "index < len" to "lookup <> None" *)
            rewrite Hnth_param_type.   (* lookup is Some Tz *)
            discriminate.         (* Some <> None *)
          }

          (* 2. Convert to bound for argtypes using the equality *)
          rewrite <- H21 in H_bound_params. (* Replace length of params with length of argtypes *)

          (* 3. Solve the goal *)
          exact H_bound_params.
        }

        have Hnth_arg: exists T_arg, nth_error argtypes z' = Some T_arg.
        {
          apply nth_error_Some_exists.
          exact Hi'_bound.
        }

        destruct Hnth_arg as [T_arg Hnth_arg].
        eapply Forall2_nth_error with (i := z') (a := T_arg) (b := Tz) in H21; [|auto|rewrite <- Hsigeq; exact Hnth_param_type].
        (* apply qualified_type_subtype_q_subtype in H20. *)
        unfold env_respects_protected_set in Hconfined.
        apply adapated_subtype_safe_implies_safe in H21; auto.

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
        have HlyInP: Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) ly.
        {
          unfold reachable_locations_from_initial_env.
          exists y, ly.
          split; auto.
          apply rch_heap.
          apply reachable_locations_from_initial_env_dom in Hin_P; auto.
          apply runtime_getObj_dom in Hobjy; auto.
        }
        specialize (Hconfined y ly Ty H10 H HlyInP); auto.
    }
    specialize (IHHeval HenvInvariant Hwf_method_frame).
    rewrite <- getmbody in Hmethodbody_typing.
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
    rewrite Hsigeq in Hmethodbody_typing.
    rewrite H14 in Hmethodbody_typing.
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
        (* apply subtype_safe_implies_safe in HmethodReturnSubtype; auto. *)
        assert (HlyInP: Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) ly).
        {
          unfold reachable_locations_from_initial_env.
          exists y, ly.
          split; auto.
          apply rch_heap.
          apply runtime_getObj_dom in Hobjy; auto.
        }
        have Hconfined_copy := Hconfined.
        specialize (Hconfined y ly Ty H10 H HlyInP).
        (* apply subtype_safe_implies_safe_adapted in H18; auto. *)
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