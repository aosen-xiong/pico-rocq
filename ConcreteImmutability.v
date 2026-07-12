Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation.
Require Import Properties DeepImmutability Reachability Preservation ReadonlyHelper ReadonlyConfinement ReadonlyNoMutation ReadonlySafety.
From Stdlib Require Import List.
From Stdlib Require String.
Import ListNotations.

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
        have Hx_safe := mut_var_cannot_point_to_P sΓ' rΓ x Tx l (reachable_locations_from_initial_env CT h rΓ) Hget_x Hval_x Hconfined Hlocalset.

        (* Case on assignability *)
        apply vpa_assingability_assign_cases_concret_imm in Hassignable.
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
        have Hget_x_copy := Hget_x.
        apply static_getType_dom in Hget_x.
        unfold static_getType in Hget_x_copy.
        specialize (Htypable Hget_x Tx Hget_x_copy).
        rewrite Hval_x in Htypable.
        unfold wf_r_typable in Htypable.
        unfold r_type in Htypable.
        rewrite Hobj in Htypable.
        destruct Htypable as [base qualifier].
        simpl in base.
        destruct Hassignable as [[Hx_mut Ha_assignable] | [Hx_mut Ha_rda]].
        ++ (* Case: a = Assignable *)
          rewrite Hx_mut in Hx_safe.
          exfalso; apply Hx_safe; reflexivity.
        ++ (* Case: sqtype Tx = Mut ∧ a = RDA *)
          exfalso.
          apply Hx_safe.
          exact Hx_mut.
      + (* Different field case: trivial *)
        unfold update_field in Hobj'.
        rewrite Hobj in Hobj'.
        simpl in Hobj'.

        (* Extract the domain bound for l *)
        assert (Hdom : l < dom h).
        {
          apply runtime_getObj_dom in Hobj.
          exact Hobj.
        }

        (* After update_field, the object at l has fields updated at f0 *)
        rewrite runtime_getObj_update_same in Hobj'; auto.

        injection Hobj' as _ Hvals'_eq.
        rewrite Hobj in Hobj0.
        injection Hobj0 as Hvals_eq.

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
        | Some o => [loc_x ↦ (set_fields_map o (update f0 val_y (fields_map o)))] h
        | None => h
        end) l = runtime_getObj h l.
      {
        destruct (runtime_getObj h loc_x).
        - apply runtime_getObj_update_diff; auto.
        - reflexivity.
      }
      rewrite Heq in Hobj'.
      rewrite Hobj0 in Hobj'.
      inversion Hobj'.
      reflexivity.
    }
  - (* New *)
    (* intros l C anyrq vals0 vals' Hin Hobj Hobj' f Hprotected. *)
    unfold protected_locset in Hlocalset.

    (* Extract l < dom h from reachable_abs *)
    assert(Hl_old : l < dom h).
    {
      apply runtime_getObj_dom in Hobj0.
      exact Hobj0.
    }

    rewrite runtime_getObj_last2 in Hobj'; auto.
  - (* Call *)
    inversion Htyping; subst sΓ'; subst.
    + destruct Hscope as [Hscope | [Hscope _]]; inversion Hscope.
    +
    have Hwfcopy := Hwf.
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hclasstable [Hheap [Hrenv [Hsenv [_ Htypable]]]]].
    unfold env_respects_protected_set in *.
    specialize (IHHeval (eq_refl)).
    destruct Hfind as [mdeflookup getmbody].
    remember (msignature mdef) as msig.
    inversion mdeflookup; revert getmbody; subst; intro getmbody.
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
    assert (Hframe_sig : msignature mdef = msignature mdef0).
    {
      eapply runtime_call_signature_agrees with
        (y := y) (Ty := Ty) (ly := ly) (cy := cy) (m := m)
        (mdef_runtime := mdef) (mdef_static := mdef0); eauto.
    }
    assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
    {
      rewrite HeqsΓmethodinit.
      rewrite HeqrΓmethodinit.
      eapply callee_frame_wf_rs_ts; eauto.
      all: rewrite Hframe_sig; assumption.
    }
    destruct (reachable_locations_from_initial_env_dec CT h rΓmethodinit l) as [Hlocalset' | Hnot_reachable].
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
        eapply method_signature_consistent_subtype with (C := rc_obj) (D := sctype Ty) (m := m); eauto.
      }
      clear - Hmsigeq Hty_safe Hrcv_sub.
      destruct Hrcv_sub as [Hrcv_sub | Hrcv_sub].
      apply qualified_type_subtype_q_subtype in Hrcv_sub.
      rewrite Hmsigeq.
      unfold vpa_mutability_tt_safe_ro in Hrcv_sub.
      destruct Hty_safe as [HRd | [HLost | [HRDM| HImm] ]].
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
        right; right; left; exact HReceiverDeclearedQualifier.
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
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy.
        2:{ discriminate. }
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        unfold r_type in Htypable.
        rewrite Hval_y in Htypable.
        rewrite Hobjy in Htypable.
        simpl in Htypable.
        destruct Htypable as [Hsubtype Hqualifier].
        simpl in Hobjy.

        assert (Hrc_obj_eq: rc_obj = cy).
        {
          simpl in Hbase.
          inversion Hbase.
          easy.
        }
        subst rc_obj.
        assert (Hsigeq: msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype with (C := cy) (D := sctype Ty) (m := m); eauto.
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
    {
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
        eapply method_signature_consistent_subtype with (C := rc_obj) (D := sctype Ty) (m := m); eauto.
      }

      rewrite Hmsigeq in Hmethodbody_typing.
      have Hconcrete_not_abs : ConcreteImm <> AbstractImm.
      {
        discriminate.
      }
      destruct (mtype (msignature mdef0)).
      { exfalso; exact (Hmt_not_abs eq_refl). }
      { exfalso; exact (Hmt_not_cs eq_refl). }
      { inversion Hmt_sub; subst; discriminate. }
      {
        specialize (IHHeval Hlocalset' vals' Hobj' vals0 Hobj sΓmethodend sΓmethodinit).
        specialize (IHHeval HenvInvariant Hwf_method_frame).
        exact (IHHeval Hmethodbody_typing).
      }
      all: inversion Hmt_sub; subst; try discriminate.
    }
    all: try solve [inversion Hmt_sub; subst; discriminate].
    {
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
    assert (Hframe_sig : msignature mdef = msignature mdef0).
    {
      eapply runtime_call_signature_agrees with
        (y := y) (Ty := Ty) (ly := ly) (cy := cy) (m := m)
        (mdef_runtime := mdef) (mdef_static := mdef0); eauto.
    }
    assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
    {
      rewrite HeqsΓmethodinit.
      rewrite HeqrΓmethodinit.
      eapply callee_frame_wf_rs_ts; eauto.
      all: rewrite Hframe_sig; assumption.
    }
    destruct (reachable_locations_from_initial_env_dec CT h rΓmethodinit l) as [Hlocalset' | Hnot_reachable].
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
        eapply method_signature_consistent_subtype with (C := rc_obj) (D := sctype Ty) (m := m); eauto.
      }
      clear - Hmsigeq Hty_safe Hrcv_sub.
      destruct Hrcv_sub as [Hrcv_sub | Hrcv_sub].
      apply qualified_type_subtype_q_subtype in Hrcv_sub.
      rewrite Hmsigeq.
      unfold vpa_mutability_tt_safe_ro in Hrcv_sub.
      destruct Hty_safe as [HRd | [HLost | [HRDM| HImm] ]].
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
        right; right; left; exact HReceiverDeclearedQualifier.
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
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy.
        2:{ discriminate. }
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        unfold r_type in Htypable.
        rewrite Hval_y in Htypable.
        rewrite Hobjy in Htypable.
        simpl in Htypable.
        destruct Htypable as [Hsubtype Hqualifier].
        simpl in Hobjy.

        assert (Hrc_obj_eq: rc_obj = cy).
        {
          simpl in Hbase.
          inversion Hbase.
          easy.
        }
        subst rc_obj.
        assert (Hsigeq: msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype with (C := cy) (D := sctype Ty) (m := m); eauto.
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
    {
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
        eapply method_signature_consistent_subtype with (C := rc_obj) (D := sctype Ty) (m := m); eauto.
      }

      rewrite Hmsigeq in Hmethodbody_typing.
      have Hconcrete_not_abs : ConcreteImm <> AbstractImm.
      {
        discriminate.
      }
      destruct (mtype (msignature mdef0)).
      { exfalso; exact (Hmt_not_abs eq_refl). }
      { exfalso; exact (Hmt_not_cs eq_refl). }
      { inversion Hmt_sub; subst; discriminate. }
      {
        specialize (IHHeval Hlocalset' vals' Hobj' vals0 Hobj sΓmethodend sΓmethodinit).
        specialize (IHHeval HenvInvariant Hwf_method_frame).
        exact (IHHeval Hmethodbody_typing).
      }
      all: inversion Hmt_sub; subst; try discriminate.
    }
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
    specialize (IHHeval1 eq_refl Hlocalset values' Hrtype vals Hobj sΓ' sΓ Hconfined Hwf Htype1).
    specialize (IHHeval2 eq_refl Hlocalset vals' Hobj' values' Hrtype sΓ'' sΓ' Hconfined_intermediate Hwf' Htype2).
    rewrite IHHeval2 in IHHeval1; auto.
Qed.

Lemma ConcreteImmutability_with_end :
  forall CT sΓ rΓ h stmt rΓ' h' sΓ' x y mindex Ty mdef zs vals ly
         loc_arg C anyrq vals_arg vals_arg' f
    (Hstmt : stmt = (SCall x mindex y zs))
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
  { destruct Hscope as [Hscope | [Hscope _]]; inversion Hscope. }
  {
  rename sΓ' into sΓ.
  rewrite Hget_y0 in Hstatic_type.
  inversion Hstatic_type; subst Ty0.

  have Hmdefeq: mdef1 = mdef.
  {
    unfold wf_r_config in Hwf.
    destruct Hwf as [HClassTable _].
    unfold wf_senv in Hwf0.
    destruct Hwf0 as [Hwf0 Hwftypeuse].
    eapply find_overriding_method_deterministic; eauto.
    eapply Forall_nth_error in Hwftypeuse; eauto.
    unfold wf_stypeuse in Hwftypeuse.
    destruct (bound CT (sctype Ty)) eqn: Hbound.
    - unfold bound in Hbound.
      destruct (find_class CT (sctype Ty)) eqn:Hfindclass; [|discriminate].
      apply find_class_dom in Hfindclass; auto.
    - contradiction.
  }
  subst mdef1.
  rename mdef into mdef1.
  rename mdef0 into mdef.
  rename Ty into Ty_call.

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
    remember (set_vars rΓ (update x retval (vars rΓ))) as rΓ'''.
    remember (mreceiver (msignature mdef)) as Ty.
    assert (Hframe_sig : msignature mdef = msignature mdef1).
    {
      eapply runtime_call_signature_agrees with
        (y := y) (Ty := Ty_call) (ly := ly) (cy := cy) (m := mindex)
        (mdef_runtime := mdef) (mdef_static := mdef1); eauto.
    }
    assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
    {
      rewrite HeqsΓmethodinit.
      rewrite HeqTy.
      rewrite HeqrΓmethodinit.
      eapply callee_frame_wf_rs_ts; eauto.
      all: rewrite Hframe_sig; assumption.
    }

    eapply deep_concrete_immutability_preservation with (stmt := (mbody_stmt mbody)) (sΓ' := sΓmethodend); eauto.
    assert (HenvImpliesEnvRespect :
      env_respects_protected_set
        (reachable_locations_from_initial_env CT h rΓmethodinit)
        sΓmethodinit rΓmethodinit).
    {
      have Hwf_frame := Hwf_method_frame.
      rewrite HeqsΓmethodinit in Hwf_frame.
      rewrite HeqTy in Hwf_frame.
      rewrite HeqrΓmethodinit in Hwf_frame.
      rewrite HeqsΓmethodinit.
      rewrite HeqTy.
      rewrite HeqrΓmethodinit.
      eapply callee_frame_respects_protected_set.
      exact Hwf_frame.
      rewrite Hframe_sig. exact Hall_readonly.
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
    specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty_call Hget_y0).
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
      eapply method_signature_consistent_subtype with (C := rc_obj) (D := sctype Ty_call) (m := mindex); eauto.
    }
    rewrite Hmsigeq in Hmethodbody_typing.
    inversion Hmt_sub; subst; try (rewrite <- H1 in Hmethodbody_typing); exact Hmethodbody_typing.
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
    remember (set_vars rΓ (update x retval (vars rΓ))) as rΓ'''.
    remember (mreceiver (msignature mdef)) as Ty.
    assert (Hframe_sig : msignature mdef = msignature mdef1).
    {
      eapply runtime_call_signature_agrees with
        (y := y) (Ty := Ty_call) (ly := ly) (cy := cy) (m := mindex)
        (mdef_runtime := mdef) (mdef_static := mdef1); eauto.
    }
    assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
    {
      rewrite HeqsΓmethodinit.
      rewrite HeqTy.
      rewrite HeqrΓmethodinit.
      eapply callee_frame_wf_rs_ts; eauto.
      all: rewrite Hframe_sig; assumption.
    }
    eapply deep_concrete_immutability_preservation with (stmt := (mbody_stmt mbody)) (sΓ' := sΓmethodend); eauto.
    assert (HenvImpliesEnvRespect :
      env_respects_protected_set
        (reachable_locations_from_initial_env CT h rΓmethodinit)
        sΓmethodinit rΓmethodinit).
    {
      have Hwf_frame := Hwf_method_frame.
      rewrite HeqsΓmethodinit in Hwf_frame.
      rewrite HeqTy in Hwf_frame.
      rewrite HeqrΓmethodinit in Hwf_frame.
      rewrite HeqsΓmethodinit.
      rewrite HeqTy.
      rewrite HeqrΓmethodinit.
      eapply callee_frame_respects_protected_set.
      exact Hwf_frame.
      rewrite Hframe_sig. exact Hall_readonly.
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
    specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty_call Hget_y0).
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
      eapply method_signature_consistent_subtype with (C := rc_obj) (D := sctype Ty_call) (m := mindex); eauto.
    }
    rewrite Hmsigeq in Hmethodbody_typing.
    inversion Hmt_sub; subst; try (rewrite <- H1 in Hmethodbody_typing); exact Hmethodbody_typing.
    have Hsubset := reachable_locations_subset_reachable_from_method_frame CT h ly vals.
    rewrite <- HeqrΓmethodinit in Hsubset.
    unfold Ensembles.Included in Hsubset.
    exact (Hsubset loc_arg HinP).
  }
Qed.

(** Public TS guarantee with final-object existence and runtime type derived
    from the successful call evaluation. *)
Theorem ConcreteImmutability :
  forall CT sΓ rΓ h stmt rΓ' h' sΓ' x y mindex Ty mdef zs vals ly
         loc_arg C anyrq vals_arg f
    (Hstmt : stmt = (SCall x mindex y zs))
    (Hstatic_type : static_getType sΓ y = Some Ty)
    (Hmethod_lookup : FindMethodWithName CT (sctype Ty) mindex mdef)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ ConcreteImm stmt sΓ')
    (Heval : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h')
    (Hget_y : runtime_getVal rΓ y = Some (Iot ly))
    (Hget_zs : runtime_lookup_list rΓ zs = Some vals)
    (HinP: Ensembles.In Loc (reachable_locations_from_vals CT h (Iot ly :: vals)) loc_arg)
    (Harg_obj : runtime_getObj h loc_arg = Some (mkObj (mkruntime_type anyrq C) vals_arg))
    (Hall_readonly : all_params_safe (msignature mdef)),
    exists vals_arg',
      runtime_getObj h' loc_arg = Some (mkObj (mkruntime_type anyrq C) vals_arg') /\
      nth_error vals_arg f = nth_error vals_arg' f.
Proof.
  intros CT sΓ rΓ h stmt rΓ' h' sΓ' x y mindex Ty mdef zs vals ly
    loc_arg C anyrq vals_arg f Hstmt Hstatic_type Hmethod_lookup Hwf Htyping
    Heval Hget_y Hget_zs HinP Harg_obj Hall_readonly.
  destruct (runtime_preserves_r_type_heap CT rΓ h loc_arg
    (mkruntime_type anyrq C) h' vals_arg stmt rΓ' Harg_obj Heval)
    as [vals_arg' Harg_obj'].
  exists vals_arg'. split; [exact Harg_obj'|].
  eapply ConcreteImmutability_with_end; eauto.
Qed.
