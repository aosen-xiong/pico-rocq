Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation.
Require Import Properties DeepImmutability Reachability Preservation ReadonlyHelper ReadonlyNoMutation ReadonlySafety.
Require Import PotentialCapability ProtectedFieldPreservation.
From Stdlib Require Import List.
From Stdlib Require String.
Import ListNotations.

(** Concrete immutability is an instance of structural protected-field
    preservation in which every field is protected. *)
Lemma deep_concrete_immutability_preservation:
  forall CT sΓ rΓ h stmt rΓ' h' sΓ' l C anyrq vals vals' f
    (Hconfined : env_respects_protected_set
      (reachable_locations_from_initial_env CT h rΓ) sΓ rΓ)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ ConcreteImm stmt sΓ')
    (Heval : eval_stmt OK
      (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK
      (reachable_locations_from_initial_env CT h rΓ) rΓ' h')
    (Hlocalset : Ensembles.In Loc
      (reachable_locations_from_initial_env CT h rΓ) l)
    (Hobj : runtime_getObj h l =
      Some (mkObj (mkruntime_type anyrq C) vals))
    (Hobj' : runtime_getObj h' l =
      Some (mkObj (mkruntime_type anyrq C) vals')),
  nth_error vals f = nth_error vals' f.
Proof.
  intros.
  have Hinitial := initial_potential_live_history CT sΓ rΓ h
    Hwf Hconfined.
  eapply successful_stmt_preserves_protected_field with
    (authority := Imm_r) (stack := [])
    (Z := reachable_locations_from_initial_env CT h rΓ)
    (cutoff := dom h); eauto.
  - split; discriminate.
  - right. right. right. reflexivity.
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
    eapply eval_stmt_protected_set_irrelevant. exact Heval_body.
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
    eapply eval_stmt_protected_set_irrelevant. exact Heval_body.
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
  destruct (runtime_preserves_r_type_heap (reachable_locations_from_initial_env CT h rΓ) CT rΓ h loc_arg
    (mkruntime_type anyrq C) h' vals_arg stmt rΓ' Harg_obj Heval)
    as [vals_arg' Harg_obj'].
  exists vals_arg'. split; [exact Harg_obj'|].
  eapply ConcreteImmutability_with_end; eauto.
Qed.
