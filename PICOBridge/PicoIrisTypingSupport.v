From iris.program_logic Require Import weakestpre ownp adequacy.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import lib.excl_auth.
From iris.base_logic Require Import own.

Require Import Syntax Helpers Typing Subtyping Bigstep Properties Preservation
  ViewpointAdaptation.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage
  PICOBridge.PicoIrisCoreWP.
Require Import Core.GenericCacheProtocol Core.CacheLRVerticalSlice.
Require Import Iris.GenericCacheGhostState Iris.IrisSemanticBridge.


(** * PICO Iris Typing Support

    This file contains only pure typed-runtime value and environment facts
    shared by the typing-directed and SemImm developments.  It deliberately
    contains no statement, method, contract, or adequacy interpretation. *)

Section pico_typing_support.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table).
  Context `{!irisGS_gen hlc (pico_core_language CT) Σ}.

(** Public state interpretation boundary for the new core language.  The
    concrete Iris [state_interp] remains abstract, but LR rules can name the
    pure agreement fact between the ordinary PICO heap and the weak
    field-history state. *)
  Definition pico_core_state_agreeI (sigma : pico_core_state) : iProp Σ :=
    ⌜heap_wm_type_agree (pcs_heap sigma) (pcs_weak sigma)⌝.

  (** Semantic value interpretation for the heap-based PICO preservation
      theorem.  Null remains permissive, integers must inhabit [TInt], and
      object references must satisfy the usual PICO runtime typing relation over
      reference bases. *)
  Definition pico_typed_runtime_value
      (h : heap) (qcontext : q_r) (T : qualified_type)
      (v : Syntax.value) : Prop :=
    match v with
    | Null_a => True
    | Int _ => sbase T = TInt
    | Iot loc =>
        match r_type h loc with
        | Some rqt =>
            base_subtype CT (TRef (rctype rqt)) (sbase T) /\
            qualifier_typable_context (rqtype rqt) (sqtype T) qcontext
        | None => False
        end
    end.

  Definition pico_typed_runtime_valueI
      (h : heap) (qcontext : q_r) (T : qualified_type)
      (v : Syntax.value) : iProp Σ :=
    ⌜pico_typed_runtime_value h qcontext T v⌝.

(** Runtime environments satisfy a static environment when PICO's
    well-formed-runtime-configuration predicate relates them. *)
  Definition pico_typed_runtime_env
      (sΓ : s_env) (rΓ : r_env) (h : heap) : Prop :=
    exists qcontext receiver,
      wf_r_config CT sΓ rΓ h /\
      get_this_var_mapping (vars rΓ) = Some receiver /\
      r_muttype h receiver = Some qcontext.

  Definition pico_typed_runtime_envI
      (sΓ : s_env) (rΓ : r_env) (h : heap) : iProp Σ :=
    ⌜pico_typed_runtime_env sΓ rΓ h⌝.

  Lemma pico_typed_runtime_env_wf_config :
    forall sΓ rΓ h
      (Henv : pico_typed_runtime_env sΓ rΓ h),
      wf_r_config CT sΓ rΓ h.
  Proof.
    intros sΓ rΓ h Henv.
    destruct Henv as (qcontext & receiver & Hwf & _).
    exact Hwf.
  Qed.

  Lemma pico_typed_runtime_env_receiver :
    forall sΓ rΓ h
      (Henv : pico_typed_runtime_env sΓ rΓ h),
      exists qcontext receiver,
        get_this_var_mapping (vars rΓ) = Some receiver /\
        r_muttype h receiver = Some qcontext.
  Proof.
    intros sΓ rΓ h Henv.
    destruct Henv as (qcontext & receiver & _ & Hthis & Hrmut).
    exists qcontext, receiver.
    auto.
  Qed.

  Lemma pico_typed_runtime_env_runtime_lookup :
    forall sΓ rΓ h x T
      (Henv : pico_typed_runtime_env sΓ rΓ h)
      (Hstatic : static_getType sΓ x = Some T),
      exists v, runtime_getVal rΓ x = Some v.
  Proof.
    intros sΓ rΓ h x T Henv Hstatic.
    pose proof (pico_typed_runtime_env_wf_config sΓ rΓ h Henv) as Hwf.
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [_ [_ [Hlen _]]]]].
    assert (Hx_dom : x < dom sΓ).
    { eapply static_getType_dom; eauto. }
    assert (Hx_rdom : x < dom (vars rΓ)).
    { rewrite <- Hlen. exact Hx_dom. }
    destruct (runtime_getVal rΓ x) as [v |] eqn:Hlookup.
    - exists v.
      reflexivity.
    - apply runtime_getVal_not_dom in Hlookup.
      lia.
  Qed.

  Lemma pico_typed_runtime_env_local_runtime_absent :
    forall sΓ rΓ h x
      (Henv : pico_typed_runtime_env sΓ rΓ h)
      (Hstatic_none : static_getType sΓ x = None),
      runtime_getVal rΓ x = None.
  Proof.
    intros sΓ rΓ h x Henv Hstatic_none.
    pose proof (pico_typed_runtime_env_wf_config sΓ rΓ h Henv) as Hwf.
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [_ [_ [Hlen _]]]]].
    apply static_getType_not_dom in Hstatic_none.
    apply nth_error_None.
    unfold runtime_getVal.
    rewrite <- Hlen.
    exact Hstatic_none.
  Qed.

  Lemma pico_typed_runtime_env_after_local :
    forall sΓ mt T x sΓ' rΓ h
      (Htyping : stmt_typing CT sΓ mt (SLocal T x) sΓ')
      (Henv : pico_typed_runtime_env sΓ rΓ h),
      pico_typed_runtime_env
        sΓ'
        (set_vars rΓ (vars rΓ ++ [default_value T]))
        h.
  Proof.
    intros sΓ mt T x sΓ' rΓ h Htyping Henv.
    inversion Htyping; subst.
    destruct Henv as (qcontext & receiver & Hcfg & Hrecv & Hrmut).
    pose proof
      (pico_typed_runtime_env_local_runtime_absent
        sΓ rΓ h x
        (ex_intro _ qcontext
          (ex_intro _ receiver (conj Hcfg (conj Hrecv Hrmut))))
        Hnone) as Hnone_rt.
    exists qcontext, receiver.
    split.
    - eapply (@preservation_local_ok
        (reachable_locations_from_initial_env CT h rΓ)); eauto.
      eapply SBS_Local.
      exact Hnone_rt.
    - split.
      + rewrite <- Hrecv.
        apply get_this_var_mapping_update_vars_app_default.
      + exact Hrmut.
  Qed.

  Lemma pico_typed_runtime_env_after_varass_null :
    forall sΓ mt x sΓ' rΓ h
      (Htyping : stmt_typing CT sΓ mt (SVarAss x ENull) sΓ')
      (Henv : pico_typed_runtime_env sΓ rΓ h),
      pico_typed_runtime_env
        sΓ'
        (set_vars rΓ (update x Null_a (vars rΓ)))
        h.
  Proof.
    intros sΓ mt x sΓ' rΓ h Htyping Henv.
    inversion Htyping; subst.
    destruct
      (pico_typed_runtime_env_runtime_lookup
        _ rΓ h x Tx Henv Hget_x)
      as (old_v & Hold).
    destruct Henv as (qcontext & receiver & Hcfg & Hrecv & Hrmut).
    exists qcontext, receiver.
    split.
    - eapply (@preservation_varass_ok
        (reachable_locations_from_initial_env CT h rΓ)); eauto.
      eapply SBS_Assign.
      + exact Hold.
      + apply EBS_Null.
    - split.
      + rewrite get_this_var_mapping_update_vars_nonzero; eauto.
      + exact Hrmut.
  Qed.

  Lemma pico_typed_runtime_env_after_varass_int :
    forall sΓ mt x n sΓ' rΓ h
      (Htyping : stmt_typing CT sΓ mt (SVarAss x (EInt n)) sΓ')
      (Henv : pico_typed_runtime_env sΓ rΓ h),
      pico_typed_runtime_env
        sΓ'
        (set_vars rΓ (update x (Int n) (vars rΓ)))
        h.
  Proof.
    intros sΓ mt x n sΓ' rΓ h Htyping Henv.
    inversion Htyping; subst.
    destruct
      (pico_typed_runtime_env_runtime_lookup
        _ rΓ h x Tx Henv Hget_x)
      as (old_v & Hold).
    destruct Henv as (qcontext & receiver & Hcfg & Hrecv & Hrmut).
    exists qcontext, receiver.
    split.
    - eapply (@preservation_varass_ok
        (reachable_locations_from_initial_env CT h rΓ)); eauto.
      eapply SBS_Assign.
      + exact Hold.
      + apply EBS_Int.
    - split.
      + rewrite get_this_var_mapping_update_vars_nonzero; eauto.
      + exact Hrmut.
  Qed.

  Lemma pico_typed_runtime_env_after_varass_var :
    forall sΓ mt x y sΓ' rΓ h
      (Htyping : stmt_typing CT sΓ mt (SVarAss x (EVar y)) sΓ')
      (Henv : pico_typed_runtime_env sΓ rΓ h),
      exists val_y,
        runtime_getVal rΓ y = Some val_y /\
        pico_typed_runtime_env
          sΓ'
          (set_vars rΓ (update x val_y (vars rΓ)))
          h.
  Proof.
    intros sΓ mt x y sΓ' rΓ h Htyping Henv.
    inversion Htyping; subst.
    inversion Htype_e; subst.
    destruct
      (pico_typed_runtime_env_runtime_lookup
        _ rΓ h x Tx Henv Hget_x)
      as (old_v & Hold).
    destruct
      (pico_typed_runtime_env_runtime_lookup
        _ rΓ h y Te Henv Hget)
      as (val_y & Hy).
    exists val_y.
    split; [exact Hy |].
    destruct Henv as (qcontext & receiver & Hcfg & Hrecv & Hrmut).
    exists qcontext, receiver.
    split.
    - eapply (@preservation_varass_ok
        (reachable_locations_from_initial_env CT h rΓ)); eauto.
      eapply SBS_Assign.
      + exact Hold.
      + eapply EBS_Val.
        exact Hy.
    - split.
      + rewrite get_this_var_mapping_update_vars_nonzero; eauto.
      + exact Hrmut.
  Qed.

  Lemma pico_typed_runtime_env_update_value :
    forall sΓ rΓ h x Tx v
      (Henv : pico_typed_runtime_env sΓ rΓ h)
      (Hget_x : static_getType sΓ x = Some Tx)
      (Hnot_rcv : x <> 0)
      (Hvalue :
        forall qcontext receiver,
          get_this_var_mapping (vars rΓ) = Some receiver ->
          r_muttype h receiver = Some qcontext ->
          pico_typed_runtime_value h qcontext Tx v),
      pico_typed_runtime_env
        sΓ
        (set_vars rΓ (update x v (vars rΓ)))
        h.
  Proof.
    intros sΓ rΓ h x Tx v Henv Hget_x Hnot_rcv Hvalue.
    destruct Henv as (qcontext & receiver & Hcfg & Hrecv & Hrmut).
    unfold wf_r_config in Hcfg.
    destruct Hcfg as
      (Hclass_table & Hheap & Hrenv & Hsenv & Hlen & Hcorr).
    exists qcontext, receiver.
    split.
    - unfold wf_r_config.
      split; [exact Hclass_table |].
      split; [exact Hheap |].
      split.
      + unfold wf_renv in *.
        destruct Hrenv as (Hvars_nonempty & Hreceiver & Hvars_wf).
        split.
        * simpl.
          rewrite update_length.
          exact Hvars_nonempty.
        * split.
          -- destruct Hreceiver as (receiver0 & Hreceiver0 & Hreceiver_dom).
             exists receiver0.
             split.
             ++ rewrite get_this_var_mapping_update_vars_nonzero; eauto.
             ++ exact Hreceiver_dom.
          -- apply Forall_update.
             ++ exact Hvars_wf.
             ++ destruct v as [| loc | n]; simpl; auto.
                specialize (Hvalue qcontext receiver Hrecv Hrmut).
                simpl in Hvalue.
                unfold r_type in Hvalue.
                destruct (runtime_getObj h loc) as [o |] eqn:Hobj;
                  [exact I | contradiction].
             ++ rewrite <- Hlen.
                eapply static_getType_dom; eauto.
      + split; [exact Hsenv |].
        split.
        * simpl.
          rewrite update_length.
          exact Hlen.
        * intros receiver' qcontext' Hrecv' Hrmut' i Hi sqt Hnth.
        assert (Hrecv_eq : receiver' = receiver).
        {
          rewrite get_this_var_mapping_update_vars_nonzero in Hrecv';
            [| exact Hnot_rcv].
          rewrite Hrecv in Hrecv'.
          inversion Hrecv'; reflexivity.
        }
        subst receiver'.
        assert (Hqcontext_eq : qcontext' = qcontext).
        {
          rewrite Hrmut in Hrmut'.
          inversion Hrmut'; reflexivity.
        }
        subst qcontext'.
        destruct (Nat.eq_dec i x) as [Heq | Hneq].
        -- subst i.
          unfold runtime_getVal.
          simpl.
          rewrite update_same.
          ++ assert (Hsqt_eq : sqt = Tx).
             {
               unfold static_getType in Hget_x.
               rewrite Hget_x in Hnth.
               inversion Hnth; reflexivity.
             }
             subst sqt.
             specialize (Hvalue qcontext receiver Hrecv Hrmut).
             destruct v as [| loc | n].
             ** exact I.
             ** unfold wf_r_typable.
                simpl in Hvalue.
                destruct (r_type h loc) as [rqt |] eqn:Hrtype;
                  [exact Hvalue | contradiction].
             ** exact Hvalue.
          ++ rewrite <- Hlen.
             exact Hi.
          -- unfold runtime_getVal.
          simpl.
          rewrite update_diff; [| intro Heq; apply Hneq; symmetry; exact Heq].
          specialize (Hcorr receiver qcontext Hrecv Hrmut i Hi sqt Hnth).
          unfold runtime_getVal in Hcorr.
          destruct (nth_error (vars rΓ) i) as [old_v |] eqn:Hold;
            [| exact Hcorr].
          destruct old_v as [| loc | n].
          ++ exact Hcorr.
          ++ simpl.
             eapply wf_r_typable_env_independent_simple.
             exact Hcorr.
          ++ exact Hcorr.
    - split.
      + rewrite get_this_var_mapping_update_vars_nonzero; eauto.
      + exact Hrmut.
  Qed.

  Lemma pico_typed_runtime_value_from_updated_env :
    forall sΓ caller h x Tx retval
      (Henv_next :
        pico_typed_runtime_env
          sΓ
          (set_vars caller (update x retval (vars caller)))
          h)
      (Hget_x : static_getType sΓ x = Some Tx)
      (Hnot_rcv : x <> 0),
      forall qcontext receiver,
        get_this_var_mapping (vars caller) = Some receiver ->
        r_muttype h receiver = Some qcontext ->
        pico_typed_runtime_value h qcontext Tx retval.
  Proof.
    intros sΓ caller h x Tx retval Henv_next Hget_x Hnot_rcv
      qcontext receiver Hthis Hrmut.
    destruct Henv_next as
      (qcontext_next & receiver_next & Hcfg_next & Hthis_next & Hrmut_next).
    unfold wf_r_config in Hcfg_next.
    destruct Hcfg_next as
      (_Hclass & _Hheap & _Hrenv & _Hsenv & Hlen & Hcorr).
    assert (Hthis_update :
      get_this_var_mapping
        (vars (set_vars caller (update x retval (vars caller)))) =
      get_this_var_mapping (vars caller)).
    {
      simpl.
      rewrite get_this_var_mapping_update_vars_nonzero; eauto.
    }
    assert (receiver_next = receiver).
    {
      rewrite Hthis_update in Hthis_next.
      rewrite Hthis in Hthis_next.
      inversion Hthis_next.
      reflexivity.
    }
    subst receiver_next.
    assert (qcontext_next = qcontext).
    {
      rewrite Hrmut in Hrmut_next.
      inversion Hrmut_next.
      reflexivity.
    }
    subst qcontext_next.
    assert (Hx_dom : x < dom sΓ).
    { eapply static_getType_dom; eauto. }
    specialize
      (Hcorr receiver qcontext Hthis_next Hrmut_next x Hx_dom Tx Hget_x).
    unfold runtime_getVal in Hcorr.
    simpl in Hcorr.
    rewrite update_same in Hcorr.
    - destruct retval as [| loc | n]; simpl.
      + exact I.
      + unfold wf_r_typable in Hcorr.
        unfold pico_typed_runtime_value.
        destruct (r_type h loc) as [rqt |] eqn:Hrtype;
          [exact Hcorr | contradiction].
      + exact Hcorr.
    - simpl in Hlen.
      rewrite <- (@update_length Syntax.value x retval (vars caller)).
      rewrite <- Hlen.
      exact Hx_dom.
  Qed.

  Lemma pico_typed_runtime_field_value_exists :
    forall sΓ rΓ h loc o f a
      (Henv : pico_typed_runtime_env sΓ rΓ h)
      (Hobj : runtime_getObj h loc = Some o)
      (Hassign : sf_assignability_rel CT (rctype (rt_type o)) f a),
      exists old_v, getVal (fields_map o) f = Some old_v.
  Proof.
    intros sΓ rΓ h loc o f a Henv Hobj Hassign.
    destruct Henv as (_qcontext & _receiver & Hcfg & _Hthis & _Hrmut).
    unfold wf_r_config in Hcfg.
    destruct Hcfg as (_Hclass_table & Hheap & _Hrenv & _Hsenv & _Hlen & _Hcorr).
    assert (Hloc_dom : loc < dom h).
    { eapply runtime_getObj_dom; eauto. }
    specialize (Hheap loc Hloc_dom).
    unfold wf_obj in Hheap.
    rewrite Hobj in Hheap.
    destruct Hheap as (_Hrtypeuse & field_defs & Hcollect & Hlen_fields & _Hfields_wf).
    unfold sf_assignability_rel in Hassign.
    destruct Hassign as (fdef & Hlookup & _Hassignability).
    inversion Hlookup as [? ? fields ? ? Hcollect_lookup Hget]; subst.
    assert (fields = field_defs).
    {
      eapply collect_fields_deterministic_rel; eauto.
    }
    subst fields.
    assert (Hf_dom : f < dom (fields_map o)).
    {
      rewrite Hlen_fields.
      eapply gget_dom; eauto.
    }
    eapply getVal_Some; eauto.
  Qed.

  Lemma pico_typed_runtime_env_after_fldwrite_success :
    forall sΓ mt x f y sΓ' rΓ h h' loc_x o a val_y
      (Htyping : stmt_typing CT sΓ mt (SFldWrite x f y) sΓ')
      (Henv : pico_typed_runtime_env sΓ rΓ h)
      (Hx : runtime_getVal rΓ x = Some (Iot loc_x))
      (Hobj : runtime_getObj h loc_x = Some o)
      (Hassign : sf_assignability_rel CT (rctype (rt_type o)) f a)
      (Hy : runtime_getVal rΓ y = Some val_y)
      (Hassignable :
        runtime_vpa_assignability (rqtype (rt_type o)) a = Assignable)
      (Hheap_update : h' = update_field h loc_x f val_y),
      pico_typed_runtime_env sΓ' rΓ h'.
  Proof.
    intros sΓ mt x f y sΓ' rΓ h h' loc_x o a val_y
      Htyping Henv Hx Hobj Hassign Hy Hassignable Hheap_update.
    destruct Henv as (qcontext & receiver & Hcfg & Hthis & Hrmut).
    destruct
      (pico_typed_runtime_field_value_exists
        sΓ rΓ h loc_x o f a
        (ex_intro _ qcontext
          (ex_intro _ receiver (conj Hcfg (conj Hthis Hrmut))))
        Hobj Hassign)
      as (old_field_v & Hfield).
    exists qcontext, receiver.
    split.
    - eapply (@preservation_fldwrite_ok
        (reachable_locations_from_initial_env CT h rΓ)); eauto.
      eapply SBS_FldWrite; eauto.
    - split.
      + exact Hthis.
      + subst h'.
        rewrite r_muttype_update_field_preserve.
        exact Hrmut.
  Qed.

  Lemma stmt_typing_fldwrite_result_env :
    forall sΓ mt x f y sΓ'
      (Htyping : stmt_typing CT sΓ mt (SFldWrite x f y) sΓ'),
      sΓ' = sΓ.
  Proof.
    intros sΓ mt x f y sΓ' Htyping.
    inversion Htyping; reflexivity.
  Qed.

  Lemma pico_typed_runtime_env_after_new_success :
    forall sΓ mt x qc C args sΓ' rΓ h h' loc_this vals
      qthisr qadapted o
      (Htyping : stmt_typing CT sΓ mt (SNew x qc C args) sΓ')
      (Henv : pico_typed_runtime_env sΓ rΓ h)
      (Hthis : runtime_getVal rΓ 0 = Some (Iot loc_this))
      (Hargs : runtime_lookup_list rΓ args = Some vals)
      (Hmut : r_muttype h loc_this = Some qthisr)
      (Hadapt : vpa_mutability_object_creation qthisr qc = qadapted)
      (Hobj : o = mkObj (mkruntime_type qadapted C) vals)
      (Hheap : h' = h ++ [o]),
      pico_typed_runtime_env
        sΓ'
        (set_vars rΓ (update x (Iot (dom h)) (vars rΓ)))
        h'.
  Proof.
    intros sΓ mt x qc C args sΓ' rΓ h h' loc_this vals
      qthisr qadapted o Htyping Henv Hruntime_this Hargs
      Hmut Hadapt Hobj Hheap.
    pose proof Htyping as Htyping_copy.
    inversion Htyping; subst.
    destruct Henv as (qcontext & receiver & Hcfg & Hrecv & Hrmut).
    exists qcontext, receiver.
    split.
    - eapply (@preservation_new_ok
        (reachable_locations_from_initial_env CT h rΓ)); eauto.
      eapply SBS_New; eauto.
    - split.
      + rewrite get_this_var_mapping_update_vars_nonzero; eauto.
      + assert (Hreceiver_dom : receiver < dom h).
        {
          unfold r_muttype in Hrmut.
          destruct (runtime_getObj h receiver) as [robj |] eqn:Hreceiver_obj;
            [| discriminate].
          eapply runtime_getObj_dom; eauto.
        }
        rewrite r_muttype_app_preserve_old; eauto.
  Qed.

  Lemma wf_renv_preserved_by_eval_heap :
    forall rΓ caller h s rΓ' h'
      (Hrenv : wf_renv CT caller h)
      (Heval :
        eval_stmt OK (reachable_locations_from_initial_env CT h rΓ)
          CT rΓ h s OK (reachable_locations_from_initial_env CT h rΓ)
          rΓ' h'),
      wf_renv CT caller h'.
  Proof.
    intros rΓ caller h s rΓ' h' Hrenv Heval.
    unfold wf_renv in Hrenv |- *.
    destruct Hrenv as (Hlen & Hthis & Hvals).
    split.
    - exact Hlen.
    - split.
      + destruct Hthis as (receiver & Hreceiver & Hreceiver_dom).
        exists receiver.
        split.
        * exact Hreceiver.
        * pose proof
            (eval_stmt_preserves_heap_domain_simple
              CT rΓ h s rΓ' h' Heval) as Hdom.
          lia.
      + eapply Forall_impl; [| exact Hvals].
        intros v Hv.
        destruct v as [| loc | n]; try exact I.
        destruct (runtime_getObj h loc) as [obj |] eqn:Hobj;
          [| contradiction].
        assert (Hloc_dom : loc < dom h).
        { eapply runtime_getObj_dom; eauto. }
        assert (Hrtype : r_type h loc = Some (rt_type obj)).
        {
          unfold r_type.
          rewrite Hobj.
          reflexivity.
        }
        pose proof
          (eval_stmt_preserves_r_type
            CT rΓ h s rΓ' h' loc (rt_type obj)
            Heval Hrtype Hloc_dom) as Hrtype'.
        unfold r_type in Hrtype'.
        destruct (runtime_getObj h' loc) as [obj' |] eqn:Hobj';
          [exact I | discriminate].
  Qed.

  Lemma wf_r_typable_preserved_by_eval_heap :
    forall rΓ h s rΓ' h' caller loc T qcontext
      (Htypable : wf_r_typable CT caller h loc T qcontext)
      (Heval :
        eval_stmt OK (reachable_locations_from_initial_env CT h rΓ)
          CT rΓ h s OK (reachable_locations_from_initial_env CT h rΓ)
          rΓ' h'),
      wf_r_typable CT caller h' loc T qcontext.
  Proof.
    intros rΓ h s rΓ' h' caller loc T qcontext Htypable Heval.
    unfold wf_r_typable in Htypable |- *.
    destruct (r_type h loc) as [rqt |] eqn:Hrtype;
      [| contradiction].
    assert (Hloc_dom : loc < dom h).
    { eapply r_type_dom; eauto. }
    pose proof
      (eval_stmt_preserves_r_type
        CT rΓ h s rΓ' h' loc rqt Heval Hrtype Hloc_dom)
      as Hrtype'.
    rewrite Hrtype'.
    exact Htypable.
  Qed.

  Lemma pico_typed_runtime_env_preserved_by_eval_heap :
    forall sΓ caller h rΓ s rΓ' h'
      (Henv : pico_typed_runtime_env sΓ caller h)
      (Hheap' : wf_heap CT h')
      (Heval :
        eval_stmt OK (reachable_locations_from_initial_env CT h rΓ)
          CT rΓ h s OK (reachable_locations_from_initial_env CT h rΓ)
          rΓ' h'),
      pico_typed_runtime_env sΓ caller h'.
  Proof.
    intros sΓ caller h rΓ s rΓ' h' Henv Hheap' Heval.
    destruct Henv as (qcontext & receiver & Hcfg & Hthis & Hrmut).
    unfold wf_r_config in Hcfg.
    destruct Hcfg as
      (Hclass & _Hheap & Hrenv & Hsenv & Hlen & Hcorr).
    assert (Hreceiver_dom : receiver < dom h).
    {
      unfold r_muttype in Hrmut.
      destruct (runtime_getObj h receiver) as [obj |] eqn:Hobj;
        [eapply runtime_getObj_dom; eauto | discriminate].
    }
    assert (Hrmut' : r_muttype h' receiver = Some qcontext).
    {
      eapply eval_stmt_preserves_r_muttype; eauto.
    }
    exists qcontext, receiver.
    split.
    - unfold wf_r_config.
      split.
      + exact Hclass.
      + split.
        * exact Hheap'.
        * split.
          -- eapply wf_renv_preserved_by_eval_heap; eauto.
          -- split.
             ++ exact Hsenv.
             ++ split.
                ** exact Hlen.
                ** intros receiver' qcontext' Hthis' Hrmut'' i Hi sqt Hnth.
        assert (receiver' = receiver) by congruence.
        subst receiver'.
        assert (qcontext' = qcontext) by congruence.
        subst qcontext'.
        specialize (Hcorr receiver qcontext Hthis Hrmut i Hi sqt Hnth).
        destruct (runtime_getVal caller i) as [v |] eqn:Hval;
          [| exact Hcorr].
        destruct v as [| loc | n].
        --- exact Hcorr.
        --- eapply wf_r_typable_preserved_by_eval_heap; eauto.
        --- exact Hcorr.
    - split.
      + exact Hthis.
      + exact Hrmut'.
  Qed.

End pico_typing_support.
