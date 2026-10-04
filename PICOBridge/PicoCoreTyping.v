From Stdlib Require Import List Lia.
From Stdlib Require Import Program.Equality.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping Bigstep Properties Preservation
  ViewpointAdaptation.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoCoreLanguage
  PICOBridge.PicoCoreInvariant PICOBridge.PicoCoreTypingSupport.

(** * Typing Lemmas for the Core Machine

    Continuation typing, the typed postcondition of each kind of machine
    step, the typing of call frames and returns, and the stability of typing
    under heap growth. *)

Section pico_typing_fundamental_ownp_pure.
  Context `{Hmem : CacheMemoryModel}.
  Context `{Hprogress : CacheMemoryModelProgress}.
  Context (CT : class_table).

  Lemma pico_core_typed_env_real_lr_env :
    forall sGamma rGamma h
      (Henv : pico_core_typed_env CT sGamma rGamma h),
      pico_typed_runtime_env CT sGamma rGamma h.
  Proof.
    intros sGamma rGamma h Henv.
    destruct Henv as
      (qcontext & receiver & Hwf & Hreceiver & Hqcontext & _).
    exists qcontext, receiver.
    auto.
  Qed.

  (** Typed continuations record the static environment expected by each
      residual frame.  In particular, a call frame records the callee return
      slot and the caller assignment target, so [Skip] can restore a caller
      without an untyped return-value premise. *)
  Inductive pico_core_cont_typed :
      heap -> method_scope -> s_env -> pico_core_cont -> Prop :=
    | PCCT_Nil : forall h mt sGamma,
        pico_core_cont_typed h mt sGamma []
    | PCCT_Seq : forall h mt sGamma sGamma' s2 K,
        stmt_typing CT sGamma mt s2 sGamma' ->
        pico_core_cont_typed h mt sGamma' K ->
        pico_core_cont_typed h mt sGamma (KSeq s2 :: K)
    | PCCT_Call : forall h mt_callee sGamma_callee
        caller mt_caller sGamma_caller x ret K Tret Tx,
        static_getType sGamma_callee ret = Some Tret ->
        static_getType sGamma_caller x = Some Tx ->
        qualified_type_subtype CT Tret Tx ->
        pico_core_typed_env CT sGamma_caller caller h ->
        pico_core_cont_typed h mt_caller sGamma_caller K ->
        pico_core_cont_typed h mt_callee sGamma_callee
          (KCall caller x ret :: K).

  (** Uniform one-statement postcondition used by the typing-directed WP.
      Successful statements expose a typed output environment at [SSkip];
      exceptional statements expose the corresponding completed core value.
      Every branch retains the full LR state, including weak-read typing. *)
  Inductive pico_core_stmt_post
      (sGamma' : s_env) (K : pico_core_cont) :
      pico_core_expr -> pico_core_state -> Prop :=
    | PCSP_Ok : forall rGamma V state,
        pico_core_typed_env CT sGamma' rGamma (pcs_heap state) ->
        pico_core_lr_state CT state ->
        pico_core_stmt_post sGamma' K
          (CoreRun rGamma SSkip V K) state
    | PCSP_NPE : forall rGamma V state,
        pico_core_lr_state CT state ->
        pico_core_stmt_post sGamma' K
          (CoreDone NPE rGamma V) state
    | PCSP_Mutation : forall rGamma V state,
        pico_core_lr_state CT state ->
        pico_core_stmt_post sGamma' K
          (CoreDone MUTATIONEXP rGamma V) state.

  Lemma pico_core_typed_skip_call_ready :
    forall h mt sGamma rGamma caller x ret K
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hcont :
        pico_core_cont_typed h mt sGamma (KCall caller x ret :: K)),
      exists retval, runtime_getVal rGamma ret = Some retval.
  Proof.
    intros h mt sGamma rGamma caller x ret K Henv Hcont.
    inversion Hcont; subst.
    match goal with
    | Hret : static_getType sGamma ret = Some ?Tret |- _ =>
        destruct
          (pico_core_typed_env_lookup
            CT sGamma rGamma h ret Tret Henv Hret)
          as (qcontext & retval & Hretval & _);
        exists retval;
        exact Hretval
    end.
  Qed.

  Lemma pico_core_typed_value_env_independent :
    forall h qcontext T v,
      pico_core_typed_value CT h qcontext T v ->
      pico_core_typed_value CT h qcontext T v.
  Proof.
    intros h qcontext T v Htyped.
    destruct v as [|loc|n]; simpl in *.
    - auto.
    - exact Htyped.
    - auto.
  Qed.

  Lemma pico_core_typed_value_real_lr_value :
    forall h qcontext T v,
      pico_core_typed_value CT h qcontext T v ->
      pico_typed_runtime_value CT h qcontext T v.
  Proof.
    intros h qcontext T v Htyped.
    destruct v as [|loc|n]; simpl in *; auto.
  Qed.

  Lemma pico_core_typed_value_subtype :
    forall h qcontext T1 T2 v
      (Hwf_CT : wf_class_table CT)
      (Hwf_heap : wf_heap CT h)
      (Htyped : pico_core_typed_value CT h qcontext T1 v)
      (Hsub : qualified_type_subtype CT T1 T2),
      pico_core_typed_value CT h qcontext T2 v.
  Proof.
	    intros h qcontext T1 T2 v Hwf_CT Hwf_heap Htyped Hsub.
	    destruct v as [|loc|n]; simpl in *.
	    - destruct Htyped as [C Hbase1].
	      pose proof
	        (qualified_type_subtype_base_subtype CT T1 T2 Hsub) as Hbase_sub.
	      rewrite Hbase1 in Hbase_sub.
	      destruct (base_subtype_from_ref CT C (sbase T2) Hbase_sub)
	        as [D [Hbase2 _]].
	      exists D.
	      exact Hbase2.
	    - eapply wf_r_typable_subtype; eauto.
	    - pose proof (qualified_type_subtype_base_subtype CT T1 T2 Hsub)
	        as Hbase_sub.
	      rewrite Htyped in Hbase_sub.
	      apply base_subtype_from_int in Hbase_sub.
	      exact Hbase_sub.
	  Qed.

  Lemma pico_core_subtype_preserves_reference :
    forall T1 T2,
      (exists C, sbase T1 = TRef C) ->
      qualified_type_subtype CT T1 T2 ->
      exists D, sbase T2 = TRef D.
  Proof.
    intros T1 T2 [C Hbase1] Hsub.
    pose proof
      (qualified_type_subtype_base_subtype CT T1 T2 Hsub) as Hbase_sub.
    rewrite Hbase1 in Hbase_sub.
    destruct (base_subtype_from_ref CT C (sbase T2) Hbase_sub)
      as [D [Hbase2 _]].
    eauto.
  Qed.

  Lemma pico_core_typed_value_heap_types_extend :
    forall h h' qcontext T v
      (Htyped : pico_core_typed_value CT h qcontext T v)
      (Hextend : pico_core_heap_types_extend h h'),
      pico_core_typed_value CT h' qcontext T v.
  Proof.
    intros h h' qcontext T v Htyped [_ Htypes].
    destruct v as [|loc|n]; simpl in *; auto.
    unfold wf_r_typable in *.
    destruct (r_type h loc) as [runtime_type |] eqn:Htype;
      try contradiction.
    rewrite (Htypes loc runtime_type Htype).
    exact Htyped.
  Qed.

  Lemma pico_core_r_muttype_heap_types_extend :
    forall h h' loc qcontext
      (Hextend : pico_core_heap_types_extend h h')
      (Hmut : r_muttype h loc = Some qcontext),
      r_muttype h' loc = Some qcontext.
  Proof.
    intros h h' loc qcontext [_ Htypes] Hmut.
    unfold r_muttype, r_type in *.
    destruct (runtime_getObj h loc) as [o |] eqn:Hobj;
      try discriminate.
    assert (Htype :
      (match runtime_getObj h loc with
       | Some old => Some (rt_type old)
       | None => None
       end) = Some (rt_type o)).
    { rewrite Hobj. reflexivity. }
    specialize (Htypes loc (rt_type o) Htype).
    destruct (runtime_getObj h' loc) as [o' |] eqn:Hobj';
      try discriminate.
    injection Htypes as Hruntime_type.
    rewrite Hruntime_type.
    exact Hmut.
  Qed.

  Lemma pico_core_wf_renv_heap_types_extend :
    forall rGamma h h'
      (Hrenv : wf_renv CT rGamma h)
      (Hextend : pico_core_heap_types_extend h h'),
      wf_renv CT rGamma h'.
  Proof.
    intros rGamma h h' Hrenv [Hlength Htypes].
    destruct Hrenv as [Hnonempty [[receiver [Hreceiver Hreceiver_dom]] Hvalues]].
    repeat split.
    - exact Hnonempty.
    - exists receiver.
      split; [exact Hreceiver | lia].
    - eapply Forall_impl; [| exact Hvalues].
      intros v Hv.
      destruct v as [|loc|n]; simpl in *; auto.
      destruct (runtime_getObj h loc) as [o |] eqn:Hobj;
        try contradiction.
      assert (Htype : r_type h loc = Some (rt_type o)).
      { unfold r_type. rewrite Hobj. reflexivity. }
      specialize (Htypes loc (rt_type o) Htype).
      unfold r_type in Htypes.
      destruct (runtime_getObj h' loc); simpl; auto.
      discriminate.
  Qed.

  Lemma pico_core_typed_env_heap_types_extend :
    forall sGamma rGamma h h'
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hextend : pico_core_heap_types_extend h h')
      (Hwf_heap' : wf_heap CT h'),
      pico_core_typed_env CT sGamma rGamma h'.
  Proof.
    intros sGamma rGamma h h' Henv Hextend Hwf_heap'.
    destruct Henv as
      (qcontext & receiver & Hwf & Hreceiver & Hmut & Hvalues).
    destruct Hwf as
      (Hwf_CT & Hwf_heap & Hwf_renv & Hwf_senv & Hlength & Hcorr).
    assert (Hwf_renv' : wf_renv CT rGamma h').
    {
      eapply pico_core_wf_renv_heap_types_extend; eauto.
    }
    assert (Hmut' : r_muttype h' receiver = Some qcontext).
    {
      eapply pico_core_r_muttype_heap_types_extend; eauto.
    }
    assert (Hwf' : wf_r_config CT sGamma rGamma h').
    {
      unfold wf_r_config.
      split; [exact Hwf_CT |].
      split; [exact Hwf_heap' |].
      split; [exact Hwf_renv' |].
      split; [exact Hwf_senv |].
      split; [exact Hlength |].
      intros receiver' qcontext' Hreceiver' Hmut_receiver'
          i Hi T Hstatic.
      assert (Hreceiver_eq : receiver' = receiver) by congruence.
      subst receiver'.
      assert (Hqcontext_eq : qcontext' = qcontext) by congruence.
      subst qcontext'.
      specialize (Hcorr receiver qcontext Hreceiver Hmut i Hi T Hstatic).
      destruct (runtime_getVal rGamma i) as [v |] eqn:Hruntime;
        try contradiction.
      destruct v as [|loc|n]; simpl in *; auto.
      change
        (pico_core_typed_value CT h' qcontext T (Iot loc)).
      eapply pico_core_typed_value_heap_types_extend; eauto.
    }
    exists qcontext, receiver.
    split; [exact Hwf' |].
    split; [exact Hreceiver |].
    split; [exact Hmut' |].
    intros x T Hstatic.
    destruct (Hvalues x T Hstatic) as (v & Hruntime & Htyped).
    exists v.
    split; [exact Hruntime |].
    eapply pico_core_typed_value_heap_types_extend; eauto.
  Qed.

  Lemma pico_core_cont_typed_heap_types_extend :
    forall h h' mt sGamma K,
      pico_core_cont_typed h mt sGamma K ->
      pico_core_heap_types_extend h h' ->
      wf_heap CT h' ->
      pico_core_cont_typed h' mt sGamma K.
  Proof.
    intros h h' mt sGamma K Hcont Hextend Hwf_heap'.
    induction Hcont.
    - constructor.
    - eapply PCCT_Seq.
      + exact H0.
      + eapply IHHcont; eauto.
    - eapply PCCT_Call; eauto.
      eapply pico_core_typed_env_heap_types_extend; eauto.
  Qed.

  Lemma pico_core_typed_resolved_method_static :
    forall sGamma sGamma' rGamma h mt x y m args
      loc C mdef vals
      (Htyping : stmt_typing CT sGamma mt (SCall x m y args) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hreceiver : runtime_getVal rGamma y = Some (Iot loc))
      (Hbase : r_basetype h loc = Some C)
      (Hfind : FindMethodWithName CT C m mdef)
      (Hargs : runtime_lookup_list rGamma args = Some vals),
	      exists Ty Cstatic argtypes mdef_static declaring_class,
	        static_getType sGamma y = Some Ty /\
	        sbase Ty = TRef Cstatic /\
	        static_getType_list sGamma args = Some argtypes /\
	        FindMethodWithName CT Cstatic m mdef_static /\
	        class_subtype CT C Cstatic /\
	        method_signature_refinement CT
	          (msignature mdef) (msignature mdef_static) /\
	        class_subtype CT C declaring_class /\
	        wf_method CT declaring_class mdef.
  Proof.
    intros sGamma sGamma' rGamma h mt x y m args
      loc C mdef vals Htyping Henv Hreceiver Hbase Hfind Hargs.
    destruct
	      (stmt_typing_call_static_components
	        CT sGamma sGamma' mt x y m args Htyping)
	      as (Ty & Cstatic & argtypes & mdef_static
	          & Hget_y & Href & Hget_args & Hfind_static).
    destruct
      (pico_core_typed_env_lookup
        CT sGamma rGamma h y Ty Henv Hget_y)
      as (qcontext & value_y & Hruntime_y & Htyped_y).
    assert (Hvalue_y : value_y = Iot loc) by congruence.
    subst value_y.
    unfold pico_core_typed_value, wf_r_typable in Htyped_y.
    unfold r_basetype in Hbase.
    destruct (runtime_getObj h loc) as [receiver_obj |] eqn:Hobj;
      try discriminate.
    injection Hbase as Hclass.
    subst C.
    unfold r_type in Htyped_y.
    rewrite Hobj in Htyped_y.
	    destruct Htyped_y as [Hsubtype Hqualifier].
	    destruct
	      (base_subtype_from_ref
	        CT (rctype (rt_type receiver_obj)) (sbase Ty) Hsubtype)
	      as [D0 [HbaseTy Hclass_sub]].
	    rewrite HbaseTy in Href.
	    inversion Href; subst D0.
    pose proof
      (pico_core_typed_env_wf_config CT sGamma rGamma h Henv)
      as Hconfig.
    destruct Hconfig as [Hwf_CT [Hwf_heap _]].
    assert (Hclass_dom : rctype (rt_type receiver_obj) < dom CT).
    {
      assert (Hbase' :
        r_basetype h loc = Some (rctype (rt_type receiver_obj))).
      { unfold r_basetype. rewrite Hobj. reflexivity. }
      exact
        (r_basetype_in_dom
          CT h loc (rctype (rt_type receiver_obj)) Hwf_heap Hbase').
    }
    destruct
      (method_lookup_in_wellformed_inherited
        CT (rctype (rt_type receiver_obj)) m mdef
        Hwf_CT Hclass_dom Hfind)
      as (declaring_class & declaring_def & Hdecl_sub &
          Hdecl_find & Hdecl_in & Hwf_method).
	    exists Ty, Cstatic, argtypes, mdef_static, declaring_class.
	    split; [exact Hget_y |].
	    split; [exact HbaseTy |].
	    split; [exact Hget_args |].
	    split; [exact Hfind_static |].
	    split; [exact Hclass_sub |].
	    split.
	    - exact
	        (method_signature_refines_subtype
	          CT (rctype (rt_type receiver_obj)) Cstatic
	          m mdef mdef_static
	          Hwf_CT Hclass_sub Hfind Hfind_static).
	    - split; [exact Hdecl_sub | exact Hwf_method].
  Qed.

  Lemma pico_core_typed_resolved_method_body :
    forall sGamma sGamma' rGamma h mt x y m args
      loc C mdef vals
      (Htyping : stmt_typing CT sGamma mt (SCall x m y args) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hreceiver : runtime_getVal rGamma y = Some (Iot loc))
      (Hbase : r_basetype h loc = Some C)
      (Hfind : FindMethodWithName CT C m mdef)
      (Hargs : runtime_lookup_list rGamma args = Some vals),
      exists body_sGamma' body_ret_type,
        stmt_typing CT
          (mreceiver (msignature mdef) :: mparams (msignature mdef))
          (mscope (msignature mdef))
          (mbody_stmt (mbody mdef)) body_sGamma' /\
        static_getType body_sGamma' (mreturn (mbody mdef)) =
          Some body_ret_type /\
        qualified_type_subtype
          CT body_ret_type (mret (msignature mdef)).
  Proof.
    intros sGamma sGamma' rGamma h mt x y m args
      loc C mdef vals Htyping Henv Hreceiver Hbase Hfind Hargs.
    destruct
      (pico_core_typed_resolved_method_static
        sGamma sGamma' rGamma h mt x y m args
        loc C mdef vals Htyping Henv Hreceiver Hbase Hfind Hargs)
	      as (Ty & Cstatic & argtypes & mdef_static & declaring_class &
	          Hget_y & Href & Hget_args & Hfind_static & Hsubtype &
	          Hrefine & Hdecl_sub & Hwf_method).
    unfold wf_method in Hwf_method.
    destruct Hwf_method as
      (Hreturn_wf & body_sGamma' & body_ret_type & Hbody & Hret_dom &
       Hret_type & Hret_subtype & Hoverride).
    exists body_sGamma', body_ret_type.
    split; [exact Hbody |].
    split.
    - unfold static_getType.
      exact Hret_type.
    - exact Hret_subtype.
  Qed.

  Lemma pico_core_resolved_method_frame_wf_renv :
    forall rGamma h loc C vals args
      (Hrenv : wf_renv CT rGamma h)
      (Hbase : r_basetype h loc = Some C)
      (Hargs : runtime_lookup_list rGamma args = Some vals),
      wf_renv CT (mkr_env (Iot loc :: vals)) h.
  Proof.
    intros rGamma h loc C vals args Hrenv Hbase Hargs.
    unfold wf_renv.
    split; [simpl; lia |].
    split.
    - exists loc. split; [reflexivity |].
      unfold r_basetype in Hbase.
      destruct (runtime_getObj h loc) as [o |] eqn:Hobj;
        try discriminate.
      apply runtime_getObj_dom in Hobj. exact Hobj.
    - eapply method_frame_vals_wf; eauto.
  Qed.

  Lemma pico_core_typed_env_after_update :
    forall sGamma rGamma h x Tx v
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hget_x : static_getType sGamma x = Some Tx)
      (Hnot_receiver : x <> 0)
      (Htyped_v :
        forall qcontext receiver,
          get_this_var_mapping (vars rGamma) = Some receiver ->
          r_muttype h receiver = Some qcontext ->
          pico_core_typed_value CT h qcontext Tx v)
      (Hwf_next :
        wf_r_config CT sGamma
          (set_vars rGamma (update x v (vars rGamma))) h),
      pico_core_typed_env CT sGamma
        (set_vars rGamma (update x v (vars rGamma))) h.
  Proof.
    intros sGamma rGamma h x Tx v Henv Hget_x Hnot_receiver
      Htyped_v Hwf_next.
    destruct Henv as
      (qcontext & receiver & Hwf & Hreceiver & Hqcontext & Hvalues).
    exists qcontext, receiver.
    split.
    - exact Hwf_next.
    - split.
      + rewrite get_this_var_mapping_update_vars_nonzero; eauto.
      + split.
        * exact Hqcontext.
        * intros i Ti Hstatic.
          destruct (Nat.eq_dec i x) as [Heq | Hneq].
          -- subst i.
             rewrite Hget_x in Hstatic.
             inversion Hstatic.
             subst Ti.
             exists v.
             split.
             ++ unfold runtime_getVal, set_vars.
                apply update_same.
                apply static_getType_dom in Hget_x.
                unfold wf_r_config in Hwf.
                destruct Hwf as [_ [_ [_ [_ [Hlength _]]]]].
                rewrite <- Hlength.
                exact Hget_x.
             ++ eapply pico_core_typed_value_env_independent.
                eapply Htyped_v; eauto.
          -- destruct (Hvalues i Ti Hstatic) as [old [Hold Htyped_old]].
             exists old.
             split.
             ++ unfold runtime_getVal, set_vars.
                change
                  (nth_error (update x v (vars rGamma)) i = Some old).
                unfold runtime_getVal in Hold.
                rewrite update_diff; [exact Hold | congruence].
             ++ exact Htyped_old.
  Qed.

  Lemma pico_core_typed_env_update_value :
    forall sGamma rGamma h x Tx v
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hget_x : static_getType sGamma x = Some Tx)
      (Hnot_receiver : x <> 0)
      (Htyped_v :
        forall qcontext receiver,
          get_this_var_mapping (vars rGamma) = Some receiver ->
          r_muttype h receiver = Some qcontext ->
          pico_core_typed_value CT h qcontext Tx v),
      pico_core_typed_env CT sGamma
        (set_vars rGamma (update x v (vars rGamma))) h.
  Proof.
    intros sGamma rGamma h x Tx v Henv Hget_x Hnot_receiver Htyped_v.
    pose proof
      (pico_core_typed_env_real_lr_env sGamma rGamma h Henv)
      as Hreal.
    assert (Hreal_value :
      forall qcontext receiver,
        get_this_var_mapping (vars rGamma) = Some receiver ->
        r_muttype h receiver = Some qcontext ->
        pico_typed_runtime_value CT h qcontext Tx v).
    {
      intros qcontext receiver Hreceiver Hqcontext.
      apply pico_core_typed_value_real_lr_value.
      eapply Htyped_v; eauto.
    }
    pose proof
      (pico_typed_runtime_env_update_value
        CT sGamma rGamma h x Tx v Hreal Hget_x Hnot_receiver Hreal_value)
      as Hreal_next.
    pose proof
      (pico_typed_runtime_env_wf_config
        CT sGamma (set_vars rGamma (update x v (vars rGamma))) h
        Hreal_next) as Hwf_next.
    eapply pico_core_typed_env_after_update; eauto.
  Qed.

  (** Return transfer reduces to one source-value subtype obligation.  The
      call-specific viewpoint lemmas only have to establish [Hsub] and the
      source value typing; updating the caller environment is uniform. *)
  Lemma pico_core_typed_env_update_value_from_subtype :
    forall sGamma rGamma h x Tsource Ttarget v
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hget_x : static_getType sGamma x = Some Ttarget)
      (Hnot_receiver : x <> 0)
      (Hsource : forall qcontext receiver,
        get_this_var_mapping (vars rGamma) = Some receiver ->
        r_muttype h receiver = Some qcontext ->
        pico_core_typed_value CT h qcontext Tsource v)
      (Hsub : qualified_type_subtype CT Tsource Ttarget),
      pico_core_typed_env CT sGamma
        (set_vars rGamma (update x v (vars rGamma))) h.
  Proof.
    intros sGamma rGamma h x Tsource Ttarget v Henv Hget_x
      Hnot_receiver Hsource Hsub.
    eapply pico_core_typed_env_update_value; eauto.
    intros qcontext receiver Hreceiver Hqcontext.
    pose proof (pico_core_typed_env_wf_config CT sGamma rGamma h Henv)
      as Hconfig.
    destruct Hconfig as [Hwf_CT [Hwf_heap _]].
    eapply pico_core_typed_value_subtype; eauto.
  Qed.

  (** Viewpoint-adapted location subtyping used by call entry and return.
      These wrappers keep the core LR independent of the large preservation
      proof while retaining its exact qualifier side conditions. *)
  Lemma pico_core_wf_r_typable_adapted_subtype_abstract_state :
    forall sGamma rGamma h Tthis locthis loc T1 T2 qcontext
      (Hwf_heap : wf_heap CT h)
      (Hthis_type : get_this_qualified_type sGamma = Some Tthis)
      (Hthis_val : get_this_var_mapping (vars rGamma) = Some locthis)
      (Hthis_mut : r_muttype h locthis = Some qcontext)
      (Hthis_qualifier :
        qualifier_typable_context qcontext (sqtype Tthis) qcontext)
      (Htyped : wf_r_typable CT h loc T1 qcontext)
      (Hsub : qualified_type_subtype CT
        (vpa_mutability_tt_abstract_state Tthis T1)
        (vpa_mutability_tt_abstract_state Tthis T2)),
      wf_r_typable CT h loc T2 qcontext.
  Proof.
    intros.
    eapply wf_r_typable_adapted_subtype_abstract_state; eauto.
  Qed.

  Lemma pico_core_wf_r_typable_adapted_subtype_readonly_state :
    forall sGamma rGamma h Tthis locthis loc T1 T2 qcontext
      (Hwf_heap : wf_heap CT h)
      (Hthis_type : get_this_qualified_type sGamma = Some Tthis)
      (Hthis_val : get_this_var_mapping (vars rGamma) = Some locthis)
      (Hthis_mut : r_muttype h locthis = Some qcontext)
      (Hthis_qualifier :
        qualifier_typable_context qcontext (sqtype Tthis) qcontext)
      (Htyped : wf_r_typable CT h loc T1 qcontext)
      (Hsub : qualified_type_subtype CT
        (vpa_mutability_tt_readonly_state Tthis T1)
        (vpa_mutability_tt_readonly_state Tthis T2)),
      wf_r_typable CT h loc T2 qcontext.
  Proof.
    intros.
    eapply wf_r_typable_adapted_subtype_readonly_state; eauto.
  Qed.

  Lemma pico_core_abstract_state_argument_qualifier_transfer :
    forall qarg qinner qouter qs_ty qs_this qs_arg qs_method,
      qualifier_typable_context qarg qs_arg qouter ->
      qualifier_typable_context qinner qs_ty qouter ->
      qualifier_typable_context qouter qs_this qouter ->
      q_subtype qs_arg
        (vpa_mutability_qq_abstract_state qs_ty qs_method) ->
      q_subtype qs_ty
        (vpa_mutability_qq_abstract_state qs_ty qs_this) ->
      qualifier_typable_context qarg qs_method qinner.
  Proof.
    intros qarg qinner qouter qs_ty qs_this qs_arg qs_method
      Harg Hty Hthis Harg_sub Hrcv_sub.
    unfold qualifier_typable_context in *.
    destruct qarg; destruct qinner; destruct qouter;
    destruct qs_ty; destruct qs_this; destruct qs_arg; destruct qs_method;
    simpl in *;
    try solve [inversion Harg_sub];
    try solve [inversion Hrcv_sub];
    try solve [exfalso; eapply lost_subtype_refl; exact Harg_sub];
    try solve [exfalso; eapply lost_subtype_refl; exact Hrcv_sub];
    eauto.
  Qed.

  Lemma pico_core_readonly_state_argument_qualifier_transfer :
    forall qarg qinner qouter qs_ty qs_this qs_arg qs_method,
      qualifier_typable_context qarg qs_arg qouter ->
      qualifier_typable_context qinner qs_ty qouter ->
      qualifier_typable_context qouter qs_this qouter ->
      q_subtype qs_arg
        (vpa_mutability_qq_readonly_state qs_ty qs_method) ->
      q_subtype qs_ty
        (vpa_mutability_qq_readonly_state qs_ty qs_this) ->
      qualifier_typable_context qarg qs_method qinner.
  Proof.
    intros qarg qinner qouter qs_ty qs_this qs_arg qs_method
      Harg Hty Hthis Harg_sub Hrcv_sub.
    unfold qualifier_typable_context in *.
    destruct qarg; destruct qinner; destruct qouter;
    destruct qs_ty; destruct qs_this; destruct qs_arg; destruct qs_method;
    simpl in *;
    try solve [inversion Harg_sub];
    try solve [inversion Hrcv_sub];
    try solve [exfalso; eapply lost_subtype_refl; exact Harg_sub];
    try solve [exfalso; eapply lost_subtype_refl; exact Hrcv_sub];
    eauto.
  Qed.

  Lemma pico_core_abstract_state_argument_special_transfer :
    forall qarg qinner qouter qs_arg qs_method,
      qualifier_typable_context qarg qs_arg qouter ->
      qualifier_typable_context qinner RO qouter ->
      q_subtype qs_arg (vpa_mutability_qq_abstract_state RO qs_method) ->
      qualifier_typable_context qarg qs_method qinner.
  Proof.
    intros qarg qinner qouter qs_arg qs_method Harg Hty Hsub.
    unfold qualifier_typable_context in *.
    destruct qarg; destruct qinner; destruct qouter;
    destruct qs_arg; destruct qs_method;
    simpl in *;
    try solve [inversion Hsub];
    try solve [exfalso; eapply lost_subtype_refl; exact Hsub];
    eauto.
  Qed.

  Lemma pico_core_abstract_state_argument_direct_transfer :
    forall qarg qinner qouter qs_ty qs_arg qs_param,
      qualifier_typable_context qarg qs_arg qouter ->
      qualifier_typable_context qinner qs_ty qouter ->
      q_subtype qs_arg
        (vpa_mutability_qq_abstract_state qs_ty qs_param) ->
      qualifier_typable_context qarg qs_param qinner.
  Proof.
    intros qarg qinner qouter qs_ty qs_arg qs_param
      Harg Hinner Harg_sub.
    unfold qualifier_typable_context in *.
    destruct qarg; destruct qinner; destruct qouter;
    destruct qs_ty; destruct qs_arg; destruct qs_param;
    simpl in *;
    try solve [inversion Harg_sub];
    try solve [exfalso; eapply lost_subtype_refl; exact Harg_sub];
    eauto.
  Qed.

  Lemma pico_core_readonly_state_argument_direct_transfer :
    forall qarg qinner qouter qs_ty qs_arg qs_param,
      qualifier_typable_context qarg qs_arg qouter ->
      qualifier_typable_context qinner qs_ty qouter ->
      q_subtype qs_arg
        (vpa_mutability_qq_readonly_state qs_ty qs_param) ->
      qualifier_typable_context qarg qs_param qinner.
  Proof.
    intros qarg qinner qouter qs_ty qs_arg qs_param
      Harg Hinner Harg_sub.
    unfold qualifier_typable_context in *.
    destruct qarg; destruct qinner; destruct qouter;
    destruct qs_ty; destruct qs_arg; destruct qs_param;
    simpl in *;
    try solve [inversion Harg_sub];
    try solve [exfalso; eapply lost_subtype_refl; exact Harg_sub];
    eauto.
  Qed.

  Lemma pico_core_readonly_state_argument_special_transfer :
    forall qarg qinner qouter qs_arg qs_method,
      qualifier_typable_context qarg qs_arg qouter ->
      qualifier_typable_context qinner RO qouter ->
      q_subtype qs_arg (vpa_mutability_qq_readonly_state RO qs_method) ->
      qualifier_typable_context qarg qs_method qinner.
  Proof.
    intros qarg qinner qouter qs_arg qs_method Harg Hty Hsub.
    unfold qualifier_typable_context in *.
    destruct qarg; destruct qinner; destruct qouter;
    destruct qs_arg; destruct qs_method;
    simpl in *;
    try solve [inversion Hsub];
    try solve [exfalso; eapply lost_subtype_refl; exact Hsub];
    eauto.
  Qed.

  Lemma pico_core_wf_r_typable_call_argument_abstract_state :
    forall h loc Targ Ty Tparam Tthis qinner qouter
      (Hsource : wf_r_typable CT h loc Targ qouter)
      (Hthis_qualifier :
        qualifier_typable_context qouter (sqtype Tthis) qouter)
      (Hinner_qualifier :
        qualifier_typable_context qinner (sqtype Ty) qouter)
      (Harg_sub : qualified_type_subtype CT Targ
        (vpa_mutability_tt_abstract_state Ty Tparam))
      (Hrcv_sub : qualified_type_subtype CT Ty
        (vpa_mutability_tt_abstract_state Ty Tthis)),
      wf_r_typable CT h loc Tparam qinner.
  Proof.
    intros h loc Targ Ty Tparam Tthis qinner qouter Hsource Hthis_qualifier Hinner_qualifier Harg_sub Hrcv_sub.
    unfold wf_r_typable in Hsource |- *.
    destruct (r_type h loc) as [rqt |] eqn:Htype;
      try contradiction.
    destruct Hsource as [Hbase Hqualifier].
    split.
    - apply qualified_type_subtype_base_subtype in Harg_sub.
      rewrite vpa_mutability_tt_sbase_abstract_state in Harg_sub.
      eapply base_trans; eauto.
    - apply qualified_type_subtype_q_subtype in Harg_sub.
      apply qualified_type_subtype_q_subtype in Hrcv_sub.
      rewrite (sq_vpa_tt_eq_qq_abstract_state Ty Tparam) in Harg_sub.
      rewrite (sq_vpa_tt_eq_qq_abstract_state Ty Tthis) in Hrcv_sub.
      eapply pico_core_abstract_state_argument_qualifier_transfer; eauto.
  Qed.

  Lemma pico_core_wf_r_typable_call_argument_readonly_state :
    forall h loc Targ Ty Tparam Tthis qinner qouter
      (Hsource : wf_r_typable CT h loc Targ qouter)
      (Hthis_qualifier :
        qualifier_typable_context qouter (sqtype Tthis) qouter)
      (Hinner_qualifier :
        qualifier_typable_context qinner (sqtype Ty) qouter)
      (Harg_sub : qualified_type_subtype CT Targ
        (vpa_mutability_tt_readonly_state Ty Tparam))
      (Hrcv_sub : qualified_type_subtype CT Ty
        (vpa_mutability_tt_readonly_state Ty Tthis)),
      wf_r_typable CT h loc Tparam qinner.
  Proof.
    intros h loc Targ Ty Tparam Tthis qinner qouter Hsource Hthis_qualifier Hinner_qualifier Harg_sub Hrcv_sub.
    unfold wf_r_typable in Hsource |- *.
    destruct (r_type h loc) as [rqt |] eqn:Htype;
      try contradiction.
    destruct Hsource as [Hbase Hqualifier].
    split.
    - apply qualified_type_subtype_base_subtype in Harg_sub.
      rewrite vpa_mutability_tt_sbase_readonly_state in Harg_sub.
      eapply base_trans; eauto.
    - apply qualified_type_subtype_q_subtype in Harg_sub.
      apply qualified_type_subtype_q_subtype in Hrcv_sub.
      rewrite (sq_vpa_tt_eq_qq_readonly_state Ty Tparam) in Harg_sub.
      rewrite (sq_vpa_tt_eq_qq_readonly_state Ty Tthis) in Hrcv_sub.
      eapply pico_core_readonly_state_argument_qualifier_transfer; eauto.
  Qed.

  Lemma pico_core_wf_r_typable_call_argument_abstract_state_special :
    forall h loc Targ Tparam qinner qouter
      (Hsource : wf_r_typable CT h loc Targ qouter)
      (Hinner_qualifier :
        qualifier_typable_context qinner RO qouter)
      (Harg_sub : qualified_type_subtype CT Targ
        (vpa_mutability_tt_abstract_state {| sqtype := RO; sbase := sbase Targ |} Tparam)),
      wf_r_typable CT h loc Tparam qinner.
  Proof.
    intros h loc Targ Tparam qinner qouter Hsource Hinner_qualifier Harg_sub.
    unfold wf_r_typable in Hsource |- *.
    destruct (r_type h loc) as [rqt |] eqn:Htype;
      try contradiction.
    destruct Hsource as [Hbase Hqualifier].
    split.
    - apply qualified_type_subtype_base_subtype in Harg_sub.
      rewrite vpa_mutability_tt_sbase_abstract_state in Harg_sub.
      eapply base_trans; eauto.
    - apply qualified_type_subtype_q_subtype in Harg_sub.
      rewrite (sq_vpa_tt_eq_qq_abstract_state
        {| sqtype := RO; sbase := sbase Targ |} Tparam) in Harg_sub.
      eapply pico_core_abstract_state_argument_special_transfer; eauto.
  Qed.

  Lemma pico_core_wf_r_typable_call_argument_readonly_state_special :
    forall h loc Targ Tparam qinner qouter
      (Hsource : wf_r_typable CT h loc Targ qouter)
      (Hinner_qualifier :
        qualifier_typable_context qinner RO qouter)
      (Harg_sub : qualified_type_subtype CT Targ
        (vpa_mutability_tt_readonly_state {| sqtype := RO; sbase := sbase Targ |} Tparam)),
      wf_r_typable CT h loc Tparam qinner.
  Proof.
    intros h loc Targ Tparam qinner qouter Hsource Hinner_qualifier Harg_sub.
    unfold wf_r_typable in Hsource |- *.
    destruct (r_type h loc) as [rqt |] eqn:Htype;
      try contradiction.
    destruct Hsource as [Hbase Hqualifier].
    split.
    - apply qualified_type_subtype_base_subtype in Harg_sub.
      rewrite vpa_mutability_tt_sbase_readonly_state in Harg_sub.
      eapply base_trans; eauto.
    - apply qualified_type_subtype_q_subtype in Harg_sub.
      rewrite (sq_vpa_tt_eq_qq_readonly_state
        {| sqtype := RO; sbase := sbase Targ |} Tparam) in Harg_sub.
      eapply pico_core_readonly_state_argument_special_transfer; eauto.
  Qed.

  Lemma pico_core_typed_location_call_argument_abstract_state :
    forall h loc Targ Ty Tparam Tthis qinner qouter
      (Hsource : pico_core_typed_value CT h qouter Targ (Iot loc))
      (Hthis_qualifier :
        qualifier_typable_context qouter (sqtype Tthis) qouter)
      (Hinner_qualifier :
        qualifier_typable_context qinner (sqtype Ty) qouter)
      (Harg_sub : qualified_type_subtype CT Targ
        (vpa_mutability_tt_abstract_state Ty Tparam))
      (Hrcv_sub : qualified_type_subtype CT Ty
        (vpa_mutability_tt_abstract_state Ty Tthis)),
      pico_core_typed_value CT h qinner Tparam (Iot loc).
  Proof.
    intros.
    unfold pico_core_typed_value in Hsource |- *.
    eapply pico_core_wf_r_typable_call_argument_abstract_state; eauto.
  Qed.

  Lemma pico_core_typed_location_call_argument_readonly_state :
    forall h loc Targ Ty Tparam Tthis qinner qouter
      (Hsource : pico_core_typed_value CT h qouter Targ (Iot loc))
      (Hthis_qualifier :
        qualifier_typable_context qouter (sqtype Tthis) qouter)
      (Hinner_qualifier :
        qualifier_typable_context qinner (sqtype Ty) qouter)
      (Harg_sub : qualified_type_subtype CT Targ
        (vpa_mutability_tt_readonly_state Ty Tparam))
      (Hrcv_sub : qualified_type_subtype CT Ty
        (vpa_mutability_tt_readonly_state Ty Tthis)),
      pico_core_typed_value CT h qinner Tparam (Iot loc).
  Proof.
    intros.
    unfold pico_core_typed_value in Hsource |- *.
    eapply pico_core_wf_r_typable_call_argument_readonly_state; eauto.
  Qed.

  Lemma pico_core_typed_location_call_argument_abstract_state_direct :
    forall h loc Targ Ty Tparam qinner qouter
      (Hsource : pico_core_typed_value CT h qouter Targ (Iot loc))
      (Hinner_qualifier :
        qualifier_typable_context qinner (sqtype Ty) qouter)
      (Harg_sub : qualified_type_subtype CT Targ
        (vpa_mutability_tt_abstract_state Ty Tparam)),
      pico_core_typed_value CT h qinner Tparam (Iot loc).
  Proof.
    intros h loc Targ Ty Tparam qinner qouter Hsource Hinner_qualifier Harg_sub.
    unfold pico_core_typed_value, wf_r_typable in Hsource |- *.
    destruct (r_type h loc) as [rqt |] eqn:Htype;
      try contradiction.
    destruct Hsource as [Hbase Hqualifier].
    split.
    - apply qualified_type_subtype_base_subtype in Harg_sub.
      rewrite vpa_mutability_tt_sbase_abstract_state in Harg_sub.
      eapply base_trans; eauto.
    - apply qualified_type_subtype_q_subtype in Harg_sub.
      rewrite (sq_vpa_tt_eq_qq_abstract_state Ty Tparam) in Harg_sub.
      eapply pico_core_abstract_state_argument_direct_transfer; eauto.
  Qed.

  Lemma pico_core_typed_location_call_argument_readonly_state_direct :
    forall h loc Targ Ty Tparam qinner qouter
      (Hsource : pico_core_typed_value CT h qouter Targ (Iot loc))
      (Hinner_qualifier :
        qualifier_typable_context qinner (sqtype Ty) qouter)
      (Harg_sub : qualified_type_subtype CT Targ
        (vpa_mutability_tt_readonly_state Ty Tparam)),
      pico_core_typed_value CT h qinner Tparam (Iot loc).
  Proof.
    intros h loc Targ Ty Tparam qinner qouter Hsource Hinner_qualifier Harg_sub.
    unfold pico_core_typed_value, wf_r_typable in Hsource |- *.
    destruct (r_type h loc) as [rqt |] eqn:Htype;
      try contradiction.
    destruct Hsource as [Hbase Hqualifier].
    split.
    - apply qualified_type_subtype_base_subtype in Harg_sub.
      rewrite vpa_mutability_tt_sbase_readonly_state in Harg_sub.
      eapply base_trans; eauto.
    - apply qualified_type_subtype_q_subtype in Harg_sub.
      rewrite (sq_vpa_tt_eq_qq_readonly_state Ty Tparam) in Harg_sub.
      eapply pico_core_readonly_state_argument_direct_transfer; eauto.
  Qed.

  (** Return transfer is the sole remaining call extraction obligation.
      It is intentionally kept out of this entry-frame module until proved
      directly from the complete source call rule. *)

  Lemma pico_core_abstract_state_return_qualifier :
    forall qr qinner qouter qreceiver qbody qmethod qtarget,
      qualifier_typable_context qr qbody qinner ->
      qualifier_typable_context qinner qreceiver qouter ->
      q_subtype qbody qmethod ->
      q_subtype (vpa_mutability_qq_abstract_state qreceiver qmethod) qtarget ->
      qualifier_typable_context qr qtarget qouter.
  Proof.
    intros qr qinner qouter qreceiver qbody qmethod qtarget
      Hvalue Hreceiver Hbody Hcall.
    destruct qr; destruct qinner; destruct qouter;
      destruct qreceiver; destruct qbody; destruct qmethod; destruct qtarget;
      simpl in *.
    all: try easy.
    all: try solve [inversion Hbody].
    all: try solve [inversion Hcall].
    all: try solve [inversion Hreceiver].
    all: try solve [eapply lost_subtype_refl; eauto with typ].
    all: eauto with typ.
  Qed.

  Lemma pico_core_readonly_state_return_qualifier :
    forall qr qinner qouter qreceiver qbody qmethod qtarget,
      qualifier_typable_context qr qbody qinner ->
      qualifier_typable_context qinner qreceiver qouter ->
      q_subtype qbody qmethod ->
      q_subtype (vpa_mutability_qq_readonly_state qreceiver qmethod) qtarget ->
      qualifier_typable_context qr qtarget qouter.
  Proof.
    intros qr qinner qouter qreceiver qbody qmethod qtarget
      Hvalue Hreceiver Hbody Hcall.
    destruct qr; destruct qinner; destruct qouter;
      destruct qreceiver; destruct qbody; destruct qmethod; destruct qtarget;
      simpl in *.
    all: try easy.
    all: try solve [inversion Hbody].
    all: try solve [inversion Hcall].
    all: try solve [inversion Hreceiver].
    all: try solve [eapply lost_subtype_refl; eauto with typ].
    all: eauto with typ.
  Qed.

  (** Flexible overriding: a result typed against the dynamically selected
      signature is typed at the caller's destination through the statically
      selected signature it refines. *)
  Lemma pico_core_typed_return_value_refined_abstract_state :
    forall h loc C Ty Tbody child parent Ttarget qinner qouter v
      (Hwf_CT : wf_class_table CT)
      (Hwf_heap : wf_heap CT h)
      (Hbase : r_basetype h loc = Some C)
      (Hqinner : r_muttype h loc = Some qinner)
      (Hreceiver_typed : pico_core_typed_value CT h qouter Ty (Iot loc))
      (Hrefine : method_signature_refinement CT child parent)
      (Hreceiver_sub : base_subtype CT (TRef C) (sbase (mreceiver child)))
      (Hvalue : pico_core_typed_value CT h qinner Tbody v)
      (Hbody_return : qualified_type_subtype CT Tbody (mret child))
      (Hcall_return : qualified_type_subtype CT
        (vpa_mutability_tt_abstract_state Ty (mret parent)) Ttarget),
      pico_core_typed_value CT h qouter Ttarget v.
  Proof.
    intros h loc C Ty Tbody child parent Ttarget qinner qouter v Hwf_CT
      Hwf_heap Hbase Hqinner Hreceiver_typed Hrefine Hreceiver_sub Hvalue
      Hbody_return Hcall_return.
    destruct v as [| result | n]; simpl in *.
    - have Hchild := pico_core_subtype_preserves_reference Tbody
        (mret child) Hvalue Hbody_return.
      destruct (refinement_preserves_ref_return CT child parent Hrefine
        Hchild) as [D HD].
      eapply pico_core_subtype_preserves_reference; [| exact Hcall_return].
      exists D. rewrite vpa_mutability_tt_sbase_abstract_state. exact HD.
    - eapply refinement_preserves_call_result_abstract; eauto.
      eapply wf_r_typable_subtype; eauto.
    - apply qualified_type_subtype_base_subtype in Hbody_return.
      rewrite Hvalue in Hbody_return.
      apply base_subtype_from_int in Hbody_return.
      have Hparent := refinement_preserves_int_return CT child parent
        Hrefine Hbody_return.
      apply qualified_type_subtype_base_subtype in Hcall_return.
      rewrite vpa_mutability_tt_sbase_abstract_state in Hcall_return.
      rewrite Hparent in Hcall_return.
      exact (base_subtype_from_int _ _ Hcall_return).
  Qed.

  (** Flexible overriding: a result typed against the dynamically selected
      signature is typed at the caller's destination through the statically
      selected signature it refines. *)
  Lemma pico_core_typed_return_value_refined_readonly_state :
    forall h loc C Ty Tbody child parent Ttarget qinner qouter v
      (Hwf_CT : wf_class_table CT)
      (Hwf_heap : wf_heap CT h)
      (Hbase : r_basetype h loc = Some C)
      (Hqinner : r_muttype h loc = Some qinner)
      (Hreceiver_typed : pico_core_typed_value CT h qouter Ty (Iot loc))
      (Hrefine : method_signature_refinement CT child parent)
      (Hreceiver_sub : base_subtype CT (TRef C) (sbase (mreceiver child)))
      (Hvalue : pico_core_typed_value CT h qinner Tbody v)
      (Hbody_return : qualified_type_subtype CT Tbody (mret child))
      (Hcall_return : qualified_type_subtype CT
        (vpa_mutability_tt_readonly_state Ty (mret parent)) Ttarget),
      pico_core_typed_value CT h qouter Ttarget v.
  Proof.
    intros h loc C Ty Tbody child parent Ttarget qinner qouter v Hwf_CT
      Hwf_heap Hbase Hqinner Hreceiver_typed Hrefine Hreceiver_sub Hvalue
      Hbody_return Hcall_return.
    destruct v as [| result | n]; simpl in *.
    - have Hchild := pico_core_subtype_preserves_reference Tbody
        (mret child) Hvalue Hbody_return.
      destruct (refinement_preserves_ref_return CT child parent Hrefine
        Hchild) as [D HD].
      eapply pico_core_subtype_preserves_reference; [| exact Hcall_return].
      exists D. rewrite vpa_mutability_tt_sbase_readonly_state. exact HD.
    - eapply refinement_preserves_call_result_readonly; eauto.
      eapply wf_r_typable_subtype; eauto.
    - apply qualified_type_subtype_base_subtype in Hbody_return.
      rewrite Hvalue in Hbody_return.
      apply base_subtype_from_int in Hbody_return.
      have Hparent := refinement_preserves_int_return CT child parent
        Hrefine Hbody_return.
      apply qualified_type_subtype_base_subtype in Hcall_return.
      rewrite vpa_mutability_tt_sbase_readonly_state in Hcall_return.
      rewrite Hparent in Hcall_return.
      exact (base_subtype_from_int _ _ Hcall_return).
  Qed.

  Lemma pico_core_r_basetype_heap_types_extend :
    forall h h' loc C
      (Hextend : pico_core_heap_types_extend h h')
      (Hbase : r_basetype h loc = Some C),
      r_basetype h' loc = Some C.
  Proof.
    intros h h' loc C [_ Htypes] Hbase.
    unfold r_basetype in *.
    destruct (runtime_getObj h loc) as [o |] eqn:Hobj; try discriminate.
    assert (Htype : r_type h loc = Some (rt_type o)).
    { unfold r_type. rewrite Hobj. reflexivity. }
    specialize (Htypes loc (rt_type o) Htype).
    unfold r_type in Htypes.
    destruct (runtime_getObj h' loc) as [o' |]; try discriminate.
    injection Htypes as ->. exact Hbase.
  Qed.

  Lemma pico_core_typed_return_value_abstract_state :
    forall h Ty Tbody Tmethod Ttarget qinner qouter v
      (Hwf_CT : wf_class_table CT)
      (Hreceiver_context :
        qualifier_typable_context qinner (sqtype Ty) qouter)
      (Hvalue : pico_core_typed_value CT h qinner Tbody v)
      (Hbody_return : qualified_type_subtype CT Tbody Tmethod)
      (Hcall_return : qualified_type_subtype CT
        (vpa_mutability_tt_abstract_state Ty Tmethod) Ttarget),
      pico_core_typed_value CT h qouter Ttarget v.
  Proof.
    intros h Ty Tbody Tmethod Ttarget qinner qouter v Hwf_CT Hreceiver_context Hvalue Hbody_return Hcall_return.
	    destruct v as [|loc|n]; simpl in *.
	    - pose proof
	        (pico_core_subtype_preserves_reference Tbody Tmethod
	          Hvalue Hbody_return) as [C Hmethod].
	      assert (Hadapt : exists D,
	        sbase (vpa_mutability_tt_abstract_state Ty Tmethod) = TRef D).
	      {
	        exists C.
	        rewrite vpa_mutability_tt_sbase_abstract_state.
	        exact Hmethod.
	      }
	      eapply pico_core_subtype_preserves_reference; eauto.
    - unfold wf_r_typable in *.
      destruct (r_type h loc) as [runtime_type |] eqn:Hruntime_type;
        try contradiction.
      destruct Hvalue as [Hbase Hqualifier].
      split.
      + apply qualified_type_subtype_base_subtype in Hbody_return.
        apply qualified_type_subtype_base_subtype in Hcall_return.
        rewrite vpa_mutability_tt_sbase_abstract_state in Hcall_return.
        eapply base_trans; [exact Hbase |].
        eapply base_trans; eauto.
      + apply qualified_type_subtype_q_subtype in Hbody_return.
        apply qualified_type_subtype_q_subtype in Hcall_return.
        rewrite (sq_vpa_tt_eq_qq_abstract_state Ty Tmethod) in Hcall_return.
        eapply pico_core_abstract_state_return_qualifier
          with (qr := rqtype runtime_type) (qinner := qinner)
            (qouter := qouter) (qreceiver := sqtype Ty)
            (qbody := sqtype Tbody) (qmethod := sqtype Tmethod)
            (qtarget := sqtype Ttarget).
        * exact Hqualifier.
        * exact Hreceiver_context.
        * exact Hbody_return.
        * exact Hcall_return.
	    - apply qualified_type_subtype_base_subtype in Hbody_return.
	      apply qualified_type_subtype_base_subtype in Hcall_return.
	      rewrite vpa_mutability_tt_sbase_abstract_state in Hcall_return.
	      rewrite Hvalue in Hbody_return.
	      apply base_subtype_from_int in Hbody_return.
	      rewrite Hbody_return in Hcall_return.
	      apply base_subtype_from_int in Hcall_return.
	      exact Hcall_return.
  Qed.

  Lemma pico_core_typed_return_value_readonly_state :
    forall h Ty Tbody Tmethod Ttarget qinner qouter v
      (Hwf_CT : wf_class_table CT)
      (Hreceiver_context :
        qualifier_typable_context qinner (sqtype Ty) qouter)
      (Hvalue : pico_core_typed_value CT h qinner Tbody v)
      (Hbody_return : qualified_type_subtype CT Tbody Tmethod)
      (Hcall_return : qualified_type_subtype CT
        (vpa_mutability_tt_readonly_state Ty Tmethod) Ttarget),
      pico_core_typed_value CT h qouter Ttarget v.
  Proof.
    intros h Ty Tbody Tmethod Ttarget qinner qouter v Hwf_CT Hreceiver_context Hvalue Hbody_return Hcall_return.
	    destruct v as [|loc|n]; simpl in *.
	    - pose proof
	        (pico_core_subtype_preserves_reference Tbody Tmethod
	          Hvalue Hbody_return) as [C Hmethod].
	      assert (Hadapt : exists D,
	        sbase (vpa_mutability_tt_readonly_state Ty Tmethod) = TRef D).
	      {
	        exists C.
	        rewrite vpa_mutability_tt_sbase_readonly_state.
	        exact Hmethod.
	      }
	      eapply pico_core_subtype_preserves_reference; eauto.
    - unfold wf_r_typable in *.
      destruct (r_type h loc) as [runtime_type |] eqn:Hruntime_type;
        try contradiction.
      destruct Hvalue as [Hbase Hqualifier].
      split.
      + apply qualified_type_subtype_base_subtype in Hbody_return.
        apply qualified_type_subtype_base_subtype in Hcall_return.
        rewrite vpa_mutability_tt_sbase_readonly_state in Hcall_return.
        eapply base_trans; [exact Hbase |].
        eapply base_trans; eauto.
      + apply qualified_type_subtype_q_subtype in Hbody_return.
        apply qualified_type_subtype_q_subtype in Hcall_return.
        rewrite (sq_vpa_tt_eq_qq_readonly_state Ty Tmethod) in Hcall_return.
        eapply pico_core_readonly_state_return_qualifier
          with (qr := rqtype runtime_type) (qinner := qinner)
            (qouter := qouter) (qreceiver := sqtype Ty)
            (qbody := sqtype Tbody) (qmethod := sqtype Tmethod)
            (qtarget := sqtype Ttarget).
        * exact Hqualifier.
        * exact Hreceiver_context.
        * exact Hbody_return.
        * exact Hcall_return.
	    - apply qualified_type_subtype_base_subtype in Hbody_return.
	      apply qualified_type_subtype_base_subtype in Hcall_return.
	      rewrite vpa_mutability_tt_sbase_readonly_state in Hcall_return.
	      rewrite Hvalue in Hbody_return.
	      apply base_subtype_from_int in Hbody_return.
	      rewrite Hbody_return in Hcall_return.
	      apply base_subtype_from_int in Hcall_return.
	      exact Hcall_return.
  Qed.

  Lemma pico_core_typed_method_frame_env :
    forall msig h loc vals qinner
      (Hwf_CT : wf_class_table CT)
      (Hwf_heap : wf_heap CT h)
      (Hwf_renv :
        wf_renv CT (mkr_env (Iot loc :: vals)) h)
      (Hwf_senv :
        wf_senv CT (mreceiver msig :: mparams msig))
      (Hqinner : r_muttype h loc = Some qinner)
      (Hreceiver_typed :
        pico_core_typed_value CT h
          qinner (mreceiver msig) (Iot loc))
      (Hlength : length (mparams msig) = length vals)
      (Hparams : forall i T,
        nth_error (mparams msig) i = Some T ->
        exists v,
          nth_error vals i = Some v /\
          pico_core_typed_value CT h
            qinner T v),
      pico_core_typed_env CT
        (mreceiver msig :: mparams msig)
        (mkr_env (Iot loc :: vals)) h.
  Proof.
    intros msig h loc vals qinner
      Hwf_CT Hwf_heap Hwf_renv Hwf_senv Hqinner
      Hreceiver_typed Hlength Hparams.
    exists qinner, loc.
    split.
    - unfold wf_r_config.
      split; [exact Hwf_CT |].
      split; [exact Hwf_heap |].
      split; [exact Hwf_renv |].
      split; [exact Hwf_senv |].
      split.
      + simpl. simpl in Hlength. lia.
      + intros receiver qcontext Hreceiver Hqcontext i Hi T Hstatic.
        simpl in Hreceiver, Hqcontext.
        assert (receiver = loc) by congruence.
        subst receiver.
        assert (qcontext = qinner) by congruence.
        subst qcontext.
        destruct i as [|i].
        * simpl in Hstatic.
          inversion Hstatic; subst T.
          exact Hreceiver_typed.
        * simpl in Hstatic.
          destruct (Hparams i T Hstatic) as (v & Hv & Htyped).
          unfold runtime_getVal.
          simpl.
          rewrite Hv.
          destruct v as [|vloc|n]; simpl in *; auto.
    - split; [reflexivity |].
      split; [exact Hqinner |].
      intros i T Hstatic.
      destruct i as [|i].
      + simpl in Hstatic.
        inversion Hstatic; subst T.
        exists (Iot loc). split; [reflexivity | exact Hreceiver_typed].
      + simpl in Hstatic.
        destruct (Hparams i T Hstatic) as (v & Hv & Htyped).
        exists v. split; [exact Hv | exact Htyped].
  Qed.

  Lemma pico_core_typed_env_lookup_at_context :
    forall sGamma rGamma h qouter receiver
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hreceiver : get_this_var_mapping (vars rGamma) = Some receiver)
      (Hqouter : r_muttype h receiver = Some qouter)
      x T,
      static_getType sGamma x = Some T ->
      exists v,
        runtime_getVal rGamma x = Some v /\
        pico_core_typed_value CT h qouter T v.
  Proof.
    intros sGamma rGamma h qouter receiver Henv Hreceiver Hqouter x T Hstatic.
    destruct Henv as
      (qcontext & receiver' & Hwf & Hreceiver' & Hqcontext & Hvalues).
    assert (receiver' = receiver) by congruence.
    subst receiver'.
    assert (qcontext = qouter) by congruence.
    subst qcontext.
    eapply Hvalues; eauto.
  Qed.

  Lemma pico_core_typed_call_params_abstract_state :
    forall sGamma rGamma h args vals argtypes Ty params
      outer inner qinner qouter
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hreceiver : get_this_var_mapping (vars rGamma) = Some outer)
      (Hqouter : r_muttype h outer = Some qouter)
      (Hget_args : static_getType_list sGamma args = Some argtypes)
      (Hargs : runtime_lookup_list rGamma args = Some vals)
      (Harg_sub : Forall2
        (fun arg T => qualified_type_subtype CT arg
          (vpa_mutability_tt_abstract_state Ty T)) argtypes params)
      (Hinner_qualifier :
        qualifier_typable_context qinner (sqtype Ty) qouter)
      (Hqinner : r_muttype h inner = Some qinner),
      forall i T,
        nth_error params i = Some T ->
        exists v,
          nth_error vals i = Some v /\
          pico_core_typed_value CT h
            qinner T v.
  Proof.
    intros sGamma rGamma h args vals argtypes Ty params
      outer inner qinner qouter Henv Hreceiver Hqouter Hget_args Hargs
      Harg_sub Hinner_qualifier Hqinner
      i T Hparam.
    assert (Harg_len : length argtypes = length params).
    { eapply Forall2_length; exact Harg_sub. }
    assert (Hi : i < length argtypes).
    { rewrite Harg_len. apply nth_error_Some. rewrite Hparam. discriminate. }
    assert (Hargtype : exists argtype, nth_error argtypes i = Some argtype).
    { eapply nth_error_Some_exists; exact Hi. }
    destruct Hargtype as [argtype Hargtype].
    assert (Harg_sub_i : qualified_type_subtype CT argtype
      (vpa_mutability_tt_abstract_state Ty T)).
    { eapply Forall2_nth_error with (i := i) (a := argtype) (b := T); eauto. }
    destruct
      (static_getType_list_nth_zs sGamma args argtypes i argtype
        Hget_args Hargtype)
      as (j & Harg_j & Hstatic_j).
    assert (Hi_vals : i < length vals).
    {
      assert (Hstatic_len : length argtypes = length args).
      { eapply static_getType_list_preserves_length; eauto. }
      assert (Hruntime_len : length vals = length args).
      { eapply runtime_lookup_list_preserves_length; eauto. }
      lia.
    }
    destruct (nth_error_Some_exists vals i Hi_vals) as (v & Hv).
    destruct
      (runtime_lookup_list_nth_zs rGamma args vals i v Hargs Hv)
      as (j' & Hj' & Hruntime_j').
    assert (j' = j) by congruence.
    subst j'.
    destruct
      (pico_core_typed_env_lookup_at_context
        sGamma rGamma h qouter outer Henv Hreceiver Hqouter
        j argtype Hstatic_j)
      as (source_v & Hruntime_v & Hsource_v).
    rewrite Hruntime_v in Hruntime_j'.
    inversion Hruntime_j'; subst source_v.
	    exists v.
	    split; [exact Hv |].
	    destruct v as [|vloc|n].
	    - pose proof
	        (pico_core_subtype_preserves_reference argtype
	          (vpa_mutability_tt_abstract_state Ty T) Hsource_v Harg_sub_i)
	        as [C Hadapt].
	      rewrite vpa_mutability_tt_sbase_abstract_state in Hadapt.
	      exists C.
	      exact Hadapt.
    - eapply pico_core_typed_value_env_independent.
      eapply pico_core_typed_location_call_argument_abstract_state_direct; eauto.
	    - simpl in Hsource_v.
	      simpl.
	      apply qualified_type_subtype_base_subtype in Harg_sub_i.
	      rewrite vpa_mutability_tt_sbase_abstract_state in Harg_sub_i.
	      rewrite Hsource_v in Harg_sub_i.
	      apply base_subtype_from_int in Harg_sub_i.
	      exact Harg_sub_i.
  Qed.

  Lemma pico_core_typed_call_params_readonly_state :
    forall sGamma rGamma h args vals argtypes Ty params
      outer inner qinner qouter
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hreceiver : get_this_var_mapping (vars rGamma) = Some outer)
      (Hqouter : r_muttype h outer = Some qouter)
      (Hget_args : static_getType_list sGamma args = Some argtypes)
      (Hargs : runtime_lookup_list rGamma args = Some vals)
      (Harg_sub : Forall2
        (fun arg T => qualified_type_subtype CT arg
          (vpa_mutability_tt_readonly_state Ty T)) argtypes params)
      (Hinner_qualifier :
        qualifier_typable_context qinner (sqtype Ty) qouter)
      (Hqinner : r_muttype h inner = Some qinner),
      forall i T,
        nth_error params i = Some T ->
        exists v,
          nth_error vals i = Some v /\
          pico_core_typed_value CT h
            qinner T v.
  Proof.
    intros sGamma rGamma h args vals argtypes Ty params
      outer inner qinner qouter Henv Hreceiver Hqouter Hget_args Hargs
      Harg_sub Hinner_qualifier Hqinner
      i T Hparam.
    assert (Harg_len : length argtypes = length params).
    { eapply Forall2_length; exact Harg_sub. }
    assert (Hi : i < length argtypes).
    { rewrite Harg_len. apply nth_error_Some. rewrite Hparam. discriminate. }
    assert (Hargtype : exists argtype, nth_error argtypes i = Some argtype).
    { eapply nth_error_Some_exists; exact Hi. }
    destruct Hargtype as [argtype Hargtype].
    assert (Harg_sub_i : qualified_type_subtype CT argtype
      (vpa_mutability_tt_readonly_state Ty T)).
    { eapply Forall2_nth_error with (i := i) (a := argtype) (b := T); eauto. }
    destruct
      (static_getType_list_nth_zs sGamma args argtypes i argtype
        Hget_args Hargtype)
      as (j & Harg_j & Hstatic_j).
    assert (Hi_vals : i < length vals).
    {
      assert (Hstatic_len : length argtypes = length args).
      { eapply static_getType_list_preserves_length; eauto. }
      assert (Hruntime_len : length vals = length args).
      { eapply runtime_lookup_list_preserves_length; eauto. }
      lia.
    }
    destruct (nth_error_Some_exists vals i Hi_vals) as (v & Hv).
    destruct
      (runtime_lookup_list_nth_zs rGamma args vals i v Hargs Hv)
      as (j' & Hj' & Hruntime_j').
    assert (j' = j) by congruence.
    subst j'.
    destruct
      (pico_core_typed_env_lookup_at_context
        sGamma rGamma h qouter outer Henv Hreceiver Hqouter
        j argtype Hstatic_j)
      as (source_v & Hruntime_v & Hsource_v).
    rewrite Hruntime_v in Hruntime_j'.
    inversion Hruntime_j'; subst source_v.
	    exists v.
	    split; [exact Hv |].
	    destruct v as [|vloc|n].
	    - pose proof
	        (pico_core_subtype_preserves_reference argtype
	          (vpa_mutability_tt_readonly_state Ty T) Hsource_v Harg_sub_i)
	        as [C Hadapt].
	      rewrite vpa_mutability_tt_sbase_readonly_state in Hadapt.
	      exists C.
	      exact Hadapt.
    - eapply pico_core_typed_value_env_independent.
      eapply pico_core_typed_location_call_argument_readonly_state_direct; eauto.
	    - simpl in Hsource_v.
	      simpl.
	      apply qualified_type_subtype_base_subtype in Harg_sub_i.
	      rewrite vpa_mutability_tt_sbase_readonly_state in Harg_sub_i.
	      rewrite Hsource_v in Harg_sub_i.
	      apply base_subtype_from_int in Harg_sub_i.
	      exact Harg_sub_i.
  Qed.

  Lemma pico_core_typed_call_params_abstract_state_special :
    forall sGamma rGamma h args vals argtypes params
      outer inner qinner qouter
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hreceiver : get_this_var_mapping (vars rGamma) = Some outer)
      (Hqouter : r_muttype h outer = Some qouter)
      (Hget_args : static_getType_list sGamma args = Some argtypes)
      (Hargs : runtime_lookup_list rGamma args = Some vals)
      (Harg_sub : Forall2
        (fun arg T => qualified_type_subtype CT arg
          (vpa_mutability_tt_abstract_state
            {| sqtype := RO; sbase := sbase T |} T))
        argtypes params)
      (Hinner_qualifier :
        qualifier_typable_context qinner RO qouter)
      (Hqinner : r_muttype h inner = Some qinner),
      forall i T,
        nth_error params i = Some T ->
        exists v,
          nth_error vals i = Some v /\
          pico_core_typed_value CT h
            qinner T v.
  Proof.
    intros sGamma rGamma h args vals argtypes params
      outer inner qinner qouter Henv Hreceiver Hqouter Hget_args Hargs
      Harg_sub Hinner_qualifier Hqinner i T Hparam.
    assert (Harg_len : length argtypes = length params).
    { eapply Forall2_length; exact Harg_sub. }
    assert (Hi : i < length argtypes).
    { rewrite Harg_len. apply nth_error_Some. rewrite Hparam. discriminate. }
    assert (Hargtype : exists argtype, nth_error argtypes i = Some argtype).
    { eapply nth_error_Some_exists; exact Hi. }
    destruct Hargtype as [argtype Hargtype].
    assert (Harg_sub_i : qualified_type_subtype CT argtype
      (vpa_mutability_tt_abstract_state
        {| sqtype := RO; sbase := sbase T |} T)).
    { eapply Forall2_nth_error with (i := i) (a := argtype) (b := T); eauto. }
    destruct
      (static_getType_list_nth_zs sGamma args argtypes i argtype
        Hget_args Hargtype)
      as (j & Harg_j & Hstatic_j).
    assert (Hi_vals : i < length vals).
    {
      assert (Hstatic_len : length argtypes = length args).
      { eapply static_getType_list_preserves_length; eauto. }
      assert (Hruntime_len : length vals = length args).
      { eapply runtime_lookup_list_preserves_length; eauto. }
      lia.
    }
    destruct (nth_error_Some_exists vals i Hi_vals) as (v & Hv).
    destruct
      (runtime_lookup_list_nth_zs rGamma args vals i v Hargs Hv)
      as (j' & Hj' & Hruntime_j').
    assert (j' = j) by congruence.
    subst j'.
    destruct
      (pico_core_typed_env_lookup_at_context
        sGamma rGamma h qouter outer Henv Hreceiver Hqouter
        j argtype Hstatic_j)
      as (source_v & Hruntime_v & Hsource_v).
    rewrite Hruntime_v in Hruntime_j'.
    inversion Hruntime_j'; subst source_v.
	    exists v.
	    split; [exact Hv |].
	    destruct v as [|vloc|n].
	    - pose proof
	        (pico_core_subtype_preserves_reference argtype
	          (vpa_mutability_tt_abstract_state
	            {| sqtype := RO; sbase := sbase T |} T)
	          Hsource_v Harg_sub_i) as [C Hadapt].
	      rewrite vpa_mutability_tt_sbase_abstract_state in Hadapt.
	      exists C.
	      exact Hadapt.
    - eapply pico_core_typed_value_env_independent.
      unfold pico_core_typed_value in Hsource_v |- *.
      eapply pico_core_wf_r_typable_call_argument_abstract_state_special;
        eauto.
	    - simpl in Hsource_v.
	      simpl.
	      apply qualified_type_subtype_base_subtype in Harg_sub_i.
	      rewrite vpa_mutability_tt_sbase_abstract_state in Harg_sub_i.
	      rewrite Hsource_v in Harg_sub_i.
	      apply base_subtype_from_int in Harg_sub_i.
	      exact Harg_sub_i.
  Qed.

  Lemma pico_core_typed_call_params_readonly_state_special :
    forall sGamma rGamma h args vals argtypes params
      outer inner qinner qouter
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hreceiver : get_this_var_mapping (vars rGamma) = Some outer)
      (Hqouter : r_muttype h outer = Some qouter)
      (Hget_args : static_getType_list sGamma args = Some argtypes)
      (Hargs : runtime_lookup_list rGamma args = Some vals)
      (Harg_sub : Forall2
        (fun arg T => qualified_type_subtype CT arg
          (vpa_mutability_tt_readonly_state
            {| sqtype := RO; sbase := sbase T |} T))
        argtypes params)
      (Hinner_qualifier :
        qualifier_typable_context qinner RO qouter)
      (Hqinner : r_muttype h inner = Some qinner),
      forall i T,
        nth_error params i = Some T ->
        exists v,
          nth_error vals i = Some v /\
          pico_core_typed_value CT h
            qinner T v.
  Proof.
    intros sGamma rGamma h args vals argtypes params
      outer inner qinner qouter Henv Hreceiver Hqouter Hget_args Hargs
      Harg_sub Hinner_qualifier Hqinner i T Hparam.
    assert (Harg_len : length argtypes = length params).
    { eapply Forall2_length; exact Harg_sub. }
    assert (Hi : i < length argtypes).
    { rewrite Harg_len. apply nth_error_Some. rewrite Hparam. discriminate. }
    assert (Hargtype : exists argtype, nth_error argtypes i = Some argtype).
    { eapply nth_error_Some_exists; exact Hi. }
    destruct Hargtype as [argtype Hargtype].
    assert (Harg_sub_i : qualified_type_subtype CT argtype
      (vpa_mutability_tt_readonly_state
        {| sqtype := RO; sbase := sbase T |} T)).
    { eapply Forall2_nth_error with (i := i) (a := argtype) (b := T); eauto. }
    destruct
      (static_getType_list_nth_zs sGamma args argtypes i argtype
        Hget_args Hargtype)
      as (j & Harg_j & Hstatic_j).
    assert (Hi_vals : i < length vals).
    {
      assert (Hstatic_len : length argtypes = length args).
      { eapply static_getType_list_preserves_length; eauto. }
      assert (Hruntime_len : length vals = length args).
      { eapply runtime_lookup_list_preserves_length; eauto. }
      lia.
    }
    destruct (nth_error_Some_exists vals i Hi_vals) as (v & Hv).
    destruct
      (runtime_lookup_list_nth_zs rGamma args vals i v Hargs Hv)
      as (j' & Hj' & Hruntime_j').
    assert (j' = j) by congruence.
    subst j'.
    destruct
      (pico_core_typed_env_lookup_at_context
        sGamma rGamma h qouter outer Henv Hreceiver Hqouter
        j argtype Hstatic_j)
      as (source_v & Hruntime_v & Hsource_v).
    rewrite Hruntime_v in Hruntime_j'.
    inversion Hruntime_j'; subst source_v.
	    exists v.
	    split; [exact Hv |].
	    destruct v as [|vloc|n].
	    - pose proof
	        (pico_core_subtype_preserves_reference argtype
	          (vpa_mutability_tt_readonly_state
	            {| sqtype := RO; sbase := sbase T |} T)
	          Hsource_v Harg_sub_i) as [C Hadapt].
	      rewrite vpa_mutability_tt_sbase_readonly_state in Hadapt.
	      exists C.
	      exact Hadapt.
    - eapply pico_core_typed_value_env_independent.
      unfold pico_core_typed_value in Hsource_v |- *.
      eapply pico_core_wf_r_typable_call_argument_readonly_state_special;
        eauto.
	    - simpl in Hsource_v.
	      simpl.
	      apply qualified_type_subtype_base_subtype in Harg_sub_i.
	      rewrite vpa_mutability_tt_sbase_readonly_state in Harg_sub_i.
	      rewrite Hsource_v in Harg_sub_i.
	      apply base_subtype_from_int in Harg_sub_i.
	      exact Harg_sub_i.
  Qed.

  Lemma pico_core_stmt_typing_call_abs_components :
    forall sGamma sGamma' x y m args
      (Htyping : stmt_typing CT sGamma AbstractState
        (SCall x m y args) sGamma'),
	      exists Ty C argtypes Tthis Tx mdef,
	        static_getType sGamma y = Some Ty /\
	        sbase Ty = TRef C /\
	        static_getType_list sGamma args = Some argtypes /\
	        get_this_qualified_type sGamma = Some Tthis /\
	        static_getType sGamma x = Some Tx /\
	        FindMethodWithName CT C m mdef /\
        qualified_type_subtype CT
          (vpa_mutability_tt_abstract_state Ty (mret (msignature mdef))) Tx /\
        (qualified_type_subtype CT Ty
          (vpa_mutability_tt_abstract_state Ty (mreceiver (msignature mdef))) \/
	         (sqtype Ty = RO /\
	          sqtype (mreceiver (msignature mdef)) = RDM /\
	          base_subtype CT (sbase Ty)
	            (sbase (mreceiver (msignature mdef))))) /\
        Forall2 (fun arg T => qualified_type_subtype CT arg
          (vpa_mutability_tt_abstract_state Ty T))
          argtypes (mparams (msignature mdef)).
  Proof.
    intros sGamma sGamma' x y m args Htyping.
    inversion Htyping; subst;
      try solve [exfalso; eauto];
	      eexists _, _, _, _, _, _;
	      repeat split; eauto.
  Qed.

  Lemma pico_core_concrete_state_call_as_abs :
    forall sGamma sGamma' x y m args,
      stmt_typing CT sGamma ConcreteState
        (SCall x m y args) sGamma' ->
      stmt_typing CT sGamma AbstractState
        (SCall x m y args) sGamma'.
  Proof.
    intros sGamma sGamma' x y m args Htyping.
    inversion Htyping; subst.
    - econstructor; eauto.
    - exfalso. eauto.
  Qed.

  Lemma pico_core_stmt_typing_call_safe_components :
    forall sGamma sGamma' mt x y m args
      (Htyping : stmt_typing CT sGamma mt
        (SCall x m y args) sGamma')
      (Hmt : mt <> AbstractState)
      (Hmt_cs : mt <> ConcreteState),
	      exists Ty C argtypes Tthis Tx mdef,
	        static_getType sGamma y = Some Ty /\
	        sbase Ty = TRef C /\
	        static_getType_list sGamma args = Some argtypes /\
	        get_this_qualified_type sGamma = Some Tthis /\
	        static_getType sGamma x = Some Tx /\
	        FindMethodWithName CT C m mdef /\
        qualified_type_subtype CT
          (vpa_mutability_tt_readonly_state Ty (mret (msignature mdef))) Tx /\
        (qualified_type_subtype CT Ty
          (vpa_mutability_tt_readonly_state Ty (mreceiver (msignature mdef))) \/
	         (sqtype Ty = RO /\
	          sqtype (mreceiver (msignature mdef)) = RDM /\
	          base_subtype CT (sbase Ty)
	            (sbase (mreceiver (msignature mdef))))) /\
        Forall2 (fun arg T => qualified_type_subtype CT arg
          (vpa_mutability_tt_readonly_state Ty T))
          argtypes (mparams (msignature mdef)).
  Proof.
    intros sGamma sGamma' mt x y m args Htyping Hmt Hmt_cs.
    inversion Htyping; subst.
    - destruct Hscope as [Habs | [Hcs _]]; subst; contradiction.
    - eexists _, _, _, _, _, _.
      repeat split; eauto.
  Qed.

  Lemma pico_core_typed_env_receiver_qualifier :
    forall sGamma rGamma h Tthis
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hthis : get_this_qualified_type sGamma = Some Tthis),
      exists receiver qcontext,
        get_this_var_mapping (vars rGamma) = Some receiver /\
        r_muttype h receiver = Some qcontext /\
        qualifier_typable_context qcontext (sqtype Tthis) qcontext.
  Proof.
    intros sGamma rGamma h Tthis Henv Hthis.
    destruct (pico_core_typed_env_receiver CT sGamma rGamma h Henv)
      as (qcontext & receiver & Hreceiver & Hqcontext).
    exists receiver, qcontext.
    split; [exact Hreceiver |].
    split; [exact Hqcontext |].
    pose proof (pico_core_typed_env_wf_config CT sGamma rGamma h Henv)
      as Hconfig.
    unfold wf_r_config in Hconfig.
    destruct Hconfig as (_ & _ & _ & Hwf_senv & _ & Hcorr).
    assert (Hthis_nth : nth_error sGamma 0 = Some Tthis).
    { eapply get_this_qualified_type_nth_error; eauto. }
    specialize (Hcorr receiver qcontext Hreceiver Hqcontext 0).
    assert (Hzero : 0 < length sGamma).
    { unfold wf_senv in Hwf_senv. destruct Hwf_senv as [Hdom _]. exact Hdom. }
    specialize (Hcorr Hzero Tthis Hthis_nth).
    assert (Hreceiver_value :
      runtime_getVal rGamma 0 = Some (Iot receiver)).
    { eapply get_this_var_mapping_runtime_getVal; eauto. }
    rewrite Hreceiver_value in Hcorr.
    unfold wf_r_typable in Hcorr.
    destruct (r_type h receiver) as [rqt |] eqn:Hruntime_type;
      try contradiction.
    destruct Hcorr as [_ Hqualifier].
    assert (Hq_eq : qcontext = rqtype rqt).
    {
      unfold r_muttype, r_type in Hqcontext.
      destruct (runtime_getObj h receiver) as [o |] eqn:Hobj;
        try discriminate.
      unfold r_type in Hruntime_type.
      rewrite Hobj in Hruntime_type.
      inversion Hruntime_type; subst rqt.
      inversion Hqcontext. reflexivity.
    }
    subst qcontext.
    exact Hqualifier.
  Qed.

  (** The source receiver of a call is typed in the caller's viewpoint.  This
      is the shared runtime fact used to move from the caller frame to the
      dynamically selected callee frame. *)
  Lemma pico_core_typed_call_receiver_qualifiers :
    forall sGamma rGamma h y Ty Tthis loc
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hget_y : static_getType sGamma y = Some Ty)
      (Hthis : get_this_qualified_type sGamma = Some Tthis)
      (Hvalue_y : runtime_getVal rGamma y = Some (Iot loc)),
      exists outer qouter qinner,
        get_this_var_mapping (vars rGamma) = Some outer /\
        r_muttype h outer = Some qouter /\
        r_muttype h loc = Some qinner /\
        qualifier_typable_context qouter (sqtype Tthis) qouter /\
        qualifier_typable_context qinner (sqtype Ty) qouter.
  Proof.
    intros sGamma rGamma h y Ty Tthis loc Henv Hget_y Hthis Hvalue_y.
    destruct
      (pico_core_typed_env_receiver_qualifier
        sGamma rGamma h Tthis Henv Hthis)
      as (outer & qouter & Houter & Hqouter & Houter_qualifier).
    destruct
      (pico_core_typed_env_lookup_at_context
        sGamma rGamma h qouter outer Henv Houter Hqouter
        y Ty Hget_y)
      as (value_y & Hruntime_y & Htyped_y).
    assert (Hvalue_eq : value_y = Iot loc) by congruence.
    subst value_y.
    unfold pico_core_typed_value, wf_r_typable in Htyped_y.
    unfold r_type in Htyped_y.
    destruct (runtime_getObj h loc) as [o |] eqn:Hobj;
      try contradiction.
    exists outer, qouter, (rqtype (rt_type o)).
    split; [exact Houter |].
    split; [exact Hqouter |].
    split.
    - unfold r_muttype. rewrite Hobj. reflexivity.
    - split; [exact Houter_qualifier | exact (proj2 Htyped_y)].
  Qed.

  (** Call-frame construction for the ordinary AbstractState receiver rule.
      All premises are produced by the source call rule, dynamic lookup, and
      [wf_method]; no method-body or runtime-frame fact is supplied by a
      client.  The readonly/RDM exception is handled separately because its
      proof additionally uses the call result constraint. *)
  Lemma pico_core_typed_location_call_receiver_abstract_state_regular :
    forall h loc Ty Treceiver qinner qouter
      (Hsource : pico_core_typed_value CT h qouter Ty (Iot loc))
      (Hqinner : r_muttype h loc = Some qinner)
      (Hrcv_sub : qualified_type_subtype CT Ty
        (vpa_mutability_tt_abstract_state Ty Treceiver)),
      pico_core_typed_value CT h qinner Treceiver (Iot loc).
  Proof.
    intros h loc Ty Treceiver qinner qouter Hsource Hqinner Hrcv_sub.
    unfold pico_core_typed_value, wf_r_typable in Hsource |- *.
    unfold r_type in Hsource |- *.
    destruct (runtime_getObj h loc) as [o |] eqn:Hobj;
      try contradiction.
    destruct o as [runtime_type fields].
    destruct runtime_type as [qruntime C].
    simpl in Hsource |- *.
    destruct Hsource as [Hbase Hqualifier].
    unfold r_muttype, r_type in Hqinner.
    rewrite Hobj in Hqinner.
    simpl in Hqinner.
    injection Hqinner as Hqinner_eq.
    subst qinner.
    split.
    - apply qualified_type_subtype_base_subtype in Hrcv_sub.
      rewrite vpa_mutability_tt_sbase_abstract_state in Hrcv_sub.
      eapply base_trans; eauto.
    - apply qualified_type_subtype_q_subtype in Hrcv_sub.
      rewrite (sq_vpa_tt_eq_qq_abstract_state Ty Treceiver) in Hrcv_sub.
      destruct qruntime; destruct qouter;
      destruct (sqtype Ty); destruct (sqtype Treceiver);
        simpl in *;
        try solve [inversion Hrcv_sub];
        try solve [exfalso; eapply lost_subtype_refl; exact Hrcv_sub];
        eauto.
  Qed.

  (** Flexible overriding: a callee frame typed against the statically
      selected signature is also typed against any signature refining it,
      in particular the dynamically selected one. *)
  Lemma pico_core_typed_env_refine_frame :
    forall h ly vals cy child parent,
      method_signature_refinement CT child parent ->
      pico_core_typed_env CT (mreceiver parent :: mparams parent)
        (mkr_env (Iot ly :: vals)) h ->
      r_basetype h ly = Some cy ->
      base_subtype CT (TRef cy) (sbase (mreceiver child)) ->
      pico_core_typed_env CT (mreceiver child :: mparams child)
        (mkr_env (Iot ly :: vals)) h.
  Proof.
    intros h ly vals cy child parent Hrefine Henv Hbase Hsub.
    destruct Henv as (qcontext & receiver & Hwf & Hthis & Hmut & Htyped).
    simpl in Hthis. injection Hthis as <-.
    have Hwf_child := refinement_preserves_callee_frame CT h ly vals cy
      child parent Hrefine Hwf Hbase Hsub.
    exists qcontext, ly.
    split; [exact Hwf_child |].
    split; [reflexivity |].
    split; [exact Hmut |].
    intros x T Hx.
    have Hwf_copy := Hwf_child.
    destruct Hwf_copy as [_ [_ [_ [_ [_ Hcorr]]]]].
    have Hxdom := Hx. apply static_getType_dom in Hxdom.
    have Hentry := Hcorr ly qcontext eq_refl Hmut x Hxdom T Hx.
    revert Hentry.
    destruct (runtime_getVal (mkr_env (Iot ly :: vals)) x) as [v |] eqn:Hv;
      intros Hentry; [| contradiction].
    exists v. split; [reflexivity |].
    destruct v as [| loc | n].
    - destruct x as [| i].
      + simpl in Hv. discriminate.
      + have Hlength := method_signature_refinement_params_length CT
          child parent Hrefine.
        assert (Hi : i < length (mparams parent)).
        { rewrite <- Hlength. apply nth_error_Some.
          unfold static_getType in Hx. simpl in Hx. rewrite Hx. discriminate. }
        destruct (nth_error_Some_exists (mparams parent) i Hi)
          as [Tparent HTparent].
        destruct (Htyped (S i) Tparent HTparent) as [v' [Hv' Hparent_typed]].
        rewrite Hv in Hv'. injection Hv' as <-.
        simpl in Hparent_typed.
        unfold static_getType in Hx. simpl in Hx.
        exact (refinement_preserves_ref_parameter CT child parent Hrefine
          i Tparent T HTparent Hx Hparent_typed).
    - exact Hentry.
    - exact Hentry.
  Qed.

  Lemma pico_core_typed_call_frame_abstract_state_regular :
    forall sGamma rGamma h y args vals Ty argtypes Tthis loc C mdef
      declaring_class
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hget_y : static_getType sGamma y = Some Ty)
      (Hget_args : static_getType_list sGamma args = Some argtypes)
      (Hthis : get_this_qualified_type sGamma = Some Tthis)
      (Hreceiver : runtime_getVal rGamma y = Some (Iot loc))
      (Hbase : r_basetype h loc = Some C)
      (Hargs : runtime_lookup_list rGamma args = Some vals)
      (Hwf_method : wf_method CT declaring_class mdef)
      (Hrcv_sub : qualified_type_subtype CT Ty
        (vpa_mutability_tt_abstract_state Ty
          (mreceiver (msignature mdef))))
      (Harg_sub : Forall2 (fun arg T => qualified_type_subtype CT arg
        (vpa_mutability_tt_abstract_state Ty T))
        argtypes (mparams (msignature mdef))),
      pico_core_typed_env CT
        (mreceiver (msignature mdef) :: mparams (msignature mdef))
        (mkr_env (Iot loc :: vals)) h.
  Proof.
    intros sGamma rGamma h y args vals Ty argtypes Tthis loc C mdef
      declaring_class Henv Hget_y Hget_args Hthis Hreceiver Hbase Hargs
      Hwf_method Hrcv_sub Harg_sub.
    destruct
      (pico_core_typed_call_receiver_qualifiers
        sGamma rGamma h y Ty Tthis loc
        Henv Hget_y Hthis Hreceiver)
      as (outer & qouter & qinner & Houter & Hqouter & Hqinner &
          Houter_qualifier & Hinner_qualifier).
    destruct
      (pico_core_typed_env_lookup_at_context
        sGamma rGamma h qouter outer Henv Houter Hqouter
        y Ty Hget_y)
      as (value_y & Hruntime_y & Htyped_y).
    assert (Hvalue_y : value_y = Iot loc) by congruence.
    subst value_y.
    assert (Hreceiver_typed :
      pico_core_typed_value CT h qinner
        (mreceiver (msignature mdef)) (Iot loc)).
    {
      eapply pico_core_typed_value_env_independent.
      eapply pico_core_typed_location_call_receiver_abstract_state_regular;
        eauto.
    }
    assert (Hparams : forall i T,
      nth_error (mparams (msignature mdef)) i = Some T ->
      exists v,
        nth_error vals i = Some v /\
        pico_core_typed_value CT h
          qinner T v).
    {
      eapply pico_core_typed_call_params_abstract_state
        with (argtypes := argtypes) (Ty := Ty)
          (outer := outer) (qouter := qouter);
        eauto.
    }
    assert (Hlength : length (mparams (msignature mdef)) = length vals).
    {
      apply Forall2_length in Harg_sub.
      apply static_getType_list_preserves_length in Hget_args.
      apply runtime_lookup_list_preserves_length in Hargs.
      lia.
    }
    pose proof (pico_core_typed_env_wf_config CT sGamma rGamma h Henv)
      as Hconfig.
    unfold wf_r_config in Hconfig.
    destruct Hconfig as
      (Hwf_CT & Hwf_heap & Hcaller_renv & Hcaller_senv & Hcaller_len &
        Hcaller_corr).
    assert (Hframe_renv : wf_renv CT (mkr_env (Iot loc :: vals)) h).
    {
      eapply pico_core_resolved_method_frame_wf_renv; eauto.
    }
    unfold wf_method in Hwf_method.
    destruct Hwf_method as
      (Hreturn_wf & body_sGamma' & body_ret_type & Hbody_typing & Hret_dom &
        Hret_type & Hret_subtype & Hoverride).
    eapply pico_core_typed_method_frame_env with (qinner := qinner);
      eauto.
    eapply stmt_typing_wf_env; eauto.
  Qed.

  Lemma pico_core_typed_location_call_receiver_readonly_state_regular :
    forall h loc Ty Treceiver qinner qouter
      (Hsource : pico_core_typed_value CT h qouter Ty (Iot loc))
      (Hqinner : r_muttype h loc = Some qinner)
      (Hrcv_sub : qualified_type_subtype CT Ty
        (vpa_mutability_tt_readonly_state Ty Treceiver)),
      pico_core_typed_value CT h qinner Treceiver (Iot loc).
  Proof.
    intros h loc Ty Treceiver qinner qouter Hsource Hqinner Hrcv_sub.
    unfold pico_core_typed_value, wf_r_typable in Hsource |- *.
    unfold r_type in Hsource |- *.
    destruct (runtime_getObj h loc) as [o |] eqn:Hobj;
      try contradiction.
    destruct o as [runtime_type fields].
    destruct runtime_type as [qruntime C].
    simpl in Hsource |- *.
    destruct Hsource as [Hbase Hqualifier].
    unfold r_muttype, r_type in Hqinner.
    rewrite Hobj in Hqinner.
    simpl in Hqinner.
    injection Hqinner as Hqinner_eq.
    subst qinner.
    split.
    - apply qualified_type_subtype_base_subtype in Hrcv_sub.
      rewrite vpa_mutability_tt_sbase_readonly_state in Hrcv_sub.
      eapply base_trans; eauto.
    - apply qualified_type_subtype_q_subtype in Hrcv_sub.
      rewrite (sq_vpa_tt_eq_qq_readonly_state Ty Treceiver) in Hrcv_sub.
      destruct qruntime; destruct qouter;
      destruct (sqtype Ty); destruct (sqtype Treceiver);
        simpl in *;
        try solve [inversion Hrcv_sub];
        try solve [exfalso; eapply lost_subtype_refl; exact Hrcv_sub];
        eauto.
  Qed.

  Lemma pico_core_typed_call_frame_readonly_state_regular :
    forall sGamma rGamma h y args vals Ty argtypes Tthis loc C mdef
      declaring_class
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hget_y : static_getType sGamma y = Some Ty)
      (Hget_args : static_getType_list sGamma args = Some argtypes)
      (Hthis : get_this_qualified_type sGamma = Some Tthis)
      (Hreceiver : runtime_getVal rGamma y = Some (Iot loc))
      (Hbase : r_basetype h loc = Some C)
      (Hargs : runtime_lookup_list rGamma args = Some vals)
      (Hwf_method : wf_method CT declaring_class mdef)
      (Hrcv_sub : qualified_type_subtype CT Ty
        (vpa_mutability_tt_readonly_state Ty
          (mreceiver (msignature mdef))))
      (Harg_sub : Forall2 (fun arg T => qualified_type_subtype CT arg
        (vpa_mutability_tt_readonly_state Ty T))
        argtypes (mparams (msignature mdef))),
      pico_core_typed_env CT
        (mreceiver (msignature mdef) :: mparams (msignature mdef))
        (mkr_env (Iot loc :: vals)) h.
  Proof.
    intros sGamma rGamma h y args vals Ty argtypes Tthis loc C mdef
      declaring_class Henv Hget_y Hget_args Hthis Hreceiver Hbase Hargs
      Hwf_method Hrcv_sub Harg_sub.
    destruct
      (pico_core_typed_call_receiver_qualifiers
        sGamma rGamma h y Ty Tthis loc
        Henv Hget_y Hthis Hreceiver)
      as (outer & qouter & qinner & Houter & Hqouter & Hqinner &
          Houter_qualifier & Hinner_qualifier).
    destruct
      (pico_core_typed_env_lookup_at_context
        sGamma rGamma h qouter outer Henv Houter Hqouter
        y Ty Hget_y)
      as (value_y & Hruntime_y & Htyped_y).
    assert (Hvalue_y : value_y = Iot loc) by congruence.
    subst value_y.
    assert (Hreceiver_typed :
      pico_core_typed_value CT h qinner
        (mreceiver (msignature mdef)) (Iot loc)).
    {
      eapply pico_core_typed_value_env_independent.
      eapply pico_core_typed_location_call_receiver_readonly_state_regular; eauto.
    }
    assert (Hparams : forall i T,
      nth_error (mparams (msignature mdef)) i = Some T ->
      exists v,
        nth_error vals i = Some v /\
        pico_core_typed_value CT h
          qinner T v).
    {
      eapply pico_core_typed_call_params_readonly_state
        with (argtypes := argtypes) (Ty := Ty)
          (outer := outer) (qouter := qouter);
        eauto.
    }
    assert (Hlength : length (mparams (msignature mdef)) = length vals).
    {
      apply Forall2_length in Harg_sub.
      apply static_getType_list_preserves_length in Hget_args.
      apply runtime_lookup_list_preserves_length in Hargs.
      lia.
    }
    pose proof (pico_core_typed_env_wf_config CT sGamma rGamma h Henv)
      as Hconfig.
    unfold wf_r_config in Hconfig.
    destruct Hconfig as
      (Hwf_CT & Hwf_heap & Hcaller_renv & Hcaller_senv & Hcaller_len &
        Hcaller_corr).
    assert (Hframe_renv : wf_renv CT (mkr_env (Iot loc :: vals)) h).
    {
      eapply pico_core_resolved_method_frame_wf_renv; eauto.
    }
    unfold wf_method in Hwf_method.
    destruct Hwf_method as
      (Hreturn_wf & body_sGamma' & body_ret_type & Hbody_typing & Hret_dom &
        Hret_type & Hret_subtype & Hoverride).
    eapply pico_core_typed_method_frame_env with (qinner := qinner);
      eauto.
    eapply stmt_typing_wf_env; eauto.
  Qed.

  Lemma pico_core_typed_resolved_method_return_abstract_state :
    forall sGamma sGamma' caller h x y m args loc C mdef vals
      body_sGamma' body_ret_type callee h' retval
      (Htyping : stmt_typing CT sGamma AbstractState
        (SCall x m y args) sGamma')
      (Hcaller : pico_core_typed_env CT sGamma caller h)
      (Hreceiver : runtime_getVal caller y = Some (Iot loc))
      (Hbase : r_basetype h loc = Some C)
      (Hfind : FindMethodWithName CT C m mdef)
      (Hargs : runtime_lookup_list caller args = Some vals)
      (Hbody_ret_static : static_getType body_sGamma'
        (mreturn (mbody mdef)) = Some body_ret_type)
      (Hbody_return_sub : qualified_type_subtype CT
        body_ret_type (mret (msignature mdef)))
      (Hextend : pico_core_heap_types_extend h h')
      (Hcallee : pico_core_typed_env CT body_sGamma' callee h')
      (Hcallee_receiver : get_this_var_mapping (vars callee) = Some loc)
      (Hretval : runtime_getVal callee (mreturn (mbody mdef)) = Some retval),
      pico_core_typed_env CT sGamma'
        (set_vars caller (update x retval (vars caller))) h'.
  Proof.
    intros sGamma sGamma' caller h x y m args loc C mdef vals
      body_sGamma' body_ret_type callee h' retval
      Htyping Hcaller Hreceiver Hbase Hfind Hargs Hbody_ret_static
      Hbody_return_sub Hextend Hcallee Hcallee_receiver Hretval.
    assert (HsGamma_eq : sGamma' = sGamma) by
      (inversion Htyping; reflexivity).
    destruct
      (pico_core_stmt_typing_call_abs_components
        sGamma sGamma' x y m args Htyping)
	      as (Ty & Cstatic & argtypes & Tthis & Tx & mdef_static
	          & Hget_y & Href_static & Hget_args & Hthis & Hget_x
	          & Hfind_static & Hret_sub & Hrcv_sub & Harg_sub).
    destruct
      (pico_core_typed_resolved_method_static
        sGamma sGamma' caller h AbstractState x y m args loc C mdef vals
        Htyping Hcaller Hreceiver Hbase Hfind Hargs)
	      as (Ty' & Cstatic' & argtypes' & mdef_static' & declaring_class
	          & Hget_y' & Href_static' & Hget_args' & Hfind_static'
	          & Hbase_sub & Hrefine & Hdecl_sub & Hwf_method).
    assert (HTy : Ty = Ty') by congruence.
    subst Ty'.
    assert (Hstatic_eq : mdef_static = mdef_static').
    { eapply find_method_with_name_deterministic; eauto. }
    subst mdef_static'.
    destruct
      (pico_core_typed_call_receiver_qualifiers
        sGamma caller h y Ty Tthis loc Hcaller Hget_y Hthis Hreceiver)
      as (outer & qouter & qinner & Houter & Hqouter & Hqinner &
          Houter_context & Hreceiver_context).
    assert (Hqouter' : r_muttype h' outer = Some qouter).
    { eapply pico_core_r_muttype_heap_types_extend; eauto. }
    assert (Hqinner' : r_muttype h' loc = Some qinner).
    { eapply pico_core_r_muttype_heap_types_extend; eauto. }
    pose proof (pico_core_typed_env_wf_config CT body_sGamma' callee h' Hcallee)
      as Hcallee_config.
    destruct Hcallee_config as [Hwf_CT [Hwf_heap' Hcallee_config]].
    assert (Hcaller' : pico_core_typed_env CT sGamma caller h').
    { eapply pico_core_typed_env_heap_types_extend; eauto. }
    destruct
      (pico_core_typed_env_lookup_at_context
        body_sGamma' callee h' qinner loc Hcallee Hcallee_receiver Hqinner'
        (mreturn (mbody mdef)) body_ret_type Hbody_ret_static)
      as (return_value & Hreturn_value & Hreturn_typed).
    assert (Hreturn_eq : return_value = retval) by congruence.
    subst return_value.
    assert (Hreturn_target : pico_core_typed_value CT h' qouter Tx retval).
    {
      destruct
        (pico_core_typed_env_lookup_at_context
          sGamma caller h' qouter outer Hcaller' Houter Hqouter' y Ty Hget_y)
        as (value_y & Hvalue_y & Hreceiver_typed).
      rewrite Hreceiver in Hvalue_y. injection Hvalue_y as <-.
      eapply pico_core_typed_return_value_refined_abstract_state
        with (C := C) (Ty := Ty) (Tbody := body_ret_type)
          (child := msignature mdef) (parent := msignature mdef_static).
      - exact Hwf_CT.
      - exact Hwf_heap'.
      - eapply pico_core_r_basetype_heap_types_extend; eauto.
      - exact Hqinner'.
      - exact Hreceiver_typed.
      - exact Hrefine.
      - rewrite (wf_method_receiver_class CT declaring_class mdef Hwf_method).
        apply base_ref. exact Hdecl_sub.
      - exact Hreturn_typed.
      - exact Hbody_return_sub.
      - exact Hret_sub.
    }
    rewrite HsGamma_eq.
    eapply pico_core_typed_env_update_value with (Tx := Tx).
    - exact Hcaller'.
    - exact Hget_x.
    - inversion Htyping; eauto.
    - intros qcontext receiver' Hreceiver' Hqcontext'.
      assert (Hreceiver_eq : receiver' = outer) by congruence.
      subst receiver'.
      assert (Hqcontext_eq : qcontext = qouter) by congruence.
      subst qcontext.
      eapply pico_core_typed_value_env_independent; eauto.
  Qed.

  Lemma pico_core_typed_resolved_method_return_readonly_state :
    forall sGamma sGamma' mt caller h x y m args loc C mdef vals
      body_sGamma' body_ret_type callee h' retval
      (Hmt : mt <> AbstractState)
      (Hmt_cs : mt <> ConcreteState)
      (Htyping : stmt_typing CT sGamma mt
        (SCall x m y args) sGamma')
      (Hcaller : pico_core_typed_env CT sGamma caller h)
      (Hreceiver : runtime_getVal caller y = Some (Iot loc))
      (Hbase : r_basetype h loc = Some C)
      (Hfind : FindMethodWithName CT C m mdef)
      (Hargs : runtime_lookup_list caller args = Some vals)
      (Hbody_ret_static : static_getType body_sGamma'
        (mreturn (mbody mdef)) = Some body_ret_type)
      (Hbody_return_sub : qualified_type_subtype CT
        body_ret_type (mret (msignature mdef)))
      (Hextend : pico_core_heap_types_extend h h')
      (Hcallee : pico_core_typed_env CT body_sGamma' callee h')
      (Hcallee_receiver : get_this_var_mapping (vars callee) = Some loc)
      (Hretval : runtime_getVal callee (mreturn (mbody mdef)) = Some retval),
      pico_core_typed_env CT sGamma'
        (set_vars caller (update x retval (vars caller))) h'.
  Proof.
    intros sGamma sGamma' mt caller h x y m args loc C mdef vals
      body_sGamma' body_ret_type callee h' retval Hmt Hmt_cs Htyping Hcaller
      Hreceiver Hbase Hfind Hargs Hbody_ret_static Hbody_return_sub Hextend
      Hcallee Hcallee_receiver Hretval.
    assert (HsGamma_eq : sGamma' = sGamma) by
      (inversion Htyping; reflexivity).
    destruct
      (pico_core_stmt_typing_call_safe_components
        sGamma sGamma' mt x y m args Htyping Hmt Hmt_cs)
	      as (Ty & Cstatic & argtypes & Tthis & Tx & mdef_static
	          & Hget_y & Href_static & Hget_args & Hthis & Hget_x
	          & Hfind_static & Hret_sub & Hrcv_sub & Harg_sub).
    destruct
      (pico_core_typed_resolved_method_static
        sGamma sGamma' caller h mt x y m args loc C mdef vals
        Htyping Hcaller Hreceiver Hbase Hfind Hargs)
	      as (Ty' & Cstatic' & argtypes' & mdef_static' & declaring_class
	          & Hget_y' & Href_static' & Hget_args' & Hfind_static'
	          & Hbase_sub & Hrefine & Hdecl_sub & Hwf_method).
    assert (HTy : Ty = Ty') by congruence.
    subst Ty'.
    assert (Hstatic_eq : mdef_static = mdef_static').
    { eapply find_method_with_name_deterministic; eauto. }
    subst mdef_static'.
    destruct
      (pico_core_typed_call_receiver_qualifiers
        sGamma caller h y Ty Tthis loc Hcaller Hget_y Hthis Hreceiver)
      as (outer & qouter & qinner & Houter & Hqouter & Hqinner &
          Houter_context & Hreceiver_context).
    assert (Hqouter' : r_muttype h' outer = Some qouter).
    { eapply pico_core_r_muttype_heap_types_extend; eauto. }
    assert (Hqinner' : r_muttype h' loc = Some qinner).
    { eapply pico_core_r_muttype_heap_types_extend; eauto. }
    pose proof (pico_core_typed_env_wf_config CT body_sGamma' callee h' Hcallee)
      as Hcallee_config.
    destruct Hcallee_config as [Hwf_CT [Hwf_heap' Hcallee_config]].
    assert (Hcaller' : pico_core_typed_env CT sGamma caller h').
    { eapply pico_core_typed_env_heap_types_extend; eauto. }
    destruct
      (pico_core_typed_env_lookup_at_context
        body_sGamma' callee h' qinner loc Hcallee Hcallee_receiver Hqinner'
        (mreturn (mbody mdef)) body_ret_type Hbody_ret_static)
      as (return_value & Hreturn_value & Hreturn_typed).
    assert (Hreturn_eq : return_value = retval) by congruence.
    subst return_value.
    assert (Hreturn_target : pico_core_typed_value CT h' qouter Tx retval).
    {
      destruct
        (pico_core_typed_env_lookup_at_context
          sGamma caller h' qouter outer Hcaller' Houter Hqouter' y Ty Hget_y)
        as (value_y & Hvalue_y & Hreceiver_typed).
      rewrite Hreceiver in Hvalue_y. injection Hvalue_y as <-.
      eapply pico_core_typed_return_value_refined_readonly_state
        with (C := C) (Ty := Ty) (Tbody := body_ret_type)
          (child := msignature mdef) (parent := msignature mdef_static).
      - exact Hwf_CT.
      - exact Hwf_heap'.
      - eapply pico_core_r_basetype_heap_types_extend; eauto.
      - exact Hqinner'.
      - exact Hreceiver_typed.
      - exact Hrefine.
      - rewrite (wf_method_receiver_class CT declaring_class mdef Hwf_method).
        apply base_ref. exact Hdecl_sub.
      - exact Hreturn_typed.
      - exact Hbody_return_sub.
      - exact Hret_sub.
    }
    rewrite HsGamma_eq.
    eapply pico_core_typed_env_update_value with (Tx := Tx).
    - exact Hcaller'.
    - exact Hget_x.
    - inversion Htyping; eauto.
    - intros qcontext receiver' Hreceiver' Hqcontext'.
      assert (Hreceiver_eq : receiver' = outer) by congruence.
      subst receiver'.
      assert (Hqcontext_eq : qcontext = qouter) by congruence.
      subst qcontext.
      eapply pico_core_typed_value_env_independent; eauto.
  Qed.

  Lemma pico_core_typed_resolved_method_return :
    forall sGamma sGamma' mt caller h x y m args loc C mdef vals
      body_sGamma' body_ret_type callee h' retval
      (Htyping : stmt_typing CT sGamma mt
        (SCall x m y args) sGamma')
      (Hcaller : pico_core_typed_env CT sGamma caller h)
      (Hreceiver : runtime_getVal caller y = Some (Iot loc))
      (Hbase : r_basetype h loc = Some C)
      (Hfind : FindMethodWithName CT C m mdef)
      (Hargs : runtime_lookup_list caller args = Some vals)
      (Hbody_ret_static : static_getType body_sGamma'
        (mreturn (mbody mdef)) = Some body_ret_type)
      (Hbody_return_sub : qualified_type_subtype CT
        body_ret_type (mret (msignature mdef)))
      (Hextend : pico_core_heap_types_extend h h')
      (Hcallee : pico_core_typed_env CT body_sGamma' callee h')
      (Hcallee_receiver : get_this_var_mapping (vars callee) = Some loc)
      (Hretval : runtime_getVal callee (mreturn (mbody mdef)) = Some retval),
      pico_core_typed_env CT sGamma'
        (set_vars caller (update x retval (vars caller))) h'.
  Proof.
    intros sGamma sGamma' mt caller h x y m args loc C mdef vals
      body_sGamma' body_ret_type callee h' retval Htyping Hcaller Hreceiver
      Hbase Hfind Hargs Hbody_ret_static Hbody_return_sub Hextend Hcallee
      Hcallee_receiver Hretval.
    destruct mt.
    - eapply pico_core_typed_resolved_method_return_abstract_state; eauto.
    - eapply pico_core_typed_resolved_method_return_abstract_state; eauto.
      eapply pico_core_concrete_state_call_as_abs; eauto.
    - change (stmt_typing CT sGamma ReadonlyState
        (SCall x m y args) sGamma') in Htyping.
      assert (Hsafe : ReadonlyState <> AbstractState) by discriminate.
      assert (Hsafe_cs : ReadonlyState <> ConcreteState) by discriminate.
      exact
        (pico_core_typed_resolved_method_return_readonly_state
          sGamma sGamma' ReadonlyState caller h x y m args loc C mdef vals
          body_sGamma' body_ret_type callee h' retval Hsafe Hsafe_cs Htyping Hcaller
          Hreceiver Hbase Hfind Hargs Hbody_ret_static Hbody_return_sub
          Hextend Hcallee Hcallee_receiver Hretval).
    - change (stmt_typing CT sGamma TransitiveState
        (SCall x m y args) sGamma') in Htyping.
      assert (Hconcrete : TransitiveState <> AbstractState) by discriminate.
      assert (Hconcrete_cs : TransitiveState <> ConcreteState) by discriminate.
      exact
        (pico_core_typed_resolved_method_return_readonly_state
          sGamma sGamma' TransitiveState caller h x y m args loc C mdef vals
          body_sGamma' body_ret_type callee h' retval Hconcrete Hconcrete_cs
          Htyping Hcaller
          Hreceiver Hbase Hfind Hargs Hbody_ret_static Hbody_return_sub
          Hextend Hcallee Hcallee_receiver Hretval).
  Qed.

  Lemma pico_core_typed_env_after_assign_null :
    forall sGamma sGamma' rGamma h mt x
      (Htyping : stmt_typing CT sGamma mt (SVarAss x ENull) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h),
      pico_core_typed_env CT sGamma'
        (set_vars rGamma (update x Null_a (vars rGamma))) h.
  Proof.
    intros sGamma sGamma' rGamma h mt x Htyping Henv.
    pose proof
      (pico_core_typed_env_real_lr_env sGamma rGamma h Henv)
      as Hreal.
    pose proof
      (pico_typed_runtime_env_after_varass_null
        CT sGamma mt x sGamma' rGamma h Htyping Hreal)
      as Hreal_next.
    pose proof
      (pico_typed_runtime_env_wf_config
        CT sGamma' (set_vars rGamma (update x Null_a (vars rGamma))) h
        Hreal_next) as Hwf_next.
    inversion Htyping; subst sGamma'.
    eapply pico_core_typed_env_after_update; eauto.
    intros qcontext receiver Hreceiver Hqcontext.
    unfold pico_core_typed_value; simpl.
    inversion Htype_e; subst.
    apply (pico_core_subtype_preserves_reference
      {| sqtype := q; sbase := TRef class_name |} Tx).
    - eexists; reflexivity.
    - exact Hsub.
  Qed.

  Lemma pico_core_typed_env_after_local :
    forall sGamma sGamma' rGamma h mt T x
      (Htyping : stmt_typing CT sGamma mt (SLocal T x) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h),
      pico_core_typed_env CT sGamma'
        (set_vars rGamma (vars rGamma ++ [default_value T])) h.
  Proof.
    intros sGamma sGamma' rGamma h mt T x Htyping Henv.
    pose proof
      (pico_core_typed_env_real_lr_env sGamma rGamma h Henv)
      as Hreal.
    pose proof
      (pico_typed_runtime_env_after_local
        CT sGamma mt T x sGamma' rGamma h Htyping Hreal)
      as Hreal_next.
    destruct Henv as
      (qcontext & receiver & Hwf & Hreceiver & Hqcontext & Hvalues).
    inversion Htyping; subst sGamma'.
    destruct Hreal_next as
      (qcontext_next & receiver_next & Hwf_next &
        Hreceiver_next & Hqcontext_next).
    assert (Hreceiver_eq : receiver_next = receiver).
    {
      rewrite get_this_var_mapping_update_vars_app_default in Hreceiver_next.
      congruence.
    }
    subst receiver_next.
    assert (Hqcontext_eq : qcontext_next = qcontext) by congruence.
    subst qcontext_next.
    exists qcontext, receiver.
    split; [exact Hwf_next |].
    split; [exact Hreceiver_next |].
    split; [exact Hqcontext_next |].
    intros i Ti Hstatic.
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [_ [_ [Hlength _]]]]].
    destruct (Nat.lt_ge_cases i (length sGamma)) as [Hold_index | Hnew_index].
    - assert (Hstatic_old : static_getType sGamma i = Some Ti).
      {
        unfold static_getType in *.
        rewrite nth_error_app1 in Hstatic; [exact Hstatic | exact Hold_index].
      }
      destruct (Hvalues i Ti Hstatic_old) as (old & Hruntime & Htyped).
      exists old.
      split.
      + unfold runtime_getVal, set_vars in *.
        rewrite nth_error_app1.
        * exact Hruntime.
        * rewrite <- Hlength.
          exact Hold_index.
      + eapply pico_core_typed_value_env_independent; eauto.
    - assert (Hbound : i < length sGamma + 1).
      {
        apply static_getType_dom in Hstatic.
        rewrite length_app in Hstatic.
        simpl in Hstatic.
        exact Hstatic.
      }
      assert (Heq : i = length sGamma) by lia.
      subst i.
      assert (Ti = T) as ->.
      {
        unfold static_getType in Hstatic.
        pose proof
          (@nth_error_app2 qualified_type sGamma [T] (length sGamma)
            (Nat.le_refl _)) as Happ.
        rewrite Nat.sub_diag in Happ.
        simpl in Happ.
        rewrite Happ in Hstatic.
        inversion Hstatic.
        reflexivity.
      }
      exists (default_value T).
      split.
      + unfold runtime_getVal, set_vars.
        rewrite nth_error_app2; [| lia].
        replace (length sGamma - length (vars rGamma)) with 0 by lia.
        reflexivity.
      + apply pico_core_typed_value_default.
  Qed.

  Lemma pico_core_typed_env_after_assign_int :
    forall sGamma rGamma h mt x n
      (Htyping : stmt_typing CT sGamma mt (SVarAss x (EInt n)) sGamma)
      (Henv : pico_core_typed_env CT sGamma rGamma h),
      pico_core_typed_env CT sGamma
        (set_vars rGamma (update x (Int n) (vars rGamma))) h.
  Proof.
    intros sGamma rGamma h mt x n Htyping Henv.
    inversion Htyping; subst.
    inversion Htype_e; subst.
    pose proof
      (pico_core_typed_env_wf_config CT sGamma rGamma h Henv)
      as Hconfig.
    destruct Hconfig as [Hwf_CT [Hwf_heap _]].
    eapply pico_core_typed_env_update_value; eauto.
    intros qcontext receiver Hreceiver Hqcontext.
    eapply pico_core_typed_value_subtype; eauto.
    apply pico_core_typed_value_int.
  Qed.

  Lemma pico_core_typed_env_after_assign_var :
    forall sGamma rGamma h mt x y val_y
      (Htyping : stmt_typing CT sGamma mt (SVarAss x (EVar y)) sGamma)
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hy : runtime_getVal rGamma y = Some val_y),
      pico_core_typed_env CT sGamma
        (set_vars rGamma (update x val_y (vars rGamma))) h.
  Proof.
    intros sGamma rGamma h mt x y val_y Htyping Henv Hy.
    inversion Htyping; subst.
    inversion Htype_e; subst.
    pose proof
      (pico_core_typed_env_wf_config CT sGamma rGamma h Henv)
      as Hconfig.
    destruct Hconfig as [Hwf_CT [Hwf_heap _]].
    eapply pico_core_typed_env_update_value; eauto.
    intros qcontext receiver Hreceiver Hqcontext.
    eapply pico_core_typed_value_subtype; eauto.
    eapply pico_core_typed_env_runtime_value; eauto.
  Qed.

  Lemma pico_core_typed_value_after_field_update :
    forall h qcontext T v loc f value o
      (Htyped : pico_core_typed_value CT h qcontext T v)
      (Hobj : runtime_getObj h loc = Some o),
      pico_core_typed_value CT
        (update_field h loc f value) qcontext T v.
  Proof.
    intros h qcontext T v loc f value o Htyped Hobj.
    destruct v as [|loc'|n]; simpl in *; auto.
    unfold wf_r_typable in *.
    rewrite
      (pico_core_r_type_update_field h loc f value o loc' Hobj).
    exact Htyped.
  Qed.

  Lemma pico_core_typed_env_after_fldwrite_success :
    forall sGamma sGamma' rGamma h h' mt x f y loc o a value
      (Htyping : stmt_typing CT sGamma mt (SFldWrite x f y) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hx : runtime_getVal rGamma x = Some (Iot loc))
      (Hobj : runtime_getObj h loc = Some o)
      (Hassign : sf_assignability_rel CT (rctype (rt_type o)) f a)
      (Hy : runtime_getVal rGamma y = Some value)
      (Hassignable :
        runtime_vpa_assignability (rqtype (rt_type o)) a = Assignable)
      (Hheap : h' = update_field h loc f value),
      pico_core_typed_env CT sGamma' rGamma h'.
  Proof.
    intros sGamma sGamma' rGamma h h' mt x f y loc o a value
      Htyping Henv Hx Hobj Hassign Hy Hassignable Hheap.
    pose proof
      (pico_core_typed_env_real_lr_env sGamma rGamma h Henv)
      as Hreal.
    pose proof
      (pico_typed_runtime_env_after_fldwrite_success
        CT sGamma mt x f y sGamma' rGamma h h' loc o a value
        Htyping Hreal Hx Hobj Hassign Hy Hassignable Hheap)
      as Hreal_next.
    pose proof
      (pico_typed_runtime_env_wf_config
        CT sGamma' rGamma h' Hreal_next)
      as Hwf_next.
    destruct Henv as
      (qcontext & receiver & Hwf & Hreceiver & Hqcontext & Hvalues).
    pose proof
      (stmt_typing_fldwrite_result_env
        CT sGamma mt x f y sGamma' Htyping) as Hresult.
    subst sGamma' h'.
    exists qcontext, receiver.
    split; [exact Hwf_next |].
    split; [exact Hreceiver |].
    split.
    - rewrite r_muttype_update_field_preserve.
      exact Hqcontext.
    - intros i T Hstatic.
      destruct (Hvalues i T Hstatic) as (v & Hruntime & Htyped).
      exists v.
      split; [exact Hruntime |].
      eapply pico_core_typed_value_after_field_update; eauto.
  Qed.

  Lemma pico_core_typed_value_heap_extension :
    forall h qcontext T v o
      (Htyped : pico_core_typed_value CT h qcontext T v),
      pico_core_typed_value CT (h ++ [o]) qcontext T v.
  Proof.
    intros h qcontext T v o Htyped.
    destruct v as [|loc|n]; simpl in *; auto.
    eapply heap_extension_preserves_wf_r_typable; eauto.
  Qed.

  Lemma pico_core_typed_env_after_new_success :
    forall sGamma sGamma' rGamma h h' mt x qc C args
      receiver qcontext vals qadapted o
      (Htyping : stmt_typing CT sGamma mt (SNew x qc C args) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hreceiver : runtime_getVal rGamma 0 = Some (Iot receiver))
      (Hargs : runtime_lookup_list rGamma args = Some vals)
      (Hqcontext : r_muttype h receiver = Some qcontext)
      (Hadapt : vpa_mutability_object_creation qcontext qc = qadapted)
      (Hobj : o = mkObj (mkruntime_type qadapted C) vals)
      (Hheap : h' = h ++ [o]),
      pico_core_typed_env CT sGamma'
        (set_vars rGamma (update x (Iot (dom h)) (vars rGamma))) h'.
  Proof.
    intros sGamma sGamma' rGamma h h' mt x qc C args
      receiver qcontext vals qadapted o Htyping Henv
      Hreceiver Hargs Hqcontext Hadapt Hobj Hheap.
    pose proof Htyping as Htyping_copy.
    inversion Htyping; subst sGamma'.
    pose proof
      (pico_core_typed_env_real_lr_env sGamma rGamma h Henv)
      as Hreal.
    pose proof
      (pico_typed_runtime_env_after_new_success
        CT sGamma mt x qc C args sGamma rGamma h h'
        receiver vals qcontext qadapted o
        Htyping_copy Hreal Hreceiver Hargs Hqcontext Hadapt Hobj Hheap)
      as Hreal_next.
    pose proof
      (pico_typed_runtime_env_wf_config
        CT sGamma
        (set_vars rGamma (update x (Iot (dom h)) (vars rGamma)))
        h' Hreal_next)
      as Hwf_next.
    pose proof Hwf_next as Hwf_next_copy.
    destruct Henv as
      (qcontext_old & receiver_old & Hwf_env & Hthis_env & Hmut_env & Hvalues).
    assert (Hreceiver_eq : receiver = receiver_old).
    {
      unfold runtime_getVal in Hreceiver.
      unfold get_this_var_mapping in Hthis_env.
      destruct (vars rGamma) as [|value values] eqn:Hvars;
        try discriminate.
      destruct value as [|loc|n]; try discriminate.
      inversion Hreceiver; inversion Hthis_env; congruence.
    }
    subst receiver_old.
    assert (Hqcontext_eq : qcontext = qcontext_old) by congruence.
    subst qcontext_old h' o.
    assert (Hreceiver_dom : receiver < dom h).
    {
      unfold r_muttype in Hqcontext.
      destruct (runtime_getObj h receiver) as [receiver_obj |] eqn:Hreceiver_obj;
        try discriminate.
      eapply runtime_getObj_dom; eauto.
    }
    assert (Hthis_next :
      get_this_var_mapping
        (vars (set_vars rGamma
          (update x (Iot (dom h)) (vars rGamma)))) = Some receiver).
    {
      simpl.
      rewrite get_this_var_mapping_update_vars_nonzero; eauto.
    }
    assert (Hmut_next :
      r_muttype
        (h ++ [mkObj (mkruntime_type qadapted C) vals]) receiver =
        Some qcontext).
    {
      rewrite r_muttype_app_preserve_old; eauto.
    }
    exists qcontext, receiver.
    split; [exact Hwf_next |].
    split; [exact Hthis_next |].
    split; [exact Hmut_next |].
    intros i T Hstatic.
    destruct (Nat.eq_dec i x) as [Heq | Hneq].
    - subst i.
      rewrite Hget_x in Hstatic.
      inversion Hstatic; subst T.
      exists (Iot (dom h)).
      split.
      + unfold runtime_getVal.
        simpl.
        apply update_same.
        pose proof
          (pico_core_typed_env_wf_config
            CT sGamma rGamma h
            (ex_intro _ qcontext
              (ex_intro _ receiver
                (conj Hwf_env
                  (conj Hthis_env (conj Hqcontext Hvalues))))))
          as Hwf_original.
        unfold wf_r_config in Hwf_original.
        destruct Hwf_original as (_ & _ & _ & _ & Hlength & _).
        rewrite <- Hlength.
        eapply static_getType_dom; eauto.
      + unfold wf_r_config in Hwf_next_copy.
        destruct Hwf_next_copy as
          (_ & _ & _ & _ & Hlength_next & Hcorr_next).
        assert (Hx_dom : x < dom sGamma).
        { eapply static_getType_dom; eauto. }
        specialize
          (Hcorr_next receiver qcontext Hthis_next Hmut_next
            x Hx_dom Tx Hget_x).
        unfold runtime_getVal in Hcorr_next.
        simpl in Hcorr_next.
        rewrite update_same in Hcorr_next.
        * exact Hcorr_next.
        * pose proof Hwf_env as Hwf_env_copy.
          unfold wf_r_config in Hwf_env_copy.
          destruct Hwf_env_copy as
            (_ & _ & _ & _ & Hlength_old & _).
          rewrite <- Hlength_old.
          exact Hx_dom.
    - destruct (Hvalues i T Hstatic) as (v & Hruntime & Htyped).
      exists v.
      split.
      + unfold runtime_getVal in *.
        simpl.
        rewrite update_diff; eauto.
      + eapply pico_core_typed_value_heap_extension; eauto.
  Qed.

  Lemma pico_core_typed_env_after_assign_field_read :
    forall sGamma sGamma' rGamma h sigma mt x y f loc v V V'
      (Htyping :
        stmt_typing CT sGamma mt (SVarAss x (EField y f)) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hreads : pico_core_reads_typed CT h sigma)
      (Hy : runtime_getVal rGamma y = Some (Iot loc))
      (Hread : wm_read sigma V (loc, f) v V'),
      pico_core_typed_env CT sGamma'
        (set_vars rGamma (update x v (vars rGamma))) h.
  Proof.
    intros sGamma sGamma' rGamma h sigma mt x y f loc v V V'
      Htyping Henv Hreads Hy Hread.
    inversion Htyping; subst sGamma'.
    pose proof
      (Hreads
        sGamma mt rGamma x y f Tx Te loc v V V'
        Henv Htype_e Hget_x Hsub Hy Hread)
      as Htyped_v.
    pose proof
      (pico_core_typed_env_real_lr_env sGamma rGamma h Henv)
      as Hreal.
    assert (Hreal_value :
      forall qcontext receiver,
        get_this_var_mapping (vars rGamma) = Some receiver ->
        r_muttype h receiver = Some qcontext ->
        pico_typed_runtime_value CT h qcontext Tx v).
    {
      intros qcontext receiver Hreceiver Hqcontext.
      apply pico_core_typed_value_real_lr_value.
      eapply Htyped_v; eauto.
    }
    pose proof
      (pico_typed_runtime_env_update_value
        CT sGamma rGamma h x Tx v Hreal Hget_x Hnot_rcv Hreal_value)
      as Hreal_next.
    pose proof
      (pico_typed_runtime_env_wf_config
        CT sGamma (set_vars rGamma (update x v (vars rGamma))) h
        Hreal_next) as Hwf_next.
    eapply pico_core_typed_env_after_update; eauto.
  Qed.

  Lemma pico_core_typed_varass_field_step_post :
    forall sGamma sGamma' rGamma h sigma mt x y f V K e' state'
      (Htyping :
        stmt_typing CT sGamma mt (SVarAss x (EField y f)) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hlrstate : pico_core_lr_state CT (mkPicoCoreState h sigma))
      (Hread_typed :
        forall loc v V',
          runtime_getVal rGamma y = Some (Iot loc) ->
          wm_read sigma V (loc, f) v V' ->
          pico_core_typed_env CT sGamma'
            (set_vars rGamma (update x v (vars rGamma))) h)
      (Hstep :
        pico_core_step CT
          (CoreRun rGamma (SVarAss x (EField y f)) V K)
          (mkPicoCoreState h sigma)
          e' state'),
      pico_core_stmt_post sGamma' K e' state'.
  Proof.
    intros sGamma sGamma' rGamma h sigma mt x y f V K e' state'
      Htyping Henv Hlrstate Hread_typed Hstep.
    inversion Hstep; subst; try discriminate; try congruence.
    - apply PCSP_Ok.
      + eapply Hread_typed; eauto.
      + exact Hlrstate.
    - apply PCSP_NPE.
      exact Hlrstate.
  Qed.

  Lemma pico_core_typed_assign_null_step_post :
    forall sGamma rGamma h sigma mt x V K e' state'
      (Htyping : stmt_typing CT sGamma mt (SVarAss x ENull) sGamma)
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hlrstate : pico_core_lr_state CT (mkPicoCoreState h sigma))
      (Hstep :
        pico_core_step CT
          (CoreRun rGamma (SVarAss x ENull) V K)
          (mkPicoCoreState h sigma)
          e' state'),
      pico_core_stmt_post sGamma K e' state'.
  Proof.
    intros sGamma rGamma h sigma mt x V K e' state'
      Htyping Henv Hlrstate Hstep.
    inversion Hstep; subst; try discriminate; try congruence.
    apply PCSP_Ok.
    - eapply pico_core_typed_env_after_assign_null; eauto.
    - exact Hlrstate.
  Qed.

  Lemma pico_core_typed_local_step_post :
    forall sGamma sGamma' rGamma h sigma mt T x V K e' state'
      (Htyping : stmt_typing CT sGamma mt (SLocal T x) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hlrstate : pico_core_lr_state CT (mkPicoCoreState h sigma))
      (Hstep :
        pico_core_step CT
          (CoreRun rGamma (SLocal T x) V K)
          (mkPicoCoreState h sigma)
          e' state'),
      pico_core_stmt_post sGamma' K e' state'.
  Proof.
    intros sGamma sGamma' rGamma h sigma mt T x V K e' state'
      Htyping Henv Hlrstate Hstep.
    inversion Hstep; subst; try discriminate; try congruence.
    apply PCSP_Ok.
    - eapply pico_core_typed_env_after_local; eauto.
    - exact Hlrstate.
  Qed.

  Lemma pico_core_typed_assign_int_step_post :
    forall sGamma rGamma h sigma mt x n V K e' state'
      (Htyping : stmt_typing CT sGamma mt (SVarAss x (EInt n)) sGamma)
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hlrstate : pico_core_lr_state CT (mkPicoCoreState h sigma))
      (Hstep :
        pico_core_step CT
          (CoreRun rGamma (SVarAss x (EInt n)) V K)
          (mkPicoCoreState h sigma)
          e' state'),
      pico_core_stmt_post sGamma K e' state'.
  Proof.
    intros sGamma rGamma h sigma mt x n V K e' state'
      Htyping Henv Hlrstate Hstep.
    inversion Hstep; subst; try discriminate; try congruence.
    apply PCSP_Ok.
    - eapply pico_core_typed_env_after_assign_int; eauto.
    - exact Hlrstate.
  Qed.

  Lemma pico_core_typed_assign_var_step_post :
    forall sGamma rGamma h sigma mt x y V K e' state'
      (Htyping : stmt_typing CT sGamma mt (SVarAss x (EVar y)) sGamma)
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hlrstate : pico_core_lr_state CT (mkPicoCoreState h sigma))
      (Hstep :
        pico_core_step CT
          (CoreRun rGamma (SVarAss x (EVar y)) V K)
          (mkPicoCoreState h sigma)
          e' state'),
      pico_core_stmt_post sGamma K e' state'.
  Proof.
    intros sGamma rGamma h sigma mt x y V K e' state'
      Htyping Henv Hlrstate Hstep.
    inversion Hstep; subst; try discriminate; try congruence.
    apply PCSP_Ok.
    - eapply pico_core_typed_env_after_assign_var; eauto.
    - exact Hlrstate.
  Qed.

  Lemma pico_core_typed_fldwrite_step_post :
    forall sGamma sGamma' rGamma h sigma mt x f y V K e' state'
      (Htyping : stmt_typing CT sGamma mt (SFldWrite x f y) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hlrstate : pico_core_lr_state CT (mkPicoCoreState h sigma))
      (Hstep :
        pico_core_step CT
          (CoreRun rGamma (SFldWrite x f y) V K)
          (mkPicoCoreState h sigma) e' state'),
      pico_core_stmt_post sGamma' K e' state'.
  Proof.
    intros sGamma sGamma' rGamma h sigma mt x f y V K e' state'
      Htyping Henv Hlrstate Hstep.
    pose proof Hstep as Hstep_copy.
    inversion Hstep; subst; try discriminate; try congruence.
    - apply PCSP_Ok.
      + eapply pico_core_typed_env_after_fldwrite_success; eauto.
      + unfold pico_core_lr_state in *.
        eapply pico_core_step_preserves_state_wf; eauto.
    - apply PCSP_NPE.
      exact Hlrstate.
    - apply PCSP_Mutation.
      exact Hlrstate.
  Qed.

  Lemma pico_core_typed_new_step_post :
    forall sGamma sGamma' rGamma h sigma mt x qc C args V K e' state'
      (Htyping : stmt_typing CT sGamma mt (SNew x qc C args) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hlrstate : pico_core_lr_state CT (mkPicoCoreState h sigma))
      (Hstep :
        pico_core_step CT
          (CoreRun rGamma (SNew x qc C args) V K)
          (mkPicoCoreState h sigma) e' state'),
      pico_core_stmt_post sGamma' K e' state'.
  Proof.
    intros sGamma sGamma' rGamma h sigma mt x qc C args V K e' state'
      Htyping Henv Hlrstate Hstep.
    pose proof Hstep as Hstep_copy.
    inversion Hstep; subst; try discriminate; try congruence.
    apply PCSP_Ok.
    - eapply pico_core_typed_env_after_new_success; eauto.
    - unfold pico_core_lr_state in *.
      eapply pico_core_step_preserves_state_wf; eauto.
  Qed.
  (** The readonly/RDM receiver exception is sound because the callee context
      is the receiver object's own runtime qualifier.  This equality is the
      missing ingredient that a standalone subtype statement does not carry. *)
  Lemma pico_core_typed_location_call_receiver_abstract_state_special :
    forall h loc Ty Treceiver qinner qouter
      (Hsource : pico_core_typed_value CT h qouter Ty (Iot loc))
      (Hqinner : r_muttype h loc = Some qinner)
      (Hbase_sub : base_subtype CT (sbase Ty) (sbase Treceiver))
      (Hty_ro : sqtype Ty = RO)
      (Hreceiver_rdm : sqtype Treceiver = RDM),
      pico_core_typed_value CT h qinner Treceiver (Iot loc).
  Proof.
    intros h loc Ty Treceiver qinner qouter Hsource Hqinner Hbase_sub Hty_ro Hreceiver_rdm.
    unfold pico_core_typed_value, wf_r_typable in Hsource |- *.
    unfold r_type in Hsource |- *.
    destruct (runtime_getObj h loc) as [o |] eqn:Hobj;
      try contradiction.
    destruct o as [runtime_type fields].
    destruct runtime_type as [qruntime C].
    simpl in Hsource |- *.
    destruct Hsource as [Hbase Hqualifier].
    unfold r_muttype, r_type in Hqinner.
    rewrite Hobj in Hqinner.
    simpl in Hqinner.
    injection Hqinner as Hqinner_eq.
    subst qinner.
    rewrite Hty_ro in Hqualifier.
    rewrite Hreceiver_rdm.
    split.
    - eapply base_trans; eauto.
    - destruct qruntime; simpl in *; auto.
  Qed.

  Lemma pico_core_typed_call_frame_abstract_state_special :
    forall sGamma rGamma h y args vals Ty argtypes Tthis loc C mdef
      declaring_class
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hget_y : static_getType sGamma y = Some Ty)
      (Hget_args : static_getType_list sGamma args = Some argtypes)
      (Hthis : get_this_qualified_type sGamma = Some Tthis)
      (Hreceiver : runtime_getVal rGamma y = Some (Iot loc))
      (Hbase : r_basetype h loc = Some C)
      (Hargs : runtime_lookup_list rGamma args = Some vals)
      (Hwf_method : wf_method CT declaring_class mdef)
      (Hty_ro : sqtype Ty = RO)
      (Hreceiver_rdm : sqtype (mreceiver (msignature mdef)) = RDM)
      (Hreceiver_base : base_subtype CT (sbase Ty)
        (sbase (mreceiver (msignature mdef))))
      (Harg_sub : Forall2 (fun arg T => qualified_type_subtype CT arg
        (vpa_mutability_tt_abstract_state Ty T))
        argtypes (mparams (msignature mdef))),
      pico_core_typed_env CT
        (mreceiver (msignature mdef) :: mparams (msignature mdef))
        (mkr_env (Iot loc :: vals)) h.
  Proof.
    intros sGamma rGamma h y args vals Ty argtypes Tthis loc C mdef
      declaring_class Henv Hget_y Hget_args Hthis Hreceiver Hbase Hargs
      Hwf_method Hty_ro Hreceiver_rdm Hreceiver_base Harg_sub.
    destruct
      (pico_core_typed_call_receiver_qualifiers
        sGamma rGamma h y Ty Tthis loc
        Henv Hget_y Hthis Hreceiver)
      as (outer & qouter & qinner & Houter & Hqouter & Hqinner &
          Houter_qualifier & Hinner_qualifier).
    destruct
      (pico_core_typed_env_lookup_at_context
        sGamma rGamma h qouter outer Henv Houter Hqouter
        y Ty Hget_y)
      as (value_y & Hruntime_y & Htyped_y).
    assert (Hvalue_y : value_y = Iot loc) by congruence.
    subst value_y.
    assert (Hreceiver_typed :
      pico_core_typed_value CT h qinner
        (mreceiver (msignature mdef)) (Iot loc)).
    {
      eapply pico_core_typed_value_env_independent.
      eapply pico_core_typed_location_call_receiver_abstract_state_special;
        eauto.
    }
    assert (Harg_sub_special : Forall2
      (fun arg T => qualified_type_subtype CT arg
        (vpa_mutability_tt_abstract_state
          {| sqtype := RO; sbase := sbase T |} T))
      argtypes (mparams (msignature mdef))).
    {
      destruct Ty as [qTy cTy].
      simpl in Hty_ro.
      subst qTy.
      exact Harg_sub.
    }
    assert (Hparams : forall i T,
      nth_error (mparams (msignature mdef)) i = Some T ->
      exists v,
        nth_error vals i = Some v /\
        pico_core_typed_value CT h
          qinner T v).
    {
      eapply pico_core_typed_call_params_abstract_state_special
        with (argtypes := argtypes) (outer := outer) (qouter := qouter).
      + exact Henv.
      + exact Houter.
      + exact Hqouter.
      + exact Hget_args.
      + exact Hargs.
      + exact Harg_sub_special.
      + rewrite Hty_ro in Hinner_qualifier.
        exact Hinner_qualifier.
      + exact Hqinner.
    }
    assert (Hlength : length (mparams (msignature mdef)) = length vals).
    {
      apply Forall2_length in Harg_sub.
      apply static_getType_list_preserves_length in Hget_args.
      apply runtime_lookup_list_preserves_length in Hargs.
      lia.
    }
    pose proof (pico_core_typed_env_wf_config CT sGamma rGamma h Henv)
      as Hconfig.
    unfold wf_r_config in Hconfig.
    destruct Hconfig as
      (Hwf_CT & Hwf_heap & Hcaller_renv & Hcaller_senv & Hcaller_len &
        Hcaller_corr).
    assert (Hframe_renv : wf_renv CT (mkr_env (Iot loc :: vals)) h).
    {
      eapply pico_core_resolved_method_frame_wf_renv; eauto.
    }
    unfold wf_method in Hwf_method.
    destruct Hwf_method as
      (Hreturn_wf & body_sGamma' & body_ret_type & Hbody_typing & Hret_dom &
        Hret_type & Hret_subtype & Hoverride).
    eapply pico_core_typed_method_frame_env with (qinner := qinner);
      eauto.
    eapply stmt_typing_wf_env; eauto.
  Qed.

  (** Dynamic call entry for an AbstractState caller.  The method body comes
      from [wf_method], while the two source-rule receiver forms select the
      regular or readonly/RDM frame proof above. *)
  Lemma pico_core_typed_resolved_method_frame_abstract_state :
    forall sGamma sGamma' rGamma h x y m args loc C mdef vals
      (Htyping : stmt_typing CT sGamma AbstractState
        (SCall x m y args) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hreceiver : runtime_getVal rGamma y = Some (Iot loc))
      (Hbase : r_basetype h loc = Some C)
      (Hfind : FindMethodWithName CT C m mdef)
      (Hargs : runtime_lookup_list rGamma args = Some vals),
      pico_core_typed_env CT
        (mreceiver (msignature mdef) :: mparams (msignature mdef))
        (mkr_env (Iot loc :: vals)) h.
  Proof.
    intros sGamma sGamma' rGamma h x y m args loc C mdef vals
      Htyping Henv Hreceiver Hbase Hfind Hargs.
    destruct
      (pico_core_typed_resolved_method_static
        sGamma sGamma' rGamma h AbstractState x y m args
        loc C mdef vals Htyping Henv Hreceiver Hbase Hfind Hargs)
	      as (Ty & Cstatic & argtypes & mdef_static & declaring_class & Hget_y &
	          Href_static & Hget_args & Hfind_static & Hbase_sub &
	          Hrefine & Hdecl_sub & Hwf_method).
    destruct
      (pico_core_stmt_typing_call_abs_components
        sGamma sGamma' x y m args Htyping)
	      as (Ty' & Cstatic' & argtypes' & Tthis & Tx & mdef_static'
	          & Hget_y' & Href_static' & Hget_args' & Hthis & Hget_x
	          & Hfind_static' & Hret_sub & Hrcv_sub & Harg_sub).
    assert (HTy : Ty' = Ty) by congruence.
    subst Ty'.
    assert (Hargtypes : argtypes' = argtypes) by congruence.
    subst argtypes'.
    assert (Hmdef_static : mdef_static' = mdef_static).
    { eapply find_method_with_name_deterministic; eauto. }
    subst mdef_static'.
    (* Type the entry frame against the statically selected signature, then
       transport it to the dynamically selected, refining signature. *)
    pose proof (pico_core_typed_env_wf_config CT sGamma rGamma h Henv)
      as Hconfig.
    destruct Hconfig as [Hwf_CT [Hwf_heap [_ [Hwf_senv _]]]].
    have Hstatic_dom : Cstatic < dom CT.
    { eapply senv_var_ref_domain; [exact Hwf_senv | exact Hget_y |
        exact Href_static]. }
    destruct (method_lookup_in_wellformed_inherited CT Cstatic m mdef_static
      Hwf_CT Hstatic_dom Hfind_static)
      as (static_class & static_def & _ & _ & _ & Hwf_static).
    assert (Hstatic_frame : pico_core_typed_env CT
      (mreceiver (msignature mdef_static) :: mparams (msignature mdef_static))
      (mkr_env (Iot loc :: vals)) h).
    {
      destruct Hrcv_sub as [Hrcv_regular | Hrcv_special].
      - eapply pico_core_typed_call_frame_abstract_state_regular
          with (argtypes := argtypes) (Tthis := Tthis)
            (C := C) (declaring_class := static_class).
        + exact Henv.
        + exact Hget_y.
        + exact Hget_args.
        + exact Hthis.
        + exact Hreceiver.
        + exact Hbase.
        + exact Hargs.
        + exact Hwf_static.
        + exact Hrcv_regular.
        + exact Harg_sub.
      - destruct Hrcv_special as
          (Hty_ro & Hreceiver_rdm & Hreceiver_base).
        eapply pico_core_typed_call_frame_abstract_state_special
          with (argtypes := argtypes) (Tthis := Tthis)
            (C := C) (declaring_class := static_class).
        + exact Henv.
        + exact Hget_y.
        + exact Hget_args.
        + exact Hthis.
        + exact Hreceiver.
        + exact Hbase.
        + exact Hargs.
        + exact Hwf_static.
        + exact Hty_ro.
        + exact Hreceiver_rdm.
        + exact Hreceiver_base.
        + exact Harg_sub.
    }
    eapply pico_core_typed_env_refine_frame.
    - exact Hrefine.
    - exact Hstatic_frame.
    - exact Hbase.
    - rewrite (wf_method_receiver_class CT declaring_class mdef Hwf_method).
      apply base_ref. exact Hdecl_sub.
  Qed.

  Lemma pico_core_typed_call_frame_readonly_state_special :
    forall sGamma rGamma h y args vals Ty argtypes Tthis loc C mdef
      declaring_class
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hget_y : static_getType sGamma y = Some Ty)
      (Hget_args : static_getType_list sGamma args = Some argtypes)
      (Hthis : get_this_qualified_type sGamma = Some Tthis)
      (Hreceiver : runtime_getVal rGamma y = Some (Iot loc))
      (Hbase : r_basetype h loc = Some C)
      (Hargs : runtime_lookup_list rGamma args = Some vals)
      (Hwf_method : wf_method CT declaring_class mdef)
      (Hty_ro : sqtype Ty = RO)
      (Hreceiver_rdm : sqtype (mreceiver (msignature mdef)) = RDM)
      (Hreceiver_base : base_subtype CT (sbase Ty)
        (sbase (mreceiver (msignature mdef))))
      (Harg_sub : Forall2 (fun arg T => qualified_type_subtype CT arg
        (vpa_mutability_tt_readonly_state Ty T))
        argtypes (mparams (msignature mdef))),
      pico_core_typed_env CT
        (mreceiver (msignature mdef) :: mparams (msignature mdef))
        (mkr_env (Iot loc :: vals)) h.
  Proof.
    intros sGamma rGamma h y args vals Ty argtypes Tthis loc C mdef
      declaring_class Henv Hget_y Hget_args Hthis Hreceiver Hbase Hargs
      Hwf_method Hty_ro Hreceiver_rdm Hreceiver_base Harg_sub.
    destruct
      (pico_core_typed_call_receiver_qualifiers
        sGamma rGamma h y Ty Tthis loc
        Henv Hget_y Hthis Hreceiver)
      as (outer & qouter & qinner & Houter & Hqouter & Hqinner &
          Houter_qualifier & Hinner_qualifier).
    destruct
      (pico_core_typed_env_lookup_at_context
        sGamma rGamma h qouter outer Henv Houter Hqouter
        y Ty Hget_y)
      as (value_y & Hruntime_y & Htyped_y).
    assert (Hvalue_y : value_y = Iot loc) by congruence.
    subst value_y.
    assert (Hreceiver_typed :
      pico_core_typed_value CT h qinner
        (mreceiver (msignature mdef)) (Iot loc)).
    {
      eapply pico_core_typed_value_env_independent.
      eapply pico_core_typed_location_call_receiver_abstract_state_special;
        eauto.
    }
    assert (Harg_sub_special : Forall2
      (fun arg T => qualified_type_subtype CT arg
        (vpa_mutability_tt_readonly_state
          {| sqtype := RO; sbase := sbase T |} T))
      argtypes (mparams (msignature mdef))).
    {
      destruct Ty as [qTy cTy].
      simpl in Hty_ro.
      subst qTy.
      exact Harg_sub.
    }
    assert (Hparams : forall i T,
      nth_error (mparams (msignature mdef)) i = Some T ->
      exists v,
        nth_error vals i = Some v /\
        pico_core_typed_value CT h
          qinner T v).
    {
      eapply pico_core_typed_call_params_readonly_state_special
        with (argtypes := argtypes) (outer := outer) (qouter := qouter).
      + exact Henv.
      + exact Houter.
      + exact Hqouter.
      + exact Hget_args.
      + exact Hargs.
      + exact Harg_sub_special.
      + rewrite Hty_ro in Hinner_qualifier.
        exact Hinner_qualifier.
      + exact Hqinner.
    }
    assert (Hlength : length (mparams (msignature mdef)) = length vals).
    {
      apply Forall2_length in Harg_sub.
      apply static_getType_list_preserves_length in Hget_args.
      apply runtime_lookup_list_preserves_length in Hargs.
      lia.
    }
    pose proof (pico_core_typed_env_wf_config CT sGamma rGamma h Henv)
      as Hconfig.
    unfold wf_r_config in Hconfig.
    destruct Hconfig as
      (Hwf_CT & Hwf_heap & Hcaller_renv & Hcaller_senv & Hcaller_len &
        Hcaller_corr).
    assert (Hframe_renv : wf_renv CT (mkr_env (Iot loc :: vals)) h).
    {
      eapply pico_core_resolved_method_frame_wf_renv; eauto.
    }
    unfold wf_method in Hwf_method.
    destruct Hwf_method as
      (Hreturn_wf & body_sGamma' & body_ret_type & Hbody_typing & Hret_dom &
        Hret_type & Hret_subtype & Hoverride).
    eapply pico_core_typed_method_frame_env with (qinner := qinner);
      eauto.
    eapply stmt_typing_wf_env; eauto.
  Qed.

  Lemma pico_core_typed_resolved_method_frame_readonly_state :
    forall sGamma sGamma' rGamma h mt x y m args loc C mdef vals
      (Htyping : stmt_typing CT sGamma mt (SCall x m y args) sGamma')
      (Hmt : mt <> AbstractState)
      (Hmt_cs : mt <> ConcreteState)
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hreceiver : runtime_getVal rGamma y = Some (Iot loc))
      (Hbase : r_basetype h loc = Some C)
      (Hfind : FindMethodWithName CT C m mdef)
      (Hargs : runtime_lookup_list rGamma args = Some vals),
      pico_core_typed_env CT
        (mreceiver (msignature mdef) :: mparams (msignature mdef))
        (mkr_env (Iot loc :: vals)) h.
  Proof.
    intros sGamma sGamma' rGamma h mt x y m args loc C mdef vals
      Htyping Hmt Hmt_cs Henv Hreceiver Hbase Hfind Hargs.
    destruct
      (pico_core_typed_resolved_method_static
        sGamma sGamma' rGamma h mt x y m args
        loc C mdef vals Htyping Henv Hreceiver Hbase Hfind Hargs)
	      as (Ty & Cstatic & argtypes & mdef_static & declaring_class & Hget_y &
	          Href_static & Hget_args & Hfind_static & Hbase_sub &
	          Hrefine & Hdecl_sub & Hwf_method).
    destruct
      (pico_core_stmt_typing_call_safe_components
        sGamma sGamma' mt x y m args Htyping Hmt Hmt_cs)
	      as (Ty' & Cstatic' & argtypes' & Tthis & Tx & mdef_static'
	          & Hget_y' & Href_static' & Hget_args' & Hthis & Hget_x
	          & Hfind_static' & Hret_sub & Hrcv_sub & Harg_sub).
    assert (HTy : Ty' = Ty) by congruence.
    subst Ty'.
    assert (Hargtypes : argtypes' = argtypes) by congruence.
    subst argtypes'.
    assert (Hmdef_static : mdef_static' = mdef_static).
    { eapply find_method_with_name_deterministic; eauto. }
    subst mdef_static'.
    (* Type the entry frame against the statically selected signature, then
       transport it to the dynamically selected, refining signature. *)
    pose proof (pico_core_typed_env_wf_config CT sGamma rGamma h Henv)
      as Hconfig.
    destruct Hconfig as [Hwf_CT [Hwf_heap [_ [Hwf_senv _]]]].
    have Hstatic_dom : Cstatic < dom CT.
    { eapply senv_var_ref_domain; [exact Hwf_senv | exact Hget_y |
        exact Href_static]. }
    destruct (method_lookup_in_wellformed_inherited CT Cstatic m mdef_static
      Hwf_CT Hstatic_dom Hfind_static)
      as (static_class & static_def & _ & _ & _ & Hwf_static).
    assert (Hstatic_frame : pico_core_typed_env CT
      (mreceiver (msignature mdef_static) :: mparams (msignature mdef_static))
      (mkr_env (Iot loc :: vals)) h).
    {
      destruct Hrcv_sub as [Hrcv_regular | Hrcv_special].
      - eapply pico_core_typed_call_frame_readonly_state_regular
          with (argtypes := argtypes) (Tthis := Tthis)
            (C := C) (declaring_class := static_class).
        + exact Henv.
        + exact Hget_y.
        + exact Hget_args.
        + exact Hthis.
        + exact Hreceiver.
        + exact Hbase.
        + exact Hargs.
        + exact Hwf_static.
        + exact Hrcv_regular.
        + exact Harg_sub.
      - destruct Hrcv_special as
          (Hty_ro & Hreceiver_rdm & Hreceiver_base).
        eapply pico_core_typed_call_frame_readonly_state_special
          with (argtypes := argtypes) (Tthis := Tthis)
            (C := C) (declaring_class := static_class).
        + exact Henv.
        + exact Hget_y.
        + exact Hget_args.
        + exact Hthis.
        + exact Hreceiver.
        + exact Hbase.
        + exact Hargs.
        + exact Hwf_static.
        + exact Hty_ro.
        + exact Hreceiver_rdm.
        + exact Hreceiver_base.
        + exact Harg_sub.
    }
    eapply pico_core_typed_env_refine_frame.
    - exact Hrefine.
    - exact Hstatic_frame.
    - exact Hbase.
    - rewrite (wf_method_receiver_class CT declaring_class mdef Hwf_method).
      apply base_ref. exact Hdecl_sub.
  Qed.

  Lemma pico_core_typed_resolved_method_frame :
    forall sGamma sGamma' rGamma h mt x y m args loc C mdef vals
      (Htyping : stmt_typing CT sGamma mt (SCall x m y args) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hreceiver : runtime_getVal rGamma y = Some (Iot loc))
      (Hbase : r_basetype h loc = Some C)
      (Hfind : FindMethodWithName CT C m mdef)
      (Hargs : runtime_lookup_list rGamma args = Some vals),
      pico_core_typed_env CT
        (mreceiver (msignature mdef) :: mparams (msignature mdef))
        (mkr_env (Iot loc :: vals)) h.
  Proof.
    intros sGamma sGamma' rGamma h mt x y m args loc C mdef vals
      Htyping Henv Hreceiver Hbase Hfind Hargs.
    destruct mt.
    - eapply pico_core_typed_resolved_method_frame_abstract_state; eauto.
    - eapply pico_core_typed_resolved_method_frame_abstract_state; eauto.
      eapply pico_core_concrete_state_call_as_abs; eauto.
    - eapply pico_core_typed_resolved_method_frame_readonly_state; eauto;
        discriminate.
    - eapply pico_core_typed_resolved_method_frame_readonly_state; eauto.
      all: discriminate.
  Qed.
End pico_typing_fundamental_ownp_pure.
