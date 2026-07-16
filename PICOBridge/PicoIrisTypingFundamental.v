From iris.program_logic Require Import weakestpre ownp.
From iris.proofmode Require Import proofmode.

Require Import Syntax Helpers Typing Subtyping Bigstep Properties
  ViewpointAdaptation.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage
  PICOBridge.PicoIrisCoreInvariant PICOBridge.PicoIrisTypingSupport.

(** * Typing-Directed PICO Core WP

    This file contains the progress-facing fundamental-theorem development.
    It is kept separate from the typed-environment support file so each new
    typing case can be checked without recompiling semantic resource proofs.

    Unlike the older runtime-outcome endpoint, rules here derive primitive-step
    readiness from typing plus [pico_core_typed_env] and
    [pico_core_state_wf].  They target [NotStuck]. *)

Section pico_typing_fundamental_ownp.
  Context `{Hmem : CacheMemoryModel}.
  Context `{Hprogress : CacheMemoryModelProgress}.
  Context (CT : class_table).
  Context `{!ownPGS (pico_core_language CT) Sigma}.

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
      heap -> method_type -> s_env -> pico_core_cont -> Prop :=
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

  Definition pico_core_stmt_post_contI
      (sGamma' : s_env) (K : pico_core_cont)
      (E : coPset)
      (Phi : val (pico_core_language CT) -> iProp Sigma) : iProp Sigma :=
    ▷ ∀ e' state',
      ⌜pico_core_stmt_post sGamma' K e' state'⌝ -∗
      ownP state' -∗
      WP e' @ NotStuck; E {{ Phi }}.

  Definition pico_core_typed_outcome_contI
      (sGamma' : s_env) (K : pico_core_cont)
      (E : coPset)
      (Phi : val (pico_core_language CT) -> iProp Sigma) : iProp Sigma :=
    (□ ∀ rGamma state V,
      ⌜pico_core_typed_env CT sGamma' rGamma (pcs_heap state)⌝ -∗
      ⌜pico_core_lr_state CT state⌝ -∗
      ownP state -∗
      WP CoreRun rGamma SSkip V K @ NotStuck; E {{ Phi }}) ∗
    (□ ∀ rGamma state V,
      ⌜pico_core_lr_state CT state⌝ -∗
      ownP state -∗
      WP CoreDone NPE rGamma V @ NotStuck; E {{ Phi }}) ∗
    (□ ∀ rGamma state V,
      ⌜pico_core_lr_state CT state⌝ -∗
      ownP state -∗
      WP CoreDone MUTATIONEXP rGamma V @ NotStuck; E {{ Phi }}).

  Lemma pico_core_stmt_post_cont_from_outcomeI :
    forall sGamma' K E Phi,
      pico_core_typed_outcome_contI sGamma' K E Phi -∗
      pico_core_stmt_post_contI sGamma' K E Phi.
  Proof.
    intros sGamma' K E Phi.
    iIntros "[#Hok [#Hnpe #Hmutation]]".
    unfold pico_core_stmt_post_contI.
    iNext.
    iIntros (e' state') "Hpost Hown".
    iDestruct "Hpost" as %Hpost.
    inversion Hpost; subst.
    - iApply ("Hok" with "[] [] Hown"); iPureIntro; assumption.
    - iApply ("Hnpe" with "[] Hown").
      iPureIntro.
      assumption.
    - iApply ("Hmutation" with "[] Hown").
      iPureIntro.
      assumption.
  Qed.

  Definition pico_core_typed_stmt_wpI
      (sGamma : s_env) (mt : method_type)
      (s : stmt) (sGamma' : s_env) : iProp Sigma :=
    □ ∀ rGamma h sigma V K E Phi,
      ⌜pico_core_typed_env CT sGamma rGamma h⌝ -∗
      ⌜pico_core_lr_state CT (mkPicoCoreState h sigma)⌝ -∗
      ownP (mkPicoCoreState h sigma) -∗
      pico_core_typed_outcome_contI sGamma' K E Phi -∗
      WP CoreRun rGamma s V K @ NotStuck; E {{ Phi }}.

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
    forall rGamma1 rGamma2 h qcontext T v,
      pico_core_typed_value CT rGamma1 h qcontext T v ->
      pico_core_typed_value CT rGamma2 h qcontext T v.
  Proof.
    intros rGamma1 rGamma2 h qcontext T v Htyped.
    destruct v as [|loc|n]; simpl in *.
    - auto.
    - eapply wf_r_typable_env_independent_simple; eauto.
    - auto.
  Qed.

  Lemma pico_core_typed_value_real_lr_value :
    forall rGamma h qcontext T v,
      pico_core_typed_value CT rGamma h qcontext T v ->
      pico_typed_runtime_value CT h qcontext T v.
  Proof.
    intros rGamma h qcontext T v Htyped.
    destruct v as [|loc|n]; simpl in *; auto.
  Qed.

  Lemma pico_core_typed_value_subtype :
    forall rGamma h qcontext T1 T2 v
      (Hwf_CT : wf_class_table CT)
      (Hwf_heap : wf_heap CT h)
      (Htyped : pico_core_typed_value CT rGamma h qcontext T1 v)
      (Hsub : qualified_type_subtype CT T1 T2),
      pico_core_typed_value CT rGamma h qcontext T2 v.
  Proof.
	    intros rGamma h qcontext T1 T2 v Hwf_CT Hwf_heap Htyped Hsub.
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
    forall rGamma h h' qcontext T v
      (Htyped : pico_core_typed_value CT rGamma h qcontext T v)
      (Hextend : pico_core_heap_types_extend h h'),
      pico_core_typed_value CT rGamma h' qcontext T v.
  Proof.
    intros rGamma h h' qcontext T v Htyped [_ Htypes].
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
        (pico_core_typed_value CT rGamma h' qcontext T (Iot loc)).
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
      (Htyping : stmt_typing CT sGamma mt (SCall x y m args) sGamma')
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
	        msignature mdef = msignature mdef_static /\
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
	        (method_signature_consistent_subtype
	          CT (rctype (rt_type receiver_obj)) Cstatic
	          m mdef mdef_static
	          Hwf_CT Hclass_sub Hfind Hfind_static).
	    - exact Hwf_method.
  Qed.

  Lemma pico_core_typed_resolved_method_body :
    forall sGamma sGamma' rGamma h mt x y m args
      loc C mdef vals
      (Htyping : stmt_typing CT sGamma mt (SCall x y m args) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hreceiver : runtime_getVal rGamma y = Some (Iot loc))
      (Hbase : r_basetype h loc = Some C)
      (Hfind : FindMethodWithName CT C m mdef)
      (Hargs : runtime_lookup_list rGamma args = Some vals),
      exists body_sGamma' body_ret_type,
        stmt_typing CT
          (mreceiver (msignature mdef) :: mparams (msignature mdef))
          (mtype (msignature mdef))
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
	          Hsignature & Hwf_method).
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
          pico_core_typed_value CT rGamma h qcontext Tx v)
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
          pico_core_typed_value CT rGamma h qcontext Tx v),
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
      apply pico_core_typed_value_real_lr_value with (rGamma := rGamma).
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
        pico_core_typed_value CT rGamma h qcontext Tsource v)
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
  Lemma pico_core_wf_r_typable_adapted_subtype_abs_imm :
    forall sGamma rGamma h Tthis locthis loc T1 T2 qcontext
      (Hwf_heap : wf_heap CT h)
      (Hthis_type : get_this_qualified_type sGamma = Some Tthis)
      (Hthis_val : get_this_var_mapping (vars rGamma) = Some locthis)
      (Hthis_mut : r_muttype h locthis = Some qcontext)
      (Hthis_qualifier :
        qualifier_typable_context qcontext (sqtype Tthis) qcontext)
      (Htyped : wf_r_typable CT rGamma h loc T1 qcontext)
      (Hsub : qualified_type_subtype CT
        (vpa_mutability_tt_abs_imm Tthis T1)
        (vpa_mutability_tt_abs_imm Tthis T2)),
      wf_r_typable CT rGamma h loc T2 qcontext.
  Proof.
    intros.
    eapply wf_r_typable_adapted_subtype_abs_imm; eauto.
  Qed.

  Lemma pico_core_wf_r_typable_adapted_subtype_safe_ro :
    forall sGamma rGamma h Tthis locthis loc T1 T2 qcontext
      (Hwf_heap : wf_heap CT h)
      (Hthis_type : get_this_qualified_type sGamma = Some Tthis)
      (Hthis_val : get_this_var_mapping (vars rGamma) = Some locthis)
      (Hthis_mut : r_muttype h locthis = Some qcontext)
      (Hthis_qualifier :
        qualifier_typable_context qcontext (sqtype Tthis) qcontext)
      (Htyped : wf_r_typable CT rGamma h loc T1 qcontext)
      (Hsub : qualified_type_subtype CT
        (vpa_mutability_tt_safe_ro Tthis T1)
        (vpa_mutability_tt_safe_ro Tthis T2)),
      wf_r_typable CT rGamma h loc T2 qcontext.
  Proof.
    intros.
    eapply wf_r_typable_adapted_subtype_safe_ro; eauto.
  Qed.

  Lemma pico_core_abs_imm_argument_qualifier_transfer :
    forall qarg qinner qouter qs_ty qs_this qs_arg qs_method,
      qualifier_typable_context qarg qs_arg qouter ->
      qualifier_typable_context qinner qs_ty qouter ->
      qualifier_typable_context qouter qs_this qouter ->
      q_subtype qs_arg
        (vpa_mutability_qq_abs_imm qs_ty qs_method) ->
      q_subtype qs_ty
        (vpa_mutability_qq_abs_imm qs_ty qs_this) ->
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

  Lemma pico_core_safe_ro_argument_qualifier_transfer :
    forall qarg qinner qouter qs_ty qs_this qs_arg qs_method,
      qualifier_typable_context qarg qs_arg qouter ->
      qualifier_typable_context qinner qs_ty qouter ->
      qualifier_typable_context qouter qs_this qouter ->
      q_subtype qs_arg
        (vpa_mutability_qq_safe_ro qs_ty qs_method) ->
      q_subtype qs_ty
        (vpa_mutability_qq_safe_ro qs_ty qs_this) ->
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

  Lemma pico_core_abs_imm_argument_special_transfer :
    forall qarg qinner qouter qs_arg qs_method,
      qualifier_typable_context qarg qs_arg qouter ->
      qualifier_typable_context qinner RO qouter ->
      q_subtype qs_arg (vpa_mutability_qq_abs_imm RO qs_method) ->
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

  Lemma pico_core_abs_imm_argument_direct_transfer :
    forall qarg qinner qouter qs_ty qs_arg qs_param,
      qualifier_typable_context qarg qs_arg qouter ->
      qualifier_typable_context qinner qs_ty qouter ->
      q_subtype qs_arg
        (vpa_mutability_qq_abs_imm qs_ty qs_param) ->
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

  Lemma pico_core_safe_ro_argument_direct_transfer :
    forall qarg qinner qouter qs_ty qs_arg qs_param,
      qualifier_typable_context qarg qs_arg qouter ->
      qualifier_typable_context qinner qs_ty qouter ->
      q_subtype qs_arg
        (vpa_mutability_qq_safe_ro qs_ty qs_param) ->
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

  Lemma pico_core_safe_ro_argument_special_transfer :
    forall qarg qinner qouter qs_arg qs_method,
      qualifier_typable_context qarg qs_arg qouter ->
      qualifier_typable_context qinner RO qouter ->
      q_subtype qs_arg (vpa_mutability_qq_safe_ro RO qs_method) ->
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

  Lemma pico_core_wf_r_typable_call_argument_abs_imm :
    forall rGamma h loc Targ Ty Tparam Tthis qinner qouter
      (Hsource : wf_r_typable CT rGamma h loc Targ qouter)
      (Hthis_qualifier :
        qualifier_typable_context qouter (sqtype Tthis) qouter)
      (Hinner_qualifier :
        qualifier_typable_context qinner (sqtype Ty) qouter)
      (Harg_sub : qualified_type_subtype CT Targ
        (vpa_mutability_tt_abs_imm Ty Tparam))
      (Hrcv_sub : qualified_type_subtype CT Ty
        (vpa_mutability_tt_abs_imm Ty Tthis)),
      wf_r_typable CT rGamma h loc Tparam qinner.
  Proof.
    intros rGamma h loc Targ Ty Tparam Tthis qinner qouter
      Hsource Hthis_qualifier Hinner_qualifier Harg_sub Hrcv_sub.
    unfold wf_r_typable in Hsource |- *.
    destruct (r_type h loc) as [rqt |] eqn:Htype;
      try contradiction.
    destruct Hsource as [Hbase Hqualifier].
    split.
    - apply qualified_type_subtype_base_subtype in Harg_sub.
      rewrite vpa_mutability_tt_sbase_abs_imm in Harg_sub.
      eapply base_trans; eauto.
    - apply qualified_type_subtype_q_subtype in Harg_sub.
      apply qualified_type_subtype_q_subtype in Hrcv_sub.
      rewrite (sq_vpa_tt_eq_qq_abs_imm Ty Tparam) in Harg_sub.
      rewrite (sq_vpa_tt_eq_qq_abs_imm Ty Tthis) in Hrcv_sub.
      eapply pico_core_abs_imm_argument_qualifier_transfer; eauto.
  Qed.

  Lemma pico_core_wf_r_typable_call_argument_safe_ro :
    forall rGamma h loc Targ Ty Tparam Tthis qinner qouter
      (Hsource : wf_r_typable CT rGamma h loc Targ qouter)
      (Hthis_qualifier :
        qualifier_typable_context qouter (sqtype Tthis) qouter)
      (Hinner_qualifier :
        qualifier_typable_context qinner (sqtype Ty) qouter)
      (Harg_sub : qualified_type_subtype CT Targ
        (vpa_mutability_tt_safe_ro Ty Tparam))
      (Hrcv_sub : qualified_type_subtype CT Ty
        (vpa_mutability_tt_safe_ro Ty Tthis)),
      wf_r_typable CT rGamma h loc Tparam qinner.
  Proof.
    intros rGamma h loc Targ Ty Tparam Tthis qinner qouter
      Hsource Hthis_qualifier Hinner_qualifier Harg_sub Hrcv_sub.
    unfold wf_r_typable in Hsource |- *.
    destruct (r_type h loc) as [rqt |] eqn:Htype;
      try contradiction.
    destruct Hsource as [Hbase Hqualifier].
    split.
    - apply qualified_type_subtype_base_subtype in Harg_sub.
      rewrite vpa_mutability_tt_sbase_safe_ro in Harg_sub.
      eapply base_trans; eauto.
    - apply qualified_type_subtype_q_subtype in Harg_sub.
      apply qualified_type_subtype_q_subtype in Hrcv_sub.
      rewrite (sq_vpa_tt_eq_qq_safe_ro Ty Tparam) in Harg_sub.
      rewrite (sq_vpa_tt_eq_qq_safe_ro Ty Tthis) in Hrcv_sub.
      eapply pico_core_safe_ro_argument_qualifier_transfer; eauto.
  Qed.

  Lemma pico_core_wf_r_typable_call_argument_abs_imm_special :
    forall rGamma h loc Targ Tparam qinner qouter
      (Hsource : wf_r_typable CT rGamma h loc Targ qouter)
      (Hinner_qualifier :
        qualifier_typable_context qinner RO qouter)
      (Harg_sub : qualified_type_subtype CT Targ
        (vpa_mutability_tt_abs_imm {| sqtype := RO; sbase := sbase Targ |} Tparam)),
      wf_r_typable CT rGamma h loc Tparam qinner.
  Proof.
    intros rGamma h loc Targ Tparam qinner qouter
      Hsource Hinner_qualifier Harg_sub.
    unfold wf_r_typable in Hsource |- *.
    destruct (r_type h loc) as [rqt |] eqn:Htype;
      try contradiction.
    destruct Hsource as [Hbase Hqualifier].
    split.
    - apply qualified_type_subtype_base_subtype in Harg_sub.
      rewrite vpa_mutability_tt_sbase_abs_imm in Harg_sub.
      eapply base_trans; eauto.
    - apply qualified_type_subtype_q_subtype in Harg_sub.
      rewrite (sq_vpa_tt_eq_qq_abs_imm
        {| sqtype := RO; sbase := sbase Targ |} Tparam) in Harg_sub.
      eapply pico_core_abs_imm_argument_special_transfer; eauto.
  Qed.

  Lemma pico_core_wf_r_typable_call_argument_safe_ro_special :
    forall rGamma h loc Targ Tparam qinner qouter
      (Hsource : wf_r_typable CT rGamma h loc Targ qouter)
      (Hinner_qualifier :
        qualifier_typable_context qinner RO qouter)
      (Harg_sub : qualified_type_subtype CT Targ
        (vpa_mutability_tt_safe_ro {| sqtype := RO; sbase := sbase Targ |} Tparam)),
      wf_r_typable CT rGamma h loc Tparam qinner.
  Proof.
    intros rGamma h loc Targ Tparam qinner qouter
      Hsource Hinner_qualifier Harg_sub.
    unfold wf_r_typable in Hsource |- *.
    destruct (r_type h loc) as [rqt |] eqn:Htype;
      try contradiction.
    destruct Hsource as [Hbase Hqualifier].
    split.
    - apply qualified_type_subtype_base_subtype in Harg_sub.
      rewrite vpa_mutability_tt_sbase_safe_ro in Harg_sub.
      eapply base_trans; eauto.
    - apply qualified_type_subtype_q_subtype in Harg_sub.
      rewrite (sq_vpa_tt_eq_qq_safe_ro
        {| sqtype := RO; sbase := sbase Targ |} Tparam) in Harg_sub.
      eapply pico_core_safe_ro_argument_special_transfer; eauto.
  Qed.

  Lemma pico_core_typed_location_call_argument_abs_imm :
    forall rGamma h loc Targ Ty Tparam Tthis qinner qouter
      (Hsource : pico_core_typed_value CT rGamma h qouter Targ (Iot loc))
      (Hthis_qualifier :
        qualifier_typable_context qouter (sqtype Tthis) qouter)
      (Hinner_qualifier :
        qualifier_typable_context qinner (sqtype Ty) qouter)
      (Harg_sub : qualified_type_subtype CT Targ
        (vpa_mutability_tt_abs_imm Ty Tparam))
      (Hrcv_sub : qualified_type_subtype CT Ty
        (vpa_mutability_tt_abs_imm Ty Tthis)),
      pico_core_typed_value CT rGamma h qinner Tparam (Iot loc).
  Proof.
    intros.
    unfold pico_core_typed_value in Hsource |- *.
    eapply pico_core_wf_r_typable_call_argument_abs_imm; eauto.
  Qed.

  Lemma pico_core_typed_location_call_argument_safe_ro :
    forall rGamma h loc Targ Ty Tparam Tthis qinner qouter
      (Hsource : pico_core_typed_value CT rGamma h qouter Targ (Iot loc))
      (Hthis_qualifier :
        qualifier_typable_context qouter (sqtype Tthis) qouter)
      (Hinner_qualifier :
        qualifier_typable_context qinner (sqtype Ty) qouter)
      (Harg_sub : qualified_type_subtype CT Targ
        (vpa_mutability_tt_safe_ro Ty Tparam))
      (Hrcv_sub : qualified_type_subtype CT Ty
        (vpa_mutability_tt_safe_ro Ty Tthis)),
      pico_core_typed_value CT rGamma h qinner Tparam (Iot loc).
  Proof.
    intros.
    unfold pico_core_typed_value in Hsource |- *.
    eapply pico_core_wf_r_typable_call_argument_safe_ro; eauto.
  Qed.

  Lemma pico_core_typed_location_call_argument_abs_imm_direct :
    forall rGamma h loc Targ Ty Tparam qinner qouter
      (Hsource : pico_core_typed_value CT rGamma h qouter Targ (Iot loc))
      (Hinner_qualifier :
        qualifier_typable_context qinner (sqtype Ty) qouter)
      (Harg_sub : qualified_type_subtype CT Targ
        (vpa_mutability_tt_abs_imm Ty Tparam)),
      pico_core_typed_value CT rGamma h qinner Tparam (Iot loc).
  Proof.
    intros rGamma h loc Targ Ty Tparam qinner qouter
      Hsource Hinner_qualifier Harg_sub.
    unfold pico_core_typed_value, wf_r_typable in Hsource |- *.
    destruct (r_type h loc) as [rqt |] eqn:Htype;
      try contradiction.
    destruct Hsource as [Hbase Hqualifier].
    split.
    - apply qualified_type_subtype_base_subtype in Harg_sub.
      rewrite vpa_mutability_tt_sbase_abs_imm in Harg_sub.
      eapply base_trans; eauto.
    - apply qualified_type_subtype_q_subtype in Harg_sub.
      rewrite (sq_vpa_tt_eq_qq_abs_imm Ty Tparam) in Harg_sub.
      eapply pico_core_abs_imm_argument_direct_transfer; eauto.
  Qed.

  Lemma pico_core_typed_location_call_argument_safe_ro_direct :
    forall rGamma h loc Targ Ty Tparam qinner qouter
      (Hsource : pico_core_typed_value CT rGamma h qouter Targ (Iot loc))
      (Hinner_qualifier :
        qualifier_typable_context qinner (sqtype Ty) qouter)
      (Harg_sub : qualified_type_subtype CT Targ
        (vpa_mutability_tt_safe_ro Ty Tparam)),
      pico_core_typed_value CT rGamma h qinner Tparam (Iot loc).
  Proof.
    intros rGamma h loc Targ Ty Tparam qinner qouter
      Hsource Hinner_qualifier Harg_sub.
    unfold pico_core_typed_value, wf_r_typable in Hsource |- *.
    destruct (r_type h loc) as [rqt |] eqn:Htype;
      try contradiction.
    destruct Hsource as [Hbase Hqualifier].
    split.
    - apply qualified_type_subtype_base_subtype in Harg_sub.
      rewrite vpa_mutability_tt_sbase_safe_ro in Harg_sub.
      eapply base_trans; eauto.
    - apply qualified_type_subtype_q_subtype in Harg_sub.
      rewrite (sq_vpa_tt_eq_qq_safe_ro Ty Tparam) in Harg_sub.
      eapply pico_core_safe_ro_argument_direct_transfer; eauto.
  Qed.

  (** Return transfer is the sole remaining call extraction obligation.
      It is intentionally kept out of this entry-frame module until proved
      directly from the complete source call rule. *)

  Lemma pico_core_abs_imm_return_qualifier :
    forall qr qinner qouter qreceiver qbody qmethod qtarget,
      qualifier_typable_context qr qbody qinner ->
      qualifier_typable_context qinner qreceiver qouter ->
      q_subtype qbody qmethod ->
      q_subtype (vpa_mutability_qq_abs_imm qreceiver qmethod) qtarget ->
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

  Lemma pico_core_safe_ro_return_qualifier :
    forall qr qinner qouter qreceiver qbody qmethod qtarget,
      qualifier_typable_context qr qbody qinner ->
      qualifier_typable_context qinner qreceiver qouter ->
      q_subtype qbody qmethod ->
      q_subtype (vpa_mutability_qq_safe_ro qreceiver qmethod) qtarget ->
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

  Lemma pico_core_typed_return_value_abs_imm :
    forall rGamma h Ty Tbody Tmethod Ttarget qinner qouter v
      (Hwf_CT : wf_class_table CT)
      (Hreceiver_context :
        qualifier_typable_context qinner (sqtype Ty) qouter)
      (Hvalue : pico_core_typed_value CT rGamma h qinner Tbody v)
      (Hbody_return : qualified_type_subtype CT Tbody Tmethod)
      (Hcall_return : qualified_type_subtype CT
        (vpa_mutability_tt_abs_imm Ty Tmethod) Ttarget),
      pico_core_typed_value CT rGamma h qouter Ttarget v.
  Proof.
    intros rGamma h Ty Tbody Tmethod Ttarget qinner qouter v
      Hwf_CT Hreceiver_context Hvalue Hbody_return Hcall_return.
	    destruct v as [|loc|n]; simpl in *.
	    - pose proof
	        (pico_core_subtype_preserves_reference Tbody Tmethod
	          Hvalue Hbody_return) as [C Hmethod].
	      assert (Hadapt : exists D,
	        sbase (vpa_mutability_tt_abs_imm Ty Tmethod) = TRef D).
	      {
	        exists C.
	        rewrite vpa_mutability_tt_sbase_abs_imm.
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
        rewrite vpa_mutability_tt_sbase_abs_imm in Hcall_return.
        eapply base_trans; [exact Hbase |].
        eapply base_trans; eauto.
      + apply qualified_type_subtype_q_subtype in Hbody_return.
        apply qualified_type_subtype_q_subtype in Hcall_return.
        rewrite (sq_vpa_tt_eq_qq_abs_imm Ty Tmethod) in Hcall_return.
        eapply pico_core_abs_imm_return_qualifier
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
	      rewrite vpa_mutability_tt_sbase_abs_imm in Hcall_return.
	      rewrite Hvalue in Hbody_return.
	      apply base_subtype_from_int in Hbody_return.
	      rewrite Hbody_return in Hcall_return.
	      apply base_subtype_from_int in Hcall_return.
	      exact Hcall_return.
  Qed.

  Lemma pico_core_typed_return_value_safe_ro :
    forall rGamma h Ty Tbody Tmethod Ttarget qinner qouter v
      (Hwf_CT : wf_class_table CT)
      (Hreceiver_context :
        qualifier_typable_context qinner (sqtype Ty) qouter)
      (Hvalue : pico_core_typed_value CT rGamma h qinner Tbody v)
      (Hbody_return : qualified_type_subtype CT Tbody Tmethod)
      (Hcall_return : qualified_type_subtype CT
        (vpa_mutability_tt_safe_ro Ty Tmethod) Ttarget),
      pico_core_typed_value CT rGamma h qouter Ttarget v.
  Proof.
    intros rGamma h Ty Tbody Tmethod Ttarget qinner qouter v
      Hwf_CT Hreceiver_context Hvalue Hbody_return Hcall_return.
	    destruct v as [|loc|n]; simpl in *.
	    - pose proof
	        (pico_core_subtype_preserves_reference Tbody Tmethod
	          Hvalue Hbody_return) as [C Hmethod].
	      assert (Hadapt : exists D,
	        sbase (vpa_mutability_tt_safe_ro Ty Tmethod) = TRef D).
	      {
	        exists C.
	        rewrite vpa_mutability_tt_sbase_safe_ro.
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
        rewrite vpa_mutability_tt_sbase_safe_ro in Hcall_return.
        eapply base_trans; [exact Hbase |].
        eapply base_trans; eauto.
      + apply qualified_type_subtype_q_subtype in Hbody_return.
        apply qualified_type_subtype_q_subtype in Hcall_return.
        rewrite (sq_vpa_tt_eq_qq_safe_ro Ty Tmethod) in Hcall_return.
        eapply pico_core_safe_ro_return_qualifier
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
	      rewrite vpa_mutability_tt_sbase_safe_ro in Hcall_return.
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
        pico_core_typed_value CT (mkr_env (Iot loc :: vals)) h
          qinner (mreceiver msig) (Iot loc))
      (Hlength : length (mparams msig) = length vals)
      (Hparams : forall i T,
        nth_error (mparams msig) i = Some T ->
        exists v,
          nth_error vals i = Some v /\
          pico_core_typed_value CT (mkr_env (Iot loc :: vals)) h
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
        pico_core_typed_value CT rGamma h qouter T v.
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

  Lemma pico_core_typed_call_params_abs_imm :
    forall sGamma rGamma h args vals argtypes Ty params
      outer inner qinner qouter
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hreceiver : get_this_var_mapping (vars rGamma) = Some outer)
      (Hqouter : r_muttype h outer = Some qouter)
      (Hget_args : static_getType_list sGamma args = Some argtypes)
      (Hargs : runtime_lookup_list rGamma args = Some vals)
      (Harg_sub : Forall2
        (fun arg T => qualified_type_subtype CT arg
          (vpa_mutability_tt_abs_imm Ty T)) argtypes params)
      (Hinner_qualifier :
        qualifier_typable_context qinner (sqtype Ty) qouter)
      (Hqinner : r_muttype h inner = Some qinner),
      forall i T,
        nth_error params i = Some T ->
        exists v,
          nth_error vals i = Some v /\
          pico_core_typed_value CT (mkr_env (Iot inner :: vals)) h
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
      (vpa_mutability_tt_abs_imm Ty T)).
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
	          (vpa_mutability_tt_abs_imm Ty T) Hsource_v Harg_sub_i)
	        as [C Hadapt].
	      rewrite vpa_mutability_tt_sbase_abs_imm in Hadapt.
	      exists C.
	      exact Hadapt.
    - eapply pico_core_typed_value_env_independent.
      eapply pico_core_typed_location_call_argument_abs_imm_direct; eauto.
	    - simpl in Hsource_v.
	      simpl.
	      apply qualified_type_subtype_base_subtype in Harg_sub_i.
	      rewrite vpa_mutability_tt_sbase_abs_imm in Harg_sub_i.
	      rewrite Hsource_v in Harg_sub_i.
	      apply base_subtype_from_int in Harg_sub_i.
	      exact Harg_sub_i.
  Qed.

  Lemma pico_core_typed_call_params_safe_ro :
    forall sGamma rGamma h args vals argtypes Ty params
      outer inner qinner qouter
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hreceiver : get_this_var_mapping (vars rGamma) = Some outer)
      (Hqouter : r_muttype h outer = Some qouter)
      (Hget_args : static_getType_list sGamma args = Some argtypes)
      (Hargs : runtime_lookup_list rGamma args = Some vals)
      (Harg_sub : Forall2
        (fun arg T => qualified_type_subtype CT arg
          (vpa_mutability_tt_safe_ro Ty T)) argtypes params)
      (Hinner_qualifier :
        qualifier_typable_context qinner (sqtype Ty) qouter)
      (Hqinner : r_muttype h inner = Some qinner),
      forall i T,
        nth_error params i = Some T ->
        exists v,
          nth_error vals i = Some v /\
          pico_core_typed_value CT (mkr_env (Iot inner :: vals)) h
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
      (vpa_mutability_tt_safe_ro Ty T)).
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
	          (vpa_mutability_tt_safe_ro Ty T) Hsource_v Harg_sub_i)
	        as [C Hadapt].
	      rewrite vpa_mutability_tt_sbase_safe_ro in Hadapt.
	      exists C.
	      exact Hadapt.
    - eapply pico_core_typed_value_env_independent.
      eapply pico_core_typed_location_call_argument_safe_ro_direct; eauto.
	    - simpl in Hsource_v.
	      simpl.
	      apply qualified_type_subtype_base_subtype in Harg_sub_i.
	      rewrite vpa_mutability_tt_sbase_safe_ro in Harg_sub_i.
	      rewrite Hsource_v in Harg_sub_i.
	      apply base_subtype_from_int in Harg_sub_i.
	      exact Harg_sub_i.
  Qed.

  Lemma pico_core_typed_call_params_abs_imm_special :
    forall sGamma rGamma h args vals argtypes params
      outer inner qinner qouter
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hreceiver : get_this_var_mapping (vars rGamma) = Some outer)
      (Hqouter : r_muttype h outer = Some qouter)
      (Hget_args : static_getType_list sGamma args = Some argtypes)
      (Hargs : runtime_lookup_list rGamma args = Some vals)
      (Harg_sub : Forall2
        (fun arg T => qualified_type_subtype CT arg
          (vpa_mutability_tt_abs_imm
            {| sqtype := RO; sbase := sbase T |} T))
        argtypes params)
      (Hinner_qualifier :
        qualifier_typable_context qinner RO qouter)
      (Hqinner : r_muttype h inner = Some qinner),
      forall i T,
        nth_error params i = Some T ->
        exists v,
          nth_error vals i = Some v /\
          pico_core_typed_value CT (mkr_env (Iot inner :: vals)) h
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
      (vpa_mutability_tt_abs_imm
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
	          (vpa_mutability_tt_abs_imm
	            {| sqtype := RO; sbase := sbase T |} T)
	          Hsource_v Harg_sub_i) as [C Hadapt].
	      rewrite vpa_mutability_tt_sbase_abs_imm in Hadapt.
	      exists C.
	      exact Hadapt.
    - eapply pico_core_typed_value_env_independent.
      unfold pico_core_typed_value in Hsource_v |- *.
      eapply pico_core_wf_r_typable_call_argument_abs_imm_special;
        eauto.
	    - simpl in Hsource_v.
	      simpl.
	      apply qualified_type_subtype_base_subtype in Harg_sub_i.
	      rewrite vpa_mutability_tt_sbase_abs_imm in Harg_sub_i.
	      rewrite Hsource_v in Harg_sub_i.
	      apply base_subtype_from_int in Harg_sub_i.
	      exact Harg_sub_i.
  Qed.

  Lemma pico_core_typed_call_params_safe_ro_special :
    forall sGamma rGamma h args vals argtypes params
      outer inner qinner qouter
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hreceiver : get_this_var_mapping (vars rGamma) = Some outer)
      (Hqouter : r_muttype h outer = Some qouter)
      (Hget_args : static_getType_list sGamma args = Some argtypes)
      (Hargs : runtime_lookup_list rGamma args = Some vals)
      (Harg_sub : Forall2
        (fun arg T => qualified_type_subtype CT arg
          (vpa_mutability_tt_safe_ro
            {| sqtype := RO; sbase := sbase T |} T))
        argtypes params)
      (Hinner_qualifier :
        qualifier_typable_context qinner RO qouter)
      (Hqinner : r_muttype h inner = Some qinner),
      forall i T,
        nth_error params i = Some T ->
        exists v,
          nth_error vals i = Some v /\
          pico_core_typed_value CT (mkr_env (Iot inner :: vals)) h
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
      (vpa_mutability_tt_safe_ro
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
	          (vpa_mutability_tt_safe_ro
	            {| sqtype := RO; sbase := sbase T |} T)
	          Hsource_v Harg_sub_i) as [C Hadapt].
	      rewrite vpa_mutability_tt_sbase_safe_ro in Hadapt.
	      exists C.
	      exact Hadapt.
    - eapply pico_core_typed_value_env_independent.
      unfold pico_core_typed_value in Hsource_v |- *.
      eapply pico_core_wf_r_typable_call_argument_safe_ro_special;
        eauto.
	    - simpl in Hsource_v.
	      simpl.
	      apply qualified_type_subtype_base_subtype in Harg_sub_i.
	      rewrite vpa_mutability_tt_sbase_safe_ro in Harg_sub_i.
	      rewrite Hsource_v in Harg_sub_i.
	      apply base_subtype_from_int in Harg_sub_i.
	      exact Harg_sub_i.
  Qed.

  Lemma pico_core_stmt_typing_call_abs_components :
    forall sGamma sGamma' x y m args
      (Htyping : stmt_typing CT sGamma AbstractImm
        (SCall x y m args) sGamma'),
	      exists Ty C argtypes Tthis Tx mdef,
	        static_getType sGamma y = Some Ty /\
	        sbase Ty = TRef C /\
	        static_getType_list sGamma args = Some argtypes /\
	        get_this_qualified_type sGamma = Some Tthis /\
	        static_getType sGamma x = Some Tx /\
	        FindMethodWithName CT C m mdef /\
        qualified_type_subtype CT
          (vpa_mutability_tt_abs_imm Ty (mret (msignature mdef))) Tx /\
        (qualified_type_subtype CT Ty
          (vpa_mutability_tt_abs_imm Ty (mreceiver (msignature mdef))) \/
	         (sqtype Ty = RO /\
	          sqtype (mreceiver (msignature mdef)) = RDM /\
	          base_subtype CT (sbase Ty)
	            (sbase (mreceiver (msignature mdef))))) /\
        Forall2 (fun arg T => qualified_type_subtype CT arg
          (vpa_mutability_tt_abs_imm Ty T))
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
        (SCall x y m args) sGamma' ->
      stmt_typing CT sGamma AbstractImm
        (SCall x y m args) sGamma'.
  Proof.
    intros sGamma sGamma' x y m args Htyping.
    inversion Htyping; subst.
    - econstructor; eauto.
    - exfalso. eauto.
  Qed.

  Lemma pico_core_stmt_typing_call_safe_components :
    forall sGamma sGamma' mt x y m args
      (Htyping : stmt_typing CT sGamma mt
        (SCall x y m args) sGamma')
      (Hmt : mt <> AbstractImm)
      (Hmt_cs : mt <> ConcreteState),
	      exists Ty C argtypes Tthis Tx mdef,
	        static_getType sGamma y = Some Ty /\
	        sbase Ty = TRef C /\
	        static_getType_list sGamma args = Some argtypes /\
	        get_this_qualified_type sGamma = Some Tthis /\
	        static_getType sGamma x = Some Tx /\
	        FindMethodWithName CT C m mdef /\
        qualified_type_subtype CT
          (vpa_mutability_tt_safe_ro Ty (mret (msignature mdef))) Tx /\
        (qualified_type_subtype CT Ty
          (vpa_mutability_tt_safe_ro Ty (mreceiver (msignature mdef))) \/
	         (sqtype Ty = RO /\
	          sqtype (mreceiver (msignature mdef)) = RDM /\
	          base_subtype CT (sbase Ty)
	            (sbase (mreceiver (msignature mdef))))) /\
        Forall2 (fun arg T => qualified_type_subtype CT arg
          (vpa_mutability_tt_safe_ro Ty T))
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

  (** Call-frame construction for the ordinary AbstractImm receiver rule.
      All premises are produced by the source call rule, dynamic lookup, and
      [wf_method]; no method-body or runtime-frame fact is supplied by a
      client.  The readonly/RDM exception is handled separately because its
      proof additionally uses the call result constraint. *)
  Lemma pico_core_typed_location_call_receiver_abs_imm_regular :
    forall rGamma h loc Ty Treceiver qinner qouter
      (Hsource : pico_core_typed_value CT rGamma h qouter Ty (Iot loc))
      (Hqinner : r_muttype h loc = Some qinner)
      (Hrcv_sub : qualified_type_subtype CT Ty
        (vpa_mutability_tt_abs_imm Ty Treceiver)),
      pico_core_typed_value CT rGamma h qinner Treceiver (Iot loc).
  Proof.
    intros rGamma h loc Ty Treceiver qinner qouter
      Hsource Hqinner Hrcv_sub.
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
      rewrite vpa_mutability_tt_sbase_abs_imm in Hrcv_sub.
      eapply base_trans; eauto.
    - apply qualified_type_subtype_q_subtype in Hrcv_sub.
      rewrite (sq_vpa_tt_eq_qq_abs_imm Ty Treceiver) in Hrcv_sub.
      destruct qruntime; destruct qouter;
      destruct (sqtype Ty); destruct (sqtype Treceiver);
        simpl in *;
        try solve [inversion Hrcv_sub];
        try solve [exfalso; eapply lost_subtype_refl; exact Hrcv_sub];
        eauto.
  Qed.

  Lemma pico_core_typed_call_frame_abs_imm_regular :
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
        (vpa_mutability_tt_abs_imm Ty
          (mreceiver (msignature mdef))))
      (Harg_sub : Forall2 (fun arg T => qualified_type_subtype CT arg
        (vpa_mutability_tt_abs_imm Ty T))
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
      pico_core_typed_value CT (mkr_env (Iot loc :: vals)) h qinner
        (mreceiver (msignature mdef)) (Iot loc)).
    {
      eapply pico_core_typed_value_env_independent with (rGamma1 := rGamma).
      eapply pico_core_typed_location_call_receiver_abs_imm_regular;
        eauto.
    }
    assert (Hparams : forall i T,
      nth_error (mparams (msignature mdef)) i = Some T ->
      exists v,
        nth_error vals i = Some v /\
        pico_core_typed_value CT (mkr_env (Iot loc :: vals)) h
          qinner T v).
    {
      eapply pico_core_typed_call_params_abs_imm
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

  (** The readonly/RDM receiver exception is sound because the callee context
      is the receiver object's own runtime qualifier.  This equality is the
      missing ingredient that a standalone subtype statement does not carry. *)
  Lemma pico_core_typed_location_call_receiver_abs_imm_special :
    forall rGamma h loc Ty Treceiver qinner qouter
      (Hsource : pico_core_typed_value CT rGamma h qouter Ty (Iot loc))
      (Hqinner : r_muttype h loc = Some qinner)
      (Hbase_sub : base_subtype CT (sbase Ty) (sbase Treceiver))
      (Hty_ro : sqtype Ty = RO)
      (Hreceiver_rdm : sqtype Treceiver = RDM),
      pico_core_typed_value CT rGamma h qinner Treceiver (Iot loc).
  Proof.
    intros rGamma h loc Ty Treceiver qinner qouter
      Hsource Hqinner Hbase_sub Hty_ro Hreceiver_rdm.
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

  Lemma pico_core_typed_call_frame_abs_imm_special :
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
        (vpa_mutability_tt_abs_imm Ty T))
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
      pico_core_typed_value CT (mkr_env (Iot loc :: vals)) h qinner
        (mreceiver (msignature mdef)) (Iot loc)).
    {
      eapply pico_core_typed_value_env_independent.
      eapply pico_core_typed_location_call_receiver_abs_imm_special;
        eauto.
    }
    assert (Harg_sub_special : Forall2
      (fun arg T => qualified_type_subtype CT arg
        (vpa_mutability_tt_abs_imm
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
        pico_core_typed_value CT (mkr_env (Iot loc :: vals)) h
          qinner T v).
    {
      eapply pico_core_typed_call_params_abs_imm_special
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

  (** Dynamic call entry for an AbstractImm caller.  The method body comes
      from [wf_method], while the two source-rule receiver forms select the
      regular or readonly/RDM frame proof above. *)
  Lemma pico_core_typed_resolved_method_frame_abs_imm :
    forall sGamma sGamma' rGamma h x y m args loc C mdef vals
      (Htyping : stmt_typing CT sGamma AbstractImm
        (SCall x y m args) sGamma')
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
        sGamma sGamma' rGamma h AbstractImm x y m args
        loc C mdef vals Htyping Henv Hreceiver Hbase Hfind Hargs)
	      as (Ty & Cstatic & argtypes & mdef_static & declaring_class & Hget_y &
	          Href_static & Hget_args & Hfind_static & Hbase_sub &
	          Hsignature & Hwf_method).
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
    rewrite <- Hsignature in Hrcv_sub, Harg_sub.
    destruct Hrcv_sub as [Hrcv_regular | Hrcv_special].
    - eapply pico_core_typed_call_frame_abs_imm_regular
        with (argtypes := argtypes) (Tthis := Tthis)
          (C := C) (declaring_class := declaring_class).
      + exact Henv.
      + exact Hget_y.
      + exact Hget_args.
      + exact Hthis.
      + exact Hreceiver.
      + exact Hbase.
      + exact Hargs.
      + exact Hwf_method.
      + exact Hrcv_regular.
      + exact Harg_sub.
    - destruct Hrcv_special as
        (Hty_ro & Hreceiver_rdm & Hreceiver_base).
      eapply pico_core_typed_call_frame_abs_imm_special
        with (argtypes := argtypes) (Tthis := Tthis)
          (C := C) (declaring_class := declaring_class).
      + exact Henv.
      + exact Hget_y.
      + exact Hget_args.
      + exact Hthis.
      + exact Hreceiver.
      + exact Hbase.
      + exact Hargs.
      + exact Hwf_method.
      + exact Hty_ro.
      + exact Hreceiver_rdm.
      + exact Hreceiver_base.
      + exact Harg_sub.
  Qed.

  Lemma pico_core_typed_location_call_receiver_safe_ro_regular :
    forall rGamma h loc Ty Treceiver qinner qouter
      (Hsource : pico_core_typed_value CT rGamma h qouter Ty (Iot loc))
      (Hqinner : r_muttype h loc = Some qinner)
      (Hrcv_sub : qualified_type_subtype CT Ty
        (vpa_mutability_tt_safe_ro Ty Treceiver)),
      pico_core_typed_value CT rGamma h qinner Treceiver (Iot loc).
  Proof.
    intros rGamma h loc Ty Treceiver qinner qouter
      Hsource Hqinner Hrcv_sub.
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
      rewrite vpa_mutability_tt_sbase_safe_ro in Hrcv_sub.
      eapply base_trans; eauto.
    - apply qualified_type_subtype_q_subtype in Hrcv_sub.
      rewrite (sq_vpa_tt_eq_qq_safe_ro Ty Treceiver) in Hrcv_sub.
      destruct qruntime; destruct qouter;
      destruct (sqtype Ty); destruct (sqtype Treceiver);
        simpl in *;
        try solve [inversion Hrcv_sub];
        try solve [exfalso; eapply lost_subtype_refl; exact Hrcv_sub];
        eauto.
  Qed.

  Lemma pico_core_typed_call_frame_safe_ro_regular :
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
        (vpa_mutability_tt_safe_ro Ty
          (mreceiver (msignature mdef))))
      (Harg_sub : Forall2 (fun arg T => qualified_type_subtype CT arg
        (vpa_mutability_tt_safe_ro Ty T))
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
      pico_core_typed_value CT (mkr_env (Iot loc :: vals)) h qinner
        (mreceiver (msignature mdef)) (Iot loc)).
    {
      eapply pico_core_typed_value_env_independent.
      eapply pico_core_typed_location_call_receiver_safe_ro_regular; eauto.
    }
    assert (Hparams : forall i T,
      nth_error (mparams (msignature mdef)) i = Some T ->
      exists v,
        nth_error vals i = Some v /\
        pico_core_typed_value CT (mkr_env (Iot loc :: vals)) h
          qinner T v).
    {
      eapply pico_core_typed_call_params_safe_ro
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

  Lemma pico_core_typed_call_frame_safe_ro_special :
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
        (vpa_mutability_tt_safe_ro Ty T))
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
      pico_core_typed_value CT (mkr_env (Iot loc :: vals)) h qinner
        (mreceiver (msignature mdef)) (Iot loc)).
    {
      eapply pico_core_typed_value_env_independent.
      eapply pico_core_typed_location_call_receiver_abs_imm_special;
        eauto.
    }
    assert (Harg_sub_special : Forall2
      (fun arg T => qualified_type_subtype CT arg
        (vpa_mutability_tt_safe_ro
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
        pico_core_typed_value CT (mkr_env (Iot loc :: vals)) h
          qinner T v).
    {
      eapply pico_core_typed_call_params_safe_ro_special
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

  Lemma pico_core_typed_resolved_method_frame_safe_ro :
    forall sGamma sGamma' rGamma h mt x y m args loc C mdef vals
      (Htyping : stmt_typing CT sGamma mt (SCall x y m args) sGamma')
      (Hmt : mt <> AbstractImm)
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
	          Hsignature & Hwf_method).
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
    rewrite <- Hsignature in Hrcv_sub, Harg_sub.
    destruct Hrcv_sub as [Hrcv_regular | Hrcv_special].
    - eapply pico_core_typed_call_frame_safe_ro_regular
        with (argtypes := argtypes) (Tthis := Tthis)
          (C := C) (declaring_class := declaring_class).
      + exact Henv.
      + exact Hget_y.
      + exact Hget_args.
      + exact Hthis.
      + exact Hreceiver.
      + exact Hbase.
      + exact Hargs.
      + exact Hwf_method.
      + exact Hrcv_regular.
      + exact Harg_sub.
    - destruct Hrcv_special as
        (Hty_ro & Hreceiver_rdm & Hreceiver_base).
      eapply pico_core_typed_call_frame_safe_ro_special
        with (argtypes := argtypes) (Tthis := Tthis)
          (C := C) (declaring_class := declaring_class).
      + exact Henv.
      + exact Hget_y.
      + exact Hget_args.
      + exact Hthis.
      + exact Hreceiver.
      + exact Hbase.
      + exact Hargs.
      + exact Hwf_method.
      + exact Hty_ro.
      + exact Hreceiver_rdm.
      + exact Hreceiver_base.
      + exact Harg_sub.
  Qed.

  Lemma pico_core_typed_resolved_method_frame :
    forall sGamma sGamma' rGamma h mt x y m args loc C mdef vals
      (Htyping : stmt_typing CT sGamma mt (SCall x y m args) sGamma')
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
    - eapply pico_core_typed_resolved_method_frame_abs_imm; eauto.
    - eapply pico_core_typed_resolved_method_frame_abs_imm; eauto.
      eapply pico_core_concrete_state_call_as_abs; eauto.
    - eapply pico_core_typed_resolved_method_frame_safe_ro; eauto;
        discriminate.
    - eapply pico_core_typed_resolved_method_frame_safe_ro; eauto.
      all: discriminate.
  Qed.

  Lemma pico_core_typed_resolved_method_return_abs_imm :
    forall sGamma sGamma' caller h x y m args loc C mdef vals
      body_sGamma' body_ret_type callee h' retval
      (Htyping : stmt_typing CT sGamma AbstractImm
        (SCall x y m args) sGamma')
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
        sGamma sGamma' caller h AbstractImm x y m args loc C mdef vals
        Htyping Hcaller Hreceiver Hbase Hfind Hargs)
	      as (Ty' & Cstatic' & argtypes' & mdef_static' & declaring_class
	          & Hget_y' & Href_static' & Hget_args' & Hfind_static'
	          & Hbase_sub & Hsignature & Hwf_method).
    assert (HTy : Ty = Ty') by congruence.
    subst Ty'.
    assert (Hstatic_eq : mdef_static = mdef_static').
    { eapply find_method_with_name_deterministic; eauto. }
    subst mdef_static'.
    rewrite <- Hsignature in Hret_sub.
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
    assert (Hreturn_target : pico_core_typed_value CT callee h' qouter Tx retval).
    {
      eapply pico_core_typed_return_value_abs_imm
        with (Ty := Ty) (Tbody := body_ret_type)
          (Tmethod := mret (msignature mdef)); eauto.
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

  Lemma pico_core_typed_resolved_method_return_safe_ro :
    forall sGamma sGamma' mt caller h x y m args loc C mdef vals
      body_sGamma' body_ret_type callee h' retval
      (Hmt : mt <> AbstractImm)
      (Hmt_cs : mt <> ConcreteState)
      (Htyping : stmt_typing CT sGamma mt
        (SCall x y m args) sGamma')
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
	          & Hbase_sub & Hsignature & Hwf_method).
    assert (HTy : Ty = Ty') by congruence.
    subst Ty'.
    assert (Hstatic_eq : mdef_static = mdef_static').
    { eapply find_method_with_name_deterministic; eauto. }
    subst mdef_static'.
    rewrite <- Hsignature in Hret_sub.
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
    assert (Hreturn_target : pico_core_typed_value CT callee h' qouter Tx retval).
    {
      eapply pico_core_typed_return_value_safe_ro
        with (Ty := Ty) (Tbody := body_ret_type)
          (Tmethod := mret (msignature mdef)); eauto.
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
        (SCall x y m args) sGamma')
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
    - eapply pico_core_typed_resolved_method_return_abs_imm; eauto.
    - eapply pico_core_typed_resolved_method_return_abs_imm; eauto.
      eapply pico_core_concrete_state_call_as_abs; eauto.
    - change (stmt_typing CT sGamma SafeRO
        (SCall x y m args) sGamma') in Htyping.
      assert (Hsafe : SafeRO <> AbstractImm) by discriminate.
      assert (Hsafe_cs : SafeRO <> ConcreteState) by discriminate.
      exact
        (pico_core_typed_resolved_method_return_safe_ro
          sGamma sGamma' SafeRO caller h x y m args loc C mdef vals
          body_sGamma' body_ret_type callee h' retval Hsafe Hsafe_cs Htyping Hcaller
          Hreceiver Hbase Hfind Hargs Hbody_ret_static Hbody_return_sub
          Hextend Hcallee Hcallee_receiver Hretval).
    - change (stmt_typing CT sGamma ConcreteImm
        (SCall x y m args) sGamma') in Htyping.
      assert (Hconcrete : ConcreteImm <> AbstractImm) by discriminate.
      assert (Hconcrete_cs : ConcreteImm <> ConcreteState) by discriminate.
      exact
        (pico_core_typed_resolved_method_return_safe_ro
          sGamma sGamma' ConcreteImm caller h x y m args loc C mdef vals
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
    forall rGamma h qcontext T v loc f value o
      (Htyped : pico_core_typed_value CT rGamma h qcontext T v)
      (Hobj : runtime_getObj h loc = Some o),
      pico_core_typed_value CT rGamma
        (update_field h loc f value) qcontext T v.
  Proof.
    intros rGamma h qcontext T v loc f value o Htyped Hobj.
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
    forall rGamma h qcontext T v o
      (Htyped : pico_core_typed_value CT rGamma h qcontext T v),
      pico_core_typed_value CT rGamma (h ++ [o]) qcontext T v.
  Proof.
    intros rGamma h qcontext T v o Htyped.
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
      apply pico_core_typed_value_real_lr_value with (rGamma := rGamma).
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

  (** [ownP_lift_step] temporarily closes every invariant while handing the
      concrete machine state to the operational semantics.  This derived rule
      retains the corresponding mask-restoration token, so a direct semantic
      continuation can resume at the caller's original mask after the step. *)
  Lemma pico_core_ownP_wp_from_direct_step_contI :
    forall E Phi e state
      (Hready : exists e' state', pico_core_step CT e state e' state'),
      ownP state -∗
      (▷ ∀ e' state',
        ⌜pico_core_step CT e state e' state'⌝ -∗
        ownP state' -∗
        WP e' @ NotStuck; E {{ Phi }}) -∗
      WP e @ NotStuck; E {{ Phi }}.
  Proof.
    intros E Phi e state Hready.
    iIntros "Hown Hcont".
    iApply ownP_lift_step.
    iMod (fupd_mask_subseteq ∅) as "Hclose".
    { set_solver. }
    iModIntro.
    iExists state.
    iSplit.
    - iPureIntro.
      apply pico_core_reducible_iff_step.
      exact Hready.
    - iSplitL "Hown".
      + iNext.
        iExact "Hown".
      + iNext.
        iIntros (k e' state' efs Hprim) "Hown".
        pose proof
          (pico_core_prim_step_no_forks CT e state k e' state' efs Hprim)
          as ->.
        pose proof
          (pico_core_prim_step_is_core_step
            CT e state k e' state' [] Hprim)
          as Hstep.
        iPoseProof
          ("Hcont" $! e' state' with "[] Hown") as "Hwp".
        { iPureIntro. exact Hstep. }
        iMod "Hclose".
        iModIntro.
        simpl.
        iFrame.
  Qed.

  Lemma pico_core_stmt_post_ownP_not_stuck_wpI :
    forall E Phi e state sGamma' K
      (Hready : exists e' state', pico_core_step CT e state e' state')
      (Hpost : forall e' state',
        pico_core_step CT e state e' state' ->
        pico_core_stmt_post sGamma' K e' state'),
      ownP state -∗
      pico_core_stmt_post_contI sGamma' K E Phi -∗
      WP e @ NotStuck; E {{ Phi }}.
  Proof.
    intros E Phi e state sGamma' K Hready Hpost.
    iIntros "Hown Hcont".
    iApply
      (pico_core_ownP_wp_from_direct_step_contI
        E Phi e state Hready with "Hown [Hcont]").
    iNext.
    iIntros (e' state') "%Hstep Hown".
    iApply ("Hcont" $! e' state' with "[] Hown").
    iPureIntro.
    eapply Hpost; eauto.
  Qed.

  Lemma pico_core_typed_local_reducible :
    forall sGamma sGamma' rGamma h sigma mt T x V K
      (Htyping : stmt_typing CT sGamma mt (SLocal T x) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h),
      @reducible
        (pico_core_language CT)
        (CoreRun rGamma (SLocal T x) V K)
        (mkPicoCoreState h sigma).
  Proof.
    intros sGamma sGamma' rGamma h sigma mt T x V K Htyping Henv.
    inversion Htyping; subst.
    pose proof
      (pico_core_typed_env_real_lr_env sGamma rGamma h Henv)
      as Hreal.
    pose proof
      (pico_typed_runtime_env_local_runtime_absent
        CT sGamma rGamma h x Hreal Hnone)
      as Hruntime_none.
    eapply pico_core_reducible_from_step.
    eapply PCS_Local.
    exact Hruntime_none.
  Qed.

  Lemma pico_core_typed_assign_null_reducible :
    forall sGamma rGamma h sigma mt x V K
      (Htyping : stmt_typing CT sGamma mt (SVarAss x ENull) sGamma)
      (Henv : pico_core_typed_env CT sGamma rGamma h),
      @reducible
        (pico_core_language CT)
        (CoreRun rGamma (SVarAss x ENull) V K)
        (mkPicoCoreState h sigma).
  Proof.
    intros sGamma rGamma h sigma mt x V K Htyping Henv.
    inversion Htyping; subst.
    destruct
      (pico_core_typed_env_lookup
        CT sGamma rGamma h x Tx Henv Hget_x)
      as (qcontext & old & Hx & Htyped).
    eapply pico_core_reducible_from_step.
    eapply PCS_AssignNull; eauto.
  Qed.

  Lemma pico_core_typed_assign_int_reducible :
    forall sGamma rGamma h sigma mt x n V K
      (Htyping : stmt_typing CT sGamma mt (SVarAss x (EInt n)) sGamma)
      (Henv : pico_core_typed_env CT sGamma rGamma h),
      @reducible
        (pico_core_language CT)
        (CoreRun rGamma (SVarAss x (EInt n)) V K)
        (mkPicoCoreState h sigma).
  Proof.
    intros sGamma rGamma h sigma mt x n V K Htyping Henv.
    inversion Htyping; subst.
    destruct
      (pico_core_typed_env_lookup
        CT sGamma rGamma h x Tx Henv Hget_x)
      as (qcontext & old & Hx & Htyped).
    eapply pico_core_reducible_from_step.
    eapply PCS_AssignInt; eauto.
  Qed.

  Lemma pico_core_typed_assign_var_reducible :
    forall sGamma rGamma h sigma mt x y V K
      (Htyping : stmt_typing CT sGamma mt (SVarAss x (EVar y)) sGamma)
      (Henv : pico_core_typed_env CT sGamma rGamma h),
      @reducible
        (pico_core_language CT)
        (CoreRun rGamma (SVarAss x (EVar y)) V K)
        (mkPicoCoreState h sigma).
  Proof.
    intros sGamma rGamma h sigma mt x y V K Htyping Henv.
    inversion Htyping; subst.
    inversion Htype_e; subst.
    destruct
      (pico_core_typed_env_lookup
        CT sGamma rGamma h x Tx Henv Hget_x)
      as (qcontext_x & old & Hx & Htyped_x).
    destruct
      (pico_core_typed_env_lookup
        CT sGamma rGamma h y _ Henv Hget)
      as (qcontext_y & val_y & Hy & Htyped_y).
    eapply pico_core_reducible_from_step.
    eapply PCS_AssignVar; eauto.
  Qed.

  Lemma pico_core_typed_seq_reducible :
    forall sGamma sGamma'' rGamma h sigma mt s1 s2 V K
      (Htyping : stmt_typing CT sGamma mt (SSeq s1 s2) sGamma''),
      @reducible
        (pico_core_language CT)
        (CoreRun rGamma (SSeq s1 s2) V K)
        (mkPicoCoreState h sigma).
  Proof.
    intros sGamma sGamma'' rGamma h sigma mt s1 s2 V K Htyping.
    eapply pico_core_reducible_from_step.
    apply PCS_Seq.
  Qed.

  Lemma pico_core_typed_local_ownP_not_stuck_wpI :
    forall sGamma sGamma' rGamma h sigma mt T x V K E Phi
      (Htyping : stmt_typing CT sGamma mt (SLocal T x) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hlrstate : pico_core_lr_state CT (mkPicoCoreState h sigma)),
      ownP (mkPicoCoreState h sigma) -∗
      pico_core_stmt_post_contI sGamma' K E Phi -∗
      WP CoreRun rGamma (SLocal T x) V K
        @ NotStuck; E {{ Phi }}.
  Proof.
    intros sGamma sGamma' rGamma h sigma mt T x V K E Phi
      Htyping Henv Hlrstate.
    assert (Hready :
      exists e' state',
        pico_core_step CT
          (CoreRun rGamma (SLocal T x) V K)
          (mkPicoCoreState h sigma) e' state').
    {
      apply pico_core_step_from_reducible.
      eapply pico_core_typed_local_reducible; eauto.
    }
    assert (Hpost : forall e' state',
      pico_core_step CT
        (CoreRun rGamma (SLocal T x) V K)
        (mkPicoCoreState h sigma) e' state' ->
      pico_core_stmt_post sGamma' K e' state').
    {
      intros e' state' Hstep.
      eapply pico_core_typed_local_step_post; eauto.
    }
    iIntros "Hown Hcont".
    iApply
      (pico_core_stmt_post_ownP_not_stuck_wpI
        E Phi
        (CoreRun rGamma (SLocal T x) V K)
        (mkPicoCoreState h sigma)
        sGamma' K Hready Hpost
        with "Hown Hcont").
  Qed.

  Lemma pico_core_typed_assign_null_ownP_not_stuck_wpI :
    forall sGamma rGamma h sigma mt x V K E Phi
      (Htyping : stmt_typing CT sGamma mt (SVarAss x ENull) sGamma)
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hlrstate : pico_core_lr_state CT (mkPicoCoreState h sigma)),
      ownP (mkPicoCoreState h sigma) -∗
      pico_core_stmt_post_contI sGamma K E Phi -∗
      WP CoreRun rGamma (SVarAss x ENull) V K
        @ NotStuck; E {{ Phi }}.
  Proof.
    intros sGamma rGamma h sigma mt x V K E Phi
      Htyping Henv Hlrstate.
    assert (Hready :
      exists e' state',
        pico_core_step CT
          (CoreRun rGamma (SVarAss x ENull) V K)
          (mkPicoCoreState h sigma) e' state').
    {
      apply pico_core_step_from_reducible.
      eapply pico_core_typed_assign_null_reducible; eauto.
    }
    assert (Hpost : forall e' state',
      pico_core_step CT
        (CoreRun rGamma (SVarAss x ENull) V K)
        (mkPicoCoreState h sigma) e' state' ->
      pico_core_stmt_post sGamma K e' state').
    {
      intros e' state' Hstep.
      eapply pico_core_typed_assign_null_step_post; eauto.
    }
    iIntros "Hown Hcont".
    iApply
      (pico_core_stmt_post_ownP_not_stuck_wpI
        E Phi
        (CoreRun rGamma (SVarAss x ENull) V K)
        (mkPicoCoreState h sigma)
        sGamma K Hready Hpost
        with "Hown Hcont").
  Qed.

  Lemma pico_core_typed_assign_int_ownP_not_stuck_wpI :
    forall sGamma rGamma h sigma mt x n V K E Phi
      (Htyping : stmt_typing CT sGamma mt (SVarAss x (EInt n)) sGamma)
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hlrstate : pico_core_lr_state CT (mkPicoCoreState h sigma)),
      ownP (mkPicoCoreState h sigma) -∗
      pico_core_stmt_post_contI sGamma K E Phi -∗
      WP CoreRun rGamma (SVarAss x (EInt n)) V K
        @ NotStuck; E {{ Phi }}.
  Proof.
    intros sGamma rGamma h sigma mt x n V K E Phi
      Htyping Henv Hlrstate.
    assert (Hready :
      exists e' state',
        pico_core_step CT
          (CoreRun rGamma (SVarAss x (EInt n)) V K)
          (mkPicoCoreState h sigma) e' state').
    {
      apply pico_core_step_from_reducible.
      eapply pico_core_typed_assign_int_reducible; eauto.
    }
    assert (Hpost : forall e' state',
      pico_core_step CT
        (CoreRun rGamma (SVarAss x (EInt n)) V K)
        (mkPicoCoreState h sigma) e' state' ->
      pico_core_stmt_post sGamma K e' state').
    {
      intros e' state' Hstep.
      eapply pico_core_typed_assign_int_step_post; eauto.
    }
    iIntros "Hown Hcont".
    iApply
      (pico_core_stmt_post_ownP_not_stuck_wpI
        E Phi
        (CoreRun rGamma (SVarAss x (EInt n)) V K)
        (mkPicoCoreState h sigma)
        sGamma K Hready Hpost
        with "Hown Hcont").
  Qed.

  Lemma pico_core_typed_assign_var_ownP_not_stuck_wpI :
    forall sGamma rGamma h sigma mt x y V K E Phi
      (Htyping : stmt_typing CT sGamma mt (SVarAss x (EVar y)) sGamma)
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hlrstate : pico_core_lr_state CT (mkPicoCoreState h sigma)),
      ownP (mkPicoCoreState h sigma) -∗
      pico_core_stmt_post_contI sGamma K E Phi -∗
      WP CoreRun rGamma (SVarAss x (EVar y)) V K
        @ NotStuck; E {{ Phi }}.
  Proof.
    intros sGamma rGamma h sigma mt x y V K E Phi
      Htyping Henv Hlrstate.
    assert (Hready :
      exists e' state',
        pico_core_step CT
          (CoreRun rGamma (SVarAss x (EVar y)) V K)
          (mkPicoCoreState h sigma) e' state').
    {
      apply pico_core_step_from_reducible.
      eapply pico_core_typed_assign_var_reducible; eauto.
    }
    assert (Hpost : forall e' state',
      pico_core_step CT
        (CoreRun rGamma (SVarAss x (EVar y)) V K)
        (mkPicoCoreState h sigma) e' state' ->
      pico_core_stmt_post sGamma K e' state').
    {
      intros e' state' Hstep.
      eapply pico_core_typed_assign_var_step_post; eauto.
    }
    iIntros "Hown Hcont".
    iApply
      (pico_core_stmt_post_ownP_not_stuck_wpI
        E Phi
        (CoreRun rGamma (SVarAss x (EVar y)) V K)
        (mkPicoCoreState h sigma)
        sGamma K Hready Hpost
        with "Hown Hcont").
  Qed.

  Lemma pico_core_typed_varass_field_ownP_not_stuck_wpI :
    forall sGamma sGamma' rGamma h sigma mt x y f V K E Phi
      (Htyping :
        stmt_typing CT sGamma mt (SVarAss x (EField y f)) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hlrstate : pico_core_lr_state CT (mkPicoCoreState h sigma))
      (Hread_typed :
        forall loc v V',
          runtime_getVal rGamma y = Some (Iot loc) ->
          wm_read sigma V (loc, f) v V' ->
          pico_core_typed_env CT sGamma'
            (set_vars rGamma (update x v (vars rGamma))) h),
      ownP (mkPicoCoreState h sigma) -∗
      pico_core_stmt_post_contI sGamma' K E Phi -∗
      WP CoreRun rGamma (SVarAss x (EField y f)) V K
        @ NotStuck; E {{ Phi }}.
  Proof.
    intros sGamma sGamma' rGamma h sigma mt x y f V K E Phi
      Htyping Henv Hlrstate Hread_typed.
    assert (Hready :
      exists e' state',
        pico_core_step CT
          (CoreRun rGamma (SVarAss x (EField y f)) V K)
          (mkPicoCoreState h sigma)
          e' state').
    {
      apply pico_core_step_from_reducible.
      eapply pico_core_typed_varass_field_reducible; eauto.
    }
    iIntros "Hown Hcont".
    iApply
      (pico_core_ownP_wp_from_direct_step_contI
        E Phi
        (CoreRun rGamma (SVarAss x (EField y f)) V K)
        (mkPicoCoreState h sigma)
        Hready
        with "Hown [Hcont]").
    iNext.
    iIntros (e' state') "%Hstep Hown".
    iApply ("Hcont" $! e' state' with "[] Hown").
    iPureIntro.
    eapply pico_core_typed_varass_field_step_post; eauto.
  Qed.

  Theorem pico_core_typed_pure_varass_ownP_not_stuck_wpI :
    forall sGamma rGamma h sigma mt x e V K E Phi
      (Htyping : stmt_typing CT sGamma mt (SVarAss x e) sGamma)
      (Henv : pico_core_typed_env CT sGamma rGamma h)
      (Hlrstate : pico_core_lr_state CT (mkPicoCoreState h sigma))
      (Hpure : match e with EField _ _ => False | _ => True end),
      ownP (mkPicoCoreState h sigma) -∗
      pico_core_stmt_post_contI sGamma K E Phi -∗
      WP CoreRun rGamma (SVarAss x e) V K
        @ NotStuck; E {{ Phi }}.
  Proof.
    intros sGamma rGamma h sigma mt x e V K E Phi
      Htyping Henv Hlrstate Hpure.
    destruct e as [|y|n|y f].
    - iIntros "Hown Hcont".
      iApply
        (pico_core_typed_assign_null_ownP_not_stuck_wpI
          with "Hown Hcont"); eauto.
    - iIntros "Hown Hcont".
      iApply
        (pico_core_typed_assign_var_ownP_not_stuck_wpI
          with "Hown Hcont"); eauto.
    - iIntros "Hown Hcont".
      iApply
        (pico_core_typed_assign_int_ownP_not_stuck_wpI
          with "Hown Hcont"); eauto.
    - contradiction.
  Qed.

  Theorem pico_core_typed_fldwrite_progress_ownP_not_stuck_wpI :
    forall sGamma sGamma' rGamma h sigma mt x f y V K E Phi
      (Htyping : stmt_typing CT sGamma mt (SFldWrite x f y) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h),
      ownP (mkPicoCoreState h sigma) -∗
      (▷ ∀ e' state',
        ⌜pico_core_step CT
          (CoreRun rGamma (SFldWrite x f y) V K)
          (mkPicoCoreState h sigma) e' state'⌝ -∗
        ownP state' -∗
        WP e' @ NotStuck; E {{ Phi }}) -∗
      WP CoreRun rGamma (SFldWrite x f y) V K
        @ NotStuck; E {{ Phi }}.
  Proof.
    intros sGamma sGamma' rGamma h sigma mt x f y V K E Phi
      Htyping Henv.
    assert (Hready :
      exists e' state',
        pico_core_step CT
          (CoreRun rGamma (SFldWrite x f y) V K)
          (mkPicoCoreState h sigma) e' state').
    {
      apply pico_core_step_from_reducible.
      eapply pico_core_typed_fldwrite_reducible; eauto.
    }
    iIntros "Hown Hnext".
    iApply
      (pico_core_ownP_wp_from_direct_step_contI
        E Phi
        (CoreRun rGamma (SFldWrite x f y) V K)
        (mkPicoCoreState h sigma) Hready
        with "Hown Hnext").
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

  Theorem pico_core_typed_fldwrite_fundamentalI :
    forall sGamma sGamma' mt x f y
      (Htyping : stmt_typing CT sGamma mt (SFldWrite x f y) sGamma'),
      ⊢ pico_core_typed_stmt_wpI
        sGamma mt (SFldWrite x f y) sGamma'.
  Proof.
    intros sGamma sGamma' mt x f y Htyping.
    unfold pico_core_typed_stmt_wpI.
    iModIntro.
    iIntros (rGamma h sigma V K E Phi)
      "%Henv %Hlrstate Hown Houtcomes".
    iPoseProof
      (pico_core_stmt_post_cont_from_outcomeI
        sGamma' K E Phi with "Houtcomes") as "Hpost".
    iApply
      (pico_core_typed_fldwrite_progress_ownP_not_stuck_wpI
        with "Hown [Hpost]"); eauto.
    iNext.
    iIntros (e' state') "%Hstep Hown".
    iApply ("Hpost" $! e' state' with "[] Hown").
    iPureIntro.
    eapply pico_core_typed_fldwrite_step_post; eauto.
  Qed.

  Theorem pico_core_typed_new_progress_ownP_not_stuck_wpI :
    forall sGamma sGamma' rGamma h sigma mt x qc C args V K E Phi
      (Htyping : stmt_typing CT sGamma mt (SNew x qc C args) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h),
      ownP (mkPicoCoreState h sigma) -∗
      (▷ ∀ e' state',
        ⌜pico_core_step CT
          (CoreRun rGamma (SNew x qc C args) V K)
          (mkPicoCoreState h sigma) e' state'⌝ -∗
        ownP state' -∗
        WP e' @ NotStuck; E {{ Phi }}) -∗
      WP CoreRun rGamma (SNew x qc C args) V K
        @ NotStuck; E {{ Phi }}.
  Proof.
    intros sGamma sGamma' rGamma h sigma mt x qc C args V K E Phi
      Htyping Henv.
    assert (Hready :
      exists e' state',
        pico_core_step CT
          (CoreRun rGamma (SNew x qc C args) V K)
          (mkPicoCoreState h sigma) e' state').
    {
      apply pico_core_step_from_reducible.
      eapply pico_core_typed_new_reducible; eauto.
    }
    iIntros "Hown Hnext".
    iApply
      (pico_core_ownP_wp_from_direct_step_contI
        E Phi
        (CoreRun rGamma (SNew x qc C args) V K)
        (mkPicoCoreState h sigma) Hready
        with "Hown Hnext").
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

  Theorem pico_core_typed_new_fundamentalI :
    forall sGamma sGamma' mt x qc C args
      (Htyping : stmt_typing CT sGamma mt (SNew x qc C args) sGamma'),
      ⊢ pico_core_typed_stmt_wpI
        sGamma mt (SNew x qc C args) sGamma'.
  Proof.
    intros sGamma sGamma' mt x qc C args Htyping.
    unfold pico_core_typed_stmt_wpI.
    iModIntro.
    iIntros (rGamma h sigma V K E Phi)
      "%Henv %Hlrstate Hown Houtcomes".
    iPoseProof
      (pico_core_stmt_post_cont_from_outcomeI
        sGamma' K E Phi with "Houtcomes") as "Hpost".
    iApply
      (pico_core_typed_new_progress_ownP_not_stuck_wpI
        with "Hown [Hpost]"); eauto.
    iNext.
    iIntros (e' state') "%Hstep Hown".
    iApply ("Hpost" $! e' state' with "[] Hown").
    iPureIntro.
    eapply pico_core_typed_new_step_post; eauto.
  Qed.

  Theorem pico_core_typed_call_progress_ownP_not_stuck_wpI :
    forall sGamma sGamma' rGamma h sigma mt x y m args V K E Phi
      (Htyping : stmt_typing CT sGamma mt (SCall x y m args) sGamma')
      (Henv : pico_core_typed_env CT sGamma rGamma h),
      ownP (mkPicoCoreState h sigma) -∗
      (▷ ∀ e' state',
        ⌜pico_core_step CT
          (CoreRun rGamma (SCall x y m args) V K)
          (mkPicoCoreState h sigma) e' state'⌝ -∗
        ownP state' -∗
        WP e' @ NotStuck; E {{ Phi }}) -∗
      WP CoreRun rGamma (SCall x y m args) V K
        @ NotStuck; E {{ Phi }}.
  Proof.
    intros sGamma sGamma' rGamma h sigma mt x y m args V K E Phi
      Htyping Henv.
    assert (Hready :
      exists e' state',
        pico_core_step CT
          (CoreRun rGamma (SCall x y m args) V K)
          (mkPicoCoreState h sigma) e' state').
    {
      apply pico_core_step_from_reducible.
      eapply pico_core_typed_call_reducible; eauto.
    }
    iIntros "Hown Hnext".
    iApply
      (pico_core_ownP_wp_from_direct_step_contI
        E Phi
        (CoreRun rGamma (SCall x y m args) V K)
        (mkPicoCoreState h sigma) Hready
        with "Hown Hnext").
  Qed.

  Theorem pico_core_typed_skip_fundamentalI :
    forall sGamma mt
      (Htyping : stmt_typing CT sGamma mt SSkip sGamma),
      ⊢ pico_core_typed_stmt_wpI sGamma mt SSkip sGamma.
  Proof.
    intros sGamma mt Htyping.
    unfold pico_core_typed_stmt_wpI.
    iModIntro.
    iIntros (rGamma h sigma V K E Phi)
      "%Henv %Hlrstate Hown Hcont".
    unfold pico_core_typed_outcome_contI.
    iDestruct "Hcont" as "[#Hok _]".
    iApply ("Hok" with "[] [] Hown").
    - iPureIntro.
      exact Henv.
    - iPureIntro.
      exact Hlrstate.
  Qed.

  Theorem pico_core_typed_local_fundamentalI :
    forall sGamma sGamma' mt T x
      (Htyping : stmt_typing CT sGamma mt (SLocal T x) sGamma'),
      ⊢ pico_core_typed_stmt_wpI sGamma mt (SLocal T x) sGamma'.
  Proof.
    intros sGamma sGamma' mt T x Htyping.
    unfold pico_core_typed_stmt_wpI.
    iModIntro.
    iIntros (rGamma h sigma V K E Phi)
      "%Henv %Hlrstate Hown Hcont".
    iPoseProof
      (pico_core_stmt_post_cont_from_outcomeI
        sGamma' K E Phi with "Hcont") as "Hpost".
    iApply
      (pico_core_typed_local_ownP_not_stuck_wpI
        with "Hown Hpost"); eauto.
  Qed.

  Theorem pico_core_typed_pure_varass_fundamentalI :
    forall sGamma mt x e
      (Htyping : stmt_typing CT sGamma mt (SVarAss x e) sGamma)
      (Hpure : match e with EField _ _ => False | _ => True end),
      ⊢ pico_core_typed_stmt_wpI sGamma mt (SVarAss x e) sGamma.
  Proof.
    intros sGamma mt x e Htyping Hpure.
    unfold pico_core_typed_stmt_wpI.
    iModIntro.
    iIntros (rGamma h sigma V K E Phi)
      "%Henv %Hlrstate Hown Hcont".
    iPoseProof
      (pico_core_stmt_post_cont_from_outcomeI
        sGamma K E Phi with "Hcont") as "Hpost".
    iApply
      (pico_core_typed_pure_varass_ownP_not_stuck_wpI
        with "Hown Hpost"); eauto.
  Qed.

  (** Sequential composition is the first genuinely compositional LR rule.
      The first statement runs under a [KSeq] frame.  Its successful outcome
      takes the administrative [PCS_SkipSeq] step and starts the second typed
      statement; exceptional outcomes are propagated to the caller unchanged. *)
  Theorem pico_core_typed_seq_compositionI :
    forall sGamma sGamma_mid sGamma' mt s1 s2,
      pico_core_typed_stmt_wpI sGamma mt s1 sGamma_mid -∗
      pico_core_typed_stmt_wpI sGamma_mid mt s2 sGamma' -∗
      pico_core_typed_stmt_wpI
        sGamma mt (SSeq s1 s2) sGamma'.
  Proof.
    intros sGamma sGamma_mid sGamma' mt s1 s2.
    iIntros "#Hfirst #Hsecond".
    unfold pico_core_typed_stmt_wpI.
    iModIntro.
    iIntros (rGamma h sigma V K E Phi)
      "%Henv %Hstate Hown #Hfinal".
    iPoseProof "Hfinal" as "#Hfinal_cases".
    iDestruct "Hfinal_cases" as
      "[#Hfinal_ok [#Hfinal_npe #Hfinal_mutation]]".
    assert (Hseq_ready :
      exists e' state',
        pico_core_step CT
          (CoreRun rGamma (SSeq s1 s2) V K)
          (mkPicoCoreState h sigma) e' state').
    {
      exists (CoreRun rGamma s1 V (KSeq s2 :: K)).
      exists (mkPicoCoreState h sigma).
      apply PCS_Seq.
    }
    iApply
      (pico_core_ownP_wp_from_direct_step_contI
        E Phi
        (CoreRun rGamma (SSeq s1 s2) V K)
        (mkPicoCoreState h sigma) Hseq_ready
        with "Hown").
    iNext.
    iIntros (e' state') "%Hseq Hown".
    inversion Hseq; subst.
    iApply
      ("Hfirst" $! rGamma h sigma V (KSeq s2 :: K) E Phi
        with "[] [] Hown").
    - iPureIntro.
      exact Henv.
    - iPureIntro.
      exact Hstate.
    - unfold pico_core_typed_outcome_contI.
      iSplit.
      + iModIntro.
        iIntros (rGamma_mid state_mid V_mid)
          "%Henv_mid %Hstate_mid Hown_mid".
        destruct state_mid as [h_mid sigma_mid].
        assert (Hskip_ready :
          exists e'' state'',
            pico_core_step CT
              (CoreRun rGamma_mid SSkip V_mid (KSeq s2 :: K))
              (mkPicoCoreState h_mid sigma_mid) e'' state'').
        {
          exists (CoreRun rGamma_mid s2 V_mid K).
          exists (mkPicoCoreState h_mid sigma_mid).
          apply PCS_SkipSeq.
        }
        iApply
          (pico_core_ownP_wp_from_direct_step_contI
            E Phi
            (CoreRun rGamma_mid SSkip V_mid (KSeq s2 :: K))
            (mkPicoCoreState h_mid sigma_mid) Hskip_ready
            with "Hown_mid").
        iNext.
        iIntros (e'' state'') "%Hskip Hown_second".
        inversion Hskip; subst.
        iApply
          ("Hsecond" $! rGamma_mid h_mid sigma_mid V_mid K E Phi
            with "[] [] Hown_second Hfinal").
        * iPureIntro.
          exact Henv_mid.
        * iPureIntro.
          exact Hstate_mid.
      + iSplit.
        * iModIntro.
          iIntros (rGamma_done state_done V_done)
            "%Hstate_done Hown_done".
          iApply ("Hfinal_npe" with "[] Hown_done").
          iPureIntro.
          exact Hstate_done.
        * iModIntro.
          iIntros (rGamma_done state_done V_done)
            "%Hstate_done Hown_done".
          iApply ("Hfinal_mutation" with "[] Hown_done").
          iPureIntro.
          exact Hstate_done.
  Qed.

  (** Semantic implementations of the weak/effectful PICO primitives.  This
      is the sole open-recursion boundary of the structural LR: field reads
      and writes are supplied by the cache protocol, allocation by the state
      invariant, and calls by the guarded method environment. *)
  Definition pico_core_semantic_primitivesI : iProp Sigma :=
    (□ ∀ (sGamma : s_env) (mt : method_type) (x y f : var),
      ⌜stmt_typing CT sGamma mt
        (SVarAss x (EField y f)) sGamma⌝ -∗
      pico_core_typed_stmt_wpI
        sGamma mt (SVarAss x (EField y f)) sGamma) ∗
    (□ ∀ (sGamma sGamma' : s_env) (mt : method_type)
          (x f y : var),
      ⌜stmt_typing CT sGamma mt (SFldWrite x f y) sGamma'⌝ -∗
      pico_core_typed_stmt_wpI
        sGamma mt (SFldWrite x f y) sGamma') ∗
    (□ ∀ (sGamma sGamma' : s_env) (mt : method_type)
          (x : var) (qc : q_c) (C : class_name) (args : list var),
      ⌜stmt_typing CT sGamma mt (SNew x qc C args) sGamma'⌝ -∗
      pico_core_typed_stmt_wpI
        sGamma mt (SNew x qc C args) sGamma') ∗
    (□ ∀ (sGamma sGamma' : s_env) (mt : method_type)
          (x y : var) (m : method_name) (args : list var),
      ⌜stmt_typing CT sGamma mt (SCall x y m args) sGamma'⌝ -∗
      pico_core_typed_stmt_wpI
        sGamma mt (SCall x y m args) sGamma') ∗
    (□ ∀ (sGamma sGamma' : s_env) (mt : method_type)
          (x : var) (s_zero s_nonzero : stmt),
      ⌜stmt_typing CT sGamma mt
        (SIfZero x s_zero s_nonzero) sGamma'⌝ -∗
      pico_core_typed_stmt_wpI
        sGamma mt (SIfZero x s_zero s_nonzero) sGamma').

  Definition pico_core_field_read_handlerI : iProp Sigma :=
    □ ∀ (sGamma : s_env) (mt : method_type) (x y f : var),
      ⌜stmt_typing CT sGamma mt
        (SVarAss x (EField y f)) sGamma⌝ -∗
      pico_core_typed_stmt_wpI
        sGamma mt (SVarAss x (EField y f)) sGamma.

  Definition pico_core_call_handlerI : iProp Sigma :=
    □ ∀ (sGamma sGamma' : s_env) (mt : method_type)
          (x y : var) (m : method_name) (args : list var),
      ⌜stmt_typing CT sGamma mt (SCall x y m args) sGamma'⌝ -∗
      pico_core_typed_stmt_wpI
        sGamma mt (SCall x y m args) sGamma'.

  (** This older typed-WP handler is the operational boundary for integer
      guards. The canonical resource LR proves [SIfZero] structurally from the
      strict [TInt] value relation and does not require this handler. *)
  Definition pico_core_ifzero_handlerI : iProp Sigma :=
    □ ∀ (sGamma sGamma' : s_env) (mt : method_type)
          (x : var) (s_zero s_nonzero : stmt),
      ⌜stmt_typing CT sGamma mt
        (SIfZero x s_zero s_nonzero) sGamma'⌝ -∗
      pico_core_typed_stmt_wpI
        sGamma mt (SIfZero x s_zero s_nonzero) sGamma'.

  Theorem pico_core_semantic_primitives_introI :
    pico_core_field_read_handlerI -∗
    pico_core_call_handlerI -∗
    pico_core_ifzero_handlerI -∗
    pico_core_semantic_primitivesI.
  Proof.
    iIntros "#Hread #Hcall #Hifzero".
    unfold pico_core_semantic_primitivesI.
    iSplit; [iExact "Hread" |].
    iSplit.
    - iModIntro.
      iIntros (sGamma sGamma' mt x f y) "%Htyping".
      iApply pico_core_typed_fldwrite_fundamentalI.
      exact Htyping.
    - iSplit.
      + iModIntro.
        iIntros (sGamma sGamma' mt x qc C args) "%Htyping".
        iApply pico_core_typed_new_fundamentalI.
        exact Htyping.
      + iSplit; [iExact "Hcall" | iExact "Hifzero"].
  Qed.

  (** Fundamental theorem for the complete source statement grammar, relative
      only to semantic implementations of its weak/effectful primitives. *)
  Theorem pico_core_stmt_fundamentalI :
    forall sGamma mt s sGamma'
      (Htyping : stmt_typing CT sGamma mt s sGamma'),
      pico_core_semantic_primitivesI -∗
      pico_core_typed_stmt_wpI sGamma mt s sGamma'.
  Proof.
    intros sGamma mt s sGamma' Htyping.
    remember CT as CT_index eqn:HCT in Htyping.
    induction Htyping.
    all: subst CT0.
    - iIntros "_".
      iApply pico_core_typed_skip_fundamentalI.
      constructor.
      exact Hwf.
    - iIntros "_".
      iApply pico_core_typed_local_fundamentalI.
      econstructor; eauto.
    - destruct e as [|source|n|receiver field].
      + iIntros "_".
        iApply pico_core_typed_pure_varass_fundamentalI.
        * econstructor; eauto.
        * exact I.
      + iIntros "_".
        iApply pico_core_typed_pure_varass_fundamentalI.
        * econstructor; eauto.
        * exact I.
      + iIntros "_".
        iApply pico_core_typed_pure_varass_fundamentalI.
        * econstructor; eauto.
        * exact I.
      + iIntros "#Hprimitives".
        iDestruct "Hprimitives" as "[#Hread _]".
        iApply ("Hread" $! sΓ mt x receiver field).
        iPureIntro.
        econstructor; eauto.
    - iIntros "#Hprimitives".
      iDestruct "Hprimitives" as "[_ [#Hwrite _]]".
      iApply ("Hwrite" $! sΓ sΓ AbstractImm x f y).
      iPureIntro.
      econstructor; eauto.
    - iIntros "#Hprimitives".
      iDestruct "Hprimitives" as "[_ [#Hwrite _]]".
      iApply ("Hwrite" $! sΓ sΓ ConcreteState x f y).
      iPureIntro.
      econstructor; eauto.
    - iIntros "#Hprimitives".
      iDestruct "Hprimitives" as "[_ [#Hwrite _]]".
      iApply ("Hwrite" $! sΓ sΓ SafeRO x f y).
      iPureIntro.
      econstructor; eauto.
    - iIntros "#Hprimitives".
      iDestruct "Hprimitives" as "[_ [#Hwrite _]]".
      iApply ("Hwrite" $! sΓ sΓ ConcreteImm x f y).
      iPureIntro.
      econstructor; eauto.
    - iIntros "#Hprimitives".
      iDestruct "Hprimitives" as "[_ [_ [#Hnew _]]]".
      iApply ("Hnew" $! sΓ sΓ mt x qc C args).
      iPureIntro.
      econstructor; eauto.
    - iIntros "#Hprimitives".
      iDestruct "Hprimitives" as "[_ [_ [_ [#Hcall _]]]]".
      iApply ("Hcall" $! sΓ sΓ mt x y m args).
      iPureIntro.
      eapply ST_Call; eauto.
    - iIntros "#Hprimitives".
      iDestruct "Hprimitives" as "[_ [_ [_ [#Hcall _]]]]".
      iApply ("Hcall" $! sΓ sΓ mt x y m args).
      iPureIntro.
      eapply ST_Call_safe_ro; eauto.
    - iIntros "#Hprimitives".
      iApply pico_core_typed_seq_compositionI.
      + iApply (IHHtyping1 eq_refl).
        iExact "Hprimitives".
      + iApply (IHHtyping2 eq_refl).
        iExact "Hprimitives".
    - iIntros "#Hprimitives".
      iDestruct "Hprimitives" as "[_ [_ [_ [_ #Hifzero]]]]".
      iApply ("Hifzero" $! sΓ sΓ' mt x s_zero s_nonzero).
      iPureIntro.
      econstructor; eauto.
  Qed.
End pico_typing_fundamental_ownp.
