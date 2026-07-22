Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation.
Require Import Properties AbstractStatePreservation Reachability Preservation ReadonlyHelper ReadonlyNoMutation PotentialCapability.
From Stdlib Require Import List.
From Stdlib Require String.
Import ListNotations.

Lemma readonly_field_write_preservation_with_end :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ' l C vals vals' f qt readonlyx anyf rhs anyrq
    (Hstmt : stmt = (SFldWrite readonlyx anyf rhs))
    (Hstatic_type : static_getType sΓ readonlyx = Some qt)
    (Hqt_ro : sqtype qt = RO)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Hreadonly_scope : readonly_state_method_scope mt)
    (Heval : eval_stmt CT rΓ h stmt OK rΓ' h')
    (Hget_readonly : runtime_getVal rΓ readonlyx = Some (Iot l))
    (Hobj_before : runtime_getObj h l = Some (mkObj (mkruntime_type anyrq C) vals))
    (Hobj_after : runtime_getObj h' l = Some (mkObj (mkruntime_type anyrq C) vals'))
    (Hassign : sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA),
    nth_error vals f = nth_error vals' f.
Proof.
  intros.
  (* Subst the statement form *)
  subst stmt.

  (* Invert the evaluation to get heap update details *)
  inversion Heval; subst.

  (* Invert typing to get field write constraints *)
  inversion Htyping; subst.
  - destruct Hreadonly_scope; discriminate.
  - destruct Hreadonly_scope; discriminate.
  -
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hclasstable [_ [Hrenv [_ [_ Htypable]]]]].
    assert (Hreadonly_dom : readonlyx < dom sΓ').
    {
      apply static_getType_dom in Hstatic_type.
      exact Hstatic_type.
    }
    rewrite Hget_readonly in Hval_x.
    inversion Hval_x.
    subst l.
    unfold wf_renv in Hrenv.
    destruct Hrenv as [_ [Hreceiver _]].
    destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
    assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
    {
      eapply receiver_mutability_exists_from_bound; eauto.
    }
    destruct HOutterReceiverMutability as [qcontext Hqcontext].
    (* Apply correspondence to get wf_r_typable *)
    specialize (Htypable iot qcontext Hget_iot Hqcontext readonlyx Hreadonly_dom qt Hstatic_type).
    rewrite Hget_readonly in Htypable.
    unfold wf_r_typable in Htypable.
    unfold r_type in Htypable.
    rewrite Hobj in Htypable.
    destruct Htypable as [base qualifier].
    rewrite Hobj in Hobj_before.
    injection Hobj_before as Hobject_eq.
    subst o.
    simpl in base.

    (* Use the fact that Final/RDA fields are protected from modification *)
    destruct Hassign as [Hfinal | Hrda].
    --
      rewrite Hstatic_type in Hget_x.
      inversion Hget_x.
      subst Tx.
      unfold vpa_assignability in Hassignable.
      destruct a0 eqn: Haeqn; try easy.
      assert (Hneq: anyf <> f).
      {
        intro Heq.
        subst anyf.
        assert (Heq_assign : Final = Assignable).
        {
          eapply sf_assignability_consistent_subtype; [exact Hclasstable | exact base | exact Hfinal | exact Hassign_rel].
        }
        discriminate.
      }
      unfold update_field in Hobj_after.
      rewrite Hobj in Hobj_after.
      simpl in Hobj_after.
      unfold update_field in Hobj_after.
      simpl in Hobj_after.
      assert (Hdom: loc_x < dom h).
      {
        apply runtime_getObj_dom in Hobj.
        exact Hobj.
      }
      rewrite runtime_getObj_update_same in Hobj_after; auto.
      inversion Hobj_after; subst.
      simpl.
      symmetry.
      apply update_diff.
      exact Hneq.
      unfold vpa_assignability in Hassignable.
      rewrite Hqt_ro in Hassignable; easy.
      rewrite Hqt_ro in Hassignable; easy.
    -- (* RDA case: RDA fields cannot be written *)
      rewrite Hstatic_type in Hget_x.
      inversion Hget_x.
      subst Tx.
      unfold vpa_assignability in Hassignable.
      destruct a0 eqn: Haeqn; try easy.
      assert (Hneq: anyf <> f).
      {
        intro Heq.
        subst anyf.
        assert (Heq_assign : RDA = Assignable).
        {
          eapply sf_assignability_consistent_subtype; [exact Hclasstable | exact base | exact Hrda | exact Hassign_rel].
        }
        discriminate.
      }
      unfold update_field in Hobj_after.
      rewrite Hobj in Hobj_after.
      simpl in Hobj_after.
      unfold update_field in Hobj_after.
      simpl in Hobj_after.
      assert (Hdom: loc_x < dom h).
      {
        apply runtime_getObj_dom in Hobj.
        exact Hobj.
      }
      rewrite runtime_getObj_update_same in Hobj_after; auto.
      inversion Hobj_after; subst.
      simpl.
      symmetry.
      apply update_diff.
      exact Hneq.
      rewrite Hqt_ro in Hassignable; easy.
      rewrite Hqt_ro in Hassignable; easy.
  -
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hclasstable [_ [Hrenv [_ [_ Htypable]]]]].
    assert (Hreadonly_dom : readonlyx < dom sΓ').
    {
      apply static_getType_dom in Hstatic_type.
      exact Hstatic_type.
    }
    rewrite Hget_readonly in Hval_x.
    inversion Hval_x.
    subst l.
    unfold wf_renv in Hrenv.
    destruct Hrenv as [_ [Hreceiver _]].
    destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
    assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
    {
      eapply receiver_mutability_exists_from_bound; eauto.
    }
    destruct HOutterReceiverMutability as [qcontext Hqcontext].
    (* Apply correspondence to get wf_r_typable *)
    specialize (Htypable iot qcontext Hget_iot Hqcontext readonlyx Hreadonly_dom qt Hstatic_type).
    rewrite Hget_readonly in Htypable.
    unfold wf_r_typable in Htypable.
    unfold r_type in Htypable.
    rewrite Hobj in Htypable.
    destruct Htypable as [base qualifier].
    rewrite Hobj in Hobj_before.
    injection Hobj_before as Hobject_eq.
    subst o.
    simpl in base.

    (* Use the fact that Final/RDA fields are protected from modification *)
    destruct Hassign as [Hfinal | Hrda].
    --
      rewrite Hstatic_type in Hget_x.
      inversion Hget_x.
      subst Tx.
      unfold vpa_assignability in Hassignable.
      destruct a0 eqn: Haeqn; try easy.
      assert (Hneq: anyf <> f).
      {
        intro Heq.
        subst anyf.
        assert (Heq_assign : Final = Assignable).
        {
          eapply sf_assignability_consistent_subtype; [exact Hclasstable | exact base | exact Hfinal | exact Hassign_rel].
        }
        discriminate.
      }
      unfold update_field in Hobj_after.
      rewrite Hobj in Hobj_after.
      simpl in Hobj_after.
      unfold update_field in Hobj_after.
      simpl in Hobj_after.
      assert (Hdom: loc_x < dom h).
      {
        apply runtime_getObj_dom in Hobj.
        exact Hobj.
      }
      rewrite runtime_getObj_update_same in Hobj_after; auto.
      inversion Hobj_after; subst.
      simpl.
      symmetry.
      apply update_diff.
      exact Hneq.
      unfold vpa_assignability in Hassignable.
      rewrite Hqt_ro in Hassignable; easy.
      rewrite Hqt_ro in Hassignable; easy.
    -- (* RDA case: RDA fields cannot be written *)
      rewrite Hstatic_type in Hget_x.
      inversion Hget_x.
      subst Tx.
      unfold vpa_assignability in Hassignable.
      destruct a0 eqn: Haeqn; try easy.
      assert (Hneq: anyf <> f).
      {
        intro Heq.
        subst anyf.
        assert (Heq_assign : RDA = Assignable).
        {
          eapply sf_assignability_consistent_subtype; [exact Hclasstable | exact base | exact Hrda | exact Hassign_rel].
        }
        discriminate.
      }
      unfold update_field in Hobj_after.
      rewrite Hobj in Hobj_after.
      simpl in Hobj_after.
      unfold update_field in Hobj_after.
      simpl in Hobj_after.
      assert (Hdom: loc_x < dom h).
      {
        apply runtime_getObj_dom in Hobj.
        exact Hobj.
      }
      rewrite runtime_getObj_update_same in Hobj_after; auto.
      inversion Hobj_after; subst.
      simpl.
      symmetry.
      apply update_diff.
      exact Hneq.
      rewrite Hqt_ro in Hassignable; easy.
      rewrite Hqt_ro in Hassignable; easy.
Qed.

(* Paper-facing form: evaluation itself preserves the object's runtime type,
   so callers need not supply the final-heap object as a premise. *)
Theorem readonly_field_write_preservation :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ' l C vals f qt readonlyx anyf rhs anyrq
    (Hstmt : stmt = (SFldWrite readonlyx anyf rhs))
    (Hstatic_type : static_getType sΓ readonlyx = Some qt)
    (Hqt_ro : sqtype qt = RO)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Hreadonly_scope : readonly_state_method_scope mt)
    (Heval : eval_stmt CT rΓ h stmt OK rΓ' h')
    (Hget_readonly : runtime_getVal rΓ readonlyx = Some (Iot l))
    (Hobj_before : runtime_getObj h l = Some (mkObj (mkruntime_type anyrq C) vals))
    (Hassign : sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA),
    exists vals',
      runtime_getObj h' l = Some (mkObj (mkruntime_type anyrq C) vals') /\
      nth_error vals f = nth_error vals' f.
Proof.
  intros CT sΓ mt rΓ h stmt rΓ' h' sΓ' l C vals f
    qt readonlyx anyf rhs anyrq Hstmt Hstatic_type Hqt_ro Hwf Htyping
    Hreadonly_scope Heval Hget_readonly Hobj_before Hassign.
  destruct (runtime_preserves_r_type_heap CT rΓ h l
    (mkruntime_type anyrq C) h' vals stmt rΓ' Hobj_before Heval)
    as [vals' Hobj_after].
  exists vals'. split; [exact Hobj_after|].
  eapply readonly_field_write_preservation_with_end; eauto.
Qed.

(** The declared receiver and formal parameters provide no direct mutable
    authority. *)
Definition signature_has_no_mutable_roots (msig : method_sig) : Prop :=
  is_nonmutable_qualifier (sqtype (mreceiver msig)) /\
  Forall (fun T => is_nonmutable_qualifier (sqtype T)) (mparams msig).

Lemma callee_frame_respects_protected_set :
  forall CT h ly vals msig
    (Hwf : wf_r_config CT
      (mreceiver msig :: mparams msig) (mkr_env (Iot ly :: vals)) h)
    (Hsafe : signature_has_no_mutable_roots msig),
    env_respects_protected_set
      (reachable_locations_from_initial_env h (mkr_env (Iot ly :: vals)))
      (mreceiver msig :: mparams msig) (mkr_env (Iot ly :: vals)).
Proof.
  intros CT h ly vals msig Hwf [Hreceiver_safe Hparams_safe].
  eapply confinement_from_all_readonly_env; eauto.
  intros index T Hlookup.
  unfold static_getType in Hlookup.
  destruct index as [|index].
  - simpl in Hlookup. injection Hlookup as <-. exact Hreceiver_safe.
  - simpl in Hlookup.
    eapply Forall_nth_error in Hparams_safe; eauto.
Qed.

Definition reachable_locations_from_vals
  (h : heap) (vals : list value) : Ensembles.Ensemble Loc :=
  fun l_target =>
    exists l_root,
      In (Iot l_root) vals /\
      reachable h l_root l_target.

Lemma reachable_locations_subset_reachable_from_method_frame :
  forall h ly vals,
    let rΓmethodinit := {| vars := Iot ly :: vals |} in
    Ensembles.Included Loc
      (reachable_locations_from_vals h (Iot ly :: vals))
      (reachable_locations_from_initial_env h rΓmethodinit).
Proof.
  intros h ly vals rΓmethodinit l Hin.
  unfold reachable_locations_from_vals in Hin.
  destruct Hin as [l_root [Hin_list Hreach]].
  unfold reachable_locations_from_initial_env.
  (* l_root is in (Iot ly :: vals), so either l_root = ly or l_root is in vals *)
  destruct Hin_list as [Heq | Hin_vals].
  - (* Case: Iot l_root = Iot ly *)
    inversion Heq; subst l_root.
    exists 0, ly.
    split.
    -- unfold runtime_getVal. simpl. reflexivity.
    -- exact Hreach.
  - (* Case: Iot l_root in vals *)
    (* Find which variable in vals contains this *)
    have Hin_runtime : exists idx, nth_error vals idx = Some (Iot l_root).
    {
      apply In_nth_error in Hin_vals.
      exact Hin_vals.
    }
    destruct Hin_runtime as [idx Hnth_vals].
    exists (S idx), l_root.
    split.
    -- unfold runtime_getVal. simpl. exact Hnth_vals.
    -- exact Hreach.
Qed.

(** A successful typed call exposes one well-formed, well-typed dynamic
    callee frame.  The dynamically selected signature agrees with the static
    signature, so signature-level safety transfers without repeating dynamic
    dispatch and inheritance reasoning in each state-preservation theorem. *)
Lemma successful_typed_safe_call_body :
  forall CT sΓ mt rΓ h x method y args sΓ' rΓfinal hfinal
         Ty static_mdef vals receiver,
    static_getType sΓ y = Some Ty ->
    FindMethodWithName CT (sctype Ty) method static_mdef ->
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ mt (SCall x method y args) sΓ' ->
    eval_stmt CT rΓ h (SCall x method y args) OK rΓfinal hfinal ->
    runtime_getVal rΓ y = Some (Iot receiver) ->
    runtime_lookup_list rΓ args = Some vals ->
    signature_has_no_mutable_roots (msignature static_mdef) ->
    readonly_state_method_scope mt ->
    exists runtime_mdef body_sΓ' body_rΓ',
      msignature runtime_mdef = msignature static_mdef /\
      stmt_typing CT
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mscope (msignature runtime_mdef))
        (mbody_stmt (mbody runtime_mdef)) body_sΓ' /\
      wf_r_config CT
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot receiver :: vals)) h /\
      eval_stmt CT (mkr_env (Iot receiver :: vals)) h
        (mbody_stmt (mbody runtime_mdef)) OK body_rΓ' hfinal /\
      signature_has_no_mutable_roots (msignature runtime_mdef) /\
      readonly_state_method_scope (mscope (msignature runtime_mdef)) /\
      method_scope_subtype (mscope (msignature runtime_mdef)) mt.
Proof.
  intros CT sΓ mt rΓ h x method y args sΓ' rΓfinal hfinal
    Ty static_mdef vals receiver Hstatic Hfind_static Hwf Htyping Heval
    Hreceiver Hargs Hsafe Hcaller_scope.
  inversion Heval; subst; try discriminate.
  have Hreceiver_eq : receiver = ly.
  { rewrite Hval_y in Hreceiver. injection Hreceiver as <-. reflexivity. }
  subst ly.
  have Hvals_eq : vals = vals0.
  { rewrite Hargs0 in Hargs. injection Hargs as ->. reflexivity. }
  subst vals0.
  destruct Hfind as [Hfind_runtime Hbody].
  subst mbody.
  have Hsignature : msignature mdef = msignature static_mdef.
  { eapply runtime_call_signature_agrees; eauto. }
  have Hruntime_scope :
    readonly_state_method_scope (mscope (msignature mdef)).
  { eapply safe_typed_call_target_method_safe; eauto. }
  have Hruntime_subscope : method_scope_subtype (mscope (msignature mdef)) mt.
  {
    have Htyping_copy := Htyping.
    inversion Htyping_copy; subst.
    - destruct Hcaller_scope as [Hrs | Hts]; subst mt;
        destruct Hscope as [Has | [Hcs _]]; discriminate.
    - assert (Ty0 = Ty) by congruence. subst Ty0.
      have Htyping_signature : msignature mdef = msignature mdef0.
      { eapply runtime_call_signature_agrees; eauto. }
      rewrite Htyping_signature. exact Hmt_sub.
  }
  destruct (typed_call_has_wf_callee_frame CT sΓ mt rΓ h x method y args
    sΓ' vals receiver cy mdef Hwf Htyping Hval_y Hbase Hfind_runtime Hargs0)
    as [body_sΓ' [Hbody_typed Hframe_wf]].
  exists mdef, body_sΓ', rΓ''.
  split; [exact Hsignature|].
  split; [exact Hbody_typed|].
  split; [exact Hframe_wf|].
  split; [exact Heval_body|].
  split.
  - rewrite Hsignature. exact Hsafe.
  - split; assumption.
Qed.

Lemma readonly_state_preservation_with_end :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ' x y mindex Ty mdef zs vals ly
         loc_arg C anyrq vals_arg vals_arg' f
    (Hstmt : stmt = (SCall x mindex y zs))
    (Hstatic_type : static_getType sΓ y = Some Ty)
    (Hmethod_lookup : FindMethodWithName CT (sctype Ty) mindex mdef)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Hreadonly_scope : readonly_state_method_scope mt)
    (Heval : eval_stmt CT rΓ h stmt OK rΓ' h')
    (Hget_y : runtime_getVal rΓ y = Some (Iot ly))
    (Hget_zs : runtime_lookup_list rΓ zs = Some vals)
    (HinP: Ensembles.In Loc (reachable_locations_from_vals h (Iot ly :: vals)) loc_arg)
    (Harg_obj : runtime_getObj h loc_arg = Some (mkObj (mkruntime_type anyrq C) vals_arg))
    (Harg_obj' : runtime_getObj h' loc_arg = Some (mkObj (mkruntime_type anyrq C) vals_arg'))
    (Hassign : sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA)
    (Hall_readonly : signature_has_no_mutable_roots (msignature mdef)),
    nth_error vals_arg f = nth_error vals_arg' f.
  Proof.
  intros CT sΓ mt rΓ h stmt rΓ' h' sΓ' x y mindex Ty mdef zs vals ly
    loc_arg C anyrq vals_arg vals_arg' f Hstmt Hstatic_type Hmethod_lookup
    Hwf Htyping Hreadonly_scope Heval Hget_y Hget_zs HinP Harg_obj
    Harg_obj' Hassign Hall_readonly.
  subst stmt.
  destruct (successful_typed_safe_call_body CT sΓ mt rΓ h x mindex y zs
    sΓ' rΓ' h' Ty mdef vals ly Hstatic_type Hmethod_lookup Hwf Htyping
    Heval Hget_y Hget_zs Hall_readonly Hreadonly_scope)
    as [runtime_mdef [body_sΓ' [body_rΓ'
      [Hsignature [Hbody_typed [Hframe_wf
        [Hbody_eval [Hbody_safe [Hbody_scope Hbody_subscope]]]]]]]]].
  eapply readonly_state_statement_preservation with
    (sΓ := mreceiver (msignature runtime_mdef) ::
      mparams (msignature runtime_mdef))
    (rΓ := mkr_env (Iot ly :: vals))
    (stmt := mbody_stmt (mbody runtime_mdef))
    (sΓ' := body_sΓ') (rΓ' := body_rΓ')
    (mt := mscope (msignature runtime_mdef)); eauto.
  - eapply callee_frame_respects_protected_set; eauto.
  - have Hsubset := reachable_locations_subset_reachable_from_method_frame
      h ly vals.
    exact (Hsubset loc_arg HinP).
Qed.

(** Public RS guarantee with final-object existence and runtime type derived
    from the successful call evaluation. *)
Theorem readonly_state_preservation :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ' x y mindex Ty mdef zs vals ly
         loc_arg C anyrq vals_arg f
    (Hstmt : stmt = (SCall x mindex y zs))
    (Hstatic_type : static_getType sΓ y = Some Ty)
    (Hmethod_lookup : FindMethodWithName CT (sctype Ty) mindex mdef)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Hreadonly_scope : readonly_state_method_scope mt)
    (Heval : eval_stmt CT rΓ h stmt OK rΓ' h')
    (Hget_y : runtime_getVal rΓ y = Some (Iot ly))
    (Hget_zs : runtime_lookup_list rΓ zs = Some vals)
    (HinP: Ensembles.In Loc (reachable_locations_from_vals h (Iot ly :: vals)) loc_arg)
    (Harg_obj : runtime_getObj h loc_arg = Some (mkObj (mkruntime_type anyrq C) vals_arg))
    (Hassign : sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA)
    (Hall_readonly : signature_has_no_mutable_roots (msignature mdef)),
    exists vals_arg',
      runtime_getObj h' loc_arg = Some (mkObj (mkruntime_type anyrq C) vals_arg') /\
      nth_error vals_arg f = nth_error vals_arg' f.
Proof.
  intros CT sΓ mt rΓ h stmt rΓ' h' sΓ' x y mindex Ty mdef zs vals ly
    loc_arg C anyrq vals_arg f Hstmt Hstatic_type Hmethod_lookup Hwf Htyping
    Hreadonly_scope Heval Hget_y Hget_zs HinP Harg_obj Hassign Hall_readonly.
  destruct (runtime_preserves_r_type_heap CT rΓ h loc_arg
    (mkruntime_type anyrq C) h' vals_arg stmt rΓ' Harg_obj Heval)
    as [vals_arg' Harg_obj'].
  exists vals_arg'. split; [exact Harg_obj'|].
  eapply readonly_state_preservation_with_end; eauto.
Qed.
