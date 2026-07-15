From Stdlib Require Import List.
From Stdlib Require String.
Import ListNotations.

Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation Properties Reachability Preservation ConcreteState.

Definition LocSet      : Type := Ensembles.Ensemble Loc.

Lemma shallow_immutability_pico_with_end :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ' l C vals vals' f
    (Hloc       : l < dom h)
    (Hobj_start : runtime_getObj h l = Some (mkObj (mkruntime_type Imm_r C) vals))
    (Hwf        : wf_r_config CT sΓ rΓ h)
    (Htyping    : stmt_typing CT sΓ mt stmt sΓ')
    (Heval      : eval_stmt OK CT rΓ h stmt OK rΓ' h')
    (Hobj_end   : runtime_getObj h' l = Some (mkObj (mkruntime_type Imm_r C) vals'))
    (Hfield_imm : sf_assignability_rel CT C f Final \/
                  sf_assignability_rel CT C f RDA \/
                  concrete_assignability_method_type mt),
    nth_error vals f = nth_error vals' f.
Proof.
  intros CT sΓ mt rΓ h stmt rΓ' h' sΓ' l C vals vals' f
    Hloc Hobj_start Hwf Htyping Heval Hobj_end Hfield_imm.
  remember OK as ok.
  generalize dependent sΓ.
  generalize dependent sΓ'.
  generalize dependent mt.
  generalize dependent vals. generalize dependent vals'.
  induction Heval; try discriminate.
  - (* Skip *)
   intros.
   match goal with
   | Htyping : stmt_typing _ _ _ SSkip _ |- _ => inversion Htyping; subst
   end.
   match goal with
   | Hobj_start : runtime_getObj h l = Some (mkObj (mkruntime_type Imm_r C) vals),
     Hobj_end : runtime_getObj h l = Some (mkObj (mkruntime_type Imm_r C) vals') |- _ =>
       rewrite Hobj_start in Hobj_end; injection Hobj_end as H_eq
   end.
   rewrite H_eq.
   reflexivity.
  - (* Local *)
  intros.
  match goal with
  | Htyping : stmt_typing _ _ _ (SLocal _ _) _ |- _ => inversion Htyping; subst
  end.
  match goal with
  | Hobj_start : runtime_getObj h l = Some (mkObj (mkruntime_type Imm_r C) vals),
    Hobj_end : runtime_getObj h l = Some (mkObj (mkruntime_type Imm_r C) vals') |- _ =>
      rewrite Hobj_start in Hobj_end; injection Hobj_end as H_eq
  end.
  rewrite H_eq.
  reflexivity.
  - (* VarAss *)
  intros.
  match goal with
  | Htyping : stmt_typing _ _ _ (SVarAss _ _) _ |- _ => inversion Htyping; subst
  end.
  match goal with
  | Hobj_start : runtime_getObj h l = Some (mkObj (mkruntime_type Imm_r C) vals),
    Hobj_end : runtime_getObj h l = Some (mkObj (mkruntime_type Imm_r C) vals') |- _ =>
      rewrite Hobj_start in Hobj_end; injection Hobj_end as H_eq
  end.
  rewrite H_eq.
  reflexivity.
  - (* FldWrite *)
  {
    intros.
    destruct (Nat.eq_dec l loc_x) as [Heq_l | Hneq_l].
    - (* Case: l = lx (same object being written to) *)
      subst l.
      (* Extract the object type from H0 and H6 *)
      rewrite Hobj_start in Hobj.
      injection Hobj as H1_eq.
      subst o.
      (* Now we have an immutable object, but can_assign returned true *)
      (* This should be impossible for Final/RDA fields on immutable objects *)
      destruct (Nat.eq_dec f f0) as [Heq_f | Hneq_f].
      + (* Case: f = f0 (same field being written) *)
        subst f.
        exfalso.
        simpl in Hruntime_assignable.
        destruct Hfield_imm as [Hffinal | [HfRDA | Hcs]].
        * assert (Heq : Final = a) by (eapply sf_assignability_deterministic_rel; eauto).
          rewrite <- Heq in Hruntime_assignable.
          discriminate.
        * assert (Heq : RDA = a) by (eapply sf_assignability_deterministic_rel; eauto).
          rewrite <- Heq in Hruntime_assignable.
          discriminate.
        * destruct Hcs as [Hcs | Hts]; subst mt.
          eapply concrete_state_write_cannot_target_immutable; eauto.
          eapply concrete_immutability_write_cannot_target_immutable; eauto.
        +
        assert (Hvals_eq : vals' = [f0 ↦ val_y] (vals)).
        {
          (* Use the definition of update_field and the fact that h' contains the updated object *)
          unfold update_field in Hupdate.
          rewrite Hobj_start in Hupdate.
          rewrite Hupdate in Hobj_end.
          unfold runtime_getObj in Hobj_end.
          (* Apply update_same to get the updated object *)
          assert (Hget_same : nth_error (update loc_x {| rt_type := {| rqtype := Imm_r; rctype := C |}; fields_map := [f0 ↦ val_y] (vals) |} h) loc_x =
                              Some {| rt_type := {| rqtype := Imm_r; rctype := C |}; fields_map := [f0 ↦ val_y] (vals) |}).
          {
            apply update_same.
            exact Hloc.
          }
          rewrite Hget_same in Hobj_end.
          injection Hobj_end as H6_eq.
          symmetry. exact H6_eq.
        }
        rewrite Hvals_eq.
        unfold getVal.
        rewrite update_diff.
        symmetry. exact Hneq_f.
        reflexivity.
    -
    assert (Hl_unchanged : runtime_getObj h' l = runtime_getObj h l).
    {
      unfold update_field in Hupdate.
      rewrite Hobj in Hupdate.
      rewrite Hupdate.
      unfold runtime_getObj.
      apply update_diff.
      easy.
    }
    rewrite Hobj_start in Hl_unchanged.
    rewrite Hl_unchanged in Hobj_end.
    injection Hobj_end as H6_eq.
    rewrite <- H6_eq.
    reflexivity.
  }
  - (* New *) (* h' = h ++ [new_obj], so l < dom h means same object *)
  intros.
  inversion Htyping; subst.
  (* Since l < dom h, the object at location l is unchanged *)
  unfold runtime_getObj in Hobj_end.
  rewrite List.nth_error_app1 in Hobj_end; auto.
  unfold runtime_getObj in Hobj_start.
  rewrite Hobj_start in Hobj_end.
  injection Hobj_end; intros; subst.
  reflexivity.
  - (* Call *) (* Similar to other non-mutating cases *)
  intros.
  inversion Htyping.
  --
  revert Hget_y.
  subst.
  intro Hget_y.
  destruct Hfind as [mdeflookup getmbody].
  remember (msignature mdef) as msig.
  have mdeflookupcopy := mdeflookup.
  apply method_body_well_typed_by_find in mdeflookup; auto.
  destruct mdeflookup as [sΓmethodend Htyping_method].
  remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit.
  assert (Hsigeq_scope : msignature mdef = msignature mdef0).
  { eapply runtime_and_static_method_signatures_agree; eauto. }
  assert (Hfield_callee : sf_assignability_rel CT C f Final \/
                          sf_assignability_rel CT C f RDA \/
                          concrete_assignability_method_type (mtype (msignature mdef))).
  {
    destruct Hfield_imm as [Hfinal | [Hrda | Hconcrete]].
    - left; exact Hfinal.
    - right; left; exact Hrda.
    - right; right.
      destruct Hscope as [Habs | [Hcs Hsub]].
      + subst mt. destruct Hconcrete as [Hbad | Hbad]; discriminate.
      + subst mt. rewrite Hsigeq_scope. eapply concrete_assignability_submethod; eauto.
  }
  apply IHHeval with (mt:=(mtype (msignature mdef)))(sΓ' := sΓmethodend)(sΓ := sΓmethodinit). 1-5: auto.
  remember {| vars := Iot ly :: vals |} as rΓmethodinit.
  destruct (r_muttype h ly) eqn: Hinnerthis.
  2:{
    unfold r_muttype in Hinnerthis.
    unfold r_basetype in Hbase.
    destruct (runtime_getObj h ly).
    discriminate Hinnerthis.
    discriminate Hbase.
  }
  assert (Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
  {
    rewrite HeqsΓmethodinit.
    rewrite HeqrΓmethodinit.
    eapply callee_frame_wf_abs; eauto.
    all: rewrite Hsigeq_scope; eauto.
  }
    exact Hwf_method_frame.
    rewrite getmbody.
    exact Htyping_method.
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hwf_classtable _].
    exact Hwf_classtable.
    unfold r_basetype in Hbase.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
    injection Hbase as H0_eq.
    subst cy.
    destruct obj as [rt_obj fields_obj].
    destruct rt_obj as [rq_obj rc_obj].
    simpl.
    destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    unfold wf_heap in Hheap.
    assert (Hly_dom : ly < dom h) by (apply runtime_getObj_dom in Hobjy; exact Hobjy).
    specialize (Hheap ly Hly_dom).
    unfold wf_obj in Hheap.
    rewrite Hobjy in Hheap.
    destruct Hheap as [Hwf_rtypeuse _].
    unfold wf_rtypeuse in Hwf_rtypeuse.
    simpl in Hwf_rtypeuse.
    destruct (bound CT rc_obj) as [class_def|] eqn:Hbound.
    destruct Hwf_rtypeuse as [Hwf_rtypeuse _].
    exact Hwf_rtypeuse.
    contradiction.
    --
    revert Hget_y.
  subst.
  intro Hget_y.
  destruct Hfind as [mdeflookup getmbody].
  remember (msignature mdef) as msig.
  have mdeflookupcopy := mdeflookup.
  apply method_body_well_typed_by_find in mdeflookup; auto.
  destruct mdeflookup as [sΓmethodend Htyping_method].
  remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit.
  assert (Hsigeq_scope : msignature mdef = msignature mdef0).
  { eapply runtime_and_static_method_signatures_agree; eauto. }
  assert (Hfield_callee : sf_assignability_rel CT C f Final \/
                          sf_assignability_rel CT C f RDA \/
                          concrete_assignability_method_type (mtype (msignature mdef))).
  {
    destruct Hfield_imm as [Hfinal | [Hrda | Hconcrete]].
    - left; exact Hfinal.
    - right; left; exact Hrda.
    - right; right. rewrite Hsigeq_scope.
      eapply concrete_assignability_submethod; eauto.
  }
  apply IHHeval with (mt:=(mtype (msignature mdef)))(sΓ' := sΓmethodend)(sΓ := sΓmethodinit). 1-5: auto.
  remember {| vars := Iot ly :: vals |} as rΓmethodinit.
  destruct (r_muttype h ly) eqn: Hinnerthis.
  2:{
    unfold r_muttype in Hinnerthis.
    unfold r_basetype in Hbase.
    destruct (runtime_getObj h ly).
    discriminate Hinnerthis.
    discriminate Hbase.
  }
  assert (Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
  {
    rewrite HeqsΓmethodinit.
    rewrite HeqrΓmethodinit.
    eapply callee_frame_wf_rs_ts; eauto.
    all: rewrite Hsigeq_scope; eauto.
  }
    exact Hwf_method_frame.
    rewrite getmbody.
    exact Htyping_method.
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hwf_classtable _].
    exact Hwf_classtable.
    unfold r_basetype in Hbase.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
    injection Hbase as H0_eq.
    subst cy.
    destruct obj as [rt_obj fields_obj].
    destruct rt_obj as [rq_obj rc_obj].
    simpl.
    destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    unfold wf_heap in Hheap.
    assert (Hly_dom : ly < dom h) by (apply runtime_getObj_dom in Hobjy; exact Hobjy).
    specialize (Hheap ly Hly_dom).
    unfold wf_obj in Hheap.
    rewrite Hobjy in Hheap.
    destruct Hheap as [Hwf_rtypeuse _].
    unfold wf_rtypeuse in Hwf_rtypeuse.
    simpl in Hwf_rtypeuse.
    destruct (bound CT rc_obj) as [class_def|] eqn:Hbound.
    destruct Hwf_rtypeuse as [Hwf_rtypeuse _].
    exact Hwf_rtypeuse.
    contradiction.
  -  (* Seq *) (* Apply IH transitively *)
  intros. inversion Htyping; subst.
  specialize (eval_stmt_preserves_heap_domain_simple CT rΓ h s1 rΓ' h' Heval1) as Hh'.
  assert (Hloc_h' : l < dom h') by lia.
  specialize (runtime_getObj_Some h' l Hloc_h') as [C' [values' Hh'some]].
  specialize (runtime_preserves_r_type_heap CT rΓ h l ({| rqtype := Imm_r; rctype := C |})
  h' vals s1 rΓ' Hobj_start Heval1) as [vals1 Hrtype].
  rewrite Hrtype in Hh'some; inversion Hh'some; subst.
  specialize (IHHeval1 Hloc Heqok values' Hrtype vals Hobj_start mt Hfield_imm sΓ'0 sΓ Hwf Htype1).
  specialize (preservation_pico CT sΓ mt rΓ h s1 rΓ' h' sΓ'0 Hwf Htype1 Heval1) as Hwf'.
  specialize (IHHeval2 Hloc_h' Heqok vals' Hobj_end values' Hrtype mt Hfield_imm sΓ' sΓ'0 Hwf' Htype2).
  rewrite IHHeval2 in IHHeval1; auto.
Qed.

(** Public shallow-immutability statement.  Evaluation preserves the runtime
    type and existence of every pre-existing object, so callers need not
    provide the final object as a separate premise. *)
Theorem shallow_immutability_pico :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ' l C vals f
    (Hloc       : l < dom h)
    (Hobj_start : runtime_getObj h l = Some (mkObj (mkruntime_type Imm_r C) vals))
    (Hwf        : wf_r_config CT sΓ rΓ h)
    (Htyping    : stmt_typing CT sΓ mt stmt sΓ')
    (Heval      : eval_stmt OK CT rΓ h stmt OK rΓ' h')
    (Hfield_imm : sf_assignability_rel CT C f Final \/
                  sf_assignability_rel CT C f RDA \/
                  concrete_assignability_method_type mt),
    exists vals',
      runtime_getObj h' l = Some (mkObj (mkruntime_type Imm_r C) vals') /\
      nth_error vals f = nth_error vals' f.
Proof.
  intros CT sΓ mt rΓ h stmt rΓ' h' sΓ' l C vals f
    Hloc Hobj_start Hwf Htyping Heval Hfield_imm.
  destruct (runtime_preserves_r_type_heap CT rΓ h l
    (mkruntime_type Imm_r C) h' vals stmt rΓ' Hobj_start Heval)
    as [vals' Hobj_end].
  exists vals'. split; [exact Hobj_end|].
  eapply shallow_immutability_pico_with_end; eauto.
Qed.

Lemma imm_step_preserves_imm :
  forall CT sΓ rΓ h l0 C vals l1 k
    (Hwf   : wf_r_config CT sΓ rΓ h)
    (HgetObj  : runtime_getObj h l0 = Some (mkObj (mkruntime_type Imm_r C) vals))
    (Hl1dom  : l1 < dom h)
    (Hnth  : nth_error vals k = Some (Iot l1))
    (HFieldmut  : sf_mutability_rel CT C k RDM_f \/ sf_mutability_rel CT C k Imm_f),
    exists C' vals',
      runtime_getObj h l1 =
        Some (mkObj (mkruntime_type Imm_r C') vals').
Proof.
  intros.
  unfold wf_r_config in Hwf.
  destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen _]]]]].
  unfold wf_heap in Hheap.
  have HgetObjCopy := HgetObj.
  apply runtime_getObj_dom in HgetObjCopy.
  specialize (Hheap l0 HgetObjCopy).
  unfold wf_obj in Hheap.
  rewrite HgetObj in Hheap.
  destruct Hheap as [_ [field_defs [Hfields [Hdom_fields Hforall2]]]].
  assert (Hfield_k : exists fdef : field_def, nth_error field_defs k = Some fdef).
  {
    simpl in Hdom_fields.
    assert (Hk_dom : k < dom vals) by (apply nth_error_Some; rewrite Hnth; discriminate).
    rewrite Hdom_fields in Hk_dom.
    apply nth_error_Some_exists in Hk_dom.
    destruct Hk_dom as [fdef Hfdef].
    exists fdef. exact Hfdef.
  }
  destruct Hfield_k as [fdef Hfdef].
  eapply Forall2_nth_error_prop in Hforall2; eauto.
  simpl in Hforall2.
  destruct (runtime_getObj h l1) eqn:HgetObj_l1; try (exfalso; lia).
  destruct Hforall2 as [rqt [Hrtype [_ Hqual]]].
  destruct HFieldmut as [Hrdm | Himm].
  - (* RDM case *)
    simpl in Hfields.
    unfold sf_mutability_rel in Hrdm.
    destruct Hrdm as [fdef1 [HFieldLookup HFieldMut]].
    assert (fdef1 = fdef).
    {
      clear - HFieldLookup Hfdef Hfields.
      inversion HFieldLookup; subst.
      assert (fields = field_defs) by (eapply collect_fields_deterministic_rel; eauto); subst.
      unfold gget in Hget.
      rewrite Hfdef in Hget.
      inversion Hget; reflexivity.
    }
    subst fdef1.
    rewrite HFieldMut in Hqual.
    unfold qualifier_typable_heap in Hqual.
    destruct (rqtype rqt) eqn:Hrqt; try easy.
    assert (o.(rt_type) = rqt).
    {
      unfold r_type in Hrtype.
      rewrite HgetObj_l1 in Hrtype.
      inversion Hrtype; reflexivity.
    }
    subst rqt.
    destruct o as [rqt vals'].
    exists (rctype rqt), vals'.
    f_equal.
    destruct rqt.
    simpl in Hrqt.
    rewrite Hrqt.
    reflexivity.
  - (* Imm case *)
    simpl in Hfields.
    unfold sf_mutability_rel in Himm.
    destruct Himm as [fdef1 [HFieldLookup HFieldMut]].
    assert (fdef1 = fdef).
    {
      clear - HFieldLookup Hfdef Hfields.
      inversion HFieldLookup; subst.
      assert (fields = field_defs) by (eapply collect_fields_deterministic_rel; eauto); subst.
      unfold gget in Hget.
      rewrite Hfdef in Hget.
      inversion Hget; reflexivity.
    }
    subst fdef1.
    rewrite HFieldMut in Hqual.
    unfold qualifier_typable_heap in Hqual.
    destruct (rqtype rqt) eqn:Hrqt; try easy.
    assert (o.(rt_type) = rqt).
    {
      unfold r_type in Hrtype.
      rewrite HgetObj_l1 in Hrtype.
      inversion Hrtype; reflexivity.
    }
    subst rqt.
    destruct o as [rqt vals'].
    exists (rctype rqt), vals'.
    f_equal.
    destruct rqt.
    simpl in Hrqt.
    rewrite Hrqt.
    reflexivity.
Qed.

Lemma reachable_abs_from_imm_points_to_imm :
  forall CT sΓ rΓ h l0 C0 vals0 l1
    (Hwf   : wf_r_config CT sΓ rΓ h)
    (Himm  : runtime_getObj h l0 = Some (mkObj (mkruntime_type Imm_r C0) vals0))
    (Hrch  : reachable_abs CT h l0 l1),
    exists C' vals',
      runtime_getObj h l1 =
        Some (mkObj (mkruntime_type Imm_r C') vals').
Proof.
  intros.
  remember l0 as l_root eqn:Heq.
  revert l0 C0 vals0 Himm Heq.
  induction Hrch as
    [l Hdom
    |l0 l1 f any C vals k Hdom1 Hget Hf
    |l0 l1 l2 Hr01 IH01 Hr12 IH12
    ]; intros l_root C_root vals_root Himm' Heq'; subst.

  - (* reachable_abs_heap: l1 = l_root *)
    exists C_root, vals_root. assumption.

  - (* reachable_abs_step: l0 -> l1 by RDM/Imm field *)
    (* Key: show l1 is Imm_r using a step lemma *)
    eapply imm_step_preserves_imm; eauto.

  - (* reachable_abs_trans: l0 -> l1 -> l2 *)
    (* First, l1 is Imm_r by IH01 *)
    destruct (IH01 l_root C_root vals_root Himm' eq_refl) as [C1 [vals1 Himm1]].
    (* Now l1 is immutable: runtime_getObj h l1 = Some (mkObj (mkruntime_type Imm_r C1) vals1) *)
    destruct (IH12 l1 C1 vals1 Himm1 eq_refl) as [C2 [vals2 Himm2]].
    (* Now l2 is immutable *)
    exists C2, vals2.
    exact Himm2.
Qed.

(* All reachable objects in the abstract state from immutable root object are immutable *)
Lemma protected_locset_all_imm :
  forall CT sΓ rΓ h root C0 vals0 l
         (Hwf : wf_r_config CT sΓ rΓ h)
         (Himm : runtime_getObj h root = Some (mkObj (mkruntime_type Imm_r C0) vals0))
         (Hin : protected_locset CT h root l),
    exists C' vals',
      runtime_getObj h l = Some (mkObj (mkruntime_type Imm_r C') vals').
Proof.
  intros.
  unfold protected_locset in Hin.
  eapply reachable_abs_from_imm_points_to_imm; eauto.
Qed.

Lemma deep_immutability_pico_with_end :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ' root C0 vals0 l C qr vals vals' f
    (Hdom : root < dom h)
    (Himm_root : runtime_getObj h root = Some (mkObj (mkruntime_type Imm_r C0) vals0))
    (Hreach : reachable_abs CT h root l)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Heval : eval_stmt OK CT rΓ h stmt OK rΓ' h')
    (Hobj : runtime_getObj h l = Some (mkObj (mkruntime_type qr C) vals))
    (Hobj' : runtime_getObj h' l = Some (mkObj (mkruntime_type qr C) vals'))
    (Hprotected : sf_assignability_rel CT C f Final \/
                  sf_assignability_rel CT C f RDA),
    nth_error vals f = nth_error vals' f.
Proof.
  intros.
  eapply protected_locset_all_imm in Hreach; eauto.
  destruct Hreach as [C' [vals'' Himm_l]].
  rewrite Himm_l in Hobj.
  injection Hobj; intros; subst.
  eapply shallow_immutability_pico_with_end with (l := l); eauto.
  apply runtime_getObj_dom in Himm_l. exact Himm_l.
  destruct Hprotected as [Hfinal | Hrda].
  - left; exact Hfinal.
  - right; left; exact Hrda.
Qed.

(** Public transitive abstract-immutability statement with the final object
    derived from evaluation. *)
Theorem deep_immutability_pico :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ' root C0 vals0 l C qr vals f
    (Hdom : root < dom h)
    (Himm_root : runtime_getObj h root = Some (mkObj (mkruntime_type Imm_r C0) vals0))
    (Hreach : reachable_abs CT h root l)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Heval : eval_stmt OK CT rΓ h stmt OK rΓ' h')
    (Hobj : runtime_getObj h l = Some (mkObj (mkruntime_type qr C) vals))
    (Hprotected : sf_assignability_rel CT C f Final \/
                  sf_assignability_rel CT C f RDA),
    exists vals',
      runtime_getObj h' l = Some (mkObj (mkruntime_type qr C) vals') /\
      nth_error vals f = nth_error vals' f.
Proof.
  intros CT sΓ mt rΓ h stmt rΓ' h' sΓ' root C0 vals0 l C qr vals f
    Hdom Himm_root Hreach Hwf Htyping Heval Hobj Hprotected.
  destruct (runtime_preserves_r_type_heap CT rΓ h l
    (mkruntime_type qr C) h' vals stmt rΓ' Hobj Heval)
    as [vals' Hobj'].
  exists vals'. split; [exact Hobj'|].
  eapply deep_immutability_pico_with_end; eauto.
Qed.
