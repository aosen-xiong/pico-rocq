Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation.
Require Import List.
Import ListNotations.
Require Import String.
From RecordUpdate Require Import RecordUpdate.

Lemma collect_methods_exists : forall CT C,
  wf_class_table CT ->
  C < dom CT ->
  exists methods, CollectMethods CT C methods.
Proof.
  intros CT C Hwf_ct Hdom.
  induction C as [C IH] using lt_wf_ind.
  assert (Hexists_class : exists class_def, find_class CT C = Some class_def).
  {
    apply find_class_Some.
    exact Hdom.
  }
  destruct Hexists_class as [class_def Hfind_class].
  assert (Hwf_class : wf_class CT class_def).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  inversion Hwf_class; subst.
  - (* WFOtherDef: has parent *)
  assert (C0 = C) by (unfold C0; eapply find_class_cname_consistent; eauto).
  subst C0.
  exists (methods (body class_def)).
  apply CM_Inherit with class_def.
  -- exact Hfind_class.
  -- exact Hdom.
  -- reflexivity.
Qed.

(* Lemma override_parent_method_found : forall parent_methods own_methods m mdef,
  gget_method own_methods m = None ->
  gget_method parent_methods m = Some mdef ->
  gget_method (override parent_methods own_methods) m = Some mdef.
Proof.
  intros parent_methods own_methods m mdef Hown Hparent.
  unfold override, gget_method.
  rewrite find_app_none; auto.
  
  (* We need to show find returns Some mdef on the filtered list *)
  induction parent_methods as [|h t IH].
  - (* parent_methods = [] *)
    simpl in Hparent.
    discriminate.
  - (* parent_methods = h :: t *)
    simpl in Hparent |- *.
    destruct (eq_method_name (mname (msignature h)) m) eqn:Heq_h.
    + (* h matches m *)
      injection Hparent as Heq_mdef.
      subst h.
      (* Show mdef passes the filter *)
      destruct (negb (existsb (fun omdef => eq_method_name (mname (msignature mdef)) (mname (msignature omdef))) own_methods)) eqn:Hfilter.
      * (* mdef passes filter *)
        simpl.
        rewrite Heq_h.
        reflexivity.
      * (* mdef doesn't pass filter - contradiction *)
        exfalso.
        rewrite Bool.negb_false_iff in Hfilter.
        apply existsb_exists in Hfilter.
        destruct Hfilter as [omdef [Hin_own Heq_names]].
        assert (Homdef_m : eq_method_name (mname (msignature omdef)) m = true).
        {
          apply Nat.eqb_eq in Heq_h.
          apply Nat.eqb_eq in Heq_names.
          rewrite <- Heq_names.
          apply Nat.eqb_eq.
          exact Heq_h.
        }
        unfold gget_method in Hown.
        assert (Hcontra : exists x, find (fun mdef => eq_method_name (mname (msignature mdef)) m) own_methods = Some x).
        {
          apply find_some_iff.
          exists omdef.
          split; [exact Hin_own | exact Homdef_m].
        }
        destruct Hcontra as [x Hx].
        rewrite Hx in Hown.
        discriminate.
    + (* h doesn't match m *)
      destruct (negb (existsb (fun omdef => eq_method_name (mname (msignature h)) (mname (msignature omdef))) own_methods)) eqn:Hfilter_h.
      * (* h passes filter *)
        simpl.
        rewrite Heq_h.
        apply IH.
        exact Hparent.
      * (* h doesn't pass filter *)
        apply IH.
        exact Hparent.
Qed. *)

(* Lemma override_parent_method_in : forall parent_methods own_methods m mdef,
  gget_method (override parent_methods own_methods) m = Some mdef ->
  gget_method own_methods m = None ->
  In mdef parent_methods /\ 
  eq_method_name (mname (msignature mdef)) m = true.
Proof.
  intros parent_methods own_methods m mdef Hoverride Hown.
  unfold override, gget_method in Hoverride.
  unfold gget_method in Hown.
  apply find_some in Hoverride.
  destruct Hoverride as [Hin Heq].
  apply in_app_or in Hin.
  destruct Hin as [Hin_own | Hin_filtered].
  - (* mdef is in own_methods - contradiction *)
    exfalso.
    (* If mdef is in own_methods and matches m, then find should return Some *)
    assert (Hfind_some : exists x, find (fun mdef => eq_method_name (mname (msignature mdef)) m) own_methods = Some x).
    {
      apply find_some_iff.
      exists mdef.
      split; [exact Hin_own | exact Heq].
    }
    destruct Hfind_some as [x Hx].
    rewrite Hx in Hown.
    discriminate.
  - (* mdef is in filtered parent_methods *)
    apply filter_In in Hin_filtered.
    destruct Hin_filtered as [Hin_parent _].
    split; [exact Hin_parent | exact Heq].
Qed. *)

Lemma gget_method_from_in : forall methods m mdef,
  In mdef methods ->
  eq_method_name (mname (msignature mdef)) m = true ->
  exists mdef', gget_method methods m = Some mdef' /\ 
                eq_method_name (mname (msignature mdef')) m = true.
Proof.
  intros methods m mdef Hin Heq.
  unfold gget_method.
  induction methods as [|h t IH].
  - (* methods = [] *)
    contradiction.
  - (* methods = h :: t *)
    simpl.
    destruct (eq_method_name (mname (msignature h)) m) eqn:Heq_h.
    + (* h matches m *)
      exists h.
      split; [reflexivity | exact Heq_h].
    + (* h doesn't match m *)
      simpl in Hin.
      destruct Hin as [Heq_mdef | Hin_t].
      * (* mdef = h - contradiction *)
        subst h.
        rewrite Heq in Heq_h.
        discriminate.
      * (* mdef in t *)
        apply IH.
        exact Hin_t.
Qed.

Lemma method_body_well_typed : forall CT C cdef mdef,
  wf_class_table CT ->
  C < dom CT ->
  find_class CT C = Some cdef ->
  In mdef (methods (body cdef)) ->
  exists sΓ', stmt_typing CT (mreceiver (msignature mdef) :: mparams (msignature mdef)) 
                           (mbody_stmt (mbody mdef)) 
                           sΓ'.
Proof.
  intros CT C cdef mdef Hwf_ct Hdom HfindC Hlookup.
  assert (Hwf_class : wf_class CT cdef).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }

  (* assert (Hcname_eq : cname (signature cdef) = C).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [_ [_ Hcname_consistent]].
    destruct Hcname_consistent as [_ Hcname_eq].
    apply Hcname_eq.
    exact HfindC.
  } *)
  assert (Hwf_mdef : wf_method CT C mdef).
  {
    eapply method_lookup_wf_class; eauto.
  }
  inversion Hwf_mdef; subst.
  destruct H as [sΓ' [Htyping _]].
  exists sΓ'.
  unfold sΓ, msig in Htyping.
  unfold methodbody, mbodystmt in Htyping.
  exact Htyping.
Qed.

Lemma method_body_well_typed_by_find : forall CT C m mdef,
  wf_class_table CT ->
  C < dom CT ->
  FindMethodWithName CT C m mdef ->
  exists sΓ', stmt_typing CT (mreceiver (msignature mdef) :: mparams (msignature mdef)) 
                           (mbody_stmt (mbody mdef)) 
                           sΓ'.
Proof.
  intros CT C m mdef Hwf_ct Hdom Hlookup.
  assert (Hexists_class : exists class_def, find_class CT C = Some class_def).
  {
    apply find_class_Some.
    exact Hdom.
  }
  destruct Hexists_class as [class_def Hfind_class].
  assert (Hwf_class : wf_class CT class_def).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  (* assert (Hcname_eq : cname (signature class_def) = C).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [_ [_ Hcname_consistent]].
    destruct Hcname_consistent as [_ Hcname_eq].
    apply Hcname_eq.
    exact Hfind_class.
  } *)
  inversion Hlookup; subst.
  eapply method_body_well_typed; eauto.
apply find_some in H1.
destruct H1 as [Hin _].
exact Hin.
Qed.

Lemma wf_method_sig_types : forall CT C mdef,
  wf_method CT C mdef ->
  wf_stypeuse CT (sqtype (mreceiver (msignature mdef))) (sctype (mreceiver (msignature mdef))) /\
  Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) (mparams (msignature mdef)).
Proof.
  intros CT C mdef Hwf_method.
  inversion Hwf_method; subst.
  destruct H as [sΓ' [Htyping _]].
  assert (Hwf_env : wf_senv CT sΓ).
  {
    eapply stmt_typing_wf_env; eauto.
  }
  unfold sΓ, msig in Hwf_env.
  inversion Hwf_env; subst.
  split.
  - (* Receiver well-formedness *)
    apply Forall_inv in H0.
    exact H0.
  - (* Parameters well-formedness *)
    apply Forall_inv_tail in H0.
    exact H0.
Qed.

Lemma method_sig_wf_reciever : forall CT C cdef mdef,
  wf_class_table CT ->
  C < dom CT ->
  find_class CT C = Some cdef ->
  In mdef (methods (body cdef)) ->
  wf_stypeuse CT (sqtype (mreceiver (msignature mdef))) (sctype (mreceiver (msignature mdef))).
Proof.
  intros CT C cdef mdef Hwf_ct Hdom HfindC Hlookup.
  assert (Hwf_class : wf_class CT cdef).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  (* assert (Hcname_eq : cname (signature cdef) = C).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [_ [_ Hcname_consistent]].
    destruct Hcname_consistent as [_ Hcname_eq].
    apply Hcname_eq.
    exact HfindC.
  } *)
  assert (Hwf_mdef : wf_method CT C mdef).
  {
    eapply method_lookup_wf_class; eauto.
  }

  eapply wf_method_sig_types; eauto.
Qed.

Lemma method_sig_wf_parameters : forall CT C cdef mdef,
  wf_class_table CT ->
  C < dom CT ->
  find_class CT C = Some cdef ->
  In mdef (methods (body cdef)) ->
  Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) (mparams (msignature mdef)).
Proof.
  intros CT C cdef mdef Hwf_ct Hdom HfindC Hlookup.
  assert (Hwf_class : wf_class CT cdef).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  (* assert (Hcname_eq : cname (signature cdef) = C).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [_ [_ Hcname_consistent]].
    destruct Hcname_consistent as [_ Hcname_eq].
    apply Hcname_eq.
    exact HfindC.
  } *)
  assert (Hwf_mdef : wf_method CT C mdef).
  {
    eapply method_lookup_wf_class; eauto.
  }

  eapply wf_method_sig_types; eauto.
Qed.

Lemma method_sig_wf_receiver_by_find : forall CT C m mdef,
  wf_class_table CT ->
  C < dom CT ->
  FindMethodWithName CT C m mdef ->
  wf_stypeuse CT (sqtype (mreceiver (msignature mdef))) (sctype (mreceiver (msignature mdef))).
Proof.
  intros CT C m mdef Hwf_ct Hdom Hlookup.
  assert (Hexists_class : exists class_def, find_class CT C = Some class_def).
{
  apply find_class_Some. exact Hdom.
}
destruct Hexists_class as [class_def Hfind_class].
inversion Hlookup; subst.
assert (Hwf_mdef : wf_method CT C mdef).
{
  eapply method_lookup_wf_class; eauto.
  apply find_some in H1.
  destruct H1 as [Hin _].
  exact Hin.
}
eapply wf_method_sig_types; eauto.
  (* assert (Hwf_inherited : exists D ddef, base_subtype CT C D /\ find_class CT D = Some ddef /\ In mdef (methods (body ddef)) /\ wf_method CT D mdef).
  {
    eapply method_lookup_in_wellformed_inherited; eauto.
  } *)
  (* destruct Hwf_inherited as [D [ddef [Hsub [Hfind_D [Hin_D Hwf_D]]]]]. *)
  (* eapply wf_method_sig_types; eauto. *)
Qed.

Lemma method_sig_wf_parameters_by_find : forall CT C m mdef,
  wf_class_table CT ->
  C < dom CT ->
  FindMethodWithName CT C m mdef ->
  Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) (mparams (msignature mdef)).
Proof.
  intros CT C m mdef Hwf_ct Hdom Hlookup.
    assert (Hexists_class : exists class_def, find_class CT C = Some class_def).
{
  apply find_class_Some. exact Hdom.
}
destruct Hexists_class as [class_def Hfind_class].
inversion Hlookup; subst.
assert (Hwf_mdef : wf_method CT C mdef).
{
  eapply method_lookup_wf_class; eauto.
  apply find_some in H1.
  destruct H1 as [Hin _].
  exact Hin.
}
  eapply wf_method_sig_types; eauto.
Qed.

Lemma In_gget_method_unique : forall method_list mdef m,
  NoDup (map (fun mdef => mname (msignature mdef)) method_list) ->
  In mdef method_list ->
  mname (msignature mdef) = m ->
  gget_method method_list m = Some mdef.
Proof.
  intros method_list mdef m Hnodup Hin Hname.
  unfold gget_method.
  induction method_list as [|hd tl IH].
  - contradiction Hin.
  - simpl in Hin.
    destruct Hin as [Heq | Hin_tl].
    + subst hd.
      simpl.
      unfold eq_method_name.
      rewrite Hname.
      rewrite Nat.eqb_refl.
      reflexivity.
    + simpl.
      unfold eq_method_name.
      destruct (Nat.eqb (mname (msignature hd)) m) eqn:Heqb.
      * (* Contradiction with NoDup *)
        exfalso.
        apply Nat.eqb_eq in Heqb.
        simpl in Hnodup.
        inversion Hnodup; subst.
        apply H1.
        apply in_map_iff.
        exists mdef.
        split; [symmetry; exact Heqb | exact Hin_tl].
      * (* Use IH *)
        apply IH.
        -- simpl in Hnodup.
           inversion Hnodup; auto.
        -- exact Hin_tl.
Qed.

Lemma In_gget_method_unique_class : forall CT C cdef mdef m,
  wf_class_table CT ->
  find_class CT C = Some cdef ->
  In mdef (methods (body cdef)) ->
  mname (msignature mdef) = m ->
  gget_method (methods (body cdef)) m = Some mdef.
Proof.
  intros CT C cdef mdef m Hwf_ct Hfind Hin Hname.
  assert (Hwf_class : wf_class CT cdef).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  apply In_gget_method_unique.
  - (* Extract NoDup from wf_class *)
    inversion Hwf_class; subst.
    (* + WFObjectDef case
      rewrite H2.
      simpl.
      constructor. *)
    + (* WFOtherDef case *)
      destruct H0 as [_ [_ [Hnodup _]]].
      unfold bod in Hnodup.
      exact Hnodup.
  - exact Hin.
  - exact Hname.
Qed.

Lemma constructor_params_field_count : forall CT C ctor csig fields,
  wf_class_table CT ->
  C < dom CT ->
  constructor_def_lookup CT C = Some ctor ->
  csig = csignature ctor ->
  CollectFields CT C fields ->
  List.length (cparams csig) = List.length fields.
  Proof.
  intros CT C ctor csig fields Hwf_ct Hdom Hctor_lookup Hcsig_eq Hcollect.
  subst csig.
  
  (* Get the class definition *)
  assert (Hclass_exists : exists cdef, find_class CT C = Some cdef).
  {
    apply find_class_Some. exact Hdom.
  }
  destruct Hclass_exists as [cdef Hfind_class].
  
  (* Establish constructor equality *)
  assert (Hctor_eq : constructor (body cdef) = ctor).
  {
    unfold constructor_def_lookup in Hctor_lookup.
    rewrite Hfind_class in Hctor_lookup.
    injection Hctor_lookup as Hctor_eq.
    exact Hctor_eq.
  }
  
  (* Extract well-formedness *)
  assert (Hwf_class : wf_class CT cdef).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  
  (* Extract constructor well-formedness *)
  inversion Hwf_class; subst.
  destruct H0 as [Hwf_ctor _].
  assert (C0 = C) by (unfold C0; eapply find_class_cname_consistent; eauto).
  subst C0.
  inversion Hwf_ctor; subst.
  (* assert (Hfields_eq : fields = this_fields_def).
  {
    eapply collect_fields_deterministic_rel; eauto.
  } *)
  (* subst fields. *)
  unfold Syntax.body.
  fold bod.
  destruct H1 as [_ [field_defs [Hcollect_H1 [Hdom_eq _]]]].
  assert (field_defs = fields) by (eapply collect_fields_deterministic_rel; eauto).
  subst field_defs.
  exact Hdom_eq.
Qed.

Lemma constructor_lookup_wf : forall CT C ctor,
  wf_class_table CT ->
  C < dom CT ->
  constructor_sig_lookup CT C = Some ctor ->
  wf_constructor CT C ctor.
Proof.
  intros CT C ctor Hwf_ct Hdom Hctor_lookup.
  assert (Hexists_class : exists cdef, find_class CT C = Some cdef).
  {
    apply find_class_Some. exact Hdom.
  }
  destruct Hexists_class as [cdef Hfind_class].
  assert (Hwf_class : wf_class CT cdef).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  inversion Hwf_class; subst.
  destruct H0 as [Hwf_ctor _].
  assert (C0 = C) by (unfold C0; eapply find_class_cname_consistent; eauto).
  subst C0.
  unfold constructor_sig_lookup in Hctor_lookup.
  unfold constructor_def_lookup in Hctor_lookup.
  rewrite Hfind_class in Hctor_lookup.
  injection Hctor_lookup as Hctor_eq.
  rewrite <- Hctor_eq.
  fold bod.
  rewrite <- H.
  exact Hwf_ctor.
Qed.

Lemma eval_stmt_preserves_heap_domain_simple : forall CT rΓ h stmt rΓ' h',
  eval_stmt OK CT rΓ h stmt OK rΓ' h' ->
  dom h <= dom h'.
Proof.
  intros CT rΓ h stmt rΓ' h' Heval.
  remember OK as ok.
  induction Heval; try reflexivity; try discriminate.
  - (* FldWrite: h' = update_field h lx f v2 *)
    rewrite H3.
    unfold update_field.
    rewrite H0.
    rewrite update_length.
    reflexivity.
  - (* New: h' = h ++ [new_obj] *)
    rewrite H4.
    rewrite length_app.
    simpl.
    lia.
  - (* Call: use IH *)
    apply IHHeval. reflexivity.
  - (* Seq: transitivity *)
    apply Nat.le_trans with (dom h').
    + apply IHHeval1. reflexivity.
    + apply IHHeval2. reflexivity.
Qed.

Lemma runtime_getObj_app_left : forall h h_ext loc obj,
  loc < dom h ->
  runtime_getObj h loc = Some obj ->
  runtime_getObj (h ++ h_ext) loc = Some obj.
Proof.
  intros h h_ext loc obj Hloc_dom Hobj.
  unfold runtime_getObj in *.
  rewrite nth_error_app1.
  - exact Hloc_dom.
  - exact Hobj.
Qed.

(* Not just length, there is no statment can do strong update. *)
Lemma eval_stmt_preserves_r_type : 
  forall CT rΓ h stmt rΓ' h' loc rqt,
    eval_stmt OK CT rΓ h stmt OK rΓ' h' ->
    r_type h loc = Some rqt ->
    loc < dom h ->
    r_type h' loc = Some rqt.
Proof.
  intros CT rΓ h stmt rΓ' h' loc rqt Heval Hrtype Hloc_dom.
  remember OK as ok.
  induction Heval; try discriminate; try (subst; exact Hrtype).
  - (* FldWrite: only fields change, not type *)
    subst h'.
    unfold r_type in Hrtype |- *.
    unfold update_field.
    destruct (runtime_getObj h loc_x) as [ox|] eqn:Hlx; [|exact Hrtype].
    destruct (Nat.eq_dec loc loc_x) as [Heq|Hneq].
    + (* loc = lx: type preserved *)
      subst loc.
      rewrite runtime_getObj_update_same.
      * apply runtime_getObj_dom in Hlx. exact Hlx.
      * simpl. unfold r_type in Hrtype.
        rewrite Hlx in Hrtype. exact Hrtype.
    + (* loc ≠ lx: unchanged *)
      rewrite runtime_getObj_update_diff.
      * symmetry. exact Hneq.
      * exact Hrtype.
  - (* New: existing objects unchanged *)
    subst h'.
    unfold r_type in Hrtype |- *.
    destruct (runtime_getObj h loc) as [obj_loc|] eqn:Hobj_loc; [|discriminate].
    injection Hrtype as Hrtype_eq.
    subst rqt.
    erewrite runtime_getObj_app_left; eauto.
  - (* Call: use IH *)
    eapply IHHeval; eauto.
  - (* Seq: transitivity *)
    assert (Hloc_dom' : loc < dom h').
    {
      have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓ h s1 rΓ' h' Heval1.
      lia.
    }
    assert (Hrtype' : r_type h' loc = Some rqt).
    {
      eapply IHHeval1; eauto.
    }
    eapply IHHeval2; eauto.
Qed.

Lemma eval_stmt_preserves_r_muttype : 
  forall CT rΓ h stmt rΓ' h' loc q,
    eval_stmt OK CT rΓ h stmt OK rΓ' h' ->
    r_muttype h loc = Some q ->
    loc < dom h ->
    r_muttype h' loc = Some q.
Proof.
  intros CT rΓ h stmt rΓ' h' loc q Heval Hmut Hloc_dom.
  remember OK as ok.
  induction Heval; try discriminate; try (subst; exact Hmut).
  - (* FldWrite: only fields change, not mutability type *)
    subst h'.
    unfold update_field.
    destruct (runtime_getObj h loc_x) as [ox|] eqn:Hlx; [|exact Hmut].
    destruct (Nat.eq_dec loc loc_x) as [Heq|Hneq].
    + (* loc = lx: mutability type preserved *)
      subst loc.
      unfold r_muttype in Hmut |- *.
      unfold update_field.
      injection H0 as H0_eq.
      subst ox.
      rewrite runtime_getObj_update_same.
      * exact Hloc_dom.
      * simpl. rewrite Hlx in Hmut. exact Hmut.
    + (* loc ≠ lx: unchanged *)
      unfold r_muttype in Hmut |- *.
      unfold update_field.
      injection H0 as H0_eq.
      subst ox.
      rewrite runtime_getObj_update_diff.
      * symmetry. exact Hneq.
      * exact Hmut.
  - (* New: existing objects unchanged *)
    subst h'.
    destruct (runtime_getObj h loc) as [obj_loc|] eqn:Hobj_loc.
    2:{
      unfold r_muttype in Hmut.
      rewrite Hobj_loc in Hmut.
        discriminate Hmut.
    }
    unfold r_muttype in Hmut |- *.
    rewrite Hobj_loc in Hmut.
    injection Hmut as Hmut_eq.
    subst q.
    erewrite runtime_getObj_app_left; eauto.
  - (* Call: use IH *)
    eapply IHHeval; eauto.
  - (* Seq: transitivity *)
    assert (Hloc_dom' : loc < dom h').
    {
      have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓ h s1 rΓ' h' Heval1.
      lia.
    }
    assert (Hmut' : r_muttype h' loc = Some q).
    {
      eapply IHHeval1; eauto.
    }
    eapply IHHeval2; eauto.
Qed.

Lemma wf_r_typable_env_independent : forall CT rΓ1 rΓ2 h loc qt l qcontext,
  get_this_var_mapping (vars rΓ1) = Some l ->
  get_this_var_mapping (vars rΓ1) = get_this_var_mapping (vars rΓ2) ->
  r_muttype h l = Some qcontext ->
  wf_r_typable CT rΓ1 h loc qt qcontext->
  wf_r_typable CT rΓ2 h loc qt qcontext.
Proof.
  intros CT rΓ1 rΓ2 h loc qt l qcontext Hreceiveraddr Henvsame Hreceiverrmut Hsame_this.
  unfold wf_r_typable in *.
  destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
  exact Hsame_this.
Qed.

Lemma r_basetype_in_dom : forall CT h loc cy,
  wf_heap CT h->
  r_basetype h loc = Some cy ->
  cy < dom CT.
Proof.
  intros CT h loc cy Hwf_heap Hr_basetype.
  unfold r_basetype in Hr_basetype.
  destruct (runtime_getObj h loc) as [obj|] eqn:Hobj; [|discriminate].
  injection Hr_basetype as Heq.
  subst cy.
  destruct obj as [rt_obj fields_obj].
  destruct rt_obj as [rq_obj rc_obj].
  simpl.
  unfold wf_heap in Hwf_heap.
  assert (Hloc_dom : loc < dom h) by (apply runtime_getObj_dom in Hobj; exact Hobj).
  specialize (Hwf_heap loc Hloc_dom).
  unfold wf_obj in Hwf_heap.
  rewrite Hobj in Hwf_heap.
  destruct Hwf_heap as [Hwf_rtypeuse _].
  unfold wf_rtypeuse in Hwf_rtypeuse.
  simpl in Hwf_rtypeuse.
  destruct (bound CT rc_obj) as [qc|] eqn:Hbound.
  - destruct Hwf_rtypeuse as [Hwf_rtypeuse _]. exact Hwf_rtypeuse.
  - contradiction.
Qed.

(* Lemma vpa_qualified_type_sctype : forall q T,
  sctype (vpa_qualified_type q T) = sctype T.
Proof.
  intros q T.
  unfold vpa_qualified_type.
  destruct T as [sq sc].
  simpl.
  reflexivity.
Qed. *)

Lemma collect_fields_consistent_through_runtime_static : forall CT C D fields1 fields2 f fdef1 fdef2,
  wf_class_table CT ->
  C = D ->
  CollectFields CT C fields1 ->
  CollectFields CT D fields2 ->
  gget fields1 f = Some fdef1 ->
  gget fields2 f = Some fdef2 ->
  fdef1 = fdef2.
Proof.
  intros CT C D fields1 fields2 f fdef1 fdef2 Hwf_ct Heq Hcf1 Hcf2 Hget1 Hget2.
  subst D.
  assert (fields1 = fields2).
  {
    eapply collect_fields_deterministic_rel; eauto.
  }
  subst fields2.
  rewrite Hget1 in Hget2.
  injection Hget2 as Heq.
  exact Heq.
Qed.

Lemma correspondence_to_typable : forall CT sΓ rΓ h i sqt loc ι qcontext,
  get_this_var_mapping (vars rΓ) = Some ι ->
  (r_muttype h ι) = Some qcontext ->
  (forall i : nat,
   i < dom sΓ ->
   forall sqt : qualified_type,
   nth_error sΓ i = Some sqt ->
   match runtime_getVal rΓ i with
   | Some Null_a => True
   | Some (Iot loc) => wf_r_typable CT rΓ h loc sqt qcontext
   | None => False
   end) ->
  i < dom sΓ ->
  nth_error sΓ i = Some sqt ->
  runtime_getVal rΓ i = Some (Iot loc) ->
  wf_r_typable CT rΓ h loc sqt qcontext.
Proof.
  intros CT sΓ rΓ h i sqt loc ι qcontext Hreceiveraddr Hreceiverrmut Hcorr Hi Hnth Hval.
  specialize (Hcorr i Hi sqt Hnth).
  rewrite Hval in Hcorr.
  exact Hcorr.
Qed.

Lemma typable_to_base_and_qualifier : forall CT rΓ h loc sqt rq_obj rc_obj ι qcontext,
  get_this_var_mapping (vars rΓ) = Some ι ->
  r_muttype h ι = Some qcontext ->
  wf_r_typable CT rΓ h loc sqt qcontext ->
  r_type h loc = Some {| rqtype := rq_obj; rctype := rc_obj |} ->
  rc_obj = sctype sqt /\
  qualifier_typable_context rq_obj ( (sqtype sqt)) qcontext.
Proof.
  intros CT rΓ h loc sqt rq_obj rc_obj ι qcontext Hreceiveraddr Hreceiverrmut Hwf_typable Hrtype.
  unfold wf_r_typable in Hwf_typable.
  rewrite Hrtype in Hwf_typable.
  exact Hwf_typable.
Qed.

Lemma qualifier_typable_subtype_receiver : forall rq Ty1 Ty2 qcontext,
  qualifier_typable_context rq (sqtype Ty1) qcontext ->
  sqtype Ty1 ⊑ sqtype Ty2 ->
  qualifier_typable_context rq (sqtype Ty2) qcontext.
Proof.
  intros rq Ty1 Ty2 qcontext Hqual_ty1 Hsubtype.
  unfold qualifier_typable_context in *.
  destruct rq as [|]; destruct (sqtype Ty1); destruct (sqtype Ty2);
  simpl in *; auto;
  try (inversion Hsubtype; auto);
  try unfold vpa_mutabilty_rs in *;
  try destruct qcontext;
  try reflexivity;
  try easy.
Qed.

Lemma gget_method_in : forall methods m mdef,
  gget_method methods m = Some mdef ->
  In mdef methods.
Proof.
  intros methods m mdef Hget.
  unfold gget_method in Hget.
  apply find_some in Hget.
  destruct Hget as [Hin _].
  exact Hin.
Qed.

Lemma gget_method_in_iff : forall methods m mdef,
  NoDup (map (fun mdef => mname (msignature mdef)) methods) ->
  (gget_method methods m = Some mdef <-> 
   In mdef methods /\ mname (msignature mdef) = m).
Proof.
  intros methods m mdef Hnodup.
  split.
  - (* gget_method -> In /\ name match *)
    intro Hget.
    split.
    + eapply gget_method_in; eauto.
    + eapply gget_method_name_consistent; eauto.
  - (* In /\ name match -> gget_method *)
    intros [Hin Hname].
    eapply In_gget_method_unique; eauto.
Qed.

Lemma qualifier_typable_trans_subtype : forall rq T1 T2 T3 qcontext,
  qualifier_typable_context rq (sqtype T1) qcontext ->
  sqtype T1 ⊑ sqtype T2 ->
  sqtype T2 ⊑ sqtype T3 ->
  qualifier_typable_context rq (sqtype T3) qcontext.
Proof.
  intros rq T1 T2 T3 qcontext Hqual H12 H23.
  eapply qualifier_typable_subtype_receiver; [|exact H23].
  eapply qualifier_typable_subtype_receiver; [exact Hqual|exact H12].
Qed.

Lemma Forall2_from_nth : forall {A B} (P : A -> B -> Prop) l1 l2,
  List.length l1 = List.length l2 ->
  (forall i a b, i < List.length l1 -> nth_error l1 i = Some a -> nth_error l2 i = Some b -> P a b) ->
  Forall2 P l1 l2.
Proof.
  intros A B P l1 l2 Hlen Hprop.
  generalize dependent l2.
  induction l1 as [|a1 l1' IH]; intros l2 Hlen Hprop.
  - (* Base case: l1 = [] *)
    destruct l2; [constructor | discriminate].
  - (* Inductive case: l1 = a1 :: l1' *)
    destruct l2 as [|a2 l2']; [discriminate|].
    constructor.
    + (* Show P a1 a2 *)
        specialize (Hprop 0 a1 a2).
  apply Hprop.
  -- simpl. lia.
  -- reflexivity.
  -- reflexivity.
    + (* Show Forall2 P l1' l2' *)
      apply IH.
      * simpl in Hlen. lia.
      * intros i a b Hi Ha Hb.
        apply Hprop with (S i); [simpl; lia | exact Ha | exact Hb].
Qed.

(* ------------------------------------------------------------- *)
(* Soundness properties for PICO *)
Theorem preservation_pico :
  forall CT sΓ rΓ h stmt rΓ' h' sΓ',
    (* get_this_var_mapping (vars rΓ) = Some ι ->
    (r_muttype h ι) = Some q_this -> *)
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ stmt sΓ' -> 
    eval_stmt OK CT rΓ h stmt OK rΓ' h' -> 
    wf_r_config CT sΓ' rΓ' h'.
Proof.
  intros CT sΓ rΓ h stmt rΓ' h' sΓ' Hwf Htyping Heval.
  (* generalize dependent ι. *)
  generalize dependent sΓ.
  generalize dependent sΓ'.
  (* generalize dependent q_this. *)
  remember OK as ok.
  induction Heval; intros; try (discriminate; inversion Htyping; subst; exact Hwf).
  6: 
  {
    inversion Htyping; subst.
    destruct H1 as [mdeflookup getmbody].
    remember (msignature mdef) as msig.
    have mdeflookupcopy := mdeflookup.
    apply method_lookup_wf_class_by_find in mdeflookup; auto.
    2:{
      unfold wf_r_config in Hwf.
      destruct Hwf as [Hwf_classtable _].
      exact Hwf_classtable.
    }
    (* 2:{
      unfold r_basetype in H0.
    } *)
    inversion mdeflookup; revert getmbody; subst.
    intro getmbody.
    (* apply method_body_well_typed_by_find in mdeflookup; auto. *)
    destruct H1 as [sΓmethodend Htyping_method].
    destruct Htyping_method as [Htyping_method Hmethodret].
    remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit.
    remember {| vars := Iot ly :: vals |} as rΓmethodinit.
    destruct (r_muttype h ly) eqn: Hinnerthis.
    2:{
      unfold r_muttype in Hinnerthis.
      unfold r_basetype in H0.
      destruct (runtime_getObj h ly).
      discriminate Hinnerthis.
      discriminate H0.
    }
    remember (rΓ <| vars := update x retval (vars rΓ) |>) as rΓ'''.
    (* TODO: should I do context switch here? how to handle the type context switch; this is very interesting *)
    assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
    { (* Method inner config wellformed.*)
      assert (get_this_var_mapping (vars rΓmethodinit) = Some ly).
      {
        unfold get_this_var_mapping.
        rewrite HeqrΓmethodinit.
        simpl.
        auto.
      }
      have Hwfcopy := Hwf.
      unfold wf_r_config in Hwf.
      unfold wf_r_config.
      destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
      have Hclasstable := Hclass.
      unfold  wf_class_table in Hclass.
      destruct Hclass as [Hclass Hcname_consistent].
      repeat split.
      exact Hclass.

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

      (* Inner runtime env is wellformed*)
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
      eapply runtime_lookup_list_preserves_wf_values with (zs:=zs)(vals0 := vals)(rΓ := rΓmethodinit) (CT:=CT); eauto.
      admit.
      admit.

      rewrite HeqsΓmethodinit.
      simpl.
      lia.

      (* Inner static env's elements are wellformed typeuse *)
      rewrite HeqsΓmethodinit.
      constructor.
      subst.

      (* Receiver type is well-formed *)
      eapply method_sig_wf_receiver_by_find; eauto.
      unfold r_basetype in H0.
      destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
      injection H0 as H2_eq.
      (* subst cy. *)
      destruct obj as [rt_obj fields_obj].
      destruct rt_obj as [rq_obj rc_obj].
      simpl.
      unfold wf_heap in Hheap.
      assert (Hly_dom : ly < dom h) by (apply runtime_getObj_dom in Hobjy; exact Hobjy).
      specialize (Hheap ly Hly_dom).
      unfold wf_obj in Hheap.
      rewrite Hobjy in Hheap.
      destruct Hheap as [Hwf_rtypeuse _].
      unfold wf_rtypeuse in Hwf_rtypeuse.
      simpl in Hwf_rtypeuse.
      destruct (bound CT rc_obj) as [class_def|] eqn:Hbound.
      subst cy.
      simpl.
      destruct Hwf_rtypeuse as [Hwf_rtypeuse _].
      exact Hwf_rtypeuse.
      contradiction.

      eapply method_sig_wf_parameters_by_find; eauto.
      unfold r_basetype in H0.
      destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
      injection H0 as H2_eq.
      subst cy.
      destruct obj as [rt_obj fields_obj].
      destruct rt_obj as [rq_obj rc_obj].
      simpl.
      unfold wf_heap in Hheap.
      assert (Hly_dom : ly < dom h) by (apply runtime_getObj_dom in Hobjy; exact Hobjy).
      specialize (Hheap ly Hly_dom).
      unfold wf_obj in Hheap.
      rewrite Hobjy in Hheap.
      destruct Hheap as [Hwf_rtypeuse _].
      unfold wf_rtypeuse in Hwf_rtypeuse.
      simpl in Hwf_rtypeuse.
      destruct (bound CT rc_obj) as [class_def|] eqn:Hbound.
      simpl.
      destruct Hwf_rtypeuse as [Hwf_rtypeuse _].
      exact Hwf_rtypeuse.
      contradiction.

      apply static_getType_list_preserves_length in H15.
      apply runtime_lookup_list_preserves_length in H4.
      rewrite HeqsΓmethodinit.
      rewrite HeqrΓmethodinit.
      simpl.
      f_equal.
      apply Forall2_length in H23.
      (* rewrite <- Heqmsig. *)
        assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H14.
          exact H14.
        }

        assert (Hytypable: wf_r_typable CT rΓ h ly Ty q). {
          (* eapply correspondence_to_typable; eauto. *)
          admit.
        }

        (* Apply correspondence to get wf_r_typable *)
        specialize (Hcorr ly q Hy_dom Ty H14).
        rewrite H in Hcorr.

        (* Extract subtyping from wf_r_typable *)
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H0.
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
        injection Hget_iot as Hv0_eq.
        subst v0.

        unfold r_type in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        (* destruct (r_muttype h iot) as [q|] eqn:Hmut; [|contradiction]. *)
        destruct Hcorr as [Hsubtype _].
       
      rewrite <- H4 in H15.
      rewrite <- H15.
      rewrite H23.
      (* rewrite Heqmsig. *)
      rewrite <- Hsubtype in H16.
      simpl in mdeflookupcopy.
      assert (mdef = mdef0). 
      {
        eapply find_overriding_method_deterministic; eauto.
      }
      rewrite H0.
      reflexivity.


      intros i Hi sqt Hnth.
      rewrite HeqsΓmethodinit in Hnth, Hi.
      rewrite HeqrΓmethodinit.
      simpl in *.
      destruct i as [|i'].
      (* Reciever *)
      simpl in Hnth.
      injection Hnth as Hsqt_eq.
      subst sqt.
      simpl.
      unfold wf_r_typable.
      unfold r_type.
      destruct (runtime_getObj h ly) as [objy|] eqn:Hobj_ly.
      2:{
        unfold r_basetype in H0.
        rewrite Hobj_ly in H0.
        discriminate.
      }
      (* Get the runtime type *)
      simpl.
      destruct (r_muttype h ly) as [qy|] eqn:Hq_ly.
      2:{
        unfold r_muttype in Hq_ly.
        rewrite Hobj_ly in Hq_ly.
        discriminate.
      }
      split.
      apply qualified_type_subtype_base_subtype in H22.
      (* rewrite vpa_qualified_type_sctype in H22. *)
      assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H14.
          exact H14.
        }

      specialize (Hcorr y Hy_dom Ty H14).
              (* Extract subtyping from wf_r_typable *)
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
        injection Hget_iot as Hv0_eq.
        subst v0.

        unfold r_type in Hcorr.
        rewrite H in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        (* destruct (r_muttype h iot) as [q|] eqn:Hmut; [|contradiction]. *)
        destruct Hcorr as [Hsubtype _].
        simpl in Hobj_ly.
        injection Hobj_ly as Hobjy_eq.

       
      rewrite <- Hsubtype in H16.
      simpl in mdeflookupcopy.
      assert (heqm : mdef = mdef0). 
      {
        eapply find_overriding_method_deterministic; eauto.
      }
      subst objy.
      simpl.
      rewrite heqm.
      rewrite <- Hsubtype in H22.
      exact H22.
      apply qualified_type_subtype_q_subtype in H22.
      assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H14.
          exact H14.
        }

      specialize (Hcorr y Hy_dom Ty H14).
              (* Extract subtyping from wf_r_typable *)
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
        injection Hget_iot as Hv0_eq.
        subst v0.

        unfold r_type in Hcorr.
        rewrite H in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        (* destruct (r_muttype h iot) as [q|] eqn:Hmut; [|contradiction]. *)
        destruct Hcorr as [Hsubtype Hqualifier].
        simpl in Hobj_ly.
        injection Hobj_ly as Hobjy_eq.
      rewrite <- Hsubtype in H16.
      simpl in mdeflookupcopy.
      assert (heqm : mdef = mdef0). 
      {
        eapply find_overriding_method_deterministic; eauto.
      }
      subst mdef0.
      rewrite <- Hobjy_eq.
      simpl.
      eapply qualifier_typable_subtype_receiver; eauto.
      (* destruct q_this, q. *)
      (* 1-4: try exact Hqualifier.
      1-2: unfold qualifier_typable in *.
      1-2: destruct rq_obj.
      1-4: destruct (sqtype Ty).
      1-24: unfold vpa_mutabilty_rs in *.
      1-24: try reflexivity.
      1-10: try easy. *)

(* -------------------------------------------------- *)
      apply qualified_type_subtype_q_subtype in H22.
        assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H14.
          exact H14.
        }
      specialize (Hcorr y Hy_dom Ty H14).
              (* Extract subtyping from wf_r_typable *)
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
        injection Hget_iot as Hv0_eq.
        subst v0.

        unfold r_type in Hcorr.
        rewrite H in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        (* destruct (r_muttype h iot) as [q|] eqn:Hmut; [|contradiction *)
        destruct Hcorr as [Hsubtype Hqualifier].
        (* simpl in Hobj_ly. *)
        (* injection Hobj_ly as Hobjy_eq. *)
      rewrite <- Hsubtype in H16.

      assert (heqm : mdef = mdef0). 
      {
        eapply find_overriding_method_deterministic; eauto.
      }
      subst mdef0.

      simpl.
      unfold runtime_getVal.
      simpl.
      destruct (nth_error vals i') as [v|] eqn:Hval_i.
      - (* Parameter i' exists *)
        destruct v as [|loc]; [trivial|].
        (* Use H23 to get the subtyping relationship *)
        assert (Hi'_bound : i' < List.length argtypes).
        {
          apply Forall2_length in H23.
          simpl in Hi.
          (* rewrite HeqsΓmethodinit in Hnth. *)
          simpl in Hnth.
          (* apply nth_error_Some in Hnth. *)
          simpl in Hnth.
          lia.
        }
        assert (Harg_type : exists argtype, nth_error argtypes i' = Some argtype).
        {
          apply nth_error_Some_exists.
          exact Hi'_bound.
        }
        destruct Harg_type as [argtype Hargtype].
        (* Use runtime_lookup_list_preserves_typing *)
        eapply runtime_lookup_list_preserves_typing with (CT:= CT) (h:=h)in H4; eauto.
        eapply Forall2_nth_error in H4; eauto.
        (* Apply subtyping from H23 *)
        eapply Forall2_nth_error in H23; eauto.
        simpl in H4.
        eapply wf_r_typable_subtype; eauto.
        
        (* eapply wf_r_typable_env_independent; [|exact H4].
        simpl.
        unfold get_this_var_mapping.
        exact H4.*)
      - (* Parameter i' doesn't exist - contradiction *)
        exfalso.
        apply nth_error_None in Hval_i.
        apply runtime_lookup_list_preserves_length in H4.
        apply static_getType_list_preserves_length in H15.
        apply Forall2_length in H23.
        rewrite H4 in Hval_i.
        rewrite <- H15 in Hval_i.
        rewrite H23 in Hval_i.
        simpl in Hi.
        simpl in Hnth.
        simpl in Hnth.
        lia.
    }
    assert (wf_r_config CT sΓmethodend rΓ'' h'). 
    {
      eapply IHHeval with (sΓ := sΓmethodinit) (sΓ' := sΓmethodend); eauto.
      unfold mbodystmt in Htyping_method.
      unfold methodbody in Htyping_method.
      subst msig0.
      fold sΓ in HeqsΓmethodinit.
      rewrite <- HeqsΓmethodinit in Htyping_method.
      rewrite <- getmbody in Htyping_method.

      exact Htyping_method.
      (* unfold get_this_var_mapping. *)
      (* rewrite HeqrΓmethodinit.
      simpl.
      reflexivity. *)
    }
    { (* Method call resulting config is wellformed *)
      have H1copy := H1.
      unfold wf_r_config in H1.
      unfold wf_r_config.
      unfold wf_r_config in Hwf.
      destruct Hwf as [_ [Hheapinit [Hrenvinit [Hsenvinit [Hleninit Hcorrinit]]]]].
      unfold wf_renv in Hrenvinit.
      destruct Hrenvinit as [HrEnvLen [Hreceiver Hrenvval]].
      (* destruct Hreceiver as [Hreceiverval Hreceivervaldom]. *)
      destruct H1 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
      destruct Hclass as [Hclass Hcname_consistent].
      repeat split.
      exact Hclass.
      apply Hcname_consistent.
      apply Hcname_consistent.
      exact Hheap.
      rewrite HeqrΓ'''.
      simpl.
      rewrite update_length.
      simpl.
      lia.
      destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
      exists iot.
      split.
      rewrite HeqrΓ'''.
      simpl.
      unfold gget in *.
      destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
      discriminate Hget_iot.
      injection Hget_iot as Hv0_eq.
      subst v0.
      unfold update.
      destruct x as [|x'].
      easy.
      simpl.
      reflexivity.
      unfold mbodystmt in Htyping_method.
      unfold methodbody in Htyping_method.
      subst msig0.
      fold sΓ in HeqsΓmethodinit.
      rewrite <- HeqsΓmethodinit in Htyping_method.
      rewrite <- getmbody in Htyping_method.
      have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓmethodinit h (mbody_stmt mbody) rΓ'' h' Heval.
      lia.

      (* Outter runtime env is wellformed*)
      rewrite HeqrΓ'''.
      simpl.
      eapply Forall_update; eauto.
      eapply Forall_impl; [|exact Hrenvval].
      intros v Hv.
      destruct v as [|loc]; [trivial|].
      destruct (runtime_getObj h loc) as [obj|] eqn:Hobjloc; [|contradiction].
            unfold mbodystmt in Htyping_method.
      unfold methodbody in Htyping_method.
      subst msig0.
      fold sΓ in HeqsΓmethodinit.
      rewrite <- HeqsΓmethodinit in Htyping_method.
      rewrite <- getmbody in Htyping_method.
      have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓmethodinit h (mbody_stmt mbody) rΓ'' h' Heval.
      assert (Hloc_dom : loc < dom h) by (apply runtime_getObj_dom in Hobjloc; exact Hobjloc).
      assert (Hloc_dom' : loc < dom h') by lia.
      destruct (runtime_getObj h' loc) as [obj'|] eqn:Hobj'.
      trivial.
      exfalso. apply runtime_getObj_not_dom in Hobj'. lia.
      unfold runtime_getVal in H6.
      destruct retval as [|loc]; [trivial|].
      unfold wf_renv in Hrenv.
      destruct Hrenv as [_ [_ Hrenv_wf]].
      eapply Forall_nth_error in Hrenv_wf; eauto.
      simpl in Hrenv_wf.
      destruct (runtime_getObj h' loc) as [obj|] eqn:Hobjloc; [trivial|].
      contradiction.
      apply static_getType_dom in H13.
      rewrite Hleninit in H13.
      exact H13.

      rewrite Hleninit.
      exact HrEnvLen.
      unfold wf_senv in Hsenvinit.
      destruct Hsenvinit as [Hsenvpdom Hsenvptypeuse].
      exact Hsenvptypeuse.

      rewrite Hleninit.
      rewrite HeqrΓ'''.
      simpl.
      rewrite update_length.
      easy.

      intros i Hi sqt Hnth.
      destruct (Nat.eq_dec i x) as [Heq | Hneq].
      - (* Case: i = x (updated variable) *)
        subst i.
        rewrite HeqrΓ'''.
        simpl.
        unfold runtime_getVal.
        rewrite update_same.
        + apply static_getType_dom in H13.
          rewrite Hleninit in H13.
          exact H13.
        + (* Show wf_r_typable for retval *)
          assert (Hnth_x : nth_error sΓ' x = Some Tx).
          {
            unfold static_getType in H13.
            exact H13.
          }
          rewrite Hnth_x in Hnth.
          injection Hnth as Hsqt_eq.
          subst sqt.
          (* Use the fact that retval is well-typed from method return *)
          unfold runtime_getVal in H6.
          destruct retval as [|loc]; [trivial|].
          assert (Hret_dom : mreturn mbody < dom (vars rΓ'')).
          {
            apply nth_error_Some.
            rewrite H6.
            discriminate.
          }
          rewrite <- Hlen in Hret_dom.
          assert (wf_class_table CT). {
            unfold wf_class_table.
            split.
            exact Hclass.
            exact Hcname_consistent.
          }
          destruct Hmethodret as [Hmbodyretvar_dom [Hnth_mbodyret Hsubtype_ret]].
          unfold methodbody0 in Hnth_mbodyret.
          rewrite <- getmbody in Hnth_mbodyret.
          have Hcorr_copy := Hcorr.
          specialize (Hcorr (mreturn mbody) Hret_dom mbodyrettype Hnth_mbodyret).
          destruct (runtime_getVal rΓ'' (mreturn mbody)) eqn: Hmet_val; [|easy].
          destruct v.
          2:{
            unfold runtime_getVal in Hmet_val.
            rewrite Hmet_val in H6.
            inversion H6.
            unfold wf_r_typable.
            unfold r_type.
            unfold runtime_getObj.
            subst loc.
            unfold wf_r_typable in Hcorr.
            unfold r_type in Hcorr.
            unfold runtime_getObj in Hcorr.
            destruct (nth_error h' l).
            2:{easy.
            }
            destruct Hcorr as [Hrorettypebase Hrorettypequalifier].
            split.
            apply qualified_type_subtype_base_subtype in Hsubtype_ret.
            rewrite <- Hrorettypebase in Hsubtype_ret.
            fold msig0 in msig1.
            subst msig1.
            apply qualified_type_subtype_base_subtype in H21.
            rewrite <- H21.
            rewrite Hsubtype_ret.
            unfold msig0.
            unfold r_type in Hcorr_copy.
            assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H14.
          exact H14.
        }

        assert (Hytypable: wf_r_typable CT rΓ h ly Ty). {
          eapply correspondence_to_typable; eauto.
        }
        unfold wf_r_typable in Hytypable.
        unfold r_type in Hytypable.
        unfold r_basetype in H0.
        destruct (runtime_getObj h ly).
        2:{easy.
        }
        destruct Hytypable as [HyBasetype _].
        inversion H0.
        rewrite H3 in HyBasetype.
        rewrite HyBasetype in mdeflookupcopy. 
        (* destruct (r_muttype h iot) as [q|] eqn:Hmut; [|contradiction]. *)
            assert (mdef = mdef0). 
            {
              eapply find_overriding_method_deterministic; eauto.
            }
            subst mdef.
            reflexivity.
            eapply qualified_type_subtype_q_subtype in H21.
            fold msig0 in msig1.
            subst msig1.
            eapply qualifier_typable_trans_subtype; [exact Hrorettypequalifier| | exact H21].
            apply qualified_type_subtype_q_subtype in Hsubtype_ret.
            unfold msig0 in Hsubtype_ret.
            assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H14.
          exact H14.
        }

        assert (Hytypable: wf_r_typable CT rΓ h ly Ty). {
          eapply correspondence_to_typable; eauto.
        }
        unfold wf_r_typable in Hytypable.
        unfold r_type in Hytypable.
        unfold r_basetype in H0.
        destruct (runtime_getObj h ly).
        2:{easy.
        }
        destruct Hytypable as [HyBasetype _].
        inversion H0.
        rewrite H3 in HyBasetype.
        rewrite HyBasetype in mdeflookupcopy. 
            assert (mdef = mdef0). 
            {
              eapply find_overriding_method_deterministic; eauto.
            }
            subst mdef.
            exact Hsubtype_ret.
          }
          unfold runtime_getVal in Hmet_val.
          rewrite H6 in Hmet_val.
          easy.
      - (* Case: i ≠ x (unchanged variable) *)
        rewrite HeqrΓ'''.
        simpl.
        unfold runtime_getVal.
        rewrite update_diff; [symmetry; exact Hneq|].
        specialize (Hcorrinit i Hi sqt Hnth).
        unfold runtime_getVal in Hcorrinit.
        destruct (nth_error (vars rΓ) i) as [v|] eqn:Hgetval; [|exact Hcorrinit].
        destruct v as [|loc]; [trivial|].
        (* Need to show wf_r_typable is preserved when changing runtime environment and heap *)
        unfold wf_r_typable in Hcorrinit |- *.
        destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
        (* destruct (get_this_var_mapping (vars rΓ)) as [ι'|] eqn:Hthis; [|contradiction]. *)
        (* destruct (r_muttype h ι') as [q|] eqn:Hmut; [|contradiction]. *)
        assert (Hrtype_preserved : r_type h' loc = Some rqt).
        {
          eapply eval_stmt_preserves_r_type; eauto.
          unfold r_type in Hrtype.
          destruct (runtime_getObj h loc) as [obj|] eqn:Hobjloc; [|discriminate].
          apply runtime_getObj_dom in Hobjloc.
          exact Hobjloc.
        }
        (* assert (Hthis_preserved : get_this_var_mapping (update x retval (vars rΓ)) = Some ι'). *)
        {
          (* unfold get_this_var_mapping in Hthis |- *. *)
          (* destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|]. *)
          (* simpl in Hthis |- *. *)
          unfold update.
          destruct x as [|x'].
          contradiction Hneq.
          easy.
          simpl.
          (* exact Hthis. *)
        (* } *)
        (* assert (Hmut_preserved : r_muttype h' ι' = Some q).
        {
          eapply eval_stmt_preserves_r_muttype; eauto.
          unfold r_muttype in Hmut.
          destruct (runtime_getObj h ι') as [obj|] eqn:Hobjl; [|discriminate].
          apply runtime_getObj_dom in Hobjl.
          exact Hobjl.
        } *)
        rewrite Hrtype_preserved.
        (* rewrite Hthis_preserved. *)
        (* rewrite Hmut_preserved. *)
        exact Hcorrinit.
    }
    }
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hwf_classtable _].
    exact Hwf_classtable.
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hclass [Hheap _]].
    unfold wf_heap in Hheap.
    unfold r_basetype in H0.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobj; [|discriminate].
    injection H0 as Hcy_eq.
    subst cy.
    assert (Hly_dom : ly < dom h) by (apply runtime_getObj_dom in Hobj; exact Hobj).
    specialize (Hheap ly Hly_dom).
    unfold wf_obj in Hheap.
    rewrite Hobj in Hheap.
    destruct Hheap as [Hwf_rtypeuse _].
    unfold wf_rtypeuse in Hwf_rtypeuse.
    destruct (bound CT (rctype (rt_type obj))) as [class_def|] eqn:Hbound.
    - destruct Hwf_rtypeuse as [Hwf_rtypeuse _]. exact Hwf_rtypeuse.
    - contradiction.
  }
  - (* Case: stmt = Skip *)
    intros.
    inversion Htyping; subst.
    exact Hwf.
  - (* Case: stmt = Local *)
    intros.
    inversion Htyping; subst.
    unfold wf_r_config in *.
    destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) 
    unfold  wf_class_table in Hclass. destruct Hclass as [Hclass _]. exact Hclass.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ Hclassnamematch]. apply Hclassnamematch.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ Hclassnamematch]. apply Hclassnamematch.
    + (* wellformed heap *) exact Hheap.
    + (* Length of runtime environment greater than 0 *)
    simpl. rewrite length_app. simpl. lia.
    + (* The first element of runtime environment is not null *)
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      destruct Hreceiverval as [iot Hiot].
      exists iot.
      simpl.
      unfold gget in *.
      destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
      * (* Case: vars rΓ = [] *)
        exfalso.
        (* rewrite Hvars in HrEnvLen. *)
        simpl in HrEnvLen.
        lia.
      * (* Case: vars rΓ = v0 :: vs *)
        simpl.
        exact Hiot.
    + (* wellformed runtime environment *)  
    unfold wf_renv in *.
    simpl.
    apply Forall_app.
    split.
    * destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]]. exact Hallvals.
    * constructor.
      -- trivial.
      -- constructor.  
    + (* Length of static environment greater than 0 *)
    destruct Hsenv as [HsenvLength HsenvWellTyped]. rewrite length_app.
    simpl. lia.
    + (* wellformed static environment *)
      unfold wf_senv in *. apply Forall_app. split.
      * destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvWellTyped.
      *
        constructor.
        -- exact H3. (* assuming H is the wellformedness of T *)
        -- constructor. (* empty tail is well-typed *)
    + (* length equality *)
      simpl. rewrite length_app. simpl. rewrite Hlen. rewrite length_app. simpl. lia.
    + (* correspondence between static and runtime environments *)
      intros i Hi sqt Hnth.
      destruct (Nat.eq_dec i (dom sΓ)) as [Heq | Hneq].
      * (* Case: i = dom sΓ (new variable) *)
        subst i.
        unfold runtime_getVal.
        simpl.
        rewrite nth_error_app2.
        -- rewrite Hlen.
           trivial.
        -- rewrite Hlen.
           assert (dom (vars rΓ) - dom (vars rΓ) = 0) by lia.
            rewrite H0.
            simpl.
            trivial.
      * (* Case: i < dom sΓ (existing variable) *)
        assert (Hi_old : i < dom sΓ).
        {
          simpl in Hi. rewrite length_app in Hi. simpl in Hi.
          lia.
        }
        assert (Hnth_old : nth_error sΓ i = Some sqt).
        {
          have Happ := nth_error_app1 sΓ [T] Hi_old.
          rewrite Happ in Hnth.
          exact Hnth.
        }
        specialize (Hcorr i Hi_old sqt Hnth_old).
        unfold runtime_getVal in *.
        simpl.
        rewrite nth_error_app1.
        -- rewrite <- Hlen. exact Hi_old.
        --
           destruct (nth_error (vars rΓ) i) as [v|] eqn:Hgetval.
           ++ (* Case: nth_error (vars rΓ) i = Some v *)
              destruct v as [|loc].
              ** trivial.
              ** unfold wf_r_typable in *. simpl.
              assert (get_this_var_mapping (vars rΓ ++ [Null_a]) = get_this_var_mapping (vars rΓ)).
              {
                unfold get_this_var_mapping.
                destruct (vars rΓ) as [|v0 vs]; reflexivity.
              }
              (* rewrite H0. *)
              exact Hcorr.
           ++ (* Case: nth_error (vars rΓ) i = None *)
              exfalso.
              apply nth_error_None in Hgetval.
              rewrite <- Hlen in Hgetval.
              lia.
  - (* Case: stmt = VarAss *)
    intros.
    inversion Htyping; subst.
    have Hwfcopy := Hwf.
    revert Hwfcopy.
    unfold wf_r_config in Hwf.
    intros.
    unfold wf_r_config.
    destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) 
    unfold  wf_class_table in Hclass. destruct Hclass as [Hclass _]. exact Hclass.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ Hclassnamematch]. apply Hclassnamematch.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ Hclassnamematch]. apply Hclassnamematch.
    + (* wellformed heap *) exact Hheap.
    + (* Length of runtime environment greater than 0 *)
      simpl. destruct Hsenv as [HsenvLength HsenvWellTyped].      
      rewrite update_length.
      rewrite <- Hlen.
      exact HsenvLength.
    + (* The first element of runtime environment is not null *)
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      destruct Hreceiverval as [iot Hiot].
      exists iot.
      simpl.
      unfold gget in *.
      destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
      * (* Case: vars rΓ = [] *)
        exfalso.
        (* rewrite Hvars in HrEnvLen. *)
        simpl in HrEnvLen.
        lia.
      * (* Case: vars rΓ = v0 :: vs *)
        destruct x as [|x'].
           -- (* x = 0 *) contradiction.
           -- (* x = S x' *)
              simpl. (* update (S x') v2 (v0 :: vs) = v0 :: update x' v2 vs *)
              exact Hiot.
    + (* wellformed runtime environment *)
    unfold wf_renv in *.
    destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
    simpl.
    apply Forall_update.
    * exact Hallvals.
    * destruct v2 as [|loc].
      -- trivial.
      -- inversion H0; subst.
        (* assert (Hloc_in_vars : exists i, nth_error (vars rΓ) i = Some (Iot loc)). *)
        ++ 
        assert (Hx0_bound : x0 < dom (vars rΓ)).
        {
          apply runtime_getVal_dom in H1.
          exact H1.
        }
        assert (Hloc_wf : match runtime_getObj h loc with Some _ => True | None => False end).
        {
          unfold runtime_getVal in H1.
          assert (Hnth_loc : nth_error (vars rΓ) x0 = Some (Iot loc)) by exact H1.
          eapply Forall_nth_error in Hallvals; eauto.
          simpl in Hallvals.
          exact Hallvals.
        }
        exact Hloc_wf.
        ++ 
        assert (Hv_bound : v < dom h).
        {
          apply runtime_getVal_dom in H1.
          unfold runtime_getVal in H1.
          apply runtime_getObj_dom in H2.
          exact H2.
        }
        specialize (Hheap v Hv_bound).
        unfold wf_obj in Hheap.
        rewrite H2 in Hheap.
        destruct Hheap as [_ [field_defs [Hcollect [Hlen_eq Hforall2]]]].
        assert (Hf_bound : f < List.length (fields_map o)).
        {
          apply nth_error_Some.
          unfold getVal in H6.
          rewrite H6.
          discriminate.
        }
        rewrite Hlen_eq in Hf_bound.
        assert (Hfield_def : exists fdef, nth_error field_defs f = Some fdef).
        {
          apply nth_error_Some_exists.
          exact Hf_bound.
        }
        destruct Hfield_def as [fdef Hfdef].
        unfold getVal in H6.
        eapply Forall2_nth_error in Hforall2; eauto.
        simpl in Hforall2.
        destruct (runtime_getObj h loc) as [obj|] eqn:Hloc_obj.
        --- (* Case: runtime_getObj h loc = Some obj *)
          trivial.
        --- (* Case: runtime_getObj h loc = None *)
          contradiction Hforall2.
    * apply runtime_getVal_dom in H.
      exact H.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvLength. 
    + (* wellformed static environment *)
      destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvWellTyped.
    + (* length equality *)
      simpl.
      rewrite update_length.
      exact Hlen.
    + (* correspondence between static and runtime environments *)
      intros i Hi sqt Hnth.
      destruct (Nat.eq_dec i x) as [Heq | Hneq].
      * (* Case: i = x (updated variable) *)
        subst i.
        unfold runtime_getVal.
        simpl.
        rewrite update_same.
        (* Need to show v2 is well-typed with respect to T' *)
        (* assert (Hsubtype: qualified_type_subtype CT Te Tx) by exact H3.
        assert (Hexpr_type: expr_has_type CT sΓ e Te) by exact H0. *)
        rewrite <- Hlen; exact Hi.
        destruct v2 as [|loc].
        -- (* Case: v2 = Null_a *)
          trivial.
        -- (* Case: v2 = Iot loc *)
          (* Use subtyping to convert from T to sqt *)
          assert (Hsubtype_preserved : wf_r_typable CT (rΓ <| vars := update x (Iot loc) (vars rΓ) |>) h loc sqt).
          {
            assert (Hsqt_eq : sqt = Tx).
          {
            unfold static_getType in H8.
            rewrite H8 in Hnth.
            injection Hnth as Hsqt_eq.
            symmetry. exact Hsqt_eq.
          }
          subst sqt.
          assert (H_loc_Te : wf_r_typable CT rΓ h loc Te).
          {
            (* Apply expression evaluation preservation lemma *)
            apply (expr_eval_preservation CT sΓ' rΓ h e (Iot loc) rΓ h Te).
            auto.
            - exact H4.
            - exact H0.
             (* unfold wf_r_config. repeat split; eauto.  *)

            (* - exact Hqthis. *)
            (* - exact Hwfcopy.
            - exact H4.
            - exact H0. *)
          }  
            (* + wellformed class 
            unfold  wf_class_table in Hclass. destruct Hclass as [Hclass _]. exact Hclass.
            + (* Class identifier match*)
            unfold  wf_class_table in Hclass. destruct Hclass as [_ Hclassnamematch]. apply Hclassnamematch.
            + (* Class identifier match*)
            unfold  wf_class_table in Hclass. destruct Hclass as [_ Hclassnamematch]. apply Hclassnamematch.
            + unfold wf_renv in Hrenv. destruct Hrenv as [Hrenvdom _]. exact Hrenvdom.
            + unfold wf_renv in Hrenv. destruct Hrenv as [_ [Hreceiver Hrvals]]. exact Hreceiver.
            + unfold wf_renv in Hrenv. destruct Hrenv as [_ [Hreceiver Hrvals]]. exact Hrvals.
            + unfold wf_senv in Hsenv. destruct Hsenv as [Hsenvdom _]. exact Hsenvdom.
            + unfold wf_senv in Hsenv. destruct Hsenv as [Hsenvdom Htypable]. exact Htypable.
            - exact H4.
            - exact H0.
          } *)
          (* Use subtyping to convert Te to Tx *)
          eapply wf_r_typable_subtype; eauto.
          (* The environment update doesn't affect loc's typing since loc is fresh *)
          }
          unfold wf_r_typable in *.
          exact Hsubtype_preserved.
          (* destruct (r_type h' loc) as [rqt|] eqn:Hrtype; [|contradiction]. *)
          (* destruct (get_this_var_mapping (vars (rΓ <| vars := update x (Iot loc) (vars rΓ) |>))) as [ι'|] eqn:Hthis. *)
          (* - simpl in Hthis.
            (* The this variable (at position 0) is preserved in the update *)
            destruct (get_this_var_mapping (vars rΓ)) as [ι0|] eqn:Hthis_orig.
            + (* Apply subtyping transitivity *)
              assert (Hι'_eq : ι' = ι0).
            {
              unfold get_this_var_mapping in Hthis, Hthis_orig.
              destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
              - discriminate Hthis_orig.
              - destruct x as [|x'].
                + easy.
                + simpl in Hthis.
                  destruct v0 as [|loc_v0] eqn:Hv0.
            * (* v0 = Null_a *)
              discriminate Hthis_orig.
            * (* v0 = Iot loc_v0 *)
              simpl in Hthis, Hthis_orig.
              injection Hthis_orig as Heq_orig.
              injection Hthis as Heq.
              rewrite <- Heq_orig, <- Heq.
              reflexivity.
            }
            eapply expr_has_type_class_in_table; eauto.
            + eapply expr_has_type_class_in_table; eauto.
          - 
            unfold get_this_var_mapping in Hthis.
            simpl in Hthis.
            destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
            * (* Empty case - contradicts well-formedness *)
              unfold wf_renv in Hrenv.
              destruct Hrenv as [Hdom _].
              rewrite Hvars in Hdom.
              simpl in Hdom.
              lia.
            * (* Non-empty case *)
              destruct x as [|x'].
              + (* x = 0 contradicts H1 *)
                easy.
              + (* x = S x', so update preserves position 0 *)
                simpl in Hthis.
                unfold wf_renv in Hrenv.
                destruct Hrenv as [_ [Hreceiver _]].
                destruct Hreceiver as [iot [Hiot_gget Hiot_dom]].
                unfold gget in Hiot_gget.
                rewrite Hvars in Hiot_gget.
                simpl in Hiot_gget.
                injection Hiot_gget as Hv0_eq.
                subst v0.
                simpl in Hthis.
                discriminate Hthis.
          - apply senv_var_domain with (sΓ:=sΓ') (i:=x). exact H3. exact Hnth.
          - 
          unfold wf_r_typable in H_loc_Te |- *.
          destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
          destruct (get_this_var_mapping (vars rΓ)) as [ι0|] eqn:Hthis_orig; [|contradiction].
          destruct (r_muttype h ι0) as [q|] eqn:Hmut; [|contradiction].
          assert (Hthis_preserved : get_this_var_mapping (vars (rΓ <| vars := update x (Iot loc) (vars rΓ) |>)) = Some ι0).
          {
            simpl.
            unfold get_this_var_mapping in Hthis_orig |- *.
            destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
            - discriminate Hthis_orig.
            - destruct x as [|x'].
              + easy.
              + simpl. exact Hthis_orig.
          }
          rewrite Hthis_preserved.
          rewrite Hmut.
          exact H_loc_Te.
          }
          exact Hsubtype_preserved. *)
      * (* Case: i ≠ x (unchanged variable) *)
        {
          unfold runtime_getVal.
          simpl.
          rewrite update_diff.
          - symmetry. exact Hneq.
          - assert (Hcorr_orig := Hcorr i Hi sqt Hnth).
            unfold runtime_getVal in Hcorr_orig.
            destruct (nth_error (vars rΓ) i) as [v|] eqn:Hval.
            + destruct v as [|loc].
              * trivial.
              * unfold wf_r_typable in Hcorr_orig |- *.
                destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
                (* destruct (get_this_var_mapping (vars rΓ)) as [ι'|] eqn:Hthis; [|contradiction]. *)
                (* destruct (r_muttype h ι') as [q|] eqn:Hmut; [|contradiction]. *)
                (* assert (Hthis_preserved : get_this_var_mapping (update x v2 (vars rΓ)) = Some ι').
                {
                  unfold get_this_var_mapping in *.
                  destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
                  - discriminate Hthis.
                  - destruct x as [|x'].
                    + 
                    simpl.
                    destruct v2 as [|loc2].
                    -- (* Case: v2 = Null_a *)
                      exfalso.
                      contradiction H5.
                      reflexivity.
                    -- (* Case: v2 = Iot loc2 *)
                      simpl.
                      destruct v0 as [|loc0].
                      ++ (* Case: v0 = Null_a *)
                        discriminate Hthis.
                      ++ (* Case: v0 = Iot loc0 *)
                        easy.
                    + simpl. exact Hthis.
                } *)
                (* rewrite Hthis_preserved. *)
                (* rewrite Hmut. *)
                exact Hcorr_orig.
            + contradiction.
        }
  - (* Case: stmt = FldWrite *)
    intros.
    inversion Htyping; subst.
    unfold wf_r_config in *.
    destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) 
    unfold  wf_class_table in Hclass. destruct Hclass as [Hclass _]. exact Hclass.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ Hclassnamematch]. apply Hclassnamematch.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ Hclassnamematch]. apply Hclassnamematch.
    + (* wellformed heap *) 
    unfold wf_heap in *.
    intros ι0 Hdom.
    unfold update_field in *.
    destruct (runtime_getObj h loc_x) as [o_x|] eqn:Hobj.
    * (* Case: object exists at lx *)
      destruct (Nat.eq_dec ι0 loc_x) as [Heq | Hneq].
      -- (* Case: ι = lx (the updated object) *)
        subst ι0.
        unfold wf_obj.
        simpl.
        specialize (Hheap loc_x).
        rewrite update_length in Hdom.
        specialize (Hheap Hdom).
        unfold wf_obj in Hheap.
        rewrite Hobj in Hheap.
        destruct Hheap as [Hrtypeuse [Hlen_fields Hwf_fields]].
        unfold runtime_getObj.
        rewrite update_same.
        ++ exact Hdom.
        ++ repeat split.
          ** exact Hrtypeuse.
          ** simpl. rewrite update_length. 
          exists Hlen_fields.
          destruct Hwf_fields as [Hcollect [Hlen_eq Hforall2]].
          split.
          --- exact Hcollect.
          --- split.
            +++ exact Hlen_eq.
            +++ 
            {
              apply Forall2_update.
              eapply Forall2_impl; [|exact Hforall2].
              intros v fdef Hv_fdef.
              destruct v as [|loc]; [trivial|].
              destruct (runtime_getObj h loc) as [obj_at_loc|] eqn:Hobj_at_loc; [|contradiction Hv_fdef].
              destruct Hv_fdef as [rqt [Hrtype Hsubtype]].
              destruct (Nat.eq_dec loc loc_x) as [Heq_loc | Hneq_loc].
              (* Case: loc = lx *)
                subst loc.
                unfold update_field.
                simpl.
                rewrite update_same.
                apply runtime_getObj_dom in Hobj_at_loc.
                exact Hobj_at_loc.
                exists rqt.
                split.
              unfold r_type.
                simpl.
                rewrite runtime_getObj_update_same.
                simpl.
                apply runtime_getObj_dom in Hobj_at_loc.
                exact Hobj_at_loc.
                simpl.
                unfold r_type in Hrtype.
                rewrite Hobj_at_loc in Hrtype.
                injection Hrtype as Hrqt_eq.
                rewrite Hobj in Hobj_at_loc.
                injection Hobj_at_loc as Heq_objs.
                subst obj_at_loc.
                rewrite Hrqt_eq.
                reflexivity.
              exact Hsubtype.

              (* Case: loc ≠ lx *)
              rewrite update_diff; [symmetry; exact Hneq_loc |].
              unfold runtime_getObj in Hobj_at_loc.
              rewrite Hobj_at_loc.
              exists rqt.
              split.
              unfold r_type.
                rewrite runtime_getObj_update_diff; [symmetry; exact Hneq_loc|].
                unfold r_type in Hrtype.
                exact Hrtype.
              exact Hsubtype.
              assert (Hf_valid : f < dom (fields_map o_x)).
              {
                injection H0 as Ho_eq. subst o_x.
                apply getVal_dom in H1. exact H1.
              }
              rewrite <- Hlen_eq. exact Hf_valid.

              intros b Hnth_b.
              destruct val_y as [|loc_y]; [trivial|].

              assert (Hx_dom : x < dom sΓ').
              {
                apply static_getType_dom in H8. exact H8.
              }

              assert (Hy_dom : y < dom sΓ').
              {
                apply static_getType_dom in H9. exact H9.
              }
              have Hcorrcopy := Hcorr.
              specialize (Hcorr x Hx_dom Tx H8).
              destruct (runtime_getVal rΓ x) as [val_x|] eqn:Hx_val; [|contradiction].
              injection H as H_val_eq.
              subst val_x.
              unfold update_field.
              destruct (runtime_getObj h loc_x) as [o_lx|] eqn:Hobj_lx.
              2:{easy.
              }
              destruct (Nat.eq_dec loc_y loc_x) as [Heq_loc2_lx | Hneq_loc2_lx].
              specialize (Hcorrcopy y Hy_dom Ty H9).
              destruct (runtime_getVal rΓ y) as [val_y|] eqn:Hy_val; [|contradiction].
              injection H2 as H_val_eq.
              subst val_y.
              unfold update_field.
              (* subst loc_y. *)
              destruct (runtime_getObj h loc_y) as [o_ly|] eqn:Hobj_ly.
              2:{
                subst loc_y.
                rewrite Hobj_lx in Hobj_ly.
                easy.
              }
                (* Case: loc_y = loc_x *)
                subst loc_y.
                unfold runtime_getObj.
                rewrite update_same; [exact Hdom|].
                unfold wf_r_typable in Hcorr.
                destruct (r_type h loc_x) as [rqt_x|] eqn:Hrtype_x; [|contradiction Hcorr].
                (* destruct (get_this_var_mapping (vars rΓ)) as [ι'|] eqn:Hthis_var; [|contradiction Hcorr]. *)
                (* destruct (r_muttype h ι') as [q|] eqn:Hmut; [|contradiction Hcorr]. *)
                destruct Hcorr as [Hbase_sub Hqual_typable].
                exists rqt_x.
                split.
                  unfold r_type.
                  unfold runtime_getObj.
                  rewrite update_same; [exact Hdom|].
                  simpl.
                  unfold r_type in Hrtype_x.
                  rewrite Hobj_lx in Hrtype_x.
                  injection Hobj as Ho_eq.
                  injection H0 as Ho_eq2.
                  subst o_lx o_x.
                  exact Hrtype_x.
                  injection Hobj as Ho_lx_eq.
                  injection H0 as Ho_x_eq.
                  subst o_lx o_x.
                  assert (Hrt_type_eq : rt_type o = rqt_x).
                  {
                    unfold r_type in Hrtype_x.
                    rewrite Hobj_lx in Hrtype_x.
                    injection Hrtype_x as Heq.
                    exact Heq.
                  }

                  rewrite Hrt_type_eq in Hcollect.
                  assert (fieldT = b). {
                    unfold sf_def_rel in H10.
                    inversion H10;subst.
                    symmetry.
                    eapply collect_fields_consistent_through_runtime_static with (C:=(rctype (rt_type o)))(fields1:=Hlen_fields)(fields2:=fields)(fdef1:=b)(fdef2:=fieldT); eauto.
                  }

                  subst b.
              (* Case: loc2 ≠ lx *)
                  rewrite Hobj_lx in Hobj_ly.
                  inversion Hobj_ly.
                  subst o_ly.
                  unfold wf_r_typable in Hcorrcopy.
                  rewrite Hrtype_x in Hcorrcopy.
                  destruct Hcorrcopy as [Hxybase Hxyqualifer].
                  {
                  constructor.
                  (* Base type *)
                  apply qualified_type_subtype_base_subtype in H15.
                  simpl in H15.
                  rewrite <- H15.
                  exact Hxybase.

                  (* Qualifier *)
                  apply qualified_type_subtype_q_subtype in H15.
                  simpl in H15.
                  unfold qualifier_typable_heap.
                  move H15 at bottom.
                  move Hqual_typable at bottom.
                  subst rqt_x.
                  destruct (rqtype (rt_type o)).
                  all: destruct (mutability (ftype fieldT)) eqn: HfieldMut.
                  all: unfold vpa_mutabilty_rec_fld.
                  all: try easy.
                  all: destruct (sqtype Tx).
                  all: unfold vpa_mutabilty_stype_fld in H15.
                  all: destruct (sqtype Ty).
                  all: try inversion H15.
                  all: try easy.
                  }

                  have H15copy := H15.
                  apply qualified_type_subtype_q_subtype in H15. 
                  simpl in *.
                  destruct (nth_error h loc_y) as [obj_y|] eqn:Hnth_y.
                  - (* loc_y exists in original heap *)
                    assert (Hnth_updated : nth_error (update loc_x (o_x <| fields_map := update f (Iot loc_y) (fields_map o_x) |>) h) loc_y = Some obj_y).
                    {
                      rewrite nth_error_update_neq; [symmetry; exact Hneq_loc2_lx | exact Hnth_y].
                    }
                    rewrite Hnth_updated.
                    specialize (Hcorrcopy y Hy_dom Ty H9).
                    rewrite H2 in Hcorrcopy.
                    unfold wf_r_typable in Hcorrcopy.
                    destruct (r_type h loc_y) as [rqt_y|] eqn:Hrtype_y; [|contradiction].
                    destruct Hcorrcopy as [Hbase_y Hqual_y].

                    exists rqt_y.
                    split.

                    unfold r_type.
                    unfold runtime_getObj.
                    rewrite Hnth_updated.
                    unfold r_type in Hrtype_y.
                    unfold runtime_getObj in Hrtype_y.
                    rewrite Hnth_y in Hrtype_y.
                    exact Hrtype_y.
                    assert (fieldT = b). {
                      unfold sf_def_rel in H10.
                      inversion H10;subst.
                      symmetry.
                      eapply collect_fields_consistent_through_runtime_static with (C:=(rctype (rt_type o_x)))(fields1:=Hlen_fields)(fields2:=fields)(fdef1:=b)(fdef2:=fieldT); eauto.
                      apply qualified_type_subtype_base_subtype in H15copy.
                      simpl in H15copy.
                      unfold wf_r_typable in Hcorr.
                      unfold r_type in Hcorr.
                      rewrite Hobj_lx in Hcorr.
                      destruct Hcorr as [Hbase_sub Hqual_typable].
                      inversion Hobj.
                      subst o_lx.
                      rewrite Hbase_sub.
                      exact H.
                    }
                    subst b.
                    split.
                    + (* Base type equality *)
                      apply qualified_type_subtype_base_subtype in H15copy.
                      simpl in H15copy.
                      rewrite <- H15copy.
                      exact Hbase_y.
                    + (* Qualifier typable *)
                      move H15 at bottom.
                      inversion H0.
                      inversion Hobj.
                      subst.
                      unfold qualifier_typable_heap.
                      unfold qualifier_typable in Hqual_y.
                      unfold wf_r_typable in Hcorr.
                      unfold r_type in Hcorr.
                      rewrite Hobj_lx in Hcorr.
                      destruct Hcorr as [_ Hqualifiertypablex].
                      all: destruct (rqtype rqt_y) eqn: Hrqy.
                      all: destruct (rqtype (rt_type o)) eqn: Hrqx.
                      all: destruct (mutability (ftype fieldT)) eqn: Hfield.
                      all: destruct (sqtype Ty) eqn: Hsqy.
                      all: unfold vpa_mutabilty_rec_fld; try easy.
                      all: destruct (sqtype Tx) eqn: Hsqx; unfold vpa_mutabilty_stype_fld in H15; try inversion H15; try easy.
                  - (* loc_y doesn't exist - contradiction *)
                    assert (Hnth_updated : nth_error (update loc_x (o_x <| fields_map := update f (Iot loc_y) (fields_map o_x) |>) h) loc_y = None).
                    {
                      rewrite nth_error_update_neq; [symmetry; exact Hneq_loc2_lx | exact Hnth_y].
                    }
                    rewrite Hnth_updated.
                    exfalso.
                    specialize (Hcorrcopy y Hy_dom Ty H9).
                    rewrite H2 in Hcorrcopy.
                    unfold wf_r_typable in Hcorrcopy.
                    unfold r_type in Hcorrcopy.
                    unfold runtime_getObj in Hcorrcopy.
                    rewrite Hnth_y in Hcorrcopy.
                    easy.
            }
        -- unfold wf_obj, runtime_getObj.
        rewrite update_diff.
        ** rewrite update_length in Hdom.
          symmetry. exact Hneq.
        **
        rewrite update_length in Hdom.
        destruct (nth_error h ι0) eqn:Htest.
        2:{
          exfalso.
          apply nth_error_None in Htest.
          lia.
        }
        split.
        specialize (Hheap ι0 Hdom).
        unfold wf_obj in Hheap.
        destruct (runtime_getObj h ι0) as [objl|] eqn: Hobjl; [| easy].
        destruct Hheap as [Hwfobjtypeuse _].
        unfold runtime_getObj in Hobjl.
        rewrite Htest in Hobjl.
        inversion Hobjl.
        subst.
        exact Hwfobjtypeuse.

        specialize (Hheap ι0 Hdom).
        unfold wf_obj in Hheap.
        destruct (runtime_getObj h ι0) as [objl|] eqn: Hobjl; [| easy].
        destruct Hheap as [Hwfobjtypeuse Hwfobjfields].
        unfold runtime_getObj in Hobjl.
        rewrite Htest in Hobjl.
        inversion Hobjl.
        subst.
        destruct Hwfobjfields as [field_defs [Hcollect [Hlen_eq Hforall2]]].

        exists field_defs.
        {
          split.
          exact Hcollect.
          split.
          exact Hlen_eq.
          eapply Forall2_impl; [|exact Hforall2].
          intros v fdef Hv_fdef.
          destruct v as [|loc]; [trivial|].
          (* First check if the object exists in the updated heap *)
          unfold update_field.
          destruct (runtime_getObj h loc_x) as [o_lx|] eqn:Hobj_lx.
            destruct (Nat.eq_dec loc loc_x) as [Heq | Hneq_loc].
              subst loc.
              rewrite Hobj_lx in Hv_fdef.
            destruct Hv_fdef as [rqt [Hrtype_loc Hsubtype]].
            unfold runtime_getObj.
            rewrite update_same.
            unfold r_type in Hrtype_loc.
            unfold r_type in Hrtype_loc.
            destruct (runtime_getObj h loc_x) as [oxx|] eqn:Hobj_lxx; [|discriminate Hrtype_loc].
            apply runtime_getObj_dom in Hobj_lxx.
            exact Hobj_lxx.
            exists rqt.
              split.
                unfold r_type.
                rewrite runtime_getObj_update_same.
                apply runtime_getObj_dom in Hobj_lx. exact Hobj_lx.
                 simpl.
                  unfold r_type in Hrtype_loc.
                  rewrite Hobj_lx in Hrtype_loc.
                  injection Hobj as Ho_new_eq.
                  subst o_x.
                  injection Hrtype_loc as Hrqt_eq.
                  subst rqt.
                  reflexivity.
                exact Hsubtype.
            destruct (runtime_getObj h loc) as [obj_loc|] eqn:Hobj_loc; [|contradiction Hv_fdef].
            destruct Hv_fdef as [rqt [Hrtype_loc Hsubtype]].
            unfold runtime_getObj.
            rewrite update_diff.
            symmetry. exact Hneq_loc.
            unfold runtime_getObj in Hobj_loc.
          destruct (nth_error h loc) as [obj|] eqn:Hnth_loc; [|discriminate Hobj_loc].
          injection Hobj_loc as Hobj_eq.
          subst obj.
          exists rqt.
          split.
            unfold r_type.
            rewrite runtime_getObj_update_diff.
            symmetry. exact Hneq_loc.
            exact Hrtype_loc.
            exact Hsubtype.
            exfalso.
            discriminate Hobj.
        }
        * exfalso.
        discriminate H0.
    + destruct Hrenv as [HrEnvLen [Hreceiver Hallvals]]. exact HrEnvLen.
    + destruct Hrenv as [HrEnvLen [Hreceiver Hallvals]]. destruct Hreceiver as [Hreceiverval Hreceivervaldom].
      exists Hreceiverval.
      split.
      * exact (proj1 Hreceivervaldom).
      * rewrite update_field_length.
        exact (proj2 Hreceivervaldom).
    + 
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      eapply Forall_impl; [| exact Hallvals].
      intros v Hv.
      destruct v as [|loc]; [trivial|].
      unfold update_field in Hv |- *.
      destruct (runtime_getObj h loc_x) as [o'|] eqn:Hobj'; [| exact Hv].
      destruct (Nat.eq_dec loc loc_x) as [Heq | Hneq].
      * subst loc. rewrite runtime_getObj_update_same; [trivial | ].
        apply runtime_getObj_dom in Hobj'. exact Hobj'. trivial.
      * 
      unfold runtime_getObj.
      rewrite update_diff.
      -- symmetry. exact Hneq.
      -- auto.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvLength.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvWellTyped.
    + exact Hlen.
    + 
    intros i Hi sqt Hnth.
      assert (Hcorr_orig := Hcorr i Hi sqt Hnth).
      destruct (runtime_getVal rΓ i) as [v|] eqn:Hval; [|exact Hcorr_orig].
      destruct v as [|loc]; [trivial|].
      (* Need to show: wf_r_typable CT rΓ' (update_field h lx f v2) loc sqt *)
      unfold wf_r_typable in Hcorr_orig |- *.
      destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
      (* destruct (get_this_var_mapping (vars rΓ)) as [ι'|] eqn:Hthis; [|contradiction]. *)
      (* destruct (r_muttype h ι') as [q|] eqn:Hmut; [|contradiction]. *)
      (* Show that r_type and r_muttype are preserved by update_field *)
      assert (Hrtype_preserved : r_type (update_field h loc_x f val_y) loc = Some rqt).
      {
        unfold r_type.
        unfold update_field.
        (* have H12_copy := H12. *)
        remember (runtime_getObj h loc_x) as obj_result eqn:Hobj_eq.
        destruct obj_result as [o'|].
        - destruct (Nat.eq_dec loc loc_x) as [Heq | Hneq].
          + subst loc. 
            rewrite runtime_getObj_update_same.
            * simpl. unfold r_type in Hrtype.
              destruct (runtime_getObj h loc_x) as [o_lx|] eqn:Hobj_lx; [|discriminate Hrtype].
              apply runtime_getObj_dom in Hobj_lx.
              exact Hobj_lx.
            * 
            have Hobj_eq_copy := Hobj_eq.
            symmetry in Hobj_eq.
            apply runtime_getObj_dom in Hobj_eq.
            simpl.
            unfold r_type in Hrtype.
            destruct (runtime_getObj h loc_x) as [o_lx|] eqn:Hobj_lx; [|discriminate Hrtype].
            injection Hrtype as Hrtype_eq.
            rewrite <- Hrtype_eq.
            (* injection H12 as Ho'_eq. *)
            (* subst o'. *)
            f_equal.
            injection Hobj_eq_copy as Ho_eq.
            rewrite Ho_eq.
            reflexivity.
          + rewrite runtime_getObj_update_diff.
            * symmetry. exact Hneq.
            * exact Hrtype.
        - exact Hrtype.
      }
      (* assert (Hmut_preserved : r_muttype (update_field h loc_x f val_y) ι' = Some q).
      {
        unfold r_muttype, update_field.
        destruct (runtime_getObj h loc_x) as [o'|] eqn:Hobj'; [|exact Hmut].
        destruct (Nat.eq_dec ι' loc_x) as [Heq | Hneq].
        subst ι'.
        rewrite runtime_getObj_update_same.
        - simpl. unfold r_muttype in Hmut.
        destruct (runtime_getObj h loc_x) as [otest|] eqn:Hobj; [|discriminate Hmut].
        apply runtime_getObj_dom in Hobj. exact Hobj.
        - simpl.
        unfold r_muttype in Hmut.
        rewrite Hobj' in Hmut.
        exact Hmut.
        -
        {
          rewrite runtime_getObj_update_diff.
          - symmetry. exact Hneq.
          - exact Hmut.
        }
      } *)
      rewrite Hrtype_preserved.
      (* rewrite Hmut_preserved. *)
      exact Hcorr_orig.
  - (* Case: stmt = New *)
    intros.
    inversion Htyping.
    have Hwf_copy := Hwf.
    unfold wf_r_config.
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) 
        unfold  wf_class_table in Hclass. destruct Hclass as [Hclass _]. exact Hclass.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ Hclassnamematch]. apply Hclassnamematch.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ Hclassnamematch]. apply Hclassnamematch.
    + (* wellformed heap *) 
    unfold wf_heap.
    intros ι0 Hι.
    subst.
    rewrite length_app in Hι.
    simpl in Hι.
    destruct (Nat.eq_dec ι0 (dom h)) as [Heq | Hneq].
    * (* ι = dom h (new object) *)
      subst.
      unfold wf_obj.
      rewrite runtime_getObj_last.
      split.
      -- (* wf_rtypeuse for new object *)
        simpl.
        unfold wf_rtypeuse.
        destruct (bound CT c) as [q_c_val|] eqn:Hbound.
        ++ unfold constructor_def_lookup in H10.
        destruct (find_class CT c) as [def|] eqn:Hfind.
        ** apply find_class_dom in Hfind.
          split.
          exact Hfind.
          unfold vpa_mutabilty_runtime_bound_agree.
          (* assert (Hexists_ctor : exists ctor, constructor_sig_lookup CT c = Some ctor).
          {
            eapply constructor_sig_lookup_implies_def in H10.
            destruct H10 as [ctor [Hctor_def _]].
            exists ctor. exact Hctor_def.
          } *)
          (* destruct Hexists_ctor as [ctor Hctor_def]. *)
          assert (Hwf_ctor : wf_constructor CT c consig).
          {
            eapply constructor_lookup_wf; eauto.
          }
          inversion Hwf_ctor; subst.
          rewrite Hbound in H0.
          inversion H0.
          destruct H1 as [Hparamswf [field_defs [Hcollect_H1 [Hdom_eq Hfieldtypematch]]]].
          (* subst q_c0. *)
          (* fold body in body0. *)
          (* subst body0. *)
          (* rewrite H0 in H10. *)
          (* inversion H10. *)
          (* subst consig. *)
          (* fold sig0 in sig. *)
          (* subst sig0. *)
          destruct q_c eqn: Hnewobjctqualifier; destruct (cqualifier consig) eqn: Hcbound; try reflexivity.
          all: unfold q_r_proj in H16.
          all: unfold vpa_mutabilty_bound in H16.
          (* all: fold consig in H16. *)
          all: move H16 at bottom.
          all: easy.
        ** exfalso.
        unfold bound in Hbound.
        rewrite Hfind in Hbound.
        discriminate Hbound.
        ++ 
          unfold constructor_sig_lookup in H10.
          destruct (constructor_def_lookup CT c) as [ctor|] eqn:Hctor.
          ** unfold constructor_def_lookup in Hctor.
            destruct (find_class CT c) as [def|] eqn:Hfind.
            --- unfold bound in Hbound.
              rewrite Hfind in Hbound.
              discriminate Hbound.
            --- discriminate Hctor.
          ** discriminate H10.
      --
        {
          assert (Hc_dom : c < dom CT).
   {
     apply constructor_sig_lookup_dom in H10.
     exact H10.
   }
   
   (* Collect fields for class c *)
   assert (Hexists_fields : exists field_defs, CollectFields CT c field_defs).
   {
     eapply collect_fields_exists; eauto.
   }
   destruct Hexists_fields as [field_defs Hcollect_fields].
   
   exists field_defs.
   split.
   + (* CollectFields CT c field_defs *)
     exact Hcollect_fields.
   + split.
     * (* Length equality: dom vals = dom field_defs *)
       (* This follows from constructor well-formedness *)
       (* The constructor should ensure vals has the right length *)
       simpl.
       apply Forall2_length in H17.
       apply runtime_lookup_list_preserves_length in H.
       apply static_getType_list_preserves_length in H9.
      rewrite H.
      rewrite <- H9.
      rewrite H17.
      eapply constructor_sig_lookup_implies_def in H10; eauto.
      destruct H10 as [cdef Hcedflookup].
      destruct Hcedflookup as [Hcedflookup Hcdefcsig].
      eapply constructor_params_field_count; eauto.
     * (* Forall2 property *)
       apply runtime_lookup_list_preserves_typing with (CT:= CT) (h := h) (sΓ := sΓ') (args := ys) (argtypes := argtypes) in H; auto.
       simpl.
       (* assert (Hexists_ctor : exists ctor, constructor_def_lookup CT c = Some ctor).
        {
          eapply constructor_sig_lookup_implies_def in H10.
          destruct H10 as [ctor [Hctor_def _]].
          exists ctor. exact Hctor_def.
        } *)
        (* destruct Hexists_ctor as [ctor Hctor_def]. *)
        assert (Hwf_ctor : wf_constructor CT c consig).
        {
          eapply constructor_lookup_wf; eauto.
        }
        inversion Hwf_ctor; subst.
        (* fold sig in sig0;
        subst sig0. *)
        (* fold body in body0;
        subst body0. *)
        unfold wf_heap in Hheap.
        unfold wf_obj in Hheap.
        eapply Forall2_from_nth.
        - (* Show lengths are equal *)
        apply Forall2_length in H.
        rewrite H.
        destruct H1 as [Hparamswf [field_defs_exists [Hcollect_H1 [Hdom_eq Hfieldtypematch]]]].
        apply Forall2_length in H17.
        rewrite H17.
        assert (field_defs_exists = field_defs). {
          eapply collect_fields_deterministic_rel; eauto.
        }
        subst field_defs_exists.
        exact Hdom_eq.
        - (* Show pointwise property *)
          intros i v fdef Hi Hv Hfdef.
          destruct v; [easy|].
          {
            assert (Hargtype : exists argtype, nth_error argtypes i = Some argtype).
        {
          apply Forall2_length in H.
          (* apply runtime_lookup_list_preserves_length in H. *)
          rewrite H in Hi.
          apply nth_error_Some_exists in Hi.
          exact Hi.
        }
        destruct Hargtype as [argtype Hargtype].
        eapply Forall2_nth_error in H; [|exact Hv|exact Hargtype].
        simpl in H.
        unfold wf_r_typable in H.
        destruct (r_type h l) as [rqt|] eqn:Hrtype; [|contradiction].
        assert (Hl_dom : l < dom h).
        {
          unfold r_type in Hrtype.
          destruct (runtime_getObj h l) as [obj|] eqn:Hobj; [|discriminate].
          apply runtime_getObj_dom in Hobj.
          exact Hobj.
        }
        rewrite runtime_getObj_last2; auto.
        destruct (runtime_getObj h l) eqn: Hl.
        2:{apply runtime_getObj_not_dom in Hl. lia.
        }
        exists rqt.
        split.
        - unfold r_type.
          rewrite runtime_getObj_last2; auto.
        - destruct H1 as [Hparamswf [field_defs_exists [Hcollect_H1 [Hdom_eq Hfieldtypematch]]]].
        assert (field_defs_exists = field_defs). {
          eapply collect_fields_deterministic_rel; eauto.
        }
        subst field_defs_exists.
        split.
          +
        destruct H as [Hrctype _].
        rewrite Hrctype.
        destruct (nth_error (cparams consig) i) as [paramtype|] eqn: Hparamtype.
        2:{
          apply nth_error_None in Hparamtype.
          assert (Hi_fdef : i < dom field_defs).
        {
          apply nth_error_Some.
          rewrite Hfdef.
          discriminate.
        }
        rewrite <- Hdom_eq in Hi_fdef.
        lia.
        }
        eapply Forall2_nth_error with (i:=i) (b:=fdef) (a:=paramtype) in Hfieldtypematch.
        apply qualified_type_subtype_base_subtype in Hfieldtypematch.
        simpl in Hfieldtypematch.
        rewrite <- Hfieldtypematch.
        eapply Forall2_nth_error with (i:=i) (b:=paramtype) (a:=argtype) in H17.
        apply qualified_type_subtype_base_subtype in H17.
        exact H17.
        exact Hargtype.
        exact Hparamtype.
        exact Hparamtype.
        exact Hfdef.
          + 
          destruct H as [Hrctype Hqctype].
        destruct (nth_error (cparams consig) i) as [paramtype|] eqn: Hparamtype.
        2:{
          apply nth_error_None in Hparamtype.
          assert (Hi_fdef : i < dom field_defs).
        {
          apply nth_error_Some.
          rewrite Hfdef.
          discriminate.
        }
        rewrite <- Hdom_eq in Hi_fdef.
        lia.
        }
        eapply Forall2_nth_error with (i:=i) (b:=fdef) (a:=paramtype) in Hfieldtypematch.
        apply qualified_type_subtype_q_subtype in Hfieldtypematch.
        eapply Forall2_nth_error with (i:=i) (b:=paramtype) (a:=argtype) in H17.
        apply qualified_type_subtype_q_subtype in H17.
        apply qualified_type_subtype_q_subtype in H18.

        2: exact Hargtype.
        2: exact Hparamtype.
        2: exact Hparamtype.
        2: exact Hfdef.
        simpl in Hfieldtypematch.
        move Hqctype at bottom.
        move Hfieldtypematch at bottom.
        move H16 at bottom.
        move H17 at bottom.
        move H18 at bottom.
        simpl in H18.
        unfold q_r_proj in *.
        destruct (mutability (ftype fdef)) eqn: Hfieldq.
        all: destruct q_c eqn: Hq_c.
        all: unfold vpa_mutabilty_rec_fld; unfold qualifier_typable_heap.
        all: destruct (rqtype rqt) eqn: Hrqtq; try easy.
        all: destruct (sqtype Tx) eqn: Htxq; try easy.
        all: destruct (cqualifier consig) eqn: Hconstructoreturnq.
        all: unfold vpa_mutabilty_constructor_fld in *; unfold vpa_mutabilty_bound in *; try easy.
        all: destruct (sqtype argtype) eqn: Hargq; unfold qualifier_typable in Hqctype; try easy.
        all: destruct (sqtype paramtype) eqn: Hparamq; try easy.
          }
      }
    * (* ι < dom h (existing object) *)
      assert (ι0 < dom h) by lia.
      unfold wf_obj.
      rewrite runtime_getObj_last2; auto.
      {
        specialize (Hheap ι0 H0).
        unfold wf_obj in Hheap |- *.
        destruct (runtime_getObj h ι0) as [o|] eqn:Hobj; [|contradiction].
          destruct Hheap as [Hrtypeuse [Hfields_len Hforall2]].
          repeat split.
          + exact Hrtypeuse.
          + 
          {
          exists Hfields_len.
          destruct Hforall2 as [Hcollect [Hlen_eq Hforall2_prop]].
          split.
          - exact Hcollect.
          - split.
            + exact Hlen_eq.
            + eapply Forall2_impl; [|exact Hforall2_prop].
              intros v fdef Hprop.
              destruct v as [|loc]; [trivial|].
              destruct (runtime_getObj h loc) as [obj_loc|] eqn:Hobj_loc.
              * (* loc exists in original heap *)
                destruct Hprop as [rqt [Hrtype_orig Hsubtype_orig]].
                assert (loc < dom h). {
                  (apply runtime_getObj_dom in Hobj_loc).
                  exact Hobj_loc.
                }
                rewrite runtime_getObj_last2; auto.
                rewrite Hobj_loc.
                exists rqt.
                split.
                -- unfold r_type in Hrtype_orig |- *.
                  rewrite runtime_getObj_last2; auto.
                -- exact Hsubtype_orig.
              * contradiction Hprop.
              }
       }
    + (* Length of runtime environment greater than 0 *)
      simpl. destruct Hsenv as [HsenvLength HsenvWellTyped].
      subst.
      rewrite update_length. rewrite <- Hlen.
      exact HsenvLength.
    +
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      destruct Hreceiverval as [iot Hiot].
      destruct Hiot as [Hiot Hiot_dom].
      exists iot.
      simpl.
      unfold gget in *.
      destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
      * (* Case: vars rΓ = [] *)
        exfalso.
        (* rewrite Hvars in HrEnvLen. *)
        simpl in HrEnvLen.
        lia.
      * (* Case: vars rΓ = v0 :: vs *)
        destruct x as [|x'].
           (* -- x = 0 contradiction. *)
           -- (* x = S x' *)
              {
                split.
                - (* Show update preserves position 0 *)
                  simpl. 
                  exfalso. easy.
                - (* Show iot is still in extended heap domain *)
                  subst.
                  rewrite length_app. simpl.
                  lia.
              }
           --
            split.   
            subst.
            exact Hiot.
            rewrite H1.
            rewrite length_app.
            simpl.
            lia.
    + 
    destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
    simpl.
    subst.
    apply Forall_update.
    * eapply Forall_impl; [| exact Hallvals].
      intros v Hv.
      destruct v as [|loc]; [trivial|].
      destruct (runtime_getObj h loc) as [obj|] eqn:Hobj; [| contradiction].
      assert (Hloc_dom : loc < dom h) by (apply runtime_getObj_dom in Hobj; exact Hobj).
    rewrite runtime_getObj_last2.
    -- exact Hloc_dom.
    -- rewrite Hobj. trivial.
    * (* Show new object is well-formed *)
      assert (dom h + 1 = S (dom h)) by lia.
      unfold runtime_getObj.
      simpl.
      assert (Hlen_extended: dom (h ++ [{| rt_type := {| rqtype := q_c; rctype := c |}; fields_map := vals |}]) = dom h + 1).
      -- rewrite length_app. simpl. lia.
      -- rewrite nth_error_app2.
      ** lia.
      ** replace (dom h - dom h) with 0 by lia.
        simpl. reflexivity.
      * assert (Hx_dom : x < dom sΓ') by (apply static_getType_dom in H8; exact H8).
      rewrite <- Hlen; exact Hx_dom.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. rewrite <- H15. exact HsenvLength.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. rewrite <- H15. exact HsenvWellTyped.
    + subst. rewrite update_length. rewrite <- Hlen. lia.
    + 
    {
      intros i Hi sqt Hnth.
      destruct (Nat.eq_dec i x) as [Heq | Hneq].
      - (* Case: i = x (newly assigned variable) *)
        subst i.
        simpl.
        unfold runtime_getVal.
        subst.
        rewrite update_same.
        + assert (x < dom sΓ') by (apply static_getType_dom in H8; exact H8).
        rewrite <- Hlen. exact H0.
        + (* Show wf_r_typable for the new object *)
          {
            unfold wf_r_typable.
            unfold r_type.
            rewrite runtime_getObj_last.
            simpl.
            unfold get_this_var_mapping.
            simpl.
            destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
            - exfalso.
              unfold wf_renv in Hrenv.
              destruct Hrenv as [HrEnvLen _].
              rewrite Hvars in HrEnvLen.
              simpl in HrEnvLen.
              lia.
            - unfold r_muttype.
            destruct x as [|x'].
            + (* Case: x = 0 *)
              easy.
            + (* Case: x = S x' *)
              (* unfold runtime_getVal in H. *)
              (* rewrite Hvars in H. *)
              (* simpl in H. *)
              (* injection H as H17_eq. *)
              (* subst v0. *)
              simpl.
              unfold r_muttype.
              unfold static_getType in H8.
              rewrite H8 in Hnth.
              inversion Hnth.
              subst sqt.
              split.
              apply qualified_type_subtype_base_subtype in H18.
              simpl in H18.
              exact H18.
              apply qualified_type_subtype_q_subtype in H18.
              simpl in H18.
              unfold qualifier_typable.
              (* unfold q_project_q_r in H3. *)
              (* destruct (vpa_mutabilty (q_r_proj qthisr) q_c) eqn:Hvpa. *)
              (* injection H3 as H3_eq. *)
              (* subst qadapted. *)
              destruct q_c.
              (* all: try inversion H20; try discriminate. *)
              all: try destruct (sqtype Tx); try reflexivity; try easy.
              all: try unfold is_q_c in H20; try destruct H20 as [Hwrong1 | Hwrong2]; try discriminate Hwrong1; try discriminate Hwrong2.
              all: try unfold vpa_mutabilty in Hvpa;
              try destruct (q_r_proj qthisr);
              try discriminate Hvpa.
              all: try destruct qadapted; try reflexivity.
              all: try rewrite Hwrong1 in Hvpa; try easy.
              all: try rewrite Hwrong2 in Hvpa; try easy.
              all: try rewrite Hwrong2 in H22; try easy.
              all: try destruct q_this; try unfold vpa_mutabilty_rs; try reflexivity.
              (* rewrite heap_extension_preserves_objects.
              unfold r_muttype in H1.
              destruct (runtime_getObj h l1) as [obj|] eqn:Hobj; [|discriminate]. *)
              (* *
                apply runtime_getObj_dom in Hobj.
                exact Hobj.
              * 
                (* injection H as H19_eq.
                rewrite H19_eq.
                split. *)
                assert (Hsqt_eq : sqt = Tx).
                {
                  unfold static_getType in H12.
                  rewrite Hnth in H12.
                  injection H12 as H0_eq.
                  exact H0_eq.
                }
                subst sqt.
                unfold runtime_type_to_qualified_type.
                simpl.
                {
                  unfold r_muttype in H1.
                  destruct (runtime_getObj h l1) as [obj|] eqn:Hobj; [|discriminate].
                  injection H1 as H1_eq.
                  subst qthisr.
                  split.
                    + apply qualified_type_subtype_base_subtype in H22.
                      * exact H22.
                    + unfold qualifier_typable.
                      unfold q_project_q_r in H3.
                      destruct (vpa_mutabilty (q_r_proj (rqtype (rt_type obj))) q_c) eqn:Hvpa; try discriminate.
                      injection H3 as H3_eq.
                      subst qadapted.
                      simpl.
                      apply qualified_type_subtype_q_subtype in H22.
                      destruct (sqtype Tx) eqn:Hsqtype_Tx.
                      - (* sqtype Tx = Mut *)
                        unfold vpa_mutabilty.
                        destruct (q_r_proj (rqtype (rt_type obj))); reflexivity.
                      - (* sqtype Tx = Imm *)
                        exfalso.
                        simpl in H22.
                        apply vpa_type_to_type_mut_cases in Hvpa.
                        destruct Hvpa as [Hqc_mut | [Hqthis_mut Hqc_rdm]].
                        * (* Case: q_c = Mut *)
                          subst q_c.
                          easy.
                        * (* Case: q_c = RDM *)
                          subst q_c.
                          easy.
                      - (* sqtype Tx = Rd *)
                        unfold vpa_mutabilty.
                        destruct (q_r_proj (rqtype (rt_type obj))). all: try reflexivity.
                        apply vpa_type_to_type_mut_cases in Hvpa.
                        destruct Hvpa as [Hqc_mut | [Hqthis_mut Hqc_rdm]]; [|trivial].
                        all: try simpl in H23.
                        subst q_c.
                        easy.
                        subst q_c.
                        (* easy. *)
                        apply vpa_type_to_type_mut_cases in Hvpa.
                        destruct Hvpa as [Hqc_mut | [Hqthis_mut Hqc_rdm]]; [|trivial].
                        subst q_c.
                        easy.
                        easy.
                        apply vpa_type_to_type_mut_cases in Hvpa.
                        destruct Hvpa as [Hqc_mut | [Hqthis_mut Hqc_rdm]]; [|trivial].
                        subst q_c.
                        easy.
                        easy.
                      - (* sqtype Tx = Lost *)
                        unfold vpa_mutabilty.
                        destruct (q_r_proj (rqtype (rt_type obj))); reflexivity.
                      - destruct (q_r_proj (rqtype (rt_type obj))). all: try reflexivity.
                      - destruct (q_r_proj (rqtype (rt_type obj))).
                        all: unfold vpa_mutabilty.
                        all: try apply vpa_type_to_type_mut_cases in Hvpa.
                        all: try destruct Hvpa as [Hqc_mut | [Hqthis_mut Hqc_rdm]]; [|trivial].
                        all: try subst q_c.
                        all: try easy.
                      - injection H3 as H3_eq. subst qadapted.
                        destruct (q_r_proj (rqtype (rt_type obj))).
                        all: unfold vpa_mutabilty.
                        all: try apply vpa_type_to_type_mut_cases in Hvpa.
                        all: try unfold vpa_mutabilty in Hvpa.
                        all: try destruct q_c.
                        all: try easy.
                        all: try destruct (sqtype Tx) eqn:Hex.
                        all: try easy.
                        all: apply qualified_type_subtype_q_subtype in H22.
                        all: simpl in H22.
                        all: try rewrite Hex in H22. 
                        all: try easy.
                        (* all: try (apply constructor_sig_lookup_dom in H14; exact H14). *)
                        all: try (
                          unfold wf_senv in Hsenv;
                          destruct Hsenv as [_ Hforall];
                          have Hwf_Tx := Forall_nth_error _ _ _ _ Hforall Hnth;
                          unfold wf_stypeuse in Hwf_Tx;
                          destruct (bound CT (sctype Tx)) as [q_bound|] eqn:Hbound; [|contradiction];
                          destruct Hwf_Tx as [_ Hdom];
                          exact Hdom
                        ).
                        all: try (simpl;
                        apply constructor_sig_lookup_dom in H14;
                        exact H14).
                } *)
          }
      - (* Case: i ≠ x (existing variable) *)
        simpl.
        unfold runtime_getVal.
        subst.
        rewrite update_diff; auto.
        assert (Hcorr_orig := Hcorr i Hi sqt Hnth).
        destruct (runtime_getVal rΓ i) as [v|] eqn:Hval.
      + (* Case: runtime_getVal rΓ i = Some v *)
        destruct v as [|loc].
        * (* Case: v = Null_a *)
        unfold runtime_getVal in Hval.
        rewrite Hval.
        trivial.
        * (* Case: v = Iot loc *)
        unfold runtime_getVal in Hval.
        rewrite Hval.
        unfold wf_r_typable in Hcorr_orig |- *.
        destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
        (* destruct (get_this_var_mapping (vars rΓ)) as [ι'|] eqn:Hthis; [|contradiction]. *)
        (* destruct (r_muttype h ι') as [q|] eqn:Hmut; [|contradiction]. *)
        (* assert (Hthis_preserved : get_this_var_mapping (vars (rΓ <| vars := update x (Iot dom h) (vars rΓ) |>)) = Some ι').
        {
          simpl. 
          unfold get_this_var_mapping in Hthis |- *.
          destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
          - discriminate Hthis.
          - destruct x as [|x'].
            + easy.
            + simpl. exact Hthis.
            }
            rewrite Hthis_preserved.
            assert (Hloc_bound : loc < dom h).
          {
            unfold r_type in Hrtype.
            destruct (runtime_getObj h loc) as [obj|] eqn:Hobj; [|discriminate].
            apply runtime_getObj_dom in Hobj. exact Hobj.
          } *)
          assert (Hrtype_ext : r_type (h ++ [{| rt_type := {| rqtype := q_c; rctype := c |}; fields_map := vals |}]) loc = Some rqt).
          {
            unfold r_type in Hrtype |- *.
            rewrite heap_extension_preserves_objects; auto.
            destruct (runtime_getObj h loc) as [obj|] eqn:Hobj; [|discriminate].
            apply runtime_getObj_dom in Hobj. exact Hobj.
          }
          (* assert (Hmut_ext : r_muttype (h ++ [{| rt_type := {| rqtype := qadapted; rctype := c |}; fields_map := vals |}]) ι' = Some q).
          {
            unfold r_muttype in Hmut |- *.
            assert (Hι'_bound : ι' < dom h).
            {
              unfold r_muttype in Hmut.
              destruct (runtime_getObj h ι') as [obj|] eqn:Hobj; [|discriminate].
              apply runtime_getObj_dom in Hobj. exact Hobj.
            }
            rewrite heap_extension_preserves_objects; auto.
          } *)
          rewrite Hrtype_ext.
          (* rewrite Hmut_ext. *)
          exact Hcorr_orig.
          + contradiction Hcorr_orig.
          }
  - (* Case: stmt = Seq *)
    intros. inversion Htyping; subst.
    specialize (IHHeval1 eq_refl sΓ'0 sΓ Hwf H4) as IH1.
    (* assert (Hreciver_addr_preserved: get_this_var_mapping (vars rΓ') = Some ι). {
    }
    assert (Hreciver_mut_preserved: r_muttype h' ι = Some q_this). {
    } *)
    specialize (IHHeval2 eq_refl sΓ' sΓ'0 IH1 H6) as IH2.
    exact IH2.
Qed.

Definition get_this_type (sΓ : s_env) : option qualified_type :=
  match sΓ with
  | [] => None
  | Tthis :: _ => 
    Some Tthis
  end.

Definition imm_runtime_type (C : class_name) : runtime_type := 
  mkruntime_type Imm_r C.

Lemma imm_not_subtype_mut : ~ q_subtype Imm Mut.
Proof.
  intro H.
  inversion H; subst; discriminate.
Qed.

(* ------------------------------------------------------------- *)
(* Immutability properties for PICO *)
Notation "l [ i ]" := (nth_error l i) (at level 50).

Theorem immutability_pico :
  forall CT sΓ rΓ h stmt rΓ' h' sΓ' l C vals vals' f,
    (* get_this_var_mapping (vars rΓ) = Some ι -> *)
    (* (r_muttype h ι) = Some q_this -> *)
    l < dom h ->
    runtime_getObj h l = Some (mkObj (mkruntime_type Imm_r C) vals) ->
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ stmt sΓ' -> 
    eval_stmt OK CT rΓ h stmt OK rΓ' h' -> 
    runtime_getObj h' l = Some (mkObj (mkruntime_type Imm_r C) vals') ->
    sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA ->
    nth_error vals f = nth_error vals' f.
Proof.
  intros. remember OK as ok.
  (* generalize dependent ι. *)
  (* generalize dependent q_this. *)
  generalize dependent sΓ.
  generalize dependent sΓ'.
  generalize dependent vals. generalize dependent vals'.
  induction H3; try discriminate.
  - (* Skip *) intros. inversion H2. subst.
   rewrite H0 in H4. injection H4; auto.
   intro H_eq.
    rewrite H_eq.
    reflexivity.
  - (* Local *) 
  intros. inversion H3. subst.
   rewrite H1 in H4. injection H4; auto.
   intro H_eq.
    rewrite H_eq.
    reflexivity.
  - (* VarAss *) 
  intros. inversion H6. subst.
   rewrite H2 in H4. injection H4; auto.
   intro H_eq.
    rewrite H_eq.
    reflexivity.
  - (* FldWrite *) 
  {
    intros.
    destruct (Nat.eq_dec l loc_x) as [Heq_l | Hneq_l].
    - (* Case: l = lx (same object being written to) *)
      subst l.
      (* Extract the object type from H0 and H6 *)
      rewrite H7 in H1.
      injection H1 as H1_eq.
      subst o.
      (* Now we have an immutable object, but can_assign returned true *)
      (* This should be impossible for Final/RDA fields on immutable objects *)
      destruct (Nat.eq_dec f f0) as [Heq_f | Hneq_f].
      + (* Case: f = f0 (same field being written) *)
        subst f.
        (* Show contradiction: can_assign should be false for immutable Final/RDA fields *)
        exfalso.
        unfold wf_r_config in H8.
        destruct H8 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
        assert (Hx_bound : x < dom sΓ) by (apply runtime_getVal_dom in H0; rewrite <- Hlen in H0; exact H0).
        inversion H9; subst.
        specialize (Hcorr x Hx_bound Tx H12).
        rewrite H0 in Hcorr.
        unfold wf_r_typable in Hcorr.
          destruct (r_type h loc_x) as [rqt|] eqn:Hrtype; [|contradiction].
          unfold r_type in Hrtype.
          rewrite H7 in Hrtype.
          simpl in Hrtype.
          injection Hrtype as Hrtype_eq.
          (* destruct (get_this_var_mapping (vars rΓ)) as [ι'|] eqn:Hthis; [|contradiction]. *)
          (* destruct (r_muttype h ι') as [q|] eqn:Hmut; [|contradiction]. *)
          destruct Hcorr as [Hbase_sub Htypable].
          destruct H5 as [Hffinal | HfRDA].
          have Hrctype_eq : rctype rqt = C by (rewrite <- Hrtype_eq; reflexivity).
          assert (Heq : a = Final).
        {
          eapply sf_assignability_deterministic_rel; eauto.
        }
        apply vpa_assingability_assign_cases in H20.
        destruct H20 as [HAassignable | HARDA ].
        rewrite HAassignable in Heq.
        discriminate.
        destruct HARDA as [_ HFinalRDA].
        rewrite HFinalRDA in Heq.
        discriminate.
        apply vpa_assingability_assign_cases in H20.
        destruct H20 as [HAassignable | HARDA ].
        have Hrctype_eq : rctype rqt = C by (rewrite <- Hrtype_eq; reflexivity).
        rewrite HAassignable in H17.
        assert (RDA = Assignable). {
          eapply sf_assignability_deterministic_rel; eauto.
        }
        discriminate.
        destruct HARDA as [HsqtypeMut _].
        unfold qualifier_typable in Htypable.
        (* rewrite HsqtypeMut in Hqual. *)
        (* unfold vpa_mutabilty in Htypable. *)
        have Hrqtype_eq : rqtype rqt = Imm_r by (rewrite <- Hrtype_eq; reflexivity).
        rewrite Hrqtype_eq in Htypable.
        rewrite HsqtypeMut in Htypable.
        easy.
        (* assert (Hq_proj : q_r_proj q = Imm \/ q_r_proj q = Mut) by apply q_r_proj_imm_or_mut.
        destruct Hq_proj as [HqImm | HqMut].
        -- (* Case: q_r_proj q = Imm *)
          (* rewrite HqImm in Htypable. *)
          rewrite Hrqtype_eq in Htypable.
          rewrite HsqtypeMut in Htypable.
          discriminate.
        -- (* Case: q_r_proj q = Mut *)  
          (* rewrite HqMut in Htypable. *)
          rewrite Hrqtype_eq in Htypable.
          rewrite HsqtypeMut in Htypable.
          discriminate. *)
        + 
        assert (Hvals_eq : vals' = [f0 ↦ val_y] (vals)).
        { 
          (* Use the definition of update_field and the fact that h' contains the updated object *)
          unfold update_field in H4.
          rewrite H7 in H4.
          rewrite H4 in H6.
          unfold runtime_getObj in H6.
          (* Apply update_same to get the updated object *)
          assert (Hget_same : nth_error (update loc_x {| rt_type := {| rqtype := Imm_r; rctype := C |}; fields_map := [f0 ↦ val_y] (vals) |} h) loc_x = 
                              Some {| rt_type := {| rqtype := Imm_r; rctype := C |}; fields_map := [f0 ↦ val_y] (vals) |}).
          {
            apply update_same.
            exact H.
          }
          rewrite Hget_same in H6.
          injection H6 as H6_eq.
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
      unfold update_field in H4.
      rewrite H1 in H4.
      rewrite H4.
      unfold runtime_getObj.
      apply update_diff.
      easy.
    }
    rewrite H7 in Hl_unchanged.
    rewrite Hl_unchanged in H6.
    injection H6 as H6_eq.
    rewrite <- H6_eq.
    reflexivity.
  }
  - (* New *) (* h' = h ++ [new_obj], so l < dom h means same object *)
  intros.
  inversion H8; subst.
  (* Since l < dom h, the object at location l is unchanged *)
  unfold runtime_getObj in H4.
  rewrite List.nth_error_app1 in H4; auto.
  unfold runtime_getObj in H6.
  rewrite H6 in H4.
  injection H4; intros; subst.
  reflexivity.
  - (* Call *) (* Similar to other non-mutating cases *) 
  intros.
  revert H13.
  inversion H14. 
  revert H20.
  subst.
  intro H20.
  intro H13.
  destruct H2 as [mdeflookup getmbody].
  remember (msignature mdef) as msig.
  have mdeflookupcopy := mdeflookup.
  apply method_body_well_typed_by_find in mdeflookup; auto.
  destruct mdeflookup as [sΓmethodend Htyping_method].
  remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit.
  apply IHeval_stmt with (sΓ' := sΓmethodend)(sΓ := sΓmethodinit). 1-9: auto.
  remember {| vars := Iot ly :: vals |} as rΓmethodinit.
  destruct (r_muttype h ly) eqn: Hinnerthis.
    2:{
      unfold r_muttype in Hinnerthis.
      unfold r_basetype in H1.
      destruct (runtime_getObj h ly).
      discriminate Hinnerthis.
      discriminate H1.
    }
  (* rename rΓ' into rΓmethodinit. *)
  assert (Hwf_method_frame : wf_r_config CT sΓmethodinit 
                                    rΓmethodinit h ).
  {
    have Hwf_copy := H13.
    unfold wf_r_config in H13.
    destruct H13 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    have Hclasstable := Hclass.
    destruct Hclass as [Hclass Hcname_consistent].
    repeat split.
    exact Hclass.
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
    unfold runtime_getVal in H0.
    destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
    injection H0 as H_eq.
    subst v.
    eapply Forall_nth_error in Hallvals; eauto.
    simpl in Hallvals.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjly; [|contradiction].
    apply runtime_getObj_dom in Hobjly.

    exact Hobjly.
    rewrite HeqrΓmethodinit.
    simpl.
    constructor.
    simpl.
    unfold runtime_getVal in H0.
    destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
    injection H0 as H_eq.
    subst v.
    unfold runtime_getVal in Hnth_y.
    unfold wf_renv in Hrenv.
    destruct Hrenv as [_ [_ Hallvals]].
    eapply Forall_nth_error in Hallvals; eauto.
    simpl in Hallvals.
    exact Hallvals.
    eapply runtime_lookup_list_preserves_wf_values; eauto.

    rewrite HeqsΓmethodinit.
    simpl.
    lia.

    (* Inner static env's elements are wellformed typeuse *)
    rewrite HeqsΓmethodinit.
    constructor.
    (* Receiver type is well-formed *)
    eapply method_sig_wf_receiver_by_find; eauto.
    unfold r_basetype in H1.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
    injection H1 as H0_eq.
    subst cy.
    destruct obj as [rt_obj fields_obj].
    destruct rt_obj as [rq_obj rc_obj].
    simpl.
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

    eapply method_sig_wf_parameters_by_find; eauto.
    unfold r_basetype in H1.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
    injection H1 as H0_eq.
    subst cy.
    destruct obj as [rt_obj fields_obj].
    destruct rt_obj as [rq_obj rc_obj].
    simpl.
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

    apply static_getType_list_preserves_length in H21.
      apply runtime_lookup_list_preserves_length in H6.
      rewrite HeqsΓmethodinit.
      simpl.
      f_equal.
      apply Forall2_length in H29.
      rewrite <- Heqmsig.
        assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H20.
          exact H20.
        }

        (* Apply correspondence to get wf_r_typable *)
        specialize (Hcorr y Hy_dom Ty H20).
        rewrite H0 in Hcorr.

        (* Extract subtyping from wf_r_typable *)
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H1.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H1 as Hcy_eq.
        subst cy.
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].


        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot _]].
        unfold get_this_var_mapping.
        unfold gget in Hget_iot.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].
        injection Hget_iot as Hv0_eq.
        subst v0.

        unfold r_type in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        (* destruct (r_muttype h iot) as [q|] eqn:Hmut; [|contradiction]. *)
        destruct Hcorr as [Hsubtype _].
    rewrite <- H6 in H21.
    rewrite HeqrΓmethodinit.
    simpl.
    f_equal.
    rewrite <- H21.
    rewrite Heqmsig.
    rewrite H29.
    rewrite <- Hsubtype in H22.
    simpl in mdeflookupcopy.
    assert (mdef = mdef0). 
    {
      eapply find_overriding_method_deterministic; eauto.
    }
    rewrite H1.
    reflexivity.


    (* Typable! *)
    intros i Hi sqt Hnth.
      rewrite HeqsΓmethodinit in Hnth, Hi.
      rewrite HeqrΓmethodinit.
      simpl in *.
      destruct i as [|i'].
      (* Reciever *)
      simpl in Hnth.
      injection Hnth as Hsqt_eq.
      subst sqt.
      simpl.
      unfold wf_r_typable.
      unfold r_type.
      destruct (runtime_getObj h ly) as [objy|] eqn:Hobj_ly.
      2:{
        unfold r_basetype in H1.
        rewrite Hobj_ly in H1.
        discriminate.
      }
      (* Get the runtime type *)
      simpl.
      (* destruct (r_muttype h ly) as [qy|] eqn:Hq_ly.
      2:{
        unfold r_muttype in Hq_ly.
        rewrite Hobj_ly in Hq_ly.
        discriminate.
      } *)
      split.
      apply qualified_type_subtype_base_subtype in H28.
      (* rewrite vpa_qualified_type_sctype in H22. *)
      assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H20.
          exact H20.
        }

      specialize (Hcorr y Hy_dom Ty H20).
              (* Extract subtyping from wf_r_typable *)
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H1.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].


        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot _]].
        unfold get_this_var_mapping.
        unfold gget in Hget_iot.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].
        injection Hget_iot as Hv0_eq.
        subst v0.

        unfold r_type in Hcorr.
        rewrite H0 in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        (* destruct (r_muttype h iot) as [q|] eqn:Hmut; [|contradiction]. *)
        destruct Hcorr as [Hsubtype _].
        simpl in Hobj_ly.
        injection Hobj_ly as Hobjy_eq.


      rewrite <- Hsubtype in H22.
      simpl in mdeflookupcopy.
      simpl in H1.
      (* unfold r_basetype in H0. *)
      (* rewrite Hobjy in H1.
      simpl in H1.
      inversion H1. *)
      inversion H1.
      rewrite <- H3 in mdeflookupcopy.
      assert (heqm : mdef = mdef0). 
      {
        symmetry.
        eapply find_overriding_method_deterministic; eauto.
      }
      subst objy.
      simpl.
      rewrite heqm.
      rewrite <- Hsubtype in H28.
      exact H28.
      apply qualified_type_subtype_q_subtype in H28.
      assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H20.
          exact H20.
        }

      specialize (Hcorr y Hy_dom Ty H20).
              (* Extract subtyping from wf_r_typable *)
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H1.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        (* injection H0 as Hcy_eq.
        subst cy. *)
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].


        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot _]].
        unfold get_this_var_mapping.
        unfold gget in Hget_iot.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].
        injection Hget_iot as Hv0_eq.
        subst v0.

        unfold r_type in Hcorr.
        rewrite H0 in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        (* destruct (r_muttype h iot) as [q|] eqn:Hmut; [|contradiction]. *)
        destruct Hcorr as [Hsubtype Hqualifier].
        simpl in Hobj_ly.
        injection Hobj_ly as Hobjy_eq.
      rewrite <- Hsubtype in H22.
      simpl in mdeflookupcopy.
      simpl in H1.
      (* unfold r_basetype in H0. *)
      (* rewrite Hobjy in H1.
      simpl in H1.
      inversion H1. *)
      inversion H1.
      rewrite <- H3 in mdeflookupcopy.
      assert (heqm : mdef = mdef0). 
      {
        eapply find_overriding_method_deterministic; eauto.
      }
      subst mdef0.
      rewrite <- Hobjy_eq.
      simpl.
      eapply qualifier_typable_subtype_receiver; eauto.

(* -------------------------------------------------- *)
      apply qualified_type_subtype_q_subtype in H28.
        assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H20.
          exact H20.
        }
      specialize (Hcorr y Hy_dom Ty H20).
              (* Extract subtyping from wf_r_typable *)
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H1.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy.
        2:{
          unfold r_basetype in H.
          discriminate H1.
        } 
        (* [|discriminate]. *)
        (* injection H0 as Hcy_eq.
        subst cy. *)
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].


        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot _]].
        unfold get_this_var_mapping.
        unfold gget in Hget_iot.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].
        injection Hget_iot as Hv0_eq.
        subst v0.

        unfold r_type in Hcorr.
        rewrite H0 in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        (* destruct (r_muttype h iot) as [q|] eqn:Hmut; [|contradiction *)
        destruct Hcorr as [Hsubtype Hqualifier].
        (* simpl in Hobj_ly. *)
        (* injection Hobj_ly as Hobjy_eq. *)
      rewrite <- Hsubtype in H22.
            (* unfold r_basetype in H0. *)
simpl in mdeflookupcopy.
      simpl in H1.
      (* unfold r_basetype in H0. *)
      (* rewrite Hobjy in H1.
      simpl in H1.
      inversion H1. *)
      inversion H1.
      rewrite <- H3 in mdeflookupcopy.

      assert (heqm : mdef = mdef0). 
      {
        eapply find_overriding_method_deterministic; eauto.
      }
      subst mdef0.

      simpl.
unfold runtime_getVal.
simpl.
destruct (nth_error vals i') as [v|] eqn:Hval_i.
- (* Parameter i' exists *)
  destruct v as [|loc]; [trivial|].
  (* Use H23 to get the subtyping relationship *)
  assert (Hi'_bound : i' < List.length argtypes).
  {
    apply Forall2_length in H29.
    simpl in Hi.
    (* rewrite HeqsΓmethodinit in Hnth. *)
    simpl in Hnth.
    (* apply nth_error_Some in Hnth. *)
    simpl in Hnth.
    lia.
  }
  assert (Harg_type : exists argtype, nth_error argtypes i' = Some argtype).
  {
    apply nth_error_Some_exists.
    exact Hi'_bound.
  }
  destruct Harg_type as [argtype Hargtype].
  (* Use runtime_lookup_list_preserves_typing *)
  eapply runtime_lookup_list_preserves_typing with (CT:= CT) (h:=h)in H6; eauto.
  eapply Forall2_nth_error in H6; eauto.
  (* Apply subtyping from H23 *)
  eapply Forall2_nth_error in H29; eauto.
  simpl in H6.
  eapply wf_r_typable_subtype; eauto.
  (* eapply wf_r_typable_env_independent; [|exact H4].
  simpl.
  unfold get_this_var_mapping.
  exact H4.*)
- (* Parameter i' doesn't exist - contradiction *)
  exfalso.
  apply nth_error_None in Hval_i.
  apply runtime_lookup_list_preserves_length in H6.
  apply static_getType_list_preserves_length in H21.
  apply Forall2_length in H29.
  rewrite H6 in Hval_i.
  rewrite <- H21 in Hval_i.
  rewrite H29 in Hval_i.
  simpl in Hi.
  simpl in Hnth.
  simpl in Hnth.
  lia.
  }
  (* rewrite getmbody. *)
  exact Hwf_method_frame.
  rewrite getmbody.
  exact Htyping_method.
  unfold wf_r_config in H13.
  destruct H13 as [Hwf_classtable _].
  exact Hwf_classtable.
  unfold r_basetype in H1.
  destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
  injection H1 as H0_eq.
  subst cy.
  destruct obj as [rt_obj fields_obj].
  destruct rt_obj as [rq_obj rc_obj].
  simpl.
  destruct H13 as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
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
  intros. inversion H2; subst. 
  specialize (eval_stmt_preserves_heap_domain_simple CT rΓ h s1 rΓ' h' H3_) as Hh'.
  assert (l < dom h') by lia. specialize (runtime_getObj_Some h' l H3) as [C' [values' Hh'some]].
  specialize (runtime_preserves_r_type_heap CT rΓ h l ({| rqtype := Imm_r; rctype := C |})
  h' vals s1 rΓ' H0 H3_) as [vals1 Hrtype]. rewrite Hrtype in Hh'some; inversion Hh'some; subst.
  specialize (IHeval_stmt1 H Heqok H5 values' Hrtype vals H0 sΓ'0 sΓ H1 H10). 
  specialize (preservation_pico CT sΓ rΓ h s1 rΓ' h' sΓ'0 H1 H10 H3_) as Hwf'.
  specialize (IHeval_stmt2 H3 Heqok H5 vals' H4 values' Hrtype sΓ' sΓ'0 Hwf' H12). 
  rewrite IHeval_stmt2 in IHeval_stmt1; auto.
Qed.

