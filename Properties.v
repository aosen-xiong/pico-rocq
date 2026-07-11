Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation.

From Stdlib Require Import List.
From Stdlib Require String.
Import ListNotations.

Ltac solve_q_subtype_wrong :=
  lazymatch goal with
  | [ H : q_subtype RO Imm |- _ ] => exfalso; inversion H; subst; congruence
  | [ H : q_subtype RO Mut |- _ ] => exfalso; inversion H; subst; congruence
  | [ H : q_subtype RO RDM |- _ ] => exfalso; inversion H; subst; congruence
  | [ H : q_subtype RO Lost |- _ ] => exfalso; inversion H; subst; congruence
  | [ H : q_subtype RO Bot  |- _ ] => exfalso; inversion H; subst; congruence
  | [ H : q_subtype Imm Mut  |- _ ] => exfalso; inversion H; subst; congruence
  | [ H : q_subtype Imm RDM |- _ ] => exfalso; inversion H; subst; congruence
  | [ H : q_subtype Imm Lost |- _ ] => exfalso; inversion H; subst; congruence
  | [ H : q_subtype Imm Bot  |- _ ] => exfalso; inversion H; subst; congruence
  | [ H : q_subtype Mut Imm  |- _ ] => exfalso; inversion H; subst; congruence
  | [ H : q_subtype Mut RDM |- _ ] => exfalso; inversion H; subst; congruence
  | [ H : q_subtype Mut Lost |- _ ] => exfalso; inversion H; subst; congruence
  | [ H : q_subtype Mut Bot  |- _ ] => exfalso; inversion H; subst; congruence
  | [ H : q_subtype RDM Imm  |- _ ] => exfalso; inversion H; subst; congruence
  | [ H : q_subtype RDM Mut  |- _ ] => exfalso; inversion H; subst; congruence
  | [ H : q_subtype RDM Lost |- _ ] => exfalso; inversion H; subst; congruence
  | [ H : q_subtype RDM Bot  |- _ ] => exfalso; inversion H; subst; congruence
  | [ H : q_subtype Lost Lost |- _ ] => exfalso; inversion H; subst; congruence
  | [ H : q_subtype Lost Imm |- _ ] => exfalso; inversion H; subst; congruence
  | [ H : q_subtype Lost Mut |- _ ] => exfalso; inversion H; subst; congruence
  | [ H : q_subtype Lost RDM |- _ ] => exfalso; inversion H; subst; congruence
  | [ H : q_subtype Lost Bot  |- _ ] => exfalso; inversion H; subst; congruence
  | _ => idtac
  end.

Local Ltac qtypable_contradiction H :=
  exfalso; unfold qualifier_typable_context, vpa_mutability_rs in H; cbn in H; contradiction H.

Ltac solve_qualifier_typable_wrong_concrete :=
  lazymatch goal with
  | [ H : qualifier_typable_context Imm_r Mut Mut_r |- _ ] => qtypable_contradiction H
  | [ H : qualifier_typable_context Imm_r RDM Mut_r |- _ ] => qtypable_contradiction H
  | [ H : qualifier_typable_context Imm_r Bot Mut_r |- _ ] => qtypable_contradiction H
  | [ H : qualifier_typable_context Imm_r Mut Imm_r |- _ ] => qtypable_contradiction H
  | [ H : qualifier_typable_context Imm_r Bot Imm_r |- _ ] => qtypable_contradiction H
  | [ H : qualifier_typable_context Mut_r Imm Mut_r |- _ ] => qtypable_contradiction H
  | [ H : qualifier_typable_context Mut_r Bot Mut_r |- _ ] => qtypable_contradiction H
  | [ H : qualifier_typable_context Mut_r Imm Imm_r |- _ ] => qtypable_contradiction H
  | [ H : qualifier_typable_context Mut_r RDM Imm_r |- _ ] => qtypable_contradiction H
  | [ H : qualifier_typable_context Mut_r Bot Imm_r |- _ ] => qtypable_contradiction H
  | [ H : qualifier_typable_context Imm_r Imm Mut_r |- _ ] => clear H
  | [ H : qualifier_typable_context Imm_r RO  Mut_r |- _ ] => clear H
  | [ H : qualifier_typable_context Imm_r Lost Mut_r |- _ ] => clear H
  | [ H : qualifier_typable_context Imm_r RO  Imm_r |- _ ] => clear H
  | [ H : qualifier_typable_context Imm_r Imm Imm_r |- _ ] => clear H
  | [ H : qualifier_typable_context Imm_r Lost Imm_r |- _ ] => clear H
  | [ H : qualifier_typable_context Imm_r RDM Imm_r |- _ ] => clear H
  | [ H : qualifier_typable_context Mut_r Mut Mut_r |- _ ] => clear H
  | [ H : qualifier_typable_context Mut_r RO  Mut_r |- _ ] => clear H
  | [ H : qualifier_typable_context Mut_r Lost Mut_r |- _ ] => clear H
  | [ H : qualifier_typable_context Mut_r RDM Mut_r |- _ ] => clear H
  | [ H : qualifier_typable_context Mut_r RO  Imm_r |- _ ] => clear H
  | [ H : qualifier_typable_context Mut_r Mut Imm_r |- _ ] => clear H
  | [ H : qualifier_typable_context Mut_r Lost Imm_r |- _ ] => clear H
  | _ => idtac
  end.

Ltac solve_qualifier_typable_correct_concrete :=
  lazymatch goal with
  | |- qualifier_typable_context Imm_r Imm Mut_r  => unfold qualifier_typable_context, vpa_mutability_rs; cbn; exact I
  | |- qualifier_typable_context Imm_r RO Mut_r   => unfold qualifier_typable_context, vpa_mutability_rs; cbn; exact I
  | |- qualifier_typable_context Imm_r Lost Mut_r => unfold qualifier_typable_context, vpa_mutability_rs; cbn; exact I
  | |- qualifier_typable_context Imm_r RO Imm_r   => unfold qualifier_typable_context, vpa_mutability_rs; cbn; exact I
  | |- qualifier_typable_context Imm_r Imm Imm_r  => unfold qualifier_typable_context, vpa_mutability_rs; cbn; exact I
  | |- qualifier_typable_context Imm_r Lost Imm_r => unfold qualifier_typable_context, vpa_mutability_rs; cbn; exact I
  | |- qualifier_typable_context Imm_r RDM Imm_r  => unfold qualifier_typable_context, vpa_mutability_rs; cbn; exact I
  | |- qualifier_typable_context Mut_r Mut Mut_r  => unfold qualifier_typable_context, vpa_mutability_rs; cbn; exact I
  | |- qualifier_typable_context Mut_r RO Mut_r   => unfold qualifier_typable_context, vpa_mutability_rs; cbn; exact I
  | |- qualifier_typable_context Mut_r Lost Mut_r => unfold qualifier_typable_context, vpa_mutability_rs; cbn; exact I
  | |- qualifier_typable_context Mut_r RDM Mut_r  => unfold qualifier_typable_context, vpa_mutability_rs; cbn; exact I
  | |- qualifier_typable_context Mut_r RO Imm_r   => unfold qualifier_typable_context, vpa_mutability_rs; cbn; exact I
  | |- qualifier_typable_context Mut_r Mut Imm_r  => unfold qualifier_typable_context, vpa_mutability_rs; cbn; exact I
  | |- qualifier_typable_context Mut_r Lost Imm_r => unfold qualifier_typable_context, vpa_mutability_rs; cbn; exact I
  end.

Lemma collect_methods_exists : forall CT C
  (Hwf_ct : wf_class_table CT)
  (Hdom   : C < dom CT),
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
    - (* WFObjectDef: no parent *)
    exists (methods (body class_def)).
    eapply CM_Object; eauto.
  - (* WFOtherDef: has parent *)
    assert (Hdom_parent : superC < dom CT).
    {
      unfold wf_class_table in Hwf_ct.
      destruct Hwf_ct as [_ [_ [Hotherclasses Hcname_consistent]]].
      assert (Hcname_eq : cname (signature class_def) = C).
      {
        apply Hcname_consistent.
        exact Hfind_class.
      }
      rewrite Hcname_eq in Hordering.
      (* Use H2: C > superC *)
      lia.
    }
    (* Apply strong induction hypothesis *)
    assert (IH_parent : exists parent_methods, CollectMethods CT superC parent_methods).
    {
      apply IH.
      (* Need to prove superC < C *)
      unfold wf_class_table in Hwf_ct.
      destruct Hwf_ct as [_ [_ [_ Hcname_consistent]]].
      assert (Hcname_eq : cname (signature class_def) = C).
      {
        apply Hcname_consistent.
        exact Hfind_class.
      }
      rewrite Hcname_eq in Hordering.
      exact Hordering.
      exact Hdom_parent.
    }
    destruct IH_parent as [parent_methods Hcollect_parent].
    exists (override parent_methods (methods (body class_def))).
    eapply CM_Inherit; eauto.
Qed.

Lemma override_parent_method_in : forall parent_methods own_methods m mdef
  (Hoverride : gget_method (override parent_methods own_methods) m = Some mdef)
  (Hown      : gget_method own_methods m = None),
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
Qed.

Lemma gget_method_from_in : forall methods m mdef
  (Hin : In mdef methods)
  (Heq : eq_method_name (mname (msignature mdef)) m = true),
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

Lemma method_body_well_typed : forall CT C cdef mdef
  (Hwf_ct  : wf_class_table CT)
  (Hdom    : C < dom CT)
  (HfindC  : find_class CT C = Some cdef)
  (Hlookup : In mdef (methods (body cdef))),
  exists sΓ', stmt_typing CT (mreceiver (msignature mdef) :: mparams (msignature mdef))
                           mdef.(msignature).(mtype)
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

  assert (Hwf_mdef : wf_method CT C mdef).
  {
    eapply method_lookup_wf_class; eauto.
  }
  inversion Hwf_mdef; subst.
  destruct H as [sΓ' [Htyping _]].
  exists x.
  exact Htyping.
Qed.

Lemma method_body_well_typed_by_find : forall CT C m mdef
  (Hwf_ct  : wf_class_table CT)
  (Hdom    : C < dom CT)
  (Hlookup : FindMethodWithName CT C m mdef),
  exists sΓ', stmt_typing CT (mreceiver (msignature mdef) :: mparams (msignature mdef))
                            mdef.(msignature).(mtype)
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
  assert (Hcname_eq : cname (signature class_def) = C).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [_ [_ Hcname_consistent]].
    destruct Hcname_consistent as [_ Hcname_eq].
    apply Hcname_eq.
    exact Hfind_class.
  }

  assert (Hwf_inherited : exists D ddef, base_subtype CT C D /\ find_class CT D = Some ddef /\ In mdef (methods (body ddef)) /\ wf_method CT D mdef).
  {
    eapply method_lookup_in_wellformed_inherited; eauto.
  }
  destruct Hwf_inherited as [D [ddef [Hsub [Hfind_D [Hin_D Hwf_D]]]]].

  (* Extract the statement typing from wf_method *)
  inversion Hwf_D; subst.
  destruct H as [sΓ' [Htyping _]].
  exists x.
  exact Htyping.
Qed.

Lemma wf_method_sig_types : forall CT C mdef
  (Hwf_method : wf_method CT C mdef),
  wf_stypeuse CT (sqtype (mreceiver (msignature mdef))) (sctype (mreceiver (msignature mdef))) /\
  Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) (mparams (msignature mdef)).
Proof.
  intros CT C mdef Hwf_method.
  inversion Hwf_method; subst.
  destruct H as [mreturn [Htyping _]].
  assert (Hwf_env : wf_senv CT (mreceiver (msignature mdef) :: mparams (msignature mdef))).
  {
    eapply stmt_typing_wf_env; eauto.
  }
  (* unfold sΓ, msig in Hwf_env. *)
  inversion Hwf_env; subst.
  split.
  - (* Receiver well-formedness *)
    apply Forall_inv in H0.
    exact H0.
  - (* Parameters well-formedness *)
    apply Forall_inv_tail in H0.
    exact H0.
Qed.

Lemma method_sig_wf_reciever : forall CT C cdef mdef
  (Hwf_ct  : wf_class_table CT)
  (Hdom    : C < dom CT)
  (HfindC  : find_class CT C = Some cdef)
  (Hlookup : In mdef (methods (body cdef))),
  wf_stypeuse CT (sqtype (mreceiver (msignature mdef))) (sctype (mreceiver (msignature mdef))).
Proof.
  intros CT C cdef mdef Hwf_ct Hdom HfindC Hlookup.
  assert (Hwf_class : wf_class CT cdef).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  assert (Hwf_mdef : wf_method CT C mdef).
  {
    eapply method_lookup_wf_class; eauto.
  }
  eapply wf_method_sig_types; eauto.
Qed.

Lemma method_sig_wf_parameters : forall CT C cdef mdef
  (Hwf_ct  : wf_class_table CT)
  (Hdom    : C < dom CT)
  (HfindC  : find_class CT C = Some cdef)
  (Hlookup : In mdef (methods (body cdef))),
  Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) (mparams (msignature mdef)).
Proof.
  intros CT C cdef mdef Hwf_ct Hdom HfindC Hlookup.
  assert (Hwf_class : wf_class CT cdef).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  assert (Hwf_mdef : wf_method CT C mdef).
  {
    eapply method_lookup_wf_class; eauto.
  }

  eapply wf_method_sig_types; eauto.
Qed.

Lemma method_sig_wf_receiver_by_find : forall CT C m mdef
  (Hwf_ct  : wf_class_table CT)
  (Hdom    : C < dom CT)
  (Hlookup : FindMethodWithName CT C m mdef),
  wf_stypeuse CT (sqtype (mreceiver (msignature mdef))) (sctype (mreceiver (msignature mdef))).
Proof.
  intros CT C m mdef Hwf_ct Hdom Hlookup.
  assert (Hwf_inherited : exists D ddef, base_subtype CT C D /\ find_class CT D = Some ddef /\ In mdef (methods (body ddef)) /\ wf_method CT D mdef).
  {
    eapply method_lookup_in_wellformed_inherited; eauto.
  }
  destruct Hwf_inherited as [D [ddef [Hsub [Hfind_D [Hin_D Hwf_D]]]]].
  eapply wf_method_sig_types; eauto.
Qed.

Lemma method_sig_wf_parameters_by_find : forall CT C m mdef
  (Hwf_ct  : wf_class_table CT)
  (Hdom    : C < dom CT)
  (Hlookup : FindMethodWithName CT C m mdef),
  Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) (mparams (msignature mdef)).
Proof.
  intros CT C m mdef Hwf_ct Hdom Hlookup.
  assert (Hwf_inherited : exists D ddef, base_subtype CT C D /\ find_class CT D = Some ddef /\ In mdef (methods (body ddef)) /\ wf_method CT D mdef).
  {
    eapply method_lookup_in_wellformed_inherited; eauto.
  }
  destruct Hwf_inherited as [D [ddef [Hsub [Hfind_D [Hin_D Hwf_D]]]]].
  eapply wf_method_sig_types; eauto.
Qed.

Lemma In_gget_method_unique : forall method_list mdef m
  (Hnodup : NoDup (map (fun mdef => mname (msignature mdef)) method_list))
  (Hin    : In mdef method_list)
  (Hname  : mname (msignature mdef) = m),
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

Lemma In_gget_method_unique_class : forall CT C cdef mdef m
  (Hwf_ct : wf_class_table CT)
  (Hfind  : find_class CT C = Some cdef)
  (Hin    : In mdef (methods (body cdef)))
  (Hname  : mname (msignature mdef) = m),
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
    + (* WFObjectDef case *)
      rewrite Hno_methods.
      simpl.
      constructor.
    + (* WFOtherDef case *)
      destruct H as [_ [_ [Hnodup _]]].
      unfold bod in Hnodup.
      exact Hnodup.
  - exact Hin.
  - exact Hname.
Qed.

Lemma constructor_params_field_count : forall CT C ctor csig fields
  (Hwf_ct       : wf_class_table CT)
  (Hdom         : C < dom CT)
  (Hctor_lookup : constructor_def_lookup CT C = Some ctor)
  (Hcsig        : csig = csignature ctor)
  (Hcollect     : CollectFields CT C fields),
  List.length (cparams csig) = List.length fields.
Proof.
  intros CT C ctor csig fields Hwf_ct Hdom Hctor_lookup Hcsig Hcollect.
  subst csig.
  
  (* Move the quantified variables inside the induction *)
  revert ctor fields Hctor_lookup Hcollect.
  
  (* Strong induction on C *)
  induction C as [C IH] using lt_wf_ind.
  
  intros ctor fields Hctor_lookup Hcollect.
  (* Get the class definition *)
  assert (Hclass_exists : exists cdef, find_class CT C = Some cdef).
  {
    apply nth_error_Some_exists.
    exact Hdom.
  }
  destruct Hclass_exists as [cdef Hfind_class].
  
  (* Extract well-formedness of the class *)
  assert (Hwf_class : wf_class CT cdef).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  
  (* Extract constructor well-formedness *)
  assert (Hctor_eq : constructor (body cdef) = ctor).
  {
    unfold constructor_def_lookup in Hctor_lookup.
    rewrite Hfind_class in Hctor_lookup.
    injection Hctor_lookup as Hctor_eq.
    exact Hctor_eq.
  }
  
  (* Case analysis on class structure *)
  inversion Hwf_class; subst.
  - (* Object class case *)
    inversion Hcollect; subst.
    destruct (find_class CT C).
    easy.
    easy.
    unfold wf_constructor_object in Hwf_ctor.
    destruct Hwf_ctor as [_  [_ Hcparams]].
    destruct Hcparams as [_ [Hcparams _]].
    rewrite Hcparams.
    reflexivity.

    exfalso.
    assert (cdef = def) by (rewrite Hfind_class in Hfind; injection Hfind; auto).
    subst def.
    rewrite Hsuper in Hno_super.
    discriminate.
  - (* Regular class case with superclass *)
    destruct H as [Hwf_ctor [Hnodup_methods [Hforall_methods Hforall_fields]]].

    (* Extract class name consistency *)
    assert (Hcname_eq : cname sig = C).
    {
      apply find_class_cname_consistent in Hfind_class; auto.
    }
    unfold wf_constructor in Hwf_ctor.
    subst C0.
    destruct Hwf_ctor as [_ [_ [field_defs [Hcollect_field_defs [Hparams_eq _]]]]].
    assert (field_defs = fields).
    {
      eapply collect_fields_deterministic_rel; eauto.
      rewrite Hcname_eq.
      exact Hcollect.
    }
    subst field_defs.
    exact Hparams_eq.
Qed.

Lemma constructor_lookup_wf : forall CT C ctor
  (Hwf_ct       : wf_class_table CT)
  (Hdom         : C < dom CT)
  (Hctor_lookup : constructor_sig_lookup CT C = Some ctor),
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
  unfold wf_constructor.
  unfold wf_constructor.
  unfold wf_constructor_object in Hwf_ctor.
  destruct Hwf_ctor as [Hbound [H2314 [Hcparams [Hcollect_fields H2341]]]].
  assert (Hcname: cname (signature cdef) = C).
  { eapply find_class_cname_consistent; eauto. }
  unfold constructor_sig_lookup in Hctor_lookup.
  unfold constructor_def_lookup in Hctor_lookup.
  rewrite Hfind_class in Hctor_lookup.
  injection Hctor_lookup as Hctor_eq.
  subst ctor.
  simpl.
  repeat split.
  - rewrite Hcname in Hcparams. symmetry. exact Hcparams.
  - rewrite Hcollect_fields. constructor.
  - exists (@nil field_def).
    split.
    -- rewrite Hcname in H2341. exact H2341.
    -- split.
    + rewrite Hcollect_fields. reflexivity.
    + rewrite Hcollect_fields. constructor.
  -
  destruct H as [Hwf_ctor _].
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

Lemma eval_stmt_preserves_heap_domain_simple : forall CT rΓ h stmt rΓ' h'
  (Heval : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h'),
  dom h <= dom h'.
Proof.
  intros CT rΓ h stmt rΓ' h' Heval.
  remember OK as ok.
  induction Heval; try reflexivity; try discriminate.
  - (* FldWrite: h' = update_field h lx f v2 *)
    rewrite Hupdate.
    unfold update_field.
    rewrite Hobj.
    rewrite update_length.
    reflexivity.
  - (* New: h' = h ++ [new_obj] *)
    rewrite Hheap.
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

Lemma runtime_getObj_app_left : forall h h_ext loc obj
  (Hloc_dom : loc < dom h)
  (Hobj     : runtime_getObj h loc = Some obj),
  runtime_getObj (h ++ [h_ext]) loc = Some obj.
Proof.
  intros h h_ext loc obj Hloc_dom Hobj.
  unfold runtime_getObj in *.
  rewrite nth_error_app1.
  - exact Hloc_dom.
  - exact Hobj.
Qed.

(* Not just length, there is no statement can do strong update. *)
Lemma eval_stmt_preserves_r_type :
  forall CT rΓ h stmt rΓ' h' loc rqt
    (Heval     : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h')
    (Hrtype    : r_type h loc = Some rqt)
    (Hloc_dom  : loc < dom h),
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
  forall CT rΓ h stmt rΓ' h' loc q
    (Heval     : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h')
    (Hmut      : r_muttype h loc = Some q)
    (Hloc_dom  : loc < dom h),
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
      injection Hobj as H0_eq.
      subst ox.
      rewrite runtime_getObj_update_same.
      * exact Hloc_dom.
      * simpl. rewrite Hlx in Hmut. exact Hmut.
    + (* loc ≠ lx: unchanged *)
      unfold r_muttype in Hmut |- *.
      unfold update_field.
      injection Hobj as H0_eq.
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

Lemma wf_r_typable_env_independent : forall CT rΓ1 rΓ2 h loc qt l qcontext
  (Hreceiveraddr  : get_this_var_mapping (vars rΓ1) = Some l)
  (Henvsame       : get_this_var_mapping (vars rΓ1) = get_this_var_mapping (vars rΓ2))
  (Hreceiverrmut  : r_muttype h l = Some qcontext)
  (Hsame_this     : wf_r_typable CT rΓ1 h loc qt qcontext),
  wf_r_typable CT rΓ2 h loc qt qcontext.
Proof.
  intros CT rΓ1 rΓ2 h loc qt l qcontext Hreceiveraddr Henvsame Hreceiverrmut Hsame_this.
  unfold wf_r_typable in *.
  destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
  (* rewrite <- Hsame_this. *)
  (* destruct (get_this_var_mapping (vars rΓ1)) as [ι'|] eqn:Hthis; [|contradiction]. *)
  (* destruct (r_muttype h ι') as [q|] eqn:Hmut; [|contradiction]. *)
  exact Hsame_this.
Qed.

Lemma r_basetype_in_dom : forall CT h loc cy
  (Hwf_heap     : wf_heap CT h)
  (Hr_basetype  : r_basetype h loc = Some cy),
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

Lemma sq_vpa_tt_eq_qq_abs_imm :
  forall T1 T2,
    sqtype (vpa_mutability_tt_abs_imm T1 T2)
    = vpa_mutability_qq_abs_imm (sqtype T1) (sqtype T2).
Proof.
  intros T1 T2.
  destruct T1 as [q1 c1], T2 as [q2 c2].
  unfold vpa_mutability_tt_abs_imm, vpa_mutability_qq_abs_imm.
  simpl.
  destruct q1; destruct q2; reflexivity.
Qed.

Lemma sq_vpa_tt_eq_qq_safe_ro :
  forall T1 T2,
    sqtype (vpa_mutability_tt_safe_ro T1 T2)
    = vpa_mutability_qq_safe_ro (sqtype T1) (sqtype T2).
Proof.
  intros T1 T2.
  destruct T1 as [q1 c1], T2 as [q2 c2].
  unfold vpa_mutability_tt_safe_ro, vpa_mutability_qq_safe_ro.
  simpl.
  destruct q1; destruct q2; reflexivity.
Qed.

Lemma collect_fields_consistent_through_runtime_static : forall CT C D fields1 fields2 f fdef1 fdef2
  (Hwf_ct  : wf_class_table CT)
  (Hsub    : base_subtype CT C D)
  (Hcf1    : CollectFields CT C fields1)
  (Hcf2    : CollectFields CT D fields2)
  (Hget1   : gget fields1 f = Some fdef1)
  (Hget2   : gget fields2 f = Some fdef2),
  fdef1 = fdef2.
Proof.
  intros CT C D fields1 fields2 f fdef1 fdef2 Hwf_ct Hsub Hcf1 Hcf2 Hget1 Hget2.
  
  (* Generalize everything that varies *)
  revert fields1 fields2 f fdef1 fdef2 Hcf1 Hcf2 Hget1 Hget2.
  
  (* Now induct on Hsub *)
  induction Hsub; intros fields1 fields2 f fdef1 fdef2 Hcf1 Hcf2 Hget1 Hget2.
  
  - (* Reflexive: C = D *)
    assert (fields1 = fields2) by (eapply collect_fields_deterministic_rel; eauto).
    subst fields2.
    congruence.
    
  - (* Transitive: C <: D <: E *)
    (* Get fields for D *)
    assert (Hexists_D : exists fields_D, CollectFields CT D fields_D).
    { 
      (* D must be in CT domain since D <: E *)
      assert (HD_dom : D < dom CT).
      {
        eapply base_subtype_domain; eauto.
      }
      (* Use collect_fields_exists *)
      eapply collect_fields_exists; eauto.
    }
    destruct Hexists_D as [fields_D HcfD].
    
    (* Get field at f in D *)
    assert (Hget_D : exists fdef_D, gget fields_D f = Some fdef_D).
    {
      assert (Hlookup_E : FieldLookup CT E f fdef2).
      { apply FL_Found with fields2; auto. }
      assert (Hlookup_D : FieldLookup CT D f fdef2).
      { apply (field_inheritance_subtyping CT D E f fdef2); auto. }
      inversion Hlookup_D as [? ? fields_D' ? ? HcfD' HgetD'].
      assert (fields_D = fields_D') by (eapply collect_fields_deterministic_rel; eauto).
      subst fields_D'.
      exists fdef2.
      exact HgetD'.
    }
    destruct Hget_D as [fdef_D HgetD].
    
    (* Apply IH1: C <: D *)
    assert (fdef1 = fdef_D) by (eapply IHHsub1; eauto).
    
    (* Apply IH2: D <: E *)
    assert (fdef_D = fdef2) by (eapply IHHsub2; eauto).
    
    congruence.
    -
    assert (Hlookup1 : FieldLookup CT C f fdef1).
    { apply FL_Found with fields1; auto. }
    assert (Hlookup2 : FieldLookup CT D f fdef2).
    { apply FL_Found with fields2; auto. }
    assert (Hlookup_in_C : FieldLookup CT C f fdef2).
    { unfold parent_lookup in Hparent.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
    eapply field_inheritance_preserves_type; eauto.
    }
    eapply field_lookup_deterministic_rel; eauto.
Qed.

Lemma sf_assignability_consistent_subtype : forall CT C D f a1 a2
  (Hwf_ct : wf_class_table CT)
  (Hsub   : base_subtype CT C D)
  (Ha1    : sf_assignability_rel CT C f a1)
  (Ha2    : sf_assignability_rel CT D f a2),
  a1 = a2.
Proof.
  intros CT C D f a1 a2 Hwf_ct Hsub Ha1 Ha2.
  unfold sf_assignability_rel in *.
  destruct Ha1 as [fdef1 [Hlookup1 Hassign1]].
  destruct Ha2 as [fdef2 [Hlookup2 Hassign2]].
  inversion Hlookup1 as [? ? fields1 ? ? Hcf1 Hget1]; subst.
  inversion Hlookup2 as [? ? fields2 ? ? Hcf2 Hget2]; subst.
  assert (fdef1 = fdef2) by (eapply collect_fields_consistent_through_runtime_static; eauto).
  subst. congruence.
Qed.

Lemma correspondence_to_typable : forall CT sΓ rΓ h i sqt loc ι qcontext
  (Hreceiveraddr  : get_this_var_mapping (vars rΓ) = Some ι)
  (Hreceiverrmut  : (r_muttype h ι) = Some qcontext)
  (Hcorr          : forall i : nat,
                     i < dom sΓ ->
                     forall sqt : qualified_type,
                     nth_error sΓ i = Some sqt ->
                     match runtime_getVal rΓ i with
                     | Some Null_a => True
                     | Some (Iot loc) => wf_r_typable CT rΓ h loc sqt qcontext
                     | None => False
                     end)
  (Hi    : i < dom sΓ)
  (Hnth  : nth_error sΓ i = Some sqt)
  (Hval  : runtime_getVal rΓ i = Some (Iot loc)),
  wf_r_typable CT rΓ h loc sqt qcontext.
Proof.
  intros CT sΓ rΓ h i sqt loc ι qcontext Hreceiveraddr Hreceiverrmut Hcorr Hi Hnth Hval.
  specialize (Hcorr i Hi sqt Hnth).
  rewrite Hval in Hcorr.
  exact Hcorr.
Qed.

Lemma typable_to_base_and_qualifier : forall CT rΓ h loc sqt rq_obj rc_obj ι qcontext
  (Hreceiveraddr  : get_this_var_mapping (vars rΓ) = Some ι)
  (Hreceiverrmut  : r_muttype h ι = Some qcontext)
  (Hwf_typable    : wf_r_typable CT rΓ h loc sqt qcontext)
  (Hrtype         : r_type h loc = Some {| rqtype := rq_obj; rctype := rc_obj |}),
  base_subtype CT rc_obj (sctype sqt) /\
  qualifier_typable_context rq_obj (  (sqtype sqt)) qcontext.
Proof.
  intros CT rΓ h loc sqt rq_obj rc_obj ι qcontext Hreceiveraddr Hreceiverrmut Hwf_typable Hrtype.
  unfold wf_r_typable in Hwf_typable.
  rewrite Hrtype in Hwf_typable.
  exact Hwf_typable.
Qed.

Lemma qualifier_typable_subtype_receiver : forall rq Ty1 Ty2 qcontext
  (Hqual_ty1 : qualifier_typable_context rq (sqtype Ty1) qcontext)
  (Hsubtype  : sqtype Ty1 ⊑ sqtype Ty2),
  qualifier_typable_context rq (sqtype Ty2) qcontext.
Proof.
  intros rq Ty1 Ty2 qcontext Hqual_ty1 Hsubtype.
  unfold qualifier_typable_context in *.
  destruct rq as [|]; destruct (sqtype Ty1); destruct (sqtype Ty2);
  simpl in *; auto;
  try (inversion Hsubtype; auto);
  try unfold vpa_mutability_rs in *;
  try destruct qcontext;
  try reflexivity;
  try easy.
Qed.

Lemma gget_method_in : forall methods m mdef
  (Hget : gget_method methods m = Some mdef),
  In mdef methods.
Proof.
  intros methods m mdef Hget.
  unfold gget_method in Hget.
  apply find_some in Hget.
  destruct Hget as [Hin _].
  exact Hin.
Qed.

Lemma gget_method_in_iff : forall methods m mdef
  (Hnodup : NoDup (map (fun mdef => mname (msignature mdef)) methods)),
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

Lemma qualifier_typable_trans_subtype : forall rq T1 T2 T3 qcontext
  (Hqual : qualifier_typable_context rq (sqtype T1) qcontext)
  (H12   : sqtype T1 ⊑ sqtype T2)
  (H23   : sqtype T2 ⊑ sqtype T3),
  qualifier_typable_context rq (sqtype T3) qcontext.
Proof.
  intros rq T1 T2 T3 qcontext Hqual H12 H23.
  eapply qualifier_typable_subtype_receiver; [|exact H23].
  eapply qualifier_typable_subtype_receiver; [exact Hqual|exact H12].
Qed.

Lemma Forall2_from_nth : forall {A B} (P : A -> B -> Prop) l1 l2
  (Hlen  : List.length l1 = List.length l2)
  (Hprop : forall i a b, i < List.length l1 -> nth_error l1 i = Some a -> nth_error l2 i = Some b -> P a b),
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

Lemma get_this_var_mapping_update_nonzero : forall vs x v
  (Hx : x <> 0),
  get_this_var_mapping (update x v vs) = get_this_var_mapping vs.
Proof.
  intros vs x v Hx.
  unfold get_this_var_mapping.
  destruct vs as [|v0 vs']; simpl.
  - (* vs = [] *)
    destruct x as [|x']; [contradiction|].
    simpl. reflexivity.
  - (* vs = v0 :: vs' *)
    destruct x as [|x']; [contradiction|].
    simpl. reflexivity.
Qed.

Lemma get_this_var_mapping_update_vars_nonzero : forall rΓ x v
  (Hx : x <> 0),
  get_this_var_mapping (vars (set_vars rΓ (update x v (vars rΓ))))
  = get_this_var_mapping (vars rΓ).
Proof.
  intros rΓ x v Hx.
  simpl.
  apply get_this_var_mapping_update_nonzero.
  exact Hx.
Qed.

Lemma eval_stmt_preserves_receiver_addr_typed :
  forall CT sΓ mt rΓ h stmt sΓ' rΓ' h' ι
    (Htyp   : stmt_typing CT sΓ mt stmt sΓ')
    (Heval  : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h')
    (Hthis  : get_this_var_mapping (vars rΓ) = Some ι),
    get_this_var_mapping (vars rΓ') = Some ι.
Proof.
  intros CT sΓ mt rΓ h stmt sΓ' rΓ' h' ι Htyp Heval Hthis.
  remember OK as ok eqn:Hok.
  revert sΓ sΓ' Htyp Hthis.
  induction Heval; intros sΓ sΓ' Htyp Hthis'; subst; try discriminate;
  inversion Htyp; subst; simpl in *.
  - (* Skip *)
    assumption.
  - (* Local: vars rΓ' = vars rΓ ++ [Null_a] *)
    (* Updating rΓ's vars projection just adds at the tail. *)
    simpl.
    unfold get_this_var_mapping in *.
    destruct (vars rΓ) as [|v0 vs]; [discriminate|].
    (* head unchanged *)
    assumption.
  - (* VarAss x e *)
    simpl.
    destruct x as [|x']; simpl in *.
    + 
      exfalso.
      (* from the typing rule: x <> 0 *)
      easy.
    + (* x = S x' *)
      destruct (vars rΓ) as [|h0 l'] eqn:Hvars; simpl in *.
      * (* vars rΓ = [] *)
        (* Impossible, since Hthis = Some ι *)
        unfold get_this_var_mapping in Hthis.
        simpl in Hthis.
        discriminate.
      * (* vars rΓ = h0 :: l' *)
        exact Hthis'.
  - (* FldWrite *)
    assumption.
  - (* FldWrite *)
    assumption.
  - (* FldWrite *)
    assumption.  
  - (* FldWrite — ConcreteImm *)
    assumption.
  - (* New x q c ys *)
    simpl.
    destruct x as [|x']; simpl in *.
    + (* x = 0 is forbidden by typing (H10 : x <> 0) *)
      exfalso. easy.
    + (* non-zero index update does not change 'this' *)
      destruct (vars rΓ) as [|h0 l'] eqn:Hvars; simpl in *.
      * (* vars rΓ = [] *)
        (* Impossible, since Hthis = Some ι *)
        unfold get_this_var_mapping in Hthis.
        simpl in Hthis.
        discriminate.
      * (* vars rΓ = h0 :: l' *)
        exact Hthis'.
  - (* Call x m y zs *)
    simpl.
    destruct x as [|x']; simpl in *.
    + (* x = 0 is forbidden by typing (H10 : x <> 0) *)
      exfalso. easy.
    + (* non-zero index update does not change 'this' *)
      destruct (vars rΓ) as [|h0 l'] eqn:Hvars; simpl in *.
      * (* vars rΓ = [] *)
        (* Impossible, since Hthis = Some ι *)
        unfold get_this_var_mapping in Hthis.
        simpl in Hthis.
        discriminate.
      * (* vars rΓ = h0 :: l' *)
        exact Hthis'.  
  - (* Call x m y zs *)
    simpl.
    destruct x as [|x']; simpl in *.
    + (* x = 0 is forbidden by typing (H10 : x <> 0) *)
      exfalso. easy.
    + (* non-zero index update does not change 'this' *)
      destruct (vars rΓ) as [|h0 l'] eqn:Hvars; simpl in *.
      * (* vars rΓ = [] *)
        (* Impossible, since Hthis = Some ι *)
        unfold get_this_var_mapping in Hthis.
        simpl in Hthis.
        discriminate.
      * (* vars rΓ = h0 :: l' *)
        exact Hthis'.      
  - (* Seq s1 s2 *)
    eapply IHHeval2; eauto.
Qed.

Lemma eval_stmt_preserves_receiver_addr_typed_backwards :
  forall CT sΓ mt rΓ h stmt sΓ' rΓ' h' ι
    (Hwf    : wf_r_config CT sΓ rΓ h)
    (Htyp   : stmt_typing CT sΓ mt stmt sΓ')
    (Heval  : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h')
    (Hthis' : get_this_var_mapping (vars rΓ') = Some ι),
    get_this_var_mapping (vars rΓ) = Some ι.
Proof.
  intros CT sΓ mt rΓ h stmt sΓ' rΓ' h' ι Hwf Htyp Heval Hthis'.
  assert (Hthis : exists ι0, get_this_var_mapping (vars rΓ) = Some ι0).
  { 
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [Hrenv _]]].
    destruct Hrenv as [Hlen [Hreceiverval _]].
    destruct Hreceiverval as [ι0 Hthis0].
    exists ι0.
    destruct Hthis0 as [Hthis0 Hthisldom].
    exact Hthis0.
  }
  destruct Hthis as [ι0 Hthis0].
  (* forward preservation gives 'ι0' also at the end *)
  pose proof (eval_stmt_preserves_receiver_addr_typed
                CT sΓ mt rΓ h stmt sΓ' rΓ' h' ι0
                Htyp Heval Hthis0) as Hthis0'.
  (* uniqueness of Some _ *)
  rewrite Hthis' in Hthis0'.
  inversion Hthis0'; subst ι0.
  assumption.
Qed.

Lemma eval_stmt_preserves_receiver_addr_mapping_eq :
  forall CT sΓ mt rΓ h stmt sΓ' rΓ' h'
    (Hwf   : wf_r_config CT sΓ rΓ h)
    (Htyp  : stmt_typing CT sΓ mt stmt sΓ')
    (Heval : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h'),
    get_this_var_mapping (vars rΓ) =
    get_this_var_mapping (vars rΓ').
Proof.
  intros CT sΓ mt rΓ h stmt sΓ' rΓ' h' Hwf Htyp Heval.
  (* get some initial receiver address ι₀ from wf_r_config *)
  assert (Hthis : exists ι0, get_this_var_mapping (vars rΓ) = Some ι0).
  { 
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [Hrenv _]]].
    destruct Hrenv as [Hlen [Hreceiverval _]].
    destruct Hreceiverval as [ι0 Hthis0].
    exists ι0.
    destruct Hthis0 as [Hthis0 Hthisldom].
    exact Hthis0.
  }
  destruct Hthis as [ι0 Hthis0].
  pose proof (eval_stmt_preserves_receiver_addr_typed
                CT sΓ mt rΓ h stmt sΓ' rΓ' h' ι0
                Htyp Heval Hthis0) as Hthis0'.
  rewrite Hthis0.
  symmetry.
  exact Hthis0'.
Qed.

Corollary eval_stmt_preserves_receiver_addr_eq_loc' :
  forall CT sΓ mt rΓ h stmt sΓ' rΓ' h' ι1 ι2
    (Hwf    : wf_r_config CT sΓ rΓ h)
    (Htyp   : stmt_typing CT sΓ mt stmt sΓ')
    (Heval  : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h')
    (Hthis1 : get_this_var_mapping (vars rΓ)  = Some ι1)
    (Hthis2 : get_this_var_mapping (vars rΓ') = Some ι2),
    ι1 = ι2.
Proof.
  intros CT sΓ mt rΓ h stmt sΓ' rΓ' h' ι1 ι2
         Hwf Htyp Heval Hthis1 Hthis2.
  pose proof (eval_stmt_preserves_receiver_addr_mapping_eq
               CT sΓ mt rΓ h stmt sΓ' rΓ' h' Hwf Htyp Heval) as Heq.
  rewrite Hthis1 in Heq.
  rewrite Hthis2 in Heq.
  inversion Heq; reflexivity.
Qed.

Lemma eval_stmt_preserves_receiver_r_type_typed :
  forall CT sΓ mt rΓ h stmt sΓ' rΓ' h' ι rqt
    (Htyp    : stmt_typing CT sΓ mt stmt sΓ')
    (Heval   : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h')
    (Hthis   : get_this_var_mapping (vars rΓ) = Some ι)
    (Hrtype  : r_type h ι = Some rqt)
    (Hι_dom  : ι < dom h),
    r_type h' ι = Some rqt.
Proof.
  intros CT sΓ mt rΓ h stmt sΓ' rΓ' h' ι rqt Htyp Heval Hthis Hrtype Hι_dom.
  (* receiver address is preserved *)
  pose proof (eval_stmt_preserves_receiver_addr_typed
                CT sΓ mt rΓ h stmt sΓ' rΓ' h' ι
                Htyp Heval Hthis) as Hthis'.
  (* heap domain grows *)
  pose proof (eval_stmt_preserves_heap_domain_simple CT rΓ h stmt rΓ' h' Heval)
    as Hdom_le.
  assert (Hι_dom' : ι < dom h') by lia.
  (* type invariant on that fixed loc *)
  eapply eval_stmt_preserves_r_type; eauto.
Qed.

Lemma eval_stmt_preserves_receiver_r_muttype_typed :
  forall CT sΓ mt rΓ h stmt sΓ' rΓ' h' ι q
    (Htyp    : stmt_typing CT sΓ mt stmt sΓ')
    (Heval   : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h')
    (Hthis   : get_this_var_mapping (vars rΓ) = Some ι)
    (Hmut    : r_muttype h ι = Some q)
    (Hι_dom  : ι < dom h),
    r_muttype h' ι = Some q.
Proof.
  intros CT sΓ mt rΓ h stmt sΓ' rΓ' h' ι q Htyp Heval Hthis Hmut Hι_dom.
  (* receiver address is preserved *)
  pose proof (eval_stmt_preserves_receiver_addr_typed
                CT sΓ mt rΓ h stmt sΓ' rΓ' h' ι
                Htyp Heval Hthis) as Hthis'.
  (* heap domain grows *)
  pose proof (eval_stmt_preserves_heap_domain_simple CT rΓ h stmt rΓ' h' Heval)
    as Hdom_le.
  assert (Hι_dom' : ι < dom h') by lia.
  (* mutability invariant on that fixed loc *)
  eapply eval_stmt_preserves_r_muttype; eauto.
Qed.

Lemma eval_stmt_preserves_r_type_backwards :
  forall CT rΓ h stmt rΓ' h' loc rqt
    (Heval     : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h')
    (Hrtype'   : r_type h' loc = Some rqt)
    (Hloc_dom  : loc < dom h),
    r_type h loc = Some rqt.
Proof.
  intros CT rΓ h stmt rΓ' h' loc rqt Heval Hrtype' Hloc_dom.
  (* Case on r_type h loc *)
  destruct (r_type h loc) as [rqt0|] eqn:Hrtype0.
  - (* Some rqt0; use forward lemma and equality *)
    specialize (eval_stmt_preserves_r_type CT rΓ h stmt rΓ' h' loc rqt0 Heval Hrtype0 Hloc_dom)
      as Hforward.
    rewrite Hforward in Hrtype'.
    inversion Hrtype'; subst rqt0.
    assumption.
  - (* None: impossible, because then no obj at loc in h but there is one in h' *)
    unfold r_type in Hrtype0.
    destruct (runtime_getObj h loc) as [o|] eqn:Hobj; [discriminate|].
    exfalso.
    apply runtime_getObj_not_dom in Hobj.
    lia.
Qed.

Lemma eval_stmt_preserves_receiver_r_type_typed_backwards :
  forall CT sΓ mt rΓ h stmt sΓ' rΓ' h' ι rqt
    (Hwf     : wf_r_config CT sΓ rΓ h)
    (Htyp    : stmt_typing CT sΓ mt stmt sΓ')
    (Heval   : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h')
    (Hthis'  : get_this_var_mapping (vars rΓ') = Some ι)
    (Hrtype' : r_type h' ι = Some rqt)
    (Hι_dom  : ι < dom h),
    r_type h ι = Some rqt.
Proof.
  intros CT sΓ mt rΓ h stmt sΓ' rΓ' h' ι rqt
         Hwf Htyp Heval Hthis' Hrtype' Hι_dom.
  (* get initial receiver address ι0 from wf_r_config *)
  assert (Hthis : exists ι0, get_this_var_mapping (vars rΓ) = Some ι0).
  { 
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [Hrenv _]]].
    destruct Hrenv as [Hlen [Hreceiverval _]].
    destruct Hreceiverval as [ι0 Hthis0].
    exists ι0.
    destruct Hthis0 as [Hthis0 Hthisldom].
    exact Hthis0.
  }
  destruct Hthis as [ι0 Hthis0].
  (* receiver addr is preserved forward, so at end we also have ι0 *)
  pose proof (eval_stmt_preserves_receiver_addr_typed
                CT sΓ mt rΓ h stmt sΓ' rΓ' h' ι0
                Htyp Heval Hthis0) as Hthis0'.
  rewrite Hthis' in Hthis0'.
  inversion Hthis0'; subst ι0.
  (* now ι is same initial receiver; apply backward r_type lemma *)
  eapply eval_stmt_preserves_r_type_backwards; eauto.
Qed.

Lemma eval_stmt_preserves_r_muttype_backwards :
  forall CT rΓ h stmt rΓ' h' loc q
    (Heval     : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h')
    (Hmut'     : r_muttype h' loc = Some q)
    (Hloc_dom  : loc < dom h),
    r_muttype h loc = Some q.
Proof.
  intros CT rΓ h stmt rΓ' h' loc q Heval Hmut' Hloc_dom.
  destruct (r_muttype h loc) as [q0|] eqn:Hmut0.
  - specialize (eval_stmt_preserves_r_muttype CT rΓ h stmt rΓ' h' loc q0
               Heval Hmut0 Hloc_dom) as Hforward.
    rewrite Hforward in Hmut'.
    inversion Hmut'; subst q0.
    assumption.
  - unfold r_muttype in Hmut0.
    destruct (runtime_getObj h loc) as [o|] eqn:Hobj; [discriminate|].
    exfalso.
    apply runtime_getObj_not_dom in Hobj.
    lia.
Qed.

Lemma eval_stmt_preserves_receiver_r_muttype_typed_backwards :
  forall CT sΓ mt rΓ h stmt sΓ' rΓ' h' ι q
    (Hwf     : wf_r_config CT sΓ rΓ h)
    (Htyp    : stmt_typing CT sΓ mt stmt sΓ')
    (Heval   : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h')
    (Hthis'  : get_this_var_mapping (vars rΓ') = Some ι)
    (Hmut'   : r_muttype h' ι = Some q)
    (Hι_dom  : ι < dom h),
    r_muttype h ι = Some q.
Proof.
  intros CT sΓ mt rΓ h stmt sΓ' rΓ' h' ι q
         Hwf Htyp Heval Hthis' Hmut' Hι_dom.
  (* same receiver address argument as in type lemma *)
  assert (Hthis : exists ι0, get_this_var_mapping (vars rΓ) = Some ι0).
  { 
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [Hrenv _]]].
    destruct Hrenv as [Hlen [Hreceiverval _]].
    destruct Hreceiverval as [ι0 Hthis0].
    exists ι0.
    destruct Hthis0 as [Hthis0 Hthisldom].
    exact Hthis0.
  }
  destruct Hthis as [ι0 Hthis0].
  pose proof (eval_stmt_preserves_receiver_addr_typed
                CT sΓ mt rΓ h stmt sΓ' rΓ' h' ι0
                Htyp Heval Hthis0) as Hthis0'.
  rewrite Hthis' in Hthis0'.
  inversion Hthis0'; subst ι0.
  eapply eval_stmt_preserves_r_muttype_backwards; eauto.
Qed.

Lemma preservation_skip :
  forall CT sΓ mt rΓ h sΓ'
    (Htyping : stmt_typing CT sΓ mt SSkip sΓ')
    (Hwf     : wf_r_config CT sΓ rΓ h),
    wf_r_config CT sΓ' rΓ h.
Proof.
  intros CT sΓ mt rΓ h sΓ' Htyping Hwf.
  inversion Htyping; subst; exact Hwf.
Qed.

Lemma preservation_local_ok :
  forall CT sΓ mt rΓ h T x rΓ' h' sΓ'
    (Hwf     : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt (SLocal T x) sΓ')
    (Heval   : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h (SLocal T x) OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h'),
    wf_r_config CT sΓ' rΓ' h'.
Proof.
    intros CT sΓ mt rΓ h T x rΓ' h' sΓ' Hwf Htyping Heval.
    inversion Heval; subst.
    inversion Htyping; subst.
    unfold wf_r_config in *.
    destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) 
    unfold  wf_class_table in Hclass. destruct Hclass as [Hclass _]. exact Hclass.
    + (* Object wellformedness *)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [Hobject _]]. exact Hobject.
    + (* All other classes have super class*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[Hotherclasses _]]]. exact Hotherclasses.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
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
        -- exact Hwf_T. (* assuming H is the wellformedness of T *)
        -- constructor. (* empty tail is well-typed *)
    + (* length equality *)
      simpl. rewrite length_app. simpl. rewrite Hlen. rewrite length_app. simpl. lia.
    + (* correspondence between static and runtime environments *)
      intros ι qcontext HreceiverAddr Hreceivermut i Hi sqt Hnth.
      destruct (Nat.eq_dec i (dom sΓ)) as [Heq | Hneq].
      * (* Case: i = dom sΓ (new variable) *)
        subst i.
        unfold runtime_getVal.
        simpl.
        rewrite nth_error_app2.
        -- rewrite Hlen.
           trivial.
        -- rewrite Hlen.
           assert (Hzero : dom (vars rΓ) - dom (vars rΓ) = 0) by lia.
            rewrite Hzero.
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
        rewrite (get_this_var_mapping_update_vars_app_null rΓ) in HreceiverAddr.
        specialize (Hcorr ι qcontext HreceiverAddr Hreceivermut i Hi_old sqt Hnth_old).
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
Qed.

Lemma preservation_varass_ok :
  forall CT sΓ mt rΓ h x e rΓ' h' sΓ'
    (Hwf              : wf_r_config CT sΓ rΓ h)
    (Htyping          : stmt_typing CT sΓ mt (SVarAss x e) sΓ')
    (Heval_stmt       : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h (SVarAss x e) OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h'),
    wf_r_config CT sΓ' rΓ' h'.
Proof.
    intros CT sΓ mt rΓ h x e rΓ' h' sΓ' Hwf Htyping Heval_stmt.
    inversion Heval_stmt; subst.
    rename Hval into Htarget.
    rename Heval into Heval_expr.
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
    + (* Object wellformedness *)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [Hobject _]]. exact Hobject.
    + (* All other classes have super class*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[Hotherclasses _]]]. exact Hotherclasses.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
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
      -- inversion Heval_expr; subst.
        (* assert (Hloc_in_vars : exists i, nth_error (vars rΓ) i = Some (Iot loc)). *)
        ++ 
          assert (Hx0_bound : x0 < dom (vars rΓ)).
          {
            apply runtime_getVal_dom in Hval.
            exact Hval.
          }
          unfold runtime_getVal in Hval.
          assert (Hnth_loc : nth_error (vars rΓ) x0 = Some (Iot loc)) by exact Hval.
          eapply Forall_nth_error in Hallvals; eauto.
          simpl in Hallvals.
          exact Hallvals.
        ++ 
          pose proof (runtime_getObj_dom v o _ Hobj) as Hv_bound.
          specialize (Hheap v Hv_bound).
          unfold wf_obj in Hheap.
          rewrite Hobj in Hheap.
          destruct Hheap as [_ [field_defs [Hcollect [Hlen_eq Hforall2]]]].
          assert (Hf_bound : f < List.length (fields_map o)).
          {
            apply nth_error_Some.
            unfold getVal in Hfield.
            rewrite Hfield.
            discriminate.
          }
          rewrite Hlen_eq in Hf_bound.
          assert (Hfield_def : exists fdef, nth_error field_defs f = Some fdef).
          {
            apply nth_error_Some_exists.
            exact Hf_bound.
          }
          destruct Hfield_def as [fdef Hfdef].
          unfold getVal in Hfield.
          eapply Forall2_nth_error in Hforall2; eauto.
          simpl in Hforall2.
          destruct (runtime_getObj h' loc) as [obj|] eqn:Hloc_obj.
          --- (* Case: runtime_getObj h' loc = Some obj *)
            trivial.
          --- (* Case: runtime_getObj h' loc = None *)
            contradiction Hforall2.
    * assert(Htarget_exists : exists v, nth_error (vars rΓ) x = Some v).
      {
        exists v1.
        exact Htarget.
      }
      destruct Htarget_exists as [v Hnth].
      apply runtime_getVal_dom in Hnth.
      exact Hnth.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvLength. 
    + (* wellformed static environment *)
      destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvWellTyped.
    + (* length equality *)
      simpl.
      rewrite update_length.
      exact Hlen.
    + (* correspondence between static and runtime environments *)
      intros ι qcontext HreceiverAddr Hreceivermut i Hi sqt Hnth.
      destruct (Nat.eq_dec i x) as [Heq | Hneq].
      * (* Case: i = x (updated variable) *)
        subst i.
        unfold runtime_getVal.
        simpl.
        rewrite update_same.
        rewrite <- Hlen; exact Hi.
        destruct v2 as [|loc] eqn: Hv2.
        -- (* Case: v2 = Null_a *)
          trivial.
        -- (* Case: v2 = Iot loc *)
          (* Use subtyping to convert from T to sqt *)
          assert (Hsubtype_preserved : wf_r_typable CT (set_vars rΓ (update x (Iot loc) (vars rΓ))) h' loc sqt qcontext).
          {
            assert (Hsqt_eq : sqt = Tx).
          {
            unfold static_getType in Hget_x.
            rewrite Hget_x in Hnth.
            injection Hnth as Hsqt_eq.
            symmetry. exact Hsqt_eq.
          }
          subst sqt.
          assert (H_loc_Te : wf_r_typable CT rΓ h' loc Te qcontext).
          {
            (* Apply expression evaluation preservation lemma *)
            apply (expr_eval_preservation (reachable_locations_from_initial_env CT h' rΓ) CT sΓ' mt rΓ h' e (Iot loc) rΓ h' Te ι).
            auto.
            - rewrite get_this_var_mapping_update_vars_nonzero in HreceiverAddr. exact Hnot_rcv. exact HreceiverAddr.
            - exact Hreceivermut.
            - exact Hwfcopy.
            - exact Htype_e.
            - exact Heval_expr.
          }
          eapply wf_r_typable_subtype with (T1:=Te)(T2:=Tx); eauto.
          }
          unfold wf_r_typable in *.
          exact Hsubtype_preserved.
      * (* Case: i ≠ x (unchanged variable) *)
        {
          unfold runtime_getVal.
          simpl.
          rewrite update_diff.
          - symmetry. exact Hneq.
          -
            rewrite get_this_var_mapping_update_vars_nonzero in HreceiverAddr. exact Hnot_rcv.
            assert (Hcorr_orig := Hcorr ι qcontext HreceiverAddr Hreceivermut i Hi sqt Hnth).
            unfold runtime_getVal in Hcorr_orig.
            destruct (nth_error (vars rΓ) i) as [v|] eqn:Hval.
            + destruct v as [|loc].
              * trivial.
              * unfold wf_r_typable in Hcorr_orig |- *.
                destruct (r_type h' loc) as [rqt|] eqn:Hrtype; [|contradiction].
                exact Hcorr_orig.
            + contradiction.
        }
Qed.

Lemma get_this_exists_from_wf_r_config :
  forall CT sΓ rΓ h
    (Hwf : wf_r_config CT sΓ rΓ h),
    exists ι, get_this_var_mapping (vars rΓ) = Some ι.
Proof.
  intros CT sΓ rΓ h Hwf.
  destruct Hwf as [_ [_ [Hrenv _]]].
  destruct Hrenv as [_ [Hrecv _]].
  destruct Hrecv as [ι [Hthis _]].
  now exists ι.
Qed.

Lemma receiver_mutability_exists_wf_renv :
  forall CT rΓ h ι
    (Hrenv  : wf_renv CT rΓ h)
    (Hthis  : get_this_var_mapping (vars rΓ) = Some ι),
    exists qcontext, r_muttype h ι = Some qcontext.
Proof.
  intros CT rΓ h ι [HrLen [Hrecv Hall]] Hthis.
  unfold get_this_var_mapping in Hthis.
  destruct (vars rΓ) as [|v vs]; [discriminate|].
  destruct v as [|loc]; try discriminate.
  simpl in Hthis. inversion Hthis; subst loc.
  apply Forall_inv in Hall.
  simpl in Hall.
  destruct (runtime_getObj h ι) as [o|] eqn:Hobj; [|contradiction].
  unfold r_muttype. rewrite Hobj. eauto.
Qed.

Lemma rqtype_update_field_invariant : forall o f v,
  rqtype (rt_type (set_fields_map o (update f v (fields_map o))))
  = rqtype (rt_type o).
Proof.
  intros [rt fm] f v; simpl; reflexivity.
Qed.

Lemma r_muttype_update_field_preserve :
  forall h locx f v loc,
    r_muttype (update_field h locx f v) loc
  = r_muttype h loc.
Proof.
  intros h locx f v loc.
  unfold r_muttype, update_field.
  destruct (runtime_getObj h locx) as [o_x|] eqn:Hobjx.
  - destruct (Nat.eq_dec loc locx) as [Heq|Hneq].
    + subst loc.
      rewrite runtime_getObj_update_same.
      * f_equal. apply runtime_getObj_dom in Hobjx.
        exact Hobjx.
      * rewrite Hobjx.
        simpl.
        reflexivity.
    + rewrite runtime_getObj_update_diff; [symmetry; exact Hneq|].
      reflexivity.
  - reflexivity.
Qed.

Lemma preservation_fldwrite_ok_abs_imm :
  forall CT sΓ rΓ h x f y h' sΓ'
    (Hwf     : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ AbstractImm (SFldWrite x f y) sΓ')
    (Heval   : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h (SFldWrite x f y) OK (reachable_locations_from_initial_env CT h rΓ) rΓ h'),
    wf_r_config CT sΓ' rΓ h'.
Proof.
    intros CT sΓ rΓ h x f y h' sΓ' Hwf Htyping Heval.
    inversion Heval; subst.
    rename Hval_x into Hgetx.
    rename Hobj into Hgetobj.
    rename Hfield into Hgetf.
    rename Hval_y into Hgety.
    have Hwfcopy := Hwf.
    inversion Htyping; subst.
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) 
    unfold  wf_class_table in Hclass. destruct Hclass as [Hclass _]. exact Hclass.
    + (* Object wellformedness *)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [Hobject _]]. exact Hobject.
    + (* All other classes have super class*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[Hotherclasses _]]]. exact Hotherclasses.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
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
                injection Hgetobj as Ho_eq. subst o_x.
                apply getVal_dom in Hgetf. exact Hgetf.
              }
              rewrite <- Hlen_eq. exact Hf_valid.

              intros b Hnth_b.
              destruct val_y as [|loc_y]; [trivial|].

              assert (Hx_dom : x < dom sΓ').
              {
                apply static_getType_dom in Hget_x. exact Hget_x.
              }

              assert (Hy_dom : y < dom sΓ').
              {
                apply static_getType_dom in Hget_y. exact Hget_y.
              }
              have Hcorrcopy := Hcorr.
              assert (Hthis_exists : exists ι, get_this_var_mapping (vars rΓ) = Some ι).
              {
                eapply get_this_exists_from_wf_r_config; eauto.
              }
              destruct Hthis_exists as [ι HreceiverAddr].
              assert (Hqcontext_exists : exists qcontext, r_muttype h ι = Some qcontext).
              {
                eapply receiver_mutability_exists_wf_renv; eauto.
              }
              destruct Hqcontext_exists as [qcontext Hreceivermut].
              have Hcorropy := Hcorr.
              specialize (Hcorr ι qcontext HreceiverAddr Hreceivermut x Hx_dom Tx Hget_x).
              destruct (runtime_getVal rΓ x) as [val_x|] eqn:Hx_val; [|contradiction].
              injection Hgetx as H_val_eq.
              subst val_x.
              unfold update_field.
              destruct (runtime_getObj h loc_x) as [o_lx|] eqn:Hobj_lx; [|easy].
              destruct (Nat.eq_dec loc_y loc_x) as [Heq_loc2_lx | Hneq_loc2_lx].
              specialize (Hcorrcopy ι qcontext HreceiverAddr Hreceivermut y Hy_dom Ty Hget_y).
              destruct (runtime_getVal rΓ y) as [val_y|] eqn:Hy_val; [|contradiction].
              injection Hgety as H_val_eq.
              subst val_y.
              unfold update_field.
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
                  injection Hgetobj as Ho_eq2.
                  subst o_lx o_x.
                  exact Hrtype_x.
                  injection Hobj as Ho_lx_eq.
                  injection Hgetobj as Ho_x_eq.
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
                    unfold sf_def_rel in Hfld_def.
                    inversion Hfld_def; subst.
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
                  apply qualified_type_subtype_base_subtype in Hsub.
                  simpl in Hsub.
                  eapply base_trans; eauto.

                  (* Qualifier *)
                  apply get_this_qualified_type_nth_error in Hthis.
                  unfold wf_senv in Hsenv;
                  destruct Hsenv as [Hsenvdom _];
                  apply qualified_type_subtype_q_subtype in Hsub.
                  simpl in Hsub.
                  unfold qualifier_typable_heap.
                  move Hsub at bottom.
                  move Hqual_typable at bottom.
                  unfold vpa_mutability_rec_fld; unfold vpa_mutability_stype_fld_abs_imm in Hsub.
                  subst rqt_x.

                  clear - Hsub Hqual_typable Hxyqualifer.
                  all: destruct (rqtype (rt_type o)) eqn: rq;
                  destruct (mutability (ftype fieldT)) eqn: HfieldMut;
                  simpl;
                  simpl in Hsub; try trivial.
                  all: 
                  destruct (sqtype Tx) eqn: qx;
                  destruct (sqtype Ty) eqn: qy;
                  simpl in Hsub;
                  try solve_q_subtype_wrong.
                  all:
                  destruct qcontext eqn: Hqcontext;
                  try solve_qualifier_typable_wrong_concrete.
            }

            have H11copy := Hsub.
            apply qualified_type_subtype_q_subtype in Hsub. 
            destruct (nth_error h loc_y) as [obj_y|] eqn:Hnth_y.
            - (* loc_y exists in original heap *)
              assert (Hnth_updated : nth_error (update loc_x (set_fields_map o_x (update f (Iot loc_y) (fields_map o_x))) h) loc_y = Some obj_y).
              {
                rewrite nth_error_update_neq; [symmetry; exact Hneq_loc2_lx | exact Hnth_y].
              }
              rewrite Hnth_updated.
              specialize (Hcorrcopy ι qcontext HreceiverAddr Hreceivermut y Hy_dom Ty Hget_y).
              rewrite Hgety in Hcorrcopy.
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
                unfold sf_def_rel in Hfld_def.
                inversion Hfld_def; subst.
                symmetry.
                eapply collect_fields_consistent_through_runtime_static with (C:=(rctype (rt_type o_x)))(fields1:=Hlen_fields)(fields2:=fields)(fdef1:=b)(fdef2:=fieldT); eauto.
                apply qualified_type_subtype_base_subtype in H11copy.
                simpl in H11copy.
                unfold wf_r_typable in Hcorr.
                unfold r_type in Hcorr.
                rewrite Hobj_lx in Hcorr.
                destruct Hcorr as [Hbase_sub Hqual_typable].
                inversion Hobj.
                subst o_lx.
                exact Hbase_sub.
              }
              subst b.
              split.
              + (* Base type equality *)
                apply qualified_type_subtype_base_subtype in H11copy.
                (* apply vpa_preserve_basetype_subtype in H11copy. *)
                simpl in H11copy.
                eapply base_trans; eauto.
              + (* Qualifier typable *)
                apply get_this_qualified_type_nth_error in Hthis.
                unfold wf_senv in Hsenv;
                destruct Hsenv as [Hsenvdom _];
                move Hsub at bottom.
                inversion Hlen.
                inversion Hobj.
                subst.
                unfold qualifier_typable_heap.
                unfold qualifier_typable_context in Hqual_y.
                unfold wf_r_typable in Hcorr.
                unfold r_type in Hcorr.
                rewrite Hobj_lx in Hcorr.
                destruct Hcorr as [_ Hqualifiertypablex].
                inversion Hgetobj; subst o.
                unfold vpa_mutability_stype_fld_abs_imm in Hsub.
                unfold vpa_mutability_rec_fld.
                unfold vpa_mutability_rs in Hqual_y.
                clear - Hqual_y Hsub Hqualifiertypablex.
                all:
                destruct (rqtype rqt_y) eqn: Hrqy;
                destruct (rqtype (rt_type o_x)) eqn: Hrqx;
                destruct (mutability (ftype fieldT)) eqn: Hfield;
                try trivial.

                all:
                destruct (sqtype Ty) eqn: Hsqy;
                destruct qcontext eqn: Hqcontext;
                simpl in Hqual_y;
                try solve_q_subtype_wrong.

                all:
                destruct (sqtype Tx) eqn: Hsqx;
                simpl in Hsub;
                try solve_q_subtype_wrong;
                try solve_qualifier_typable_wrong_concrete.

                all: try easy.
            - (* loc_y doesn't exist - contradiction *)
              assert (Hnth_updated : nth_error (update loc_x (set_fields_map o_x (update f (Iot loc_y) (fields_map o_x))) h) loc_y = None).
              {
                rewrite nth_error_update_neq; [symmetry; exact Hneq_loc2_lx | exact Hnth_y].
              }
              rewrite Hnth_updated.
              exfalso.
              specialize (Hcorrcopy ι qcontext HreceiverAddr Hreceivermut y Hy_dom Ty Hget_y).
              rewrite Hgety in Hcorrcopy.
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
          discriminate Hgetobj.
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
    intros ι qcontext HreceiverAddr Hreceivermut i Hi sqt Hnth.
      assert (r_muttype h ι = Some qcontext) as Hreceivermut_orig.
      {
        rewrite (r_muttype_update_field_preserve h loc_x f val_y ι) in Hreceivermut.
        exact Hreceivermut.
      }
      assert (Hcorr_orig := Hcorr ι qcontext HreceiverAddr Hreceivermut_orig i Hi sqt Hnth).
      destruct (runtime_getVal rΓ i) as [v|] eqn:Hval; [|exact Hcorr_orig].
      destruct v as [|loc]; [trivial|].
      unfold wf_r_typable in Hcorr_orig |- *.
      destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
      assert (Hrtype_preserved : r_type (update_field h loc_x f val_y) loc = Some rqt).
      {
        unfold r_type.
        unfold update_field.
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
            f_equal.
            injection Hobj_eq_copy as Ho_eq.
            rewrite Ho_eq.
            reflexivity.
          + rewrite runtime_getObj_update_diff.
            * symmetry. exact Hneq.
            * exact Hrtype.
        - exact Hrtype.
      }
      rewrite Hrtype_preserved.
      exact Hcorr_orig.
Qed.

Lemma preservation_fldwrite_ok_safe_ro :
  forall CT sΓ rΓ h x f y h' sΓ'
    (Hwf     : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ SafeRO (SFldWrite x f y) sΓ')
    (Heval   : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h (SFldWrite x f y) OK (reachable_locations_from_initial_env CT h rΓ) rΓ h'),
    wf_r_config CT sΓ' rΓ h'.
Proof.
    intros CT sΓ rΓ h x f y h' sΓ' Hwf Htyping Heval.
    inversion Heval; subst.
    rename Hval_x into Hgetx.
    rename Hobj into Hgetobj.
    rename Hfield into Hgetf.
    rename Hval_y into Hgety.
    have Hwfcopy := Hwf.
    inversion Htyping; subst.
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) 
    unfold  wf_class_table in Hclass. destruct Hclass as [Hclass _]. exact Hclass.
    + (* Object wellformedness *)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [Hobject _]]. exact Hobject.
    + (* All other classes have super class*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[Hotherclasses _]]]. exact Hotherclasses.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
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
                injection Hgetobj as Ho_eq. subst o_x.
                apply getVal_dom in Hgetf. exact Hgetf.
              }
              rewrite <- Hlen_eq. exact Hf_valid.

              intros b Hnth_b.
              destruct val_y as [|loc_y]; [trivial|].

              assert (Hx_dom : x < dom sΓ').
              {
                apply static_getType_dom in Hget_x. exact Hget_x.
              }

              assert (Hy_dom : y < dom sΓ').
              {
                apply static_getType_dom in Hget_y. exact Hget_y.
              }
              have Hcorrcopy := Hcorr.
              assert (Hthis_exists : exists ι, get_this_var_mapping (vars rΓ) = Some ι).
              {
                eapply get_this_exists_from_wf_r_config; eauto.
              }
              destruct Hthis_exists as [ι HreceiverAddr].
              assert (Hqcontext_exists : exists qcontext, r_muttype h ι = Some qcontext).
              {
                eapply receiver_mutability_exists_wf_renv; eauto.
              }
              destruct Hqcontext_exists as [qcontext Hreceivermut].
              have Hcorropy := Hcorr.
              specialize (Hcorr ι qcontext HreceiverAddr Hreceivermut x Hx_dom Tx Hget_x).
              destruct (runtime_getVal rΓ x) as [val_x|] eqn:Hx_val; [|contradiction].
              injection Hgetx as H_val_eq.
              subst val_x.
              unfold update_field.
              destruct (runtime_getObj h loc_x) as [o_lx|] eqn:Hobj_lx; [|easy].
              destruct (Nat.eq_dec loc_y loc_x) as [Heq_loc2_lx | Hneq_loc2_lx].
              specialize (Hcorrcopy ι qcontext HreceiverAddr Hreceivermut y Hy_dom Ty Hget_y).
              destruct (runtime_getVal rΓ y) as [val_y|] eqn:Hy_val; [|contradiction].
              injection Hgety as H_val_eq.
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
                  injection Hgetobj as Ho_eq2.
                  subst o_lx o_x.
                  exact Hrtype_x.
                  injection Hobj as Ho_lx_eq.
                  injection Hgetobj as Ho_x_eq.
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
                    unfold sf_def_rel in Hfld_def.
                  inversion Hfld_def; subst.
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
                apply qualified_type_subtype_base_subtype in Hsub.
                (* apply vpa_preserve_basetype_subtype in H11. *)
                simpl in Hsub.
                eapply base_trans; eauto.

                (* Qualifier *)
                apply get_this_qualified_type_nth_error in Hthis.
                unfold wf_senv in Hsenv;
                destruct Hsenv as [Hsenvdom _];
                apply qualified_type_subtype_q_subtype in Hsub.
                simpl in Hsub.
                unfold qualifier_typable_heap.
                move Hsub at bottom.
                move Hqual_typable at bottom.
                unfold vpa_mutability_rec_fld; unfold vpa_mutability_stype_fld_abs_imm in Hsub.
                subst rqt_x.

                clear - Hsub Hqual_typable Hxyqualifer.
                all: destruct (rqtype (rt_type o)) eqn: rq;
                destruct (mutability (ftype fieldT)) eqn: HfieldMut;
                simpl;
                simpl in Hsub; try trivial.
                all: 
                destruct (sqtype Tx) eqn: qx;
                destruct (sqtype Ty) eqn: qy;
                simpl in Hsub;
                try solve_q_subtype_wrong.
                all:
                destruct qcontext eqn: Hqcontext;
                try solve_qualifier_typable_wrong_concrete.
            }

            have H11copy := Hsub.
            apply qualified_type_subtype_q_subtype in Hsub.
            destruct (nth_error h loc_y) as [obj_y|] eqn:Hnth_y.
            - (* loc_y exists in original heap *)
              assert (Hnth_updated : nth_error (update loc_x (set_fields_map o_x (update f (Iot loc_y) (fields_map o_x))) h) loc_y = Some obj_y).
              {
                rewrite nth_error_update_neq; [symmetry; exact Hneq_loc2_lx | exact Hnth_y].
              }
              rewrite Hnth_updated.
              specialize (Hcorrcopy ι qcontext HreceiverAddr Hreceivermut y Hy_dom Ty Hget_y).
              rewrite Hgety in Hcorrcopy.
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
                unfold sf_def_rel in Hfld_def.
                inversion Hfld_def; subst.
                symmetry.
                eapply collect_fields_consistent_through_runtime_static with (C:=(rctype (rt_type o_x)))(fields1:=Hlen_fields)(fields2:=fields)(fdef1:=b)(fdef2:=fieldT); eauto.
                apply qualified_type_subtype_base_subtype in H11copy.
                simpl in H11copy.
                unfold wf_r_typable in Hcorr.
                unfold r_type in Hcorr.
                rewrite Hobj_lx in Hcorr.
                destruct Hcorr as [Hbase_sub Hqual_typable].
                inversion Hobj.
                subst o_lx.
                exact Hbase_sub.
              }
              subst b.
              split.
              + (* Base type equality *)
                apply qualified_type_subtype_base_subtype in H11copy.
                (* apply vpa_preserve_basetype_subtype in H11copy. *)
                simpl in H11copy.
                eapply base_trans; eauto.
              + (* Qualifier typable *)
                apply get_this_qualified_type_nth_error in Hthis.
                unfold wf_senv in Hsenv;
                destruct Hsenv as [Hsenvdom _];
                move Hsub at bottom.
                inversion Hlen.
                inversion Hobj.
                subst.
                unfold qualifier_typable_heap.
                unfold qualifier_typable_context in Hqual_y.
                unfold wf_r_typable in Hcorr.
                unfold r_type in Hcorr.
                rewrite Hobj_lx in Hcorr.
                destruct Hcorr as [_ Hqualifiertypablex].
                inversion Hgetobj; subst o.
                unfold vpa_mutability_stype_fld_abs_imm in Hsub.
                unfold vpa_mutability_rec_fld.
                unfold vpa_mutability_rs in Hqual_y.
                clear - Hqual_y Hsub Hqualifiertypablex.
                all:
                destruct (rqtype rqt_y) eqn: Hrqy;
                destruct (rqtype (rt_type o_x)) eqn: Hrqx;
                destruct (mutability (ftype fieldT)) eqn: Hfield;
                try trivial.

                all:
                destruct (sqtype Ty) eqn: Hsqy;
                destruct qcontext eqn: Hqcontext;
                simpl in Hqual_y;
                try solve_q_subtype_wrong.

                all:
                destruct (sqtype Tx) eqn: Hsqx;
                simpl in Hsub;
                try solve_q_subtype_wrong;
                try solve_qualifier_typable_wrong_concrete.

                all: try easy.
            - (* loc_y doesn't exist - contradiction *)
              assert (Hnth_updated : nth_error (update loc_x (set_fields_map o_x (update f (Iot loc_y) (fields_map o_x))) h) loc_y = None).
              {
                rewrite nth_error_update_neq; [symmetry; exact Hneq_loc2_lx | exact Hnth_y].
              }
              rewrite Hnth_updated.
              exfalso.
              specialize (Hcorrcopy ι qcontext HreceiverAddr Hreceivermut y Hy_dom Ty Hget_y).
              rewrite Hgety in Hcorrcopy.
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
          discriminate Hgetobj.
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
    intros ι qcontext HreceiverAddr Hreceivermut i Hi sqt Hnth.
      assert (r_muttype h ι = Some qcontext) as Hreceivermut_orig.
      {
        rewrite (r_muttype_update_field_preserve h loc_x f val_y ι) in Hreceivermut.
        exact Hreceivermut.
      }
      assert (Hcorr_orig := Hcorr ι qcontext HreceiverAddr Hreceivermut_orig i Hi sqt Hnth).
      destruct (runtime_getVal rΓ i) as [v|] eqn:Hval; [|exact Hcorr_orig].
      destruct v as [|loc]; [trivial|].
      unfold wf_r_typable in Hcorr_orig |- *.
      destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
      assert (Hrtype_preserved : r_type (update_field h loc_x f val_y) loc = Some rqt).
      {
        unfold r_type.
        unfold update_field.
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
            f_equal.
            injection Hobj_eq_copy as Ho_eq.
            rewrite Ho_eq.
            reflexivity.
          + rewrite runtime_getObj_update_diff.
            * symmetry. exact Hneq.
            * exact Hrtype.
        - exact Hrtype.
      }
      rewrite Hrtype_preserved.
      exact Hcorr_orig.
Qed.

Lemma preservation_fldwrite_ok_concrete_imm :
  forall CT sΓ rΓ h x f y h' sΓ'
    (Hwf     : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ ConcreteImm (SFldWrite x f y) sΓ')
    (Heval   : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h (SFldWrite x f y) OK (reachable_locations_from_initial_env CT h rΓ) rΓ h'),
    wf_r_config CT sΓ' rΓ h'.
Proof.
    intros CT sΓ rΓ h x f y h' sΓ' Hwf Htyping Heval.
    inversion Heval; subst.
    rename Hval_x into Hgetx.
    rename Hobj into Hgetobj.
    rename Hfield into Hgetf.
    rename Hval_y into Hgety.
    have Hwfcopy := Hwf.
    inversion Htyping; subst.
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) 
    unfold  wf_class_table in Hclass. destruct Hclass as [Hclass _]. exact Hclass.
    + (* Object wellformedness *)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [Hobject _]]. exact Hobject.
    + (* All other classes have super class*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[Hotherclasses _]]]. exact Hotherclasses.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
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
                injection Hgetobj as Ho_eq. subst o_x.
                apply getVal_dom in Hgetf. exact Hgetf.
              }
              rewrite <- Hlen_eq. exact Hf_valid.

              intros b Hnth_b.
              destruct val_y as [|loc_y]; [trivial|].

              assert (Hx_dom : x < dom sΓ').
              {
                apply static_getType_dom in Hget_x. exact Hget_x.
              }

              assert (Hy_dom : y < dom sΓ').
              {
                apply static_getType_dom in Hget_y. exact Hget_y.
              }
              have Hcorrcopy := Hcorr.
              assert (Hthis_exists : exists ι, get_this_var_mapping (vars rΓ) = Some ι).
              {
                eapply get_this_exists_from_wf_r_config; eauto.
              }
              destruct Hthis_exists as [ι HreceiverAddr].
              assert (Hqcontext_exists : exists qcontext, r_muttype h ι = Some qcontext).
              {
                eapply receiver_mutability_exists_wf_renv; eauto.
              }
              destruct Hqcontext_exists as [qcontext Hreceivermut].
              have Hcorropy := Hcorr.
              specialize (Hcorr ι qcontext HreceiverAddr Hreceivermut x Hx_dom Tx Hget_x).
              destruct (runtime_getVal rΓ x) as [val_x|] eqn:Hx_val; [|contradiction].
              injection Hgetx as H_val_eq.
              subst val_x.
              unfold update_field.
              destruct (runtime_getObj h loc_x) as [o_lx|] eqn:Hobj_lx; [|easy].
              destruct (Nat.eq_dec loc_y loc_x) as [Heq_loc2_lx | Hneq_loc2_lx].
              specialize (Hcorrcopy ι qcontext HreceiverAddr Hreceivermut y Hy_dom Ty Hget_y).
              destruct (runtime_getVal rΓ y) as [val_y|] eqn:Hy_val; [|contradiction].
              injection Hgety as H_val_eq.
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
                  injection Hgetobj as Ho_eq2.
                  subst o_lx o_x.
                  exact Hrtype_x.
                  injection Hobj as Ho_lx_eq.
                  injection Hgetobj as Ho_x_eq.
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
                    unfold sf_def_rel in Hfld_def.
                    inversion Hfld_def; subst.
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
                  apply qualified_type_subtype_base_subtype in Hsub.
                  (* apply vpa_preserve_basetype_subtype in H11. *)
                  simpl in Hsub.
                  eapply base_trans; eauto.

                  (* Qualifier *)
                  apply get_this_qualified_type_nth_error in Hthis.
                  unfold wf_senv in Hsenv;
                  destruct Hsenv as [Hsenvdom _];
                  apply qualified_type_subtype_q_subtype in Hsub.
                  simpl in Hsub.
                  unfold qualifier_typable_heap.
                  move Hsub at bottom.
                  move Hqual_typable at bottom.
                  unfold vpa_mutability_rec_fld; unfold vpa_mutability_stype_fld_abs_imm in Hsub.
                  subst rqt_x.

                  clear - Hsub Hqual_typable Hxyqualifer.
                  all: destruct (rqtype (rt_type o)) eqn: rq;
                  destruct (mutability (ftype fieldT)) eqn: HfieldMut;
                  simpl;
                  simpl in Hsub; try trivial.
                  all: 
                  destruct (sqtype Tx) eqn: qx;
                  destruct (sqtype Ty) eqn: qy;
                  simpl in Hsub;
                  try solve_q_subtype_wrong.
                  all:
                  destruct qcontext eqn: Hqcontext;
                  try solve_qualifier_typable_wrong_concrete.
            }

            have H11copy := Hsub.
            apply qualified_type_subtype_q_subtype in Hsub. 
            destruct (nth_error h loc_y) as [obj_y|] eqn:Hnth_y.
            - (* loc_y exists in original heap *)
              assert (Hnth_updated : nth_error (update loc_x (set_fields_map o_x (update f (Iot loc_y) (fields_map o_x))) h) loc_y = Some obj_y).
              {
                rewrite nth_error_update_neq; [symmetry; exact Hneq_loc2_lx | exact Hnth_y].
              }
              rewrite Hnth_updated.
              specialize (Hcorrcopy ι qcontext HreceiverAddr Hreceivermut y Hy_dom Ty Hget_y).
              rewrite Hgety in Hcorrcopy.
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
                unfold sf_def_rel in Hfld_def.
                inversion Hfld_def; subst.
                symmetry.
                eapply collect_fields_consistent_through_runtime_static with (C:=(rctype (rt_type o_x)))(fields1:=Hlen_fields)(fields2:=fields)(fdef1:=b)(fdef2:=fieldT); eauto.
                apply qualified_type_subtype_base_subtype in H11copy.
                simpl in H11copy.
                unfold wf_r_typable in Hcorr.
                unfold r_type in Hcorr.
                rewrite Hobj_lx in Hcorr.
                destruct Hcorr as [Hbase_sub Hqual_typable].
                inversion Hobj.
                subst o_lx.
                exact Hbase_sub.
              }
              subst b.
              split.
              + (* Base type equality *)
                apply qualified_type_subtype_base_subtype in H11copy.
                (* apply vpa_preserve_basetype_subtype in H11copy. *)
                simpl in H11copy.
                eapply base_trans; eauto.
              + (* Qualifier typable *)
                apply get_this_qualified_type_nth_error in Hthis.
                unfold wf_senv in Hsenv;
                destruct Hsenv as [Hsenvdom _];
                move Hsub at bottom.
                inversion Hlen.
                inversion Hobj.
                subst.
                unfold qualifier_typable_heap.
                unfold qualifier_typable_context in Hqual_y.
                unfold wf_r_typable in Hcorr.
                unfold r_type in Hcorr.
                rewrite Hobj_lx in Hcorr.
                destruct Hcorr as [_ Hqualifiertypablex].
                inversion Hgetobj; subst o.
                unfold vpa_mutability_stype_fld_abs_imm in Hsub.
                unfold vpa_mutability_rec_fld.
                unfold vpa_mutability_rs in Hqual_y.
                clear - Hqual_y Hsub Hqualifiertypablex.
                all:
                destruct (rqtype rqt_y) eqn: Hrqy;
                destruct (rqtype (rt_type o_x)) eqn: Hrqx;
                destruct (mutability (ftype fieldT)) eqn: Hfield;
                try trivial.

                all:
                destruct (sqtype Ty) eqn: Hsqy;
                destruct qcontext eqn: Hqcontext;
                simpl in Hqual_y;
                try solve_q_subtype_wrong.

                all:
                destruct (sqtype Tx) eqn: Hsqx;
                simpl in Hsub;
                try solve_q_subtype_wrong;
                try solve_qualifier_typable_wrong_concrete.

                all: try easy.
            - (* loc_y doesn't exist - contradiction *)
              assert (Hnth_updated : nth_error (update loc_x (set_fields_map o_x (update f (Iot loc_y) (fields_map o_x))) h) loc_y = None).
              {
                rewrite nth_error_update_neq; [symmetry; exact Hneq_loc2_lx | exact Hnth_y].
              }
              rewrite Hnth_updated.
              exfalso.
              specialize (Hcorrcopy ι qcontext HreceiverAddr Hreceivermut y Hy_dom Ty Hget_y).
              rewrite Hgety in Hcorrcopy.
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
          discriminate Hgetobj.
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
    intros ι qcontext HreceiverAddr Hreceivermut i Hi sqt Hnth.
      assert (r_muttype h ι = Some qcontext) as Hreceivermut_orig.
      {
        rewrite (r_muttype_update_field_preserve h loc_x f val_y ι) in Hreceivermut.
        exact Hreceivermut.
      }
      assert (Hcorr_orig := Hcorr ι qcontext HreceiverAddr Hreceivermut_orig i Hi sqt Hnth).
      destruct (runtime_getVal rΓ i) as [v|] eqn:Hval; [|exact Hcorr_orig].
      destruct v as [|loc]; [trivial|].
      unfold wf_r_typable in Hcorr_orig |- *.
      destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
      assert (Hrtype_preserved : r_type (update_field h loc_x f val_y) loc = Some rqt).
      {
        unfold r_type.
        unfold update_field.
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
            f_equal.
            injection Hobj_eq_copy as Ho_eq.
            rewrite Ho_eq.
            reflexivity.
          + rewrite runtime_getObj_update_diff.
            * symmetry. exact Hneq.
            * exact Hrtype.
        - exact Hrtype.
      }
      rewrite Hrtype_preserved.
      exact Hcorr_orig.
Qed.

Lemma preservation_fldwrite_ok :
  forall CT sΓ mt rΓ h x f y h' sΓ'
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt (SFldWrite x f y) sΓ')
    (Heval : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h (SFldWrite x f y) OK (reachable_locations_from_initial_env CT h rΓ) rΓ h'),
    wf_r_config CT sΓ' rΓ h'.
Proof.
    intros.
    inversion Htyping; subst.
    - eapply preservation_fldwrite_ok_abs_imm; eauto.
    - eapply preservation_fldwrite_ok_abs_imm; eauto.
      econstructor; eauto.
      eapply concrete_assignable_implies_assignable; eauto.
    - eapply preservation_fldwrite_ok_safe_ro; eauto.
    - eapply preservation_fldwrite_ok_concrete_imm; eauto.
Qed.

Lemma r_muttype_app_preserve_old :
  forall h h_ext loc
    (Hlt : loc < dom h),
    r_muttype (h ++ [h_ext]) loc = r_muttype h loc.
Proof.
  intros h h_ext loc Hlt.
  unfold r_muttype.
  destruct (runtime_getObj h loc) as [o|] eqn:Hobj.
  - rewrite (runtime_getObj_app_left h h_ext loc o Hlt Hobj). reflexivity.
  - (* impossible under loc < dom h *)
    exfalso.
    apply runtime_getObj_not_dom in Hobj. lia.
Qed.

Lemma r_muttype_app_preserve_old_Some :
  forall h h_ext loc q
    (Hlt   : loc < dom h)
    (Hext  : r_muttype (h ++ [h_ext]) loc = Some q),
    r_muttype h loc = Some q.
Proof.
  intros h h_ext loc q Hlt Hext.
  rewrite (r_muttype_app_preserve_old h h_ext loc Hlt) in Hext.
  exact Hext.
Qed.

Lemma preservation_new_ok :
  forall CT sΓ mt rΓ h x q_c c ys rΓ' h' sΓ'
    (Hwf                    : wf_r_config CT sΓ rΓ h)
    (Htyping                : stmt_typing CT sΓ mt (SNew x q_c c ys) sΓ')
    (Heval                  : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h (SNew x q_c c ys) OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h'),
    wf_r_config CT sΓ' rΓ' h'.
Proof.
  intros CT sΓ mt rΓ h x q_c c ys rΓ' h' sΓ' Hwf Htyping Heval.
    inversion Heval; subst.
    rename Hthis into Hgetthis.
    rename Hargs into Hlookupvals.
    rename Hmut into HgetthisRuntimeType.
    inversion Htyping.
    have Hwf_copy := Hwf.
    unfold wf_r_config.
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) 
    unfold  wf_class_table in Hclass. destruct Hclass as [Hclass _]. exact Hclass.
    + (* Object wellformedness *)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [Hobject _]]. exact Hobject.
    + (* All other classes have super class*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[Hotherclasses _]]]. exact Hotherclasses.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
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
        ++ unfold constructor_def_lookup in Hconsig.
        destruct (find_class CT c) as [def|] eqn:Hfind.
        ** apply find_class_dom in Hfind.
          split.
          exact Hfind.
          unfold vpa_mutability_runtime_bound_agree.
          assert (Hwf_ctor : wf_constructor CT c consig).
          {
            eapply constructor_lookup_wf; eauto.
          }
          unfold wf_constructor in Hwf_ctor.
          destruct Hwf_ctor as [Hctor_bound [Hparamswf [field_defs [Hcollect_H1 [Hdom_eq Hfieldtypematch]]]]].
          rewrite Hbound in Hctor_bound.
          inversion Hctor_bound; subst.
          unfold vpa_mutability_object_creation.
          unfold vpa_mutability_bound in Hqc.
          destruct q_c eqn:Hnewq;
          destruct (cqualifier consig) eqn: Hcbound;
          destruct qthisr eqn: Hqthis;
          simpl in *; try easy.
        ** exfalso.
        unfold bound in Hbound.
        rewrite Hfind in Hbound.
        discriminate Hbound.
        ++ 
          unfold constructor_sig_lookup in Hconsig.
          destruct (constructor_def_lookup CT c) as [ctor|] eqn:Hctor.
          ** unfold constructor_def_lookup in Hctor.
            destruct (find_class CT c) as [def|] eqn:Hfind.
            --- unfold bound in Hbound.
              rewrite Hfind in Hbound.
              discriminate Hbound.
            --- discriminate Hctor.
          ** easy.
      --
        {
          assert (Hc_dom : c < dom CT).
   {
     apply constructor_sig_lookup_dom in Hconsig.
     exact Hconsig.
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
      simpl.
      apply Forall2_length in Harg_sub.
      apply runtime_lookup_list_preserves_length in Hlookupvals.
      apply static_getType_list_preserves_length in Hget_args.
	      rewrite Hlookupvals.
	      rewrite <- Hget_args.
	      rewrite Harg_sub.
	      rewrite length_map.
	      eapply constructor_sig_lookup_implies_def in Hconsig; eauto.
      destruct Hconsig as [cdef Hcedflookup].
      destruct Hcedflookup as [Hcedflookup Hcdefcsig].
      eapply constructor_params_field_count; eauto.
     * (* Forall2 property *)
	      assert (Hthis_exists : exists ι, get_this_var_mapping (vars rΓ) = Some ι).
      {
        eapply get_this_exists_from_wf_r_config; eauto.
      }
	      destruct Hthis_exists as [ι HreceiverAddr].
	      assert (Hqcontext_exists : exists qcontext, r_muttype h ι = Some qcontext).
      {
        eapply receiver_mutability_exists_wf_renv; eauto.
      }
	      destruct Hqcontext_exists as [qcontext Hreceivermut].
      apply runtime_lookup_list_preserves_typing with (ι:= ι) (qcontext:=qcontext) (CT:= CT) (h := h) (sΓ := sΓ') (args := ys) (argtypes := argtypes) in Hlookupvals; auto.
      simpl.
      assert (Hwf_ctor : wf_constructor CT c consig).
      {
        eapply constructor_lookup_wf; eauto.
      }
      unfold wf_constructor in Hwf_ctor.
      destruct Hwf_ctor as [Hctor_bound [Hparamswf [field_defs_exists [Hcollect_H1 [Hdom_eq Hfieldtypematch]]]]].
      unfold wf_heap in Hheap.
      unfold wf_obj in Hheap.
      eapply Forall2_from_nth.
        - (* Show lengths are equal *)
        apply Forall2_length in Hlookupvals.
        rewrite Hlookupvals.
	        apply Forall2_length in Harg_sub.
	        rewrite Harg_sub.
	        rewrite length_map.
	        assert (field_defs_exists = field_defs). {
          eapply collect_fields_deterministic_rel; eauto.
        }
        subst field_defs_exists.
        exact Hdom_eq.
	        - (* Show pointwise property *)
	          intros i v fdef Hi Hv Hfdef.
	          assert (field_defs_exists = field_defs) as Hfields_eq.
	          {
	            eapply collect_fields_deterministic_rel; eauto.
	          }
	          subst field_defs_exists.
	          destruct v; [easy|].
          {
            assert (Hargtype : exists argtype, nth_error argtypes i = Some argtype).
        {
          apply Forall2_length in Hlookupvals.
          rewrite Hlookupvals in Hi.
          apply nth_error_Some_exists in Hi.
          exact Hi.
        }
        destruct Hargtype as [argtype Hargtype].
        eapply Forall2_nth_error in Hlookupvals; [|exact Hv|exact Hargtype].
        simpl in Hlookupvals.
        unfold wf_r_typable in Hlookupvals.
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
        - split.
        +
          destruct Hlookupvals as [Hrctype _].
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
	          assert (Hadapted_paramtype :
	            nth_error (map (vpa_mutability_constructor_param q_c) (cparams consig)) i =
	            Some (vpa_mutability_constructor_param q_c paramtype)).
	          {
	            rewrite nth_error_map.
	            rewrite Hparamtype.
	            reflexivity.
	          }
	          eapply Forall2_nth_error with
	            (i:=i) (b:=vpa_mutability_constructor_param q_c paramtype) (a:=argtype) in Harg_sub.
	          apply qualified_type_subtype_base_subtype in Harg_sub.
	          unfold vpa_mutability_constructor_param in Harg_sub.
	          simpl in Harg_sub.
	          eapply base_trans; eauto.
	          eapply base_trans; eauto.
	          exact Hargtype.
	          exact Hadapted_paramtype.
	          exact Hparamtype.
	          exact Hfdef.
        + 
          destruct Hlookupvals as [Hrctype Hqctype].
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
	          assert (Hadapted_paramtype :
	            nth_error (map (vpa_mutability_constructor_param q_c) (cparams consig)) i =
	            Some (vpa_mutability_constructor_param q_c paramtype)).
	          {
	            rewrite nth_error_map.
	            rewrite Hparamtype.
	            reflexivity.
	          }
	          eapply Forall2_nth_error with
	            (i:=i) (b:=vpa_mutability_constructor_param q_c paramtype) (a:=argtype) in Harg_sub.
	          apply qualified_type_subtype_q_subtype in Harg_sub.
	          apply qualified_type_subtype_q_subtype in Hresult_sub.

	          2: exact Hargtype.
	          2: exact Hadapted_paramtype.
	          2: exact Hparamtype.
	          2: exact Hfdef.
	          simpl in Hfieldtypematch.
	          unfold vpa_mutability_constructor_param in Harg_sub.
	          simpl in Harg_sub.
	          move Hqctype at bottom.
	          move Hfieldtypematch at bottom.
          unfold wf_senv in Hsenv;
          destruct Hsenv as [Hsenvdom _];
          destruct (r_type h ι) as [rqt_receiver|] eqn: Hrtype_receiver.
          assert(H100: qcontext = rqtype rqt_receiver).
          {
            unfold r_muttype in Hreceivermut.
            unfold r_type in Hrtype_receiver.
            destruct (runtime_getObj h ι) eqn: save; [|easy].
            inversion Hreceivermut; subst.
            inversion Hrtype_receiver; reflexivity.
          }
          2:{
            unfold r_type in Hrtype_receiver.
            unfold r_muttype in Hreceivermut.
            destruct (runtime_getObj h ι) eqn: save; [|easy].
            discriminate Hrtype_receiver.
          }
          unfold qualifier_typable_heap.
          unfold vpa_mutability_rec_fld.
          unfold vpa_mutability_constructor_fld in Hfieldtypematch.
          unfold vpa_mutability_object_creation.
          unfold qc2q in Hresult_sub.
          simpl in Hresult_sub.
          assert (l1 = ι). {
            apply get_this_var_mapping_runtime_getVal in HreceiverAddr.
            rewrite Hgetthis in HreceiverAddr.
            injection HreceiverAddr as Heq.
            exact Heq.
          }
          subst l1.
          assert (qthisr = qcontext). {
            rewrite Hreceivermut in HgetthisRuntimeType.
            inversion HgetthisRuntimeType; reflexivity.
          }
          subst qthisr.
	          unfold vpa_mutability_bound in Hqc.
	          clear - Hfieldtypematch Hqctype Harg_sub Hqc.
	          destruct (rqtype rqt) eqn: Hrqtq;
	          destruct qcontext eqn: Hqthis;
	          destruct q_c eqn: Hnewq;
	          destruct (cqualifier consig) eqn: Hconstructoreturnq;
	          destruct (mutability (ftype fdef)) eqn: Hfieldq;
	          try easy.
          all: destruct (sqtype paramtype) eqn: Hparamq;
          try solve_q_subtype_wrong.
          all: 
	          destruct (sqtype argtype) eqn: Hargq;
	          try solve_q_subtype_wrong;
	          destruct qcontext eqn: Hqcontext;
	          try solve_qualifier_typable_wrong_concrete;
	          try solve_qualifier_typable_correct_concrete;
	          try easy.
        }
      }
    * (* ι < dom h (existing object) *)
	      assert (Hι_old : ι0 < dom h) by lia.
      unfold wf_obj.
      rewrite runtime_getObj_last2; auto.
      {
        unfold wf_heap in Hheap.
	        specialize (Hheap ι0 Hι_old).
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
                assert (loc < dom h).
                {
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
        simpl in HrEnvLen.
        lia.
      * (* Case: vars rΓ = v0 :: vs *)
        destruct x as [|x'].
        -- (* x = S x' *)
          split.
          --- (* Show update preserves position 0 *)
            simpl. 
            exfalso. easy.
          --- (* Show iot is still in extended heap domain *)
            subst.
            rewrite length_app. simpl.
            lia.
        --
          split.
          subst.
          exact Hiot.
	          rewrite length_app.
          simpl.
          lia.
    + 
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      simpl.
      subst.
      apply Forall_update.
    * 
      eapply Forall_impl; [| exact Hallvals].
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
	      assert (Hlen_extended: dom (h ++ [{| rt_type := {| rqtype := vpa_mutability_object_creation
qthisr q_c; rctype := c |}; fields_map := vals |}]) = dom h + 1).
      -- rewrite length_app. simpl. lia.
      -- rewrite nth_error_app2.
      ** lia.
      ** replace (dom h - dom h) with 0 by lia.
        simpl. reflexivity.
      * assert (Hx_dom : x < dom sΓ') by (apply static_getType_dom in Hget_x; exact Hget_x).
      rewrite <- Hlen; exact Hx_dom.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. subst. exact HsenvLength.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. subst. exact HsenvWellTyped.
    + subst. rewrite update_length. rewrite <- Hlen. lia.
    + 
    {
      intros ι qcontext HreceiverAddr Hreceivermut i Hi sqt Hnth.
      destruct (Nat.eq_dec i x) as [Heq | Hneq].
      - (* Case: i = x (newly assigned variable) *)
        subst i.
        simpl.
        unfold runtime_getVal.
        subst.
        rewrite update_same.
	        + assert (Hx_dom : x < dom sΓ') by (apply static_getType_dom in Hget_x; exact Hget_x).
	          rewrite <- Hlen. exact Hx_dom.
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
              simpl.
              unfold r_muttype.
              unfold static_getType in Hget_x.
              rewrite Hget_x in Hnth.
              inversion Hnth.
              subst sqt.
              split.
              apply qualified_type_subtype_base_subtype in Hresult_sub.
              unfold qc2q in Hresult_sub.
              simpl in Hresult_sub.
              
              exact Hresult_sub.
              apply qualified_type_subtype_q_subtype in Hresult_sub.
              simpl in Hresult_sub.
              unfold wf_senv in Hsenv;
              destruct Hsenv as [Hsenvdom _];
              destruct (r_type h ι) as [rqt_receiver|] eqn: Hrtype_receiver.
	              assert(H100: qcontext = rqtype rqt_receiver).
	              {
	                unfold r_type in Hrtype_receiver.
	                destruct (runtime_getObj h ι) eqn: save; [|easy].
	                assert (Hι_dom : ι < dom h).
	                {
	                  apply runtime_getObj_dom in save.
	                  exact save.
	                }
	                pose proof Hreceivermut as Hreceivermut_old.
	                eapply r_muttype_app_preserve_old_Some in Hreceivermut_old; eauto.
	                unfold r_muttype in Hreceivermut_old.
	                rewrite save in Hreceivermut_old.
	                inversion Hreceivermut_old; subst.
	                inversion Hrtype_receiver; subst.
	                reflexivity.
	              }
              2:{
                unfold r_type in Hrtype_receiver.
                unfold r_muttype in Hreceivermut.
                simpl in HreceiverAddr.
                destruct v0 as [|]; [easy|].
                inversion HreceiverAddr; subst.
                destruct (runtime_getObj h ι) eqn: save.
                2:{
                  destruct Hrenv as [HrEnvLen [Hrecv Hallvals]].
                  destruct Hrecv as [ι0 [Hthis' Hι0_dom]].
                  rewrite Hvars in Hthis'. simpl in Hthis'. inversion Hthis'; subst ι0.
                  exfalso.
                  apply runtime_getObj_not_dom in save.
                  lia.
                }
                discriminate Hrtype_receiver.
              }
              unfold r_type in Hrtype_receiver.
              destruct (runtime_getObj h ι) eqn: save; [|easy].
              have save_copy := save.
              apply runtime_getObj_dom in save.
              apply r_muttype_app_preserve_old_Some in Hreceivermut; auto.
              rewrite (get_this_var_mapping_update_nonzero (v0 :: vs) (S x') (Iot (dom h))) in HreceiverAddr.
              discriminate.
              specialize (Hcorr ι qcontext HreceiverAddr Hreceivermut 0 Hsenvdom Tthis Hthis).
              rewrite Hgetthis in Hcorr.
              unfold wf_r_typable in Hcorr.
              unfold r_type in Hcorr.
              assert (l1 = ι).
              {
                rewrite <- Hvars in HreceiverAddr.
                pose proof (get_this_var_mapping_runtime_getVal rΓ ι HreceiverAddr) as Hthis_rt.
                rewrite Hgetthis in Hthis_rt.
	                inversion Hthis_rt; subst; reflexivity.
              }
              subst l1.
              rewrite save_copy in Hcorr.
              destruct Hcorr as [_ Hqual_receiver].
              inversion Hrtype_receiver.
              subst rqt_receiver.
              rewrite <- H100 in Hqual_receiver.
              assert (qcontext = qthisr).
              {
                rewrite HgetthisRuntimeType in Hreceivermut.
                inversion Hreceivermut; reflexivity.
              }
              subst qthisr.
              unfold qualifier_typable_context in *.
              unfold vpa_mutability_object_creation in *.
	              unfold vpa_mutability_rs in *;
	              unfold qc2q in *;
	              unfold vpa_mutability_tt_abs_imm in *.
	              unfold vpa_mutability_bound in Hqc.
	              destruct q_c eqn:Hnewq;
	              destruct (cqualifier consig) eqn: Hcbound;
	              destruct qcontext eqn: Hqcontext;
	              destruct (rqtype (rt_type o)) eqn: Hrqtq;
	              destruct (sqtype Tx) eqn: Htxq; try easy.
	              all: destruct (sqtype Tthis) eqn: Hqthisr;
	                try rewrite Htxq in Hresult_sub;
	                simpl in Hresult_sub;
	                try inversion Hresult_sub;
	                try easy.
	          }
      - (* Case: i ≠ x (existing variable) *)
        simpl.
        unfold runtime_getVal.
        subst.
        rewrite update_diff; auto.
        rewrite get_this_var_mapping_update_vars_nonzero in HreceiverAddr; auto.
        (* Show that the original wf_r_typable holds *)
        assert (r_muttype h ι = Some qcontext) as Hreceivermut_orig.
        {
          eapply r_muttype_app_preserve_old_Some in Hreceivermut; eauto.
          destruct Hrenv as [HrEnvLen [Hrecv Hallvals]].
          destruct Hrecv as [ι0 [Hthis' Hι0_dom]].
          rewrite Hthis' in HreceiverAddr. inversion HreceiverAddr; subst ι.
          exact Hι0_dom.
        }
        assert (Hcorr_orig := Hcorr ι qcontext HreceiverAddr Hreceivermut_orig i Hi sqt Hnth).
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
	          assert (Hrtype_ext : r_type (h ++ [{| rt_type := {| rqtype := vpa_mutability_object_creation qthisr
q_c; rctype := c |}; fields_map := vals |}]) loc = Some rqt).
          {
            unfold r_type in Hrtype |- *.
            rewrite heap_extension_preserves_objects; auto.
            destruct (runtime_getObj h loc) as [obj|] eqn:Hobj; [|discriminate].
            apply runtime_getObj_dom in Hobj. exact Hobj.
          }
          rewrite Hrtype_ext.
          exact Hcorr_orig.
          + contradiction Hcorr_orig.
          }
Qed.

Lemma vpa_mutability_tt_sctype_abs_imm :
  forall Tthis T : qualified_type,
    sctype (vpa_mutability_tt_abs_imm Tthis T) = sctype T.
Proof.
  intros Tthis [q c].
  unfold vpa_mutability_tt_abs_imm.
  simpl.
  destruct (sqtype Tthis); simpl; try reflexivity.
  all: destruct q; simpl; reflexivity.
Qed.

Lemma vpa_mutability_tt_sctype_safe_ro :
  forall Tthis T : qualified_type,
    sctype (vpa_mutability_tt_safe_ro Tthis T) = sctype T.
Proof.
  intros Tthis [q c].
  unfold vpa_mutability_tt_safe_ro.
  simpl.
  destruct (sqtype Tthis); simpl; try reflexivity.
  all: destruct q; simpl; reflexivity.
Qed.

Lemma receiver_mutability_exists_from_bound :
  forall h ι
    (Hlt : ι < dom h),
    exists q, r_muttype h ι = Some q.
Proof.
  intros h ι Hlt.
  unfold r_muttype.
  destruct (runtime_getObj h ι) as [o|] eqn:Hobj.
  - eexists. reflexivity.
  - exfalso.
    apply runtime_getObj_not_dom in Hobj.
    lia.
Qed.

Lemma static_getType_list_index_strong :
  forall sΓ zs argtypes i j argtype
    (Hmap  : mapM (fun x => static_getType sΓ x) zs = Some argtypes)
    (Hzs   : nth_error zs i = Some j)
    (Hargs : nth_error argtypes i = Some argtype),
    static_getType sΓ j = Some argtype.
Proof.
  intros sΓ zs.
  induction zs as [|z zs' IH]; intros argtypes i j argtype Hmap Hzs Hargs.
  - (* zs = [] *)
    simpl in Hmap.
    inversion Hmap; subst argtypes.
    simpl in Hargs.
    inversion Hzs.
    exfalso.
    rewrite nth_error_nil in Hzs.
    discriminate Hzs.
  - (* zs = z :: zs' *)
    simpl in Hmap.
    destruct (static_getType sΓ z) as [Tz|] eqn:HTz; try discriminate.
    destruct (mapM (fun x : Loc => static_getType sΓ x) zs')
      as [argtypes'|] eqn:Hrec; try discriminate.
    inversion Hmap; subst argtypes; clear Hmap.
    destruct i as [|i'].
    + (* i = 0 *)
      simpl in Hzs, Hargs.
      inversion Hzs; subst j.
      inversion Hargs; subst argtype.
      exact HTz.
    + (* i = S i' *)
      simpl in Hzs, Hargs.
      eapply IH; eauto.
Qed.

Lemma static_getType_list_nth_zs :
  forall sΓ zs argtypes i argtype
    (Hlist : static_getType_list sΓ zs = Some argtypes)
    (Hnth  : nth_error argtypes i = Some argtype),
    exists j,
      nth_error zs i = Some j /\
      static_getType sΓ j = Some argtype.
Proof.
  intros sΓ zs.
  induction zs as [|z zs' IH]; intros argtypes i argtype Hlist Hnth.
  - (* zs = [] *)
    simpl in Hlist.
    inversion Hlist; subst argtypes.
    simpl in Hnth.
    rewrite nth_error_nil in Hnth.
    discriminate.
  - (* zs = z :: zs' *)
    simpl in Hlist.
    destruct (static_getType sΓ z) as [Tz|] eqn:HTz.
    2:{ 
      exfalso. 
      unfold static_getType_list in Hlist.
      simpl in Hlist.
      rewrite HTz in Hlist.
      discriminate Hlist.
      }
    destruct (mapM (fun x : Loc => static_getType sΓ x) zs')
      as [argtypes'|] eqn:Hrec. 
      2:{
        unfold static_getType_list in Hlist.
        simpl in Hlist.
        rewrite HTz in Hlist.
        rewrite Hrec in Hlist.
        discriminate Hlist.
      }
    (* inversion Hlist; subst argtypes; clear Hlist. *)
    destruct i as [|i'].
    + (* i = 0 *)
      unfold static_getType_list in Hlist.
      simpl in Hlist.
      rewrite HTz in Hlist.
      rewrite Hrec in Hlist.
      inversion Hlist; subst argtypes; clear Hlist.

      simpl in Hnth.
      inversion Hnth; subst argtype; clear Hnth.

      exists z.
      split; [simpl; reflexivity | exact HTz].
    + (* i = S i' *)
      simpl in Hnth.
      unfold static_getType_list in Hlist.
      simpl in Hlist.
      rewrite HTz in Hlist.
      rewrite Hrec in Hlist.
      inversion Hlist as [Heq_argtypes]; subst argtypes; clear Hlist.
      simpl in Hnth.
      (* nth_error (Tz :: argtypes') (S i') = nth_error argtypes' i' *)
      destruct (IH argtypes' i' argtype Hrec Hnth) as [j [Hnth_zs Hj]].
      exists j.
      split; simpl; assumption.
Qed.

Lemma runtime_lookup_list_nth_zs :
  forall rΓ zs vals i v
    (Hlist : runtime_lookup_list rΓ zs = Some vals)
    (Hnth  : nth_error vals i = Some v),
    exists j,
      nth_error zs i = Some j /\
      runtime_getVal rΓ j = Some v.
Proof.
  intros rΓ zs.
  induction zs as [|z zs' IH]; intros vals i v Hlist Hnth.
  - (* zs = [] *)
    simpl in Hlist.
    inversion Hlist; subst vals.
    simpl in Hnth.
    rewrite nth_error_nil in Hnth.
    discriminate.
  - (* zs = z :: zs' *)
    simpl in Hlist.
    destruct (runtime_getVal rΓ z) as [Vz|] eqn:HVz.
    2:{
      exfalso.
      unfold runtime_lookup_list in Hlist.
      simpl in Hlist.
      rewrite HVz in Hlist.
      discriminate Hlist.
    }
    destruct (mapM (fun x : Loc => runtime_getVal rΓ x) zs')
      as [vals'|] eqn:Hrec.
    2:{
      unfold runtime_lookup_list in Hlist.
      simpl in Hlist.
      rewrite HVz in Hlist.
      rewrite Hrec in Hlist.
      discriminate Hlist.
    }
    destruct i as [|i'].
    + (* i = 0 *)
      unfold runtime_lookup_list in Hlist.
      simpl in Hlist.
      rewrite HVz in Hlist.
      rewrite Hrec in Hlist.
      inversion Hlist; subst vals; clear Hlist.

      simpl in Hnth.
      inversion Hnth; subst v; clear Hnth.

      exists z.
      split; [simpl; reflexivity | exact HVz].
    + (* i = S i' *)
      simpl in Hnth.
      unfold runtime_lookup_list in Hlist.
      simpl in Hlist.
      rewrite HVz in Hlist.
      rewrite Hrec in Hlist.
      inversion Hlist as [Heq_vals]; subst vals; clear Hlist.
      simpl in Hnth.
      (* nth_error (Vz :: vals') (S i') = nth_error vals' i' *)
      destruct (IH vals' i' v Hrec Hnth) as [j [Hnth_zs Hj]].
      exists j.
      split; simpl; assumption.
Qed.

(** A statically typed variable that evaluates to a non-null location has a
    runtime class below its static class.  This is the caller-side fact needed
    to relate static and dynamically selected method signatures. *)
Lemma runtime_value_base_subtype :
  forall CT sΓ rΓ h y Ty ly cy
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Hget_y : static_getType sΓ y = Some Ty)
    (Hval_y : runtime_getVal rΓ y = Some (Iot ly))
    (Hbase : r_basetype h ly = Some cy),
    base_subtype CT cy (sctype Ty).
Proof.
  intros CT sΓ rΓ h y Ty ly cy Hwf Hget_y Hval_y Hbase.
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [Hrenv [_ [_ Hcorr]]]]].
  unfold wf_renv in Hrenv.
  destruct Hrenv as [_ [[receiver [Hreceiver Hreceiver_dom]] _]].
  destruct (receiver_mutability_exists_from_bound h receiver
              Hreceiver_dom) as [qcontext Hqcontext].
  specialize (Hcorr receiver qcontext Hreceiver Hqcontext).
  assert (Hy_dom : y < dom sΓ).
  { apply static_getType_dom in Hget_y. exact Hget_y. }
  specialize (Hcorr y Hy_dom Ty Hget_y).
  rewrite Hval_y in Hcorr.
  unfold wf_r_typable, r_type in Hcorr.
  unfold r_basetype in Hbase.
  destruct (runtime_getObj h ly) as [obj|] eqn:Hobj; [|discriminate].
  destruct obj as [[rq rc] fields].
  simpl in Hbase, Hcorr.
  injection Hbase as Hcy; subst rc.
  exact (proj1 Hcorr).
Qed.

Lemma runtime_call_signature_agrees :
  forall CT sΓ rΓ h y Ty ly cy m mdef_runtime mdef_static
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Hget_y : static_getType sΓ y = Some Ty)
    (Hval_y : runtime_getVal rΓ y = Some (Iot ly))
    (Hbase : r_basetype h ly = Some cy)
    (Hfind_runtime : FindMethodWithName CT cy m mdef_runtime)
    (Hfind_static : FindMethodWithName CT (sctype Ty) m mdef_static),
    msignature mdef_runtime = msignature mdef_static.
Proof.
  intros.
  eapply method_signature_consistent_subtype; eauto.
  - unfold wf_r_config in Hwf. exact (proj1 Hwf).
  - eapply runtime_value_base_subtype; eauto.
Qed.
