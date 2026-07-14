Require Import Syntax Subtyping ViewpointAdaptation Helpers.

From Stdlib Require String.
From Stdlib Require Import List.
Import ListNotations.

(* STATIC HELPER FUNCTIONS *)
Inductive CollectFields : class_table -> class_name -> list field_def -> Prop :=
  (* Base case: class not found *)
  | CF_NotFound : forall CT C
      (Hnone : find_class CT C = None),
      CollectFields CT C []

  (* Base case: Object class (no superclass) *)
  | CF_Object : forall CT C def
      (Hfind  : find_class CT C = Some def)
      (Hsuper : super (signature def) = None),
      CollectFields CT C []

  (* Inductive case: class with superclass *)
  | CF_Inherit : forall CT C def parent parent_fields own_fields
      (Hfind        : find_class CT C = Some def)
      (Hsuper       : super (signature def) = Some parent)
      (Hparent_cf   : CollectFields CT parent parent_fields)
      (Hown_fields  : own_fields = Syntax.fields (body def)),
      CollectFields CT C (parent_fields ++ own_fields).

(* Field lookup relation *)
Inductive FieldLookup : class_table -> class_name -> var -> field_def -> Prop :=
  | FL_Found : forall CT C fields f fdef
      (Hcf  : CollectFields CT C fields)
      (Hget : gget fields f = Some fdef),
      FieldLookup CT C f fdef.

(* Relational versions of your lookup functions *)
Definition sf_def_rel (CT: class_table) (C: class_name) (f: var) (fdef: field_def) : Prop :=
  FieldLookup CT C f fdef.

Definition sf_assignability_rel (CT: class_table) (C: class_name) (f: var) (a: a) : Prop :=
  exists fdef, FieldLookup CT C f fdef /\ assignability (ftype fdef) = a.

Definition sf_mutability_rel (CT: class_table) (C: class_name) (f: var) (qf: q_f) : Prop :=
  exists fdef, FieldLookup CT C f fdef /\ mutability (ftype fdef) = qf.

Definition sf_base_rel (CT: class_table) (C: class_name) (f: var) (base: class_name) : Prop :=
  exists fdef, FieldLookup CT C f fdef /\ f_base_type (ftype fdef) = base.
  
(* Key properties of relational field collection *)
Lemma collect_fields_deterministic_rel : forall CT C fields1 fields2
  (Hcf1 : CollectFields CT C fields1)
  (Hcf2 : CollectFields CT C fields2),
  fields1 = fields2.
Proof.
  intros CT C fields1 fields2 H1 H2.
  generalize dependent fields2.
  induction H1; intros fields2 H3; inversion H3; subst; try reflexivity.
  - (* CF_NotFound vs CF_Inherit: Hnone contradicts find_class = Some *)
    congruence.
  - (* CF_Object vs CF_Inherit: Hsuper contradicts super = Some *)
    congruence.
  - (* CF_Inherit vs CF_NotFound: Hfind contradicts find_class = None *)
    congruence.
  - (* CF_Inherit vs CF_Object: Hsuper contradicts super = None *)
    congruence.
  - (* Both CF_Inherit *)
    assert (Hdef_eq : def = def0) by congruence. subst def0.
    assert (Hparent_eq : parent = parent0) by congruence. subst parent0.
    assert (parent_fields = parent_fields0) by eauto.
    subst parent_fields0. reflexivity.
Qed.

Lemma field_lookup_deterministic_rel : forall CT C f fdef1 fdef2
  (Hlookup1 : FieldLookup CT C f fdef1)
  (Hlookup2 : FieldLookup CT C f fdef2),
  fdef1 = fdef2.
Proof.
  intros CT C f fdef1 fdef2 H1 H2.
  inversion H1 as [CT1 C1 fields1 f1 fdef1' Hcf1 Hget1]. subst.
  inversion H2 as [CT2 C2 fields2 f2 fdef2' Hcf2 Hget2]. subst.
  apply (collect_fields_deterministic_rel CT C fields1 fields2) in Hcf1; auto.
  subst. rewrite Hget1 in Hget2. injection Hget2. auto.
Qed.

Lemma field_inheritance_preserves_type : forall CT C parent def f fdef
  (Hfind         : find_class CT C = Some def)
  (Hsuper        : super (signature def) = Some parent)
  (Hparent_lookup : FieldLookup CT parent f fdef),
  FieldLookup CT C f fdef.
Proof.
  intros CT C parent def f fdef Hfind Hsuper Hparent_lookup.
  inversion Hparent_lookup as [CT' parent' parent_fields f' fdef' Hparent_cf Hparent_get]. subst.
  apply FL_Found with (parent_fields ++ Syntax.fields (body def)).
  - eapply CF_Inherit; eauto.
  - (* Prove gget (parent_fields ++ Syntax.fields (body def)) f = Some fdef *)
    unfold gget in *.
    rewrite nth_error_app1.
    + apply nth_error_Some. rewrite Hparent_get. discriminate.
    + exact Hparent_get.
Qed.

(* Transitive field inheritance via subtyping *)
Lemma field_inheritance_subtyping : forall CT C D f fdef
  (Hsub    : base_subtype CT C D)
  (Hlookup : FieldLookup CT D f fdef),
  FieldLookup CT C f fdef.
Proof.
  intros CT C D f fdef Hsub Hlookup.
  induction Hsub.
  - (* Reflexivity: C = D *)
    exact Hlookup.
  - (* Transitivity: C <: E <: D *)
    apply IHHsub1.
    apply IHHsub2.
    exact Hlookup.
  - (* Direct inheritance: C extends D *)
    destruct (find_class CT C) as [def|] eqn:Hfind.
    apply (field_inheritance_preserves_type CT C D def f fdef); auto.
    unfold parent_lookup in Hparent.
    rewrite Hfind in Hparent.
    simpl in Hparent.
    exact Hparent.
    unfold parent_lookup in Hparent.
    rewrite Hfind in Hparent.
    discriminate Hparent.
Qed.

Lemma field_def_consistent_through_subtyping : forall CT C D f fdef1 fdef2
  (Hsub      : base_subtype CT C D)
  (Hlookup1  : FieldLookup CT C f fdef1)
  (Hlookup2  : FieldLookup CT D f fdef2),
  fdef1 = fdef2.
Proof.
  intros CT C D f fdef1 fdef2 Hsub Hlookup1 Hlookup2.
  (* Use field inheritance: since C <: D, field f in D is also in C *)
  assert (Hlookup2_in_C : FieldLookup CT C f fdef2).
  {
    apply (field_inheritance_subtyping CT C D f fdef2); assumption.
  }
  (* Now both lookups are in C, so use determinism *)
  eapply field_lookup_deterministic_rel; eauto.
Qed.

(* Corollary for all field properties *)
Lemma sf_def_subtyping : forall CT C D f fdef
  (Hsub    : base_subtype CT C D)
  (Hlookup : sf_def_rel CT D f fdef),
  sf_def_rel CT C f fdef.
Proof.
  intros CT C D f fdef Hsub Hlookup.
  unfold sf_def_rel in *.
  apply (field_inheritance_subtyping CT C D f fdef); auto.
Qed.

Lemma sf_assignability_subtyping : forall CT C D f a
  (Hsub    : base_subtype CT C D)
  (Hlookup : sf_assignability_rel CT D f a),
  sf_assignability_rel CT C f a.
Proof.
  intros CT C D f a Hsub Hlookup.
  unfold sf_assignability_rel in *.
  destruct Hlookup as [fdef [Hfield Hassign]].
  exists fdef. split; auto.
  apply (sf_def_subtyping CT C D f fdef); auto.
Qed.

Lemma sf_mutability_subtyping : forall CT C D f q
  (Hsub    : base_subtype CT C D)
  (Hlookup : sf_mutability_rel CT D f q),
  sf_mutability_rel CT C f q.
Proof.
  intros CT C D f q Hsub Hlookup.
  unfold sf_mutability_rel in *.
  destruct Hlookup as [fdef [Hfield Hmut]].
  exists fdef. split; auto.
  apply (sf_def_subtyping CT C D f fdef); auto.
Qed.

Lemma sf_base_subtyping : forall CT C D f base
  (Hsub    : base_subtype CT C D)
  (Hlookup : sf_base_rel CT D f base),
  sf_base_rel CT C f base.
Proof.
  intros CT C D f base Hsub Hlookup.
  unfold sf_base_rel in *.
  destruct Hlookup as [fdef [Hfield Hbase]].
  exists fdef. split; auto.
  apply (sf_def_subtyping CT C D f fdef); auto.
Qed.

Lemma sf_assignability_deterministic_rel : forall CT C f a1 a2
  (H1 : sf_assignability_rel CT C f a1)
  (H2 : sf_assignability_rel CT C f a2),
  a1 = a2.
Proof.
  intros CT C f a1 a2 H1 H2.
  unfold sf_assignability_rel in H1, H2.
  destruct H1 as [fdef1 [Hlookup1 Hassign1]].
  destruct H2 as [fdef2 [Hlookup2 Hassign2]].
  
  (* Use field lookup determinism *)
  assert (Hfdef_eq: fdef1 = fdef2).
  {
    eapply field_lookup_deterministic_rel; eauto.
  }
  subst fdef2.
  
  (* Now assignability (ftype fdef1) = a1 and assignability (ftype fdef1) = a2 *)
  rewrite -> Hassign1 in Hassign2.
  exact Hassign2.
Qed.

(* Look up the constructor for a class *)
Definition constructor_def_lookup (CT : class_table) (C : class_name) : option constructor_def :=
  match find_class CT C with
  | Some def => Some (constructor (body def))
  | None => None
  end.

(* Look up the constructor signature for a class *)
Definition constructor_sig_lookup (CT : class_table) (C : class_name) : option constructor_sig :=
  match constructor_def_lookup CT C with
  | Some ctor => Some (csignature ctor)
  | None => None
  end.

Lemma constructor_def_lookup_dom : forall CT C ctor
  (Hctor : constructor_def_lookup CT C = Some ctor),
  C < dom CT.
Proof.
  intros CT C ctor H.
  unfold constructor_def_lookup in H.
  destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
  apply find_class_dom in Hfind.
  exact Hfind.
Qed.

Lemma constructor_sig_lookup_dom : forall CT C csig
  (Hcsig : constructor_sig_lookup CT C = Some csig),
  C < dom CT.
Proof.
  intros CT C csig H.
  unfold constructor_sig_lookup in H.
  destruct (constructor_def_lookup CT C) as [ctor|] eqn:Hctor; [|discriminate].
  apply constructor_def_lookup_dom in Hctor.
  exact Hctor.
Qed.

Lemma constructor_sig_lookup_implies_def : forall CT C csig
  (Hcsig : constructor_sig_lookup CT C = Some csig),
  exists cdef, constructor_def_lookup CT C = Some cdef /\ csignature cdef = csig.
Proof.
  intros CT C csig H.
  unfold constructor_sig_lookup in H.
  destruct (constructor_def_lookup CT C) as [ctor|] eqn:Hctor; [|discriminate].
  exists ctor.
  split.
  - reflexivity.
  - injection H as H. exact H.
Qed.

Lemma constructor_def_lookup_Some : forall CT C
  (Hdom : C < dom CT),
  exists ctor, constructor_def_lookup CT C = Some ctor.
Proof.
  intros CT C H.
  apply find_class_Some in H.
  destruct H as [def Hdef].
  unfold constructor_def_lookup.
  rewrite Hdef.
  eexists. reflexivity.
Qed.

Lemma constructor_sig_lookup_Some : forall CT C
  (Hdom : C < dom CT),
  exists csig, constructor_sig_lookup CT C = Some csig.
Proof.
  intros CT C H.
  apply constructor_def_lookup_Some in H.
  destruct H as [ctor Hctor].
  unfold constructor_sig_lookup.
  rewrite Hctor.
  eexists. reflexivity.
Qed.  

(* Helper to compare class names *)
Definition eq_class_name (c1 c2 : class_name) : bool :=
  match c1, c2 with
  | n1, n2 => Nat.eqb n1 n2
  end.

(* Helper to compare method names *)
Definition eq_method_name (m1 m2 : method_name) : bool :=
  match m1, m2 with
  | n1, n2 => Nat.eqb n1 n2
  end.

Definition gget_method (methods : list method_def) (m : method_name) : option method_def :=
  find (fun mdef => eq_method_name (mname (msignature mdef)) m) methods.

Definition override (parent_methods own_methods : list method_def) : list method_def :=
  own_methods ++ filter (fun pmdef => 
    negb (existsb (fun omdef => 
      eq_method_name (mname (msignature pmdef)) (mname (msignature omdef))) 
    own_methods)) parent_methods.

Inductive CollectMethods : class_table -> class_name -> list method_def -> Prop :=
  (* Class not found *)
  | CM_NotFound : forall CT C
      (Hnone : find_class CT C = None),
      CollectMethods CT C []

  (* Object class: no superclass *)
  | CM_Object : forall CT C def
      (Hfind  : find_class CT C = Some def)
      (Hsuper : super (signature def) = None)
      (Hdom   : C < dom CT),
      CollectMethods CT C (methods (body def))

  (* Class with superclass *)
  | CM_Inherit : forall CT C def parent parent_methods own_methods merged
      (Hfind          : find_class CT C = Some def)
      (Hsuper         : super (signature def) = Some parent)
      (Hdom_C         : C < dom CT)
      (Hdom_parent    : parent < dom CT)
      (Hordering      : cname (signature def) > parent)
      (Hparent_cm     : CollectMethods CT parent parent_methods)
      (Hown_methods   : own_methods = methods (body def))
      (Hmerged        : merged = override parent_methods own_methods),
      CollectMethods CT C merged.
 
Lemma collect_methods_deterministic : forall CT C methods1 methods2
  (Hcm1 : CollectMethods CT C methods1)
  (Hcm2 : CollectMethods CT C methods2),
  methods1 = methods2.
Proof.
  intros CT C methods1 methods2 H1 H2.
  generalize dependent methods2.
  induction H1; intros; inversion H2; subst; try reflexivity; try congruence.
  - (* Both CM_Inherit *)
    assert (def = def0) by congruence. subst def0.
    assert (parent = parent0) by congruence. subst parent0.
    assert (parent_methods = parent_methods0) by eauto.
    subst parent_methods0. reflexivity.
Qed.

(* STATIC WELLFORMEDNESS CONDITION *)
(* Well-formedness of type use *)
Definition wf_stypeuse (CT : class_table) (q_use: q) (c: class_name) : Prop :=
  match bound CT c with
  | Some q_bound =>
                  (* Lost is an internal helper qualifier. Since Lost is not
                     reflexive in q_subtype, this condition prevents direct
                     Lost type uses in well-formed static environments. *)
                  q_subtype (vpa_mutability_bound q_use q_bound) q_use /\
                   c < dom CT
  | None => False (* or False, depending on your semantics *)
  end.

(* Well-formedness of field *)
Definition wf_field (CT : class_table) (fdef: field_def) : Prop :=
  exists qbound,
    bound CT (f_base_type (ftype fdef)) = Some qbound /\
    vpa_mutability_fld_bound (mutability (ftype fdef)) qbound = (mutability (ftype fdef)).

(* Well-formedness of static environment *)
Definition wf_senv (CT : class_table) (sΓ : s_env) : Prop :=
  (* The first variable is the receiver and should always be present *)
  dom sΓ > 0 /\
  Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) sΓ.

Lemma senv_var_domain : forall CT sΓ i T
  (Hwf_senv : wf_senv CT sΓ)
  (Hnth     : nth_error sΓ i = Some T),
  sctype T < dom CT.
Proof.
  intros CT sΓ i T Hwf_senv Hnth.
  unfold wf_senv in Hwf_senv.
  destruct Hwf_senv as [_ Hforall_wf].
  assert (Hi_bound : i < dom sΓ).
  {
    apply nth_error_Some. rewrite Hnth. discriminate.
  }
  eapply Forall_nth_error in Hforall_wf; eauto.
  unfold wf_stypeuse in Hforall_wf.
  destruct (bound CT (sctype T)) as [qc|] eqn:Hbound.
  - destruct Hforall_wf as [_ Hdom]. exact Hdom.
  - contradiction Hforall_wf.
Qed.

Inductive FindMethodWithName : class_table -> class_name -> method_name -> method_def -> Prop :=
  (* Case 1: method is defined directly in class *)
  | FOM_Here : forall CT C def own_methods m mdef
      (Hfind       : find_class CT C = Some def)
      (Hown        : own_methods = methods (body def))
      (Hget_method : gget_method own_methods m = Some mdef),
      FindMethodWithName CT C m mdef

  (* Case 2: method not in class, look in superclass *)
  | FOM_Super : forall CT C def parent m mdef own_methods
      (Hfind       : find_class CT C = Some def)
      (Hown        : own_methods = methods (body def))
      (Hnot_here   : gget_method own_methods m = None)
      (Hsuper      : super (signature def) = Some parent)
      (Hparent_fmn : FindMethodWithName CT parent m mdef),
      FindMethodWithName CT C m mdef.

Lemma gget_method_name_consistent : forall methods m mdef
  (Hget : gget_method methods m = Some mdef),
  mname (msignature mdef) = m.
Proof.
  intros methods m mdef H.
  unfold gget_method in H.
  apply find_some in H.
  destruct H as [_ Heq_name].
  unfold eq_method_name in Heq_name.
  apply Nat.eqb_eq in Heq_name.
  exact Heq_name.
Qed.

Lemma find_method_with_name_consistent : forall CT C m mdef
  (Hfmn : FindMethodWithName CT C m mdef),
  mname (msignature mdef) = m.
Proof.
  intros CT C m mdef H.
  induction H.
  - (* FOM_Here *)
    eapply gget_method_name_consistent; eauto.
  - (* FOM_Super *)
    exact IHFindMethodWithName.
Qed.

Lemma find_method_with_name_deterministic : forall CT C m mdef1 mdef2
  (H1 : FindMethodWithName CT C m mdef1)
  (H2 : FindMethodWithName CT C m mdef2),
  mdef1 = mdef2.
Proof.
  intros CT C m mdef1 mdef2 H1.
  generalize dependent mdef2.
  induction H1; intros mdef2 H2.
  - (* H1 = FOM_Here *)
    inversion H2; subst.
    + (* H2 = FOM_Here: gget_method is functional *)
      rewrite Hfind0 in Hfind; injection Hfind as Hdef_eq; subst def0.
      rewrite Hget_method0 in Hget_method; injection Hget_method as ?; subst.
      reflexivity.
    + (* H2 = FOM_Super: contradicts gget_method = Some vs None *)
      rewrite Hfind0 in Hfind; injection Hfind as Hdef_eq; subst def0.
      rewrite Hget_method in Hnot_here; discriminate.
  - (* H1 = FOM_Super *)
    inversion H2; subst.
    + (* H2 = FOM_Here: contradicts None vs Some *)
      rewrite Hfind0 in Hfind; injection Hfind as Hdef_eq; subst def0.
      rewrite Hget_method in Hnot_here; discriminate.
    + (* H2 = FOM_Super: both recurse on the same parent *)
      rewrite Hfind0 in Hfind; injection Hfind as Hdef_eq; subst def0.
      rewrite Hsuper0 in Hsuper; injection Hsuper as ?; subst parent0.
      apply IHFindMethodWithName; auto.
Qed.

(* EXPRESSION TYPING RULES *)
Inductive expr_has_type : class_table -> s_env -> method_type -> expr -> qualified_type -> Prop :=

  (* Null typing *)
  | ET_Null : forall CT Γ mt q class_name
      (Hwf  : wf_senv CT Γ)
      (Hdom : class_name < dom CT),
      expr_has_type CT Γ mt ENull (Build_qualified_type q class_name)

  (* Variable typing *)
  | ET_Var : forall CT Γ mt x T
      (Hwf  : wf_senv CT Γ)
      (Hget : static_getType Γ x = Some T),
      expr_has_type CT Γ mt (EVar x) T

  (* Field access typing — AbstractImm scope *)
  | ET_Field_abs_imm : forall CT Γ mt x T fDef f
      (Hwf      : wf_senv CT Γ)
      (Hget_x   : static_getType Γ x = Some T)
      (Hfld_def : sf_def_rel CT (sctype T) f fDef)
      (Hmt      : mt = AbstractImm \/ mt = ConcreteState),
      expr_has_type CT Γ mt (EField x f)
        (Build_qualified_type
          (vpa_mutability_stype_fld_abs_imm (sqtype T) (mutability (ftype fDef)))
          (f_base_type (ftype fDef)))

  (* Field access typing — SafeRO / ConcreteImm scope *)
  | ET_Field_safe_ro : forall CT Γ mt x T fDef f
      (Hwf      : wf_senv CT Γ)
      (Hget_x   : static_getType Γ x = Some T)
      (Hfld_def : sf_def_rel CT (sctype T) f fDef)
      (Hmt      : mt = SafeRO \/ mt = ConcreteImm),
      expr_has_type CT Γ mt (EField x f)
        (Build_qualified_type
          (vpa_mutability_stype_fld_safe_ro (sqtype T) (mutability (ftype fDef)))
          (f_base_type (ftype fDef)))
.

Definition qc2q (qi : q_c) : q :=
  match qi with
    | RDM_c => RDM
    | Imm_c => Imm
    | Mut_c => Mut
    end.

Definition vpa_mutability_constructor_param (qc : q_c) (T : qualified_type) : qualified_type :=
  Build_qualified_type
    (vpa_mutability_qq_abs_imm (qc2q qc) (sqtype T))
    (sctype T).

Definition get_this_qualified_type (sΓ : s_env) : option qualified_type :=
  match sΓ with
  | [] => None
  | T_this :: _ => 
      Some T_this
  end.

Inductive stmt_typing : class_table -> s_env -> method_type -> stmt -> s_env -> Prop :=
  (* Skip statement *)
  | ST_Skip : forall CT sΓ mt
      (Hwf : wf_senv CT sΓ),
      stmt_typing CT sΓ mt SSkip sΓ

  (* Local variable declaration *)
  | ST_Local : forall CT sΓ mt T x sΓ'
      (Hwf       : wf_senv CT sΓ)
      (Hwf_T     : wf_stypeuse CT (sqtype T) (sctype T))
      (Hnone     : static_getType sΓ x = None)
      (Henv'     : sΓ' = sΓ ++ [T])
      (Hget_x    : static_getType sΓ' x = Some T),
      stmt_typing CT sΓ mt (SLocal T x) sΓ'

  (* Variable assignment *)
  | ST_VarAss : forall CT sΓ mt x e Te Tthis Tx
      (Hwf      : wf_senv CT sΓ)
      (Htype_e  : expr_has_type CT sΓ mt e Te)
      (Hthis    : get_this_qualified_type sΓ = Some Tthis)
      (Hnot_rcv : x <> 0)
      (Hget_x   : static_getType sΓ x = Some Tx)
      (Hsub     : qualified_type_subtype CT Te Tx),
      stmt_typing CT sΓ mt (SVarAss x e) sΓ

  (* Field write — AbstractImm scope *)
  | ST_FldWrite_abs_imm : forall CT sΓ x f y Tx Ty Tthis fieldT a
      (Hwf         : wf_senv CT sΓ)
      (Hget_x      : static_getType sΓ x = Some Tx)
      (Hget_y      : static_getType sΓ y = Some Ty)
      (Hthis       : get_this_qualified_type sΓ = Some Tthis)
      (Hfld_def    : sf_def_rel CT (sctype Tx) f fieldT)
      (Hassign_rel : sf_assignability_rel CT (sctype Tx) f a)
      (Hsub        : qualified_type_subtype CT Ty
                       (Build_qualified_type
                         (vpa_mutability_stype_fld_abs_imm (sqtype Tx) (mutability (ftype fieldT)))
                         (f_base_type (ftype fieldT))))
      (Hassignable : vpa_assignability (sqtype Tx) a = Assignable),
      stmt_typing CT sΓ AbstractImm (SFldWrite x f y) sΓ

  (* Field write — ConcreteState uses AS mutability and TS assignability *)
  | ST_FldWrite_concrete_state : forall CT sΓ x f y Tx Ty Tthis fieldT a
      (Hwf         : wf_senv CT sΓ)
      (Hget_x      : static_getType sΓ x = Some Tx)
      (Hget_y      : static_getType sΓ y = Some Ty)
      (Hthis       : get_this_qualified_type sΓ = Some Tthis)
      (Hfld_def    : sf_def_rel CT (sctype Tx) f fieldT)
      (Hassign_rel : sf_assignability_rel CT (sctype Tx) f a)
      (Hsub        : qualified_type_subtype CT Ty
                       (Build_qualified_type
                         (vpa_mutability_stype_fld_abs_imm (sqtype Tx) (mutability (ftype fieldT)))
                         (f_base_type (ftype fieldT))))
      (Hassignable : vpa_assignability_concret_imm (sqtype Tx) a = Assignable),
      stmt_typing CT sΓ ConcreteState (SFldWrite x f y) sΓ

  (* Field write — SafeRO scope *)
  | ST_FldWrite_safe_ro : forall CT sΓ x f y Tx Ty Tthis fieldT a
      (Hwf         : wf_senv CT sΓ)
      (Hget_x      : static_getType sΓ x = Some Tx)
      (Hget_y      : static_getType sΓ y = Some Ty)
      (Hthis       : get_this_qualified_type sΓ = Some Tthis)
      (Hfld_def    : sf_def_rel CT (sctype Tx) f fieldT)
      (Hassign_rel : sf_assignability_rel CT (sctype Tx) f a)
      (Hsub        : qualified_type_subtype CT Ty
                       (Build_qualified_type
                         (vpa_mutability_stype_fld_safe_ro (sqtype Tx) (mutability (ftype fieldT)))
                         (f_base_type (ftype fieldT))))
      (Hassignable : vpa_assignability (sqtype Tx) a = Assignable),
      stmt_typing CT sΓ SafeRO (SFldWrite x f y) sΓ

  (* Field write — ConcreteImm scope *)
  | ST_FldWrite_concrete_imm : forall CT sΓ x f y Tx Ty Tthis fieldT a
      (Hwf         : wf_senv CT sΓ)
      (Hget_x      : static_getType sΓ x = Some Tx)
      (Hget_y      : static_getType sΓ y = Some Ty)
      (Hthis       : get_this_qualified_type sΓ = Some Tthis)
      (Hfld_def    : sf_def_rel CT (sctype Tx) f fieldT)
      (Hassign_rel : sf_assignability_rel CT (sctype Tx) f a)
      (Hsub        : qualified_type_subtype CT Ty
                       (Build_qualified_type
                         (vpa_mutability_stype_fld_safe_ro (sqtype Tx) (mutability (ftype fieldT)))
                         (f_base_type (ftype fieldT))))
      (Hassignable : vpa_assignability_concret_imm (sqtype Tx) a = Assignable),
      stmt_typing CT sΓ ConcreteImm (SFldWrite x f y) sΓ

  (* Object creation *)
  | S_New : forall CT sΓ mt x Tx (qc:q_c) C args argtypes Tthis consig
      (Hwf         : wf_senv CT sΓ)
      (Hget_x      : static_getType sΓ x = Some Tx)
      (Hget_args   : static_getType_list sΓ args = Some argtypes)
      (Hthis       : get_this_qualified_type sΓ = Some Tthis)
      (Hconsig     : constructor_sig_lookup CT C = Some consig)
      (Hnot_rcv    : x <> 0)
      (Hqc         : vpa_mutability_bound (qc2q qc) (cqualifier consig) = qc2q qc)
      (Harg_sub    : Forall2 (fun arg T => qualified_type_subtype CT arg T)
                       argtypes (map (vpa_mutability_constructor_param qc) consig.(cparams)))
      (Hresult_sub : qualified_type_subtype CT (Build_qualified_type (qc2q qc) C) Tx),
      stmt_typing CT sΓ mt (SNew x qc C args) sΓ

  (* Method call — AbstractImm scope *)
  | ST_Call : forall CT sΓ mt x m y args argtypes Tthis Tx Ty mdef
      (Hwf         : wf_senv CT sΓ)
      (Hget_x      : static_getType sΓ x = Some Tx)
      (Hget_y      : static_getType sΓ y = Some Ty)
      (Hget_args   : static_getType_list sΓ args = Some argtypes)
      (Hthis       : get_this_qualified_type sΓ = Some Tthis)
      (Hfind_m     : FindMethodWithName CT (sctype Ty) m mdef)
      (Hnot_rcv    : x <> 0)
      (Hret_sub    : qualified_type_subtype CT (vpa_mutability_tt_abs_imm Ty (mret (msignature mdef))) Tx)
      (Hrcv_sub    : qualified_type_subtype CT Ty (vpa_mutability_tt_abs_imm Ty (mreceiver (msignature mdef)))
                     \/ (sqtype Ty = RO /\ mdef.(msignature).(mreceiver).(sqtype) = RDM
                         /\ base_subtype CT (sctype Ty) mdef.(msignature).(mreceiver).(sctype)))
      (Harg_sub    : Forall2 (fun arg T => qualified_type_subtype CT arg (vpa_mutability_tt_abs_imm Ty T))
                       argtypes (mparams (msignature mdef)))
      (Hscope      : mt = AbstractImm \/
                     (mt = ConcreteState /\ method_subtype mdef.(msignature).(mtype) ConcreteState)),
      stmt_typing CT sΓ mt (SCall x m y args) sΓ

  (* Method call — SafeRO / ConcreteImm scope *)
  | ST_Call_safe_ro : forall CT sΓ mt x m y args argtypes Tthis Tx Ty mdef
      (Hwf         : wf_senv CT sΓ)
      (Hget_x      : static_getType sΓ x = Some Tx)
      (Hget_y      : static_getType sΓ y = Some Ty)
      (Hget_args   : static_getType_list sΓ args = Some argtypes)
      (Hthis       : get_this_qualified_type sΓ = Some Tthis)
      (Hfind_m     : FindMethodWithName CT (sctype Ty) m mdef)
      (Hnot_rcv    : x <> 0)
      (Hmt_not_abs : mdef.(msignature).(mtype) <> AbstractImm)
      (Hmt_not_cs  : mdef.(msignature).(mtype) <> ConcreteState)
      (Hret_sub    : qualified_type_subtype CT (vpa_mutability_tt_safe_ro Ty (mret (msignature mdef))) Tx)
      (Hrcv_sub    : qualified_type_subtype CT Ty (vpa_mutability_tt_safe_ro Ty (mreceiver (msignature mdef)))
                     \/ (sqtype Ty = RO /\ mdef.(msignature).(mreceiver).(sqtype) = RDM
                         /\ base_subtype CT (sctype Ty) mdef.(msignature).(mreceiver).(sctype)))
      (Harg_sub    : Forall2 (fun arg T => qualified_type_subtype CT arg (vpa_mutability_tt_safe_ro Ty T))
                       argtypes (mparams (msignature mdef)))
      (Hmt_not_abs2 : mt <> AbstractImm)
      (Hmt_not_cs2  : mt <> ConcreteState)
      (Hmt_sub     : method_subtype mdef.(msignature).(mtype) mt),
      stmt_typing CT sΓ mt (SCall x m y args) sΓ

  (* Sequence of statements *)
  | ST_Seq : forall CT sΓ mt s1 sΓ' s2 sΓ''
      (Hwf    : wf_senv CT sΓ)
      (Htype1 : stmt_typing CT sΓ mt s1 sΓ')
      (Htype2 : stmt_typing CT sΓ' mt s2 sΓ''),
      stmt_typing CT sΓ mt (SSeq s1 s2) sΓ''
.

Lemma stmt_typing_wf_env : forall CT sΓ mt stmt sΓ'
  (Htyping : stmt_typing CT sΓ mt stmt sΓ'),
  wf_senv CT sΓ.
Proof.
  intros CT sΓ mt stmt sΓ' Htyping.
  induction Htyping; auto.
Qed.

Lemma new_stmt_args_length : forall CT sΓ mt x qc C args argtypes consig
  (Htyping : stmt_typing CT sΓ mt (SNew x qc C args) sΓ)
  (Hstatic : static_getType_list sΓ args = Some argtypes)
  (Hconsig : constructor_sig_lookup CT C = Some consig),
  length consig.(cparams) = length args.
Proof.
  intros CT sΓ mt x qc C args argtypes consig Htyping Hstatic Hconsig.
  inversion Htyping; subst.
  assert (consig = consig0) by congruence.
  assert (argtypes = argtypes0) by congruence.
  subst.
  apply Forall2_length in Harg_sub.
  rewrite length_map in Harg_sub.
  rewrite <- Harg_sub.
  eapply static_getType_list_preserves_length; eauto.
Qed.

Definition wf_constructor_object (CT : class_table) (C : class_name) (ctor : constructor_def) : Prop :=
  parent_lookup CT C = None /\
  constructor_def_lookup CT C = Some ctor /\
  let sig := csignature ctor in
  let q_c := cqualifier sig in
  Some q_c = bound CT C /\
  cparams sig = [] /\
  CollectFields CT C [].

Definition wf_constructor (CT : class_table) (c : class_name) (ctor : constructor_sig) : Prop :=
  (* 1. Constructor qualifier matches class bound *)
  bound CT c = Some (cqualifier ctor) /\
  
  (* 2. Parameter types are well-formed *)
  Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) (cparams ctor) /\
  
  (* 3. Parameter count matches field count *)
  exists field_defs, 
    CollectFields CT c field_defs /\
    length (cparams ctor) = length field_defs /\
    
  (* 4. Parameter types are compatible with field types *)
  Forall2 (fun param_type field_def =>
    qualified_type_subtype CT param_type 
      {| sqtype := vpa_mutability_constructor_fld (cqualifier ctor) (mutability (ftype field_def));
         sctype := f_base_type (ftype field_def) |})
    (cparams ctor) field_defs.

Definition wf_method (CT : class_table) (C : class_name) (mdef : method_def) : Prop :=
  let mtype := mdef.(msignature).(mtype) in
  let msig := msignature mdef in
  let methodbody := mbody mdef in
  let mbodystmt := mbody_stmt methodbody in
  let sΓ := msig.(mreceiver) :: msig.(mparams) in
  exists sΓ' mbodyrettype,
    stmt_typing CT sΓ mtype mbodystmt sΓ' /\
    let mbodyretvar := mreturn methodbody in
    mbodyretvar < dom sΓ' /\
    nth_error sΓ' mbodyretvar = Some mbodyrettype /\
    qualified_type_subtype CT mbodyrettype (mret msig) /\
    (* Rocq scope note: the paper presents viewpoint-adapted variant
       overriding, but this mechanization intentionally uses invariant
       overriding. If a parent method exists, the child signature must match
       exactly. *)
    (forall parent_def parent mdef_parent,
      find_class CT C = Some parent_def ->
      super (signature parent_def) = Some parent ->
      FindMethodWithName CT parent (mname msig) mdef_parent ->
      msignature mdef_parent = msig).

(* Well-formedness of class *)
Inductive wf_class : class_table -> class_def -> Prop :=

(* Object class *)
| WFObjectDef : forall CT cdef class_name
    (Hno_super    : cdef.(signature).(super) = None)
    (Hrdm         : cdef.(signature).(class_qualifier) = RDM_c)
    (Hno_fields   : cdef.(body).(Syntax.fields) = [])
    (Hno_methods  : cdef.(body).(methods) = [])
    (Hcname       : cdef.(signature).(cname) = class_name)
    (Hwf_ctor     : wf_constructor_object CT class_name cdef.(body).(constructor))
    (Hwf_fields   : Forall (wf_field CT) cdef.(body).(Syntax.fields))
    (Hnodup       : NoDup (map (fun mdef => mname (msignature mdef)) cdef.(body).(methods))),
    wf_class CT cdef

(* Other class *)
| WFOtherDef : forall CT cdef superC thisC
    (Hsuper    : cdef.(signature).(super) = Some superC)
    (Hcname    : cdef.(signature).(cname) = thisC)
    (Hordering : thisC > superC),
    let sig := cdef.(signature) in
    let bod := cdef.(body) in
    let C := cname sig in
    let qC := class_qualifier sig in
    (wf_constructor CT C (csignature (constructor bod)) /\
    Forall (wf_method CT C) (methods bod) /\
    NoDup (map (fun mdef => mname (msignature mdef)) (methods bod)) /\
    match bound CT superC with
    | Some q_super =>
        exists fs, CollectFields CT C fs /\
        (qC = q_super \/ q_super = RDM_c) /\
        Forall (wf_field CT) fs
    | None =>
        CollectFields CT C []
    end) ->
    wf_class CT cdef
.

(* Enhanced class table well-formedness *)
Definition wf_class_table (CT : class_table) : Prop :=
  let object_class_at_zero :=
    exists obj_def, find_class CT 0 = Some obj_def /\
                    super (signature obj_def) = None in
  let non_object_classes_extend_object :=
    forall i def, i > 0 -> find_class CT i = Some def ->
                  super (signature def) <> None in
  let class_name_matches_index :=
    forall i def, find_class CT i = Some def <->
                  cname (signature def) = i in
  Forall (wf_class CT) CT /\
  object_class_at_zero /\
  non_object_classes_extend_object /\
  class_name_matches_index.

Lemma find_class_cname_consistent : forall CT i def
  (Hwf_ct : wf_class_table CT)
  (Hfind  : find_class CT i = Some def),
  cname (signature def) = i.
Proof.
  intros CT i def Hwf_ct Hfind.
  unfold wf_class_table in Hwf_ct.
  destruct Hwf_ct as [_ Hcname_consistent].
  apply Hcname_consistent; exact Hfind.
Qed.

Lemma find_class_consistent : forall CT i def def'
  (Hwf_ct : wf_class_table CT)
  (Hfind  : find_class CT i = Some def)
  (Hfind' : find_class CT i = Some def'),
  def = def'.
Proof.
  intros CT i def def' Hwf_ct Hfind Hfind'.
  rewrite Hfind in Hfind'.
  injection Hfind' as Heq.
  exact Heq.
Qed.

Lemma sf_def_rel_wf_field : forall CT C f fdef
  (Hwf_ct  : wf_class_table CT)
  (Hsf_def : sf_def_rel CT C f fdef),
  wf_field CT fdef.
Proof.
  intros CT C f fdef Hwf_ct Hsf_def.
  unfold sf_def_rel in Hsf_def.
  inversion Hsf_def as [CT' C' fields f' fdef' Hcf Hget]. subst.
  generalize dependent fdef.
  induction Hcf; intros fdef Hget.
  - (* CF_NotFound case *)
    intros Hgget.
    inversion Hget as [CT' C' fields f' fdef' Hcf Hget']. subst.
    assert (Hfields_empty : fields = []).
    {
      eapply collect_fields_deterministic_rel; eauto.
      apply CF_NotFound. exact Hnone.
    }
    subst fields.
    unfold gget in Hget'.
    simpl in Hget'.
    exfalso.
    simpl in Hget'.
    destruct f; discriminate Hget'.
  - (* CF_Object case *)
    intros Hgget.
    unfold gget in Hgget.
    simpl in Hgget.
    destruct f; discriminate Hgget.
  - (* CF_Inherit case *)
    intros Hgget.
    unfold gget in Hgget.
    rewrite nth_error_app in Hgget.
    destruct (lt_dec f (length parent_fields)) as [Hlt | Hge].
    + (* Field is from parent class *)
      apply IHHcf; auto.
      apply FL_Found with parent_fields; auto.
      unfold gget.
      destruct (f <? dom parent_fields) eqn:Hcmp.
      -- exact Hgget.
      -- exfalso. 
        apply Nat.ltb_nlt in Hcmp.
        lia.
      --
      unfold gget.
    assert (Hcmp : f <? dom parent_fields = true).
    {
      apply Nat.ltb_lt.
      exact Hlt.
    }
    rewrite Hcmp in Hgget.
    exact Hgget.
    + (* Field is from own class *)
    assert (Hown_field : nth_error own_fields (f - dom parent_fields) = Some fdef).
    {
      assert (Hcmp : f <? dom parent_fields = false).
      {
        apply Nat.ltb_nlt.
        exact Hge.
      }
      rewrite Hcmp in Hgget.
      exact Hgget.
    }
    assert (HWFC : wf_class CT def).
    {
      unfold wf_class_table in Hwf_ct.
      destruct Hwf_ct as [wf _].
      eapply Forall_nth_error; eauto.
    }
    inversion HWFC; subst.
  rewrite Hno_fields in Hown_field.
  simpl in Hown_field.
  destruct (f - dom parent_fields) as [|ntest]; simpl in Hown_field; discriminate Hown_field.
  subst sig0.
  destruct H as [Hwf_ctor [Hwf_methods Hbound_case]].
  destruct (bound CT superC) as [q_super|] eqn:Hbound.
  ++ (* Some q_super case *)
    destruct Hbound_case as [mnameunique fieldlist].
    destruct fieldlist as [fs fieldlistproperty].
    destruct fieldlistproperty as [collectfields [boundqualifier wellformedfields]].
    assert (Hfields_eq : fs = parent_fields ++ fields (body def)).
    {
      eapply collect_fields_deterministic_rel; eauto.
      assert (HC_eq : C = C0).
      {
        unfold C0, sig.
        symmetry.
        eapply find_class_cname_consistent; eauto.
      }
      subst C0.
      apply CF_Inherit with (def := def) (parent := parent); eauto.
      
      rewrite <- HC_eq.
      exact Hfind.
    }
    subst fs.
    apply Forall_app in wellformedfields.
    destruct wellformedfields as [_ Hwf_own].
    eapply Forall_nth_error; eauto.
  ++ (* None case *)
    exfalso.
    destruct Hbound_case as [Hnodup Hcf_empty].
    assert (Hfields_eq : [] = parent_fields ++ fields (body def)).
    {
      eapply collect_fields_deterministic_rel; eauto.
      apply CF_Inherit with (def := def) (parent := parent); eauto.
            assert (HC_eq : C = C0).
      {
        unfold C0, sig.
        symmetry.
        eapply find_class_cname_consistent; eauto.
      }
      rewrite <- HC_eq.
      exact Hfind.
    }
    destruct parent_fields, (fields (body def)); simpl in Hfields_eq; try discriminate.
    simpl in Hown_field.
    destruct (f - 0); simpl in Hown_field; discriminate.
Qed.

Lemma expr_has_type_class_in_table : forall CT mt sΓ e T
  (HWFCT : wf_class_table CT)
  (Htype : expr_has_type CT mt sΓ e T),
  sctype T < dom CT.
Proof.
  intros CT mt sΓ e T HWFCT Htype.
  induction Htype.
  - (* ET_Null case *)
    exact Hdom.
  - (* ET_Var case *)
    (* Use the fact that variables in well-formed environments have bounded types *)
    eapply senv_var_domain; eauto.
  - (* ET_Field case *)
    assert (Hwf_field : wf_field CT fDef).
    {
      eapply sf_def_rel_wf_field; eauto.
    }
    unfold wf_field, wf_stypeuse in Hwf_field.
    destruct (bound CT (f_base_type (ftype fDef))) as [qc|] eqn:Hbound.
    +
     destruct Hwf_field as [qbound Hwf_field].
     
      (* rewrite vpa_type_to_type_sctype. *)
      simpl.
      apply bound_some_dom in Hbound.
      exact Hbound.
    + unfold bound in Hbound. destruct Hwf_field as [qbound [Hfalse Hfieldwfm]]. easy.
  - (* ET_Field case *)
    assert (Hwf_field : wf_field CT fDef).
    {
      eapply sf_def_rel_wf_field; eauto.
    }
    unfold wf_field, wf_stypeuse in Hwf_field.
    destruct (bound CT (f_base_type (ftype fDef))) as [qc|] eqn:Hbound.
    +
     destruct Hwf_field as [qbound Hwf_field].
     
      (* rewrite vpa_type_to_type_sctype. *)
      simpl.
      apply bound_some_dom in Hbound.
      exact Hbound.
    + unfold bound in Hbound. destruct Hwf_field as [qbound [Hfalse Hfieldwfm]]. easy.  
Qed.

(* Well-formedness of program. Put it at the end because the main statement needs to be well-typed. *)
(* Definition WFProgram (p: program_def) : Prop :=
  Forall (fun decl => WFClass p.(classes) decl) p.(classes) . *)
Lemma find_app : forall A (f : A -> bool) l1 l2 x
  (H : find f l1 = Some x),
  find f (l1 ++ l2) = Some x.
Proof.
  intros A f l1 l2 x H.
  induction l1 as [|h t IH].
  - (* l1 = [] *)
    simpl in H.
    discriminate.
  - (* l1 = h :: t *)
    simpl in H |- *.
    destruct (f h) eqn:Heq.
    + (* f h = true *)
      injection H as Heq_x.
      subst x.
      reflexivity.
    + (* f h = false *)
      apply IH.
      exact H.
Qed.

Lemma find_app_none : forall A (f : A -> bool) l1 l2
  (H : find f l1 = None),
  find f (l1 ++ l2) = find f l2.
Proof.
  intros A f l1 l2 H.
  induction l1 as [|h t IH].
  - (* l1 = [] *)
    simpl.
    reflexivity.
  - (* l1 = h :: t *)
    simpl in H |- *.
    destruct (f h) eqn:Heq.
    + (* f h = true - contradiction *)
      discriminate H.
    + (* f h = false *)
      apply IH.
      exact H.
Qed.

Lemma find_filter_equiv : forall A (f g : A -> bool) l
  (H : forall x, In x l -> f x = true -> g x = true),
  find f (filter g l) = find f l.
Proof.
  intros A f g l H.
  induction l as [|h t IH].
  - (* l = [] *)
    simpl.
    reflexivity.
  - (* l = h :: t *)
    simpl.
    destruct (g h) eqn:Hg.
    + (* g h = true *)
      simpl.
      destruct (f h) eqn:Hf.
      * (* f h = true *)
        reflexivity.
      * (* f h = false *)
        apply IH.
        intros x Hin Hfx.
        apply H; auto.
        right; exact Hin.
    + (* g h = false *)
      destruct (f h) eqn:Hf.
      * (* f h = true, but g h = false - contradiction with H *)
        exfalso.
        have Hg_true := H h (or_introl eq_refl) Hf.
        rewrite Hg in Hg_true.
        discriminate.
      * (* f h = false *)
        apply IH.
        intros x Hin Hfx.
        apply H; auto.
        right; exact Hin.
Qed.

Lemma find_some_iff : forall A (f : A -> bool) l,
  (exists x, find f l = Some x) <-> (exists x, In x l /\ f x = true).
Proof.
  intros A f l.
  split.
  - (* -> direction *)
    intro H.
    destruct H as [x Hfind].
    exists x.
    apply find_some in Hfind.
    exact Hfind.
  - (* <- direction *)
    intro H.
    destruct H as [x [Hin Hf]].
    induction l as [|h t IH].
    + (* l = [] *)
      simpl in Hin.
      contradiction.
    + (* l = h :: t *)
      simpl.
      destruct (f h) eqn:Heq.
      * (* f h = true *)
        exists h.
        reflexivity.
      * (* f h = false *)
        apply IH.
        simpl in Hin.
        destruct Hin as [Heq_h | Hin_t].
        -- (* x = h *)
           subst x.
           rewrite Hf in Heq.
           discriminate.
        -- (* x in t *)
           exact Hin_t.
Qed.

Lemma override_own_method_found : forall parent_methods own_methods m mdef
  (Hown : gget_method own_methods m = Some mdef),
  gget_method (override parent_methods own_methods) m = Some mdef.
Proof.
  intros parent_methods own_methods m mdef Hown.
unfold override.
unfold gget_method.
induction own_methods as [|h t IH].
- (* own_methods = [] *)
  simpl in Hown.
  discriminate.
- (* own_methods = h :: t *)
  simpl.
  destruct (eq_method_name (mname (msignature h)) m) eqn:Heq.
  + (* Found in head *)
    unfold gget_method in Hown.
    simpl in Hown.
    rewrite Heq in Hown.
    injection Hown as Heq_mdef.
    subst mdef.
    reflexivity.
  + (* Not in head, check tail *)
  assert (Hfind_t : find (fun mdef0 => eq_method_name (mname (msignature mdef0)) m) t = Some mdef).
  {
    unfold gget_method in Hown.
    simpl in Hown.
    rewrite Heq in Hown.
    exact Hown.
  }
  eapply find_app.
  exact Hfind_t.
Qed.

Lemma override_parent_method_preserved : forall parent_methods own_methods m
  (Hnone : gget_method own_methods m = None),
  gget_method (override parent_methods own_methods) m = gget_method parent_methods m.
Proof.
  intros parent_methods own_methods m Hnone.
  unfold override, gget_method.
  induction own_methods as [|h t IH].
  - (* own_methods = [] *)
    simpl.
    induction parent_methods as [|h t IH].
    -- simpl. reflexivity.
    -- simpl. 
    destruct (eq_method_name (mname (msignature h)) m) eqn:Heq.
    --- (* eq_method_name returns true *)
      reflexivity.
    --- (* eq_method_name returns false *)
      exact IH.
  - (* own_methods = h :: t *)
    simpl in Hnone |- *.
    destruct (eq_method_name (mname (msignature h)) m) eqn:Heq.
    + (* Found in h - contradiction *)
      discriminate Hnone.
    + (* Not in h, continue *)
    assert (Hfind_t_none : find (fun mdef => eq_method_name (mname (msignature mdef)) m) t = None).
    {
      unfold gget_method in Hnone.
      exact Hnone.
    }
    rewrite find_app_none.
    -- (* Show find on t returns None *)
      exact Hfind_t_none.
    -- (* Show filters are equivalent *)
      apply find_filter_equiv.
      intro pmdef.
      intro Hin.
      rewrite Bool.negb_orb.
      rewrite Bool.andb_true_iff.
      split.
    --- (* Show ~~eq_method_name(pmdef, h) = true *)
      rewrite Bool.negb_true_iff.
      assert (Hneq : mname (msignature pmdef) <> mname (msignature h)).
      {
        intro Heq_names.
        rewrite Heq_names in H.
        rewrite H in Heq.
        discriminate.
      }
      destruct (eq_method_name (mname (msignature pmdef)) (mname (msignature h))) eqn:Heq_pmdef_h.
      +++ (* eq_method_name returns true - contradiction *)
        exfalso.
        apply Hneq.
        apply Nat.eqb_eq in Heq_pmdef_h.
        exact Heq_pmdef_h.
      +++ (* eq_method_name returns false - this is what we want *)
        reflexivity.
    --- (* Show ~~existsb(...) = true *)
      rewrite Bool.negb_true_iff.
      destruct (existsb (fun omdef => eq_method_name (mname (msignature pmdef)) (mname (msignature omdef))) t) eqn:Hexistsb.
      +++ (* existsb returns true - contradiction *)
        exfalso.
        apply existsb_exists in Hexistsb.
        destruct Hexistsb as [omdef [Hin_t Heq_names]].
        (* pmdef matches m, and omdef has same name as pmdef, so omdef matches m *)
        assert (Homdef_m : eq_method_name (mname (msignature omdef)) m = true).
        {
          apply Nat.eqb_eq in H.
          apply Nat.eqb_eq in Heq_names.
          rewrite <- Heq_names.
          apply Nat.eqb_eq.
          exact H.
        }
        (* This contradicts that find on t returns None *)
        unfold gget_method in Hnone.
        assert (Hcontra : find (fun mdef => eq_method_name (mname (msignature mdef)) m) t <> None).
        {
          assert (Hfind_exists : exists x, find (fun mdef => eq_method_name (mname (msignature mdef)) m) t = Some x).
          {
            apply find_some_iff.
            exists omdef.
            split; [exact Hin_t | exact Homdef_m].
          }
          intro Hcontra.
          destruct Hfind_exists as [x Hfind_x].
          rewrite Hfind_x in Hcontra.
          discriminate.
        }
        rewrite Hfind_t_none in Hcontra.
        apply Hcontra.
        reflexivity.
      +++ (* existsb returns false - this is what we want *)
        reflexivity.
Qed.

Lemma override_preserves_param_count : forall CT C parent_methods own_methods m mdef mdef'
  (Hwf_ct   : wf_class_table CT)
  (Hcollect : CollectMethods CT C (override parent_methods own_methods))
  (Hown     : gget_method own_methods m = Some mdef)
  (Hoverride : gget_method (override parent_methods own_methods) m = Some mdef'),
  dom (mparams (msignature mdef)) = dom (mparams (msignature mdef')).
Proof.
  intros CT C parent_methods own_methods m mdef mdef' Hwf_ct Hcollect Hown Hoverride.
  have Hfound := override_own_method_found parent_methods own_methods m mdef Hown.
  rewrite Hfound in Hoverride.
  injection Hoverride as Heq.
  subst mdef'.
  reflexivity.
Qed.

Lemma parent_implies_strict_ordering : forall CT C D cdef_C
  (Hwf    : wf_class_table CT)
  (Hcdom  : C < dom CT)
  (Hfind  : find_class CT C = Some cdef_C)
  (Hsuper : super (signature cdef_C) = Some D),
  D < C.
Proof.
  intros CT C D cdef_C Hwf Hcdom Hfind Hsuper.
  
  (* From well-formed class table, get wf_class for C *)
  assert (Hwf_class_C : wf_class CT cdef_C).
  {
    unfold wf_class_table in Hwf.
    destruct Hwf as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  
  (* From wf_class, parent relationship implies strict ordering *)
  inversion Hwf_class_C; subst.
  - (* WFObjectDef - contradiction since C has parent *)
    rewrite Hno_super in Hsuper. discriminate.
  - (* WFOtherDef *)
    assert (Hcname_eq : cname (signature cdef_C) = C).
    {
      unfold wf_class_table in Hwf.
      destruct Hwf as [_ [_ [_ Hcname_consistent]]].
      apply Hcname_consistent.
      exact Hfind.
    }
    rewrite Hsuper0 in Hsuper.
    injection Hsuper as Heq.
    subst D.
    rewrite Hcname_eq in Hordering.
    exact Hordering.
Qed.

Lemma collect_fields_exists : forall CT c
  (Hwf_classtable : wf_class_table CT)
  (Hdom           : c < dom CT),
  exists field_defs, CollectFields CT c field_defs.
Proof.
  intros CT c Hwf_classtable.
  induction c using lt_wf_ind.
  intros Hdom.
  assert (Hfind : exists def, find_class CT c = Some def).
  {
    apply find_class_Some. exact Hdom.
  }
  destruct Hfind as [def Hfind].
  destruct (super (signature def)) as [parent|] eqn:Hsuper.
  - (* Case: class has superclass *)
    assert (Hparent_dom : parent < c).
    {
      eapply parent_implies_strict_ordering with (cdef_C:= def); eauto.
    }
    assert (Hparent_in_ct : parent < dom CT).
    {
      lia.
    }
    (* Apply induction hypothesis *)
    destruct (H parent Hparent_dom Hparent_in_ct) as [parent_fields Hparent_collect].
    exists (parent_fields ++ Syntax.fields (body def)).
    apply CF_Inherit with (def := def) (parent := parent) (parent_fields := parent_fields) (own_fields := Syntax.fields (body def)); auto.
  - (* Case: Object class (no superclass) *)
    exists ([] : list field_def).
    apply CF_Object with def; auto.
Qed.

Lemma find_overriding_method_deterministic : forall CT C mname mdef1 mdef2
  (Hwf_ct : wf_class_table CT)
  (Hbound : C < dom CT)
  (Hfind1 : FindMethodWithName CT C mname mdef1)
  (Hfind2 : FindMethodWithName CT C mname mdef2),
  mdef1 = mdef2.
Proof.
  intros CT C mname mdef1 mdef2 Hwf_ct Hbound Hfind1 Hfind2.
  (* Strong induction on C *)
  induction C using lt_wf_ind.
  intros.
  
  inversion Hfind1; subst.
  inversion Hfind2; subst.
  
  (* Case analysis on both calls *)
  - (* Both find locally *)
    (* Establish same class definition *)
    assert (Heq_def : def = def0).
    { 
      rewrite Hfind in Hfind0.
      injection Hfind0 as Heq.
      exact Heq.
    }
    subst def0.
    rewrite Hget_method in Hget_method0.
    injection Hget_method0 as Heq.
    exact Heq.
    
  - (* First local, second parent - contradiction *)
    exfalso.
    assert (Heq_def : def = def0).
    { 
      rewrite Hfind in Hfind0.
      injection Hfind0 as Heq.
      exact Heq.
    }
    subst def0.
    rewrite Hget_method in Hnot_here.
    discriminate Hnot_here.
    
  - (* First parent, second local - contradiction *)
    {
      inversion Hfind2; subst.
      - (* Case: Hfind2 finds method locally - contradiction *)
        assert (Heq_def : def = def0).
        { 
          rewrite Hfind in Hfind0.
          injection Hfind0 as Heq.
          exact Heq.
        }
        subst def0.
        rewrite Hget_method in Hnot_here.
        discriminate Hnot_here.
      - (* Case: Hfind2 also goes to parent *)
        assert (Heq_def : def = def0).
        { 
          rewrite Hfind in Hfind0.
          injection Hfind0 as Heq.
          exact Heq.
        }
        subst def0.
        assert (Heq_parent : parent = parent0).
        {
          rewrite Hsuper in Hsuper0.
          injection Hsuper0 as Heq.
          exact Heq.
        }
        subst parent0.
        
        (* Apply induction hypothesis *)
        apply (H parent).
        + (* parent < C *)
          eapply parent_implies_strict_ordering; eauto.
        + 
          assert (parent < C). 
          {eapply parent_implies_strict_ordering; eauto.
          }
          lia.
        + exact Hparent_fmn.
        + exact Hparent_fmn0. 
    }
Qed.

Lemma method_lookup_wf_class: forall CT C mdef cdef
  (Hwf_ct  : wf_class_table CT)
  (Hdom    : C < dom CT)
  (HfindC  : find_class CT C = Some cdef)
  (Hlookup : In mdef (methods (body cdef))),
  wf_method CT C mdef.
Proof.
  intros CT C mdef cdef Hwf_ct Hdom HfindC Hlookup.
  (* Get the well-formed class from the class table *)
  assert (Hwf_class : wf_class CT cdef).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  
  (* Extract the methods well-formedness from the class well-formedness *)
  inversion Hwf_class; subst.
    - (* WFObjectDef case *)
    exfalso.
    (* Object class has no methods, contradiction *)
    rewrite Hno_methods in Hlookup.
    simpl in Hlookup.
    exact Hlookup.
  - (* WFOtherDef case *)
    destruct H as [_ [Hforall_methods _]].
    (* Apply Forall to get wf_method for our specific mdef *)
    apply In_nth_error in Hlookup.
    destruct Hlookup as [n Hnth].
    assert (HC0_eq : C0 = C).
    {
      unfold C0.
      unfold wf_class_table in Hwf_ct.
      destruct Hwf_ct as [_ Hcname_consistent].
      apply Hcname_consistent.
      exact HfindC.
    }
    rewrite HC0_eq in Hforall_methods.
    eapply Forall_nth_error; eauto.
Qed.

Lemma method_lookup_in_wellformed_inherited: forall CT C m mdef
  (Hwf_ct  : wf_class_table CT)
  (Hdom    : C < dom CT)
  (Hlookup : FindMethodWithName CT C m mdef),
  exists D ddef, base_subtype CT C D /\ find_class CT D = Some ddef /\ In mdef (methods (body ddef)) /\ wf_method CT D mdef.
Proof.
  intros CT C m mdef Hwf_ct Hdom Hlookup.
  induction C as [C IH] using lt_wf_ind.
  inversion Hlookup; subst.
  - (* FOM_Here case *)
    exists C, def.
    split; [apply base_refl; exact Hdom | split; [exact Hfind | split]].
    + unfold gget_method in Hget_method.
      apply find_some in Hget_method.
      destruct Hget_method as [Hin _].
      (* rewrite <- H0. *)
      exact Hin.
    + eapply method_lookup_wf_class; eauto.
      unfold gget_method in Hget_method.
      apply find_some in Hget_method.
      destruct Hget_method as [Hin _].
      (* rewrite <- H0. *)
      exact Hin.
  - (* FOM_Super case *)
    assert (Hparent_lt : parent < C).
    {
      eapply parent_implies_strict_ordering; eauto.
    }
    assert (Hparent_dom : parent < dom CT) by lia.
    destruct (IH parent Hparent_lt Hparent_dom Hparent_fmn) as
      [D [ddef [Hsub [Hfind_D [Hin_D Hwf_D]]]]].
    exists D, ddef.
    split.
    + eapply base_trans.
      * eapply base_extends; eauto.
        unfold parent_lookup.
        rewrite Hfind.
        simpl.
        exact Hsuper.
      * exact Hsub.
    + split; [exact Hfind_D | split; [exact Hin_D | exact Hwf_D]].
Qed.

Lemma method_name_unique_implies_equal : forall methods mdef1 mdef2
  (Hnodup    : NoDup (map (fun mdef => mname (msignature mdef)) methods))
  (Hin1      : In mdef1 methods)
  (Hin2      : In mdef2 methods)
  (Hname_eq  : mname (msignature mdef1) = mname (msignature mdef2)),
  mdef1 = mdef2.
Proof.
  intros methods mdef1 mdef2 Hnodup Hin1 Hin2 Hname_eq.
  induction methods as [|h t IH].
  - (* methods = [] *)
    contradiction.
  - (* methods = h :: t *)
    simpl in Hnodup.
    inversion Hnodup; subst.
    simpl in Hin1, Hin2.
    destruct Hin1 as [Heq1 | Hin1_t], Hin2 as [Heq2 | Hin2_t].
    + (* Both are h *)
      rewrite <- Heq1, <- Heq2. reflexivity.
    + (* mdef1 = h, mdef2 in t *)
      exfalso.
      subst mdef1.
      apply H1.
      rewrite  Hname_eq.
      apply (in_map (fun mdef => mname (msignature mdef))).
      exact Hin2_t.
    + (* mdef1 in t, mdef2 = h *)
      exfalso.
      subst mdef2.
      apply H1.
      rewrite <- Hname_eq.
      apply (in_map (fun mdef => mname (msignature mdef))).
      exact Hin1_t.
    + (* Both in t *)
      apply IH; auto.
Qed.

Lemma override_local_precedence : forall parent_methods own_methods m mdef
  (Hown : gget_method own_methods m = Some mdef),
  gget_method (override parent_methods own_methods) m = Some mdef.
Proof.
  intros parent_methods own_methods m mdef Hown.
  unfold override.
  unfold gget_method in *.
  apply find_app.
  exact Hown.
Qed.

Lemma method_inheritance_exists : forall CT C D m mdef
  (Hwf_ct : wf_class_table CT)
  (Hsub   : base_subtype CT C D)
  (Hfind  : FindMethodWithName CT D m mdef),
  exists mdef', FindMethodWithName CT C m mdef'.
Proof.
  intros CT C D m mdef Hwf_ct Hsub.
  revert mdef.
  induction Hsub; intros mdef Hfind.
  - (* Reflexive *) exists mdef. exact Hfind.
  - (* Transitive *)
    assert (HD_dom : D < dom CT) by (eapply base_subtype_domain; eauto).
    apply IHHsub2 in Hfind; auto.
    destruct Hfind as [mdef_D HfindD].
    apply IHHsub1 in HfindD; auto.
  - (* Direct inheritance *)
    destruct (find_class CT C) as [def|] eqn:HfindC; [|unfold parent_lookup in Hparent; rewrite HfindC in Hparent; discriminate].
    destruct (gget_method (methods (body def)) m) as [mdef'|] eqn:Hget.
    + exists mdef'. eapply FOM_Here; eauto.
    + exists mdef. eapply FOM_Super; eauto.
      unfold parent_lookup in Hparent. rewrite HfindC in Hparent. simpl in Hparent. exact Hparent.
Qed.

Lemma method_signature_consistent_subtype : forall CT C D m mdef1 mdef2
  (Hwf_ct : wf_class_table CT)
  (Hsub   : base_subtype CT C D)
  (Hfind1 : FindMethodWithName CT C m mdef1)
  (Hfind2 : FindMethodWithName CT D m mdef2),
  msignature mdef1 = msignature mdef2.
Proof.
  intros CT C D m mdef1 mdef2 Hwf_ct Hsub Hfind1 Hfind2.
  generalize dependent mdef1. generalize dependent mdef2.
  induction Hsub; intros.
  - (* Reflexive *) 
    assert (mdef1 = mdef2) by (eapply find_overriding_method_deterministic; eauto).
    congruence.
  - (* Transitive *)
    assert (HD_dom : D < dom CT) by (eapply base_subtype_domain; eauto).
    (* Method m exists in E, and D <: E, so by inheritance m must exist in D *)
    assert (Hexists_D : exists mdef_D, FindMethodWithName CT D m mdef_D).
    {
      eapply method_inheritance_exists; eauto.
    }
    destruct Hexists_D as [mdef_D HfindD].
    assert (msignature mdef1 = msignature mdef_D) by (eapply IHHsub1; eauto).
    assert (msignature mdef_D = msignature mdef2) by (eapply IHHsub2; eauto).
    congruence.
  - (* Direct inheritance *)
    destruct (find_class CT C) as [def|] eqn:Hfind; [|unfold parent_lookup in Hparent; rewrite Hfind in Hparent; discriminate].
    assert (Hwf_class : wf_class CT def) by (unfold wf_class_table in Hwf_ct; destruct Hwf_ct as [Hforall _]; eapply Forall_nth_error; eauto).
    inversion Hwf_class; subst.
    + unfold parent_lookup in Hparent. rewrite Hfind in Hparent. simpl in Hparent. 
      exfalso. rewrite Hno_super in Hparent. discriminate.
    +
      destruct H as [_ [Hforall_methods _]].
      inversion Hfind1; subst.
  * (* mdef1 found locally in C *)
    assert (Heq_def : def = def0) by (rewrite Hfind in Hfind0; injection Hfind0; auto).
    subst def0.
    assert (Hin1 : In mdef1 (methods (body def))).
    { unfold gget_method in Hget_method. apply find_some in Hget_method. destruct Hget_method. exact H. }
    apply In_nth_error in Hin1.
    destruct Hin1 as [n Hn].
    eapply Forall_nth_error in Hforall_methods; eauto.
    unfold wf_method in Hforall_methods.
    destruct Hforall_methods as [sΓ' [mbodyrettype [_ [_ [_ [_ Hoverride]]]]]].
    unfold parent_lookup in Hparent. rewrite Hfind in Hparent. simpl in Hparent. symmetry.
    eapply Hoverride.
    -- assert (HC0_eq : C0 = C) by (unfold wf_class_table in Hwf_ct; destruct Hwf_ct as [_ [_ [_ Hcname]]]; apply Hcname; exact Hfind).
      rewrite HC0_eq. exact Hfind.
    -- unfold parent_lookup in Hparent. exact Hparent.
    -- assert (Hm_eq : mname (msignature mdef1) = m) by (eapply find_method_with_name_consistent; eauto).
      rewrite Hm_eq. exact Hfind2.
    * (* mdef1 inherited from parent - use determinism *)
      assert (Heq_def : def = def0) by (rewrite Hfind in Hfind0; injection Hfind0; auto).
      subst def0.
      assert (Heq_parent : parent = D).
      {
        unfold parent_lookup in Hparent.
        rewrite Hfind in Hparent.
        simpl in Hparent.
        rewrite Hsuper0 in Hparent.
        injection Hparent as Heq.
        exact Heq.
      }
      subst parent.
      assert (mdef1 = mdef2). {
        eapply find_overriding_method_deterministic with (C:=D); eauto.
      }
      congruence.
Qed.
