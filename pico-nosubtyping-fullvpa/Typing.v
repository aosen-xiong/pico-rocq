Require Import Syntax Subtyping ViewpointAdaptation Helpers.
Require Import String.
Require Import List.
Import ListNotations.
Require Import Arith.

(* STATIC HELPER FUNCTIONS *)

Inductive CollectFields : class_table -> class_name -> list field_def -> Prop :=
  (* Base case: class not found *)
  | CF_NotFound : forall CT C,
      find_class CT C = None ->
      CollectFields CT C []
      
  (* Inductive case: class with superclass *)
  | CF_Body : forall CT C def own_fields,
      find_class CT C = Some def ->
      own_fields = Syntax.fields (body def) ->
      CollectFields CT C own_fields.

(* Field lookup relation *)
Inductive FieldLookup : class_table -> class_name -> var -> field_def -> Prop :=
  | FL_Found : forall CT C fields f fdef,
      CollectFields CT C fields ->
      gget fields f = Some fdef ->
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
Lemma collect_fields_deterministic_rel : forall CT C fields1 fields2,
  CollectFields CT C fields1 ->
  CollectFields CT C fields2 ->
  fields1 = fields2.
Proof.
  intros CT C fields1 fields2 H1 H2.
  generalize dependent fields2.
  induction H1; intros fields2 H3; inversion H3; subst.
  - (* Both not found *) reflexivity.
  - (* H1: not found, H2: inherit - contradiction *)
    rewrite H in H0. discriminate.
  - (* H1: object, H2: inherit - contradiction *)
    rewrite H in H1.
     discriminate.
  - (* Both inherit *)
  assert (def = def0). 
  {
  rewrite H in H1. injection H1 as Heq. exact Heq.
  }
  rewrite H0.
  reflexivity.
Qed.

Lemma field_lookup_deterministic_rel : forall CT C f fdef1 fdef2,
  FieldLookup CT C f fdef1 ->
  FieldLookup CT C f fdef2 ->
  fdef1 = fdef2.
Proof.
  intros CT C f fdef1 fdef2 H1 H2.
  inversion H1 as [CT1 C1 fields1 f1 fdef1' Hcf1 Hget1]. subst.
  inversion H2 as [CT2 C2 fields2 f2 fdef2' Hcf2 Hget2]. subst.
  apply (collect_fields_deterministic_rel CT C fields1 fields2) in Hcf1; auto.
  subst. rewrite Hget1 in Hget2. injection Hget2. auto.
Qed.

Lemma sf_assignability_deterministic_rel : forall CT C f a1 a2,
  sf_assignability_rel CT C f a1 ->
  sf_assignability_rel CT C f a2 ->
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

(* Collect fields of a class and its superclasses, with fuel to prevent infinite loops *)
(* Fixpoint collect_fields_fuel (fuel : nat) (CT : class_table) (C : class_name) : list field_def :=
  match fuel with
  | O => []
  | S fuel' =>
    match find_class CT C with
    | None => []
    | Some def =>
      let super_fields :=
        match super (signature def) with
        | Some n => collect_fields_fuel fuel' CT n
        | None => []
        end in
      super_fields ++ fields (body def)
    end
  end.

Definition collect_fields (CT : class_table) (C : class_name) : list field_def :=
collect_fields_fuel (length CT) CT C.

Definition fields := collect_fields.

Lemma collect_fields_fuel_zero : forall CT C,
  collect_fields_fuel 0 CT C = [].
Proof.
  intros CT C.
  simpl.
  reflexivity.
Qed.

Lemma collect_fields_fuel_no_class : forall fuel CT C,
  find_class CT C = None ->
  collect_fields_fuel fuel CT C = [].
Proof.
  intros fuel CT C Hno_class.
  destruct fuel as [|fuel'].
  - simpl. reflexivity.
  - simpl. rewrite Hno_class. reflexivity.
Qed.

Lemma collect_fields_fuel_structure : forall fuel' CT C def,
  find_class CT C = Some def ->
  collect_fields_fuel (S fuel') CT C = 
    (match super (signature def) with
     | Some parent => collect_fields_fuel fuel' CT parent
     | None => []
     end) ++ Syntax.fields (body def).
Proof.
  intros fuel' CT C def Hfind.
  simpl. rewrite Hfind. 
  destruct (super (signature def)) as [parent|].
  + reflexivity.
  + simpl. reflexivity.
Qed.

Lemma collect_fields_fuel_inherits_parent : forall fuel CT C def parent f fdef,
  find_class CT C = Some def ->
  super (signature def) = Some parent ->
  fuel > 0 ->
  nth_error (collect_fields_fuel fuel CT parent) f = Some fdef ->
  nth_error (collect_fields_fuel (S fuel) CT C) f = Some fdef.
Proof.
  intros fuel CT C def parent f fdef Hfind Hsuper Hfuel Hparent_field.
  simpl.
  rewrite Hfind.
  rewrite Hsuper.
  (* First prove the length bound *)
  assert (Hbound : f < length (collect_fields_fuel fuel CT parent)).
  {
    apply nth_error_Some.
    rewrite Hparent_field.
    discriminate.
  }
  rewrite nth_error_app1.
  - exact Hbound.
  - exact Hparent_field.
Qed.

(* Static field def look up; We assume identifiers are globally unique  *)
Definition sf_def (CT: class_table) (C: class_name) (f: var) : option field_def :=
  gget (fields CT C) f.

(* Static field assignablity lookup *)
Definition sf_assignability (CT: class_table) (C: class_name) (f: var) : option a :=
  match sf_def CT C f with
  | Some fd => Some (assignability (ftype fd))
  | None => None
  end.

(* Static field mutability lookup *)
Definition sf_mutability (CT: class_table) (C: class_name) (f: var) : option q_f :=
  match sf_def CT C f with
  | Some fd => Some (mutability (ftype fd))
  | None => None
  end.

(* Static field base type lookup *)
Definition sf_base (CT: class_table) (C: class_name) (f: var) : option class_name :=
  match sf_def CT C f with
  | Some fd => Some (f_base_type (ftype fd))
  | None => None
  end.

Lemma field_lookup_deterministic : forall CT C f fdef fdef',
  sf_def CT C f = Some fdef ->
  sf_def CT C f = Some fdef' ->
  fdef = fdef'.
Proof.
  intros CT C f fdef fdef' H1 H2.
  unfold sf_def in *.
  rewrite H1 in H2.
  injection H2.
  auto.
Qed.

(* Fields collection is deterministic *)
Lemma collect_fields_deterministic : forall CT C fds fds',
  collect_fields CT C = fds ->
  collect_fields CT C = fds' ->
  fds = fds'.
Proof.
  intros CT C fds fds' H1 H2.
  rewrite H1 in H2.
  exact H2.
Qed.  *)

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

Lemma constructor_def_lookup_dom : forall CT C ctor,
  constructor_def_lookup CT C = Some ctor ->
  C < dom CT.
Proof.
  intros CT C ctor H.
  unfold constructor_def_lookup in H.
  destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
  apply find_class_dom in Hfind.
  exact Hfind.
Qed.

Lemma constructor_sig_lookup_dom : forall CT C csig,
  constructor_sig_lookup CT C = Some csig ->
  C < dom CT.
Proof.
  intros CT C csig H.
  unfold constructor_sig_lookup in H.
  destruct (constructor_def_lookup CT C) as [ctor|] eqn:Hctor; [|discriminate].
  apply constructor_def_lookup_dom in Hctor.
  exact Hctor.
Qed.

Lemma constructor_sig_lookup_implies_def : forall CT C csig,
  constructor_sig_lookup CT C = Some csig ->
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

Lemma constructor_def_lookup_Some : forall CT C,
  C < dom CT ->
  exists ctor, constructor_def_lookup CT C = Some ctor.
Proof.
  intros CT C H.
  apply find_class_Some in H.
  destruct H as [def Hdef].
  unfold constructor_def_lookup.
  rewrite Hdef.
  eexists. reflexivity.
Qed.

Lemma constructor_sig_lookup_Some : forall CT C,
  C < dom CT ->
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

(* Definition override (parent_methods own_methods : list method_def) : list method_def :=
  own_methods ++ filter (fun pmdef => 
    negb (existsb (fun omdef => 
      eq_method_name (mname (msignature pmdef)) (mname (msignature omdef))) 
    own_methods)) parent_methods. *)

Inductive CollectMethods : class_table -> class_name -> list method_def -> Prop :=
  (* Class not found *)
  | CM_NotFound : forall CT C,
      find_class CT C = None ->
      CollectMethods CT C []
  (* Object class: no superclass *)
  (* | CM_Object : forall CT C def,
      find_class CT C = Some def ->
      super (signature def) = None ->
      C < dom CT ->
      CollectMethods CT C (methods (body def)) *)
  (* Class with superclass *)
  | CM_Inherit : forall CT C def own_methods,
      find_class CT C = Some def ->
      C < dom CT ->
      own_methods = methods (body def) ->
      CollectMethods CT C own_methods.
 
Lemma collect_methods_deterministic : forall CT C methods1 methods2,
  CollectMethods CT C methods1 ->
  CollectMethods CT C methods2 ->
  methods1 = methods2.
Proof.
  intros CT C methods1 methods2 H1 H2.
  generalize dependent methods2.
  induction H1; intros.
  inversion H2; subst.
  - (* Both CM_NotFound *)
    reflexivity.
  - (* CM_NotFound vs CM_Object - contradiction *)
    rewrite H in H0. discriminate.
  - (* CM_NotFound vs CM_Inherit - contradiction *)
    inversion H2; subst.
    -- rewrite H in H3. discriminate.
    -- rewrite H in H3. injection H3 as Heq. subst def0. reflexivity.
Qed.

(* STATIC WELLFORMEDNESS CONDITION *)
(* Well-formedness of type use *)
Definition wf_stypeuse (CT : class_table) (q_use: q) (c: class_name) : Prop :=
  match bound CT c with
  | Some q_bound => 
                  (* AOSEN: Current rule disallow direct lost variable in the environment including the receiver
                   which should not be important? *)
                  q_subtype (vpa_mutabilty_bound q_use q_bound) q_use /\ 
                   c < dom CT
  | None => False
  end.

(* Well-formedness of field *)
Definition wf_field (CT : class_table) (fdef: field_def) : Prop :=
  exists qbound,
    bound CT (f_base_type (ftype fdef)) = Some qbound /\
    vpa_mutabilty_fld_bound (mutability (ftype fdef)) qbound = (mutability (ftype fdef)).

(* Well-formedness of static environment *)
Definition wf_senv (CT : class_table) (sΓ : s_env) : Prop :=
  (* The first variable is the receiver and should always be present *)
  dom sΓ > 0 /\
  Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) sΓ.

Lemma senv_var_domain : forall CT sΓ i T,
  wf_senv CT sΓ ->
  nth_error sΓ i = Some T ->
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
  | FOM_Here : forall CT C def own_methods m mdef,
      find_class CT C = Some def ->
      own_methods = methods (body def) ->
      gget_method own_methods m = Some mdef ->
      FindMethodWithName CT C m mdef.

Lemma gget_method_name_consistent : forall methods m mdef,
  gget_method methods m = Some mdef ->
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

Lemma find_method_with_name_consistent : forall CT C m mdef,
  FindMethodWithName CT C m mdef ->
  mname (msignature mdef) = m.
Proof.
  intros CT C m mdef H.
  induction H.
  - (* FOM_Here *)
    eapply gget_method_name_consistent; eauto.
Qed.

(* EXPRESSION TYPING RULES *)
Inductive expr_has_type : class_table -> s_env -> expr -> qualified_type -> Prop :=

  (* Null typing *)
  | ET_Null : forall CT Γ q class_name,
      q = Rd -> (* did not define the bottom type of Java base type *)
      wf_senv CT Γ ->
      class_name < dom CT -> (* Add this constraint *)
      expr_has_type CT Γ ENull (Build_qualified_type q class_name)

  (* Variable typing *)
  | ET_Var : forall CT Γ x T,
      wf_senv CT Γ ->
      static_getType Γ x = Some T ->
      expr_has_type CT Γ (EVar x) T
      
  (* Field access typing *)    
  | ET_Field : forall CT Γ x T fDef f,
      wf_senv CT Γ ->
      static_getType Γ x = Some T ->
      sf_def_rel CT (sctype T) f fDef ->
      expr_has_type CT Γ (EField x f) (Build_qualified_type (vpa_mutabilty_stype_fld (sqtype T) ((mutability (ftype fDef)))) (f_base_type (ftype fDef)))
.

Definition qc2q (qi : q_c) : q :=
  match qi with
    | RDM_c => RDM
    | Imm_c => Imm
    | Mut_c => Mut
    end.

Inductive stmt_typing : class_table -> s_env -> stmt -> s_env -> Prop :=
  (* Skip statement *)
  | ST_Skip : forall CT sΓ,
      wf_senv CT sΓ ->
      stmt_typing CT sΓ SSkip sΓ

  (* Local variable declaration *)
  | ST_Local : forall CT sΓ T x sΓ',
      wf_senv CT sΓ ->
      wf_stypeuse CT (sqtype T) (sctype T) ->
      static_getType sΓ x = None ->
      sΓ' = (sΓ ++ [T]) ->
      (* The local variable is added to the static environment *)
      stmt_typing CT sΓ (SLocal T x) sΓ'

  (* Variable assignment *)
  | ST_VarAss : forall CT sΓ x e Te Tx,
      wf_senv CT sΓ ->
      expr_has_type CT sΓ e Te ->
      x <> 0 -> (* x is not the receiver variable *)
      static_getType sΓ x = Some Tx -> (* rename the varaibles to be more clear*)
      qualified_type_subtype CT Te Tx ->
      stmt_typing CT sΓ (SVarAss x e) sΓ

  (* Field write *)
  | ST_FldWrite : forall CT sΓ x f y Tx Ty fieldT a,
      wf_senv CT sΓ ->
      static_getType sΓ x = Some Tx ->
      static_getType sΓ y = Some Ty ->
      sf_def_rel CT (sctype Tx) f fieldT ->
      sf_assignability_rel CT (sctype Tx) f a ->
      (* TODO: define a helper method to get the adapated type *)
      qualified_type_subtype CT Ty (Build_qualified_type (vpa_mutabilty_stype_fld (sqtype Tx) ((mutability (ftype fieldT)))) (f_base_type (ftype fieldT))) ->
      vpa_assignability (sqtype Tx) a = Assignable ->
      stmt_typing CT sΓ (SFldWrite x f y) sΓ

  (* Object creation *)
  | S_New : forall CT sΓ x Tx (qc:q_c) C args argtypes consig consreturn,
      wf_senv CT sΓ ->
      static_getType sΓ x = Some Tx ->
      static_getType_list sΓ args = Some argtypes ->
      constructor_sig_lookup CT C = Some consig ->
      x <> 0 ->
      consig.(cqualifier) = consreturn ->
      qc = consreturn ->
      Forall2 (fun arg T => qualified_type_subtype CT arg (T)) argtypes consig.(cparams) ->
      qualified_type_subtype CT (Build_qualified_type (qc2q qc) C) Tx ->
      stmt_typing CT sΓ (SNew x qc C args) sΓ

  (* Method call *)
  | ST_Call : forall CT sΓ x m y args argtypes Tx Ty mdef,
      wf_senv CT sΓ ->
      static_getType sΓ x = Some Tx ->
      static_getType sΓ y = Some Ty ->
      static_getType_list sΓ args = Some argtypes ->
      FindMethodWithName CT (sctype Ty) m mdef ->
      x <> 0 -> (* x is not the receiver variable *)
      (* TODO: AOSEN REFINE THIS TO ADAPTED TYPE to context sensitivity, i.e. imm/mut can invoke rdm method *)
      qualified_type_subtype CT (mret (msignature mdef)) Tx -> (* assignment subtype checking*)
      qualified_type_subtype CT Ty (mreceiver (msignature mdef)) -> (* receiver subtype checking *) 
      Forall2 (fun arg T => qualified_type_subtype CT arg T) argtypes (mparams (msignature mdef)) -> (* argument subtype checking *)
      stmt_typing CT sΓ (SCall x m y args) sΓ

  (* Cast statement *)
  (* | S_Cast : forall CT Γ x q C y,
      static_lookup Γ y = Some (ctype (Build_qualified_type (q_f_proj q) C)) ->
      wf_stypeuse CT q C ->
      stmt_eval CT Γ (SCast x q C y) Γ *)

  (* Sequence of statements *)
  | ST_Seq : forall CT sΓ s1 sΓ' s2 sΓ'',
      wf_senv CT sΓ ->
      stmt_typing CT sΓ s1 sΓ' ->
      stmt_typing CT sΓ' s2 sΓ'' ->
      stmt_typing CT sΓ (SSeq s1 s2) sΓ''
.

Lemma stmt_typing_wf_env : forall CT sΓ stmt sΓ',
  stmt_typing CT sΓ stmt sΓ' ->
  wf_senv CT sΓ.
Proof.
  intros CT sΓ stmt sΓ' Htyping.
  induction Htyping; auto.
Qed.

Lemma new_stmt_args_length : forall CT sΓ x qc C args argtypes consig,
  stmt_typing CT sΓ (SNew x qc C args) sΓ ->
  static_getType_list sΓ args = Some argtypes ->
  constructor_sig_lookup CT C = Some consig ->
  length consig.(cparams) = length args.
Proof.
  intros CT sΓ x qc C args argtypes consig Htyping Hstatic Hconsig.
  inversion Htyping; subst.
  assert (consig = consig0) by congruence.
  assert (argtypes = argtypes0) by congruence.
  subst.
  apply Forall2_length in H13.
  rewrite <- H13.
  eapply static_getType_list_preserves_length; eauto.
Qed.

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
      {| sqtype := vpa_mutabilty_constructor_fld (cqualifier ctor) (mutability (ftype field_def));
         sctype := f_base_type (ftype field_def) |})
    (cparams ctor) field_defs.

(* Inductive wf_constructor : class_table -> class_name -> constructor_def -> Prop :=
  (* Other case: super class and this class both have fields *)
  | WFConstructorInductive: forall CT C ctor this_fields_def,
    constructor_def_lookup CT C = Some ctor ->
    let sig := csignature ctor in
    let q_c := cqualifier sig in
    (* let ccon := ctor_type sig in *)
    (* constructor mutability qualifier is same as bound; Constructor name is the same as class name *)
    Some q_c = bound CT C -> 
    (* Parameter types are wellformed *)
    Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) (cparams sig) ->
    CollectFields CT C this_fields_def -> (* This class has fields *)
    let body := cbody ctor in
    let list_assignment := assignments body in
    let this_fields := map fname this_fields_def in
    (* Constructor body well-formedness *)
    (* 1. The assignments in this constructor has the same length as fields for this class *)
    length list_assignment = length this_fields_def ->
    (* 2. The first component (field def) in list_assignment is in this_fields - super_fields *)
    Forall (fun '(f, _) => In f this_fields) list_assignment ->
    (* 3. Assignment preserve subtyping *)
    let ctypes := cparams sig in 
    Forall (fun '(f1, f2) =>
    exists mf Cf T2,
      sf_mutability_rel CT C f1 mf /\
      sf_base_rel CT C f1 Cf /\
      nth_error ctypes f2 = Some T2 /\
      qualified_type_subtype CT 
        ((Build_qualified_type (vpa_mutabilty_constructor_fld q_c mf) Cf))  (* AOSEN: May need revisit*)
        (T2)
    ) list_assignment ->
    (* 4 Constructor supercall wellformed *)
    (* 4.1 Bound compatibility *)
    (* 4.2 Argument types are adapted subtype of Parameter type of super constructor *)
    length (cparams sig) = length this_fields_def ->
    wf_constructor CT C ctor
  .*)

Inductive wf_method : class_table -> class_name -> method_def -> Prop :=
  | WFMethod: forall CT C mdef mbodyrettype,
    let msig := msignature mdef in
    let methodbody := mbody mdef in
    let mbodystmt := mbody_stmt methodbody in
    let sΓ := msig.(mreceiver) :: msig.(mparams) in
    (* Basic method body well-formedness *)
    (exists sΓ', 
      stmt_typing CT sΓ mbodystmt sΓ' /\
      let mbodyretvar := mreturn methodbody in
      mbodyretvar < dom sΓ' /\
      nth_error sΓ' mbodyretvar = Some mbodyrettype /\
      qualified_type_subtype CT mbodyrettype (mret msig)) ->
    wf_method CT C mdef.

(* Well-formedness of class *)
Inductive wf_class : class_table -> class_def -> Prop :=
(* Other object *) 
| WFOtherDef: forall CT cdef thisC, 
  (* is_q_c (class_qualifier (signature cdef)) -> *)
  cdef.(signature).(cname) = thisC ->
  let sig := cdef.(signature) in
  let bod := cdef.(body) in
  let C := cname sig in
  let qC := class_qualifier sig in
  (wf_constructor CT C (csignature (constructor bod)) /\
  Forall (wf_method CT C) (methods bod) /\
  NoDup (map (fun mdef => mname (msignature mdef)) (methods bod)) /\
  exists fs, CollectFields CT C fs /\
  Forall (wf_field CT) fs) ->
  wf_class CT cdef
.

(* Enhanced class table well-formedness *)
Definition wf_class_table (CT : class_table) : Prop :=
  Forall (wf_class CT) CT /\
  (* Class name matches index *)
  (forall i def, find_class CT i = Some def <-> 
                 cname (signature def) = i).

Lemma find_class_cname_consistent : forall CT i def,
  wf_class_table CT ->
  find_class CT i = Some def ->
  cname (signature def) = i.
Proof.
  intros CT i def Hwf_ct Hfind.
  unfold wf_class_table in Hwf_ct.
  destruct Hwf_ct as [_ Hcname_consistent].
  apply Hcname_consistent; exact Hfind.
Qed.

Lemma find_class_consistent : forall CT i def def',
  wf_class_table CT ->
  find_class CT i = Some def ->
  find_class CT i = Some def' ->
  def = def'.
Proof.
  intros CT i def def' Hwf_ct Hfind Hfind'.
  rewrite Hfind in Hfind'.
  injection Hfind' as Heq.
  exact Heq.
Qed.

Lemma sf_def_rel_wf_field : forall CT C f fdef,
  wf_class_table CT ->
  sf_def_rel CT C f fdef ->
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
      apply CF_NotFound. exact H.
    }
    subst fields.
    unfold gget in Hget'.
    simpl in Hget'.
    exfalso.
    simpl in Hget'.
    destruct f; discriminate Hget'.
  - (* CF_Object case *)
    intro Hgget.
    assert (Hwf_class : wf_class CT def).
    {
      unfold wf_class_table in Hwf_ct.
      destruct Hwf_ct as [Hwf_all _].
      eapply Forall_nth_error; eauto.
    }
    inversion Hwf_class; subst.
    destruct H2 as [_ [_ [_ Hbound_case]]].
    destruct Hbound_case as [fs [Hcf_fs Hwf_fs]].
    assert (C0 = C) by (unfold C0; eapply find_class_cname_consistent; eauto).
    subst C0.
    inversion Hget; subst.
    assert (fs = fields) by (eapply collect_fields_deterministic_rel; eauto).
    subst fs.
    eapply Forall_nth_error; eauto.
Qed.

(* Lemma vpa_type_to_type_sctype : forall T fieldType,
  sctype (vpa_type_to_type T fieldType) = sctype fieldType.
Proof.
  intros T fieldType.
  unfold vpa_type_to_type.
  destruct T as [q1 c1].
  destruct fieldType as [q2 c2].
  simpl.
  reflexivity.
Qed. *)

Lemma expr_has_type_class_in_table : forall CT sΓ e T,
  wf_class_table CT ->
  expr_has_type CT sΓ e T ->
  sctype T < dom CT.
Proof.
  intros CT sΓ e T HWFCT Htype.
  induction Htype.
  - (* ET_Null case *)
    exact H1.
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
Qed.

(* Well-formedness of program  Aosen: I put it at the end because the main statement need to be well-typed*)
(* Definition WFProgram (p: program_def) : Prop :=
  Forall (fun decl => WFClass p.(classes) decl) p.(classes) . *)

Lemma find_app : forall A (f : A -> bool) l1 l2 x,
  find f l1 = Some x ->
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

Lemma find_app_none : forall A (f : A -> bool) l1 l2,
  find f l1 = None ->
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

Lemma find_filter_equiv : forall A (f g : A -> bool) l,
  (forall x, In x l -> f x = true -> g x = true) ->
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

(* Lemma override_own_method_found : forall parent_methods own_methods m mdef,
  gget_method own_methods m = Some mdef ->
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

Lemma override_parent_method_preserved : forall parent_methods own_methods m,
  gget_method own_methods m = None ->
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

Lemma override_preserves_param_count : forall CT C parent_methods own_methods m mdef mdef',
  wf_class_table CT ->
  CollectMethods CT C (override parent_methods own_methods) ->
  gget_method own_methods m = Some mdef ->
  gget_method (override parent_methods own_methods) m = Some mdef' ->
  dom (mparams (msignature mdef)) = dom (mparams (msignature mdef')).
Proof.
  intros CT C parent_methods own_methods m mdef mdef' Hwf_ct Hcollect Hown Hoverride.
  have Hfound := override_own_method_found parent_methods own_methods m mdef Hown.
  rewrite Hfound in Hoverride.
  injection Hoverride as Heq.
  subst mdef'.
  reflexivity.
Qed. *)

(* Lemma method_lookup_in_local_methods : forall CT C mdef m,
  MethodLookup CT C m mdef ->
  exists def, find_class CT C = Some def /\
    (In mdef (methods (body def)) \/
     exists parent_methods, 
       CollectMethods CT C (override parent_methods (methods (body def))) /\
       In mdef (override parent_methods (methods (body def)))).
Proof.
  intros CT C mdef m Hlookup.
  inversion Hlookup; subst.
  inversion H; subst.
  - (* CM_NotFound *)
    exfalso.
    unfold gget_method in H0.
    discriminate.
  - (* CM_Object *)
    exists def.
    split.
    -- exact H1.
    -- left.
      unfold gget_method in H0.
      eapply find_some in H0.
      destruct H0 as [Hin _].
      exact Hin.
  - (* CM_Inherit *)
    exists def.
    split.
    -- exact H1.
    -- right.
      exists parent_methods.
      split.
      + exact H.
      + unfold gget_method in H0.
        eapply find_some in H0.
        destruct H0 as [Hin _].
        exact Hin.
Qed. *)

Lemma collect_fields_exists : forall CT c,
  wf_class_table CT ->
  c < dom CT ->
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
exists (Syntax.fields (body def)).
apply CF_Body with def.
- exact Hfind.
- reflexivity.

Qed.

Lemma find_overriding_method_deterministic : forall CT C mname mdef1 mdef2,
  wf_class_table CT ->
  FindMethodWithName CT C mname mdef1 ->
  FindMethodWithName CT C mname mdef2 ->
  mdef1 = mdef2.
Proof.
  intros CT C mname mdef1 mdef2 Hwf_ct Hfind1 Hfind2.
  (* Strong induction on C *)
  induction C using lt_wf_ind.
  intros.
  
  inversion Hfind1; subst.
  inversion Hfind2; subst.
  
  (* Establish same class definition *)
  assert (Heq_def : def = def0).
  { 
    rewrite H0 in H1.
    injection H1 as Heq.
    exact Heq.
  }
  subst def0.
  
  (* Case analysis on both calls *)
  - (* Both find locally *)
    rewrite H2 in H4.
    injection H4 as Heq.
    exact Heq.
Qed.

Lemma method_lookup_wf_class: forall CT C mdef cdef,
  wf_class_table CT ->
  C < dom CT ->
  find_class CT C = Some cdef ->
  In mdef (methods (body cdef)) ->
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
  - (* WFOtherDef case *)
    destruct H0 as [_ [Hforall_methods _]].
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

Lemma method_lookup_wf_class_by_find: forall CT C m mdef,
  wf_class_table CT ->
  C < dom CT ->
  FindMethodWithName CT C m mdef ->
  wf_method CT C mdef.
Proof.
  intros CT C m mdef Hwf_ct Hdom HfindMethod.
  inversion HfindMethod; subst.
  assert (Hwf_class : wf_class CT def).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  inversion Hwf_class; subst.
  destruct H2 as [_ [Hforall_methods _]].
  assert (HC0_eq : C0 = C).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [_ Hcname_consistent].
    apply Hcname_consistent.
    exact H.
  }
  rewrite HC0_eq in Hforall_methods.
unfold gget_method in H1.
eapply find_some in H1.
destruct H1 as [Hin _].
apply In_nth_error in Hin.
destruct Hin as [n Hnth].
eapply Forall_nth_error; eauto.

Qed.

(* Lemma wf_method_override_same_param_length : forall CT C mdef cdef parentname supermdef,
  wf_method CT C mdef ->
  find_class CT C = Some cdef ->
  super (signature cdef) = Some parentname ->
  FindOverrideMethod CT C (mname (msignature mdef)) mdef ->
  FindOverrideMethod CT parentname (mname (msignature mdef)) supermdef ->
  dom (mparams (msignature mdef)) = dom (mparams (msignature supermdef)).
Proof.
  intros CT C mdef cdef parentname supermdef Hwf_mdef Hfind_C Hsuper Hfind_C_mdef Hfind_parent_mdef.
  inversion Hwf_mdef; subst.
  specialize (H0 cdef parentname supermdef Hfind_C Hsuper Hfind_C_mdef Hfind_parent_mdef).
  destruct H0 as [Heq | [Hforall2 _]].
  - (* Case: mdef = supermdef *)
    rewrite Heq. reflexivity.
  - (* Case: overriding with parameter constraints *)
    apply Forall2_length in Hforall2.
    symmetry.
    exact Hforall2.
Qed. *)

Lemma method_name_unique_implies_equal : forall methods mdef1 mdef2,
  NoDup (map (fun mdef => mname (msignature mdef)) methods) ->
  In mdef1 methods ->
  In mdef2 methods ->
  mname (msignature mdef1) = mname (msignature mdef2) ->
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

(* Lemma override_local_precedence : forall parent_methods own_methods m mdef,
  gget_method own_methods m = Some mdef ->
  gget_method (override parent_methods own_methods) m = Some mdef.
Proof.
  intros parent_methods own_methods m mdef Hown.
  unfold override.
  unfold gget_method in *.
  apply find_app.
  exact Hown.
Qed. *)
