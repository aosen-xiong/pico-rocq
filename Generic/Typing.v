Require Import Syntax Subtyping ViewpointAdaptation Helpers.

From Stdlib Require String.
From Stdlib Require Import List.
Import ListNotations.

(* ------------------STATIC LOOKUP------------------*)

(** Transport an inherited field declaration to the subclass: the superclass's
    type parameters are replaced by the declared superclass arguments. *)
Definition subst_field (Ss : list qualified_type) (fd : field_def) : field_def :=
  {| assignability := assignability fd;
     ftype := subst Ss [] [] (ftype fd) |}.

(** All fields of a class, inherited fields first, every declared type
    expressed over the class's own type parameters. *)
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
  | CF_Inherit : forall CT C def parent Ss parent_fields own_fields
      (Hfind        : find_class CT C = Some def)
      (Hsuper       : super (signature def) = Some (parent, Ss))
      (Hparent_cf   : CollectFields CT parent parent_fields)
      (Hown_fields  : own_fields = Syntax.fields (body def)),
      CollectFields CT C (map (subst_field Ss) parent_fields ++ own_fields).

(* Field lookup relation *)
Inductive FieldLookup : class_table -> class_name -> var -> field_def -> Prop :=
  | FL_Found : forall CT C fields f fdef
      (Hcf  : CollectFields CT C fields)
      (Hget : gget fields f = Some fdef),
      FieldLookup CT C f fdef.

Definition sf_def_rel (CT: class_table) (C: class_name) (f: var) (fdef: field_def) : Prop :=
  FieldLookup CT C f fdef.

Definition sf_assignability_rel (CT: class_table) (C: class_name) (f: var) (a: a) : Prop :=
  exists fdef, FieldLookup CT C f fdef /\ assignability fdef = a.

Lemma collect_fields_deterministic_rel : forall CT C fields1 fields2
  (Hcf1 : CollectFields CT C fields1)
  (Hcf2 : CollectFields CT C fields2),
  fields1 = fields2.
Proof.
  intros CT C fields1 fields2 H1.
  generalize dependent fields2.
  induction H1; intros fields2 H3; inversion H3; subst; try reflexivity;
    try congruence.
  assert (Hdef_eq : def = def0) by congruence. subst def0.
  rewrite Hsuper in Hsuper0. inversion Hsuper0; subst.
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

Lemma sf_assignability_deterministic_rel : forall CT C f a1 a2
  (H1 : sf_assignability_rel CT C f a1)
  (H2 : sf_assignability_rel CT C f a2),
  a1 = a2.
Proof.
  intros CT C f a1 a2 H1 H2.
  destruct H1 as [fdef1 [Hlookup1 Hassign1]].
  destruct H2 as [fdef2 [Hlookup2 Hassign2]].
  assert (Hfdef_eq: fdef1 = fdef2)
    by (eapply field_lookup_deterministic_rel; eauto).
  subst fdef2. congruence.
Qed.

(* Helper to compare method names *)
Definition eq_method_name (m1 m2 : method_name) : bool := Nat.eqb m1 m2.

Definition gget_method (methods : list method_def) (m : method_name) : option method_def :=
  find (fun mdef => eq_method_name (mname (msignature mdef)) m) methods.

(** Method lookup.  Besides the selected declaration it reports the class that
    declares it, because the declaration's types are written over that class's
    type parameters. *)
Inductive FindMethodWithName
    : class_table -> class_name -> method_name -> class_name -> method_def -> Prop :=
  (* Case 1: method is defined directly in class *)
  | FOM_Here : forall CT C def own_methods m mdef
      (Hfind       : find_class CT C = Some def)
      (Hown        : own_methods = methods (body def))
      (Hget_method : gget_method own_methods m = Some mdef),
      FindMethodWithName CT C m C mdef

  (* Case 2: method not in class, look in superclass *)
  | FOM_Super : forall CT C def parent Ss m D mdef own_methods
      (Hfind       : find_class CT C = Some def)
      (Hown        : own_methods = methods (body def))
      (Hnot_here   : gget_method own_methods m = None)
      (Hsuper      : super (signature def) = Some (parent, Ss))
      (Hparent_fmn : FindMethodWithName CT parent m D mdef),
      FindMethodWithName CT C m D mdef.

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

Lemma find_method_with_name_consistent : forall CT C m D mdef
  (Hfmn : FindMethodWithName CT C m D mdef),
  mname (msignature mdef) = m.
Proof.
  intros CT C m D mdef H.
  induction H.
  - eapply gget_method_name_consistent; eauto.
  - exact IHFindMethodWithName.
Qed.

Lemma find_method_with_name_deterministic : forall CT C m D1 mdef1 D2 mdef2
  (H1 : FindMethodWithName CT C m D1 mdef1)
  (H2 : FindMethodWithName CT C m D2 mdef2),
  D1 = D2 /\ mdef1 = mdef2.
Proof.
  intros CT C m D1 mdef1 D2 mdef2 H1.
  generalize dependent mdef2. generalize dependent D2.
  induction H1; intros D2 mdef2 H2.
  - inversion H2; subst.
    + rewrite Hfind0 in Hfind; injection Hfind as Hdef_eq; subst def0.
      rewrite Hget_method0 in Hget_method; injection Hget_method as ?; subst.
      split; reflexivity.
    + rewrite Hfind0 in Hfind; injection Hfind as Hdef_eq; subst def0.
      rewrite Hget_method in Hnot_here; discriminate.
  - inversion H2; subst.
    + rewrite Hfind0 in Hfind; injection Hfind as Hdef_eq; subst def0.
      rewrite Hget_method in Hnot_here; discriminate.
    + rewrite Hfind0 in Hfind; injection Hfind as Hdef_eq; subst def0.
      rewrite Hsuper0 in Hsuper; injection Hsuper as ? ?; subst.
      apply IHFindMethodWithName; auto.
Qed.

Lemma find_method_with_name_base : forall CT C m D mdef
  (Hfmn : FindMethodWithName CT C m D mdef),
  base_subtype CT C D.
Proof.
  intros CT C m D mdef H. induction H.
  - apply base_refl. eapply find_class_dom; eauto.
  - eapply base_trans; [|exact IHFindMethodWithName].
    destruct (base_subtype_domain _ _ _ IHFindMethodWithName) as [Hp _].
    eapply base_extends; eauto using find_class_dom.
    unfold parent_lookup. rewrite Hfind. exact Hsuper.
Qed.

(* ------------------STATIC WELL-FORMEDNESS------------------*)

(** Well-formed type use.  The flag says whether the type stands at the top of
    a declaration ([true]) or in an argument position ([false]).  In an
    argument position [Lost] may always be written; at the top it may be
    written on a class declared receiver-dependent, like any other qualifier,
    since the qualifier order is reflexive at [Lost].  A type argument is checked against its
    declared bound, adapted through the head qualifier. *)
(** When a use of a type variable may be written.  A use under a qualifier
    parameter needs that parameter in scope; any other use may be [Lost] only
    inside a type argument. *)
Definition tv_use_ok (Δ : tv_env) (top : bool) (u : tv_use) : Prop :=
  match u with
  | TVPoly m => m < qparams Δ
  | _ => top = false \/ u <> TVQual Lost
  end.

(** A use that is plain or carries a written qualifier, not a qualifier
    parameter. *)
Definition tv_concrete (u : tv_use) : Prop :=
  match u with
  | TVPoly _ => False
  | _ => True
  end.

Inductive wf_stype (CT : class_table) (Δ : tv_env) : bool -> qualified_type -> Prop :=
  | wfs_class : forall top q0 C Ts def
      (Hfind   : find_class CT C = Some def)
      (Hhead   : (top = false /\ q0 = Lost) \/
                 q_subtype
                   (vpa_mutability_bound q0 (class_qualifier (signature def))) q0)
      (Hlen    : length Ts = length (ctparams (signature def)))
      (Hargs   : Forall (wf_stype CT Δ false) Ts)
      (Hbounds : Forall2
                   (fun T B =>
                      bound_sub CT Δ T
                        (subst Ts [] [] (adapt AbstractState q0 B)))
                   Ts (ctparams (signature def))),
      wf_stype CT Δ top (TClass q0 C Ts)
  | wfs_var : forall top u o n B
      (Hbound : tv_bound Δ o n = Some B)
      (Huse   : tv_use_ok Δ top u),
      wf_stype CT Δ top (TVar u o n)
  (* A class type under a qualifier parameter of the enclosing method is
     checked through its readonly view, the view valid for every qualifier
     the parameter may stand for. *)
  | wfs_head : forall top n C Ts
      (Hbound : n < qparams Δ)
      (Hview  : wf_stype CT Δ top (TClass RO C Ts)),
      wf_stype CT Δ top (THead n C Ts).

Definition wf_stypeuse (CT : class_table) (Δ : tv_env) (T : qualified_type) : Prop :=
  wf_stype CT Δ true T.

(* Well-formedness of static environment *)
Definition wf_senv (CT : class_table) (Δ : tv_env) (sΓ : s_env) : Prop :=
  (* The first variable is the receiver and should always be present *)
  dom sΓ > 0 /\
  Forall (wf_stypeuse CT Δ) sΓ.

(** The class type through which members of a type are looked up: a class type
    is its own view; a bare type variable is viewed at its declared bound.  A
    qualified use of a type variable is viewed at its declared bound's class
    with the written qualifier when that bound has no type arguments. *)
Definition ubound (Δ : tv_env) (T : qualified_type) : option qualified_type :=
  match T with
  | TClass _ _ _ => Some T
  | TVar TVSub o n =>
      match tv_bound Δ o n with
      | Some (TClass qb C Ts) => Some (TClass qb C Ts)
      | _ => None
      end
  | TVar (TVQual q0) o n =>
      match tv_bound Δ o n with
      | Some (TClass qb C []) => Some (TClass q0 C [])
      | _ => None
      end
  | TVar (TVPoly m) o n =>
      match tv_bound Δ o n with
      | Some (TClass qb C []) =>
          if Nat.ltb m (qparams Δ) then Some (TClass RO C []) else None
      | _ => None
      end
  | THead n C Ts =>
      if Nat.ltb n (qparams Δ) then Some (TClass RO C Ts) else None
  end.

(** A declared member type as seen through a receiver: adapt the written
    qualifiers through the receiver's qualifier, then substitute the
    receiver's class arguments [Vs] and the method arguments [Us]. *)
Definition member_type (mt : method_scope) (qrecv : q)
    (Vs Us : list qualified_type) (Qs : list qarg) (T : qualified_type)
    : qualified_type :=
  subst Vs Us Qs (adapt mt qrecv T).

(** The declared receiver of a method as a client with receiver qualifier
    [qrecv] must supply it: receiver adaptation, then substitution. *)
Definition member_recv (qrecv : q)
    (Vs Us : list qualified_type) (Qs : list qarg) (T : qualified_type)
    : qualified_type :=
  subst Vs Us Qs (map_qual (vpa_recv qrecv) T).

(** A reference of static type [A] may be the receiver of a call whose
    adapted declared receiver is [R]: [A] is a subtype of [R].  The qualifier
    of [R] may be [Lost]: a receiver declared [RDM] takes the caller's
    qualifier unchanged, and through a [Lost] reference the callee sees a
    receiver of either mutability, as through a readonly one.  The type
    arguments of [R] are the reference's own, viewed at the declaring class;
    they are not required to be known. *)
Definition receiver_ok (CT : class_table) (Δ : tv_env)
    (A R : qualified_type) : Prop :=
  qualified_type_subtype CT Δ A R.

(** The type arguments of a class type. *)
Definition targs (T : qualified_type) : list qualified_type :=
  match T with
  | TClass _ _ args => args
  | THead _ _ args => args
  | TVar _ _ _ => []
  end.

(** A declared receiver may requalify a type parameter of its class.  At a
    call, such a written qualifier, seen through the caller's view of the
    receiver in the caller's mode, must be known. *)
Definition recv_args_known (mt : method_scope) (qrecv : q)
    (R : qualified_type) : Prop :=
  forall u o n, List.In (TVar (TVQual u) o n) (targs R) ->
    vpa_q mt qrecv u <> Lost.

(** A value of static type [A] may be stored where [F] is expected: [F] has
    no unknown position, and [A] is a subtype of it. *)
Definition assignable_to (CT : class_table) (Δ : tv_env)
    (A F : qualified_type) : Prop :=
  qualified_type_subtype CT Δ A F /\ lost_free F.

(* ------------------EXPRESSION TYPING------------------*)
Inductive expr_has_type
    : class_table -> tv_env -> s_env -> method_scope -> expr -> qualified_type -> Prop :=

  (* Null typing *)
  | ET_Null : forall CT Δ Γ mt T
      (Hwf  : wf_senv CT Δ Γ),
      expr_has_type CT Δ Γ mt ENull T

  (* Variable typing *)
  | ET_Var : forall CT Δ Γ mt x T
      (Hwf  : wf_senv CT Δ Γ)
      (Hget : static_getType Γ x = Some T),
      expr_has_type CT Δ Γ mt (EVar x) T

  (* Field access typing: adapt the declared type through the receiver in the
     current mode, then substitute the receiver's type arguments *)
  | ET_Field : forall CT Δ Γ mt x T qx C Ts fDef f
      (Hwf      : wf_senv CT Δ Γ)
      (Hget_x   : static_getType Γ x = Some T)
      (Hub      : ubound Δ T = Some (TClass qx C Ts))
      (Hfld_def : sf_def_rel CT C f fDef),
      expr_has_type CT Δ Γ mt (EField x f)
        (member_type mt qx Ts [] [] (ftype fDef)).

(* ------------------CASTS------------------*)

(** A narrowing cast moves a readonly view of a class down to the mutability
    that the class declaration pins for every one of its objects.  The class
    and the type arguments are unchanged. *)
Definition cast_narrowing_ok (CT : class_table) (S T : qualified_type) : Prop :=
  match S, T with
  | TClass qs Cs args_s, TClass qt Ct args_t =>
      Cs = Ct /\ args_s = args_t /\
      (qt = Mut \/ qt = Imm) /\
      q_subtype qt qs /\ qs <> qt /\
      exists def, find_class CT Ct = Some def /\
                  qc2q (class_qualifier (signature def)) = qt
  | _, _ => False
  end.

Definition cast_source_ok (CT : class_table) (Δ : tv_env) (S T : qualified_type) : Prop :=
  qualified_type_subtype CT Δ S T \/ cast_narrowing_ok CT S T.

(** The readonly-state and transitive-state modes promise that mutable access
    never grows, so they allow no narrowing cast. *)
Definition cast_target_ok_in_scope (CT : class_table) (mt : method_scope)
    (S T : qualified_type) : Prop :=
  match mt with
  | AbstractState | ConcreteState => True
  | ReadonlyState | TransitiveState => ~ cast_narrowing_ok CT S T
  end.

(** A qualifier argument of a call: a written qualifier other than [Lost],
    or one of the calling method's own qualifier parameters. *)
Definition qarg_ok (Δ : tv_env) (a : qarg) : Prop :=
  match a with
  | QLit q0 => q0 <> Lost
  | QVar m => m < qparams Δ
  end.

(* ------------------STATEMENT TYPING------------------*)

Definition get_this_qualified_type (sΓ : s_env) : option qualified_type :=
  match sΓ with
  | [] => None
  | T_this :: _ => Some T_this
  end.

Inductive stmt_typing
    : class_table -> tv_env -> s_env -> method_scope -> stmt -> s_env -> Prop :=
  (* Skip statement *)
  | ST_Skip : forall CT Δ sΓ mt
      (Hwf : wf_senv CT Δ sΓ),
      stmt_typing CT Δ sΓ mt SSkip sΓ

  (* Local variable declaration *)
  | ST_Local : forall CT Δ sΓ mt T x sΓ'
      (Hwf       : wf_senv CT Δ sΓ)
      (Hwf_T     : wf_stypeuse CT Δ T)
      (Hnone     : static_getType sΓ x = None)
      (Henv'     : sΓ' = sΓ ++ [T])
      (Hget_x    : static_getType sΓ' x = Some T),
      stmt_typing CT Δ sΓ mt (SLocal T x) sΓ'

  (* Variable assignment *)
  | ST_VarAss : forall CT Δ sΓ mt x e Te Tx
      (Hwf      : wf_senv CT Δ sΓ)
      (Htype_e  : expr_has_type CT Δ sΓ mt e Te)
      (Hnot_rcv : x <> 0)
      (Hget_x   : static_getType sΓ x = Some Tx)
      (Hsub     : qualified_type_subtype CT Δ Te Tx),
      stmt_typing CT Δ sΓ mt (SVarAss x e) sΓ

  (* Field write: the mode selects both the mutability adaptation of the
     declared field type and the assignability adaptation of the slot *)
  | ST_FldWrite : forall CT Δ sΓ mt x f y Tx Ty qx C Ts fieldT
      (Hwf         : wf_senv CT Δ sΓ)
      (Hget_x      : static_getType sΓ x = Some Tx)
      (Hget_y      : static_getType sΓ y = Some Ty)
      (Hub         : ubound Δ Tx = Some (TClass qx C Ts))
      (Hfld_def    : sf_def_rel CT C f fieldT)
      (Hsub        : assignable_to CT Δ Ty
                       (member_type mt qx Ts [] [] (ftype fieldT)))
      (Hassignable : vpa_a mt qx (assignability fieldT) = Assignable),
      stmt_typing CT Δ sΓ mt (SFldWrite x f y) sΓ

  (* Object creation: the initializers are checked pointwise against the
     class's fields, seen through the allocation qualifier and arguments in
     the mode of the allocating code *)
  | ST_New : forall CT Δ sΓ mt x Tx (qc:q_c) C Ts args argtypes def fds
      (Hwf         : wf_senv CT Δ sΓ)
      (Hget_x      : static_getType sΓ x = Some Tx)
      (Hget_args   : static_getType_list sΓ args = Some argtypes)
      (Hfind       : find_class CT C = Some def)
      (Hnot_rcv    : x <> 0)
      (Hqc         : vpa_mutability_bound (qc2q qc)
                       (class_qualifier (signature def)) = qc2q qc)
      (Hwf_new     : wf_stypeuse CT Δ (TClass (qc2q qc) C Ts))
      (Hlost_free  : Forall lost_free Ts)
      (Hbounds     : Forall2
                       (fun T B =>
                          lost_free (member_type AbstractState (qc2q qc) Ts [] [] B) /\
                          bound_sub CT Δ T
                            (member_type AbstractState (qc2q qc) Ts [] [] B))
                       Ts (ctparams (signature def)))
      (Hfields     : CollectFields CT C fds)
      (Harg_sub    : Forall2
                       (fun A fd =>
                          assignable_to CT Δ A
                            (member_type mt (qc2q qc) Ts [] [] (ftype fd)))
                       argtypes fds)
      (Hresult_sub : qualified_type_subtype CT Δ (TClass (qc2q qc) C Ts) Tx),
      stmt_typing CT Δ sΓ mt (SNew x qc C Ts args) sΓ

  (* Method call.  The callee's mode must be at least as strong as the
     caller's, and the caller's mode selects the mutability adaptation. *)
  | ST_Call : forall CT Δ sΓ mt x m y Us Qs args argtypes Tx Ty qy C Ts D Vs mdef
      (Hwf         : wf_senv CT Δ sΓ)
      (Hget_x      : static_getType sΓ x = Some Tx)
      (Hget_y      : static_getType sΓ y = Some Ty)
      (Hget_args   : static_getType_list sΓ args = Some argtypes)
      (Hub         : ubound Δ Ty = Some (TClass qy C Ts))
      (Hfind_m     : FindMethodWithName CT C m D mdef)
      (Hsuper      : super_inst CT mt qy C Ts D Vs)
      (Hnot_rcv    : x <> 0)
      (Htargs_wf   : Forall (wf_stypeuse CT Δ) Us)
      (Htargs_lf   : Forall lost_free Us)
      (Htargs_len  : length Us = length (mtparams (msignature mdef)))
      (Htargs_bnd  : Forall2
                       (fun U B =>
                          lost_free (member_type mt qy Vs Us Qs B) /\
                          bound_sub CT Δ U (member_type mt qy Vs Us Qs B))
                       Us (mtparams (msignature mdef)))
      (Hret_sub    : qualified_type_subtype CT Δ
                       (member_type mt qy Vs Us Qs (mret (msignature mdef))) Tx)
      (Hrcv_sub    : receiver_ok CT Δ Ty
                       (member_recv qy Vs Us Qs (mreceiver (msignature mdef))))
      (Harg_sub    : Forall2
                       (fun A P => assignable_to CT Δ A (member_type mt qy Vs Us Qs P))
                       argtypes (mparams (msignature mdef)))
      (Hscope      : method_scope_subtype (mscope (msignature mdef)) mt)
      (Hqargs_len  : length Qs = mqparams (msignature mdef))
      (Hqargs_ok   : Forall (qarg_ok Δ) Qs)
      (Hrcv_args   : recv_args_known mt qy (mreceiver (msignature mdef))),
      stmt_typing CT Δ sΓ mt (SCall x m y Us Qs args) sΓ

  (* Cast.  The value is copied unchanged; the checker admits only casts that
     cannot fail. *)
  | ST_Cast : forall CT Δ sΓ mt x T y Tx Ty
      (Hwf      : wf_senv CT Δ sΓ)
      (Hget_x   : static_getType sΓ x = Some Tx)
      (Hget_y   : static_getType sΓ y = Some Ty)
      (Hnot_rcv : x <> 0)
      (Hwf_T    : wf_stypeuse CT Δ T)
      (Hsource  : cast_source_ok CT Δ Ty T)
      (Hsub     : qualified_type_subtype CT Δ T Tx)
      (Hscope   : cast_target_ok_in_scope CT mt Ty T),
      stmt_typing CT Δ sΓ mt (SCast x T y) sΓ

  (* Sequence of statements *)
  | ST_Seq : forall CT Δ sΓ mt s1 sΓ' s2 sΓ''
      (Hwf    : wf_senv CT Δ sΓ)
      (Htype1 : stmt_typing CT Δ sΓ mt s1 sΓ')
      (Htype2 : stmt_typing CT Δ sΓ' mt s2 sΓ''),
      stmt_typing CT Δ sΓ mt (SSeq s1 s2) sΓ''
.

Lemma stmt_typing_wf_env : forall CT Δ sΓ mt stmt sΓ'
  (Htyping : stmt_typing CT Δ sΓ mt stmt sΓ'),
  wf_senv CT Δ sΓ.
Proof.
  intros CT Δ sΓ mt stmt sΓ' Htyping.
  induction Htyping; auto.
Qed.

(* ------------------DECLARATION WELL-FORMEDNESS------------------*)

(** Class bound look up as a full qualifier. *)
Definition class_tparams (CT : class_table) (C : class_name) : list qualified_type :=
  match find_class CT C with
  | Some def => ctparams (signature def)
  | None => []
  end.

(** The bound environment in which a method body is checked. *)
Definition method_tv_env (CT : class_table) (C : class_name) (msig : method_sig) : tv_env :=
  mk_tv_env (class_tparams CT C) (mtparams msig) (mscope msig) (mqparams msig).

(** The declared receiver of a method of class [C]: [C] applied to its own
    type parameters, each written plainly or under a qualifier, the whole
    under a written qualifier or under one of the method's qualifier
    parameters. *)
Definition recv_args (n : nat) (args : list qualified_type) : Prop :=
  length args = n /\
  forall i T, nth_error args i = Some T -> exists u, T = TVar u ClassVar i.

Definition receiver_shape (CT : class_table) (C : class_name) (T : qualified_type) : Prop :=
  exists args, recv_args (length (class_tparams CT C)) args /\
    ((exists qr, T = TClass qr C args) \/ (exists n, T = THead n C args)).

(** The receiver names every type parameter plainly. *)
Definition receiver_plain (CT : class_table) (C : class_name) (T : qualified_type) : Prop :=
  (exists qr, T = TClass qr C (class_var_types (length (class_tparams CT C)))) \/
  (exists n, T = THead n C (class_var_types (length (class_tparams CT C)))).

Lemma recv_args_plain : forall n, recv_args n (class_var_types n).
Proof.
  intros n. unfold class_var_types. split; [rewrite length_map; rewrite length_seq; reflexivity|].
  intros i T H. rewrite nth_error_map in H.
  destruct (nth_error (seq 0 n) i) as [j|] eqn:Hj; [|discriminate].
  assert (Hlt : i < length (seq 0 n)) by (apply nth_error_Some; congruence).
  rewrite length_seq in Hlt.
  apply (nth_error_nth _ _ 0) in Hj. assert (Hs : nth i (seq 0 n) 0 = 0 + i) by (apply seq_nth; exact Hlt). rewrite Hs in Hj.
  simpl in Hj. subst j. simpl in H. inversion H. exists TVSub. reflexivity.
Qed.

Lemma receiver_plain_shape : forall CT C T,
  receiver_plain CT C T -> receiver_shape CT C T.
Proof.
  intros CT C T H. exists (class_var_types (length (class_tparams CT C))).
  split; [apply recv_args_plain | exact H].
Qed.

(** What a method well-formedness proof for a plainly written receiver needs. *)
Lemma receiver_plain_ok : forall CT C T (P Q : Prop),
  receiver_plain CT C T ->
  receiver_shape CT C T /\ (P -> receiver_plain CT C T \/ Q).
Proof. intros. split; [apply receiver_plain_shape; assumption | auto]. Qed.

Lemma plain_targs : forall CT C T,
  receiver_plain CT C T -> targs T = class_var_types (length (class_tparams CT C)).
Proof. intros CT C T [[q0 ->] | [n ->]]; reflexivity. Qed.

(** An object of mutability [qr] whose type arguments, at the receiver's
    class, are [ca] satisfies what the declared receiver [R] asks of them in
    a call whose qualifier arguments are [ka]. *)
Definition radmit (qr : q) (ca : list rtype) (ka : list q)
    (R : qualified_type) : Prop :=
  forall ma, Forall2 rarg_sub ca (map (dyn qr ca ma ka) (targs R)).

Lemma recv_args_known_plain : forall CT C T mt qrecv,
  receiver_plain CT C T -> recv_args_known mt qrecv T.
Proof.
  intros CT C T mt qrecv H u o n Hin. rewrite (plain_targs _ _ _ H) in Hin.
  unfold class_var_types in Hin. apply in_map_iff in Hin.
  destruct Hin as (i & E & _). discriminate.
Qed.

(** Closes the receiver-argument premise of a call on a concrete signature. *)
Ltac recv_known :=
  let H := fresh in
  intros ? ? ? H; cbn in H; intuition discriminate.

(** Closes the receiver-admission part of an override check when the
    overriding receiver names its class's parameters plainly. *)
Ltac radmit_plain :=
  let H := fresh "H" in let ca := fresh "ca" in
  intros ? ca ? _ _ H _ _ ?; cbn in H;
  repeat (destruct ca as [|? ca]; cbn in H; try discriminate H);
  cbn; repeat (constructor; [apply rarg_sub_refl|]); constructor.

(** A type moved to the class and the arguments of another type, keeping its
    qualifier. *)
Definition rehead (T : qualified_type) (C : class_name)
    (args : list qualified_type) : qualified_type :=
  match T with
  | TClass q0 _ _ => TClass q0 C args
  | THead n _ _ => THead n C args
  | TVar _ _ _ => T
  end.

Definition rebase (T R : qualified_type) : qualified_type :=
  match R with
  | TClass _ C args => rehead T C args
  | THead _ C args => rehead T C args
  | TVar _ _ _ => T
  end.

(** Viewpoint-adapted behavioral subtyping for one override.  [Vs] expresses
    the overridden method's declaring class over the overriding class's type
    parameters.  Scope, the method type-parameter bounds and the number of
    qualifier parameters are invariant; the return is covariant; the ordinary
    parameters are contravariant.  The receiver is contravariant in its
    qualifier only: the overridden receiver, seen from the overriding class
    and moved onto the overriding receiver's class and arguments, is a
    subtype of the overriding method's receiver.  A receiver under a
    qualifier parameter may so be kept under the same parameter or declared
    readonly. *)
Definition method_override_compatible
    (CT : class_table) (Δ : tv_env) (qc : q_c) (Vs : list qualified_type)
    (overrider overridden : method_sig) : Prop :=
  let ms := method_var_types (length (mtparams overridden)) in
  let ks := qvar_args (mqparams overridden) in
  let view := member_type AbstractState (qc2q qc) Vs ms ks in
  mname overrider = mname overridden /\
  mscope overrider = mscope overridden /\
  (mtparams overrider = map view (mtparams overridden) /\
   mqparams overrider = mqparams overridden) /\
  qualified_type_subtype CT Δ (mret overrider) (view (mret overridden)) /\
  Forall2
    (fun overridden_param overrider_param =>
      qualified_type_subtype CT Δ (view overridden_param) overrider_param)
    (mparams overridden) (mparams overrider) /\
  (qualified_type_subtype CT Δ
     (rebase (view (mreceiver overridden)) (mreceiver overrider))
     (mreceiver overrider) /\
   forall (qr : q_r) (ca : list rtype) (ka : list q),
     (qc = Mut_c -> qr = Mut_r) -> (qc = Imm_c -> qr = Imm_r) ->
     length ca = length (class_bounds Δ) ->
     length ka = mqparams overridden ->
     radmit (qr2q qr) (map (dyn (qr2q qr) ca [] []) Vs) ka (mreceiver overridden) ->
     radmit (qr2q qr) ca ka (mreceiver overrider)).

(** No mutable position, reading type variables through their bounds.  This is
    the paper's predicate on a readonly-state or transitive-state signature.
    It is read as "no mutable position is ever reached", so a bound may mention
    its own variable, as in [E extends Comparable<E>]: the walk through the
    bounds need not end. *)
CoInductive no_mut (Δ : tv_env) : qualified_type -> Prop :=
  | nm_class : forall q0 C Ts
      (Hq : q0 <> Mut)
      (Hargs : Forall (no_mut Δ) Ts),
      no_mut Δ (TClass q0 C Ts)
  | nm_var : forall o n B
      (Hbound : tv_bound Δ o n = Some B)
      (Hrec : no_mut Δ B),
      no_mut Δ (TVar TVSub o n)
  | nm_qvar : forall q0 o n qb C Ts
      (Hq : q0 <> Mut)
      (Hbound : tv_bound Δ o n = Some (TClass qb C Ts))
      (Hargs : Forall (no_mut Δ) Ts),
      no_mut Δ (TVar (TVQual q0) o n)
  | nm_pvar : forall m o n qb C Ts
      (Hbound : tv_bound Δ o n = Some (TClass qb C Ts))
      (Hargs : Forall (no_mut Δ) Ts),
      no_mut Δ (TVar (TVPoly m) o n)
  | nm_head : forall n C Ts
      (Hargs : Forall (no_mut Δ) Ts),
      no_mut Δ (THead n C Ts).

Definition signature_has_no_mutable_roots (Δ : tv_env) (msig : method_sig) : Prop :=
  no_mut Δ (mreceiver msig) /\ Forall (no_mut Δ) (mparams msig).

(** A type-parameter bound is a non-variable class type. *)
Definition is_class_type (T : qualified_type) : Prop :=
  match T with
  | TClass _ _ _ => True
  | TVar _ _ _ => False
  | THead _ _ _ => False
  end.

(** The receiver of a readonly-state or transitive-state method may requalify
    a type parameter of its class, but not as mutable, and then the bounds of
    the class's type parameters reach no mutable position.  (With a plainly written receiver the same follows from the
    rule on the receiver type.) *)
Definition recv_protected (Δ : tv_env) (R : qualified_type) : Prop :=
  Forall (no_mut Δ) (class_bounds Δ) /\
  forall u o n, List.In (TVar (TVQual u) o n) (targs R) -> u <> Mut.

Definition wf_method (CT : class_table) (C : class_name) (mdef : method_def) : Prop :=
  let msig := msignature mdef in
  let methodbody := mbody mdef in
  let Δ := method_tv_env CT C msig in
  let sΓ := mreceiver msig :: mparams msig in
  (receiver_shape CT C (mreceiver msig) /\
   (readonly_state_method_scope (mscope msig) ->
    receiver_plain CT C (mreceiver msig) \/ recv_protected Δ (mreceiver msig))) /\
  Forall (fun B => is_class_type B /\ wf_stypeuse CT Δ B /\
                   (readonly_state_method_scope (mscope msig) -> no_mut Δ B))
    (mtparams msig) /\
  wf_stypeuse CT Δ (mret msig) /\
  (exists sΓ' mbodyrettype,
    stmt_typing CT Δ sΓ (mscope msig) (mbody_stmt methodbody) sΓ' /\
    nth_error sΓ' (mreturn methodbody) = Some mbodyrettype /\
    qualified_type_subtype CT Δ mbodyrettype (mret msig)) /\
  (forall def parent Ss D mdef_parent Vs,
      find_class CT C = Some def ->
      super (signature def) = Some (parent, Ss) ->
      FindMethodWithName CT parent (mname msig) D mdef_parent ->
      super_inst CT AbstractState (qc2q (class_qualifier (signature def))) C
        (class_var_types (length (ctparams (signature def)))) D Vs ->
      method_override_compatible CT Δ (class_qualifier (signature def)) Vs
        msig (msignature mdef_parent)) /\
  (readonly_state_method_scope (mscope msig) ->
      signature_has_no_mutable_roots Δ msig).

Definition wf_field (CT : class_table) (Δ : tv_env) (fdef : field_def) : Prop :=
  wf_stypeuse CT Δ (ftype fdef).

(* Well-formedness of class *)
Inductive wf_class : class_table -> class_def -> Prop :=

(* Object class *)
| WFObjectDef : forall CT cdef
    (Hno_super    : cdef.(signature).(super) = None)
    (Hrdm         : cdef.(signature).(class_qualifier) = RDM_c)
    (Hno_tparams  : cdef.(signature).(ctparams) = [])
    (Hno_fields   : cdef.(body).(Syntax.fields) = [])
    (Hno_methods  : cdef.(body).(methods) = []),
    wf_class CT cdef

(* Other class *)
| WFOtherDef : forall CT cdef superC Ss super_def
    (Hsuper     : cdef.(signature).(super) = Some (superC, Ss))
    (Hordering  : cdef.(signature).(cname) > superC)
    (Hsuper_def : find_class CT superC = Some super_def),
    let sig := cdef.(signature) in
    let bod := cdef.(body) in
    let C := cname sig in
    let qC := class_qualifier sig in
    let Δ := mk_tv_env (ctparams sig) [] AbstractState 0 in
    (* type-parameter bounds are well-formed class types *)
    Forall (fun B => is_class_type B /\ wf_stypeuse CT Δ B) (ctparams sig) ->
    (* the superclass type is well formed and its arguments are fully known
       and satisfy the superclass's bounds *)
    wf_stypeuse CT Δ (TClass (qc2q qC) superC Ss) ->
    Forall lost_free Ss ->
    Forall2
      (fun T B =>
         lost_free (member_type AbstractState (qc2q qC) Ss [] [] B) /\
         bound_sub CT Δ T (member_type AbstractState (qc2q qC) Ss [] [] B))
      Ss (ctparams (signature super_def)) ->
    (* a subclass keeps a pinned superclass mutability *)
    (qC = class_qualifier (signature super_def) \/
     class_qualifier (signature super_def) = RDM_c) ->
    Forall (wf_field CT Δ) (Syntax.fields bod) ->
    Forall (wf_method CT C) (methods bod) ->
    NoDup (map (fun mdef => mname (msignature mdef)) (methods bod)) ->
    wf_class CT cdef
.

(* Class table well-formedness *)
Definition wf_class_table (CT : class_table) : Prop :=
  let object_class_at_zero :=
    exists obj_def, find_class CT 0 = Some obj_def /\
                    super (signature obj_def) = None in
  let non_object_classes_extend_object :=
    forall i def, i > 0 -> find_class CT i = Some def ->
                  super (signature def) <> None in
  let class_name_matches_index :=
    forall i def, find_class CT i = Some def ->
                  cname (signature def) = i in
  Forall (wf_class CT) CT /\
  object_class_at_zero /\
  non_object_classes_extend_object /\
  class_name_matches_index.
