From Stdlib Require Import List.
Import ListNotations.
Require Import Syntax.

(* ------------------QUALIFIER ADAPTATION------------------*)

(* AS/CS mutability viewpoint adaptation *)
Definition vpa_mutability_qq_abstract_state (q1: q)(q2 : q) : q :=
  match q1, q2 with
    | RO, RDM => Lost
    | q1, RDM => q1
    | _, q2 => q2
  end.

(* RS/TS mutability viewpoint adaptation *)
Definition vpa_mutability_qq_readonly_state (q1: q)(q2 : q) : q :=
  match q1, q2 with
    | RO, RDM => Lost
    | q1, RDM => q1
    | Mut, Mut => Mut
    | _, Mut => Lost
    | _, q2 => q2
  end.

(** Mutability adaptation selected by the protection mode of the enclosing
    method: AS and CS share one table, RS and TS share the other. *)
Definition vpa_q (mt : method_scope) (q1 q2 : q) : q :=
  match mt with
  | AbstractState | ConcreteState => vpa_mutability_qq_abstract_state q1 q2
  | ReadonlyState | TransitiveState => vpa_mutability_qq_readonly_state q1 q2
  end.

(* Viewpoint adaptation of assignability qualifiers *)
Definition vpa_assignability (q1: q) (a1: a) : a :=
  match q1, a1 with
    | Mut, RDA => Assignable
    | _, Assignable => Assignable
    | _, _ => Final
  end.

(* CS/TS assignability viewpoint adaptation *)
Definition vpa_assignability_cs_ts (q1: q) (a1: a) : a :=
  match q1, a1 with
    | Mut, RDA => Assignable
    | Mut, Assignable => Assignable
    | _, _ => Final
  end.

(** Assignability adaptation selected by the protection mode: AS and RS are
    permissive, CS and TS are strict. *)
Definition vpa_a (mt : method_scope) (q1 : q) (a1 : a) : a :=
  match mt with
  | AbstractState | ReadonlyState => vpa_assignability q1 a1
  | ConcreteState | TransitiveState => vpa_assignability_cs_ts q1 a1
  end.

Lemma concrete_assignable_implies_assignable : forall q1 a1,
  vpa_assignability_cs_ts q1 a1 = Assignable ->
  vpa_assignability q1 a1 = Assignable.
Proof.
  intros q1 a1 H.
  destruct q1, a1; simpl in *; try discriminate; reflexivity.
Qed.

Lemma vpa_a_assignable_implies_assignable : forall mt q1 a1,
  vpa_a mt q1 a1 = Assignable ->
  vpa_assignability q1 a1 = Assignable.
Proof.
  intros mt q1 a1 H.
  destruct mt; simpl in H; auto using concrete_assignable_implies_assignable.
Qed.

(* Check whether a type use respects its class bound *)
Definition vpa_mutability_bound (q1: q)(q2 : q_c) : q :=
  match q1, q2 with
    | RO, RDM_c => Lost
    | q1, RDM_c => q1
    | _, Imm_c => Imm
    | _, Mut_c => Mut
    end.

Definition qc2q (qi : q_c) : q :=
  match qi with
    | RDM_c => RDM
    | Imm_c => Imm
    | Mut_c => Mut
    end.

(** Runtime resolution of a written qualifier.  The first argument is the
    mutability through which [RDM] is read: an object's own mutability, or the
    head of a runtime type.  Only a mutable or immutable head resolves [RDM];
    anything else leaves it unknown. *)
Definition dynq (qctx : q) (q0 : q) : q :=
  match q0 with
  | RDM =>
      match qctx with
      | Mut => Mut
      | Imm => Imm
      | _ => Lost
      end
  | _ => q0
  end.

(*  Adapted object creation for operational semantics *)
Definition vpa_mutability_object_creation (q1: q_r)(q2 : q_c) : q_r :=
  match q1, q2 with
    | Imm_r, RDM_c => Imm_r
    | Mut_r, RDM_c => Mut_r
    | _, Imm_c => Imm_r
    | _, Mut_c => Mut_r
    end.

(* ------------------TYPE-LEVEL OPERATIONS------------------*)

(** Apply a qualifier function to every written qualifier of a type.  A bare
    type-variable use carries no written qualifier and is left unchanged. *)
Fixpoint map_qual (f : q -> q) (T : qualified_type) : qualified_type :=
  match T with
  | TClass q0 C args => TClass (f q0) C (map (map_qual f) args)
  | TVar TVSub o n => TVar TVSub o n
  | TVar (TVQual q0) o n => TVar (TVQual (f q0)) o n
  | THead o n C args => THead o n C (map (map_qual f) args)
  end.

(** Adapt a declared type through a receiver qualifier.  Written qualifiers are
    adapted at every depth; type variables stay, to be substituted later. *)
Definition adapt (mt : method_scope) (qrecv : q) (T : qualified_type) : qualified_type :=
  map_qual (vpa_q mt qrecv) T.

(** Replace the outer qualifier of a static type. *)
Definition requalify (q0 : q) (T : qualified_type) : qualified_type :=
  match T with
  | TClass _ C args => TClass q0 C args
  | TVar _ o n => TVar (TVQual q0) o n
  | THead _ _ C args => TClass q0 C args
  end.

(** The class type [C<args>] with the qualifier of the type [U]. *)
Definition headby (U : qualified_type) (C : class_name)
    (args : list qualified_type) : qualified_type :=
  match U with
  | TClass q0 _ _ => TClass q0 C args
  | TVar TVSub o n => THead o n C args
  | TVar (TVQual q0) _ _ => TClass q0 C args
  | THead o n _ _ => THead o n C args
  end.

Definition default_type : qualified_type := TClass RO 0 [].

Definition tv_lookup {A : Type} (o : tv_owner) (cs ms : list A) (n : nat) : option A :=
  match o with
  | ClassVar => nth_error cs n
  | MethodVar => nth_error ms n
  end.

(** Substitute class type arguments [cs] and method type arguments [ms] for
    type variables.  A qualified use of a variable keeps the supplied class and
    arguments and replaces the outer qualifier. *)
Fixpoint subst (cs ms : list qualified_type) (T : qualified_type) : qualified_type :=
  match T with
  | TClass q0 C args => TClass q0 C (map (subst cs ms) args)
  | TVar u o n =>
      let U := match tv_lookup o cs ms n with
               | Some U => U
               | None => default_type
               end in
      match u with
      | TVSub => U
      | TVQual q0 => requalify q0 U
      end
  | THead o n C args =>
      headby (match tv_lookup o cs ms n with
              | Some U => U
              | None => default_type
              end) C (map (subst cs ms) args)
  end.

(** The identity instantiation of [n] class type parameters. *)
Definition class_var_types (n : nat) : list qualified_type :=
  map (fun i => TVar TVSub ClassVar i) (seq 0 n).

Definition method_var_types (n : nat) : list qualified_type :=
  map (fun i => TVar TVSub MethodVar i) (seq 0 n).

Definition default_rtype : rtype := RClass RO 0 [].

Definition rhead (R : rtype) : q :=
  match R with RClass q0 _ _ => q0 end.

Definition rrequalify (q0 : q) (R : rtype) : rtype :=
  match R with
  | RClass _ C args => RClass q0 C args
  end.

(** Dynamization: resolve a static type to a runtime type.  [qctx] is the
    mutability through which [RDM] is read, [ca] and [ma] are the runtime class
    and method type arguments.  [Lost] stays [Lost]: it marks a position whose
    concrete mutability the static type does not know. *)
Fixpoint dyn (qctx : q) (ca ma : list rtype) (T : qualified_type) : rtype :=
  match T with
  | TClass q0 C args => RClass (dynq qctx q0) C (map (dyn qctx ca ma) args)
  | TVar u o n =>
      let R := match tv_lookup o ca ma n with
               | Some R => R
               | None => default_rtype
               end in
      match u with
      | TVSub => R
      | TVQual q0 => rrequalify (dynq qctx q0) R
      end
  | THead o n C args =>
      RClass (rhead (match tv_lookup o ca ma n with
                     | Some R => R
                     | None => default_rtype
                     end)) C (map (dyn qctx ca ma) args)
  end.

(** No [Lost] anywhere in a type. *)
Fixpoint lost_free (T : qualified_type) : Prop :=
  match T with
  | TClass q0 _ args =>
      q0 <> Lost /\
      (fix go (l : list qualified_type) : Prop :=
         match l with
         | [] => True
         | t :: r => lost_free t /\ go r
         end) args
  | TVar TVSub _ _ => True
  | TVar (TVQual q0) _ _ => q0 <> Lost
  | THead _ _ _ args =>
      (fix go (l : list qualified_type) : Prop :=
         match l with
         | [] => True
         | t :: r => lost_free t /\ go r
         end) args
  end.

Fixpoint rlost_free (R : rtype) : Prop :=
  match R with
  | RClass q0 _ args =>
      q0 <> Lost /\
      (fix go (l : list rtype) : Prop :=
         match l with
         | [] => True
         | t :: r => rlost_free t /\ go r
         end) args
  end.

(** No [RDM] anywhere in a type. *)
Fixpoint rdm_free (T : qualified_type) : Prop :=
  match T with
  | TClass q0 _ args =>
      q0 <> RDM /\
      (fix go (l : list qualified_type) : Prop :=
         match l with
         | [] => True
         | t :: r => rdm_free t /\ go r
         end) args
  | TVar TVSub _ _ => True
  | TVar (TVQual q0) _ _ => q0 <> RDM
  | THead _ _ _ args =>
      (fix go (l : list qualified_type) : Prop :=
         match l with
         | [] => True
         | t :: r => rdm_free t /\ go r
         end) args
  end.

Lemma lost_free_go_Forall : forall l,
  (fix go (l : list qualified_type) : Prop :=
     match l with
     | [] => True
     | t :: r => lost_free t /\ go r
     end) l <-> Forall lost_free l.
Proof.
  induction l; simpl; split; intros H; auto.
  - destruct H. constructor; auto. apply IHl; auto.
  - inversion H; subst. split; auto. apply IHl; auto.
Qed.

Lemma lost_free_class : forall q0 C args,
  lost_free (TClass q0 C args) <-> q0 <> Lost /\ Forall lost_free args.
Proof.
  intros. simpl. rewrite lost_free_go_Forall. reflexivity.
Qed.

Lemma rlost_free_go_Forall : forall l,
  (fix go (l : list rtype) : Prop :=
     match l with
     | [] => True
     | t :: r => rlost_free t /\ go r
     end) l <-> Forall rlost_free l.
Proof.
  induction l; simpl; split; intros H; auto.
  - destruct H. constructor; auto. apply IHl; auto.
  - inversion H; subst. split; auto. apply IHl; auto.
Qed.

Lemma rlost_free_class : forall q0 C args,
  rlost_free (RClass q0 C args) <-> q0 <> Lost /\ Forall rlost_free args.
Proof.
  intros. simpl. rewrite rlost_free_go_Forall. reflexivity.
Qed.

Lemma rdm_free_go_Forall : forall l,
  (fix go (l : list qualified_type) : Prop :=
     match l with
     | [] => True
     | t :: r => rdm_free t /\ go r
     end) l <-> Forall rdm_free l.
Proof.
  induction l; simpl; split; intros H; auto.
  - destruct H. constructor; auto. apply IHl; auto.
  - inversion H; subst. split; auto. apply IHl; auto.
Qed.

Lemma rdm_free_class : forall q0 C args,
  rdm_free (TClass q0 C args) <-> q0 <> RDM /\ Forall rdm_free args.
Proof.
  intros. simpl. rewrite rdm_free_go_Forall. reflexivity.
Qed.

Lemma lost_free_head : forall o n C args,
  lost_free (THead o n C args) <-> Forall lost_free args.
Proof.
  intros. simpl. rewrite lost_free_go_Forall. reflexivity.
Qed.
