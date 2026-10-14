From Stdlib Require Import List.
Import ListNotations.

(** Generic PICO: the flat PICO calculus extended with class and method type
    parameters with qualified bounds, and a cast statement.  The design follows
    the GAIT paper and the Lean development's generic immutability instance;
    evaluation stays big-step. *)

(* ------------------SYNTAX------------------*)
Definition var : Type := nat.
Definition method_name : Type := nat.
Definition class_name : Type := nat.

(** All mutability qualifiers *)
Inductive q : Type :=
  (* q_c *)
  | Mut
  | Imm
  | RDM
  (* q_f *)
  | RO
  (* q_h *)
  | Lost
  | Bot.

(** Class declaration / allocation mutability qualifier *)
Inductive q_c : Type :=
  | Mut_c
  | Imm_c
  | RDM_c.

(* Assignability qualifier *)
Inductive a : Type :=
  | Assignable
  | Final
  | RDA.

(** Who declared a type variable.  Class parameter [n] and method parameter
    [n] are different variables. *)
Inductive tv_owner : Type :=
  | ClassVar
  | MethodVar.

(** How a type variable is used.  [TVSub] stands for exactly the supplied
    type.  [TVQual q] keeps the supplied class and arguments and replaces the
    outer qualifier by [q].  [TVPoly m] does the same with the [m]-th
    qualifier parameter of the enclosing method. *)
Inductive tv_use : Type :=
  | TVSub
  | TVQual (qual : q)
  | TVPoly (param : nat).

(** Qualified types: a qualified class type with type arguments, a use of a
    declared type variable, or a class type whose qualifier is a qualifier
    parameter of the enclosing method: [THead n C args] is [C<args>] under
    the method's [n]-th qualifier parameter. *)
Inductive qualified_type : Type :=
  | TClass : q -> class_name -> list qualified_type -> qualified_type
  | TVar : tv_use -> tv_owner -> nat -> qualified_type
  | THead : nat -> class_name -> list qualified_type -> qualified_type.

(** A qualifier argument of a call: a written qualifier, or one of the
    calling method's own qualifier parameters. *)
Inductive qarg : Type :=
  | QLit : q -> qarg
  | QVar : nat -> qarg.

(** Induction principle that also covers the nested argument lists. *)
Section qualified_type_ind'.
  Variable P : qualified_type -> Prop.
  Hypothesis Hclass : forall qual C args,
    Forall P args -> P (TClass qual C args).
  Hypothesis Hvar : forall u o n, P (TVar u o n).
  Hypothesis Hhead : forall n C args,
    Forall P args -> P (THead n C args).

  Fixpoint qualified_type_ind' (T : qualified_type) : P T :=
    match T with
    | TClass qual C args =>
        Hclass qual C args
          ((fix go (l : list qualified_type) : Forall P l :=
              match l with
              | [] => Forall_nil P
              | t :: r => Forall_cons t (qualified_type_ind' t) (go r)
              end) args)
    | TVar u o n => Hvar u o n
    | THead n C args =>
        Hhead n C args
          ((fix go (l : list qualified_type) : Forall P l :=
              match l with
              | [] => Forall_nil P
              | t :: r => Forall_cons t (qualified_type_ind' t) (go r)
              end) args)
    end.
End qualified_type_ind'.

Definition s_env := list qualified_type.

Inductive expr : Type :=
  | ENull : expr
  | EVar : var -> expr
  | EField : var -> var -> expr.

Inductive stmt: Type :=
  | SSkip: stmt (* skip *)
  | SLocal: qualified_type -> var -> stmt (* T x *)
  | SVarAss: var -> expr -> stmt (* x = e *)
  | SFldWrite: var -> var -> var -> stmt (* x.f = y *)
  | SNew: var -> q_c -> class_name -> list qualified_type -> list var -> stmt
      (* x = new q_c C<Ts>(y1, ..., yn) *)
  | SCall: var -> method_name -> var -> list qualified_type -> list qarg ->
           list var -> stmt
      (* x = y.<Ts; Qs>m(z1, ..., zn): type arguments, then qualifier
         arguments *)
  | SCast: var -> qualified_type -> var -> stmt (* x = (T) y *)
  | SSeq: stmt -> stmt -> stmt. (* s1; s2 *)

(** Field declaration: assignability and declared type.  The declared type may
    mention the class's type parameters. *)
Record field_def := {
  assignability : a;
  ftype : qualified_type;
}.

Record method_body := {
  mbody_stmt: stmt; (* Method body statement *)
  mreturn: var; (* Return variable *)
}.

Inductive method_scope : Type :=
  | AbstractState
  | ConcreteState
  | ReadonlyState
  | TransitiveState.

Definition readonly_state_method_scope (mt : method_scope) : Prop :=
  mt = ReadonlyState \/ mt = TransitiveState.

Definition strict_assignability_method_scope (mt : method_scope) : Prop :=
  mt = ConcreteState \/ mt = TransitiveState.

(** Type-parameter bounds, class parameters first, method parameters second
    (bounds are non-variable class types, checked by well-formedness),
    together with the protection mode of the enclosing code.  The mode
    selects the table through which superclass type arguments are seen. *)
Record tv_env := mk_tv_env {
  class_bounds : list qualified_type;
  method_bounds : list qualified_type;
  tv_mode : method_scope;
  qparams : nat; (* number of qualifier parameters of the enclosing method *)
}.

Record method_sig := {
  mscope: method_scope;
  mtparams : list qualified_type; (* bounds of the method's type parameters *)
  mqparams : nat; (* number of the method's qualifier parameters *)
  mret : qualified_type; (* Return type *)
  mname : method_name; (* Method name *)
  mreceiver: qualified_type; (* T this *)
  mparams : list qualified_type; (* T x1, ..., T xn *)
}.

Record method_def := {
  msignature : method_sig; (* Method signature *)
  mbody : method_body; (* Method body *)
}.

Record class_body := {
  fields : list field_def; (* Class fields *)
  methods : list method_def; (* Class methods *)
}.

Record class_sig := {
  class_qualifier : q_c; (* Mutable, Immutable, or RDM *)
  cname : class_name; (* Must equal the class's index in the class table *)
  ctparams : list qualified_type; (* bounds of the class's type parameters *)
  super : option (class_name * list qualified_type);
    (* superclass with explicit type arguments over this class's parameters *)
}.

Record class_def := {
  signature : class_sig; (* Class signature *)
  body : class_body; (* Class body *)
}.

(* Class table is a list of class declarations *)
Definition class_table := list class_def.

(* ------------------RUNTIME MODEL------------------*)

(** Runtime object mutability *)
Inductive q_r : Type :=
  | Mut_r
  | Imm_r.

Definition qr2q (qr : q_r) : q :=
  match qr with
  | Mut_r => Mut
  | Imm_r => Imm
  end.

(** Runtime types are fully resolved class types: no type variables.  They are
    what an object stores for its type arguments.  Their qualifiers reuse [q];
    resolution never produces [RDM]. *)
Inductive rtype : Type :=
  | RClass : q -> class_name -> list rtype -> rtype.

Section rtype_ind'.
  Variable P : rtype -> Prop.
  Hypothesis Hclass : forall qual C args,
    Forall P args -> P (RClass qual C args).

  Fixpoint rtype_ind' (R : rtype) : P R :=
    match R with
    | RClass qual C args =>
        Hclass qual C args
          ((fix go (l : list rtype) : Forall P l :=
              match l with
              | [] => Forall_nil P
              | t :: r => Forall_cons t (rtype_ind' t) (go r)
              end) args)
    end.
End rtype_ind'.

(** Runtime object type: mutability, class, and runtime type arguments. *)
Record runtime_type := mkruntime_type {
  rqtype: q_r; (* Runtime mutability *)
  rctype: class_name; (* Class name *)
  rtargs: list rtype; (* Runtime type arguments *)
}.

(** Memory address *)
Definition Loc : Type := nat.

(** Runtime value *)
Inductive value : Type :=
  | Null_a : value
  | Iot: Loc -> value.

(** Variable mapping *)
Definition var_mapping := list value.

(** Runtime environment of one activation: the variables, the runtime type
    arguments of the receiver viewed at the class that declares the running
    method, the runtime type arguments of the method itself, and the
    qualifiers supplied for the method's qualifier parameters. *)
Record r_env := mkr_env {
  vars: var_mapping;
  cargs: list rtype;
  margs: list rtype;
  qargs: list q; (* the activation's qualifier arguments *)
}.

Definition set_vars (rΓ : r_env) (vars' : var_mapping) : r_env :=
  mkr_env vars' (cargs rΓ) (margs rΓ) (qargs rΓ).

(** Field mapping *)
Definition fields_mapping := list value.

(** Runtime object *)
Record Obj := mkObj {
  rt_type: runtime_type; (* Runtime type *)
  fields_map: fields_mapping; (* Field mapping *)
}.

Definition set_fields_map (o : Obj) (fields' : fields_mapping) : Obj :=
  mkObj (rt_type o) fields'.

(** Heap *)
Definition heap := list Obj.
