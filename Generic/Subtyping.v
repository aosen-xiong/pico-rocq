From Stdlib Require Import List.
Require Import Stdlib.Classes.RelationClasses.
Import ListNotations.
Require Import Syntax Notations LibTactics Tactics Helpers ViewpointAdaptation.

Inductive method_scope_subtype : method_scope -> method_scope -> Prop :=
  | method_subtyping_refl : forall mt,
      method_scope_subtype mt mt
  | method_cs_as : method_scope_subtype ConcreteState AbstractState
  | method_rs_as : method_scope_subtype ReadonlyState AbstractState
  | method_ts_as : method_scope_subtype TransitiveState AbstractState
  | method_ts_cs : method_scope_subtype TransitiveState ConcreteState
  | method_ts_rs : method_scope_subtype TransitiveState ReadonlyState
  .

Lemma concrete_assignability_submethod : forall callee caller,
  strict_assignability_method_scope caller ->
  method_scope_subtype callee caller ->
  strict_assignability_method_scope callee.
Proof.
  intros callee caller Hcaller Hsub.
  destruct Hcaller as [Hcaller | Hcaller]; subst caller;
    inversion Hsub; subst; unfold strict_assignability_method_scope; auto.
Qed.

Lemma readonly_state_submethod : forall callee caller,
  readonly_state_method_scope caller ->
  method_scope_subtype callee caller ->
  readonly_state_method_scope callee.
Proof.
  intros callee caller Hcaller Hsub.
  destruct Hcaller as [-> | ->]; inversion Hsub; subst;
    unfold readonly_state_method_scope; auto.
Qed.

(** Qualifier Ordering *)
Inductive q_subtype : q -> q -> Prop :=
  | q_refl : forall q1
      (Hnot_lost : q1 <> Lost),
      q_subtype q1 q1
  | q_rd : forall q1,
      q_subtype q1 RO
  | q_bot : forall q1,
      q_subtype Bot q1
where "q1 ⊑ q2" := (q_subtype q1 q2).
Global Hint Constructors q_subtype: typ.

Example lost_subtype_refl: Lost ⊑ Lost -> False.
Proof.
  intros H.
  inversion H; subst; try congruence.
Qed.

Lemma q_subtype_trans: forall μ1 μ2 μ3, μ1 ⊑ μ2 -> μ2 ⊑ μ3 -> μ1 ⊑ μ3.
Proof.
  intros.
  inversion H; steps;
    inversion H0; eauto with typ lia.
Qed.
Global Hint Resolve q_subtype_trans: typ.

(** The declared superclass together with its explicit type arguments. *)
Definition parent_lookup (CT : class_table) (C : class_name)
    : option (class_name * list qualified_type) :=
  match find_class CT C with
  | Some def => super (signature def)
  | None => None
  end.

(* Java base type subtyping, ignoring type arguments *)
Inductive base_subtype : class_table -> class_name -> class_name -> Prop :=
  | base_refl : forall (CT : class_table) (C : class_name)
      (Hdom : C < dom CT),
      base_subtype CT C C
  | base_trans : forall (CT : class_table) (C D E : class_name)
      (Hsub1 : base_subtype CT C D)
      (Hsub2 : base_subtype CT D E),
      base_subtype CT C E
  | base_extends : forall (CT : class_table) (C D : class_name) Ss
      (Hdom_C  : C < dom CT)
      (Hdom_D  : D < dom CT)
      (Hparent : parent_lookup CT C = Some (D, Ss)),
      base_subtype CT C D.
Global Hint Constructors base_subtype: typ.

(** Static superclass instantiation.  [super_inst CT mt qh C Ts D Vs] says
    that, in code of mode [mt], a [C<Ts>] headed by qualifier [qh] is, viewed
    at superclass [D], a [D<Vs>].  Each step adapts the declared superclass
    arguments through the head qualifier, with the mutability table of the
    mode, and then substitutes the subclass's arguments.  In readonly-state
    and transitive-state code a mutable superclass argument seen through a
    non-mutable head therefore becomes unknown. *)
Inductive super_inst (CT : class_table) (mt : method_scope) (qh : q)
    : class_name -> list qualified_type -> class_name -> list qualified_type -> Prop :=
  | si_refl : forall C Ts,
      super_inst CT mt qh C Ts C Ts
  | si_step : forall C Ts P Ss D Vs
      (Hparent : parent_lookup CT C = Some (P, Ss))
      (Hrest : super_inst CT mt qh P
                 (map (subst Ts []) (map (adapt mt qh) Ss)) D Vs),
      super_inst CT mt qh C Ts D Vs.

(** Runtime superclass instantiation: the same walk over runtime type
    arguments, resolving [RDM] in superclass arguments through [qh]. *)
Inductive rsuper_inst (CT : class_table) (qh : q)
    : class_name -> list rtype -> class_name -> list rtype -> Prop :=
  | rsi_refl : forall C Rs,
      rsuper_inst CT qh C Rs C Rs
  | rsi_step : forall C Rs P Ss D Vs
      (Hparent : parent_lookup CT C = Some (P, Ss))
      (Hrest : rsuper_inst CT qh P (map (dyn qh Rs []) Ss) D Vs),
      rsuper_inst CT qh C Rs D Vs.

(** Type-argument compatibility.  Arguments are invariant, except that a
    mutable or immutable head may be forgotten to [Lost]. *)
Definition arg_q_sub (q1 q2 : q) : Prop :=
  q2 = q1 \/ (q2 = Lost /\ (q1 = Mut \/ q1 = Imm)).

Inductive targ_sub : qualified_type -> qualified_type -> Prop :=
  | tas_var : forall u o n,
      targ_sub (TVar u o n) (TVar u o n)
  | tas_class : forall q1 q2 C Ts Us
      (Hq : arg_q_sub q1 q2)
      (Hargs : Forall2 targ_sub Ts Us),
      targ_sub (TClass q1 C Ts) (TClass q2 C Us)
  | tas_head : forall o n C Ts Us
      (Hargs : Forall2 targ_sub Ts Us),
      targ_sub (THead o n C Ts) (THead o n C Us).

Section targ_sub_ind'.
  Variable P : qualified_type -> qualified_type -> Prop.
  Hypothesis Hvar : forall u o n, P (TVar u o n) (TVar u o n).
  Hypothesis Hclass : forall q1 q2 C Ts Us,
    arg_q_sub q1 q2 ->
    Forall2 targ_sub Ts Us ->
    Forall2 P Ts Us ->
    P (TClass q1 C Ts) (TClass q2 C Us).
  Hypothesis Hhead : forall o n C Ts Us,
    Forall2 targ_sub Ts Us ->
    Forall2 P Ts Us ->
    P (THead o n C Ts) (THead o n C Us).

  Fixpoint targ_sub_ind' T U (H : targ_sub T U) : P T U :=
    match H with
    | tas_var u o n => Hvar u o n
    | tas_class q1 q2 C Ts Us Hq Hargs =>
        Hclass q1 q2 C Ts Us Hq Hargs
          ((fix go Ts Us (Hl : Forall2 targ_sub Ts Us) : Forall2 P Ts Us :=
              match Hl with
              | Forall2_nil _ => Forall2_nil P
              | Forall2_cons t u Ht Hr =>
                  Forall2_cons t u (targ_sub_ind' t u Ht) (go _ _ Hr)
              end) Ts Us Hargs)
    | tas_head o n C Ts Us Hargs =>
        Hhead o n C Ts Us Hargs
          ((fix go Ts Us (Hl : Forall2 targ_sub Ts Us) : Forall2 P Ts Us :=
              match Hl with
              | Forall2_nil _ => Forall2_nil P
              | Forall2_cons t u Ht Hr =>
                  Forall2_cons t u (targ_sub_ind' t u Ht) (go _ _ Hr)
              end) Ts Us Hargs)
    end.
End targ_sub_ind'.

(** The same relation on runtime types. *)
Inductive rarg_sub : rtype -> rtype -> Prop :=
  | ras_class : forall q1 q2 C Rs Us
      (Hq : arg_q_sub q1 q2)
      (Hargs : Forall2 rarg_sub Rs Us),
      rarg_sub (RClass q1 C Rs) (RClass q2 C Us).

Section rarg_sub_ind'.
  Variable P : rtype -> rtype -> Prop.
  Hypothesis Hclass : forall q1 q2 C Rs Us,
    arg_q_sub q1 q2 ->
    Forall2 rarg_sub Rs Us ->
    Forall2 P Rs Us ->
    P (RClass q1 C Rs) (RClass q2 C Us).

  Fixpoint rarg_sub_ind' R U (H : rarg_sub R U) : P R U :=
    match H with
    | ras_class q1 q2 C Rs Us Hq Hargs =>
        Hclass q1 q2 C Rs Us Hq Hargs
          ((fix go Rs Us (Hl : Forall2 rarg_sub Rs Us) : Forall2 P Rs Us :=
              match Hl with
              | Forall2_nil _ => Forall2_nil P
              | Forall2_cons t u Ht Hr =>
                  Forall2_cons t u (rarg_sub_ind' t u Ht) (go _ _ Hr)
              end) Rs Us Hargs)
    end.
End rarg_sub_ind'.

(** Declared bound of a type variable. *)
Definition tv_bound (Δ : tv_env) (o : tv_owner) (n : nat) : option qualified_type :=
  tv_lookup o (class_bounds Δ) (method_bounds Δ) n.

(* Qualified type subtyping *)
Inductive qualified_type_subtype (CT : class_table) (Δ : tv_env)
    : qualified_type -> qualified_type -> Prop :=
  (* Same class: widen the head qualifier, arguments stay compatible *)
  | qtype_qual : forall q1 q2 C Ts Us
      (Hdom  : C < dom CT)
      (Hqsub : q_subtype q1 q2)
      (Hargs : Forall2 targ_sub Ts Us),
      qualified_type_subtype CT Δ (TClass q1 C Ts) (TClass q2 C Us)
  (* Same qualifier: move up the class hierarchy *)
  | qtype_hier : forall q1 C Ts D Vs
      (Hsuper : super_inst CT (tv_mode Δ) q1 C Ts D Vs),
      qualified_type_subtype CT Δ (TClass q1 C Ts) (TClass q1 D Vs)
  (* A bare type variable is a subtype of itself and of its bound *)
  | qtype_var_refl : forall o n,
      qualified_type_subtype CT Δ (TVar TVSub o n) (TVar TVSub o n)
  | qtype_var_bound : forall o n B
      (Hbound : tv_bound Δ o n = Some B),
      qualified_type_subtype CT Δ (TVar TVSub o n) B
  (* A qualified use of a type variable: the written qualifier may be
     widened, and the supplied type itself may be viewed as readonly. *)
  | qtype_qvar_qual : forall q1 q2 o n
      (Hqsub : q_subtype q1 q2),
      qualified_type_subtype CT Δ (TVar (TVQual q1) o n) (TVar (TVQual q2) o n)
  | qtype_var_ro : forall o n,
      qualified_type_subtype CT Δ (TVar TVSub o n) (TVar (TVQual RO) o n)
  (* A qualified use may be viewed at an argument-free class that bounds the
     variable.  With no arguments there is nothing whose meaning could depend
     on the replaced qualifier. *)
  | qtype_qvar_bound : forall q1 o n qb C
      (Hbound : qualified_type_subtype CT Δ (TVar TVSub o n) (TClass qb C [])),
      qualified_type_subtype CT Δ (TVar (TVQual q1) o n) (TClass q1 C [])
  (* A class type whose qualifier is that of a type variable's argument: it
     may be viewed as readonly, its arguments stay compatible, and the
     bottom-qualified type of the class is below it. *)
  | qtype_head_ro : forall o n C Ts Us B
      (Hbound : tv_bound Δ o n = Some B)
      (Hargs : Forall2 targ_sub Ts Us),
      qualified_type_subtype CT Δ (THead o n C Ts) (TClass RO C Us)
  | qtype_head_args : forall o n C Ts Us
      (Hargs : Forall2 targ_sub Ts Us),
      qualified_type_subtype CT Δ (THead o n C Ts) (THead o n C Us)
  (* Up the class hierarchy with the same qualifier.  The superclass arguments
     are read through the readonly view, the only one valid for every
     qualifier the variable may stand for. *)
  | qtype_head_hier : forall o n C Ts D Vs
      (Hsuper : super_inst CT (tv_mode Δ) RO C Ts D Vs),
      qualified_type_subtype CT Δ (THead o n C Ts) (THead o n D Vs)
  | qtype_head_bot : forall o n C Ts Us
      (Hdom  : C < dom CT)
      (Hargs : Forall2 targ_sub Ts Us),
      qualified_type_subtype CT Δ (TClass Bot C Ts) (THead o n C Us)
  | qtype_trans : forall T1 T2 T3
      (Hsub12 : qualified_type_subtype CT Δ T1 T2)
      (Hsub23 : qualified_type_subtype CT Δ T2 T3),
      qualified_type_subtype CT Δ T1 T3.

(** Runtime head-qualifier order between runtime types. *)
Definition rq_sub (q1 q2 : q) : Prop :=
  q2 = q1 \/ q2 = RO \/ (q2 = Lost /\ (q1 = Mut \/ q1 = Imm)).

(** Runtime subtyping between runtime types.  A bottom-headed runtime type
    (the type of null only) is below every runtime type of a superclass with
    the right number of arguments. *)
Definition rtype_subtype (CT : class_table) (R1 R2 : rtype) : Prop :=
  match R1, R2 with
  | RClass q1 C Rs, RClass q2 D Us =>
      (q1 = Bot /\
       exists Vs, rsuper_inst CT Bot C Rs D Vs /\ length Vs = length Us) \/
      (rq_sub q1 q2 /\
       exists Vs, rsuper_inst CT q1 C Rs D Vs /\ Forall2 rarg_sub Vs Us)
  end.

(* ------------------BASIC FACTS------------------*)

(** A type argument satisfies a bound when it is below the bound in every
    protection mode: the same type use is visible from code of every mode. *)
Definition with_mode (Δ : tv_env) (m : method_scope) : tv_env :=
  mk_tv_env (class_bounds Δ) (method_bounds Δ) m.

Definition bound_sub (CT : class_table) (Δ : tv_env) (T B : qualified_type) : Prop :=
  forall m, qualified_type_subtype CT (with_mode Δ m) T B.

Lemma with_mode_self : forall Δ, with_mode Δ (tv_mode Δ) = Δ.
Proof. intros [cb mb m]. reflexivity. Qed.

Lemma bound_sub_self : forall CT Δ T B,
  bound_sub CT Δ T B -> qualified_type_subtype CT Δ T B.
Proof.
  intros CT Δ T B H. specialize (H (tv_mode Δ)). rewrite with_mode_self in H.
  exact H.
Qed.

Lemma targ_sub_refl : forall T, targ_sub T T.
Proof.
  induction T using qualified_type_ind'.
  - apply tas_class; [left; reflexivity|].
    induction H; constructor; auto.
  - apply tas_var.
  - apply tas_head. induction H; constructor; auto.
Qed.

Lemma Forall2_targ_sub_refl : forall Ts, Forall2 targ_sub Ts Ts.
Proof.
  induction Ts; constructor; auto using targ_sub_refl.
Qed.

Lemma rarg_sub_refl : forall R, rarg_sub R R.
Proof.
  induction R using rtype_ind'.
  apply ras_class; [left; reflexivity|].
  induction H; constructor; auto.
Qed.

Lemma Forall2_rarg_sub_refl : forall Rs, Forall2 rarg_sub Rs Rs.
Proof.
  induction Rs; constructor; auto using rarg_sub_refl.
Qed.

Lemma arg_q_sub_trans : forall q1 q2 q3,
  arg_q_sub q1 q2 -> arg_q_sub q2 q3 -> arg_q_sub q1 q3.
Proof.
  unfold arg_q_sub. intros q1 q2 q3 H12 H23.
  destruct H12 as [-> | [-> H1]]; destruct H23 as [-> | [-> H2]]; auto;
    try (destruct H2; discriminate).
Qed.

Lemma rarg_sub_trans : forall R1 R2,
  rarg_sub R1 R2 -> forall R3, rarg_sub R2 R3 -> rarg_sub R1 R3.
Proof.
  intros R1 R2 H12.
  induction H12 using rarg_sub_ind'.
  intros R3 H23. inversion H23; subst.
  apply ras_class; [eauto using arg_q_sub_trans|].
  clear H23 H0 Hq. generalize dependent Us0.
  induction H1; intros Us0 Hargs; inversion Hargs; subst; constructor; eauto.
Qed.

Lemma targ_sub_trans : forall T1 T2,
  targ_sub T1 T2 -> forall T3, targ_sub T2 T3 -> targ_sub T1 T3.
Proof.
  intros T1 T2 H12.
  induction H12 using targ_sub_ind'; intros T3 H23.
  - exact H23.
  - inversion H23; subst.
    apply tas_class; [eauto using arg_q_sub_trans|].
    clear H23 H0 Hq. generalize dependent Us0.
    induction H1; intros Us0 Hargs; inversion Hargs; subst; constructor; eauto.
  - inversion H23; subst.
    apply tas_head.
    clear H23 H. generalize dependent Us0.
    induction H0; intros Us0 Hargs; inversion Hargs; subst; constructor; eauto.
Qed.

Lemma qualified_type_subtype_refl_class : forall CT Δ q0 C Ts,
  C < dom CT -> q0 <> Lost ->
  qualified_type_subtype CT Δ (TClass q0 C Ts) (TClass q0 C Ts).
Proof.
  intros. apply qtype_qual; auto using Forall2_targ_sub_refl.
  apply q_refl; auto.
Qed.

Lemma parent_lookup_dom : forall CT C P Ss,
  parent_lookup CT C = Some (P, Ss) -> C < dom CT.
Proof.
  intros CT C P Ss H. unfold parent_lookup in H.
  destruct (find_class CT C) eqn:Hfind; [|discriminate].
  eapply find_class_dom; eauto.
Qed.

Lemma base_subtype_domain : forall CT C D,
  base_subtype CT C D ->
  C < dom CT /\ D < dom CT.
Proof.
  intros CT C D Hsub.
  induction Hsub.
  - split; exact Hdom.
  - destruct IHHsub1 as [HC HD].
    destruct IHHsub2 as [_ HE].
    split; auto.
  - split; auto.
Qed.

(** Superclass declarations name existing classes. *)
Definition supers_in_dom (CT : class_table) : Prop :=
  forall C P Ss, parent_lookup CT C = Some (P, Ss) -> P < dom CT.

Lemma super_inst_base : forall CT mt qh C Ts D Vs,
  supers_in_dom CT -> C < dom CT ->
  super_inst CT mt qh C Ts D Vs -> base_subtype CT C D.
Proof.
  intros CT mt qh C Ts D Vs Hsd Hdom H. induction H.
  - apply base_refl; auto.
  - eapply base_trans; [|apply IHsuper_inst; eauto].
    eapply base_extends; eauto.
Qed.

Lemma rsuper_inst_base : forall CT qh C Rs D Vs,
  supers_in_dom CT -> C < dom CT ->
  rsuper_inst CT qh C Rs D Vs -> base_subtype CT C D.
Proof.
  intros CT qh C Rs D Vs Hsd Hdom H. induction H.
  - apply base_refl; auto.
  - eapply base_trans; [|apply IHrsuper_inst; eauto].
    eapply base_extends; eauto.
Qed.

Lemma rsuper_inst_trans : forall CT qh C Rs D Vs,
  rsuper_inst CT qh C Rs D Vs ->
  forall E Ws, rsuper_inst CT qh D Vs E Ws ->
  rsuper_inst CT qh C Rs E Ws.
Proof.
  intros CT qh C Rs D Vs H. induction H; intros E Ws H2; auto.
  eapply rsi_step; eauto.
Qed.

Lemma super_inst_trans : forall CT mt qh C Ts D Vs,
  super_inst CT mt qh C Ts D Vs ->
  forall E Ws, super_inst CT mt qh D Vs E Ws ->
  super_inst CT mt qh C Ts E Ws.
Proof.
  intros CT mt qh C Ts D Vs H. induction H; intros E Ws H2; auto.
  eapply si_step; eauto.
Qed.
