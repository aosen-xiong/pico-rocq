From Stdlib Require Import List.
Require Import Stdlib.Classes.RelationClasses.
Import ListNotations.
Require Import Syntax Notations LibTactics Tactics Helpers.

Inductive method_subtype : method_type -> method_type -> Prop :=
  | method_subtyping_refl : forall mt,
      method_subtype mt mt
  | method_cs_as : method_subtype ConcreteState AbstractImm
  | method_rs_as : method_subtype SafeRO AbstractImm
  | method_ts_as : method_subtype ConcreteImm AbstractImm
  | method_ts_cs : method_subtype ConcreteImm ConcreteState
  | method_ts_rs : method_subtype ConcreteImm SafeRO
  .

Lemma method_subtyping_trans : 
  forall mt1 mt2 mt3
    (H12 : method_subtype mt1 mt2)
    (H23 : method_subtype mt2 mt3),
    method_subtype mt1 mt3.
Proof.
  intros mt1 mt2 mt3 H12 H23.
  inversion H12; subst; inversion H23; subst; constructor.
Qed.

Lemma concrete_assignability_submethod : forall callee caller,
  concrete_assignability_method_type caller ->
  method_subtype callee caller ->
  concrete_assignability_method_type callee.
Proof.
  intros callee caller Hcaller Hsub.
  destruct Hcaller as [Hcaller | Hcaller]; subst caller;
    inversion Hsub; subst; unfold concrete_assignability_method_type; auto.
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

(* Subtyping for qualified types *)
Lemma q_subtype_trans: forall μ1 μ2 μ3, μ1 ⊑ μ2 -> μ2 ⊑ μ3 -> μ1 ⊑ μ3.
Proof.
  intros.
  inversion H; steps;
    inversion H0; eauto with typ lia.
Qed.
Global Hint Resolve q_subtype_trans: typ.

Definition parent_lookup (CT : class_table) (C : class_name) : option class_name :=
  match find_class CT C with
  | Some def => super (signature def)
  | None => None
  end.

(* Java base type subtyping *)
Inductive base_subtype : class_table -> class_name -> class_name -> Prop :=
  | base_refl : forall (CT : class_table) (C : class_name)
      (Hdom : C < dom CT),
      base_subtype CT C C
  | base_trans : forall (CT : class_table) (C D E : class_name)
      (Hsub1 : base_subtype CT C D)
      (Hsub2 : base_subtype CT D E),
      base_subtype CT C E
  | base_extends : forall (CT : class_table) (C D : class_name)
      (Hdom_C  : C < dom CT)
      (Hdom_D  : D < dom CT)
      (Hparent : parent_lookup CT C = Some D),
      base_subtype CT C D.
Global Hint Constructors base_subtype: typ.

(* Qualified type subtyping *)
Inductive qualified_type_subtype : class_table -> qualified_type -> qualified_type -> Prop :=
  | qtype_sub : forall CT qt1 qt2
      (Hdom1  : sctype qt1 < dom CT)
      (Hdom2  : sctype qt2 < dom CT)
      (Hqsub  : q_subtype (sqtype qt1) (sqtype qt2))
      (Hbsub  : base_subtype CT (sctype qt1) (sctype qt2)),
      qualified_type_subtype CT qt1 qt2
  | qtype_trans : forall CT qt1 qt2 qt3
      (Hsub12 : qualified_type_subtype CT qt1 qt2)
      (Hsub23 : qualified_type_subtype CT qt2 qt3),
      qualified_type_subtype CT qt1 qt3
  | qtype_refl : forall CT qt
      (Hdom      : sctype qt < dom CT)
      (Hnot_lost : sqtype qt <> Lost),
      qualified_type_subtype CT qt qt.

Lemma qualified_type_subtype_dom2 :
  forall CT qt1 qt2,
    qualified_type_subtype CT qt1 qt2 ->
    sctype qt2 < dom CT.
Proof.
  intros CT qt1 qt2 H.
  induction H.
  - exact Hdom2.
  - exact IHqualified_type_subtype2.
  - exact Hdom.
Qed.

Lemma qualified_type_subtype_dom1 :
  forall CT qt1 qt2,
    qualified_type_subtype CT qt1 qt2 ->
    sctype qt1 < dom CT.
Proof.
  intros CT qt1 qt2 H.
  induction H.
  - exact Hdom1.
  - exact IHqualified_type_subtype1.
  - exact Hdom.
Qed.

Lemma qualified_type_subtype_base_subtype :
  forall CT qt1 qt2,
    qualified_type_subtype CT qt1 qt2 ->
    base_subtype CT (sctype qt1) (sctype qt2).
Proof.
  intros CT qt1 qt2 H.
  induction H.
  - exact Hbsub.
  - eapply base_trans; eauto.
  - eapply base_refl; eauto.
Qed.

Lemma qualified_type_subtype_q_subtype :
  forall CT qt1 qt2,
    qualified_type_subtype CT qt1 qt2 ->
    q_subtype (sqtype qt1) (sqtype qt2).
Proof.
  intros CT qt1 qt2 H.
  induction H.
  - exact Hqsub.
  - eapply q_subtype_trans; eauto.
  - destruct qt as [q c]; simpl.
    destruct q; try (apply q_refl; discriminate).
    exfalso. simpl in Hnot_lost. apply Hnot_lost. reflexivity.
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
