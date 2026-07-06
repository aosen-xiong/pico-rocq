From Stdlib Require Import List.
Require Import Stdlib.Classes.RelationClasses.
Import ListNotations.
Require Import Syntax Notations LibTactics Tactics Helpers.

Inductive method_subtype : method_type -> method_type -> Prop :=
  | method_subtyping_refl : forall mt,
      method_subtype mt mt
  | mt_concret_imm : forall mt,
      method_subtype mt AbstractImm
  | method_abs_imm : forall mt,
      method_subtype ConcreteImm mt
  .

Lemma method_subtyping_trans : 
  forall mt1 mt2 mt3
    (H12 : method_subtype mt1 mt2)
    (H23 : method_subtype mt2 mt3),
    method_subtype mt1 mt3.
Proof.
  intros mt1 mt2 mt3 H12 H23.
  inversion H12; subst.
  - (* H12: method_subtyping_refl mt2 *)
    exact H23.
  - (* H12: mt_concret_imm: method_subtyping mt2 ConcreteImm *)
    inversion H23; subst.
    + (* H23: method_subtyping_refl ConcreteImm *)
      exact (mt_concret_imm mt1).
    + (* H23: mt_concret_imm: method_subtyping ConcreteImm ConcreteImm *)
      exact (mt_concret_imm mt1).
  - (* H12: method_abs_imm: method_subtyping AbstractImm mt2 *)
    apply method_abs_imm.
Qed.

(** Qualifier Ordering *)
Inductive q_subtype : q -> q -> Prop :=
  | q_refl : forall q1
      (Hnot_lost : q1 <> Lost),
      q_subtype q1 q1
  | q_rd : forall q1,
      q_subtype q1 RO
  | q_bot : forall q1,
      q_subtype Bot q1.
Global Hint Constructors q_subtype: typ.

Example lost_subtype_refl: q_subtype Lost Lost -> False.
Proof.
  intros H.
  inversion H; subst; try congruence.
Qed.

(* Subtyping for qualified types *)
Lemma q_subtype_trans: forall μ1 μ2 μ3,
  q_subtype μ1 μ2 -> q_subtype μ2 μ3 -> q_subtype μ1 μ3.
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
