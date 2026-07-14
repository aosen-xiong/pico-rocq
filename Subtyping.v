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

(* Object-class inheritance is kept separate from source-base subtyping so
   field and method lookup can state object-only premises directly. *)
Inductive class_subtype : class_table -> class_name -> class_name -> Prop :=
  | class_refl : forall (CT : class_table) (C : class_name)
      (Hdom : C < dom CT),
      class_subtype CT C C
  | class_trans : forall (CT : class_table) (C D E : class_name)
      (Hsub1 : class_subtype CT C D)
      (Hsub2 : class_subtype CT D E),
      class_subtype CT C E
  | class_extends : forall (CT : class_table) (C D : class_name)
      (Hdom_C  : C < dom CT)
      (Hdom_D  : D < dom CT)
      (Hparent : parent_lookup CT C = Some D),
      class_subtype CT C D.
Global Hint Constructors class_subtype: typ.

(* [TInt] has equality-only subtyping.  References use [class_subtype]. *)
Inductive base_subtype : class_table -> base_type -> base_type -> Prop :=
  | base_int : forall CT,
      base_subtype CT TInt TInt
  | base_ref : forall CT C D,
      class_subtype CT C D ->
      base_subtype CT (TRef C) (TRef D)
  | base_trans : forall CT b1 b2 b3,
      base_subtype CT b1 b2 ->
      base_subtype CT b2 b3 ->
      base_subtype CT b1 b3.
Global Hint Constructors base_subtype: typ.

Definition wf_base_type (CT : class_table) (b : base_type) : Prop :=
  match b with
  | TInt => True
  | TRef C => C < dom CT
  end.

Definition wf_qualified_base (CT : class_table) (T : qualified_type) : Prop :=
  match sbase T with
  | TInt => sqtype T = Imm
  | TRef C => C < dom CT
  end.

(* Qualified type subtyping *)
Inductive qualified_type_subtype : class_table -> qualified_type -> qualified_type -> Prop :=
  | qtype_sub : forall CT qt1 qt2
      (Hwf1   : wf_qualified_base CT qt1)
      (Hwf2   : wf_qualified_base CT qt2)
      (Hqsub  : q_subtype (sqtype qt1) (sqtype qt2))
      (Hbsub  : base_subtype CT (sbase qt1) (sbase qt2)),
      qualified_type_subtype CT qt1 qt2
  | qtype_trans : forall CT qt1 qt2 qt3
      (Hsub12 : qualified_type_subtype CT qt1 qt2)
      (Hsub23 : qualified_type_subtype CT qt2 qt3),
      qualified_type_subtype CT qt1 qt3
  | qtype_refl : forall CT qt
      (Hwf       : wf_qualified_base CT qt)
      (Hnot_lost : sqtype qt <> Lost),
      qualified_type_subtype CT qt qt.

Lemma qualified_type_subtype_base_subtype :
  forall CT qt1 qt2,
    qualified_type_subtype CT qt1 qt2 ->
    base_subtype CT (sbase qt1) (sbase qt2).
Proof.
  intros CT qt1 qt2 H.
  induction H.
  - exact Hbsub.
  - eapply base_trans; eauto.
  - destruct qt as [q b].
    destruct b as [|C]; simpl in Hwf.
    + apply base_int.
    + apply base_ref.
      apply class_refl; exact Hwf.
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

Lemma class_subtype_domain : forall CT C D,
  class_subtype CT C D ->
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

Lemma base_subtype_domain : forall CT C D,
  base_subtype CT C D ->
  wf_base_type CT C /\ wf_base_type CT D.
Proof.
  intros CT C D Hsub.
  induction Hsub.
  - split; exact I.
  - destruct (class_subtype_domain CT C D H) as [HC HD].
    split; simpl; assumption.
  - destruct IHHsub1 as [HC HD].
    destruct IHHsub2 as [_ HE].
    split; auto.
Qed.

Lemma base_subtype_from_ref : forall CT C b,
  base_subtype CT (TRef C) b ->
  exists D, b = TRef D /\ class_subtype CT C D.
Proof.
  intros CT C b Hsub.
  remember (TRef C) as start eqn:Hstart.
  revert C Hstart.
  induction Hsub; intros C0 Hstart.
  - discriminate Hstart.
  - inversion Hstart; subst.
    exists D.
    split; [reflexivity | exact H].
  - destruct (IHHsub1 _ Hstart) as [D [Hb2 HCD]].
    subst b2.
    destruct (IHHsub2 _ eq_refl) as [E [Hb3 HDE]].
    exists E.
    split; [exact Hb3 | eapply class_trans; eauto].
Qed.

Lemma base_subtype_from_int : forall CT b,
  base_subtype CT TInt b ->
  b = TInt.
Proof.
  intros CT b Hsub.
  remember TInt as start eqn:Hstart.
  revert Hstart.
  induction Hsub; intros Hstart.
  - reflexivity.
  - discriminate Hstart.
  - pose proof (IHHsub1 Hstart) as Hb2.
    subst b2.
    pose proof (IHHsub2 Hstart) as Hb3.
    rewrite Hb3.
    reflexivity.
Qed.
