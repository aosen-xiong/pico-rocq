Require Import Syntax Notations LibTactics Tactics Helpers.
Require Import List.
Require Import Stdlib.Classes.RelationClasses.
Import ListNotations.

(* Qualifier ordering  *)
Inductive q_subtype : q -> q -> Prop :=
  | q_refl : forall q1,
      q1 <> Lost ->
      q_subtype q1 q1
  | q_rd : forall q1,
      q_subtype q1 Rd
  | q_bot: forall q1,
      q_subtype Bot q1
where "q1 ⊑ q2" := (q_subtype q1 q2).
Global Hint Constructors q_subtype: typ.

(* Example q_subtype_refl: forall q, q <> Lost -> q ⊑ q. *)
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
  | base_refl : forall (CT : class_table) (C : class_name),
      (* Reflexivity of base subtyping *)
      C < dom CT ->
      base_subtype CT C C
  | base_trans : forall (CT : class_table) (C D E : class_name),
      base_subtype CT C D ->
      base_subtype CT D E -> 
      base_subtype CT C E
  | base_extends : forall (CT : class_table) (C D : class_name),
      C < dom CT ->
      D < dom CT ->
      parent_lookup CT C = Some D ->
      base_subtype CT C D.
Global Hint Constructors base_subtype: typ.

(* Qualified type subtyping *)
Inductive qualified_type_subtype : class_table -> qualified_type -> qualified_type -> Prop :=
  | qtype_sub : forall CT qt1 qt2,
	 		(sctype qt1) < (dom CT) ->
      (sctype qt2) < (dom CT) ->
      q_subtype (sqtype qt1) (sqtype qt2) ->
      base_subtype CT (sctype qt1) (sctype qt2) ->
      qualified_type_subtype CT qt1 qt2
  | qtype_trans: forall CT qt1 qt2 qt3,
      qualified_type_subtype CT qt1 qt2 ->
      qualified_type_subtype CT qt2 qt3 ->
      qualified_type_subtype CT qt1 qt3
  | qtype_refl: forall CT qt,
      (sctype qt) < (dom CT) ->
      sqtype qt <> Lost ->
      qualified_type_subtype CT qt qt.

Lemma qualified_type_subtype_dom2 :
  forall CT qt1 qt2,
    qualified_type_subtype CT qt1 qt2 ->
    sctype qt2 < dom CT.
Proof.
  intros CT qt1 qt2 H.
  induction H.
  - assumption.
  - exact IHqualified_type_subtype2.
  - assumption.
Qed.

Lemma qualified_type_subtype_dom1 :
  forall CT qt1 qt2,
    qualified_type_subtype CT qt1 qt2 ->
    sctype qt1 < dom CT.
Proof.
  intros CT qt1 qt2 H.
  induction H.
  - assumption.
  - exact IHqualified_type_subtype1.
  - assumption.
Qed.

Lemma qualified_type_subtype_base_subtype :
  forall CT qt1 qt2,
    qualified_type_subtype CT qt1 qt2 ->
    base_subtype CT (sctype qt1) (sctype qt2).
Proof.
    intros CT qt1 qt2 H.
    induction H.
    generalize dependent qt1.
    generalize dependent qt2.
    - intros. exact H2.
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
  - (* qtype_sub case *)
    intros. exact H1.
  - (* qtype_trans case *)
  eapply q_subtype_trans; eauto.
  - (* qtype_refl case *)
    intros. 
    destruct qt as [q c]; simpl.
    destruct q; try (apply q_refl; discriminate).
    exfalso.
    simpl in H0.
    apply H0.
    reflexivity.
Qed.

Lemma base_subtype_domain : forall CT C D,
  base_subtype CT C D ->
  C < dom CT /\ D < dom CT.
Proof.
  intros CT C D Hsub.
  induction Hsub.
  - (* Reflexive *) 
    split; exact H. (* Need to extract from wf_class_table *)
  - (* Transitive *)
    destruct IHHsub1 as [HC HD].
    destruct IHHsub2 as [_ HE].
    split; auto.
  - split; auto.
Qed.