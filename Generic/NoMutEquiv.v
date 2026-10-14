From Stdlib Require Import List.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing.

(** The no-mutable-position predicate, read as the absence of a finite path
    to a mutable position.

    [may_mut Δ T] holds when a mutable position is reached from [T] in
    finitely many steps through type arguments and through the declared
    bounds of type variables.  A type variable without a declared bound, and
    a qualified use of a variable whose bound is not a class type, count as
    reaching one; well-formed types have neither.  [no_mut], used by the
    method rule, excludes every such path. *)

Inductive may_mut (Δ : tv_env) : qualified_type -> Prop :=
  | mm_mut : forall C Ts,
      may_mut Δ (TClass Mut C Ts)
  | mm_arg : forall q0 C Ts T
      (Hin : List.In T Ts)
      (Hrec : may_mut Δ T),
      may_mut Δ (TClass q0 C Ts)
  | mm_head_arg : forall n C Ts T
      (Hin : List.In T Ts)
      (Hrec : may_mut Δ T),
      may_mut Δ (THead n C Ts)
  | mm_var : forall o n B
      (Hbound : tv_bound Δ o n = Some B)
      (Hrec : may_mut Δ B),
      may_mut Δ (TVar TVSub o n)
  | mm_unbound : forall u o n
      (Hbound : tv_bound Δ o n = None),
      may_mut Δ (TVar u o n)
  | mm_qvar_mut : forall o n,
      may_mut Δ (TVar (TVQual Mut) o n)
  | mm_qvar_arg : forall q0 o n qb C Ts T
      (Hbound : tv_bound Δ o n = Some (TClass qb C Ts))
      (Hin : List.In T Ts)
      (Hrec : may_mut Δ T),
      may_mut Δ (TVar (TVQual q0) o n)
  | mm_qvar_shape : forall q0 o n B
      (Hbound : tv_bound Δ o n = Some B)
      (Hshape : forall qb C Ts, B <> TClass qb C Ts),
      may_mut Δ (TVar (TVQual q0) o n)
  | mm_pvar_arg : forall m o n qb C Ts T
      (Hbound : tv_bound Δ o n = Some (TClass qb C Ts))
      (Hin : List.In T Ts)
      (Hrec : may_mut Δ T),
      may_mut Δ (TVar (TVPoly m) o n)
  | mm_pvar_shape : forall m o n B
      (Hbound : tv_bound Δ o n = Some B)
      (Hshape : forall qb C Ts, B <> TClass qb C Ts),
      may_mut Δ (TVar (TVPoly m) o n).

Lemma no_mut_not_may_mut : forall Δ T, no_mut Δ T -> ~ may_mut Δ T.
Proof.
  intros Δ T Hn Hm. revert Hn.
  induction Hm; intros Hn; inversion Hn; subst;
    try congruence;
    try (rewrite Hbound in Hbound0; first [discriminate | inversion Hbound0; subst]);
    try (rewrite Forall_forall in Hargs);
    try solve [auto | eapply Hshape; reflexivity].
Qed.

Print Assumptions no_mut_not_may_mut.
