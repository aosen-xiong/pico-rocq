From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall.

(** No object has a lost qualifier.  A dynamized static type may contain
    [Lost], and the value-typing relation matches such a position against any
    stored qualifier.  This file shows that the relation says the same as:
    some reading of the type, in which every [Lost] is replaced by a mutable,
    immutable or readonly qualifier, describes the object exactly. *)

(** [reading R R']: [R'] is [R] with each [Lost] replaced by [Mut], [Imm] or
    [RO], and nothing else changed. *)
Inductive reading : rtype -> rtype -> Prop :=
  | rd_class : forall q0 q' C Us Us'
      (Hq : q0 = q' \/ (q0 = Lost /\ (q' = Mut \/ q' = Imm \/ q' = RO)))
      (Hargs : Forall2 reading Us Us'),
      reading (RClass q0 C Us) (RClass q' C Us').

Lemma Forall2_swap : forall (A B : Type) (P : A -> B -> Prop) (Q : B -> A -> Prop) l1 l2,
  (forall a b, P a b -> Q b a) -> Forall2 P l1 l2 -> Forall2 Q l2 l1.
Proof. intros A B P Q l1 l2 HPQ H. induction H; constructor; auto. Qed.

Lemma rarg_sub_reading : forall R' R, rarg_sub R' R -> reading R R'.
Proof.
  intros R' R H. induction H using rarg_sub_ind'.
  constructor; [exact H|].
  eapply Forall2_swap; [|eassumption]. intros a b Hab. exact Hab.
Qed.

Lemma reading_rarg_sub : forall R R', reading R R' -> rarg_sub R' R.
Proof.
  intros R. induction R using rtype_ind'. intros R' Hr.
  inversion Hr; subst. constructor; [exact Hq|].
  clear Hr Hq. revert Us' Hargs.
  induction H; intros Us' Hargs; inversion Hargs; subst; constructor; auto.
Qed.

(** The object at [ι] is described exactly by [R]: its mutability is seen as
    itself or as readonly, and its type arguments, viewed at the class of
    [R], are the arguments of [R]. *)
Definition loc_has_exact (CT : class_table) (h : heap) (ι : Loc) (R : rtype) : Prop :=
  match runtime_getObj h ι, R with
  | Some o, RClass rq D Us =>
      (rq = RO \/ rq = qr2q (rqtype (rt_type o))) /\
      rsuper_inst CT (qr2q (rqtype (rt_type o)))
        (rctype (rt_type o)) (rtargs (rt_type o)) D Us
  | _, _ => False
  end.

(** For an object with a well-formed header, value typing against a type
    that may contain [Lost] is exact typing against some lost-free reading
    of it. *)
Theorem lost_is_some_reading : forall CT h ι o R,
  wf_class_table CT ->
  runtime_getObj h ι = Some o ->
  wf_rtypeuse CT (rt_type o) ->
  (loc_has_rtype CT h ι R <->
   exists R', reading R R' /\ rlost_free R' /\ loc_has_exact CT h ι R').
Proof.
  intros CT h ι o R Hct Ho Hwf.
  destruct o as [[qr C Rs] fs]. destruct R as [rq D Us].
  unfold loc_has_rtype, loc_has_exact. rewrite Ho. cbn [rt_type rqtype rctype rtargs] in *.
  split.
  - intros [Hhead (Vs & Hsup & Hle)].
    pose proof (rsuper_wf _ _ _ _ _ _ Hct Hsup Hwf) as HwfD.
    unfold wf_rtypeuse in HwfD. simpl in HwfD.
    destruct (find_class CT D) as [defD|]; [|contradiction].
    destruct HwfD as (_ & Hlf & _).
    assert (Hrd : Forall2 reading Us Vs).
    { eapply Forall2_swap; [|exact Hle]. intros a b. apply rarg_sub_reading. }
    destruct Hhead as [-> | [-> | ->]].
    + exists (RClass RO D Vs). split; [constructor; [left; reflexivity | exact Hrd]|].
      split; [apply rlost_free_class; split; [discriminate | exact Hlf]|].
      split; [left; reflexivity | exact Hsup].
    + exists (RClass RO D Vs). split; [constructor; [right; auto | exact Hrd]|].
      split; [apply rlost_free_class; split; [discriminate | exact Hlf]|].
      split; [left; reflexivity | exact Hsup].
    + exists (RClass (qr2q qr) D Vs). split; [constructor; [left; reflexivity | exact Hrd]|].
      split; [apply rlost_free_class; split; [destruct qr; discriminate | exact Hlf]|].
      split; [right; reflexivity | exact Hsup].
  - intros (R' & Hrd & _ & Hex). destruct R' as [q' D' Us'].
    inversion Hrd; subst. destruct Hex as [Hh Hsup].
    split.
    + unfold head_ok. destruct Hq as [-> | [-> _]]; [|auto].
      destruct Hh as [-> | ->]; auto.
    + exists Us'. split; [exact Hsup|].
      eapply Forall2_swap; [|exact Hargs]. intros a b. apply reading_rarg_sub.
Qed.

Print Assumptions lost_is_some_reading.
