From Stdlib Require Import List PeanoNat.
Import ListNotations.

Require Import Syntax.

(** * Final-Field Freeze and Publication Interface

    This small operational model captures the publication guarantee required
    by the cache development.  A location is frozen with one final-field
    snapshot before it may be published; an observer may acquire only a
    published location and receives that frozen snapshot.

    The model is an adequacy target for JLS final-field semantics.  It is not a
    formalization of Java constructors, dereference chains, or JMM executions. *)

Definition final_snapshot : Type := list value.

(** [frozen_snapshot_lookup loc frozen] returns the unique snapshot recorded
    when [loc] was frozen.  [FinalFreeze] prevents duplicate entries. *)
Fixpoint frozen_snapshot_lookup
    (loc : Loc) (frozen : list (Loc * final_snapshot)) :
    option final_snapshot :=
  match frozen with
  | [] => None
  | (candidate, snapshot) :: tail =>
      if Nat.eqb candidate loc
      then Some snapshot
      else frozen_snapshot_lookup loc tail
  end.

Record final_publication_state : Type := mkFinalPublicationState {
  fps_frozen : list (Loc * final_snapshot);
  fps_published : list Loc;
  fps_observed : list (nat * Loc * final_snapshot)
}.

Definition empty_final_publication_state : final_publication_state :=
  mkFinalPublicationState [] [] [].

Definition final_snapshot_frozen
    (state : final_publication_state) (loc : Loc)
    (snapshot : final_snapshot) : Prop :=
  frozen_snapshot_lookup loc (fps_frozen state) = Some snapshot.

(** Publication makes a previously frozen location available to observers. *)
Definition final_location_published
    (state : final_publication_state) (loc : Loc) : Prop :=
  In loc (fps_published state).

(** An observation records the snapshot obtained by one abstract observer.
    [FinalAcquire] predates the Java-facing fragment; its name does not denote
    a Java acquire-mode access. *)
Definition final_snapshot_observed
    (state : final_publication_state) (observer : nat) (loc : Loc)
    (snapshot : final_snapshot) : Prop :=
  In (observer, loc, snapshot) (fps_observed state).

(** Primitive publication actions.  Their premises encode the intended order:
    freeze precedes publish, and publish precedes acquire. *)
Inductive final_publication_step :
    final_publication_state -> final_publication_state -> Prop :=
  | FinalFreeze : forall state loc snapshot,
      frozen_snapshot_lookup loc (fps_frozen state) = None ->
      final_publication_step state
        (mkFinalPublicationState
          ((loc, snapshot) :: fps_frozen state)
          (fps_published state)
          (fps_observed state))
  | FinalPublish : forall state loc snapshot,
      final_snapshot_frozen state loc snapshot ->
      final_publication_step state
        (mkFinalPublicationState
          (fps_frozen state)
          (loc :: fps_published state)
          (fps_observed state))
  | FinalAcquire : forall state observer loc snapshot,
      final_location_published state loc ->
      final_snapshot_frozen state loc snapshot ->
      final_publication_step state
        (mkFinalPublicationState
          (fps_frozen state)
          (fps_published state)
          ((observer, loc, snapshot) :: fps_observed state)).

Inductive final_publication_steps :
    final_publication_state -> final_publication_state -> Prop :=
  | FinalPublicationStepsRefl : forall state,
      final_publication_steps state state
  | FinalPublicationStepsStep : forall first middle last,
      final_publication_step first middle ->
      final_publication_steps middle last ->
      final_publication_steps first last.

Lemma final_publication_steps_trans : forall first middle last,
  final_publication_steps first middle ->
  final_publication_steps middle last ->
  final_publication_steps first last.
Proof.
  intros first middle last Hfirst Hlast.
  induction Hfirst.
  - exact Hlast.
  - eapply FinalPublicationStepsStep; eauto.
Qed.

(** Every acquired observation agrees with the immutable frozen snapshot. *)
Definition final_publication_consistent
    (state : final_publication_state) : Prop :=
  forall observer loc snapshot,
    final_snapshot_observed state observer loc snapshot ->
    final_snapshot_frozen state loc snapshot.

Lemma frozen_snapshot_lookup_same : forall loc snapshot frozen,
  frozen_snapshot_lookup loc ((loc, snapshot) :: frozen) = Some snapshot.
Proof.
  intros loc snapshot frozen. simpl.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma frozen_snapshot_lookup_other : forall target loc snapshot frozen,
  target <> loc ->
  frozen_snapshot_lookup target ((loc, snapshot) :: frozen) =
  frozen_snapshot_lookup target frozen.
Proof.
  intros target loc snapshot frozen Hneq. simpl.
  destruct (Nat.eqb loc target) eqn:Heq.
  - apply Nat.eqb_eq in Heq. symmetry in Heq. contradiction.
  - reflexivity.
Qed.

Lemma final_freeze_preserves_existing_snapshot :
  forall state state' target snapshot
    (Hstep : final_publication_step state state')
    (Hfrozen : final_snapshot_frozen state target snapshot),
    final_snapshot_frozen state' target snapshot.
Proof.
  intros state state' target snapshot Hstep Hfrozen.
  inversion Hstep; subst; unfold final_snapshot_frozen in *.
  - cbn.
    destruct (Nat.eqb loc target) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst loc.
      rewrite Hfrozen in H. discriminate.
    + exact Hfrozen.
  - exact Hfrozen.
  - exact Hfrozen.
Qed.

Lemma final_publication_step_preserves_consistency :
  forall state state'
    (Hconsistent : final_publication_consistent state)
    (Hstep : final_publication_step state state'),
    final_publication_consistent state'.
Proof.
  intros state state' Hconsistent Hstep observer target snapshot Hobserved.
  inversion Hstep; subst; simpl in Hobserved.
  - eapply final_freeze_preserves_existing_snapshot.
    + exact Hstep.
    + eapply Hconsistent. exact Hobserved.
  - eapply Hconsistent. exact Hobserved.
  - destruct Hobserved as [Heq | Hobserved].
    + inversion Heq; subst. assumption.
    + eapply Hconsistent. exact Hobserved.
Qed.

Theorem final_publication_steps_preserve_consistency :
  forall initial final
    (Hconsistent : final_publication_consistent initial)
    (Hsteps : final_publication_steps initial final),
    final_publication_consistent final.
Proof.
  intros initial final Hconsistent Hsteps.
  induction Hsteps.
  - exact Hconsistent.
  - apply IHHsteps.
    eapply final_publication_step_preserves_consistency; eauto.
Qed.

Lemma empty_final_publication_consistent :
  final_publication_consistent empty_final_publication_state.
Proof.
  intros observer loc snapshot Hobserved.
  inversion Hobserved.
Qed.

(** Starting from the empty state, every observer acquisition is grounded in
    the frozen snapshot for the acquired location. *)
Theorem acquired_final_snapshot_is_frozen :
  forall final observer loc snapshot
    (Hsteps : final_publication_steps empty_final_publication_state final)
    (Hobserved : final_snapshot_observed final observer loc snapshot),
    final_snapshot_frozen final loc snapshot.
Proof.
  intros final observer loc snapshot Hsteps Hobserved.
  pose proof (final_publication_steps_preserve_consistency
    empty_final_publication_state final
    empty_final_publication_consistent Hsteps) as Hconsistent.
  eapply Hconsistent. exact Hobserved.
Qed.
