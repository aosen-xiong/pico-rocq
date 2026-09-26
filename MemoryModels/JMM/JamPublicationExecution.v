From Stdlib Require Import List.
Import ListNotations.

Require Import Syntax.
Require Import MemoryModels.JAM.JamEvents MemoryModels.JAM.JamHistory
  MemoryModels.JAM.JamLegality.
Require Import MemoryModels.JMM.FinalFieldPublication.

(** * Combined Publication and JAM Executions

    A combined execution is one ordered trace containing object construction,
    final-field publication, and plain field-access events (cache accesses
    and reads of final fields).  Publication replay and
    JAM legality are projections of this trace, so their temporal composition
    is explicit rather than an external conjunction of two executions. *)

Inductive combined_memory_action : Type :=
  | CombinedConstruct (loc : Loc) (snapshot : final_snapshot)
  | CombinedFreeze (loc : Loc) (snapshot : final_snapshot)
  | CombinedPublish (loc : Loc)
  | CombinedAcquire (observer : nat) (loc : Loc)
      (snapshot : final_snapshot)
  | CombinedAccess (event : jam_event).

Fixpoint combined_jam_events
    (actions : list combined_memory_action) : list jam_event :=
  match actions with
  | [] => []
  | CombinedAccess event :: tail => event :: combined_jam_events tail
  | _ :: tail => combined_jam_events tail
  end.

Definition combined_jam_execution
    (actions : list combined_memory_action)
    (reads_from : jam_event -> jam_event -> Prop) : jam_execution :=
  mkJamExecution (combined_jam_events actions) reads_from.

(** [combined_action_before first second actions] uses the order of the
    combined trace, independently of JAM event identifiers. *)
Definition combined_action_before
    (first second : combined_memory_action)
    (actions : list combined_memory_action) : Prop :=
  exists prefix middle suffix,
    actions = prefix ++ first :: middle ++ second :: suffix.

(** One action's effect on final-field publication state.  Construction and
    field accesses do not mutate publication metadata. [CombinedAcquire] is an
    abstract observation action, not a Java acquire-mode access. *)
Inductive combined_publication_action_step :
    final_publication_state -> combined_memory_action ->
    final_publication_state -> Prop :=
  | CombinedPublicationConstruct : forall state loc snapshot,
      combined_publication_action_step state
        (CombinedConstruct loc snapshot) state
  | CombinedPublicationFreeze : forall state loc snapshot,
      frozen_snapshot_lookup loc (fps_frozen state) = None ->
      combined_publication_action_step state
        (CombinedFreeze loc snapshot)
        (mkFinalPublicationState
          ((loc, snapshot) :: fps_frozen state)
          (fps_published state) (fps_observed state))
  | CombinedPublicationPublish : forall state loc snapshot,
      final_snapshot_frozen state loc snapshot ->
      combined_publication_action_step state (CombinedPublish loc)
        (mkFinalPublicationState
          (fps_frozen state) (loc :: fps_published state)
          (fps_observed state))
  | CombinedPublicationAcquire : forall state observer loc snapshot,
      final_location_published state loc ->
      final_snapshot_frozen state loc snapshot ->
      combined_publication_action_step state
        (CombinedAcquire observer loc snapshot)
        (mkFinalPublicationState
          (fps_frozen state) (fps_published state)
          ((observer, loc, snapshot) :: fps_observed state))
  | CombinedPublicationAccess : forall state event,
      combined_publication_action_step state (CombinedAccess event) state.

Inductive combined_publication_replay :
    final_publication_state -> list combined_memory_action ->
    final_publication_state -> Prop :=
  | CombinedPublicationReplayNil : forall state,
      combined_publication_replay state [] state
  | CombinedPublicationReplayCons : forall state middle final action tail,
      combined_publication_action_step state action middle ->
      combined_publication_replay middle tail final ->
      combined_publication_replay state (action :: tail) final.

(** Lifecycle actions erase to an ordinary final-publication execution. *)
Lemma combined_publication_action_is_steps :
  forall initial action final
    (Haction : combined_publication_action_step initial action final),
    final_publication_steps initial final.
Proof.
  intros initial action final Haction.
  inversion Haction; subst.
  - constructor.
  - eapply FinalPublicationStepsStep; [constructor; exact H | constructor].
  - eapply FinalPublicationStepsStep.
    + eapply FinalPublish. exact H.
    + constructor.
  - eapply FinalPublicationStepsStep.
    + eapply FinalAcquire; eauto.
    + constructor.
  - constructor.
Qed.

Theorem combined_publication_replay_projects :
  forall initial actions final
    (Hreplay : combined_publication_replay initial actions final),
    final_publication_steps initial final.
Proof.
  intros initial actions final Hreplay.
  induction Hreplay.
  - constructor.
  - eapply final_publication_steps_trans.
    + eapply combined_publication_action_is_steps. exact H.
    + exact IHHreplay.
Qed.

Record combined_memory_execution_legal
    (actions : list combined_memory_action)
    (reads_from : jam_event -> jam_event -> Prop)
    (final : final_publication_state) : Prop := {
  combined_publication_is_legal :
    combined_publication_replay empty_final_publication_state actions final;

  combined_jam_is_plain_legal :
    jam_plain_legal (combined_jam_execution actions reads_from);

  combined_freezes_follow_construction : forall loc snapshot,
    In (CombinedFreeze loc snapshot) actions ->
    combined_action_before
      (CombinedConstruct loc snapshot) (CombinedFreeze loc snapshot) actions;

  combined_accesses_follow_acquire : forall event,
    In event (combined_jam_events actions) ->
    jam_event_kind event <> JamInit ->
    exists snapshot,
      combined_action_before
        (CombinedAcquire (jam_event_thread event)
          (fst (jam_event_addr event)) snapshot)
        (CombinedAccess event) actions
}.

Theorem combined_memory_execution_publication_projection :
  forall actions reads_from final
    (Hlegal : combined_memory_execution_legal actions reads_from final),
    final_publication_steps empty_final_publication_state final.
Proof.
  intros actions reads_from final Hlegal.
  eapply combined_publication_replay_projects.
  exact (combined_publication_is_legal actions reads_from final Hlegal).
Qed.

Theorem combined_memory_execution_jam_projection :
  forall actions reads_from final
    (Hlegal : combined_memory_execution_legal actions reads_from final),
    jam_plain_legal (combined_jam_execution actions reads_from).
Proof.
  intros actions reads_from final Hlegal.
  exact (combined_jam_is_plain_legal actions reads_from final Hlegal).
Qed.
