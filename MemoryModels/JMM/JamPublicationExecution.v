From Stdlib Require Import List PeanoNat.
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

(** ** Reads of final fields

    The snapshot of a frozen location lists the values of its final fields,
    in the order given by [final_fields loc]. *)
Definition snapshot_field_value
    (fields : list var) (snapshot : final_snapshot) (f : var) (v : value) :
    Prop :=
  exists i, nth_error fields i = Some f /\ nth_error snapshot i = Some v.

(** Constructor discipline for final fields: each final field of a frozen
    location has exactly one write in the whole execution.  It is an
    initialization, it occurs before the freeze, and the snapshot records its
    value.  In particular, no final field is written after its freeze. *)
Definition combined_final_fields_initialized
    (final_fields : Loc -> list var)
    (actions : list combined_memory_action) : Prop :=
  forall loc snapshot f,
    In (CombinedFreeze loc snapshot) actions ->
    In f (final_fields loc) ->
    exists init,
      In init (combined_jam_events actions) /\
      jam_event_kind init = JamInit /\
      jam_event_addr init = (loc, f) /\
      combined_action_before (CombinedAccess init)
        (CombinedFreeze loc snapshot) actions /\
      snapshot_field_value (final_fields loc) snapshot f
        (jam_event_value init) /\
      forall write,
        In write (combined_jam_events actions) ->
        jam_is_write write ->
        jam_event_addr write = (loc, f) ->
        write = init.

Lemma combined_publication_action_step_preserves_frozen :
  forall state action state' loc snapshot,
    combined_publication_action_step state action state' ->
    final_snapshot_frozen state loc snapshot ->
    final_snapshot_frozen state' loc snapshot.
Proof.
  intros state action state' loc snapshot Hstep Hfrozen.
  inversion Hstep; subst; unfold final_snapshot_frozen in *; simpl;
    try exact Hfrozen.
  destruct (Nat.eqb loc0 loc) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst loc0.
    rewrite Hfrozen in H. discriminate.
  - exact Hfrozen.
Qed.

Lemma combined_publication_replay_preserves_frozen :
  forall state actions final loc snapshot,
    combined_publication_replay state actions final ->
    final_snapshot_frozen state loc snapshot ->
    final_snapshot_frozen final loc snapshot.
Proof.
  intros state actions final loc snapshot Hreplay.
  induction Hreplay as [state | state middle final action tail Hstep Htail IH];
    intros Hfrozen; [exact Hfrozen |].
  apply IH. eapply combined_publication_action_step_preserves_frozen; eauto.
Qed.

(** A freeze in the trace determines the final frozen snapshot. *)
Lemma combined_publication_replay_freeze_frozen :
  forall state actions final loc snapshot,
    combined_publication_replay state actions final ->
    In (CombinedFreeze loc snapshot) actions ->
    final_snapshot_frozen final loc snapshot.
Proof.
  intros state actions final loc snapshot Hreplay.
  induction Hreplay as [state | state middle final action tail Hstep Htail IH];
    intros Hin; [contradiction |].
  destruct Hin as [-> | Hin]; [| exact (IH Hin)].
  inversion Hstep; subst.
  eapply combined_publication_replay_preserves_frozen; [exact Htail |].
  unfold final_snapshot_frozen. simpl. apply frozen_snapshot_lookup_same.
Qed.

(** Every frozen snapshot of a replay from the empty state comes from a
    freeze action in the trace. *)
Lemma combined_publication_replay_frozen_has_freeze :
  forall state actions final loc snapshot,
    combined_publication_replay state actions final ->
    final_snapshot_frozen final loc snapshot ->
    final_snapshot_frozen state loc snapshot \/
    In (CombinedFreeze loc snapshot) actions.
Proof.
  intros state actions final loc snapshot Hreplay.
  induction Hreplay as [state | state middle final action tail Hstep Htail IH];
    intros Hfrozen; [left; exact Hfrozen |].
  destruct (IH Hfrozen) as [Hmiddle | Hin]; [| right; right; exact Hin].
  inversion Hstep; subst; unfold final_snapshot_frozen in *; simpl in Hmiddle;
    try (left; exact Hmiddle).
  destruct (Nat.eqb loc0 loc) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst loc0.
    injection Hmiddle as ->. right. left. reflexivity.
  - left. exact Hmiddle.
Qed.

Lemma combined_publication_replay_preserves_observed :
  forall state actions final observer loc snapshot,
    combined_publication_replay state actions final ->
    final_snapshot_observed state observer loc snapshot ->
    final_snapshot_observed final observer loc snapshot.
Proof.
  intros state actions final observer loc snapshot Hreplay.
  induction Hreplay as [state | state middle final action tail Hstep Htail IH];
    intros Hobserved; [exact Hobserved |].
  apply IH.
  inversion Hstep; subst; unfold final_snapshot_observed in *; simpl;
    auto.
Qed.

Lemma combined_publication_replay_acquire_observed :
  forall state actions final observer loc snapshot,
    combined_publication_replay state actions final ->
    In (CombinedAcquire observer loc snapshot) actions ->
    final_snapshot_observed final observer loc snapshot.
Proof.
  intros state actions final observer loc snapshot Hreplay.
  induction Hreplay as [state | state middle final action tail Hstep Htail IH];
    intros Hin; [contradiction |].
  destruct Hin as [-> | Hin]; [| exact (IH Hin)].
  inversion Hstep; subst.
  eapply combined_publication_replay_preserves_observed; [exact Htail |].
  unfold final_snapshot_observed. simpl. left. reflexivity.
Qed.

Lemma combined_action_before_in_second :
  forall first second actions,
    combined_action_before first second actions ->
    In second actions.
Proof.
  intros first second actions (prefix & middle & suffix & ->).
  apply in_or_app. right. right. apply in_or_app. right. left. reflexivity.
Qed.

Lemma combined_action_before_in_first :
  forall first second actions,
    combined_action_before first second actions ->
    In first actions.
Proof.
  intros first second actions (prefix & middle & suffix & ->).
  apply in_or_app. right. left. reflexivity.
Qed.

(** Final-field guarantee for combined executions.  A plain read of a final
    field comes after its thread acquired the published location, reads from
    the constructor's initialization of that field (which precedes the
    freeze), and returns the value that field has in the snapshot the thread
    acquired, which is also the frozen snapshot. *)
Theorem combined_final_field_read_sees_snapshot :
  forall final_fields actions reads_from final read loc f,
    combined_memory_execution_legal actions reads_from final ->
    combined_final_fields_initialized final_fields actions ->
    In read (combined_jam_events actions) ->
    jam_is_read read ->
    jam_event_addr read = (loc, f) ->
    In f (final_fields loc) ->
    exists snapshot init,
      combined_action_before
        (CombinedAcquire (jam_event_thread read) loc snapshot)
        (CombinedAccess read) actions /\
      final_snapshot_observed final (jam_event_thread read) loc snapshot /\
      final_snapshot_frozen final loc snapshot /\
      jam_reads_from (combined_jam_execution actions reads_from) init read /\
      combined_action_before (CombinedAccess init)
        (CombinedFreeze loc snapshot) actions /\
      snapshot_field_value (final_fields loc) snapshot f
        (jam_event_value read).
Proof.
  intros final_fields actions reads_from final read loc f Hlegal Hinit
    Hin Hread Haddr Hfinal.
  pose proof (combined_publication_is_legal actions reads_from final Hlegal) as Hreplay.
  pose proof (combined_jam_is_plain_legal actions reads_from final Hlegal) as Hjam.
  pose proof (jam_plain_history_wf _ Hjam) as Hwf.
  (* The read follows an acquire by its thread. *)
  assert (Hnot_init : jam_event_kind read <> JamInit).
  { unfold jam_is_read in Hread. rewrite Hread. discriminate. }
  destruct (combined_accesses_follow_acquire actions reads_from final Hlegal
    read Hin Hnot_init) as [snapshot Hbefore].
  rewrite Haddr in Hbefore. simpl in Hbefore.
  pose proof (combined_publication_replay_acquire_observed _ _ _ _ _ _
    Hreplay (combined_action_before_in_first _ _ _ Hbefore)) as Hobserved.
  pose proof (acquired_final_snapshot_is_frozen final _ _ _
    (combined_publication_replay_projects _ _ _ Hreplay) Hobserved) as Hfrozen.
  (* The acquired snapshot is the one recorded by a freeze in the trace. *)
  destruct (combined_publication_replay_frozen_has_freeze _ _ _ _ _
    Hreplay Hfrozen) as [Hempty | Hfreeze].
  { unfold final_snapshot_frozen in Hempty. discriminate. }
  destruct (Hinit loc snapshot f Hfreeze Hfinal) as
    (init & Hinit_in & Hinit_kind & Hinit_addr & Hinit_before & Hinit_value &
      Hunique).
  (* The read reads from the unique write to the final field. *)
  destruct (jam_reads_complete _ Hwf read Hin Hread) as [write Hrf].
  destruct (jam_rf_shapes _ Hwf write read Hrf) as
    (Hwrite & _ & Hsame_loc & Hsame_value).
  destruct (jam_rf_events _ Hwf write read Hrf) as [Hwrite_in _].
  assert (Hwrite_addr : jam_event_addr write = (loc, f)).
  { unfold jam_same_location in Hsame_loc. rewrite Hsame_loc. exact Haddr. }
  pose proof (Hunique write Hwrite_in Hwrite Hwrite_addr) as Heq.
  subst write.
  exists snapshot, init.
  split; [exact Hbefore |].
  split; [exact Hobserved |].
  split; [exact Hfrozen |].
  split; [exact Hrf |].
  split; [exact Hinit_before |].
  unfold jam_same_value in Hsame_value. rewrite <- Hsame_value.
  exact Hinit_value.
Qed.
