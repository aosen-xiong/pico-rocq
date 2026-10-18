From Stdlib Require Import List.
Import ListNotations.

Require Import Syntax.
Require Import MemoryModels.JAM.JamEvents MemoryModels.JAM.JamHistory
  MemoryModels.JAM.JamLegality.
Require Import MemoryModels.JMM.FinalFieldPublication
  MemoryModels.JMM.JamPublicationExecution.

(** * A Narrow JLS Final-Field and Cache Fragment

    This module isolates the Java-side actions needed by the derived-cache
    theorem: constructor completion freezes a final-field snapshot, a reference
    is published, each invoking thread dereferences that reference, and plain
    field accesses (cache accesses and reads of final fields) are checked by
    the plain JAM semantics.

    [JlsDereferenceReference] records the JLS final-field observation boundary;
    it is not a Java acquire-mode access.  This fragment deliberately omits the
    full JMM causality, happens-before, synchronization-order, and dereference-
    chain definitions.  Its simulation theorem is therefore a scoped adequacy
    result for executions satisfying this fragment, not full JMM adequacy. *)

Inductive jls_cache_action : Type :=
  | JlsConstructorReturn (loc : Loc) (snapshot : final_snapshot)
      (initial_events : list jam_event)
  | JlsPublishReference (loc : Loc)
  | JlsDereferenceReference (observer : nat) (loc : Loc)
      (snapshot : final_snapshot)
  | JlsPlainAccess (event : jam_event).

Fixpoint jls_cache_jam_events
    (actions : list jls_cache_action) : list jam_event :=
  match actions with
  | [] => []
  | JlsConstructorReturn _ _ initial_events :: tail =>
      initial_events ++ jls_cache_jam_events tail
  | JlsPlainAccess event :: tail => event :: jls_cache_jam_events tail
  | _ :: tail => jls_cache_jam_events tail
  end.

Definition jls_cache_jam_execution
    (actions : list jls_cache_action)
    (reads_from : jam_event -> jam_event -> Prop) : jam_execution :=
  mkJamExecution (jls_cache_jam_events actions) reads_from.

Definition jls_cache_action_before
    (first second : jls_cache_action)
    (actions : list jls_cache_action) : Prop :=
  exists prefix middle suffix,
    actions = prefix ++ first :: middle ++ second :: suffix.

(** Exact state effects for the fragment. Constructor return performs the JLS
    freeze action; publication and dereference are legal only in that order. *)
Inductive jls_cache_publication_step :
    final_publication_state -> jls_cache_action ->
    final_publication_state -> Prop :=
  | JlsCacheConstructorReturn : forall state loc snapshot initial_events,
      frozen_snapshot_lookup loc (fps_frozen state) = None ->
      jls_cache_publication_step state
        (JlsConstructorReturn loc snapshot initial_events)
        (mkFinalPublicationState
          ((loc, snapshot) :: fps_frozen state)
          (fps_published state) (fps_observed state))
  | JlsCachePublishReference : forall state loc snapshot,
      final_snapshot_frozen state loc snapshot ->
      jls_cache_publication_step state (JlsPublishReference loc)
        (mkFinalPublicationState
          (fps_frozen state) (loc :: fps_published state)
          (fps_observed state))
  | JlsCacheDereferenceReference : forall state observer loc snapshot,
      final_location_published state loc ->
      final_snapshot_frozen state loc snapshot ->
      jls_cache_publication_step state
        (JlsDereferenceReference observer loc snapshot)
        (mkFinalPublicationState
          (fps_frozen state) (fps_published state)
          ((observer, loc, snapshot) :: fps_observed state))
  | JlsCachePlainAccess : forall state event,
      jls_cache_publication_step state (JlsPlainAccess event) state.

Inductive jls_cache_publication_replay :
    final_publication_state -> list jls_cache_action ->
    final_publication_state -> Prop :=
  | JlsCacheReplayNil : forall state,
      jls_cache_publication_replay state [] state
  | JlsCacheReplayCons : forall state middle final action tail,
      jls_cache_publication_step state action middle ->
      jls_cache_publication_replay middle tail final ->
      jls_cache_publication_replay state (action :: tail) final.

Record jls_cache_execution_legal
    (actions : list jls_cache_action)
    (reads_from : jam_event -> jam_event -> Prop)
    (final : final_publication_state) : Prop := {
  jls_cache_publication_is_legal :
    jls_cache_publication_replay empty_final_publication_state actions final;

  jls_cache_jam_is_plain_legal :
    jam_plain_legal (jls_cache_jam_execution actions reads_from);

  jls_cache_accesses_follow_dereference : forall event,
    In event (jls_cache_jam_events actions) ->
    jam_event_kind event <> JamInit ->
    exists snapshot,
      jls_cache_action_before
        (JlsDereferenceReference (jam_event_thread event)
          (fst (jam_event_addr event)) snapshot)
        (JlsPlainAccess event) actions
  ;

  jls_cache_constructor_initializations : forall loc snapshot initial_events,
    In (JlsConstructorReturn loc snapshot initial_events) actions ->
    Forall
      (fun event =>
        jam_event_kind event = JamInit /\
        jam_event_mode event = JamPlain /\
        fst (jam_event_addr event) = loc)
      initial_events
}.

(** Constructor return expands to explicit construction, its initialization
    accesses, and then freeze. Other actions translate one-for-one. *)
Fixpoint jls_cache_to_combined
    (actions : list jls_cache_action) : list combined_memory_action :=
  match actions with
  | [] => []
  | JlsConstructorReturn loc snapshot initial_events :: tail =>
      CombinedConstruct loc snapshot ::
        map CombinedAccess initial_events ++
        CombinedFreeze loc snapshot :: jls_cache_to_combined tail
  | JlsPublishReference loc :: tail =>
      CombinedPublish loc :: jls_cache_to_combined tail
  | JlsDereferenceReference observer loc snapshot :: tail =>
      CombinedAcquire observer loc snapshot :: jls_cache_to_combined tail
  | JlsPlainAccess event :: tail =>
      CombinedAccess event :: jls_cache_to_combined tail
  end.

Lemma jls_cache_to_combined_app : forall prefix suffix,
  jls_cache_to_combined (prefix ++ suffix) =
  jls_cache_to_combined prefix ++ jls_cache_to_combined suffix.
Proof.
  intros prefix suffix.
  induction prefix as [|action prefix IH]; simpl; [reflexivity |].
  destruct action; simpl; rewrite IH; try reflexivity.
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma combined_jam_events_access_map : forall events tail,
  combined_jam_events (map CombinedAccess events ++ tail) =
  events ++ combined_jam_events tail.
Proof.
  intros events.
  induction events as [|event events IH]; intros tail; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma jls_cache_jam_projection : forall actions,
  combined_jam_events (jls_cache_to_combined actions) =
  jls_cache_jam_events actions.
Proof.
  intros actions.
  induction actions as [|action actions IH]; simpl; [reflexivity |].
  destruct action; simpl.
  - rewrite combined_jam_events_access_map. simpl.
    exact (f_equal (fun tail => initial_events ++ tail) IH).
  - exact IH.
  - exact IH.
  - f_equal. exact IH.
Qed.

Lemma combined_publication_replay_accesses : forall state events tail final,
  combined_publication_replay state tail final ->
  combined_publication_replay state
    (map CombinedAccess events ++ tail) final.
Proof.
  intros state events.
  induction events as [|event events IH]; intros tail final Hreplay; simpl.
  - exact Hreplay.
  - eapply CombinedPublicationReplayCons.
    + constructor.
    + eapply IH. exact Hreplay.
Qed.

Lemma jls_cache_publication_replay_translates :
  forall initial actions final
    (Hreplay : jls_cache_publication_replay initial actions final),
    combined_publication_replay initial
      (jls_cache_to_combined actions) final.
Proof.
  intros initial actions final Hreplay.
  induction Hreplay.
  - constructor.
  - inversion H; subst; simpl.
    + eapply CombinedPublicationReplayCons with (middle := state).
      * constructor.
      * eapply combined_publication_replay_accesses.
        eapply CombinedPublicationReplayCons.
        -- eapply CombinedPublicationFreeze. exact H0.
        -- exact IHHreplay.
    + eapply CombinedPublicationReplayCons.
      * eapply CombinedPublicationPublish. exact H0.
      * exact IHHreplay.
    + eapply CombinedPublicationReplayCons.
      * eapply CombinedPublicationAcquire; eassumption.
      * exact IHHreplay.
    + eapply CombinedPublicationReplayCons.
      * eapply CombinedPublicationAccess.
      * exact IHHreplay.
Qed.

Lemma combined_action_before_cons : forall head first second tail,
  combined_action_before first second tail ->
  combined_action_before first second (head :: tail).
Proof.
  intros head first second tail Hbefore.
  destruct Hbefore as [prefix [middle [suffix Heq]]].
  exists (head :: prefix), middle, suffix.
  simpl. rewrite Heq. reflexivity.
Qed.

Lemma combined_action_before_prefix : forall prefix first second tail,
  combined_action_before first second tail ->
  combined_action_before first second (prefix ++ tail).
Proof.
  intros prefix first second tail Hbefore.
  induction prefix as [|head prefix IH]; simpl; [exact Hbefore |].
  apply combined_action_before_cons. exact IH.
Qed.

Lemma jls_cache_freezes_follow_construction : forall actions loc snapshot,
  In (CombinedFreeze loc snapshot) (jls_cache_to_combined actions) ->
  combined_action_before
    (CombinedConstruct loc snapshot) (CombinedFreeze loc snapshot)
    (jls_cache_to_combined actions).
Proof.
  intros actions.
  induction actions as [|action actions IH]; intros loc snapshot Hin;
    [contradiction |].
  destruct action as [constructed_loc constructed_snapshot initial_events
    | published_loc
    | observer observed_loc observed_snapshot
    | event]; simpl in Hin.
  - destruct Hin as [Hfalse | Hin]; [discriminate |].
    apply in_app_or in Hin. destruct Hin as [Hin_initial | [Heq | Hin]].
    + apply in_map_iff in Hin_initial.
      destruct Hin_initial as [event [Heq _]]. discriminate.
    + inversion Heq; subst.
      exists [], (map CombinedAccess initial_events),
        (jls_cache_to_combined actions). reflexivity.
    + apply combined_action_before_cons.
      change (combined_action_before
        (CombinedConstruct loc snapshot) (CombinedFreeze loc snapshot)
        (map CombinedAccess initial_events ++
          CombinedFreeze constructed_loc constructed_snapshot ::
          jls_cache_to_combined actions)).
      destruct (IH loc snapshot Hin) as
        [prefix [middle [suffix Heq]]].
      exists
        (map CombinedAccess initial_events ++
          CombinedFreeze constructed_loc constructed_snapshot :: prefix),
        middle, suffix.
      rewrite Heq. rewrite <- app_assoc. reflexivity.
  - destruct Hin as [Hfalse | Hin]; [discriminate |].
    apply combined_action_before_cons. eapply IH. exact Hin.
  - destruct Hin as [Hfalse | Hin]; [discriminate |].
    apply combined_action_before_cons. eapply IH. exact Hin.
  - destruct Hin as [Hfalse | Hin]; [discriminate |].
    apply combined_action_before_cons. eapply IH. exact Hin.
Qed.

Lemma jls_cache_dereference_before_access_translates :
  forall actions observer loc snapshot event,
    jls_cache_action_before
      (JlsDereferenceReference observer loc snapshot)
      (JlsPlainAccess event) actions ->
    combined_action_before
      (CombinedAcquire observer loc snapshot)
      (CombinedAccess event) (jls_cache_to_combined actions).
Proof.
  intros actions observer loc snapshot event Hbefore.
  destruct Hbefore as [prefix [middle [suffix Heq]]].
  subst actions.
  unfold combined_action_before.
  exists (jls_cache_to_combined prefix),
    (jls_cache_to_combined middle), (jls_cache_to_combined suffix).
  rewrite !jls_cache_to_combined_app. simpl.
  rewrite jls_cache_to_combined_app. simpl.
  repeat rewrite app_assoc. reflexivity.
Qed.

(** Every legal execution of the supported JLS fragment induces a legal
    combined publication/JAM execution. *)
Theorem jls_cache_execution_simulates_combined :
  forall actions reads_from final
    (Hlegal : jls_cache_execution_legal actions reads_from final),
    combined_memory_execution_legal
      (jls_cache_to_combined actions) reads_from final.
Proof.
  intros actions reads_from final Hlegal.
  refine {| combined_publication_is_legal := _;
            combined_jam_is_plain_legal := _;
            combined_freezes_follow_construction := _;
            combined_accesses_follow_acquire := _ |}.
  - eapply jls_cache_publication_replay_translates.
    exact (jls_cache_publication_is_legal actions reads_from final Hlegal).
  - unfold combined_jam_execution, jls_cache_jam_execution.
    rewrite jls_cache_jam_projection.
    exact (jls_cache_jam_is_plain_legal actions reads_from final Hlegal).
  - eapply jls_cache_freezes_follow_construction.
  - intros event Hin Hnot_init.
    rewrite jls_cache_jam_projection in Hin.
    destruct (jls_cache_accesses_follow_dereference
      actions reads_from final Hlegal event Hin Hnot_init)
      as [snapshot Hbefore].
    exists snapshot.
    eapply jls_cache_dereference_before_access_translates.
    exact Hbefore.
Qed.
