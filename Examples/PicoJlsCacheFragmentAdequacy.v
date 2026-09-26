From Stdlib Require Import List.
Import ListNotations.

Require Import Syntax Typing Core.GenericDerivedCache.
Require Import Examples.PicoIfZeroCacheExamples Examples.PicoConcreteHashModel
  Examples.PicoSemanticConcurrencyExamples
  Examples.PicoSemanticConcurrencySafety Examples.PicoJamHashAdequacy
  Examples.PicoFinalFieldPublicationExamples
  Examples.PicoConstructionPublicationExamples
  Examples.PicoCombinedMemoryExecution.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoConstructionPublication
  PICOBridge.PicoSemanticConcurrency PICOBridge.PicoIrisSemImmLogicalRelation
  PICOBridge.PicoJamSimulation.
Require Import MemoryModels.JAM.JamEvents MemoryModels.JAM.JamHistory.
Require Import MemoryModels.JMM.FinalFieldPublication
  MemoryModels.JMM.JamPublicationExecution
  MemoryModels.JMM.JlsCacheFragment.

(** * Concrete Hash Race in the Narrow JLS Cache Fragment *)

Definition pico_hash_jls_cache_actions : list jls_cache_action :=
  [JlsConstructorReturn pico_hash_concurrent_receiver
     pico_hash_combined_snapshot
     [pico_hash_jam_init; pico_hash_jam_payload_init];
   JlsPublishReference pico_hash_concurrent_receiver;
   JlsDereferenceReference 0 pico_hash_concurrent_receiver
     pico_hash_combined_snapshot;
   JlsDereferenceReference 1 pico_hash_concurrent_receiver
     pico_hash_combined_snapshot;
   JlsPlainAccess pico_hash_jam_read0;
   JlsPlainAccess pico_hash_jam_read1;
   JlsPlainAccess pico_hash_jam_payload_read0;
   JlsPlainAccess pico_hash_jam_payload_read1;
   JlsPlainAccess pico_hash_jam_write1;
   JlsPlainAccess pico_hash_jam_write0].

Lemma jls_cache_action_before_here : forall first second tail,
  In second tail ->
  jls_cache_action_before first second (first :: tail).
Proof.
  intros first second tail Hin.
  destruct (in_split second tail Hin) as (middle & suffix & ->).
  exists [], middle, suffix. reflexivity.
Qed.

Lemma jls_cache_action_before_later : forall head first second tail,
  jls_cache_action_before first second tail ->
  jls_cache_action_before first second (head :: tail).
Proof.
  intros head first second tail (prefix & middle & suffix & ->).
  exists (head :: prefix), middle, suffix. reflexivity.
Qed.

Ltac solve_jls_before :=
  repeat first
    [ apply jls_cache_action_before_here;
      repeat first [apply in_eq | apply in_cons]
    | apply jls_cache_action_before_later ].

Lemma pico_hash_jls_cache_jam_projection :
  jls_cache_jam_execution pico_hash_jls_cache_actions pico_hash_jam_rf =
  pico_hash_jam_execution.
Proof.
  reflexivity.
Qed.

Lemma pico_hash_jls_cache_translation :
  jls_cache_to_combined pico_hash_jls_cache_actions =
  pico_hash_combined_actions.
Proof.
  reflexivity.
Qed.

Lemma pico_hash_jls_cache_publication_replay :
  jls_cache_publication_replay empty_final_publication_state
    pico_hash_jls_cache_actions pico_hash_after_both_acquire.
Proof.
  unfold pico_hash_jls_cache_actions.
  eapply JlsCacheReplayCons with (middle := pico_hash_after_freeze).
  - eapply JlsCacheConstructorReturn. reflexivity.
  - eapply JlsCacheReplayCons with (middle := pico_hash_after_publish).
    + eapply JlsCachePublishReference.
      unfold final_snapshot_frozen, pico_hash_after_freeze,
        pico_hash_combined_snapshot. simpl. reflexivity.
    + eapply JlsCacheReplayCons with (middle := pico_hash_after_acquire0).
      * eapply JlsCacheDereferenceReference.
        -- unfold final_location_published, pico_hash_after_publish.
           simpl. auto.
        -- unfold final_snapshot_frozen, pico_hash_after_publish,
             pico_hash_combined_snapshot. simpl. reflexivity.
      * eapply JlsCacheReplayCons with
          (middle := pico_hash_after_both_acquire).
        -- eapply JlsCacheDereferenceReference.
           ++ unfold final_location_published, pico_hash_after_acquire0.
              simpl. auto.
           ++ unfold final_snapshot_frozen, pico_hash_after_acquire0,
                pico_hash_combined_snapshot. simpl. reflexivity.
        -- repeat (eapply JlsCacheReplayCons; [constructor |]).
           constructor.
Qed.

Lemma pico_hash_jls_cache_accesses_follow_dereference :
  forall event,
    In event (jls_cache_jam_events pico_hash_jls_cache_actions) ->
    jam_event_kind event <> JamInit ->
    exists snapshot,
      jls_cache_action_before
        (JlsDereferenceReference (jam_event_thread event)
          (fst (jam_event_addr event)) snapshot)
        (JlsPlainAccess event) pico_hash_jls_cache_actions.
Proof.
  intros event Hin Hnot_init.
  unfold pico_hash_jls_cache_actions in Hin. simpl in Hin.
  repeat destruct Hin as [Hin | Hin]; try contradiction; subst event;
    try (exfalso; apply Hnot_init; reflexivity);
    exists pico_hash_combined_snapshot;
    unfold pico_hash_jls_cache_actions; simpl; solve_jls_before.
Qed.

Lemma pico_hash_jls_constructor_initializations :
  forall loc snapshot initial_events,
    In (JlsConstructorReturn loc snapshot initial_events)
      pico_hash_jls_cache_actions ->
    Forall
      (fun event =>
        jam_event_kind event = JamInit /\
        jam_event_mode event = JamPlain /\
        fst (jam_event_addr event) = loc)
      initial_events.
Proof.
  intros loc snapshot initial_events Hin.
  unfold pico_hash_jls_cache_actions in Hin. simpl in Hin.
  destruct Hin as [Heq | Hrest].
  - inversion Heq; subst. repeat constructor.
  - repeat destruct Hrest as [Hrest | Hrest]; try discriminate.
    contradiction.
Qed.

Theorem pico_hash_jls_cache_fragment_legal :
  jls_cache_execution_legal pico_hash_jls_cache_actions
    pico_hash_jam_rf pico_hash_after_both_acquire.
Proof.
  refine {| jls_cache_publication_is_legal :=
              pico_hash_jls_cache_publication_replay;
            jls_cache_jam_is_plain_legal := _;
            jls_cache_accesses_follow_dereference :=
              pico_hash_jls_cache_accesses_follow_dereference;
            jls_cache_constructor_initializations :=
              pico_hash_jls_constructor_initializations |}.
  rewrite pico_hash_jls_cache_jam_projection.
  exact pico_hash_jam_execution_plain_legal.
Qed.

Theorem pico_hash_jls_cache_fragment_simulates_combined :
  combined_memory_execution_legal pico_hash_combined_actions
    pico_hash_jam_rf pico_hash_after_both_acquire.
Proof.
  rewrite <- pico_hash_jls_cache_translation.
  eapply jls_cache_execution_simulates_combined.
  exact pico_hash_jls_cache_fragment_legal.
Qed.

(** Scoped Java-facing endpoint: the typed PICO allocation and benign race are
    realized by a legal execution of the supported JLS cache fragment. *)
Theorem pico_hash_source_constructed_jls_fragment_benign_race :
  stmt_typing pico_hash_concurrent_CT pico_hash_allocation_static_env
    AbstractState (SNew 3 Imm_c pico_hash_witness_class [1; 2])
    pico_hash_allocation_static_env /\
  @pico_new_freeze_step history_cache_memory_model
    pico_hash_concurrent_CT [1]
    pico_hash_before_source_new pico_hash_after_source_new /\
  jls_cache_execution_legal pico_hash_jls_cache_actions
    pico_hash_jam_rf pico_hash_after_both_acquire /\
  jls_cache_to_combined pico_hash_jls_cache_actions =
    pico_hash_combined_actions /\
  combined_memory_execution_legal pico_hash_combined_actions
    pico_hash_jam_rf pico_hash_after_both_acquire /\
  @pico_semantic_benign_race history_cache_memory_model
      pico_hash_concurrent_CT pico_hash_concurrent_initial_pool
      (@pcsi_state_inv nat nat hash_cache_protocol
        pico_hash_stable_abs pico_hash_concurrent_value
        (pico_hash_cache_adapter pico_hash_concurrent_receiver)
        (pico_concrete_hash_semimm pico_hash_concurrent_CT
          pico_hash_concurrent_receiver
          pico_hash_derive_method pico_hash_concurrent_initial_heap pico_hash_concurrent_value))
      pico_hash_result_ok /\
  pico_hash_race_access_schedule /\
  pico_jam_realization pico_hash_race_accesses pico_hash_jam_execution.
Proof.
  split; [exact pico_hash_source_new_typed |].
  split; [exact pico_hash_source_new_freezes_final_payload |].
  split; [exact pico_hash_jls_cache_fragment_legal |].
  split; [exact pico_hash_jls_cache_translation |].
  split; [exact pico_hash_jls_cache_fragment_simulates_combined |].
  pose proof pico_hash_source_constructed_combined_benign_race as Hcombined.
  tauto.
Qed.
