From Stdlib Require Import List.
Import ListNotations.

Require Import Syntax Typing Core.GenericDerivedCache.
Require Import Examples.PicoIfZeroCacheExamples Examples.PicoConcreteHashModel
  Examples.PicoSemanticConcurrencyExamples
  Examples.PicoSemanticConcurrencySafety Examples.PicoJamHashAdequacy
  Examples.PicoFinalFieldPublicationExamples
  Examples.PicoConstructionPublicationExamples.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoConstructionPublication
  PICOBridge.PicoSemanticConcurrency PICOBridge.PicoIrisSemImmLogicalRelation
  PICOBridge.PicoJamSimulation.
Require Import MemoryModels.JAM.JamEvents MemoryModels.JAM.JamHistory.
Require Import MemoryModels.JMM.FinalFieldPublication
  MemoryModels.JMM.JamPublicationExecution.

(** * One Memory-Event Execution for the Concrete Hash Race *)

Definition pico_hash_combined_snapshot : final_snapshot :=
  [Int pico_hash_concurrent_value].

Definition pico_hash_after_acquire0 : final_publication_state :=
  mkFinalPublicationState
    [(pico_hash_concurrent_receiver, pico_hash_combined_snapshot)]
    [pico_hash_concurrent_receiver]
    [(0, pico_hash_concurrent_receiver, pico_hash_combined_snapshot)].

Definition pico_hash_after_both_acquire : final_publication_state :=
  mkFinalPublicationState
    [(pico_hash_concurrent_receiver, pico_hash_combined_snapshot)]
    [pico_hash_concurrent_receiver]
    [(1, pico_hash_concurrent_receiver, pico_hash_combined_snapshot);
     (0, pico_hash_concurrent_receiver, pico_hash_combined_snapshot)].

Definition pico_hash_combined_actions : list combined_memory_action :=
  [CombinedConstruct pico_hash_concurrent_receiver pico_hash_combined_snapshot;
   CombinedAccess pico_hash_jam_init;
   CombinedFreeze pico_hash_concurrent_receiver pico_hash_combined_snapshot;
   CombinedPublish pico_hash_concurrent_receiver;
   CombinedAcquire 0 pico_hash_concurrent_receiver pico_hash_combined_snapshot;
   CombinedAcquire 1 pico_hash_concurrent_receiver pico_hash_combined_snapshot;
   CombinedAccess pico_hash_jam_read0;
   CombinedAccess pico_hash_jam_read1;
   CombinedAccess pico_hash_jam_write1;
   CombinedAccess pico_hash_jam_write0].

Lemma pico_hash_source_new_realizes_combined_prefix :
  @pico_new_freeze_step history_cache_memory_model
    pico_hash_concurrent_CT [1]
    pico_hash_before_source_new pico_hash_after_source_new /\
  exists tail,
    pico_hash_combined_actions =
      CombinedConstruct pico_hash_concurrent_receiver
        pico_hash_combined_snapshot ::
      CombinedAccess pico_hash_jam_init ::
      CombinedFreeze pico_hash_concurrent_receiver
        pico_hash_combined_snapshot :: tail /\
    final_snapshot_frozen (pnpc_publication pico_hash_after_source_new)
      pico_hash_concurrent_receiver pico_hash_combined_snapshot.
Proof.
  split; [exact pico_hash_source_new_freezes_final_payload |].
  exists [CombinedPublish pico_hash_concurrent_receiver;
    CombinedAcquire 0 pico_hash_concurrent_receiver pico_hash_combined_snapshot;
    CombinedAcquire 1 pico_hash_concurrent_receiver pico_hash_combined_snapshot;
    CombinedAccess pico_hash_jam_read0;
    CombinedAccess pico_hash_jam_read1;
    CombinedAccess pico_hash_jam_write1;
    CombinedAccess pico_hash_jam_write0].
  split; [reflexivity |].
  unfold pico_hash_after_source_new, final_snapshot_frozen,
    pico_hash_combined_snapshot. simpl. reflexivity.
Qed.

Lemma pico_hash_combined_jam_projection :
  combined_jam_execution pico_hash_combined_actions pico_hash_jam_rf =
  pico_hash_jam_execution.
Proof.
  reflexivity.
Qed.

Lemma pico_hash_combined_publication_replay :
  combined_publication_replay empty_final_publication_state
    pico_hash_combined_actions pico_hash_after_both_acquire.
Proof.
  unfold pico_hash_combined_actions.
  eapply CombinedPublicationReplayCons with
    (middle := empty_final_publication_state).
  - constructor.
  - eapply CombinedPublicationReplayCons with
      (middle := empty_final_publication_state).
    + constructor.
    + eapply CombinedPublicationReplayCons with
        (middle := pico_hash_after_freeze).
      * eapply CombinedPublicationFreeze.
        unfold empty_final_publication_state. reflexivity.
      * eapply CombinedPublicationReplayCons with
        (middle := pico_hash_after_publish).
        -- eapply CombinedPublicationPublish.
        unfold final_snapshot_frozen, pico_hash_after_freeze,
          pico_hash_combined_snapshot. simpl. reflexivity.
        -- eapply CombinedPublicationReplayCons with
          (middle := pico_hash_after_acquire0).
           ++ eapply CombinedPublicationAcquire.
              ** unfold final_location_published, pico_hash_after_publish.
                 simpl. auto.
              ** unfold final_snapshot_frozen, pico_hash_after_publish,
                   pico_hash_combined_snapshot. simpl. reflexivity.
           ++ eapply CombinedPublicationReplayCons with
             (middle := pico_hash_after_both_acquire).
              ** eapply CombinedPublicationAcquire.
                 --- unfold final_location_published,
                       pico_hash_after_acquire0. simpl. auto.
                 --- unfold final_snapshot_frozen,
                       pico_hash_after_acquire0,
                       pico_hash_combined_snapshot. simpl. reflexivity.
              ** repeat (eapply CombinedPublicationReplayCons;
                   [constructor |]).
                 constructor.
Qed.

Lemma pico_hash_combined_freeze_follows_construction :
  forall loc snapshot,
    In (CombinedFreeze loc snapshot) pico_hash_combined_actions ->
    combined_action_before
      (CombinedConstruct loc snapshot) (CombinedFreeze loc snapshot)
      pico_hash_combined_actions.
Proof.
  intros loc snapshot Hin.
  unfold pico_hash_combined_actions in Hin.
  simpl in Hin.
  destruct Hin as [Hfalse | [Hinit | [Heq | Hfalse]]].
  - discriminate.
  - discriminate.
  - inversion Heq; subst.
    unfold combined_action_before, pico_hash_combined_actions.
    exists [], [CombinedAccess pico_hash_jam_init],
      [CombinedPublish pico_hash_concurrent_receiver;
       CombinedAcquire 0 pico_hash_concurrent_receiver
         pico_hash_combined_snapshot;
       CombinedAcquire 1 pico_hash_concurrent_receiver
         pico_hash_combined_snapshot;
       CombinedAccess pico_hash_jam_read0;
       CombinedAccess pico_hash_jam_read1;
       CombinedAccess pico_hash_jam_write1;
       CombinedAccess pico_hash_jam_write0].
    reflexivity.
  - repeat destruct Hfalse as [Hfalse | Hfalse]; try discriminate.
    contradiction.
Qed.

Lemma pico_hash_combined_accesses_follow_acquire :
  forall event,
    In event (combined_jam_events pico_hash_combined_actions) ->
    jam_event_kind event <> JamInit ->
    exists snapshot,
      combined_action_before
        (CombinedAcquire (jam_event_thread event)
          (fst (jam_event_addr event)) snapshot)
        (CombinedAccess event) pico_hash_combined_actions.
Proof.
  intros event Hin Hnot_init.
  unfold pico_hash_combined_actions in Hin. simpl in Hin.
  destruct Hin as [Heq | [Heq | [Heq | [Heq | [Heq | Hfalse]]]]];
    [subst event; exfalso; apply Hnot_init; reflexivity
    | subst event | subst event | subst event | subst event | contradiction].
  - exists pico_hash_combined_snapshot.
    unfold combined_action_before, pico_hash_combined_actions.
    exists [CombinedConstruct pico_hash_concurrent_receiver
              pico_hash_combined_snapshot;
            CombinedAccess pico_hash_jam_init;
            CombinedFreeze pico_hash_concurrent_receiver
              pico_hash_combined_snapshot;
            CombinedPublish pico_hash_concurrent_receiver],
      [CombinedAcquire 1 pico_hash_concurrent_receiver
         pico_hash_combined_snapshot],
      [CombinedAccess pico_hash_jam_read1;
       CombinedAccess pico_hash_jam_write1;
       CombinedAccess pico_hash_jam_write0].
    reflexivity.
  - exists pico_hash_combined_snapshot.
    unfold combined_action_before, pico_hash_combined_actions.
    exists [CombinedConstruct pico_hash_concurrent_receiver
              pico_hash_combined_snapshot;
            CombinedAccess pico_hash_jam_init;
            CombinedFreeze pico_hash_concurrent_receiver
              pico_hash_combined_snapshot;
            CombinedPublish pico_hash_concurrent_receiver;
            CombinedAcquire 0 pico_hash_concurrent_receiver
              pico_hash_combined_snapshot],
      [CombinedAccess pico_hash_jam_read0],
      [CombinedAccess pico_hash_jam_write1;
       CombinedAccess pico_hash_jam_write0].
    reflexivity.
  - exists pico_hash_combined_snapshot.
    unfold combined_action_before, pico_hash_combined_actions.
    exists [CombinedConstruct pico_hash_concurrent_receiver
              pico_hash_combined_snapshot;
            CombinedAccess pico_hash_jam_init;
            CombinedFreeze pico_hash_concurrent_receiver
              pico_hash_combined_snapshot;
            CombinedPublish pico_hash_concurrent_receiver;
            CombinedAcquire 0 pico_hash_concurrent_receiver
              pico_hash_combined_snapshot],
      [CombinedAccess pico_hash_jam_read0;
       CombinedAccess pico_hash_jam_read1],
      [CombinedAccess pico_hash_jam_write0].
    reflexivity.
  - exists pico_hash_combined_snapshot.
    unfold combined_action_before, pico_hash_combined_actions.
    exists [CombinedConstruct pico_hash_concurrent_receiver
              pico_hash_combined_snapshot;
            CombinedAccess pico_hash_jam_init;
            CombinedFreeze pico_hash_concurrent_receiver
              pico_hash_combined_snapshot;
            CombinedPublish pico_hash_concurrent_receiver],
      [CombinedAcquire 1 pico_hash_concurrent_receiver
         pico_hash_combined_snapshot;
       CombinedAccess pico_hash_jam_read0;
       CombinedAccess pico_hash_jam_read1;
       CombinedAccess pico_hash_jam_write1], [].
    reflexivity.
Qed.

Theorem pico_hash_combined_execution_legal :
  combined_memory_execution_legal pico_hash_combined_actions
    pico_hash_jam_rf pico_hash_after_both_acquire.
Proof.
  refine {| combined_publication_is_legal :=
              pico_hash_combined_publication_replay;
            combined_jam_is_plain_legal := _;
            combined_freezes_follow_construction :=
              pico_hash_combined_freeze_follows_construction;
            combined_accesses_follow_acquire :=
              pico_hash_combined_accesses_follow_acquire |}.
  rewrite pico_hash_combined_jam_projection.
  exact pico_hash_jam_execution_plain_legal.
Qed.

(** The construction event denotes the exact allocation/freeze transition
    used to create the shared receiver, and the remainder of the same trace
    realizes the legal benign race. *)
Theorem pico_hash_source_constructed_combined_benign_race :
  stmt_typing pico_hash_concurrent_CT pico_hash_allocation_static_env
    AbstractState (SNew 3 Imm_c pico_hash_witness_class [1; 2])
    pico_hash_allocation_static_env /\
  @pico_new_freeze_step history_cache_memory_model
    pico_hash_concurrent_CT [1]
    pico_hash_before_source_new pico_hash_after_source_new /\
  (exists tail,
    pico_hash_combined_actions =
      CombinedConstruct pico_hash_concurrent_receiver
        pico_hash_combined_snapshot ::
      CombinedAccess pico_hash_jam_init ::
      CombinedFreeze pico_hash_concurrent_receiver
        pico_hash_combined_snapshot :: tail /\
    final_snapshot_frozen (pnpc_publication pico_hash_after_source_new)
      pico_hash_concurrent_receiver pico_hash_combined_snapshot) /\
  pnpc_state pico_hash_after_source_new = pico_hash_concurrent_initial_state /\
  pnpc_publication pico_hash_after_source_new = pico_hash_after_freeze /\
  combined_memory_execution_legal pico_hash_combined_actions
    pico_hash_jam_rf pico_hash_after_both_acquire /\
  final_publication_steps empty_final_publication_state
    pico_hash_after_both_acquire /\
  combined_jam_execution pico_hash_combined_actions pico_hash_jam_rf =
    pico_hash_jam_execution /\
  @pico_semantic_benign_race history_cache_memory_model
      pico_hash_concurrent_CT pico_hash_concurrent_initial_pool
      (@pcsi_state_inv nat nat hash_cache_protocol
        pico_hash_stable_abs pico_hash_concurrent_value
        (pico_hash_cache_adapter pico_hash_concurrent_receiver)
        (pico_concrete_hash_semimm pico_hash_concurrent_CT
          pico_hash_concurrent_receiver
          pico_hash_witness_function pico_hash_concurrent_value))
      pico_hash_result_ok /\
  pico_hash_race_access_schedule /\
  pico_jam_realization pico_hash_race_accesses pico_hash_jam_execution.
Proof.
  split; [exact pico_hash_source_new_typed |].
  split; [exact pico_hash_source_new_freezes_final_payload |].
  split; [exact (proj2 pico_hash_source_new_realizes_combined_prefix) |].
  split; [reflexivity |].
  split; [reflexivity |].
  split; [exact pico_hash_combined_execution_legal |].
  split.
  - eapply combined_memory_execution_publication_projection.
    exact pico_hash_combined_execution_legal.
  - split; [exact pico_hash_combined_jam_projection |].
    pose proof pico_hash_plain_jam_benign_race as Hrace.
    tauto.
Qed.
