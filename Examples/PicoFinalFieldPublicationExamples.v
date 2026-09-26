From Stdlib Require Import List.
Import ListNotations.

Require Import Syntax Helpers DerivedCache Core.GenericDerivedCache.
Require Import Examples.PicoIfZeroCacheExamples
  Examples.PicoConcreteHashModel
  Examples.PicoSemanticConcurrencyExamples
  Examples.PicoSemanticConcurrencySafety
  Examples.PicoJamHashAdequacy.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage
  PICOBridge.PicoSemanticConcurrency PICOBridge.PicoJamSimulation
  PICOBridge.PicoStableAbsPreservation PICOBridge.PicoFinalFieldPublication
  PICOBridge.PicoIrisSemImmLogicalRelation.
Require Import MemoryModels.JMM.FinalFieldPublication.
Require Import MemoryModels.JAM.JamLegality.

(** * Publishing the Concrete Hash Receiver's Final Payload *)

Definition pico_hash_after_freeze : final_publication_state :=
  mkFinalPublicationState
    [(pico_hash_concurrent_receiver, [Int pico_hash_concurrent_value])] [] [].

Definition pico_hash_after_publish : final_publication_state :=
  mkFinalPublicationState
    [(pico_hash_concurrent_receiver, [Int pico_hash_concurrent_value])]
    [pico_hash_concurrent_receiver] [].

Definition pico_hash_after_acquire : final_publication_state :=
  mkFinalPublicationState
    [(pico_hash_concurrent_receiver, [Int pico_hash_concurrent_value])]
    [pico_hash_concurrent_receiver]
    [(1, pico_hash_concurrent_receiver, [Int pico_hash_concurrent_value])].

(** The concrete receiver is frozen, published, and acquired by observer 1. *)
Theorem pico_hash_final_publication_execution :
  final_publication_steps
    empty_final_publication_state pico_hash_after_acquire.
Proof.
  eapply FinalPublicationStepsStep with (middle := pico_hash_after_freeze).
  - unfold empty_final_publication_state, pico_hash_after_freeze. constructor.
    reflexivity.
  - eapply FinalPublicationStepsStep with (middle := pico_hash_after_publish).
    + unfold pico_hash_after_freeze, pico_hash_after_publish.
      eapply FinalPublish with
        (snapshot := [Int pico_hash_concurrent_value]).
      unfold final_snapshot_frozen. simpl. reflexivity.
    + eapply FinalPublicationStepsStep with (middle := pico_hash_after_acquire).
      * unfold pico_hash_after_publish, pico_hash_after_acquire.
        eapply FinalAcquire with
          (snapshot := [Int pico_hash_concurrent_value]).
        -- unfold final_location_published. simpl. auto.
        -- unfold final_snapshot_frozen. simpl. reflexivity.
      * constructor.
Qed.

Lemma pico_hash_final_snapshot_observed :
  final_snapshot_observed pico_hash_after_acquire 1
    pico_hash_concurrent_receiver
    [Int pico_hash_concurrent_value].
Proof.
  unfold final_snapshot_observed, pico_hash_after_acquire. simpl. auto.
Qed.

Lemma pico_hash_concurrent_final_heap_snapshot :
  pico_final_heap_snapshot pico_hash_concurrent_CT pico_hash_witness_class
    [1] (pcs_heap pico_hash_concurrent_initial_state)
    pico_hash_concurrent_receiver
    [Int pico_hash_concurrent_value].
Proof.
  unfold pico_final_heap_snapshot, pico_hash_concurrent_initial_state.
  exists pico_hash_witness_object.
  split; [reflexivity |].
  split; [reflexivity |].
  split.
  - constructor; [exact pico_hash_concurrent_payload_final | constructor].
  - unfold field_reads. constructor.
    + unfold field_read. exists pico_hash_witness_object.
      split; reflexivity.
    + constructor.
Qed.

Theorem pico_hash_publication_establishes_observer_stable_abs :
  pico_observer_stable_abs pico_hash_concurrent_CT pico_hash_witness_class [1]
    (pcs_heap pico_hash_concurrent_initial_state) pico_hash_after_acquire 1
    pico_hash_concurrent_receiver
    [Int pico_hash_concurrent_value].
Proof.
  eapply pico_publication_execution_establishes_observer_stable_abs.
  - exact pico_hash_final_publication_execution.
  - exact pico_hash_concurrent_final_heap_snapshot.
  - exact pico_hash_final_snapshot_observed.
Qed.

Theorem pico_hash_publication_establishes_core_stable_abs :
  pico_core_stable_abs pico_hash_concurrent_CT pico_hash_witness_class [1]
    pico_hash_concurrent_receiver
    pico_hash_concurrent_initial_state [Int pico_hash_concurrent_value].
Proof.
  eapply pico_publication_execution_establishes_core_stable_abs with
    (final := pico_hash_after_acquire) (observer := 1).
  - exact pico_hash_final_publication_execution.
  - exact pico_hash_concurrent_final_heap_snapshot.
  - exact pico_hash_final_snapshot_observed.
Qed.

(** End-to-end model composition for the concrete case: the receiver's final
    payload is published before the already-proved legal plain-JAM cache race. *)
Theorem pico_hash_published_plain_jam_benign_race :
  final_publication_steps
    empty_final_publication_state pico_hash_after_acquire /\
  final_snapshot_observed pico_hash_after_acquire 1
    pico_hash_concurrent_receiver
    [Int pico_hash_concurrent_value] /\
  pico_core_stable_abs pico_hash_concurrent_CT pico_hash_witness_class [1]
    pico_hash_concurrent_receiver
    pico_hash_concurrent_initial_state [Int pico_hash_concurrent_value] /\
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
  pico_jam_realization pico_hash_race_accesses pico_hash_jam_execution /\
  jam_plain_legal pico_hash_jam_execution.
Proof.
  split; [exact pico_hash_final_publication_execution |].
  split; [exact pico_hash_final_snapshot_observed |].
  split; [exact pico_hash_publication_establishes_core_stable_abs |].
  exact pico_hash_plain_jam_benign_race.
Qed.
