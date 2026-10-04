From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Subtyping Typing Bigstep DerivedCache.
Require Import Core.GenericDerivedCache.
Require Import Examples.PicoIfZeroCache Examples.PicoConcreteHashProvider
  Examples.PicoSemanticConcurrencyExamples
  Examples.PicoSemanticConcurrencySafety Examples.PicoJamHashAdequacy
  Examples.PicoFinalFieldPublicationExamples.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoCoreLanguage
  PICOBridge.PicoConstructionPublication PICOBridge.PicoFinalFieldPublication
  PICOBridge.PicoStableAbsPreservation PICOBridge.PicoSemanticConcurrency
  PICOBridge.PicoJamSimulation PICOBridge.PicoCoreSemImm.
Require Import MemoryModels.JAM.JamLegality.
Require Import MemoryModels.JMM.FinalFieldPublication.

(** * Source Allocation and Publication of the Hash Receiver

    A root receiver executes [SNew] with the cache default and stable payload
    as constructor arguments.  The synchronized construction step freezes the
    allocated object's final payload at location 1; publication and observer
    acquisition happen only afterwards. *)

Definition pico_hash_allocation_root_object : Obj :=
  pico_hash_concurrent_owner.

Definition pico_hash_allocation_env : r_env :=
  mkr_env [Iot 0; Int 0; Int pico_hash_concurrent_value; Null_a].

Definition pico_hash_allocation_root_type : qualified_type :=
  Build_qualified_type Imm (TRef pico_hash_witness_root).

Definition pico_hash_allocation_static_env : s_env :=
  [pico_hash_allocation_root_type; int_type; int_type;
   pico_hash_witness_receiver_type].

Definition pico_hash_allocation_pre_state : pico_core_state :=
  mkPicoCoreState [pico_hash_allocation_root_object]
    (pico_core_alloc_weak empty_wm_state
      pico_hash_allocation_root_object 0).

Definition pico_hash_allocation_post_env : r_env :=
  set_vars pico_hash_allocation_env
    (update 3 (Iot pico_hash_concurrent_receiver)
      (vars pico_hash_allocation_env)).

Definition pico_hash_allocation_post_state : pico_core_state :=
  pico_hash_concurrent_initial_state.

Definition pico_hash_before_source_new : pico_new_publication_config :=
  mkPicoNewPublicationConfig
    (CoreRun pico_hash_allocation_env
      (SNew 3 Imm_c pico_hash_witness_class [1; 2]) 0 [])
    pico_hash_allocation_pre_state
    empty_final_publication_state.

Definition pico_hash_after_source_new : pico_new_publication_config :=
  mkPicoNewPublicationConfig
    (CoreRun pico_hash_allocation_post_env SSkip 0 [])
    pico_hash_allocation_post_state
    (mkFinalPublicationState
      [(pico_hash_concurrent_receiver, [Int pico_hash_concurrent_value])]
      [] []).

Definition pico_hash_source_after_publish : final_publication_state :=
  mkFinalPublicationState
    [(pico_hash_concurrent_receiver, [Int pico_hash_concurrent_value])]
    [pico_hash_concurrent_receiver] [].

Definition pico_hash_source_after_acquire : final_publication_state :=
  mkFinalPublicationState
    [(pico_hash_concurrent_receiver, [Int pico_hash_concurrent_value])]
    [pico_hash_concurrent_receiver]
    [(1, pico_hash_concurrent_receiver, [Int pico_hash_concurrent_value])].

Theorem pico_hash_source_new_typed :
  stmt_typing pico_hash_concurrent_CT pico_hash_allocation_static_env
    AbstractState (SNew 3 Imm_c pico_hash_witness_class [1; 2])
    pico_hash_allocation_static_env.
Proof.
  assert (Hwf : wf_senv pico_hash_concurrent_CT
      pico_hash_allocation_static_env).
  {
    unfold wf_senv, pico_hash_allocation_static_env,
      pico_hash_allocation_root_type, pico_hash_witness_receiver_type,
      wf_stypeuse, pico_hash_concurrent_CT,
      pico_hash_concurrent_class_def, pico_hash_witness_root_def,
      pico_hash_witness_root, pico_hash_witness_class,
      bound, find_class, gget, int_type.
    simpl. split; [lia |].
    repeat constructor; try reflexivity; try discriminate.
  }
  eapply S_New with
    (Tx := pico_hash_witness_receiver_type)
    (argtypes := [int_type; int_type])
    (Tthis := pico_hash_allocation_root_type)
    (consig := csignature pico_hash_witness_constructor).
  - exact Hwf.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - discriminate.
  - reflexivity.
  - constructor.
    + apply qtype_refl; simpl; [reflexivity | discriminate].
    + constructor.
      * apply qtype_refl; simpl; [reflexivity | discriminate].
      * constructor.
  - apply qtype_refl.
    + unfold wf_qualified_base, pico_hash_witness_receiver_type,
        pico_hash_concurrent_CT, pico_hash_witness_class.
      simpl. lia.
    + unfold pico_hash_witness_receiver_type. discriminate.
Qed.

Theorem pico_hash_source_new_freezes_final_payload :
  @pico_new_freeze_step history_cache_memory_model
    pico_hash_concurrent_CT [1]
    pico_hash_before_source_new pico_hash_after_source_new.
Proof.
  unfold pico_hash_before_source_new, pico_hash_after_source_new,
    pico_hash_allocation_pre_state, pico_hash_allocation_post_state,
    pico_hash_allocation_post_env, pico_hash_allocation_env,
    pico_hash_allocation_root_object, pico_hash_witness_object,
    empty_final_publication_state.
  eapply PicoNewFreezeStep with
    (loc_this := 0) (qthisr := Imm_r)
    (values := [Int 0; Int pico_hash_concurrent_value])
    (qadapted := Imm_r) (snapshot := [Int pico_hash_concurrent_value]);
    simpl; try reflexivity.
  constructor; [exact pico_hash_concurrent_payload_final | constructor].
Qed.

Theorem pico_hash_source_new_erases_to_core :
  @pico_core_step history_cache_memory_model pico_hash_concurrent_CT
    (pnpc_control pico_hash_before_source_new)
    (pnpc_state pico_hash_before_source_new)
    (pnpc_control pico_hash_after_source_new)
    (pnpc_state pico_hash_after_source_new).
Proof.
  eapply pico_new_freeze_step_erases_to_core.
  exact pico_hash_source_new_freezes_final_payload.
Qed.

Theorem pico_hash_source_publication_execution :
  final_publication_steps empty_final_publication_state
    pico_hash_source_after_acquire.
Proof.
  eapply FinalPublicationStepsStep with
    (middle := pnpc_publication pico_hash_after_source_new).
  - exact (@pico_new_freeze_step_projects_to_publication
      history_cache_memory_model pico_hash_concurrent_CT [1]
      pico_hash_before_source_new pico_hash_after_source_new
      pico_hash_source_new_freezes_final_payload).
  - eapply FinalPublicationStepsStep with
      (middle := pico_hash_source_after_publish).
    + unfold pico_hash_after_source_new, pico_hash_source_after_publish.
      eapply FinalPublish with
        (snapshot := [Int pico_hash_concurrent_value]).
      unfold final_snapshot_frozen. simpl. reflexivity.
    + eapply FinalPublicationStepsStep with
        (middle := pico_hash_source_after_acquire).
      * unfold pico_hash_source_after_publish,
          pico_hash_source_after_acquire.
        eapply FinalAcquire with
          (snapshot := [Int pico_hash_concurrent_value]).
        -- unfold final_location_published. simpl. auto.
        -- unfold final_snapshot_frozen. simpl. reflexivity.
      * constructor.
Qed.

Lemma pico_hash_source_final_snapshot_observed :
  final_snapshot_observed pico_hash_source_after_acquire 1
    pico_hash_concurrent_receiver
    [Int pico_hash_concurrent_value].
Proof.
  unfold final_snapshot_observed, pico_hash_source_after_acquire.
  simpl. auto.
Qed.

Lemma pico_hash_source_final_heap_snapshot :
  pico_final_heap_snapshot pico_hash_concurrent_CT pico_hash_witness_class [1]
    (pcs_heap pico_hash_allocation_post_state) pico_hash_concurrent_receiver
    [Int pico_hash_concurrent_value].
Proof.
  unfold pico_final_heap_snapshot, pico_hash_allocation_post_state.
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

Lemma pico_hash_source_cache_declared :
  derived_cache_field pico_hash_concurrent_CT pico_hash_witness_class
    hash_cache_field.
Proof.
  unfold derived_cache_field, cache_field.
  exact pico_hash_concurrent_cache_assignable.
Qed.

Theorem pico_hash_source_allocation_establishes_provider_inv :
  pico_hash_provider_inv pico_hash_concurrent_CT pico_hash_concurrent_receiver
    pico_hash_derive_method pico_hash_concurrent_initial_heap pico_hash_concurrent_value
    pico_hash_allocation_post_state.
Proof.
  exact pico_hash_concurrent_initial_provider_inv.
Qed.

Theorem pico_hash_source_construction_establishes_observer_stable_abs :
  pico_observer_stable_abs
    pico_hash_concurrent_CT pico_hash_witness_class [1]
    (pcs_heap pico_hash_allocation_post_state)
    pico_hash_source_after_acquire 1 pico_hash_concurrent_receiver
    [Int pico_hash_concurrent_value].
Proof.
  eapply pico_publication_execution_establishes_observer_stable_abs.
  - exact pico_hash_source_publication_execution.
  - exact pico_hash_source_final_heap_snapshot.
  - exact pico_hash_source_final_snapshot_observed.
Qed.

Theorem pico_hash_source_construction_publication_ready :
  stmt_typing pico_hash_concurrent_CT pico_hash_allocation_static_env
    AbstractState (SNew 3 Imm_c pico_hash_witness_class [1; 2])
    pico_hash_allocation_static_env /\
  @pico_new_freeze_step history_cache_memory_model
    pico_hash_concurrent_CT [1]
    pico_hash_before_source_new pico_hash_after_source_new /\
  pico_hash_provider_inv pico_hash_concurrent_CT pico_hash_concurrent_receiver
    pico_hash_derive_method pico_hash_concurrent_initial_heap pico_hash_concurrent_value
    pico_hash_allocation_post_state /\
  pico_observer_stable_abs
    pico_hash_concurrent_CT pico_hash_witness_class [1]
    (pcs_heap pico_hash_allocation_post_state)
    pico_hash_source_after_acquire 1 pico_hash_concurrent_receiver
    [Int pico_hash_concurrent_value].
Proof.
  split; [exact pico_hash_source_new_typed |].
  split; [exact pico_hash_source_new_freezes_final_payload |].
  split.
  - exact pico_hash_source_allocation_establishes_provider_inv.
  - exact pico_hash_source_construction_establishes_observer_stable_abs.
Qed.

(** The source construction reaches exactly the receiver state and frozen
    publication state used by the concurrent plain-JAM proof. *)
Theorem pico_hash_source_constructed_plain_jam_benign_race :
  stmt_typing pico_hash_concurrent_CT pico_hash_allocation_static_env
    AbstractState (SNew 3 Imm_c pico_hash_witness_class [1; 2])
    pico_hash_allocation_static_env /\
  @pico_new_freeze_step history_cache_memory_model
    pico_hash_concurrent_CT [1]
    pico_hash_before_source_new pico_hash_after_source_new /\
  pnpc_state pico_hash_after_source_new = pico_hash_concurrent_initial_state /\
  pnpc_publication pico_hash_after_source_new = pico_hash_after_freeze /\
  pico_hash_source_after_acquire = pico_hash_after_acquire /\
  final_publication_steps
    empty_final_publication_state pico_hash_after_acquire /\
  final_snapshot_observed pico_hash_after_acquire 1
    pico_hash_concurrent_receiver [Int pico_hash_concurrent_value] /\
  pico_core_stable_abs pico_hash_concurrent_CT pico_hash_witness_class [1]
    pico_hash_concurrent_receiver pico_hash_concurrent_initial_state
    [Int pico_hash_concurrent_value] /\
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
  split; [exact pico_hash_source_new_typed |].
  split; [exact pico_hash_source_new_freezes_final_payload |].
  split; [reflexivity |].
  split; [reflexivity |].
  split; [reflexivity |].
  exact pico_hash_published_plain_jam_benign_race.
Qed.
