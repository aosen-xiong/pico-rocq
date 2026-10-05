From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Subtyping Typing Bigstep.
Require Import Core.GenericCacheProtocol Core.GenericDerivedCache.
Require Import Examples.PicoIfZeroCache
  Examples.PicoHashMethod
  Examples.PicoConcreteHashProvider
  Examples.PicoSemanticConcurrencyExamples
  Examples.PicoSemanticConcurrencySafety
  Examples.PicoCacheMethodJudgment Examples.PicoHashCacheMethod
  Examples.PicoCacheClients Examples.PicoCacheClientCalls.
Require Import PICOBridge.PicoCoreLanguage
  PICOBridge.PicoMemoryModel PICOBridge.PicoCacheTyping
  PICOBridge.PicoCoreSemImm
  PICOBridge.PicoDerivationNoninterference
  PICOBridge.PicoSemanticConcurrency PICOBridge.PicoCoreTraceRobust.

(** * Hash Clients

    A client thread that calls the hash method twice and branches on the
    result in between, running alongside other such clients and threads that
    read the cache field directly. *)

Definition pico_hash_client_stmt : stmt :=
  SSeq (SCall 1 pico_hash_concurrent_method 0 [])
    (SIfZero 1 SSkip (SCall 1 pico_hash_concurrent_method 0 [])).

Definition pico_hash_client : pico_core_expr :=
  CoreRun pico_hash_concurrent_caller pico_hash_client_stmt 0 [].

Notation concurrent_machine :=
  (@pico_concrete_hash_semimm history_cache_memory_model
     pico_hash_concurrent_CT pico_hash_concurrent_receiver
     pico_hash_derive_method pico_hash_concurrent_initial_heap
     pico_hash_concurrent_value).

Lemma pico_hash_client_stmt_ok :
  client_stmt pico_hash_concurrent_method 0 pico_hash_client_stmt.
Proof.
  repeat constructor; discriminate.
Qed.

Theorem pico_hash_client_trace_robust :
  @machine_cache_safe history_cache_memory_model pico_hash_concurrent_CT _ _
    hash_cache_protocol pico_hash_stable_abs pico_hash_concurrent_value
    (pico_hash_cache_adapter pico_hash_concurrent_receiver)
    concurrent_machine (fun _ => True) pico_hash_client.
Proof.
  eapply (client_code_trace_robust pico_hash_concurrent_CT
    pico_hash_derivations pico_hash_concurrent_receiver
    pico_hash_derive_method pico_hash_concurrent_initial_heap
    pico_hash_concurrent_value pico_hash_read_compute_stmt
    pico_hash_concurrent_method pico_hash_concurrent_method_def
    pico_hash_witness_receiver_type pico_hash_frame_senv AbstractState
    (mkruntime_type Imm_r pico_hash_witness_class) [Int 0; Int 7] 0).
  - reflexivity.
  - reflexivity.
  - exact pico_hash_concurrent_derivation_table.
  - exact pico_hash_compute_deriv.
  - exact pico_hash_compute_typing.
  - exact pico_hash_frame_config_wf.
  - exact pico_hash_compute_value.
  - reflexivity.
  - exact pico_hash_concurrent_cache_declared.
  - exact pico_hash_concurrent_find_method.
  - reflexivity.
  - exact pico_hash_client_stmt_ok.
Qed.

Definition pico_hash_clients_and_readers (n k : nat) : pico_pool_config :=
  mkPicoPoolConfig pico_hash_concurrent_initial_state
    (repeat pico_hash_client n ++ repeat pico_hash_reader k).

(** Any number of clients and direct readers preserve semantic
    immutability under every interleaving. *)
Theorem pico_hash_clients_and_readers_semimm : forall n k cfg,
  @pico_pool_steps history_cache_memory_model pico_hash_concurrent_CT
    (pico_hash_clients_and_readers n k) cfg ->
  CacheHistSnapshotOK hash_cache_protocol
    (pico_hash_snapshot pico_hash_concurrent_receiver (pool_state cfg))
    pico_hash_concurrent_value.
Proof.
  intros n k cfg Hsteps.
  assert (Hpool : @mixed_pool history_cache_memory_model
    pico_hash_concurrent_CT _ _ hash_cache_protocol pico_hash_stable_abs
    pico_hash_concurrent_value
    (pico_hash_cache_adapter pico_hash_concurrent_receiver)
    concurrent_machine (fun _ => True)
    (pico_hash_clients_and_readers n k)).
  { split.
    - split; [exact pico_hash_concurrent_initial_provider_inv |].
      exact (proj2 (proj2 pico_hash_concurrent_initial_provider_inv)).
    - simpl. apply Forall_app. split; apply Forall_forall;
        intros e Hin; apply repeat_spec in Hin; subst e.
      + left. apply machine_local_start.
        exact pico_hash_client_trace_robust.
      + right. exists pico_hash_reader.
        split; [exact pico_hash_reader_client | constructor]. }
  exact (proj2 (machine_mixed_pool_semimm _ _ _ _ _ _ _ _ _ Hpool Hsteps)).
Qed.
