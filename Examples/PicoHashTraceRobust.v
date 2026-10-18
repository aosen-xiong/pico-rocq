From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Bigstep.
Require Import Core.GenericCacheProtocol Core.GenericDerivedCache.
Require Import Examples.PicoIfZeroCache
  Examples.PicoHashMethod
  Examples.PicoConcreteHashProvider
  Examples.PicoSemanticConcurrencyExamples
  Examples.PicoSemanticConcurrencySafety.
Require Import PICOBridge.PicoCoreLanguage
  PICOBridge.PicoMemoryModel PICOBridge.PicoCoreSemImm
  PICOBridge.PicoSemanticConcurrency PICOBridge.PicoCoreTraceRobust.

(** * The Hash Method is Trace Robust on the Core Machine

    The local-copy hash call inhabits the machine-level trace-robustness
    condition for the derivation-defined hash provider, so the generic
    machine theorems apply to any number of concurrent calls. *)

Definition pico_hash_machine :
    PicoCoreSemImmInstantiation hash_cache_protocol pico_hash_stable_abs
      pico_hash_concurrent_value
      (pico_hash_cache_adapter pico_hash_concurrent_receiver) :=
  @pico_concrete_hash_semimm history_cache_memory_model
    pico_hash_concurrent_CT pico_hash_concurrent_receiver
    pico_hash_derive_method pico_hash_concurrent_initial_heap
    pico_hash_concurrent_value.

Notation hash_thread_run :=
  (@thread_run history_cache_memory_model pico_hash_concurrent_CT _ _
     hash_cache_protocol pico_hash_stable_abs pico_hash_concurrent_value
     (pico_hash_cache_adapter pico_hash_concurrent_receiver)
     pico_hash_machine).

(** Every control reached by a run of the call with a valid read trace is one
    of the phases of the method. *)
Lemma pico_hash_thread_run_phase : forall tr e,
  hash_thread_run (pico_hash_phase_control HashCall) tr e ->
  ValidTrace hash_cache_protocol pico_hash_concurrent_value tr ->
  pico_hash_thread_safe e.
Proof.
  intros tr e Hrun.
  induction Hrun as
    [| tr rGamma x y f V V' K old loc k v cv sigma Hrun IH Hx Hy Hread
         Hfield Hvalue
     | tr e S e' S' Hrun IH Hnoread Hinv Hstep];
    intros Hvalid.
  - exists HashCall. reflexivity.
  - apply Forall_app in Hvalid. destruct Hvalid as [Hvalid Hobs].
    destruct (IH Hvalid) as [phase Heq].
    destruct (pico_hash_cache_adapter_some _ _ _ Hfield) as [Haddr ->].
    injection Haddr as -> ->.
    simpl in Hvalue. injection Hvalue as <-.
    inversion Hobs as [| ? ? Hcv _]; subst.
    destruct Hread as [-> _].
    destruct phase; cbv in Heq; try discriminate Heq;
      injection Heq as -> -> -> -> ->.
    unfold ValidObs in Hcv. simpl in Hcv. unfold hash_cache_valid in Hcv.
    destruct Hcv as [-> | [-> _]].
    + exists HashReadZeroDone. reflexivity.
    + exists HashReadHitDone. reflexivity.
  - destruct (IH Hvalid) as [phase ->].
    exact (proj2 (pico_hash_phase_step_preserves phase S e' S'
      (proj1 Hinv) Hstep)).
Qed.

Theorem pico_hash_call_machine_cache_safe :
  @machine_cache_safe history_cache_memory_model pico_hash_concurrent_CT _ _
    hash_cache_protocol pico_hash_stable_abs pico_hash_concurrent_value
    (pico_hash_cache_adapter pico_hash_concurrent_receiver)
    pico_hash_machine pico_hash_result_ok
    (pico_hash_phase_control HashCall).
Proof.
  intros tr e Hrun Hvalid.
  destruct (pico_hash_thread_run_phase tr e Hrun Hvalid) as [phase Heq].
  split.
  - intros rGamma x f y V K loc v -> Hx Hy.
    destruct phase; cbv in Heq; try discriminate Heq.
    injection Heq as -> -> -> -> -> ->.
    cbv in Hx. injection Hx as <-.
    cbv in Hy. injection Hy as <-.
    right. exists HashField, (Int pico_hash_concurrent_value).
    split; [reflexivity |]. split; [reflexivity |].
    right. split; [reflexivity | discriminate].
  - intros r rGamma V ->.
    exact (pico_hash_safe_done_result r rGamma V (ex_intro _ phase Heq)).
Qed.

Lemma pico_hash_n_call_machine_pool : forall n,
  @machine_pool history_cache_memory_model pico_hash_concurrent_CT _ _
    hash_cache_protocol pico_hash_stable_abs pico_hash_concurrent_value
    (pico_hash_cache_adapter pico_hash_concurrent_receiver)
    pico_hash_machine pico_hash_result_ok
    (pico_hash_n_call_pool n).
Proof.
  intros n.
  split.
  - split; [exact pico_hash_concurrent_initial_provider_inv |].
    exact (proj2 (proj2 pico_hash_concurrent_initial_provider_inv)).
  - simpl. apply Forall_forall.
    intros e Hin. apply repeat_spec in Hin. subst e.
    apply machine_local_start.
    exact pico_hash_call_machine_cache_safe.
Qed.

(** The theorem for any number of hash calls, as an instance of the generic
    machine theorems. *)
Theorem pico_hash_n_calls_trace_robust : forall n cfg,
  @pico_pool_steps history_cache_memory_model pico_hash_concurrent_CT
    (pico_hash_n_call_pool n) cfg ->
  CacheHistSnapshotOK hash_cache_protocol
    (pico_hash_snapshot pico_hash_concurrent_receiver (pool_state cfg))
    pico_hash_concurrent_value /\
  pico_pool_results_satisfy pico_hash_result_ok cfg.
Proof.
  intros n cfg Hsteps.
  split.
  - exact (proj2 (machine_trace_robust_semimm _ _ _ _ _ _ _ _ _
      (pico_hash_n_call_machine_pool n) Hsteps)).
  - exact (machine_trace_robust_results _ _ _ _ _ _ _ _ _
      (pico_hash_n_call_machine_pool n) Hsteps).
Qed.
