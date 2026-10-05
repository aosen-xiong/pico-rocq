From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Subtyping Typing Bigstep.
Require Import Core.GenericCacheProtocol Core.GenericDerivedCache.
Require Import Examples.PicoIfZeroCache
  Examples.PicoHashMethod
  Examples.PicoConcreteHashProvider
  Examples.PicoSemanticConcurrencyExamples
  Examples.PicoSemanticConcurrencySafety
  Examples.PicoCacheMethodJudgment.
Require Import PICOBridge.PicoCoreLanguage
  PICOBridge.PicoMemoryModel PICOBridge.PicoCacheTyping
  PICOBridge.PicoCoreSemImm
  PICOBridge.PicoDerivationNoninterference
  PICOBridge.PicoSemanticConcurrency PICOBridge.PicoCoreTraceRobust.

(** * The Hash Method Satisfies the Cache-Method Judgment

    The concrete hash method has the local-copy shape and its initializer
    reads the receiver's final payload, which is derivation code.  The
    judgment's soundness theorem therefore gives trace robustness of the
    call, with no analysis of the method's executions. *)

Definition pico_hash_frame_senv : s_env :=
  [pico_hash_witness_receiver_type; int_type; int_type].

Definition pico_hash_frame_env : r_env :=
  mkr_env [Iot pico_hash_concurrent_receiver; Int 0; Int 0].

Lemma pico_hash_compute_deriv :
  deriv_stmt pico_hash_concurrent_CT pico_hash_derivations
    pico_hash_frame_senv pico_hash_read_compute_stmt pico_hash_frame_senv.
Proof.
  apply DS_VarAss.
  eapply TSERO_Field with
    (T := pico_hash_witness_receiver_type) (C := pico_hash_witness_class).
  - reflexivity.
  - reflexivity.
  - exact (pico_hash_payload_abstract pico_hash_concurrent_CT
      pico_hash_concurrent_payload_field_def).
Qed.

Lemma pico_hash_compute_typing :
  stmt_typing pico_hash_concurrent_CT pico_hash_frame_senv AbstractState
    pico_hash_read_compute_stmt pico_hash_frame_senv.
Proof.
  unfold pico_hash_read_compute_stmt.
  eapply ST_VarAss with (Te := int_type)
    (Tthis := pico_hash_witness_receiver_type) (Tx := int_type).
  - exact pico_hash_concurrent_wf_env3.
  - change (expr_has_type pico_hash_concurrent_CT
      [pico_hash_witness_receiver_type; int_type; int_type] AbstractState
      (EField 0 1) (Build_qualified_type Imm TInt)).
    eapply ET_Field_abstract_state with
      (T := pico_hash_witness_receiver_type)
      (C := pico_hash_witness_class)
      (fDef := pico_hash_witness_payload_def).
    + exact pico_hash_concurrent_wf_env3.
    + reflexivity.
    + reflexivity.
    + exact pico_hash_concurrent_payload_field_def.
    + left. reflexivity.
  - reflexivity.
  - unfold cache_tmp. discriminate.
  - reflexivity.
  - apply qtype_refl; simpl; [reflexivity | discriminate].
Qed.

Lemma pico_hash_frame_config_wf :
  wf_r_config pico_hash_concurrent_CT pico_hash_frame_senv
    pico_hash_frame_env pico_hash_concurrent_initial_heap.
Proof.
  unfold wf_r_config.
  split; [exact pico_hash_concurrent_class_table_wf |].
  split; [exact pico_hash_concurrent_heap_wf |].
  split.
  - unfold wf_renv, pico_hash_concurrent_initial_heap,
      pico_hash_frame_env, pico_hash_concurrent_receiver. simpl.
    split; [lia |]. split.
    + exists 1. split; reflexivity || lia.
    + constructor; [simpl; trivial |].
      constructor; [trivial |]. constructor; [trivial | constructor].
  - split.
    + exact pico_hash_concurrent_wf_env3.
    + split; [reflexivity |].
      intros receiver qcontext Hreceiver Hmut i Hi T Htype.
      simpl in Hreceiver. inversion Hreceiver; subst receiver.
      unfold pico_hash_concurrent_initial_heap, pico_hash_witness_object,
        r_muttype, runtime_getObj in Hmut. simpl in Hmut.
      inversion Hmut; subst qcontext.
      destruct i as [| [| [| i]]]; [| | | simpl in Hi; lia].
      * simpl in Htype. inversion Htype; subst T. simpl.
        unfold wf_r_typable, r_type, pico_hash_concurrent_initial_heap,
          pico_hash_witness_object, runtime_getObj. simpl.
        split.
        -- apply base_ref. apply class_refl.
           unfold pico_hash_witness_class. simpl. lia.
        -- trivial.
      * simpl in Htype. inversion Htype; subst T. reflexivity.
      * simpl in Htype. inversion Htype; subst T. reflexivity.
Qed.

(** Evaluated in the reference heap, the initializer reads the payload. *)
Lemma pico_hash_compute_value : forall rGamma1,
  eval_stmt pico_hash_concurrent_CT pico_hash_frame_env
    pico_hash_concurrent_initial_heap pico_hash_read_compute_stmt OK rGamma1
    pico_hash_concurrent_initial_heap ->
  runtime_getVal rGamma1 cache_tmp = Some (Int pico_hash_concurrent_value).
Proof.
  intros rGamma1 Heval.
  unfold pico_hash_read_compute_stmt in Heval.
  inversion Heval; subst.
  match goal with
  | He : eval_expr _ _ _ (EField _ _) _ OK _ _ |- _ => inversion He; subst
  end.
  match goal with
  | Hv : runtime_getVal pico_hash_frame_env cache_receiver = Some (Iot ?l),
    Ho : runtime_getObj _ ?l = Some ?o,
    Hf : getVal (fields_map ?o) 1 = Some _ |- _ =>
      cbv in Hv; injection Hv as <-;
      cbv in Ho; injection Ho as <-;
      cbv in Hf; injection Hf as <-
  end.
  reflexivity.
Qed.

(** The call is trace robust on the machine, by the judgment alone. *)
Theorem pico_hash_call_trace_robust_by_judgment : forall V0,
  @machine_cache_safe history_cache_memory_model pico_hash_concurrent_CT _ _
    hash_cache_protocol pico_hash_stable_abs pico_hash_concurrent_value
    (pico_hash_cache_adapter pico_hash_concurrent_receiver)
    (@pico_concrete_hash_semimm history_cache_memory_model
       pico_hash_concurrent_CT pico_hash_concurrent_receiver
       pico_hash_derive_method pico_hash_concurrent_initial_heap
       pico_hash_concurrent_value)
    (cache_call_result_ok pico_hash_concurrent_value 1)
    (CoreRun pico_hash_concurrent_caller
       (SCall 1 pico_hash_concurrent_method 0 []) V0 []).
Proof.
  intros V0.
  eapply (cache_method_call_trace_robust pico_hash_concurrent_CT
    pico_hash_derivations pico_hash_concurrent_receiver
    pico_hash_derive_method pico_hash_concurrent_initial_heap
    pico_hash_concurrent_value pico_hash_read_compute_stmt
    pico_hash_concurrent_method pico_hash_concurrent_method_def
    pico_hash_witness_receiver_type pico_hash_frame_senv AbstractState
    (mkruntime_type Imm_r pico_hash_witness_class) [Int 0; Int 7]
    pico_hash_concurrent_caller 1 0).
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
  - simpl. lia.
Qed.

(** Any number of calls: semantic immutability is preserved, and every call
    that returns normally returns the hash. *)
Theorem pico_hash_n_calls_by_judgment : forall n cfg,
  @pico_pool_steps history_cache_memory_model pico_hash_concurrent_CT
    (pico_hash_n_call_pool n) cfg ->
  CacheHistSnapshotOK hash_cache_protocol
    (pico_hash_snapshot pico_hash_concurrent_receiver (pool_state cfg))
    pico_hash_concurrent_value /\
  pico_pool_results_satisfy
    (cache_call_result_ok pico_hash_concurrent_value 1) cfg.
Proof.
  intros n cfg Hsteps.
  assert (Hpool : @machine_pool history_cache_memory_model
    pico_hash_concurrent_CT _ _ hash_cache_protocol pico_hash_stable_abs
    pico_hash_concurrent_value
    (pico_hash_cache_adapter pico_hash_concurrent_receiver)
    (@pico_concrete_hash_semimm history_cache_memory_model
       pico_hash_concurrent_CT pico_hash_concurrent_receiver
       pico_hash_derive_method pico_hash_concurrent_initial_heap
       pico_hash_concurrent_value)
    (cache_call_result_ok pico_hash_concurrent_value 1)
    (pico_hash_n_call_pool n)).
  { split.
    - split; [exact pico_hash_concurrent_initial_provider_inv |].
      exact (proj2 (proj2 pico_hash_concurrent_initial_provider_inv)).
    - simpl. apply Forall_forall.
      intros e Hin. apply repeat_spec in Hin. subst e.
      apply machine_local_start.
      exact (pico_hash_call_trace_robust_by_judgment 0). }
  split.
  - exact (proj2 (machine_trace_robust_semimm _ _ _ _ _ _ _ _ _ Hpool Hsteps)).
  - exact (machine_trace_robust_results _ _ _ _ _ _ _ _ _ Hpool Hsteps).
Qed.
