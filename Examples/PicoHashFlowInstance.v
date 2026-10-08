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
  Examples.PicoCacheFlowJudgment Examples.PicoCacheClients
  Examples.PicoCacheFlowClients.
Require Import PICOBridge.PicoCoreLanguage
  PICOBridge.PicoMemoryModel PICOBridge.PicoCacheTyping
  PICOBridge.PicoCoreSemImm
  PICOBridge.PicoDerivationNoninterference
  PICOBridge.PicoSemanticConcurrency PICOBridge.PicoCoreTraceRobust.

(** * The Hash Class Satisfies the Flow Judgment

    The flow judgment and the class-table discipline are stated under
    hypotheses.  This file discharges all of them for the concrete hash
    class, so both results have a closed, well-typed instance: the hash
    method is accepted by the flow judgment, the class table is
    disciplined, and any number of hash calls together with any quiet
    threads preserve semantic immutability. *)

Notation hash_CT := pico_hash_concurrent_CT.
Notation hash_recv := pico_hash_concurrent_receiver.
Notation hash_h0 := pico_hash_concurrent_initial_heap.
Notation hash_H := pico_hash_concurrent_value.
Notation hash_Trecv := pico_hash_witness_receiver_type.

Notation hash_flow :=
  (flow hash_CT pico_hash_derivations hash_recv hash_h0 hash_H AbstractState).
Notation hash_sem := (sem hash_recv hash_H).

(** ** The leaves are well typed *)

Lemma hash_int_subtype :
  qualified_type_subtype hash_CT int_type int_type.
Proof. apply qtype_refl; simpl; [reflexivity | discriminate]. Qed.

Lemma hash_local_tmp_typing :
  stmt_typing hash_CT [hash_Trecv] AbstractState
    (SLocal int_type cache_tmp) [hash_Trecv; int_type].
Proof.
  eapply ST_Local with (T := int_type) (x := cache_tmp);
    [exact pico_hash_concurrent_wf_env1 | reflexivity ..].
Qed.

Lemma hash_local_result_typing :
  stmt_typing hash_CT [hash_Trecv; int_type] AbstractState
    (SLocal int_type cache_result) pico_hash_frame_senv.
Proof.
  eapply ST_Local with (T := int_type) (x := cache_result);
    [exact pico_hash_concurrent_wf_env2 | reflexivity ..].
Qed.

Lemma hash_int_assign_typing :
  forall n,
    stmt_typing hash_CT pico_hash_frame_senv AbstractState
      (SVarAss cache_tmp (EInt n)) pico_hash_frame_senv.
Proof.
  intros n.
  eapply ST_VarAss with (Te := int_type) (Tthis := hash_Trecv)
    (Tx := int_type).
  - exact pico_hash_concurrent_wf_env3.
  - apply ET_Int. exact pico_hash_concurrent_wf_env3.
  - reflexivity.
  - unfold cache_tmp. discriminate.
  - reflexivity.
  - exact hash_int_subtype.
Qed.

Lemma hash_copy_typing :
  stmt_typing hash_CT pico_hash_frame_senv AbstractState
    (SVarAss cache_result (EVar cache_tmp)) pico_hash_frame_senv.
Proof.
  eapply ST_VarAss with (Te := int_type) (Tthis := hash_Trecv)
    (Tx := int_type).
  - exact pico_hash_concurrent_wf_env3.
  - apply ET_Var; [exact pico_hash_concurrent_wf_env3 | reflexivity].
  - reflexivity.
  - unfold cache_result. discriminate.
  - reflexivity.
  - exact hash_int_subtype.
Qed.

(** ** The initializer yields the derived value *)

Lemma hash_sem_frame :
  forall rho,
    hash_sem [OThis; OSentinel; OSentinel] rho ->
    rho = pico_hash_frame_env.
Proof.
  intros [vs] Hs. unfold sem in Hs. simpl in Hs.
  repeat match goal with
         | Hf : Forall2 _ (_ :: _) _ |- _ => inversion Hf; subst; clear Hf
         | Hf : Forall2 _ [] _ |- _ => inversion Hf; subst; clear Hf
         end.
  simpl in *. subst. reflexivity.
Qed.

Lemma hash_compute_sem :
  forall rho rhob,
    hash_sem [OThis; OSentinel; OSentinel] rho ->
    eval_stmt hash_CT rho hash_h0 pico_hash_read_compute_stmt OK rhob
      hash_h0 ->
    hash_sem [OThis; ODerived; OOther] rhob.
Proof.
  intros rho rhob Hs Heval.
  have Hrho := hash_sem_frame rho Hs. subst rho.
  have Hval := pico_hash_compute_value rhob Heval.
  unfold pico_hash_read_compute_stmt in Heval.
  inversion Heval; subst.
  unfold runtime_getVal in Hval. simpl in Hval.
  injection Hval as ->.
  unfold sem. simpl.
  constructor; [reflexivity |].
  constructor; [reflexivity |].
  constructor; [exact I | constructor].
Qed.

(** ** The hash method is accepted *)

Theorem hash_method_flow :
  hash_flow [hash_Trecv] [OThis]
    (mbody_stmt (mbody pico_hash_concurrent_method_def))
    pico_hash_frame_senv [OThis; ODerived; ODerived].
Proof.
  change (mbody_stmt (mbody pico_hash_concurrent_method_def))
    with (pico_hash_method_stmt_with pico_hash_read_compute_stmt).
  apply (local_copy_flow hash_CT pico_hash_derivations hash_recv hash_h0
    hash_H hash_Trecv AbstractState pico_hash_read_compute_stmt).
  - exact hash_local_tmp_typing.
  - exact hash_local_result_typing.
  - exact hash_int_assign_typing.
  - exact hash_copy_typing.
  - discriminate.
  - exact pico_hash_compute_deriv.
  - exact pico_hash_compute_typing.
  - exact hash_compute_sem.
Qed.

(** The call is trace robust on the machine, by the flow judgment. *)
Theorem pico_hash_call_trace_robust_by_flow : forall V0,
  @machine_cache_safe history_cache_memory_model hash_CT _ _
    hash_cache_protocol pico_hash_stable_abs hash_H
    (pico_hash_cache_adapter hash_recv)
    (@pico_concrete_hash_semimm history_cache_memory_model
       hash_CT hash_recv pico_hash_derive_method hash_h0 hash_H)
    (cache_call_result_ok hash_H 1)
    (CoreRun pico_hash_concurrent_caller
       (SCall 1 pico_hash_concurrent_method 0 []) V0 []).
Proof.
  intros V0.
  eapply (flow_cache_method_trace_robust hash_CT pico_hash_derivations
    hash_recv pico_hash_derive_method hash_h0 hash_H
    pico_hash_concurrent_method pico_hash_concurrent_method_def
    hash_Trecv AbstractState
    (mkruntime_type Imm_r pico_hash_witness_class) [Int 0; Int 7]
    pico_hash_concurrent_caller 1 0).
  - exact pico_hash_concurrent_derivation_table.
  - exact pico_hash_concurrent_config_wf.
  - reflexivity.
  - exact pico_hash_concurrent_cache_declared.
  - exact pico_hash_concurrent_find_method.
  - reflexivity.
  - exact hash_method_flow.
  - reflexivity.
  - simpl. lia.
Qed.

(** Any number of calls, by the flow judgment. *)
Theorem pico_hash_n_calls_by_flow : forall n cfg,
  @pico_pool_steps history_cache_memory_model hash_CT
    (pico_hash_n_call_pool n) cfg ->
  CacheHistSnapshotOK hash_cache_protocol
    (pico_hash_snapshot hash_recv (pool_state cfg)) hash_H /\
  pico_pool_results_satisfy (cache_call_result_ok hash_H 1) cfg.
Proof.
  intros n cfg Hsteps.
  assert (Hpool : @machine_pool history_cache_memory_model
    hash_CT _ _ hash_cache_protocol pico_hash_stable_abs hash_H
    (pico_hash_cache_adapter hash_recv)
    (@pico_concrete_hash_semimm history_cache_memory_model
       hash_CT hash_recv pico_hash_derive_method hash_h0 hash_H)
    (cache_call_result_ok hash_H 1)
    (pico_hash_n_call_pool n)).
  { split.
    - split; [exact pico_hash_concurrent_initial_provider_inv |].
      exact (proj2 (proj2 pico_hash_concurrent_initial_provider_inv)).
    - simpl. apply Forall_forall.
      intros e Hin. apply repeat_spec in Hin. subst e.
      apply machine_local_start.
      exact (pico_hash_call_trace_robust_by_flow 0). }
  split.
  - exact (proj2 (machine_trace_robust_semimm _ _ _ _ _ _ _ _ _ Hpool Hsteps)).
  - exact (machine_trace_robust_results _ _ _ _ _ _ _ _ _ Hpool Hsteps).
Qed.

(** ** The class table is disciplined *)

Theorem hash_class_table_quiet :
  quiet_table pico_hash_concurrent_method hash_CT.
Proof.
  intros C m' md Hfind Hne.
  destruct C as [| [| C]].
  - (* the root class has no methods *)
    inversion Hfind as
      [CT C def own m mdef Hclass Hown Hget
      | CT C def parent m mdef own Hclass Hown Hnot Hsuper Hparent]; subst.
    + assert (def = pico_hash_witness_root_def)
        by (unfold find_class, gget in Hclass; simpl in Hclass; congruence).
      subst def. unfold gget_method in Hget. simpl in Hget. discriminate.
    + assert (def = pico_hash_witness_root_def)
        by (unfold find_class, gget in Hclass; simpl in Hclass; congruence).
      subst def. simpl in Hsuper. discriminate.
  - (* the hash class: the cache method and the derivation method *)
    inversion Hfind as
      [CT C def own m mdef Hclass Hown Hget
      | CT C def parent m mdef own Hclass Hown Hnot Hsuper Hparent]; subst.
    + assert (def = pico_hash_concurrent_class_def)
        by (unfold find_class, gget in Hclass; simpl in Hclass; congruence).
      subst def.
      destruct m' as [| [| m']].
      * exfalso. apply Hne. reflexivity.
      * unfold gget_method in Hget. simpl in Hget.
        injection Hget as <-. simpl. split; exact I.
      * unfold gget_method in Hget. simpl in Hget. discriminate.
    + assert (def = pico_hash_concurrent_class_def)
        by (unfold find_class, gget in Hclass; simpl in Hclass; congruence).
      subst def. simpl in Hsuper. injection Hsuper as <-.
      inversion Hparent as
        [CT C def own m mdef Hclass0 Hown0 Hget0
        | CT C def parent m mdef own Hclass0 Hown0 Hnot0 Hsuper0 Hparent0];
        subst.
      * assert (def = pico_hash_witness_root_def)
          by (unfold find_class, gget in Hclass0; simpl in Hclass0;
              congruence).
        subst def. unfold gget_method in Hget0. simpl in Hget0. discriminate.
      * assert (def = pico_hash_witness_root_def)
          by (unfold find_class, gget in Hclass0; simpl in Hclass0;
              congruence).
        subst def. simpl in Hsuper0. discriminate.
  - (* no other class *)
    inversion Hfind as
      [CT C' def own m mdef Hclass Hown Hget
      | CT C' def parent m mdef own Hclass Hown Hnot Hsuper Hparent]; subst;
      unfold find_class, gget in Hclass; simpl in Hclass;
      destruct C; discriminate.
Qed.

(** ** Hash calls alongside any quiet threads

    Any number of calls of the hash method, with any threads that run quiet
    code, preserve semantic immutability under every interleaving. *)
Theorem pico_hash_calls_and_quiet_threads_semimm :
  forall n clients cfg,
    Forall (quiet_control pico_hash_concurrent_method) clients ->
    @pico_pool_steps history_cache_memory_model hash_CT
      (mkPicoPoolConfig pico_hash_concurrent_initial_state
         (repeat (pico_hash_phase_control HashCall) n ++ clients)) cfg ->
    CacheHistSnapshotOK hash_cache_protocol
      (pico_hash_snapshot hash_recv (pool_state cfg)) hash_H.
Proof.
  intros n clients cfg Hquiet Hsteps.
  eapply (disciplined_pool_semimm hash_CT pico_hash_derivations hash_recv
    pico_hash_derive_method hash_h0 hash_H pico_hash_concurrent_method
    pico_hash_concurrent_method_def hash_Trecv AbstractState
    (mkruntime_type Imm_r pico_hash_witness_class) [Int 0; Int 7]
    pico_hash_concurrent_footprint_immutable hash_class_table_quiet
    pico_hash_concurrent_derivation_table pico_hash_concurrent_config_wf
    eq_refl pico_hash_concurrent_cache_declared
    pico_hash_concurrent_find_method
    pico_hash_frame_senv [OThis; ODerived; ODerived] hash_method_flow
    eq_refl 1).
  - split; [exact pico_hash_concurrent_initial_provider_inv |].
    exact (proj2 (proj2 pico_hash_concurrent_initial_provider_inv)).
  - apply Forall_app. split.
    + apply Forall_forall. intros e Hin. apply repeat_spec in Hin. subst e.
      left. exists pico_hash_concurrent_caller, 0, 0.
      split; [reflexivity |]. split; [reflexivity | simpl; lia].
    + eapply Forall_impl; [| exact Hquiet]. intros e He. right. exact He.
  - exact Hsteps.
Qed.
