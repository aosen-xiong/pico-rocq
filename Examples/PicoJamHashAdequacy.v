From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers.
Require Import Core.GenericDerivedCache.
Require Import Examples.PicoIfZeroCacheExamples
  Examples.PicoSemanticCacheAPIExamples
  Examples.PicoConcreteHashModel
  Examples.PicoSemanticConcurrencyExamples
  Examples.PicoSemanticConcurrencySafety.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoSemanticConcurrency
  PICOBridge.PicoIrisCoreLanguage PICOBridge.PicoLabeledExecution
  PICOBridge.PicoJamSimulation
  PICOBridge.PicoIrisSemImmLogicalRelation.
Require Import MemoryModels.JAM.JamEvents MemoryModels.JAM.JamHistory
  MemoryModels.JAM.JamRelations MemoryModels.JAM.JamLegality
  MemoryModels.JAM.JamFieldHistoryBridge.

(** * The Two-Invocation Hash Race under Plain JAM Accesses *)

Definition pico_hash_read0 : pico_access_event :=
  mkPicoAccessEvent 0 PicoRead
    (pico_hash_concurrent_receiver, hash_cache_field) (Int 0).

Definition pico_hash_read1 : pico_access_event :=
  mkPicoAccessEvent 1 PicoRead
    (pico_hash_concurrent_receiver, hash_cache_field) (Int 0).

Definition pico_hash_write1 : pico_access_event :=
  mkPicoAccessEvent 1 PicoWrite
    (pico_hash_concurrent_receiver, hash_cache_field)
    (Int pico_hash_concurrent_value).

Definition pico_hash_write0 : pico_access_event :=
  mkPicoAccessEvent 0 PicoWrite
    (pico_hash_concurrent_receiver, hash_cache_field)
    (Int pico_hash_concurrent_value).

Definition pico_hash_race_accesses : list pico_access_event :=
  [pico_hash_read0; pico_hash_read1; pico_hash_write1; pico_hash_write0].

Definition pico_hash_race_access_schedule : Prop :=
  exists before_read after_read0 after_read1 before_write after_write1
    after_write0,
    @pico_pool_steps history_cache_memory_model pico_hash_concurrent_CT
      pico_hash_concurrent_initial_pool before_read /\
    @pico_pool_access history_cache_memory_model pico_hash_concurrent_CT
      before_read pico_hash_read0 after_read0 /\
    @pico_pool_access history_cache_memory_model pico_hash_concurrent_CT
      after_read0 pico_hash_read1 after_read1 /\
    @pico_pool_steps history_cache_memory_model pico_hash_concurrent_CT
      after_read1 before_write /\
    @pico_pool_access history_cache_memory_model pico_hash_concurrent_CT
      before_write pico_hash_write1 after_write1 /\
    @pico_pool_access history_cache_memory_model pico_hash_concurrent_CT
      after_write1 pico_hash_write0 after_write0.

Theorem pico_hash_race_accesses_are_one_execution :
  pico_hash_race_access_schedule.
Proof.
  destruct pico_hash_concurrent_both_read_default_before_writes as
    [before_read [after_read0 [after_read1
      [Hreach [Hread0 [Hread1 [Hstate Hthreads]]]]]]].
  destruct after_read1 as [state threads]. simpl in Hstate, Hthreads.
  subst state threads.
  assert (Hmethod : @pico_core_steps history_cache_memory_model
    pico_hash_concurrent_CT pico_hash_concurrent_after_read_control
    pico_hash_concurrent_initial_state pico_hash_concurrent_write_control
    pico_hash_concurrent_initial_state).
  { apply pico_hash_concurrent_after_read_to_write. }
  assert (Hfirst : @pico_pool_steps history_cache_memory_model
    pico_hash_concurrent_CT
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [pico_hash_concurrent_after_read_control;
       pico_hash_concurrent_after_read_control])
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [pico_hash_concurrent_write_control;
       pico_hash_concurrent_after_read_control])).
  {
    change (@pico_pool_steps history_cache_memory_model
      pico_hash_concurrent_CT
      (mkPicoPoolConfig pico_hash_concurrent_initial_state
        [pico_hash_concurrent_after_read_control;
         pico_hash_concurrent_after_read_control])
      (mkPicoPoolConfig pico_hash_concurrent_initial_state
        (update 0 pico_hash_concurrent_write_control
          [pico_hash_concurrent_after_read_control;
           pico_hash_concurrent_after_read_control]))).
    eapply pico_pool_steps_lift_thread; simpl; eauto.
  }
  assert (Hsecond : @pico_pool_steps history_cache_memory_model
    pico_hash_concurrent_CT
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [pico_hash_concurrent_write_control;
       pico_hash_concurrent_after_read_control])
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [pico_hash_concurrent_write_control;
       pico_hash_concurrent_write_control])).
  {
    change (@pico_pool_steps history_cache_memory_model
      pico_hash_concurrent_CT
      (mkPicoPoolConfig pico_hash_concurrent_initial_state
        [pico_hash_concurrent_write_control;
         pico_hash_concurrent_after_read_control])
      (mkPicoPoolConfig pico_hash_concurrent_initial_state
        (update 1 pico_hash_concurrent_write_control
          [pico_hash_concurrent_write_control;
           pico_hash_concurrent_after_read_control]))).
    eapply pico_pool_steps_lift_thread; simpl; eauto.
  }
  exists before_read, after_read0,
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [pico_hash_concurrent_after_read_control;
       pico_hash_concurrent_after_read_control]),
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [pico_hash_concurrent_write_control;
       pico_hash_concurrent_write_control]),
    (mkPicoPoolConfig pico_hash_concurrent_bad_state
      [pico_hash_concurrent_write_control;
       pico_hash_concurrent_after_write_control]),
    (mkPicoPoolConfig pico_hash_concurrent_twice_state
      [pico_hash_concurrent_after_write_control;
       pico_hash_concurrent_after_write_control]).
  split; [exact Hreach |].
  split; [exact Hread0 |].
  split; [exact Hread1 |].
  split.
  - eapply pico_pool_steps_trans; eauto.
  - split.
    + exact pico_hash_concurrent_first_write.
    + exact pico_hash_concurrent_second_write.
Qed.

Definition pico_hash_jam_init : jam_event :=
  mkJamEvent 0 2 JamInit
    (pico_hash_concurrent_receiver, hash_cache_field) (Int 0) JamPlain.

Definition pico_hash_jam_read0 : jam_event :=
  mkJamEvent 1 0 JamRead
    (pico_hash_concurrent_receiver, hash_cache_field) (Int 0) JamPlain.

Definition pico_hash_jam_read1 : jam_event :=
  mkJamEvent 2 1 JamRead
    (pico_hash_concurrent_receiver, hash_cache_field) (Int 0) JamPlain.

Definition pico_hash_jam_write1 : jam_event :=
  mkJamEvent 3 1 JamWrite
    (pico_hash_concurrent_receiver, hash_cache_field)
    (Int pico_hash_concurrent_value) JamPlain.

Definition pico_hash_jam_write0 : jam_event :=
  mkJamEvent 4 0 JamWrite
    (pico_hash_concurrent_receiver, hash_cache_field)
    (Int pico_hash_concurrent_value) JamPlain.

Inductive pico_hash_jam_rf : jam_event -> jam_event -> Prop :=
  | PicoHashJamRfRead0 :
      pico_hash_jam_rf pico_hash_jam_init pico_hash_jam_read0
  | PicoHashJamRfRead1 :
      pico_hash_jam_rf pico_hash_jam_init pico_hash_jam_read1.

Definition pico_hash_jam_execution : jam_execution :=
  mkJamExecution
    [pico_hash_jam_init; pico_hash_jam_read0; pico_hash_jam_read1;
     pico_hash_jam_write1; pico_hash_jam_write0]
    pico_hash_jam_rf.

Lemma pico_hash_jam_execution_wf :
  jam_history_wf pico_hash_jam_execution.
Proof.
  refine {| jam_event_ids_unique := _;
            jam_rf_events := _;
            jam_rf_shapes := _;
            jam_rf_executed_before := _;
            jam_reads_complete := _;
            jam_rf_functional := _ |}.
  - unfold pico_hash_jam_execution, jam_event_ids. simpl.
    repeat constructor; simpl; intuition discriminate.
  - intros write read Hrf. inversion Hrf; subst;
      unfold jam_event_in, pico_hash_jam_execution; simpl; auto.
  - intros write read Hrf. inversion Hrf; subst;
      unfold jam_is_write, jam_is_read, jam_same_location, jam_same_value;
      simpl; repeat split; auto.
  - intros write read Hrf. inversion Hrf; subst.
    + unfold jam_trace_before, pico_hash_jam_execution. simpl.
      repeat split; auto; try lia.
      unfold jam_list_before.
      exists (@nil jam_event), (@nil jam_event),
        [pico_hash_jam_read1; pico_hash_jam_write1;
        pico_hash_jam_write0]. reflexivity.
    + unfold jam_trace_before, pico_hash_jam_execution. simpl.
      repeat split; auto; try lia.
      unfold jam_list_before.
      exists (@nil jam_event), [pico_hash_jam_read0],
        [pico_hash_jam_write1; pico_hash_jam_write0]. reflexivity.
  - intros read Hin Hread.
    unfold jam_event_in, pico_hash_jam_execution in Hin. simpl in Hin.
    destruct Hin as [Heq | [Heq | [Heq | [Heq | [Heq | Hfalse]]]]];
      try contradiction; subst read;
      unfold jam_is_read in Hread; simpl in Hread; try discriminate.
    + exists pico_hash_jam_init. constructor.
    + exists pico_hash_jam_init. constructor.
  - intros first second read Hfirst Hsecond.
    inversion Hfirst; inversion Hsecond; reflexivity.
Qed.

Lemma pico_hash_jam_rf_id_lt : forall write read,
  jam_reads_from pico_hash_jam_execution write read ->
  jam_event_id write < jam_event_id read.
Proof.
  intros write read Hrf.
  unfold jam_reads_from, pico_hash_jam_execution in Hrf. simpl in Hrf.
  inversion Hrf; subst; simpl; lia.
Qed.

Lemma pico_hash_jam_rf_source : forall write read,
  jam_reads_from pico_hash_jam_execution write read ->
  write = pico_hash_jam_init /\
  (read = pico_hash_jam_read0 \/ read = pico_hash_jam_read1).
Proof.
  intros write read Hrf.
  unfold jam_reads_from, pico_hash_jam_execution in Hrf. simpl in Hrf.
  inversion Hrf; subst; auto.
Qed.

Lemma pico_hash_jam_event_cases : forall event,
  jam_event_in pico_hash_jam_execution event ->
  event = pico_hash_jam_init \/
  event = pico_hash_jam_read0 \/
  event = pico_hash_jam_read1 \/
  event = pico_hash_jam_write1 \/
  event = pico_hash_jam_write0.
Proof.
  intros event Hin.
  unfold jam_event_in, pico_hash_jam_execution in Hin. simpl in Hin.
  destruct Hin as [Heq | [Heq | [Heq | [Heq | [Heq | Hfalse]]]]];
    try contradiction; auto.
Qed.

Lemma pico_hash_jam_po_id_lt : forall first second,
  jam_program_order pico_hash_jam_execution first second ->
  jam_event_id first < jam_event_id second.
Proof.
  intros first second Hpo.
  unfold jam_program_order, jam_trace_before in Hpo.
  exact (proj1 (proj2 (proj2 (proj2 Hpo)))).
Qed.

Lemma pico_hash_jam_po_write_read_impossible : forall write read,
  jam_program_order pico_hash_jam_execution write read ->
  jam_is_write write ->
  jam_is_read read ->
  False.
Proof.
  intros write read Hpo Hwrite Hread.
  unfold jam_program_order, jam_trace_before in Hpo.
  destruct Hpo as [Hthread [Hwrite_in [Hread_in [Hlt _]]]].
  destruct (pico_hash_jam_event_cases write Hwrite_in) as
    [-> | [-> | [-> | [-> | ->]]]];
  destruct (pico_hash_jam_event_cases read Hread_in) as
    [-> | [-> | [-> | [-> | ->]]]];
  unfold jam_is_write, jam_is_read in *; simpl in *;
  try discriminate; lia.
Qed.

Lemma pico_hash_jam_visibility_source_init : forall write read,
  jam_plain_visibility pico_hash_jam_execution write read ->
  write = pico_hash_jam_init.
Proof.
  intros write read Hvisible.
  unfold jam_plain_visibility in Hvisible.
  induction Hvisible.
  - exact (proj1 (pico_hash_jam_rf_source first second H)).
  - exact (proj1 (pico_hash_jam_rf_source first middle H)).
Qed.

Lemma pico_hash_jam_visible_write_to_read_source_init : forall write read,
  jam_plain_visible_or_po pico_hash_jam_execution write read ->
  jam_is_write write ->
  jam_is_read read ->
  write = pico_hash_jam_init.
Proof.
  intros write read [Hvisible | Hpo] Hwrite Hread.
  - eapply pico_hash_jam_visibility_source_init; eauto.
  - exfalso.
    eapply pico_hash_jam_po_write_read_impossible; eauto.
Qed.

Lemma pico_hash_jam_visible_or_po_id_lt : forall first second,
  jam_plain_visible_or_po pico_hash_jam_execution first second ->
  jam_event_id first < jam_event_id second.
Proof.
  intros first second [Hvisible | Hpo].
  - unfold jam_plain_visibility in Hvisible.
    eapply jam_plus_rank; [exact pico_hash_jam_rf_id_lt | exact Hvisible].
  - eapply pico_hash_jam_po_id_lt; eauto.
Qed.

Lemma pico_hash_jam_coherence_id_lt : forall first second,
  jam_plain_coherence pico_hash_jam_execution first second ->
  jam_event_id first < jam_event_id second.
Proof.
  intros first second Hcoherence.
  destruct Hcoherence as
    [first second addr Hvisible Hfirst_write Hsecond_write
    | first selected read addr Hvisible Hrf Hfirst_write Hread Hneq
    | first read second addr Hvisible Hpo Hfirst_write Hread Hsecond_write
    | first second first_read second_read addr Hfirst_rf Hsecond_rf Hpo
        Hfirst_write Hsecond_write Hneq].
  - eapply pico_hash_jam_visible_or_po_id_lt; eauto.
  - assert (Hfirst : first = pico_hash_jam_init).
    { eapply pico_hash_jam_visible_write_to_read_source_init;
        [exact Hvisible | exact (proj1 Hfirst_write) | exact (proj1 Hread)]. }
    assert (Hselected : selected = pico_hash_jam_init).
    { exact (proj1 (pico_hash_jam_rf_source selected read Hrf)). }
    subst first selected. contradiction.
  - assert (Hfirst : first = pico_hash_jam_init).
    { eapply pico_hash_jam_visible_write_to_read_source_init;
        [exact Hvisible | exact (proj1 Hfirst_write) | exact (proj1 Hread)]. }
    subst first.
    pose proof (pico_hash_jam_po_id_lt read second Hpo).
    simpl. lia.
  - assert (Hfirst : first = pico_hash_jam_init).
    { exact (proj1 (pico_hash_jam_rf_source first first_read Hfirst_rf)). }
    assert (Hsecond : second = pico_hash_jam_init).
    { exact (proj1 (pico_hash_jam_rf_source second second_read Hsecond_rf)). }
    subst first second. contradiction.
Qed.

Lemma pico_hash_jam_causality_acyclic :
  jam_acyclic (jam_plain_causality pico_hash_jam_execution).
Proof.
  eapply jam_ranked_relation_acyclic with (rank := jam_event_id).
  intros first second Hrf.
  exact (pico_hash_jam_rf_id_lt first second Hrf).
Qed.

Lemma pico_hash_jam_coherence_acyclic :
  jam_acyclic (jam_plain_coherence pico_hash_jam_execution).
Proof.
  eapply jam_ranked_relation_acyclic with (rank := jam_event_id).
  intros first second Hcoherence.
  exact (pico_hash_jam_coherence_id_lt first second Hcoherence).
Qed.

Theorem pico_hash_jam_execution_plain_legal :
  jam_plain_legal pico_hash_jam_execution.
Proof.
  refine {| jam_plain_history_wf := pico_hash_jam_execution_wf;
            jam_plain_events := _;
            jam_plain_causality_acyclic := pico_hash_jam_causality_acyclic;
            jam_plain_coherence_acyclic := pico_hash_jam_coherence_acyclic |}.
  unfold pico_hash_jam_execution, jam_is_plain. simpl.
  repeat constructor.
Qed.

Theorem pico_hash_race_realized_by_jam :
  pico_jam_realization pico_hash_race_accesses pico_hash_jam_execution.
Proof.
  exists [pico_hash_jam_init].
  exists [pico_hash_jam_read0; pico_hash_jam_read1;
    pico_hash_jam_write1; pico_hash_jam_write0].
  split.
  - reflexivity.
  - split.
    + constructor; [split; reflexivity | constructor].
    + unfold pico_hash_race_accesses, pico_hash_read0, pico_hash_read1,
        pico_hash_write1, pico_hash_write0, pico_hash_jam_read0,
        pico_hash_jam_read1, pico_hash_jam_write1, pico_hash_jam_write0,
        pico_access_matches_jam, pico_access_jam_kind.
      repeat constructor; repeat split; reflexivity.
Qed.

Theorem pico_hash_jam_reads_observe_initial_value :
  List.In (Int 0)
    (jam_field_history pico_hash_jam_execution
      (pico_hash_concurrent_receiver, hash_cache_field)).
Proof.
  eapply jam_plain_read_from_same_field_history with
    (read := pico_hash_jam_read0).
  - exact pico_hash_jam_execution_plain_legal.
  - unfold jam_event_in, pico_hash_jam_execution. simpl. auto.
  - unfold jam_is_read, pico_hash_jam_read0. reflexivity.
Qed.

(** JAM admissibility restricts the executions quantified over by the existing
    universal PICO theorem.  Since that theorem already proves safety for the
    larger history-based semantics, its result guarantee applies directly. *)
Theorem pico_hash_jam_admissible_results_correct :
  forall accesses cfg execution,
    @pico_pool_access_trace history_cache_memory_model
      pico_hash_concurrent_CT pico_hash_concurrent_initial_pool accesses cfg ->
    pico_jam_realization accesses execution ->
    jam_plain_legal execution ->
    pico_pool_results_satisfy pico_hash_result_ok cfg.
Proof.
  intros accesses cfg execution Htrace Hrealized Hlegal.
  apply pico_hash_pool_results_correct.
  eapply pico_pool_access_trace_erases; eauto.
Qed.

Theorem pico_hash_plain_jam_benign_race :
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
  pico_jam_realization pico_hash_race_accesses pico_hash_jam_execution /\
  jam_plain_legal pico_hash_jam_execution.
Proof.
  split.
  - exact pico_two_hash_invocations_semimm_benign_race.
  - split.
    + exact pico_hash_race_accesses_are_one_execution.
    + split.
      * exact pico_hash_race_realized_by_jam.
      * exact pico_hash_jam_execution_plain_legal.
Qed.
