From Stdlib Require Import List PeanoNat.
Import ListNotations.

Require Import MemoryModels.JAM.JamEvents MemoryModels.JAM.JamHistory
  MemoryModels.JAM.JamRelations.

(** * Well-Formed and Plain JAM Executions

    These obligations are the history-semantic foundation used by JAM: reads
    take their value from one already executed write to the same location, and
    reads-from is functional.  Access-mode-specific visibility and coherence
    can strengthen [jam_history_wf] without changing the cache bridge. *)

Record jam_history_wf (execution : jam_execution) : Prop := {
  jam_event_ids_unique : NoDup (jam_event_ids (jam_events execution));

  jam_rf_events : forall write read,
    jam_reads_from execution write read ->
    jam_event_in execution write /\ jam_event_in execution read;

  jam_rf_shapes : forall write read,
    jam_reads_from execution write read ->
    jam_is_write write /\
    jam_is_read read /\
    jam_same_location write read /\
    jam_same_value write read;

  jam_rf_executed_before : forall write read,
    jam_reads_from execution write read ->
    jam_trace_before (jam_events execution) write read;

  jam_reads_complete : forall read,
    jam_event_in execution read ->
    jam_is_read read ->
    exists write, jam_reads_from execution write read;

  jam_rf_functional : forall first second read,
    jam_reads_from execution first read ->
    jam_reads_from execution second read ->
    first = second
}.

Record jam_plain_legal (execution : jam_execution) : Prop := {
  jam_plain_history_wf : jam_history_wf execution;
  jam_plain_events : Forall jam_is_plain (jam_events execution);
  jam_plain_causality_acyclic :
    jam_acyclic (jam_plain_causality execution);
  jam_plain_coherence_acyclic :
    jam_acyclic (jam_plain_coherence execution)
}.

Lemma jam_plain_legal_history_wf : forall execution,
  jam_plain_legal execution -> jam_history_wf execution.
Proof.
  intros execution Hlegal.
  exact (jam_plain_history_wf execution Hlegal).
Qed.
