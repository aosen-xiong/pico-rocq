From Stdlib Require Import List.

Require Import MemoryModels.JAM.JamEvents MemoryModels.JAM.JamHistory
  MemoryModels.JAM.JamFieldHistoryBridge.
Require Import MemoryModels.JMM.FinalFieldPublication
  MemoryModels.JMM.JamPublicationExecution
  MemoryModels.JMM.JlsCacheFragment.

(** * External JMM Adequacy Interface

    This file states the exact remaining obligation for connecting a complete
    JMM formalization to the cache theory.  It does not define JMM legality.
    Instead, an external model supplies:

    - its execution type and legality judgment;
    - a scope predicate selecting executions whose governed cache fields have
      whole-value, field-isolated accesses and whose abstract payload is
      justified by final-field publication;
    - a relation projecting one external execution to the supported JLS cache
      fragment.

    The projection is adequate only when every legal in-scope execution has a
    projected fragment execution satisfying [jls_cache_execution_legal].  The
    scope predicate is where an external Java proof must establish atomic
    cache-field admissibility, initialization, safe final-field publication,
    and exclusion of ungrounded reads. *)

Definition JmmCacheProjectionAdequate {JmmExecution : Type}
    (jmm_legal : JmmExecution -> Prop)
    (jmm_cache_in_scope : JmmExecution -> Prop)
    (projects_to_cache_fragment :
      JmmExecution ->
      list jls_cache_action ->
      (jam_event -> jam_event -> Prop) ->
      final_publication_state -> Prop) : Prop :=
  forall execution,
    jmm_legal execution ->
    jmm_cache_in_scope execution ->
    exists actions reads_from final,
      projects_to_cache_fragment execution actions reads_from final /\
      jls_cache_execution_legal actions reads_from final.

(** Adequacy of an external projection composes directly with the proved JLS
    fragment simulation.  Thus no external model needs to reason about the
    internal combined publication/JAM representation. *)
Theorem jmm_cache_projection_simulates_combined :
  forall {JmmExecution : Type}
    (jmm_legal : JmmExecution -> Prop)
    (jmm_cache_in_scope : JmmExecution -> Prop)
    (projects_to_cache_fragment :
      JmmExecution ->
      list jls_cache_action ->
      (jam_event -> jam_event -> Prop) ->
      final_publication_state -> Prop)
    (Hadequate : JmmCacheProjectionAdequate
      jmm_legal jmm_cache_in_scope projects_to_cache_fragment)
    execution
    (Hlegal : jmm_legal execution)
    (Hscope : jmm_cache_in_scope execution),
    exists actions reads_from final,
      projects_to_cache_fragment execution actions reads_from final /\
      combined_memory_execution_legal
        (jls_cache_to_combined actions) reads_from final.
Proof.
  intros JmmExecution jmm_legal jmm_cache_in_scope
    projects_to_cache_fragment Hadequate execution Hlegal Hscope.
  destruct (Hadequate execution Hlegal Hscope) as
    [actions [reads_from [final [Hprojects Hfragment]]]].
  exists actions, reads_from, final.
  split; [exact Hprojects |].
  eapply jls_cache_execution_simulates_combined.
  exact Hfragment.
Qed.

(** The same adequacy obligation yields the memory-side premise consumed by
    the generic cache theorem: every projected read observes a complete value
    appearing in the history of the same field address. *)
Theorem jmm_cache_projection_reads_from_field_history :
  forall {JmmExecution : Type}
    (jmm_legal : JmmExecution -> Prop)
    (jmm_cache_in_scope : JmmExecution -> Prop)
    (projects_to_cache_fragment :
      JmmExecution ->
      list jls_cache_action ->
      (jam_event -> jam_event -> Prop) ->
      final_publication_state -> Prop)
    (Hadequate : JmmCacheProjectionAdequate
      jmm_legal jmm_cache_in_scope projects_to_cache_fragment)
    execution
    (Hlegal : jmm_legal execution)
    (Hscope : jmm_cache_in_scope execution),
    exists actions reads_from final,
      projects_to_cache_fragment execution actions reads_from final /\
      forall read,
        In read (jls_cache_jam_events actions) ->
        jam_is_read read ->
        In (jam_event_value read)
          (jam_field_history
            (jls_cache_jam_execution actions reads_from)
            (jam_event_addr read)).
Proof.
  intros JmmExecution jmm_legal jmm_cache_in_scope
    projects_to_cache_fragment Hadequate execution Hlegal Hscope.
  destruct (Hadequate execution Hlegal Hscope) as
    [actions [reads_from [final [Hprojects Hfragment]]]].
  exists actions, reads_from, final.
  split; [exact Hprojects |].
  intros read Hin Hread.
  eapply jam_plain_read_from_same_field_history.
  - exact (jls_cache_jam_is_plain_legal
      actions reads_from final Hfragment).
  - exact Hin.
  - exact Hread.
Qed.
