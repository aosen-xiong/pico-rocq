Require Import Syntax Helpers Bigstep DerivedCache PICOBridge.ConcurrentPico.

From Stdlib Require Import List.
Import ListNotations.

(** * Weak-Memory-Facing PICO Model

    Unlike [ConcurrentPico], this file makes read observations explicit.  A weak
    execution may propose a cache write computed from observed abstract-field
    values.  We accept the write only when those observations are coherent with
    the final-field values in the shared heap at commit time.

    This is still not the full Java memory model.  It is the next artifact
    layer: it separates candidate weak executions from the safety condition
    needed for derived-cache soundness. *)

(** Candidate cache write with explicit observed abstract-field values. *)
Record weak_cache_write := mkWeakCacheWrite {
  weak_loc : Loc;
  weak_class : class_name;
  weak_abs_fields : list var;
  weak_cache_field : var;
  weak_observed_abs_vals : list value;
  weak_observed_old_cache : value;
  weak_written_cache_n : nat;
}.

(** Coherence condition for accepting a weak cache write. *)
Definition weak_cache_write_coherent
    (CT : class_table) (h : heap) (derived : list value -> nat)
    (e : weak_cache_write) : Prop :=
  exists o,
    runtime_getObj h (weak_loc e) = Some o /\
    rctype (rt_type o) = weak_class e /\
    final_fields CT (weak_class e) (weak_abs_fields e) /\
    cache_field CT (weak_class e) (weak_cache_field e) /\
    field_reads h (weak_loc e) (weak_abs_fields e)
      (weak_observed_abs_vals e) /\
    field_read h (weak_loc e) (weak_cache_field e)
      (weak_observed_old_cache e) /\
    weak_written_cache_n e = derived (weak_observed_abs_vals e) /\
    weak_written_cache_n e <> 0.

(** Commit relation for the concrete cache write. *)
Definition weak_cache_write_commit
    (h h' : heap) (e : weak_cache_write) : Prop :=
  h' =
    update_field h (weak_loc e) (weak_cache_field e)
      (Int (weak_written_cache_n e)).

Definition weak_candidate_cache_transition
    (h h' : heap) (e : weak_cache_write) : Prop :=
  weak_cache_write_commit h h' e.

Definition weak_accepts_cache_transition
    (CT : class_table) (h h' : heap) (derived : list value -> nat)
    (e : weak_cache_write) : Prop :=
  weak_candidate_cache_transition h h' e /\
  weak_cache_write_coherent CT h derived e.

Definition weak_rejects_cache_transition
    (CT : class_table) (h h' : heap) (derived : list value -> nat)
    (e : weak_cache_write) : Prop :=
  not (weak_accepts_cache_transition CT h h' derived e).

Lemma weak_accepts_preserves_protocol :
  forall CT h h' derived e,
    weak_accepts_cache_transition CT h h' derived e ->
    derived_int_cache_protocol
      CT h'
      (weak_loc e)
      (weak_class e)
      (weak_abs_fields e)
      (weak_cache_field e)
      derived.
Proof.
  intros CT h h' derived e [Hcommit Hcoherent].
  destruct Hcoherent as
    [o [Hobj [HC [Hfinals [Hcache [Hreads
      [Hcache_read [Hderived Hnz]]]]]]]].
  unfold weak_candidate_cache_transition, weak_cache_write_commit in Hcommit.
  eapply update_known_int_cache_preserves_protocol; eauto.
Qed.

Theorem weak_rejects_protocol_break :
  forall CT h h' derived e,
    weak_candidate_cache_transition h h' e ->
    not
      (derived_int_cache_protocol
        CT h'
        (weak_loc e)
        (weak_class e)
        (weak_abs_fields e)
        (weak_cache_field e)
        derived) ->
    weak_rejects_cache_transition CT h h' derived e.
Proof.
  intros CT h h' derived e Hcandidate Hbreak Haccepted.
  apply Hbreak.
  eapply weak_accepts_preserves_protocol; eauto.
Qed.

Definition weak_event_matches_sc_transition
    (CT : class_table) (h h' : heap) (derived : list value -> nat)
    (e : weak_cache_write) : Prop :=
  weak_accepts_cache_transition CT h h' derived e.

Theorem weak_accepted_event_is_sc_cache_safe :
  forall CT h h' derived e,
    weak_event_matches_sc_transition CT h h' derived e ->
    sc_accepts_cache_transition
      CT h h'
      (weak_loc e)
      (weak_class e)
      (weak_abs_fields e)
      (weak_cache_field e)
      derived.
Proof.
  intros CT h h' derived e [Hcommit Hcoherent].
  destruct Hcoherent as
    [o [Hobj [HC [_ [_ [Hreads
      [Hcache_read [Hderived Hnz]]]]]]]].
  unfold weak_candidate_cache_transition, weak_cache_write_commit in Hcommit.
  eapply sc_accepts_derived_cache_write; eauto.
Qed.

Definition weak_event_targets_cache
    (loc : Loc) (C : class_name) (abs_fields : list var) (cache_f : var)
    (e : weak_cache_write) : Prop :=
  weak_loc e = loc /\
  weak_class e = C /\
  weak_abs_fields e = abs_fields /\
  weak_cache_field e = cache_f.

Inductive weak_execution
    (CT : class_table) (derived : list value -> nat) :
    heap -> list weak_cache_write -> heap -> Prop :=
  | WE_Nil : forall h,
      weak_execution CT derived h [] h
  | WE_Cons : forall h h' h'' e es,
      weak_accepts_cache_transition CT h h' derived e ->
      weak_execution CT derived h' es h'' ->
      weak_execution CT derived h (e :: es) h''.

Inductive weak_candidate_execution :
    heap -> list weak_cache_write -> heap -> Prop :=
  | WCE_Nil : forall h,
      weak_candidate_execution h [] h
  | WCE_Cons : forall h h' h'' e es,
      weak_candidate_cache_transition h h' e ->
      weak_candidate_execution h' es h'' ->
      weak_candidate_execution h (e :: es) h''.

Inductive weak_coherent_candidate_execution
    (CT : class_table) (derived : list value -> nat) :
    heap -> list weak_cache_write -> heap -> Prop :=
  | WCCE_Nil : forall h,
      weak_coherent_candidate_execution CT derived h [] h
  | WCCE_Cons : forall h h' h'' e es,
      weak_candidate_cache_transition h h' e ->
      weak_cache_write_coherent CT h derived e ->
      weak_coherent_candidate_execution CT derived h' es h'' ->
      weak_coherent_candidate_execution CT derived h (e :: es) h''.

Definition weak_rejects_execution
    (CT : class_table) (derived : list value -> nat)
    (h : heap) (events : list weak_cache_write) (h' : heap) : Prop :=
  weak_candidate_execution h events h' /\
  not (weak_execution CT derived h events h').

Lemma weak_candidate_cache_transition_deterministic :
  forall h h1 h2 e,
    weak_candidate_cache_transition h h1 e ->
    weak_candidate_cache_transition h h2 e ->
    h1 = h2.
Proof.
  intros h h1 h2 e H1 H2.
  unfold weak_candidate_cache_transition, weak_cache_write_commit in *.
  congruence.
Qed.

Theorem weak_execution_to_coherent_candidate_execution :
  forall CT derived h events h',
    weak_execution CT derived h events h' ->
    weak_coherent_candidate_execution CT derived h events h'.
Proof.
  intros CT derived h events h' Hexec.
  induction Hexec as [h0 | h0 h1 h2 e es Haccepted Htail IH].
  - apply WCCE_Nil.
  - destruct Haccepted as [Hcandidate Hcoherent].
    eapply WCCE_Cons; eauto.
Qed.

Theorem weak_coherent_candidate_execution_to_execution :
  forall CT derived h events h',
    weak_coherent_candidate_execution CT derived h events h' ->
    weak_execution CT derived h events h'.
Proof.
  intros CT derived h events h' Hcoherent_exec.
  induction Hcoherent_exec as
    [h0 | h0 h1 h2 e es Hcandidate Hcoherent Htail IH].
  - apply WE_Nil.
  - eapply WE_Cons; eauto.
    split; assumption.
Qed.

Theorem weak_execution_iff_coherent_candidate_execution :
  forall CT derived h events h',
    weak_execution CT derived h events h' <->
    weak_coherent_candidate_execution CT derived h events h'.
Proof.
  split.
  - apply weak_execution_to_coherent_candidate_execution.
  - apply weak_coherent_candidate_execution_to_execution.
Qed.

Theorem weak_rejects_execution_at_head :
  forall CT derived h h1 h' e es,
    weak_candidate_cache_transition h h1 e ->
    weak_rejects_cache_transition CT h h1 derived e ->
    weak_candidate_execution h1 es h' ->
    weak_rejects_execution CT derived h (e :: es) h'.
Proof.
  intros CT derived h h1 h' e es Hcandidate Hreject Htail.
  split.
  - eapply WCE_Cons; eauto.
  - intro Haccepted_execution.
    inversion Haccepted_execution as
      [|h0 h_acc h_final e0 es0 Haccepted_head Haccepted_tail]; subst.
    destruct Haccepted_head as [Haccepted_candidate Hcoherent].
    assert (h_acc = h1).
    {
      eapply weak_candidate_cache_transition_deterministic; eauto.
    }
    subst h_acc.
    apply Hreject.
    split; assumption.
Qed.

Theorem weak_rejects_execution_with_rejected_event :
  forall CT derived h h_bad h_after h_final prefix e suffix,
    weak_candidate_execution h prefix h_bad ->
    weak_candidate_cache_transition h_bad h_after e ->
    weak_rejects_cache_transition CT h_bad h_after derived e ->
    weak_candidate_execution h_after suffix h_final ->
    weak_rejects_execution
      CT derived h (prefix ++ e :: suffix) h_final.
Proof.
  intros CT derived h h_bad h_after h_final prefix e suffix Hprefix.
  revert h_after h_final e suffix.
  induction Hprefix as [h0 | h0 h1 h2 e0 prefix_tail Hhead Htail IH].
  - intros h_after h_final e suffix Hbad_candidate Hbad_reject Hsuffix.
    simpl.
    eapply weak_rejects_execution_at_head; eauto.
  - intros h_after h_final e suffix Hbad_candidate Hbad_reject Hsuffix.
    simpl.
    destruct (IH h_after h_final e suffix
      Hbad_candidate Hbad_reject Hsuffix) as
      [Htail_candidate Htail_reject].
    split.
    + eapply WCE_Cons; eauto.
    + intro Haccepted_execution.
      inversion Haccepted_execution as
        [|h_start h_acc h_end e_head events_tail
          Haccepted_head Haccepted_tail]; subst.
      destruct Haccepted_head as [Haccepted_candidate _].
      assert (h_acc = h1).
      {
        eapply weak_candidate_cache_transition_deterministic; eauto.
      }
      subst h_acc.
      apply Htail_reject.
      exact Haccepted_tail.
Qed.

Lemma weak_accepts_preserves_cache_state_for_target :
  forall CT h h' loc C abs_fields cache_f derived e,
    weak_event_targets_cache loc C abs_fields cache_f e ->
    weak_accepts_cache_transition CT h h' derived e ->
    concurrent_derived_cache_state CT h loc C abs_fields cache_f derived ->
    concurrent_derived_cache_state CT h' loc C abs_fields cache_f derived.
Proof.
  intros CT h h' loc C abs_fields cache_f derived e
         [Hloc [HC_target [Habs Hcache_target]]] Haccepted _.
  destruct Haccepted as [Hcommit Hcoherent].
  destruct Hcoherent as
    [o [Hobj [HC [Hfinals [Hcache [Hreads
      [Hcache_read [Hderived Hnz]]]]]]]].
  unfold weak_candidate_cache_transition, weak_cache_write_commit in Hcommit.
  subst h'.
  subst loc C abs_fields cache_f.
  exists (set_fields_map o
    (update (weak_cache_field e) (Int (weak_written_cache_n e))
      (fields_map o))).
  split.
  - eapply update_cache_field_preserves_runtime_type; eauto.
  - split.
    + simpl. exact HC.
    + eapply update_known_int_cache_preserves_protocol; eauto.
Qed.

Theorem weak_execution_preserves_cache_state_for_target :
  forall CT h h' events loc C abs_fields cache_f derived,
    weak_execution CT derived h events h' ->
    Forall (weak_event_targets_cache loc C abs_fields cache_f) events ->
    concurrent_derived_cache_state CT h loc C abs_fields cache_f derived ->
    concurrent_derived_cache_state CT h' loc C abs_fields cache_f derived.
Proof.
  intros CT h h' events loc C abs_fields cache_f derived Hexec Htargets Hstate.
  induction Hexec as [h0 | h0 h1 h2 e es Haccepted Hexec_tail IH].
  - exact Hstate.
  - inversion Htargets as [|? ? Htarget Htargets_tail]; subst.
    apply IH; [exact Htargets_tail |].
    eapply weak_accepts_preserves_cache_state_for_target; eauto.
Qed.
