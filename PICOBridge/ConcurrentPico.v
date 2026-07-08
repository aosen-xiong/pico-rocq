Require Import Syntax Helpers Typing Bigstep DerivedCache.

From Stdlib Require Import List Lia.
Import ListNotations.

(** * Sequentially Consistent Concurrent PICO

    This machine is intentionally smaller than Java's full memory model.  It is
    an interleaving semantics with one shared heap and one runtime environment
    plus residual statement per thread.  Heap updates are ordinary
    sequentially consistent steps.  This gives us a real concurrent PICO
    artifact to connect to the derived-cache invariant before adding
    weak-memory features. *)

(** Runtime state for one concurrent PICO thread. *)
Record thread_state := mkThread {
  thread_env : r_env;
  thread_stmt : stmt;
}.

(** Shared-heap thread-pool configuration. *)
Record concurrent_config := mkConcurrentConfig {
  concurrent_heap : heap;
  concurrent_threads : list thread_state;
}.

Definition residual_seq (s1 s2 : stmt) : stmt :=
  match s1 with
  | SSkip => s2
  | _ => SSeq s1 s2
  end.

(** One sequentially consistent thread step. *)
Inductive thread_step
    (CT : class_table) :
    heap -> thread_state -> heap -> thread_state -> Prop :=
  | TS_AssignInt : forall h rΓ x n old_v,
      runtime_getVal rΓ x = Some old_v ->
      thread_step CT h
        (mkThread rΓ (SVarAss x (EInt n)))
        h
        (mkThread (set_vars rΓ (update x (Int n) (vars rΓ))) SSkip)

  | TS_FldWrite : forall h h' rΓ x f y loc_x o a vf val_y,
      runtime_getVal rΓ x = Some (Iot loc_x) ->
      runtime_getObj h loc_x = Some o ->
      getVal (fields_map o) f = Some vf ->
      sf_assignability_rel CT (rctype (rt_type o)) f a ->
      runtime_getVal rΓ y = Some val_y ->
      runtime_vpa_assignability (rqtype (rt_type o)) a = Assignable ->
      h' = update_field h loc_x f val_y ->
      thread_step CT h
        (mkThread rΓ (SFldWrite x f y))
        h'
        (mkThread rΓ SSkip)

  | TS_SeqSkip : forall h rΓ s2,
      thread_step CT h
        (mkThread rΓ (SSeq SSkip s2))
        h
        (mkThread rΓ s2)

  | TS_SeqStep : forall h h' rΓ rΓ' s1 s1' s2,
      thread_step CT h (mkThread rΓ s1) h' (mkThread rΓ' s1') ->
      thread_step CT h
        (mkThread rΓ (SSeq s1 s2))
        h'
        (mkThread rΓ' (residual_seq s1' s2)).

(** One pool step selects and steps a single thread. *)
Inductive concurrent_step
    (CT : class_table) :
    concurrent_config -> concurrent_config -> Prop :=
  | CS_Thread : forall h h' threads threads' i t t',
      nth_error threads i = Some t ->
      thread_step CT h t h' t' ->
      threads' = update i t' threads ->
      concurrent_step CT
        (mkConcurrentConfig h threads)
        (mkConcurrentConfig h' threads').

Inductive concurrent_steps
    (CT : class_table) :
    concurrent_config -> concurrent_config -> Prop :=
  | CS_Refl : forall cfg,
      concurrent_steps CT cfg cfg
  | CS_Step : forall cfg1 cfg2 cfg3,
      concurrent_step CT cfg1 cfg2 ->
      concurrent_steps CT cfg2 cfg3 ->
      concurrent_steps CT cfg1 cfg3.

Definition concurrent_derived_cache_state
    (CT : class_table) (h : heap) (loc : Loc) (C : class_name)
    (abs_fields : list var) (cache_f : var)
    (derived : list value -> nat) : Prop :=
  exists o,
    runtime_getObj h loc = Some o /\
    rctype (rt_type o) = C /\
    derived_int_cache_protocol CT h loc C abs_fields cache_f derived.

Definition cache_safe_heap_transition
    (CT : class_table) (h h' : heap) (loc : Loc) (C : class_name)
    (abs_fields : list var) (cache_f : var)
    (derived : list value -> nat) : Prop :=
  h' = h \/
  exists o abs_vals old_cache_v n,
    runtime_getObj h loc = Some o /\
    rctype (rt_type o) = C /\
    field_reads h loc abs_fields abs_vals /\
    field_read h loc cache_f old_cache_v /\
    n = derived abs_vals /\
    n <> 0 /\
    h' = update_field h loc cache_f (Int n).

Definition sc_accepts_cache_transition
    (CT : class_table) (h h' : heap) (loc : Loc) (C : class_name)
    (abs_fields : list var) (cache_f : var)
    (derived : list value -> nat) : Prop :=
  cache_safe_heap_transition CT h h' loc C abs_fields cache_f derived.

Definition sc_rejects_cache_transition
    (CT : class_table) (h h' : heap) (loc : Loc) (C : class_name)
    (abs_fields : list var) (cache_f : var)
    (derived : list value -> nat) : Prop :=
  not (sc_accepts_cache_transition CT h h' loc C abs_fields cache_f derived).

Lemma sc_accepts_stutter :
  forall CT h loc C abs_fields cache_f derived,
    sc_accepts_cache_transition CT h h loc C abs_fields cache_f derived.
Proof.
  intros.
  left.
  reflexivity.
Qed.

Lemma sc_accepts_derived_cache_write :
  forall CT h h' loc C abs_fields cache_f derived abs_vals old_cache_v n o,
    runtime_getObj h loc = Some o ->
    rctype (rt_type o) = C ->
    field_reads h loc abs_fields abs_vals ->
    field_read h loc cache_f old_cache_v ->
    n = derived abs_vals ->
    n <> 0 ->
    h' = update_field h loc cache_f (Int n) ->
    sc_accepts_cache_transition CT h h' loc C abs_fields cache_f derived.
Proof.
  intros CT h h' loc C abs_fields cache_f derived abs_vals old_cache_v n o
         Hobj HC Hreads Hcache_read Hderived Hnz Hupdate.
  right.
  exists o, abs_vals, old_cache_v, n.
  repeat split; assumption.
Qed.

Lemma sc_accepted_transition_preserves_final_reads :
  forall CT h h' loc C abs_fields cache_f derived abs_vals o,
    runtime_getObj h loc = Some o ->
    rctype (rt_type o) = C ->
    final_fields CT C abs_fields ->
    cache_field CT C cache_f ->
    field_reads h loc abs_fields abs_vals ->
    sc_accepts_cache_transition CT h h' loc C abs_fields cache_f derived ->
    field_reads h' loc abs_fields abs_vals.
Proof.
  intros CT h h' loc C abs_fields cache_f derived abs_vals o
         Hobj HC Hfinals Hcache Hreads Haccepted.
  destruct Haccepted as [Heq | Hwrite].
  - subst h'. exact Hreads.
  - destruct Hwrite as
      [o_write [abs_vals_write [old_cache_v [n
        [Hobj_write [HC_write [Hreads_write
          [Hcache_read [Hderived [Hnz Hupdate]]]]]]]]]].
    eapply update_cache_field_preserves_final_field_reads; eauto.
Qed.

Theorem sc_rejects_final_read_change :
  forall CT h h' loc C abs_fields cache_f derived abs_vals o,
    runtime_getObj h loc = Some o ->
    rctype (rt_type o) = C ->
    final_fields CT C abs_fields ->
    cache_field CT C cache_f ->
    field_reads h loc abs_fields abs_vals ->
    not (field_reads h' loc abs_fields abs_vals) ->
    sc_rejects_cache_transition CT h h' loc C abs_fields cache_f derived.
Proof.
  intros CT h h' loc C abs_fields cache_f derived abs_vals o
         Hobj HC Hfinals Hcache Hreads Hchanged Haccepted.
  apply Hchanged.
  eapply sc_accepted_transition_preserves_final_reads; eauto.
Qed.

Lemma cache_safe_heap_transition_preserves_cache_state :
  forall CT h h' loc C abs_fields cache_f derived,
    concurrent_derived_cache_state CT h loc C abs_fields cache_f derived ->
    cache_safe_heap_transition CT h h' loc C abs_fields cache_f derived ->
    concurrent_derived_cache_state CT h' loc C abs_fields cache_f derived.
Proof.
  intros CT h h' loc C abs_fields cache_f derived Hstate Hsafe.
  destruct Hsafe as [Heq | Hsafe].
  - subst h'. exact Hstate.
  - destruct Hsafe as
      [o [abs_vals [old_cache_v [n
        [Hobj [HC [Hreads [Hcache_read [Hderived [Hnz Hupdate]]]]]]]]]].
    destruct Hstate as [o0 [Hobj0 [HC0 Hprotocol]]].
    assert (o0 = o) by congruence.
    subst o0.
    subst h'.
    exists (set_fields_map o (update cache_f (Int n) (fields_map o))).
    split.
    + eapply update_cache_field_preserves_runtime_type; eauto.
    + split.
      * simpl. exact HC.
      * eapply update_known_int_cache_preserves_existing_protocol; eauto.
Qed.

Theorem concurrent_step_preserves_cache_state :
  forall CT cfg cfg' loc C abs_fields cache_f derived,
    concurrent_step CT cfg cfg' ->
    concurrent_derived_cache_state
      CT (concurrent_heap cfg) loc C abs_fields cache_f derived ->
    cache_safe_heap_transition
      CT (concurrent_heap cfg) (concurrent_heap cfg')
      loc C abs_fields cache_f derived ->
    concurrent_derived_cache_state
      CT (concurrent_heap cfg') loc C abs_fields cache_f derived.
Proof.
  intros CT cfg cfg' loc C abs_fields cache_f derived _ Hstate Hsafe.
  eapply cache_safe_heap_transition_preserves_cache_state; eauto.
Qed.

Theorem concurrent_steps_preserve_cache_state :
  forall CT cfg cfg' loc C abs_fields cache_f derived,
    concurrent_steps CT cfg cfg' ->
    (forall c1 c2,
      concurrent_step CT c1 c2 ->
      cache_safe_heap_transition
        CT (concurrent_heap c1) (concurrent_heap c2)
        loc C abs_fields cache_f derived) ->
    concurrent_derived_cache_state
      CT (concurrent_heap cfg) loc C abs_fields cache_f derived ->
    concurrent_derived_cache_state
      CT (concurrent_heap cfg') loc C abs_fields cache_f derived.
Proof.
  intros CT cfg cfg' loc C abs_fields cache_f derived Hsteps Hsafe_all Hstate.
  induction Hsteps as [cfg0 | cfg1 cfg2 cfg3 Hstep Hsteps_tail IH].
  - exact Hstate.
  - apply IH.
    eapply concurrent_step_preserves_cache_state; eauto.
Qed.
