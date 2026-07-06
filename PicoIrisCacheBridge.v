From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spawn.

From Stdlib Require Import ZArith.

Require Import Syntax Helpers Typing Bigstep.
Require Import DerivedCache ConcurrentPico WeakPico DerivedCacheIris StringCacheIris.

(* This file is the artifact boundary between the two models.

   PICO gives a sequential semantic theorem for a final-field-derived cache
   update and a small interleaving machine for thread pools sharing one heap.
   This is sequentially consistent concurrency, not Java's weak memory model.

   WeakPico adds a second versioned model with explicit read observations.  It
   accepts weak cache writes only when the observed final-field snapshot is
   coherent with the shared heap at commit time.

   Iris/heap_lang gives a separate sequentially consistent concurrency model.
   We use it to model concurrent calls to a String-like hash cache method that
   share an invariant around the immutable payload and mutable cache fields.
*)

Section bridge.
  Context `{!heapGS Σ}.

  Definition pico_sequential_cache_result
      (CT : class_table) (h' : heap) (loc : Loc) (C : class_name)
      (abs_fields : list var) (cache_f : var)
      (derived : list value -> nat) (abs_vals : list value) : iProp Σ :=
    field_readsI h' loc abs_fields abs_vals ∧
    derived_int_cache_protocolI CT h' loc C abs_fields cache_f derived.

  Theorem pico_sequential_cache_result_from_eval :
    forall CT sΓ mt rΓ rΓ_mid h h' receiver tmp loc C abs_fields cache_f
           derived abs_vals old_cache_v n o,
      wf_r_config CT sΓ rΓ h ->
      stmt_typing CT sΓ mt (SVarAss tmp (EInt n)) sΓ ->
      stmt_typing CT sΓ mt (SFldWrite receiver cache_f tmp) sΓ ->
      rΓ_mid = set_vars rΓ (update tmp (Int n) (vars rΓ)) ->
      reachable_locations_from_initial_env CT h rΓ_mid =
        reachable_locations_from_initial_env CT h rΓ ->
      eval_stmt
        OK
        (reachable_locations_from_initial_env CT h rΓ)
        CT rΓ h
        (SSeq (SVarAss tmp (EInt n)) (SFldWrite receiver cache_f tmp))
        OK
        (reachable_locations_from_initial_env CT h rΓ)
        rΓ_mid h' ->
      runtime_getVal rΓ_mid receiver = Some (Iot loc) ->
      runtime_getVal rΓ_mid tmp = Some (Int n) ->
      runtime_getObj h loc = Some o ->
      rctype (rt_type o) = C ->
      final_fields CT C abs_fields ->
      cache_field CT C cache_f ->
      field_reads h loc abs_fields abs_vals ->
      field_read h loc cache_f old_cache_v ->
      n = derived abs_vals ->
      not (n = 0%nat) ->
      ⊢ pico_sequential_cache_result
          CT h' loc C abs_fields cache_f derived abs_vals.
  Proof.
    intros CT sΓ mt rΓ rΓ_mid h h' receiver tmp loc C abs_fields cache_f
           derived abs_vals old_cache_v n o
           Hwf Htype_compute Htype_write Hmid Hreach_stable Hseq
           Hreceiver_mid Htmp_mid Hobj HC Hfinals Hcache Hreads Hcache_read
           Hderived Hnz.
    unfold pico_sequential_cache_result.
    eapply derived_cache_update_sequence_soundI; eauto.
  Qed.

  Theorem pico_concurrent_cache_result_from_steps :
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
    intros CT cfg cfg' loc C abs_fields cache_f derived
           Hsteps Hsafe_all Hstate.
    eapply concurrent_steps_preserve_cache_state; eauto.
  Qed.

  Theorem pico_weak_cache_result_from_coherent_event :
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
    intros CT h h' derived e Haccepted.
    eapply weak_accepts_preserves_protocol; eauto.
  Qed.

  Theorem pico_weak_cache_result_from_coherent_execution :
    forall CT h h' events loc C abs_fields cache_f derived,
      weak_execution CT derived h events h' ->
      Forall (weak_event_targets_cache loc C abs_fields cache_f) events ->
      concurrent_derived_cache_state CT h loc C abs_fields cache_f derived ->
      concurrent_derived_cache_state CT h' loc C abs_fields cache_f derived.
  Proof.
    intros CT h h' events loc C abs_fields cache_f derived
           Hexec Htargets Hstate.
    eapply weak_execution_preserves_cache_state_for_target; eauto.
  Qed.

  Theorem iris_sc_concurrent_hash_result_from_spawn
      `{!spawnG Σ} N (Nspawn : namespace) o v c :
    {{{ ImmString N o v c }}}
      hashCode_spawn2_join o
    {{{ RET (#(deterministic_hash v c), #(deterministic_hash v c))%V;
        ImmString N o v c }}}.
  Proof.
    iIntros (Φ) "Himm HΦ".
    iApply (hashCode_spawn2_join_spec N Nspawn with "Himm").
    iExact "HΦ".
  Qed.
End bridge.
