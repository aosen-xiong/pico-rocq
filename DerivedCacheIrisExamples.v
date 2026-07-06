From iris.bi Require Import bi.
From iris.proofmode Require Import proofmode.

Require Import Syntax Helpers Bigstep DerivedCache DerivedCacheExamples
  DerivedCacheIris.

Section simple_derived_cache_iris_example.
  Context {PROP : bi}.

  Definition simple_cache_final_heap : heap :=
    update_field (simple_heap (Int 41) (Int 0)) simple_loc
      simple_cache_field (Int (simple_derived [Int 41])).

  Lemma simple_cache_compute_and_write_protocolI :
    ⊢ @derived_int_cache_protocolI PROP
        simple_CT
        simple_cache_final_heap
        simple_loc
        simple_class
        simple_abs_fields
        simple_cache_field
        simple_derived.
  Proof.
    apply derived_int_cache_protocolI_intro.
    unfold simple_cache_final_heap.
    apply simple_update_known_cache_protocol.
  Qed.

  Lemma simple_cache_write_preserves_final_readsI :
    ⊢ @field_readsI PROP
        simple_cache_final_heap
        simple_loc
        simple_abs_fields
        [Int 41].
  Proof.
    apply field_readsI_intro.
    unfold simple_cache_final_heap.
    eapply update_cache_field_preserves_final_field_reads
      with
        (CT := simple_CT)
        (C := simple_class)
        (o := simple_obj (Int 41) (Int 0)).
    - apply simple_object_lookup.
    - reflexivity.
    - apply simple_cache_field_assignable.
    - apply simple_final_fields.
    - apply simple_field_reads.
    - reflexivity.
  Qed.

  Lemma simple_cache_compute_and_write_eval_protocolI :
    exists h',
      eval_stmt
        OK
        (reachable_locations_from_initial_env
           simple_CT
           (simple_heap (Int 41) (Int 0))
           (simple_cache_env (Int 0)))
        simple_CT
        (simple_cache_env (Int 0))
        (simple_heap (Int 41) (Int 0))
        simple_cache_compute_and_write_stmt
        OK
        (reachable_locations_from_initial_env
           simple_CT
           (simple_heap (Int 41) (Int 0))
           (simple_cache_env (Int 0)))
        (simple_cache_env (Int (simple_derived [Int 41])))
      h' /\
      (⊢ @derived_int_cache_protocolI PROP
            simple_CT
            h'
            simple_loc
            simple_class
            simple_abs_fields
            simple_cache_field
            simple_derived).
  Proof.
    exists simple_cache_final_heap.
    split.
    - unfold simple_cache_final_heap.
      apply simple_cache_compute_and_write_eval.
    - apply simple_cache_compute_and_write_protocolI.
  Qed.

  Lemma simple_cache_compute_and_write_eval_soundI :
    exists h',
      eval_stmt
        OK
        (reachable_locations_from_initial_env
           simple_CT
           (simple_heap (Int 41) (Int 0))
           (simple_cache_env (Int 0)))
        simple_CT
        (simple_cache_env (Int 0))
        (simple_heap (Int 41) (Int 0))
        simple_cache_compute_and_write_stmt
        OK
        (reachable_locations_from_initial_env
           simple_CT
           (simple_heap (Int 41) (Int 0))
           (simple_cache_env (Int 0)))
        (simple_cache_env (Int (simple_derived [Int 41])))
        h' /\
      (⊢ @field_readsI PROP h' simple_loc simple_abs_fields [Int 41]) /\
      (⊢ @derived_int_cache_protocolI PROP
            simple_CT
            h'
            simple_loc
            simple_class
            simple_abs_fields
            simple_cache_field
            simple_derived).
  Proof.
    exists simple_cache_final_heap.
    repeat split.
    - unfold simple_cache_final_heap.
      apply simple_cache_compute_and_write_eval.
    - apply simple_cache_write_preserves_final_readsI.
    - apply simple_cache_compute_and_write_protocolI.
  Qed.

  Lemma simple_cache_compute_and_write_component_soundI :
    ⊢ @field_readsI PROP
        simple_cache_final_heap
        simple_loc
        simple_abs_fields
        [Int 41] ∧
      @derived_int_cache_protocolI PROP
        simple_CT
        simple_cache_final_heap
        simple_loc
        simple_class
        simple_abs_fields
        simple_cache_field
        simple_derived.
  Proof.
    unfold simple_cache_final_heap.
    eapply eval_int_compute_and_cache_write_soundI
      with
        (CT := simple_CT)
        (rΓ := simple_cache_env (Int 0))
        (rΓ_mid := simple_cache_env (Int (simple_derived [Int 41])))
        (receiver := 0)
        (tmp := simple_cache_tmp_var)
        (C := simple_class)
        (abs_vals := [Int 41])
        (old_cache_v := Int 0)
        (n := simple_derived [Int 41])
        (o := simple_obj (Int 41) (Int 0)).
    - apply simple_assign_literal_eval.
    - apply simple_cache_write_eval.
    - unfold simple_cache_env, simple_loc. reflexivity.
    - unfold simple_cache_env, simple_cache_tmp_var. reflexivity.
    - apply simple_object_lookup.
    - reflexivity.
    - apply simple_final_fields.
    - apply simple_cache_field_assignable.
    - apply simple_field_reads.
    - apply simple_cache_read.
    - unfold simple_derived. reflexivity.
    - unfold simple_derived. lia.
  Qed.
End simple_derived_cache_iris_example.
