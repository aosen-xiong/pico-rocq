Require Import Syntax Helpers Bigstep DerivedCache DerivedCacheExamples.
Require Import ConcurrentPico.

From Stdlib Require Import List.
Import ListNotations.

Definition simple_sc_initial_heap : heap :=
  simple_heap (Int 41) (Int 0).

Definition simple_sc_cache_written_heap : heap :=
  update_field
    simple_sc_initial_heap simple_loc simple_cache_field
    (Int (simple_derived [Int 41])).

Definition simple_sc_final_changed_heap : heap :=
  simple_heap (Int 99) (Int 0).

Lemma simple_sc_accepts_cache_write :
  sc_accepts_cache_transition
    simple_CT
    simple_sc_initial_heap
    simple_sc_cache_written_heap
    simple_loc
    simple_class
    simple_abs_fields
    simple_cache_field
    simple_derived.
Proof.
  unfold simple_sc_initial_heap, simple_sc_cache_written_heap.
  eapply sc_accepts_derived_cache_write
    with
      (o := simple_obj (Int 41) (Int 0))
      (abs_vals := [Int 41])
      (old_cache_v := Int 0)
      (n := simple_derived [Int 41]).
  - reflexivity.
  - reflexivity.
  - apply simple_field_reads.
  - apply simple_cache_read.
  - reflexivity.
  - unfold simple_derived. discriminate.
  - reflexivity.
Qed.

Lemma simple_final_changed_heap_loses_original_final_read :
  not
    (field_reads
      simple_sc_final_changed_heap
      simple_loc
      simple_abs_fields
      [Int 41]).
Proof.
  intro Hreads.
  unfold simple_sc_final_changed_heap, simple_heap, simple_obj, simple_loc,
    simple_abs_fields in Hreads.
  inversion Hreads as [|? ? v vs Hread Htail]; subst.
  destruct Hread as [o [Hobj Hfield]].
  simpl in Hobj.
  inversion Hobj; subst.
  simpl in Hfield.
  discriminate.
Qed.

Lemma simple_sc_rejects_final_field_change :
  sc_rejects_cache_transition
    simple_CT
    simple_sc_initial_heap
    simple_sc_final_changed_heap
    simple_loc
    simple_class
    simple_abs_fields
    simple_cache_field
    simple_derived.
Proof.
  unfold simple_sc_initial_heap.
  eapply sc_rejects_final_read_change
    with
      (o := simple_obj (Int 41) (Int 0))
      (abs_vals := [Int 41]).
  - reflexivity.
  - reflexivity.
  - apply simple_final_fields.
  - apply simple_cache_field_assignable.
  - apply simple_field_reads.
  - apply simple_final_changed_heap_loses_original_final_read.
Qed.
