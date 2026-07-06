Require Import Syntax Helpers Typing Bigstep DerivedCache DerivedCacheExamples.
Require Import ConcurrentPico WeakPico ConcurrentPicoExamples.

From Stdlib Require Import List Lia.
Import ListNotations.

Definition simple_weak_coherent_event : weak_cache_write :=
  mkWeakCacheWrite
    simple_loc
    simple_class
    simple_abs_fields
    simple_cache_field
    [Int 41]
    (Int 0)
    (simple_derived [Int 41]).

Definition simple_weak_incoherent_event : weak_cache_write :=
  mkWeakCacheWrite
    simple_loc
    simple_class
    simple_abs_fields
    simple_cache_field
    [Int 99]
    (Int 0)
    (simple_derived [Int 99]).

Definition simple_weak_coherent_rewrite_event : weak_cache_write :=
  mkWeakCacheWrite
    simple_loc
    simple_class
    simple_abs_fields
    simple_cache_field
    [Int 41]
    (Int (simple_derived [Int 41]))
    (simple_derived [Int 41]).

Definition simple_weak_bad_heap : heap :=
  update_field
    simple_sc_initial_heap
    simple_loc
    simple_cache_field
    (Int (simple_derived [Int 99])).

Lemma simple_weak_accepts_coherent_cache_write :
  weak_accepts_cache_transition
    simple_CT
    simple_sc_initial_heap
    simple_sc_cache_written_heap
    simple_derived
    simple_weak_coherent_event.
Proof.
  split.
  - reflexivity.
  - exists (simple_obj (Int 41) (Int 0)).
    split; [reflexivity |].
    split; [reflexivity |].
    split; [apply simple_final_fields |].
    split; [apply simple_cache_field_assignable |].
    split; [apply simple_field_reads |].
    split; [apply simple_cache_read |].
    split; [reflexivity |].
    unfold simple_derived. discriminate.
Qed.

Lemma simple_weak_bad_heap_not_protocol :
  not
    (derived_int_cache_protocol
      simple_CT
      simple_weak_bad_heap
      simple_loc
      simple_class
      simple_abs_fields
      simple_cache_field
      simple_derived).
Proof.
  intro Hprotocol.
  destruct Hprotocol as
    [abs_vals [cache_v [_ [_ [Hreads [Hcache_read Hcache_value]]]]]].
  unfold simple_weak_bad_heap, simple_sc_initial_heap, simple_heap, simple_obj,
    simple_loc, simple_abs_fields, simple_cache_field in *.
  simpl in Hreads.
  inversion Hreads as [|? ? abs_v abs_tail Hread_abs Hreads_tail]; subst.
  inversion Hreads_tail; subst.
  destruct Hread_abs as [o_abs [Hobj_abs Hfield_abs]].
  simpl in Hobj_abs.
  inversion Hobj_abs; subst.
  simpl in Hfield_abs.
  inversion Hfield_abs; subst.
  destruct Hcache_read as [o_cache [Hobj_cache Hfield_cache]].
  simpl in Hobj_cache.
  inversion Hobj_cache; subst.
  simpl in Hfield_cache.
  inversion Hfield_cache; subst.
  simpl in Hcache_value.
  destruct Hcache_value as [Hunknown | Hknown].
  - discriminate.
  - destruct Hknown as [n [Hcache_eq [Hderived Hnz]]].
    assert (Hn : n = simple_derived [Int 99]).
    { inversion Hcache_eq. reflexivity. }
    simpl in Hderived.
    simpl in Hn.
    lia.
Qed.

Lemma simple_weak_rejects_incoherent_cache_write :
  weak_rejects_cache_transition
    simple_CT
    simple_sc_initial_heap
    simple_weak_bad_heap
    simple_derived
    simple_weak_incoherent_event.
Proof.
  eapply weak_rejects_protocol_break.
  - reflexivity.
  - apply simple_weak_bad_heap_not_protocol.
Qed.

Lemma simple_weak_coherent_event_targets_cache :
  weak_event_targets_cache
    simple_loc
    simple_class
    simple_abs_fields
    simple_cache_field
    simple_weak_coherent_event.
Proof.
  repeat split; reflexivity.
Qed.

Lemma simple_weak_coherent_rewrite_event_targets_cache :
  weak_event_targets_cache
    simple_loc
    simple_class
    simple_abs_fields
    simple_cache_field
    simple_weak_coherent_rewrite_event.
Proof.
  repeat split; reflexivity.
Qed.

Lemma simple_sc_cache_written_heap_stable_write :
  weak_accepts_cache_transition
    simple_CT
    simple_sc_cache_written_heap
    simple_sc_cache_written_heap
    simple_derived
    simple_weak_coherent_rewrite_event.
Proof.
  split.
  - reflexivity.
  - unfold simple_sc_cache_written_heap, simple_sc_initial_heap,
      simple_weak_coherent_rewrite_event.
    simpl.
    exists (simple_obj (Int 41) (Int (simple_derived [Int 41]))).
    split; [reflexivity |].
    split; [reflexivity |].
    split; [apply simple_final_fields |].
    split; [apply simple_cache_field_assignable |].
    split.
    + unfold simple_heap, simple_obj, simple_loc, simple_abs_fields.
      constructor.
      * unfold field_read.
        exists (mkObj (mkruntime_type Imm_r simple_class)
          [Int 41; Int (simple_derived [Int 41])]).
        split; reflexivity.
      * constructor.
    + split.
      * unfold field_read, simple_heap, simple_obj, simple_loc,
          simple_cache_field.
        exists (mkObj (mkruntime_type Imm_r simple_class)
          [Int 41; Int (simple_derived [Int 41])]).
        split; reflexivity.
      * split; [reflexivity |].
        unfold simple_derived. discriminate.
Qed.

Lemma simple_weak_two_duplicate_writes_execution :
  weak_execution
    simple_CT
    simple_derived
    simple_sc_initial_heap
    [simple_weak_coherent_event; simple_weak_coherent_rewrite_event]
    simple_sc_cache_written_heap.
Proof.
  eapply WE_Cons.
  - apply simple_weak_accepts_coherent_cache_write.
  - eapply WE_Cons.
    + apply simple_sc_cache_written_heap_stable_write.
    + apply WE_Nil.
Qed.

Lemma simple_initial_concurrent_cache_state :
  concurrent_derived_cache_state
    simple_CT
    simple_sc_initial_heap
    simple_loc
    simple_class
    simple_abs_fields
    simple_cache_field
    simple_derived.
Proof.
  exists (simple_obj (Int 41) (Int 0)).
  split; [reflexivity |].
  split; [reflexivity |].
  exists [Int 41], (Int 0).
  repeat split.
  - apply simple_final_fields.
  - apply simple_cache_field_assignable.
  - apply simple_field_reads.
  - apply simple_cache_read.
  - left. reflexivity.
Qed.

Lemma simple_weak_two_duplicate_writes_preserve_cache_state :
  concurrent_derived_cache_state
    simple_CT
    simple_sc_cache_written_heap
    simple_loc
    simple_class
    simple_abs_fields
    simple_cache_field
    simple_derived.
Proof.
  eapply weak_execution_preserves_cache_state_for_target.
  - apply simple_weak_two_duplicate_writes_execution.
  - constructor.
    + apply simple_weak_coherent_event_targets_cache.
    + constructor.
      * apply simple_weak_coherent_rewrite_event_targets_cache.
      * constructor.
  - apply simple_initial_concurrent_cache_state.
Qed.

Definition pair_left_field : var := 0.
Definition pair_right_field : var := 1.
Definition pair_cache_field : var := 2.
Definition pair_root_class : class_name := 0.
Definition pair_class : class_name := 1.

Definition pair_left_field_def : field_def :=
  {|
    ftype :=
      {|
        assignability := Final;
        mutability := Imm_f;
        f_base_type := int_class_name
      |};
    fname := pair_left_field
  |}.

Definition pair_right_field_def : field_def :=
  {|
    ftype :=
      {|
        assignability := Final;
        mutability := Imm_f;
        f_base_type := int_class_name
      |};
    fname := pair_right_field
  |}.

Definition pair_cache_field_def : field_def :=
  {|
    ftype :=
      {|
        assignability := Assignable;
        mutability := Imm_f;
        f_base_type := int_class_name
      |};
    fname := pair_cache_field
  |}.

Definition pair_constructor : constructor_def :=
  {|
    csignature :=
      {|
        cqualifier := Imm_c;
        cparams := []
      |}
  |}.

Definition pair_root_class_def : class_def :=
  {|
    signature :=
      {|
        class_qualifier := Imm_c;
        cname := pair_root_class;
        super := None
      |};
    body :=
      {|
        fields := [];
        constructor := pair_constructor;
        methods := []
      |}
  |}.

Definition pair_class_def : class_def :=
  {|
    signature :=
      {|
        class_qualifier := Imm_c;
        cname := pair_class;
        super := Some pair_root_class
      |};
    body :=
      {|
        fields := [pair_left_field_def; pair_right_field_def;
          pair_cache_field_def];
        constructor := pair_constructor;
        methods := []
      |}
  |}.

Definition pair_CT : class_table := [pair_root_class_def; pair_class_def].

Definition pair_obj (left_v right_v cache_v : value) : Obj :=
  mkObj
    (mkruntime_type Imm_r pair_class)
    [left_v; right_v; cache_v].

Definition pair_heap (left_v right_v cache_v : value) : heap :=
  [pair_obj left_v right_v cache_v].

Definition pair_loc : Loc := 0.

Definition pair_abs_fields : list var := [pair_left_field; pair_right_field].

Definition pair_derived (vs : list value) : nat :=
  match vs with
  | [Int left_n; Int right_n] => left_n + right_n
  | _ => 1
  end.

Definition pair_initial_heap : heap :=
  pair_heap (Int 1) (Int 2) (Int 0).

Definition pair_mixed_snapshot_event : weak_cache_write :=
  mkWeakCacheWrite
    pair_loc
    pair_class
    pair_abs_fields
    pair_cache_field
    [Int 1; Int 99]
    (Int 0)
    (pair_derived [Int 1; Int 99]).

Definition pair_mixed_snapshot_heap : heap :=
  update_field
    pair_initial_heap
    pair_loc
    pair_cache_field
    (Int (pair_derived [Int 1; Int 99])).

Lemma pair_left_field_final :
  final_field pair_CT pair_class pair_left_field.
Proof.
  unfold final_field, sf_assignability_rel, pair_CT, pair_class,
    pair_left_field.
  exists pair_left_field_def.
  split.
  - apply FL_Found with
      (fields := [] ++ [pair_left_field_def; pair_right_field_def;
        pair_cache_field_def]).
    + eapply CF_Inherit.
      * reflexivity.
      * reflexivity.
      * apply CF_Object with (def := pair_root_class_def); reflexivity.
      * reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma pair_right_field_final :
  final_field pair_CT pair_class pair_right_field.
Proof.
  unfold final_field, sf_assignability_rel, pair_CT, pair_class,
    pair_right_field.
  exists pair_right_field_def.
  split.
  - apply FL_Found with
      (fields := [] ++ [pair_left_field_def; pair_right_field_def;
        pair_cache_field_def]).
    + eapply CF_Inherit.
      * reflexivity.
      * reflexivity.
      * apply CF_Object with (def := pair_root_class_def); reflexivity.
      * reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma pair_cache_field_assignable :
  cache_field pair_CT pair_class pair_cache_field.
Proof.
  unfold cache_field, sf_assignability_rel, pair_CT, pair_class,
    pair_cache_field.
  exists pair_cache_field_def.
  split.
  - apply FL_Found with
      (fields := [] ++ [pair_left_field_def; pair_right_field_def;
        pair_cache_field_def]).
    + eapply CF_Inherit.
      * reflexivity.
      * reflexivity.
      * apply CF_Object with (def := pair_root_class_def); reflexivity.
      * reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma pair_final_fields :
  final_fields pair_CT pair_class pair_abs_fields.
Proof.
  unfold final_fields, pair_abs_fields.
  repeat constructor.
  - apply pair_left_field_final.
  - apply pair_right_field_final.
Qed.

Lemma pair_field_reads :
  forall left_v right_v cache_v,
    field_reads (pair_heap left_v right_v cache_v) pair_loc pair_abs_fields
      [left_v; right_v].
Proof.
  intros left_v right_v cache_v.
  unfold field_reads, pair_heap, pair_obj, pair_loc, pair_abs_fields.
  repeat constructor.
  - unfold field_read.
    exists (mkObj (mkruntime_type Imm_r pair_class)
      [left_v; right_v; cache_v]).
    split; reflexivity.
  - unfold field_read.
    exists (mkObj (mkruntime_type Imm_r pair_class)
      [left_v; right_v; cache_v]).
    split; reflexivity.
Qed.

Lemma pair_cache_read :
  forall left_v right_v cache_v,
    field_read (pair_heap left_v right_v cache_v) pair_loc pair_cache_field
      cache_v.
Proof.
  intros left_v right_v cache_v.
  unfold field_read, pair_heap, pair_obj, pair_loc, pair_cache_field.
  exists (mkObj (mkruntime_type Imm_r pair_class)
    [left_v; right_v; cache_v]).
  split; reflexivity.
Qed.

Lemma pair_mixed_snapshot_heap_not_protocol :
  not
    (derived_int_cache_protocol
      pair_CT
      pair_mixed_snapshot_heap
      pair_loc
      pair_class
      pair_abs_fields
      pair_cache_field
      pair_derived).
Proof.
  intro Hprotocol.
  destruct Hprotocol as
    [abs_vals [cache_v [_ [_ [Hreads [Hcache_read Hcache_value]]]]]].
  unfold pair_mixed_snapshot_heap, pair_initial_heap, pair_heap, pair_obj,
    pair_loc, pair_abs_fields, pair_cache_field in *.
  simpl in Hreads.
  inversion Hreads as [|? ? left_v rest Hread_left Hreads_tail]; subst.
  inversion Hreads_tail as [|? ? right_v rest_tail Hread_right Hreads_done];
    subst.
  inversion Hreads_done; subst.
  destruct Hread_left as [o_left [Hobj_left Hfield_left]].
  destruct Hread_right as [o_right [Hobj_right Hfield_right]].
  simpl in Hobj_left, Hobj_right.
  inversion Hobj_left; subst.
  inversion Hobj_right; subst.
  simpl in Hfield_left, Hfield_right.
  inversion Hfield_left; subst.
  inversion Hfield_right; subst.
  destruct Hcache_read as [o_cache [Hobj_cache Hfield_cache]].
  simpl in Hobj_cache.
  inversion Hobj_cache; subst.
  simpl in Hfield_cache.
  inversion Hfield_cache; subst.
  simpl in Hcache_value.
  destruct Hcache_value as [Hunknown | Hknown].
  - discriminate.
  - destruct Hknown as [n [Hcache_eq [Hderived Hnz]]].
    assert (Hn : n = pair_derived [Int 1; Int 99]).
    { inversion Hcache_eq. reflexivity. }
    simpl in Hderived.
    simpl in Hn.
    lia.
Qed.

Lemma pair_weak_rejects_mixed_snapshot :
  weak_rejects_cache_transition
    pair_CT
    pair_initial_heap
    pair_mixed_snapshot_heap
    pair_derived
    pair_mixed_snapshot_event.
Proof.
  eapply weak_rejects_protocol_break.
  - reflexivity.
  - apply pair_mixed_snapshot_heap_not_protocol.
Qed.

Lemma pair_weak_rejects_mixed_snapshot_execution :
  weak_rejects_execution
    pair_CT
    pair_derived
    pair_initial_heap
    [pair_mixed_snapshot_event]
    pair_mixed_snapshot_heap.
Proof.
  eapply weak_rejects_execution_at_head.
  - reflexivity.
  - apply pair_weak_rejects_mixed_snapshot.
  - apply WCE_Nil.
Qed.
