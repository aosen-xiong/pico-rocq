Require Import Syntax Helpers Typing Bigstep DerivedCache ViewpointAdaptation Subtyping.

From Stdlib Require Import List Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.PropExtensionality.
Import ListNotations.

Definition simple_value_field : var := 0.
Definition simple_cache_field : var := 1.
Definition simple_root_class : class_name := 0.
Definition simple_class : class_name := 1.

Definition simple_value_field_def : field_def :=
  {|
    ftype :=
      {|
        assignability := Final;
        mutability := Imm_f;
	        f_base_type := TRef simple_class
      |};
    fname := simple_value_field
  |}.

Definition simple_cache_field_def : field_def :=
  {|
    ftype :=
      {|
        assignability := Assignable;
        mutability := Imm_f;
	        f_base_type := TInt
      |};
    fname := simple_cache_field
  |}.

Definition simple_constructor : constructor_def :=
  {|
    csignature :=
      {|
        cqualifier := Imm_c;
        cparams := []
      |}
  |}.

Definition simple_root_class_def : class_def :=
  {|
    signature :=
      {|
        class_qualifier := Imm_c;
        cname := simple_root_class;
        super := None
      |};
    body :=
      {|
        fields := [];
        constructor := simple_constructor;
        methods := []
      |}
  |}.

Definition simple_class_def : class_def :=
  {|
    signature :=
      {|
        class_qualifier := Imm_c;
        cname := simple_class;
        super := Some simple_root_class
      |};
    body :=
      {|
        fields := [simple_value_field_def; simple_cache_field_def];
        constructor := simple_constructor;
        methods := []
      |}
  |}.

Definition simple_CT : class_table := [simple_root_class_def; simple_class_def].

Definition simple_obj (abstract_v cache_v : value) : Obj :=
  mkObj
    (mkruntime_type Imm_r simple_class)
    [abstract_v; cache_v].

Definition simple_heap (abstract_v cache_v : value) : heap :=
  [simple_obj abstract_v cache_v].

Definition simple_loc : Loc := 0.

Definition simple_abs_fields : list var := [simple_value_field].

Definition simple_derived (vs : list value) : nat :=
  match vs with
  | [Int n] => S n
  | _ => 1
  end.

Definition simple_cache_tmp_var : var := 1.

Definition simple_cache_env (derived_v : value) : r_env :=
  mkr_env [Iot simple_loc; derived_v].

Definition simple_cache_write_stmt : stmt :=
  SFldWrite 0 simple_cache_field simple_cache_tmp_var.

Definition simple_cache_compute_stmt : stmt :=
  SVarAss simple_cache_tmp_var (EInt (simple_derived [Int 41])).

Definition simple_cache_compute_and_write_stmt : stmt :=
  SSeq simple_cache_compute_stmt simple_cache_write_stmt.

Definition simple_cache_senv : s_env :=
  [Build_qualified_type Imm (TRef simple_class); int_type].

Lemma simple_value_field_final :
  final_field simple_CT simple_class simple_value_field.
Proof.
  unfold final_field, sf_assignability_rel, simple_CT, simple_class,
    simple_value_field.
  exists simple_value_field_def.
  split.
  - apply FL_Found with
      (fields := [] ++ [simple_value_field_def; simple_cache_field_def]).
    + eapply CF_Inherit.
      * reflexivity.
      * reflexivity.
      * apply CF_Object with (def := simple_root_class_def); reflexivity.
      * reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma simple_cache_field_assignable :
  cache_field simple_CT simple_class simple_cache_field.
Proof.
  unfold cache_field, sf_assignability_rel, simple_CT, simple_class,
    simple_cache_field.
  exists simple_cache_field_def.
  split.
  - apply FL_Found with
      (fields := [] ++ [simple_value_field_def; simple_cache_field_def]).
    + eapply CF_Inherit.
      * reflexivity.
      * reflexivity.
      * apply CF_Object with (def := simple_root_class_def); reflexivity.
      * reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma simple_final_fields :
  final_fields simple_CT simple_class simple_abs_fields.
Proof.
  unfold final_fields, simple_abs_fields.
  constructor.
  - apply simple_value_field_final.
  - constructor.
Qed.

Lemma simple_field_reads :
  forall abstract_v cache_v,
    field_reads (simple_heap abstract_v cache_v) simple_loc simple_abs_fields
      [abstract_v].
Proof.
  intros abstract_v cache_v.
  unfold field_reads, simple_heap, simple_obj, simple_loc, simple_abs_fields.
  constructor.
  - unfold field_read.
    exists (mkObj (mkruntime_type Imm_r simple_class) [abstract_v; cache_v]).
    split; reflexivity.
  - constructor.
Qed.

Lemma simple_cache_read :
  forall abstract_v cache_v,
    field_read (simple_heap abstract_v cache_v) simple_loc simple_cache_field
      cache_v.
Proof.
  intros abstract_v cache_v.
  unfold field_read, simple_heap, simple_obj, simple_loc, simple_cache_field.
  exists (mkObj (mkruntime_type Imm_r simple_class) [abstract_v; cache_v]).
  split; reflexivity.
Qed.

Lemma simple_object_lookup :
  forall abstract_v cache_v,
    runtime_getObj (simple_heap abstract_v cache_v) simple_loc =
      Some (simple_obj abstract_v cache_v).
Proof.
  reflexivity.
Qed.

Lemma simple_cache_senv_wf :
  wf_senv simple_CT simple_cache_senv.
Proof.
	  unfold wf_senv, simple_cache_senv, wf_stypeuse, simple_CT,
	    simple_class, int_type, bound, find_class, gget,
	    vpa_mutability_bound.
  simpl.
  repeat split; try lia; repeat constructor; discriminate.
Qed.

Lemma simple_int_literal_typed :
  expr_has_type simple_CT simple_cache_senv SafeRO
    (EInt (simple_derived [Int 41]))
    int_type.
Proof.
	  apply ET_Int.
	  apply simple_cache_senv_wf.
Qed.

Lemma simple_assign_literal_typed :
  stmt_typing simple_CT simple_cache_senv SafeRO
    simple_cache_compute_stmt
    simple_cache_senv.
Proof.
  unfold simple_cache_compute_stmt.
	eapply ST_VarAss with
	  (Te := int_type)
	  (Tthis := Build_qualified_type Imm (TRef simple_class))
	  (Tx := int_type).
  - apply simple_cache_senv_wf.
  - apply simple_int_literal_typed.
  - reflexivity.
  - unfold simple_cache_tmp_var. discriminate.
  - reflexivity.
	  - apply qtype_refl.
	    + unfold int_type, wf_qualified_base. simpl. reflexivity.
	    + unfold int_type. simpl. discriminate.
Qed.

Lemma simple_int_literal_eval :
  eval_expr
    OK simple_CT
    (simple_cache_env (Int 0))
    (simple_heap (Int 41) (Int 0))
    (EInt (simple_derived [Int 41]))
    (Int (simple_derived [Int 41]))
    OK
    (simple_cache_env (Int 0))
    (simple_heap (Int 41) (Int 0)).
Proof.
  apply EBS_Int.
Qed.

Lemma simple_assign_literal_eval :
  eval_stmt
    OK simple_CT
    (simple_cache_env (Int 0))
    (simple_heap (Int 41) (Int 0))
    simple_cache_compute_stmt
    OK
    (simple_cache_env (Int (simple_derived [Int 41])))
    (simple_heap (Int 41) (Int 0)).
Proof.
  unfold simple_cache_compute_stmt, simple_cache_env, simple_cache_tmp_var,
    simple_derived.
  simpl.
  change {| vars := [Iot simple_loc; Int 42] |} with
    (set_vars {| vars := [Iot simple_loc; Int 0] |}
      (update 1 (Int 42) [Iot simple_loc; Int 0])).
  eapply SBS_Assign with (v1 := Int 0).
  - reflexivity.
  - apply EBS_Int.
Qed.

Lemma simple_cache_write_typed :
  stmt_typing simple_CT simple_cache_senv SafeRO
    simple_cache_write_stmt
    simple_cache_senv.
Proof.
  unfold simple_cache_write_stmt.
	  eapply ST_FldWrite_safe_ro with
	    (Tx := Build_qualified_type Imm (TRef simple_class))
	    (Ty := int_type)
	    (Tthis := Build_qualified_type Imm (TRef simple_class))
    (fieldT := simple_cache_field_def)
    (a := Assignable).
  - apply simple_cache_senv_wf.
  - reflexivity.
  - reflexivity.
	  - reflexivity.
	  - reflexivity.
	  - unfold sf_def_rel, simple_CT, simple_class, simple_cache_field.
    apply FL_Found with
      (fields := [] ++ [simple_value_field_def; simple_cache_field_def]).
    + eapply CF_Inherit.
      * reflexivity.
      * reflexivity.
      * apply CF_Object with (def := simple_root_class_def); reflexivity.
      * reflexivity.
    + reflexivity.
  - apply simple_cache_field_assignable.
	  - apply qtype_refl.
	    + unfold int_type, wf_qualified_base. simpl. reflexivity.
	    + unfold int_type. simpl. discriminate.
  - reflexivity.
Qed.

Lemma simple_cache_compute_and_write_typed :
  stmt_typing simple_CT simple_cache_senv SafeRO
    simple_cache_compute_and_write_stmt
    simple_cache_senv.
Proof.
  unfold simple_cache_compute_and_write_stmt.
  eapply ST_Seq with (sΓ' := simple_cache_senv).
  - apply simple_cache_senv_wf.
  - apply simple_assign_literal_typed.
  - apply simple_cache_write_typed.
Qed.

Lemma simple_update_known_cache_protocol :
    derived_int_cache_protocol
      simple_CT
      (update_field (simple_heap (Int 41) (Int 0)) simple_loc
         simple_cache_field (Int (simple_derived [Int 41])))
      simple_loc
      simple_class
      simple_abs_fields
      simple_cache_field
      simple_derived.
Proof.
  eapply update_known_int_cache_preserves_protocol
    with
      (h := simple_heap (Int 41) (Int 0))
      (o := simple_obj (Int 41) (Int 0))
      (abs_vals := [Int 41])
      (old_cache_v := Int 0).
  - apply simple_object_lookup.
  - reflexivity.
  - apply simple_final_fields.
  - apply simple_cache_field_assignable.
  - apply simple_field_reads.
  - apply simple_cache_read.
  - unfold simple_derived. reflexivity.
  - unfold simple_derived. lia.
  - reflexivity.
Qed.

Lemma simple_cache_write_eval :
  eval_stmt
    OK simple_CT
    (simple_cache_env (Int (simple_derived [Int 41])))
    (simple_heap (Int 41) (Int 0))
    simple_cache_write_stmt
    OK
    (simple_cache_env (Int (simple_derived [Int 41])))
    (update_field (simple_heap (Int 41) (Int 0)) simple_loc
       simple_cache_field (Int (simple_derived [Int 41]))).
Proof.
  unfold simple_cache_write_stmt.
  eapply SBS_FldWrite
    with
      (loc_x := simple_loc)
      (o := simple_obj (Int 41) (Int 0))
      (a := Assignable)
      (vf := Int 0)
      (val_y := Int (simple_derived [Int 41])).
  - unfold simple_cache_env, simple_loc. reflexivity.
  - apply simple_object_lookup.
  - unfold simple_obj, simple_cache_field. reflexivity.
  - apply simple_cache_field_assignable.
  - unfold simple_cache_env, simple_cache_tmp_var. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma simple_cache_write_eval_protocol :
  exists h',
    eval_stmt
      OK simple_CT
      (simple_cache_env (Int (simple_derived [Int 41])))
      (simple_heap (Int 41) (Int 0))
      simple_cache_write_stmt
      OK
      (simple_cache_env (Int (simple_derived [Int 41])))
      h' /\
    derived_int_cache_protocol
      simple_CT
      h'
      simple_loc
      simple_class
      simple_abs_fields
      simple_cache_field
      simple_derived.
Proof.
  exists (update_field (simple_heap (Int 41) (Int 0)) simple_loc
            simple_cache_field (Int (simple_derived [Int 41]))).
  split.
  - apply simple_cache_write_eval.
  - eapply eval_cache_field_write_establishes_protocol
      with
        (rΓ := simple_cache_env (Int (simple_derived [Int 41])))
        (x := 0)
        (y := simple_cache_tmp_var)
        (o := simple_obj (Int 41) (Int 0))
        (abs_vals := [Int 41])
        (old_cache_v := Int 0)
        (n := simple_derived [Int 41]).
    + apply simple_cache_write_eval.
    + unfold simple_cache_env, simple_loc. reflexivity.
    + unfold simple_cache_env, simple_cache_tmp_var. reflexivity.
    + apply simple_object_lookup.
    + reflexivity.
    + apply simple_final_fields.
    + apply simple_cache_field_assignable.
    + apply simple_field_reads.
    + apply simple_cache_read.
    + unfold simple_derived. reflexivity.
    + unfold simple_derived. lia.
Qed.

Lemma simple_cache_reachable_ignores_tmp_int :
  forall n1 n2,
    reachable_locations_from_initial_env
      simple_CT
      (simple_heap (Int 41) (Int 0))
      (simple_cache_env (Int n1)) =
    reachable_locations_from_initial_env
      simple_CT
      (simple_heap (Int 41) (Int 0))
      (simple_cache_env (Int n2)).
Proof.
  intros n1 n2.
  apply functional_extensionality.
  intro l_target.
  apply propositional_extensionality.
  unfold reachable_locations_from_initial_env, simple_cache_env.
  split; intros [x [l_root [Hroot Hreach]]].
  - destruct x as [|x].
    + simpl in Hroot.
      injection Hroot as ?; subst.
      exists 0, simple_loc. split; [reflexivity | exact Hreach].
    + destruct x as [|x].
      * unfold runtime_getVal, simple_cache_env in Hroot.
        simpl in Hroot. discriminate Hroot.
      * unfold runtime_getVal, simple_cache_env in Hroot.
        destruct x; simpl in Hroot; discriminate Hroot.
  - destruct x as [|x].
    + simpl in Hroot.
      injection Hroot as ?; subst.
      exists 0, simple_loc. split; [reflexivity | exact Hreach].
    + destruct x as [|x].
      * unfold runtime_getVal, simple_cache_env in Hroot.
        simpl in Hroot. discriminate Hroot.
      * unfold runtime_getVal, simple_cache_env in Hroot.
        destruct x; simpl in Hroot; discriminate Hroot.
Qed.

Lemma simple_cache_compute_and_write_eval :
  eval_stmt
    OK simple_CT
    (simple_cache_env (Int 0))
    (simple_heap (Int 41) (Int 0))
    simple_cache_compute_and_write_stmt
    OK
    (simple_cache_env (Int (simple_derived [Int 41])))
    (update_field (simple_heap (Int 41) (Int 0)) simple_loc
       simple_cache_field (Int (simple_derived [Int 41]))).
Proof.
  unfold simple_cache_compute_and_write_stmt.
  eapply SBS_Seq with
    (rΓ' := simple_cache_env (Int (simple_derived [Int 41])))
    (h' := simple_heap (Int 41) (Int 0)).
  - apply simple_assign_literal_eval.
  - apply simple_cache_write_eval.
Qed.

Lemma simple_cache_compute_and_write_eval_protocol :
  exists h',
    eval_stmt
      OK simple_CT
      (simple_cache_env (Int 0))
      (simple_heap (Int 41) (Int 0))
      simple_cache_compute_and_write_stmt
      OK
      (simple_cache_env (Int (simple_derived [Int 41])))
      h' /\
    derived_int_cache_protocol
      simple_CT
      h'
      simple_loc
      simple_class
      simple_abs_fields
      simple_cache_field
      simple_derived.
Proof.
  exists (update_field (simple_heap (Int 41) (Int 0)) simple_loc
            simple_cache_field (Int (simple_derived [Int 41]))).
  split.
  - apply simple_cache_compute_and_write_eval.
  - apply simple_update_known_cache_protocol.
Qed.
