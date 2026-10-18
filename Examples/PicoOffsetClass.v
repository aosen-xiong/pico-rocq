From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Subtyping Typing Bigstep DerivedCache.
Require Import Core.GenericCacheProtocol Core.GenericDerivedCache.
Require Import Examples.PicoIfZeroCache
  Examples.PicoHashMethod
  Examples.PicoConcreteHashProvider
  Examples.PicoCacheMethodJudgment
  Examples.PicoCacheFlowJudgment
  Examples.PicoOffsetFlowInstance.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoCoreLanguage
  PICOBridge.PicoCacheTyping
  PICOBridge.PicoCoreSemImm PICOBridge.PicoSemanticConcurrency
  PICOBridge.PicoStableAbsPreservation PICOBridge.PicoCoreTraceRobust.
Require Import PICOBridge.PicoDerivationNoninterference
  PICOBridge.PicoDerivationCache.

(** * A Class with an Offset-Encoded Cache

    The class of this file has a final integer payload, an assignable
    integer cache, a derivation method that returns the payload, and one
    cache method: the offset-encoded accessor of [PicoOffsetFlowInstance],
    which returns the cached value minus one.  The payload plays the
    encoded value.

    The first part establishes that the class table, the heap and the
    initial state are well formed, following the hash class.  The second
    part shows that the accessor is accepted by the flow judgment with the
    predecessor as decoding.  The last part concludes that any number of
    concurrent calls of the accessor preserve semantic immutability and
    return the decoded value. *)

Definition poc_method : method_name := 0.
Definition poc_value : nat := 7.

Definition poc_method_def : method_def :=
  {| msignature :=
       pico_hash_method_signature pico_hash_witness_receiver_type poc_method;
     mbody := {| mbody_stmt := offset_accessor_stmt;
                 mreturn := cache_result |} |}.

Definition poc_class_def : class_def :=
  {| signature :=
       {| class_qualifier := Imm_c;
          cname := pico_hash_witness_class;
          super := Some pico_hash_witness_root |};
     body :=
       {| fields :=
            [pico_hash_witness_cache_def; pico_hash_witness_payload_def];
          constructor := pico_hash_witness_constructor;
          methods :=
            [poc_method_def; pico_hash_derive_method_def] |} |}.

Definition poc_CT : class_table :=
  [pico_hash_witness_root_def; poc_class_def].

Definition poc_receiver : Loc := 1.

Definition poc_owner : Obj :=
  mkObj (mkruntime_type Imm_r pico_hash_witness_root) [].

Definition poc_initial_heap : heap :=
  [poc_owner; pico_hash_witness_object].

Definition poc_initial_weak : wm_state :=
  pico_core_alloc_weak
    (pico_core_alloc_weak empty_wm_state poc_owner 0)
    pico_hash_witness_object 0.

Definition poc_initial_state : pico_core_state :=
  mkPicoCoreState poc_initial_heap
    poc_initial_weak.

Lemma poc_find_method :
  FindMethodWithName poc_CT pico_hash_witness_class
    poc_method poc_method_def.
Proof.
  eapply FOM_Here with
    (def := poc_class_def)
    (own_methods :=
      [poc_method_def; pico_hash_derive_method_def]).
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma poc_collect_fields :
  CollectFields poc_CT pico_hash_witness_class
    [pico_hash_witness_cache_def; pico_hash_witness_payload_def].
Proof.
  eapply CF_Inherit with
    (def := poc_class_def)
    (parent := pico_hash_witness_root)
    (parent_fields := [])
    (own_fields :=
      [pico_hash_witness_cache_def; pico_hash_witness_payload_def]).
  - reflexivity.
  - reflexivity.
  - eapply CF_Object with (def := pico_hash_witness_root_def); reflexivity.
  - reflexivity.
Qed.

Lemma poc_cache_field_def :
  sf_def_rel poc_CT pico_hash_witness_class
    hash_cache_field pico_hash_witness_cache_def.
Proof.
  unfold sf_def_rel.
  eapply FL_Found with
    (fields := [pico_hash_witness_cache_def; pico_hash_witness_payload_def]).
  - exact poc_collect_fields.
  - reflexivity.
Qed.

Lemma poc_cache_assignable :
  sf_assignability_rel poc_CT pico_hash_witness_class
    hash_cache_field Assignable.
Proof.
  unfold sf_assignability_rel.
  exists pico_hash_witness_cache_def.
  split; [exact poc_cache_field_def | reflexivity].
Qed.

Lemma poc_payload_field_def :
  sf_def_rel poc_CT pico_hash_witness_class 1
    pico_hash_witness_payload_def.
Proof.
  unfold sf_def_rel.
  eapply FL_Found with
    (fields := [pico_hash_witness_cache_def; pico_hash_witness_payload_def]).
  - exact poc_collect_fields.
  - reflexivity.
Qed.

Lemma poc_payload_final :
  final_field poc_CT pico_hash_witness_class 1.
Proof.
  unfold final_field, sf_assignability_rel.
  exists pico_hash_witness_payload_def.
  split; [exact poc_payload_field_def | reflexivity].
Qed.

Lemma poc_initial_core_stable_abs :
  pico_core_stable_abs poc_CT pico_hash_witness_class [1]
    poc_receiver
    poc_initial_state [Int poc_value].
Proof.
  unfold pico_core_stable_abs, poc_initial_state,
    poc_initial_heap, poc_receiver.
  exists pico_hash_witness_object.
  split; [reflexivity |].
  split; [reflexivity |].
  unfold pico_stable_abs.
  split.
  - constructor; [exact poc_payload_final | constructor].
  - unfold field_reads. constructor.
    + unfold field_read. exists pico_hash_witness_object.
      split; reflexivity.
    + constructor.
Qed.

Lemma poc_wf_env1 :
  wf_senv poc_CT [pico_hash_witness_receiver_type].
Proof.
  unfold wf_senv, wf_stypeuse, pico_hash_witness_receiver_type,
    poc_CT, poc_class_def,
    pico_hash_witness_class, bound, find_class, gget.
  simpl. split; [lia |].
  constructor.
  - unfold gget. simpl. split; [constructor; discriminate | lia].
  - constructor.
Qed.

Lemma poc_wf_env2 :
  wf_senv poc_CT
    [pico_hash_witness_receiver_type; int_type].
Proof.
  unfold wf_senv, wf_stypeuse, pico_hash_witness_receiver_type,
    poc_CT, poc_class_def,
    pico_hash_witness_class, bound, find_class, gget, int_type.
  simpl. split; [lia |].
  constructor.
  - unfold gget. simpl. split; [constructor; discriminate | lia].
  - constructor; [reflexivity | constructor].
Qed.

Lemma poc_wf_env3 :
  wf_senv poc_CT
    [pico_hash_witness_receiver_type; int_type; int_type].
Proof.
  unfold wf_senv, wf_stypeuse, pico_hash_witness_receiver_type,
    poc_CT, poc_class_def,
    pico_hash_witness_class, bound, find_class, gget, int_type.
  simpl. split; [lia |].
  constructor.
  - unfold gget. simpl. split; [constructor; discriminate | lia].
  - constructor; [reflexivity |].
    constructor; [reflexivity | constructor].
Qed.

Lemma poc_method_typing :
  stmt_typing poc_CT
    [pico_hash_witness_receiver_type] AbstractState
    offset_accessor_stmt
    [pico_hash_witness_receiver_type; int_type; int_type].
Proof.
  assert (Hint_sub : qualified_type_subtype poc_CT
    int_type int_type).
  { apply qtype_refl; simpl; [reflexivity | discriminate]. }
  assert (Hread : expr_has_type poc_CT
    [pico_hash_witness_receiver_type; int_type; int_type] AbstractState
    (EField cache_receiver hash_cache_field) int_type).
  { change (expr_has_type poc_CT
      [pico_hash_witness_receiver_type; int_type; int_type] AbstractState
      (EField 0 0) (Build_qualified_type Imm TInt)).
    eapply ET_Field_abstract_state with
      (T := pico_hash_witness_receiver_type)
      (C := pico_hash_witness_class)
      (fDef := pico_hash_witness_cache_def).
    - exact poc_wf_env3.
    - reflexivity.
    - reflexivity.
    - exact poc_cache_field_def.
    - left. reflexivity. }
  assert (Hread_assign : stmt_typing poc_CT
    [pico_hash_witness_receiver_type; int_type; int_type] AbstractState
    (SVarAss cache_tmp (EField cache_receiver hash_cache_field))
    [pico_hash_witness_receiver_type; int_type; int_type]).
  { eapply ST_VarAss with (Te := int_type)
      (Tthis := pico_hash_witness_receiver_type) (Tx := int_type).
    - exact poc_wf_env3.
    - exact Hread.
    - reflexivity.
    - unfold cache_tmp. discriminate.
    - reflexivity.
    - exact Hint_sub. }
  assert (Hcompute : stmt_typing poc_CT
    [pico_hash_witness_receiver_type; int_type; int_type] AbstractState
    pico_hash_read_compute_stmt
    [pico_hash_witness_receiver_type; int_type; int_type]).
  { unfold pico_hash_read_compute_stmt.
    eapply ST_VarAss with (Te := int_type)
      (Tthis := pico_hash_witness_receiver_type) (Tx := int_type).
    - exact poc_wf_env3.
    - change (expr_has_type poc_CT
        [pico_hash_witness_receiver_type; int_type; int_type] AbstractState
        (EField 0 1) (Build_qualified_type Imm TInt)).
      eapply ET_Field_abstract_state with
        (T := pico_hash_witness_receiver_type)
        (C := pico_hash_witness_class)
        (fDef := pico_hash_witness_payload_def).
      + exact poc_wf_env3.
      + reflexivity.
      + reflexivity.
      + exact poc_payload_field_def.
      + left. reflexivity.
    - reflexivity.
    - unfold cache_tmp. discriminate.
    - reflexivity.
    - exact Hint_sub. }
  assert (Hwrite : stmt_typing poc_CT
    [pico_hash_witness_receiver_type; int_type; int_type] AbstractState
    (SFldWrite cache_receiver hash_cache_field cache_tmp)
    [pico_hash_witness_receiver_type; int_type; int_type]).
  { eapply ST_FldWrite_abstract_state with
      (Tx := pico_hash_witness_receiver_type) (Ty := int_type)
      (Tthis := pico_hash_witness_receiver_type)
      (C := pico_hash_witness_class)
      (fieldT := pico_hash_witness_cache_def) (a := Assignable).
    - exact poc_wf_env3.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact poc_cache_field_def.
    - exact poc_cache_assignable.
    - exact Hint_sub.
    - reflexivity. }
  assert (Hone : stmt_typing poc_CT
    [pico_hash_witness_receiver_type; int_type; int_type] AbstractState
    (SVarAss cache_result (EInt 1))
    [pico_hash_witness_receiver_type; int_type; int_type]).
  { eapply ST_VarAss with (Te := int_type)
      (Tthis := pico_hash_witness_receiver_type) (Tx := int_type).
    - exact poc_wf_env3.
    - apply ET_Int. exact poc_wf_env3.
    - reflexivity.
    - unfold cache_result. discriminate.
    - reflexivity.
    - exact Hint_sub. }
  assert (Hsub1 : stmt_typing poc_CT
    [pico_hash_witness_receiver_type; int_type; int_type] AbstractState
    (SVarAss cache_result (EBin BSub cache_tmp cache_result))
    [pico_hash_witness_receiver_type; int_type; int_type]).
  { eapply ST_VarAss with (Te := int_type)
      (Tthis := pico_hash_witness_receiver_type) (Tx := int_type).
    - exact poc_wf_env3.
    - eapply ET_Bin with (Tx := int_type) (Ty := int_type);
        [exact poc_wf_env3 | reflexivity ..].
    - reflexivity.
    - unfold cache_result. discriminate.
    - reflexivity.
    - exact Hint_sub. }
  assert (Hfinal : stmt_typing poc_CT
    [pico_hash_witness_receiver_type; int_type; int_type] AbstractState
    offset_decode_stmt
    [pico_hash_witness_receiver_type; int_type; int_type]).
  { eapply ST_Seq; [exact poc_wf_env3 | exact Hone | exact Hsub1]. }
  unfold offset_accessor_stmt, pico_local_copy_cache_branch.
  eapply ST_Seq with
    (sΓ' := [pico_hash_witness_receiver_type; int_type]).
  - exact poc_wf_env1.
  - eapply ST_Local with (T := int_type) (x := cache_tmp).
    + exact poc_wf_env1.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - eapply ST_Seq with
      (sΓ' := [pico_hash_witness_receiver_type; int_type; int_type]).
    + exact poc_wf_env2.
    + eapply ST_Local with (T := int_type) (x := cache_result).
      * exact poc_wf_env2.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
    + eapply ST_Seq; [exact poc_wf_env3 | exact Hread_assign |].
      eapply ST_Seq; [exact poc_wf_env3 | | exact Hfinal].
      eapply ST_IfZero with (Tx := int_type).
      * exact poc_wf_env3.
      * reflexivity.
      * left. reflexivity.
      * eapply ST_Seq with
          (sΓ' := [pico_hash_witness_receiver_type; int_type; int_type]).
        -- exact poc_wf_env3.
        -- exact Hcompute.
        -- exact Hwrite.
      * apply ST_Skip. exact poc_wf_env3.
Qed.

Lemma poc_method_wf :
  wf_method poc_CT pico_hash_witness_class
    poc_method_def.
Proof.
  unfold wf_method, poc_method_def; simpl.
  split; [reflexivity |].
  exists [pico_hash_witness_receiver_type; int_type; int_type], int_type.
  split; [exact poc_method_typing |].
  split; [unfold cache_result; simpl; lia |].
  split; [unfold cache_result; reflexivity |].
  split.
  { apply qtype_sub; simpl.
    + reflexivity.
    + reflexivity.
    + constructor; discriminate.
    + constructor. }
  split; [| split; [reflexivity | intros [Hscope | Hscope]; discriminate]].
  - intros parent_def parent mdef_parent qc Hclass Hsuper Hbound Hfind.
    simpl in Hclass. inversion Hclass; subst parent_def.
    simpl in Hsuper. inversion Hsuper; subst parent.
    inversion Hfind; subst.
    + simpl in Hfind0. inversion Hfind0; subst def.
      unfold pico_hash_witness_root_def in Hget_method.
      simpl in Hget_method. discriminate.
    + simpl in Hfind0. inversion Hfind0; subst def.
      unfold pico_hash_witness_root_def in Hsuper0.
      simpl in Hsuper0. discriminate.
Qed.

Lemma poc_derive_wf :
  wf_method poc_CT pico_hash_witness_class
    pico_hash_derive_method_def.
Proof.
  apply pico_hash_derive_method_wf.
  - apply pico_hash_derive_method_typing.
    + exact poc_wf_env1.
    + exact poc_wf_env2.
    + exact poc_payload_field_def.
  - intros parent_def parent mdef_parent qc Hclass Hsuper Hbound Hfind.
    simpl in Hclass. inversion Hclass; subst parent_def.
    simpl in Hsuper. inversion Hsuper; subst parent.
    inversion Hfind; subst.
    + simpl in Hfind0. inversion Hfind0; subst def.
      unfold pico_hash_witness_root_def in Hget_method.
      simpl in Hget_method. discriminate.
    + simpl in Hfind0. inversion Hfind0; subst def.
      unfold pico_hash_witness_root_def in Hsuper0.
      simpl in Hsuper0. discriminate.
Qed.

Lemma poc_class_table_wf :
  wf_class_table poc_CT.
Proof.
  unfold wf_class_table.
  repeat split.
  - constructor.
    + eapply WFObjectDef with (class_name := pico_hash_witness_root);
        simpl; try reflexivity.
      * unfold wf_constructor_object. simpl.
        repeat split; try reflexivity.
        eapply CF_Object with (def := pico_hash_witness_root_def);
          reflexivity.
      * constructor.
      * constructor.
    + constructor.
      * eapply WFOtherDef with
          (superC := pico_hash_witness_root)
          (thisC := pico_hash_witness_class);
          simpl; try reflexivity.
        -- unfold pico_hash_witness_class, pico_hash_witness_root. lia.
        -- split.
           ++ unfold wf_constructor. simpl.
              split; [reflexivity |].
              split.
              ** repeat constructor; reflexivity.
              ** exists
                   [pico_hash_witness_cache_def;
                    pico_hash_witness_payload_def].
                 repeat split; try reflexivity.
                 --- exact poc_collect_fields.
                 --- constructor.
                     ++++ apply qtype_refl; simpl;
                            [reflexivity | discriminate].
                     ++++ constructor.
                          **** apply qtype_refl; simpl;
                                 [reflexivity | discriminate].
                          **** constructor.
           ++ split.
              ** constructor; [exact poc_method_wf |].
                 constructor; [exact poc_derive_wf | constructor].
              ** split.
                 --- constructor.
                     +++ simpl. intros [Heq | []]. discriminate.
                     +++ constructor; [simpl; tauto | constructor].
                 --- exists
                      [pico_hash_witness_cache_def;
                       pico_hash_witness_payload_def].
                     repeat split; try reflexivity.
                     ++++ exact poc_collect_fields.
                     ++++ right. reflexivity.
                     ++++ repeat constructor; simpl; trivial.
      * constructor.
  - exists pico_hash_witness_root_def. split; reflexivity.
  - intros i def Hi Hfind.
    destruct i as [|[|i]].
    + lia.
    + simpl in Hfind. inversion Hfind; subst. discriminate.
    + unfold find_class, gget in Hfind. simpl in Hfind.
      rewrite nth_error_nil in Hfind. discriminate.
  - intros i def Hfind.
    destruct i as [|[|i]].
    + simpl in Hfind. inversion Hfind. reflexivity.
    + simpl in Hfind. inversion Hfind. reflexivity.
    + unfold find_class, gget in Hfind. simpl in Hfind.
      rewrite nth_error_nil in Hfind. discriminate.
Qed.

Lemma poc_cache_declared :
  derived_cache_field poc_CT pico_hash_witness_class
    hash_cache_field.
Proof.
  unfold derived_cache_field.
  exists pico_hash_witness_cache_def.
  split; [exact poc_cache_field_def | reflexivity].
Qed.

Lemma poc_find_derive :
  FindMethodWithName poc_CT pico_hash_witness_class
    pico_hash_derive_method pico_hash_derive_method_def.
Proof.
  eapply FOM_Here with
    (def := poc_class_def)
    (own_methods :=
      [poc_method_def; pico_hash_derive_method_def]).
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma poc_derivation_table :
  derivation_table poc_CT pico_hash_derivations.
Proof.
  exact (pico_hash_derivation_table poc_CT
    poc_payload_field_def).
Qed.

Lemma poc_heap_wf :
  wf_heap poc_CT poc_initial_heap.
Proof.
  unfold wf_heap. intros loc Hloc.
  unfold poc_initial_heap in Hloc. simpl in Hloc.
  destruct loc as [| [| loc]]; [| | lia].
  - unfold wf_obj, runtime_getObj, poc_initial_heap,
      poc_owner. simpl.
    split.
    + unfold wf_rtypeuse, bound. simpl.
      split; [unfold pico_hash_witness_root, poc_CT; simpl; lia
             | trivial].
    + exists (@nil field_def). split.
      * eapply CF_Object with (def := pico_hash_witness_root_def);
          reflexivity.
      * split; [reflexivity | constructor].
  - unfold wf_obj, runtime_getObj, poc_initial_heap,
      pico_hash_witness_object. simpl.
    split.
    + unfold wf_rtypeuse, bound. simpl.
      split; [unfold pico_hash_witness_class, poc_CT; simpl; lia
             | trivial].
    + exists [pico_hash_witness_cache_def; pico_hash_witness_payload_def].
      split; [exact poc_collect_fields |].
      split; [reflexivity |].
      repeat constructor; reflexivity.
Qed.

Lemma poc_config_wf :
  wf_r_config poc_CT [pico_hash_witness_receiver_type]
    (mkr_env [Iot poc_receiver])
    poc_initial_heap.
Proof.
  unfold wf_r_config.
  split; [exact poc_class_table_wf |].
  split; [exact poc_heap_wf |].
  split.
  - unfold wf_renv, poc_initial_heap,
      poc_receiver. simpl.
    split; [lia |]. split.
    + exists 1. split; reflexivity || lia.
    + constructor; [simpl; trivial | constructor].
  - split.
    + exact poc_wf_env1.
    + split; [reflexivity |].
      intros receiver qcontext Hreceiver Hmut i Hi T Htype.
      simpl in Hreceiver. inversion Hreceiver; subst receiver.
      unfold poc_initial_heap, pico_hash_witness_object,
        r_muttype, runtime_getObj in Hmut. simpl in Hmut.
      inversion Hmut; subst qcontext.
      destruct i; [|simpl in Hi; lia].
      simpl in Htype. inversion Htype; subst T. simpl.
      unfold wf_r_typable, r_type, poc_initial_heap,
        pico_hash_witness_object, runtime_getObj. simpl.
      split.
      * apply base_ref. apply class_refl.
        unfold pico_hash_witness_class. simpl. lia.
      * trivial.
Qed.

Lemma poc_ready :
  derivation_ready poc_CT pico_hash_derivations
    pico_hash_derive_method poc_initial_heap
    poc_receiver.
Proof.
  exists pico_hash_witness_class, pico_hash_derive_method_def.
  split; [reflexivity |].
  split; [exact poc_find_derive |].
  split; [reflexivity |].
  split; [reflexivity |].
  exact poc_config_wf.
Qed.

(** The PICO derivation method returns the concurrent example's hash. *)
Lemma poc_derived :
  derived_by poc_CT pico_hash_derive_method
    poc_initial_heap poc_receiver
    (Int poc_value).
Proof.
  eapply pico_hash_derive_by with
    (rt := mkruntime_type Imm_r pico_hash_witness_class) (c := Int 0).
  - reflexivity.
  - exact poc_find_derive.
Qed.

Theorem poc_initial_provider_inv :
  pico_hash_provider_inv poc_CT poc_receiver
    pico_hash_derive_method poc_initial_heap
    poc_value
    poc_initial_state.
Proof.
  unfold poc_initial_state.
  apply (pico_hash_provider_inv_at_reference poc_CT
    pico_hash_derivations).
  - exact poc_derivation_table.
  - exact poc_ready.
  - exact poc_derived.
  - exists (rt_type pico_hash_witness_object),
      (fields_map pico_hash_witness_object).
    split; [reflexivity | exact poc_cache_declared].
  - unfold poc_initial_heap,
      poc_initial_weak.
    change (heap_wm_type_agree
      ([poc_owner] ++ [pico_hash_witness_object])
      (pico_core_alloc_weak
        (pico_core_alloc_weak empty_wm_state poc_owner 0)
        pico_hash_witness_object 0)).
    apply heap_wm_type_agree_alloc.
    change (heap_wm_type_agree
      ([] ++ [poc_owner])
      (pico_core_alloc_weak empty_wm_state poc_owner 0)).
    apply heap_wm_type_agree_alloc.
    split; [reflexivity |].
    intros loc object Hobject. destruct loc; discriminate.
  - unfold poc_initial_heap,
      poc_initial_weak.
    change (pico_hash_allocated_histories
      (([] ++ [poc_owner]) ++ [pico_hash_witness_object])
      (pico_core_alloc_weak
        (pico_core_alloc_weak empty_wm_state poc_owner 0)
        pico_hash_witness_object 0)).
    apply pico_hash_allocated_histories_alloc; [reflexivity |].
    apply pico_hash_allocated_histories_alloc; [reflexivity |].
    exact pico_hash_allocated_histories_empty.
  - intros [] value Hin.
    unfold pico_hash_snapshot, values_written_to, history_of,
      poc_initial_heap, poc_initial_weak,
      poc_receiver,
      pico_core_alloc_weak, poc_owner,
      pico_hash_witness_object, empty_wm_state in Hin.
    simpl in Hin. destruct Hin as [<- | []].
    unfold hash_cache_valid. left. reflexivity.
Qed.

Lemma poc_payload_footprint :
  pico_hash_abstract_field poc_CT
    poc_initial_heap poc_receiver
    (poc_receiver, 1).
Proof.
  split.
  - apply Reachability.reachable_abs_heap.
    unfold poc_receiver, poc_initial_heap.
    simpl. lia.
  - exists (rt_type pico_hash_witness_object),
      (fields_map pico_hash_witness_object).
    split; [reflexivity |].
    exact (pico_hash_payload_abstract poc_CT
      poc_payload_field_def).
Qed.

(** In every provider state, a weak read of the receiver's payload returns
    the hash and leaves the view unchanged. *)
Lemma poc_payload_read :
  forall h sigma V v V',
    pico_hash_provider_inv poc_CT
      poc_receiver pico_hash_derive_method
      poc_initial_heap poc_value
      (mkPicoCoreState h sigma) ->
    @wm_read history_cache_memory_model sigma V
      (poc_receiver, 1) v V' ->
    v = Int poc_value /\ V' = V.
Proof.
  intros h sigma V v V' (_ & (_ & _ & _ & Hhist & _) & _)
    [HV (msg & Hin & Hval)].
  destruct (Hhist poc_receiver 1
    (Int poc_value)
    poc_payload_footprint) as [_ Honly].
  - exists pico_hash_witness_object. split; reflexivity.
  - split; [| exact HV].
    apply Honly. simpl. unfold values_written_to.
    rewrite <- Hval. apply List.in_map. exact Hin.
Qed.

Lemma poc_valid_value :
  hash_cache_valid poc_value HashField
    (Int poc_value).
Proof.
  unfold hash_cache_valid, poc_value.
  right. split; [reflexivity | discriminate].
Qed.

(** This is the only shared-state mutation rule needed by the concrete hash
    controls: appending the derived hash preserves the provider invariant. *)
Theorem poc_valid_write_preserves_provider :
  forall h h' sigma sigma' V V',
    pico_hash_provider_inv poc_CT
      poc_receiver
      pico_hash_derive_method poc_initial_heap poc_value
      (mkPicoCoreState h sigma) ->
    h' = update_field h poc_receiver hash_cache_field
      (Int poc_value) ->
    wm_write sigma sigma' V V'
      (poc_receiver, hash_cache_field)
      (Int poc_value) ->
    pico_hash_provider_inv poc_CT
      poc_receiver
      pico_hash_derive_method poc_initial_heap poc_value
      (mkPicoCoreState h' sigma').
Proof.
  intros h h' sigma sigma' V V' Hinv Hheap Hwrite.
  pose proof (pcsi_valid_cache_write_effect
    hash_cache_protocol pico_hash_stable_abs
    poc_value
    (pico_hash_cache_adapter poc_receiver)
    (pico_concrete_hash_semimm poc_CT
      poc_receiver
      pico_hash_derive_method poc_initial_heap poc_value)
    h h' sigma sigma' V V' poc_receiver hash_cache_field
    (Int poc_value) HashField
    (Int poc_value)
    Hinv Hheap Hwrite
    (pico_concrete_hash_adapter_at poc_receiver)
    (pico_concrete_hash_value_adapter poc_receiver
      (Int poc_value))
    poc_valid_value) as Heffect.
  exact (proj2 Heffect).
Qed.

Definition poc_caller : r_env :=
  mkr_env [Iot poc_receiver; Int 0].

(** ** The frame of the accessor *)

Definition poc_frame_senv : s_env :=
  [pico_hash_witness_receiver_type; int_type; int_type].

Definition poc_frame_env : r_env :=
  mkr_env [Iot poc_receiver; Int 0; Int 0].

Lemma poc_compute_deriv :
  deriv_stmt poc_CT pico_hash_derivations
    poc_frame_senv pico_hash_read_compute_stmt poc_frame_senv.
Proof.
  apply DS_VarAss.
  eapply TSERO_Field with
    (T := pico_hash_witness_receiver_type) (C := pico_hash_witness_class).
  - reflexivity.
  - reflexivity.
  - exact (pico_hash_payload_abstract poc_CT
      poc_payload_field_def).
Qed.

Lemma poc_compute_typing :
  stmt_typing poc_CT poc_frame_senv AbstractState
    pico_hash_read_compute_stmt poc_frame_senv.
Proof.
  unfold pico_hash_read_compute_stmt.
  eapply ST_VarAss with (Te := int_type)
    (Tthis := pico_hash_witness_receiver_type) (Tx := int_type).
  - exact poc_wf_env3.
  - change (expr_has_type poc_CT
      [pico_hash_witness_receiver_type; int_type; int_type] AbstractState
      (EField 0 1) (Build_qualified_type Imm TInt)).
    eapply ET_Field_abstract_state with
      (T := pico_hash_witness_receiver_type)
      (C := pico_hash_witness_class)
      (fDef := pico_hash_witness_payload_def).
    + exact poc_wf_env3.
    + reflexivity.
    + reflexivity.
    + exact poc_payload_field_def.
    + left. reflexivity.
  - reflexivity.
  - unfold cache_tmp. discriminate.
  - reflexivity.
  - apply qtype_refl; simpl; [reflexivity | discriminate].
Qed.

Lemma poc_frame_config_wf :
  wf_r_config poc_CT poc_frame_senv
    poc_frame_env poc_initial_heap.
Proof.
  unfold wf_r_config.
  split; [exact poc_class_table_wf |].
  split; [exact poc_heap_wf |].
  split.
  - unfold wf_renv, poc_initial_heap,
      poc_frame_env, poc_receiver. simpl.
    split; [lia |]. split.
    + exists 1. split; reflexivity || lia.
    + constructor; [simpl; trivial |].
      constructor; [trivial |]. constructor; [trivial | constructor].
  - split.
    + exact poc_wf_env3.
    + split; [reflexivity |].
      intros receiver qcontext Hreceiver Hmut i Hi T Htype.
      simpl in Hreceiver. inversion Hreceiver; subst receiver.
      unfold poc_initial_heap, pico_hash_witness_object,
        r_muttype, runtime_getObj in Hmut. simpl in Hmut.
      inversion Hmut; subst qcontext.
      destruct i as [| [| [| i]]]; [| | | simpl in Hi; lia].
      * simpl in Htype. inversion Htype; subst T. simpl.
        unfold wf_r_typable, r_type, poc_initial_heap,
          pico_hash_witness_object, runtime_getObj. simpl.
        split.
        -- apply base_ref. apply class_refl.
           unfold pico_hash_witness_class. simpl. lia.
        -- trivial.
      * simpl in Htype. inversion Htype; subst T. reflexivity.
      * simpl in Htype. inversion Htype; subst T. reflexivity.
Qed.

(** Evaluated in the reference heap, the initializer reads the payload. *)
Lemma poc_compute_value : forall rGamma1,
  eval_stmt poc_CT poc_frame_env
    poc_initial_heap pico_hash_read_compute_stmt OK rGamma1
    poc_initial_heap ->
  runtime_getVal rGamma1 cache_tmp = Some (Int poc_value).
Proof.
  intros rGamma1 Heval.
  unfold pico_hash_read_compute_stmt in Heval.
  inversion Heval; subst.
  match goal with
  | He : eval_expr _ _ _ (EField _ _) _ OK _ _ |- _ => inversion He; subst
  end.
  match goal with
  | Hv : runtime_getVal poc_frame_env cache_receiver = Some (Iot ?l),
    Ho : runtime_getObj _ ?l = Some ?o,
    Hf : getVal (fields_map ?o) 1 = Some _ |- _ =>
      cbv in Hv; injection Hv as <-;
      cbv in Ho; injection Ho as <-;
      cbv in Hf; injection Hf as <-
  end.
  reflexivity.
Qed.


(** ** The accessor is accepted *)

Lemma poc_int_subtype :
  qualified_type_subtype poc_CT int_type int_type.
Proof. apply qtype_refl; simpl; [reflexivity | discriminate]. Qed.

Lemma poc_local_tmp_typing :
  stmt_typing poc_CT [pico_hash_witness_receiver_type] AbstractState
    (SLocal int_type cache_tmp) [pico_hash_witness_receiver_type; int_type].
Proof.
  eapply ST_Local with (T := int_type) (x := cache_tmp);
    [exact poc_wf_env1 | reflexivity ..].
Qed.

Lemma poc_local_result_typing :
  stmt_typing poc_CT [pico_hash_witness_receiver_type; int_type] AbstractState
    (SLocal int_type cache_result) poc_frame_senv.
Proof.
  eapply ST_Local with (T := int_type) (x := cache_result);
    [exact poc_wf_env2 | reflexivity ..].
Qed.

Lemma poc_int_assign_typing :
  forall n,
    stmt_typing poc_CT poc_frame_senv AbstractState
      (SVarAss cache_tmp (EInt n)) poc_frame_senv.
Proof.
  intros n.
  eapply ST_VarAss with (Te := int_type) (Tthis := pico_hash_witness_receiver_type)
    (Tx := int_type).
  - exact poc_wf_env3.
  - apply ET_Int. exact poc_wf_env3.
  - reflexivity.
  - unfold cache_tmp. discriminate.
  - reflexivity.
  - exact poc_int_subtype.
Qed.

Lemma poc_copy_typing :
  stmt_typing poc_CT poc_frame_senv AbstractState
    (SVarAss cache_result (EVar cache_tmp)) poc_frame_senv.
Proof.
  eapply ST_VarAss with (Te := int_type) (Tthis := pico_hash_witness_receiver_type)
    (Tx := int_type).
  - exact poc_wf_env3.
  - apply ET_Var; [exact poc_wf_env3 | reflexivity].
  - reflexivity.
  - unfold cache_result. discriminate.
  - reflexivity.
  - exact poc_int_subtype.
Qed.

(** ** The initializer yields the derived value *)

Lemma poc_sem_frame :
  forall dec rho,
    sem poc_receiver poc_value dec [OThis; OSentinel; OSentinel] rho ->
    rho = poc_frame_env.
Proof.
  intros dec [vs] Hs. unfold sem in Hs. simpl in Hs.
  repeat match goal with
         | Hf : Forall2 _ (_ :: _) _ |- _ => inversion Hf; subst; clear Hf
         | Hf : Forall2 _ [] _ |- _ => inversion Hf; subst; clear Hf
         end.
  simpl in *. subst. reflexivity.
Qed.

Lemma poc_compute_sem :
  forall dec rho rhob,
    sem poc_receiver poc_value dec [OThis; OSentinel; OSentinel] rho ->
    eval_stmt poc_CT rho poc_initial_heap pico_hash_read_compute_stmt OK rhob
      poc_initial_heap ->
    sem poc_receiver poc_value dec [OThis; ODerived; OOther] rhob.
Proof.
  intros dec rho rhob Hs Heval.
  have Hrho := poc_sem_frame dec rho Hs. subst rho.
  have Hval := poc_compute_value rhob Heval.
  unfold pico_hash_read_compute_stmt in Heval.
  inversion Heval; subst.
  unfold runtime_getVal in Hval. simpl in Hval.
  injection Hval as ->.
  unfold sem. simpl.
  constructor; [reflexivity |].
  constructor; [reflexivity |].
  constructor; [exact I | constructor].
Qed.

Lemma poc_bin_typing :
  forall op x y,
    (x = cache_tmp \/ x = cache_result) ->
    (y = cache_tmp \/ y = cache_result) ->
    stmt_typing poc_CT poc_frame_senv AbstractState
      (SVarAss cache_result (EBin op x y)) poc_frame_senv.
Proof.
  intros op x y Hx Hy.
  eapply ST_VarAss with (Te := int_type)
    (Tthis := pico_hash_witness_receiver_type) (Tx := int_type).
  - exact poc_wf_env3.
  - eapply ET_Bin with (Tx := int_type) (Ty := int_type).
    + exact poc_wf_env3.
    + destruct Hx as [-> | ->]; reflexivity.
    + reflexivity.
    + destruct Hy as [-> | ->]; reflexivity.
    + reflexivity.
  - reflexivity.
  - unfold cache_result. discriminate.
  - reflexivity.
  - apply qtype_refl; simpl; [reflexivity | discriminate].
Qed.


Notation poc_offset_flow :=
  (flow poc_CT pico_hash_derivations
     poc_receiver poc_initial_heap
     poc_value offset_dec AbstractState).
Notation poc_offset_sem :=
  (sem poc_receiver poc_value offset_dec).

Lemma poc_offset_one_typing :
  stmt_typing poc_CT poc_frame_senv AbstractState
    (SVarAss cache_result (EInt 1)) poc_frame_senv.
Proof.
  eapply ST_VarAss with (Te := int_type)
    (Tthis := pico_hash_witness_receiver_type) (Tx := int_type).
  - exact poc_wf_env3.
  - apply ET_Int. exact poc_wf_env3.
  - reflexivity.
  - unfold cache_result. discriminate.
  - reflexivity.
  - exact poc_int_subtype.
Qed.

Lemma poc_offset_decode_typing :
  stmt_typing poc_CT poc_frame_senv AbstractState
    offset_decode_stmt poc_frame_senv.
Proof.
  eapply ST_Seq; [exact poc_wf_env3 | |].
  - exact poc_offset_one_typing.
  - apply poc_bin_typing; [left | right]; reflexivity.
Qed.

Lemma poc_offset_decode_deriv :
  deriv_stmt poc_CT pico_hash_derivations
    poc_frame_senv offset_decode_stmt poc_frame_senv.
Proof.
  eapply DS_Seq; apply DS_VarAss; [apply TSERO_Int | apply TSERO_Bin].
Qed.

(** The decoding step takes the derived value to the decoded value. *)
Lemma poc_offset_decode_sem :
  forall rho rhob,
    poc_offset_sem [OThis; ODerived; OOther] rho ->
    eval_stmt poc_CT rho poc_initial_heap
      offset_decode_stmt OK rhob poc_initial_heap ->
    poc_offset_sem [OThis; ODerived; ODecoded] rhob.
Proof.
  intros [vs] rhob Hs Heval. unfold sem in Hs. simpl in Hs.
  repeat match goal with
         | Hf : Forall2 _ (_ :: _) _ |- _ => inversion Hf; subst; clear Hf
         | Hf : Forall2 _ [] _ |- _ => inversion Hf; subst; clear Hf
         end.
  simpl in *. subst.
  unfold offset_decode_stmt in Heval.
  inversion Heval; subst.
  repeat match goal with
         | He : eval_stmt _ _ _ (SVarAss _ _) OK _ _ |- _ =>
             inversion He; subst; clear He
         | He : eval_expr _ _ _ (EInt _) _ _ _ _ |- _ =>
             inversion He; subst; clear He
         | He : eval_expr _ _ _ (EBin _ _ _) _ _ _ _ |- _ =>
             inversion He; subst; clear He
         end.
  repeat match goal with
         | Hv : runtime_getVal _ _ = Some _ |- _ =>
             cbv in Hv; injection Hv as ?; subst
         end.
  unfold sem. simpl.
  constructor; [reflexivity |].
  constructor; [reflexivity |].
  constructor; [reflexivity | constructor].
Qed.

Theorem poc_offset_accessor_flow :
  poc_offset_flow [pico_hash_witness_receiver_type] [OThis]
    offset_accessor_stmt poc_frame_senv [OThis; ODerived; ODecoded].
Proof.
  unfold offset_accessor_stmt, pico_local_copy_cache_branch.
  eapply F_Seq.
  { exact (flow_local_int _ _ _ _ _ _ _ _ [OThis] cache_tmp
             poc_local_tmp_typing). }
  { apply Forall2_refl_le. }
  eapply F_Seq.
  { exact (flow_local_int _ _ _ _ _ _ _ _ [OThis; OSentinel] cache_result
             poc_local_result_typing). }
  { apply Forall2_refl_le. }
  eapply F_Seq.
  { apply (F_Read _ _ _ _ _ _ _ poc_frame_senv
             [OThis; OSentinel; OSentinel] cache_tmp cache_receiver);
      [reflexivity | exact poc_int_assign_typing]. }
  { apply Forall2_refl_le. }
  eapply F_Seq.
  { apply (F_If _ _ _ _ _ _ _ poc_frame_senv
             [OThis; OUnchecked; OSentinel] cache_tmp _ _ poc_frame_senv
             [OThis; ODerived; OOther] [OThis; ODerived; OSentinel]
             [OThis; ODerived; OOther]).
    - eapply F_Seq.
      + apply (F_Deriv _ _ _ _ _ _ _ poc_frame_senv
                 [OThis; OSentinel; OSentinel] pico_hash_read_compute_stmt
                 poc_frame_senv [OThis; ODerived; OOther]).
        * discriminate.
        * exact poc_compute_deriv.
        * exact poc_compute_typing.
        * exact (poc_compute_sem offset_dec).
      + apply Forall2_refl_le.
      + apply F_Write; reflexivity.
    - apply F_Skip.
    - apply Forall2_refl_le.
    - constructor; [apply origin_le_refl |].
      constructor; [apply origin_le_refl |].
      constructor; [right; left; reflexivity | constructor]. }
  { apply Forall2_refl_le. }
  apply (F_Deriv _ _ _ _ _ _ _ poc_frame_senv
           [OThis; ODerived; OOther] offset_decode_stmt poc_frame_senv
           [OThis; ODerived; ODecoded]).
  - discriminate.
  - exact poc_offset_decode_deriv.
  - exact poc_offset_decode_typing.
  - exact poc_offset_decode_sem.
Qed.


(** ** Concurrent calls of the accessor *)

Definition poc_call : pico_core_expr :=
  CoreRun poc_caller (SCall 1 poc_method 0 []) 0 [].

Definition poc_n_call_pool (n : nat) : pico_pool_config :=
  mkPicoPoolConfig poc_initial_state (repeat poc_call n).

(** The decoded value: the payload is 7, so the accessor returns 6. *)
Lemma poc_decoded_value : offset_dec poc_value = 6.
Proof. reflexivity. Qed.

(** One call is trace robust on the machine, by the flow judgment. *)
Theorem poc_call_trace_robust : forall V0,
  @machine_cache_safe history_cache_memory_model poc_CT _ _
    hash_cache_protocol pico_hash_stable_abs poc_value
    (pico_hash_cache_adapter poc_receiver)
    (@pico_concrete_hash_semimm history_cache_memory_model
       poc_CT poc_receiver pico_hash_derive_method poc_initial_heap poc_value)
    (cache_call_result_ok (offset_dec poc_value) 1)
    (CoreRun poc_caller (SCall 1 poc_method 0 []) V0 []).
Proof.
  intros V0.
  eapply (flow_cache_method_trace_robust poc_CT pico_hash_derivations
    poc_receiver pico_hash_derive_method poc_initial_heap poc_value
    offset_dec poc_method poc_method_def
    pico_hash_witness_receiver_type AbstractState
    (mkruntime_type Imm_r pico_hash_witness_class) [Int 0; Int 7]
    poc_caller 1 0).
  - exact poc_derivation_table.
  - exact poc_config_wf.
  - reflexivity.
  - exact poc_cache_declared.
  - exact poc_find_method.
  - reflexivity.
  - exact poc_offset_accessor_flow.
  - reflexivity.
  - simpl. lia.
Qed.

(** Any number of concurrent calls of the offset accessor preserve semantic
    immutability, and every call that returns normally returns the decoded
    value. *)
Theorem poc_n_calls_sound : forall n cfg,
  @pico_pool_steps history_cache_memory_model poc_CT (poc_n_call_pool n) cfg ->
  CacheHistSnapshotOK hash_cache_protocol
    (pico_hash_snapshot poc_receiver (pool_state cfg)) poc_value /\
  pico_pool_results_satisfy
    (cache_call_result_ok (offset_dec poc_value) 1) cfg.
Proof.
  intros n cfg Hsteps.
  assert (Hpool : @machine_pool history_cache_memory_model
    poc_CT _ _ hash_cache_protocol pico_hash_stable_abs poc_value
    (pico_hash_cache_adapter poc_receiver)
    (@pico_concrete_hash_semimm history_cache_memory_model
       poc_CT poc_receiver pico_hash_derive_method poc_initial_heap poc_value)
    (cache_call_result_ok (offset_dec poc_value) 1)
    (poc_n_call_pool n)).
  { split.
    - split; [exact poc_initial_provider_inv |].
      exact (proj2 (proj2 poc_initial_provider_inv)).
    - simpl. apply Forall_forall.
      intros e Hin. apply repeat_spec in Hin. subst e.
      apply machine_local_start.
      exact (poc_call_trace_robust 0). }
  split.
  - exact (proj2 (machine_trace_robust_semimm _ _ _ _ _ _ _ _ _ Hpool Hsteps)).
  - exact (machine_trace_robust_results _ _ _ _ _ _ _ _ _ Hpool Hsteps).
Qed.
