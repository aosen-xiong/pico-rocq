From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Subtyping Typing Bigstep.
Require Import Core.GenericDerivedCache.
Require Import Examples.PicoIfZeroCacheExamples
  Examples.PicoSemanticCacheAPIExamples
  Examples.PicoConcreteHashModel.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage
  PICOBridge.PicoIrisSemImmLogicalRelation PICOBridge.PicoSemanticConcurrency.

(** * A Closed Concurrent Hash-Cache Execution

    This file instantiates the source-independent scheduler with two calls to
    one concrete PICO hash method.  The source language remains sequential;
    the invocation pool is the semantic context in which the two calls race. *)

Definition pico_hash_concurrent_method : method_name := 0.
Definition pico_hash_concurrent_value : nat := 7.

Definition pico_hash_concurrent_method_def : method_def :=
  pico_hash_method_def pico_hash_witness_receiver_type
    pico_hash_concurrent_method pico_hash_concurrent_value.

Definition pico_hash_concurrent_class_def : class_def :=
  {| signature :=
       {| class_qualifier := Imm_c;
          cname := pico_hash_witness_class;
          super := Some pico_hash_witness_root |};
     body :=
       {| fields :=
            [pico_hash_witness_cache_def; pico_hash_witness_payload_def];
          constructor := pico_hash_witness_constructor;
          methods := [pico_hash_concurrent_method_def] |} |}.

Definition pico_hash_concurrent_CT : class_table :=
  [pico_hash_witness_root_def; pico_hash_concurrent_class_def].

Definition pico_hash_concurrent_initial_state : pico_core_state :=
  mkPicoCoreState pico_hash_witness_initial_heap
    pico_hash_witness_initial_weak.

Lemma pico_hash_concurrent_find_method :
  FindMethodWithName pico_hash_concurrent_CT pico_hash_witness_class
    pico_hash_concurrent_method pico_hash_concurrent_method_def.
Proof.
  eapply FOM_Here with
    (def := pico_hash_concurrent_class_def)
    (own_methods := [pico_hash_concurrent_method_def]).
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma pico_hash_concurrent_collect_fields :
  CollectFields pico_hash_concurrent_CT pico_hash_witness_class
    [pico_hash_witness_cache_def; pico_hash_witness_payload_def].
Proof.
  eapply CF_Inherit with
    (def := pico_hash_concurrent_class_def)
    (parent := pico_hash_witness_root)
    (parent_fields := [])
    (own_fields :=
      [pico_hash_witness_cache_def; pico_hash_witness_payload_def]).
  - reflexivity.
  - reflexivity.
  - eapply CF_Object with (def := pico_hash_witness_root_def); reflexivity.
  - reflexivity.
Qed.

Lemma pico_hash_concurrent_cache_field_def :
  sf_def_rel pico_hash_concurrent_CT pico_hash_witness_class
    hash_cache_field pico_hash_witness_cache_def.
Proof.
  unfold sf_def_rel.
  eapply FL_Found with
    (fields := [pico_hash_witness_cache_def; pico_hash_witness_payload_def]).
  - exact pico_hash_concurrent_collect_fields.
  - reflexivity.
Qed.

Lemma pico_hash_concurrent_cache_assignable :
  sf_assignability_rel pico_hash_concurrent_CT pico_hash_witness_class
    hash_cache_field Assignable.
Proof.
  unfold sf_assignability_rel.
  exists pico_hash_witness_cache_def.
  split; [exact pico_hash_concurrent_cache_field_def | reflexivity].
Qed.

Lemma pico_hash_concurrent_wf_env1 :
  wf_senv pico_hash_concurrent_CT [pico_hash_witness_receiver_type].
Proof.
  unfold wf_senv, wf_stypeuse, pico_hash_witness_receiver_type,
    pico_hash_concurrent_CT, pico_hash_concurrent_class_def,
    pico_hash_witness_class, bound, find_class, gget.
  simpl. split; [lia |].
  constructor.
  - unfold gget. simpl. split; [constructor; discriminate | lia].
  - constructor.
Qed.

Lemma pico_hash_concurrent_wf_env2 :
  wf_senv pico_hash_concurrent_CT
    [pico_hash_witness_receiver_type; int_type].
Proof.
  unfold wf_senv, wf_stypeuse, pico_hash_witness_receiver_type,
    pico_hash_concurrent_CT, pico_hash_concurrent_class_def,
    pico_hash_witness_class, bound, find_class, gget, int_type.
  simpl. split; [lia |].
  constructor.
  - unfold gget. simpl. split; [constructor; discriminate | lia].
  - constructor; [reflexivity | constructor].
Qed.

Lemma pico_hash_concurrent_wf_env3 :
  wf_senv pico_hash_concurrent_CT
    [pico_hash_witness_receiver_type; int_type; int_type].
Proof.
  unfold wf_senv, wf_stypeuse, pico_hash_witness_receiver_type,
    pico_hash_concurrent_CT, pico_hash_concurrent_class_def,
    pico_hash_witness_class, bound, find_class, gget, int_type.
  simpl. split; [lia |].
  constructor.
  - unfold gget. simpl. split; [constructor; discriminate | lia].
  - constructor; [reflexivity |].
    constructor; [reflexivity | constructor].
Qed.

Lemma pico_hash_concurrent_method_typing :
  stmt_typing pico_hash_concurrent_CT
    [pico_hash_witness_receiver_type] AbstractImm
    (pico_hash_method_stmt pico_hash_concurrent_value)
    [pico_hash_witness_receiver_type; int_type; int_type].
Proof.
  assert (Hint_sub : qualified_type_subtype pico_hash_concurrent_CT
    int_type int_type).
  { apply qtype_refl; simpl; [reflexivity | discriminate]. }
  assert (Hread : expr_has_type pico_hash_concurrent_CT
    [pico_hash_witness_receiver_type; int_type; int_type] AbstractImm
    (EField cache_receiver hash_cache_field) int_type).
  { change (expr_has_type pico_hash_concurrent_CT
      [pico_hash_witness_receiver_type; int_type; int_type] AbstractImm
      (EField 0 0) (Build_qualified_type Imm TInt)).
    eapply ET_Field_abs_imm with
      (T := pico_hash_witness_receiver_type)
      (C := pico_hash_witness_class)
      (fDef := pico_hash_witness_cache_def).
    - exact pico_hash_concurrent_wf_env3.
    - reflexivity.
    - reflexivity.
    - exact pico_hash_concurrent_cache_field_def. }
  assert (Hread_assign : stmt_typing pico_hash_concurrent_CT
    [pico_hash_witness_receiver_type; int_type; int_type] AbstractImm
    (SVarAss cache_tmp (EField cache_receiver hash_cache_field))
    [pico_hash_witness_receiver_type; int_type; int_type]).
  { eapply ST_VarAss with (Te := int_type)
      (Tthis := pico_hash_witness_receiver_type) (Tx := int_type).
    - exact pico_hash_concurrent_wf_env3.
    - exact Hread.
    - reflexivity.
    - unfold cache_tmp. discriminate.
    - reflexivity.
    - exact Hint_sub. }
  assert (Hcompute : stmt_typing pico_hash_concurrent_CT
    [pico_hash_witness_receiver_type; int_type; int_type] AbstractImm
    (pico_hash_compute_stmt pico_hash_concurrent_value)
    [pico_hash_witness_receiver_type; int_type; int_type]).
  { unfold pico_hash_compute_stmt.
    eapply ST_VarAss with (Te := int_type)
      (Tthis := pico_hash_witness_receiver_type) (Tx := int_type).
    - exact pico_hash_concurrent_wf_env3.
    - apply ET_Int. exact pico_hash_concurrent_wf_env3.
    - reflexivity.
    - unfold cache_tmp. discriminate.
    - reflexivity.
    - exact Hint_sub. }
  assert (Hwrite : stmt_typing pico_hash_concurrent_CT
    [pico_hash_witness_receiver_type; int_type; int_type] AbstractImm
    (SFldWrite cache_receiver hash_cache_field cache_tmp)
    [pico_hash_witness_receiver_type; int_type; int_type]).
  { eapply ST_FldWrite_abs_imm with
      (Tx := pico_hash_witness_receiver_type) (Ty := int_type)
      (Tthis := pico_hash_witness_receiver_type)
      (C := pico_hash_witness_class)
      (fieldT := pico_hash_witness_cache_def) (a := Assignable).
    - exact pico_hash_concurrent_wf_env3.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact pico_hash_concurrent_cache_field_def.
    - exact pico_hash_concurrent_cache_assignable.
    - exact Hint_sub.
    - reflexivity. }
  assert (Hfinal : stmt_typing pico_hash_concurrent_CT
    [pico_hash_witness_receiver_type; int_type; int_type] AbstractImm
    (SVarAss cache_result (EVar cache_tmp))
    [pico_hash_witness_receiver_type; int_type; int_type]).
  { eapply ST_VarAss with (Te := int_type)
      (Tthis := pico_hash_witness_receiver_type) (Tx := int_type).
    - exact pico_hash_concurrent_wf_env3.
    - apply ET_Var; [exact pico_hash_concurrent_wf_env3 | reflexivity].
    - reflexivity.
    - unfold cache_result. discriminate.
    - reflexivity.
    - exact Hint_sub. }
  unfold pico_hash_method_stmt, pico_hash_method_stmt_with,
    pico_hash_method_core_stmt_with, pico_local_copy_cache_stmt,
    pico_local_copy_cache_branch.
  eapply ST_Seq with
    (sΓ' := [pico_hash_witness_receiver_type; int_type]).
  - exact pico_hash_concurrent_wf_env1.
  - eapply ST_Local with (T := int_type) (x := cache_tmp).
    + exact pico_hash_concurrent_wf_env1.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - eapply ST_Seq with
      (sΓ' := [pico_hash_witness_receiver_type; int_type; int_type]).
    + exact pico_hash_concurrent_wf_env2.
    + eapply ST_Local with (T := int_type) (x := cache_result).
      * exact pico_hash_concurrent_wf_env2.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
    + eapply ST_Seq; [exact pico_hash_concurrent_wf_env3 | exact Hread_assign |].
      eapply ST_Seq; [exact pico_hash_concurrent_wf_env3 | | exact Hfinal].
      eapply ST_IfZero with (Tx := int_type).
      * exact pico_hash_concurrent_wf_env3.
      * reflexivity.
      * reflexivity.
      * eapply ST_Seq with
          (sΓ' := [pico_hash_witness_receiver_type; int_type; int_type]).
        -- exact pico_hash_concurrent_wf_env3.
        -- exact Hcompute.
        -- exact Hwrite.
      * apply ST_Skip. exact pico_hash_concurrent_wf_env3.
Qed.

Lemma pico_hash_concurrent_method_wf :
  wf_method pico_hash_concurrent_CT pico_hash_witness_class
    pico_hash_concurrent_method_def.
Proof.
  unfold pico_hash_concurrent_method_def.
  eapply pico_hash_method_def_with_wf.
  - exact pico_hash_concurrent_method_typing.
  - intros parent_def parent mdef_parent Hclass Hsuper Hfind.
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

Lemma pico_hash_concurrent_class_table_wf :
  wf_class_table pico_hash_concurrent_CT.
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
                 --- exact pico_hash_concurrent_collect_fields.
                 --- constructor.
                     ++++ apply qtype_refl; simpl;
                            [reflexivity | discriminate].
                     ++++ constructor.
                          **** apply qtype_refl; simpl;
                                 [reflexivity | discriminate].
                          **** constructor.
           ++ split.
              ** constructor; [exact pico_hash_concurrent_method_wf | constructor].
              ** split.
                 --- constructor; [simpl; tauto | constructor].
                 --- exists
                      [pico_hash_witness_cache_def;
                       pico_hash_witness_payload_def].
                     repeat split; try reflexivity.
                     ++++ exact pico_hash_concurrent_collect_fields.
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

Lemma pico_hash_concurrent_cache_declared :
  derived_cache_field pico_hash_concurrent_CT pico_hash_witness_class
    hash_cache_field.
Proof.
  unfold derived_cache_field.
  exists pico_hash_witness_cache_def.
  split; [exact pico_hash_concurrent_cache_field_def | reflexivity].
Qed.

Theorem pico_hash_concurrent_initial_provider_inv :
  pico_hash_provider_inv pico_hash_concurrent_CT 0
    pico_hash_witness_function pico_hash_concurrent_value
    pico_hash_concurrent_initial_state.
Proof.
  unfold pico_hash_concurrent_initial_state,
    pico_hash_concurrent_value.
  eapply pico_concrete_hash_initial_state with
    (initial := Int 0) (abstract_values := [Int 7]).
  - reflexivity.
  - reflexivity.
  - exact pico_hash_concurrent_cache_declared.
  - reflexivity.
  - unfold hash_cache_valid. left. reflexivity.
Qed.

Lemma pico_hash_concurrent_valid_value :
  hash_cache_valid pico_hash_concurrent_value HashField
    (Int pico_hash_concurrent_value).
Proof.
  unfold hash_cache_valid, pico_hash_concurrent_value.
  right. split; [reflexivity | discriminate].
Qed.

(** This is the only shared-state mutation rule needed by the concrete hash
    controls: appending the derived hash preserves the provider invariant. *)
Theorem pico_hash_concurrent_valid_write_preserves_provider :
  forall h h' sigma sigma' V V',
    pico_hash_provider_inv pico_hash_concurrent_CT 0
      pico_hash_witness_function pico_hash_concurrent_value
      (mkPicoCoreState h sigma) ->
    h' = update_field h 0 hash_cache_field
      (Int pico_hash_concurrent_value) ->
    wm_write sigma sigma' V V' (0, hash_cache_field)
      (Int pico_hash_concurrent_value) ->
    pico_hash_provider_inv pico_hash_concurrent_CT 0
      pico_hash_witness_function pico_hash_concurrent_value
      (mkPicoCoreState h' sigma').
Proof.
  intros h h' sigma sigma' V V' Hinv Hheap Hwrite.
  pose proof (pcsi_valid_cache_write_effect
    pico_hash_concurrent_CT hash_cache_protocol pico_hash_stable_abs
    pico_hash_concurrent_value (pico_hash_cache_adapter 0)
    (pico_concrete_hash_semimm pico_hash_concurrent_CT 0
      pico_hash_witness_function pico_hash_concurrent_value)
    h h' sigma sigma' V V' 0 hash_cache_field
    (Int pico_hash_concurrent_value) HashField
    (Int pico_hash_concurrent_value)
    Hinv Hheap Hwrite
    (pico_concrete_hash_adapter_at 0)
    (pico_concrete_hash_value_adapter 0
      (Int pico_hash_concurrent_value))
    pico_hash_concurrent_valid_value) as Heffect.
  exact (proj2 Heffect).
Qed.

Definition pico_hash_concurrent_caller : r_env :=
  mkr_env [Iot 0; Int 0].

Definition pico_hash_concurrent_invocation (initial_view : view) :
    pico_invocation :=
  mkPicoInvocation pico_hash_concurrent_caller 1 0
    pico_hash_concurrent_method [] initial_view.

Definition pico_hash_concurrent_calls : list pico_invocation :=
  [pico_hash_concurrent_invocation 0; pico_hash_concurrent_invocation 0].

Definition pico_hash_concurrent_initial_pool : pico_pool_config :=
  pico_initial_pool pico_hash_concurrent_initial_state
    pico_hash_concurrent_calls.

Lemma pico_hash_concurrent_call_entry
    `{CacheMemoryModel} :
  pico_core_step pico_hash_concurrent_CT
    (pico_invocation_control (pico_hash_concurrent_invocation 0))
    pico_hash_concurrent_initial_state
    (CoreRun (mkr_env [Iot 0])
      (pico_hash_method_stmt pico_hash_concurrent_value) 0
      [KCall pico_hash_concurrent_caller 1 cache_result])
    pico_hash_concurrent_initial_state.
Proof.
  unfold pico_invocation_control, pico_hash_concurrent_invocation,
    pico_hash_concurrent_caller, pico_hash_concurrent_initial_state.
  eapply PCS_Call with
    (loc_y := 0)
    (C := pico_hash_witness_class)
    (mdef := pico_hash_concurrent_method_def)
    (body := mbody pico_hash_concurrent_method_def)
    (mstmt := pico_hash_method_stmt pico_hash_concurrent_value)
    (ret := cache_result)
    (vals := []).
  - reflexivity.
  - reflexivity.
  - exact pico_hash_concurrent_find_method.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma pico_hash_concurrent_two_calls_enter
    `{CacheMemoryModel} :
  exists cfg,
    pico_pool_steps pico_hash_concurrent_CT
      pico_hash_concurrent_initial_pool cfg /\
    pool_state cfg = pico_hash_concurrent_initial_state /\
    pool_threads cfg =
      [CoreRun (mkr_env [Iot 0])
         (pico_hash_method_stmt pico_hash_concurrent_value) 0
         [KCall pico_hash_concurrent_caller 1 cache_result];
       CoreRun (mkr_env [Iot 0])
         (pico_hash_method_stmt pico_hash_concurrent_value) 0
         [KCall pico_hash_concurrent_caller 1 cache_result]].
Proof.
  set (entered := CoreRun (mkr_env [Iot 0])
    (pico_hash_method_stmt pico_hash_concurrent_value) 0
    [KCall pico_hash_concurrent_caller 1 cache_result]).
  exists (mkPicoPoolConfig pico_hash_concurrent_initial_state
    [entered; entered]).
  split.
  - eapply PicoPoolStepsStep.
    + eapply pico_pool_step_selected with
        (tid := 0)
        (e := pico_invocation_control (pico_hash_concurrent_invocation 0))
        (e' := entered).
      * reflexivity.
      * subst entered. apply pico_hash_concurrent_call_entry.
    + eapply PicoPoolStepsStep.
      * eapply pico_pool_step_selected with
          (tid := 1)
          (e := pico_invocation_control (pico_hash_concurrent_invocation 0))
          (e' := entered).
        -- reflexivity.
        -- subst entered. apply pico_hash_concurrent_call_entry.
      * constructor.
  - split; reflexivity.
Qed.

Definition pico_hash_concurrent_method_env : r_env :=
  mkr_env [Iot 0; Int 0; Int 0].

Definition pico_hash_concurrent_after_read_stmt : stmt :=
  SSeq
    (pico_local_copy_cache_branch
      (pico_hash_compute_stmt pico_hash_concurrent_value))
    (SVarAss cache_result (EVar cache_tmp)).

Definition pico_hash_concurrent_call_cont : pico_core_cont :=
  [KCall pico_hash_concurrent_caller 1 cache_result].

Definition pico_hash_concurrent_read_cont : pico_core_cont :=
  KSeq pico_hash_concurrent_after_read_stmt ::
    pico_hash_concurrent_call_cont.

Definition pico_hash_concurrent_read_control : pico_core_expr :=
  CoreRun pico_hash_concurrent_method_env
    (SVarAss cache_tmp (EField cache_receiver hash_cache_field)) 0
    pico_hash_concurrent_read_cont.

Lemma pico_hash_concurrent_method_to_read
    `{CacheMemoryModel} :
  pico_core_steps pico_hash_concurrent_CT
    (CoreRun (mkr_env [Iot 0])
      (pico_hash_method_stmt pico_hash_concurrent_value) 0
      pico_hash_concurrent_call_cont)
    pico_hash_concurrent_initial_state
    pico_hash_concurrent_read_control
    pico_hash_concurrent_initial_state.
Proof.
  unfold pico_hash_method_stmt, pico_hash_method_stmt_with,
    pico_hash_method_core_stmt_with, pico_local_copy_cache_stmt,
    pico_hash_concurrent_call_cont, pico_hash_concurrent_read_control,
    pico_hash_concurrent_read_cont, pico_hash_concurrent_after_read_stmt,
    pico_hash_concurrent_method_env, pico_hash_concurrent_initial_state.
  eapply PicoCoreStepsStep; [apply PCS_Seq |].
  eapply PicoCoreStepsStep; [apply PCS_Local; reflexivity |].
  eapply PicoCoreStepsStep; [apply PCS_SkipSeq |].
  eapply PicoCoreStepsStep; [apply PCS_Seq |].
  eapply PicoCoreStepsStep; [apply PCS_Local; reflexivity |].
  eapply PicoCoreStepsStep; [apply PCS_SkipSeq |].
  eapply PicoCoreStepsStep; [apply PCS_Seq |].
  constructor.
Qed.

Lemma pico_hash_concurrent_two_calls_reach_reads
    `{CacheMemoryModel} :
  exists cfg,
    pico_pool_steps pico_hash_concurrent_CT
      pico_hash_concurrent_initial_pool cfg /\
    pool_state cfg = pico_hash_concurrent_initial_state /\
    pool_threads cfg =
      [pico_hash_concurrent_read_control;
       pico_hash_concurrent_read_control].
Proof.
  destruct pico_hash_concurrent_two_calls_enter as
    [entered [Henter [Hstate Hthreads]]].
  destruct entered as [entered_state entered_threads].
  simpl in Hstate, Hthreads.
  subst entered_state entered_threads.
  set (method_control := CoreRun (mkr_env [Iot 0])
    (pico_hash_method_stmt pico_hash_concurrent_value) 0
    pico_hash_concurrent_call_cont).
  assert (Hmethod : pico_core_steps pico_hash_concurrent_CT method_control
    pico_hash_concurrent_initial_state pico_hash_concurrent_read_control
    pico_hash_concurrent_initial_state).
  { subst method_control. apply pico_hash_concurrent_method_to_read. }
  change (pico_pool_steps pico_hash_concurrent_CT
    pico_hash_concurrent_initial_pool
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [method_control; method_control])) in Henter.
  assert (Hfirst : pico_pool_steps pico_hash_concurrent_CT
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [method_control; method_control])
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [pico_hash_concurrent_read_control; method_control])).
  { change (pico_pool_steps pico_hash_concurrent_CT
      (mkPicoPoolConfig pico_hash_concurrent_initial_state
        [method_control; method_control])
      (mkPicoPoolConfig pico_hash_concurrent_initial_state
        (update 0 pico_hash_concurrent_read_control
          [method_control; method_control]))).
    eapply pico_pool_steps_lift_thread; simpl; eauto. }
  assert (Hsecond : pico_pool_steps pico_hash_concurrent_CT
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [pico_hash_concurrent_read_control; method_control])
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [pico_hash_concurrent_read_control;
       pico_hash_concurrent_read_control])).
  { change (pico_pool_steps pico_hash_concurrent_CT
      (mkPicoPoolConfig pico_hash_concurrent_initial_state
        [pico_hash_concurrent_read_control; method_control])
      (mkPicoPoolConfig pico_hash_concurrent_initial_state
        (update 1 pico_hash_concurrent_read_control
          [pico_hash_concurrent_read_control; method_control]))).
    eapply pico_pool_steps_lift_thread; simpl; eauto. }
  exists (mkPicoPoolConfig pico_hash_concurrent_initial_state
    [pico_hash_concurrent_read_control; pico_hash_concurrent_read_control]).
  split.
  - eapply pico_pool_steps_trans.
    + exact Henter.
    + eapply pico_pool_steps_trans; eauto.
  - split; reflexivity.
Qed.

Definition pico_hash_concurrent_after_read_control : pico_core_expr :=
  CoreRun
    (set_vars pico_hash_concurrent_method_env
      (update cache_tmp (Int 0) (vars pico_hash_concurrent_method_env)))
    SSkip 0
    pico_hash_concurrent_read_cont.

Lemma pico_hash_concurrent_initial_read :
  @wm_read history_cache_memory_model pico_hash_witness_initial_weak 0
    (0, hash_cache_field) (Int 0) 0.
Proof.
  split; [reflexivity |].
  exists (mkWriteMsg (Int 0) 0 0).
  split; [|reflexivity].
  unfold pico_hash_witness_initial_weak, pico_hash_witness_object,
    pico_core_alloc_weak, history_of, hash_cache_field.
  simpl. left. reflexivity.
Qed.

Lemma pico_hash_concurrent_first_default_read :
  @pico_pool_access history_cache_memory_model pico_hash_concurrent_CT
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [pico_hash_concurrent_read_control;
       pico_hash_concurrent_read_control])
    (mkPicoAccessEvent 0 PicoRead (0, hash_cache_field) (Int 0))
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [pico_hash_concurrent_after_read_control;
       pico_hash_concurrent_read_control]).
Proof.
  unfold pico_hash_concurrent_read_control,
    pico_hash_concurrent_after_read_control,
    pico_hash_concurrent_method_env, pico_hash_concurrent_initial_state.
  unfold cache_tmp, cache_receiver, hash_cache_field.
  eapply PicoPoolRead with
    (state := pico_hash_concurrent_initial_state)
    (threads := [pico_hash_concurrent_read_control;
      pico_hash_concurrent_read_control])
    (tid := 0) (rGamma := mkr_env [Iot 0; Int 0; Int 0])
    (x := 1) (y := 0) (f := 0) (old := Int 0) (loc := 0)
    (v := Int 0) (V := 0) (V' := 0)
    (K := pico_hash_concurrent_read_cont)
    (h := pico_hash_witness_initial_heap)
    (sigma := pico_hash_witness_initial_weak); simpl; eauto.
  exact pico_hash_concurrent_initial_read.
Qed.

Lemma pico_hash_concurrent_second_default_read :
  @pico_pool_access history_cache_memory_model pico_hash_concurrent_CT
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [pico_hash_concurrent_after_read_control;
       pico_hash_concurrent_read_control])
    (mkPicoAccessEvent 1 PicoRead (0, hash_cache_field) (Int 0))
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [pico_hash_concurrent_after_read_control;
       pico_hash_concurrent_after_read_control]).
Proof.
  unfold pico_hash_concurrent_read_control,
    pico_hash_concurrent_after_read_control,
    pico_hash_concurrent_method_env, pico_hash_concurrent_initial_state.
  unfold cache_tmp, cache_receiver, hash_cache_field.
  eapply PicoPoolRead with
    (state := pico_hash_concurrent_initial_state)
    (threads := [pico_hash_concurrent_after_read_control;
      pico_hash_concurrent_read_control])
    (tid := 1) (rGamma := mkr_env [Iot 0; Int 0; Int 0])
    (x := 1) (y := 0) (f := 0) (old := Int 0) (loc := 0)
    (v := Int 0) (V := 0) (V' := 0)
    (K := pico_hash_concurrent_read_cont)
    (h := pico_hash_witness_initial_heap)
    (sigma := pico_hash_witness_initial_weak); simpl; eauto.
  exact pico_hash_concurrent_initial_read.
Qed.

Theorem pico_hash_concurrent_both_read_default_before_writes :
  exists before_reads after_first after_second,
    @pico_pool_steps history_cache_memory_model pico_hash_concurrent_CT
      pico_hash_concurrent_initial_pool before_reads /\
    @pico_pool_access history_cache_memory_model pico_hash_concurrent_CT
      before_reads
      (mkPicoAccessEvent 0 PicoRead (0, hash_cache_field) (Int 0))
      after_first /\
    @pico_pool_access history_cache_memory_model pico_hash_concurrent_CT
      after_first
      (mkPicoAccessEvent 1 PicoRead (0, hash_cache_field) (Int 0))
      after_second /\
    pool_state after_second = pico_hash_concurrent_initial_state /\
    pool_threads after_second =
      [pico_hash_concurrent_after_read_control;
       pico_hash_concurrent_after_read_control].
Proof.
  destruct (@pico_hash_concurrent_two_calls_reach_reads
    history_cache_memory_model) as [before [Hreach [Hstate Hthreads]]].
  destruct before as [state threads]. simpl in Hstate, Hthreads.
  subst state threads.
  exists
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [pico_hash_concurrent_read_control;
       pico_hash_concurrent_read_control]),
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [pico_hash_concurrent_after_read_control;
       pico_hash_concurrent_read_control]),
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [pico_hash_concurrent_after_read_control;
       pico_hash_concurrent_after_read_control]).
  repeat split; try reflexivity.
  - exact Hreach.
  - exact pico_hash_concurrent_first_default_read.
  - exact pico_hash_concurrent_second_default_read.
Qed.

Definition pico_hash_concurrent_hash_env : r_env :=
  set_vars pico_hash_concurrent_method_env
    (update cache_tmp (Int pico_hash_concurrent_value)
      (vars pico_hash_concurrent_method_env)).

Definition pico_hash_concurrent_write_cont : pico_core_cont :=
  KSeq (SVarAss cache_result (EVar cache_tmp)) ::
    pico_hash_concurrent_call_cont.

Definition pico_hash_concurrent_write_control : pico_core_expr :=
  CoreRun pico_hash_concurrent_hash_env
    (SFldWrite cache_receiver hash_cache_field cache_tmp) 0
    pico_hash_concurrent_write_cont.

Lemma pico_hash_concurrent_after_read_to_write
    `{CacheMemoryModel} :
  pico_core_steps pico_hash_concurrent_CT
    pico_hash_concurrent_after_read_control
    pico_hash_concurrent_initial_state
    pico_hash_concurrent_write_control
    pico_hash_concurrent_initial_state.
Proof.
  unfold pico_hash_concurrent_after_read_control,
    pico_hash_concurrent_read_cont, pico_hash_concurrent_after_read_stmt,
    pico_hash_concurrent_write_control, pico_hash_concurrent_write_cont,
    pico_hash_concurrent_hash_env, pico_hash_concurrent_method_env,
    pico_hash_concurrent_initial_state, pico_local_copy_cache_branch,
    pico_hash_compute_stmt, pico_hash_concurrent_value,
    cache_tmp, cache_result, cache_receiver, hash_cache_field,
    pico_hash_concurrent_call_cont, set_vars.
  simpl.
  eapply PicoCoreStepsStep; [apply PCS_SkipSeq |].
  eapply PicoCoreStepsStep; [apply PCS_Seq |].
  eapply PicoCoreStepsStep; [apply PCS_IfZero; reflexivity |].
  eapply PicoCoreStepsStep; [apply PCS_Seq |].
  eapply PicoCoreStepsStep;
    [apply PCS_AssignInt with (old_v := Int 0); reflexivity |].
  eapply PicoCoreStepsStep; [apply PCS_SkipSeq |].
  constructor.
Qed.

Theorem pico_hash_concurrent_both_reach_writes_after_default_reads :
  exists cfg,
    @pico_pool_steps history_cache_memory_model pico_hash_concurrent_CT
      pico_hash_concurrent_initial_pool cfg /\
    pool_state cfg = pico_hash_concurrent_initial_state /\
    pool_threads cfg =
      [pico_hash_concurrent_write_control;
       pico_hash_concurrent_write_control].
Proof.
  destruct pico_hash_concurrent_both_read_default_before_writes as
    [before [after_first [after_second
      [Hreach [Hread0 [Hread1 [Hstate Hthreads]]]]]]].
  destruct after_second as [state threads]. simpl in Hstate, Hthreads.
  subst state threads.
  pose proof (pico_pool_access_is_step _ _ _ _ Hread0) as Hread0_step.
  pose proof (pico_pool_access_is_step _ _ _ _ Hread1) as Hread1_step.
  assert (Hreads : @pico_pool_steps history_cache_memory_model
    pico_hash_concurrent_CT pico_hash_concurrent_initial_pool
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [pico_hash_concurrent_after_read_control;
       pico_hash_concurrent_after_read_control])).
  { eapply pico_pool_steps_trans; [exact Hreach |].
    eapply PicoPoolStepsStep; [exact Hread0_step |].
    eapply PicoPoolStepsStep; [exact Hread1_step | constructor]. }
  assert (Hmethod : @pico_core_steps history_cache_memory_model
    pico_hash_concurrent_CT pico_hash_concurrent_after_read_control
    pico_hash_concurrent_initial_state pico_hash_concurrent_write_control
    pico_hash_concurrent_initial_state).
  { apply pico_hash_concurrent_after_read_to_write. }
  assert (Hfirst : @pico_pool_steps history_cache_memory_model
    pico_hash_concurrent_CT
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [pico_hash_concurrent_after_read_control;
       pico_hash_concurrent_after_read_control])
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [pico_hash_concurrent_write_control;
       pico_hash_concurrent_after_read_control])).
  { change (@pico_pool_steps history_cache_memory_model
      pico_hash_concurrent_CT
      (mkPicoPoolConfig pico_hash_concurrent_initial_state
        [pico_hash_concurrent_after_read_control;
         pico_hash_concurrent_after_read_control])
      (mkPicoPoolConfig pico_hash_concurrent_initial_state
        (update 0 pico_hash_concurrent_write_control
          [pico_hash_concurrent_after_read_control;
           pico_hash_concurrent_after_read_control]))).
    eapply pico_pool_steps_lift_thread; simpl; eauto. }
  assert (Hsecond : @pico_pool_steps history_cache_memory_model
    pico_hash_concurrent_CT
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [pico_hash_concurrent_write_control;
       pico_hash_concurrent_after_read_control])
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [pico_hash_concurrent_write_control;
       pico_hash_concurrent_write_control])).
  { change (@pico_pool_steps history_cache_memory_model
      pico_hash_concurrent_CT
      (mkPicoPoolConfig pico_hash_concurrent_initial_state
        [pico_hash_concurrent_write_control;
         pico_hash_concurrent_after_read_control])
      (mkPicoPoolConfig pico_hash_concurrent_initial_state
        (update 1 pico_hash_concurrent_write_control
          [pico_hash_concurrent_write_control;
           pico_hash_concurrent_after_read_control]))).
    eapply pico_pool_steps_lift_thread; simpl; eauto. }
  exists (mkPicoPoolConfig pico_hash_concurrent_initial_state
    [pico_hash_concurrent_write_control;
     pico_hash_concurrent_write_control]).
  split.
  - eapply pico_pool_steps_trans; [exact Hreads |].
    eapply pico_pool_steps_trans; eauto.
  - split; reflexivity.
Qed.

Definition pico_hash_concurrent_after_write_control : pico_core_expr :=
  CoreRun pico_hash_concurrent_hash_env SSkip 0
    pico_hash_concurrent_write_cont.

Lemma pico_hash_concurrent_first_write :
  @pico_pool_access history_cache_memory_model pico_hash_concurrent_CT
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [pico_hash_concurrent_write_control;
       pico_hash_concurrent_write_control])
    (mkPicoAccessEvent 1 PicoWrite (0, hash_cache_field)
      (Int pico_hash_concurrent_value))
    (mkPicoPoolConfig pico_hash_witness_bad_state
      [pico_hash_concurrent_write_control;
       pico_hash_concurrent_after_write_control]).
Proof.
  unfold pico_hash_concurrent_write_control,
    pico_hash_concurrent_after_write_control,
    pico_hash_concurrent_hash_env, pico_hash_concurrent_method_env,
    pico_hash_concurrent_initial_state, pico_hash_witness_bad_state,
    pico_hash_witness_bad_heap, pico_hash_witness_bad_weak,
    pico_hash_witness_initial_heap, pico_hash_witness_initial_weak,
    pico_hash_concurrent_value, cache_receiver, cache_tmp,
    hash_cache_field, set_vars.
  eapply PicoPoolWrite with
    (threads :=
      [CoreRun {| vars := [Iot 0; Int 7; Int 0] |}
         (SFldWrite 0 0 1) 0 pico_hash_concurrent_write_cont;
       CoreRun {| vars := [Iot 0; Int 7; Int 0] |}
         (SFldWrite 0 0 1) 0 pico_hash_concurrent_write_cont])
    (tid := 1) (rGamma := mkr_env [Iot 0; Int 7; Int 0])
    (x := 0) (f := 0) (y := 1) (loc := 0)
    (o := pico_hash_witness_object) (assign := Assignable)
    (v := Int 7) (V := 0) (V' := 0)
    (K := pico_hash_concurrent_write_cont); simpl; eauto.
  - exact pico_hash_concurrent_cache_assignable.
  - exact pico_hash_witness_valid_write.
Qed.

Definition pico_hash_concurrent_twice_weak : wm_state :=
  append_write_msg pico_hash_witness_bad_weak (0, hash_cache_field)
    (mkWriteMsg (Int pico_hash_concurrent_value)
      (length (history_of pico_hash_witness_bad_weak
        (0, hash_cache_field))) 0).

Definition pico_hash_concurrent_twice_heap : heap :=
  update_field pico_hash_witness_bad_heap 0 hash_cache_field
    (Int pico_hash_concurrent_value).

Definition pico_hash_concurrent_twice_state : pico_core_state :=
  mkPicoCoreState pico_hash_concurrent_twice_heap
    pico_hash_concurrent_twice_weak.

Lemma pico_hash_concurrent_second_write_relation :
  wm_write pico_hash_witness_bad_weak pico_hash_concurrent_twice_weak
    0 0 (0, hash_cache_field) (Int pico_hash_concurrent_value).
Proof. split; reflexivity. Qed.

Lemma pico_hash_concurrent_second_write :
  @pico_pool_access history_cache_memory_model pico_hash_concurrent_CT
    (mkPicoPoolConfig pico_hash_witness_bad_state
      [pico_hash_concurrent_write_control;
       pico_hash_concurrent_after_write_control])
    (mkPicoAccessEvent 0 PicoWrite (0, hash_cache_field)
      (Int pico_hash_concurrent_value))
    (mkPicoPoolConfig pico_hash_concurrent_twice_state
      [pico_hash_concurrent_after_write_control;
       pico_hash_concurrent_after_write_control]).
Proof.
  assert (Hobj : exists o,
    runtime_getObj pico_hash_witness_bad_heap 0 = Some o).
  { unfold pico_hash_witness_bad_heap, pico_hash_witness_initial_heap.
    eexists. unfold runtime_getObj, update_field. simpl. reflexivity. }
  destruct Hobj as [written_obj Hobj].
  assert (Hwritten_class : rctype (rt_type written_obj) =
      pico_hash_witness_class).
  { unfold pico_hash_witness_bad_heap, pico_hash_witness_initial_heap,
      runtime_getObj, update_field, pico_hash_witness_object in Hobj.
    simpl in Hobj. inversion Hobj. reflexivity. }
  assert (Hwritten_qualifier : rqtype (rt_type written_obj) = Imm_r).
  { unfold pico_hash_witness_bad_heap, pico_hash_witness_initial_heap,
      runtime_getObj, update_field, pico_hash_witness_object in Hobj.
    simpl in Hobj. inversion Hobj. reflexivity. }
  unfold pico_hash_concurrent_write_control,
    pico_hash_concurrent_after_write_control,
    pico_hash_concurrent_hash_env, pico_hash_concurrent_method_env,
    pico_hash_witness_bad_state, pico_hash_concurrent_twice_state,
    pico_hash_concurrent_twice_heap, pico_hash_concurrent_value,
    cache_receiver, cache_tmp, hash_cache_field, set_vars.
  eapply PicoPoolWrite with
    (threads :=
      [CoreRun {| vars := [Iot 0; Int 7; Int 0] |}
         (SFldWrite 0 0 1) 0 pico_hash_concurrent_write_cont;
       CoreRun {| vars := [Iot 0; Int 7; Int 0] |}
         SSkip 0 pico_hash_concurrent_write_cont])
    (tid := 0) (rGamma := mkr_env [Iot 0; Int 7; Int 0])
    (x := 0) (f := 0) (y := 1) (loc := 0)
    (o := written_obj) (assign := Assignable)
    (v := Int 7) (V := 0) (V' := 0)
    (K := pico_hash_concurrent_write_cont); simpl; eauto.
  - rewrite Hwritten_class. exact pico_hash_concurrent_cache_assignable.
  - rewrite Hwritten_qualifier. reflexivity.
  - exact pico_hash_concurrent_second_write_relation.
Qed.

Theorem pico_two_hash_invocations_exhibit_race :
  @pico_semantic_race history_cache_memory_model pico_hash_concurrent_CT
    pico_hash_concurrent_initial_pool.
Proof.
  destruct pico_hash_concurrent_both_reach_writes_after_default_reads as
    [before [Hreach [Hstate Hthreads]]].
  destruct before as [state threads]. simpl in Hstate, Hthreads.
  subst state threads.
  exists
    (mkPicoPoolConfig pico_hash_concurrent_initial_state
      [pico_hash_concurrent_write_control;
       pico_hash_concurrent_write_control]),
    (mkPicoPoolConfig pico_hash_witness_bad_state
      [pico_hash_concurrent_write_control;
       pico_hash_concurrent_after_write_control]),
    (mkPicoPoolConfig pico_hash_witness_bad_state
      [pico_hash_concurrent_write_control;
       pico_hash_concurrent_after_write_control]),
    (mkPicoPoolConfig pico_hash_concurrent_twice_state
      [pico_hash_concurrent_after_write_control;
       pico_hash_concurrent_after_write_control]),
    (mkPicoAccessEvent 1 PicoWrite (0, hash_cache_field)
      (Int pico_hash_concurrent_value)),
    (mkPicoAccessEvent 0 PicoWrite (0, hash_cache_field)
      (Int pico_hash_concurrent_value)).
  split; [exact Hreach |].
  split; [exact pico_hash_concurrent_first_write |].
  split; [constructor |].
  split; [exact pico_hash_concurrent_second_write |].
  unfold pico_accesses_conflict. simpl.
  split; [discriminate |].
  split; [reflexivity |].
  left. reflexivity.
Qed.
