From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Subtyping Typing Bigstep Reachability
  ViewpointAdaptation AbstractStatePreservation.
Require Import Examples.PicoIfZeroCache
  Examples.PicoConcreteHashProvider
  Examples.PicoRefCacheJudgment.
Require Import PICOBridge.PicoCoreLanguage
  PICOBridge.PicoMemoryModel PICOBridge.PicoCacheTyping
  PICOBridge.PicoDerivationNoninterference PICOBridge.PicoDerivationSmallStep
  PICOBridge.PicoSemanticConcurrency.

(** * A Class with a Reference Cache

    An immutable class with one field, a lazily initialized reference to a
    view object.  Its accessor has the reference-cache shape and is well
    typed, so the judgment applies: any number of concurrent calls preserve
    the invariant and return valid references. *)

Definition ref_view_class : class_name := pico_hash_witness_root.
Definition ref_class : class_name := 1.
Definition ref_cache_field : var := 0.
Definition ref_method : method_name := 0.

Definition ref_view_type : qualified_type :=
  Build_qualified_type Imm (TRef ref_view_class).
Definition ref_receiver_type : qualified_type :=
  Build_qualified_type Imm (TRef ref_class).

Definition ref_cache_def : field_def :=
  {| ftype :=
       {| assignability := Assignable;
          mutability := Imm_f;
          f_base_type := TRef ref_view_class |};
     fname := ref_cache_field |}.

Definition ref_method_body : stmt :=
  ref_cache_body ref_cache_field ref_view_class Imm_c [] SSkip ref_view_type.

Definition ref_method_def : method_def :=
  {| msignature :=
       {| mscope := AbstractState;
          mret := ref_view_type;
          mname := ref_method;
          mreceiver := ref_receiver_type;
          mparams := [] |};
     mbody := {| mbody_stmt := ref_method_body; mreturn := cache_result |} |}.

Definition ref_constructor : constructor_def :=
  {| csignature := {| cqualifier := Imm_c; cparams := [ref_view_type] |} |}.

Definition ref_class_def : class_def :=
  {| signature :=
       {| class_qualifier := Imm_c;
          cname := ref_class;
          super := Some pico_hash_witness_root |};
     body :=
       {| fields := [ref_cache_def];
          constructor := ref_constructor;
          methods := [ref_method_def] |} |}.

Definition ref_CT : class_table := [pico_hash_witness_root_def; ref_class_def].

Definition ref_receiver : Loc := 1.
Definition ref_owner : Obj :=
  mkObj (mkruntime_type Imm_r pico_hash_witness_root) [].
Definition ref_object : Obj :=
  mkObj (mkruntime_type Imm_r ref_class) [Null_a].
Definition ref_heap : heap := [ref_owner; ref_object].
Definition ref_weak : wm_state :=
  pico_core_alloc_weak (pico_core_alloc_weak empty_wm_state ref_owner 0)
    ref_object 0.
Definition ref_state : pico_core_state := mkPicoCoreState ref_heap ref_weak.

Definition ref_senv3 : s_env :=
  [ref_receiver_type; ref_view_type; ref_view_type].

Lemma ref_collect_fields :
  CollectFields ref_CT ref_class [ref_cache_def].
Proof.
  eapply CF_Inherit with
    (def := ref_class_def) (parent := pico_hash_witness_root)
    (parent_fields := []) (own_fields := [ref_cache_def]).
  - reflexivity.
  - reflexivity.
  - eapply CF_Object with (def := pico_hash_witness_root_def); reflexivity.
  - reflexivity.
Qed.

Lemma ref_cache_field_def :
  sf_def_rel ref_CT ref_class ref_cache_field ref_cache_def.
Proof.
  eapply FL_Found; [exact ref_collect_fields | reflexivity].
Qed.

Lemma ref_cache_assignable :
  sf_assignability_rel ref_CT ref_class ref_cache_field Assignable.
Proof.
  exists ref_cache_def. split; [exact ref_cache_field_def | reflexivity].
Qed.

Lemma ref_wf_env1 : wf_senv ref_CT [ref_receiver_type].
Proof.
  unfold wf_senv, wf_stypeuse, ref_receiver_type, ref_CT, ref_class_def,
    ref_class, bound, find_class, gget.
  simpl. split; [lia |].
  constructor.
  - unfold gget. simpl. split; [constructor; discriminate | lia].
  - constructor.
Qed.

Lemma ref_view_type_wf :
  wf_stypeuse ref_CT (sqtype ref_view_type) (sbase ref_view_type).
Proof.
  unfold wf_stypeuse, ref_view_type, ref_view_class, ref_CT, bound,
    find_class, gget. simpl.
  split; [constructor; discriminate | unfold pico_hash_witness_root; lia].
Qed.

Lemma ref_wf_env2 : wf_senv ref_CT [ref_receiver_type; ref_view_type].
Proof.
  destruct ref_wf_env1 as [Hlen Hall].
  split; [simpl; lia |].
  inversion Hall; subst.
  constructor; [assumption |].
  constructor; [exact ref_view_type_wf | constructor].
Qed.

Lemma ref_wf_env3 : wf_senv ref_CT ref_senv3.
Proof.
  destruct ref_wf_env2 as [Hlen Hall].
  split; [simpl; lia |].
  inversion Hall as [| ? ? H1 Hrest]; subst.
  inversion Hrest; subst.
  constructor; [assumption |].
  constructor; [assumption |].
  constructor; [exact ref_view_type_wf | constructor].
Qed.

(** The accessor is well typed. *)
Lemma ref_method_typing :
  stmt_typing ref_CT [ref_receiver_type] AbstractState ref_method_body
    ref_senv3.
Proof.
  assert (Hsub : qualified_type_subtype ref_CT ref_view_type ref_view_type).
  { apply qtype_refl; simpl; [| discriminate].
    unfold wf_qualified_base, ref_view_type, ref_view_class,
      pico_hash_witness_root, ref_CT. simpl. lia. }
  assert (Hread : stmt_typing ref_CT ref_senv3 AbstractState
    (SVarAss cache_tmp (EField cache_receiver ref_cache_field)) ref_senv3).
  { eapply ST_VarAss with (Te := ref_view_type)
      (Tthis := ref_receiver_type) (Tx := ref_view_type).
    - exact ref_wf_env3.
    - change (expr_has_type ref_CT ref_senv3 AbstractState
        (EField 0 0) (Build_qualified_type Imm (TRef ref_view_class))).
      eapply ET_Field_abstract_state with
        (T := ref_receiver_type) (C := ref_class) (fDef := ref_cache_def).
      + exact ref_wf_env3.
      + reflexivity.
      + reflexivity.
      + exact ref_cache_field_def.
      + left. reflexivity.
    - reflexivity.
    - unfold cache_tmp. discriminate.
    - reflexivity.
    - exact Hsub. }
  assert (Hnew : stmt_typing ref_CT ref_senv3 AbstractState
    (SNew cache_tmp Imm_c ref_view_class []) ref_senv3).
  { eapply S_New with (Tx := ref_view_type) (argtypes := [])
      (Tthis := ref_receiver_type)
      (consig := csignature pico_hash_witness_root_constructor).
    - exact ref_wf_env3.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold cache_tmp. discriminate.
    - reflexivity.
    - constructor.
    - exact Hsub. }
  assert (Hwrite : stmt_typing ref_CT ref_senv3 AbstractState
    (SFldWrite cache_receiver ref_cache_field cache_tmp) ref_senv3).
  { eapply ST_FldWrite_abstract_state with
      (Tx := ref_receiver_type) (Ty := ref_view_type)
      (Tthis := ref_receiver_type) (C := ref_class)
      (fieldT := ref_cache_def) (a := Assignable).
    - exact ref_wf_env3.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact ref_cache_field_def.
    - exact ref_cache_assignable.
    - exact Hsub.
    - reflexivity. }
  assert (Hfinal : stmt_typing ref_CT ref_senv3 AbstractState
    (SVarAss cache_result (EVar cache_tmp)) ref_senv3).
  { eapply ST_VarAss with (Te := ref_view_type)
      (Tthis := ref_receiver_type) (Tx := ref_view_type).
    - exact ref_wf_env3.
    - apply ET_Var; [exact ref_wf_env3 | reflexivity].
    - reflexivity.
    - unfold cache_result. discriminate.
    - reflexivity.
    - exact Hsub. }
  unfold ref_method_body, ref_cache_body.
  eapply ST_Seq with (sΓ' := [ref_receiver_type; ref_view_type]).
  - exact ref_wf_env1.
  - eapply ST_Local with (T := ref_view_type) (x := cache_tmp).
    + exact ref_wf_env1.
    + exact ref_view_type_wf.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - eapply ST_Seq with (sΓ' := ref_senv3).
    + exact ref_wf_env2.
    + eapply ST_Local with (T := ref_view_type) (x := cache_result).
      * exact ref_wf_env2.
      * exact ref_view_type_wf.
      * reflexivity.
      * reflexivity.
      * reflexivity.
    + eapply ST_Seq; [exact ref_wf_env3 | exact Hread |].
      eapply ST_Seq; [exact ref_wf_env3 | | exact Hfinal].
      eapply ST_IfZero with (Tx := ref_view_type).
      * exact ref_wf_env3.
      * reflexivity.
      * right. exists ref_view_class. reflexivity.
      * eapply ST_Seq with (sΓ' := ref_senv3).
        -- exact ref_wf_env3.
        -- apply ST_Skip. exact ref_wf_env3.
        -- eapply ST_Seq with (sΓ' := ref_senv3);
             [exact ref_wf_env3 | exact Hnew | exact Hwrite].
      * apply ST_Skip. exact ref_wf_env3.
Qed.

Lemma ref_method_wf : wf_method ref_CT ref_class ref_method_def.
Proof.
  unfold wf_method; simpl.
  split; [exact ref_view_type_wf |].
  exists ref_senv3, ref_view_type.
  split; [exact ref_method_typing |].
  split; [unfold cache_result; simpl; lia |].
  split; [unfold cache_result; reflexivity |].
  split.
  - apply qtype_refl; simpl; [| discriminate].
    unfold wf_qualified_base, ref_view_type, ref_view_class,
      pico_hash_witness_root, ref_CT. simpl. lia.
  - split.
    + intros parent_def parent mdef_parent qc Hclass Hsuper Hbound Hfind.
      simpl in Hclass. inversion Hclass; subst parent_def.
      simpl in Hsuper. inversion Hsuper; subst parent.
      inversion Hfind; subst.
      * simpl in Hfind0. inversion Hfind0; subst def.
        unfold pico_hash_witness_root_def in Hget_method.
        simpl in Hget_method. discriminate.
      * simpl in Hfind0. inversion Hfind0; subst def.
        unfold pico_hash_witness_root_def in Hsuper0.
        simpl in Hsuper0. discriminate.
    + split; [reflexivity |].
      intros [Hscope | Hscope]; discriminate.
Qed.

Lemma ref_class_table_wf : wf_class_table ref_CT.
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
          (superC := pico_hash_witness_root) (thisC := ref_class);
          simpl; try reflexivity.
        -- unfold ref_class, pico_hash_witness_root. lia.
        -- split.
           ++ unfold wf_constructor. simpl.
              split; [reflexivity |].
              split.
              ** repeat constructor; try reflexivity;
                   first [exact ref_view_type_wf | discriminate
                         | unfold wf_qualified_base, ref_view_type,
                             ref_view_class, pico_hash_witness_root, ref_CT;
                           simpl; lia ].
              ** exists [ref_cache_def].
                 repeat split; try reflexivity.
                 --- exact ref_collect_fields.
                 --- constructor; [| constructor].
                     apply qtype_refl; simpl; [| discriminate].
                     unfold wf_qualified_base, ref_view_class,
                       pico_hash_witness_root, ref_CT. simpl. lia.
           ++ split.
              ** constructor; [exact ref_method_wf | constructor].
              ** split.
                 --- constructor; [simpl; tauto | constructor].
                 --- exists [ref_cache_def].
                     repeat split; try reflexivity.
                     ++++ exact ref_collect_fields.
                     ++++ right. reflexivity.
                     ++++ repeat constructor; simpl; trivial;
                            first [discriminate | unfold pico_hash_witness_root; lia].
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

Lemma ref_heap_wf : wf_heap ref_CT ref_heap.
Proof.
  unfold wf_heap. intros loc Hloc.
  unfold ref_heap in Hloc. simpl in Hloc.
  destruct loc as [| [| loc]]; [| | lia].
  - unfold wf_obj, runtime_getObj, ref_heap, ref_owner. simpl.
    split.
    + unfold wf_rtypeuse, bound. simpl.
      split; [unfold pico_hash_witness_root, ref_CT; simpl; lia | trivial].
    + exists (@nil field_def). split.
      * eapply CF_Object with (def := pico_hash_witness_root_def);
          reflexivity.
      * split; [reflexivity | constructor].
  - unfold wf_obj, runtime_getObj, ref_heap, ref_object. simpl.
    split.
    + unfold wf_rtypeuse, bound. simpl.
      split; [unfold ref_class, ref_CT; simpl; lia | trivial].
    + exists [ref_cache_def].
      split; [exact ref_collect_fields |].
      split; [reflexivity |].
      repeat constructor.
Qed.

Definition ref_frame_env : r_env := mkr_env [Iot ref_receiver; Null_a; Null_a].

Lemma ref_frame_config_wf :
  wf_r_config ref_CT ref_senv3 ref_frame_env ref_heap.
Proof.
  unfold wf_r_config.
  split; [exact ref_class_table_wf |].
  split; [exact ref_heap_wf |].
  split.
  - unfold wf_renv, ref_heap, ref_frame_env, ref_receiver. simpl.
    split; [lia |]. split.
    + exists 1. split; reflexivity || lia.
    + constructor; [simpl; trivial |].
      constructor; [trivial |]. constructor; [trivial | constructor].
  - split.
    + exact ref_wf_env3.
    + split; [reflexivity |].
      intros receiver qcontext Hreceiver Hmut i Hi T Htype.
      simpl in Hreceiver. inversion Hreceiver; subst receiver.
      unfold ref_heap, ref_object, r_muttype, runtime_getObj in Hmut.
      simpl in Hmut. inversion Hmut; subst qcontext.
      destruct i as [| [| [| i]]]; [| | | simpl in Hi; lia].
      * simpl in Htype. inversion Htype; subst T. simpl.
        unfold wf_r_typable, r_type, ref_heap, ref_object, runtime_getObj.
        simpl. split.
        -- apply base_ref. apply class_refl. unfold ref_class. simpl. lia.
        -- trivial.
      * simpl. trivial.
      * simpl. trivial.
Qed.

Lemma ref_footprint_immutable :
  forall l,
    reachable_abs ref_CT ref_heap ref_receiver l ->
    exists C vals,
      runtime_getObj ref_heap l = Some (mkObj (mkruntime_type Imm_r C) vals).
Proof.
  intros l Hreach.
  eapply reachable_abs_from_imm_points_to_imm;
    [exact ref_frame_config_wf | | exact Hreach].
  reflexivity.
Qed.

Lemma ref_find_method :
  FindMethodWithName ref_CT ref_class ref_method ref_method_def.
Proof.
  eapply FOM_Here with
    (def := ref_class_def) (own_methods := [ref_method_def]).
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** The initial state satisfies the invariant: the cache is [null]. *)
Lemma ref_initial_inv :
  ref_inv ref_CT ref_receiver ref_heap ref_cache_field ref_view_class []
    ref_state.
Proof.
  assert (Hagree : heap_wm_type_agree ref_heap ref_weak).
  { unfold ref_heap, ref_weak.
    change (heap_wm_type_agree ([ref_owner] ++ [ref_object])
      (pico_core_alloc_weak
        (pico_core_alloc_weak empty_wm_state ref_owner 0) ref_object 0)).
    apply heap_wm_type_agree_alloc.
    change (heap_wm_type_agree ([] ++ [ref_owner])
      (pico_core_alloc_weak empty_wm_state ref_owner 0)).
    apply heap_wm_type_agree_alloc.
    split; [reflexivity |].
    intros loc object Hobject. destruct loc; discriminate. }
  have Habs := abs_agree_reachable_refl ref_CT ref_heap ref_receiver ref_heap_wf.
  split; [exact Hagree |].
  split.
  - split; [exact Habs |].
    apply (pico_hash_footprint_histories_stable ref_CT ref_receiver ref_heap
      ref_heap ref_weak ref_heap_wf Habs).
    apply pico_hash_allocated_footprint_histories.
    unfold ref_heap, ref_weak.
    change (pico_hash_allocated_histories
      (([] ++ [ref_owner]) ++ [ref_object])
      (pico_core_alloc_weak
        (pico_core_alloc_weak empty_wm_state ref_owner 0) ref_object 0)).
    apply pico_hash_allocated_histories_alloc; [reflexivity |].
    apply pico_hash_allocated_histories_alloc; [reflexivity |].
    exact pico_hash_allocated_histories_empty.
  - split; [exists ref_object; reflexivity |].
    intros v Hin. cbv in Hin. destruct Hin as [<- | []].
    left. reflexivity.
Qed.

Definition ref_caller : r_env := mkr_env [Iot ref_receiver; Null_a].

(** Any number of concurrent calls of the accessor preserve the invariant,
    and every call that returns normally returns a reference to an immutable
    view object. *)
Theorem ref_cache_example_sound :
  forall n cfg,
    @pico_pool_steps history_cache_memory_model ref_CT
      (ref_call_pool ref_method ref_caller 1 0 ref_state 0 n) cfg ->
    ref_inv ref_CT ref_receiver ref_heap ref_cache_field ref_view_class []
      (pool_state cfg) /\
    forall rG V,
      List.In (CoreDone OK rG V) (pool_threads cfg) ->
      exists l,
        runtime_getVal rG 1 = Some (Iot l) /\
        view_ok ref_CT ref_view_class [] (pool_state cfg) l.
Proof.
  intros n cfg Hsteps.
  eapply (@ref_cache_calls_sound history_cache_memory_model ref_CT
    (fun _ => False) ref_receiver ref_heap ref_cache_field ref_view_class []
    Imm_c [] SSkip ref_method ref_method_def ref_receiver_type ref_view_type
    ref_senv3 AbstractState (mkruntime_type Imm_r ref_class) [Null_a]
    ref_caller 1 0).
  - exact ref_footprint_immutable.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros mdef [].
  - apply DS_Skip.
  - apply ST_Skip. exact ref_wf_env3.
  - exact ref_frame_config_wf.
  - intros rGamma1 Heval. inversion Heval; subst.
    split; [reflexivity | simpl; unfold cache_result; lia].
  - reflexivity.
  - reflexivity.
  - exact ref_find_method.
  - reflexivity.
  - exact ref_initial_inv.
  - simpl. lia.
  - exact Hsteps.
Qed.
