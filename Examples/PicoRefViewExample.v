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

(** * A Cached View that Captures its Owner

    An immutable class whose only field is a lazily initialized reference to
    a view object, and a view class whose final field refers back to the
    owner, as an inner-class view does.  The accessor allocates
    [new View(this)] on a miss.  Any number of concurrent calls return
    references to view objects whose owner field is the receiver. *)

Definition rv_view_class : class_name := 2.
Definition rv_class : class_name := 1.
Definition rv_cache_field : var := 0.
Definition rv_method : method_name := 0.

Definition rv_view_type : qualified_type :=
  Build_qualified_type Imm (TRef rv_view_class).
Definition rv_receiver_type : qualified_type :=
  Build_qualified_type Imm (TRef rv_class).

Definition rv_cache_def : field_def :=
  {| ftype :=
       {| assignability := Assignable;
          mutability := Imm_f;
          f_base_type := TRef rv_view_class |};
     fname := rv_cache_field |}.

Definition rv_outer_def : field_def :=
  {| ftype :=
       {| assignability := Final;
          mutability := Imm_f;
          f_base_type := TRef rv_class |};
     fname := 0 |}.

Definition rv_method_body : stmt :=
  ref_cache_body rv_cache_field rv_view_class Imm_c [cache_receiver] SSkip
    rv_view_type.

Definition rv_method_def : method_def :=
  {| msignature :=
       {| mscope := AbstractState;
          mret := rv_view_type;
          mname := rv_method;
          mreceiver := rv_receiver_type;
          mparams := [] |};
     mbody := {| mbody_stmt := rv_method_body; mreturn := cache_result |} |}.

Definition rv_constructor : constructor_def :=
  {| csignature := {| cqualifier := Imm_c; cparams := [rv_view_type] |} |}.

Definition rv_class_def : class_def :=
  {| signature :=
       {| class_qualifier := Imm_c;
          cname := rv_class;
          super := Some pico_hash_witness_root |};
     body :=
       {| fields := [rv_cache_def];
          constructor := rv_constructor;
          methods := [rv_method_def] |} |}.

Definition rv_view_constructor : constructor_def :=
  {| csignature := {| cqualifier := Imm_c; cparams := [rv_receiver_type] |} |}.

Definition rv_view_class_def : class_def :=
  {| signature :=
       {| class_qualifier := Imm_c;
          cname := rv_view_class;
          super := Some pico_hash_witness_root |};
     body :=
       {| fields := [rv_outer_def];
          constructor := rv_view_constructor;
          methods := [] |} |}.

Definition rv_CT : class_table :=
  [pico_hash_witness_root_def; rv_class_def; rv_view_class_def].

Definition rv_receiver : Loc := 1.
Definition rv_owner : Obj :=
  mkObj (mkruntime_type Imm_r pico_hash_witness_root) [].
Definition rv_object : Obj :=
  mkObj (mkruntime_type Imm_r rv_class) [Null_a].
Definition rv_heap : heap := [rv_owner; rv_object].
Definition rv_weak : wm_state :=
  pico_core_alloc_weak (pico_core_alloc_weak empty_wm_state rv_owner 0)
    rv_object 0.
Definition rv_state : pico_core_state := mkPicoCoreState rv_heap rv_weak.

Definition rv_senv3 : s_env :=
  [rv_receiver_type; rv_view_type; rv_view_type].

Lemma rv_collect_fields :
  CollectFields rv_CT rv_class [rv_cache_def].
Proof.
  eapply CF_Inherit with
    (def := rv_class_def) (parent := pico_hash_witness_root)
    (parent_fields := []) (own_fields := [rv_cache_def]).
  - reflexivity.
  - reflexivity.
  - eapply CF_Object with (def := pico_hash_witness_root_def); reflexivity.
  - reflexivity.
Qed.

Lemma rv_cache_field_def :
  sf_def_rel rv_CT rv_class rv_cache_field rv_cache_def.
Proof.
  eapply FL_Found; [exact rv_collect_fields | reflexivity].
Qed.

Lemma rv_cache_assignable :
  sf_assignability_rel rv_CT rv_class rv_cache_field Assignable.
Proof.
  exists rv_cache_def. split; [exact rv_cache_field_def | reflexivity].
Qed.

Lemma rv_wf_env1 : wf_senv rv_CT [rv_receiver_type].
Proof.
  unfold wf_senv, wf_stypeuse, rv_receiver_type, rv_CT, rv_class_def,
    rv_class, bound, find_class, gget.
  simpl. split; [lia |].
  constructor.
  - unfold gget. simpl. split; [constructor; discriminate | lia].
  - constructor.
Qed.

Lemma rv_view_type_wf :
  wf_stypeuse rv_CT (sqtype rv_view_type) (sbase rv_view_type).
Proof.
  unfold wf_stypeuse, rv_view_type, rv_view_class, rv_CT, bound,
    find_class, gget. simpl.
  split; [constructor; discriminate | unfold pico_hash_witness_root; lia].
Qed.

Lemma rv_wf_env2 : wf_senv rv_CT [rv_receiver_type; rv_view_type].
Proof.
  destruct rv_wf_env1 as [Hlen Hall].
  split; [simpl; lia |].
  inversion Hall; subst.
  constructor; [assumption |].
  constructor; [exact rv_view_type_wf | constructor].
Qed.

Lemma rv_wf_env3 : wf_senv rv_CT rv_senv3.
Proof.
  destruct rv_wf_env2 as [Hlen Hall].
  split; [simpl; lia |].
  inversion Hall as [| ? ? H1 Hrest]; subst.
  inversion Hrest; subst.
  constructor; [assumption |].
  constructor; [assumption |].
  constructor; [exact rv_view_type_wf | constructor].
Qed.

(** The accessor is well typed. *)
Lemma rv_method_typing :
  stmt_typing rv_CT [rv_receiver_type] AbstractState rv_method_body
    rv_senv3.
Proof.
  assert (Hsub : qualified_type_subtype rv_CT rv_view_type rv_view_type).
  { apply qtype_refl; simpl; [| discriminate].
    unfold wf_qualified_base, rv_view_type, rv_view_class,
      pico_hash_witness_root, rv_CT. simpl. lia. }
  assert (Hread : stmt_typing rv_CT rv_senv3 AbstractState
    (SVarAss cache_tmp (EField cache_receiver rv_cache_field)) rv_senv3).
  { eapply ST_VarAss with (Te := rv_view_type)
      (Tthis := rv_receiver_type) (Tx := rv_view_type).
    - exact rv_wf_env3.
    - change (expr_has_type rv_CT rv_senv3 AbstractState
        (EField 0 0) (Build_qualified_type Imm (TRef rv_view_class))).
      eapply ET_Field_abstract_state with
        (T := rv_receiver_type) (C := rv_class) (fDef := rv_cache_def).
      + exact rv_wf_env3.
      + reflexivity.
      + reflexivity.
      + exact rv_cache_field_def.
      + left. reflexivity.
    - reflexivity.
    - unfold cache_tmp. discriminate.
    - reflexivity.
    - exact Hsub. }
  assert (Hnew : stmt_typing rv_CT rv_senv3 AbstractState
    (SNew cache_tmp Imm_c rv_view_class [cache_receiver]) rv_senv3).
  { eapply S_New with (Tx := rv_view_type) (argtypes := [rv_receiver_type])
      (Tthis := rv_receiver_type)
      (consig := csignature rv_view_constructor).
    - exact rv_wf_env3.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold cache_tmp. discriminate.
    - reflexivity.
    - constructor; [| constructor].
      apply qtype_refl; simpl; [| discriminate].
      cbv. lia.
    - exact Hsub. }
  assert (Hwrite : stmt_typing rv_CT rv_senv3 AbstractState
    (SFldWrite cache_receiver rv_cache_field cache_tmp) rv_senv3).
  { eapply ST_FldWrite_abstract_state with
      (Tx := rv_receiver_type) (Ty := rv_view_type)
      (Tthis := rv_receiver_type) (C := rv_class)
      (fieldT := rv_cache_def) (a := Assignable).
    - exact rv_wf_env3.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact rv_cache_field_def.
    - exact rv_cache_assignable.
    - exact Hsub.
    - reflexivity. }
  assert (Hfinal : stmt_typing rv_CT rv_senv3 AbstractState
    (SVarAss cache_result (EVar cache_tmp)) rv_senv3).
  { eapply ST_VarAss with (Te := rv_view_type)
      (Tthis := rv_receiver_type) (Tx := rv_view_type).
    - exact rv_wf_env3.
    - apply ET_Var; [exact rv_wf_env3 | reflexivity].
    - reflexivity.
    - unfold cache_result. discriminate.
    - reflexivity.
    - exact Hsub. }
  unfold rv_method_body, ref_cache_body.
  eapply ST_Seq with (sΓ' := [rv_receiver_type; rv_view_type]).
  - exact rv_wf_env1.
  - eapply ST_Local with (T := rv_view_type) (x := cache_tmp).
    + exact rv_wf_env1.
    + exact rv_view_type_wf.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - eapply ST_Seq with (sΓ' := rv_senv3).
    + exact rv_wf_env2.
    + eapply ST_Local with (T := rv_view_type) (x := cache_result).
      * exact rv_wf_env2.
      * exact rv_view_type_wf.
      * reflexivity.
      * reflexivity.
      * reflexivity.
    + eapply ST_Seq; [exact rv_wf_env3 | exact Hread |].
      eapply ST_Seq; [exact rv_wf_env3 | | exact Hfinal].
      eapply ST_IfZero with (Tx := rv_view_type).
      * exact rv_wf_env3.
      * reflexivity.
      * right. exists rv_view_class. reflexivity.
      * eapply ST_Seq with (sΓ' := rv_senv3).
        -- exact rv_wf_env3.
        -- apply ST_Skip. exact rv_wf_env3.
        -- eapply ST_Seq with (sΓ' := rv_senv3);
             [exact rv_wf_env3 | exact Hnew | exact Hwrite].
      * apply ST_Skip. exact rv_wf_env3.
Qed.

Lemma rv_method_wf : wf_method rv_CT rv_class rv_method_def.
Proof.
  unfold wf_method; simpl.
  split; [exact rv_view_type_wf |].
  exists rv_senv3, rv_view_type.
  split; [exact rv_method_typing |].
  split; [unfold cache_result; simpl; lia |].
  split; [unfold cache_result; reflexivity |].
  split.
  - apply qtype_refl; simpl; [| discriminate].
    unfold wf_qualified_base, rv_view_type, rv_view_class,
      pico_hash_witness_root, rv_CT. simpl. lia.
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

Lemma rv_view_collect_fields :
  CollectFields rv_CT rv_view_class [rv_outer_def].
Proof.
  eapply CF_Inherit with
    (def := rv_view_class_def) (parent := pico_hash_witness_root)
    (parent_fields := []) (own_fields := [rv_outer_def]).
  - reflexivity.
  - reflexivity.
  - eapply CF_Object with (def := pico_hash_witness_root_def); reflexivity.
  - reflexivity.
Qed.

Lemma rv_receiver_type_wf :
  wf_stypeuse rv_CT (sqtype rv_receiver_type) (sbase rv_receiver_type).
Proof.
  unfold wf_stypeuse, rv_receiver_type, rv_class, rv_CT, bound,
    find_class, gget. simpl.
  split; [constructor; discriminate | lia].
Qed.

Lemma rv_class_table_wf : wf_class_table rv_CT.
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
          (superC := pico_hash_witness_root) (thisC := rv_class);
          simpl; try reflexivity.
        -- unfold rv_class, pico_hash_witness_root. lia.
        -- split.
           ++ unfold wf_constructor. simpl.
              split; [reflexivity |].
              split.
              ** repeat constructor; try reflexivity;
                   first [exact rv_view_type_wf | discriminate | cbv; lia].
              ** exists [rv_cache_def].
                 repeat split; try reflexivity.
                 --- exact rv_collect_fields.
                 --- constructor; [| constructor].
                     apply qtype_refl; simpl; [| discriminate]. cbv. lia.
           ++ split.
              ** constructor; [exact rv_method_wf | constructor].
              ** split.
                 --- constructor; [simpl; tauto | constructor].
                 --- exists [rv_cache_def].
                     repeat split; try reflexivity.
                     ++++ exact rv_collect_fields.
                     ++++ right. reflexivity.
                     ++++ repeat constructor; simpl; trivial;
                            first [discriminate | cbv; lia].
      * constructor; [| constructor].
        eapply WFOtherDef with
          (superC := pico_hash_witness_root) (thisC := rv_view_class);
          simpl; try reflexivity.
        -- unfold rv_view_class, pico_hash_witness_root. lia.
        -- split.
           ++ unfold wf_constructor. simpl.
              split; [reflexivity |].
              split.
              ** repeat constructor; try reflexivity;
                   first [exact rv_receiver_type_wf | discriminate | cbv; lia].
              ** exists [rv_outer_def].
                 repeat split; try reflexivity.
                 --- exact rv_view_collect_fields.
                 --- constructor; [| constructor].
                     apply qtype_refl; simpl; [| discriminate]. cbv. lia.
           ++ split.
              ** constructor.
              ** split.
                 --- constructor.
                 --- exists [rv_outer_def].
                     repeat split; try reflexivity.
                     ++++ exact rv_view_collect_fields.
                     ++++ right. reflexivity.
                     ++++ repeat constructor; simpl; trivial;
                            first [discriminate | cbv; lia].
  - exists pico_hash_witness_root_def. split; reflexivity.
  - intros i def Hi Hfind.
    destruct i as [|[|[|i]]].
    + lia.
    + simpl in Hfind. inversion Hfind; subst. discriminate.
    + simpl in Hfind. inversion Hfind; subst. discriminate.
    + unfold find_class, gget in Hfind. simpl in Hfind.
      rewrite nth_error_nil in Hfind. discriminate.
  - intros i def Hfind.
    destruct i as [|[|[|i]]].
    + simpl in Hfind. inversion Hfind. reflexivity.
    + simpl in Hfind. inversion Hfind. reflexivity.
    + simpl in Hfind. inversion Hfind. reflexivity.
    + unfold find_class, gget in Hfind. simpl in Hfind.
      rewrite nth_error_nil in Hfind. discriminate.
Qed.

Lemma rv_heap_wf : wf_heap rv_CT rv_heap.
Proof.
  unfold wf_heap. intros loc Hloc.
  unfold rv_heap in Hloc. simpl in Hloc.
  destruct loc as [| [| loc]]; [| | lia].
  - unfold wf_obj, runtime_getObj, rv_heap, rv_owner. simpl.
    split.
    + unfold wf_rtypeuse, bound. simpl.
      split; [unfold pico_hash_witness_root, rv_CT; simpl; lia | trivial].
    + exists (@nil field_def). split.
      * eapply CF_Object with (def := pico_hash_witness_root_def);
          reflexivity.
      * split; [reflexivity | constructor].
  - unfold wf_obj, runtime_getObj, rv_heap, rv_object. simpl.
    split.
    + unfold wf_rtypeuse, bound. simpl.
      split; [unfold rv_class, rv_CT; simpl; lia | trivial].
    + exists [rv_cache_def].
      split; [exact rv_collect_fields |].
      split; [reflexivity |].
      repeat constructor.
Qed.

Definition rv_frame_env : r_env := mkr_env [Iot rv_receiver; Null_a; Null_a].

Lemma rv_frame_config_wf :
  wf_r_config rv_CT rv_senv3 rv_frame_env rv_heap.
Proof.
  unfold wf_r_config.
  split; [exact rv_class_table_wf |].
  split; [exact rv_heap_wf |].
  split.
  - unfold wf_renv, rv_heap, rv_frame_env, rv_receiver. simpl.
    split; [lia |]. split.
    + exists 1. split; reflexivity || lia.
    + constructor; [simpl; trivial |].
      constructor; [trivial |]. constructor; [trivial | constructor].
  - split.
    + exact rv_wf_env3.
    + split; [reflexivity |].
      intros receiver qcontext Hreceiver Hmut i Hi T Htype.
      simpl in Hreceiver. inversion Hreceiver; subst receiver.
      unfold rv_heap, rv_object, r_muttype, runtime_getObj in Hmut.
      simpl in Hmut. inversion Hmut; subst qcontext.
      destruct i as [| [| [| i]]]; [| | | simpl in Hi; lia].
      * simpl in Htype. inversion Htype; subst T. simpl.
        unfold wf_r_typable, r_type, rv_heap, rv_object, runtime_getObj.
        simpl. split.
        -- apply base_ref. apply class_refl. unfold rv_class. simpl. lia.
        -- trivial.
      * simpl. trivial.
      * simpl. trivial.
Qed.

Lemma rv_footprint_immutable :
  forall l,
    reachable_abs rv_CT rv_heap rv_receiver l ->
    exists C vals,
      runtime_getObj rv_heap l = Some (mkObj (mkruntime_type Imm_r C) vals).
Proof.
  intros l Hreach.
  eapply reachable_abs_from_imm_points_to_imm;
    [exact rv_frame_config_wf | | exact Hreach].
  reflexivity.
Qed.

Lemma rv_find_method :
  FindMethodWithName rv_CT rv_class rv_method rv_method_def.
Proof.
  eapply FOM_Here with
    (def := rv_class_def) (own_methods := [rv_method_def]).
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** The initial state satisfies the invariant: the cache is [null]. *)
Lemma rv_initial_inv :
  ref_inv rv_CT rv_receiver rv_heap rv_cache_field rv_view_class [Iot rv_receiver]
    rv_state.
Proof.
  assert (Hagree : heap_wm_type_agree rv_heap rv_weak).
  { unfold rv_heap, rv_weak.
    change (heap_wm_type_agree ([rv_owner] ++ [rv_object])
      (pico_core_alloc_weak
        (pico_core_alloc_weak empty_wm_state rv_owner 0) rv_object 0)).
    apply heap_wm_type_agree_alloc.
    change (heap_wm_type_agree ([] ++ [rv_owner])
      (pico_core_alloc_weak empty_wm_state rv_owner 0)).
    apply heap_wm_type_agree_alloc.
    split; [reflexivity |].
    intros loc object Hobject. destruct loc; discriminate. }
  have Habs := abs_agree_reachable_refl rv_CT rv_heap rv_receiver rv_heap_wf.
  split; [exact Hagree |].
  split.
  - split; [exact Habs |].
    apply (pico_hash_footprint_histories_stable rv_CT rv_receiver rv_heap
      rv_heap rv_weak rv_heap_wf Habs).
    apply pico_hash_allocated_footprint_histories.
    unfold rv_heap, rv_weak.
    change (pico_hash_allocated_histories
      (([] ++ [rv_owner]) ++ [rv_object])
      (pico_core_alloc_weak
        (pico_core_alloc_weak empty_wm_state rv_owner 0) rv_object 0)).
    apply pico_hash_allocated_histories_alloc; [reflexivity |].
    apply pico_hash_allocated_histories_alloc; [reflexivity |].
    exact pico_hash_allocated_histories_empty.
  - split; [exists rv_object; reflexivity |].
    intros v Hin. cbv in Hin. destruct Hin as [<- | []].
    left. reflexivity.
Qed.

Definition rv_caller : r_env := mkr_env [Iot rv_receiver; Null_a].

(** Any number of concurrent calls of the accessor preserve the invariant,
    and every call that returns normally returns a reference to an immutable
    view object whose owner field is the receiver. *)
Theorem rv_cache_example_sound :
  forall n cfg,
    @pico_pool_steps history_cache_memory_model rv_CT
      (ref_call_pool rv_method rv_caller 1 0 rv_state 0 n) cfg ->
    ref_inv rv_CT rv_receiver rv_heap rv_cache_field rv_view_class [Iot rv_receiver]
      (pool_state cfg) /\
    forall rG V,
      List.In (CoreDone OK rG V) (pool_threads cfg) ->
      exists l,
        runtime_getVal rG 1 = Some (Iot l) /\
        view_ok rv_CT rv_view_class [Iot rv_receiver] (pool_state cfg) l.
Proof.
  intros n cfg Hsteps.
  eapply (@ref_cache_calls_sound history_cache_memory_model rv_CT
    (fun _ => False) rv_receiver rv_heap rv_cache_field rv_view_class [Iot rv_receiver]
    Imm_c [cache_receiver] SSkip rv_method rv_method_def rv_receiver_type rv_view_type
    rv_senv3 AbstractState (mkruntime_type Imm_r rv_class) [Null_a]
    rv_caller 1 0).
  - exact rv_footprint_immutable.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros mdef [].
  - apply DS_Skip.
  - apply ST_Skip. exact rv_wf_env3.
  - exact rv_frame_config_wf.
  - intros rGamma1 Heval. inversion Heval; subst.
    split; [reflexivity | simpl; unfold cache_result; lia].
  - reflexivity.
  - reflexivity.
  - exact rv_find_method.
  - reflexivity.
  - exact rv_initial_inv.
  - simpl. lia.
  - exact Hsteps.
Qed.

Lemma rv_outer_abstract : abstract_field rv_CT rv_view_class 0.
Proof.
  assert (Hdef : sf_def_rel rv_CT rv_view_class 0 rv_outer_def)
    by (eapply FL_Found; [exact rv_view_collect_fields | reflexivity]).
  split.
  - right. exists rv_outer_def. split; [exact Hdef | reflexivity].
  - right. exists rv_outer_def. split; [exact Hdef | reflexivity].
Qed.

(** The returned view refers back to the receiver. *)
Corollary rv_cache_example_owner :
  forall n cfg rG V,
    @pico_pool_steps history_cache_memory_model rv_CT
      (ref_call_pool rv_method rv_caller 1 0 rv_state 0 n) cfg ->
    List.In (CoreDone OK rG V) (pool_threads cfg) ->
    exists l fs,
      runtime_getVal rG 1 = Some (Iot l) /\
      runtime_getObj (pcs_heap (pool_state cfg)) l =
        Some (mkObj (mkruntime_type Imm_r rv_view_class) fs) /\
      nth_error fs 0 = Some (Iot rv_receiver).
Proof.
  intros n cfg rG V Hsteps Hin.
  destruct (rv_cache_example_sound n cfg Hsteps) as [_ Hres].
  destruct (Hres rG V Hin) as (l & Hl & fs & Hobj & Hfields).
  exists l, fs. split; [exact Hl |]. split; [exact Hobj |].
  exact (proj1 (Hfields 0 rv_outer_abstract)).
Qed.
