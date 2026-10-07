From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat.

(** A concrete program for the readonly-state and transitive-state
    preservation theorems of the fragment without type parameters.

    class 0: @RDM class Object {}
    class 1: @RDM class Cell extends Object {
       @RDA @RO Object value;          // field 0
       @Assignable @RO Object cache;   // field 1
    }
    class 2: @RDM class Tool extends Object {
       @RS @RO Object peek(@RO Tool this, @RO Cell c)      // method 0
         { @RO Object r; r = c.value; c.cache = r; return r; }
       @TS @RO Object look(@RO Tool this, @RO Cell c)      // method 1
         { @RO Object r; r = c.value; return r; }
    }

    main (variable 0 is the receiver, a @Mut Object):
      @Mut Object o;   // var 1
      @Mut Cell c;     // var 2
      @Mut Tool t;     // var 3
      @RO Object x;    // var 4
      @RO Object n;    // var 5, never assigned, so it holds null
      o = new @Mut Object();
      c = new @Mut Cell(o, n);
      t = new @Mut Tool();
      x = t.peek(c);   // call A
      x = t.look(c);   // call B
*)

(* ------------------THE PROGRAM------------------*)

Definition ROObject : qualified_type := TClass RO 0 [].
Definition MutObject : qualified_type := TClass Mut 0 [].
Definition ROCell : qualified_type := TClass RO 1 [].
Definition MutCell : qualified_type := TClass Mut 1 [].
Definition ROTool : qualified_type := TClass RO 2 [].
Definition MutTool : qualified_type := TClass Mut 2 [].

Definition ObjectDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 0; ctparams := [];
                     super := None |};
     body := {| fields := []; methods := [] |} |}.

Definition value_field : field_def :=
  {| assignability := RDA; ftype := ROObject |}.

Definition cache_field : field_def :=
  {| assignability := Assignable; ftype := ROObject |}.

Definition CellDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 1; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := [value_field; cache_field]; methods := [] |} |}.

Definition tool_peek : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mret := ROObject;
          mname := 0;
          mreceiver := ROTool;
          mparams := [ROCell] |};
     mbody :=
       {| mbody_stmt :=
            SSeq (SLocal ROObject 2)
            (SSeq (SVarAss 2 (EField 1 0))
                  (SFldWrite 1 1 2));
          mreturn := 2 |} |}.

Definition tool_look : method_def :=
  {| msignature :=
       {| mscope := TransitiveState;
          mtparams := [];
          mret := ROObject;
          mname := 1;
          mreceiver := ROTool;
          mparams := [ROCell] |};
     mbody :=
       {| mbody_stmt := SSeq (SLocal ROObject 2) (SVarAss 2 (EField 1 0));
          mreturn := 2 |} |}.

Definition ToolDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 2; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := []; methods := [tool_peek; tool_look] |} |}.

Definition CT : class_table := [ObjectDef; CellDef; ToolDef].

Definition prefix : stmt :=
  SSeq (SLocal MutObject 1)
  (SSeq (SLocal MutCell 2)
  (SSeq (SLocal MutTool 3)
  (SSeq (SLocal ROObject 4)
  (SSeq (SLocal ROObject 5)
  (SSeq (SNew 1 Mut_c 0 [] [])
  (SSeq (SNew 2 Mut_c 1 [] [1; 5])
        (SNew 3 Mut_c 2 [] []))))))).

Definition callA : stmt := SCall 4 0 3 [] [2].
Definition callB : stmt := SCall 4 1 3 [] [2].

Definition main : stmt := SSeq prefix (SSeq callA callB).

Definition Δ0 : tv_env := mk_tv_env [] [] AbstractState.
Definition sΓ0 : s_env := [MutObject].
Definition sΓA : s_env :=
  [MutObject; MutObject; MutCell; MutTool; ROObject; ROObject].

(* ------------------SMALL TACTICS AND FACTS------------------*)

Ltac qs := first [apply q_refl; discriminate | apply q_rd | apply q_bot].

Lemma wf_plain : forall Δ top q0 C,
  C < 3 -> q0 <> Lost -> wf_stype CT Δ top (TClass q0 C []).
Proof.
  intros Δ top q0 C HC Hq.
  destruct C as [|[|[|C]]]; try lia;
    (eapply wfs_class;
       [reflexivity | right | reflexivity | constructor | constructor]);
    destruct q0; cbn; try qs; congruence.
Qed.

Lemma wf_plain_use : forall Δ q0 C,
  C < 3 -> q0 <> Lost -> wf_stypeuse CT Δ (TClass q0 C []).
Proof. intros. apply wf_plain; auto. Qed.

Ltac wfp := apply wf_plain_use; [cbn; lia | discriminate].

Ltac wfenv :=
  split; [cbn; lia |
          cbn; repeat (apply Forall_cons; [solve [wfp]|]); apply Forall_nil].

Ltac refl_sub :=
  apply qualified_type_subtype_refl_class; [cbn; lia | discriminate].

Ltac qual_sub := apply qtype_qual; [cbn; lia | qs | constructor].

Lemma collect_Object : CollectFields CT 0 [].
Proof. eapply CF_Object; reflexivity. Qed.

Lemma collect_Cell : CollectFields CT 1 [value_field; cache_field].
Proof.
  change (CollectFields CT 1
            (map (subst_field []) [] ++ Syntax.fields (body CellDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma collect_Tool : CollectFields CT 2 [].
Proof.
  change (CollectFields CT 2
            (map (subst_field []) [] ++ Syntax.fields (body ToolDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma value_is_rda : sf_assignability_rel CT 1 0 RDA.
Proof.
  exists value_field. split; [|reflexivity].
  eapply FL_Found; [apply collect_Cell | reflexivity].
Qed.

Lemma cache_is_assignable : sf_assignability_rel CT 1 1 Assignable.
Proof.
  exists cache_field. split; [|reflexivity].
  eapply FL_Found; [apply collect_Cell | reflexivity].
Qed.

Lemma no_method_in_Object : forall m D mdef,
  ~ FindMethodWithName CT 0 m D mdef.
Proof.
  intros m D mdef H. inversion H; subst.
  - cbn in Hfind. injection Hfind as <-. cbn in Hget_method. discriminate.
  - cbn in Hfind. injection Hfind as <-. cbn in Hsuper. discriminate.
Qed.

Lemma find_peek : FindMethodWithName CT 2 0 2 tool_peek.
Proof. eapply FOM_Here; reflexivity. Qed.

Lemma find_look : FindMethodWithName CT 2 1 2 tool_look.
Proof. eapply FOM_Here; reflexivity. Qed.

(* ------------------DELIVERABLE 1: THE CLASS TABLE------------------*)

Lemma wf_tool_peek : wf_method CT 2 tool_peek.
Proof.
  unfold wf_method. cbn.
  split; [left; exists RO; reflexivity|].
  split; [constructor|].
  split; [wfp|].
  split.
  { exists [ROTool; ROCell; ROObject], ROObject. split; [|split].
    - eapply ST_Seq; [wfenv | |].
      + eapply ST_Local; [wfenv | wfp | | reflexivity |]; reflexivity.
      + eapply ST_Seq; [wfenv | |].
        * (* r = c.value *)
          eapply ST_VarAss with (Tx := ROObject);
            [wfenv | | discriminate | reflexivity | ].
          -- eapply ET_Field with (x := 1) (T := ROCell) (qx := RO) (C := 1)
               (Ts := []) (fDef := value_field);
               [wfenv | reflexivity | reflexivity |].
             eapply FL_Found; [apply collect_Cell | reflexivity].
          -- cbn. refl_sub.
        * (* c.cache = r: through a readonly reference, in readonly-state
             mode, because the slot is declared assignable *)
          eapply ST_FldWrite with (Tx := ROCell) (Ty := ROObject) (qx := RO)
            (C := 1) (Ts := []) (fieldT := cache_field);
            [wfenv | reflexivity | reflexivity | reflexivity | | | reflexivity].
          -- eapply FL_Found; [apply collect_Cell | reflexivity].
          -- split; [cbn; refl_sub | left; cbn; intuition discriminate].
    - reflexivity.
    - refl_sub. }
  split.
  { intros def parent Ss D mdef_parent Vs Hfind Hsuper Hfm _.
    cbn in Hfind. injection Hfind as <-. cbn in Hsuper.
    injection Hsuper as <- <-.
    exfalso. eapply no_method_in_Object; eauto. }
  (* a readonly-state signature has no mutable root *)
  intros _. split.
  - constructor; [discriminate | constructor].
  - constructor; [|constructor]. constructor; [discriminate | constructor].
Qed.

Lemma wf_tool_look : wf_method CT 2 tool_look.
Proof.
  unfold wf_method. cbn.
  split; [left; exists RO; reflexivity|].
  split; [constructor|].
  split; [wfp|].
  split.
  { exists [ROTool; ROCell; ROObject], ROObject. split; [|split].
    - eapply ST_Seq; [wfenv | |].
      + eapply ST_Local; [wfenv | wfp | | reflexivity |]; reflexivity.
      + eapply ST_VarAss with (Tx := ROObject);
          [wfenv | | discriminate | reflexivity | ].
        * eapply ET_Field with (x := 1) (T := ROCell) (qx := RO) (C := 1)
            (Ts := []) (fDef := value_field);
            [wfenv | reflexivity | reflexivity |].
          eapply FL_Found; [apply collect_Cell | reflexivity].
        * cbn. refl_sub.
    - reflexivity.
    - refl_sub. }
  split.
  { intros def parent Ss D mdef_parent Vs Hfind Hsuper Hfm _.
    cbn in Hfind. injection Hfind as <-. cbn in Hsuper.
    injection Hsuper as <- <-.
    exfalso. eapply no_method_in_Object; eauto. }
  intros _. split.
  - constructor; [discriminate | constructor].
  - constructor; [|constructor]. constructor; [discriminate | constructor].
Qed.

Lemma ro_ct_wf : wf_class_table CT.
Proof.
  unfold wf_class_table. split; [|split; [|split]].
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + apply WFObjectDef; reflexivity.
    + eapply WFOtherDef with (superC := 0) (Ss := []);
        try reflexivity; cbn; try solve [constructor]; auto.
      * wfp.
      * constructor; [unfold wf_field; cbn; wfp|].
        constructor; [unfold wf_field; cbn; wfp | constructor].
    + eapply WFOtherDef with (superC := 0) (Ss := []);
        try reflexivity; cbn; try solve [constructor]; auto.
      * wfp.
      * constructor; [apply wf_tool_peek|].
        constructor; [apply wf_tool_look | constructor].
      * constructor; [cbn; intros [H | []]; discriminate|].
        constructor; [intros [] | constructor].
  - exists ObjectDef. split; reflexivity.
  - intros i def Hi Hfind.
    destruct i as [|[|[|i]]]; try lia; cbn in Hfind.
    + injection Hfind as <-. discriminate.
    + injection Hfind as <-. discriminate.
    + destruct i; discriminate.
  - intros i def Hfind.
    destruct i as [|[|[|i]]]; cbn in Hfind.
    + injection Hfind as <-. reflexivity.
    + injection Hfind as <-. reflexivity.
    + injection Hfind as <-. reflexivity.
    + destruct i; discriminate.
Qed.

Lemma ro_no_tparams : no_tparams CT.
Proof.
  intros C def Hfind.
  destruct C as [|[|[|C]]]; cbn in Hfind.
  - injection Hfind as <-. split; [reflexivity | constructor].
  - injection Hfind as <-. split; [reflexivity | constructor].
  - injection Hfind as <-. split; [reflexivity|].
    constructor; [reflexivity|]. constructor; [reflexivity | constructor].
  - destruct C; discriminate.
Qed.

Lemma ro_no_rdm_fields : no_rdm_fields CT.
Proof.
  intros C fs Hcf.
  destruct C as [|[|[|C]]].
  - pose proof (collect_fields_deterministic_rel _ _ _ _ Hcf collect_Object)
      as Heq.
    subst fs. constructor.
  - pose proof (collect_fields_deterministic_rel _ _ _ _ Hcf collect_Cell)
      as Heq.
    subst fs.
    constructor; [discriminate|]. constructor; [discriminate | constructor].
  - pose proof (collect_fields_deterministic_rel _ _ _ _ Hcf collect_Tool)
      as Heq.
    subst fs. constructor.
  - assert (Hnone : CollectFields CT (S (S (S C))) []).
    { apply CF_NotFound. destruct C; reflexivity. }
    pose proof (collect_fields_deterministic_rel _ _ _ _ Hcf Hnone) as Heq.
    subst fs. constructor.
Qed.

(* ------------------DELIVERABLE 2: TYPING AND THE PREFIX------------------*)

Ltac ty_local :=
  eapply ST_Local;
    [wfenv | wfp | reflexivity | reflexivity | reflexivity].

Ltac ty_seq := eapply ST_Seq; [wfenv | |].

Lemma prefix_typed : stmt_typing CT Δ0 sΓ0 AbstractState prefix sΓA.
Proof.
  unfold prefix, sΓA, sΓ0, Δ0.
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  ty_seq; [ty_local|]. ty_seq; [ty_local|].
  cbn.
  (* o = new @Mut Object() *)
  ty_seq.
  { eapply ST_New with (Tx := MutObject) (argtypes := []) (fds := []);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | wfp | constructor | constructor
      | apply collect_Object | constructor | ].
    cbn. refl_sub. }
  (* c = new @Mut Cell(o, n) *)
  ty_seq.
  { eapply ST_New with (Tx := MutCell) (argtypes := [MutObject; ROObject]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | wfp | constructor | constructor
      | apply collect_Cell | | ].
    - constructor; [|constructor; [|constructor]]; cbn; split.
      + qual_sub.
      + left. cbn. intuition discriminate.
      + refl_sub.
      + left. cbn. intuition discriminate.
    - cbn. refl_sub. }
  (* t = new @Mut Tool() *)
  eapply ST_New with (Tx := MutTool) (argtypes := []) (fds := []);
    [wfenv | reflexivity | reflexivity | reflexivity | discriminate
    | reflexivity | wfp | constructor | constructor
    | apply collect_Tool | constructor | ].
  cbn. refl_sub.
Qed.

(** Both calls are typed in main's abstract-state mode; the callee's mode is
    stronger than the caller's. *)
Lemma callA_typed : stmt_typing CT Δ0 sΓA AbstractState callA sΓA.
Proof.
  unfold callA, sΓA, Δ0.
  eapply ST_Call with (Tx := ROObject) (Ty := MutTool)
    (argtypes := [MutCell])
    (qy := Mut) (C := 2) (Ts := []) (D := 2) (Vs := [])
    (mdef := tool_peek);
    [wfenv | reflexivity | reflexivity | reflexivity | reflexivity
    | apply find_peek | apply si_refl | discriminate | constructor
    | constructor | reflexivity
    | constructor | | | | apply method_rs_as].
  - cbn. refl_sub.
  - left. cbn. split; [qual_sub|]. left. cbn. intuition discriminate.
  - constructor; [|constructor]. cbn. split; [qual_sub|].
    left. cbn. intuition discriminate.
Qed.

Lemma callB_typed : stmt_typing CT Δ0 sΓA AbstractState callB sΓA.
Proof.
  unfold callB, sΓA, Δ0.
  eapply ST_Call with (Tx := ROObject) (Ty := MutTool)
    (argtypes := [MutCell])
    (qy := Mut) (C := 2) (Ts := []) (D := 2) (Vs := [])
    (mdef := tool_look);
    [wfenv | reflexivity | reflexivity | reflexivity | reflexivity
    | apply find_look | apply si_refl | discriminate | constructor
    | constructor | reflexivity
    | constructor | | | | apply method_ts_as].
  - cbn. refl_sub.
  - left. cbn. split; [qual_sub|]. left. cbn. intuition discriminate.
  - constructor; [|constructor]. cbn. split; [qual_sub|].
    left. cbn. intuition discriminate.
Qed.

Lemma main_typed : stmt_typing CT Δ0 sΓ0 AbstractState main sΓA.
Proof.
  unfold main.
  eapply ST_Seq; [unfold sΓ0; wfenv | apply prefix_typed |].
  eapply ST_Seq; [unfold sΓA; wfenv | apply callA_typed | apply callB_typed].
Qed.

(** The states.  Location 0 is main's receiver, 1 is o, 2 is the Cell, 3 is
    the Tool. *)
Definition rΓ0 : r_env := mkr_env [Iot 0] [] [].
Definition h0 : heap := [mkObj (mkruntime_type Mut_r 0 []) []].

Definition rΓA : r_env :=
  mkr_env [Iot 0; Iot 1; Iot 2; Iot 3; Null_a; Null_a] [] [].

Definition hA : heap :=
  [ mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 1 []) [Iot 1; Null_a];
    mkObj (mkruntime_type Mut_r 2 []) [] ].

Ltac ev_local := eapply SBS_Seq; [apply SBS_Local; reflexivity|]; cbn.

Lemma prefix_eval : eval_stmt CT rΓ0 h0 prefix OK rΓA hA.
Proof.
  unfold prefix, rΓ0, h0.
  ev_local. ev_local. ev_local. ev_local. ev_local.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_New; reflexivity.
Qed.

Lemma initial_config : wf_r_config CT Δ0 sΓ0 rΓ0 h0.
Proof.
  unfold Δ0, sΓ0, rΓ0, h0.
  refine (conj ro_ct_wf (conj _ (conj _ (conj _ (conj _ (conj eq_refl _)))))).
  - intros ι Hι. simpl in Hι. assert (ι = 0) by lia. subst ι.
    unfold wf_obj. simpl. split.
    + unfold wf_rtypeuse. simpl.
      refine (conj eq_refl (conj (Forall_nil _) _)). constructor.
    + exists (@nil field_def).
      refine (conj collect_Object (conj eq_refl _)). constructor.
  - refine (conj _ (conj _ _)); simpl.
    + lia.
    + exists 0. split; auto.
    + constructor; [exact I | constructor].
  - split; simpl; [lia|]. constructor; [wfp | constructor].
  - exists 0, (mkObj (mkruntime_type Mut_r 0 []) []), 0. simpl.
    refine (conj eq_refl (conj eq_refl (conj eq_refl (conj (rsi_refl _ _ _ _)
             (conj (Forall_nil _) (conj (Forall_nil _) (conj _ _))))))); constructor.
  - intros ι qcontext Hthis Hmut i Hi sqt Hnth.
    simpl in Hi. assert (i = 0) by lia. subst i.
    simpl in Hthis. inversion Hthis; subst ι.
    cbn in Hmut. inversion Hmut; subst qcontext.
    cbn in Hnth. inversion Hnth; subst sqt.
    cbn. unfold wf_r_typable, loc_has_rtype. cbn.
    split; [unfold head_ok; auto|].
    exists (@nil rtype). split; constructor.
Qed.

(** The configuration just before call A is well formed. *)
Lemma config_A : wf_r_config CT Δ0 sΓA rΓA hA.
Proof.
  eapply preservation_pico;
    eauto using prefix_eval, initial_config, prefix_typed.
Qed.

(* ------------------DELIVERABLE 3: CALL A, READONLY STATE------------------*)

(** After call A, x holds o, and the Cell's cache slot holds o as well. *)
Definition rΓA' : r_env :=
  mkr_env [Iot 0; Iot 1; Iot 2; Iot 3; Iot 1; Null_a] [] [].

Definition hA' : heap :=
  [ mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 1 []) [Iot 1; Iot 1];
    mkObj (mkruntime_type Mut_r 2 []) [] ].

Lemma callA_eval : eval_stmt CT rΓA hA callA OK rΓA' hA'.
Proof.
  unfold callA, rΓA, hA.
  eapply SBS_Call with (mdef := tool_peek) (D := 2)
    (rΓ' := mkr_env [Iot 3; Iot 2] [] [])
    (rΓ'' := mkr_env [Iot 3; Iot 2; Iot 1] [] []).
  - reflexivity.
  - reflexivity.
  - apply find_peek.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold callee_env. do 4 eexists.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [apply rsi_refl | reflexivity].
  - cbn. eapply SBS_Seq; [apply SBS_Local; reflexivity|]. cbn.
    eapply SBS_Seq.
    + eapply SBS_Assign; [reflexivity|]. eapply EBS_Field; reflexivity.
    + cbn. eapply SBS_FldWrite with (a := Assignable);
        [reflexivity | reflexivity | reflexivity | apply cache_is_assignable
        | reflexivity | reflexivity | reflexivity].
  - reflexivity.
  - reflexivity.
Qed.

(** The readonly-state theorem applied to call A, for any outcome of the
    call: the Cell (location 2) keeps the value of its receiver-dependent
    assignable field [value] (field 0). *)
Theorem callA_preserves_value : forall rΓ' h',
  eval_stmt CT rΓA hA callA OK rΓ' h' ->
  exists vals',
    runtime_getObj h' 2 = Some (mkObj (mkruntime_type Mut_r 1 []) vals') /\
    nth_error [Iot 1; Null_a] 0 = nth_error vals' 0.
Proof.
  intros rΓ' h' Heval.
  eapply (readonly_state_preservation_flat CT Δ0 sΓA AbstractState rΓA hA
            4 0 3 [] [2] sΓA rΓ' h' 3 2 2 tool_peek
            ro_no_tparams ro_no_rdm_fields config_A callA_typed Heval).
  - reflexivity.
  - reflexivity.
  - apply find_peek.
  - left. reflexivity.
  - reflexivity.
  - right. apply value_is_rda.
Qed.

(** On the explicit final heap: the value slot still holds o. *)
Corollary callA_value_unchanged :
  exists vals',
    runtime_getObj hA' 2 = Some (mkObj (mkruntime_type Mut_r 1 []) vals') /\
    nth_error vals' 0 = Some (Iot 1).
Proof.
  destruct (callA_preserves_value _ _ callA_eval) as (vals' & Hobj & Hnth).
  exists vals'. split; [exact Hobj|]. symmetry. exact Hnth.
Qed.

(** The theorem is not vacuous and says nothing about the assignable slot:
    the same call changed the Cell's [cache] (field 1) from null to o. *)
Lemma callA_cache_changed :
  (exists o, runtime_getObj hA 2 = Some o /\
             nth_error (fields_map o) 1 = Some Null_a) /\
  (exists o', runtime_getObj hA' 2 = Some o' /\
              nth_error (fields_map o') 1 = Some (Iot 1)) /\
  hA <> hA'.
Proof.
  split; [|split].
  - eexists. split; reflexivity.
  - eexists. split; reflexivity.
  - discriminate.
Qed.

(** The cache slot is outside the readonly-state guarantee: it is neither
    final nor receiver-dependent assignable. *)
Lemma cache_not_protected :
  ~ (sf_assignability_rel CT 1 1 Final \/ sf_assignability_rel CT 1 1 RDA).
Proof.
  intros [H | H];
    pose proof (sf_assignability_deterministic_rel _ _ _ _ _ H
                  cache_is_assignable) as Heq;
    discriminate.
Qed.

(* ------------------DELIVERABLE 4: CALL B, TRANSITIVE STATE------------------*)

(** The configuration between the two calls is well formed. *)
Lemma config_B : wf_r_config CT Δ0 sΓA rΓA' hA'.
Proof.
  eapply preservation_pico;
    eauto using callA_eval, config_A, callA_typed.
Qed.

(** Call B assigns o to x again and leaves the heap as it was. *)
Lemma callB_eval : eval_stmt CT rΓA' hA' callB OK rΓA' hA'.
Proof.
  unfold callB, rΓA', hA'.
  eapply SBS_Call with (mdef := tool_look) (D := 2)
    (rΓ' := mkr_env [Iot 3; Iot 2] [] []).
  - reflexivity.
  - reflexivity.
  - apply find_look.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold callee_env. do 4 eexists.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [apply rsi_refl | reflexivity].
  - cbn. eapply SBS_Seq; [apply SBS_Local; reflexivity|]. cbn.
    eapply SBS_Assign; [reflexivity|]. eapply EBS_Field; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** The whole program runs from the initial state to the final one. *)
Lemma main_eval : eval_stmt CT rΓ0 h0 main OK rΓA' hA'.
Proof.
  unfold main.
  eapply SBS_Seq; [apply prefix_eval|].
  eapply SBS_Seq; [apply callA_eval | apply callB_eval].
Qed.

(** The transitive-state theorem applied to call B, for any outcome of the
    call: every field of every object of the entry heap keeps its value. *)
Theorem callB_preserves_everything : forall rΓ' h',
  eval_stmt CT rΓA' hA' callB OK rΓ' h' ->
  forall l qr C Rs vals f,
    runtime_getObj hA' l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
    exists vals',
      runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
      nth_error vals f = nth_error vals' f.
Proof.
  intros rΓ' h' Heval.
  eapply (transitive_state_preservation_flat CT Δ0 sΓA AbstractState rΓA' hA'
            4 1 3 [] [2] sΓA rΓ' h' 3 2 2 tool_look
            ro_no_tparams ro_no_rdm_fields config_B callB_typed Heval).
  - reflexivity.
  - reflexivity.
  - apply find_look.
  - reflexivity.
Qed.

(** For the Cell: both slots, including the assignable cache, are unchanged. *)
Corollary callB_cell_unchanged : forall rΓ' h',
  eval_stmt CT rΓA' hA' callB OK rΓ' h' ->
  exists vals',
    runtime_getObj h' 2 = Some (mkObj (mkruntime_type Mut_r 1 []) vals') /\
    nth_error vals' 0 = Some (Iot 1) /\
    nth_error vals' 1 = Some (Iot 1).
Proof.
  intros rΓ' h' Heval.
  destruct (callB_preserves_everything _ _ Heval 2 Mut_r 1 [] [Iot 1; Iot 1] 0
              eq_refl) as (vals0 & Hobj0 & Hnth0).
  destruct (callB_preserves_everything _ _ Heval 2 Mut_r 1 [] [Iot 1; Iot 1] 1
              eq_refl) as (vals1 & Hobj1 & Hnth1).
  rewrite Hobj0 in Hobj1. injection Hobj1 as Heq. subst vals1.
  exists vals0. split; [exact Hobj0|].
  split; symmetry; assumption.
Qed.

Print Assumptions callA_preserves_value.
Print Assumptions callB_preserves_everything.
