From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric
  GhostLabels GhostTyping GhostForget GhostInvariant GhostOverride GhostCall
  GhostEntry ArgViews ArgTyping ArgFit ArgInvariant
  ArgCases ArgClean ArgOverride ArgCall ArgMain ArgEntry ArgRsf.

(** A worked example for the readonly-state theorem whose only condition on
    the class table is on type-parameter bounds.  The protected method below
    writes a mutable qualifier inside a type argument, which the earlier
    theorem for generic programs ruled out.

    class 0: @RDM class Object {}
    class 1: @RDM class Cell extends Object {
       @RDA @RO Object value;             // field 0
    }
    class 2: @RDM class Box<E extends @RO Object> extends Object {
       @RDA E item;                       // field 0
    }
    class 3: @RDM class Tool extends Object {
       // method 0, readonly-state
       @RS @RO Object work(@RO Tool this, @RO Object y) {
           @RO Object n;             // var 2, never assigned, so it holds null
           @Mut Cell k;              // var 3
           @Mut Box<@Mut Cell> b;    // var 4
           @Mut Cell k2;             // var 5
           k = new @Mut Cell(n);
           b = new @Mut Box<@Mut Cell>(k);   // mutable inside a type argument
           k2 = b.item;                      // read back as a mutable Cell
           k2.value = y;                     // write through that reference
           return y;
       }
    }

    main (variable 0 is the receiver, a @Mut Object; abstract-state mode):
      @Mut Object o;            // var 1
      @Mut Cell c;              // var 2
      @Mut Box<@Mut Cell> b;    // var 3
      @Mut Tool t;              // var 4
      @RO Object x;             // var 5
      o = new @Mut Object();
      c = new @Mut Cell(o);
      b = new @Mut Box<@Mut Cell>(c);
      t = new @Mut Tool();
      x = t.work(c);                      // the call

    One change from the sketch: the fresh Cell is created holding null, not
    y, so that the later write of y into it is visible in the heap. *)

(* ------------------THE PROGRAM------------------*)

Definition ROObject : qualified_type := TClass RO 0 [].
Definition MutObject : qualified_type := TClass Mut 0 [].
Definition ROCell : qualified_type := TClass RO 1 [].
Definition MutCell : qualified_type := TClass Mut 1 [].
Definition ROTool : qualified_type := TClass RO 3 [].
Definition MutTool : qualified_type := TClass Mut 3 [].
Definition tE : qualified_type := TVar TVSub ClassVar 0.
Definition MutBoxMutCell : qualified_type := TClass Mut 2 [MutCell].

Definition ObjectDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 0; ctparams := [];
                     super := None |};
     body := {| fields := []; methods := [] |} |}.

Definition value_field : field_def :=
  {| assignability := RDA; ftype := ROObject |}.

Definition CellDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 1; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := [value_field]; methods := [] |} |}.

Definition item_field : field_def :=
  {| assignability := RDA; ftype := tE |}.

Definition BoxDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 2;
                     ctparams := [ROObject];
                     super := Some (0, []) |};
     body := {| fields := [item_field]; methods := [] |} |}.

Definition work : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mret := ROObject;
          mname := 0;
          mreceiver := ROTool;
          mparams := [ROObject] |};
     mbody :=
       {| mbody_stmt :=
            SSeq (SLocal ROObject 2)
            (SSeq (SLocal MutCell 3)
            (SSeq (SLocal MutBoxMutCell 4)
            (SSeq (SLocal MutCell 5)
            (SSeq (SNew 3 Mut_c 1 [] [2])
            (SSeq (SNew 4 Mut_c 2 [MutCell] [3])
            (SSeq (SVarAss 5 (EField 4 0))
                  (SFldWrite 5 0 1)))))));
          mreturn := 1 |} |}.

Definition ToolDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 3; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := []; methods := [work] |} |}.

Definition CT : class_table := [ObjectDef; CellDef; BoxDef; ToolDef].

Definition prefix : stmt :=
  SSeq (SLocal MutObject 1)
  (SSeq (SLocal MutCell 2)
  (SSeq (SLocal MutBoxMutCell 3)
  (SSeq (SLocal MutTool 4)
  (SSeq (SLocal ROObject 5)
  (SSeq (SNew 1 Mut_c 0 [] [])
  (SSeq (SNew 2 Mut_c 1 [] [1])
  (SSeq (SNew 3 Mut_c 2 [MutCell] [2])
        (SNew 4 Mut_c 3 [] [])))))))).

Definition callW : stmt := SCall 5 0 4 [] [2].

Definition main : stmt := SSeq prefix callW.

Definition Δ0 : tv_env := mk_tv_env [] [] AbstractState.
Definition sΓ0 : s_env := [MutObject].
Definition sΓA : s_env :=
  [MutObject; MutObject; MutCell; MutBoxMutCell; MutTool; ROObject].

(** The bound environment of work: no type parameter is in scope. *)
Definition ΔW : tv_env := mk_tv_env [] [] ReadonlyState.

(* ------------------SMALL TACTICS AND FACTS------------------*)

Ltac qs := (apply q_refl; discriminate) || apply q_rd || apply q_bot.

(** Classes 0, 1, 3 take no type arguments and are declared @RDM: any written
    qualifier is fine. *)
Lemma wf_plain : forall Δ top q0 C,
  C = 0 \/ C = 1 \/ C = 3 -> q0 <> Lost -> wf_stype CT Δ top (TClass q0 C []).
Proof.
  intros Δ top q0 C HC Hq.
  destruct HC as [-> | [-> | ->]];
    (eapply wfs_class;
       [reflexivity | right | reflexivity | constructor | constructor]);
    destruct q0; cbn; try qs; congruence.
Qed.

Lemma wf_use : forall Δ q0 C,
  C = 0 \/ C = 1 \/ C = 3 -> q0 <> Lost -> wf_stypeuse CT Δ (TClass q0 C []).
Proof. intros. apply wf_plain; auto. Qed.

Ltac wfp := apply wf_use; [auto | discriminate].

(** Any Cell is a readonly Object. *)
Lemma sub_Cell_ROObject : forall Δ q0,
  qualified_type_subtype CT Δ (TClass q0 1 []) ROObject.
Proof.
  intros Δ q0. eapply qtype_trans.
  - apply qtype_hier with (D := 0) (Vs := []).
    eapply si_step; [reflexivity|]. cbn. apply si_refl.
  - apply qtype_qual; [cbn; lia | apply q_rd | constructor].
Qed.

(** A Box type is well formed when its argument is, and the argument is
    below the declared bound @RO Object. *)
Lemma wf_Box : forall Δ top q0 A,
  q0 <> Lost ->
  wf_stype CT Δ false A ->
  bound_sub CT Δ A ROObject ->
  wf_stype CT Δ top (TClass q0 2 [A]).
Proof.
  intros Δ top q0 A Hq HA Hsub.
  eapply wfs_class; [reflexivity | right | reflexivity | |].
  - destruct q0; cbn; try qs; congruence.
  - constructor; [exact HA | constructor].
  - constructor; [|constructor].
    destruct q0; cbn; exact Hsub.
Qed.

Lemma wf_MutBoxMutCell : forall Δ, wf_stypeuse CT Δ MutBoxMutCell.
Proof.
  intros. apply wf_Box; [discriminate | | intros m; apply sub_Cell_ROObject].
  apply wf_plain; [auto | discriminate].
Qed.

Lemma wf_MutObject : forall Δ, wf_stypeuse CT Δ MutObject.
Proof. intros. wfp. Qed.
Lemma wf_ROObject : forall Δ, wf_stypeuse CT Δ ROObject.
Proof. intros. wfp. Qed.
Lemma wf_MutCell : forall Δ, wf_stypeuse CT Δ MutCell.
Proof. intros. wfp. Qed.
Lemma wf_ROCell : forall Δ, wf_stypeuse CT Δ ROCell.
Proof. intros. wfp. Qed.
Lemma wf_MutTool : forall Δ, wf_stypeuse CT Δ MutTool.
Proof. intros. wfp. Qed.
Lemma wf_ROTool : forall Δ, wf_stypeuse CT Δ ROTool.
Proof. intros. wfp. Qed.

Create HintDb exl.
Local Hint Resolve wf_MutObject wf_ROObject wf_MutCell wf_ROCell wf_MutTool
  wf_ROTool wf_MutBoxMutCell : exl.

Ltac wfenv :=
  split; [cbn; lia |
          cbn; repeat (apply Forall_cons; [solve [auto with exl]|]);
          apply Forall_nil].

Ltac refl_sub :=
  apply qualified_type_subtype_refl_class; [cbn; lia | discriminate].

Ltac qual_sub :=
  apply qtype_qual; [cbn; lia | qs | apply Forall2_targ_sub_refl].

Lemma collect_Object : CollectFields CT 0 [].
Proof. eapply CF_Object; reflexivity. Qed.

Lemma collect_Cell : CollectFields CT 1 [value_field].
Proof.
  change (CollectFields CT 1
            (map (subst_field []) [] ++ Syntax.fields (body CellDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma collect_Box : CollectFields CT 2 [item_field].
Proof.
  change (CollectFields CT 2
            (map (subst_field []) [] ++ Syntax.fields (body BoxDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma collect_Tool : CollectFields CT 3 [].
Proof.
  change (CollectFields CT 3
            (map (subst_field []) [] ++ Syntax.fields (body ToolDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma value_is_rda : sf_assignability_rel CT 1 0 RDA.
Proof.
  exists value_field. split; [|reflexivity].
  eapply FL_Found; [apply collect_Cell | reflexivity].
Qed.

Lemma item_is_rda : sf_assignability_rel CT 2 0 RDA.
Proof.
  exists item_field. split; [|reflexivity].
  eapply FL_Found; [apply collect_Box | reflexivity].
Qed.

Lemma no_method_in_Object : forall m D mdef,
  ~ FindMethodWithName CT 0 m D mdef.
Proof.
  intros m D mdef H. inversion H; subst.
  - cbn in Hfind. injection Hfind as <-. cbn in Hget_method. discriminate.
  - cbn in Hfind. injection Hfind as <-. cbn in Hsuper. discriminate.
Qed.

Lemma find_work : FindMethodWithName CT 3 0 3 work.
Proof. eapply FOM_Here; reflexivity. Qed.

Ltac ty_local :=
  eapply ST_Local;
    [wfenv | solve [auto with exl] | reflexivity | reflexivity | reflexivity].

Ltac ty_seq := eapply ST_Seq; [wfenv | |].

(* ------------------DELIVERABLE 1: THE CLASS TABLE------------------*)

(** The body of work, checked in readonly-state mode.  Each of the three
    steps of interest is accepted: the allocation of a Box whose type
    argument is a mutable Cell, the read of its item at the type mutable
    Cell, and the write through the reference so obtained. *)
Lemma work_body_typed :
  stmt_typing CT ΔW [ROTool; ROObject] ReadonlyState
    (mbody_stmt (mbody work))
    [ROTool; ROObject; ROObject; MutCell; MutBoxMutCell; MutCell].
Proof.
  cbn. unfold ΔW.
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  ty_seq; [ty_local|].
  cbn.
  (* k = new @Mut Cell(n) *)
  ty_seq.
  { eapply ST_New with (Tx := MutCell) (argtypes := [ROObject]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutCell | constructor | constructor
      | apply collect_Cell | | ].
    - constructor; [|constructor]. cbn. split; [refl_sub|].
      left. cbn. intuition discriminate.
    - cbn. refl_sub. }
  (* b = new @Mut Box<@Mut Cell>(k) *)
  ty_seq.
  { eapply ST_New with (Tx := MutBoxMutCell) (argtypes := [MutCell]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutBoxMutCell | | | apply collect_Box | | ].
    - constructor; [|constructor]. cbn. intuition discriminate.
    - constructor; [|constructor]. cbn. split; [intuition discriminate|].
      intros m. apply sub_Cell_ROObject.
    - constructor; [|constructor]; cbn.
      split; [refl_sub | left; cbn; intuition discriminate].
    - cbn. refl_sub. }
  (* k2 = b.item: read through @Mut Box<@Mut Cell>, the field has type
     @Mut Cell even in readonly-state mode *)
  ty_seq.
  { eapply ST_VarAss with (Tx := MutCell);
      [wfenv | | discriminate | reflexivity | ].
    - eapply ET_Field with (x := 4) (T := MutBoxMutCell) (qx := Mut) (C := 2)
        (Ts := [MutCell]) (fDef := item_field);
        [wfenv | reflexivity | reflexivity |].
      eapply FL_Found; [apply collect_Box | reflexivity].
    - cbn. refl_sub. }
  (* k2.value = y: the slot is receiver-dependent assignable and the
     reference is mutable *)
  eapply ST_FldWrite with (Tx := MutCell) (Ty := ROObject) (qx := Mut)
    (C := 1) (Ts := []) (fieldT := value_field);
    [wfenv | reflexivity | reflexivity | reflexivity | | | reflexivity].
  - eapply FL_Found; [apply collect_Cell | reflexivity].
  - split; [cbn; refl_sub | left; cbn; intuition discriminate].
Qed.

Lemma wf_work : wf_method CT 3 work.
Proof.
  unfold wf_method.
  change (method_tv_env CT 3 (msignature work)) with ΔW.
  cbn.
  split; [left; exists RO; reflexivity|].
  split; [constructor|].
  split; [apply wf_ROObject|].
  split.
  { exists [ROTool; ROObject; ROObject; MutCell; MutBoxMutCell; MutCell],
      ROObject.
    split; [|split].
    - apply work_body_typed.
    - reflexivity.
    - refl_sub. }
  split.
  { intros def parent Ss D mdef_parent Vs Hfind Hsuper Hfm _.
    cbn in Hfind. injection Hfind as <-. cbn in Hsuper.
    injection Hsuper as <- <-.
    exfalso. eapply no_method_in_Object; eauto. }
  intros _. split.
  - constructor; [discriminate | constructor].
  - constructor; [|constructor].
    constructor; [discriminate | constructor].
Qed.

Theorem labels_ct_wf : wf_class_table CT.
Proof.
  unfold wf_class_table. split; [|split; [|split]].
  - constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + apply WFObjectDef; reflexivity.
    + eapply WFOtherDef with (superC := 0) (Ss := []);
        try reflexivity; cbn; try solve [constructor]; auto.
      * wfp.
      * constructor; [unfold wf_field; cbn; wfp | constructor].
    + eapply WFOtherDef with (superC := 0) (Ss := []);
        try reflexivity; cbn; try solve [constructor]; auto.
      * constructor; [|constructor]. split; [exact I | wfp].
      * wfp.
      * constructor; [|constructor]; unfold wf_field; cbn.
        eapply wfs_var; [reflexivity|]. right. discriminate.
    + eapply WFOtherDef with (superC := 0) (Ss := []);
        try reflexivity; cbn; try solve [constructor]; auto.
      * wfp.
      * constructor; [apply wf_work | constructor].
      * constructor; [intros [] | constructor].
  - exists ObjectDef. split; reflexivity.
  - intros i def Hi Hfind.
    destruct i as [|[|[|[|i]]]]; try lia; cbn in Hfind.
    + injection Hfind as <-. discriminate.
    + injection Hfind as <-. discriminate.
    + injection Hfind as <-. discriminate.
    + destruct i; discriminate.
  - intros i def Hfind.
    destruct i as [|[|[|[|i]]]]; cbn in Hfind.
    + injection Hfind as <-. reflexivity.
    + injection Hfind as <-. reflexivity.
    + injection Hfind as <-. reflexivity.
    + injection Hfind as <-. reflexivity.
    + destruct i; discriminate.
Qed.

(* ------------------DELIVERABLE 2: THE NEW CONDITION HOLDS------------------*)

(** The only readonly-state method is work, and no type parameter is in
    scope there, so the condition on bounds has nothing to check. *)
(** Every class type-parameter bound of this table is a class type with no
    mutable position. *)
Lemma ct_bounds_nm : class_bounds_nm CT.
Proof.
  intros C def n B Hfind Hn.
  do 4 (destruct C as [|C]; cbn in Hfind;
        [ injection Hfind as <-; cbn in Hn;
          destruct n as [|[|n]]; cbn in Hn; try discriminate;
          try solve [injection Hn as <-;
                     split; [exact I | apply nm_class; [discriminate | constructor]]]
        | ]).
  destruct C; discriminate.
Qed.

Theorem labels_ct_clean_bounds : clean_bounds_ct CT.
Proof.
  intros C def md Hfind Hin _.
  destruct C as [|[|[|[|C]]]]; cbn in Hfind.
  - injection Hfind as <-. destruct Hin.
  - injection Hfind as <-. destruct Hin.
  - injection Hfind as <-. destruct Hin.
  - injection Hfind as <-. cbn in Hin. destruct Hin as [<- | []].
    intros o n B Hb. destruct o; destruct n; discriminate.
  - destruct C; discriminate.
Qed.

(* ------------------DELIVERABLE 3: THE OLD CONDITION FAILS------------------*)

(** The earlier condition asks that the body of every readonly-state method
    write no mutable qualifier inside a type argument.  The body of work
    allocates a Box of mutable Cells. *)
Theorem labels_ct_not_clean : ~ clean_ct CT.
Proof.
  intros Hcc.
  destruct (cc_methods CT Hcc 3 ToolDef work eq_refl (or_introl eq_refl)
              (or_introl eq_refl)) as (_ & _ & Hcs).
  cbn [mbody_stmt mbody work clean_stmt] in Hcs.
  destruct Hcs as (_ & _ & _ & _ & _ & Hnew & _).
  inversion Hnew as [|T l Harg _]; subst.
  apply clean_arg_class in Harg. destruct Harg as [[Hmut _] _].
  apply Hmut. reflexivity.
Qed.

(** The same failure, seen at the declaration of the local of type
    Box of mutable Cells. *)
Lemma work_body_not_clean : ~ clean_stmt (mbody_stmt (mbody work)).
Proof.
  cbn [mbody_stmt mbody work clean_stmt].
  intros (_ & _ & Hloc & _).
  unfold MutBoxMutCell, clean_top in Hloc.
  inversion Hloc as [|T l Harg _]; subst.
  apply clean_arg_class in Harg. destruct Harg as [[Hmut _] _].
  apply Hmut. reflexivity.
Qed.

(* ------------------DELIVERABLE 4: CONFIGURATION, TYPING, RUN------------------*)

Lemma prefix_typed : stmt_typing CT Δ0 sΓ0 AbstractState prefix sΓA.
Proof.
  unfold prefix, sΓA, sΓ0, Δ0.
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  ty_seq; [ty_local|]. ty_seq; [ty_local|].
  cbn.
  ty_seq.
  { eapply ST_New with (Tx := MutObject) (argtypes := []) (fds := []);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutObject | constructor | constructor
      | apply collect_Object | constructor | ].
    cbn. refl_sub. }
  ty_seq.
  { eapply ST_New with (Tx := MutCell) (argtypes := [MutObject]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutCell | constructor | constructor
      | apply collect_Cell | | ].
    - constructor; [|constructor]. cbn. split; [qual_sub|].
      left. cbn. intuition discriminate.
    - cbn. refl_sub. }
  ty_seq.
  { eapply ST_New with (Tx := MutBoxMutCell) (argtypes := [MutCell]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutBoxMutCell | | | apply collect_Box | | ].
    - constructor; [|constructor]. cbn. intuition discriminate.
    - constructor; [|constructor]. cbn. split; [intuition discriminate|].
      intros m. apply sub_Cell_ROObject.
    - constructor; [|constructor]; cbn.
      split; [refl_sub | left; cbn; intuition discriminate].
    - cbn. refl_sub. }
  eapply ST_New with (Tx := MutTool) (argtypes := []) (fds := []);
    [wfenv | reflexivity | reflexivity | reflexivity | discriminate
    | reflexivity | apply wf_MutTool | constructor | constructor
    | apply collect_Tool | constructor | ].
  cbn. refl_sub.
Qed.

(** The call, made from abstract-state code.  The Cell c is passed where a
    readonly Object is expected. *)
Lemma callW_typed : stmt_typing CT Δ0 sΓA AbstractState callW sΓA.
Proof.
  unfold callW, sΓA, Δ0.
  eapply ST_Call with (Tx := ROObject) (Ty := MutTool)
    (argtypes := [MutCell])
    (qy := Mut) (C := 3) (Ts := []) (D := 3) (Vs := [])
    (mdef := work);
    [wfenv | reflexivity | reflexivity | reflexivity | reflexivity
    | apply find_work | apply si_refl | discriminate | | | reflexivity
    | | | | | apply method_rs_as].
  - constructor.
  - constructor.
  - constructor.
  - cbn. refl_sub.
  - left. cbn. split; [qual_sub | left; cbn; intuition discriminate].
  - constructor; [|constructor]; cbn.
    split; [apply sub_Cell_ROObject | left; cbn; intuition discriminate].
Qed.

Lemma main_typed : stmt_typing CT Δ0 sΓ0 AbstractState main sΓA.
Proof.
  unfold main.
  eapply ST_Seq; [unfold sΓ0; wfenv | apply prefix_typed | apply callW_typed].
Qed.

(** The states.  Location 0 is main's receiver, 1 is o, 2 is the Cell c, 3 is
    the Box b, 4 is the Tool. *)
Definition rΓ0 : r_env := mkr_env [Iot 0] [] [].
Definition h0 : heap := [mkObj (mkruntime_type Mut_r 0 []) []].

Definition rΓA : r_env :=
  mkr_env [Iot 0; Iot 1; Iot 2; Iot 3; Iot 4; Null_a] [] [].

Definition hA : heap :=
  [ mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 1 []) [Iot 1];
    mkObj (mkruntime_type Mut_r 2 [RClass Mut 1 []]) [Iot 2];
    mkObj (mkruntime_type Mut_r 3 []) [] ].

Ltac ev_local := eapply SBS_Seq; [apply SBS_Local; reflexivity|]; cbn.

Lemma prefix_eval : eval_stmt CT rΓ0 h0 prefix OK rΓA hA.
Proof.
  unfold prefix, rΓ0, h0.
  ev_local. ev_local. ev_local. ev_local. ev_local.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_New; reflexivity.
Qed.

Lemma initial_config : wf_r_config CT Δ0 sΓ0 rΓ0 h0.
Proof.
  unfold Δ0, sΓ0, rΓ0, h0.
  refine (conj labels_ct_wf
            (conj _ (conj _ (conj _ (conj _ (conj eq_refl _)))))).
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
  - split; simpl; [lia|]. constructor; [apply wf_MutObject | constructor].
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

(** The configuration just before the call is well formed. *)
Theorem config_A : wf_r_config CT Δ0 sΓA rΓA hA.
Proof.
  eapply preservation_pico;
    eauto using prefix_eval, initial_config, prefix_typed.
Qed.

(** The initial configuration satisfies its bounds in the protected reading:
    the only object is of a class without type parameters, and main has no
    type parameter in scope. *)
Lemma initial_rsf : RSF CT Δ0 rΓ0 h0.
Proof.
  split.
  - apply rsfit_heap_intro. intros l o def Ho Hfc L o' n B Hb.
    destruct (tv_bound_class_env _ _ _ _ Hb) as [_ Hn].
    destruct l as [|l]; cbn in Ho; [injection Ho as <- | destruct l; discriminate].
    cbn in Hfc. injection Hfc as <-. cbn in Hn. destruct n; discriminate.
  - intros ι o _ _ L o' n B Hb. destruct o'; destruct n; discriminate.
Qed.

(** So does the configuration just before the call. *)
Theorem rsf_A : RSF CT Δ0 rΓA hA.
Proof.
  exact (rsf_preservation CT Δ0 sΓ0 AbstractState prefix sΓA rΓ0 h0 rΓA hA
           initial_config prefix_typed prefix_eval initial_rsf).
Qed.

(** The same in the payload form, which the theorem asks for.  The initial
    state has no type variable in scope and its only object is of a class
    without type parameters; every well-typed execution keeps the
    condition. *)
Lemma initial_rsfp : RSFp CT Δ0 rΓ0 h0.
Proof.
  apply RSFp_start; [exact initial_rsf | reflexivity | reflexivity |].
  intros l o def Ho Hfc.
  destruct l as [|l]; cbn in Ho; [injection Ho as <- | destruct l; discriminate].
  cbn in Hfc. injection Hfc as <-. reflexivity.
Qed.

Theorem rsfp_A : RSFp CT Δ0 rΓA hA.
Proof.
  exact (rsfp_preservation CT Δ0 sΓ0 AbstractState prefix sΓA rΓ0 h0 rΓA hA
           initial_config prefix_typed prefix_eval initial_rsfp).
Qed.

(** The activation of work: receiver the Tool, argument the Cell c. *)
Definition rΓwork : r_env := mkr_env [Iot 4; Iot 2] [] [].

(** The fresh objects: a Cell at location 5 and a Box at location 6 whose
    stored type argument is the mutable Cell type. *)
Definition fresh_box : Obj :=
  mkObj (mkruntime_type Mut_r 2 [RClass Mut 1 []]) [Iot 5].

(** The heap after the two allocations and before the write. *)
Definition hmid : heap :=
  hA ++ [mkObj (mkruntime_type Mut_r 1 []) [Null_a]; fresh_box].

(** The heap when work returns. *)
Definition hA' : heap :=
  hA ++ [mkObj (mkruntime_type Mut_r 1 []) [Iot 2]; fresh_box].

Definition rΓmid : r_env :=
  mkr_env [Iot 4; Iot 2; Null_a; Iot 5; Iot 6; Iot 5] [] [].

Definition rΓA' : r_env :=
  mkr_env [Iot 0; Iot 1; Iot 2; Iot 3; Iot 4; Iot 2] [] [].

Definition work_allocs : stmt :=
  SSeq (SLocal ROObject 2)
  (SSeq (SLocal MutCell 3)
  (SSeq (SLocal MutBoxMutCell 4)
  (SSeq (SLocal MutCell 5)
  (SSeq (SNew 3 Mut_c 1 [] [2])
  (SSeq (SNew 4 Mut_c 2 [MutCell] [3])
        (SVarAss 5 (EField 4 0))))))).

(** Up to the write: two objects are allocated, and the reference read back
    out of the Box points to the fresh Cell. *)
Lemma work_allocs_eval : eval_stmt CT rΓwork hA work_allocs OK rΓmid hmid.
Proof.
  unfold work_allocs, rΓwork, rΓmid, hmid, fresh_box, hA.
  ev_local. ev_local. ev_local. ev_local.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  match goal with
  | |- eval_stmt _ ?r ?h _ _ _ _ =>
      refine (SBS_Assign CT r h 5 _ Null_a (Iot 5) eq_refl _)
  end.
  eapply EBS_Field; reflexivity.
Qed.

(** The write itself. *)
Lemma work_write_eval :
  eval_stmt CT rΓmid hmid (SFldWrite 5 0 1) OK rΓmid hA'.
Proof.
  eapply SBS_FldWrite with (a := RDA);
    [reflexivity | reflexivity | reflexivity | apply value_is_rda
    | reflexivity | reflexivity | reflexivity].
Qed.

Lemma work_body_eval :
  eval_stmt CT rΓwork hA (mbody_stmt (mbody work)) OK rΓmid hA'.
Proof.
  cbn. unfold rΓwork.
  ev_local. ev_local. ev_local. ev_local.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq.
  { eapply SBS_Assign; [reflexivity|]. eapply EBS_Field; reflexivity. }
  cbn. exact work_write_eval.
Qed.

Theorem callW_eval : eval_stmt CT rΓA hA callW OK rΓA' hA'.
Proof.
  unfold callW, rΓA.
  eapply SBS_Call with (mdef := work) (D := 3) (cy := 3)
    (rΓ' := rΓwork) (rΓ'' := rΓmid).
  - reflexivity.
  - reflexivity.
  - apply find_work.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold callee_env. do 4 eexists.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [apply rsi_refl | reflexivity].
  - apply work_body_eval.
  - reflexivity.
  - reflexivity.
Qed.

Lemma main_eval : eval_stmt CT rΓ0 h0 main OK rΓA' hA'.
Proof.
  unfold main. eapply SBS_Seq; [apply prefix_eval | apply callW_eval].
Qed.

(* ------------------DELIVERABLE 5: THE THEOREM APPLIED------------------*)

(** The readonly-state theorem applied to the call, for any outcome of the
    call and any object of the entry heap.  The hypothesis used is the
    condition on bounds; the earlier condition is false for this table. *)
Theorem callW_preserves : forall rΓ' h',
  eval_stmt CT rΓA hA callW OK rΓ' h' ->
  forall l qr C Rs vals f,
    runtime_getObj hA l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
    (sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA) ->
    exists vals',
      runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
      nth_error vals f = nth_error vals' f.
Proof.
  intros rΓ' h' Heval.
  eapply (readonly_state_preservation_final CT Δ0 sΓA AbstractState rΓA hA
            5 0 4 [] [2] sΓA rΓ' h' 4 3 3 work
            labels_ct_clean_bounds config_A rsfp_A
            callW_typed Heval).
  - reflexivity.
  - reflexivity.
  - apply find_work.
  - left. reflexivity.
Qed.

(** The Cell c (location 2), which was passed to work, keeps its value. *)
Theorem callW_preserves_value : forall rΓ' h',
  eval_stmt CT rΓA hA callW OK rΓ' h' ->
  exists vals',
    runtime_getObj h' 2 = Some (mkObj (mkruntime_type Mut_r 1 []) vals') /\
    nth_error vals' 0 = Some (Iot 1).
Proof.
  intros rΓ' h' Heval.
  destruct (callW_preserves rΓ' h' Heval 2 Mut_r 1 [] [Iot 1] 0 eq_refl
              (or_intror value_is_rda))
    as (vals' & Hobj & Hnth).
  exists vals'. split; [exact Hobj|]. symmetry. exact Hnth.
Qed.

(** The Box b (location 3), whose stored type argument is mutable, keeps its
    item. *)
Theorem callW_preserves_item : forall rΓ' h',
  eval_stmt CT rΓA hA callW OK rΓ' h' ->
  exists vals',
    runtime_getObj h' 3 =
      Some (mkObj (mkruntime_type Mut_r 2 [RClass Mut 1 []]) vals') /\
    nth_error vals' 0 = Some (Iot 2).
Proof.
  intros rΓ' h' Heval.
  destruct (callW_preserves rΓ' h' Heval 3 Mut_r 2 [RClass Mut 1 []]
              [Iot 2] 0 eq_refl (or_intror item_is_rda))
    as (vals' & Hobj & Hnth).
  exists vals'. split; [exact Hobj|]. symmetry. exact Hnth.
Qed.

(** Both, for the run exhibited above. *)
Theorem callW_preserves_run :
  (exists vals',
     runtime_getObj hA' 2 = Some (mkObj (mkruntime_type Mut_r 1 []) vals') /\
     nth_error vals' 0 = Some (Iot 1)) /\
  (exists vals',
     runtime_getObj hA' 3 =
       Some (mkObj (mkruntime_type Mut_r 2 [RClass Mut 1 []]) vals') /\
     nth_error vals' 0 = Some (Iot 2)).
Proof.
  split.
  - exact (callW_preserves_value rΓA' hA' callW_eval).
  - exact (callW_preserves_item rΓA' hA' callW_eval).
Qed.

(* ------------------DELIVERABLE 6: THE RUN DOES SOMETHING------------------*)

(** The call allocated two objects; the fresh Cell (location 5) held null
    after its allocation and holds the Cell c (location 2) when work
    returns; the fresh Box (location 6) stores the mutable type argument and
    points to the fresh Cell. *)
Theorem callW_not_vacuous :
  dom hA' = dom hA + 2 /\
  runtime_getObj hA 5 = None /\
  (exists o, runtime_getObj hmid 5 = Some o /\
             nth_error (fields_map o) 0 = Some Null_a) /\
  (exists o, runtime_getObj hA' 5 = Some o /\
             rt_type o = mkruntime_type Mut_r 1 [] /\
             nth_error (fields_map o) 0 = Some (Iot 2)) /\
  (exists o, runtime_getObj hA' 6 = Some o /\
             rt_type o = mkruntime_type Mut_r 2 [RClass Mut 1 []] /\
             nth_error (fields_map o) 0 = Some (Iot 5)) /\
  runtime_getVal rΓA 2 = Some (Iot 2) /\
  hmid <> hA' /\ hA <> hA'.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [eexists; split; reflexivity|].
  split; [eexists; split; [reflexivity | split; reflexivity]|].
  split; [eexists; split; [reflexivity | split; reflexivity]|].
  split; [reflexivity|].
  split; discriminate.
Qed.

(** The slot written inside work is receiver-dependent assignable: it is one
    of the slots the theorem protects on objects of the entry heap.  The
    write is allowed because its target did not exist at entry. *)
Lemma written_slot_is_protected_kind :
  sf_assignability_rel CT 1 0 Final \/ sf_assignability_rel CT 1 0 RDA.
Proof. right. apply value_is_rda. Qed.

Print Assumptions labels_ct_wf.
Print Assumptions labels_ct_clean_bounds.
Print Assumptions labels_ct_not_clean.
Print Assumptions rsf_A.
Print Assumptions callW_eval.
Print Assumptions callW_preserves.
Print Assumptions callW_preserves_run.
Print Assumptions callW_not_vacuous.
