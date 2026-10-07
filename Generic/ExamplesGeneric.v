From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric.

(** A concrete generic program for the readonly-state preservation theorem
    with type parameters.  The caller instantiates a protected generic method
    with a mutable type argument: a protected container with a mutable
    payload.

    class 0: @RDM class Object {}
    class 1: @RDM class Cell extends Object {
       @RDA @RO Object value;             // field 0
    }
    class 2: @RDM class Box<E extends @RO Object> extends Object {
       @RDA E item;                       // field 0
       @Assignable @RO Object note;       // field 1
    }
    class 3: @RDM class Tool extends Object {
       // method 0, readonly-state, one method type parameter X
       @RS <X extends @RO Cell> @RO Object look(@RO Tool this, @RO Box<X> b, X c) {
           @RO Object r;     // var 3
           X t;              // var 4
           t = b.item;       // the result has type X
           r = t.value;      // member access through X, via its bound @RO Cell
           b.note = r;       // the slot is declared assignable
           return r;
       }
    }

    main (variable 0 is the receiver, a @Mut Object; no type variables;
    abstract-state mode):
      @Mut Object o;            // var 1
      @Mut Cell c;              // var 2
      @Mut Box<@Mut Cell> b;    // var 3
      @Mut Tool t;              // var 4
      @RO Object x;             // var 5
      @RO Object n;             // var 6, never assigned, so it holds null
      o = new @Mut Object();
      c = new @Mut Cell(o);
      b = new @Mut Box<@Mut Cell>(c, n);
      t = new @Mut Tool();
      x = t.look<@Mut Cell>(b, c);        // call A

    The program is typed exactly as sketched; nothing had to be changed. *)

(* ------------------THE PROGRAM------------------*)

Definition ROObject : qualified_type := TClass RO 0 [].
Definition MutObject : qualified_type := TClass Mut 0 [].
Definition ROCell : qualified_type := TClass RO 1 [].
Definition MutCell : qualified_type := TClass Mut 1 [].
Definition ROTool : qualified_type := TClass RO 3 [].
Definition MutTool : qualified_type := TClass Mut 3 [].

(* The class type parameter E of Box, and the method type parameter X of look *)
Definition tE : qualified_type := TVar TVSub ClassVar 0.
Definition tX : qualified_type := TVar TVSub MethodVar 0.

Definition ROBoxX : qualified_type := TClass RO 2 [tX].
Definition MutBoxMutCell : qualified_type := TClass Mut 2 [MutCell].
Definition ROBoxMutCell : qualified_type := TClass RO 2 [MutCell].

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

Definition note_field : field_def :=
  {| assignability := Assignable; ftype := ROObject |}.

Definition BoxDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 2;
                     ctparams := [ROObject];
                     super := Some (0, []) |};
     body := {| fields := [item_field; note_field]; methods := [] |} |}.

Definition look : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [ROCell];
          mret := ROObject;
          mname := 0;
          mreceiver := ROTool;
          mparams := [ROBoxX; tX] |};
     mbody :=
       {| mbody_stmt :=
            SSeq (SLocal ROObject 3)
            (SSeq (SLocal tX 4)
            (SSeq (SVarAss 4 (EField 1 0))
            (SSeq (SVarAss 3 (EField 4 0))
                  (SFldWrite 1 1 3))));
          mreturn := 3 |} |}.

Definition ToolDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 3; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := []; methods := [look] |} |}.

Definition CT : class_table := [ObjectDef; CellDef; BoxDef; ToolDef].

Definition prefix : stmt :=
  SSeq (SLocal MutObject 1)
  (SSeq (SLocal MutCell 2)
  (SSeq (SLocal MutBoxMutCell 3)
  (SSeq (SLocal MutTool 4)
  (SSeq (SLocal ROObject 5)
  (SSeq (SLocal ROObject 6)
  (SSeq (SNew 1 Mut_c 0 [] [])
  (SSeq (SNew 2 Mut_c 1 [] [1])
  (SSeq (SNew 3 Mut_c 2 [MutCell] [2; 6])
        (SNew 4 Mut_c 3 [] []))))))))).

(** Call A: the caller supplies the mutable type argument. *)
Definition callA : stmt := SCall 5 0 4 [MutCell] [3; 2].

Definition main : stmt := SSeq prefix callA.

Definition Δ0 : tv_env := mk_tv_env [] [] AbstractState.
Definition sΓ0 : s_env := [MutObject].
Definition sΓA : s_env :=
  [MutObject; MutObject; MutCell; MutBoxMutCell; MutTool; ROObject; ROObject].

(** The bound environment of look: no class parameters, one method parameter
    bounded by a readonly Cell. *)
Definition ΔX : tv_env := mk_tv_env [] [ROCell] ReadonlyState.

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

Lemma wf_tX : forall top, wf_stype CT ΔX top tX.
Proof. intros. eapply wfs_var; [reflexivity|]. right. discriminate. Qed.

Lemma sub_tX_ROObject : bound_sub CT ΔX tX ROObject.
Proof.
  intros m.
  eapply qtype_trans; [|apply (sub_Cell_ROObject (with_mode ΔX m) RO)].
  apply qtype_var_bound. reflexivity.
Qed.

Lemma wf_ROBoxX : wf_stypeuse CT ΔX ROBoxX.
Proof.
  apply wf_Box; [discriminate | apply wf_tX | apply sub_tX_ROObject].
Qed.

Lemma wf_tX_use : wf_stypeuse CT ΔX tX.
Proof. apply wf_tX. Qed.

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

Create HintDb exg.
Local Hint Resolve wf_MutObject wf_ROObject wf_MutCell wf_ROCell wf_MutTool
  wf_ROTool wf_MutBoxMutCell wf_ROBoxX wf_tX_use : exg.

Ltac wfenv :=
  split; [cbn; lia |
          cbn; repeat (apply Forall_cons; [solve [auto with exg]|]);
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

Lemma collect_Box : CollectFields CT 2 [item_field; note_field].
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

Lemma note_is_assignable : sf_assignability_rel CT 2 1 Assignable.
Proof.
  exists note_field. split; [|reflexivity].
  eapply FL_Found; [apply collect_Box | reflexivity].
Qed.

Lemma no_method_in_Object : forall m D mdef,
  ~ FindMethodWithName CT 0 m D mdef.
Proof.
  intros m D mdef H. inversion H; subst.
  - cbn in Hfind. injection Hfind as <-. cbn in Hget_method. discriminate.
  - cbn in Hfind. injection Hfind as <-. cbn in Hsuper. discriminate.
Qed.

Lemma find_look : FindMethodWithName CT 3 0 3 look.
Proof. eapply FOM_Here; reflexivity. Qed.

(* ------------------DELIVERABLE 1: THE CLASS TABLE------------------*)

(** The body of look, checked in readonly-state mode under X <: @RO Cell. *)
Lemma look_body_typed :
  stmt_typing CT ΔX [ROTool; ROBoxX; tX] ReadonlyState
    (mbody_stmt (mbody look)) [ROTool; ROBoxX; tX; ROObject; tX].
Proof.
  cbn.
  eapply ST_Seq; [wfenv | |].
  { eapply ST_Local;
      [wfenv | auto with exg | reflexivity | reflexivity | reflexivity]. }
  eapply ST_Seq; [wfenv | |].
  { eapply ST_Local;
      [wfenv | auto with exg | reflexivity | reflexivity | reflexivity]. }
  cbn.
  eapply ST_Seq; [wfenv | |].
  { (* t = b.item: the field is typed by Box's parameter; read through
       @RO Box<X> it has type X *)
    eapply ST_VarAss with (Tx := tX);
      [wfenv | | discriminate | reflexivity | ].
    - eapply ET_Field with (x := 1) (T := ROBoxX) (qx := RO) (C := 2)
        (Ts := [tX]) (fDef := item_field);
        [wfenv | reflexivity | reflexivity |].
      eapply FL_Found; [apply collect_Box | reflexivity].
    - cbn. apply qtype_var_refl. }
  eapply ST_Seq; [wfenv | |].
  { (* r = t.value: t has the bare type X; its members are those of the
       bound @RO Cell *)
    eapply ST_VarAss with (Tx := ROObject);
      [wfenv | | discriminate | reflexivity | ].
    - eapply ET_Field with (x := 4) (T := tX) (qx := RO) (C := 1)
        (Ts := []) (fDef := value_field);
        [wfenv | reflexivity | reflexivity |].
      eapply FL_Found; [apply collect_Cell | reflexivity].
    - cbn. refl_sub. }
  (* b.note = r: the slot is assignable through any reference *)
  eapply ST_FldWrite with (Tx := ROBoxX) (Ty := ROObject) (qx := RO)
    (C := 2) (Ts := [tX]) (fieldT := note_field);
    [wfenv | reflexivity | reflexivity | reflexivity | | | reflexivity].
  - eapply FL_Found; [apply collect_Box | reflexivity].
  - split; [cbn; refl_sub | left; cbn; intuition discriminate].
Qed.

Lemma wf_look : wf_method CT 3 look.
Proof.
  unfold wf_method.
  change (method_tv_env CT 3 (msignature look)) with ΔX.
  cbn.
  split; [left; exists RO; reflexivity|].
  split.
  { constructor; [|constructor]. split; [exact I | apply wf_ROCell]. }
  split; [apply wf_ROObject|].
  split.
  { exists [ROTool; ROBoxX; tX; ROObject; tX], ROObject. split; [|split].
    - apply look_body_typed.
    - reflexivity.
    - refl_sub. }
  split.
  { intros def parent Ss D mdef_parent Vs Hfind Hsuper Hfm _.
    cbn in Hfind. injection Hfind as <-. cbn in Hsuper.
    injection Hsuper as <- <-.
    exfalso. eapply no_method_in_Object; eauto. }
  (* the signature has no mutable position, reading X through its bound *)
  intros _. split.
  - constructor; [discriminate | constructor].
  - constructor.
    + constructor; [discriminate|]. constructor; [|constructor].
      eapply nm_var; [reflexivity|].
      constructor; [discriminate | constructor].
    + constructor; [|constructor].
      eapply nm_var; [reflexivity|].
      constructor; [discriminate | constructor].
Qed.

Lemma generic_ct_wf : wf_class_table CT.
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
      * constructor; [|constructor; [|constructor]]; unfold wf_field; cbn.
        -- eapply wfs_var; [reflexivity|]. right. discriminate.
        -- wfp.
    + eapply WFOtherDef with (superC := 0) (Ss := []);
        try reflexivity; cbn; try solve [constructor]; auto.
      * wfp.
      * constructor; [apply wf_look | constructor].
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

Lemma clean_q_RO : clean_q RO.
Proof. repeat split; discriminate. Qed.

(** The bounds in scope inside look are clean: the only one is @RO Cell. *)
Lemma look_bounds_clean : clean_bounds ΔX.
Proof.
  intros o n B Hb. destruct o; cbn in Hb.
  - destruct n; discriminate.
  - destruct n as [|n]; cbn in Hb.
    + injection Hb as <-. exists RO, 1, (@nil qualified_type).
      split; [reflexivity|]. split; [apply clean_q_RO | constructor].
    + destruct n; discriminate.
Qed.

(** The class table is clean.  look is the only readonly-state method: its
    bound environment, its receiver and parameter types, and its body mention
    no mutable type argument (they mention X instead); and no class passes a
    type argument to its superclass. *)
Lemma generic_ct_clean : clean_ct CT.
Proof.
  constructor.
  - intros C P Ss Hp. unfold parent_lookup in Hp.
    destruct C as [|[|[|[|C]]]]; cbn in Hp.
    + discriminate.
    + injection Hp as <- <-. constructor.
    + injection Hp as <- <-. constructor.
    + injection Hp as <- <-. constructor.
    + destruct C; discriminate.
  - intros C def mdef Hfind Hin _.
    destruct C as [|[|[|[|C]]]]; cbn in Hfind.
    + injection Hfind as <-. destruct Hin.
    + injection Hfind as <-. destruct Hin.
    + injection Hfind as <-. destruct Hin.
    + injection Hfind as <-. cbn in Hin. destruct Hin as [<- | []].
      change (method_tv_env CT 3 (msignature look)) with ΔX.
      split; [apply look_bounds_clean|]. split.
      * cbn. constructor; [constructor|].
        constructor; [constructor; [exact I | constructor]|].
        constructor; [exact I | constructor].
      * cbn. split; [constructor|]. repeat split.
    + destruct C; discriminate.
Qed.

(* ------------------DELIVERABLE 2: TYPING AND THE PREFIX------------------*)

Ltac ty_local :=
  eapply ST_Local;
    [wfenv | solve [auto with exg] | reflexivity | reflexivity | reflexivity].

Ltac ty_seq := eapply ST_Seq; [wfenv | |].

Lemma prefix_typed : stmt_typing CT Δ0 sΓ0 AbstractState prefix sΓA.
Proof.
  unfold prefix, sΓA, sΓ0, Δ0.
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  cbn.
  (* o = new @Mut Object() *)
  ty_seq.
  { eapply ST_New with (Tx := MutObject) (argtypes := []) (fds := []);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutObject | constructor | constructor
      | apply collect_Object | constructor | ].
    cbn. refl_sub. }
  (* c = new @Mut Cell(o) *)
  ty_seq.
  { eapply ST_New with (Tx := MutCell) (argtypes := [MutObject]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutCell | constructor | constructor
      | apply collect_Cell | | ].
    - constructor; [|constructor]. cbn. split; [qual_sub|].
      left. cbn. intuition discriminate.
    - cbn. refl_sub. }
  (* b = new @Mut Box<@Mut Cell>(c, n): the payload field, declared E, is
     seen as @Mut Cell *)
  ty_seq.
  { eapply ST_New with (Tx := MutBoxMutCell)
      (argtypes := [MutCell; ROObject]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutBoxMutCell | | | apply collect_Box | | ].
    - constructor; [|constructor]. cbn. intuition discriminate.
    - constructor; [|constructor]. cbn. split; [intuition discriminate|].
      intros m. apply sub_Cell_ROObject.
    - constructor; [|constructor; [|constructor]]; cbn.
      + split; [refl_sub | left; cbn; intuition discriminate].
      + split; [refl_sub | left; cbn; intuition discriminate].
    - cbn. refl_sub. }
  (* t = new @Mut Tool() *)
  eapply ST_New with (Tx := MutTool) (argtypes := []) (fds := []);
    [wfenv | reflexivity | reflexivity | reflexivity | discriminate
    | reflexivity | apply wf_MutTool | constructor | constructor
    | apply collect_Tool | constructor | ].
  cbn. refl_sub.
Qed.

(** Call A.  The written type argument @Mut Cell is checked against the
    bound @RO Cell; the parameter types @RO Box<X> and X become
    @RO Box<@Mut Cell> and @Mut Cell. *)
Lemma callA_typed : stmt_typing CT Δ0 sΓA AbstractState callA sΓA.
Proof.
  unfold callA, sΓA, Δ0.
  eapply ST_Call with (Tx := ROObject) (Ty := MutTool)
    (argtypes := [MutBoxMutCell; MutCell])
    (qy := Mut) (C := 3) (Ts := []) (D := 3) (Vs := [])
    (mdef := look);
    [wfenv | reflexivity | reflexivity | reflexivity | reflexivity
    | apply find_look | apply si_refl | discriminate | | | reflexivity
    | | | | | apply method_rs_as].
  - constructor; [apply wf_MutCell | constructor].
  - constructor; [|constructor]. cbn. intuition discriminate.
  - constructor; [|constructor]. cbn. split; [intuition discriminate|].
    intros m. qual_sub.
  - cbn. refl_sub.
  - left. cbn. split; [qual_sub | left; cbn; intuition discriminate].
  - constructor; [|constructor; [|constructor]]; cbn.
    + split; [qual_sub | left; cbn; intuition discriminate].
    + split; [refl_sub | left; cbn; intuition discriminate].
Qed.

Lemma main_typed : stmt_typing CT Δ0 sΓ0 AbstractState main sΓA.
Proof.
  unfold main.
  eapply ST_Seq; [unfold sΓ0; wfenv | apply prefix_typed | apply callA_typed].
Qed.

(** The states.  Location 0 is main's receiver, 1 is o, 2 is the Cell, 3 is
    the Box, 4 is the Tool. *)
Definition rΓ0 : r_env := mkr_env [Iot 0] [] [].
Definition h0 : heap := [mkObj (mkruntime_type Mut_r 0 []) []].

Definition rΓA : r_env :=
  mkr_env [Iot 0; Iot 1; Iot 2; Iot 3; Iot 4; Null_a; Null_a] [] [].

(** The Box object stores the runtime type argument [@Mut Cell]. *)
Definition hA : heap :=
  [ mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 1 []) [Iot 1];
    mkObj (mkruntime_type Mut_r 2 [RClass Mut 1 []]) [Iot 2; Null_a];
    mkObj (mkruntime_type Mut_r 3 []) [] ].

Ltac ev_local := eapply SBS_Seq; [apply SBS_Local; reflexivity|]; cbn.

Lemma prefix_eval : eval_stmt CT rΓ0 h0 prefix OK rΓA hA.
Proof.
  unfold prefix, rΓ0, h0.
  ev_local. ev_local. ev_local. ev_local. ev_local. ev_local.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_New; reflexivity.
Qed.

Lemma initial_config : wf_r_config CT Δ0 sΓ0 rΓ0 h0.
Proof.
  unfold Δ0, sΓ0, rΓ0, h0.
  refine (conj generic_ct_wf
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

(** The configuration just before call A is well formed. *)
Lemma config_A : wf_r_config CT Δ0 sΓA rΓA hA.
Proof.
  eapply preservation_pico;
    eauto using prefix_eval, initial_config, prefix_typed.
Qed.

(* ------------------DELIVERABLE 3: CALL A------------------*)

(** After call A: x holds o, and the Box's note slot holds o. *)
Definition rΓA' : r_env :=
  mkr_env [Iot 0; Iot 1; Iot 2; Iot 3; Iot 4; Iot 1; Null_a] [] [].

Definition hA' : heap :=
  [ mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 1 []) [Iot 1];
    mkObj (mkruntime_type Mut_r 2 [RClass Mut 1 []]) [Iot 2; Iot 1];
    mkObj (mkruntime_type Mut_r 3 []) [] ].

(** The activation of look: receiver the Tool, arguments the Box and the
    Cell, and the runtime method type argument [@Mut Cell]. *)
Definition rΓlook : r_env :=
  mkr_env [Iot 4; Iot 3; Iot 2] [] [RClass Mut 1 []].

Lemma callA_eval : eval_stmt CT rΓA hA callA OK rΓA' hA'.
Proof.
  unfold callA, rΓA.
  eapply SBS_Call with (mdef := look) (D := 3) (cy := 3)
    (rΓ' := rΓlook)
    (rΓ'' := mkr_env [Iot 4; Iot 3; Iot 2; Iot 1; Iot 2] [] [RClass Mut 1 []]).
  - reflexivity.
  - reflexivity.
  - apply find_look.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold callee_env. do 4 eexists.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [apply rsi_refl | reflexivity].
  - cbn. unfold rΓlook.
    eapply SBS_Seq; [apply SBS_Local; reflexivity|]. cbn.
    eapply SBS_Seq; [apply SBS_Local; reflexivity|]. cbn.
    eapply SBS_Seq.
    { eapply SBS_Assign; [reflexivity|]. eapply EBS_Field; reflexivity. }
    cbn.
    eapply SBS_Seq.
    { eapply SBS_Assign; [reflexivity|]. eapply EBS_Field; reflexivity. }
    cbn.
    eapply SBS_FldWrite with (a := Assignable);
      [reflexivity | reflexivity | reflexivity | apply note_is_assignable
      | reflexivity | reflexivity | reflexivity].
  - reflexivity.
  - reflexivity.
Qed.

(** The whole program runs from the initial state to the final one. *)
Lemma main_eval : eval_stmt CT rΓ0 h0 main OK rΓA' hA'.
Proof.
  unfold main. eapply SBS_Seq; [apply prefix_eval | apply callA_eval].
Qed.

(** The readonly-state theorem for generic programs, applied to call A, for
    any outcome of the call and any object of the entry heap. *)
Lemma callA_preserves : forall rΓ' h',
  eval_stmt CT rΓA hA callA OK rΓ' h' ->
  forall l qr C Rs vals f,
    runtime_getObj hA l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
    (sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA) ->
    exists vals',
      runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
      nth_error vals f = nth_error vals' f.
Proof.
  intros rΓ' h' Heval.
  eapply (readonly_state_preservation_generic CT Δ0 sΓA AbstractState rΓA hA
            5 0 4 [MutCell] [3; 2] sΓA rΓ' h' 4 3 3 look
            generic_ct_clean config_A callA_typed Heval).
  - reflexivity.
  - reflexivity.
  - apply find_look.
  - left. reflexivity.
Qed.

(** The Box (location 3), whose stored type argument is mutable, keeps its
    payload field item (field 0). *)
Theorem callA_preserves_item : forall rΓ' h',
  eval_stmt CT rΓA hA callA OK rΓ' h' ->
  exists vals',
    runtime_getObj h' 3 =
      Some (mkObj (mkruntime_type Mut_r 2 [RClass Mut 1 []]) vals') /\
    nth_error vals' 0 = Some (Iot 2).
Proof.
  intros rΓ' h' Heval.
  destruct (callA_preserves rΓ' h' Heval 3 Mut_r 2 [RClass Mut 1 []]
              [Iot 2; Null_a] 0 eq_refl (or_intror item_is_rda))
    as (vals' & Hobj & Hnth).
  exists vals'. split; [exact Hobj|]. symmetry. exact Hnth.
Qed.

(** The mutable Cell (location 2) keeps its field value (field 0). *)
Theorem callA_preserves_value : forall rΓ' h',
  eval_stmt CT rΓA hA callA OK rΓ' h' ->
  exists vals',
    runtime_getObj h' 2 = Some (mkObj (mkruntime_type Mut_r 1 []) vals') /\
    nth_error vals' 0 = Some (Iot 1).
Proof.
  intros rΓ' h' Heval.
  destruct (callA_preserves rΓ' h' Heval 2 Mut_r 1 [] [Iot 1] 0 eq_refl
              (or_intror value_is_rda))
    as (vals' & Hobj & Hnth).
  exists vals'. split; [exact Hobj|]. symmetry. exact Hnth.
Qed.

(** Both at once. *)
Theorem callA_preserves_item_and_value : forall rΓ' h',
  eval_stmt CT rΓA hA callA OK rΓ' h' ->
  (exists vals',
     runtime_getObj h' 3 =
       Some (mkObj (mkruntime_type Mut_r 2 [RClass Mut 1 []]) vals') /\
     nth_error vals' 0 = Some (Iot 2)) /\
  (exists vals',
     runtime_getObj h' 2 = Some (mkObj (mkruntime_type Mut_r 1 []) vals') /\
     nth_error vals' 0 = Some (Iot 1)).
Proof.
  intros rΓ' h' Heval. split.
  - eapply callA_preserves_item; eauto.
  - eapply callA_preserves_value; eauto.
Qed.

(** By computation on the explicit final heap: the Box's note slot (field 1)
    held null before the call and holds o (location 1) afterwards, while
    item and the Cell's value are as before. *)
Lemma callA_note_changed :
  (exists o, runtime_getObj hA 3 = Some o /\
             nth_error (fields_map o) 1 = Some Null_a) /\
  (exists o', runtime_getObj hA' 3 = Some o' /\
              nth_error (fields_map o') 1 = Some (Iot 1) /\
              nth_error (fields_map o') 0 = Some (Iot 2)) /\
  (exists o', runtime_getObj hA' 2 = Some o' /\
              nth_error (fields_map o') 0 = Some (Iot 1)) /\
  hA <> hA'.
Proof.
  split; [eexists; split; reflexivity|].
  split; [eexists; split; [reflexivity | split; reflexivity]|].
  split; [eexists; split; reflexivity|].
  discriminate.
Qed.

(** The slot written by the call is outside the readonly-state guarantee: it
    is neither final nor receiver-dependent assignable. *)
Lemma note_not_protected :
  ~ (sf_assignability_rel CT 2 1 Final \/ sf_assignability_rel CT 2 1 RDA).
Proof.
  intros [H | H];
    pose proof (sf_assignability_deterministic_rel _ _ _ _ _ H
                  note_is_assignable) as Heq;
    discriminate.
Qed.

Print Assumptions callA_preserves_item.
Print Assumptions callA_preserves_value.
Print Assumptions callA_preserves_item_and_value.
