From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric
  GhostLabels GhostTyping GhostForget GhostInvariant GhostOverride GhostCall
  GhostEntry ArgViews ArgTyping ArgFit ArgInvariant
  ArgCases ArgClean ArgOverride ArgCall ArgMain ArgEntry ArgRsf.

(** A worked example for the readonly-state theorem in which a type parameter
    has a receiver-dependent bound, and the parameter is used at that bound
    inside a readonly-state method.

    class 0: @RDM class Object {}
    class 1: @RDM class Person extends Object {
       @RDA @RO Object name;              // field 0
    }
    class 2: @RDM class RDMBox<E extends @RDM Person> extends Object {
       @RDA E item;                       // field 0
       // method 0, readonly-state
       @RS @RDM Person peek(@RDM RDMBox<E> this) {
           @RDM Person p;            // var 1
           p = this.item;            // E is used at its bound @RDM Person
           return p;
       }
    }
    class 3: @RDM class Tool extends Object {
       // method 0, readonly-state
       @RS @RO Object work(@RO Tool this, @RO Object y) {
           @RO Object n;                  // var 2, never assigned: null
           @Mut Person q;                 // var 3
           @Mut RDMBox<@Mut Person> b;    // var 4
           @Mut Person r;                 // var 5
           q = new @Mut Person(n);
           b = new @Mut RDMBox<@Mut Person>(q);
           r = b.peek();                  // a mutable Person comes back
           r.name = y;                    // write through it
           return y;
       }
    }

    main (variable 0 is the receiver, a @Mut Object; abstract-state mode):
      @Mut Object o;                 // var 1
      @Mut Person c;                 // var 2
      @Imm Person ip;                // var 3
      @Imm RDMBox<@Imm Person> ib;   // var 4
      @Mut Tool t;                   // var 5
      @RO Object x;                  // var 6
      o = new @Mut Object();
      c = new @Mut Person(o);
      ip = new @Imm Person(o);
      ib = new @Imm RDMBox<@Imm Person>(ip);
      t = new @Mut Tool();
      x = t.work(c);                      // the call *)

(* ------------------THE PROGRAM------------------*)

Definition ROObject : qualified_type := TClass RO 0 [].
Definition MutObject : qualified_type := TClass Mut 0 [].
Definition MutPerson : qualified_type := TClass Mut 1 [].
Definition ImmPerson : qualified_type := TClass Imm 1 [].
Definition RDMPerson : qualified_type := TClass RDM 1 [].
Definition ROTool : qualified_type := TClass RO 3 [].
Definition MutTool : qualified_type := TClass Mut 3 [].
Definition tE : qualified_type := TVar TVSub ClassVar 0.
Definition MutBoxMutPerson : qualified_type := TClass Mut 2 [MutPerson].
Definition ImmBoxImmPerson : qualified_type := TClass Imm 2 [ImmPerson].
Definition RDMBoxE : qualified_type := TClass RDM 2 [tE].

Definition ObjectDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 0; ctparams := [];
                     super := None |};
     body := {| fields := []; methods := [] |} |}.

Definition name_field : field_def :=
  {| assignability := RDA; ftype := ROObject |}.

Definition PersonDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 1; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := [name_field]; methods := [] |} |}.

Definition item_field : field_def :=
  {| assignability := RDA; ftype := tE |}.

Definition peek : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mqparams := 0;
          mret := RDMPerson;
          mname := 0;
          mreceiver := RDMBoxE;
          mparams := [] |};
     mbody :=
       {| mbody_stmt :=
            SSeq (SLocal RDMPerson 1) (SVarAss 1 (EField 0 0));
          mreturn := 1 |} |}.

Definition BoxDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 2;
                     ctparams := [RDMPerson];
                     super := Some (0, []) |};
     body := {| fields := [item_field]; methods := [peek] |} |}.

Definition peekCall : stmt := SCall 5 0 4 [] [] [].

Definition work : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mqparams := 0;
          mret := ROObject;
          mname := 0;
          mreceiver := ROTool;
          mparams := [ROObject] |};
     mbody :=
       {| mbody_stmt :=
            SSeq (SLocal ROObject 2)
            (SSeq (SLocal MutPerson 3)
            (SSeq (SLocal MutBoxMutPerson 4)
            (SSeq (SLocal MutPerson 5)
            (SSeq (SNew 3 Mut_c 1 [] [2])
            (SSeq (SNew 4 Mut_c 2 [MutPerson] [3])
            (SSeq peekCall
                  (SFldWrite 5 0 1)))))));
          mreturn := 1 |} |}.

Definition ToolDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 3; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := []; methods := [work] |} |}.

Definition CT : class_table := [ObjectDef; PersonDef; BoxDef; ToolDef].

Definition prefix : stmt :=
  SSeq (SLocal MutObject 1)
  (SSeq (SLocal MutPerson 2)
  (SSeq (SLocal ImmPerson 3)
  (SSeq (SLocal ImmBoxImmPerson 4)
  (SSeq (SLocal MutTool 5)
  (SSeq (SLocal ROObject 6)
  (SSeq (SNew 1 Mut_c 0 [] [])
  (SSeq (SNew 2 Mut_c 1 [] [1])
  (SSeq (SNew 3 Imm_c 1 [] [1])
  (SSeq (SNew 4 Imm_c 2 [ImmPerson] [3])
        (SNew 5 Mut_c 3 [] [])))))))))).

Definition callW : stmt := SCall 6 0 5 [] [] [2].

Definition main : stmt := SSeq prefix callW.

Definition Δ0 : tv_env := mk_tv_env [] [] AbstractState 0.
Definition sΓ0 : s_env := [MutObject].
Definition sΓA : s_env :=
  [MutObject; MutObject; MutPerson; ImmPerson; ImmBoxImmPerson; MutTool;
   ROObject].

(** The bound environment of work: no type parameter is in scope. *)
Definition ΔW : tv_env := mk_tv_env [] [] ReadonlyState 0.

(** The bound environment of peek: the class parameter E, bounded by
    @RDM Person. *)
Definition ΔP : tv_env := mk_tv_env [RDMPerson] [] ReadonlyState 0.

(* ------------------SMALL TACTICS AND FACTS------------------*)

Ltac qs := (apply q_refl; discriminate) || apply q_rd || apply q_bot.

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

Ltac refl_sub :=
  apply qualified_type_subtype_refl_class; [cbn; lia | discriminate].

Ltac qual_sub :=
  apply qtype_qual; [cbn; lia | qs | apply Forall2_targ_sub_refl].

(** Any Person is a readonly Object. *)
Lemma sub_Person_ROObject : forall Δ q0,
  qualified_type_subtype CT Δ (TClass q0 1 []) ROObject.
Proof.
  intros Δ q0. eapply qtype_trans.
  - apply qtype_hier with (D := 0) (Vs := []).
    eapply si_step; [reflexivity|]. cbn. apply si_refl.
  - apply qtype_qual; [cbn; lia | apply q_rd | constructor].
Qed.

(** A mutable box of mutable Persons: seen through the mutable head, the
    declared bound @RDM Person reads @Mut Person. *)
Lemma wf_MutBoxMutPerson : forall Δ, wf_stypeuse CT Δ MutBoxMutPerson.
Proof.
  intros Δ. eapply wfs_class; [reflexivity | right | reflexivity | |].
  - cbn. qs.
  - constructor; [|constructor]. apply wf_plain; [auto | discriminate].
  - constructor; [|constructor]. intros m. cbn. refl_sub.
Qed.

(** An immutable box of immutable Persons: the bound reads @Imm Person. *)
Lemma wf_ImmBoxImmPerson : forall Δ, wf_stypeuse CT Δ ImmBoxImmPerson.
Proof.
  intros Δ. eapply wfs_class; [reflexivity | right | reflexivity | |].
  - cbn. qs.
  - constructor; [|constructor]. apply wf_plain; [auto | discriminate].
  - constructor; [|constructor]. intros m. cbn. refl_sub.
Qed.

(** The declared receiver of peek: the bound reads @RDM Person, and E is
    below it because that is its declared bound. *)
Lemma wf_RDMBoxE : wf_stypeuse CT ΔP RDMBoxE.
Proof.
  eapply wfs_class; [reflexivity | right | reflexivity | |].
  - cbn. qs.
  - constructor; [|constructor]. eapply wfs_var; [reflexivity | left; reflexivity].
  - constructor; [|constructor]. intros m. cbn.
    apply qtype_var_bound. reflexivity.
Qed.

Lemma wf_MutObject : forall Δ, wf_stypeuse CT Δ MutObject.
Proof. intros. wfp. Qed.
Lemma wf_ROObject : forall Δ, wf_stypeuse CT Δ ROObject.
Proof. intros. wfp. Qed.
Lemma wf_MutPerson : forall Δ, wf_stypeuse CT Δ MutPerson.
Proof. intros. wfp. Qed.
Lemma wf_ImmPerson : forall Δ, wf_stypeuse CT Δ ImmPerson.
Proof. intros. wfp. Qed.
Lemma wf_RDMPerson : forall Δ, wf_stypeuse CT Δ RDMPerson.
Proof. intros. wfp. Qed.
Lemma wf_MutTool : forall Δ, wf_stypeuse CT Δ MutTool.
Proof. intros. wfp. Qed.
Lemma wf_ROTool : forall Δ, wf_stypeuse CT Δ ROTool.
Proof. intros. wfp. Qed.

Create HintDb exr.
Local Hint Resolve wf_MutObject wf_ROObject wf_MutPerson wf_ImmPerson
  wf_RDMPerson wf_MutTool wf_ROTool wf_MutBoxMutPerson wf_ImmBoxImmPerson
  wf_RDMBoxE : exr.

Ltac wfenv :=
  split; [cbn; lia |
          cbn; repeat (apply Forall_cons; [solve [auto with exr]|]);
          apply Forall_nil].

Lemma collect_Object : CollectFields CT 0 [].
Proof. eapply CF_Object; reflexivity. Qed.

Lemma collect_Person : CollectFields CT 1 [name_field].
Proof.
  change (CollectFields CT 1
            (map (subst_field []) [] ++ Syntax.fields (body PersonDef))).
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

Lemma name_is_rda : sf_assignability_rel CT 1 0 RDA.
Proof.
  exists name_field. split; [|reflexivity].
  eapply FL_Found; [apply collect_Person | reflexivity].
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

Lemma find_peek : FindMethodWithName CT 2 0 2 peek.
Proof. eapply FOM_Here; reflexivity. Qed.

Ltac ty_local :=
  eapply ST_Local;
    [wfenv | solve [auto with exr] | reflexivity | reflexivity | reflexivity].

Ltac ty_seq := eapply ST_Seq; [wfenv | |].

(* ------------------DELIVERABLE 1: THE CLASS TABLE------------------*)

(** The read of the item inside peek.  Through the receiver-dependent
    receiver the field has the bare type E. *)
Lemma peek_read_typed :
  expr_has_type CT ΔP [RDMBoxE; RDMPerson] ReadonlyState (EField 0 0) tE.
Proof.
  eapply ET_Field with (x := 0) (T := RDMBoxE) (qx := RDM) (C := 2)
    (Ts := [tE]) (fDef := item_field);
    [wfenv | reflexivity | reflexivity |].
  eapply FL_Found; [apply collect_Box | reflexivity].
Qed.

(** The step of interest: inside readonly-state code, the type variable E is
    a subtype of its receiver-dependent bound @RDM Person. *)
Lemma E_below_its_bound : qualified_type_subtype CT ΔP tE RDMPerson.
Proof. apply qtype_var_bound. reflexivity. Qed.

Lemma peek_body_typed :
  stmt_typing CT ΔP [RDMBoxE] ReadonlyState
    (mbody_stmt (mbody peek)) [RDMBoxE; RDMPerson].
Proof.
  cbn. unfold ΔP.
  ty_seq; [ty_local|]. cbn.
  eapply ST_VarAss with (Tx := RDMPerson) (Te := tE);
    [wfenv | apply peek_read_typed | discriminate | reflexivity
    | apply E_below_its_bound].
Qed.

Lemma wf_peek : wf_method CT 2 peek.
Proof.
  unfold wf_method.
  change (method_tv_env CT 2 (msignature peek)) with ΔP.
  cbn.
  split; [apply receiver_plain_ok; left; exists RDM; reflexivity|].
  split; [constructor|].
  split; [apply wf_RDMPerson|].
  split.
  { exists [RDMBoxE; RDMPerson], RDMPerson.
    split; [|split].
    - apply peek_body_typed.
    - reflexivity.
    - refl_sub. }
  split.
  { intros def parent Ss D mdef_parent Vs Hfind Hsuper Hfm _.
    cbn in Hfind. injection Hfind as <-. cbn in Hsuper.
    injection Hsuper as <- <-.
    exfalso. eapply no_method_in_Object; eauto. }
  intros _. split.
  - constructor; [discriminate|].
    constructor; [|constructor].
    eapply nm_var; [reflexivity|].
    constructor; [discriminate | constructor].
  - constructor.
Qed.

(** The call b.peek() inside work, in readonly-state mode: through the
    mutable box the declared result @RDM Person reads @Mut Person. *)
Lemma peekCall_typed :
  stmt_typing CT ΔW
    [ROTool; ROObject; ROObject; MutPerson; MutBoxMutPerson; MutPerson]
    ReadonlyState peekCall
    [ROTool; ROObject; ROObject; MutPerson; MutBoxMutPerson; MutPerson].
Proof.
  unfold peekCall, ΔW.
  eapply ST_Call with (Tx := MutPerson) (Ty := MutBoxMutPerson)
    (argtypes := [])
    (qy := Mut) (C := 2) (Ts := [MutPerson]) (D := 2) (Vs := [MutPerson])
    (mdef := peek);
    [wfenv | reflexivity | reflexivity | reflexivity | reflexivity
    | apply find_peek | apply si_refl | discriminate | constructor
    | constructor | reflexivity | constructor | | | constructor
    | apply method_subtyping_refl | reflexivity | constructor | recv_known].
  - cbn. refl_sub.
  - cbn. split; [refl_sub | cbn; intuition discriminate].
Qed.

Lemma work_body_typed :
  stmt_typing CT ΔW [ROTool; ROObject] ReadonlyState
    (mbody_stmt (mbody work))
    [ROTool; ROObject; ROObject; MutPerson; MutBoxMutPerson; MutPerson].
Proof.
  cbn. unfold ΔW.
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  ty_seq; [ty_local|].
  cbn.
  (* q = new @Mut Person(n) *)
  ty_seq.
  { eapply ST_New with (Tx := MutPerson) (argtypes := [ROObject]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutPerson | constructor | constructor
      | apply collect_Person | | ].
    - constructor; [|constructor]. cbn. split; [refl_sub|].
      cbn. intuition discriminate.
    - cbn. refl_sub. }
  (* b = new @Mut RDMBox<@Mut Person>(q) *)
  ty_seq.
  { eapply ST_New with (Tx := MutBoxMutPerson) (argtypes := [MutPerson]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutBoxMutPerson | | | apply collect_Box | | ].
    - constructor; [|constructor]. cbn. intuition discriminate.
    - constructor; [|constructor]. cbn. split; [intuition discriminate|].
      intros m. refl_sub.
    - constructor; [|constructor]; cbn.
      split; [refl_sub | cbn; intuition discriminate].
    - cbn. refl_sub. }
  (* r = b.peek() *)
  ty_seq; [apply peekCall_typed|].
  (* r.name = y *)
  eapply ST_FldWrite with (Tx := MutPerson) (Ty := ROObject) (qx := Mut)
    (C := 1) (Ts := []) (fieldT := name_field);
    [wfenv | reflexivity | reflexivity | reflexivity | | | reflexivity].
  - eapply FL_Found; [apply collect_Person | reflexivity].
  - split; [cbn; refl_sub | cbn; intuition discriminate].
Qed.

Lemma wf_work : wf_method CT 3 work.
Proof.
  unfold wf_method.
  change (method_tv_env CT 3 (msignature work)) with ΔW.
  cbn.
  split; [apply receiver_plain_ok; left; exists RO; reflexivity|].
  split; [constructor|].
  split; [apply wf_ROObject|].
  split.
  { exists [ROTool; ROObject; ROObject; MutPerson; MutBoxMutPerson; MutPerson],
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

Theorem rdm_ct_wf : wf_class_table CT.
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
      * constructor; [apply wf_peek | constructor].
      * constructor; [intros [] | constructor].
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

(* ------------------DELIVERABLE 2: THE CONDITION ON BOUNDS HOLDS------------------*)

(** There are two readonly-state methods.  No type parameter is in scope of
    work.  In scope of peek there is one, E, and its bound @RDM Person is a
    class type with no mutable position: its head is receiver-dependent and
    it has no type arguments. *)
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

Theorem rdm_ct_clean_bounds : clean_bounds_ct CT.
Proof.
  intros C def md Hfind Hin _.
  destruct C as [|[|[|[|C]]]]; cbn in Hfind.
  - injection Hfind as <-. destruct Hin.
  - injection Hfind as <-. destruct Hin.
  - injection Hfind as <-. cbn in Hin. destruct Hin as [<- | []].
    intros o n B Hb.
    destruct o; [destruct n as [|[|n]] | destruct n]; cbn in Hb;
      try discriminate.
    injection Hb as <-.
    split; [exact I | apply nm_class; [discriminate | constructor]].
  - injection Hfind as <-. cbn in Hin. destruct Hin as [<- | []].
    intros o n B Hb. destruct o; destruct n; discriminate.
  - destruct C; discriminate.
Qed.

(** The condition is not vacuous: peek is a readonly-state method of the
    table and the bound environment in which it is checked contains the
    receiver-dependent bound. *)
Lemma peek_is_readonly_state :
  find_class CT 2 = Some BoxDef /\
  List.In peek (methods (body BoxDef)) /\
  readonly_state_method_scope (mscope (msignature peek)).
Proof.
  split; [reflexivity|]. split; [left; reflexivity | left; reflexivity].
Qed.

Lemma peek_bound_in_scope :
  tv_bound (method_tv_env CT 2 (msignature peek)) ClassVar 0
    = Some (TClass RDM 1 []).
Proof. reflexivity. Qed.

(** What the condition says about that bound. *)
Lemma peek_bound_checked :
  is_class_type (TClass RDM 1 []) /\
  no_mut (method_tv_env CT 2 (msignature peek)) (TClass RDM 1 []).
Proof.
  exact (rdm_ct_clean_bounds 2 BoxDef peek eq_refl (or_introl eq_refl)
           (or_introl eq_refl) ClassVar 0 (TClass RDM 1 [])
           peek_bound_in_scope).
Qed.

(* ------------------DELIVERABLE 3: THE STRICTER CONDITION FAILS------------------*)

(** The stricter condition used before asked the head of every such bound to
    be none of mutable, receiver-dependent and bottom.  The head of the bound
    of E is receiver-dependent. *)
Lemma rdm_head_not_clean : ~ clean_q RDM.
Proof. intros (_ & H & _). apply H. reflexivity. Qed.

Lemma peek_bound_not_closed_clean : ~ closed_clean (TClass RDM 1 []).
Proof. intros [H _]. exact (rdm_head_not_clean H). Qed.

(* ------------------DELIVERABLE 4: CONFIGURATION, TYPING, RUN------------------*)

Lemma prefix_typed : stmt_typing CT Δ0 sΓ0 AbstractState prefix sΓA.
Proof.
  unfold prefix, sΓA, sΓ0, Δ0.
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  cbn.
  ty_seq.
  { eapply ST_New with (Tx := MutObject) (argtypes := []) (fds := []);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutObject | constructor | constructor
      | apply collect_Object | constructor | ].
    cbn. refl_sub. }
  ty_seq.
  { eapply ST_New with (Tx := MutPerson) (argtypes := [MutObject]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutPerson | constructor | constructor
      | apply collect_Person | | ].
    - constructor; [|constructor]. cbn. split; [qual_sub|].
      cbn. intuition discriminate.
    - cbn. refl_sub. }
  ty_seq.
  { eapply ST_New with (Tx := ImmPerson) (argtypes := [MutObject]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_ImmPerson | constructor | constructor
      | apply collect_Person | | ].
    - constructor; [|constructor]. cbn. split; [qual_sub|].
      cbn. intuition discriminate.
    - cbn. refl_sub. }
  ty_seq.
  { eapply ST_New with (Tx := ImmBoxImmPerson) (argtypes := [ImmPerson]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_ImmBoxImmPerson | | | apply collect_Box | | ].
    - constructor; [|constructor]. cbn. intuition discriminate.
    - constructor; [|constructor]. cbn. split; [intuition discriminate|].
      intros m. refl_sub.
    - constructor; [|constructor]; cbn.
      split; [refl_sub | cbn; intuition discriminate].
    - cbn. refl_sub. }
  eapply ST_New with (Tx := MutTool) (argtypes := []) (fds := []);
    [wfenv | reflexivity | reflexivity | reflexivity | discriminate
    | reflexivity | apply wf_MutTool | constructor | constructor
    | apply collect_Tool | constructor | ].
  cbn. refl_sub.
Qed.

(** The call, made from abstract-state code.  The Person c is passed where a
    readonly Object is expected. *)
Lemma callW_typed : stmt_typing CT Δ0 sΓA AbstractState callW sΓA.
Proof.
  unfold callW, sΓA, Δ0.
  eapply ST_Call with (Tx := ROObject) (Ty := MutTool)
    (argtypes := [MutPerson])
    (qy := Mut) (C := 3) (Ts := []) (D := 3) (Vs := [])
    (mdef := work);
    [wfenv | reflexivity | reflexivity | reflexivity | reflexivity
    | apply find_work | apply si_refl | discriminate | | | reflexivity
    | | | | | apply method_rs_as | reflexivity | constructor | recv_known].
  - constructor.
  - constructor.
  - constructor.
  - cbn. refl_sub.
  - cbn. split; [qual_sub | cbn; intuition discriminate].
  - constructor; [|constructor]; cbn.
    split; [apply sub_Person_ROObject | cbn; intuition discriminate].
Qed.

Lemma main_typed : stmt_typing CT Δ0 sΓ0 AbstractState main sΓA.
Proof.
  unfold main.
  eapply ST_Seq; [unfold sΓ0; wfenv | apply prefix_typed | apply callW_typed].
Qed.

(** The states.  Location 0 is main's receiver, 1 is o, 2 is the mutable
    Person c, 3 is the immutable Person ip, 4 is the immutable box ib that
    holds ip, 5 is the Tool. *)
Definition rΓ0 : r_env := mkr_env [Iot 0] [] [] [].
Definition h0 : heap := [mkObj (mkruntime_type Mut_r 0 []) []].

Definition rΓA : r_env :=
  mkr_env [Iot 0; Iot 1; Iot 2; Iot 3; Iot 4; Iot 5; Null_a] [] [] [].

Definition hA : heap :=
  [ mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 1 []) [Iot 1];
    mkObj (mkruntime_type Imm_r 1 []) [Iot 1];
    mkObj (mkruntime_type Imm_r 2 [RClass Imm 1 []]) [Iot 3];
    mkObj (mkruntime_type Mut_r 3 []) [] ].

Ltac ev_local := eapply SBS_Seq; [apply SBS_Local; reflexivity|]; cbn.

Lemma prefix_eval : eval_stmt CT rΓ0 h0 prefix OK rΓA hA.
Proof.
  unfold prefix, rΓ0, h0.
  ev_local. ev_local. ev_local. ev_local. ev_local. ev_local.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_New; reflexivity.
Qed.

Lemma initial_config : wf_r_config CT Δ0 sΓ0 rΓ0 h0.
Proof.
  unfold Δ0, sΓ0, rΓ0, h0.
  refine (conj rdm_ct_wf
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
             (conj (Forall_nil _) (conj (conj (Forall_nil _) (Forall_nil _)) (conj _ _))))))); constructor.
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

(** The activation of work: receiver the Tool, argument the Person c. *)
Definition rΓwork : r_env := mkr_env [Iot 5; Iot 2] [] [] [].

(** The fresh objects: a Person at location 6 and a box at location 7 whose
    stored type argument is the mutable Person type. *)
Definition fresh_box : Obj :=
  mkObj (mkruntime_type Mut_r 2 [RClass Mut 1 []]) [Iot 6].

(** The heap after the two allocations; the call to peek leaves it as it
    is. *)
Definition hmid : heap :=
  hA ++ [mkObj (mkruntime_type Mut_r 1 []) [Null_a]; fresh_box].

(** The heap when work returns. *)
Definition hA' : heap :=
  hA ++ [mkObj (mkruntime_type Mut_r 1 []) [Iot 2]; fresh_box].

(** The activation of work just before and just after the call to peek. *)
Definition rΓpre : r_env :=
  mkr_env [Iot 5; Iot 2; Null_a; Iot 6; Iot 7; Null_a] [] [] [].
Definition rΓmid : r_env :=
  mkr_env [Iot 5; Iot 2; Null_a; Iot 6; Iot 7; Iot 6] [] [] [].

(** The activation of peek: receiver the fresh box, whose type argument,
    resolved at run time, is the mutable Person type. *)
Definition rΓpeek : r_env := mkr_env [Iot 7] [RClass Mut 1 []] [] [].
Definition rΓpeek' : r_env := mkr_env [Iot 7; Iot 6] [RClass Mut 1 []] [] [].

Definition rΓA' : r_env :=
  mkr_env [Iot 0; Iot 1; Iot 2; Iot 3; Iot 4; Iot 5; Iot 2] [] [] [].

Definition work_allocs : stmt :=
  SSeq (SLocal ROObject 2)
  (SSeq (SLocal MutPerson 3)
  (SSeq (SLocal MutBoxMutPerson 4)
  (SSeq (SLocal MutPerson 5)
  (SSeq (SNew 3 Mut_c 1 [] [2])
        (SNew 4 Mut_c 2 [MutPerson] [3]))))).

Lemma work_allocs_eval : eval_stmt CT rΓwork hA work_allocs OK rΓpre hmid.
Proof.
  unfold work_allocs, rΓwork, rΓpre, hmid, fresh_box, hA.
  ev_local. ev_local. ev_local. ev_local.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_New; reflexivity.
Qed.

(** The body of peek, run on the fresh box. *)
Lemma peek_body_eval :
  eval_stmt CT rΓpeek hmid (mbody_stmt (mbody peek)) OK rΓpeek' hmid.
Proof.
  cbn. unfold rΓpeek.
  ev_local.
  match goal with
  | |- eval_stmt _ ?r ?h _ _ _ _ =>
      refine (SBS_Assign CT r h 1 _ Null_a (Iot 6) eq_refl _)
  end.
  eapply EBS_Field; reflexivity.
Qed.

(** The nested call: peek runs on the fresh box and hands back the fresh
    Person. *)
Lemma peekCall_eval : eval_stmt CT rΓpre hmid peekCall OK rΓmid hmid.
Proof.
  unfold peekCall, rΓpre.
  eapply SBS_Call with (mdef := peek) (D := 2) (cy := 2)
    (rΓ' := rΓpeek) (rΓ'' := rΓpeek').
  - reflexivity.
  - reflexivity.
  - apply find_peek.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold callee_env. do 4 eexists.
    split; [reflexivity|]. split; [reflexivity|]. split; [split; reflexivity|].
    split; [apply rsi_refl | reflexivity].
  - apply peek_body_eval.
  - reflexivity.
  - reflexivity.
Qed.

(** The write itself. *)
Lemma work_write_eval :
  eval_stmt CT rΓmid hmid (SFldWrite 5 0 1) OK rΓmid hA'.
Proof.
  eapply SBS_FldWrite with (a := RDA);
    [reflexivity | reflexivity | reflexivity | apply name_is_rda
    | reflexivity | reflexivity | reflexivity].
Qed.

Lemma work_body_eval :
  eval_stmt CT rΓwork hA (mbody_stmt (mbody work)) OK rΓmid hA'.
Proof.
  change (mbody_stmt (mbody work)) with
    (SSeq (SLocal ROObject 2)
    (SSeq (SLocal MutPerson 3)
    (SSeq (SLocal MutBoxMutPerson 4)
    (SSeq (SLocal MutPerson 5)
    (SSeq (SNew 3 Mut_c 1 [] [2])
    (SSeq (SNew 4 Mut_c 2 [MutPerson] [3])
    (SSeq peekCall (SFldWrite 5 0 1)))))))).
  unfold rΓwork.
  ev_local. ev_local. ev_local. ev_local.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq; [exact peekCall_eval | exact work_write_eval].
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
    split; [reflexivity|]. split; [reflexivity|]. split; [split; reflexivity|].
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

(** The readonly-state theorem applied to the call to work, for any outcome
    of the call and any object of the entry heap. *)
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
            6 0 5 [] [] [2] sΓA rΓ' h' 5 3 3 work
            rdm_ct_clean_bounds config_A rsfp_A
            callW_typed Heval).
  - reflexivity.
  - reflexivity.
  - apply find_work.
  - left. reflexivity.
Qed.

(** The mutable Person c (location 2), which was passed to work, keeps its
    name. *)
Theorem callW_preserves_c : forall rΓ' h',
  eval_stmt CT rΓA hA callW OK rΓ' h' ->
  exists vals',
    runtime_getObj h' 2 = Some (mkObj (mkruntime_type Mut_r 1 []) vals') /\
    nth_error vals' 0 = Some (Iot 1).
Proof.
  intros rΓ' h' Heval.
  destruct (callW_preserves rΓ' h' Heval 2 Mut_r 1 [] [Iot 1] 0 eq_refl
              (or_intror name_is_rda))
    as (vals' & Hobj & Hnth).
  exists vals'. split; [exact Hobj|]. symmetry. exact Hnth.
Qed.

(** The immutable Person ip (location 3) keeps its name. *)
Theorem callW_preserves_ip : forall rΓ' h',
  eval_stmt CT rΓA hA callW OK rΓ' h' ->
  exists vals',
    runtime_getObj h' 3 = Some (mkObj (mkruntime_type Imm_r 1 []) vals') /\
    nth_error vals' 0 = Some (Iot 1).
Proof.
  intros rΓ' h' Heval.
  destruct (callW_preserves rΓ' h' Heval 3 Imm_r 1 [] [Iot 1] 0 eq_refl
              (or_intror name_is_rda))
    as (vals' & Hobj & Hnth).
  exists vals'. split; [exact Hobj|]. symmetry. exact Hnth.
Qed.

(** The immutable box ib (location 4) keeps its item. *)
Theorem callW_preserves_ib : forall rΓ' h',
  eval_stmt CT rΓA hA callW OK rΓ' h' ->
  exists vals',
    runtime_getObj h' 4 =
      Some (mkObj (mkruntime_type Imm_r 2 [RClass Imm 1 []]) vals') /\
    nth_error vals' 0 = Some (Iot 3).
Proof.
  intros rΓ' h' Heval.
  destruct (callW_preserves rΓ' h' Heval 4 Imm_r 2 [RClass Imm 1 []]
              [Iot 3] 0 eq_refl (or_intror item_is_rda))
    as (vals' & Hobj & Hnth).
  exists vals'. split; [exact Hobj|]. symmetry. exact Hnth.
Qed.

(** All three, for the run exhibited above. *)
Theorem callW_preserves_run :
  (exists vals',
     runtime_getObj hA' 2 = Some (mkObj (mkruntime_type Mut_r 1 []) vals') /\
     nth_error vals' 0 = Some (Iot 1)) /\
  (exists vals',
     runtime_getObj hA' 3 = Some (mkObj (mkruntime_type Imm_r 1 []) vals') /\
     nth_error vals' 0 = Some (Iot 1)) /\
  (exists vals',
     runtime_getObj hA' 4 =
       Some (mkObj (mkruntime_type Imm_r 2 [RClass Imm 1 []]) vals') /\
     nth_error vals' 0 = Some (Iot 3)).
Proof.
  split; [|split].
  - exact (callW_preserves_c rΓA' hA' callW_eval).
  - exact (callW_preserves_ip rΓA' hA' callW_eval).
  - exact (callW_preserves_ib rΓA' hA' callW_eval).
Qed.

(* ------------------DELIVERABLE 6: THE RUN DOES SOMETHING------------------*)

(** The call allocated two objects.  The fresh Person (location 6) held null
    after its allocation and holds the Person c (location 2) when work
    returns.  The fresh box (location 7) stores the mutable type argument and
    points to the fresh Person.  The call to peek stored into r (variable 5 of
    work's activation) the location of the fresh Person, the one the fresh
    box holds. *)
Theorem callW_not_vacuous :
  dom hA' = dom hA + 2 /\
  runtime_getObj hA 6 = None /\
  (exists o, runtime_getObj hmid 6 = Some o /\
             nth_error (fields_map o) 0 = Some Null_a) /\
  (exists o, runtime_getObj hA' 6 = Some o /\
             rt_type o = mkruntime_type Mut_r 1 [] /\
             nth_error (fields_map o) 0 = Some (Iot 2)) /\
  (exists o, runtime_getObj hA' 7 = Some o /\
             rt_type o = mkruntime_type Mut_r 2 [RClass Mut 1 []] /\
             nth_error (fields_map o) 0 = Some (Iot 6)) /\
  runtime_getVal rΓA 2 = Some (Iot 2) /\
  runtime_getVal rΓpre 5 = Some Null_a /\
  runtime_getVal rΓmid 5 = Some (Iot 6) /\
  runtime_getVal rΓpeek' (mreturn (mbody peek)) = Some (Iot 6) /\
  hmid <> hA' /\ hA <> hA'.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [eexists; split; reflexivity|].
  split; [eexists; split; [reflexivity | split; reflexivity]|].
  split; [eexists; split; [reflexivity | split; reflexivity]|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; discriminate.
Qed.

(** The slot written inside work is receiver-dependent assignable: it is one
    of the slots the theorem protects on objects of the entry heap.  The
    write is allowed because its target did not exist at entry. *)
Lemma written_slot_is_protected_kind :
  sf_assignability_rel CT 1 0 Final \/ sf_assignability_rel CT 1 0 RDA.
Proof. right. apply name_is_rda. Qed.

Print Assumptions rdm_ct_wf.
Print Assumptions rdm_ct_clean_bounds.
Print Assumptions peek_bound_in_scope.
Print Assumptions rdm_head_not_clean.
Print Assumptions config_A.
Print Assumptions main_typed.
Print Assumptions peekCall_eval.
Print Assumptions rsf_A.
Print Assumptions callW_eval.
Print Assumptions callW_preserves.
Print Assumptions callW_preserves_run.
Print Assumptions callW_not_vacuous.
