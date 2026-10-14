From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric
  GhostLabels GhostTyping GhostForget GhostFit GhostInvariant GhostOverride
  GhostCall GhostEntry ArgViews ArgTyping ArgFit ArgInvariant
  ArgCases ArgClean ArgOverride ArgCall ArgMain ArgEntry ArgRsf.

(** A worked example for the readonly-state theorem in which a class has
    [Mut] inside the bound of its type parameter.

    class 0: @RDM class Object {}
    class 1: @RDM class Cell extends Object {
       @Assignable @RO Object v;           // field 0
    }
    class 2: @RDM class D<X extends @RO Object> extends Object {
       @RDA X f;                           // field 0
    }
    class 3: @RDM class P<Y extends @RO Object> extends Object {
       @RDA Y g;                           // field 0
       // method 0, readonly-state
       @RS @RO Object look(@RO P<Y> this) {
           @RO Object o;      // var 1
           o = this.g;
           return o;
       }
    }
    class 4: @RDM class C<X extends @RO D<@Mut Cell>> extends P<X> {}
             // the bound mentions Mut
    class 5: @RDM class Runner extends Object {
       // method 1, readonly-state
       @RS @RO Object run(@RO Runner this, @RO Object y) {      // y is var 1
           @Mut Cell c;                            // var 2
           @Mut D<@Mut Cell> d0;                   // var 3
           @Imm C<@RO D<@Mut Cell>> bi;            // var 4
           @Mut C<@RO D<@Mut Cell>> bm;            // var 5
           @RO Object r;                           // var 6
           @RO Object r2;                          // var 7
           c  = new @Mut Cell(y);
           d0 = new @Mut D<@Mut Cell>(c);
           bi = new @Imm C<@RO D<@Mut Cell>>(d0);
           bm = new @Mut C<@RO D<@Mut Cell>>(d0);
           r  = bi.look();     // inherited from P, on the immutable one
           r2 = bm.look();     // and on the mutable one
           return y;
       }
    }

    main (variable 0 is the receiver, a @Mut Object; abstract-state mode):
      @Mut Object y0;                          // var 1
      @Mut Cell s0;                            // var 2
      @Mut D<@Mut Cell> pd;                    // var 3
      @Imm C<@RO D<@Mut Cell>> pc;             // var 4
      @Mut Runner rn;                          // var 5
      @RO Object x;                            // var 6
      y0 = new @Mut Object();
      s0 = new @Mut Cell(y0);
      pd = new @Mut D<@Mut Cell>(s0);
      pc = new @Imm C<@RO D<@Mut Cell>>(pd);
      rn = new @Mut Runner();
      x = rn.run(y0);                     // the call

    The objects pd and pc exist before the call.  The f of pd and the g of
    pc are receiver-dependent assignable, so the theorem says the call leaves
    them as they are. *)

(* ------------------THE PROGRAM------------------*)

Definition ROObject : qualified_type := TClass RO 0 [].
Definition MutObject : qualified_type := TClass Mut 0 [].
Definition MutCell : qualified_type := TClass Mut 1 [].
Definition tX : qualified_type := TVar TVSub ClassVar 0.
Definition RODMutCell : qualified_type := TClass RO 2 [MutCell].
Definition MutDMutCell : qualified_type := TClass Mut 2 [MutCell].
Definition ROPY : qualified_type := TClass RO 3 [tX].
Definition ImmC : qualified_type := TClass Imm 4 [RODMutCell].
Definition MutC : qualified_type := TClass Mut 4 [RODMutCell].
Definition RORunner : qualified_type := TClass RO 5 [].
Definition MutRunner : qualified_type := TClass Mut 5 [].

Definition ObjectDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 0; ctparams := [];
                     super := None |};
     body := {| fields := []; methods := [] |} |}.

Definition v_field : field_def :=
  {| assignability := Assignable; ftype := ROObject |}.

Definition CellDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 1; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := [v_field]; methods := [] |} |}.

Definition f_field : field_def :=
  {| assignability := RDA; ftype := TVar TVSub ClassVar 0 |}.

Definition DDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 2;
                     ctparams := [ROObject];
                     super := Some (0, []) |};
     body := {| fields := [f_field]; methods := [] |} |}.

Definition g_field : field_def :=
  {| assignability := RDA; ftype := TVar TVSub ClassVar 0 |}.

Definition look : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mqparams := 0;
          mret := ROObject;
          mname := 0;
          mreceiver := ROPY;
          mparams := [] |};
     mbody :=
       {| mbody_stmt :=
            SSeq (SLocal ROObject 1) (SVarAss 1 (EField 0 0));
          mreturn := 1 |} |}.

Definition PDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 3;
                     ctparams := [ROObject];
                     super := Some (0, []) |};
     body := {| fields := [g_field]; methods := [look] |} |}.

(** The class whose bound mentions Mut. *)
Definition CDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 4;
                     ctparams := [RODMutCell];
                     super := Some (3, [tX]) |};
     body := {| fields := []; methods := [] |} |}.

Definition lookCallImm : stmt := SCall 6 0 4 [] [] [].
Definition lookCallMut : stmt := SCall 7 0 5 [] [] [].

Definition run : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mqparams := 0;
          mret := ROObject;
          mname := 1;
          mreceiver := RORunner;
          mparams := [ROObject] |};
     mbody :=
       {| mbody_stmt :=
            SSeq (SLocal MutCell 2)
            (SSeq (SLocal MutDMutCell 3)
            (SSeq (SLocal ImmC 4)
            (SSeq (SLocal MutC 5)
            (SSeq (SLocal ROObject 6)
            (SSeq (SLocal ROObject 7)
            (SSeq (SNew 2 Mut_c 1 [] [1])
            (SSeq (SNew 3 Mut_c 2 [MutCell] [2])
            (SSeq (SNew 4 Imm_c 4 [RODMutCell] [3])
            (SSeq (SNew 5 Mut_c 4 [RODMutCell] [3])
            (SSeq lookCallImm lookCallMut))))))))));
          mreturn := 1 |} |}.

Definition RunnerDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 5; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := []; methods := [run] |} |}.

Definition CT : class_table :=
  [ObjectDef; CellDef; DDef; PDef; CDef; RunnerDef].

Definition prefix : stmt :=
  SSeq (SLocal MutObject 1)
  (SSeq (SLocal MutCell 2)
  (SSeq (SLocal MutDMutCell 3)
  (SSeq (SLocal ImmC 4)
  (SSeq (SLocal MutRunner 5)
  (SSeq (SLocal ROObject 6)
  (SSeq (SNew 1 Mut_c 0 [] [])
  (SSeq (SNew 2 Mut_c 1 [] [1])
  (SSeq (SNew 3 Mut_c 2 [MutCell] [2])
  (SSeq (SNew 4 Imm_c 4 [RODMutCell] [3])
        (SNew 5 Mut_c 5 [] [])))))))))).

Definition callR : stmt := SCall 6 1 5 [] [] [1].

Definition main : stmt := SSeq prefix callR.

Definition Δ0 : tv_env := mk_tv_env [] [] AbstractState 0.
Definition sΓ0 : s_env := [MutObject].
Definition sΓA : s_env :=
  [MutObject; MutObject; MutCell; MutDMutCell; ImmC; MutRunner; ROObject].

(** The bound environment of run: no type parameter is in scope. *)
Definition ΔR : tv_env := mk_tv_env [] [] ReadonlyState 0.

(** The bound environment of look: Y bounded by @RO Object. *)
Definition ΔL : tv_env := mk_tv_env [ROObject] [] ReadonlyState 0.

Definition sΓRun : s_env :=
  [RORunner; ROObject; MutCell; MutDMutCell; ImmC; MutC; ROObject; ROObject].

Definition sΓLook : s_env := [ROPY; ROObject].

(* ------------------SMALL TACTICS AND FACTS------------------*)

Ltac qs := (apply q_refl; discriminate) || apply q_rd || apply q_bot.

Lemma wf_plain : forall Δ top q0 C,
  C = 0 \/ C = 1 \/ C = 5 -> q0 <> Lost -> wf_stype CT Δ top (TClass q0 C []).
Proof.
  intros Δ top q0 C HC Hq.
  destruct HC as [-> | [-> | ->]];
    (eapply wfs_class;
       [reflexivity | right | reflexivity | constructor | constructor]);
    destruct q0; cbn; try qs; congruence.
Qed.

Lemma wf_use : forall Δ q0 C,
  C = 0 \/ C = 1 \/ C = 5 -> q0 <> Lost -> wf_stypeuse CT Δ (TClass q0 C []).
Proof. intros. apply wf_plain; auto. Qed.

Ltac wfp := apply wf_use; [tauto | discriminate].

Ltac refl_sub :=
  apply qualified_type_subtype_refl_class; [cbn; lia | discriminate].

Ltac qual_sub :=
  apply qtype_qual; [cbn; lia | qs | apply Forall2_targ_sub_refl].

Ltac lf := cbn; intuition discriminate.

(** Any Cell is a readonly Object. *)
Lemma sub_Cell_ROObject : forall Δ q0,
  qualified_type_subtype CT Δ (TClass q0 1 []) ROObject.
Proof.
  intros Δ q0. eapply qtype_trans.
  - apply qtype_hier with (D := 0) (Vs := []).
    eapply si_step; [reflexivity|]. cbn. apply si_refl.
  - apply qtype_qual; [cbn; lia | apply q_rd | constructor].
Qed.

(** A readonly D of anything is a readonly Object. *)
Lemma sub_ROD_ROObject : forall Δ Ts,
  qualified_type_subtype CT Δ (TClass RO 2 Ts) ROObject.
Proof.
  intros Δ Ts. apply qtype_hier with (D := 0) (Vs := []).
  eapply si_step; [reflexivity|]. cbn. apply si_refl.
Qed.

(** Inside C, X is below its bound @RO D<@Mut Cell> and hence a readonly
    Object. *)
Lemma sub_tX_ROObject : forall mt,
  qualified_type_subtype CT (mk_tv_env [RODMutCell] [] mt 0) tX ROObject.
Proof.
  intros mt. eapply qtype_trans.
  - apply qtype_var_bound with (B := RODMutCell). reflexivity.
  - apply sub_ROD_ROObject.
Qed.

(** A D of mutable Cells, with any head but the unknown one. *)
Lemma wf_DMutCell : forall Δ top q0,
  q0 <> Lost -> wf_stype CT Δ top (TClass q0 2 [MutCell]).
Proof.
  intros Δ top q0 Hq.
  eapply wfs_class; [reflexivity | right | reflexivity | |].
  - destruct q0; cbn; try qs; congruence.
  - constructor; [apply wf_plain; [tauto | discriminate] | constructor].
  - constructor; [|constructor]. intros m.
    destruct q0; cbn; apply sub_Cell_ROObject.
Qed.

(** What the bound of C reads as for the instantiation C<@RO D<@Mut Cell>>,
    seen through an immutable head and through a mutable head: in both cases
    it stays @RO D<@Mut Cell>, with its Mut. *)
Lemma C_bound_read :
  member_type AbstractState Imm [RODMutCell] [] [] RODMutCell = RODMutCell /\
  member_type AbstractState Mut [RODMutCell] [] [] RODMutCell = RODMutCell.
Proof. split; reflexivity. Qed.

(** A C<@RO D<@Mut Cell>>, immutable or mutable.  The argument is compared
    with the bound, in every mode. *)
Lemma wf_C : forall Δ top q0,
  q0 = Imm \/ q0 = Mut -> wf_stype CT Δ top (TClass q0 4 [RODMutCell]).
Proof.
  intros Δ top q0 Hq.
  eapply wfs_class; [reflexivity | right | reflexivity | |].
  - destruct Hq as [-> | ->]; cbn; qs.
  - constructor; [apply wf_DMutCell; discriminate | constructor].
  - constructor; [|constructor]. intros m.
    destruct Hq as [-> | ->]; cbn; refl_sub.
Qed.

(** The declared receiver of look. *)
Lemma wf_ROPY_look : wf_stypeuse CT ΔL ROPY.
Proof.
  eapply wfs_class; [reflexivity | right; cbn; qs | reflexivity | |].
  - constructor; [|constructor].
    eapply wfs_var; [reflexivity | left; reflexivity].
  - constructor; [|constructor]. intros m. cbn.
    apply qtype_var_bound. reflexivity.
Qed.

Lemma wf_ROObject : forall Δ, wf_stypeuse CT Δ ROObject.
Proof. intros. wfp. Qed.
Lemma wf_MutObject : forall Δ, wf_stypeuse CT Δ MutObject.
Proof. intros. wfp. Qed.
Lemma wf_MutCell : forall Δ, wf_stypeuse CT Δ MutCell.
Proof. intros. wfp. Qed.
Lemma wf_RORunner : forall Δ, wf_stypeuse CT Δ RORunner.
Proof. intros. wfp. Qed.
Lemma wf_MutRunner : forall Δ, wf_stypeuse CT Δ MutRunner.
Proof. intros. wfp. Qed.
Lemma wf_MutDMutCell : forall Δ, wf_stypeuse CT Δ MutDMutCell.
Proof. intros. apply wf_DMutCell. discriminate. Qed.
Lemma wf_ImmC : forall Δ, wf_stypeuse CT Δ ImmC.
Proof. intros. apply wf_C. left. reflexivity. Qed.
Lemma wf_MutC : forall Δ, wf_stypeuse CT Δ MutC.
Proof. intros. apply wf_C. right. reflexivity. Qed.

Create HintDb edb.
Local Hint Resolve wf_ROObject wf_MutObject wf_MutCell wf_RORunner
  wf_MutRunner wf_MutDMutCell wf_ImmC wf_MutC wf_ROPY_look : edb.

Ltac wfenv :=
  split; [cbn; lia |
          cbn; repeat (apply Forall_cons; [solve [auto with edb]|]);
          apply Forall_nil].

Lemma collect_Object : CollectFields CT 0 [].
Proof. eapply CF_Object; reflexivity. Qed.

Lemma collect_Cell : CollectFields CT 1 [v_field].
Proof.
  change (CollectFields CT 1
            (map (subst_field []) [] ++ Syntax.fields (body CellDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma collect_D : CollectFields CT 2 [f_field].
Proof.
  change (CollectFields CT 2
            (map (subst_field []) [] ++ Syntax.fields (body DDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma collect_P : CollectFields CT 3 [g_field].
Proof.
  change (CollectFields CT 3
            (map (subst_field []) [] ++ Syntax.fields (body PDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

(** C has the one field it inherits from P, typed by C's own parameter. *)
Lemma collect_C : CollectFields CT 4 [g_field].
Proof.
  change (CollectFields CT 4
            (map (subst_field [tX]) [g_field] ++ Syntax.fields (body CDef))).
  eapply CF_Inherit; try reflexivity. apply collect_P.
Qed.

Lemma collect_Runner : CollectFields CT 5 [].
Proof.
  change (CollectFields CT 5
            (map (subst_field []) [] ++ Syntax.fields (body RunnerDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

(** Field 0 of D, f, is receiver-dependent assignable. *)
Lemma f_is_rda : sf_assignability_rel CT 2 0 RDA.
Proof.
  exists f_field. split; [|reflexivity].
  eapply FL_Found; [apply collect_D | reflexivity].
Qed.

(** Field 0 of C, the inherited g, is receiver-dependent assignable. *)
Lemma g_is_rda : sf_assignability_rel CT 4 0 RDA.
Proof.
  exists g_field. split; [|reflexivity].
  eapply FL_Found; [apply collect_C | reflexivity].
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

(** A call of look on a C finds the method declared in P. *)
Lemma find_look_C : FindMethodWithName CT 4 0 3 look.
Proof.
  eapply FOM_Super; [reflexivity | reflexivity | reflexivity | reflexivity |].
  apply find_look.
Qed.

Lemma find_run : FindMethodWithName CT 5 1 5 run.
Proof. eapply FOM_Here; reflexivity. Qed.

(** In readonly-state code a C<@RO D<@Mut Cell>>, whatever its head, is at P
    a P<@RO D<@Mut Cell>>: the Mut inside the argument is kept. *)
Lemma super_C_P : forall mt qh,
  super_inst CT mt qh 4 [RODMutCell] 3 [RODMutCell].
Proof.
  intros mt qh. eapply si_step; [reflexivity|]. cbn. apply si_refl.
Qed.

Lemma sub_C_ROP : forall Δ q0,
  qualified_type_subtype CT Δ (TClass q0 4 [RODMutCell])
    (TClass RO 3 [RODMutCell]).
Proof.
  intros Δ q0. eapply qtype_trans.
  - apply qtype_hier. apply super_C_P.
  - apply qtype_qual; [cbn; lia | apply q_rd | apply Forall2_targ_sub_refl].
Qed.

Ltac ty_local :=
  eapply ST_Local;
    [wfenv | solve [auto with edb] | reflexivity | reflexivity | reflexivity].

Ltac ty_seq := eapply ST_Seq; [wfenv | |].

Ltac fl H := eapply FL_Found; [apply H | reflexivity].

Ltac no_override :=
  let def := fresh "def" in
  let Hfind := fresh "Hfind" in
  let Hsuper := fresh "Hsuper" in
  let Hfm := fresh "Hfm" in
  intros def ? ? ? ? ? Hfind Hsuper Hfm _;
  cbn in Hfind; injection Hfind as <-; cbn in Hsuper;
  injection Hsuper as <- <-;
  exfalso; eapply no_method_in_Object; eauto.

(* ------------------DELIVERABLE 1: THE CLASS TABLE------------------*)

(** *** P.look *)

(** o = this.g: through the readonly receiver the field reads as the bare
    variable Y, and Y is below its bound @RO Object. *)
Lemma look_body_typed :
  stmt_typing CT ΔL [ROPY] ReadonlyState (mbody_stmt (mbody look)) sΓLook.
Proof.
  cbn. unfold sΓLook.
  ty_seq; [ty_local|].
  cbn.
  eapply ST_VarAss with (Tx := ROObject) (Te := tX);
    [wfenv | | discriminate | reflexivity | ].
  - eapply ET_Field with (x := 0) (T := ROPY) (qx := RO) (C := 3)
      (Ts := [tX]) (fDef := g_field);
      [wfenv | reflexivity | reflexivity | fl collect_P].
  - apply qtype_var_bound. reflexivity.
Qed.

(** The signature of look has no mutable position: the receiver is
    @RO P<Y>, and Y is read as @RO Object. *)
Lemma look_no_mutable_roots :
  signature_has_no_mutable_roots ΔL (msignature look).
Proof.
  split; [|constructor].
  cbn. constructor; [discriminate|].
  constructor; [|constructor].
  eapply nm_var; [reflexivity|]. constructor; [discriminate | constructor].
Qed.

Lemma wf_look : wf_method CT 3 look.
Proof.
  unfold wf_method.
  change (method_tv_env CT 3 (msignature look)) with ΔL.
  split; [apply receiver_plain_ok; left; exists RO; reflexivity|].
  split; [constructor|].
  split; [apply wf_ROObject|].
  split.
  { exists sΓLook, ROObject. split; [|split].
    - apply look_body_typed.
    - reflexivity.
    - refl_sub. }
  split; [no_override|].
  intros _. apply look_no_mutable_roots.
Qed.

(** *** Runner.run *)

(** c = new @Mut Cell(y). *)
Lemma run_new_Cell_typed :
  stmt_typing CT ΔR sΓRun ReadonlyState (SNew 2 Mut_c 1 [] [1]) sΓRun.
Proof.
  unfold sΓRun, ΔR.
  eapply ST_New with (Tx := MutCell) (argtypes := [ROObject]);
    [wfenv | reflexivity | reflexivity | reflexivity | discriminate
    | reflexivity | apply wf_MutCell | constructor | constructor
    | apply collect_Cell | | ].
  - constructor; [|constructor]; cbn.
    split; [refl_sub | lf].
  - cbn. refl_sub.
Qed.

(** d0 = new @Mut D<@Mut Cell>(c). *)
Lemma run_new_D_typed :
  stmt_typing CT ΔR sΓRun ReadonlyState (SNew 3 Mut_c 2 [MutCell] [2]) sΓRun.
Proof.
  unfold sΓRun, ΔR.
  eapply ST_New with (Tx := MutDMutCell) (argtypes := [MutCell]);
    [wfenv | reflexivity | reflexivity | reflexivity | discriminate
    | reflexivity | apply wf_MutDMutCell | | | apply collect_D | | ].
  - constructor; [lf | constructor].
  - constructor; [|constructor]. cbn.
    split; [lf | intros m; apply sub_Cell_ROObject].
  - constructor; [|constructor]; cbn.
    split; [refl_sub | lf].
  - cbn. refl_sub.
Qed.

(** bi = new @Imm C<@RO D<@Mut Cell>>(d0), inside readonly-state code: an
    immutable object of the class whose bound mentions Mut.  The type
    argument is compared with that bound in every mode.  The initialiser d0,
    a @Mut D<@Mut Cell>, fills the inherited field g, which for this object
    reads @RO D<@Mut Cell>. *)
Lemma run_new_ImmC_typed :
  stmt_typing CT ΔR sΓRun ReadonlyState
    (SNew 4 Imm_c 4 [RODMutCell] [3]) sΓRun.
Proof.
  unfold sΓRun, ΔR.
  eapply ST_New with (Tx := ImmC) (argtypes := [MutDMutCell]);
    [wfenv | reflexivity | reflexivity | reflexivity | discriminate
    | reflexivity | apply wf_ImmC | | | apply collect_C | | ].
  - constructor; [lf | constructor].
  - constructor; [|constructor]; cbn.
    split; [lf | intros m; refl_sub].
  - constructor; [|constructor]; cbn.
    split; [qual_sub | lf].
  - cbn. refl_sub.
Qed.

(** bm = new @Mut C<@RO D<@Mut Cell>>(d0): the mutable one. *)
Lemma run_new_MutC_typed :
  stmt_typing CT ΔR sΓRun ReadonlyState
    (SNew 5 Mut_c 4 [RODMutCell] [3]) sΓRun.
Proof.
  unfold sΓRun, ΔR.
  eapply ST_New with (Tx := MutC) (argtypes := [MutDMutCell]);
    [wfenv | reflexivity | reflexivity | reflexivity | discriminate
    | reflexivity | apply wf_MutC | | | apply collect_C | | ].
  - constructor; [lf | constructor].
  - constructor; [|constructor]; cbn.
    split; [lf | intros m; refl_sub].
  - constructor; [|constructor]; cbn.
    split; [qual_sub | lf].
  - cbn. refl_sub.
Qed.

(** r = bi.look(), in readonly-state code: the method is inherited from P;
    the immutable C<@RO D<@Mut Cell>> is passed as the declared receiver
    @RO P<Y>, which for this object reads @RO P<@RO D<@Mut Cell>>. *)
Lemma lookCallImm_typed :
  stmt_typing CT ΔR sΓRun ReadonlyState lookCallImm sΓRun.
Proof.
  unfold lookCallImm, sΓRun, ΔR.
  eapply ST_Call with (Tx := ROObject) (Ty := ImmC)
    (argtypes := [])
    (qy := Imm) (C := 4) (Ts := [RODMutCell]) (D := 3)
    (Vs := [RODMutCell])
    (mdef := look);
    [wfenv | reflexivity | reflexivity | reflexivity | reflexivity
    | apply find_look_C | apply super_C_P | discriminate | constructor
    | constructor | reflexivity | constructor | | | constructor
    | apply method_subtyping_refl | reflexivity | constructor | recv_known].
  - cbn. refl_sub.
  - cbn. split; [apply sub_C_ROP | lf].
Qed.

(** r2 = bm.look(): the same on the mutable one. *)
Lemma lookCallMut_typed :
  stmt_typing CT ΔR sΓRun ReadonlyState lookCallMut sΓRun.
Proof.
  unfold lookCallMut, sΓRun, ΔR.
  eapply ST_Call with (Tx := ROObject) (Ty := MutC)
    (argtypes := [])
    (qy := Mut) (C := 4) (Ts := [RODMutCell]) (D := 3)
    (Vs := [RODMutCell])
    (mdef := look);
    [wfenv | reflexivity | reflexivity | reflexivity | reflexivity
    | apply find_look_C | apply super_C_P | discriminate | constructor
    | constructor | reflexivity | constructor | | | constructor
    | apply method_subtyping_refl | reflexivity | constructor | recv_known].
  - cbn. refl_sub.
  - cbn. split; [apply sub_C_ROP | lf].
Qed.

Lemma run_body_typed :
  stmt_typing CT ΔR [RORunner; ROObject] ReadonlyState
    (mbody_stmt (mbody run)) sΓRun.
Proof.
  cbn. unfold ΔR.
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  cbn.
  ty_seq; [apply run_new_Cell_typed|].
  ty_seq; [apply run_new_D_typed|].
  ty_seq; [apply run_new_ImmC_typed|].
  ty_seq; [apply run_new_MutC_typed|].
  ty_seq; [apply lookCallImm_typed|].
  apply lookCallMut_typed.
Qed.

Lemma wf_run : wf_method CT 5 run.
Proof.
  unfold wf_method.
  change (method_tv_env CT 5 (msignature run)) with ΔR.
  split; [apply receiver_plain_ok; left; exists RO; reflexivity|].
  split; [constructor|].
  split; [apply wf_ROObject|].
  split.
  { exists sΓRun, ROObject. split; [|split].
    - apply run_body_typed.
    - reflexivity.
    - refl_sub. }
  split; [no_override|].
  intros _. split.
  - constructor; [discriminate | constructor].
  - constructor; [|constructor].
    constructor; [discriminate | constructor].
Qed.

(** *** The classes *)

Ltac wf_other sc ss sd :=
  eapply WFOtherDef with (superC := sc) (Ss := ss) (super_def := sd);
    [reflexivity | cbn; lia | reflexivity
    | cbn | cbn | cbn | cbn | cbn | cbn | cbn | cbn].

Lemma wf_ObjectDef : wf_class CT ObjectDef.
Proof. apply WFObjectDef; reflexivity. Qed.

Lemma wf_CellDef : wf_class CT CellDef.
Proof.
  wf_other 0 (@nil qualified_type) ObjectDef.
  - constructor.
  - wfp.
  - constructor.
  - constructor.
  - left. reflexivity.
  - constructor; [unfold wf_field; cbn; wfp | constructor].
  - constructor.
  - constructor.
Qed.

Lemma wf_DDef : wf_class CT DDef.
Proof.
  wf_other 0 (@nil qualified_type) ObjectDef.
  - constructor; [|constructor]. split; [exact I | wfp].
  - wfp.
  - constructor.
  - constructor.
  - left. reflexivity.
  - constructor; [|constructor]; unfold wf_field; cbn.
    eapply wfs_var; [reflexivity|]. right. discriminate.
  - constructor.
  - constructor.
Qed.

Lemma wf_PDef : wf_class CT PDef.
Proof.
  wf_other 0 (@nil qualified_type) ObjectDef.
  - constructor; [|constructor]. split; [exact I | wfp].
  - wfp.
  - constructor.
  - constructor.
  - left. reflexivity.
  - constructor; [|constructor]; unfold wf_field; cbn.
    eapply wfs_var; [reflexivity|]. right. discriminate.
  - constructor; [apply wf_look | constructor].
  - constructor; [intros [] | constructor].
Qed.

(** The class with Mut in its bound is a well-formed class.  Its bound
    @RO D<@Mut Cell> is a well-formed type, and its superclass P<X> is well
    formed because X, read through that bound, is a readonly Object. *)
Lemma wf_CDef : wf_class CT CDef.
Proof.
  wf_other 3 [tX] PDef.
  - constructor; [|constructor].
    split; [exact I | apply wf_DMutCell; discriminate].
  - eapply wfs_class; [reflexivity | right; cbn; qs | reflexivity | |].
    + constructor; [|constructor].
      eapply wfs_var; [reflexivity | left; reflexivity].
    + constructor; [|constructor]. intros m. cbn. apply sub_tX_ROObject.
  - constructor; [exact I | constructor].
  - constructor; [|constructor]. cbn.
    split; [lf | intros m; apply sub_tX_ROObject].
  - left. reflexivity.
  - constructor.
  - constructor.
  - constructor.
Qed.

Lemma wf_RunnerDef : wf_class CT RunnerDef.
Proof.
  wf_other 0 (@nil qualified_type) ObjectDef.
  - constructor.
  - wfp.
  - constructor.
  - constructor.
  - left. reflexivity.
  - constructor.
  - constructor; [apply wf_run | constructor].
  - constructor; [intros [] | constructor].
Qed.

Theorem mutbound_ct_wf : wf_class_table CT.
Proof.
  unfold wf_class_table. split; [|split; [|split]].
  - constructor; [apply wf_ObjectDef|].
    constructor; [apply wf_CellDef|].
    constructor; [apply wf_DDef|].
    constructor; [apply wf_PDef|].
    constructor; [apply wf_CDef|].
    constructor; [apply wf_RunnerDef | constructor].
  - exists ObjectDef. split; reflexivity.
  - intros i def Hi Hfind.
    destruct i as [|[|[|[|[|[|i]]]]]]; try lia; cbn in Hfind;
      try (injection Hfind as <-; discriminate).
    destruct i; discriminate.
  - intros i def Hfind.
    destruct i as [|[|[|[|[|[|i]]]]]]; cbn in Hfind;
      try (injection Hfind as <-; reflexivity).
    destruct i; discriminate.
Qed.

(* ------------------DELIVERABLE 2: THE CONDITIONS THE THEOREM ASKS FOR------------------*)

(** There are two readonly-state methods.  No type parameter is in scope of
    run.  In scope of look there is one, with the bound @RO Object.  The
    bound of C, the one with Mut, is in scope of no method: C declares
    none. *)
Theorem mutbound_ct_clean_bounds : clean_bounds_ct CT.
Proof.
  intros C def md Hfind Hin _.
  destruct C as [|[|[|[|[|[|C]]]]]]; cbn in Hfind;
    try (destruct C; discriminate);
    injection Hfind as <-; cbn in Hin; try (destruct Hin; fail).
  - destruct Hin as [<- | []].
    intros o n B Hb.
    destruct o; [destruct n as [|[|n]] | destruct n]; cbn in Hb;
      try discriminate.
    injection Hb as <-. split; [exact I|].
    apply nm_class; [discriminate | constructor].
  - destruct Hin as [<- | []].
    intros o n B Hb. destruct o; destruct n; discriminate.
Qed.

(* ------------------DELIVERABLE 3: THE EARLIER CONDITION FAILS HERE------------------*)

(** The bound of C's type parameter. *)
Lemma C_bound :
  find_class CT 4 = Some CDef /\
  nth_error (ctparams (signature CDef)) 0 = Some (TClass RO 2 [TClass Mut 1 []]).
Proof. split; reflexivity. Qed.

(** That bound has a mutable position. *)
Lemma C_bound_has_mut : forall Δ, ~ no_mut Δ RODMutCell.
Proof.
  intros Δ H. inversion H as [q0 C Ts _ Hargs | | | |]; subst.
  inversion Hargs as [|T Ts' HT _]; subst.
  inversion HT as [q1 C1 Ts1 Hq _ | | | |]; subst.
  apply Hq. reflexivity.
Qed.

(** So the earlier condition, that no class type-parameter bound mentions
    Mut, is false for this class table. *)
Theorem mutbound_ct_not_bounds_nm : ~ class_bounds_nm CT.
Proof.
  intros H.
  destruct (H 4 CDef 0 RODMutCell eq_refl eq_refl) as [_ Hnm].
  exact (C_bound_has_mut _ Hnm).
Qed.


(* ------------------DELIVERABLE 4: CONFIGURATION, TYPING, RUN------------------*)

Lemma prefix_typed : stmt_typing CT Δ0 sΓ0 AbstractState prefix sΓA.
Proof.
  unfold prefix, sΓA, sΓ0, Δ0.
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  cbn.
  (* y0 = new @Mut Object() *)
  ty_seq.
  { eapply ST_New with (Tx := MutObject) (argtypes := []) (fds := []);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutObject | constructor | constructor
      | apply collect_Object | constructor | ].
    cbn. refl_sub. }
  (* s0 = new @Mut Cell(y0) *)
  ty_seq.
  { eapply ST_New with (Tx := MutCell) (argtypes := [MutObject]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutCell | constructor | constructor
      | apply collect_Cell | | ].
    - constructor; [|constructor]; cbn.
      split; [qual_sub | lf].
    - cbn. refl_sub. }
  (* pd = new @Mut D<@Mut Cell>(s0) *)
  ty_seq.
  { eapply ST_New with (Tx := MutDMutCell) (argtypes := [MutCell]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutDMutCell | | | apply collect_D | | ].
    - constructor; [lf | constructor].
    - constructor; [|constructor]. cbn.
      split; [lf | intros m; apply sub_Cell_ROObject].
    - constructor; [|constructor]; cbn.
      split; [refl_sub | lf].
    - cbn. refl_sub. }
  (* pc = new @Imm C<@RO D<@Mut Cell>>(pd) *)
  ty_seq.
  { eapply ST_New with (Tx := ImmC) (argtypes := [MutDMutCell]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_ImmC | | | apply collect_C | | ].
    - constructor; [lf | constructor].
    - constructor; [|constructor]; cbn.
      split; [lf | intros m; refl_sub].
    - constructor; [|constructor]; cbn.
      split; [qual_sub | lf].
    - cbn. refl_sub. }
  (* rn = new @Mut Runner() *)
  eapply ST_New with (Tx := MutRunner) (argtypes := []) (fds := []);
    [wfenv | reflexivity | reflexivity | reflexivity | discriminate
    | reflexivity | apply wf_MutRunner | constructor | constructor
    | apply collect_Runner | constructor | ].
  cbn. refl_sub.
Qed.

(** The call, made from abstract-state code. *)
Lemma callR_typed : stmt_typing CT Δ0 sΓA AbstractState callR sΓA.
Proof.
  unfold callR, sΓA, Δ0.
  eapply ST_Call with (Tx := ROObject) (Ty := MutRunner)
    (argtypes := [MutObject])
    (qy := Mut) (C := 5) (Ts := []) (D := 5) (Vs := [])
    (mdef := run);
    [wfenv | reflexivity | reflexivity | reflexivity | reflexivity
    | apply find_run | apply si_refl | discriminate | | | reflexivity
    | | | | | apply method_rs_as | reflexivity | constructor | recv_known].
  - constructor.
  - constructor.
  - constructor.
  - cbn. refl_sub.
  - cbn. split; [qual_sub | lf].
  - constructor; [|constructor]; cbn.
    split; [qual_sub | lf].
Qed.

Lemma main_typed : stmt_typing CT Δ0 sΓ0 AbstractState main sΓA.
Proof.
  unfold main.
  eapply ST_Seq; [unfold sΓ0; wfenv | apply prefix_typed | apply callR_typed].
Qed.

(** The states.  Location 0 is main's receiver, 1 is y0, 2 is the Cell s0,
    3 is the D pd that holds s0, 4 is the immutable C pc that holds pd, 5 is
    the Runner. *)
Definition rΓ0 : r_env := mkr_env [Iot 0] [] [] [].
Definition h0 : heap := [mkObj (mkruntime_type Mut_r 0 []) []].

Definition rΓA : r_env :=
  mkr_env [Iot 0; Iot 1; Iot 2; Iot 3; Iot 4; Iot 5; Null_a] [] [] [].

Definition rMutCell : rtype := RClass Mut 1 [].
Definition rRODMutCell : rtype := RClass RO 2 [rMutCell].

Definition hA : heap :=
  [ mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 1 []) [Iot 1];
    mkObj (mkruntime_type Mut_r 2 [rMutCell]) [Iot 2];
    mkObj (mkruntime_type Imm_r 4 [rRODMutCell]) [Iot 3];
    mkObj (mkruntime_type Mut_r 5 []) [] ].

Ltac ev_local := eapply SBS_Seq; [apply SBS_Local; reflexivity|]; cbn.
Ltac ev_new := eapply SBS_Seq; [eapply SBS_New; reflexivity|]; cbn.

Lemma prefix_eval : eval_stmt CT rΓ0 h0 prefix OK rΓA hA.
Proof.
  unfold prefix, rΓ0, h0.
  ev_local. ev_local. ev_local. ev_local. ev_local. ev_local.
  ev_new. ev_new. ev_new. ev_new.
  eapply SBS_New; reflexivity.
Qed.

Lemma initial_config : wf_r_config CT Δ0 sΓ0 rΓ0 h0.
Proof.
  unfold Δ0, sΓ0, rΓ0, h0.
  refine (conj mutbound_ct_wf
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

(** The configuration just before the call is well formed. *)
Theorem config_A : wf_r_config CT Δ0 sΓA rΓA hA.
Proof.
  eapply preservation_pico;
    eauto using prefix_eval, initial_config, prefix_typed.
Qed.

(** It also satisfies its bounds in the protected reading.  Here that says
    something: the heap now holds the immutable object pc of the class whose
    bound mentions Mut.  No condition on the bounds of the class table is
    used to get here. *)
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

(** The activation of run: receiver the Runner, argument y0. *)
Definition rΓrun : r_env := mkr_env [Iot 5; Iot 1] [] [] [].

(** The four fresh objects: a Cell at location 6, a D at location 7 that
    holds it, an immutable C at location 8 and a mutable C at location 9
    that both hold the D. *)
Definition fresh_Cell : Obj := mkObj (mkruntime_type Mut_r 1 []) [Iot 1].
Definition fresh_D : Obj :=
  mkObj (mkruntime_type Mut_r 2 [rMutCell]) [Iot 6].
Definition fresh_ImmC : Obj :=
  mkObj (mkruntime_type Imm_r 4 [rRODMutCell]) [Iot 7].
Definition fresh_MutC : Obj :=
  mkObj (mkruntime_type Mut_r 4 [rRODMutCell]) [Iot 7].

(** The heap when run returns; the two calls to look leave it as it is. *)
Definition hA' : heap := hA ++ [fresh_Cell; fresh_D; fresh_ImmC; fresh_MutC].

(** The activation of run before the first call to look, between the two
    calls, and after the second. *)
Definition rΓpre : r_env :=
  mkr_env [Iot 5; Iot 1; Iot 6; Iot 7; Iot 8; Iot 9; Null_a; Null_a] [] [] [].
Definition rΓmid : r_env :=
  mkr_env [Iot 5; Iot 1; Iot 6; Iot 7; Iot 8; Iot 9; Iot 7; Null_a] [] [] [].
Definition rΓend : r_env :=
  mkr_env [Iot 5; Iot 1; Iot 6; Iot 7; Iot 8; Iot 9; Iot 7; Iot 7] [] [] [].

(** The activation of look on a receiver at location l: the class argument
    of P is the object's own type argument, carried up from C. *)
Definition rΓlook (l : Loc) : r_env := mkr_env [Iot l] [rRODMutCell] [] [].
Definition rΓlook' (l : Loc) : r_env :=
  mkr_env [Iot l; Iot 7] [rRODMutCell] [] [].

Definition rΓA' : r_env :=
  mkr_env [Iot 0; Iot 1; Iot 2; Iot 3; Iot 4; Iot 5; Iot 1] [] [] [].

Definition run_allocs : stmt :=
  SSeq (SLocal MutCell 2)
  (SSeq (SLocal MutDMutCell 3)
  (SSeq (SLocal ImmC 4)
  (SSeq (SLocal MutC 5)
  (SSeq (SLocal ROObject 6)
  (SSeq (SLocal ROObject 7)
  (SSeq (SNew 2 Mut_c 1 [] [1])
  (SSeq (SNew 3 Mut_c 2 [MutCell] [2])
  (SSeq (SNew 4 Imm_c 4 [RODMutCell] [3])
        (SNew 5 Mut_c 4 [RODMutCell] [3]))))))))).

Lemma run_allocs_eval : eval_stmt CT rΓrun hA run_allocs OK rΓpre hA'.
Proof.
  unfold run_allocs, rΓrun, rΓpre, hA', fresh_Cell, fresh_D, fresh_ImmC,
    fresh_MutC, hA.
  ev_local. ev_local. ev_local. ev_local. ev_local. ev_local.
  ev_new. ev_new. ev_new.
  eapply SBS_New; reflexivity.
Qed.

(** The body of look, run on either of the two fresh C objects. *)
Lemma look_body_eval : forall l,
  l = 8 \/ l = 9 ->
  eval_stmt CT (rΓlook l) hA' (mbody_stmt (mbody look)) OK (rΓlook' l) hA'.
Proof.
  intros l Hl. cbn. unfold rΓlook.
  ev_local.
  match goal with
  | |- eval_stmt _ ?r ?h _ _ _ _ =>
      refine (SBS_Assign CT r h 1 _ Null_a (Iot 7) eq_refl _)
  end.
  destruct Hl as [-> | ->]; eapply EBS_Field; reflexivity.
Qed.

(** The first nested call: look, found in P, runs on the immutable C and
    hands back the D it holds. *)
Lemma lookCallImm_eval : eval_stmt CT rΓpre hA' lookCallImm OK rΓmid hA'.
Proof.
  unfold lookCallImm, rΓpre.
  eapply SBS_Call with (mdef := look) (D := 3) (cy := 4)
    (rΓ' := rΓlook 8) (rΓ'' := rΓlook' 8).
  - reflexivity.
  - reflexivity.
  - apply find_look_C.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold callee_env. do 4 eexists.
    split; [reflexivity|]. split; [reflexivity|]. split; [split; reflexivity|].
    split; [|reflexivity].
    cbn. eapply rsi_step; [reflexivity|]. cbn. apply rsi_refl.
  - apply look_body_eval. left. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** The second: the same on the mutable C. *)
Lemma lookCallMut_eval : eval_stmt CT rΓmid hA' lookCallMut OK rΓend hA'.
Proof.
  unfold lookCallMut, rΓmid.
  eapply SBS_Call with (mdef := look) (D := 3) (cy := 4)
    (rΓ' := rΓlook 9) (rΓ'' := rΓlook' 9).
  - reflexivity.
  - reflexivity.
  - apply find_look_C.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold callee_env. do 4 eexists.
    split; [reflexivity|]. split; [reflexivity|]. split; [split; reflexivity|].
    split; [|reflexivity].
    cbn. eapply rsi_step; [reflexivity|]. cbn. apply rsi_refl.
  - apply look_body_eval. right. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma run_body_eval :
  eval_stmt CT rΓrun hA (mbody_stmt (mbody run)) OK rΓend hA'.
Proof.
  change (mbody_stmt (mbody run)) with
    (SSeq (SLocal MutCell 2)
    (SSeq (SLocal MutDMutCell 3)
    (SSeq (SLocal ImmC 4)
    (SSeq (SLocal MutC 5)
    (SSeq (SLocal ROObject 6)
    (SSeq (SLocal ROObject 7)
    (SSeq (SNew 2 Mut_c 1 [] [1])
    (SSeq (SNew 3 Mut_c 2 [MutCell] [2])
    (SSeq (SNew 4 Imm_c 4 [RODMutCell] [3])
    (SSeq (SNew 5 Mut_c 4 [RODMutCell] [3])
    (SSeq lookCallImm lookCallMut))))))))))).
  unfold rΓrun.
  ev_local. ev_local. ev_local. ev_local. ev_local. ev_local.
  ev_new. ev_new. ev_new. ev_new.
  eapply SBS_Seq; [exact lookCallImm_eval | exact lookCallMut_eval].
Qed.

(** The call to run has a normal run: the body, with both allocations of C
    and both calls to look, executes to the end. *)
Theorem callR_eval : eval_stmt CT rΓA hA callR OK rΓA' hA'.
Proof.
  unfold callR, rΓA.
  eapply SBS_Call with (mdef := run) (D := 5) (cy := 5)
    (rΓ' := rΓrun) (rΓ'' := rΓend).
  - reflexivity.
  - reflexivity.
  - apply find_run.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold callee_env. do 4 eexists.
    split; [reflexivity|]. split; [reflexivity|]. split; [split; reflexivity|].
    split; [apply rsi_refl | reflexivity].
  - apply run_body_eval.
  - reflexivity.
  - reflexivity.
Qed.

Lemma main_eval : eval_stmt CT rΓ0 h0 main OK rΓA' hA'.
Proof.
  unfold main. eapply SBS_Seq; [apply prefix_eval | apply callR_eval].
Qed.

(* ------------------DELIVERABLE 5: THE THEOREM APPLIED------------------*)

(** The readonly-state theorem applied to the call to run, for any outcome
    of the call and any object of the entry heap.  The one condition on the
    class table is the one proved above; the earlier condition on class
    bounds, which fails for this table, is not used, and nothing is asked
    of what the protected methods allocate. *)
Theorem callR_preserves : forall rΓ' h',
  eval_stmt CT rΓA hA callR OK rΓ' h' ->
  forall l qr C Rs vals f,
    runtime_getObj hA l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
    (sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA) ->
    exists vals',
      runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
      nth_error vals f = nth_error vals' f.
Proof.
  intros rΓ' h' Heval.
  eapply (readonly_state_preservation_final CT Δ0 sΓA AbstractState rΓA hA
            6 1 5 [] [] [1] sΓA rΓ' h' 5 5 5 run
            mutbound_ct_clean_bounds config_A rsfp_A
            callR_typed Heval).
  - reflexivity.
  - reflexivity.
  - apply find_run.
  - left. reflexivity.
Qed.

(** The D pd (location 3) keeps its f. *)
Theorem callR_preserves_pd : forall rΓ' h',
  eval_stmt CT rΓA hA callR OK rΓ' h' ->
  exists vals',
    runtime_getObj h' 3 =
      Some (mkObj (mkruntime_type Mut_r 2 [rMutCell]) vals') /\
    nth_error vals' 0 = Some (Iot 2).
Proof.
  intros rΓ' h' Heval.
  destruct (callR_preserves rΓ' h' Heval 3 Mut_r 2 [rMutCell] [Iot 2] 0
              eq_refl (or_intror f_is_rda))
    as (vals' & Hobj & Hnth).
  exists vals'. split; [exact Hobj|]. symmetry. exact Hnth.
Qed.

(** The immutable C pc (location 4), an object of the class whose bound
    mentions Mut, keeps its g. *)
Theorem callR_preserves_pc : forall rΓ' h',
  eval_stmt CT rΓA hA callR OK rΓ' h' ->
  exists vals',
    runtime_getObj h' 4 =
      Some (mkObj (mkruntime_type Imm_r 4 [rRODMutCell]) vals') /\
    nth_error vals' 0 = Some (Iot 3).
Proof.
  intros rΓ' h' Heval.
  destruct (callR_preserves rΓ' h' Heval 4 Imm_r 4 [rRODMutCell] [Iot 3] 0
              eq_refl (or_intror g_is_rda))
    as (vals' & Hobj & Hnth).
  exists vals'. split; [exact Hobj|]. symmetry. exact Hnth.
Qed.

(** Both, for the run exhibited above. *)
Theorem callR_preserves_run :
  (exists vals',
     runtime_getObj hA' 3 =
       Some (mkObj (mkruntime_type Mut_r 2 [rMutCell]) vals') /\
     nth_error vals' 0 = Some (Iot 2)) /\
  (exists vals',
     runtime_getObj hA' 4 =
       Some (mkObj (mkruntime_type Imm_r 4 [rRODMutCell]) vals') /\
     nth_error vals' 0 = Some (Iot 3)).
Proof.
  split.
  - exact (callR_preserves_pd rΓA' hA' callR_eval).
  - exact (callR_preserves_pc rΓA' hA' callR_eval).
Qed.

(* ------------------DELIVERABLE 6: THE RUN DOES SOMETHING------------------*)

(** The call allocated four objects.  Location 8 is an immutable C and
    location 9 a mutable C, both storing the type argument @RO D<@Mut Cell>
    and both pointing to the fresh D (location 7), which points to the fresh
    Cell (location 6).  Each call to look stored the location of that D into
    its target variable (variables 6 and 7 of run's activation). *)
Theorem callR_not_vacuous :
  dom hA' = dom hA + 4 /\
  runtime_getObj hA 6 = None /\
  (exists o, runtime_getObj hA' 6 = Some o /\
             rt_type o = mkruntime_type Mut_r 1 [] /\
             nth_error (fields_map o) 0 = Some (Iot 1)) /\
  (exists o, runtime_getObj hA' 7 = Some o /\
             rt_type o = mkruntime_type Mut_r 2 [rMutCell] /\
             nth_error (fields_map o) 0 = Some (Iot 6)) /\
  (exists o, runtime_getObj hA' 8 = Some o /\
             rt_type o = mkruntime_type Imm_r 4 [rRODMutCell] /\
             nth_error (fields_map o) 0 = Some (Iot 7)) /\
  (exists o, runtime_getObj hA' 9 = Some o /\
             rt_type o = mkruntime_type Mut_r 4 [rRODMutCell] /\
             nth_error (fields_map o) 0 = Some (Iot 7)) /\
  runtime_getVal rΓpre 6 = Some Null_a /\
  runtime_getVal rΓmid 6 = Some (Iot 7) /\
  runtime_getVal rΓmid 7 = Some Null_a /\
  runtime_getVal rΓend 7 = Some (Iot 7) /\
  runtime_getVal (rΓlook' 8) (mreturn (mbody look)) = Some (Iot 7) /\
  runtime_getVal (rΓlook' 9) (mreturn (mbody look)) = Some (Iot 7) /\
  hA <> hA'.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [eexists; split; [reflexivity | split; reflexivity]|].
  split; [eexists; split; [reflexivity | split; reflexivity]|].
  split; [eexists; split; [reflexivity | split; reflexivity]|].
  split; [eexists; split; [reflexivity | split; reflexivity]|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  discriminate.
Qed.

Print Assumptions mutbound_ct_wf.
Print Assumptions mutbound_ct_clean_bounds.
Print Assumptions mutbound_ct_not_bounds_nm.
Print Assumptions config_A.
Print Assumptions rsf_A.
Print Assumptions main_typed.
Print Assumptions callR_eval.
Print Assumptions callR_not_vacuous.
Print Assumptions callR_preserves_run.
Print Assumptions callR_preserves.
