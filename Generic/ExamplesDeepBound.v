From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric
  GhostLabels GhostTyping GhostForget GhostFit GhostInvariant GhostOverride
  GhostCall GhostEntry ArgViews ArgTyping ArgFit ArgInvariant
  ArgCases ArgClean ArgOverride ArgCall ArgMain ArgEntry ArgRsf.

(** A worked example for the readonly-state theorem in which one
    type-parameter bound mentions another type parameter and a second bound is
    receiver-dependent, and both parameters are used at their bounds inside a
    readonly-state method.

    class 0: @RDM class Object {}
    class 1: @RDM class Cell extends Object {
       @Assignable @RDM Cell cache;        // field 0
       @RDA @RO Object value;              // field 1
    }
    class 2: @RDM class D<X extends @RO Object> extends Object {
       @RDA X f;                           // field 0
    }
    class 3: @RDM class Box2<E extends @RO D<X>, X extends @RDM Cell>
             extends Object {
       @Assignable E item;                 // field 0
       // method 0, readonly-state
       @RS @RDM Cell first(@RDM Box2<E,X> this) {
           @RO D<X> d;    // var 1
           X x;           // var 2
           @RDM Cell yy;  // var 3
           d = this.item;     // E used at its bound, which mentions X
           x = d.f;           // read as X
           yy = x;            // X used at its receiver-dependent bound
           return yy;
       }
    }
    class 4: @RDM class Runner extends Object {
       // method 1, readonly-state
       @RS @RO Object run(@RO Runner this, @RO Object y) {      // y is var 1
           @Mut Cell nc;                                 // var 2, never assigned
           @Mut Cell c;                                  // var 3
           @Mut D<@Mut Cell> d0;                         // var 4
           @Mut Box2<@RO D<@Mut Cell>, @Mut Cell> b;     // var 5
           @Mut Cell r;                                  // var 6
           c  = new @Mut Cell(nc, y);
           d0 = new @Mut D<@Mut Cell>(c);
           b  = new @Mut Box2<@RO D<@Mut Cell>, @Mut Cell>(d0);
           r  = b.first();      // through the mutable box: a @Mut Cell
           r.value = this;      // write through it
           return y;
       }
    }

    main (variable 0 is the receiver, a @Mut Object; abstract-state mode):
      @Mut Object y0;                                // var 1
      @Mut Cell nc;                                  // var 2, never assigned
      @Mut Cell s0;                                  // var 3
      @Mut D<@Mut Cell> pd;                          // var 4
      @Mut Box2<@RO D<@Mut Cell>, @Mut Cell> pb;     // var 5
      @Mut Runner rn;                                // var 6
      @RO Object x;                                  // var 7
      y0 = new @Mut Object();
      s0 = new @Mut Cell(nc, y0);
      pd = new @Mut D<@Mut Cell>(s0);
      pb = new @Mut Box2<@RO D<@Mut Cell>, @Mut Cell>(pd);
      rn = new @Mut Runner();
      x = rn.run(y0);                     // the call

    The objects s0, pd and pb exist before the call.  The value of s0 and the
    f of pd are receiver-dependent assignable, so the theorem says the call
    leaves them as they are. *)

(* ------------------THE PROGRAM------------------*)

Definition ROObject : qualified_type := TClass RO 0 [].
Definition MutObject : qualified_type := TClass Mut 0 [].
Definition RDMCell : qualified_type := TClass RDM 1 [].
Definition MutCell : qualified_type := TClass Mut 1 [].
Definition tE : qualified_type := TVar TVSub ClassVar 0.
Definition tX : qualified_type := TVar TVSub ClassVar 1.
Definition RODX : qualified_type := TClass RO 2 [tX].
Definition RODMutCell : qualified_type := TClass RO 2 [MutCell].
Definition MutDMutCell : qualified_type := TClass Mut 2 [MutCell].
Definition MutBox : qualified_type := TClass Mut 3 [RODMutCell; MutCell].
Definition RDMBoxEX : qualified_type := TClass RDM 3 [tE; tX].
Definition RORunner : qualified_type := TClass RO 4 [].
Definition MutRunner : qualified_type := TClass Mut 4 [].

Definition ObjectDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 0; ctparams := [];
                     super := None |};
     body := {| fields := []; methods := [] |} |}.

Definition cache_field : field_def :=
  {| assignability := Assignable; ftype := RDMCell |}.
Definition value_field : field_def :=
  {| assignability := RDA; ftype := ROObject |}.

Definition CellDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 1; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := [cache_field; value_field]; methods := [] |} |}.

Definition f_field : field_def :=
  {| assignability := RDA; ftype := TVar TVSub ClassVar 0 |}.

Definition DDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 2;
                     ctparams := [ROObject];
                     super := Some (0, []) |};
     body := {| fields := [f_field]; methods := [] |} |}.

Definition item_field : field_def :=
  {| assignability := Assignable; ftype := tE |}.

Definition first : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mqparams := 0;
          mret := RDMCell;
          mname := 0;
          mreceiver := RDMBoxEX;
          mparams := [] |};
     mbody :=
       {| mbody_stmt :=
            SSeq (SLocal RODX 1)
            (SSeq (SLocal tX 2)
            (SSeq (SLocal RDMCell 3)
            (SSeq (SVarAss 1 (EField 0 0))
            (SSeq (SVarAss 2 (EField 1 0))
                  (SVarAss 3 (EVar 2))))));
          mreturn := 3 |} |}.

Definition BoxDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 3;
                     ctparams := [RODX; RDMCell];
                     super := Some (0, []) |};
     body := {| fields := [item_field]; methods := [first] |} |}.

Definition firstCall : stmt := SCall 6 0 5 [] [] [].

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
            (SSeq (SLocal MutCell 3)
            (SSeq (SLocal MutDMutCell 4)
            (SSeq (SLocal MutBox 5)
            (SSeq (SLocal MutCell 6)
            (SSeq (SNew 3 Mut_c 1 [] [2; 1])
            (SSeq (SNew 4 Mut_c 2 [MutCell] [3])
            (SSeq (SNew 5 Mut_c 3 [RODMutCell; MutCell] [4])
            (SSeq firstCall
                  (SFldWrite 6 1 0)))))))));
          mreturn := 1 |} |}.

Definition RunnerDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 4; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := []; methods := [run] |} |}.

Definition CT : class_table := [ObjectDef; CellDef; DDef; BoxDef; RunnerDef].

Definition prefix : stmt :=
  SSeq (SLocal MutObject 1)
  (SSeq (SLocal MutCell 2)
  (SSeq (SLocal MutCell 3)
  (SSeq (SLocal MutDMutCell 4)
  (SSeq (SLocal MutBox 5)
  (SSeq (SLocal MutRunner 6)
  (SSeq (SLocal ROObject 7)
  (SSeq (SNew 1 Mut_c 0 [] [])
  (SSeq (SNew 3 Mut_c 1 [] [2; 1])
  (SSeq (SNew 4 Mut_c 2 [MutCell] [3])
  (SSeq (SNew 5 Mut_c 3 [RODMutCell; MutCell] [4])
        (SNew 6 Mut_c 4 [] []))))))))))).

Definition callR : stmt := SCall 7 1 6 [] [] [1].

Definition main : stmt := SSeq prefix callR.

Definition Δ0 : tv_env := mk_tv_env [] [] AbstractState 0.
Definition sΓ0 : s_env := [MutObject].
Definition sΓA : s_env :=
  [MutObject; MutObject; MutCell; MutCell; MutDMutCell; MutBox; MutRunner;
   ROObject].

(** The bound environment of run: no type parameter is in scope. *)
Definition ΔR : tv_env := mk_tv_env [] [] ReadonlyState 0.

(** The bound environment of first: E bounded by @RO D<X>, X bounded by
    @RDM Cell. *)
Definition ΔF : tv_env := mk_tv_env [RODX; RDMCell] [] ReadonlyState 0.

Definition sΓRun : s_env :=
  [RORunner; ROObject; MutCell; MutCell; MutDMutCell; MutBox; MutCell].

Definition sΓFirst : s_env := [RDMBoxEX; RODX; tX; RDMCell].

(* ------------------SMALL TACTICS AND FACTS------------------*)

Ltac qs := (apply q_refl; discriminate) || apply q_rd || apply q_bot.

Lemma wf_plain : forall Δ top q0 C,
  C = 0 \/ C = 1 \/ C = 4 -> q0 <> Lost -> wf_stype CT Δ top (TClass q0 C []).
Proof.
  intros Δ top q0 C HC Hq.
  destruct HC as [-> | [-> | ->]];
    (eapply wfs_class;
       [reflexivity | right | reflexivity | constructor | constructor]);
    destruct q0; cbn; try qs; congruence.
Qed.

Lemma wf_use : forall Δ q0 C,
  C = 0 \/ C = 1 \/ C = 4 -> q0 <> Lost -> wf_stypeuse CT Δ (TClass q0 C []).
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

(** Any Runner is a readonly Object. *)
Lemma sub_Runner_ROObject : forall Δ q0,
  qualified_type_subtype CT Δ (TClass q0 4 []) ROObject.
Proof.
  intros Δ q0. eapply qtype_trans.
  - apply qtype_hier with (D := 0) (Vs := []).
    eapply si_step; [reflexivity|]. cbn. apply si_refl.
  - apply qtype_qual; [cbn; lia | apply q_rd | constructor].
Qed.

(** Inside Box2, X is below its bound and hence a readonly Object. *)
Lemma sub_tX_ROObject : forall mt,
  qualified_type_subtype CT (mk_tv_env [RODX; RDMCell] [] mt 0) tX ROObject.
Proof.
  intros mt. eapply qtype_trans.
  - apply qtype_var_bound with (B := RDMCell). reflexivity.
  - apply sub_Cell_ROObject.
Qed.

(** The bound of E, @RO D<X>, is a well-formed type inside Box2. *)
Lemma wf_RODX : forall mt top,
  wf_stype CT (mk_tv_env [RODX; RDMCell] [] mt 0) top RODX.
Proof.
  intros mt top.
  eapply wfs_class; [reflexivity | right; cbn; qs | reflexivity | |].
  - constructor; [|constructor].
    eapply wfs_var; [reflexivity | left; reflexivity].
  - constructor; [|constructor]. intros m. cbn. apply sub_tX_ROObject.
Qed.

Lemma wf_tvar : forall mt top n B,
  nth_error [RODX; RDMCell] n = Some B ->
  wf_stype CT (mk_tv_env [RODX; RDMCell] [] mt 0) top (TVar TVSub ClassVar n).
Proof.
  intros. eapply wfs_var; [exact H | right; discriminate].
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

(** What the two bounds of Box2 read as for the instantiation
    Box2<@RO D<@Mut Cell>, @Mut Cell> seen through a mutable head: the bound
    of E, which mentions X, becomes @RO D<@Mut Cell>; the receiver-dependent
    bound of X becomes @Mut Cell. *)
Lemma MutBox_bounds_read :
  member_type AbstractState Mut [RODMutCell; MutCell] [] [] RODX = RODMutCell /\
  member_type AbstractState Mut [RODMutCell; MutCell] [] [] RDMCell = MutCell.
Proof. split; reflexivity. Qed.

(** The mutable box.  Both arguments are compared with their bounds, in
    every mode: @RO D<@Mut Cell> against @RO D<@Mut Cell> and @Mut Cell
    against @Mut Cell. *)
Lemma wf_MutBox : forall Δ, wf_stypeuse CT Δ MutBox.
Proof.
  intros Δ.
  eapply wfs_class; [reflexivity | right; cbn; qs | reflexivity | |].
  - constructor; [apply wf_DMutCell; discriminate|].
    constructor; [apply wf_plain; [tauto | discriminate] | constructor].
  - constructor; [|constructor; [|constructor]]; intros m; cbn; refl_sub.
Qed.

(** The declared receiver of first.  Both bound checks are performed: read
    through the @RDM head the bounds are @RO D<X> and @RDM Cell, and E and X
    are below them because those are their declared bounds. *)
Lemma wf_RDMBoxEX_first : wf_stypeuse CT ΔF RDMBoxEX.
Proof.
  eapply wfs_class; [reflexivity | right; cbn; qs | reflexivity | |].
  - constructor; [eapply wf_tvar; reflexivity|].
    constructor; [eapply wf_tvar; reflexivity | constructor].
  - constructor; [|constructor; [|constructor]]; cbn.
    + intros m. apply qtype_var_bound. reflexivity.
    + intros m. apply qtype_var_bound. reflexivity.
Qed.

Lemma wf_ROObject : forall Δ, wf_stypeuse CT Δ ROObject.
Proof. intros. wfp. Qed.
Lemma wf_MutObject : forall Δ, wf_stypeuse CT Δ MutObject.
Proof. intros. wfp. Qed.
Lemma wf_RDMCell : forall Δ, wf_stypeuse CT Δ RDMCell.
Proof. intros. wfp. Qed.
Lemma wf_MutCell : forall Δ, wf_stypeuse CT Δ MutCell.
Proof. intros. wfp. Qed.
Lemma wf_RORunner : forall Δ, wf_stypeuse CT Δ RORunner.
Proof. intros. wfp. Qed.
Lemma wf_MutRunner : forall Δ, wf_stypeuse CT Δ MutRunner.
Proof. intros. wfp. Qed.
Lemma wf_MutDMutCell : forall Δ, wf_stypeuse CT Δ MutDMutCell.
Proof. intros. apply wf_DMutCell. discriminate. Qed.
Lemma wf_RODX_first : wf_stypeuse CT ΔF RODX.
Proof. apply wf_RODX. Qed.
Lemma wf_tX_first : wf_stypeuse CT ΔF tX.
Proof. eapply wf_tvar. reflexivity. Qed.

Create HintDb edb.
Local Hint Resolve wf_ROObject wf_MutObject wf_RDMCell wf_MutCell wf_RORunner
  wf_MutRunner wf_MutDMutCell wf_MutBox wf_RODX_first wf_tX_first
  wf_RDMBoxEX_first : edb.

Ltac wfenv :=
  split; [cbn; lia |
          cbn; repeat (apply Forall_cons; [solve [auto with edb]|]);
          apply Forall_nil].

Lemma collect_Object : CollectFields CT 0 [].
Proof. eapply CF_Object; reflexivity. Qed.

Lemma collect_Cell : CollectFields CT 1 [cache_field; value_field].
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

Lemma collect_Box : CollectFields CT 3 [item_field].
Proof.
  change (CollectFields CT 3
            (map (subst_field []) [] ++ Syntax.fields (body BoxDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma collect_Runner : CollectFields CT 4 [].
Proof.
  change (CollectFields CT 4
            (map (subst_field []) [] ++ Syntax.fields (body RunnerDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

(** Field 1 of Cell, value, is receiver-dependent assignable. *)
Lemma value_is_rda : sf_assignability_rel CT 1 1 RDA.
Proof.
  exists value_field. split; [|reflexivity].
  eapply FL_Found; [apply collect_Cell | reflexivity].
Qed.

(** Field 0 of D, f, is receiver-dependent assignable. *)
Lemma f_is_rda : sf_assignability_rel CT 2 0 RDA.
Proof.
  exists f_field. split; [|reflexivity].
  eapply FL_Found; [apply collect_D | reflexivity].
Qed.

Lemma no_method_in_Object : forall m D mdef,
  ~ FindMethodWithName CT 0 m D mdef.
Proof.
  intros m D mdef H. inversion H; subst.
  - cbn in Hfind. injection Hfind as <-. cbn in Hget_method. discriminate.
  - cbn in Hfind. injection Hfind as <-. cbn in Hsuper. discriminate.
Qed.

Lemma find_first : FindMethodWithName CT 3 0 3 first.
Proof. eapply FOM_Here; reflexivity. Qed.

Lemma find_run : FindMethodWithName CT 4 1 4 run.
Proof. eapply FOM_Here; reflexivity. Qed.

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

(** *** Box2.first, one statement at a time *)

(** d = this.item: through the @RDM receiver the field reads as the bare
    variable E, and E is below its bound @RO D<X>, a bound that mentions the
    other type variable. *)
Lemma first_read_item :
  member_type ReadonlyState RDM [tE; tX] [] [] (ftype item_field) = tE /\
  qualified_type_subtype CT ΔF tE RODX.
Proof.
  split; [reflexivity|]. apply qtype_var_bound. reflexivity.
Qed.

(** x = d.f: d is an @RO D<X>; the field f of D is typed by D's parameter, and
    read through d it is exactly X. *)
Lemma first_read_f :
  member_type ReadonlyState RO [tX] [] [] (ftype f_field) = tX.
Proof. reflexivity. Qed.

(** yy = x: X is below its receiver-dependent bound @RDM Cell. *)
Lemma first_X_below_bound : qualified_type_subtype CT ΔF tX RDMCell.
Proof. apply qtype_var_bound. reflexivity. Qed.

Lemma first_body_typed :
  stmt_typing CT ΔF [RDMBoxEX] ReadonlyState (mbody_stmt (mbody first)) sΓFirst.
Proof.
  cbn. unfold sΓFirst.
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  cbn.
  (* d = this.item *)
  ty_seq.
  { eapply ST_VarAss with (Tx := RODX) (Te := tE);
      [wfenv | | discriminate | reflexivity | ].
    - eapply ET_Field with (x := 0) (T := RDMBoxEX) (qx := RDM) (C := 3)
        (Ts := [tE; tX]) (fDef := item_field);
        [wfenv | reflexivity | reflexivity | fl collect_Box].
    - apply qtype_var_bound. reflexivity. }
  (* x = d.f *)
  ty_seq.
  { eapply ST_VarAss with (Tx := tX) (Te := tX);
      [wfenv | | discriminate | reflexivity | ].
    - eapply ET_Field with (x := 1) (T := RODX) (qx := RO) (C := 2)
        (Ts := [tX]) (fDef := f_field);
        [wfenv | reflexivity | reflexivity | fl collect_D].
    - apply qtype_var_refl. }
  (* yy = x *)
  eapply ST_VarAss with (Tx := RDMCell) (Te := tX);
    [wfenv | | discriminate | reflexivity | ].
  - apply ET_Var; [wfenv | reflexivity].
  - apply first_X_below_bound.
Qed.

(** The signature of first has no mutable position, reading the type
    variables through their bounds: the receiver is @RDM Box2<E, X>, E is read
    as @RO D<X>, X as @RDM Cell. *)
Lemma first_no_mutable_roots :
  signature_has_no_mutable_roots ΔF (msignature first).
Proof.
  split; [|constructor].
  cbn. constructor; [discriminate|].
  constructor; [|constructor; [|constructor]].
  - eapply nm_var; [reflexivity|].
    constructor; [discriminate|]. constructor; [|constructor].
    eapply nm_var; [reflexivity|]. constructor; [discriminate | constructor].
  - eapply nm_var; [reflexivity|]. constructor; [discriminate | constructor].
Qed.

Lemma wf_first : wf_method CT 3 first.
Proof.
  unfold wf_method.
  change (method_tv_env CT 3 (msignature first)) with ΔF.
  split; [apply receiver_plain_ok; left; exists RDM; reflexivity|].
  split; [constructor|].
  split; [apply wf_RDMCell|].
  split.
  { exists sΓFirst, RDMCell. split; [|split].
    - apply first_body_typed.
    - reflexivity.
    - refl_sub. }
  split; [no_override|].
  intros _. apply first_no_mutable_roots.
Qed.

(** *** Runner.run *)

(** c = new @Mut Cell(nc, y). *)
Lemma run_new_Cell_typed :
  stmt_typing CT ΔR sΓRun ReadonlyState (SNew 3 Mut_c 1 [] [2; 1]) sΓRun.
Proof.
  unfold sΓRun, ΔR.
  eapply ST_New with (Tx := MutCell) (argtypes := [MutCell; ROObject]);
    [wfenv | reflexivity | reflexivity | reflexivity | discriminate
    | reflexivity | apply wf_MutCell | constructor | constructor
    | apply collect_Cell | | ].
  - constructor; [|constructor; [|constructor]]; cbn.
    + split; [refl_sub | lf].
    + split; [refl_sub | lf].
  - cbn. refl_sub.
Qed.

(** d0 = new @Mut D<@Mut Cell>(c). *)
Lemma run_new_D_typed :
  stmt_typing CT ΔR sΓRun ReadonlyState (SNew 4 Mut_c 2 [MutCell] [3]) sΓRun.
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

(** b = new @Mut Box2<@RO D<@Mut Cell>, @Mut Cell>(d0), inside
    readonly-state code.  Both type arguments are compared with their bounds
    in every mode.  The initialiser d0, a @Mut D<@Mut Cell>, fills the field
    item, which for this box reads @RO D<@Mut Cell>. *)
Lemma run_new_Box_typed :
  stmt_typing CT ΔR sΓRun ReadonlyState
    (SNew 5 Mut_c 3 [RODMutCell; MutCell] [4]) sΓRun.
Proof.
  unfold sΓRun, ΔR.
  eapply ST_New with (Tx := MutBox) (argtypes := [MutDMutCell]);
    [wfenv | reflexivity | reflexivity | reflexivity | discriminate
    | reflexivity | apply wf_MutBox | | | apply collect_Box | | ].
  - constructor; [lf | constructor; [lf | constructor]].
  - constructor; [|constructor; [|constructor]]; cbn.
    + split; [lf | intros m; refl_sub].
    + split; [lf | intros m; refl_sub].
  - constructor; [|constructor]; cbn.
    split; [qual_sub | lf].
  - cbn. refl_sub.
Qed.

(** r = b.first(), in readonly-state code: through the mutable box the
    declared result @RDM Cell reads @Mut Cell. *)
Lemma firstCall_typed :
  stmt_typing CT ΔR sΓRun ReadonlyState firstCall sΓRun.
Proof.
  unfold firstCall, sΓRun, ΔR.
  eapply ST_Call with (Tx := MutCell) (Ty := MutBox)
    (argtypes := [])
    (qy := Mut) (C := 3) (Ts := [RODMutCell; MutCell]) (D := 3)
    (Vs := [RODMutCell; MutCell])
    (mdef := first);
    [wfenv | reflexivity | reflexivity | reflexivity | reflexivity
    | apply find_first | apply si_refl | discriminate | constructor
    | constructor | reflexivity | constructor | | | constructor
    | apply method_subtyping_refl | reflexivity | constructor | recv_known].
  - cbn. refl_sub.
  - cbn. split; [refl_sub | lf].
Qed.

(** r.value = this: r is a @Mut Cell, so its value slot is assignable. *)
Lemma run_write_typed :
  stmt_typing CT ΔR sΓRun ReadonlyState (SFldWrite 6 1 0) sΓRun.
Proof.
  unfold sΓRun, ΔR.
  eapply ST_FldWrite with (Tx := MutCell) (Ty := RORunner) (qx := Mut)
    (C := 1) (Ts := []) (fieldT := value_field);
    [wfenv | reflexivity | reflexivity | reflexivity | fl collect_Cell
    | | reflexivity].
  split; [cbn; apply sub_Runner_ROObject | lf].
Qed.

Lemma run_body_typed :
  stmt_typing CT ΔR [RORunner; ROObject] ReadonlyState
    (mbody_stmt (mbody run)) sΓRun.
Proof.
  cbn. unfold ΔR.
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  ty_seq; [ty_local|]. ty_seq; [ty_local|].
  cbn.
  ty_seq; [apply run_new_Cell_typed|].
  ty_seq; [apply run_new_D_typed|].
  ty_seq; [apply run_new_Box_typed|].
  ty_seq; [apply firstCall_typed|].
  apply run_write_typed.
Qed.

Lemma wf_run : wf_method CT 4 run.
Proof.
  unfold wf_method.
  change (method_tv_env CT 4 (msignature run)) with ΔR.
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
  - constructor; [unfold wf_field; cbn; wfp|].
    constructor; [unfold wf_field; cbn; wfp | constructor].
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

Lemma wf_BoxDef : wf_class CT BoxDef.
Proof.
  wf_other 0 (@nil qualified_type) ObjectDef.
  - constructor; [|constructor; [|constructor]].
    + split; [exact I | apply wf_RODX].
    + split; [exact I | wfp].
  - wfp.
  - constructor.
  - constructor.
  - left. reflexivity.
  - constructor; [|constructor]; unfold wf_field; cbn.
    eapply wfs_var; [reflexivity|]. right. discriminate.
  - constructor; [apply wf_first | constructor].
  - constructor; [intros [] | constructor].
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

Theorem deep_ct_wf : wf_class_table CT.
Proof.
  unfold wf_class_table. split; [|split; [|split]].
  - constructor; [apply wf_ObjectDef|].
    constructor; [apply wf_CellDef|].
    constructor; [apply wf_DDef|].
    constructor; [apply wf_BoxDef|].
    constructor; [apply wf_RunnerDef | constructor].
  - exists ObjectDef. split; reflexivity.
  - intros i def Hi Hfind.
    destruct i as [|[|[|[|[|i]]]]]; try lia; cbn in Hfind.
    + injection Hfind as <-. discriminate.
    + injection Hfind as <-. discriminate.
    + injection Hfind as <-. discriminate.
    + injection Hfind as <-. discriminate.
    + destruct i; discriminate.
  - intros i def Hfind.
    destruct i as [|[|[|[|[|i]]]]]; cbn in Hfind.
    + injection Hfind as <-. reflexivity.
    + injection Hfind as <-. reflexivity.
    + injection Hfind as <-. reflexivity.
    + injection Hfind as <-. reflexivity.
    + injection Hfind as <-. reflexivity.
    + destruct i; discriminate.
Qed.

(* ------------------DELIVERABLE 2: THE CONDITIONS ON BOUNDS HOLD------------------*)

(** @RO D<X> has no mutable position when X is read through its bound
    @RDM Cell; @RDM Cell and @RO Object have none either. *)
Lemma no_mut_RODX : forall mb mt kq,
  no_mut (mk_tv_env [RODX; RDMCell] mb mt kq) RODX.
Proof.
  intros mb mt kq. apply nm_class; [discriminate|].
  constructor; [|constructor].
  eapply nm_var; [reflexivity|].
  apply nm_class; [discriminate | constructor].
Qed.

Lemma no_mut_plain : forall Δ q0 C,
  q0 <> Mut -> no_mut Δ (TClass q0 C []).
Proof. intros. apply nm_class; [assumption | constructor]. Qed.

(** Every class type-parameter bound of this table is a class type with no
    mutable position.  There are three: the bound of D's parameter and the
    two bounds of Box2. *)
Lemma ct_bounds_nm : class_bounds_nm CT.
Proof.
  intros C def n B Hfind Hn.
  destruct C as [|[|[|[|[|C]]]]]; cbn in Hfind;
    try (destruct C; discriminate);
    injection Hfind as <-; cbn in Hn.
  - destruct n; discriminate.
  - destruct n; discriminate.
  - destruct n as [|[|n]]; cbn in Hn; try discriminate.
    injection Hn as <-. split; [exact I | apply no_mut_plain; discriminate].
  - destruct n as [|[|[|n]]]; cbn in Hn; try discriminate.
    + injection Hn as <-. split; [exact I | apply no_mut_RODX].
    + injection Hn as <-. split; [exact I | apply no_mut_plain; discriminate].
  - destruct n; discriminate.
Qed.

(** There are two readonly-state methods.  No type parameter is in scope of
    run.  In scope of first there are two, with the bounds @RO D<X> and
    @RDM Cell. *)
Theorem deep_ct_clean_bounds : clean_bounds_ct CT.
Proof.
  intros C def md Hfind Hin _.
  destruct C as [|[|[|[|[|C]]]]]; cbn in Hfind;
    try (destruct C; discriminate);
    injection Hfind as <-; cbn in Hin.
  - destruct Hin.
  - destruct Hin.
  - destruct Hin.
  - destruct Hin as [<- | []].
    intros o n B Hb.
    destruct o; [destruct n as [|[|[|n]]] | destruct n]; cbn in Hb;
      try discriminate.
    + injection Hb as <-. split; [exact I | apply no_mut_RODX].
    + injection Hb as <-. split; [exact I | apply no_mut_plain; discriminate].
  - destruct Hin as [<- | []].
    intros o n B Hb. destruct o; destruct n; discriminate.
Qed.

(** The condition is not vacuous: first is a readonly-state method of the
    table, and the bound environment in which it is checked contains a bound
    that mentions another type variable and a receiver-dependent bound. *)
Lemma first_is_readonly_state :
  find_class CT 3 = Some BoxDef /\
  List.In first (methods (body BoxDef)) /\
  readonly_state_method_scope (mscope (msignature first)).
Proof.
  split; [reflexivity|]. split; [left; reflexivity | left; reflexivity].
Qed.

Lemma first_bound_of_E :
  tv_bound (method_tv_env CT 3 (msignature first)) ClassVar 0
    = Some (TClass RO 2 [TVar TVSub ClassVar 1]).
Proof. reflexivity. Qed.

Lemma first_bound_of_X :
  tv_bound (method_tv_env CT 3 (msignature first)) ClassVar 1
    = Some (TClass RDM 1 []).
Proof. reflexivity. Qed.

(** What the condition says about those two bounds. *)
Lemma first_bounds_checked :
  (is_class_type (TClass RO 2 [TVar TVSub ClassVar 1]) /\
   no_mut (method_tv_env CT 3 (msignature first))
     (TClass RO 2 [TVar TVSub ClassVar 1])) /\
  (is_class_type (TClass RDM 1 []) /\
   no_mut (method_tv_env CT 3 (msignature first)) (TClass RDM 1 [])).
Proof.
  split.
  - exact (deep_ct_clean_bounds 3 BoxDef first eq_refl (or_introl eq_refl)
             (or_introl eq_refl) ClassVar 0 _ first_bound_of_E).
  - exact (deep_ct_clean_bounds 3 BoxDef first eq_refl (or_introl eq_refl)
             (or_introl eq_refl) ClassVar 1 _ first_bound_of_X).
Qed.

(* ------------------DELIVERABLE 3: CONFIGURATION, TYPING, RUN------------------*)

Lemma prefix_typed : stmt_typing CT Δ0 sΓ0 AbstractState prefix sΓA.
Proof.
  unfold prefix, sΓA, sΓ0, Δ0.
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  ty_seq; [ty_local|].
  cbn.
  (* y0 = new @Mut Object() *)
  ty_seq.
  { eapply ST_New with (Tx := MutObject) (argtypes := []) (fds := []);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutObject | constructor | constructor
      | apply collect_Object | constructor | ].
    cbn. refl_sub. }
  (* s0 = new @Mut Cell(nc, y0) *)
  ty_seq.
  { eapply ST_New with (Tx := MutCell) (argtypes := [MutCell; MutObject]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutCell | constructor | constructor
      | apply collect_Cell | | ].
    - constructor; [|constructor; [|constructor]]; cbn.
      + split; [refl_sub | lf].
      + split; [qual_sub | lf].
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
  (* pb = new @Mut Box2<@RO D<@Mut Cell>, @Mut Cell>(pd) *)
  ty_seq.
  { eapply ST_New with (Tx := MutBox) (argtypes := [MutDMutCell]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutBox | | | apply collect_Box | | ].
    - constructor; [lf | constructor; [lf | constructor]].
    - constructor; [|constructor; [|constructor]]; cbn.
      + split; [lf | intros m; refl_sub].
      + split; [lf | intros m; refl_sub].
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
    (qy := Mut) (C := 4) (Ts := []) (D := 4) (Vs := [])
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
    3 is the D pd that holds s0, 4 is the box pb that holds pd, 5 is the
    Runner. *)
Definition rΓ0 : r_env := mkr_env [Iot 0] [] [] [].
Definition h0 : heap := [mkObj (mkruntime_type Mut_r 0 []) []].

Definition rΓA : r_env :=
  mkr_env [Iot 0; Iot 1; Null_a; Iot 2; Iot 3; Iot 4; Iot 5; Null_a] [] [] [].

Definition rMutCell : rtype := RClass Mut 1 [].
Definition rRODMutCell : rtype := RClass RO 2 [rMutCell].

Definition hA : heap :=
  [ mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 1 []) [Null_a; Iot 1];
    mkObj (mkruntime_type Mut_r 2 [rMutCell]) [Iot 2];
    mkObj (mkruntime_type Mut_r 3 [rRODMutCell; rMutCell]) [Iot 3];
    mkObj (mkruntime_type Mut_r 4 []) [] ].

Ltac ev_local := eapply SBS_Seq; [apply SBS_Local; reflexivity|]; cbn.
Ltac ev_new := eapply SBS_Seq; [eapply SBS_New; reflexivity|]; cbn.

Lemma prefix_eval : eval_stmt CT rΓ0 h0 prefix OK rΓA hA.
Proof.
  unfold prefix, rΓ0, h0.
  ev_local. ev_local. ev_local. ev_local. ev_local. ev_local. ev_local.
  ev_new. ev_new. ev_new. ev_new.
  eapply SBS_New; reflexivity.
Qed.

Lemma initial_config : wf_r_config CT Δ0 sΓ0 rΓ0 h0.
Proof.
  unfold Δ0, sΓ0, rΓ0, h0.
  refine (conj deep_ct_wf
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
    something: the heap now holds the box pb, whose first bound mentions its
    second type argument. *)
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

(** The three fresh objects: a Cell at location 6, a D at location 7 that
    holds it, a box at location 8 that holds the D. *)
Definition fresh_D : Obj :=
  mkObj (mkruntime_type Mut_r 2 [rMutCell]) [Iot 6].
Definition fresh_box : Obj :=
  mkObj (mkruntime_type Mut_r 3 [rRODMutCell; rMutCell]) [Iot 7].

(** The heap after the three allocations; the call to first leaves it as it
    is. *)
Definition hmid : heap :=
  hA ++ [mkObj (mkruntime_type Mut_r 1 []) [Null_a; Iot 1]; fresh_D; fresh_box].

(** The heap when run returns. *)
Definition hA' : heap :=
  hA ++ [mkObj (mkruntime_type Mut_r 1 []) [Null_a; Iot 5]; fresh_D; fresh_box].

(** The activation of run just before and just after the call to first. *)
Definition rΓpre : r_env :=
  mkr_env [Iot 5; Iot 1; Null_a; Iot 6; Iot 7; Iot 8; Null_a] [] [] [].
Definition rΓmid : r_env :=
  mkr_env [Iot 5; Iot 1; Null_a; Iot 6; Iot 7; Iot 8; Iot 6] [] [] [].

(** The activation of first: receiver the fresh box, with its two type
    arguments resolved at run time. *)
Definition rΓfirst : r_env := mkr_env [Iot 8] [rRODMutCell; rMutCell] [] [].
Definition rΓfirst' : r_env :=
  mkr_env [Iot 8; Iot 7; Iot 6; Iot 6] [rRODMutCell; rMutCell] [] [].

Definition rΓA' : r_env :=
  mkr_env [Iot 0; Iot 1; Null_a; Iot 2; Iot 3; Iot 4; Iot 5; Iot 1] [] [] [].

Definition run_allocs : stmt :=
  SSeq (SLocal MutCell 2)
  (SSeq (SLocal MutCell 3)
  (SSeq (SLocal MutDMutCell 4)
  (SSeq (SLocal MutBox 5)
  (SSeq (SLocal MutCell 6)
  (SSeq (SNew 3 Mut_c 1 [] [2; 1])
  (SSeq (SNew 4 Mut_c 2 [MutCell] [3])
        (SNew 5 Mut_c 3 [RODMutCell; MutCell] [4]))))))).

Lemma run_allocs_eval : eval_stmt CT rΓrun hA run_allocs OK rΓpre hmid.
Proof.
  unfold run_allocs, rΓrun, rΓpre, hmid, fresh_D, fresh_box, hA.
  ev_local. ev_local. ev_local. ev_local. ev_local.
  ev_new. ev_new.
  eapply SBS_New; reflexivity.
Qed.

(** The body of first, run on the fresh box. *)
Lemma first_body_eval :
  eval_stmt CT rΓfirst hmid (mbody_stmt (mbody first)) OK rΓfirst' hmid.
Proof.
  cbn. unfold rΓfirst.
  ev_local. ev_local. ev_local.
  eapply SBS_Seq.
  { match goal with
    | |- eval_stmt _ ?r ?h _ _ _ _ =>
        refine (SBS_Assign CT r h 1 _ Null_a (Iot 7) eq_refl _)
    end.
    eapply EBS_Field; reflexivity. }
  cbn.
  eapply SBS_Seq.
  { match goal with
    | |- eval_stmt _ ?r ?h _ _ _ _ =>
        refine (SBS_Assign CT r h 2 _ Null_a (Iot 6) eq_refl _)
    end.
    eapply EBS_Field; reflexivity. }
  cbn.
  match goal with
  | |- eval_stmt _ ?r ?h _ _ _ _ =>
      refine (SBS_Assign CT r h 3 _ Null_a (Iot 6) eq_refl _)
  end.
  apply EBS_Val. reflexivity.
Qed.

(** The nested call: first runs on the fresh box and hands back the fresh
    Cell. *)
Lemma firstCall_eval : eval_stmt CT rΓpre hmid firstCall OK rΓmid hmid.
Proof.
  unfold firstCall, rΓpre.
  eapply SBS_Call with (mdef := first) (D := 3) (cy := 3)
    (rΓ' := rΓfirst) (rΓ'' := rΓfirst').
  - reflexivity.
  - reflexivity.
  - apply find_first.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold callee_env. do 4 eexists.
    split; [reflexivity|]. split; [reflexivity|]. split; [split; reflexivity|].
    split; [apply rsi_refl | reflexivity].
  - apply first_body_eval.
  - reflexivity.
  - reflexivity.
Qed.

(** The write itself. *)
Lemma run_write_eval :
  eval_stmt CT rΓmid hmid (SFldWrite 6 1 0) OK rΓmid hA'.
Proof.
  eapply SBS_FldWrite with (a := RDA);
    [reflexivity | reflexivity | reflexivity | apply value_is_rda
    | reflexivity | reflexivity | reflexivity].
Qed.

Lemma run_body_eval :
  eval_stmt CT rΓrun hA (mbody_stmt (mbody run)) OK rΓmid hA'.
Proof.
  change (mbody_stmt (mbody run)) with
    (SSeq (SLocal MutCell 2)
    (SSeq (SLocal MutCell 3)
    (SSeq (SLocal MutDMutCell 4)
    (SSeq (SLocal MutBox 5)
    (SSeq (SLocal MutCell 6)
    (SSeq (SNew 3 Mut_c 1 [] [2; 1])
    (SSeq (SNew 4 Mut_c 2 [MutCell] [3])
    (SSeq (SNew 5 Mut_c 3 [RODMutCell; MutCell] [4])
    (SSeq firstCall (SFldWrite 6 1 0)))))))))).
  unfold rΓrun.
  ev_local. ev_local. ev_local. ev_local. ev_local.
  ev_new. ev_new. ev_new.
  eapply SBS_Seq; [exact firstCall_eval | exact run_write_eval].
Qed.

Theorem callR_eval : eval_stmt CT rΓA hA callR OK rΓA' hA'.
Proof.
  unfold callR, rΓA.
  eapply SBS_Call with (mdef := run) (D := 4) (cy := 4)
    (rΓ' := rΓrun) (rΓ'' := rΓmid).
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

(* ------------------DELIVERABLE 4: THE THEOREM APPLIED------------------*)

(** The readonly-state theorem applied to the call to run, for any outcome
    of the call and any object of the entry heap. *)
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
            7 1 6 [] [] [1] sΓA rΓ' h' 5 4 4 run
            deep_ct_clean_bounds config_A rsfp_A
            callR_typed Heval).
  - reflexivity.
  - reflexivity.
  - apply find_run.
  - left. reflexivity.
Qed.

(** The Cell s0 (location 2) keeps its value. *)
Theorem callR_preserves_s0 : forall rΓ' h',
  eval_stmt CT rΓA hA callR OK rΓ' h' ->
  exists vals',
    runtime_getObj h' 2 = Some (mkObj (mkruntime_type Mut_r 1 []) vals') /\
    nth_error vals' 1 = Some (Iot 1).
Proof.
  intros rΓ' h' Heval.
  destruct (callR_preserves rΓ' h' Heval 2 Mut_r 1 [] [Null_a; Iot 1] 1
              eq_refl (or_intror value_is_rda))
    as (vals' & Hobj & Hnth).
  exists vals'. split; [exact Hobj|]. symmetry. exact Hnth.
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

(** Both, for the run exhibited above. *)
Theorem callR_preserves_run :
  (exists vals',
     runtime_getObj hA' 2 = Some (mkObj (mkruntime_type Mut_r 1 []) vals') /\
     nth_error vals' 1 = Some (Iot 1)) /\
  (exists vals',
     runtime_getObj hA' 3 =
       Some (mkObj (mkruntime_type Mut_r 2 [rMutCell]) vals') /\
     nth_error vals' 0 = Some (Iot 2)).
Proof.
  split.
  - exact (callR_preserves_s0 rΓA' hA' callR_eval).
  - exact (callR_preserves_pd rΓA' hA' callR_eval).
Qed.

(* ------------------DELIVERABLE 5: THE RUN DOES SOMETHING------------------*)

(** The call allocated three objects.  The fresh box (location 8) stores the
    two type arguments and points to the fresh D (location 7), which points
    to the fresh Cell (location 6).  The call to first stored into r
    (variable 6 of run's activation) the location of that fresh Cell.  Its
    value slot held y0 (location 1) after the allocation and holds the Runner
    (location 5) when run returns. *)
Theorem callR_not_vacuous :
  dom hA' = dom hA + 3 /\
  runtime_getObj hA 6 = None /\
  (exists o, runtime_getObj hmid 6 = Some o /\
             nth_error (fields_map o) 1 = Some (Iot 1)) /\
  (exists o, runtime_getObj hA' 6 = Some o /\
             rt_type o = mkruntime_type Mut_r 1 [] /\
             nth_error (fields_map o) 1 = Some (Iot 5)) /\
  (exists o, runtime_getObj hA' 7 = Some o /\
             rt_type o = mkruntime_type Mut_r 2 [rMutCell] /\
             nth_error (fields_map o) 0 = Some (Iot 6)) /\
  (exists o, runtime_getObj hA' 8 = Some o /\
             rt_type o = mkruntime_type Mut_r 3 [rRODMutCell; rMutCell] /\
             nth_error (fields_map o) 0 = Some (Iot 7)) /\
  runtime_getVal rΓA 1 = Some (Iot 1) /\
  runtime_getVal rΓA 6 = Some (Iot 5) /\
  runtime_getVal rΓpre 6 = Some Null_a /\
  runtime_getVal rΓmid 6 = Some (Iot 6) /\
  runtime_getVal rΓfirst' (mreturn (mbody first)) = Some (Iot 6) /\
  hmid <> hA' /\ hA <> hA'.
Proof.
  split; [reflexivity|].
  split; [reflexivity|].
  split; [eexists; split; reflexivity|].
  split; [eexists; split; [reflexivity | split; reflexivity]|].
  split; [eexists; split; [reflexivity | split; reflexivity]|].
  split; [eexists; split; [reflexivity | split; reflexivity]|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; discriminate.
Qed.

(** The slot written inside run is receiver-dependent assignable: it is one
    of the slots the theorem protects on objects of the entry heap.  The
    write is allowed because its target did not exist at entry. *)
Lemma written_slot_is_protected_kind :
  sf_assignability_rel CT 1 1 Final \/ sf_assignability_rel CT 1 1 RDA.
Proof. right. apply value_is_rda. Qed.

Print Assumptions deep_ct_wf.
Print Assumptions deep_ct_clean_bounds.
Print Assumptions ct_bounds_nm.
Print Assumptions first_bound_of_E.
Print Assumptions first_bound_of_X.
Print Assumptions first_bounds_checked.
Print Assumptions config_A.
Print Assumptions rsf_A.
Print Assumptions main_typed.
Print Assumptions firstCall_eval.
Print Assumptions callR_eval.
Print Assumptions callR_preserves.
Print Assumptions callR_preserves_run.
Print Assumptions callR_not_vacuous.
