From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  GhostOverride.

(** Regression file for the rule that a type argument must be below its bound
    in every protection mode.

    The program below has a type-parameter bound that mentions another type
    parameter.  Under the previous typing rules it was accepted, and its
    readonly-state method attack changed a receiver-dependent-assignable
    field of an object that existed before the call.  This file used to prove
    exactly that.  The program text is unchanged.

    class 0: @RDM class Object {}
    class 1: @RDM class Cell extends Object {
       @Assignable @RDM Cell cache;        // field 0
       @RDA @RO Object value;              // field 1
    }
    class 2: @RDM class D<X extends @RO Object> extends Object {
       @RDA X f;                           // field 0
    }
    class 3: @RDM class K extends D<@Mut Cell> {}
    class 4: @RDM class Box2<E extends @RO D<X>, X extends @RDM Cell>
             extends Object {
       @Assignable E item;                 // field 0
       @RDA @RDM Cell hold;                // field 1
       // method 0, readonly-state
       @RS @RO Object mix(@RDM Box2<E,X> this) {
           @RO D<X> d;    // var 1
           X x;           // var 2
           @RDM Cell yy;  // var 3
           @RDM Cell h;   // var 4
           @RO Object r;  // var 5, never assigned
           d = this.item;  x = d.f;  yy = x;  h = this.hold;  yy.cache = h;
           return r;
       }
    }
    class 5: @RDM class Owner extends Object {
       @RDA @Mut Box2<@RO K, @Mut Cell> bx;    // field 0     NOW REJECTED
       // method 1, readonly-state
       @RS @RO Object attack(@RDM Owner this, @RO Object y) {   // y is var 1
           @RO Box2<@RO K, @Lost Cell> rb;       // var 2
           @Mut Cell nc;                         // var 3, never assigned
           @RO Object n;                         // var 4, never assigned
           @Mut Cell c0;                         // var 5
           @Mut K v;                             // var 6
           @RO Object ig;                        // var 7
           @Mut Cell m;                          // var 8
           rb = this.bx;
           c0 = new @Mut Cell(nc, n);
           v = new @Mut K(c0);
           rb.item = v;
           ig = rb.mix();
           m = c0.cache;
           m.value = y;
           return y;
       }
    }

    main (variable 0 is the receiver, a @Mut Object; abstract-state mode):
      @Mut Object o;                        // var 1
      @Mut Cell nc;                         // var 2, never assigned
      @Mut Cell s0;                         // var 3
      @RO K nk;                             // var 4, never assigned
      @Mut Box2<@RO K, @Mut Cell> b0;       // var 5          NOW REJECTED
      @Mut Owner ow;                        // var 6
      @Mut Object y0;                       // var 7
      @RO Object x;                         // var 8
      o = new @Mut Object();
      s0 = new @Mut Cell(nc, o);
      b0 = new @Mut Box2<@RO K, @Mut Cell>(nk, s0);           NOW REJECTED
      ow = new @Mut Owner(b0);
      y0 = new @Mut Object();
      x = ow.attack(y0);                    // the call

    Method names are 0 (mix) and 1 (attack).

    What changed.  A type argument now has to be below its bound in every
    protection mode, not only in the mode of the code that writes the type.
    In @Mut Box2<@RO K, @Mut Cell> the bound of E reads @RO D<@Mut Cell>.
    K extends D<@Mut Cell>.  In abstract-state code a readonly K is a
    readonly D<@Mut Cell>, so the check used to pass.  In readonly-state code
    (and in transitive-state code) a readonly K is only a D<@Lost Cell>: the
    code cannot rely on the superclass argument being mutable.  So @RO K is
    not below @RO D<@Mut Cell> in those modes, and the type
    @Mut Box2<@RO K, @Mut Cell> is not a well-formed type use anywhere.  The
    reference checker reports:

      Owner, bx: in method mode RS: @RO K is not a subtype of @RO D<@Mut Cell>

    Consequences proved below: the field bx of Owner is not well formed,
    Owner is not a well-formed class, the class table is not well formed, the
    allocation of the box in main has no typing, and main has no typing.

    What is kept from the earlier version because it still holds: the type
    @RO Box2<@RO K, @Lost Cell> is still a well-formed type use with both
    bound checks skipped, Box2.mix is still a well-formed method, the body of
    attack is still typable statement by statement and attack is still a
    well-formed method, and every class other than Owner is still well
    formed.  The rejection is at the declaration of the field (and at the
    allocation in main), not inside attack.  The well-formedness of the
    table, the run of the program and the changed field are gone.  The
    labels STEP (a) to STEP (f) on kept lemmas are those of the earlier
    version: the steps of the route the program used to take. *)

(* ------------------THE PROGRAM------------------*)

Definition ROObject : qualified_type := TClass RO 0 [].
Definition MutObject : qualified_type := TClass Mut 0 [].
Definition RDMCell : qualified_type := TClass RDM 1 [].
Definition MutCell : qualified_type := TClass Mut 1 [].
Definition LostCell : qualified_type := TClass Lost 1 [].
Definition tE : qualified_type := TVar TVSub ClassVar 0.
Definition tX : qualified_type := TVar TVSub ClassVar 1.
Definition RODX : qualified_type := TClass RO 2 [tX].
Definition RODMutCell : qualified_type := TClass RO 2 [MutCell].
Definition ROK : qualified_type := TClass RO 3 [].
Definition MutK : qualified_type := TClass Mut 3 [].
Definition ROBoxT : qualified_type := TClass RO 4 [ROK; LostCell].
Definition LostBoxT : qualified_type := TClass Lost 4 [ROK; LostCell].
Definition MutBox : qualified_type := TClass Mut 4 [ROK; MutCell].
Definition RDMBoxEX : qualified_type := TClass RDM 4 [tE; tX].
Definition RDMOwner : qualified_type := TClass RDM 5 [].
Definition MutOwner : qualified_type := TClass Mut 5 [].

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

Definition KDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 3; ctparams := [];
                     super := Some (2, [MutCell]) |};
     body := {| fields := []; methods := [] |} |}.

Definition item_field : field_def :=
  {| assignability := Assignable; ftype := tE |}.
Definition hold_field : field_def :=
  {| assignability := RDA; ftype := RDMCell |}.

Definition mix : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mqparams := 0;
          mret := ROObject;
          mname := 0;
          mreceiver := RDMBoxEX;
          mparams := [] |};
     mbody :=
       {| mbody_stmt :=
            SSeq (SLocal RODX 1)
            (SSeq (SLocal tX 2)
            (SSeq (SLocal RDMCell 3)
            (SSeq (SLocal RDMCell 4)
            (SSeq (SLocal ROObject 5)
            (SSeq (SVarAss 1 (EField 0 0))
            (SSeq (SVarAss 2 (EField 1 0))
            (SSeq (SVarAss 3 (EVar 2))
            (SSeq (SVarAss 4 (EField 0 1))
                  (SFldWrite 3 0 4)))))))));
          mreturn := 5 |} |}.

Definition BoxDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 4;
                     ctparams := [RODX; RDMCell];
                     super := Some (0, []) |};
     body := {| fields := [item_field; hold_field]; methods := [mix] |} |}.

Definition bx_field : field_def :=
  {| assignability := RDA; ftype := MutBox |}.

Definition attack : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mqparams := 0;
          mret := ROObject;
          mname := 1;
          mreceiver := RDMOwner;
          mparams := [ROObject] |};
     mbody :=
       {| mbody_stmt :=
            SSeq (SLocal ROBoxT 2)
            (SSeq (SLocal MutCell 3)
            (SSeq (SLocal ROObject 4)
            (SSeq (SLocal MutCell 5)
            (SSeq (SLocal MutK 6)
            (SSeq (SLocal ROObject 7)
            (SSeq (SLocal MutCell 8)
            (SSeq (SVarAss 2 (EField 0 0))
            (SSeq (SNew 5 Mut_c 1 [] [3; 4])
            (SSeq (SNew 6 Mut_c 3 [] [5])
            (SSeq (SFldWrite 2 0 6)
            (SSeq (SCall 7 0 2 [] [] [])
            (SSeq (SVarAss 8 (EField 5 0))
                  (SFldWrite 8 1 1)))))))))))));
          mreturn := 1 |} |}.

Definition OwnerDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 5; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := [bx_field]; methods := [attack] |} |}.

Definition CT : class_table :=
  [ObjectDef; CellDef; DDef; KDef; BoxDef; OwnerDef].

Definition prefix : stmt :=
  SSeq (SLocal MutObject 1)
  (SSeq (SLocal MutCell 2)
  (SSeq (SLocal MutCell 3)
  (SSeq (SLocal ROK 4)
  (SSeq (SLocal MutBox 5)
  (SSeq (SLocal MutOwner 6)
  (SSeq (SLocal MutObject 7)
  (SSeq (SLocal ROObject 8)
  (SSeq (SNew 1 Mut_c 0 [] [])
  (SSeq (SNew 3 Mut_c 1 [] [2; 1])
  (SSeq (SNew 5 Mut_c 4 [ROK; MutCell] [4; 3])
  (SSeq (SNew 6 Mut_c 5 [] [5])
        (SNew 7 Mut_c 0 [] [])))))))))))).

Definition callA : stmt := SCall 8 1 6 [] [] [7].

Definition main : stmt := SSeq prefix callA.

(** Bound environments: main and the class-level checks; the body of mix;
    the body of attack. *)
Definition Δ0 : tv_env := mk_tv_env [] [] AbstractState 0.
Definition ΔMix : tv_env := mk_tv_env [RODX; RDMCell] [] ReadonlyState 0.
Definition ΔR : tv_env := mk_tv_env [] [] ReadonlyState 0.

(* ------------------SMALL TACTICS AND FACTS------------------*)

Ltac qs := (apply q_refl; discriminate) || apply q_rd || apply q_bot.

(** Classes 0, 1, 3, 5 take no type arguments and are declared @RDM: any
    written qualifier other than @Lost is fine. *)
Lemma wf_plain : forall Δ top q0 C,
  C = 0 \/ C = 1 \/ C = 3 \/ C = 5 -> q0 <> Lost ->
  wf_stype CT Δ top (TClass q0 C []).
Proof.
  intros Δ top q0 C HC Hq.
  destruct HC as [-> | [-> | [-> | ->]]];
    (eapply wfs_class;
       [reflexivity | right | reflexivity | constructor | constructor]);
    destruct q0; cbn; try qs; congruence.
Qed.

Lemma wf_use : forall Δ q0 C,
  C = 0 \/ C = 1 \/ C = 3 \/ C = 5 -> q0 <> Lost ->
  wf_stypeuse CT Δ (TClass q0 C []).
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

(** Inside Box2, X is below its bound and hence a readonly Object. *)
Lemma sub_tX_ROObject : forall mt,
  qualified_type_subtype CT (mk_tv_env [RODX; RDMCell] [] mt 0) tX ROObject.
Proof.
  intros mt. eapply qtype_trans.
  - apply qtype_var_bound with (B := RDMCell). reflexivity.
  - apply sub_Cell_ROObject.
Qed.

(** The bound of E, @RO D<X>, is a well-formed type inside Box2.  Its one
    bound check (X below @RO Object) is performed and passes. *)
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

(** In abstract-state code a readonly K is a readonly D of mutable Cells:
    the superclass argument @Mut Cell read through the @RO head stays
    @Mut Cell. *)
Lemma sub_ROK_RODMutCell : forall cb mb kq,
  qualified_type_subtype CT (mk_tv_env cb mb AbstractState kq) ROK RODMutCell.
Proof.
  intros cb mb kq. apply qtype_hier.
  eapply si_step; [reflexivity|]. cbn. apply si_refl.
Qed.

(** The two bound checks of @Mut Box2<@RO K, @Mut Cell> are both performed:
    the bound of E reads @RO D<@Mut Cell> and the bound of X reads @Mut Cell,
    both fully known. *)
Lemma step_g_bounds_read :
  subst [ROK; MutCell] [] [] (adapt AbstractState Mut RODX) = RODMutCell /\
  subst [ROK; MutCell] [] [] (adapt AbstractState Mut RDMCell) = MutCell /\
  lost_free RODMutCell /\ lost_free MutCell.
Proof.
  split; [reflexivity|]. split; [reflexivity|]. split; lf.
Qed.

(** STEP (b).  The type @RO Box2<@RO K, @Lost Cell> is a well-formed type use
    in every bound environment.  The head is fine (@RO on an @RDM class), the
    arguments are well formed (@Lost is allowed in an argument position), and
    NEITHER argument is compared with its bound: read through the @RO head
    and the written arguments, the bound of E is @RO D<@Lost Cell> and the
    bound of X is @Lost Cell; both contain @Lost, so both checks are
    skipped. *)
Lemma step_b_bounds_skipped :
  subst [ROK; LostCell] [] [] (adapt AbstractState RO RODX)
    = TClass RO 2 [LostCell] /\
  subst [ROK; LostCell] [] [] (adapt AbstractState RO RDMCell) = LostCell /\
  ~ lost_free (TClass RO 2 [LostCell]) /\
  ~ lost_free LostCell.
Proof.
  split; [reflexivity|]. split; [reflexivity|]. split.
  - intros [_ [[H _] _]]. apply H. reflexivity.
  - intros [H _]. apply H. reflexivity.
Qed.

Lemma step_b_wf_ROBoxT_gen : forall Δ top, wf_stype CT Δ top ROBoxT.
Proof.
  intros Δ top.
  eapply wfs_class; [reflexivity | right; cbn; apply q_rd | reflexivity | |].
  - constructor; [apply wf_plain; [tauto | discriminate]|].
    constructor; [|constructor].
    eapply wfs_class;
      [reflexivity | left; split; reflexivity | reflexivity
      | constructor | constructor].
  - constructor; [|constructor; [|constructor]]; cbn.
    + (* @RO K against @RO D<@Lost Cell>, in every mode *)
      intros m. eapply qtype_trans.
      * apply qtype_hier. eapply si_step; [reflexivity|]. cbn. apply si_refl.
      * apply qtype_qual; [cbn; lia | apply q_rd|].
        constructor; [|constructor].
        apply tas_class; [|constructor].
        destruct m; cbn; unfold arg_q_sub; auto.
    + (* @Lost Cell against @Lost Cell *)
      intros m. apply qtype_hier. apply si_refl.
Qed.

Lemma wf_ROObject : forall Δ, wf_stypeuse CT Δ ROObject.
Proof. intros. wfp. Qed.
Lemma wf_MutObject : forall Δ, wf_stypeuse CT Δ MutObject.
Proof. intros. wfp. Qed.
Lemma wf_RDMCell : forall Δ, wf_stypeuse CT Δ RDMCell.
Proof. intros. wfp. Qed.
Lemma wf_MutCell : forall Δ, wf_stypeuse CT Δ MutCell.
Proof. intros. wfp. Qed.
Lemma wf_ROK : forall Δ, wf_stypeuse CT Δ ROK.
Proof. intros. wfp. Qed.
Lemma wf_MutK : forall Δ, wf_stypeuse CT Δ MutK.
Proof. intros. wfp. Qed.
Lemma wf_RDMOwner : forall Δ, wf_stypeuse CT Δ RDMOwner.
Proof. intros. wfp. Qed.
Lemma wf_MutOwner : forall Δ, wf_stypeuse CT Δ MutOwner.
Proof. intros. wfp. Qed.
Lemma step_b_wf_ROBoxT : forall Δ, wf_stypeuse CT Δ ROBoxT.
Proof. intros. apply step_b_wf_ROBoxT_gen. Qed.
Lemma wf_RODX_mix : wf_stypeuse CT ΔMix RODX.
Proof. apply wf_RODX. Qed.
Lemma wf_tX_mix : wf_stypeuse CT ΔMix tX.
Proof. eapply wf_tvar. reflexivity. Qed.

(** The declared receiver of mix.  Both bound checks are performed: read
    through the @RDM head the bounds are @RO D<X> and @RDM Cell, and E and X
    are below them because those are their declared bounds. *)
Lemma wf_RDMBoxEX_mix : wf_stypeuse CT ΔMix RDMBoxEX.
Proof.
  eapply wfs_class; [reflexivity | right; cbn; qs | reflexivity | |].
  - constructor; [eapply wf_tvar; reflexivity|].
    constructor; [eapply wf_tvar; reflexivity | constructor].
  - constructor; [|constructor; [|constructor]]; cbn.
    + intros m. apply qtype_var_bound. reflexivity.
    + intros m. apply qtype_var_bound. reflexivity.
Qed.

Create HintDb dbq.
Local Hint Resolve wf_ROObject wf_MutObject wf_RDMCell wf_MutCell wf_ROK
  wf_MutK wf_RDMOwner wf_MutOwner step_b_wf_ROBoxT
  wf_RODX_mix wf_tX_mix wf_RDMBoxEX_mix : dbq.

Ltac wfenv :=
  split; [cbn; lia |
          cbn; repeat (apply Forall_cons; [solve [auto with dbq]|]);
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

(** The one field of K: the field f of D with X replaced by @Mut Cell. *)
Definition Kf_field : field_def :=
  {| assignability := RDA; ftype := MutCell |}.

Lemma collect_K : CollectFields CT 3 [Kf_field].
Proof.
  change (CollectFields CT 3
            (map (subst_field [MutCell]) [f_field]
               ++ Syntax.fields (body KDef))).
  eapply CF_Inherit; try reflexivity. apply collect_D.
Qed.

Lemma collect_Box : CollectFields CT 4 [item_field; hold_field].
Proof.
  change (CollectFields CT 4
            (map (subst_field []) [] ++ Syntax.fields (body BoxDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma collect_Owner : CollectFields CT 5 [bx_field].
Proof.
  change (CollectFields CT 5
            (map (subst_field []) [] ++ Syntax.fields (body OwnerDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

(** Field 1 of Cell, [value], is receiver-dependent assignable. *)
Lemma value_is_rda : sf_assignability_rel CT 1 1 RDA.
Proof.
  exists value_field. split; [|reflexivity].
  eapply FL_Found; [apply collect_Cell | reflexivity].
Qed.

Lemma cache_is_assignable : sf_assignability_rel CT 1 0 Assignable.
Proof.
  exists cache_field. split; [|reflexivity].
  eapply FL_Found; [apply collect_Cell | reflexivity].
Qed.

Lemma item_is_assignable : sf_assignability_rel CT 4 0 Assignable.
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

Lemma find_mix : FindMethodWithName CT 4 0 4 mix.
Proof. eapply FOM_Here; reflexivity. Qed.

Lemma find_attack : FindMethodWithName CT 5 1 5 attack.
Proof. eapply FOM_Here; reflexivity. Qed.

Ltac ty_local :=
  eapply ST_Local;
    [wfenv | solve [auto with dbq] | reflexivity | reflexivity | reflexivity].

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

(* ------------------WHAT STILL HOLDS: THE METHODS AND THE OTHER CLASSES------------------*)

(** *** Box2.mix *)

Definition sΓMix : s_env :=
  [RDMBoxEX; RODX; tX; RDMCell; RDMCell; ROObject].

(** STEP (e), the four facts one at a time.

    d = this.item: through the @RDM receiver the field reads as the bare
    variable E, and E is below its bound @RO D<X>. *)
Lemma step_e_read_item :
  member_type ReadonlyState RDM [tE; tX] [] [] (ftype item_field) = tE /\
  qualified_type_subtype CT ΔMix tE RODX.
Proof.
  split; [reflexivity|]. apply qtype_var_bound. reflexivity.
Qed.

(** x = d.f: d is an @RO D<X>.  The field f of D is typed by D's parameter.
    Reading through the @RO receiver adapts written qualifiers only; a bare
    type variable has none, so the field reads as exactly X. *)
Lemma step_e_read_f :
  member_type ReadonlyState RO [tX] [] [] (ftype f_field) = tX.
Proof. reflexivity. Qed.

(** yy = x: X is below its bound @RDM Cell. *)
Lemma step_e_X_below_bound : qualified_type_subtype CT ΔMix tX RDMCell.
Proof. apply qtype_var_bound. reflexivity. Qed.

(** yy.cache = h: through the @RDM reference yy the field cache reads
    @RDM Cell, which is the type of h, and the slot is assignable. *)
Lemma step_e_write_cache :
  member_type ReadonlyState RDM [] [] [] (ftype cache_field) = RDMCell /\
  vpa_a ReadonlyState RDM (assignability cache_field) = Assignable.
Proof. split; reflexivity. Qed.

Lemma step_e_mix_body_typed :
  stmt_typing CT ΔMix [RDMBoxEX] ReadonlyState (mbody_stmt (mbody mix)) sΓMix.
Proof.
  cbn. unfold sΓMix.
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  ty_seq; [ty_local|]. ty_seq; [ty_local|].
  cbn.
  (* d = this.item *)
  ty_seq.
  { eapply ST_VarAss with (Tx := RODX) (Te := tE);
      [wfenv | | discriminate | reflexivity | ].
    - eapply ET_Field with (x := 0) (T := RDMBoxEX) (qx := RDM) (C := 4)
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
  ty_seq.
  { eapply ST_VarAss with (Tx := RDMCell) (Te := tX);
      [wfenv | | discriminate | reflexivity | ].
    - apply ET_Var; [wfenv | reflexivity].
    - apply qtype_var_bound. reflexivity. }
  (* h = this.hold *)
  ty_seq.
  { eapply ST_VarAss with (Tx := RDMCell) (Te := RDMCell);
      [wfenv | | discriminate | reflexivity | refl_sub].
    eapply ET_Field with (x := 0) (T := RDMBoxEX) (qx := RDM) (C := 4)
      (Ts := [tE; tX]) (fDef := hold_field);
      [wfenv | reflexivity | reflexivity | fl collect_Box]. }
  (* yy.cache = h *)
  eapply ST_FldWrite with (Tx := RDMCell) (Ty := RDMCell) (qx := RDM)
    (C := 1) (Ts := []) (fieldT := cache_field);
    [wfenv | reflexivity | reflexivity | reflexivity | fl collect_Cell
    | | reflexivity].
  split; [cbn; refl_sub | lf].
Qed.

(** STEP (f).  The signature of mix has no mutable position, reading the
    type variables through their bounds: the receiver is
    @RDM Box2<E, X>, E is read as @RO D<X>, X as @RDM Cell. *)
Lemma step_f_mix_no_mutable_roots :
  signature_has_no_mutable_roots ΔMix (msignature mix).
Proof.
  split; [|constructor].
  cbn. constructor; [discriminate|].
  constructor; [|constructor; [|constructor]].
  - eapply nm_var; [reflexivity|].
    constructor; [discriminate|]. constructor; [|constructor].
    eapply nm_var; [reflexivity|]. constructor; [discriminate | constructor].
  - eapply nm_var; [reflexivity|]. constructor; [discriminate | constructor].
Qed.

Lemma wf_mix : wf_method CT 4 mix.
Proof.
  unfold wf_method.
  change (method_tv_env CT 4 (msignature mix)) with ΔMix.
  split; [apply receiver_plain_ok; left; exists RDM; reflexivity|].
  split; [constructor|].
  split; [apply wf_ROObject|].
  split.
  { exists sΓMix, ROObject. split; [|split].
    - apply step_e_mix_body_typed.
    - reflexivity.
    - refl_sub. }
  split; [no_override|].
  intros _. apply step_f_mix_no_mutable_roots.
Qed.

(** *** Owner.attack *)

Definition sΓAtk : s_env :=
  [RDMOwner; ROObject; ROBoxT; MutCell; ROObject; MutCell; MutK; ROObject;
   MutCell].

(** STEP (a).  rb = this.bx.  In readonly-state code the declared field type
    @Mut Box2<@RO K, @Mut Cell>, read through the @RDM receiver, is
    @Lost Box2<@RO K, @Lost Cell>; that is a subtype of the declared type of
    rb, @RO Box2<@RO K, @Lost Cell> (the head widens to @RO, the arguments
    are the same). *)
Lemma step_a_field_read :
  member_type ReadonlyState RDM [] [] [] (ftype bx_field) = LostBoxT /\
  (forall Δ, qualified_type_subtype CT Δ LostBoxT ROBoxT).
Proof.
  split; [reflexivity|]. intros Δ.
  apply qtype_qual; [cbn; lia | apply q_rd | apply Forall2_targ_sub_refl].
Qed.

Lemma step_a_typed :
  stmt_typing CT ΔR sΓAtk ReadonlyState (SVarAss 2 (EField 0 0)) sΓAtk.
Proof.
  unfold sΓAtk.
  eapply ST_VarAss with (Tx := ROBoxT) (Te := LostBoxT);
    [wfenv | | discriminate | reflexivity | apply step_a_field_read].
  eapply ET_Field with (x := 0) (T := RDMOwner) (qx := RDM) (C := 5)
    (Ts := []) (fDef := bx_field);
    [wfenv | reflexivity | reflexivity | fl collect_Owner].
Qed.

(** The two allocations inside attack.  A fresh @Mut Cell: read through the
    @Mut allocation in readonly-state code its fields are @Mut Cell and
    @RO Object. *)
Lemma alloc_c0_typed :
  stmt_typing CT ΔR sΓAtk ReadonlyState (SNew 5 Mut_c 1 [] [3; 4]) sΓAtk.
Proof.
  unfold sΓAtk.
  eapply ST_New with (qc := Mut_c) (Tx := MutCell)
    (argtypes := [MutCell; ROObject]);
    [wfenv | reflexivity | reflexivity | reflexivity | discriminate
    | reflexivity | apply wf_MutCell | constructor | constructor
    | apply collect_Cell | | ].
  - constructor; [|constructor; [|constructor]]; cbn;
      (split; [refl_sub | lf]).
  - cbn. refl_sub.
Qed.

(** A fresh @Mut K: its one field, declared X in D and @Mut Cell in K, read
    through the @Mut allocation in readonly-state code is @Mut Cell, and c0
    is a @Mut Cell.  (This is where the earlier probe was stopped: it
    allocated the K as @RDM.) *)
Lemma alloc_K_field_read :
  member_type ReadonlyState (qc2q Mut_c) [] [] [] (ftype Kf_field) = MutCell.
Proof. reflexivity. Qed.

Lemma alloc_v_typed :
  stmt_typing CT ΔR sΓAtk ReadonlyState (SNew 6 Mut_c 3 [] [5]) sΓAtk.
Proof.
  unfold sΓAtk.
  eapply ST_New with (qc := Mut_c) (Tx := MutK) (argtypes := [MutCell]);
    [wfenv | reflexivity | reflexivity | reflexivity | discriminate
    | reflexivity | apply wf_MutK | constructor | constructor
    | apply collect_K | | ].
  - constructor; [|constructor]; cbn. split; [refl_sub | lf].
  - cbn. refl_sub.
Qed.

(** STEP (c).  rb.item = v.  The field type E, read through rb's arguments,
    is @RO K, which has no unknown position; a @Mut K is a subtype of @RO K;
    the slot is assignable through a readonly reference in readonly-state
    code. *)
Lemma step_c_field_write_typed :
  member_type ReadonlyState RO [ROK; LostCell] [] [] (ftype item_field) = ROK /\
  lost_free ROK /\
  (forall Δ, qualified_type_subtype CT Δ MutK ROK) /\
  vpa_a ReadonlyState RO (assignability item_field) = Assignable /\
  stmt_typing CT ΔR sΓAtk ReadonlyState (SFldWrite 2 0 6) sΓAtk.
Proof.
  split; [reflexivity|]. split; [lf|].
  split; [intros Δ; qual_sub|]. split; [reflexivity|].
  eapply ST_FldWrite with (Tx := ROBoxT) (Ty := MutK) (qx := RO)
    (C := 4) (Ts := [ROK; LostCell]) (fieldT := item_field);
    [unfold sΓAtk; wfenv | reflexivity | reflexivity | reflexivity
    | fl collect_Box | | reflexivity].
  split; [cbn; qual_sub | lf].
Qed.

(** STEP (d).  ig = rb.mix() is typed.  The declared receiver of mix is
    @RDM Box2<E,X>; receiver adaptation makes it the caller's view,
    @RO Box2<@RO K, @Lost Cell>.  Its qualifier is known, which is all the
    receiver check asks; the unknown type argument is the reference's own. *)
Lemma step_d_call_typed :
  stmt_typing CT ΔR sΓAtk ReadonlyState (SCall 7 0 2 [] [] []) sΓAtk.
Proof.
  eapply ST_Call with (Tx := ROObject) (Ty := ROBoxT)
    (argtypes := []) (qy := RO) (C := 4) (Ts := [ROK; LostCell]) (D := 4)
    (Vs := [ROK; LostCell]) (mdef := mix);
    [unfold sΓAtk; wfenv | reflexivity | reflexivity | reflexivity
    | reflexivity | apply find_mix | apply si_refl | discriminate
    | constructor | constructor | reflexivity | constructor | | |
    | apply method_subtyping_refl | reflexivity | constructor | recv_known].
  - cbn. refl_sub.
  - cbn; apply qtype_hier; apply si_refl.
  - constructor.
Qed.

(** m = c0.cache: through the mutable c0 the receiver-dependent field reads
    @Mut Cell. *)
Lemma read_cache_typed :
  member_type ReadonlyState Mut [] [] [] (ftype cache_field) = MutCell /\
  stmt_typing CT ΔR sΓAtk ReadonlyState (SVarAss 8 (EField 5 0)) sΓAtk.
Proof.
  split; [reflexivity|]. unfold sΓAtk.
  eapply ST_VarAss with (Tx := MutCell) (Te := MutCell);
    [wfenv | | discriminate | reflexivity | refl_sub].
  eapply ET_Field with (x := 5) (T := MutCell) (qx := Mut) (C := 1)
    (Ts := []) (fDef := cache_field);
    [wfenv | reflexivity | reflexivity | fl collect_Cell].
Qed.

(** m.value = y: through the mutable m the receiver-dependent-assignable
    slot is assignable. *)
Lemma write_value_typed :
  vpa_a ReadonlyState Mut (assignability value_field) = Assignable /\
  stmt_typing CT ΔR sΓAtk ReadonlyState (SFldWrite 8 1 1) sΓAtk.
Proof.
  split; [reflexivity|].
  eapply ST_FldWrite with (Tx := MutCell) (Ty := ROObject) (qx := Mut)
    (C := 1) (Ts := []) (fieldT := value_field);
    [unfold sΓAtk; wfenv | reflexivity | reflexivity | reflexivity
    | fl collect_Cell | | reflexivity].
  split; [cbn; refl_sub | lf].
Qed.

Lemma attack_body_typed :
  stmt_typing CT ΔR [RDMOwner; ROObject] ReadonlyState
    (mbody_stmt (mbody attack)) sΓAtk.
Proof.
  cbn. unfold sΓAtk.
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  ty_seq; [ty_local|].
  cbn.
  ty_seq; [apply step_a_typed|].
  ty_seq; [apply alloc_c0_typed|].
  ty_seq; [apply alloc_v_typed|].
  ty_seq; [apply step_c_field_write_typed|].
  ty_seq; [apply step_d_call_typed|].
  ty_seq; [apply read_cache_typed|].
  apply write_value_typed.
Qed.

Lemma attack_no_mutable_roots :
  signature_has_no_mutable_roots ΔR (msignature attack).
Proof.
  split.
  - cbn. constructor; [discriminate | constructor].
  - cbn. constructor; [|constructor].
    constructor; [discriminate | constructor].
Qed.

Lemma wf_attack : wf_method CT 5 attack.
Proof.
  unfold wf_method.
  change (method_tv_env CT 5 (msignature attack)) with ΔR.
  split; [apply receiver_plain_ok; left; exists RDM; reflexivity|].
  split; [constructor|].
  split; [apply wf_ROObject|].
  split.
  { exists sΓAtk, ROObject. split; [|split].
    - apply attack_body_typed.
    - reflexivity.
    - refl_sub. }
  split; [no_override|].
  intros _. apply attack_no_mutable_roots.
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

Lemma wf_KDef : wf_class CT KDef.
Proof.
  wf_other 2 [MutCell] DDef.
  - constructor.
  - eapply wfs_class; [reflexivity | right; cbn; qs | reflexivity | |].
    + constructor; [apply wf_plain; [tauto | discriminate] | constructor].
    + constructor; [|constructor]. intros m. cbn. apply sub_Cell_ROObject.
  - constructor; [lf | constructor].
  - constructor; [|constructor].
    split; [lf | intros m; apply sub_Cell_ROObject].
  - left. reflexivity.
  - constructor.
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
  - constructor; [|constructor; [|constructor]]; unfold wf_field; cbn.
    + eapply wfs_var; [reflexivity|]. right. discriminate.
    + wfp.
  - constructor; [apply wf_mix | constructor].
  - constructor; [intros [] | constructor].
Qed.

(* ------------------THE REJECTION------------------*)

(** *** (a) What a readonly K is, mode by mode *)

(** The classes and argument lists a readonly K can be viewed at in
    readonly-state and transitive-state code. *)
Definition reach (C : class_name) (Ts : list qualified_type) : Prop :=
  (C = 3 /\ Ts = []) \/ (C = 2 /\ Ts = [LostCell]) \/ (C = 0 /\ Ts = []).

Definition protecting (mt : method_scope) : Prop :=
  mt = ReadonlyState \/ mt = TransitiveState.

Lemma super_inst_reach : forall mt C Ts D Vs,
  protecting mt ->
  super_inst CT mt RO C Ts D Vs ->
  reach C Ts -> reach D Vs.
Proof.
  intros mt C Ts D Vs Hmt H. induction H; intros Hr; [exact Hr|].
  apply IHsuper_inst.
  destruct Hr as [[-> ->] | [[-> ->] | [-> ->]]]; cbn in Hparent.
  - injection Hparent as <- <-. right. left.
    destruct Hmt as [-> | ->]; split; reflexivity.
  - injection Hparent as <- <-. right. right. split; reflexivity.
  - discriminate.
Qed.

(** The supertypes of @RO K in those modes. *)
Definition sup_ROK (T : qualified_type) : Prop :=
  T = ROK \/ T = TClass RO 2 [LostCell] \/ T = ROObject.

(** Every supertype of a type in the set is in the set, whatever the type
    variables in scope and their bounds. *)
Lemma sup_ROK_closed : forall Δ,
  protecting (tv_mode Δ) ->
  forall T U, qualified_type_subtype CT Δ T U -> sup_ROK T -> sup_ROK U.
Proof.
  intros Δ Hmode T U H. unfold sup_ROK, ROK, ROObject, LostCell.
  induction H; intros Hs.
  - assert (Hq2 : q2 = RO /\ q1 = RO).
    { destruct Hs as [Hs | [Hs | Hs]]; injection Hs as -> _ _;
        inversion Hqsub; subst; split; reflexivity || discriminate. }
    destruct Hq2 as [-> ->].
    destruct Hs as [Hs | [Hs | Hs]]; injection Hs as -> ->.
    + inversion Hargs; subst. left. reflexivity.
    + inversion Hargs as [|a b l l' Hab Hl]; subst.
      inversion Hl; subst.
      inversion Hab as [|qa qb Ca Tsa Usa Hq Hargs'|]; subst.
      inversion Hargs'; subst.
      destruct Hq as [-> | [_ [Hq | [Hq | Hq]]]]; try discriminate.
      right. left. reflexivity.
    + inversion Hargs; subst. right. right. reflexivity.
  - assert (Hr : q1 = RO /\ reach C Ts).
    { destruct Hs as [Hs | [Hs | Hs]]; injection Hs as -> -> ->;
        (split; [reflexivity|]); unfold reach, LostCell; auto. }
    destruct Hr as [-> Hr].
    destruct (super_inst_reach _ _ _ _ _ Hmode Hsuper Hr)
      as [[-> ->] | [[-> ->] | [-> ->]]]; auto.
  - destruct Hs as [Hs | [Hs | Hs]]; discriminate.
  - destruct Hs as [Hs | [Hs | Hs]]; discriminate.
  - destruct Hs as [Hs | [Hs | Hs]]; discriminate.
  - destruct Hs as [Hs | [Hs | Hs]]; discriminate.
  - destruct Hs as [Hs | [Hs | Hs]]; discriminate.
  - destruct Hs as [Hs | [Hs | Hs]]; discriminate.
  - destruct Hs as [Hs | [Hs | Hs]]; discriminate.
  - destruct Hs as [Hs | [Hs | Hs]]; discriminate.
  - destruct Hs as [Hs | [Hs | Hs]]; discriminate.
  - destruct Hs as [Hs | [Hs | Hs]]; discriminate.
  - destruct Hs as [Hs | [Hs | Hs]]; discriminate.
  - auto.
Qed.

(** The characterisation: in readonly-state and transitive-state code every
    supertype of @RO K is @RO K, @RO D<@Lost Cell>, or @RO Object. *)
Theorem supertypes_of_ROK : forall Δ U,
  protecting (tv_mode Δ) ->
  qualified_type_subtype CT Δ ROK U ->
  U = ROK \/ U = TClass RO 2 [LostCell] \/ U = ROObject.
Proof.
  intros Δ U Hmode H.
  apply (sup_ROK_closed Δ Hmode _ _ H). left. reflexivity.
Qed.

(** In those modes @RO K is not below @RO D<@Mut Cell>, for every choice of
    type variables in scope and their bounds. *)
Theorem ROK_not_below_RODMutCell : forall Δ,
  tv_mode Δ = ReadonlyState \/ tv_mode Δ = TransitiveState ->
  ~ qualified_type_subtype CT Δ ROK RODMutCell.
Proof.
  intros Δ Hmode H.
  destruct (supertypes_of_ROK Δ _ Hmode H) as [E | [E | E]]; discriminate.
Qed.

Corollary ROK_not_below_RODMutCell_RS : forall cb mb kq,
  ~ qualified_type_subtype CT (mk_tv_env cb mb ReadonlyState kq) ROK RODMutCell.
Proof. intros. apply ROK_not_below_RODMutCell. left. reflexivity. Qed.

Corollary ROK_not_below_RODMutCell_TS : forall cb mb kq,
  ~ qualified_type_subtype CT (mk_tv_env cb mb TransitiveState kq) ROK RODMutCell.
Proof. intros. apply ROK_not_below_RODMutCell. right. reflexivity. Qed.

(** What it is instead. *)
Theorem ROK_below_RODLostCell : forall Δ,
  tv_mode Δ = ReadonlyState \/ tv_mode Δ = TransitiveState ->
  qualified_type_subtype CT Δ ROK (TClass RO 2 [LostCell]).
Proof.
  intros [cb mb mt kq] Hmode. cbn in Hmode. apply qtype_hier. cbn.
  eapply si_step; [reflexivity|].
  destruct Hmode as [-> | ->]; cbn; apply si_refl.
Qed.

(** Contrast: in abstract-state and in concrete-state code the check passes
    (the first of these is the lemma sub_ROK_RODMutCell kept above). *)
Theorem ROK_below_RODMutCell_other_modes : forall Δ,
  tv_mode Δ = AbstractState \/ tv_mode Δ = ConcreteState ->
  qualified_type_subtype CT Δ ROK RODMutCell.
Proof.
  intros [cb mb mt kq] Hmode. cbn in Hmode. apply qtype_hier. cbn.
  eapply si_step; [reflexivity|].
  destruct Hmode as [-> | ->]; cbn; apply si_refl.
Qed.

(** *** (b) The bound check fails *)

Theorem bound_check_fails : forall Δ, ~ bound_sub CT Δ ROK RODMutCell.
Proof.
  intros Δ H. specialize (H ReadonlyState). revert H.
  apply ROK_not_below_RODMutCell. left. reflexivity.
Qed.

(** The same for the two environments of the program: the class-level
    environment of Owner, which is also the environment of main. *)
Corollary bound_check_fails_Owner : ~ bound_sub CT Δ0 ROK RODMutCell.
Proof. apply bound_check_fails. Qed.

(** *** (c) The type, the field, the class, the table *)

(** @Mut Box2<@RO K, @Mut Cell> is not a well-formed type, in any
    environment and in argument position or not. *)
Theorem MutBox_not_wf : forall Δ top, ~ wf_stype CT Δ top MutBox.
Proof.
  intros Δ top H. unfold MutBox in H.
  inversion H as [top' q0 C Ts def Hfind Hhead Hlen Hargs Hbounds| |]; subst.
  cbn in Hfind. injection Hfind as <-.
  inversion Hbounds as [|T B l l' HE _]; subst.
  apply (bound_check_fails Δ). apply HE.
Qed.

Corollary MutBox_not_wf_use : forall Δ, ~ wf_stypeuse CT Δ MutBox.
Proof. intros Δ. apply MutBox_not_wf. Qed.

Corollary MutBox_not_wf_use_Owner : ~ wf_stypeuse CT Δ0 MutBox.
Proof. apply MutBox_not_wf_use. Qed.

Theorem bx_field_not_wf : forall Δ, ~ wf_field CT Δ bx_field.
Proof. intros Δ. apply MutBox_not_wf_use. Qed.

Theorem OwnerDef_not_wf : ~ wf_class CT OwnerDef.
Proof.
  intros H. inversion H.
  - discriminate.
  - match goal with
    | Hf : Forall (wf_field _ _) _ |- _ =>
        cbn in Hf; inversion Hf as [|? ? Hbx _]; subst
    end.
    revert Hbx. apply bx_field_not_wf.
Qed.

(** The program is rejected. *)
Theorem probe2_ct_not_wf : ~ wf_class_table CT.
Proof.
  intros [Hall _]. rewrite Forall_forall in Hall.
  apply OwnerDef_not_wf. apply Hall.
  cbn. tauto.
Qed.

(** *** (d) The allocation in main *)

(** new @Mut Box2<@RO K, @Mut Cell>(...) has no typing: in any environment,
    in any mode, into any variable, with any initialisers. *)
Theorem alloc_MutBox_rejected : forall Δ sΓ sΓ' mt x args,
  ~ stmt_typing CT Δ sΓ mt (SNew x Mut_c 4 [ROK; MutCell] args) sΓ'.
Proof.
  intros Δ sΓ sΓ' mt x args H. inversion H; subst.
  eapply MutBox_not_wf_use. eassumption.
Qed.

(** Declaring a local of that type is rejected as well. *)
Theorem local_MutBox_rejected : forall Δ sΓ sΓ' mt x,
  ~ stmt_typing CT Δ sΓ mt (SLocal MutBox x) sΓ'.
Proof.
  intros Δ sΓ sΓ' mt x H. inversion H; subst.
  eapply MutBox_not_wf_use. eassumption.
Qed.

Lemma seq_typed_inv : forall Δ sΓ mt s1 s2 sΓ'',
  stmt_typing CT Δ sΓ mt (SSeq s1 s2) sΓ'' ->
  exists sΓ', stmt_typing CT Δ sΓ mt s1 sΓ' /\ stmt_typing CT Δ sΓ' mt s2 sΓ''.
Proof.
  intros Δ sΓ mt s1 s2 sΓ'' H. inversion H; subst. eexists. split; eassumption.
Qed.

(** The entry code has no typing. *)
Theorem main_untypable : forall Δ sΓ mt sΓ',
  ~ stmt_typing CT Δ sΓ mt main sΓ'.
Proof.
  intros Δ sΓ mt sΓ' H. unfold main, prefix in H.
  apply seq_typed_inv in H. destruct H as (G1 & H & _).
  do 4 (apply seq_typed_inv in H; destruct H as (? & _ & H)).
  apply seq_typed_inv in H. destruct H as (? & H & _).
  revert H. apply local_MutBox_rejected.
Qed.

Print Assumptions supertypes_of_ROK.
Print Assumptions ROK_not_below_RODMutCell.
Print Assumptions ROK_below_RODLostCell.
Print Assumptions ROK_below_RODMutCell_other_modes.
Print Assumptions bound_check_fails.
Print Assumptions MutBox_not_wf.
Print Assumptions bx_field_not_wf.
Print Assumptions OwnerDef_not_wf.
Print Assumptions probe2_ct_not_wf.
Print Assumptions alloc_MutBox_rejected.
Print Assumptions local_MutBox_rejected.
Print Assumptions main_untypable.
Print Assumptions step_g_bounds_read.
Print Assumptions step_b_bounds_skipped.
Print Assumptions step_b_wf_ROBoxT_gen.
Print Assumptions wf_mix.
Print Assumptions attack_body_typed.
Print Assumptions wf_attack.
Print Assumptions wf_BoxDef.
