From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  GhostOverride.

(** Regression file for the mode-aware object-creation rule.

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
       @RDA @RDM Cell prot;                // field 1
    }
    class 3: @RDM class K extends D<@Mut Cell> {}
    class 4: @RDM class Box3<E extends @RDM D<X>, X extends @RDM Cell>
             extends Object {
       @Assignable E e1;                   // field 0
       // method 1, readonly-state
       @RS @RO Object mix(@RDM Box3<E,X> this) {
           @RDM D<X> d;   // var 1
           X x;           // var 2
           @RDM Cell yy;  // var 3
           @RDM Cell h;   // var 4
           @RO Object r;  // var 5, never assigned
           d = this.e1;  x = d.f;  yy = x;  h = d.prot;  yy.cache = h;
           return r;
       }
    }
    class 5: @RDM class Factory extends Object {
       // method 0, readonly-state
       @RS @RO Box3<@RDM K, @Lost Cell> make(@RDM Factory this) {
           @RO Box3<@RDM K, @Lost Cell> r;   // var 1, never assigned
           return r;
       }
    }
    class 6: @Mut class MutFactory extends Factory {
       // method 0, readonly-state, overrides Factory.make
       @RS @Mut Box3<@Mut K, @Mut Cell> make(@RO MutFactory this) {
           @Mut K n;                             // var 1, never assigned
           @Mut Box3<@Mut K, @Mut Cell> b;       // var 2
           b = new @Mut Box3<@Mut K, @Mut Cell>(n);
           return b;
       }
    }
    class 7: @RDM class Owner extends Object {
       @RDA @RDM Factory fac;              // field 0
       @RDA @RDM Cell secret;              // field 1
       // method 2, readonly-state
       @RS @RO Object attack(@RDM Owner this, @RO Object y) {
           @RDM Factory f;                       // var 2
           @RO Box3<@RDM K, @Lost Cell> rb;      // var 3
           @Mut Cell nc;                         // var 4, never assigned
           @RO Object n;                         // var 5, never assigned
           @Mut Cell c0;                         // var 6
           @RDM Cell s;                          // var 7
           @RDM K v;                             // var 8
           @RO Object ig;                        // var 9
           @Mut Cell m;                          // var 10
           f = this.fac;
           rb = f.make();
           c0 = new @Mut Cell(nc, n);
           s = this.secret;
           v = new @RDM K(c0, s);                // NOW REJECTED
           rb.e1 = v;
           ig = rb.mix();
           m = c0.cache;
           m.value = y;
           return y;
       }
    }

    main (variable 0 is the receiver, a @Mut Object; abstract-state mode):
      @Mut Object o;          // var 1
      @Mut Cell nc;           // var 2, never assigned
      @Mut Cell s0;           // var 3
      @Mut MutFactory mf;     // var 4
      @Mut Owner ow;          // var 5
      @Mut Object y;          // var 6
      @RO Object x;           // var 7
      o = new @Mut Object();
      s0 = new @Mut Cell(nc, o);
      mf = new @Mut MutFactory();
      ow = new @Mut Owner(mf, s0);
      y = new @Mut Object();
      x = ow.attack(y);                 // the call

    Method names are 0 (make), 1 (mix), 2 (attack).

    What changed.  When an object is created, each initialiser is checked
    against the type of the field it fills, and that field type is now read
    through the allocation qualifier in the mode of the code doing the
    allocation.  K extends D<@Mut Cell>, so the first field of a K is a
    @Mut Cell.  In readonly-state code, a @Mut field type read through an
    @RDM allocation is @Lost Cell: the allocating code does not know whether
    the new K will be seen as mutable or not.  A target type with an unknown
    position accepts no source, and c0 is a @Mut Cell.  So
    v = new @RDM K(c0, s) has no typing inside attack, attack is not a
    well-formed method, and the class table is not well formed.

    Everything else that the earlier version of this file established about
    the program still holds and is kept below: the declared type
    @RO Box3<@RDM K, @Lost Cell> is still a well-formed type use with both
    bound checks skipped, the override of make is still accepted, the write
    rb.e1 = v and the call rb.mix() are still typable as single statements,
    and every class other than Owner is still well formed.  The run of the
    program and the changed field are gone, because they were stated for a
    well-formed table. *)

(* ------------------THE PROGRAM------------------*)

Definition ROObject : qualified_type := TClass RO 0 [].
Definition MutObject : qualified_type := TClass Mut 0 [].
Definition RDMCell : qualified_type := TClass RDM 1 [].
Definition MutCell : qualified_type := TClass Mut 1 [].
Definition LostCell : qualified_type := TClass Lost 1 [].
Definition tE : qualified_type := TVar TVSub ClassVar 0.
Definition tX : qualified_type := TVar TVSub ClassVar 1.
Definition RDMDX : qualified_type := TClass RDM 2 [tX].
Definition MutDMutCell : qualified_type := TClass Mut 2 [MutCell].
Definition RDMK : qualified_type := TClass RDM 3 [].
Definition MutK : qualified_type := TClass Mut 3 [].
Definition ROBoxT : qualified_type := TClass RO 4 [RDMK; LostCell].
Definition MutBox : qualified_type := TClass Mut 4 [MutK; MutCell].
Definition RDMBoxEX : qualified_type := TClass RDM 4 [tE; tX].
Definition RDMFactory : qualified_type := TClass RDM 5 [].
Definition MutFactoryT : qualified_type := TClass Mut 5 [].
Definition ROMF : qualified_type := TClass RO 6 [].
Definition MutMF : qualified_type := TClass Mut 6 [].
Definition RDMOwner : qualified_type := TClass RDM 7 [].
Definition MutOwner : qualified_type := TClass Mut 7 [].

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
Definition prot_field : field_def :=
  {| assignability := RDA; ftype := RDMCell |}.

Definition DDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 2;
                     ctparams := [ROObject];
                     super := Some (0, []) |};
     body := {| fields := [f_field; prot_field]; methods := [] |} |}.

Definition KDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 3; ctparams := [];
                     super := Some (2, [MutCell]) |};
     body := {| fields := []; methods := [] |} |}.

Definition e1_field : field_def :=
  {| assignability := Assignable; ftype := tE |}.

Definition mix : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mqparams := 0;
          mret := ROObject;
          mname := 1;
          mreceiver := RDMBoxEX;
          mparams := [] |};
     mbody :=
       {| mbody_stmt :=
            SSeq (SLocal RDMDX 1)
            (SSeq (SLocal tX 2)
            (SSeq (SLocal RDMCell 3)
            (SSeq (SLocal RDMCell 4)
            (SSeq (SLocal ROObject 5)
            (SSeq (SVarAss 1 (EField 0 0))
            (SSeq (SVarAss 2 (EField 1 0))
            (SSeq (SVarAss 3 (EVar 2))
            (SSeq (SVarAss 4 (EField 1 1))
                  (SFldWrite 3 0 4)))))))));
          mreturn := 5 |} |}.

Definition BoxDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 4;
                     ctparams := [RDMDX; RDMCell];
                     super := Some (0, []) |};
     body := {| fields := [e1_field]; methods := [mix] |} |}.

Definition factory_make : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mqparams := 0;
          mret := ROBoxT;
          mname := 0;
          mreceiver := RDMFactory;
          mparams := [] |};
     mbody := {| mbody_stmt := SLocal ROBoxT 1; mreturn := 1 |} |}.

Definition FactoryDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 5; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := []; methods := [factory_make] |} |}.

Definition mf_make : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mqparams := 0;
          mret := MutBox;
          mname := 0;
          mreceiver := ROMF;
          mparams := [] |};
     mbody :=
       {| mbody_stmt :=
            SSeq (SLocal MutK 1)
            (SSeq (SLocal MutBox 2)
                  (SNew 2 Mut_c 4 [MutK; MutCell] [1]));
          mreturn := 2 |} |}.

Definition MutFactoryDef : class_def :=
  {| signature := {| class_qualifier := Mut_c; cname := 6; ctparams := [];
                     super := Some (5, []) |};
     body := {| fields := []; methods := [mf_make] |} |}.

Definition fac_field : field_def :=
  {| assignability := RDA; ftype := RDMFactory |}.
Definition secret_field : field_def :=
  {| assignability := RDA; ftype := RDMCell |}.

Definition attack : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mqparams := 0;
          mret := ROObject;
          mname := 2;
          mreceiver := RDMOwner;
          mparams := [ROObject] |};
     mbody :=
       {| mbody_stmt :=
            SSeq (SLocal RDMFactory 2)
            (SSeq (SLocal ROBoxT 3)
            (SSeq (SLocal MutCell 4)
            (SSeq (SLocal ROObject 5)
            (SSeq (SLocal MutCell 6)
            (SSeq (SLocal RDMCell 7)
            (SSeq (SLocal RDMK 8)
            (SSeq (SLocal ROObject 9)
            (SSeq (SLocal MutCell 10)
            (SSeq (SVarAss 2 (EField 0 0))
            (SSeq (SCall 3 0 2 [] [] [])
            (SSeq (SNew 6 Mut_c 1 [] [4; 5])
            (SSeq (SVarAss 7 (EField 0 1))
            (SSeq (SNew 8 RDM_c 3 [] [6; 7])
            (SSeq (SFldWrite 3 0 8)
            (SSeq (SCall 9 1 3 [] [] [])
            (SSeq (SVarAss 10 (EField 6 0))
                  (SFldWrite 10 1 1)))))))))))))))));
          mreturn := 1 |} |}.

Definition OwnerDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 7; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := [fac_field; secret_field]; methods := [attack] |} |}.

Definition CT : class_table :=
  [ObjectDef; CellDef; DDef; KDef; BoxDef; FactoryDef; MutFactoryDef; OwnerDef].

Definition prefix : stmt :=
  SSeq (SLocal MutObject 1)
  (SSeq (SLocal MutCell 2)
  (SSeq (SLocal MutCell 3)
  (SSeq (SLocal MutMF 4)
  (SSeq (SLocal MutOwner 5)
  (SSeq (SLocal MutObject 6)
  (SSeq (SLocal ROObject 7)
  (SSeq (SNew 1 Mut_c 0 [] [])
  (SSeq (SNew 3 Mut_c 1 [] [2; 1])
  (SSeq (SNew 4 Mut_c 6 [] [])
  (SSeq (SNew 5 Mut_c 7 [] [4; 3])
        (SNew 6 Mut_c 0 [] []))))))))))).

Definition callA : stmt := SCall 7 2 5 [] [] [6].

Definition main : stmt := SSeq prefix callA.

(** The bound environments of the four method bodies. *)
Definition ΔMix : tv_env := mk_tv_env [RDMDX; RDMCell] [] ReadonlyState 0.
Definition ΔR : tv_env := mk_tv_env [] [] ReadonlyState 0.

(* ------------------SMALL TACTICS AND FACTS------------------*)

Ltac qs := (apply q_refl; discriminate) || apply q_rd || apply q_bot.

(** Classes 0, 1, 3, 5, 7 take no type arguments and are declared @RDM: any
    written qualifier is fine. *)
Lemma wf_plain : forall Δ top q0 C,
  C = 0 \/ C = 1 \/ C = 3 \/ C = 5 \/ C = 7 -> q0 <> Lost ->
  wf_stype CT Δ top (TClass q0 C []).
Proof.
  intros Δ top q0 C HC Hq.
  destruct HC as [-> | [-> | [-> | [-> | ->]]]];
    (eapply wfs_class;
       [reflexivity | right | reflexivity | constructor | constructor]);
    destruct q0; cbn; try qs; congruence.
Qed.

Lemma wf_use : forall Δ q0 C,
  C = 0 \/ C = 1 \/ C = 3 \/ C = 5 \/ C = 7 -> q0 <> Lost ->
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

(** Inside Box3, X is below its bound and hence a readonly Object. *)
Lemma sub_tX_ROObject : forall mt,
  qualified_type_subtype CT (mk_tv_env [RDMDX; RDMCell] [] mt 0) tX ROObject.
Proof.
  intros mt. eapply qtype_trans.
  - apply qtype_var_bound with (B := RDMCell). reflexivity.
  - apply sub_Cell_ROObject.
Qed.

(** The bound of E, @RDM D<X>, is a well-formed type inside Box3. *)
Lemma wf_RDMDX : forall mt top,
  wf_stype CT (mk_tv_env [RDMDX; RDMCell] [] mt 0) top RDMDX.
Proof.
  intros mt top.
  eapply wfs_class; [reflexivity | right; cbn; qs | reflexivity | |].
  - constructor; [|constructor].
    eapply wfs_var; [reflexivity | left; reflexivity].
  - constructor; [|constructor]. intros m. cbn. apply sub_tX_ROObject.
Qed.

Lemma wf_tvar : forall mt top n B,
  nth_error [RDMDX; RDMCell] n = Some B ->
  wf_stype CT (mk_tv_env [RDMDX; RDMCell] [] mt 0) top (TVar TVSub ClassVar n).
Proof.
  intros. eapply wfs_var; [exact H | right; discriminate].
Qed.

(** A mutable K is a mutable D of mutable Cells, in every mode. *)
Lemma sub_MutK_MutDMutCell : forall Δ,
  qualified_type_subtype CT Δ MutK MutDMutCell.
Proof.
  intros [cb mb mt kq]. apply qtype_hier.
  eapply si_step; [reflexivity|].
  destruct mt; cbn; apply si_refl.
Qed.

(** LENIENCY (e), first half: the fully mutable Box3 type is well formed;
    both of its bound checks are required and both pass. *)
Lemma wf_MutBox_gen : forall Δ top, wf_stype CT Δ top MutBox.
Proof.
  intros Δ top.
  eapply wfs_class; [reflexivity | right; cbn; qs | reflexivity | |].
  - constructor; [apply wf_plain; [tauto | discriminate]|].
    constructor; [apply wf_plain; [tauto | discriminate] | constructor].
  - constructor; [|constructor; [|constructor]]; cbn.
    + intros m. apply sub_MutK_MutDMutCell.
    + intros m. refl_sub.
Qed.



(** The two skipped checks, spelled out: the adapted bounds are
    @Lost D<@Lost Cell> and @Lost Cell. *)
Lemma leniency_a_bounds_skipped :
  subst [RDMK; LostCell] [] [] (adapt AbstractState RO RDMDX)
    = TClass Lost 2 [LostCell] /\
  subst [RDMK; LostCell] [] [] (adapt AbstractState RO RDMCell) = LostCell /\
  ~ lost_free (TClass Lost 2 [LostCell]) /\
  ~ lost_free LostCell.
Proof.
  split; [reflexivity|]. split; [reflexivity|].
  split; intros [H _]; apply H; reflexivity.
Qed.

Lemma wf_MutMF_gen : forall Δ top, wf_stype CT Δ top MutMF.
Proof.
  intros. eapply wfs_class;
    [reflexivity | right; cbn; qs | reflexivity | constructor | constructor].
Qed.

Lemma wf_ROMF_gen : forall Δ top, wf_stype CT Δ top ROMF.
Proof.
  intros. eapply wfs_class;
    [reflexivity | right; cbn; qs | reflexivity | constructor | constructor].
Qed.

Lemma wf_ROObject : forall Δ, wf_stypeuse CT Δ ROObject.
Proof. intros. wfp. Qed.
Lemma wf_MutObject : forall Δ, wf_stypeuse CT Δ MutObject.
Proof. intros. wfp. Qed.
Lemma wf_RDMCell : forall Δ, wf_stypeuse CT Δ RDMCell.
Proof. intros. wfp. Qed.
Lemma wf_MutCell : forall Δ, wf_stypeuse CT Δ MutCell.
Proof. intros. wfp. Qed.
Lemma wf_RDMK : forall Δ, wf_stypeuse CT Δ RDMK.
Proof. intros. wfp. Qed.
Lemma wf_MutK : forall Δ, wf_stypeuse CT Δ MutK.
Proof. intros. wfp. Qed.
Lemma wf_RDMFactory : forall Δ, wf_stypeuse CT Δ RDMFactory.
Proof. intros. wfp. Qed.
Lemma wf_RDMOwner : forall Δ, wf_stypeuse CT Δ RDMOwner.
Proof. intros. wfp. Qed.
Lemma wf_MutOwner : forall Δ, wf_stypeuse CT Δ MutOwner.
Proof. intros. wfp. Qed.
Lemma wf_MutBox : forall Δ, wf_stypeuse CT Δ MutBox.
Proof. intros. apply wf_MutBox_gen. Qed.

Lemma wf_MutMF : forall Δ, wf_stypeuse CT Δ MutMF.
Proof. intros. apply wf_MutMF_gen. Qed.
Lemma wf_ROMF : forall Δ, wf_stypeuse CT Δ ROMF.
Proof. intros. apply wf_ROMF_gen. Qed.
Lemma wf_RDMDX_mix : wf_stypeuse CT ΔMix RDMDX.
Proof. apply wf_RDMDX. Qed.
Lemma wf_tX_mix : wf_stypeuse CT ΔMix tX.
Proof. eapply wf_tvar. reflexivity. Qed.
Lemma wf_RDMBoxEX_mix : wf_stypeuse CT ΔMix RDMBoxEX.
Proof.
  eapply wfs_class; [reflexivity | right; cbn; qs | reflexivity | |].
  - constructor; [eapply wf_tvar; reflexivity|].
    constructor; [eapply wf_tvar; reflexivity | constructor].
  - constructor; [|constructor; [|constructor]]; cbn.
    + intros m. apply qtype_var_bound. reflexivity.
    + intros m. apply qtype_var_bound. reflexivity.
Qed.

Create HintDb dbp.
Local Hint Resolve wf_ROObject wf_MutObject wf_RDMCell wf_MutCell wf_RDMK
  wf_MutK wf_RDMFactory wf_RDMOwner wf_MutOwner wf_MutBox wf_MutMF
  wf_ROMF wf_RDMDX_mix wf_tX_mix wf_RDMBoxEX_mix : dbp.

Ltac wfenv :=
  split; [cbn; lia |
          cbn; repeat (apply Forall_cons; [solve [auto with dbp]|]);
          apply Forall_nil].

Lemma collect_Object : CollectFields CT 0 [].
Proof. eapply CF_Object; reflexivity. Qed.

Lemma collect_Cell : CollectFields CT 1 [cache_field; value_field].
Proof.
  change (CollectFields CT 1
            (map (subst_field []) [] ++ Syntax.fields (body CellDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma collect_D : CollectFields CT 2 [f_field; prot_field].
Proof.
  change (CollectFields CT 2
            (map (subst_field []) [] ++ Syntax.fields (body DDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

(** The fields of K: those of D with X replaced by @Mut Cell. *)
Definition Kf_field : field_def :=
  {| assignability := RDA; ftype := MutCell |}.

Lemma collect_K : CollectFields CT 3 [Kf_field; prot_field].
Proof.
  change (CollectFields CT 3
            (map (subst_field [MutCell]) [f_field; prot_field]
               ++ Syntax.fields (body KDef))).
  eapply CF_Inherit; try reflexivity. apply collect_D.
Qed.

Lemma collect_Box : CollectFields CT 4 [e1_field].
Proof.
  change (CollectFields CT 4
            (map (subst_field []) [] ++ Syntax.fields (body BoxDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma collect_Factory : CollectFields CT 5 [].
Proof.
  change (CollectFields CT 5
            (map (subst_field []) [] ++ Syntax.fields (body FactoryDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma collect_MutFactory : CollectFields CT 6 [].
Proof.
  change (CollectFields CT 6
            (map (subst_field []) [] ++ Syntax.fields (body MutFactoryDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Factory.
Qed.

Lemma collect_Owner : CollectFields CT 7 [fac_field; secret_field].
Proof.
  change (CollectFields CT 7
            (map (subst_field []) [] ++ Syntax.fields (body OwnerDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

(** The field written at the end of attack: field 1 of Cell, [value], is
    receiver-dependent assignable. *)
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

Lemma e1_is_assignable : sf_assignability_rel CT 4 0 Assignable.
Proof.
  exists e1_field. split; [|reflexivity].
  eapply FL_Found; [apply collect_Box | reflexivity].
Qed.

Lemma no_method_in_Object : forall m D mdef,
  ~ FindMethodWithName CT 0 m D mdef.
Proof.
  intros m D mdef H. inversion H; subst.
  - cbn in Hfind. injection Hfind as <-. cbn in Hget_method. discriminate.
  - cbn in Hfind. injection Hfind as <-. cbn in Hsuper. discriminate.
Qed.

Lemma find_mix : FindMethodWithName CT 4 1 4 mix.
Proof. eapply FOM_Here; reflexivity. Qed.

Lemma find_factory_make : FindMethodWithName CT 5 0 5 factory_make.
Proof. eapply FOM_Here; reflexivity. Qed.

Lemma find_mf_make : FindMethodWithName CT 6 0 6 mf_make.
Proof. eapply FOM_Here; reflexivity. Qed.

Lemma find_attack : FindMethodWithName CT 7 2 7 attack.
Proof. eapply FOM_Here; reflexivity. Qed.

(** Looking up method 0 from Factory finds Factory's own declaration. *)
Lemma find_make_in_Factory : forall D mdef,
  FindMethodWithName CT 5 0 D mdef -> D = 5 /\ mdef = factory_make.
Proof.
  intros D mdef H. inversion H; subst.
  - cbn in Hfind. injection Hfind as <-. cbn in Hget_method.
    injection Hget_method as <-. split; reflexivity.
  - cbn in Hfind. injection Hfind as <-. cbn in Hnot_here. discriminate.
Qed.

Ltac ty_local :=
  eapply ST_Local;
    [wfenv | solve [auto with dbp] | reflexivity | reflexivity | reflexivity].

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

(** *** Box3.mix *)

Definition sΓMix : s_env :=
  [RDMBoxEX; RDMDX; tX; RDMCell; RDMCell; ROObject].

Lemma mix_body_typed :
  stmt_typing CT ΔMix [RDMBoxEX] ReadonlyState (mbody_stmt (mbody mix)) sΓMix.
Proof.
  cbn. unfold sΓMix.
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  ty_seq; [ty_local|]. ty_seq; [ty_local|].
  cbn.
  (* d = this.e1: E is used at its bound @RDM D<X> *)
  ty_seq.
  { eapply ST_VarAss with (Tx := RDMDX) (Te := tE);
      [wfenv | | discriminate | reflexivity | ].
    - eapply ET_Field with (x := 0) (T := RDMBoxEX) (qx := RDM) (C := 4)
        (Ts := [tE; tX]) (fDef := e1_field);
        [wfenv | reflexivity | reflexivity | fl collect_Box].
    - apply qtype_var_bound. reflexivity. }
  (* x = d.f: the field of D typed by D's parameter reads as X *)
  ty_seq.
  { eapply ST_VarAss with (Tx := tX) (Te := tX);
      [wfenv | | discriminate | reflexivity | ].
    - eapply ET_Field with (x := 1) (T := RDMDX) (qx := RDM) (C := 2)
        (Ts := [tX]) (fDef := f_field);
        [wfenv | reflexivity | reflexivity | fl collect_D].
    - apply qtype_var_refl. }
  (* yy = x: X is used at its bound @RDM Cell *)
  ty_seq.
  { eapply ST_VarAss with (Tx := RDMCell) (Te := tX);
      [wfenv | | discriminate | reflexivity | ].
    - apply ET_Var; [wfenv | reflexivity].
    - apply qtype_var_bound. reflexivity. }
  (* h = d.prot *)
  ty_seq.
  { eapply ST_VarAss with (Tx := RDMCell) (Te := RDMCell);
      [wfenv | | discriminate | reflexivity | refl_sub].
    eapply ET_Field with (x := 1) (T := RDMDX) (qx := RDM) (C := 2)
      (Ts := [tX]) (fDef := prot_field);
      [wfenv | reflexivity | reflexivity | fl collect_D]. }
  (* yy.cache = h *)
  eapply ST_FldWrite with (Tx := RDMCell) (Ty := RDMCell) (qx := RDM)
    (C := 1) (Ts := []) (fieldT := cache_field);
    [wfenv | reflexivity | reflexivity | reflexivity | fl collect_Cell
    | | reflexivity].
  split; [cbn; refl_sub | lf].
Qed.

Lemma wf_mix : wf_method CT 4 mix.
Proof.
  unfold wf_method.
  change (method_tv_env CT 4 (msignature mix)) with ΔMix.
  cbn.
  split; [apply receiver_plain_ok; left; exists RDM; reflexivity|].
  split; [constructor|].
  split; [apply wf_ROObject|].
  split.
  { exists sΓMix, ROObject. split; [|split].
    - apply mix_body_typed.
    - reflexivity.
    - refl_sub. }
  split; [no_override|].
  intros _. split; [|constructor].
  constructor; [discriminate|].
  constructor; [|constructor; [|constructor]].
  - eapply nm_var; [reflexivity|].
    constructor; [discriminate|]. constructor; [|constructor].
    eapply nm_var; [reflexivity|]. constructor; [discriminate | constructor].
  - eapply nm_var; [reflexivity|]. constructor; [discriminate | constructor].
Qed.

(** *** Factory.make *)


(** *** MutFactory.make *)

(** LENIENCY (e): the allocation of the fully mutable Box3, in the
    readonly-state body of MutFactory.make, passes its bound checks. *)
Lemma leniency_e_allocation_typed :
  stmt_typing CT ΔR [ROMF; MutK; MutBox] ReadonlyState
    (SNew 2 Mut_c 4 [MutK; MutCell] [1]) [ROMF; MutK; MutBox].
Proof.
  eapply ST_New with (Tx := MutBox) (argtypes := [MutK]) (fds := [e1_field]);
    [wfenv | reflexivity | reflexivity | reflexivity | discriminate
    | reflexivity | apply wf_MutBox | | | apply collect_Box | | ].
  - constructor; [lf | constructor; [lf | constructor]].
  - constructor; [|constructor; [|constructor]]; cbn.
    + split; [intuition discriminate | intros m; apply sub_MutK_MutDMutCell].
    + split; [intuition discriminate | intros m; refl_sub].
  - constructor; [|constructor]. cbn. split; [refl_sub | lf].
  - cbn. refl_sub.
Qed.

Lemma mf_make_body_typed :
  stmt_typing CT ΔR [ROMF] ReadonlyState (mbody_stmt (mbody mf_make))
    [ROMF; MutK; MutBox].
Proof.
  cbn.
  ty_seq; [ty_local|]. ty_seq; [ty_local|].
  cbn. apply leniency_e_allocation_typed.
Qed.

(** LENIENCY (b): the return type of the override is below the overridden
    return type as seen from the @Mut class, @RO Box3<@Mut K, @Lost Cell>:
    head Mut below RO, argument @Mut Cell forgotten to @Lost Cell. *)
Lemma leniency_b_override_return : forall Δ Vs,
  member_type AbstractState Mut Vs [] [] ROBoxT
    = TClass RO 4 [MutK; LostCell] /\
  qualified_type_subtype CT Δ MutBox
    (member_type AbstractState Mut Vs [] [] ROBoxT).
Proof.
  intros Δ Vs. split; [reflexivity|].
  cbn. apply qtype_qual; [cbn; lia | apply q_rd |].
  constructor; [apply targ_sub_refl|].
  constructor; [|constructor].
  apply tas_class; [|constructor].
  right. split; [reflexivity | left; reflexivity].
Qed.

Lemma mf_make_overrides : forall Vs,
  method_override_compatible CT ΔR Mut_c Vs
    (msignature mf_make) (msignature factory_make).
Proof.
  intros Vs. unfold method_override_compatible.
  split; [reflexivity|]. split; [reflexivity|]. split; [split; reflexivity|].
  split; [apply (leniency_b_override_return ΔR Vs)|].
  split; [constructor|].
  cbn. split; [apply qtype_qual; [cbn; lia | cbn; apply q_rd | apply Forall2_targ_sub_refl] | radmit_plain].
Qed.

Lemma wf_mf_make : wf_method CT 6 mf_make.
Proof.
  unfold wf_method.
  change (method_tv_env CT 6 (msignature mf_make)) with ΔR.
  split; [apply receiver_plain_ok; left; exists RO; reflexivity|].
  split; [constructor|].
  split; [apply wf_MutBox|].
  split.
  { exists [ROMF; MutK; MutBox], MutBox. split; [|split].
    - apply mf_make_body_typed.
    - reflexivity.
    - cbn. refl_sub. }
  split.
  { intros def parent Ss D mdef_parent Vs Hfind Hsuper Hfm _.
    cbn in Hfind. injection Hfind as <-. cbn in Hsuper.
    injection Hsuper as <- <-.
    apply find_make_in_Factory in Hfm. destruct Hfm as [-> ->].
    apply mf_make_overrides. }
  intros _. split; [|constructor].
  constructor; [discriminate | constructor].
Qed.

(** *** Owner.attack *)

Definition sΓAtk : s_env :=
  [RDMOwner; ROObject; RDMFactory; ROBoxT; MutCell; ROObject; MutCell;
   RDMCell; RDMK; ROObject; MutCell].




(** *** The classes *)

Definition ΔA (bs : list qualified_type) : tv_env :=
  mk_tv_env bs [] AbstractState 0.

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
  - constructor; [|constructor; [|constructor]]; unfold wf_field; cbn.
    + eapply wfs_var; [reflexivity|]. right. discriminate.
    + wfp.
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
    + split; [exact I | apply wf_RDMDX].
    + split; [exact I | wfp].
  - wfp.
  - constructor.
  - constructor.
  - left. reflexivity.
  - constructor; [|constructor]. unfold wf_field. cbn.
    eapply wfs_var; [reflexivity|]. right. discriminate.
  - constructor; [apply wf_mix | constructor].
  - constructor; [intros [] | constructor].
Qed.


Lemma wf_MutFactoryDef : wf_class CT MutFactoryDef.
Proof.
  wf_other 5 (@nil qualified_type) FactoryDef.
  - constructor.
  - wfp.
  - constructor.
  - constructor.
  - right. reflexivity.
  - constructor.
  - constructor; [apply wf_mf_make | constructor].
  - constructor; [intros [] | constructor].
Qed.

(* ------------------1. THE EXACT REASON------------------*)

(** The first field of K is the field f of D with X replaced by @Mut Cell. *)
Lemma K_first_field_type : ftype Kf_field = MutCell.
Proof. reflexivity. Qed.

(** In readonly-state code, that field type read through an @RDM allocation
    is @Lost Cell. *)
Lemma K_first_field_read_readonly_state :
  member_type ReadonlyState (qc2q RDM_c) [] [] [] (ftype Kf_field) = LostCell.
Proof. reflexivity. Qed.

(** The same in transitive-state code. *)
Lemma K_first_field_read_transitive_state :
  member_type TransitiveState (qc2q RDM_c) [] [] [] (ftype Kf_field) = LostCell.
Proof. reflexivity. Qed.

(** In abstract-state and concrete-state code it stays @Mut Cell. *)
Lemma K_first_field_read_abstract_state :
  member_type AbstractState (qc2q RDM_c) [] [] [] (ftype Kf_field) = MutCell /\
  member_type ConcreteState (qc2q RDM_c) [] [] [] (ftype Kf_field) = MutCell.
Proof. split; reflexivity. Qed.

Lemma LostCell_not_lost_free : ~ lost_free LostCell.
Proof. intros [Hl _]. apply Hl. reflexivity. Qed.

(** A @Mut Cell cannot be stored where a @Lost Cell is expected: the target
    has an unknown position. *)
Lemma MutCell_not_assignable_to_LostCell : forall CT0 Δ,
  ~ assignable_to CT0 Δ MutCell LostCell.
Proof.
  intros CT0 Δ [_ Hlf]. apply LostCell_not_lost_free. exact Hlf.
Qed.

(* ------------------2. THE ALLOCATION IS REJECTED------------------*)

(** v = new @RDM K(c0, s) has no typing in readonly-state or transitive-state
    code, in any bound environment and in any static environment in which c0
    is a @Mut Cell. *)
Theorem alloc_RDM_K_rejected : forall Δ sΓ sΓ' mt,
  readonly_state_method_scope mt ->
  static_getType sΓ 6 = Some MutCell ->
  ~ stmt_typing CT Δ sΓ mt (SNew 8 RDM_c 3 [] [6; 7]) sΓ'.
Proof.
  intros Δ sΓ sΓ' mt Hmt Hc0 H.
  inversion H; subst.
  pose proof (collect_fields_deterministic_rel _ _ _ _ Hfields collect_K)
    as Efds.
  subst fds.
  unfold static_getType_list in Hget_args. cbn [mapM] in Hget_args.
  rewrite Hc0 in Hget_args.
  match type of Hget_args with
  | context [static_getType ?G 7] =>
      destruct (static_getType G 7) as [T7|]; [|discriminate]
  end.
  injection Hget_args as <-.
  inversion Harg_sub as [|a b l l' Hhead _]; subst.
  apply (MutCell_not_assignable_to_LostCell CT Δ).
  destruct Hmt as [-> | ->]; exact Hhead.
Qed.

(** The same statement for the environment attack has at that point. *)
Corollary alloc_RDM_K_rejected_in_attack : forall sΓ',
  ~ stmt_typing CT ΔR sΓAtk ReadonlyState (SNew 8 RDM_c 3 [] [6; 7]) sΓ'.
Proof.
  intros sΓ'. apply alloc_RDM_K_rejected; [left; reflexivity | reflexivity].
Qed.

(* ------------------3. ATTACK AND THE CLASS TABLE ARE REJECTED------------------*)

(** The body of attack has no typing in readonly-state mode. *)
Theorem attack_body_untypable : forall Δ sΓ',
  ~ stmt_typing CT Δ [RDMOwner; ROObject] ReadonlyState
      (mbody_stmt (mbody attack)) sΓ'.
Proof.
  intros Δ sΓ' H. cbn [mbody_stmt mbody attack] in H.
  (* the nine declarations *)
  do 9 (match goal with
        | Hs : stmt_typing _ _ _ _ (SSeq (SLocal _ _) _) _ |- _ =>
            let Hloc := fresh "Hloc" in
            let Hnext := fresh "Hnext" in
            inversion Hs as [| | | | | | |? ? ? ? ? ? ? ? _ Hloc Hnext];
            subst; clear Hs; inversion Hloc; subst; clear Hloc
        end).
  match goal with
  | Hs : stmt_typing _ _ _ _ (SSeq _ _) _ |- _ => rename Hs into Hrest
  end.
  cbn [app] in *.
  (* f = this.fac *)
  inversion Hrest as [| | | | | | |? ? ? ? ? ? ? ? _ Hs1 Hrest1]; subst.
  inversion Hs1; subst. clear Hrest Hs1.
  (* rb = f.make() *)
  inversion Hrest1 as [| | | | | | |? ? ? ? ? ? ? ? _ Hs2 Hrest2]; subst.
  inversion Hs2; subst. clear Hrest1 Hs2.
  (* c0 = new @Mut Cell(nc, n) *)
  inversion Hrest2 as [| | | | | | |? ? ? ? ? ? ? ? _ Hs3 Hrest3]; subst.
  inversion Hs3; subst. clear Hrest2 Hs3.
  (* s = this.secret *)
  inversion Hrest3 as [| | | | | | |? ? ? ? ? ? ? ? _ Hs4 Hrest4]; subst.
  inversion Hs4; subst. clear Hrest3 Hs4.
  (* v = new @RDM K(c0, s) *)
  inversion Hrest4 as [| | | | | | |? ? ? ? ? ? ? ? _ Hs5 _]; subst.
  revert Hs5. apply alloc_RDM_K_rejected; [left; reflexivity | reflexivity].
Qed.

Theorem attack_not_wf : ~ wf_method CT 7 attack.
Proof.
  intros H. unfold wf_method in H.
  destruct H as (_ & _ & _ & (sΓ' & T & Hty & _) & _).
  revert Hty. apply attack_body_untypable.
Qed.

Theorem OwnerDef_not_wf : ~ wf_class CT OwnerDef.
Proof.
  intros H. inversion H.
  - discriminate.
  - match goal with
    | Hm : Forall (wf_method _ _) _ |- _ =>
        cbn in Hm; inversion Hm as [|? ? Hatk _]; subst
    end.
    apply attack_not_wf. exact Hatk.
Qed.

(** The program is rejected. *)
Theorem probe_ct_not_wf : ~ wf_class_table CT.
Proof.
  intros [Hall _]. rewrite Forall_forall in Hall.
  apply OwnerDef_not_wf. apply Hall.
  cbn. tauto.
Qed.

(* ------------------4. ESCAPE ROUTES------------------*)

(** A class type headed [q0] (not bottom) only has supertypes that are class
    types headed [q0] or @RO.  This holds for every class table, every bound
    environment and every mode. *)
Definition head_in (q0 : q) (T : qualified_type) : Prop :=
  exists q1 C Ts, T = TClass q1 C Ts /\ (q1 = q0 \/ q1 = RO).

Lemma head_in_closed : forall CT0 Δ q0 T U,
  q0 <> Bot ->
  qualified_type_subtype CT0 Δ T U ->
  head_in q0 T -> head_in q0 U.
Proof.
  intros CT0 Δ q0 T U Hnb H.
  induction H; intros (qa & C0 & Ts0 & E & Hq); try discriminate.
  - injection E as -> -> ->.
    exists q2, C0, Us. split; [reflexivity|].
    inversion Hqsub; subst; auto.
    destruct Hq as [Hq | Hq]; [exfalso; apply Hnb; symmetry; exact Hq
                              | discriminate].
  - injection E as -> -> ->.
    exists qa, D, Vs. split; [reflexivity | exact Hq].
  - inversion E; subst.
    destruct Hq as [Hq | Hq]; [exfalso; apply Hnb; symmetry; exact Hq
                              | discriminate].
  - apply IHqualified_type_subtype2. apply IHqualified_type_subtype1.
    exists qa, C0, Ts0. split; [exact E | exact Hq].
Qed.

(** (i) Allocating the K as @Mut instead gives a @Mut K, and a @Mut K is not
    an @RDM K, so it can be stored neither in v nor in rb.e1, whose type
    reads @RDM K (see leniency_c_field_write_typed). *)
Theorem MutK_not_RDMK : forall CT0 Δ,
  ~ qualified_type_subtype CT0 Δ (TClass Mut 3 []) (TClass RDM 3 []).
Proof.
  intros CT0 Δ H.
  assert (Hh : head_in Mut (TClass RDM 3 [])).
  { eapply head_in_closed; [discriminate | exact H |].
    exists Mut, 3, (@nil qualified_type).
    split; [reflexivity | left; reflexivity]. }
  destruct Hh as (q1 & C0 & Ts0 & E & [-> | ->]); discriminate.
Qed.

(** The type @RO Box3<@RDM K, @Lost Cell>, through which the program hoped
    to see the box, is not a well-formed type use: seen through the @RO head
    the first bound is @Lost D<@Lost Cell>, and @RDM K is not below it.  The
    bound check is made whatever the adapted bound contains. *)
Theorem ROBoxT_not_wf : forall Δ top, ~ wf_stype CT Δ top ROBoxT.
Proof.
  intros Δ top H. inversion H; subst.
  cbn in Hfind. injection Hfind as <-. cbn in Hbounds.
  inversion Hbounds as [|? ? ? ? Hb _]; subst.
  apply bound_sub_self in Hb.
  assert (Hh : head_in RDM (TClass Lost 2 [LostCell])).
  { eapply head_in_closed; [discriminate | exact Hb |].
    exists RDM, 3, (@nil qualified_type).
    split; [reflexivity | left; reflexivity]. }
  destruct Hh as (q1 & C0 & Ts0 & E & [-> | ->]); discriminate.
Qed.

(** So v = new @Mut K(...) has no typing while v is declared @RDM K, in any
    mode and with any initialisers. *)
Theorem alloc_Mut_K_into_RDM_var_rejected : forall Δ sΓ sΓ' mt args,
  static_getType sΓ 8 = Some RDMK ->
  ~ stmt_typing CT Δ sΓ mt (SNew 8 Mut_c 3 [] args) sΓ'.
Proof.
  intros Δ sΓ sΓ' mt args Hv H.
  inversion H; subst.
  rewrite Hv in Hget_x. injection Hget_x as <-.
  revert Hresult_sub. apply MutK_not_RDMK.
Qed.

(** And rb.e1 = w has no typing when w is a @Mut K. *)
Theorem write_Mut_K_into_e1_rejected : forall Δ sΓ sΓ' mt w,
  static_getType sΓ 3 = Some ROBoxT ->
  static_getType sΓ w = Some MutK ->
  ~ stmt_typing CT Δ sΓ mt (SFldWrite 3 0 w) sΓ'.
Proof.
  intros Δ sΓ sΓ' mt w Hrb Hw H.
  inversion H; subst.
  rewrite Hrb in Hget_x. injection Hget_x as <-.
  rewrite Hw in Hget_y. injection Hget_y as <-.
  cbn in Hub. injection Hub as <- <- <-.
  assert (E : fieldT = e1_field).
  { eapply field_lookup_deterministic_rel; [exact Hfld_def|].
    eapply FL_Found; [apply collect_Box | reflexivity]. }
  subst fieldT.
  destruct Hsub as [Hsub _].
  revert Hsub. destruct mt; cbn; apply MutK_not_RDMK.
Qed.

(** A second obstacle on the same route: the second field of K is declared
    @RDM Cell; read through a @Mut allocation it is a @Mut Cell, and s is an
    @RDM Cell, which is not a @Mut Cell.  So new @Mut K(c0, s) is not typable
    as an allocation either, whatever it is assigned to. *)
Lemma K_second_field_read_through_Mut : forall mt,
  member_type mt (qc2q Mut_c) [] [] [] (ftype prot_field) = MutCell.
Proof. intros mt. destruct mt; reflexivity. Qed.

Theorem RDMCell_not_MutCell : forall CT0 Δ,
  ~ qualified_type_subtype CT0 Δ (TClass RDM 1 []) (TClass Mut 1 []).
Proof.
  intros CT0 Δ H.
  assert (Hh : head_in RDM (TClass Mut 1 [])).
  { eapply head_in_closed; [discriminate | exact H |].
    exists RDM, 1, (@nil qualified_type).
    split; [reflexivity | left; reflexivity]. }
  destruct Hh as (q1 & C0 & Ts0 & E & [-> | ->]); discriminate.
Qed.

Theorem alloc_Mut_K_with_RDM_secret_rejected : forall Δ sΓ sΓ' mt x a,
  static_getType sΓ 7 = Some RDMCell ->
  ~ stmt_typing CT Δ sΓ mt (SNew x Mut_c 3 [] [a; 7]) sΓ'.
Proof.
  intros Δ sΓ sΓ' mt x a Hs H.
  inversion H; subst.
  pose proof (collect_fields_deterministic_rel _ _ _ _ Hfields collect_K)
    as Efds.
  subst fds.
  unfold static_getType_list in Hget_args. cbn [mapM] in Hget_args.
  rewrite Hs in Hget_args.
  match type of Hget_args with
  | context [static_getType ?G a] =>
      destruct (static_getType G a) as [Ta|]; [|discriminate]
  end.
  injection Hget_args as <-.
  inversion Harg_sub as [|? ? ? ? _ Htl]; subst.
  inversion Htl as [|? ? ? ? Hsnd _]; subst.
  destruct Hsnd as [Hsub _].
  rewrite K_second_field_read_through_Mut in Hsub.
  revert Hsub. apply RDMCell_not_MutCell.
Qed.

(** A @Mut K can be allocated in readonly-state code when both initialisers
    are @Mut Cells and the result goes into a @Mut K variable. *)
Theorem alloc_Mut_K_typed_readonly_state :
  stmt_typing CT ΔR [RDMOwner; MutCell; MutCell; MutK] ReadonlyState
    (SNew 3 Mut_c 3 [] [1; 2]) [RDMOwner; MutCell; MutCell; MutK].
Proof.
  eapply ST_New with (qc := Mut_c) (Tx := MutK)
    (argtypes := [MutCell; MutCell]);
    [wfenv | reflexivity | reflexivity | reflexivity | discriminate
    | reflexivity | apply wf_MutK | constructor | constructor
    | apply collect_K | | ].
  - constructor; [|constructor; [|constructor]]; cbn;
      (split; [refl_sub | lf]).
  - cbn. refl_sub.
Qed.


Print Assumptions leniency_e_allocation_typed.
Print Assumptions ROBoxT_not_wf.
