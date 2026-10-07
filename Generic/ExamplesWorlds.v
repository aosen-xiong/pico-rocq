From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds.

(** A concrete program for the readonly-state preservation theorem that
    allows receiver-dependent field types (no type parameters).

    class 0: @RDM class Object {}
    class 1: @RDM class D extends Object {
       @Assignable @RDM Object slot;       // field 0
    }
    class 2: @RDM class J extends Object {
       @RDA @RDM D d;                      // field 0
       @RS @RDM D make(@RDM J this)        // method 0
         { @RDM D r; r = this.d; return r; }
       @RS @RO Object run(@RDM J this) {   // method 1
           @RDM D g;        // var 1
           @RDM D old;      // var 2
           g = this.make();
           old = this.d;
           g.slot = old;
           return old;
       }
    }
    class 3: @Mut class K extends J {
       @RS @Mut D make(@RO K this)         // overrides method 0
         { @Mut D r; @Mut Object n; r = new @Mut D(n); return r; }
    }

    main (variable 0 is the receiver, a @Mut Object):
      @Mut D d0;       // var 1
      @Mut K k;        // var 2
      @RO J j;         // var 3
      @RO Object x;    // var 4
      @Mut Object n;   // var 5, never assigned, so it holds null
      d0 = new @Mut D(n);
      k  = new @Mut K(d0);
      j  = k;
      x  = j.run();    // call A

    Two changes from the program as first sketched, both forced by the
    typing rules:
    - K.make's receiver is @RO K, not @RDM K.  A class declared @Mut pins the
      head of every use of it to @Mut, so the only well-formed uses are @Mut K
      and @RO K; and a readonly-state signature may not have a @Mut receiver.
    - The never-assigned initializer n is @Mut Object, not @RO Object.  The
      slot of a D allocated as @Mut is seen as @Mut Object, and a readonly
      reference is not accepted there.
*)

(* ------------------THE PROGRAM------------------*)

Definition ROObject : qualified_type := TClass RO 0 [].
Definition MutObject : qualified_type := TClass Mut 0 [].
Definition RDMObject : qualified_type := TClass RDM 0 [].
Definition MutD : qualified_type := TClass Mut 1 [].
Definition RDMD : qualified_type := TClass RDM 1 [].
Definition ROJ : qualified_type := TClass RO 2 [].
Definition RDMJ : qualified_type := TClass RDM 2 [].
Definition ROK : qualified_type := TClass RO 3 [].
Definition MutK : qualified_type := TClass Mut 3 [].

Definition ObjectDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 0; ctparams := [];
                     super := None |};
     body := {| fields := []; methods := [] |} |}.

Definition slot_field : field_def :=
  {| assignability := Assignable; ftype := RDMObject |}.

Definition DDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 1; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := [slot_field]; methods := [] |} |}.

Definition d_field : field_def :=
  {| assignability := RDA; ftype := RDMD |}.

Definition j_make : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mret := RDMD;
          mname := 0;
          mreceiver := RDMJ;
          mparams := [] |};
     mbody :=
       {| mbody_stmt := SSeq (SLocal RDMD 1) (SVarAss 1 (EField 0 0));
          mreturn := 1 |} |}.

Definition j_run : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mret := ROObject;
          mname := 1;
          mreceiver := RDMJ;
          mparams := [] |};
     mbody :=
       {| mbody_stmt :=
            SSeq (SLocal RDMD 1)
            (SSeq (SLocal RDMD 2)
            (SSeq (SCall 1 0 0 [] [])
            (SSeq (SVarAss 2 (EField 0 0))
                  (SFldWrite 1 0 2))));
          mreturn := 2 |} |}.

Definition JDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 2; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := [d_field]; methods := [j_make; j_run] |} |}.

Definition k_make : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mret := MutD;
          mname := 0;
          mreceiver := ROK;
          mparams := [] |};
     mbody :=
       {| mbody_stmt :=
            SSeq (SLocal MutD 1)
            (SSeq (SLocal MutObject 2)
                  (SNew 1 Mut_c 1 [] [2]));
          mreturn := 1 |} |}.

Definition KDef : class_def :=
  {| signature := {| class_qualifier := Mut_c; cname := 3; ctparams := [];
                     super := Some (2, []) |};
     body := {| fields := []; methods := [k_make] |} |}.

Definition CT : class_table := [ObjectDef; DDef; JDef; KDef].

Definition prefix : stmt :=
  SSeq (SLocal MutD 1)
  (SSeq (SLocal MutK 2)
  (SSeq (SLocal ROJ 3)
  (SSeq (SLocal ROObject 4)
  (SSeq (SLocal MutObject 5)
  (SSeq (SNew 1 Mut_c 1 [] [5])
  (SSeq (SNew 2 Mut_c 3 [] [1])
        (SVarAss 3 (EVar 2)))))))).

Definition callA : stmt := SCall 4 1 3 [] [].

Definition main : stmt := SSeq prefix callA.

Definition Δ0 : tv_env := mk_tv_env [] [] AbstractState.
Definition sΓ0 : s_env := [MutObject].
Definition sΓA : s_env := [MutObject; MutD; MutK; ROJ; ROObject; MutObject].

(* ------------------SMALL TACTICS AND FACTS------------------*)

Ltac qs := first [apply q_refl; discriminate | apply q_rd | apply q_bot].

(** Classes 0, 1, 2 are declared @RDM: any written qualifier is fine. *)
Lemma wf_plain : forall Δ top q0 C,
  C < 3 -> q0 <> Lost -> wf_stype CT Δ top (TClass q0 C []).
Proof.
  intros Δ top q0 C HC Hq.
  destruct C as [|[|[|C]]]; try lia;
    (eapply wfs_class;
       [reflexivity | right | reflexivity | constructor | constructor]);
    destruct q0; cbn; try qs; congruence.
Qed.

(** Class 3 is declared @Mut: only @Mut and @RO uses are well formed. *)
Lemma wf_K : forall Δ top q0,
  q0 = Mut \/ q0 = RO -> wf_stype CT Δ top (TClass q0 3 []).
Proof.
  intros Δ top q0 Hq.
  eapply wfs_class;
    [reflexivity | right | reflexivity | constructor | constructor].
  destruct Hq as [-> | ->]; cbn; qs.
Qed.

(** The rejected receiver: @RDM K is not a well-formed type. *)
Lemma rdm_K_not_wf : forall Δ top, ~ wf_stype CT Δ top (TClass RDM 3 []).
Proof.
  intros Δ top H. inversion H; subst.
  cbn in Hfind. injection Hfind as <-. cbn in Hhead.
  destruct Hhead as [[_ Hl] | Hs]; [discriminate|].
  inversion Hs.
Qed.

Lemma wf_use : forall Δ q0 C,
  C < 3 -> q0 <> Lost -> wf_stypeuse CT Δ (TClass q0 C []).
Proof. intros. apply wf_plain; auto. Qed.

Lemma wf_K_use : forall Δ q0,
  q0 = Mut \/ q0 = RO -> wf_stypeuse CT Δ (TClass q0 3 []).
Proof. intros. apply wf_K; auto. Qed.

Ltac wfp :=
  solve [ apply wf_use; [cbn; lia | discriminate]
        | apply wf_K_use; left; reflexivity
        | apply wf_K_use; right; reflexivity ].

Ltac wfenv :=
  split; [cbn; lia |
          cbn; repeat (apply Forall_cons; [solve [wfp]|]); apply Forall_nil].

Ltac refl_sub :=
  apply qualified_type_subtype_refl_class; [cbn; lia | discriminate].

Ltac qual_sub := apply qtype_qual; [cbn; lia | qs | constructor].

(** One step up the hierarchy, to a direct superclass, same qualifier. *)
Ltac hier_sub :=
  apply qtype_hier; eapply si_step; [reflexivity | cbn; apply si_refl].

Lemma collect_Object : CollectFields CT 0 [].
Proof. eapply CF_Object; reflexivity. Qed.

Lemma collect_D : CollectFields CT 1 [slot_field].
Proof.
  change (CollectFields CT 1
            (map (subst_field []) [] ++ Syntax.fields (body DDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma collect_J : CollectFields CT 2 [d_field].
Proof.
  change (CollectFields CT 2
            (map (subst_field []) [] ++ Syntax.fields (body JDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

(** K inherits the field d from J. *)
Lemma collect_K : CollectFields CT 3 [d_field].
Proof.
  change (CollectFields CT 3
            (map (subst_field []) [d_field] ++ Syntax.fields (body KDef))).
  eapply CF_Inherit; try reflexivity. apply collect_J.
Qed.

Lemma slot_is_assignable : sf_assignability_rel CT 1 0 Assignable.
Proof.
  exists slot_field. split; [|reflexivity].
  eapply FL_Found; [apply collect_D | reflexivity].
Qed.

Lemma d_is_rda_in_K : sf_assignability_rel CT 3 0 RDA.
Proof.
  exists d_field. split; [|reflexivity].
  eapply FL_Found; [apply collect_K | reflexivity].
Qed.

Lemma no_method_in_Object : forall m D mdef,
  ~ FindMethodWithName CT 0 m D mdef.
Proof.
  intros m D mdef H. inversion H; subst.
  - cbn in Hfind. injection Hfind as <-. cbn in Hget_method. discriminate.
  - cbn in Hfind. injection Hfind as <-. cbn in Hsuper. discriminate.
Qed.

Lemma find_j_make : FindMethodWithName CT 2 0 2 j_make.
Proof. eapply FOM_Here; reflexivity. Qed.

Lemma find_j_run : FindMethodWithName CT 2 1 2 j_run.
Proof. eapply FOM_Here; reflexivity. Qed.

Lemma find_k_make : FindMethodWithName CT 3 0 3 k_make.
Proof. eapply FOM_Here; reflexivity. Qed.

(** K does not declare run; lookup from K finds J's. *)
Lemma find_run_from_K : FindMethodWithName CT 3 1 2 j_run.
Proof.
  eapply FOM_Super; [reflexivity | reflexivity | reflexivity | reflexivity |].
  apply find_j_run.
Qed.

(* ------------------DELIVERABLE 1: THE CLASS TABLE------------------*)

Lemma wf_j_make : wf_method CT 2 j_make.
Proof.
  unfold wf_method. cbn.
  split; [left; exists RDM; reflexivity|].
  split; [constructor|].
  split; [wfp|].
  split.
  { exists [RDMJ; RDMD], RDMD. split; [|split].
    - eapply ST_Seq; [wfenv | |].
      + eapply ST_Local; [wfenv | wfp | | reflexivity |]; reflexivity.
      + (* r = this.d: a receiver-dependent field read through a
           receiver-dependent receiver stays receiver-dependent *)
        eapply ST_VarAss with (Tx := RDMD);
          [wfenv | | discriminate | reflexivity | ].
        * eapply ET_Field with (x := 0) (T := RDMJ) (qx := RDM) (C := 2)
            (Ts := []) (fDef := d_field);
            [wfenv | reflexivity | reflexivity |].
          eapply FL_Found; [apply collect_J | reflexivity].
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
  - constructor.
Qed.

Lemma wf_j_run : wf_method CT 2 j_run.
Proof.
  unfold wf_method. cbn.
  split; [left; exists RDM; reflexivity|].
  split; [constructor|].
  split; [wfp|].
  split.
  { exists [RDMJ; RDMD; RDMD], RDMD. split; [|split].
    - eapply ST_Seq; [wfenv | |].
      { eapply ST_Local; [wfenv | wfp | | reflexivity |]; reflexivity. }
      eapply ST_Seq; [wfenv | |].
      { eapply ST_Local; [wfenv | wfp | | reflexivity |]; reflexivity. }
      cbn.
      eapply ST_Seq; [wfenv | |].
      { (* g = this.make(), through the receiver-dependent receiver *)
        eapply ST_Call with (Tx := RDMD) (Ty := RDMJ) (argtypes := [])
          (qy := RDM) (C := 2) (Ts := []) (D := 2) (Vs := [])
          (mdef := j_make);
          [wfenv | reflexivity | reflexivity | reflexivity | reflexivity
          | apply find_j_make | apply si_refl | discriminate | constructor
          | constructor | reflexivity
          | constructor | | | constructor | apply method_subtyping_refl].
        - cbn. refl_sub.
        - left. cbn. split; [refl_sub|]. left. cbn. intuition discriminate. }
      eapply ST_Seq; [wfenv | |].
      { (* old = this.d *)
        eapply ST_VarAss with (Tx := RDMD);
          [wfenv | | discriminate | reflexivity | ].
        * eapply ET_Field with (x := 0) (T := RDMJ) (qx := RDM) (C := 2)
            (Ts := []) (fDef := d_field);
            [wfenv | reflexivity | reflexivity |].
          eapply FL_Found; [apply collect_J | reflexivity].
        * cbn. refl_sub. }
      (* g.slot = old: the slot is assignable, both sides receiver-dependent *)
      eapply ST_FldWrite with (Tx := RDMD) (Ty := RDMD) (qx := RDM)
        (C := 1) (Ts := []) (fieldT := slot_field);
        [wfenv | reflexivity | reflexivity | reflexivity | | | reflexivity].
      + eapply FL_Found; [apply collect_D | reflexivity].
      + split; [cbn; hier_sub | left; cbn; intuition discriminate].
    - reflexivity.
    - (* @RDM D <: @RO Object *)
      eapply qtype_trans; [hier_sub | qual_sub]. }
  split.
  { intros def parent Ss D mdef_parent Vs Hfind Hsuper Hfm _.
    cbn in Hfind. injection Hfind as <-. cbn in Hsuper.
    injection Hsuper as <- <-.
    exfalso. eapply no_method_in_Object; eauto. }
  intros _. split.
  - constructor; [discriminate | constructor].
  - constructor.
Qed.

(** K.make, including the override check against J.make: the overridden
    return type @RDM D, seen through the class's declared @Mut, is @Mut D. *)
Lemma wf_k_make : wf_method CT 3 k_make.
Proof.
  unfold wf_method. cbn.
  split; [left; exists RO; reflexivity|].
  split; [constructor|].
  split; [wfp|].
  split.
  { exists [ROK; MutD; MutObject], MutD. split; [|split].
    - eapply ST_Seq; [wfenv | |].
      { eapply ST_Local; [wfenv | wfp | | reflexivity |]; reflexivity. }
      eapply ST_Seq; [wfenv | |].
      { eapply ST_Local; [wfenv | wfp | | reflexivity |]; reflexivity. }
      cbn.
      eapply ST_New with (Tx := MutD) (argtypes := [MutObject]);
        [wfenv | reflexivity | reflexivity | reflexivity | discriminate
        | reflexivity | wfp | constructor | constructor
        | apply collect_D | | ].
      + constructor; [|constructor]. cbn. split; [refl_sub|].
        left. cbn. intuition discriminate.
      + cbn. refl_sub.
    - reflexivity.
    - refl_sub. }
  split.
  { intros def parent Ss D mdef_parent Vs Hfind Hsuper Hfm _.
    cbn in Hfind. injection Hfind as <-. cbn in Hsuper.
    injection Hsuper as <- <-.
    destruct (find_method_with_name_deterministic _ _ _ _ _ _ _ Hfm find_j_make)
      as [-> ->].
    unfold method_override_compatible. cbn.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [refl_sub|].
    split; [constructor|].
    cbn. apply qtype_qual; [cbn; lia | cbn; qs | apply Forall2_targ_sub_refl]. }
  intros _. split.
  - constructor; [discriminate | constructor].
  - constructor.
Qed.

Lemma worlds_ct_wf : wf_class_table CT.
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
      * wfp.
      * constructor; [unfold wf_field; cbn; wfp | constructor].
      * constructor; [apply wf_j_make|].
        constructor; [apply wf_j_run | constructor].
      * constructor; [cbn; intros [H | []]; discriminate|].
        constructor; [intros [] | constructor].
    + eapply WFOtherDef with (superC := 2) (Ss := []);
        try reflexivity; cbn; try solve [constructor]; auto.
      * (* the superclass J seen from a class declared @Mut *)
        wfp.
      * constructor; [apply wf_k_make | constructor].
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

Lemma worlds_no_tparams : no_tparams CT.
Proof.
  intros C def Hfind.
  destruct C as [|[|[|[|C]]]]; cbn in Hfind.
  - injection Hfind as <-. split; [reflexivity | constructor].
  - injection Hfind as <-. split; [reflexivity | constructor].
  - injection Hfind as <-. split; [reflexivity|].
    constructor; [reflexivity|]. constructor; [reflexivity | constructor].
  - injection Hfind as <-. split; [reflexivity|].
    constructor; [reflexivity | constructor].
  - destruct C; discriminate.
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
  (* d0 = new @Mut D(n) *)
  ty_seq.
  { eapply ST_New with (Tx := MutD) (argtypes := [MutObject]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | wfp | constructor | constructor
      | apply collect_D | | ].
    - constructor; [|constructor]. cbn. split; [refl_sub|].
      left. cbn. intuition discriminate.
    - cbn. refl_sub. }
  (* k = new @Mut K(d0): the inherited field d, declared @RDM D, is seen
     through the allocation's @Mut as @Mut D *)
  ty_seq.
  { eapply ST_New with (Tx := MutK) (argtypes := [MutD]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | wfp | constructor | constructor
      | apply collect_K | | ].
    - constructor; [|constructor]. cbn. split; [refl_sub|].
      left. cbn. intuition discriminate.
    - cbn. refl_sub. }
  (* j = k: @Mut K <: @RO J *)
  eapply ST_VarAss with (Tx := ROJ) (Te := MutK);
    [wfenv | | discriminate | reflexivity | ].
  - apply ET_Var; [wfenv | reflexivity].
  - apply qtype_trans with (T2 := ROK); [qual_sub | hier_sub].
Qed.

(** Call A is typed through the readonly receiver j.  The ordinary receiver
    check would fail (a receiver-dependent receiver type seen through a
    readonly reference is unknown); the call is accepted by the rule for
    readonly receivers calling a method whose declared receiver is
    receiver-dependent. *)
Lemma callA_typed : stmt_typing CT Δ0 sΓA AbstractState callA sΓA.
Proof.
  unfold callA, sΓA, Δ0.
  eapply ST_Call with (Tx := ROObject) (Ty := ROJ)
    (argtypes := [])
    (qy := RO) (C := 2) (Ts := []) (D := 2) (Vs := [])
    (mdef := j_run);
    [wfenv | reflexivity | reflexivity | reflexivity | reflexivity
    | apply find_j_run | apply si_refl | discriminate | constructor
    | constructor | reflexivity
    | constructor | | | constructor | apply method_rs_as].
  - cbn. refl_sub.
  - right. split; [reflexivity|]. exists (@nil qualified_type). reflexivity.
Qed.

Lemma main_typed : stmt_typing CT Δ0 sΓ0 AbstractState main sΓA.
Proof.
  unfold main.
  eapply ST_Seq; [unfold sΓ0; wfenv | apply prefix_typed | apply callA_typed].
Qed.

(** The states.  Location 0 is main's receiver, 1 is d0, 2 is the K object. *)
Definition rΓ0 : r_env := mkr_env [Iot 0] [] [].
Definition h0 : heap := [mkObj (mkruntime_type Mut_r 0 []) []].

Definition rΓA : r_env :=
  mkr_env [Iot 0; Iot 1; Iot 2; Iot 2; Null_a; Null_a] [] [].

Definition hA : heap :=
  [ mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 1 []) [Null_a];
    mkObj (mkruntime_type Mut_r 3 []) [Iot 1] ].

Ltac ev_local := eapply SBS_Seq; [apply SBS_Local; reflexivity|]; cbn.

Lemma prefix_eval : eval_stmt CT rΓ0 h0 prefix OK rΓA hA.
Proof.
  unfold prefix, rΓ0, h0.
  ev_local. ev_local. ev_local. ev_local. ev_local.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  refine (SBS_Assign _
            (mkr_env [Iot 0; Iot 1; Iot 2; Null_a; Null_a; Null_a] [] [])
            _ 3 _ Null_a (Iot 2) eq_refl _).
  apply EBS_Val. reflexivity.
Qed.

Lemma initial_config : wf_r_config CT Δ0 sΓ0 rΓ0 h0.
Proof.
  unfold Δ0, sΓ0, rΓ0, h0.
  refine (conj worlds_ct_wf
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

(* ------------------DELIVERABLE 3: CALL A------------------*)

(** After call A: x holds d0, and a fresh D (location 3), allocated by
    K.make, holds d0 in its slot. *)
Definition rΓA' : r_env :=
  mkr_env [Iot 0; Iot 1; Iot 2; Iot 2; Iot 1; Null_a] [] [].

Definition hA' : heap :=
  [ mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 1 []) [Null_a];
    mkObj (mkruntime_type Mut_r 3 []) [Iot 1];
    mkObj (mkruntime_type Mut_r 1 []) [Iot 1] ].

(** The inner call this.make(), run in run's activation on the K object:
    lookup starts at the object's class K and selects K.make, which
    allocates the fresh D at location 3. *)
Lemma inner_make_eval :
  eval_stmt CT (mkr_env [Iot 2; Null_a; Null_a] [] []) hA
    (SCall 1 0 0 [] []) OK
    (mkr_env [Iot 2; Iot 3; Null_a] [] [])
    (hA ++ [mkObj (mkruntime_type Mut_r 1 []) [Null_a]]).
Proof.
  unfold hA.
  eapply SBS_Call with (mdef := k_make) (D := 3) (cy := 3)
    (rΓ' := mkr_env [Iot 2] [] [])
    (rΓ'' := mkr_env [Iot 2; Iot 3; Null_a] [] []).
  - reflexivity.
  - reflexivity.
  - apply find_k_make.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold callee_env. do 4 eexists.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [apply rsi_refl | reflexivity].
  - cbn. eapply SBS_Seq; [apply SBS_Local; reflexivity|]. cbn.
    eapply SBS_Seq; [apply SBS_Local; reflexivity|]. cbn.
    eapply SBS_New; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma callA_eval : eval_stmt CT rΓA hA callA OK rΓA' hA'.
Proof.
  unfold callA, rΓA.
  eapply SBS_Call with (mdef := j_run) (D := 2) (cy := 3)
    (rΓ' := mkr_env [Iot 2] [] [])
    (rΓ'' := mkr_env [Iot 2; Iot 3; Iot 1] [] []).
  - reflexivity.
  - reflexivity.
  - apply find_run_from_K.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold callee_env. do 4 eexists.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [|reflexivity].
    cbn. eapply rsi_step; [reflexivity | cbn; apply rsi_refl].
  - cbn. eapply SBS_Seq; [apply SBS_Local; reflexivity|]. cbn.
    eapply SBS_Seq; [apply SBS_Local; reflexivity|]. cbn.
    eapply SBS_Seq; [apply inner_make_eval|].
    eapply SBS_Seq.
    + eapply SBS_Assign; [reflexivity|]. eapply EBS_Field; reflexivity.
    + cbn. eapply SBS_FldWrite with (a := Assignable);
        [reflexivity | reflexivity | reflexivity | apply slot_is_assignable
        | reflexivity | reflexivity | reflexivity].
  - reflexivity.
  - reflexivity.
Qed.

(** The whole program runs from the initial state to the final one. *)
Lemma main_eval : eval_stmt CT rΓ0 h0 main OK rΓA' hA'.
Proof.
  unfold main. eapply SBS_Seq; [apply prefix_eval | apply callA_eval].
Qed.

(** The readonly-state theorem for receiver-dependent field types, applied to
    call A, for any outcome of the call: the K object (location 2) keeps the
    value of its field d (field 0, receiver-dependent assignable, of
    receiver-dependent type). *)
Theorem callA_preserves_d : forall rΓ' h',
  eval_stmt CT rΓA hA callA OK rΓ' h' ->
  exists vals',
    runtime_getObj h' 2 = Some (mkObj (mkruntime_type Mut_r 3 []) vals') /\
    nth_error [Iot 1] 0 = nth_error vals' 0.
Proof.
  intros rΓ' h' Heval.
  eapply (readonly_state_preservation_rdm CT Δ0 sΓA AbstractState rΓA hA
            4 1 3 [] [] sΓA rΓ' h' 2 3 2 j_run
            worlds_no_tparams config_A callA_typed Heval).
  - reflexivity.
  - reflexivity.
  - apply find_run_from_K.
  - left. reflexivity.
  - reflexivity.
  - right. apply d_is_rda_in_K.
Qed.

(** On the explicit final heap: the K object's d still holds d0. *)
Corollary callA_d_unchanged :
  exists vals',
    runtime_getObj hA' 2 = Some (mkObj (mkruntime_type Mut_r 3 []) vals') /\
    nth_error vals' 0 = Some (Iot 1).
Proof.
  destruct (callA_preserves_d _ _ callA_eval) as (vals' & Hobj & Hnth).
  exists vals'. split; [exact Hobj|]. symmetry. exact Hnth.
Qed.

(** By computation on the explicit final heap:
    - K.make ran: location 3 did not exist before and is a D afterwards;
    - the fresh D's slot holds d0 (location 1);
    - d0's own assignable slot is unchanged (still null);
    - the heap did change. *)
Lemma callA_fresh_object :
  runtime_getObj hA 3 = None /\
  (exists o', runtime_getObj hA' 3 = Some o' /\
              rctype (rt_type o') = 1 /\
              nth_error (fields_map o') 0 = Some (Iot 1)) /\
  (exists o, runtime_getObj hA 1 = Some o /\
             nth_error (fields_map o) 0 = Some Null_a) /\
  (exists o', runtime_getObj hA' 1 = Some o' /\
              nth_error (fields_map o') 0 = Some Null_a) /\
  hA <> hA'.
Proof.
  split; [reflexivity|].
  split; [eexists; split; [reflexivity | split; reflexivity]|].
  split; [eexists; split; reflexivity|].
  split; [eexists; split; reflexivity|].
  discriminate.
Qed.

(** The slot written by the call is outside the readonly-state guarantee: it
    is neither final nor receiver-dependent assignable. *)
Lemma slot_not_protected :
  ~ (sf_assignability_rel CT 1 0 Final \/ sf_assignability_rel CT 1 0 RDA).
Proof.
  intros [H | H];
    pose proof (sf_assignability_deterministic_rel _ _ _ _ _ H
                  slot_is_assignable) as Heq;
    discriminate.
Qed.

Print Assumptions callA_preserves_d.
