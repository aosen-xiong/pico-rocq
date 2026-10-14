From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation.

(** A second concrete program.  It exercises method overriding with dynamic
    dispatch, and a field read through a qualified use of a method type
    variable whose bound has no type arguments. *)

(* ------------------THE PROGRAM------------------*)

Definition ROObject : qualified_type := TClass RO 0 [].
Definition MutObject : qualified_type := TClass Mut 0 [].
Definition ROCell : qualified_type := TClass RO 1 [].
Definition MutCell : qualified_type := TClass Mut 1 [].
Definition ROBase : qualified_type := TClass RO 2 [].
Definition RODerived : qualified_type := TClass RO 3 [].

(* @RO X, for the method type parameter X of look *)
Definition roX : qualified_type := TVar (TVQual RO) MethodVar 0.

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

(* @RO Object id(@RO Base this, @RO Object a) { return a; } *)
Definition base_id : method_def :=
  {| msignature :=
       {| mscope := AbstractState;
          mtparams := [];
          mqparams := 0;
          mret := ROObject;
          mname := 0;
          mreceiver := ROBase;
          mparams := [ROObject] |};
     mbody := {| mbody_stmt := SSkip; mreturn := 1 |} |}.

(* <X extends @RO Cell> @RO Object look(@RO Base this, @RO X c)
     { @RO Object r; r = c.value; return r; } *)
Definition base_look : method_def :=
  {| msignature :=
       {| mscope := AbstractState;
          mtparams := [ROCell];
          mqparams := 0;
          mret := ROObject;
          mname := 1;
          mreceiver := ROBase;
          mparams := [roX] |};
     mbody :=
       {| mbody_stmt := SSeq (SLocal ROObject 2) (SVarAss 2 (EField 1 0));
          mreturn := 2 |} |}.

Definition BaseDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 2; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := []; methods := [base_id; base_look] |} |}.

(* @RO Object id(@RO Derived this, @RO Object a)
     { @RO Object r; r = null; return r; } *)
Definition derived_id : method_def :=
  {| msignature :=
       {| mscope := AbstractState;
          mtparams := [];
          mqparams := 0;
          mret := ROObject;
          mname := 0;
          mreceiver := RODerived;
          mparams := [ROObject] |};
     mbody :=
       {| mbody_stmt := SSeq (SLocal ROObject 2) (SVarAss 2 ENull);
          mreturn := 2 |} |}.

Definition DerivedDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 3; ctparams := [];
                     super := Some (2, []) |};
     body := {| fields := []; methods := [derived_id] |} |}.

Definition CT : class_table := [ObjectDef; CellDef; BaseDef; DerivedDef].

Definition main : stmt :=
  SSeq (SLocal ROBase 1)
  (SSeq (SLocal MutCell 2)
  (SSeq (SLocal ROObject 3)
  (SSeq (SLocal ROObject 4)
  (SSeq (SLocal MutObject 5)
  (SSeq (SNew 5 Mut_c 0 [] [])
  (SSeq (SNew 2 Mut_c 1 [] [5])
  (SSeq (SNew 1 Mut_c 3 [] [])
  (SSeq (SCall 3 0 1 [] [] [5])
        (SCall 4 1 1 [MutCell] [] [2]))))))))).

Definition Δ0 : tv_env := mk_tv_env [] [] AbstractState 0.
Definition sΓ0 : s_env := [MutObject].
Definition sΓfinal : s_env :=
  [MutObject; ROBase; MutCell; ROObject; ROObject; MutObject].

(* ------------------SMALL TACTICS AND FACTS------------------*)

Ltac qs := first [apply q_refl; discriminate | apply q_rd | apply q_bot].

(** Every class here is declared @RDM without type parameters, so any
    non-lost qualifier on any of them is a well-formed type. *)
Lemma wf_plain : forall Δ top q0 C,
  C < 4 -> q0 <> Lost -> wf_stype CT Δ top (TClass q0 C []).
Proof.
  intros Δ top q0 C HC Hq.
  destruct C as [|[|[|[|C]]]]; try lia;
    (eapply wfs_class;
       [reflexivity | right | reflexivity | constructor | constructor]);
    destruct q0; cbn; try qs; congruence.
Qed.

Lemma wf_plain_use : forall Δ q0 C,
  C < 4 -> q0 <> Lost -> wf_stypeuse CT Δ (TClass q0 C []).
Proof. intros. apply wf_plain; auto. Qed.

Ltac wfp := apply wf_plain_use; [cbn; lia | discriminate].

Ltac wfenv :=
  split; [cbn; lia |
          cbn; repeat (apply Forall_cons; [solve [wfp]|]); apply Forall_nil].

Ltac refl_sub :=
  apply qualified_type_subtype_refl_class; [cbn; lia | discriminate].

Ltac qual_sub := apply qtype_qual; [cbn; lia | qs | constructor].

Lemma sub_MutDerived_ROBase : forall Δ,
  qualified_type_subtype CT Δ (TClass Mut 3 []) ROBase.
Proof.
  intros Δ. eapply qtype_trans.
  - apply qtype_hier with (D := 2) (Vs := []).
    eapply si_step; [reflexivity|]. cbn. apply si_refl.
  - qual_sub.
Qed.

Lemma collect_Object : CollectFields CT 0 [].
Proof. eapply CF_Object; reflexivity. Qed.

Lemma collect_Cell : CollectFields CT 1 [value_field].
Proof.
  change (CollectFields CT 1
            (map (subst_field []) [] ++ Syntax.fields (body CellDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma collect_Base : CollectFields CT 2 [].
Proof.
  change (CollectFields CT 2
            (map (subst_field []) [] ++ Syntax.fields (body BaseDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma collect_Derived : CollectFields CT 3 [].
Proof.
  change (CollectFields CT 3
            (map (subst_field []) [] ++ Syntax.fields (body DerivedDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Base.
Qed.

Lemma no_method_in_Object : forall m D mdef,
  ~ FindMethodWithName CT 0 m D mdef.
Proof.
  intros m D mdef H. inversion H; subst.
  - cbn in Hfind. injection Hfind as <-. cbn in Hget_method. discriminate.
  - cbn in Hfind. injection Hfind as <-. cbn in Hsuper. discriminate.
Qed.

(** Looking up method 0 from Base finds Base's own declaration. *)
Lemma find_id_in_Base : forall D mdef,
  FindMethodWithName CT 2 0 D mdef -> D = 2 /\ mdef = base_id.
Proof.
  intros D mdef H. inversion H; subst.
  - cbn in Hfind. injection Hfind as <-. cbn in Hget_method.
    injection Hget_method as <-. split; reflexivity.
  - cbn in Hfind. injection Hfind as <-. cbn in Hnot_here. discriminate.
Qed.

(* ------------------CLASS TABLE WELL-FORMEDNESS------------------*)

Lemma wf_base_id : wf_method CT 2 base_id.
Proof.
  unfold wf_method. cbn.
  split; [apply receiver_plain_ok; left; exists RO; reflexivity|].
  split; [constructor|].
  split; [wfp|].
  split.
  { exists [ROBase; ROObject], ROObject. split; [|split].
    - apply ST_Skip. wfenv.
    - reflexivity.
    - refl_sub. }
  split.
  { intros def parent Ss D mdef_parent Vs Hfind Hsuper Hfm _.
    cbn in Hfind. injection Hfind as <-. cbn in Hsuper.
    injection Hsuper as <- <-.
    exfalso. eapply no_method_in_Object; eauto. }
  intros [H | H]; discriminate.
Qed.

(** The bound environment of look's body: no class parameters, one method
    parameter bounded by @RO Cell. *)
Definition ΔL : tv_env := mk_tv_env [] [ROCell] AbstractState 0.

Lemma wf_roX : wf_stypeuse CT ΔL roX.
Proof.
  unfold wf_stypeuse, roX. eapply wfs_var; [reflexivity|].
  right. discriminate.
Qed.

Lemma wf_base_look : wf_method CT 2 base_look.
Proof.
  unfold wf_method. cbn.
  assert (Hwf1 : wf_senv CT ΔL [ROBase; roX]).
  { split; [cbn; lia|].
    constructor; [wfp|]. constructor; [apply wf_roX | constructor]. }
  assert (Hwf2 : wf_senv CT ΔL [ROBase; roX; ROObject]).
  { split; [cbn; lia|].
    constructor; [wfp|]. constructor; [apply wf_roX|].
    constructor; [wfp | constructor]. }
  split; [apply receiver_plain_ok; left; exists RO; reflexivity|].
  split; [constructor; [split; [exact I | split; [wfp | intros [H | H]; discriminate]] | constructor]|].
  split; [wfp|].
  split.
  { exists [ROBase; roX; ROObject], ROObject. split; [|split].
    - eapply ST_Seq; [exact Hwf1 | |].
      + eapply ST_Local; [exact Hwf1 | wfp | | reflexivity |]; reflexivity.
      + eapply ST_VarAss with (Tx := ROObject);
          [exact Hwf2 | | discriminate | reflexivity | ].
        * (* c.value, where c : @RO X.  The members of @RO X are looked up
             at @RO Cell, the bound's class under the written qualifier. *)
          eapply ET_Field with (x := 1) (T := roX) (qx := RO) (C := 1)
            (Ts := []) (fDef := value_field);
            [exact Hwf2 | reflexivity | reflexivity |].
          eapply FL_Found; [apply collect_Cell | reflexivity].
        * cbn. refl_sub.
    - reflexivity.
    - refl_sub. }
  split.
  { intros def parent Ss D mdef_parent Vs Hfind Hsuper Hfm _.
    cbn in Hfind. injection Hfind as <-. cbn in Hsuper.
    injection Hsuper as <- <-.
    exfalso. eapply no_method_in_Object; eauto. }
  intros [H | H]; discriminate.
Qed.

Lemma wf_derived_id : wf_method CT 3 derived_id.
Proof.
  unfold wf_method. cbn.
  split; [apply receiver_plain_ok; left; exists RO; reflexivity|].
  split; [constructor|].
  split; [wfp|].
  split.
  { exists [RODerived; ROObject; ROObject], ROObject. split; [|split].
    - eapply ST_Seq; [wfenv | |].
      + eapply ST_Local; [wfenv | wfp | | reflexivity |]; reflexivity.
      + eapply ST_VarAss with (Tx := ROObject) (Te := ROObject);
          [wfenv | | discriminate | reflexivity | refl_sub].
        apply ET_Null. wfenv.
    - reflexivity.
    - refl_sub. }
  split.
  { (* The override check against Base.id *)
    intros def parent Ss D mdef_parent Vs Hfind Hsuper Hfm _.
    cbn in Hfind. injection Hfind as <-. cbn in Hsuper.
    injection Hsuper as <- <-.
    apply find_id_in_Base in Hfm. destruct Hfm as [-> ->].
    unfold method_override_compatible. cbn.
    split; [reflexivity|]. split; [reflexivity|]. split; [split; reflexivity|].
    split; [refl_sub|].
    split; [constructor; [refl_sub | constructor]|].
    cbn. split; [apply qtype_qual; [cbn; lia | cbn; qs | apply Forall2_targ_sub_refl] | radmit_plain]. }
  intros [H | H]; discriminate.
Qed.

Lemma ov_ct_wf : wf_class_table CT.
Proof.
  unfold wf_class_table. split; [|split; [|split]].
  - constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + apply WFObjectDef; reflexivity.
    + eapply WFOtherDef with (superC := 0) (Ss := []);
        try reflexivity; cbn; try solve [constructor]; auto.
      * wfp.
      * constructor; [|constructor]. unfold wf_field. cbn. wfp.
    + eapply WFOtherDef with (superC := 0) (Ss := []);
        try reflexivity; cbn; try solve [constructor]; auto.
      * wfp.
      * constructor; [apply wf_base_id|].
        constructor; [apply wf_base_look | constructor].
      * constructor; [cbn; intros [H | []]; discriminate|].
        constructor; [intros [] | constructor].
    + eapply WFOtherDef with (superC := 2) (Ss := []);
        try reflexivity; cbn; try solve [constructor]; auto.
      * wfp.
      * constructor; [apply wf_derived_id | constructor].
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

(* ------------------MAIN IS WELL TYPED------------------*)

Ltac ty_local :=
  eapply ST_Local;
    [wfenv | wfp | reflexivity | reflexivity | reflexivity].

Ltac ty_seq := eapply ST_Seq; [wfenv | |].

Lemma ov_main_typed :
  stmt_typing CT (mk_tv_env [] [] AbstractState 0) [TClass Mut 0 []] AbstractState main sΓfinal.
Proof.
  unfold main, sΓfinal.
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
  (* c = new @Mut Cell(o) *)
  ty_seq.
  { eapply ST_New with (Tx := MutCell) (argtypes := [MutObject]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | wfp | constructor | constructor
      | apply collect_Cell | | ].
    - constructor; [|constructor]. cbn. split.
      + qual_sub.
      + cbn. intuition discriminate.
    - cbn. refl_sub. }
  (* b = new @Mut Derived() *)
  ty_seq.
  { eapply ST_New with (Tx := ROBase) (argtypes := []) (fds := []);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | wfp | constructor | constructor
      | apply collect_Derived | constructor | ].
    cbn. apply sub_MutDerived_ROBase. }
  (* x = b.id(o): the static lookup starts at Base and finds Base.id *)
  ty_seq.
  { eapply ST_Call with (Tx := ROObject) (Ty := ROBase)
      (argtypes := [MutObject])
      (qy := RO) (C := 2) (Ts := []) (D := 2) (Vs := [])
      (mdef := base_id);
      [wfenv | reflexivity | reflexivity | reflexivity | reflexivity
      | | | discriminate | constructor | constructor | reflexivity
      | constructor | | | | apply method_subtyping_refl | reflexivity | constructor | recv_known].
    - eapply FOM_Here; reflexivity.
    - apply si_refl.
    - cbn. refl_sub.
    - cbn. split; [refl_sub|]. cbn. intuition discriminate.
    - constructor; [|constructor]. cbn. split; [qual_sub|].
      cbn. intuition discriminate. }
  (* y = b.look<@Mut Cell>(c) *)
  eapply ST_Call with (Tx := ROObject) (Ty := ROBase)
    (argtypes := [MutCell])
    (qy := RO) (C := 2) (Ts := []) (D := 2) (Vs := [])
    (mdef := base_look);
    [wfenv | reflexivity | reflexivity | reflexivity | reflexivity
    | | | discriminate | | | reflexivity
    | | | | | apply method_subtyping_refl | reflexivity | constructor | recv_known].
  - eapply FOM_Here; reflexivity.
  - apply si_refl.
  - constructor; [wfp | constructor].
  - constructor; [|constructor]. cbn. intuition discriminate.
  - constructor; [|constructor]. cbn. split; [intuition discriminate|].
    intros m. qual_sub.
  - cbn. refl_sub.
  - cbn. split; [refl_sub|]. cbn. intuition discriminate.
  - (* the parameter type @RO X becomes @RO Cell at this call *)
    constructor; [|constructor]. cbn. split; [qual_sub|].
    cbn. intuition discriminate.
Qed.

(* ------------------EVALUATION------------------*)

Definition rΓ0 : r_env := mkr_env [Iot 0] [] [] [].
Definition h0 : heap := [mkObj (mkruntime_type Mut_r 0 []) []].

(** x (variable 3) is null because Derived.id ran; y (variable 4) is the
    object o at location 1, read out of the Cell at location 2. *)
Definition rΓfinal : r_env :=
  mkr_env [Iot 0; Iot 3; Iot 2; Null_a; Iot 1; Iot 1] [] [] [].

Definition hfinal : heap :=
  [ mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 1 []) [Iot 1];
    mkObj (mkruntime_type Mut_r 3 []) [] ].

Ltac ev_local := eapply SBS_Seq; [apply SBS_Local; reflexivity|]; cbn.

Lemma ov_main_eval :
  eval_stmt CT (mkr_env [Iot 0] [] [] []) [mkObj (mkruntime_type Mut_r 0 []) []]
    main OK rΓfinal hfinal.
Proof.
  unfold main.
  ev_local. ev_local. ev_local. ev_local. ev_local.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq.
  { (* the receiver's runtime class is Derived, so Derived.id runs *)
    eapply SBS_Call with (mdef := derived_id) (D := 3).
    - reflexivity.
    - reflexivity.
    - eapply FOM_Here; reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold callee_env. do 4 eexists.
      split; [reflexivity|]. split; [reflexivity|]. split; [split; reflexivity|].
      split; [apply rsi_refl | reflexivity].
    - cbn. eapply SBS_Seq; [apply SBS_Local; reflexivity|]. cbn.
      eapply SBS_Assign; [reflexivity|]. apply EBS_Null.
    - reflexivity.
    - reflexivity. }
  cbn.
  (* look is not declared in Derived; the lookup climbs to Base *)
  eapply SBS_Call with (mdef := base_look) (D := 2).
  - reflexivity.
  - reflexivity.
  - eapply FOM_Super; [reflexivity | reflexivity | reflexivity | reflexivity |].
    eapply FOM_Here; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold callee_env. do 4 eexists.
    split; [reflexivity|]. split; [reflexivity|]. split; [split; reflexivity|].
    split; [|reflexivity].
    cbn. eapply rsi_step; [reflexivity|]. cbn. apply rsi_refl.
  - cbn. eapply SBS_Seq; [apply SBS_Local; reflexivity|]. cbn.
    eapply SBS_Assign; [reflexivity|].
    eapply EBS_Field; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* ------------------THE RUN PRESERVES WELL-FORMEDNESS------------------*)

Lemma ov_initial_config :
  wf_r_config CT (mk_tv_env [] [] AbstractState 0) [TClass Mut 0 []]
    (mkr_env [Iot 0] [] [] []) [mkObj (mkruntime_type Mut_r 0 []) []].
Proof.
  refine (conj ov_ct_wf (conj _ (conj _ (conj _ (conj _ (conj eq_refl _)))))).
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

(** The run ends in a well-formed configuration. *)
Corollary ov_final_config :
  wf_r_config CT (mk_tv_env [] [] AbstractState 0) sΓfinal rΓfinal hfinal.
Proof.
  eapply preservation_pico;
    eauto using ov_main_eval, ov_initial_config, ov_main_typed.
Qed.

Print Assumptions ov_final_config.
