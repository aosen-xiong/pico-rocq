From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation MutationSafety Progress Interp Immutability ReadonlyFlat
  ReadonlyWorlds ReadonlyGeneric GhostLabels ArgViews GhostTyping GhostForget
  GhostFit ArgTyping GhostInvariant ArgFit ArgInvariant ArgCases GhostOverride
  ArgClean ArgOverride GhostCall ArgCall GhostEntry ArgMain ArgEntry ArgRsf
  GhostSignature ArgSignature.

(** The abstract-state, concrete-state and transitive-state theorems applied
    to one generic program.

    class 0: @RDM class Object {}
    class 1: @RDM class Person extends Object {
       @RDA @RO Object name;            // field 0
       @Assignable @RO Object cache;    // field 1
    }
    class 2: @RDM class Box<E extends @RDM Person> extends Object {
       @Final E item;                   // field 0
    }
    class 3: @RDM class Tool extends Object {
       @TS @RO Object look(@RO Tool this, @Imm Box<@Imm Person> b, @RO Object v) {
           @Mut Person n;               // var 3
           n = new @Mut Person(v, v);
           n.name = v;
           return v;
       }
    }

    main (this : @Mut Object):
       @Imm Person p;  @Imm Box<@Imm Person> b;  @Mut Tool t;
       @RO Object r;   @Mut Person m;
       p = new @Imm Person(this, this);
       b = new @Imm Box<@Imm Person>(p);
       t = new @Mut Tool();
       m = new @Mut Person(this, this);
       --- the three statements examined below ---
       p.cache = m;          // abstract-state code
       m.name = this;        // concrete-state code
       r = t.look(b, this);  // a transitive-state call

    The box is coupled to its element: the bound of [E] is receiver-dependent,
    so the field [item], typed by the bare type variable, belongs to the
    box's abstract state, and the immutable box protects the person. *)

(* ------------------THE PROGRAM------------------*)

Definition ROObject : qualified_type := TClass RO 0 [].
Definition MutObject : qualified_type := TClass Mut 0 [].
Definition ImmPerson : qualified_type := TClass Imm 1 [].
Definition MutPerson : qualified_type := TClass Mut 1 [].
Definition RDMPerson : qualified_type := TClass RDM 1 [].
Definition tE : qualified_type := TVar TVSub ClassVar 0.
Definition ImmBox : qualified_type := TClass Imm 2 [ImmPerson].
Definition MutTool : qualified_type := TClass Mut 3 [].
Definition ROTool : qualified_type := TClass RO 3 [].

Definition name_field : field_def := {| assignability := RDA; ftype := ROObject |}.
Definition cache_field : field_def := {| assignability := Assignable; ftype := ROObject |}.
Definition item_field : field_def := {| assignability := Final; ftype := tE |}.

Definition look_body : stmt :=
  SSeq (SLocal MutPerson 3)
    (SSeq (SNew 3 Mut_c 1 [] [2; 2]) (SFldWrite 3 0 2)).

Definition look_def : method_def :=
  {| msignature := {| mscope := TransitiveState; mtparams := []; mqparams := 0;
                      mret := ROObject; mname := 0;
                      mreceiver := ROTool; mparams := [ImmBox; ROObject] |};
     mbody := {| mbody_stmt := look_body; mreturn := 2 |} |}.

Definition ObjectDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 0; ctparams := [];
                     super := None |};
     body := {| fields := []; methods := [] |} |}.
Definition PersonDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 1; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := [name_field; cache_field]; methods := [] |} |}.
Definition BoxDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 2; ctparams := [RDMPerson];
                     super := Some (0, []) |};
     body := {| fields := [item_field]; methods := [] |} |}.
Definition ToolDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 3; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := []; methods := [look_def] |} |}.
Definition CT : class_table := [ObjectDef; PersonDef; BoxDef; ToolDef].

Definition Δ0 : tv_env := mk_tv_env [] [] AbstractState 0.
Definition sΓ0 : s_env := [MutObject].
Definition sΓ1 : s_env := [MutObject; ImmPerson; ImmBox; MutTool; ROObject; MutPerson].

Definition prefix : stmt :=
  SSeq (SLocal ImmPerson 1)
  (SSeq (SLocal ImmBox 2)
  (SSeq (SLocal MutTool 3)
  (SSeq (SLocal ROObject 4)
  (SSeq (SLocal MutPerson 5)
  (SSeq (SNew 1 Imm_c 1 [] [0; 0])
  (SSeq (SNew 2 Imm_c 2 [ImmPerson] [1])
  (SSeq (SNew 3 Mut_c 3 [] [])
        (SNew 5 Mut_c 1 [] [0; 0])))))))).

Definition stmtA : stmt := SFldWrite 1 1 5.       (* p.cache = m *)
Definition stmtC : stmt := SFldWrite 5 0 0.       (* m.name = this *)
Definition callT : stmt := SCall 4 0 3 [] [] [2; 0].  (* r = t.look(b, this) *)

(* ------------------WELL-FORMED TYPES------------------*)

Ltac qs := first [apply q_refl; discriminate | apply q_rd | apply q_bot].
Ltac wf_plain :=
  eapply wfs_class;
    [reflexivity | right; cbn; qs | reflexivity | constructor | constructor].
Ltac refl_sub :=
  apply qualified_type_subtype_refl_class; [cbn; lia | discriminate].

Lemma wf_ROObject : forall Δ, wf_stypeuse CT Δ ROObject.
Proof. intros. unfold wf_stypeuse, ROObject. wf_plain. Qed.
Lemma wf_MutObject : forall Δ, wf_stypeuse CT Δ MutObject.
Proof. intros. unfold wf_stypeuse, MutObject. wf_plain. Qed.
Lemma wf_ImmPerson : forall Δ top, wf_stype CT Δ top ImmPerson.
Proof. intros. unfold ImmPerson. wf_plain. Qed.
Lemma wf_MutPerson : forall Δ top, wf_stype CT Δ top MutPerson.
Proof. intros. unfold MutPerson. wf_plain. Qed.
Lemma wf_MutTool : forall Δ, wf_stypeuse CT Δ MutTool.
Proof. intros. unfold wf_stypeuse, MutTool. wf_plain. Qed.
Lemma wf_ROTool : forall Δ, wf_stypeuse CT Δ ROTool.
Proof. intros. unfold wf_stypeuse, ROTool. wf_plain. Qed.

Lemma wf_ImmBox : forall Δ, wf_stypeuse CT Δ ImmBox.
Proof.
  intros. unfold wf_stypeuse, ImmBox.
  eapply wfs_class; [reflexivity | right; cbn; qs | reflexivity | |].
  - constructor; [apply wf_ImmPerson | constructor].
  - constructor; [|constructor]. intros m. cbn. refl_sub.
Qed.

Lemma sub_to_ROObject : forall Δ q0 C,
  C = 1 \/ C = 3 -> qualified_type_subtype CT Δ (TClass q0 C []) ROObject.
Proof.
  intros Δ q0 C HC. eapply qtype_trans.
  - apply qtype_hier with (D := 0) (Vs := []).
    eapply si_step; [destruct HC; subst; reflexivity|]. cbn. apply si_refl.
  - apply qtype_qual; [cbn; lia | apply q_rd | constructor].
Qed.

Lemma sub_Object_RO : forall Δ q0, qualified_type_subtype CT Δ (TClass q0 0 []) ROObject.
Proof. intros. apply qtype_qual; [cbn; lia | apply q_rd | constructor]. Qed.

Local Hint Resolve wf_ROObject wf_MutObject wf_MutTool wf_ROTool wf_ImmBox : ex.
Lemma wf_ImmPerson_use : forall Δ, wf_stypeuse CT Δ ImmPerson.
Proof. intros. apply wf_ImmPerson. Qed.
Lemma wf_MutPerson_use : forall Δ, wf_stypeuse CT Δ MutPerson.
Proof. intros. apply wf_MutPerson. Qed.
Local Hint Resolve wf_ImmPerson_use wf_MutPerson_use : ex.

Ltac wfenv :=
  split; [cbn; lia |
          cbn; repeat (apply Forall_cons; [solve [auto with ex]|]); apply Forall_nil].

(* ------------------FIELDS AND METHODS------------------*)

Lemma collect_Object : CollectFields CT 0 [].
Proof. eapply CF_Object; reflexivity. Qed.
Lemma collect_Person : CollectFields CT 1 [name_field; cache_field].
Proof.
  change (CollectFields CT 1 (map (subst_field []) [] ++ Syntax.fields (body PersonDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.
Lemma collect_Box : CollectFields CT 2 [item_field].
Proof.
  change (CollectFields CT 2 (map (subst_field []) [] ++ Syntax.fields (body BoxDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.
Lemma collect_Tool : CollectFields CT 3 [].
Proof.
  change (CollectFields CT 3 (map (subst_field []) [] ++ Syntax.fields (body ToolDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma no_method_in_Object : forall m D mdef, ~ FindMethodWithName CT 0 m D mdef.
Proof.
  intros m D mdef H. inversion H; subst.
  - cbn in Hfind. injection Hfind as <-. cbn in Hget_method. discriminate.
  - cbn in Hfind. injection Hfind as <-. cbn in Hsuper. discriminate.
Qed.

Definition ΔL : tv_env := method_tv_env CT 3 (msignature look_def).

Lemma look_body_typed :
  stmt_typing CT ΔL [ROTool; ImmBox; ROObject] TransitiveState look_body
    [ROTool; ImmBox; ROObject; MutPerson].
Proof.
  unfold look_body.
  eapply ST_Seq; [wfenv | |].
  { eapply ST_Local; [wfenv | apply wf_MutPerson | reflexivity | reflexivity | reflexivity]. }
  eapply ST_Seq; [wfenv | |].
  { eapply ST_New with (Tx := MutPerson) (argtypes := [ROObject; ROObject])
      (fds := [name_field; cache_field]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutPerson | constructor | constructor
      | apply collect_Person | | ].
    - constructor; [|constructor; [|constructor]]; cbn;
        (split; [refl_sub | cbn; intuition discriminate]).
    - cbn. refl_sub. }
  eapply ST_FldWrite with (Tx := MutPerson) (Ty := ROObject) (qx := Mut)
    (C := 1) (Ts := []) (fieldT := name_field);
    [wfenv | reflexivity | reflexivity | reflexivity | | | reflexivity].
  - eapply FL_Found; [apply collect_Person | reflexivity].
  - split; [cbn; refl_sub | cbn; intuition discriminate].
Qed.

Lemma wf_look : wf_method CT 3 look_def.
Proof.
  unfold wf_method. cbn. fold ΔL.
  split; [apply receiver_plain_ok; left; exists RO; reflexivity|].
  split; [constructor|].
  split; [apply wf_ROObject|].
  split.
  { exists [ROTool; ImmBox; ROObject; MutPerson], ROObject. split; [|split].
    - exact look_body_typed.
    - reflexivity.
    - refl_sub. }
  split.
  { intros def parent Ss D mdef_parent Vs Hfind Hsuper Hfm _.
    cbn in Hfind. injection Hfind as <-. cbn in Hsuper. injection Hsuper as <- <-.
    exfalso. eapply no_method_in_Object; eauto. }
  intros _. split.
  - apply nm_class; [discriminate | constructor].
  - constructor; [|constructor; [|constructor]].
    + apply nm_class; [discriminate|]. constructor; [|constructor].
      apply nm_class; [discriminate | constructor].
    + apply nm_class; [discriminate | constructor].
Qed.

Lemma ct_wf : wf_class_table CT.
Proof.
  unfold wf_class_table. split; [|split; [|split]].
  - constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + apply WFObjectDef; reflexivity.
    + eapply WFOtherDef with (superC := 0) (Ss := []);
        try reflexivity; cbn; try solve [constructor]; auto.
      * unfold wf_stypeuse. wf_plain.
      * constructor; [apply wf_ROObject | constructor; [apply wf_ROObject | constructor]].
    + eapply WFOtherDef with (superC := 0) (Ss := []);
        try reflexivity; cbn; try solve [constructor]; auto.
      * constructor; [|constructor]. split; [exact I|]. unfold wf_stypeuse. wf_plain.
      * unfold wf_stypeuse. wf_plain.
      * constructor; [|constructor]. eapply wfs_var; [reflexivity | right; discriminate].
    + eapply WFOtherDef with (superC := 0) (Ss := []);
        try reflexivity; cbn; try solve [constructor]; auto.
      * unfold wf_stypeuse. wf_plain.
      * constructor; [|constructor]. apply wf_look.
      * constructor; [intros []|constructor].
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

(* ------------------THE START AND THE PREFIX------------------*)

Definition rΓ0 : r_env := mkr_env [Iot 0] [] [] [].
Definition h0 : heap := [mkObj (mkruntime_type Mut_r 0 []) []].

Lemma initial_config : wf_r_config CT Δ0 sΓ0 rΓ0 h0.
Proof.
  refine (conj ct_wf (conj _ (conj _ (conj _ (conj _ (conj eq_refl _)))))).
  - intros ι Hι. simpl in Hι. assert (ι = 0) by lia. subst ι.
    unfold wf_obj. simpl. split.
    + unfold wf_rtypeuse. simpl.
      refine (conj eq_refl (conj (Forall_nil _) _)). constructor.
    + exists (@nil field_def). refine (conj collect_Object (conj eq_refl _)). constructor.
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

Lemma start : start_state CT Δ0 sΓ0 rΓ0 h0.
Proof.
  refine (conj initial_config (conj eq_refl (conj eq_refl _))).
  intros l o def Hl Hf. destruct l as [|l]; cbn in Hl; [|destruct l; discriminate].
  inversion Hl; subst o. cbn in Hf. inversion Hf. reflexivity.
Qed.

Ltac ty_local :=
  eapply ST_Local;
    [wfenv | solve [auto with ex] | reflexivity | reflexivity | reflexivity].
Ltac ty_seq := eapply ST_Seq; [wfenv | |].

Lemma prefix_typed : stmt_typing CT Δ0 sΓ0 AbstractState prefix sΓ1.
Proof.
  unfold prefix, sΓ0, sΓ1.
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. cbn.
  (* p = new @Imm Person(this, this) *)
  ty_seq.
  { eapply ST_New with (Tx := ImmPerson) (argtypes := [MutObject; MutObject])
      (fds := [name_field; cache_field]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_ImmPerson | constructor | constructor
      | apply collect_Person | | ].
    - constructor; [|constructor; [|constructor]]; cbn;
        (split; [apply sub_Object_RO | cbn; intuition discriminate]).
    - cbn. refl_sub. }
  (* b = new @Imm Box<@Imm Person>(p) *)
  ty_seq.
  { eapply ST_New with (Tx := ImmBox) (argtypes := [ImmPerson]) (fds := [item_field]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_ImmBox | | | apply collect_Box | | ].
    - constructor; [|constructor]. cbn. intuition discriminate.
    - constructor; [|constructor]. cbn. split; [intuition discriminate|].
      intros m. refl_sub.
    - constructor; [|constructor]. cbn. split; [refl_sub | cbn; intuition discriminate].
    - cbn. refl_sub. }
  (* t = new @Mut Tool() *)
  ty_seq.
  { eapply ST_New with (Tx := MutTool) (argtypes := []) (fds := []);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutTool | constructor | constructor
      | apply collect_Tool | constructor | ].
    cbn. refl_sub. }
  (* m = new @Mut Person(this, this) *)
  eapply ST_New with (Tx := MutPerson) (argtypes := [MutObject; MutObject])
    (fds := [name_field; cache_field]);
    [wfenv | reflexivity | reflexivity | reflexivity | discriminate
    | reflexivity | apply wf_MutPerson | constructor | constructor
    | apply collect_Person | | ].
  - constructor; [|constructor; [|constructor]]; cbn;
      (split; [apply sub_Object_RO | cbn; intuition discriminate]).
  - cbn. refl_sub.
Qed.

(** The state after the prefix: main object 0, immutable person 1, immutable
    box 2 holding it, tool 3, mutable person 4. *)
Definition rΓ1 : r_env := mkr_env [Iot 0; Iot 1; Iot 2; Iot 3; Null_a; Iot 4] [] [] [].
Definition h1 : heap :=
  [ mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Imm_r 1 []) [Iot 0; Iot 0];
    mkObj (mkruntime_type Imm_r 2 [RClass Imm 1 []]) [Iot 1];
    mkObj (mkruntime_type Mut_r 3 []) [];
    mkObj (mkruntime_type Mut_r 1 []) [Iot 0; Iot 0] ].

(** The interpreter computes this state. *)
Lemma prefix_run : run CT 0 rΓ0 h0 prefix = Some (FDone OK, rΓ1, h1).
Proof. reflexivity. Qed.

Lemma prefix_eval : eval_stmt CT rΓ0 h0 prefix OK rΓ1 h1.
Proof. eapply eval_fuel_erase; [apply run_sound; exact prefix_run | reflexivity]. Qed.

Lemma config1 : wf_r_config CT Δ0 sΓ1 rΓ1 h1.
Proof.
  eapply preservation_pico;
    [exact prefix_eval | reflexivity | exact initial_config | exact prefix_typed].
Qed.

(** The box reaches the person through its abstract state: the field is
    typed by the bare variable [E], whose declared bound is
    receiver-dependent. *)
Lemma box_reaches_person : reachable_abs CT h1 2 1.
Proof.
  eapply reachable_abs_step with (k := 0) (fd := item_field);
    [reflexivity | reflexivity | | | right; reflexivity].
  - eapply FL_Found; [apply collect_Box | reflexivity].
  - cbn. exists RDM, 1, (@nil qualified_type). split; [reflexivity | right; reflexivity].
Qed.

(* ------------------ABSTRACT STATE------------------*)

(** [p.cache = m] is abstract-state code: it replaces an assignable field
    of the immutable person. *)
Lemma stmtA_typed : stmt_typing CT Δ0 sΓ1 AbstractState stmtA sΓ1.
Proof.
  eapply ST_FldWrite with (Tx := ImmPerson) (Ty := MutPerson) (qx := Imm)
    (C := 1) (Ts := []) (fieldT := cache_field);
    [wfenv | reflexivity | reflexivity | reflexivity | | | reflexivity].
  - eapply FL_Found; [apply collect_Person | reflexivity].
  - split; [cbn; apply sub_to_ROObject; auto | cbn; intuition discriminate].
Qed.

(** However the statement ends, the person's [name] and the box's [item]
    are unchanged: both are in the abstract state of the immutable box. *)
Theorem abstract_state_example : forall res rΓ' h',
  eval_stmt CT rΓ1 h1 stmtA res rΓ' h' ->
  (exists vals', runtime_getObj h' 1 = Some (mkObj (mkruntime_type Imm_r 1 []) vals') /\
                 nth_error vals' 0 = Some (Iot 0)) /\
  (exists vals', runtime_getObj h' 2 =
                   Some (mkObj (mkruntime_type Imm_r 2 [RClass Imm 1 []]) vals') /\
                 nth_error vals' 0 = Some (Iot 1)).
Proof.
  intros res rΓ' h' Hev. split.
  - destruct (abstract_state_preservation CT Δ0 sΓ1 AbstractState rΓ1 h1 stmtA
                res rΓ' h' sΓ1 2 2 [RClass Imm 1 []] [Iot 1] 1 1 Imm_r [] [Iot 0; Iot 0] 0
                eq_refl box_reaches_person config1 stmtA_typed Hev eq_refl)
      as (vals' & Ho & Hn).
    + right. exists name_field. split; [|reflexivity].
      eapply FL_Found; [apply collect_Person | reflexivity].
    + exists vals'. split; [exact Ho | symmetry; exact Hn].
  - destruct (abstract_state_preservation CT Δ0 sΓ1 AbstractState rΓ1 h1 stmtA
                res rΓ' h' sΓ1 2 2 [RClass Imm 1 []] [Iot 1] 2 2 Imm_r [RClass Imm 1 []]
                [Iot 1] 0 eq_refl (reachable_abs_heap CT h1 2 ltac:(cbn; lia))
                config1 stmtA_typed Hev eq_refl)
      as (vals' & Ho & Hn).
    + left. exists item_field. split; [|reflexivity].
      eapply FL_Found; [apply collect_Box | reflexivity].
    + exists vals'. split; [exact Ho | symmetry; exact Hn].
Qed.

(** The statement is not a no-op: the interpreter runs it, and the person's
    [cache] now holds the mutable person. *)
Example abstract_state_example_runs : exists h',
  run CT 0 rΓ1 h1 stmtA = Some (FDone OK, rΓ1, h') /\
  runtime_getObj h' 1 = Some (mkObj (mkruntime_type Imm_r 1 []) [Iot 0; Iot 4]).
Proof. eexists. split; reflexivity. Qed.

(* ------------------CONCRETE STATE------------------*)

(** [m.name = this] is concrete-state code: it writes a mutable object
    outside the abstract state of the box. *)
Lemma stmtC_typed : stmt_typing CT Δ0 sΓ1 ConcreteState stmtC sΓ1.
Proof.
  eapply ST_FldWrite with (Tx := MutPerson) (Ty := MutObject) (qx := Mut)
    (C := 1) (Ts := []) (fieldT := name_field);
    [wfenv | reflexivity | reflexivity | reflexivity | | | reflexivity].
  - eapply FL_Found; [apply collect_Person | reflexivity].
  - split; [cbn; apply sub_Object_RO | cbn; intuition discriminate].
Qed.

(** In concrete-state code even the assignable [cache] of the person is
    unchanged. *)
Theorem concrete_state_example : forall res rΓ' h',
  eval_stmt CT rΓ1 h1 stmtC res rΓ' h' ->
  exists vals', runtime_getObj h' 1 = Some (mkObj (mkruntime_type Imm_r 1 []) vals') /\
                nth_error vals' 1 = Some (Iot 0).
Proof.
  intros res rΓ' h' Hev.
  destruct (concrete_state_preservation CT Δ0 sΓ1 ConcreteState rΓ1 h1 stmtC
              res rΓ' h' sΓ1 2 2 [RClass Imm 1 []] [Iot 1] 1 1 Imm_r [] [Iot 0; Iot 0] 1
              (or_introl eq_refl) eq_refl box_reaches_person config1 stmtC_typed Hev
              eq_refl) as (vals' & Ho & Hn).
  exists vals'. split; [exact Ho | symmetry; exact Hn].
Qed.

(** The write to the abstract-state code's target is rejected here: in
    concrete-state code the [cache] of an immutable person is not
    assignable. *)
Example stmtA_not_concrete : vpa_a ConcreteState Imm Assignable = Final.
Proof. reflexivity. Qed.

(* ------------------TRANSITIVE STATE------------------*)

Lemma find_look : FindMethodWithName CT 3 0 3 look_def.
Proof. eapply FOM_Here; reflexivity. Qed.

Lemma callT_typed : stmt_typing CT Δ0 sΓ1 AbstractState callT sΓ1.
Proof.
  eapply ST_Call with (Tx := ROObject) (Ty := MutTool) (argtypes := [ImmBox; MutObject])
    (qy := Mut) (C := 3) (Ts := []) (D := 3) (Vs := []) (mdef := look_def);
    [wfenv | reflexivity | reflexivity | reflexivity | reflexivity
    | apply find_look | apply si_refl | discriminate | constructor | constructor
    | reflexivity | constructor | | | | apply method_ts_as | reflexivity
    | constructor | recv_known].
  - cbn. refl_sub.
  - cbn. apply qtype_qual; [cbn; lia | apply q_rd | constructor].
  - constructor; [|constructor; [|constructor]]; cbn.
    + split; [refl_sub | cbn; intuition discriminate].
    + split; [apply sub_Object_RO | cbn; intuition discriminate].
Qed.

(** However the transitive-state call ends, every field of every object that
    existed before it is unchanged: here the assignable [cache] of the
    immutable person and the [name] of the mutable person. *)
Theorem transitive_state_example : forall res rΓ' h',
  eval_stmt CT rΓ1 h1 callT res rΓ' h' ->
  (exists vals', runtime_getObj h' 1 = Some (mkObj (mkruntime_type Imm_r 1 []) vals') /\
                 nth_error vals' 1 = Some (Iot 0)) /\
  (exists vals', runtime_getObj h' 4 = Some (mkObj (mkruntime_type Mut_r 1 []) vals') /\
                 nth_error vals' 0 = Some (Iot 0)).
Proof.
  intros res rΓ' h' Hev.
  pose proof (rs_ts_preservation_from_start CT Δ0 sΓ0 AbstractState rΓ0 h0 prefix
                sΓ1 rΓ1 h1 4 0 3 [] [] [2; 0] sΓ1 rΓ' h' 3 3 3 look_def res
                start prefix_typed prefix_eval callT_typed Hev eq_refl eq_refl find_look)
    as Hall.
  split.
  - destruct (Hall 1 Imm_r 1 [] [Iot 0; Iot 0] 1 eq_refl (or_intror eq_refl))
      as (vals' & Ho & Hn).
    exists vals'. split; [exact Ho | symmetry; exact Hn].
  - destruct (Hall 4 Mut_r 1 [] [Iot 0; Iot 0] 0 eq_refl (or_intror eq_refl))
      as (vals' & Ho & Hn).
    exists vals'. split; [exact Ho | symmetry; exact Hn].
Qed.

(** The call is not a no-op: the interpreter runs it, and it allocates and
    writes a new person. *)
Example transitive_state_example_runs : exists rΓ' h',
  run CT 1 rΓ1 h1 callT = Some (FDone OK, rΓ', h') /\ length h' = 6.
Proof. do 2 eexists. split; reflexivity. Qed.

Print Assumptions abstract_state_example.
Print Assumptions concrete_state_example.
Print Assumptions transitive_state_example.
