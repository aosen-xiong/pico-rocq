From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation MutationSafety Progress Interp.

(** A qualifier parameter on a type argument of a method's declared receiver.

    class 0: @RDM class Object {}
    class 1: @RDM class Person extends Object {
       @RDA @RO Object name;            // field 0
    }
    class 2: @RDM class Box<E extends @RO Person> extends Object {
       @RDA E item;                     // field 0
       // returns the element with the mutability the caller chose
       @RS <Q> [Q]E get(@RO Box<[Q]E> this) {
           [Q]E r;  r = this.item;  return r;
       }
    }

    main (this : @Mut Object):
       @Mut Person p;  @Imm Person i;
       @Mut Box<@Mut Person> b;  @Imm Box<@Imm Person> c;
       @Mut Person m;  @Imm Person j;
       p = new @Mut Person(this);
       i = new @Imm Person(this);
       b = new @Mut Box<@Mut Person>(p);
       c = new @Imm Box<@Imm Person>(i);
       m = b.<@Mut>get();
       j = c.<@Imm>get();

    The receiver of [get] is a readonly box whose element type is [E] under
    the qualifier parameter [Q].  A call replaces [Q] by its qualifier
    argument, so the first call asks for a box of mutable persons and returns
    a mutable person, and the second asks for a box of immutable persons and
    returns an immutable one. *)

(* ------------------THE PROGRAM------------------*)

Definition ROObject : qualified_type := TClass RO 0 [].
Definition MutObject : qualified_type := TClass Mut 0 [].
Definition ROPerson : qualified_type := TClass RO 1 [].
Definition MutPerson : qualified_type := TClass Mut 1 [].
Definition ImmPerson : qualified_type := TClass Imm 1 [].
Definition tE : qualified_type := TVar TVSub ClassVar 0.
(* [Q]E: the class's type variable under the method's qualifier parameter *)
Definition tQE : qualified_type := TVar (TVPoly 0) ClassVar 0.
Definition ROBoxQE : qualified_type := TClass RO 2 [tQE].
Definition MutBox : qualified_type := TClass Mut 2 [MutPerson].
Definition ImmBox : qualified_type := TClass Imm 2 [ImmPerson].

Definition name_field : field_def := {| assignability := RDA; ftype := ROObject |}.
Definition item_field : field_def := {| assignability := RDA; ftype := tE |}.

Definition get_body : stmt := SSeq (SLocal tQE 1) (SVarAss 1 (EField 0 0)).

Definition get_def : method_def :=
  {| msignature := {| mscope := ReadonlyState; mtparams := []; mqparams := 1;
                      mret := tQE; mname := 0;
                      mreceiver := ROBoxQE; mparams := [] |};
     mbody := {| mbody_stmt := get_body; mreturn := 1 |} |}.

Definition ObjectDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 0; ctparams := [];
                     super := None |};
     body := {| fields := []; methods := [] |} |}.
Definition PersonDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 1; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := [name_field]; methods := [] |} |}.
Definition BoxDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 2; ctparams := [ROPerson];
                     super := Some (0, []) |};
     body := {| fields := [item_field]; methods := [get_def] |} |}.
Definition CT : class_table := [ObjectDef; PersonDef; BoxDef].

Definition Δ0 : tv_env := mk_tv_env [] [] AbstractState 0.
Definition sΓ0 : s_env := [MutObject].
Definition sΓ1 : s_env :=
  [MutObject; MutPerson; ImmPerson; MutBox; ImmBox; MutPerson; ImmPerson].

Definition main : stmt :=
  SSeq (SLocal MutPerson 1)
  (SSeq (SLocal ImmPerson 2)
  (SSeq (SLocal MutBox 3)
  (SSeq (SLocal ImmBox 4)
  (SSeq (SLocal MutPerson 5)
  (SSeq (SLocal ImmPerson 6)
  (SSeq (SNew 1 Mut_c 1 [] [0])
  (SSeq (SNew 2 Imm_c 1 [] [0])
  (SSeq (SNew 3 Mut_c 2 [MutPerson] [1])
  (SSeq (SNew 4 Imm_c 2 [ImmPerson] [2])
  (SSeq (SCall 5 0 3 [] [QLit Mut] [])
        (SCall 6 0 4 [] [QLit Imm] []))))))))))).

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
Lemma wf_ROPerson : forall Δ, wf_stypeuse CT Δ ROPerson.
Proof. intros. unfold wf_stypeuse, ROPerson. wf_plain. Qed.
Lemma wf_MutPerson : forall Δ top, wf_stype CT Δ top MutPerson.
Proof. intros. unfold MutPerson. wf_plain. Qed.
Lemma wf_ImmPerson : forall Δ top, wf_stype CT Δ top ImmPerson.
Proof. intros. unfold ImmPerson. wf_plain. Qed.

Lemma sub_Person_RO : forall Δ q0, qualified_type_subtype CT Δ (TClass q0 1 []) ROPerson.
Proof. intros. apply qtype_qual; [cbn; lia | apply q_rd | constructor]. Qed.
Lemma sub_Object_RO : forall Δ q0, qualified_type_subtype CT Δ (TClass q0 0 []) ROObject.
Proof. intros. apply qtype_qual; [cbn; lia | apply q_rd | constructor]. Qed.

Lemma wf_MutBox : forall Δ, wf_stypeuse CT Δ MutBox.
Proof.
  intros. unfold wf_stypeuse, MutBox.
  eapply wfs_class; [reflexivity | right; cbn; qs | reflexivity | |].
  - constructor; [apply wf_MutPerson | constructor].
  - constructor; [|constructor]. intros m. cbn. apply sub_Person_RO.
Qed.
Lemma wf_ImmBox : forall Δ, wf_stypeuse CT Δ ImmBox.
Proof.
  intros. unfold wf_stypeuse, ImmBox.
  eapply wfs_class; [reflexivity | right; cbn; qs | reflexivity | |].
  - constructor; [apply wf_ImmPerson | constructor].
  - constructor; [|constructor]. intros m. cbn. apply sub_Person_RO.
Qed.

Definition ΔM : tv_env := method_tv_env CT 2 (msignature get_def).

(** The use [[Q]E] is well formed where [Q] is in scope. *)
Lemma wf_tQE : forall top, wf_stype CT ΔM top tQE.
Proof. intros top. unfold tQE. eapply wfs_var; [reflexivity | cbn; lia]. Qed.

(** Whichever qualifier [Q] stands for, [[Q]E] is a readonly [Person]. *)
Lemma sub_tQE_ROPerson : forall m,
  qualified_type_subtype CT (with_mode ΔM m) tQE ROPerson.
Proof.
  intros m. eapply qtype_trans; [apply qtype_pvar_ro|].
  eapply qtype_qvar_bound. apply qtype_var_bound. reflexivity.
Qed.

(** The declared receiver [@RO Box<[Q]E>] is well formed. *)
Lemma wf_ROBoxQE : wf_stypeuse CT ΔM ROBoxQE.
Proof.
  eapply wfs_class; [reflexivity | right; cbn; apply q_rd | reflexivity | |].
  - constructor; [apply wf_tQE | constructor].
  - constructor; [|constructor]. intros m. cbn. apply sub_tQE_ROPerson.
Qed.

Lemma wf_tQE_use : wf_stypeuse CT ΔM tQE.
Proof. apply wf_tQE. Qed.
Lemma wf_MutPerson_use : forall Δ, wf_stypeuse CT Δ MutPerson.
Proof. intros. apply wf_MutPerson. Qed.
Lemma wf_ImmPerson_use : forall Δ, wf_stypeuse CT Δ ImmPerson.
Proof. intros. apply wf_ImmPerson. Qed.

Local Hint Resolve wf_ROObject wf_MutObject wf_ROPerson wf_MutPerson_use
  wf_ImmPerson_use wf_MutBox wf_ImmBox wf_tQE_use wf_ROBoxQE : ex.

Ltac wfenv :=
  split; [cbn; lia |
          cbn; repeat (apply Forall_cons; [solve [auto with ex]|]); apply Forall_nil].

(* ------------------FIELDS AND METHODS------------------*)

Lemma collect_Object : CollectFields CT 0 [].
Proof. eapply CF_Object; reflexivity. Qed.
Lemma collect_Person : CollectFields CT 1 [name_field].
Proof.
  change (CollectFields CT 1 (map (subst_field []) [] ++ Syntax.fields (body PersonDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.
Lemma collect_Box : CollectFields CT 2 [item_field].
Proof.
  change (CollectFields CT 2 (map (subst_field []) [] ++ Syntax.fields (body BoxDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma no_method_in_Object : forall m D mdef, ~ FindMethodWithName CT 0 m D mdef.
Proof.
  intros m D mdef H. inversion H; subst.
  - cbn in Hfind. injection Hfind as <-. cbn in Hget_method. discriminate.
  - cbn in Hfind. injection Hfind as <-. cbn in Hsuper. discriminate.
Qed.

(** Reading the field through the declared receiver gives [[Q]E]: the stored
    element under the method's qualifier parameter. *)
Example item_through_receiver :
  member_type ReadonlyState RO [tQE] [] [] (ftype item_field) = tQE.
Proof. reflexivity. Qed.

(** [[Q]E] reaches no mutable position. *)
Lemma tQE_no_mut : no_mut ΔM tQE.
Proof. unfold tQE. eapply nm_pvar; [reflexivity | constructor]. Qed.

Lemma get_body_typed :
  stmt_typing CT ΔM [ROBoxQE] ReadonlyState get_body [ROBoxQE; tQE].
Proof.
  unfold get_body.
  eapply ST_Seq; [wfenv | |].
  { eapply ST_Local; [wfenv | apply wf_tQE | reflexivity | reflexivity | reflexivity]. }
  eapply ST_VarAss with (Tx := tQE) (Te := tQE);
    [wfenv | | discriminate | reflexivity | apply qtype_pvar_refl].
  change tQE with (member_type ReadonlyState RO [tQE] [] [] (ftype item_field)) at 2.
  eapply ET_Field with (T := ROBoxQE) (C := 2); [wfenv | reflexivity | reflexivity |].
  eapply FL_Found; [apply collect_Box | reflexivity].
Qed.

Lemma wf_get : wf_method CT 2 get_def.
Proof.
  unfold wf_method. cbn. fold ΔM.
  assert (HnmP : no_mut ΔM ROPerson) by (apply nm_class; [discriminate | constructor]).
  split.
  { split.
    - exists [tQE]. split.
      + split; [reflexivity|]. intros [|i] T H; [|destruct i; discriminate].
        inversion H. eexists. reflexivity.
      + left. exists RO. reflexivity.
    - intros _. right. split.
      + constructor; [exact HnmP | constructor].
      + intros u o n [H | []]. inversion H. }
  split; [constructor|].
  split; [apply wf_tQE|].
  split.
  { exists [ROBoxQE; tQE], tQE. split; [|split].
    - exact get_body_typed.
    - reflexivity.
    - apply qtype_pvar_refl. }
  split.
  { intros def parent Ss D mdef_parent Vs Hfind Hsuper Hfm _.
    cbn in Hfind. injection Hfind as <-. cbn in Hsuper. injection Hsuper as <- <-.
    exfalso. eapply no_method_in_Object; eauto. }
  intros _. split.
  - apply nm_class; [discriminate|]. constructor; [apply tQE_no_mut | constructor].
  - constructor.
Qed.

Lemma ct_wf : wf_class_table CT.
Proof.
  unfold wf_class_table. split; [|split; [|split]].
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + apply WFObjectDef; reflexivity.
    + eapply WFOtherDef with (superC := 0) (Ss := []);
        try reflexivity; cbn; try solve [constructor]; auto.
      * unfold wf_stypeuse. wf_plain.
      * constructor; [apply wf_ROObject | constructor].
    + eapply WFOtherDef with (superC := 0) (Ss := []);
        try reflexivity; cbn; try solve [constructor]; auto.
      * constructor; [|constructor]. split; [exact I|]. unfold wf_stypeuse. wf_plain.
      * unfold wf_stypeuse. wf_plain.
      * constructor; [|constructor]. eapply wfs_var; [reflexivity | right; discriminate].
      * constructor; [apply wf_get | constructor].
      * constructor; [intros [] | constructor].
  - exists ObjectDef. split; reflexivity.
  - intros i def Hi Hfind.
    destruct i as [|[|[|i]]]; try lia; cbn in Hfind.
    + injection Hfind as <-. discriminate.
    + injection Hfind as <-. discriminate.
    + destruct i; discriminate.
  - intros i def Hfind.
    destruct i as [|[|[|i]]]; cbn in Hfind.
    + injection Hfind as <-. reflexivity.
    + injection Hfind as <-. reflexivity.
    + injection Hfind as <-. reflexivity.
    + destruct i; discriminate.
Qed.

(* ------------------WHAT A CALL ASKS OF THE RECEIVER------------------*)

(** With the qualifier argument [@Mut], the call asks for a box of mutable
    persons and returns a mutable person. *)
Example recv_at_mut :
  member_recv Mut [MutPerson] [] [QLit Mut] ROBoxQE = TClass RO 2 [MutPerson].
Proof. reflexivity. Qed.
Example result_at_mut :
  member_type AbstractState Mut [MutPerson] [] [QLit Mut] tQE = MutPerson.
Proof. reflexivity. Qed.

(** With [@Imm] on the same box it asks for a box of immutable persons, which
    a box of mutable persons is not: type arguments are compared exactly. *)
Example recv_at_imm_on_mut_box :
  member_recv Mut [MutPerson] [] [QLit Imm] ROBoxQE = TClass RO 2 [ImmPerson].
Proof. reflexivity. Qed.

(* ------------------THE START AND THE RUN------------------*)

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

Ltac ty_local :=
  eapply ST_Local;
    [wfenv | solve [auto with ex] | reflexivity | reflexivity | reflexivity].
Ltac ty_seq := eapply ST_Seq; [wfenv | |].

Lemma find_get : FindMethodWithName CT 2 0 2 get_def.
Proof. eapply FOM_Here; reflexivity. Qed.

(** A call of [get] on a box with element type [A0] and head [q0]. *)
Ltac ty_call Tx0 Ty0 q0 A0 :=
  eapply ST_Call with (Tx := Tx0) (Ty := Ty0) (argtypes := [])
    (qy := q0) (C := 2) (Ts := [A0]) (D := 2) (Vs := [A0]) (mdef := get_def);
    [wfenv | reflexivity | reflexivity | reflexivity | reflexivity
    | apply find_get | apply si_refl | discriminate
    | constructor | constructor | reflexivity | constructor
    | cbn; refl_sub
    | cbn; apply qtype_qual; [cbn; lia | apply q_rd | apply Forall2_targ_sub_refl]
    | constructor
    | apply method_rs_as | reflexivity
    | constructor; [cbn; discriminate | constructor] | recv_known].

Lemma main_typed : stmt_typing CT Δ0 sΓ0 AbstractState main sΓ1.
Proof.
  unfold main, sΓ0, sΓ1.
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|]. cbn.
  (* p = new @Mut Person(this) *)
  ty_seq.
  { eapply ST_New with (Tx := MutPerson) (argtypes := [MutObject])
      (fds := [name_field]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutPerson | constructor | constructor
      | apply collect_Person | | ].
    - constructor; [|constructor]; cbn.
      split; [apply sub_Object_RO | cbn; intuition discriminate].
    - cbn. refl_sub. }
  (* i = new @Imm Person(this) *)
  ty_seq.
  { eapply ST_New with (Tx := ImmPerson) (argtypes := [MutObject])
      (fds := [name_field]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_ImmPerson | constructor | constructor
      | apply collect_Person | | ].
    - constructor; [|constructor]; cbn.
      split; [apply sub_Object_RO | cbn; intuition discriminate].
    - cbn. refl_sub. }
  (* b = new @Mut Box<@Mut Person>(p) *)
  ty_seq.
  { eapply ST_New with (Tx := MutBox) (argtypes := [MutPerson]) (fds := [item_field]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutBox | | | apply collect_Box | | ].
    - constructor; [|constructor]. cbn. intuition discriminate.
    - constructor; [|constructor]. cbn. split; [intuition discriminate|].
      intros m. apply sub_Person_RO.
    - constructor; [|constructor]. cbn. split; [refl_sub | cbn; intuition discriminate].
    - cbn. refl_sub. }
  (* c = new @Imm Box<@Imm Person>(i) *)
  ty_seq.
  { eapply ST_New with (Tx := ImmBox) (argtypes := [ImmPerson]) (fds := [item_field]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_ImmBox | | | apply collect_Box | | ].
    - constructor; [|constructor]. cbn. intuition discriminate.
    - constructor; [|constructor]. cbn. split; [intuition discriminate|].
      intros m. apply sub_Person_RO.
    - constructor; [|constructor]. cbn. split; [refl_sub | cbn; intuition discriminate].
    - cbn. refl_sub. }
  (* m = b.<@Mut>get() *)
  ty_seq.
  { ty_call MutPerson MutBox Mut MutPerson. }
  (* j = c.<@Imm>get() *)
  ty_call ImmPerson ImmBox Imm ImmPerson.
Qed.

(** The state after the run: [m] is the person stored in the mutable box and
    [j] the person stored in the immutable one. *)
Definition rΓ1 : r_env :=
  mkr_env [Iot 0; Iot 1; Iot 2; Iot 3; Iot 4; Iot 1; Iot 2] [] [] [].
Definition h1 : heap :=
  [ mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 1 []) [Iot 0];
    mkObj (mkruntime_type Imm_r 1 []) [Iot 0];
    mkObj (mkruntime_type Mut_r 2 [RClass Mut 1 []]) [Iot 1];
    mkObj (mkruntime_type Imm_r 2 [RClass Imm 1 []]) [Iot 2] ].

(** The interpreter computes this state. *)
Lemma main_run : run CT 1 rΓ0 h0 main = Some (FDone OK, rΓ1, h1).
Proof. reflexivity. Qed.

Lemma main_eval : eval_stmt CT rΓ0 h0 main OK rΓ1 h1.
Proof. eapply eval_fuel_erase; [apply run_sound; exact main_run | reflexivity]. Qed.

(** Type preservation: the final state is well formed at the final static
    environment, in which [m] has type [@Mut Person] and [j] has type
    [@Imm Person]. *)
Theorem polyrecv_preserved : wf_r_config CT Δ0 sΓ1 rΓ1 h1.
Proof.
  eapply preservation_pico;
    [exact main_eval | reflexivity | exact initial_config | exact main_typed].
Qed.

Print Assumptions polyrecv_preserved.
