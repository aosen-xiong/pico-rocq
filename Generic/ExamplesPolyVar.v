From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation MutationSafety Progress Interp.

(** A qualifier parameter on a use of a type variable.

    class 0: @RDM class Object {}
    class 1: @RDM class Person extends Object {
       @RDA @RO Object name;            // field 0
    }
    class 2: @RDM class Util extends Object {
       // returns its argument with the mutability the caller chose
       @RS <Q, X extends @RO Person> [Q]X id(@RO Util this, [Q]X x) { return x; }
       // reads through the argument, which the body sees as readonly
       @RS <Q, X extends @RO Person> @RO Object peek(@RO Util this, [Q]X x) {
           @RO Object r;  r = x.name;  return r;
       }
    }

    main (this : @Mut Object):
       @Mut Person m;  @Imm Person i;  @Mut Util u;
       @Mut Person m2; @Imm Person i2; @RO Object r;
       m = new @Mut Person(this);
       i = new @Imm Person(this);
       u = new @Mut Util();
       m2 = u.<@Mut; @RO Person>id(m);
       i2 = u.<@Imm; @RO Person>id(i);
       r  = u.<@Imm; @RO Person>peek(i);

    [[Q]X] is the use of the type variable [X] under the qualifier parameter
    [Q].  A call replaces [Q] by its qualifier argument and [X] by its type
    argument, so the first call types [id] at [@Mut Person] and the second at
    [@Imm Person]. *)

(* ------------------THE PROGRAM------------------*)

Definition ROObject : qualified_type := TClass RO 0 [].
Definition MutObject : qualified_type := TClass Mut 0 [].
Definition ROPerson : qualified_type := TClass RO 1 [].
Definition MutPerson : qualified_type := TClass Mut 1 [].
Definition ImmPerson : qualified_type := TClass Imm 1 [].
Definition ROUtil : qualified_type := TClass RO 2 [].
Definition MutUtil : qualified_type := TClass Mut 2 [].
(* [Q]X: the method's type variable under its qualifier parameter *)
Definition tQX : qualified_type := TVar (TVPoly 0) MethodVar 0.

Definition name_field : field_def := {| assignability := RDA; ftype := ROObject |}.

Definition id_def : method_def :=
  {| msignature := {| mscope := ReadonlyState; mtparams := [ROPerson]; mqparams := 1;
                      mret := tQX; mname := 0;
                      mreceiver := ROUtil; mparams := [tQX] |};
     mbody := {| mbody_stmt := SSkip; mreturn := 1 |} |}.

Definition peek_body : stmt := SSeq (SLocal ROObject 2) (SVarAss 2 (EField 1 0)).

Definition peek_def : method_def :=
  {| msignature := {| mscope := ReadonlyState; mtparams := [ROPerson]; mqparams := 1;
                      mret := ROObject; mname := 1;
                      mreceiver := ROUtil; mparams := [tQX] |};
     mbody := {| mbody_stmt := peek_body; mreturn := 2 |} |}.

Definition ObjectDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 0; ctparams := [];
                     super := None |};
     body := {| fields := []; methods := [] |} |}.
Definition PersonDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 1; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := [name_field]; methods := [] |} |}.
Definition UtilDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 2; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := []; methods := [id_def; peek_def] |} |}.
Definition CT : class_table := [ObjectDef; PersonDef; UtilDef].

Definition Δ0 : tv_env := mk_tv_env [] [] AbstractState 0.
Definition sΓ0 : s_env := [MutObject].
Definition sΓ1 : s_env :=
  [MutObject; MutPerson; ImmPerson; MutUtil; MutPerson; ImmPerson; ROObject].

Definition main : stmt :=
  SSeq (SLocal MutPerson 1)
  (SSeq (SLocal ImmPerson 2)
  (SSeq (SLocal MutUtil 3)
  (SSeq (SLocal MutPerson 4)
  (SSeq (SLocal ImmPerson 5)
  (SSeq (SLocal ROObject 6)
  (SSeq (SNew 1 Mut_c 1 [] [0])
  (SSeq (SNew 2 Imm_c 1 [] [0])
  (SSeq (SNew 3 Mut_c 2 [] [])
  (SSeq (SCall 4 0 3 [ROPerson] [QLit Mut] [1])
  (SSeq (SCall 5 0 3 [ROPerson] [QLit Imm] [2])
        (SCall 6 1 3 [ROPerson] [QLit Imm] [2]))))))))))).

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
Lemma wf_MutPerson : forall Δ, wf_stypeuse CT Δ MutPerson.
Proof. intros. unfold wf_stypeuse, MutPerson. wf_plain. Qed.
Lemma wf_ImmPerson : forall Δ, wf_stypeuse CT Δ ImmPerson.
Proof. intros. unfold wf_stypeuse, ImmPerson. wf_plain. Qed.
Lemma wf_ROUtil : forall Δ, wf_stypeuse CT Δ ROUtil.
Proof. intros. unfold wf_stypeuse, ROUtil. wf_plain. Qed.
Lemma wf_MutUtil : forall Δ, wf_stypeuse CT Δ MutUtil.
Proof. intros. unfold wf_stypeuse, MutUtil. wf_plain. Qed.

Definition ΔM : tv_env := method_tv_env CT 2 (msignature id_def).

(** The use [[Q]X] is well formed where [Q] and [X] are in scope. *)
Lemma wf_tQX : wf_stypeuse CT ΔM tQX.
Proof. unfold wf_stypeuse, tQX. eapply wfs_var; [reflexivity | cbn; lia]. Qed.

(** It is not well formed in a field or in main, where no qualifier
    parameter is in scope. *)
Lemma tQX_needs_param : forall o n, ~ wf_stypeuse CT Δ0 (TVar (TVPoly 0) o n).
Proof.
  intros o n H. inversion H; subst. cbn in Huse. lia.
Qed.

Local Hint Resolve wf_ROObject wf_MutObject wf_ROPerson wf_MutPerson
  wf_ImmPerson wf_ROUtil wf_MutUtil wf_tQX : ex.

Ltac wfenv :=
  split; [cbn; lia |
          cbn; repeat (apply Forall_cons; [solve [auto with ex]|]); apply Forall_nil].

Lemma sub_to_ROObject : forall Δ q0 C,
  C = 1 \/ C = 2 -> qualified_type_subtype CT Δ (TClass q0 C []) ROObject.
Proof.
  intros Δ q0 C HC. eapply qtype_trans.
  - apply qtype_hier with (D := 0) (Vs := []).
    eapply si_step; [destruct HC; subst; reflexivity|]. cbn. apply si_refl.
  - apply qtype_qual; [cbn; lia | apply q_rd | constructor].
Qed.

Lemma sub_Object_RO : forall Δ q0, qualified_type_subtype CT Δ (TClass q0 0 []) ROObject.
Proof. intros. apply qtype_qual; [cbn; lia | apply q_rd | constructor]. Qed.

(* ------------------FIELDS AND METHODS------------------*)

Lemma collect_Object : CollectFields CT 0 [].
Proof. eapply CF_Object; reflexivity. Qed.
Lemma collect_Person : CollectFields CT 1 [name_field].
Proof.
  change (CollectFields CT 1 (map (subst_field []) [] ++ Syntax.fields (body PersonDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.
Lemma collect_Util : CollectFields CT 2 [].
Proof.
  change (CollectFields CT 2 (map (subst_field []) [] ++ Syntax.fields (body UtilDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma no_method_in_Object : forall m D mdef, ~ FindMethodWithName CT 0 m D mdef.
Proof.
  intros m D mdef H. inversion H; subst.
  - cbn in Hfind. injection Hfind as <-. cbn in Hget_method. discriminate.
  - cbn in Hfind. injection Hfind as <-. cbn in Hsuper. discriminate.
Qed.

(** Inside the method, [[Q]X] is viewed as a readonly [Person]: the view that
    is valid whichever qualifier [Q] stands for. *)
Example tQX_view : ubound ΔM tQX = Some ROPerson.
Proof. reflexivity. Qed.

(** So the body cannot write through it: the [name] field is not assignable
    through a readonly receiver in readonly-state code. *)
Example tQX_not_writable : vpa_a ReadonlyState RO (assignability name_field) = Final.
Proof. reflexivity. Qed.

(** [[Q]X] reaches no mutable position, so it may be a parameter type of a
    readonly-state method. *)
Lemma tQX_no_mut : no_mut ΔM tQX.
Proof. unfold tQX. eapply nm_pvar; [reflexivity | constructor]. Qed.

Lemma wf_id : wf_method CT 2 id_def.
Proof.
  unfold wf_method. cbn. fold ΔM.
  split; [apply receiver_plain_ok; left; exists RO; reflexivity|].
  split.
  { constructor; [|constructor]. split; [exact I|]. split; [apply wf_ROPerson|].
    intros _. apply nm_class; [discriminate | constructor]. }
  split; [apply wf_tQX|].
  split.
  { exists [ROUtil; tQX], tQX. split; [|split].
    - apply ST_Skip. wfenv.
    - reflexivity.
    - apply qtype_pvar_refl. }
  split.
  { intros def parent Ss D mdef_parent Vs Hfind Hsuper Hfm _.
    cbn in Hfind. injection Hfind as <-. cbn in Hsuper. injection Hsuper as <- <-.
    exfalso. eapply no_method_in_Object; eauto. }
  intros _. split.
  - apply nm_class; [discriminate | constructor].
  - constructor; [apply tQX_no_mut | constructor].
Qed.

Lemma peek_body_typed :
  stmt_typing CT ΔM [ROUtil; tQX] ReadonlyState peek_body [ROUtil; tQX; ROObject].
Proof.
  unfold peek_body.
  eapply ST_Seq; [wfenv | |].
  { eapply ST_Local; [wfenv | apply wf_ROObject | reflexivity | reflexivity | reflexivity]. }
  eapply ST_VarAss with (Tx := ROObject) (Te := ROObject);
    [wfenv | | discriminate | reflexivity | apply sub_Object_RO].
  change ROObject with (member_type ReadonlyState RO [] [] [] (ftype name_field)).
  eapply ET_Field with (T := tQX) (C := 1); [wfenv | reflexivity | reflexivity |].
  eapply FL_Found; [apply collect_Person | reflexivity].
Qed.

Lemma wf_peek : wf_method CT 2 peek_def.
Proof.
  unfold wf_method. cbn.
  change (method_tv_env CT 2 (msignature peek_def)) with ΔM.
  split; [apply receiver_plain_ok; left; exists RO; reflexivity|].
  split.
  { constructor; [|constructor]. split; [exact I|]. split; [apply wf_ROPerson|].
    intros _. apply nm_class; [discriminate | constructor]. }
  split; [apply wf_ROObject|].
  split.
  { exists [ROUtil; tQX; ROObject], ROObject. split; [|split].
    - exact peek_body_typed.
    - reflexivity.
    - apply sub_Object_RO. }
  split.
  { intros def parent Ss D mdef_parent Vs Hfind Hsuper Hfm _.
    cbn in Hfind. injection Hfind as <-. cbn in Hsuper. injection Hsuper as <- <-.
    exfalso. eapply no_method_in_Object; eauto. }
  intros _. split.
  - apply nm_class; [discriminate | constructor].
  - constructor; [apply tQX_no_mut | constructor].
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
      * unfold wf_stypeuse. wf_plain.
      * constructor; [apply wf_id | constructor; [apply wf_peek | constructor]].
      * constructor; [intros [H | []]; discriminate | constructor; [intros [] | constructor]].
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

Lemma find_id : FindMethodWithName CT 2 0 2 id_def.
Proof. eapply FOM_Here; reflexivity. Qed.
Lemma find_peek : FindMethodWithName CT 2 1 2 peek_def.
Proof. eapply FOM_Here; reflexivity. Qed.

(** A call of [id] or [peek] on [u] with the type argument [@RO Person]. *)
Ltac ty_call Tx0 A0 md fm :=
  eapply ST_Call with (Tx := Tx0) (Ty := MutUtil) (argtypes := [A0])
    (qy := Mut) (C := 2) (Ts := []) (D := 2) (Vs := []) (mdef := md);
    [wfenv | reflexivity | reflexivity | reflexivity | reflexivity
    | apply fm | apply si_refl | discriminate
    | constructor; [apply wf_ROPerson | constructor]
    | constructor; [cbn; split; [discriminate | exact I] | constructor]
    | reflexivity
    | constructor; [|constructor]; cbn;
      (split; [split; [discriminate | exact I] | intros mm; refl_sub])
    | | | | apply method_rs_as | reflexivity
    | constructor; [cbn; discriminate | constructor] | recv_known].

Lemma main_typed : stmt_typing CT Δ0 sΓ0 AbstractState main sΓ1.
Proof.
  unfold main, sΓ0, sΓ1.
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|]. cbn.
  (* m = new @Mut Person(this) *)
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
  (* u = new @Mut Util() *)
  ty_seq.
  { eapply ST_New with (Tx := MutUtil) (argtypes := []) (fds := []);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutUtil | constructor | constructor
      | apply collect_Util | constructor | ].
    cbn. refl_sub. }
  (* m2 = u.<@Mut; @RO Person>id(m): [Q]X is @Mut Person *)
  ty_seq.
  { ty_call MutPerson MutPerson id_def find_id.
    - cbn. refl_sub.
    - cbn. split; [apply qtype_qual; [cbn; lia | apply q_rd | constructor] | cbn; discriminate].
    - constructor; [|constructor]; cbn.
      split; [refl_sub | cbn; intuition discriminate]. }
  (* i2 = u.<@Imm; @RO Person>id(i): [Q]X is @Imm Person *)
  ty_seq.
  { ty_call ImmPerson ImmPerson id_def find_id.
    - cbn. refl_sub.
    - cbn. split; [apply qtype_qual; [cbn; lia | apply q_rd | constructor] | cbn; discriminate].
    - constructor; [|constructor]; cbn.
      split; [refl_sub | cbn; intuition discriminate]. }
  (* r = u.<@Imm; @RO Person>peek(i) *)
  ty_call ROObject ImmPerson peek_def find_peek.
  - cbn. apply sub_Object_RO.
  - cbn. split; [apply qtype_qual; [cbn; lia | apply q_rd | constructor] | cbn; discriminate].
  - constructor; [|constructor]; cbn.
    split; [refl_sub | cbn; intuition discriminate].
Qed.

(** The state after the run: the two results are the two arguments, and [r]
    is the name read through the immutable person. *)
Definition rΓ1 : r_env :=
  mkr_env [Iot 0; Iot 1; Iot 2; Iot 3; Iot 1; Iot 2; Iot 0] [] [] [].
Definition h1 : heap :=
  [ mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 1 []) [Iot 0];
    mkObj (mkruntime_type Imm_r 1 []) [Iot 0];
    mkObj (mkruntime_type Mut_r 2 []) [] ].

(** The interpreter computes this state. *)
Lemma main_run : run CT 1 rΓ0 h0 main = Some (FDone OK, rΓ1, h1).
Proof. reflexivity. Qed.

Lemma main_eval : eval_stmt CT rΓ0 h0 main OK rΓ1 h1.
Proof. eapply eval_fuel_erase; [apply run_sound; exact main_run | reflexivity]. Qed.

(** Type preservation: the final state is well formed at the final static
    environment, in which [m2] has type [@Mut Person] and [i2] has type
    [@Imm Person]. *)
Theorem polyvar_preserved : wf_r_config CT Δ0 sΓ1 rΓ1 h1.
Proof.
  eapply preservation_pico;
    [exact main_eval | reflexivity | exact initial_config | exact main_typed].
Qed.

Print Assumptions polyvar_preserved.
