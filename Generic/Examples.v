From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing Bigstep.

(** A concrete program exercising the generic definitions: a generic box, a
    call whose result type is the type argument, an upcast, and a narrowing
    cast to the mutability that a class declaration pins. *)

(* ------------------THE PROGRAM------------------*)

Definition get_name : method_name := 0.

(* The class type parameter E of Box *)
Definition tE : qualified_type := TVar TVSub ClassVar 0.

Definition ObjectDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 0; ctparams := [];
                     super := None |};
     body := {| fields := []; methods := [] |} |}.

Definition PersonDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 1; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := []; methods := [] |} |}.

(* E get(@RO Box<E> this) { E r; r = this.item; return r; } *)
Definition get_def : method_def :=
  {| msignature :=
       {| mscope := AbstractState;
          mtparams := [];
          mqparams := 0;
          mret := tE;
          mname := get_name;
          mreceiver := TClass RO 2 [tE];
          mparams := [] |};
     mbody :=
       {| mbody_stmt := SSeq (SLocal tE 1) (SVarAss 1 (EField 0 0));
          mreturn := 1 |} |}.

Definition BoxDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 2;
                     ctparams := [TClass RO 0 []];
                     super := Some (0, []) |};
     body := {| fields := [ {| assignability := Final; ftype := tE |} ];
                methods := [get_def] |} |}.

Definition MPersonDef : class_def :=
  {| signature := {| class_qualifier := Mut_c; cname := 3; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := []; methods := [] |} |}.

Definition CT : class_table := [ObjectDef; PersonDef; BoxDef; MPersonDef].

Definition MutPerson : qualified_type := TClass Mut 1 [].
Definition ImmBox : qualified_type := TClass Imm 2 [MutPerson].
Definition ROPerson : qualified_type := TClass RO 1 [].
Definition ROMPerson : qualified_type := TClass RO 3 [].
Definition MutMPerson : qualified_type := TClass Mut 3 [].

Definition main : stmt :=
  SSeq (SLocal MutPerson 1)
  (SSeq (SLocal ImmBox 2)
  (SSeq (SLocal MutPerson 3)
  (SSeq (SLocal ROPerson 4)
  (SSeq (SLocal ROMPerson 5)
  (SSeq (SLocal MutMPerson 6)
  (SSeq (SNew 1 Mut_c 1 [] [])
  (SSeq (SNew 2 Imm_c 2 [MutPerson] [1])
  (SSeq (SCall 3 get_name 2 [] [] [])
  (SSeq (SCast 4 ROPerson 3)
  (SSeq (SNew 5 Mut_c 3 [] [])
        (SCast 6 MutMPerson 5))))))))))).

Definition Δ0 : tv_env := mk_tv_env [] [] AbstractState 0.
Definition sΓ0 : s_env := [TClass Mut 0 []].
Definition sΓfinal : s_env :=
  [TClass Mut 0 []; MutPerson; ImmBox; MutPerson; ROPerson; ROMPerson; MutMPerson].

(* ------------------SMALL TACTICS------------------*)

Ltac qs := first [apply q_refl; discriminate | apply q_rd | apply q_bot].

(* A class type without type arguments *)
Ltac wf_plain :=
  eapply wfs_class;
    [reflexivity | right; cbn; qs | reflexivity | constructor | constructor].

Lemma sub_MutPerson_ROObject : forall Δ,
  qualified_type_subtype CT Δ (TClass Mut 1 []) (TClass RO 0 []).
Proof.
  intros Δ. eapply qtype_trans.
  - apply qtype_hier with (D := 0) (Vs := []).
    eapply si_step; [reflexivity|]. cbn. apply si_refl; try (cbn; lia).
  - apply qtype_qual; [cbn; lia | qs | constructor].
Qed.

Lemma wf_any_Object : forall Δ top q0, q0 <> Lost -> wf_stype CT Δ top (TClass q0 0 []).
Proof.
  intros. eapply wfs_class;
    [reflexivity | right | reflexivity | constructor | constructor].
  destruct q0; cbn; try qs; congruence.
Qed.

Lemma wf_MutPerson : forall Δ top, wf_stype CT Δ top MutPerson.
Proof. intros. unfold MutPerson. wf_plain. Qed.

Lemma wf_ROPerson : forall Δ, wf_stypeuse CT Δ ROPerson.
Proof. intros. unfold wf_stypeuse, ROPerson. wf_plain. Qed.

Lemma wf_ROMPerson : forall Δ, wf_stypeuse CT Δ ROMPerson.
Proof. intros. unfold wf_stypeuse, ROMPerson. wf_plain. Qed.

Lemma wf_MutMPerson : forall Δ, wf_stypeuse CT Δ MutMPerson.
Proof. intros. unfold wf_stypeuse, MutMPerson. wf_plain. Qed.

Lemma wf_ImmBox : forall Δ, wf_stypeuse CT Δ ImmBox.
Proof.
  intros. unfold wf_stypeuse, ImmBox.
  eapply wfs_class; [reflexivity | right; cbn; qs | reflexivity | |].
  - constructor; [apply wf_MutPerson | constructor].
  - constructor; [|constructor]. intros m. cbn. apply sub_MutPerson_ROObject.
Qed.

Lemma wf_MutPerson_use : forall Δ, wf_stypeuse CT Δ MutPerson.
Proof. intros. apply wf_MutPerson. Qed.

Lemma wf_MutObject_use : forall Δ, wf_stypeuse CT Δ (TClass Mut 0 []).
Proof. intros. apply wf_any_Object. discriminate. Qed.

Local Hint Resolve wf_MutPerson_use wf_ROPerson wf_ROMPerson wf_MutMPerson
  wf_ImmBox wf_MutObject_use : ex.

Ltac wfenv :=
  split; [cbn; lia |
          cbn; repeat (apply Forall_cons; [solve [auto with ex]|]); apply Forall_nil].

Ltac refl_sub :=
  apply qualified_type_subtype_refl_class; [cbn; lia | discriminate].

(* ------------------CLASS TABLE WELL-FORMEDNESS------------------*)

Definition ΔBox : tv_env := mk_tv_env [TClass RO 0 []] [] AbstractState 0.

Lemma wf_tE : forall top, wf_stype CT ΔBox top tE.
Proof.
  intros. eapply wfs_var; [reflexivity|]. right. discriminate.
Qed.

Lemma wf_ROBoxE : wf_stypeuse CT ΔBox (TClass RO 2 [tE]).
Proof.
  unfold wf_stypeuse.
  eapply wfs_class; [reflexivity | right; cbn; qs | reflexivity | |].
  - constructor; [apply wf_tE | constructor].
  - constructor; [|constructor]. intros m. cbn.
    apply qtype_var_bound. reflexivity.
Qed.

Lemma collect_Object : CollectFields CT 0 [].
Proof. eapply CF_Object; reflexivity. Qed.

Lemma collect_Person : CollectFields CT 1 [].
Proof.
  change (CollectFields CT 1
            (map (subst_field []) [] ++ Syntax.fields (body PersonDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma collect_MPerson : CollectFields CT 3 [].
Proof.
  change (CollectFields CT 3
            (map (subst_field []) [] ++ Syntax.fields (body MPersonDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma collect_Box :
  CollectFields CT 2 [ {| assignability := Final; ftype := tE |} ].
Proof.
  change (CollectFields CT 2
            (map (subst_field []) [] ++ Syntax.fields (body BoxDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma no_method_in_Object : forall m D mdef,
  ~ FindMethodWithName CT 0 m D mdef.
Proof.
  intros m D mdef H. inversion H; subst.
  - cbn in Hfind. injection Hfind as <-. cbn in Hget_method. discriminate.
  - cbn in Hfind. injection Hfind as <-. cbn in Hsuper. discriminate.
Qed.

Lemma wf_get : wf_method CT 2 get_def.
Proof.
  unfold wf_method. cbn.
  assert (Hwf1 : wf_senv CT ΔBox [TClass RO 2 [tE]]).
  { split; [cbn; lia|]. constructor; [apply wf_ROBoxE | constructor]. }
  assert (Hwf2 : wf_senv CT ΔBox [TClass RO 2 [tE]; tE]).
  { split; [cbn; lia|].
    constructor; [apply wf_ROBoxE|]. constructor; [apply wf_tE | constructor]. }
  split; [apply receiver_plain_ok; left; exists RO; reflexivity|].
  split; [constructor|].
  split; [apply wf_tE|].
  split.
  { exists [TClass RO 2 [tE]; tE], tE. split; [|split].
    - eapply ST_Seq; [exact Hwf1 | |].
      + eapply ST_Local; [exact Hwf1 | apply wf_tE | | reflexivity |]; reflexivity.
      + eapply ST_VarAss with (Tx := tE);
          [exact Hwf2 | | discriminate | reflexivity | ].
        * eapply ET_Field with (fDef := {| assignability := Final; ftype := tE |});
            [exact Hwf2 | reflexivity | reflexivity |].
          eapply FL_Found; [apply collect_Box | reflexivity].
        * cbn. apply qtype_var_refl.
    - reflexivity.
    - apply qtype_var_refl. }
  split.
  { intros def parent Ss D mdef_parent Vs Hfind Hsuper Hfm _.
    cbn in Hfind. injection Hfind as <-. cbn in Hsuper.
    injection Hsuper as <- <-.
    exfalso. eapply no_method_in_Object; eauto. }
  intros [H | H]; discriminate.
Qed.

Lemma example_ct_wf : wf_class_table CT.
Proof.
  unfold wf_class_table. split; [|split; [|split]].
  - constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + apply WFObjectDef; reflexivity.
    + eapply WFOtherDef with (superC := 0) (Ss := []);
        try reflexivity; cbn; try solve [constructor]; auto.
      * apply wf_any_Object. discriminate.
    + eapply WFOtherDef with (superC := 0) (Ss := []);
        try reflexivity; cbn; try solve [constructor]; auto.
      * constructor; [|constructor]. split; [exact I|].
        apply wf_any_Object. discriminate.
      * apply wf_any_Object. discriminate.
      * constructor; [|constructor]. apply wf_tE.
      * constructor; [|constructor]. apply wf_get.
      * constructor; [intros []|constructor].
    + eapply WFOtherDef with (superC := 0) (Ss := []);
        try reflexivity; cbn; try solve [constructor]; auto.
      * apply wf_any_Object. discriminate.
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
    [wfenv | solve [auto with ex] | reflexivity | reflexivity | reflexivity].

Ltac ty_seq := eapply ST_Seq; [wfenv | |].

Lemma example_main_typed_exact :
  stmt_typing CT Δ0 sΓ0 AbstractState main sΓfinal.
Proof.
  unfold main, sΓ0, sΓfinal.
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  cbn.
  (* p = new @Mut Person() *)
  ty_seq.
  { eapply ST_New with (Tx := MutPerson) (argtypes := []) (fds := []);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutPerson | constructor | constructor
      | apply collect_Person | constructor | ].
    cbn. refl_sub. }
  (* b = new @Imm Box<@Mut Person>(p) *)
  ty_seq.
  { eapply ST_New with (Tx := ImmBox) (argtypes := [MutPerson]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_ImmBox | | | apply collect_Box | | ].
    - constructor; [|constructor]. cbn. intuition discriminate.
    - constructor; [|constructor]. cbn. split; [intuition discriminate|].
      intros m. apply sub_MutPerson_ROObject.
    - constructor; [|constructor]. cbn. split.
      + refl_sub.
      + cbn. intuition discriminate.
    - cbn. refl_sub. }
  (* q = b.get(): the result type is the type argument itself *)
  ty_seq.
  { eapply ST_Call with (Tx := MutPerson) (Ty := ImmBox) (argtypes := [])
      (qy := Imm) (C := 2) (Ts := [MutPerson]) (D := 2) (Vs := [MutPerson])
      (mdef := get_def);
      [wfenv | reflexivity | reflexivity | reflexivity | reflexivity
      | | | discriminate | constructor | constructor | reflexivity
      | constructor | | | constructor | apply method_subtyping_refl | reflexivity | constructor | recv_known].
    - eapply FOM_Here; reflexivity.
    - apply si_refl; try (cbn; lia).
    - cbn. refl_sub.
    - cbn. split.
      + apply qtype_qual; [cbn; lia | qs | apply Forall2_targ_sub_refl].
      + cbn. intuition discriminate. }
  (* o = (@RO Person) q *)
  ty_seq.
  { eapply ST_Cast with (Tx := ROPerson) (Ty := MutPerson);
      [wfenv | reflexivity | reflexivity | discriminate | apply wf_ROPerson
      | | | exact I].
    - left. apply qtype_qual; [cbn; lia | qs | constructor].
    - refl_sub. }
  (* r = new @Mut MPerson() *)
  ty_seq.
  { eapply ST_New with (Tx := ROMPerson) (argtypes := []) (fds := []);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutMPerson | constructor | constructor
      | apply collect_MPerson | constructor | ].
    cbn. apply qtype_qual; [cbn; lia | qs | constructor]. }
  (* m = (@Mut MPerson) r: narrowing to the pinned mutability *)
  eapply ST_Cast with (Tx := MutMPerson) (Ty := ROMPerson);
    [wfenv | reflexivity | reflexivity | discriminate | apply wf_MutMPerson
    | | | exact I].
  - right. cbn. repeat split; auto; try qs; try discriminate.
    exists MPersonDef. split; reflexivity.
  - refl_sub.
Qed.

Lemma example_main_typed :
  exists sΓ', stmt_typing CT (mk_tv_env [] [] AbstractState 0) [TClass Mut 0 []] AbstractState main sΓ'.
Proof. exists sΓfinal. apply example_main_typed_exact. Qed.

(* ------------------NEGATIVE CHECKS------------------*)

(** Person is declared @RDM, so a readonly Person cannot be narrowed to
    mutable or to immutable. *)
Lemma person_not_narrowable_mut :
  ~ cast_narrowing_ok CT (TClass RO 1 []) (TClass Mut 1 []).
Proof.
  cbn. intros (_ & _ & _ & _ & _ & def & Hfind & Hq).
  injection Hfind as <-. discriminate.
Qed.

Lemma person_not_narrowable_imm :
  ~ cast_narrowing_ok CT (TClass RO 1 []) (TClass Imm 1 []).
Proof.
  cbn. intros (_ & _ & _ & _ & _ & def & Hfind & Hq).
  injection Hfind as <-. discriminate.
Qed.

(** Every supertype of a readonly class type is a readonly class type. *)
Lemma ro_class_supertype : forall CT0 Δ S T,
  qualified_type_subtype CT0 Δ S T ->
  (exists C Ts, S = TClass RO C Ts) ->
  exists D Vs, T = TClass RO D Vs.
Proof.
  intros CT0 Δ S T H.
  induction H; intros (C0 & Ts0 & Heq); try discriminate.
  - injection Heq as -> -> ->. inversion Hqsub; subst; eauto.
  - injection Heq as -> -> ->. eauto.
  - apply IHqualified_type_subtype2. apply IHqualified_type_subtype1. eauto.
Qed.

(** Casting a readonly Person to an immutable (or mutable) Person is rejected
    in every environment and every mode. *)
Lemma bad_cast_untypable : forall Δ sΓ mt x y qt sΓ',
  static_getType sΓ y = Some (TClass RO 1 []) ->
  qt = Mut \/ qt = Imm ->
  ~ stmt_typing CT Δ sΓ mt (SCast x (TClass qt 1 []) y) sΓ'.
Proof.
  intros Δ sΓ mt x y qt sΓ' Hy Hqt Htyp.
  inversion Htyp; subst.
  rewrite Hy in Hget_y. injection Hget_y as <-.
  destruct Hsource as [Hup | Hnarrow].
  - apply ro_class_supertype in Hup; [|eauto].
    destruct Hup as (D & Vs & Heq). injection Heq as -> _ _.
    destruct Hqt; discriminate.
  - destruct Hqt; subst qt.
    + exact (person_not_narrowable_mut Hnarrow).
    + exact (person_not_narrowable_imm Hnarrow).
Qed.

(* ------------------EVALUATION------------------*)

Definition rΓ0 : r_env := mkr_env [Iot 0] [] [] [].
Definition h0 : heap := [mkObj (mkruntime_type Mut_r 0 []) []].

Definition rΓfinal : r_env :=
  mkr_env [Iot 0; Iot 1; Iot 2; Iot 1; Iot 1; Iot 3; Iot 3] [] [] [].

(** The Box object (location 2) is immutable and stores the runtime type
    argument [@Mut Person]; its field holds the Person at location 1. *)
Definition hfinal : heap :=
  [ mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 1 []) [];
    mkObj (mkruntime_type Imm_r 2 [RClass Mut 1 []]) [Iot 1];
    mkObj (mkruntime_type Mut_r 3 []) [] ].

Ltac ev_local := eapply SBS_Seq; [apply SBS_Local; reflexivity|]; cbn.

Lemma example_main_eval_exact :
  eval_stmt CT rΓ0 h0 main OK rΓfinal hfinal.
Proof.
  unfold main, rΓ0, h0.
  ev_local. ev_local. ev_local. ev_local. ev_local. ev_local.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq.
  { eapply SBS_Call with (mdef := get_def) (D := 2).
    - reflexivity.
    - reflexivity.
    - eapply FOM_Here; reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold callee_env. do 4 eexists.
      split; [reflexivity|]. split; [reflexivity|]. split; [split; reflexivity|].
      split; [apply rsi_refl; try (cbn; lia) | reflexivity].
    - cbn. eapply SBS_Seq; [apply SBS_Local; reflexivity|]. cbn.
      eapply SBS_Assign; [reflexivity|].
      eapply EBS_Field; reflexivity.
    - reflexivity.
    - reflexivity. }
  cbn.
  eapply SBS_Seq; [eapply SBS_Cast; reflexivity|]. cbn.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  match goal with
  | |- eval_stmt _ ?r ?h _ _ _ _ =>
      change (eval_stmt CT r h (SCast 6 MutMPerson 5) OK
                (set_vars r (update 6 (Iot 3) (vars r))) h)
  end.
  eapply SBS_Cast; reflexivity.
Qed.

Lemma example_main_eval :
  exists rΓ' h',
    eval_stmt CT (mkr_env [Iot 0] [] [] []) [mkObj (mkruntime_type Mut_r 0 []) []]
      main OK rΓ' h'.
Proof. exists rΓfinal, hfinal. apply example_main_eval_exact. Qed.
