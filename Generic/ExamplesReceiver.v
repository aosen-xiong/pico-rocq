From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing.

(** A declared receiver that requalifies a type parameter of its class.

    class 0: @RDM class Object {}
    class 1: @RDM class Person extends Object { @RDA @RO Object age; }
    class 2: @RDM class ROBox<E extends @RO Person> extends Object {
       @RDA E element;
       @AS @RO Object ageUp(@RO ROBox<@Mut E> this, @RO Object v) {
           @Mut E p;          // var 2
           p = this.element;
           p.age = v;
           return v;
       }
    }

    [ageUp] may be called only on a box whose element type is mutable: its
    body writes the element.  The call is accepted on a
    [@RO ROBox<@Mut Person>] and rejected on a [@RO ROBox<@Imm Person>]. *)

Definition ROObject : qualified_type := TClass RO 0 [].
Definition ROPerson : qualified_type := TClass RO 1 [].
Definition MutPerson : qualified_type := TClass Mut 1 [].
Definition ImmPerson : qualified_type := TClass Imm 1 [].
Definition tE : qualified_type := TVar TVSub ClassVar 0.
Definition MutE : qualified_type := TVar (TVQual Mut) ClassVar 0.
Definition ROBoxMutE : qualified_type := TClass RO 2 [MutE].

Definition ageUp_def : method_def :=
  {| msignature := {| mscope := AbstractState; mtparams := []; mqparams := 0;
                      mret := ROObject; mname := 0;
                      mreceiver := ROBoxMutE; mparams := [ROObject] |};
     mbody := {| mbody_stmt :=
                   SSeq (SLocal MutE 2)
                     (SSeq (SVarAss 2 (EField 0 0)) (SFldWrite 2 0 1));
                 mreturn := 1 |} |}.

Definition ObjectDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 0; ctparams := [];
                     super := None |};
     body := {| fields := []; methods := [] |} |}.
Definition PersonDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 1; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := [ {| assignability := RDA; ftype := ROObject |} ];
                methods := [] |} |}.
Definition ROBoxDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 2; ctparams := [ROPerson];
                     super := Some (0, []) |};
     body := {| fields := [ {| assignability := RDA; ftype := tE |} ];
                methods := [ageUp_def] |} |}.
(** class 3: @RDM class RSBox<E extends @RO Person> extends Object {
       @RS @RO Object peek(@RDM RSBox<@RDM E> this, @RO Object v) { return v; }
    }
    A readonly-state method may requalify a receiver argument too, here as
    receiver-dependent; only a mutable requalification is excluded. *)
Definition ROE : qualified_type := TVar (TVQual RDM) ClassVar 0.
Definition RSBoxROE : qualified_type := TClass RDM 3 [ROE].
Definition peek_def : method_def :=
  {| msignature := {| mscope := ReadonlyState; mtparams := []; mqparams := 0;
                      mret := ROObject; mname := 0;
                      mreceiver := RSBoxROE; mparams := [ROObject] |};
     mbody := {| mbody_stmt := SSkip; mreturn := 1 |} |}.
Definition RSBoxDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 3; ctparams := [ROPerson];
                     super := Some (0, []) |};
     body := {| fields := []; methods := [peek_def] |} |}.

Definition CT : class_table := [ObjectDef; PersonDef; ROBoxDef; RSBoxDef].

Definition ΔBox : tv_env := mk_tv_env [ROPerson] [] AbstractState 0.

Ltac qs := first [apply q_refl; discriminate | apply q_rd | apply q_bot].
Ltac wf_plain :=
  eapply wfs_class;
    [reflexivity | right; cbn; qs | reflexivity | constructor | constructor].

Lemma sub_person_object : forall Δ q0,
  qualified_type_subtype CT Δ (TClass q0 1 []) ROObject.
Proof.
  intros Δ q0. eapply qtype_trans.
  - apply qtype_hier. eapply si_step; [reflexivity | apply si_refl].
  - apply qtype_qual; [cbn; lia | apply q_rd | constructor].
Qed.

Lemma sub_MutE_ROPerson : forall m,
  qualified_type_subtype CT (with_mode ΔBox m) MutE ROPerson.
Proof.
  intros m. eapply qtype_trans.
  - eapply qtype_qvar_bound. apply qtype_var_bound. reflexivity.
  - apply qtype_qual; [cbn; lia | apply q_rd | constructor].
Qed.

Lemma wf_MutE : forall top, wf_stype CT ΔBox top MutE.
Proof. intros top. eapply wfs_var; [reflexivity | right; discriminate]. Qed.

Lemma wf_ROBoxMutE : wf_stypeuse CT ΔBox ROBoxMutE.
Proof.
  eapply wfs_class; [reflexivity | right; cbn; apply q_rd | reflexivity | |].
  - constructor; [apply wf_MutE | constructor].
  - constructor; [|constructor]. intros m. cbn. apply sub_MutE_ROPerson.
Qed.

Lemma wf_ROObject : forall Δ, wf_stypeuse CT Δ ROObject.
Proof. intros Δ. unfold wf_stypeuse, ROObject. wf_plain. Qed.

Lemma collect_Person : CollectFields CT 1 [ {| assignability := RDA; ftype := ROObject |} ].
Proof.
  change [ {| assignability := RDA; ftype := ROObject |} ]
    with (map (subst_field []) [] ++ [ {| assignability := RDA; ftype := ROObject |} ]).
  eapply CF_Inherit; [reflexivity | reflexivity | | reflexivity].
  eapply CF_Object; reflexivity.
Qed.

Lemma collect_ROBox : CollectFields CT 2 [ {| assignability := RDA; ftype := tE |} ].
Proof.
  change [ {| assignability := RDA; ftype := tE |} ]
    with (map (subst_field []) [] ++ [ {| assignability := RDA; ftype := tE |} ]).
  eapply CF_Inherit; [reflexivity | reflexivity | | reflexivity].
  eapply CF_Object; reflexivity.
Qed.

(** The method is well formed: its receiver requalifies [E], and its body
    writes the element through the mutable view the receiver promises. *)
Lemma wf_ageUp : wf_method CT 2 ageUp_def.
Proof.
  unfold wf_method. cbn.
  change (method_tv_env CT 2 (msignature ageUp_def)) with ΔBox.
  assert (Hwf1 : wf_senv CT ΔBox [ROBoxMutE; ROObject]).
  { split; [cbn; lia|].
    constructor; [apply wf_ROBoxMutE|]. constructor; [apply wf_ROObject | constructor]. }
  assert (Hwf2 : wf_senv CT ΔBox [ROBoxMutE; ROObject; MutE]).
  { split; [cbn; lia|].
    constructor; [apply wf_ROBoxMutE|]. constructor; [apply wf_ROObject|].
    constructor; [apply wf_MutE | constructor]. }
  split.
  { split.
    - exists [MutE]. split.
      + split; [reflexivity|]. intros [|i] T H; [|destruct i; discriminate].
        inversion H. eexists. reflexivity.
      + left. exists RO. reflexivity.
    - intros [H | H]; discriminate. }
  split; [constructor|].
  split; [apply wf_ROObject|].
  split.
  { exists [ROBoxMutE; ROObject; MutE], ROObject. split; [|split].
    - eapply ST_Seq; [exact Hwf1 | |].
      + eapply ST_Local; [exact Hwf1 | apply wf_MutE | | reflexivity |]; reflexivity.
      + eapply ST_Seq; [exact Hwf2 | |].
        * eapply ST_VarAss with (Tx := MutE) (Te := MutE);
            [exact Hwf2 | | discriminate | reflexivity | apply qtype_qvar_qual; apply q_refl].
          change MutE with (member_type AbstractState RO [MutE] [] [] (ftype {| assignability := RDA; ftype := tE |})).
          eapply ET_Field with (T := ROBoxMutE) (C := 2);
            [exact Hwf2 | reflexivity | reflexivity |].
          eapply FL_Found; [apply collect_ROBox | reflexivity].
        * eapply ST_FldWrite with (Tx := MutE) (Ty := ROObject) (qx := Mut)
            (C := 1) (Ts := [])
            (fieldT := {| assignability := RDA; ftype := ROObject |});
            [exact Hwf2 | reflexivity | reflexivity | reflexivity | | | reflexivity].
          -- eapply FL_Found; [apply collect_Person | reflexivity].
          -- split; [|cbn; intuition discriminate].
             cbn. apply qtype_qual; [cbn; lia | apply q_refl | constructor].
    - reflexivity.
    - apply qtype_qual; [cbn; lia | apply q_refl | constructor]. }
  split.
  { intros def parent Ss D mdef_parent Vs Hfind Hsuper Hfm _.
    cbn in Hfind. injection Hfind as <-. cbn in Hsuper. injection Hsuper as <- <-.
    exfalso.
    inversion Hfm as [? ? ? ? ? ? Hf Ho Hg | ? ? ? ? ? ? ? ? ? Hf Ho Hn Hs Hp];
      subst; cbn in Hf; inversion Hf; subst; cbn in *; discriminate. }
  intros [H | H]; discriminate.
Qed.

(** The readonly-state method with a requalified receiver argument is well
    formed. *)
Lemma wf_peek : wf_method CT 3 peek_def.
Proof.
  unfold wf_method. cbn.
  set (ΔR := method_tv_env CT 3 (msignature peek_def)).
  assert (HwfE : wf_stype CT ΔR false ROE).
  { eapply wfs_var; [reflexivity | right; discriminate]. }
  assert (Hsub : forall m, qualified_type_subtype CT (with_mode ΔR m) ROE ROPerson).
  { intros m. eapply qtype_trans.
    - eapply qtype_qvar_bound. apply qtype_var_bound. reflexivity.
    - apply qtype_qual; [cbn; lia | apply q_rd | constructor]. }
  assert (HwfR : wf_stypeuse CT ΔR RSBoxROE).
  { eapply wfs_class; [reflexivity | right; cbn; apply q_refl | reflexivity | |].
    - constructor; [exact HwfE | constructor].
    - constructor; [|constructor]. intros m. cbn. apply Hsub. }
  assert (HnmP : no_mut ΔR ROPerson) by (apply nm_class; [discriminate | constructor]).
  split.
  { split.
    - exists [ROE]. split.
      + split; [reflexivity|]. intros [|i] T H; [|destruct i; discriminate].
        inversion H. eexists. reflexivity.
      + left. exists RDM. reflexivity.
    - intros _. right. split.
      + constructor; [exact HnmP | constructor].
      + intros u o n [H | []]. inversion H; subst. discriminate. }
  split; [constructor|].
  split; [apply wf_ROObject|].
  split.
  { exists [RSBoxROE; ROObject], ROObject. split; [|split].
    - apply ST_Skip. split; [cbn; lia|].
      constructor; [exact HwfR|]. constructor; [apply wf_ROObject | constructor].
    - reflexivity.
    - apply qtype_qual; [cbn; lia | apply q_refl | constructor]. }
  split.
  { intros def parent Ss D mdef_parent Vs Hfind Hsuper Hfm _.
    cbn in Hfind. injection Hfind as <-. cbn in Hsuper. injection Hsuper as <- <-.
    exfalso.
    inversion Hfm as [? ? ? ? ? ? Hf Ho Hg | ? ? ? ? ? ? ? ? ? Hf Ho Hn Hs Hp];
      subst; cbn in Hf; inversion Hf; subst; cbn in *; discriminate. }
  intros _. split.
  - apply nm_class; [discriminate|]. constructor; [|constructor].
    eapply nm_qvar with (qb := RO) (C := 1) (Ts := []);
      [discriminate | reflexivity | constructor].
  - constructor; [apply nm_class; [discriminate | constructor] | constructor].
Qed.

(* ------------------CALLS------------------*)

Definition Δ0 : tv_env := mk_tv_env [] [] AbstractState 0.
Definition ROBoxMutPerson : qualified_type := TClass RO 2 [MutPerson].
Definition ROBoxImmPerson : qualified_type := TClass RO 2 [ImmPerson].

(** What the call rule asks of the receiver: the adapted declared receiver of
    [ageUp], seen through a readonly [ROBox<A>], is [@RO ROBox<@Mut Person>]
    whatever the qualifier of [A]. *)
Example recv_seen_mut :
  member_recv RO [MutPerson] [] [] ROBoxMutE = ROBoxMutPerson.
Proof. reflexivity. Qed.
Example recv_seen_imm :
  member_recv RO [ImmPerson] [] [] ROBoxMutE = ROBoxMutPerson.
Proof. reflexivity. Qed.

(** Accepted on a box of mutable persons. *)
Example call_on_mut_accepted :
  receiver_ok CT Δ0 ROBoxMutPerson (member_recv RO [MutPerson] [] [] ROBoxMutE) /\
  recv_args_known AbstractState RO ROBoxMutE.
Proof.
  split.
  - split; [|cbn; discriminate].
    apply qtype_qual; [cbn; lia | apply q_refl | apply Forall2_targ_sub_refl].
  - intros u o n [H | []]. inversion H; subst. cbn. discriminate.
Qed.

(** With no type variable in scope, a subtype of a [ROBox<A>] is a
    [ROBox<A'>] whose argument is [A] up to forgotten positions. *)
Lemma box_arg_inv : forall T U, qualified_type_subtype CT Δ0 T U ->
  forall q2 A, U = TClass q2 2 [A] ->
  exists q1 A', T = TClass q1 2 [A'] /\ targ_sub A' A.
Proof.
  intros T U H. induction H; intros q2' A HU; try discriminate.
  - inversion HU; subst. inversion Hargs as [|a b la lb Hab Hrest0]; subst.
    inversion Hrest0; subst. eauto.
  - inversion HU; subst. inversion Hsuper; subst.
    + do 2 eexists. split; [reflexivity | apply targ_sub_refl].
    + exfalso.
      destruct C as [|[|[|[|C]]]]; cbn in Hparent; try discriminate;
        try (destruct C; discriminate);
        inversion Hparent; subst; inversion Hrest; subst;
        match goal with
        | Hp : parent_lookup _ 0 = Some _ |- _ => cbn in Hp; discriminate
        end.
  - unfold tv_bound in Hbound. destruct o, n; discriminate.
  - inversion HU; subst. simpl in Hbound. lia.
  - destruct (IHqualified_type_subtype2 _ _ HU) as (qa & Aa & -> & Ha).
    destruct (IHqualified_type_subtype1 _ _ eq_refl) as (qb & Ab & -> & Hb).
    do 2 eexists. split; [reflexivity | eapply targ_sub_trans; eauto].
Qed.

(** Rejected on a box of immutable persons: the box does not have the
    element type the receiver asks for. *)
Example call_on_imm_rejected :
  ~ receiver_ok CT Δ0 ROBoxImmPerson (member_recv RO [ImmPerson] [] [] ROBoxMutE).
Proof.
  intros [H _]. rewrite recv_seen_imm in H.
  destruct (box_arg_inv _ _ H _ _ eq_refl) as (q1 & A' & E & Ha).
  inversion E; subst. inversion Ha; subst.
  destruct Hq as [Hq | [Hq _]]; discriminate.
Qed.

(** A receiver argument that follows the receiver, [@RDM E], cannot be
    checked through a readonly reference: the call rule rejects it. *)
Example rdm_arg_through_ro_rejected :
  ~ recv_args_known AbstractState RO
      (TClass RDM 2 [TVar (TVQual RDM) ClassVar 0]).
Proof. intros H. apply (H RDM ClassVar 0); [left; reflexivity | reflexivity]. Qed.

(* ------------------OVERRIDING------------------*)

(** An override may not ask more of the receiver's type arguments than the
    overridden method does.  For [Parent<E>] with
    [inspect(@RO Parent<E> this)] and [Child<E> extends Parent<E>], an
    override [inspect(@RO Child<@Mut E> this)] fails the receiver part of the
    override check: a child with an immutable element type is accepted by
    the inherited method and not by the override. *)
Example override_narrowing_rejected :
  ~ (forall (qr : q_r) (ca : list rtype),
       length ca = 1 ->
       radmit (qr2q qr) (map (dyn (qr2q qr) ca [] []) [tE]) [] (TClass RO 3 [tE]) ->
       radmit (qr2q qr) ca [] (TClass RO 4 [MutE])).
Proof.
  intros H.
  specialize (H Mut_r [RClass Imm 1 []] eq_refl).
  assert (Hp : radmit Mut (map (dyn Mut [RClass Imm 1 []] [] []) [tE]) [] (TClass RO 3 [tE])).
  { intros ma. cbn. constructor; [apply rarg_sub_refl | constructor]. }
  specialize (H Hp []). cbn in H. inversion H; subst.
  inversion H3; subst. destruct Hq as [Hq | [Hq _]]; discriminate.
Qed.

(** With the plain receiver [@RO Child<E>] the same check holds. *)
Example override_plain_accepted :
  forall (qr : q_r) (ca : list rtype),
    length ca = 1 ->
    radmit (qr2q qr) (map (dyn (qr2q qr) ca [] []) [tE]) [] (TClass RO 3 [tE]) ->
    radmit (qr2q qr) ca [] (TClass RO 4 [tE]).
Proof.
  intros qr [|R [|? ?]] Hlen _; try discriminate.
  intros ma. cbn. constructor; [apply rarg_sub_refl | constructor].
Qed.
