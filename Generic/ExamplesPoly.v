From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric
  GhostLabels GhostTyping GhostForget GhostInvariant GhostOverride GhostCall
  GhostEntry ArgViews ArgTyping ArgFit ArgInvariant
  ArgCases ArgClean ArgOverride ArgCall ArgMain ArgEntry ArgRsf.

(** A method that is polymorphic in a qualifier.

    A qualifier parameter stands for a qualifier only.  It is declared
    separately from the method's type parameters, it has no bound, and it is
    instantiated at a call by a qualifier ([@Mut], [@Imm], ..) or by a
    qualifier parameter of the caller.  [[Q]C<..>] is the class type [C<..>]
    carrying the qualifier supplied for [Q].  Only a qualifier parameter can
    be written in the brackets: a type variable there is not expressible.

      class Box  { }
      class Cell { rda @RDM Object item; }
      class Util {
        rs <Q> [Q]Box id([Q]Box b) { return b; }
        <Q1, Q2> [Q1]Box first([Q1]Box a, [Q2]Box b) { return a; }
        rs <Q> @RO Object peek([Q]Cell c) { @RO Object r; r = c.item; return r; }
        rs <Q> [Q]Box id2([Q]Box b) { [Q]Box r; r = this.<Q>id(b); return r; }
        rs <Q> [Q]Util self([Q]Util this) { return this; }
        rs <Q> [Q]Util self2([Q]Util this) {
          [Q]Util r; r = this.<Q>self(); return r; }
      }

      @Mut Box m  = new @Mut Box();
      @Imm Box i  = new @Imm Box();
      @Mut Util u = new @Mut Util();
      @Mut Object o = new @Mut Object();
      @Mut Cell c = new @Mut Cell(o);
      @Mut Box m2 = u.<@Mut>id(m);
      @Imm Box i2 = u.<@Imm>id(i);
      @Mut Box m3 = u.<@Mut, @Imm>first(m, i);
      @Imm Box i3 = u.<@Imm>id2(i);
      @Imm Util v = new @Imm Util();
      @Imm Util v2 = v.<@Imm>self2();
      @RO Object r = u.<@Mut>peek(c);
      @Mut Util u2 = u.<@Mut>self();

      class Sub extends Util {
        rs <Q> [Q]Sub self([Q]Sub this) { return this; }       // overrides
        rs <Q> [Q]Util self2(@RO Sub this) { [Q]Util r; return r; }
      }
      @Mut Util su = new @Mut Sub();
      @Mut Util u3 = su.<@Mut>self();     // runs Sub.self                   *)

(* ------------------THE PROGRAM------------------*)

Definition id_name : method_name := 0.
Definition first_name : method_name := 1.
Definition peek_name : method_name := 2.
Definition id2_name : method_name := 3.
Definition self_name : method_name := 4.
Definition self2_name : method_name := 5.

Definition ROObject : qualified_type := TClass RO 0 [].

(* [Q]C and [Q2]C, for the first and the second qualifier parameter *)
Definition tQ (C : class_name) : qualified_type := THead 0 C [].
Definition tQ2 (C : class_name) : qualified_type := THead 1 C [].

Definition ObjectDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 0; ctparams := [];
                     super := None |};
     body := {| fields := []; methods := [] |} |}.

Definition BoxDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 1; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := []; methods := [] |} |}.

Definition item_field : field_def :=
  {| assignability := RDA; ftype := TClass RDM 0 [] |}.

Definition CellDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 2; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := [item_field]; methods := [] |} |}.

Definition id_def : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mqparams := 1;
          mret := tQ 1;
          mname := id_name;
          mreceiver := TClass RO 3 [];
          mparams := [tQ 1] |};
     mbody := {| mbody_stmt := SSkip; mreturn := 1 |} |}.

Definition first_def : method_def :=
  {| msignature :=
       {| mscope := AbstractState;
          mtparams := [];
          mqparams := 2;
          mret := tQ 1;
          mname := first_name;
          mreceiver := TClass RO 3 [];
          mparams := [tQ 1; tQ2 1] |};
     mbody := {| mbody_stmt := SSkip; mreturn := 1 |} |}.

Definition peek_def : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mqparams := 1;
          mret := ROObject;
          mname := peek_name;
          mreceiver := TClass RO 3 [];
          mparams := [tQ 2] |};
     mbody :=
       {| mbody_stmt := SSeq (SLocal ROObject 2) (SVarAss 2 (EField 1 0));
          mreturn := 2 |} |}.

(* The method's own qualifier parameter, as a qualifier argument *)
Definition ownQ : qarg := QVar 0.

Definition id2_def : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mqparams := 1;
          mret := tQ 1;
          mname := id2_name;
          mreceiver := TClass RO 3 [];
          mparams := [tQ 1] |};
     mbody :=
       {| mbody_stmt := SSeq (SLocal (tQ 1) 2) (SCall 2 id_name 0 [] [ownQ] [1]);
          mreturn := 2 |} |}.

(* The receiver takes its qualifier from the method's qualifier parameter *)
Definition self_def : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mqparams := 1;
          mret := tQ 3;
          mname := self_name;
          mreceiver := tQ 3;
          mparams := [] |};
     mbody := {| mbody_stmt := SSkip; mreturn := 0 |} |}.

Definition self2_def : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mqparams := 1;
          mret := tQ 3;
          mname := self2_name;
          mreceiver := tQ 3;
          mparams := [] |};
     mbody :=
       {| mbody_stmt := SSeq (SLocal (tQ 3) 1) (SCall 1 self_name 0 [] [ownQ] []);
          mreturn := 1 |} |}.

Definition UtilDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 3; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := []; methods := [id_def; first_def; peek_def; id2_def; self_def; self2_def] |} |}.

(* Overrides self, keeping the [Q] receiver and returning the more specific
   [Q]Sub *)
Definition sub_self_def : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mqparams := 1;
          mret := tQ 4;
          mname := self_name;
          mreceiver := tQ 4;
          mparams := [] |};
     mbody := {| mbody_stmt := SSkip; mreturn := 0 |} |}.

(* Overrides self2 with a readonly receiver *)
Definition sub_self2_def : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mqparams := 1;
          mret := tQ 3;
          mname := self2_name;
          mreceiver := TClass RO 4 [];
          mparams := [] |};
     mbody := {| mbody_stmt := SLocal (tQ 3) 1; mreturn := 1 |} |}.

Definition SubDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 4; ctparams := [];
                     super := Some (3, []) |};
     body := {| fields := []; methods := [sub_self_def; sub_self2_def] |} |}.

Definition CT : class_table := [ObjectDef; BoxDef; CellDef; UtilDef; SubDef].

Definition MutBox : qualified_type := TClass Mut 1 [].
Definition ImmBox : qualified_type := TClass Imm 1 [].
Definition MutUtil : qualified_type := TClass Mut 3 [].
Definition MutObject : qualified_type := TClass Mut 0 [].
Definition ImmObject : qualified_type := TClass Imm 0 [].
Definition MutCell : qualified_type := TClass Mut 2 [].
Definition ImmUtil : qualified_type := TClass Imm 3 [].

(* Everything up to the call of peek *)
Definition prefix : stmt :=
  SSeq (SLocal MutBox 1)
  (SSeq (SLocal ImmBox 2)
  (SSeq (SLocal MutUtil 3)
  (SSeq (SLocal MutBox 4)
  (SSeq (SLocal ImmBox 5)
  (SSeq (SLocal MutObject 6)
  (SSeq (SLocal MutCell 7)
  (SSeq (SLocal ROObject 8)
  (SSeq (SLocal MutBox 9)
  (SSeq (SLocal ImmBox 10)
  (SSeq (SLocal MutUtil 11)
  (SSeq (SLocal ImmUtil 12)
  (SSeq (SLocal ImmUtil 13)
  (SSeq (SLocal MutUtil 14)
  (SSeq (SLocal MutUtil 15)
  (SSeq (SNew 1 Mut_c 1 [] [])
  (SSeq (SNew 2 Imm_c 1 [] [])
  (SSeq (SNew 3 Mut_c 3 [] [])
  (SSeq (SNew 6 Mut_c 0 [] [])
  (SSeq (SNew 7 Mut_c 2 [] [6])
  (SSeq (SNew 12 Imm_c 3 [] [])
  (SSeq (SNew 14 Mut_c 4 [] [])
  (SSeq (SCall 4 id_name 3 [] [QLit Mut] [1])
  (SSeq (SCall 5 id_name 3 [] [QLit Imm] [2])
  (SSeq (SCall 9 first_name 3 [] [QLit Mut; QLit Imm] [1; 2])
  (SSeq (SCall 10 id2_name 3 [] [QLit Imm] [2])
        (SCall 13 self2_name 12 [] [QLit Imm] [])))))))))))))))))))))))))).

(* r = u.<@Mut>peek(c) *)
Definition callP : stmt := SCall 8 peek_name 3 [] [QLit Mut] [7].

(* u2 = u.<@Mut>self() *)
Definition callS : stmt := SCall 11 self_name 3 [] [QLit Mut] [].

(* u3 = su.<@Mut>self(): the object is a Sub, so Sub.self runs *)
Definition callO : stmt := SCall 15 self_name 14 [] [QLit Mut] [].

Definition main : stmt := SSeq prefix (SSeq callP (SSeq callS callO)).

Definition Δ0 : tv_env := mk_tv_env [] [] AbstractState 0.
Definition sΓ0 : s_env := [MutObject].
Definition sΓfinal : s_env :=
  [MutObject; MutBox; ImmBox; MutUtil; MutBox; ImmBox; MutObject; MutCell;
   ROObject; MutBox; ImmBox; MutUtil; ImmUtil; ImmUtil; MutUtil; MutUtil].

(* ------------------SMALL TACTICS------------------*)

Ltac qs := first [apply q_refl; discriminate | apply q_rd | apply q_bot].

Ltac wf_plain :=
  eapply wfs_class;
    [reflexivity | right; cbn; qs | reflexivity | constructor | constructor].

Lemma wf_plain_class : forall Δ top q0 C,
  C < 5 -> q0 <> Lost -> wf_stype CT Δ top (TClass q0 C []).
Proof.
  intros Δ top q0 C HC Hq.
  destruct C as [|[|[|[|[|C]]]]]; try lia;
    (eapply wfs_class;
       [reflexivity | right | reflexivity | constructor | constructor];
     destruct q0; cbn; try qs; congruence).
Qed.

Lemma wf_use : forall Δ q0 C,
  C < 5 -> q0 <> Lost -> wf_stypeuse CT Δ (TClass q0 C []).
Proof. intros. apply wf_plain_class; auto. Qed.

Ltac wfu := apply wf_use; [cbn; lia | discriminate].

Ltac wfenv :=
  split; [cbn; lia |
          cbn; repeat (apply Forall_cons; [solve [wfu]|]); apply Forall_nil].

Ltac refl_sub :=
  apply qualified_type_subtype_refl_class; [cbn; lia | discriminate].

(* ------------------WHAT THE NEW TYPE FORM MEANS------------------*)

(** Instantiating the qualifier parameter: [[Q]Box] with [Q := @Mut] is
    [@Mut Box], with [Q := @Imm] it is [@Imm Box], and with the caller's own
    qualifier parameter it is the caller's [[Q']Box]. *)
Example inst_mut :
  member_type AbstractState Mut [] [] [QLit Mut] (tQ 1) = MutBox.
Proof. reflexivity. Qed.

Example inst_imm :
  member_type AbstractState Mut [] [] [QLit Imm] (tQ 1) = ImmBox.
Proof. reflexivity. Qed.

Example inst_bot :
  member_type AbstractState Mut [] [] [QLit Bot] (tQ 1) = TClass Bot 1 [].
Proof. reflexivity. Qed.

Example inst_caller_param :
  member_type AbstractState Mut [] [] [QVar 0] (tQ 1) = tQ 1.
Proof. reflexivity. Qed.

(** Two qualifier parameters are instantiated independently. *)
Example inst_two :
  member_type AbstractState Mut [] [] [QLit Mut; QLit Imm] (tQ 1) = MutBox /\
  member_type AbstractState Mut [] [] [QLit Mut; QLit Imm] (tQ2 1) = ImmBox.
Proof. split; reflexivity. Qed.

(** Inside the method the parameter is used through its readonly view, so a
    field declared [@RDM] reads as [@Lost]: [Q |> RDM = Lost]. *)
Definition ΔQ (m : method_scope) : tv_env := mk_tv_env [] [] m 1.

Example view_of_head : forall m, ubound (ΔQ m) (tQ 2) = Some (TClass RO 2 []).
Proof. reflexivity. Qed.

Example read_through_head : forall m,
  member_type m RO [] [] [] (ftype item_field) = TClass Lost 0 [].
Proof. intros []; reflexivity. Qed.

(* ------------------CLASS TABLE WELL-FORMEDNESS------------------*)

Lemma wf_tQ : forall m top C, C < 5 -> wf_stype CT (ΔQ m) top (tQ C).
Proof.
  intros m top C HC. apply wfs_head; [cbn; lia|].
  apply wf_plain_class; [exact HC | discriminate].
Qed.

Definition ΔQ2 : tv_env := mk_tv_env [] [] AbstractState 2.

Lemma wf_tQ_2 : forall top, wf_stype CT ΔQ2 top (tQ 1).
Proof.
  intros top. apply wfs_head; [cbn; lia|].
  apply wf_plain_class; [lia | discriminate].
Qed.

Lemma wf_tQ2_2 : forall top, wf_stype CT ΔQ2 top (tQ2 1).
Proof.
  intros top. apply wfs_head; [cbn; lia|].
  apply wf_plain_class; [lia | discriminate].
Qed.

Lemma collect_Object : CollectFields CT 0 [].
Proof. eapply CF_Object; reflexivity. Qed.

Lemma collect_Box : CollectFields CT 1 [].
Proof.
  change (CollectFields CT 1
            (map (subst_field []) [] ++ Syntax.fields (body BoxDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma collect_Cell : CollectFields CT 2 [item_field].
Proof.
  change (CollectFields CT 2
            (map (subst_field []) [] ++ Syntax.fields (body CellDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma collect_Util : CollectFields CT 3 [].
Proof.
  change (CollectFields CT 3
            (map (subst_field []) [] ++ Syntax.fields (body UtilDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma collect_Sub : CollectFields CT 4 [].
Proof.
  change (CollectFields CT 4
            (map (subst_field []) [] ++ Syntax.fields (body SubDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Util.
Qed.

Lemma no_method_in_Object : forall m D mdef,
  ~ FindMethodWithName CT 0 m D mdef.
Proof.
  intros m D mdef H. inversion H; subst.
  - cbn in Hfind. injection Hfind as <-. cbn in Hget_method. discriminate.
  - cbn in Hfind. injection Hfind as <-. cbn in Hsuper. discriminate.
Qed.

Ltac no_override :=
  intros def parent Ss D mdef_parent Vs Hfind Hsuper Hfm _;
  cbn in Hfind; injection Hfind as <-; cbn in Hsuper;
  injection Hsuper as <- <-;
  exfalso; eapply no_method_in_Object; eauto.

Lemma sub_tQ_refl : forall Δ C, qualified_type_subtype CT Δ (tQ C) (tQ C).
Proof. intros. apply qtype_head_args. constructor. Qed.

(** [id] is a readonly-state method.  Its signature writes no mutable
    position: [[Q]Box] is checked through its readonly view
    [@RO Box]. *)
Lemma wf_id : wf_method CT 3 id_def.
Proof.
  unfold wf_method. cbn.
  change (method_tv_env CT 3 (msignature id_def)) with (ΔQ ReadonlyState).
  assert (Hwf : wf_senv CT (ΔQ ReadonlyState) [TClass RO 3 []; tQ 1]).
  { split; [cbn; lia|].
    constructor; [wfu|]. constructor; [apply wf_tQ; lia | constructor]. }
  split; [apply receiver_plain_ok; left; exists RO; reflexivity|].
  split; [constructor|].
  split; [apply wf_tQ; lia|].
  split.
  { exists [TClass RO 3 []; tQ 1], (tQ 1). split; [|split].
    - apply ST_Skip. exact Hwf.
    - reflexivity.
    - apply sub_tQ_refl. }
  split; [no_override|].
  intros _. split.
  - apply nm_class; [discriminate | constructor].
  - constructor; [|constructor].
    apply nm_head; constructor.
Qed.

Lemma wf_first : wf_method CT 3 first_def.
Proof.
  unfold wf_method. cbn.
  change (method_tv_env CT 3 (msignature first_def)) with ΔQ2.
  assert (Hwf : wf_senv CT ΔQ2 [TClass RO 3 []; tQ 1; tQ2 1]).
  { split; [cbn; lia|].
    constructor; [wfu|]. constructor; [apply wf_tQ_2|].
    constructor; [apply wf_tQ2_2 | constructor]. }
  split; [apply receiver_plain_ok; left; exists RO; reflexivity|].
  split; [constructor|].
  split; [apply wf_tQ_2|].
  split.
  { exists [TClass RO 3 []; tQ 1; tQ2 1], (tQ 1). split; [|split].
    - apply ST_Skip. exact Hwf.
    - reflexivity.
    - apply sub_tQ_refl. }
  split; [no_override|].
  intros [H | H]; discriminate.
Qed.

(** [peek] reads a field through a parameter of type [[Q]Cell]: the read is
    typed through the readonly view, and gives [@Lost Object]. *)
Lemma wf_peek : wf_method CT 3 peek_def.
Proof.
  unfold wf_method. cbn.
  change (method_tv_env CT 3 (msignature peek_def)) with (ΔQ ReadonlyState).
  assert (Hwf1 : wf_senv CT (ΔQ ReadonlyState) [TClass RO 3 []; tQ 2]).
  { split; [cbn; lia|].
    constructor; [wfu|]. constructor; [apply wf_tQ; lia | constructor]. }
  assert (Hwf2 : wf_senv CT (ΔQ ReadonlyState) [TClass RO 3 []; tQ 2; ROObject]).
  { split; [cbn; lia|].
    constructor; [wfu|]. constructor; [apply wf_tQ; lia|].
    constructor; [wfu | constructor]. }
  split; [apply receiver_plain_ok; left; exists RO; reflexivity|].
  split; [constructor|].
  split; [wfu|].
  split.
  { exists [TClass RO 3 []; tQ 2; ROObject], ROObject. split; [|split].
    - eapply ST_Seq; [exact Hwf1 | |].
      + eapply ST_Local; [exact Hwf1 | wfu | | reflexivity |]; reflexivity.
      + eapply ST_VarAss with (Tx := ROObject);
          [exact Hwf2 | | discriminate | reflexivity | ].
        * eapply ET_Field with (fDef := item_field) (T := tQ 2);
            [exact Hwf2 | reflexivity | reflexivity |].
          eapply FL_Found; [apply collect_Cell | reflexivity].
        * cbn. apply qtype_qual; [cbn; lia | qs | constructor].
    - reflexivity.
    - refl_sub. }
  split; [no_override|].
  intros _. split.
  - apply nm_class; [discriminate | constructor].
  - constructor; [|constructor].
    apply nm_head; constructor.
Qed.

(** [id2] passes its own qualifier parameter on: the call [this.<Q>id(b)]
    is typed inside a readonly-state body, and its result is again
    [[Q]Box]. *)
Lemma wf_id2 : wf_method CT 3 id2_def.
Proof.
  unfold wf_method. cbn.
  change (method_tv_env CT 3 (msignature id2_def)) with (ΔQ ReadonlyState).
  assert (Hwf1 : wf_senv CT (ΔQ ReadonlyState) [TClass RO 3 []; tQ 1]).
  { split; [cbn; lia|].
    constructor; [wfu|]. constructor; [apply wf_tQ; lia | constructor]. }
  assert (Hwf2 : wf_senv CT (ΔQ ReadonlyState) [TClass RO 3 []; tQ 1; tQ 1]).
  { split; [cbn; lia|].
    constructor; [wfu|]. constructor; [apply wf_tQ; lia|].
    constructor; [apply wf_tQ; lia | constructor]. }
  split; [apply receiver_plain_ok; left; exists RO; reflexivity|].
  split; [constructor|].
  split; [apply wf_tQ; lia|].
  split.
  { exists [TClass RO 3 []; tQ 1; tQ 1], (tQ 1). split; [|split].
    - eapply ST_Seq; [exact Hwf1 | |].
      + eapply ST_Local; [exact Hwf1 | apply wf_tQ; lia | | reflexivity |];
          reflexivity.
      + eapply ST_Call with (Tx := tQ 1) (Ty := TClass RO 3 [])
          (argtypes := [tQ 1]) (qy := RO) (C := 3) (Ts := []) (D := 3)
          (Vs := []) (mdef := id_def);
          [exact Hwf2 | reflexivity | reflexivity | reflexivity | reflexivity
          | | | discriminate | | | reflexivity | | | | | apply method_subtyping_refl
          | reflexivity |  | recv_known].
        * eapply FOM_Here; reflexivity.
        * apply si_refl.
        * constructor.
        * constructor.
        * constructor.
        * cbn. apply sub_tQ_refl.
        * cbn. split; [refl_sub|].
          cbn. discriminate.
        * constructor; [|constructor]. cbn. split; [apply sub_tQ_refl|].
          exact I.
        * constructor; [cbn; lia | constructor].
    - reflexivity.
    - apply sub_tQ_refl. }
  split; [no_override|].
  intros _. split.
  - apply nm_class; [discriminate | constructor].
  - constructor; [|constructor].
    apply nm_head; constructor.
Qed.

(** [self] has a receiver of type [[Q]Util] and returns it. *)
Lemma wf_self : wf_method CT 3 self_def.
Proof.
  unfold wf_method. cbn.
  change (method_tv_env CT 3 (msignature self_def)) with (ΔQ ReadonlyState).
  assert (Hwf : wf_senv CT (ΔQ ReadonlyState) [tQ 3]).
  { split; [cbn; lia|]. constructor; [apply wf_tQ; lia | constructor]. }
  split; [apply receiver_plain_ok; right; exists 0; reflexivity|].
  split; [constructor|].
  split; [apply wf_tQ; lia|].
  split.
  { exists [tQ 3], (tQ 3). split; [|split].
    - apply ST_Skip. exact Hwf.
    - reflexivity.
    - apply sub_tQ_refl. }
  split; [no_override|].
  intros _. split.
  - apply nm_head; constructor.
  - constructor.
Qed.

(** [self2] calls [self] on its own receiver, passing its qualifier
    parameter on. *)
Lemma wf_self2 : wf_method CT 3 self2_def.
Proof.
  unfold wf_method. cbn.
  change (method_tv_env CT 3 (msignature self2_def)) with (ΔQ ReadonlyState).
  assert (Hwf1 : wf_senv CT (ΔQ ReadonlyState) [tQ 3]).
  { split; [cbn; lia|]. constructor; [apply wf_tQ; lia | constructor]. }
  assert (Hwf2 : wf_senv CT (ΔQ ReadonlyState) [tQ 3; tQ 3]).
  { split; [cbn; lia|]. constructor; [apply wf_tQ; lia|].
    constructor; [apply wf_tQ; lia | constructor]. }
  split; [apply receiver_plain_ok; right; exists 0; reflexivity|].
  split; [constructor|].
  split; [apply wf_tQ; lia|].
  split.
  { exists [tQ 3; tQ 3], (tQ 3). split; [|split].
    - eapply ST_Seq; [exact Hwf1 | |].
      + eapply ST_Local; [exact Hwf1 | apply wf_tQ; lia | | reflexivity |];
          reflexivity.
      + eapply ST_Call with (Tx := tQ 3) (Ty := tQ 3)
          (argtypes := []) (qy := RO) (C := 3) (Ts := []) (D := 3)
          (Vs := []) (mdef := self_def);
          [exact Hwf2 | reflexivity | reflexivity | reflexivity | reflexivity
          | | | discriminate | | | reflexivity | | | | | apply method_subtyping_refl
          | reflexivity |  | recv_known].
        * eapply FOM_Here; reflexivity.
        * apply si_refl.
        * constructor.
        * constructor.
        * constructor.
        * cbn. apply sub_tQ_refl.
        * cbn. split; [apply sub_tQ_refl|]. exact I.
        * constructor.
        * constructor; [cbn; lia | constructor].
    - reflexivity.
    - apply sub_tQ_refl. }
  split; [no_override|].
  intros _. split.
  - apply nm_head; constructor.
  - constructor.
Qed.

(** A field that is not declared assignable cannot be written through a
    variable whose qualifier is a qualifier parameter, the receiver
    included. *)
Theorem head_write_untypable : forall CT0 Δ sΓ mt x f y n C Ts sΓ',
  static_getType sΓ x = Some (THead n C Ts) ->
  (forall fd, sf_def_rel CT0 C f fd -> assignability fd <> Assignable) ->
  ~ stmt_typing CT0 Δ sΓ mt (SFldWrite x f y) sΓ'.
Proof.
  intros CT0 Δ sΓ mt x f y n C Ts sΓ' Hx Hna Htyp.
  inversion Htyp; subst.
  rewrite Hx in Hget_x. injection Hget_x as <-.
  simpl in Hub. destruct (Nat.ltb n (qparams Δ)); [|discriminate].
  injection Hub as <- <- <-.
  apply (Hna _ Hfld_def).
  destruct mt, (assignability fieldT); simpl in Hassignable;
    try discriminate; reflexivity.
Qed.

(* ------------------OVERRIDING A METHOD WHOSE RECEIVER IS [Q]------------------*)

(** The receiver part of the override check, for an overridden receiver
    [[Q]Util] seen from a subclass declared [@RDM]: the overriding method may
    keep the receiver [[Q]..] or declare it [@RO ..]; it may not declare it
    [@Mut ..].  A method whose receiver is [@Mut ..] cannot be overridden by
    one whose receiver is [[Q]..]. *)
Definition seen (T : qualified_type) : qualified_type :=
  member_type AbstractState (qc2q RDM_c) [] [] (qvar_args 1) T.

Example override_head_by_head :
  qualified_type_subtype CT (ΔQ ReadonlyState)
    (rebase (seen (tQ 3)) (tQ 3)) (tQ 3).
Proof. cbn. apply sub_tQ_refl. Qed.

Example override_head_by_ro :
  qualified_type_subtype CT (ΔQ ReadonlyState)
    (rebase (seen (tQ 3)) (TClass RO 3 [])) (TClass RO 3 []).
Proof. cbn. apply qtype_head_ro; [cbn; lia | constructor]. Qed.

Example override_head_by_mut_rejected :
  ~ qualified_type_subtype CT (ΔQ ReadonlyState)
      (rebase (seen (tQ 3)) (TClass Mut 3 [])) (TClass Mut 3 []).
Proof.
  cbn. intros H.
  destruct (proj2 (sub_head_inv _ _ _ _ H) _ _ _ eq_refl)
    as [(D & Us & E) | (D & Us & E)]; discriminate.
Qed.

Example override_mut_by_head_rejected :
  ~ qualified_type_subtype CT (ΔQ ReadonlyState)
      (rebase (seen (TClass Mut 3 [])) (tQ 3)) (tQ 3).
Proof.
  cbn. intros H.
  destruct (proj1 (sub_head_inv _ _ _ _ H) _ _ _ eq_refl)
    as [(q2 & D & Us & E & _) | (E & _)]; discriminate.
Qed.

(** On two written receivers the check is the old one: the overridden
    qualifier, seen from the subclass, is below the overriding one. *)
Example override_written :
  qualified_type_subtype CT (ΔQ ReadonlyState)
    (rebase (seen (TClass RDM 3 [])) (TClass RO 3 [])) (TClass RO 3 []).
Proof. cbn. apply qtype_qual; [cbn; lia | apply q_rd | constructor]. Qed.

(* ------------------A SUBCLASS THAT OVERRIDES------------------*)

Ltac overrides md :=
  intros def parent Ss D mdef_parent Vs Hfind Hsuper Hfm _;
  cbn in Hfind; injection Hfind as <-; cbn in Hsuper;
  injection Hsuper as <- <-;
  let Hh := fresh "Hh" in
  assert (Hh : FindMethodWithName CT 3 (mname (msignature md)) 3 md)
    by (eapply FOM_Here; reflexivity);
  destruct (find_method_with_name_deterministic _ _ _ _ _ _ _ Hfm Hh)
    as [-> ->];
  clear Hh Hfm; unfold method_override_compatible; cbn.

(** [Sub.self] overrides [Util.self]: the receiver stays [[Q]..], now on
    [Sub], and the result is the more specific [[Q]Sub]. *)
Lemma wf_sub_self : wf_method CT 4 sub_self_def.
Proof.
  unfold wf_method. cbn.
  change (method_tv_env CT 4 (msignature sub_self_def)) with (ΔQ ReadonlyState).
  assert (Hwf : wf_senv CT (ΔQ ReadonlyState) [tQ 4]).
  { split; [cbn; lia|]. constructor; [apply wf_tQ; lia | constructor]. }
  split; [apply receiver_plain_ok; right; exists 0; reflexivity|].
  split; [constructor|].
  split; [apply wf_tQ; lia|].
  split.
  { exists [tQ 4], (tQ 4). split; [|split].
    - apply ST_Skip. exact Hwf.
    - reflexivity.
    - apply sub_tQ_refl. }
  split.
  { overrides self_def.
    split; [reflexivity|]. split; [reflexivity|]. split; [split; reflexivity|].
    split.
    - (* the result: [Q]Sub is a [Q]Util *)
      apply qtype_head_hier. eapply si_step; [reflexivity|]. cbn. apply si_refl.
    - split; [constructor|].
      (* the receiver: the overridden [Q]Util, seen on Sub, is [Q]Sub *)
      split; [apply sub_tQ_refl | radmit_plain]. }
  intros _. split.
  - apply nm_head; constructor.
  - constructor.
Qed.

(** [Sub.self2] overrides [Util.self2] with a readonly receiver. *)
Lemma wf_sub_self2 : wf_method CT 4 sub_self2_def.
Proof.
  unfold wf_method. cbn.
  change (method_tv_env CT 4 (msignature sub_self2_def)) with (ΔQ ReadonlyState).
  assert (Hwf : wf_senv CT (ΔQ ReadonlyState) [TClass RO 4 []]).
  { split; [cbn; lia|]. constructor; [wfu | constructor]. }
  split; [apply receiver_plain_ok; left; exists RO; reflexivity|].
  split; [constructor|].
  split; [apply wf_tQ; lia|].
  split.
  { exists [TClass RO 4 []; tQ 3], (tQ 3). split; [|split].
    - eapply ST_Local; [exact Hwf | apply wf_tQ; lia | | reflexivity |];
        reflexivity.
    - reflexivity.
    - apply sub_tQ_refl. }
  split.
  { overrides self2_def.
    split; [reflexivity|]. split; [reflexivity|]. split; [split; reflexivity|].
    split; [apply sub_tQ_refl|].
    split; [constructor|].
    (* the receiver: the overridden [Q]Util, seen on Sub, is a readonly Sub *)
    split; [apply qtype_head_ro; [cbn; lia | constructor] | radmit_plain]. }
  intros _. split.
  - apply nm_class; [discriminate | constructor].
  - constructor.
Qed.

(** A written-mutable receiver is not accepted for an override of
    [Util.self]: the receiver part of the check fails. *)
Example sub_self_mut_receiver_rejected :
  ~ qualified_type_subtype CT (ΔQ ReadonlyState)
      (rebase (seen (mreceiver (msignature self_def))) (TClass Mut 4 []))
      (TClass Mut 4 []).
Proof.
  cbn. intros H.
  destruct (proj2 (sub_head_inv _ _ _ _ H) _ _ _ eq_refl)
    as [(D & Us & E) | (D & Us & E)]; discriminate.
Qed.

Lemma poly_ct_wf : wf_class_table CT.
Proof.
  unfold wf_class_table. split; [|split; [|split]].
  - constructor; [|constructor; [|constructor; [|constructor;
      [|constructor; [|constructor]]]]].
    + apply WFObjectDef; reflexivity.
    + eapply WFOtherDef with (superC := 0) (Ss := []);
        try reflexivity; cbn; try solve [constructor]; auto.
      * apply wf_use; [lia | discriminate].
    + eapply WFOtherDef with (superC := 0) (Ss := []);
        try reflexivity; cbn; try solve [constructor]; auto.
      * apply wf_use; [lia | discriminate].
      * constructor; [|constructor]. apply wf_use; [lia | discriminate].
    + eapply WFOtherDef with (superC := 0) (Ss := []);
        try reflexivity; cbn; try solve [constructor]; auto.
      * apply wf_use; [lia | discriminate].
      * constructor; [apply wf_id|].
        constructor; [apply wf_first|].
        constructor; [apply wf_peek|].
        constructor; [apply wf_id2|].
        constructor; [apply wf_self|].
        constructor; [apply wf_self2 | constructor].
      * repeat constructor; cbn; intuition discriminate.
    + eapply WFOtherDef with (superC := 3) (Ss := []);
        try reflexivity; cbn; try solve [constructor]; try lia; auto.
      * apply wf_use; [lia | discriminate].
      * constructor; [apply wf_sub_self|].
        constructor; [apply wf_sub_self2 | constructor].
      * repeat constructor; cbn; intuition discriminate.
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

(* ------------------MAIN IS WELL TYPED------------------*)

Ltac ty_local :=
  eapply ST_Local;
    [wfenv | solve [wfu] | reflexivity | reflexivity | reflexivity].

Ltac ty_seq := eapply ST_Seq; [wfenv | |].

Lemma sub_to_ROObject : forall Δ q0,
  qualified_type_subtype CT Δ (TClass q0 0 []) ROObject.
Proof. intros. apply qtype_qual; [cbn; lia | qs | constructor]. Qed.

(** A call of [id] with the qualifier argument [qa]: the box goes in and
    comes back at the same qualifier. *)
Lemma call_id_typed : forall sΓ x z qa nm md,
  (nm = id_name /\ md = id_def) \/ (nm = id2_name /\ md = id2_def) ->
  wf_senv CT Δ0 sΓ ->
  qa = Mut \/ qa = Imm ->
  static_getType sΓ x = Some (TClass qa 1 []) ->
  static_getType sΓ 3 = Some MutUtil ->
  static_getType sΓ z = Some (TClass qa 1 []) ->
  x <> 0 ->
  stmt_typing CT Δ0 sΓ AbstractState
    (SCall x nm 3 [] [QLit qa] [z]) sΓ.
Proof.
  intros sΓ x z qa nm md Hmd Hwf Hqa Hx Hu Hz Hx0.
  assert (Hnl : qa <> Lost) by (destruct Hqa; subst; discriminate).
  assert (Hfind : FindMethodWithName CT 3 nm 3 md).
  { destruct Hmd as [[-> ->] | [-> ->]]; eapply FOM_Here; reflexivity. }
  assert (Hsig : mscope (msignature md) = ReadonlyState /\
                 mtparams (msignature md) = [] /\
                 mqparams (msignature md) = 1 /\
                 mret (msignature md) = tQ 1 /\
                 mreceiver (msignature md) = TClass RO 3 [] /\
                 mparams (msignature md) = [tQ 1]).
  { destruct Hmd as [[-> ->] | [-> ->]]; repeat split; reflexivity. }
  destruct Hsig as (Hsc & Htp & Hqp & Hrt & Hrc & Hpm).
  eapply ST_Call with (Tx := TClass qa 1 []) (Ty := MutUtil)
    (argtypes := [TClass qa 1 []])
    (qy := Mut) (C := 3) (Ts := []) (D := 3) (Vs := []) (mdef := md);
    [exact Hwf | exact Hx | exact Hu | | reflexivity
    | exact Hfind | | exact Hx0 | | | rewrite Htp; reflexivity | | | | |
    | rewrite Hqp; reflexivity |  | rewrite Hrc; recv_known];
    try rewrite Htp; try rewrite Hrt; try rewrite Hrc; try rewrite Hpm;
    try rewrite Hsc; try apply method_rs_as.
  - cbn. rewrite Hz. reflexivity.
  - apply si_refl.
  - constructor.
  - constructor.
  - constructor.
  - cbn. apply qualified_type_subtype_refl_class; [cbn; lia | exact Hnl].
  - cbn. split.
    + apply qtype_qual; [cbn; lia | qs | constructor].
    + cbn. discriminate.
  - constructor; [|constructor]. cbn. split.
    + apply qualified_type_subtype_refl_class; [cbn; lia | exact Hnl].
    + cbn. split; [exact Hnl | exact I].
  - constructor; [exact Hnl | constructor].
Qed.

(** A call of [self] or [self2] on a receiver of qualifier [qa], with the
    qualifier argument [qa]: the receiver comes back at the same qualifier. *)
Lemma call_self_typed : forall sΓ x y qa nm md,
  (nm = self_name /\ md = self_def) \/ (nm = self2_name /\ md = self2_def) ->
  wf_senv CT Δ0 sΓ ->
  qa = Mut \/ qa = Imm ->
  static_getType sΓ x = Some (TClass qa 3 []) ->
  static_getType sΓ y = Some (TClass qa 3 []) ->
  x <> 0 ->
  stmt_typing CT Δ0 sΓ AbstractState (SCall x nm y [] [QLit qa] []) sΓ.
Proof.
  intros sΓ x y qa nm md Hmd Hwf Hqa Hx Hy Hx0.
  assert (Hnl : qa <> Lost) by (destruct Hqa; subst; discriminate).
  assert (Hvr : forall q0, q0 <> RDM -> vpa_q AbstractState qa q0 = q0).
  { intros q0 Hq0. destruct Hqa; subst; destruct q0; simpl; congruence. }
  assert (Hfind : FindMethodWithName CT 3 nm 3 md).
  { destruct Hmd as [[-> ->] | [-> ->]]; eapply FOM_Here; reflexivity. }
  assert (Hsig : mscope (msignature md) = ReadonlyState /\
                 mtparams (msignature md) = [] /\
                 mqparams (msignature md) = 1 /\
                 mret (msignature md) = tQ 3 /\
                 mreceiver (msignature md) = tQ 3 /\
                 mparams (msignature md) = []).
  { destruct Hmd as [[-> ->] | [-> ->]]; repeat split; reflexivity. }
  destruct Hsig as (Hsc & Htp & Hqp & Hrt & Hrc & Hpm).
  eapply ST_Call with (Tx := TClass qa 3 []) (Ty := TClass qa 3 [])
    (argtypes := [])
    (qy := qa) (C := 3) (Ts := []) (D := 3) (Vs := []) (mdef := md);
    [exact Hwf | exact Hx | exact Hy | reflexivity | reflexivity
    | exact Hfind | | exact Hx0 | | | rewrite Htp; reflexivity | | | | |
    | rewrite Hqp; reflexivity |  | rewrite Hrc; recv_known];
    try rewrite Htp; try rewrite Hrt; try rewrite Hrc; try rewrite Hpm;
    try rewrite Hsc; try apply method_rs_as.
  - apply si_refl.
  - constructor.
  - constructor.
  - constructor.
  - cbn. apply qualified_type_subtype_refl_class; [cbn; lia | exact Hnl].
  - cbn. split.
    + apply qualified_type_subtype_refl_class; [cbn; lia | exact Hnl].
    + cbn. exact Hnl.
  - constructor.
  - constructor; [exact Hnl | constructor].
Qed.

Lemma prefix_typed :
  stmt_typing CT Δ0 sΓ0 AbstractState prefix sΓfinal.
Proof.
  unfold prefix, sΓ0, sΓfinal.
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  cbn.
  ty_seq.
  { eapply ST_New with (Tx := MutBox) (argtypes := []) (fds := []);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | wfu | constructor | constructor
      | apply collect_Box | constructor | ].
    cbn. refl_sub. }
  ty_seq.
  { eapply ST_New with (Tx := ImmBox) (argtypes := []) (fds := []);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | wfu | constructor | constructor
      | apply collect_Box | constructor | ].
    cbn. refl_sub. }
  ty_seq.
  { eapply ST_New with (Tx := MutUtil) (argtypes := []) (fds := []);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | wfu | constructor | constructor
      | apply collect_Util | constructor | ].
    cbn. refl_sub. }
  ty_seq.
  { eapply ST_New with (Tx := MutObject) (argtypes := []) (fds := []);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | wfu | constructor | constructor
      | apply collect_Object | constructor | ].
    cbn. refl_sub. }
  ty_seq.
  { eapply ST_New with (Tx := MutCell) (argtypes := [MutObject])
      (fds := [item_field]);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | wfu | constructor | constructor
      | apply collect_Cell | | ].
    - constructor; [|constructor]. cbn. split.
      + refl_sub.
      + cbn. split; [discriminate | exact I].
    - cbn. refl_sub. }
  ty_seq.
  { eapply ST_New with (Tx := ImmUtil) (argtypes := []) (fds := []);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | wfu | constructor | constructor
      | apply collect_Util | constructor | ].
    cbn. refl_sub. }
  (* su = new @Mut Sub(), held as a @Mut Util *)
  ty_seq.
  { eapply ST_New with (Tx := MutUtil) (argtypes := []) (fds := []);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | wfu | constructor | constructor
      | apply collect_Sub | constructor | ].
    cbn. apply qtype_hier. eapply si_step; [reflexivity|]. cbn. apply si_refl. }
  ty_seq.
  { apply call_id_typed with (qa := Mut) (md := id_def);
      [left; split; reflexivity | wfenv | left; reflexivity | reflexivity
      | reflexivity | reflexivity | discriminate]. }
  ty_seq.
  { apply call_id_typed with (qa := Imm) (md := id_def);
      [left; split; reflexivity | wfenv | right; reflexivity | reflexivity
      | reflexivity | reflexivity | discriminate]. }
  (* m3 = u.<@Mut, @Imm>first(m, i): two qualifier arguments *)
  ty_seq.
  { eapply ST_Call with (Tx := MutBox) (Ty := MutUtil)
      (argtypes := [MutBox; ImmBox])
      (qy := Mut) (C := 3) (Ts := []) (D := 3) (Vs := []) (mdef := first_def);
      [wfenv | reflexivity | reflexivity | reflexivity | reflexivity
      | | | discriminate | | | reflexivity | | | | | apply method_subtyping_refl
          | reflexivity |  | recv_known].
    - eapply FOM_Here; reflexivity.
    - apply si_refl.
    - constructor.
    - constructor.
    - constructor.
    - cbn. refl_sub.
    - cbn. split.
      + apply qtype_qual; [cbn; lia | qs | constructor].
      + cbn. discriminate.
    - constructor; [|constructor; [|constructor]]; cbn; (split;
        [refl_sub | cbn; split; [discriminate | exact I]]).
    - constructor; [discriminate|]. constructor; [discriminate | constructor]. }
  (* i3 = u.<@Imm>id2(i): the callee passes its own parameter on *)
  ty_seq.
  { apply call_id_typed with (qa := Imm) (md := id2_def);
      [right; split; reflexivity | wfenv | right; reflexivity | reflexivity
      | reflexivity | reflexivity | discriminate]. }
  (* v2 = v.<@Imm>self2(): an immutable receiver for a [Q] receiver *)
  apply call_self_typed with (qa := Imm) (md := self2_def);
    [right; split; reflexivity | wfenv | right; reflexivity | reflexivity
    | reflexivity | discriminate].
Qed.

(** The call of [self] on the mutable [u] with [Q := @Mut]. *)
Lemma callS_typed : stmt_typing CT Δ0 sΓfinal AbstractState callS sΓfinal.
Proof.
  unfold callS, sΓfinal.
  apply call_self_typed with (qa := Mut) (md := self_def);
    [left; split; reflexivity | wfenv | left; reflexivity | reflexivity
    | reflexivity | discriminate].
Qed.

(** The call of [peek] with [Q := @Mut]: a mutable cell is passed where
    [[Q]Cell] is expected. *)
Lemma callP_typed : stmt_typing CT Δ0 sΓfinal AbstractState callP sΓfinal.
Proof.
  unfold callP, sΓfinal.
  eapply ST_Call with (Tx := ROObject) (Ty := MutUtil) (argtypes := [MutCell])
    (qy := Mut) (C := 3) (Ts := []) (D := 3) (Vs := []) (mdef := peek_def);
    [wfenv | reflexivity | reflexivity | reflexivity | reflexivity
    | | | discriminate | | | reflexivity | | | | | apply method_rs_as
    | reflexivity |  | recv_known].
  - eapply FOM_Here; reflexivity.
  - apply si_refl.
  - constructor.
  - constructor.
  - constructor.
  - cbn. refl_sub.
  - cbn. split.
    + apply qtype_qual; [cbn; lia | qs | constructor].
    + cbn. discriminate.
  - constructor; [|constructor]. cbn. split.
    + refl_sub.
    + cbn. split; [discriminate | exact I].
  - constructor; [discriminate | constructor].
Qed.

(** The call of [self] on [su], whose static type is [@Mut Util]: it is
    checked against [Util.self]. *)
Lemma callO_typed : stmt_typing CT Δ0 sΓfinal AbstractState callO sΓfinal.
Proof.
  unfold callO, sΓfinal.
  apply call_self_typed with (qa := Mut) (md := self_def);
    [left; split; reflexivity | wfenv | left; reflexivity | reflexivity
    | reflexivity | discriminate].
Qed.

Lemma poly_main_typed : stmt_typing CT Δ0 sΓ0 AbstractState main sΓfinal.
Proof.
  unfold main. eapply ST_Seq; [| apply prefix_typed |].
  - split; [cbn; lia|]. constructor; [wfu | constructor].
  - eapply ST_Seq; [unfold sΓfinal; wfenv | apply callP_typed |].
    eapply ST_Seq; [| apply callS_typed | apply callO_typed].
    unfold sΓfinal. wfenv.
Qed.

(* ------------------NEGATIVE CHECKS------------------*)

(** Nothing mutable is below-or-equal a type whose qualifier is a qualifier
    parameter: from [[Q]C<..>] only [[Q]..] types and readonly class types
    are reached. *)
Definition head_or_ro (T : qualified_type) : Prop :=
  (exists n C Ts, T = THead n C Ts) \/ (exists C Ts, T = TClass RO C Ts).

Lemma head_or_ro_closed : forall CT0 Δ T U,
  qualified_type_subtype CT0 Δ T U -> head_or_ro T -> head_or_ro U.
Proof.
  intros CT0 Δ T U H.
  induction H; intros [(n0 & C0 & Ts0 & E) | (C0 & Ts0 & E)];
    try discriminate.
  - injection E as -> -> ->. right. inversion Hqsub; subst; eauto.
  - injection E as -> -> ->. right. eauto.
  - right. eauto.
  - left. eauto 6.
  - left. eauto 6.
  - apply IHqualified_type_subtype2. apply IHqualified_type_subtype1.
    left. eauto 6.
  - apply IHqualified_type_subtype2. apply IHqualified_type_subtype1.
    right. eauto.
Qed.

(** So a value held at [[Q]Box] cannot be passed where [@Mut Box] or
    [@Imm Box] is expected: the body of a qualifier-polymorphic method cannot
    assume what [Q] stands for. *)
Theorem head_not_mut : forall Δ n C Ts q0 D Us,
  q0 <> RO ->
  ~ qualified_type_subtype CT Δ (THead n C Ts) (TClass q0 D Us).
Proof.
  intros Δ n C Ts q0 D Us Hq H.
  apply head_or_ro_closed in H; [|left; eauto 6].
  destruct H as [(n1 & C1 & Ts1 & E) | (C1 & Ts1 & E)]; [discriminate|].
  injection E as -> _ _. congruence.
Qed.

(** A qualifier parameter is not a type: inside a method whose only
    parameter is the qualifier parameter [Q], there is no type variable to
    write, so [Q] cannot be used as the type of a variable or as a type
    argument. *)
Example qparam_is_not_a_type : forall m top u o n,
  ~ wf_stype CT (ΔQ m) top (TVar u o n).
Proof.
  intros m top u o n H. inversion H; subst.
  destruct o; destruct n; discriminate.
Qed.

(** Only a declared qualifier parameter may be written in the brackets. *)
Example undeclared_qparam_rejected : forall m top C Ts,
  ~ wf_stype CT (ΔQ m) top (THead 1 C Ts).
Proof.
  intros m top C Ts H. inversion H; subst. cbn in *. lia.
Qed.

(** A qualifier argument is a qualifier or a qualifier parameter in scope;
    [@Lost] is not accepted, and neither is a parameter that is not
    declared. *)
Example qarg_lost_rejected : forall Δ, ~ qarg_ok Δ (QLit Lost).
Proof. intros Δ H. apply H. reflexivity. Qed.

Example qarg_undeclared_rejected : ~ qarg_ok Δ0 (QVar 0).
Proof. cbn. lia. Qed.

(** A call must supply exactly as many qualifier arguments as the method
    declares: [u.id(m)] without one is not typable. *)
Example call_without_qarg_untypable : forall sΓ sΓ',
  static_getType sΓ 3 = Some MutUtil ->
  ~ stmt_typing CT Δ0 sΓ AbstractState (SCall 4 id_name 3 [] [] [1]) sΓ'.
Proof.
  intros sΓ sΓ' Hu H. inversion H; subst.
  rewrite Hu in Hget_y. injection Hget_y as <-.
  cbn in Hub. injection Hub as <- <- <-.
  assert (Hh : FindMethodWithName CT 3 id_name 3 id_def)
    by (eapply FOM_Here; reflexivity).
  destruct (find_method_with_name_deterministic _ _ _ _ _ _ _ Hfind_m Hh)
    as [-> ->].
  cbn in Hqargs_len. discriminate.
Qed.

(* ------------------EVALUATION------------------*)

Definition rΓ0 : r_env := mkr_env [Iot 0] [] [] [].
Definition h0 : heap := [mkObj (mkruntime_type Mut_r 0 []) []].

(* Before the call of peek: r is still null *)
Definition rΓA : r_env :=
  mkr_env [Iot 0; Iot 1; Iot 2; Iot 3; Iot 1; Iot 2; Iot 4; Iot 5; Null_a;
           Iot 1; Iot 2; Null_a; Iot 6; Iot 6; Iot 7; Null_a] [] [] [].

(* After the call of peek: r is the cell's item *)
Definition rΓB : r_env :=
  mkr_env [Iot 0; Iot 1; Iot 2; Iot 3; Iot 1; Iot 2; Iot 4; Iot 5; Iot 4;
           Iot 1; Iot 2; Null_a; Iot 6; Iot 6; Iot 7; Null_a] [] [] [].

(* After the call of Sub.self: u3 is su *)
Definition rΓfinal : r_env :=
  mkr_env [Iot 0; Iot 1; Iot 2; Iot 3; Iot 1; Iot 2; Iot 4; Iot 5; Iot 4;
           Iot 1; Iot 2; Iot 3; Iot 6; Iot 6; Iot 7; Iot 7] [] [] [].

(* After the call of self: u2 is u *)
Definition rΓC : r_env :=
  mkr_env [Iot 0; Iot 1; Iot 2; Iot 3; Iot 1; Iot 2; Iot 4; Iot 5; Iot 4;
           Iot 1; Iot 2; Iot 3; Iot 6; Iot 6; Iot 7; Null_a] [] [] [].

(* The cell is at location 5 and its item is the object at location 4 *)
Definition hfinal : heap :=
  [ mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 1 []) [];
    mkObj (mkruntime_type Imm_r 1 []) [];
    mkObj (mkruntime_type Mut_r 3 []) [];
    mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 2 []) [Iot 4];
    mkObj (mkruntime_type Imm_r 3 []) [];
    mkObj (mkruntime_type Mut_r 4 []) [] ].

Ltac ev_local := eapply SBS_Seq; [apply SBS_Local; reflexivity|]; cbn.

Ltac ev_id :=
  eapply SBS_Call with (mdef := id_def) (D := 3);
    [ reflexivity | reflexivity | eapply FOM_Here; reflexivity
    | reflexivity | reflexivity | reflexivity
    | unfold callee_env; do 4 eexists;
      split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
      split; [apply rsi_refl | reflexivity]
    | cbn; apply SBS_Skip | reflexivity | reflexivity ].

Ltac ev_self :=
  eapply SBS_Call with (mdef := self_def) (D := 3);
    [ reflexivity | reflexivity | eapply FOM_Here; reflexivity
    | reflexivity | reflexivity | reflexivity
    | unfold callee_env; do 4 eexists;
      split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
      split; [apply rsi_refl | reflexivity]
    | cbn; apply SBS_Skip | reflexivity | reflexivity ].

Lemma prefix_eval : eval_stmt CT rΓ0 h0 prefix OK rΓA hfinal.
Proof.
  unfold prefix, rΓ0, h0.
  ev_local. ev_local. ev_local. ev_local. ev_local. ev_local. ev_local.
  ev_local. ev_local. ev_local. ev_local. ev_local. ev_local. ev_local.
  ev_local.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq; [eapply SBS_New; reflexivity|]. cbn.
  eapply SBS_Seq; [ev_id|]. cbn.
  eapply SBS_Seq; [ev_id|]. cbn.
  eapply SBS_Seq.
  { eapply SBS_Call with (mdef := first_def) (D := 3);
      [ reflexivity | reflexivity | eapply FOM_Here; reflexivity
      | reflexivity | reflexivity | reflexivity
      | unfold callee_env; do 4 eexists;
        split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
        split; [apply rsi_refl | reflexivity]
      | cbn; apply SBS_Skip | reflexivity | reflexivity ]. }
  cbn.
  eapply SBS_Seq.
  { eapply SBS_Call with (mdef := id2_def) (D := 3);
      [ reflexivity | reflexivity | eapply FOM_Here; reflexivity
      | reflexivity | reflexivity | reflexivity
      | unfold callee_env; do 4 eexists;
        split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
        split; [apply rsi_refl | reflexivity]
      | | | ].
    - cbn. eapply SBS_Seq; [apply SBS_Local; reflexivity|]. cbn. ev_id.
    - reflexivity.
    - reflexivity. }
  cbn.
  eapply SBS_Call with (mdef := self2_def) (D := 3);
    [ reflexivity | reflexivity | eapply FOM_Here; reflexivity
    | reflexivity | reflexivity | reflexivity
    | unfold callee_env; do 4 eexists;
      split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
      split; [apply rsi_refl | reflexivity]
    | | | ].
  - cbn. eapply SBS_Seq; [apply SBS_Local; reflexivity|]. cbn. ev_self.
  - reflexivity.
  - reflexivity.
Qed.

Lemma callS_eval : eval_stmt CT rΓB hfinal callS OK rΓC hfinal.
Proof. unfold callS, rΓB. ev_self. Qed.

(** The object is a [Sub]: the method that runs is [Sub.self]. *)
Lemma callO_eval : eval_stmt CT rΓC hfinal callO OK rΓfinal hfinal.
Proof.
  unfold callO, rΓC.
  eapply SBS_Call with (mdef := sub_self_def) (D := 4);
    [ reflexivity | reflexivity | eapply FOM_Here; reflexivity
    | reflexivity | reflexivity | reflexivity
    | unfold callee_env; do 4 eexists;
      split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
      split; [apply rsi_refl | reflexivity]
    | cbn; apply SBS_Skip | reflexivity | reflexivity ].
Qed.

Lemma callP_eval : eval_stmt CT rΓA hfinal callP OK rΓB hfinal.
Proof.
  unfold callP, rΓA.
  eapply SBS_Call with (mdef := peek_def) (D := 3);
    [ reflexivity | reflexivity | eapply FOM_Here; reflexivity
    | reflexivity | reflexivity | reflexivity
    | unfold callee_env; do 4 eexists;
      split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
      split; [apply rsi_refl | reflexivity]
    | | | ].
  - cbn. eapply SBS_Seq; [apply SBS_Local; reflexivity|]. cbn.
    eapply SBS_Assign; [reflexivity|].
    eapply EBS_Field; reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma poly_main_eval : eval_stmt CT rΓ0 h0 main OK rΓfinal hfinal.
Proof.
  unfold main. eapply SBS_Seq; [apply prefix_eval|].
  eapply SBS_Seq; [apply callP_eval|].
  eapply SBS_Seq; [apply callS_eval | apply callO_eval].
Qed.

(** Inside the first call the frame's argument for [Q] is [@Mut], and
    the parameter's type [[Q]Box] is read as [@Mut Box]; inside the second it
    is read as [@Imm Box]. *)
Example runtime_reading :
  dyn Mut [] [] [Mut] (tQ 1) = RClass Mut 1 [] /\
  dyn Mut [] [] [Imm] (tQ 1) = RClass Imm 1 [].
Proof. split; reflexivity. Qed.

(* ------------------THE THEOREMS APPLY------------------*)

Lemma poly_initial_config : wf_r_config CT Δ0 sΓ0 rΓ0 h0.
Proof.
  refine (conj poly_ct_wf (conj _ (conj _ (conj _ (conj _ (conj eq_refl _)))))).
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
  - split; simpl; [lia|]. constructor; [wfu | constructor].
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

(** Type preservation applies to the run: the final state is well formed,
    with [m2] a mutable box and [i2] an immutable one. *)
Corollary poly_final_config : wf_r_config CT Δ0 sΓfinal rΓfinal hfinal.
Proof.
  eapply preservation_pico;
    eauto using poly_main_eval, poly_initial_config, poly_main_typed.
Qed.

(* ------------------THE READONLY-STATE THEOREM APPLIES------------------*)

(** No readonly-state method has a type parameter in scope: a qualifier
    parameter is not a type parameter and has no bound. *)
Theorem poly_ct_clean_bounds : clean_bounds_ct CT.
Proof.
  intros C def md Hfind Hin Hrs.
  assert (Hq : forall m k, GhostFit.nomut_bounds (mk_tv_env [] [] m k)).
  { intros m k o n B Hb. destruct o; destruct n; discriminate. }
  destruct C as [|[|[|[|[|C]]]]]; cbn in Hfind;
    try (injection Hfind as <-; cbn in Hin).
  - destruct Hin.
  - destruct Hin.
  - destruct Hin.
  - destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; apply Hq.
  - destruct Hin as [<- | [<- | []]]; apply Hq.
  - destruct C; discriminate.
Qed.

Theorem config_A : wf_r_config CT Δ0 sΓfinal rΓA hfinal.
Proof.
  eapply preservation_pico;
    eauto using prefix_eval, poly_initial_config, prefix_typed.
Qed.

Lemma initial_rsf : RSF CT Δ0 rΓ0 h0.
Proof.
  split.
  - apply rsfit_heap_intro. intros l o def Ho Hfc L o' n B Hb.
    destruct (tv_bound_class_env _ _ _ _ Hb) as [_ Hn].
    destruct l as [|l]; cbn in Ho; [injection Ho as <- | destruct l; discriminate].
    cbn in Hfc. injection Hfc as <-. cbn in Hn. destruct n; discriminate.
  - intros ι o _ _ L o' n B Hb. destruct o'; destruct n; discriminate.
Qed.

Lemma initial_rsfp : RSFp CT Δ0 rΓ0 h0.
Proof.
  apply RSFp_start; [exact initial_rsf | reflexivity | reflexivity |].
  intros l o def Ho Hfc.
  destruct l as [|l]; cbn in Ho; [injection Ho as <- | destruct l; discriminate].
  cbn in Hfc. injection Hfc as <-. reflexivity.
Qed.

Theorem rsfp_A : RSFp CT Δ0 rΓA hfinal.
Proof.
  exact (rsfp_preservation CT Δ0 sΓ0 AbstractState prefix sΓfinal rΓ0 h0 rΓA
           hfinal poly_initial_config prefix_typed prefix_eval initial_rsfp).
Qed.

Lemma item_is_rda : sf_assignability_rel CT 2 0 RDA.
Proof.
  exists item_field. split; [|reflexivity].
  eapply FL_Found; [apply collect_Cell | reflexivity].
Qed.

(** The readonly-state theorem applied to the call of [peek]: whatever the
    call does, no final or receiver-dependent-assignable field of any object
    of the entry heap changes.  The qualifier parameter is instantiated with
    [@Mut] and the cell passed in is mutable. *)
Theorem callP_preserves : forall rΓ' h',
  eval_stmt CT rΓA hfinal callP OK rΓ' h' ->
  forall l qr C Rs vals f,
    runtime_getObj hfinal l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
    (sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA) ->
    exists vals',
      runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
      nth_error vals f = nth_error vals' f.
Proof.
  intros rΓ' h' Heval.
  eapply (readonly_state_preservation_final CT Δ0 sΓfinal AbstractState rΓA
            hfinal 8 peek_name 3 [] [QLit Mut] [7] sΓfinal rΓ' h' 3 3 3 peek_def
            poly_ct_clean_bounds config_A rsfp_A callP_typed Heval).
  - reflexivity.
  - reflexivity.
  - eapply FOM_Here; reflexivity.
  - left. reflexivity.
Qed.

(** In particular the mutable cell that was passed for the [[Q]Cell]
    parameter keeps its item. *)
Theorem callP_preserves_item : forall rΓ' h',
  eval_stmt CT rΓA hfinal callP OK rΓ' h' ->
  exists vals',
    runtime_getObj h' 5 = Some (mkObj (mkruntime_type Mut_r 2 []) vals') /\
    nth_error vals' 0 = Some (Iot 4).
Proof.
  intros rΓ' h' Heval.
  destruct (callP_preserves rΓ' h' Heval 5 Mut_r 2 [] [Iot 4] 0 eq_refl
              (or_intror item_is_rda))
    as (vals' & Hobj & Hnth).
  exists vals'. split; [exact Hobj|]. symmetry. exact Hnth.
Qed.

(** The statement is not vacuous: the call does run. *)
Theorem callP_runs : exists rΓ' h', eval_stmt CT rΓA hfinal callP OK rΓ' h'.
Proof. exists rΓB, hfinal. apply callP_eval. Qed.

(** The same for the call of [self]: its receiver is the mutable [u], its
    declared receiver type is [[Q]Util], and [Q] is instantiated with
    [@Mut]. *)
Theorem config_B : wf_r_config CT Δ0 sΓfinal rΓB hfinal.
Proof.
  eapply preservation_pico;
    eauto using callP_eval, config_A, callP_typed.
Qed.

Theorem rsfp_B : RSFp CT Δ0 rΓB hfinal.
Proof.
  exact (rsfp_preservation CT Δ0 sΓfinal AbstractState callP sΓfinal rΓA hfinal
           rΓB hfinal config_A callP_typed callP_eval rsfp_A).
Qed.

Theorem callS_preserves_item : forall rΓ' h',
  eval_stmt CT rΓB hfinal callS OK rΓ' h' ->
  exists vals',
    runtime_getObj h' 5 = Some (mkObj (mkruntime_type Mut_r 2 []) vals') /\
    nth_error vals' 0 = Some (Iot 4).
Proof.
  intros rΓ' h' Heval.
  destruct (readonly_state_preservation_final CT Δ0 sΓfinal AbstractState rΓB
              hfinal 11 self_name 3 [] [QLit Mut] [] sΓfinal rΓ' h' 3 3 3 self_def
              poly_ct_clean_bounds config_B rsfp_B callS_typed Heval
              eq_refl eq_refl ltac:(eapply FOM_Here; reflexivity)
              (or_introl eq_refl)
              5 Mut_r 2 [] [Iot 4] 0 eq_refl (or_intror item_is_rda))
    as (vals' & Hobj & Hnth).
  exists vals'. split; [exact Hobj|]. symmetry. exact Hnth.
Qed.

Theorem callS_runs : exists rΓ' h', eval_stmt CT rΓB hfinal callS OK rΓ' h'.
Proof. exists rΓC, hfinal. apply callS_eval. Qed.

(** The same for the overriding method: the call is checked against
    [Util.self], runs [Sub.self], and the readonly-state theorem applies. *)
Theorem config_C : wf_r_config CT Δ0 sΓfinal rΓC hfinal.
Proof.
  eapply preservation_pico;
    eauto using callS_eval, config_B, callS_typed.
Qed.

Theorem rsfp_C : RSFp CT Δ0 rΓC hfinal.
Proof.
  exact (rsfp_preservation CT Δ0 sΓfinal AbstractState callS sΓfinal rΓB hfinal
           rΓC hfinal config_B callS_typed callS_eval rsfp_B).
Qed.

Theorem callO_preserves_item : forall rΓ' h',
  eval_stmt CT rΓC hfinal callO OK rΓ' h' ->
  exists vals',
    runtime_getObj h' 5 = Some (mkObj (mkruntime_type Mut_r 2 []) vals') /\
    nth_error vals' 0 = Some (Iot 4).
Proof.
  intros rΓ' h' Heval.
  destruct (readonly_state_preservation_final CT Δ0 sΓfinal AbstractState rΓC
              hfinal 15 self_name 14 [] [QLit Mut] [] sΓfinal rΓ' h' 7 4 4
              sub_self_def
              poly_ct_clean_bounds config_C rsfp_C callO_typed Heval
              eq_refl eq_refl ltac:(eapply FOM_Here; reflexivity)
              (or_introl eq_refl)
              5 Mut_r 2 [] [Iot 4] 0 eq_refl (or_intror item_is_rda))
    as (vals' & Hobj & Hnth).
  exists vals'. split; [exact Hobj|]. symmetry. exact Hnth.
Qed.

Theorem callO_runs : exists rΓ' h', eval_stmt CT rΓC hfinal callO OK rΓ' h'.
Proof. exists rΓfinal, hfinal. apply callO_eval. Qed.

Print Assumptions poly_final_config.
Print Assumptions head_not_mut.
Print Assumptions callP_preserves_item.
Print Assumptions callS_preserves_item.
Print Assumptions callO_preserves_item.
Print Assumptions head_write_untypable.
Print Assumptions call_without_qarg_untypable.
