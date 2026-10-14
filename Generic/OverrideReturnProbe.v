From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep.

(** Probe: can an override with a covariant return type leak a mutable view
    of a protected object into readonly-state code?

    class 0: @RDM class Object {}
    class 1: @RDM class Cell extends Object { @RDA @RO Object value; }
    class 2: @RDM class P<E extends @RO Object> extends Object { @RDA E item; }
    class 3: @RDM class C extends P<@Mut Cell> {}
    class 4: @RDM class Super<X extends @RO Object> extends Object {
        @RS @RO P<X> pick(@RO Super<X> this, @RO C c) { @RO P<X> r; return r; }
    }
    class 5: @RDM class Sub extends Super<@Mut Cell> {
        @RS @RO C pick(@RO Sub this, @RO C c) { return c; }
    }
    class 6: @RDM class Tool extends Object {
        @RS @RO Object hack(@RO Tool this, @RO C c, @RO Object y) {
            @Mut Sub s;                  // var 3
            @Mut Super<@Mut Cell> r;     // var 4
            @RO P<@Mut Cell> b;          // var 5
            @Mut Cell k;                 // var 6
            s = new @Mut Sub();
            r = s;
            b = r.pick(c);
            k = b.item;
            k.value = y;
            return y;
        }
    }

    Result.  Super.pick and Tool.hack are well formed.  Sub.pick is not: its
    return type is compared with the overridden return type in the bound
    environment of Sub.pick itself, whose mode is readonly-state, and in that
    mode a readonly C is a P<@Lost Cell>, not a P<@Mut Cell>.  So the class
    table is rejected, at the return-type premise of the override check. *)

(* ------------------THE PROGRAM------------------*)

Definition ROObject : qualified_type := TClass RO 0 [].
Definition MutCell : qualified_type := TClass Mut 1 [].
Definition LostCell : qualified_type := TClass Lost 1 [].
Definition ROC : qualified_type := TClass RO 3 [].
Definition tX : qualified_type := TVar TVSub ClassVar 0.
Definition ROPX : qualified_type := TClass RO 2 [tX].
Definition ROSuperX : qualified_type := TClass RO 4 [tX].
Definition ROPMutCell : qualified_type := TClass RO 2 [MutCell].
Definition ROPLostCell : qualified_type := TClass RO 2 [LostCell].
Definition ROSub : qualified_type := TClass RO 5 [].
Definition MutSub : qualified_type := TClass Mut 5 [].
Definition MutSuperMC : qualified_type := TClass Mut 4 [MutCell].
Definition ROTool : qualified_type := TClass RO 6 [].

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

Definition item_field : field_def :=
  {| assignability := RDA; ftype := tX |}.

Definition PDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 2;
                     ctparams := [ROObject];
                     super := Some (0, []) |};
     body := {| fields := [item_field]; methods := [] |} |}.

Definition CDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 3; ctparams := [];
                     super := Some (2, [MutCell]) |};
     body := {| fields := []; methods := [] |} |}.

(* @RS @RO P<X> pick(@RO Super<X> this, @RO C c) { @RO P<X> r; return r; } *)
Definition Super_pick : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mqparams := 0;
          mret := ROPX;
          mname := 0;
          mreceiver := ROSuperX;
          mparams := [ROC] |};
     mbody := {| mbody_stmt := SLocal ROPX 2; mreturn := 2 |} |}.

Definition SuperDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 4;
                     ctparams := [ROObject];
                     super := Some (0, []) |};
     body := {| fields := []; methods := [Super_pick] |} |}.

(* @RS @RO C pick(@RO Sub this, @RO C c) { return c; } *)
Definition Sub_pick : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mqparams := 0;
          mret := ROC;
          mname := 0;
          mreceiver := ROSub;
          mparams := [ROC] |};
     mbody := {| mbody_stmt := SSkip; mreturn := 1 |} |}.

Definition SubDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 5; ctparams := [];
                     super := Some (4, [MutCell]) |};
     body := {| fields := []; methods := [Sub_pick] |} |}.

Definition hack : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mqparams := 0;
          mret := ROObject;
          mname := 1;
          mreceiver := ROTool;
          mparams := [ROC; ROObject] |};
     mbody :=
       {| mbody_stmt :=
            SSeq (SLocal MutSub 3)
            (SSeq (SLocal MutSuperMC 4)
            (SSeq (SLocal ROPMutCell 5)
            (SSeq (SLocal MutCell 6)
            (SSeq (SNew 3 Mut_c 5 [] [])
            (SSeq (SVarAss 4 (EVar 3))
            (SSeq (SCall 5 0 4 [] [] [1])
            (SSeq (SVarAss 6 (EField 5 0))
                  (SFldWrite 6 0 2))))))));
          mreturn := 2 |} |}.

Definition ToolDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 6; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := []; methods := [hack] |} |}.

Definition CT : class_table :=
  [ObjectDef; CellDef; PDef; CDef; SuperDef; SubDef; ToolDef].

(* ------------------SMALL TACTICS AND FACTS------------------*)

Ltac qs := first [apply q_refl; discriminate | apply q_rd | apply q_bot].

(** Any non-lost qualifier on a class without type parameters is a
    well-formed type. *)
Lemma wf_plain : forall Δ top q0 C,
  (C = 0 \/ C = 1 \/ C = 3 \/ C = 5 \/ C = 6) -> q0 <> Lost ->
  wf_stype CT Δ top (TClass q0 C []).
Proof.
  intros Δ top q0 C HC Hq.
  destruct HC as [-> | [-> | [-> | [-> | ->]]]];
    (eapply wfs_class;
       [reflexivity | right | reflexivity | constructor | constructor]);
    destruct q0; cbn; try qs; congruence.
Qed.

(** P and Super take one argument bounded by @RO Object. *)
Lemma wf_one : forall Δ top q0 C T,
  (C = 2 \/ C = 4) -> q0 <> Lost ->
  wf_stype CT Δ false T ->
  bound_sub CT Δ T ROObject ->
  wf_stype CT Δ top (TClass q0 C [T]).
Proof.
  intros Δ top q0 C T HC Hq HT Hsub.
  assert (Hh : q_subtype (vpa_mutability_bound q0 RDM_c) q0)
    by (destruct q0; cbn; try qs; congruence).
  destruct HC as [-> | ->].
  - eapply wfs_class with (def := PDef);
      [reflexivity | right; exact Hh | reflexivity
      | constructor; [exact HT | constructor] | ].
    cbn. constructor; [|constructor].
    destruct q0; exact Hsub.
  - eapply wfs_class with (def := SuperDef);
      [reflexivity | right; exact Hh | reflexivity
      | constructor; [exact HT | constructor] | ].
    cbn. constructor; [|constructor].
    destruct q0; exact Hsub.
Qed.

Lemma sub_MutCell_ROObject : forall Δ,
  qualified_type_subtype CT Δ MutCell ROObject.
Proof.
  intros Δ. eapply qtype_trans.
  - apply qtype_hier with (D := 0) (Vs := []).
    eapply si_step; [reflexivity|]. cbn. apply si_refl.
  - apply qtype_qual; [cbn; lia | apply q_rd | constructor].
Qed.

Lemma wf_ROObject : forall Δ, wf_stypeuse CT Δ ROObject.
Proof. intros. apply wf_plain; [auto | discriminate]. Qed.
Lemma wf_ROC : forall Δ, wf_stypeuse CT Δ ROC.
Proof. intros. apply wf_plain; [auto | discriminate]. Qed.
Lemma wf_ROSub : forall Δ, wf_stypeuse CT Δ ROSub.
Proof. intros. apply wf_plain; [auto 6 | discriminate]. Qed.
Lemma wf_MutSub : forall Δ, wf_stypeuse CT Δ MutSub.
Proof. intros. apply wf_plain; [auto 6 | discriminate]. Qed.
Lemma wf_ROTool : forall Δ, wf_stypeuse CT Δ ROTool.
Proof. intros. apply wf_plain; [auto 6 | discriminate]. Qed.
Lemma wf_MutCell : forall Δ top, wf_stype CT Δ top MutCell.
Proof. intros. apply wf_plain; [auto | discriminate]. Qed.
Lemma wf_ROPMutCell : forall Δ, wf_stypeuse CT Δ ROPMutCell.
Proof.
  intros. apply wf_one; [auto | discriminate | apply wf_MutCell
                        | intros m; apply sub_MutCell_ROObject].
Qed.
Lemma wf_MutSuperMC : forall Δ, wf_stypeuse CT Δ MutSuperMC.
Proof.
  intros. apply wf_one; [auto | discriminate | apply wf_MutCell
                        | intros m; apply sub_MutCell_ROObject].
Qed.

Ltac wft :=
  first [apply wf_ROObject | apply wf_ROC | apply wf_ROSub | apply wf_MutSub
        | apply wf_ROTool | apply wf_MutCell | apply wf_ROPMutCell
        | apply wf_MutSuperMC].

Ltac wfenv :=
  split; [cbn; lia |
          repeat (apply Forall_cons; [solve [wft]|]); apply Forall_nil].

Ltac refl_sub :=
  apply qualified_type_subtype_refl_class; [cbn; lia | discriminate].

Lemma collect_Object : CollectFields CT 0 [].
Proof. eapply CF_Object; reflexivity. Qed.

Lemma collect_Cell : CollectFields CT 1 [value_field].
Proof.
  change (CollectFields CT 1
            (map (subst_field []) [] ++ Syntax.fields (body CellDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma collect_P : CollectFields CT 2 [item_field].
Proof.
  change (CollectFields CT 2
            (map (subst_field []) [] ++ Syntax.fields (body PDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma collect_Super : CollectFields CT 4 [].
Proof.
  change (CollectFields CT 4
            (map (subst_field []) [] ++ Syntax.fields (body SuperDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma collect_Sub : CollectFields CT 5 [].
Proof.
  change (CollectFields CT 5
            (map (subst_field [MutCell]) [] ++ Syntax.fields (body SubDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Super.
Qed.

Lemma no_method_in_Object : forall m D mdef,
  ~ FindMethodWithName CT 0 m D mdef.
Proof.
  intros m D mdef H. inversion H; subst.
  - cbn in Hfind. injection Hfind as <-. cbn in Hget_method. discriminate.
  - cbn in Hfind. injection Hfind as <-. cbn in Hsuper. discriminate.
Qed.

Lemma find_pick_in_Super : FindMethodWithName CT 4 0 4 Super_pick.
Proof. eapply FOM_Here; reflexivity. Qed.

(* ------------------1. SUPER.PICK IS WELL FORMED------------------*)

Definition ΔS : tv_env := mk_tv_env [ROObject] [] ReadonlyState 0.

Lemma wf_ROPX : wf_stypeuse CT ΔS ROPX.
Proof.
  apply wf_one; [auto | discriminate | | ].
  - eapply wfs_var; [reflexivity | left; reflexivity].
  - intros m. apply qtype_var_bound. reflexivity.
Qed.

Lemma wf_ROSuperX : wf_stypeuse CT ΔS ROSuperX.
Proof.
  apply wf_one; [auto | discriminate | | ].
  - eapply wfs_var; [reflexivity | left; reflexivity].
  - intros m. apply qtype_var_bound. reflexivity.
Qed.

Theorem Super_pick_wf : wf_method CT 4 Super_pick.
Proof.
  unfold wf_method.
  change (method_tv_env CT 4 (msignature Super_pick)) with ΔS.
  cbv zeta.
  assert (Hwf1 : wf_senv CT ΔS [ROSuperX; ROC]).
  { split; [cbn; lia|].
    constructor; [apply wf_ROSuperX|]. constructor; [apply wf_ROC | constructor]. }
  split; [apply receiver_plain_ok; left; exists RO; reflexivity|].
  split; [constructor|].
  split; [apply wf_ROPX|].
  split.
  { exists [ROSuperX; ROC; ROPX], ROPX. split; [|split].
    - eapply ST_Local; [exact Hwf1 | apply wf_ROPX | | reflexivity |]; reflexivity.
    - reflexivity.
    - refl_sub. }
  split.
  { intros def parent Ss D mdef_parent Vs Hfind Hsuper Hfm _.
    cbn in Hfind. injection Hfind as <-. cbn in Hsuper.
    injection Hsuper as <- <-.
    exfalso. eapply no_method_in_Object; eauto. }
  intros _. split.
  - apply nm_class; [discriminate|].
    constructor; [|constructor].
    eapply nm_var; [reflexivity|].
    apply nm_class; [discriminate | constructor].
  - constructor; [|constructor].
    apply nm_class; [discriminate | constructor].
Qed.

(* ------------------2. TOOL.HACK IS WELL FORMED------------------*)

(** The caller is accepted on its own: the call through
    @Mut Super<@Mut Cell> has result type @RO P<@Mut Cell>, reading item from
    that gives @Mut Cell, and the write to value is allowed. *)

Definition Δh : tv_env := mk_tv_env [] [] ReadonlyState 0.

Definition G0 : s_env := [ROTool; ROC; ROObject].
Definition G1 : s_env := G0 ++ [MutSub].
Definition G2 : s_env := G1 ++ [MutSuperMC].
Definition G3 : s_env := G2 ++ [ROPMutCell].
Definition G4 : s_env := G3 ++ [MutCell].

Lemma wf_G0 : wf_senv CT Δh G0. Proof. wfenv. Qed.
Lemma wf_G1 : wf_senv CT Δh G1. Proof. wfenv. Qed.
Lemma wf_G2 : wf_senv CT Δh G2. Proof. wfenv. Qed.
Lemma wf_G3 : wf_senv CT Δh G3. Proof. wfenv. Qed.
Lemma wf_G4 : wf_senv CT Δh G4. Proof. wfenv. Qed.

(** The result type of r.pick(c) seen by the caller. *)
Lemma call_result_type :
  member_type ReadonlyState Mut [MutCell] [] [] (mret (msignature Super_pick))
  = ROPMutCell.
Proof. reflexivity. Qed.

(** Reading item through @RO P<@Mut Cell> in readonly-state code. *)
Lemma item_read_type :
  member_type ReadonlyState RO [MutCell] [] [] (ftype item_field) = MutCell.
Proof. reflexivity. Qed.

Lemma hack_new_typed :
  stmt_typing CT Δh G4 ReadonlyState (SNew 3 Mut_c 5 [] []) G4.
Proof.
  eapply ST_New with (Tx := MutSub) (argtypes := []) (def := SubDef) (fds := []);
    [apply wf_G4 | reflexivity | reflexivity | reflexivity | discriminate
    | reflexivity | apply wf_MutSub | constructor | constructor
    | apply collect_Sub | constructor | refl_sub].
Qed.

Lemma hack_upcast_typed :
  stmt_typing CT Δh G4 ReadonlyState (SVarAss 4 (EVar 3)) G4.
Proof.
  eapply ST_VarAss with (Tx := MutSuperMC) (Te := MutSub);
    [apply wf_G4 | apply ET_Var; [apply wf_G4 | reflexivity]
    | discriminate | reflexivity | ].
  apply qtype_hier.
  eapply si_step; [reflexivity|]. cbn. apply si_refl.
Qed.

Lemma hack_call_typed :
  stmt_typing CT Δh G4 ReadonlyState (SCall 5 0 4 [] [] [1]) G4.
Proof.
  eapply ST_Call with (argtypes := [ROC]) (Tx := ROPMutCell) (Ty := MutSuperMC)
    (qy := Mut) (C := 4) (Ts := [MutCell]) (D := 4) (Vs := [MutCell])
    (mdef := Super_pick).
  - apply wf_G4.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply find_pick_in_Super.
  - apply si_refl.
  - discriminate.
  - constructor.
  - constructor.
  - reflexivity.
  - constructor.
  - rewrite call_result_type. refl_sub.
  - split.
    + change (qualified_type_subtype CT Δh MutSuperMC (TClass RO 4 [MutCell])).
      apply qtype_qual; [cbn; lia | apply q_rd | apply Forall2_targ_sub_refl].
    + cbn. intuition discriminate.
  - constructor; [|constructor]. split.
    + change (qualified_type_subtype CT Δh ROC ROC). refl_sub.
    + cbn. intuition discriminate.
  - apply method_subtyping_refl.
  - reflexivity.
  - constructor.
  - recv_known.
Qed.

Lemma hack_read_typed :
  stmt_typing CT Δh G4 ReadonlyState (SVarAss 6 (EField 5 0)) G4.
Proof.
  assert (He : expr_has_type CT Δh G4 ReadonlyState (EField 5 0)
                 (member_type ReadonlyState RO [MutCell] [] [] (ftype item_field))).
  { eapply ET_Field with (T := ROPMutCell) (C := 2);
      [apply wf_G4 | reflexivity | reflexivity |].
    eapply FL_Found; [apply collect_P | reflexivity]. }
  rewrite item_read_type in He.
  eapply ST_VarAss with (Tx := MutCell) (Te := MutCell);
    [apply wf_G4 | exact He | discriminate | reflexivity | refl_sub].
Qed.

Lemma hack_write_typed :
  stmt_typing CT Δh G4 ReadonlyState (SFldWrite 6 0 2) G4.
Proof.
  eapply ST_FldWrite with (Tx := MutCell) (Ty := ROObject) (qx := Mut)
    (C := 1) (Ts := []) (fieldT := value_field);
    [apply wf_G4 | reflexivity | reflexivity | reflexivity
    | eapply FL_Found; [apply collect_Cell | reflexivity] | | reflexivity].
  split.
  - change (qualified_type_subtype CT Δh ROObject ROObject). refl_sub.
  - cbn. intuition discriminate.
Qed.

Lemma hack_body_typed :
  stmt_typing CT Δh G0 ReadonlyState (mbody_stmt (mbody hack)) G4.
Proof.
  cbn [mbody_stmt mbody hack].
  eapply ST_Seq; [apply wf_G0 | |].
  { eapply ST_Local with (sΓ' := G1);
      [apply wf_G0 | apply wf_MutSub | reflexivity | reflexivity | reflexivity]. }
  eapply ST_Seq; [apply wf_G1 | |].
  { eapply ST_Local with (sΓ' := G2);
      [apply wf_G1 | apply wf_MutSuperMC | reflexivity | reflexivity | reflexivity]. }
  eapply ST_Seq; [apply wf_G2 | |].
  { eapply ST_Local with (sΓ' := G3);
      [apply wf_G2 | apply wf_ROPMutCell | reflexivity | reflexivity | reflexivity]. }
  eapply ST_Seq; [apply wf_G3 | |].
  { eapply ST_Local with (sΓ' := G4);
      [apply wf_G3 | apply wf_MutCell | reflexivity | reflexivity | reflexivity]. }
  eapply ST_Seq; [apply wf_G4 | apply hack_new_typed |].
  eapply ST_Seq; [apply wf_G4 | apply hack_upcast_typed |].
  eapply ST_Seq; [apply wf_G4 | apply hack_call_typed |].
  eapply ST_Seq; [apply wf_G4 | apply hack_read_typed | apply hack_write_typed].
Qed.

Theorem hack_wf : wf_method CT 6 hack.
Proof.
  unfold wf_method.
  change (method_tv_env CT 6 (msignature hack)) with Δh.
  cbv zeta.
  split; [apply receiver_plain_ok; left; exists RO; reflexivity|].
  split; [constructor|].
  split; [apply wf_ROObject|].
  split.
  { exists G4, ROObject. split; [|split].
    - apply hack_body_typed.
    - reflexivity.
    - change (qualified_type_subtype CT Δh ROObject ROObject). refl_sub. }
  split.
  { intros def parent Ss D mdef_parent Vs Hfind Hsuper Hfm _.
    cbn in Hfind. injection Hfind as <-. cbn in Hsuper.
    injection Hsuper as <- <-.
    exfalso. eapply no_method_in_Object; eauto. }
  intros _. split.
  - apply nm_class; [discriminate | constructor].
  - constructor; [apply nm_class; [discriminate | constructor]|].
    constructor; [apply nm_class; [discriminate | constructor] | constructor].
Qed.

(* ------------------3. SUB.PICK IS REJECTED------------------*)

(** The classes and argument lists a readonly C can be viewed at in
    readonly-state or transitive-state code. *)
Definition reach (C : class_name) (Ts : list qualified_type) : Prop :=
  (C = 3 /\ Ts = []) \/ (C = 2 /\ Ts = [LostCell]) \/ (C = 0 /\ Ts = []).

Lemma super_inst_reach : forall mt,
  readonly_state_method_scope mt ->
  forall C Ts D Vs,
  super_inst CT mt RO C Ts D Vs ->
  reach C Ts -> reach D Vs.
Proof.
  intros mt [-> | ->] C Ts D Vs H; induction H; intros Hr; try exact Hr;
    apply IHsuper_inst;
    destruct Hr as [[-> ->] | [[-> ->] | [-> ->]]]; cbn in Hparent;
    try discriminate; injection Hparent as <- <-; unfold reach; cbn; auto.
Qed.

Definition sup_ROC (T : qualified_type) : Prop :=
  T = TClass RO 3 [] \/
  T = TClass RO 2 [TClass Lost 1 []] \/
  T = TClass RO 0 [].

Lemma sup_ROC_closed : forall Δ,
  readonly_state_method_scope (tv_mode Δ) ->
  forall T U, qualified_type_subtype CT Δ T U -> sup_ROC T -> sup_ROC U.
Proof.
  intros Δ Hmode T U H.
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
        (split; [reflexivity|]); unfold reach; auto. }
    destruct Hr as [-> Hr].
    destruct (super_inst_reach _ Hmode _ _ _ _ Hsuper Hr)
      as [[-> ->] | [[-> ->] | [-> ->]]]; unfold sup_ROC; auto.
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

(** In readonly-state or transitive-state code every supertype of @RO C is
    @RO C, @RO P<@Lost Cell>, or @RO Object. *)
Theorem supertypes_of_ROC : forall Δ U,
  readonly_state_method_scope (tv_mode Δ) ->
  qualified_type_subtype CT Δ ROC U ->
  U = ROC \/ U = ROPLostCell \/ U = ROObject.
Proof.
  intros Δ U Hmode H.
  apply (sup_ROC_closed Δ Hmode _ _ H). left. reflexivity.
Qed.

Theorem upcast_rejected : forall Δ,
  readonly_state_method_scope (tv_mode Δ) ->
  ~ qualified_type_subtype CT Δ ROC ROPMutCell.
Proof.
  intros Δ Hmode H.
  destruct (supertypes_of_ROC Δ _ Hmode H) as [E | [E | E]]; discriminate.
Qed.

(** What the override check asks of Sub.pick's return type.  [Vs] is how
    Sub sees Super's type parameter; the overridden return type @RO P<X> is
    seen as @RO P<@Mut Cell>. *)
Lemma Sub_sees_Super :
  super_inst CT AbstractState (qc2q (class_qualifier (signature SubDef))) 5
    (class_var_types (length (ctparams (signature SubDef)))) 4 [MutCell].
Proof. eapply si_step; [reflexivity|]. cbn. apply si_refl. Qed.

Lemma overridden_return_view :
  member_type AbstractState (qc2q (class_qualifier (signature SubDef)))
    [MutCell]
    (method_var_types (length (mtparams (msignature Super_pick)))) (qvar_args (mqparams (msignature Super_pick)))
    (mret (msignature Super_pick))
  = ROPMutCell.
Proof. reflexivity. Qed.

(** The check runs in Sub.pick's own bound environment, whose mode is
    readonly-state. *)
Lemma Sub_pick_env :
  method_tv_env CT 5 (msignature Sub_pick) = mk_tv_env [] [] ReadonlyState 0.
Proof. reflexivity. Qed.

(** The return-type premise of the override check fails. *)
Theorem Sub_pick_return_premise_fails :
  ~ qualified_type_subtype CT (method_tv_env CT 5 (msignature Sub_pick))
      (mret (msignature Sub_pick))
      (member_type AbstractState (qc2q (class_qualifier (signature SubDef)))
         [MutCell]
         (method_var_types (length (mtparams (msignature Super_pick)))) (qvar_args (mqparams (msignature Super_pick)))
         (mret (msignature Super_pick))).
Proof.
  rewrite overridden_return_view. rewrite Sub_pick_env.
  apply upcast_rejected. left. reflexivity.
Qed.

Theorem Sub_pick_override_rejected :
  ~ method_override_compatible CT (method_tv_env CT 5 (msignature Sub_pick))
      (class_qualifier (signature SubDef)) [MutCell]
      (msignature Sub_pick) (msignature Super_pick).
Proof.
  intros H. unfold method_override_compatible in H. cbv zeta in H.
  destruct H as (_ & _ & _ & Hret & _).
  exact (Sub_pick_return_premise_fails Hret).
Qed.

Theorem Sub_pick_not_wf : ~ wf_method CT 5 Sub_pick.
Proof.
  intros H. unfold wf_method in H. cbv zeta in H.
  destruct H as (_ & _ & _ & _ & Hov & _).
  apply Sub_pick_override_rejected.
  exact (Hov SubDef 4 [MutCell] 4 Super_pick [MutCell] eq_refl eq_refl
           find_pick_in_Super Sub_sees_Super).
Qed.

Theorem CT_not_wf : ~ wf_class_table CT.
Proof.
  intros H. destruct H as (HF & _).
  assert (Hin : List.In SubDef CT) by (do 5 right; left; reflexivity).
  pose proof (proj1 (Forall_forall (wf_class CT) CT) HF SubDef Hin) as Hs.
  inversion Hs.
  - match goal with Hn : super _ = None |- _ => cbn in Hn; discriminate Hn end.
  - match goal with
    | Hm : Forall (wf_method _ _) _ |- _ =>
        cbn in Hm; inversion Hm; subst; apply Sub_pick_not_wf; assumption
    end.
Qed.

(** No choice of return type rescues the override: the body returns c, a
    @RO C, so the declared return type must be a supertype of @RO C, and it
    must also be a subtype of @RO P<@Mut Cell>. *)
Theorem no_return_type_works : forall Δ T,
  readonly_state_method_scope (tv_mode Δ) ->
  qualified_type_subtype CT Δ ROC T ->
  qualified_type_subtype CT Δ T ROPMutCell ->
  False.
Proof.
  intros Δ T Hmode H1 H2.
  apply (upcast_rejected Δ Hmode). eapply qtype_trans; eauto.
Qed.

(** Everything else about Sub.pick is fine: the remaining parts of its
    well-formedness and the remaining parts of the override check hold. *)
Theorem Sub_pick_rest_ok :
  let Δ := method_tv_env CT 5 (msignature Sub_pick) in
  let view := member_type AbstractState RDM [MutCell] [] [] in
  receiver_shape CT 5 ROSub /\
  wf_stypeuse CT Δ ROC /\
  stmt_typing CT Δ [ROSub; ROC] ReadonlyState SSkip [ROSub; ROC] /\
  qualified_type_subtype CT Δ ROC ROC /\
  signature_has_no_mutable_roots Δ (msignature Sub_pick) /\
  mname (msignature Sub_pick) = mname (msignature Super_pick) /\
  mscope (msignature Sub_pick) = mscope (msignature Super_pick) /\
  mtparams (msignature Sub_pick) = map view (mtparams (msignature Super_pick)) /\
  Forall2 (fun p_super p_sub => qualified_type_subtype CT Δ (view p_super) p_sub)
    (mparams (msignature Super_pick)) (mparams (msignature Sub_pick)) /\
  q_subtype (vpa_mutability_qq_abstract_state RDM RO) RO.
Proof.
  cbv zeta. rewrite Sub_pick_env.
  split; [apply receiver_plain_shape; left; exists RO; reflexivity|].
  split; [apply wf_ROC|].
  split; [apply ST_Skip; wfenv|].
  split; [refl_sub|].
  split.
  { split.
    - apply nm_class; [discriminate | constructor].
    - constructor; [apply nm_class; [discriminate | constructor] | constructor]. }
  split; [reflexivity|]. split; [reflexivity|]. split; [split; reflexivity|].
  split.
  { constructor; [|constructor].
    change (qualified_type_subtype CT (mk_tv_env [] [] ReadonlyState 0) ROC ROC).
    refl_sub. }
  cbn. qs.
Qed.

(* ------------------4. CONTRAST------------------*)

(** The same return-type comparison succeeds when the mode is
    abstract-state. *)
Theorem return_check_accepted_abstract : forall Δ,
  tv_mode Δ = AbstractState ->
  qualified_type_subtype CT Δ ROC ROPMutCell.
Proof.
  intros Δ Hmode. apply qtype_hier. rewrite Hmode.
  eapply si_step; [reflexivity|]. cbn. apply si_refl.
Qed.

(** But a method checked in abstract-state or concrete-state mode cannot be
    called from readonly-state or transitive-state code, and an override
    keeps the mode of the method it overrides. *)
Theorem weaker_mode_not_callable : forall callee caller,
  (callee = AbstractState \/ callee = ConcreteState) ->
  readonly_state_method_scope caller ->
  ~ method_scope_subtype callee caller.
Proof.
  intros callee caller [-> | ->] [-> | ->] H; inversion H.
Qed.

(** The whole override check for Sub.pick against Super.pick passes when the
    comparison is made in abstract-state mode.  So the mode of the comparison
    is the only thing that rejects this override. *)
Theorem override_accepted_if_compared_abstractly :
  method_override_compatible CT (mk_tv_env [] [] AbstractState 0)
    (class_qualifier (signature SubDef)) [MutCell]
    (msignature Sub_pick) (msignature Super_pick).
Proof.
  unfold method_override_compatible. cbv zeta.
  split; [reflexivity|]. split; [reflexivity|]. split; [split; reflexivity|].
  split.
  { rewrite overridden_return_view.
    apply return_check_accepted_abstract. reflexivity. }
  split.
  { constructor; [|constructor].
    change (qualified_type_subtype CT (mk_tv_env [] [] AbstractState 0) ROC ROC).
    refl_sub. }
  cbn. split; [apply qtype_qual; [cbn; lia | cbn; qs | apply Forall2_targ_sub_refl] | radmit_plain].
Qed.

(** No runtime configuration over this class table is well formed, so the
    readonly-state theorems, which assume one, say nothing about it. *)
Theorem no_wf_config : forall Δ sΓ rΓ h, ~ wf_r_config CT Δ sΓ rΓ h.
Proof. intros Δ sΓ rΓ h [H _]. exact (CT_not_wf H). Qed.

Print Assumptions Super_pick_wf.
Print Assumptions hack_wf.
Print Assumptions supertypes_of_ROC.
Print Assumptions Sub_pick_return_premise_fails.
Print Assumptions Sub_pick_override_rejected.
Print Assumptions Sub_pick_not_wf.
Print Assumptions CT_not_wf.
Print Assumptions no_return_type_works.
Print Assumptions Sub_pick_rest_ok.
Print Assumptions return_check_accepted_abstract.
Print Assumptions weaker_mode_not_callable.
Print Assumptions override_accepted_if_compared_abstractly.
Print Assumptions no_wf_config.
