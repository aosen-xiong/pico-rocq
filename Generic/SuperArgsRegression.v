From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing.

(** Regression file for the mode-aware superclass view.

    class 0: @RDM class Object {}
    class 1: @RDM class Cell extends Object { @RDA @RO Object value; }
    class 2: @RDM class P<E extends @RO Object> extends Object { @RDA E item; }
    class 3: @RDM class C extends P<@Mut Cell> {}
    class 4: @RDM class Tool extends Object {
       @RS @RO Object hack(@RO Tool this, @RO C c, @RO Object y) {
           @RO P<@Mut Cell> p;   // var 3
           @Mut Cell k;          // var 4
           p = c;                // no longer accepted in readonly-state code
           k = p.item;
           k.value = y;
           return y;
       }
    }

    Before the change, a C seen through a readonly reference was a
    P<@Mut Cell> in every mode, so hack was accepted and changed a protected
    field.  Now, in readonly-state code, a readonly C is only a P<@Lost Cell>,
    and what is read out of it cannot be used as a mutable Cell. *)

(* ------------------THE PROGRAM------------------*)

Definition ROObject : qualified_type := TClass RO 0 [].
Definition MutCell : qualified_type := TClass Mut 1 [].
Definition LostCell : qualified_type := TClass Lost 1 [].
Definition ROC : qualified_type := TClass RO 3 [].
Definition ROTool : qualified_type := TClass RO 4 [].
Definition tE : qualified_type := TVar TVSub ClassVar 0.
Definition ROPMutCell : qualified_type := TClass RO 2 [MutCell].
Definition ROPLostCell : qualified_type := TClass RO 2 [LostCell].

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
  {| assignability := RDA; ftype := tE |}.

Definition PDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 2;
                     ctparams := [ROObject];
                     super := Some (0, []) |};
     body := {| fields := [item_field]; methods := [] |} |}.

(** The superclass type argument is mutable. *)
Definition CDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 3; ctparams := [];
                     super := Some (2, [MutCell]) |};
     body := {| fields := []; methods := [] |} |}.

Definition hack : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mret := ROObject;
          mname := 0;
          mreceiver := ROTool;
          mparams := [ROC; ROObject] |};
     mbody :=
       {| mbody_stmt :=
            SSeq (SLocal ROPMutCell 3)
            (SSeq (SLocal MutCell 4)
            (SSeq (SVarAss 3 (EVar 1))
            (SSeq (SVarAss 4 (EField 3 0))
                  (SFldWrite 4 0 2))));
          mreturn := 2 |} |}.

Definition ToolDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 4; ctparams := [];
                     super := Some (0, []) |};
     body := {| fields := []; methods := [hack] |} |}.

Definition CT : class_table := [ObjectDef; CellDef; PDef; CDef; ToolDef].

(* ------------------1. THE UPCAST IS REJECTED IN READONLY-STATE CODE------------------*)

(** The classes and argument lists a readonly C can be viewed at in
    readonly-state code. *)
Definition reach (C : class_name) (Ts : list qualified_type) : Prop :=
  (C = 3 /\ Ts = []) \/ (C = 2 /\ Ts = [LostCell]) \/ (C = 0 /\ Ts = []).

Lemma super_inst_reach : forall C Ts D Vs,
  super_inst CT ReadonlyState RO C Ts D Vs ->
  reach C Ts -> reach D Vs.
Proof.
  intros C Ts D Vs H. induction H; intros Hr; [exact Hr|].
  apply IHsuper_inst.
  destruct Hr as [[-> ->] | [[-> ->] | [-> ->]]]; cbn in Hparent.
  - injection Hparent as <- <-. right. left. split; reflexivity.
  - injection Hparent as <- <-. right. right. split; reflexivity.
  - discriminate.
Qed.

(** The supertypes of @RO C in readonly-state code. *)
Definition sup_ROC (T : qualified_type) : Prop :=
  T = TClass RO 3 [] \/
  T = TClass RO 2 [TClass Lost 1 []] \/
  T = TClass RO 0 [].

(** Every supertype of a type in the set is in the set. *)
Lemma sup_ROC_closed : forall Δ,
  tv_mode Δ = ReadonlyState ->
  forall T U, qualified_type_subtype CT Δ T U -> sup_ROC T -> sup_ROC U.
Proof.
  intros Δ Hmode T U H.
  induction H; intros Hs.
  - (* same class, wider qualifier, compatible arguments *)
    assert (Hq2 : q2 = RO /\ q1 = RO).
    { destruct Hs as [Hs | [Hs | Hs]]; injection Hs as -> _ _;
        inversion Hqsub; subst; split; reflexivity || discriminate. }
    destruct Hq2 as [-> ->].
    destruct Hs as [Hs | [Hs | Hs]]; injection Hs as -> ->.
    + inversion Hargs; subst. left. reflexivity.
    + inversion Hargs as [|a b l l' Hab Hl]; subst.
      inversion Hl; subst.
      inversion Hab as [|qa qb Ca Tsa Usa Hq Hargs'|]; subst.
      inversion Hargs'; subst.
      destruct Hq as [-> | [_ [Hq | Hq]]]; try discriminate.
      right. left. reflexivity.
    + inversion Hargs; subst. right. right. reflexivity.
  - (* same qualifier, up the class hierarchy *)
    rewrite Hmode in Hsuper.
    assert (Hr : q1 = RO /\ reach C Ts).
    { destruct Hs as [Hs | [Hs | Hs]]; injection Hs as -> -> ->;
        (split; [reflexivity|]); unfold reach; auto. }
    destruct Hr as [-> Hr].
    destruct (super_inst_reach _ _ _ _ Hsuper Hr)
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
  - auto.
Qed.

(** The characterization: in readonly-state code every supertype of @RO C is
    @RO C, @RO P<@Lost Cell>, or @RO Object. *)
Theorem supertypes_of_ROC : forall Δ U,
  tv_mode Δ = ReadonlyState ->
  qualified_type_subtype CT Δ (TClass RO 3 []) U ->
  U = TClass RO 3 [] \/
  U = TClass RO 2 [TClass Lost 1 []] \/
  U = TClass RO 0 [].
Proof.
  intros Δ U Hmode H.
  apply (sup_ROC_closed Δ Hmode _ _ H). left. reflexivity.
Qed.

(** The upcast used by hack is rejected. *)
Theorem upcast_rejected : forall Δ,
  tv_mode Δ = ReadonlyState ->
  ~ qualified_type_subtype CT Δ (TClass RO 3 []) (TClass RO 2 [TClass Mut 1 []]).
Proof.
  intros Δ Hmode H.
  destruct (supertypes_of_ROC Δ _ Hmode H) as [E | [E | E]]; discriminate.
Qed.

(** The same statement for the environment the task names: readonly-state
    mode and empty bounds. *)
Corollary upcast_rejected_empty_bounds :
  ~ qualified_type_subtype CT (mk_tv_env [] [] ReadonlyState)
      (TClass RO 3 []) (TClass RO 2 [TClass Mut 1 []]).
Proof. apply upcast_rejected. reflexivity. Qed.

(* ------------------2. CONTRAST: ABSTRACT-STATE CODE------------------*)

Theorem upcast_accepted_abstract : forall Δ,
  tv_mode Δ = AbstractState ->
  qualified_type_subtype CT Δ (TClass RO 3 []) (TClass RO 2 [TClass Mut 1 []]).
Proof.
  intros Δ Hmode. apply qtype_hier. rewrite Hmode.
  eapply si_step; [reflexivity|]. cbn. apply si_refl.
Qed.

(* ------------------3. WHAT THE UPCAST GIVES NOW------------------*)

Theorem upcast_gives_lost : forall Δ,
  tv_mode Δ = ReadonlyState ->
  qualified_type_subtype CT Δ (TClass RO 3 []) (TClass RO 2 [TClass Lost 1 []]).
Proof.
  intros Δ Hmode. apply qtype_hier. rewrite Hmode.
  eapply si_step; [reflexivity|]. cbn. apply si_refl.
Qed.

(** Reading item through @RO P<@Lost Cell> in readonly-state code. *)
Theorem item_read_type :
  member_type ReadonlyState RO [TClass Lost 1 []] [] (TVar TVSub ClassVar 0)
  = TClass Lost 1 [].
Proof. reflexivity. Qed.

(** The field item of P is the type variable, so the equation above is the
    static type of the field read. *)
Lemma item_field_type : ftype item_field = TVar TVSub ClassVar 0.
Proof. reflexivity. Qed.

(** A class type headed @Lost or @RO only has supertypes that are class types
    headed @Lost or @RO.  This holds for every class table, every bound
    environment and every mode. *)
Definition lost_or_ro_head (T : qualified_type) : Prop :=
  exists q0 C Ts, T = TClass q0 C Ts /\ (q0 = Lost \/ q0 = RO).

Lemma lost_or_ro_head_closed : forall CT0 Δ T U,
  qualified_type_subtype CT0 Δ T U ->
  lost_or_ro_head T -> lost_or_ro_head U.
Proof.
  intros CT0 Δ T U H.
  induction H; intros (q0 & C0 & Ts0 & E & Hq); try discriminate.
  - injection E as -> -> ->.
    exists q2, C0, Us. split; [reflexivity|].
    inversion Hqsub; subst; auto.
    destruct Hq; discriminate.
  - injection E as -> -> ->.
    exists q0, D, Vs. split; [reflexivity | exact Hq].
  - inversion E; subst. destruct Hq; discriminate.
  - apply IHqualified_type_subtype2. apply IHqualified_type_subtype1.
    exists q0, C0, Ts0. split; [exact E | exact Hq].
Qed.

(** What was read is not a mutable Cell. *)
Theorem lost_cell_not_mut : forall Δ,
  ~ qualified_type_subtype CT Δ (TClass Lost 1 []) (TClass Mut 1 []).
Proof.
  intros Δ H.
  assert (Hh : lost_or_ro_head (TClass Mut 1 [])).
  { eapply lost_or_ro_head_closed; [exact H|].
    exists Lost, 1, (@nil qualified_type). split; [reflexivity | left; reflexivity]. }
  destruct Hh as (q0 & C0 & Ts0 & E & [-> | ->]); discriminate.
Qed.

(* ------------------4. HACK IS NO LONGER WELL FORMED------------------*)

(** The assignment p = c has no typing in readonly-state code, in any static
    environment where c is a @RO C and p is a @RO P<@Mut Cell>. *)
Theorem assignment_rejected : forall sΓ sΓ',
  static_getType sΓ 1 = Some ROC ->
  static_getType sΓ 3 = Some ROPMutCell ->
  ~ stmt_typing CT (method_tv_env CT 4 (msignature hack)) sΓ ReadonlyState
      (SVarAss 3 (EVar 1)) sΓ'.
Proof.
  intros sΓ sΓ' Hc Hp H.
  inversion H; subst.
  inversion Htype_e; subst.
  rewrite Hc in Hget. injection Hget as <-.
  rewrite Hp in Hget_x. injection Hget_x as <-.
  revert Hsub. apply upcast_rejected. reflexivity.
Qed.

(** The body of hack has no typing at all in readonly-state mode. *)
Theorem hack_body_untypable : forall sΓ',
  ~ stmt_typing CT (method_tv_env CT 4 (msignature hack))
      [ROTool; ROC; ROObject] ReadonlyState (mbody_stmt (mbody hack)) sΓ'.
Proof.
  intros sΓ' H. cbn [mbody_stmt mbody hack] in H.
  inversion H as [| | | | | | |? ? ? ? ? Γ1 ? ? _ Hloc1 Hrest1]; subst.
  inversion Hloc1; subst.
  inversion Hrest1 as [| | | | | | |? ? ? ? ? Γ2 ? ? _ Hloc2 Hrest2]; subst.
  inversion Hloc2; subst.
  inversion Hrest2 as [| | | | | | |? ? ? ? ? Γ3 ? ? _ Hass _]; subst.
  revert Hass. apply assignment_rejected; reflexivity.
Qed.

Theorem hack_not_wf : ~ wf_method CT 4 hack.
Proof.
  intros H. unfold wf_method in H.
  destruct H as (_ & _ & _ & (sΓ' & T & Hty & _) & _).
  revert Hty. apply hack_body_untypable.
Qed.

(* ------------------5. THE INHERITED-METHOD ROUTE------------------*)

(** Class P gets a readonly-state getter:

      @RS E get(@RO P<E> this) { E r; r = this.item; return r; }

    Everything else is as before. *)
Definition get : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mret := tE;
          mname := 0;
          mreceiver := TClass RO 2 [tE];
          mparams := [] |};
     mbody :=
       {| mbody_stmt :=
            SSeq (SLocal tE 1) (SVarAss 1 (EField 0 0));
          mreturn := 1 |} |}.

Definition PDef2 : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 2;
                     ctparams := [ROObject];
                     super := Some (0, []) |};
     body := {| fields := [item_field]; methods := [get] |} |}.

Definition CT2 : class_table := [ObjectDef; CellDef; PDef2; CDef; ToolDef].

(** A call c.get() on a C finds the getter declared in P. *)
Lemma find_get : FindMethodWithName CT2 3 0 2 get.
Proof.
  eapply FOM_Super; [reflexivity | reflexivity | reflexivity | reflexivity |].
  eapply FOM_Here; reflexivity.
Qed.

(** In readonly-state code a readonly C is, at P, a P<@Lost Cell>. *)
Theorem super_C_P_lost :
  super_inst CT2 ReadonlyState RO 3 [] 2 [TClass Lost 1 []].
Proof. eapply si_step; [reflexivity|]. cbn. apply si_refl. Qed.

(** And nothing else. *)
Theorem super_C_P_unique : forall Vs,
  super_inst CT2 ReadonlyState RO 3 [] 2 Vs -> Vs = [TClass Lost 1 []].
Proof.
  intros Vs H.
  inversion H as [|? ? P1 Ss1 ? ? Hp1 Hr1]; subst.
  cbn in Hp1. injection Hp1 as <- <-. cbn in Hr1.
  inversion Hr1 as [|? ? P2 Ss2 ? ? Hp2 Hr2]; subst; [reflexivity|].
  cbn in Hp2. injection Hp2 as <- <-. cbn in Hr2.
  inversion Hr2 as [|? ? P3 Ss3 ? ? Hp3 Hr3]; subst.
  cbn in Hp3. discriminate.
Qed.

(** The declared return type of get, seen by the call rule through that
    view. *)
Theorem get_result_type :
  member_type ReadonlyState RO [TClass Lost 1 []] []
    (TVar TVSub ClassVar 0) = TClass Lost 1 [].
Proof. reflexivity. Qed.

Lemma get_return_type : mret (msignature get) = TVar TVSub ClassVar 0.
Proof. reflexivity. Qed.

(** The three facts together. *)
Theorem inherited_route_closed :
  super_inst CT2 ReadonlyState RO 3 [] 2 [TClass Lost 1 []] /\
  (forall Vs, super_inst CT2 ReadonlyState RO 3 [] 2 Vs ->
              Vs = [TClass Lost 1 []]) /\
  member_type ReadonlyState RO [TClass Lost 1 []] []
    (TVar TVSub ClassVar 0) = TClass Lost 1 [].
Proof.
  split; [apply super_C_P_lost|].
  split; [apply super_C_P_unique | reflexivity].
Qed.

(** As specified, the getter declares its receiver @RO P<E>.  In
    readonly-state code that receiver, seen from a readonly C, is
    @RO P<@Lost Cell>, and a type with an unknown position accepts only a
    bottom-typed source.  So the call c.get() itself is rejected, at the
    receiver, before its result type matters. *)
Theorem get_receiver_rejected : forall Δ,
  ~ assignable_to CT2 Δ (TClass RO 3 [])
      (member_type ReadonlyState RO [TClass Lost 1 []] []
         (mreceiver (msignature get))).
Proof.
  intros Δ [_ [Hlf | (C' & Ts' & E)]].
  - cbn in Hlf. destruct Hlf as [_ [[Hl _] _]]. apply Hl. reflexivity.
  - discriminate.
Qed.

Theorem get_call_untypable : forall Δ sΓ sΓ' x y Us args,
  static_getType sΓ y = Some ROC ->
  ~ stmt_typing CT2 Δ sΓ ReadonlyState (SCall x 0 y Us args) sΓ'.
Proof.
  intros Δ sΓ sΓ' x y Us args Hy H.
  inversion H; subst.
  rewrite Hy in Hget_y. injection Hget_y as <-.
  cbn in Hub. injection Hub as <- <- <-.
  destruct (find_method_with_name_deterministic _ _ _ _ _ _ _ Hfind_m find_get)
    as [-> ->].
  apply super_C_P_unique in Hsuper. subst Vs.
  destruct Hrcv_sub as [Ha | [_ (Rargs & E)]].
  - destruct Ha as [_ [Hlf | (C' & Ts' & E)]].
    + cbn in Hlf. destruct Hlf as [_ [[Hl _] _]]. apply Hl. reflexivity.
    + discriminate.
  - discriminate.
Qed.

(** The variant in which the call is accepted: the same getter with the
    receiver declared @RDM P<E>,

      @RS E get(@RDM P<E> this) { E r; r = this.item; return r; }

    A readonly receiver is then allowed.  Every typing of k = c.get() in
    readonly-state code with c a @RO C forces @Lost Cell to be a subtype of
    the type of k, so k cannot be a @Mut Cell. *)
Definition get_rdm : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mret := tE;
          mname := 0;
          mreceiver := TClass RDM 2 [tE];
          mparams := [] |};
     mbody :=
       {| mbody_stmt :=
            SSeq (SLocal tE 1) (SVarAss 1 (EField 0 0));
          mreturn := 1 |} |}.

Definition PDef3 : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 2;
                     ctparams := [ROObject];
                     super := Some (0, []) |};
     body := {| fields := [item_field]; methods := [get_rdm] |} |}.

Definition CT3 : class_table := [ObjectDef; CellDef; PDef3; CDef; ToolDef].

Lemma find_get_rdm : FindMethodWithName CT3 3 0 2 get_rdm.
Proof.
  eapply FOM_Super; [reflexivity | reflexivity | reflexivity | reflexivity |].
  eapply FOM_Here; reflexivity.
Qed.

Lemma super_C_P_unique3 : forall Vs,
  super_inst CT3 ReadonlyState RO 3 [] 2 Vs -> Vs = [TClass Lost 1 []].
Proof.
  intros Vs H.
  inversion H as [|? ? P1 Ss1 ? ? Hp1 Hr1]; subst.
  cbn in Hp1. injection Hp1 as <- <-. cbn in Hr1.
  inversion Hr1 as [|? ? P2 Ss2 ? ? Hp2 Hr2]; subst; [reflexivity|].
  cbn in Hp2. injection Hp2 as <- <-. cbn in Hr2.
  inversion Hr2 as [|? ? P3 Ss3 ? ? Hp3 Hr3]; subst.
  cbn in Hp3. discriminate.
Qed.

Theorem get_rdm_call_result : forall Δ sΓ sΓ' x y Us args Tx,
  static_getType sΓ y = Some ROC ->
  static_getType sΓ x = Some Tx ->
  stmt_typing CT3 Δ sΓ ReadonlyState (SCall x 0 y Us args) sΓ' ->
  qualified_type_subtype CT3 Δ (TClass Lost 1 []) Tx.
Proof.
  intros Δ sΓ sΓ' x y Us args Tx Hy Hx H.
  inversion H; subst.
  rewrite Hy in Hget_y. injection Hget_y as <-.
  rewrite Hx in Hget_x. injection Hget_x as <-.
  cbn in Hub. injection Hub as <- <- <-.
  destruct (find_method_with_name_deterministic _ _ _ _ _ _ _ Hfind_m find_get_rdm)
    as [-> ->].
  apply super_C_P_unique3 in Hsuper. subst Vs.
  exact Hret_sub.
Qed.

Theorem get_rdm_call_not_mut : forall Δ sΓ sΓ' x y Us args,
  static_getType sΓ y = Some ROC ->
  static_getType sΓ x = Some (TClass Mut 1 []) ->
  ~ stmt_typing CT3 Δ sΓ ReadonlyState (SCall x 0 y Us args) sΓ'.
Proof.
  intros Δ sΓ sΓ' x y Us args Hy Hx H.
  pose proof (get_rdm_call_result _ _ _ _ _ _ _ _ Hy Hx H) as Hsub.
  assert (Hh : lost_or_ro_head (TClass Mut 1 [])).
  { eapply lost_or_ro_head_closed; [exact Hsub|].
    exists Lost, 1, (@nil qualified_type).
    split; [reflexivity | left; reflexivity]. }
  destruct Hh as (q0 & C0 & Ts0 & E & [-> | ->]); discriminate.
Qed.

Print Assumptions supertypes_of_ROC.
Print Assumptions upcast_rejected.
Print Assumptions upcast_accepted_abstract.
Print Assumptions upcast_gives_lost.
Print Assumptions item_read_type.
Print Assumptions lost_cell_not_mut.
Print Assumptions assignment_rejected.
Print Assumptions hack_not_wf.
Print Assumptions inherited_route_closed.
Print Assumptions get_receiver_rejected.
Print Assumptions get_call_untypable.
Print Assumptions get_rdm_call_result.
Print Assumptions get_rdm_call_not_mut.
