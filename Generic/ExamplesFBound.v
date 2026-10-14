From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric
  GhostLabels GhostTyping GhostForget GhostFit GhostInvariant GhostOverride
  GhostCall GhostEntry ArgViews ArgTyping ArgFit ArgInvariant
  ArgCases ArgClean ArgOverride ArgCall ArgMain ArgEntry ArgRsf.

(** A worked example for the readonly-state theorem in which the bound of a
    type parameter mentions that same parameter, and a readonly-state method
    is declared in a class with such a parameter.

    class 0: @RDM class Object {}
    class 1: @RDM class Comparable<T extends @RO Comparable<T>>
             extends Object {}
    class 2: @RDM class Item extends Comparable<@RO Item> {}
    class 3: @RDM class Sorted<E extends @RO Comparable<E>> extends Object {
       @RDA E head;                        // field 0
       // method 0, readonly-state
       @RS @RO Object peek(@RO Sorted<E> this) {
           @RO Object r;      // var 1
           r = this.head;     // E used at its bound, which mentions E
           return r;
       }
    }

    main (variable 0 is the receiver, a @Mut Object; abstract-state mode):
      @Mut Item it;                       // var 1
      @Mut Sorted<@RO Item> s;            // var 2
      @RO Object x;                       // var 3
      it = new @Mut Item();
      s  = new @Mut Sorted<@RO Item>(it);
      x  = s.peek();                      // the call

    The Item and the Sorted exist before the call.  The head of the Sorted is
    receiver-dependent assignable, so the theorem says the call leaves it as
    it is. *)

(* ------------------THE PROGRAM------------------*)

Definition ROObject : qualified_type := TClass RO 0 [].
Definition MutObject : qualified_type := TClass Mut 0 [].
Definition tV : qualified_type := TVar TVSub ClassVar 0.
(** The bound shared by Comparable's T and Sorted's E: a readonly Comparable
    of the variable itself. *)
Definition ROCompV : qualified_type := TClass RO 1 [tV].
Definition ROItem : qualified_type := TClass RO 2 [].
Definition MutItem : qualified_type := TClass Mut 2 [].
Definition ROCompItem : qualified_type := TClass RO 1 [ROItem].
Definition ROSortedE : qualified_type := TClass RO 3 [tV].
Definition MutSorted : qualified_type := TClass Mut 3 [ROItem].
Definition ROSortedItem : qualified_type := TClass RO 3 [ROItem].

Definition ObjectDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 0; ctparams := [];
                     super := None |};
     body := {| fields := []; methods := [] |} |}.

Definition ComparableDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 1;
                     ctparams := [ROCompV];
                     super := Some (0, []) |};
     body := {| fields := []; methods := [] |} |}.

Definition ItemDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 2; ctparams := [];
                     super := Some (1, [ROItem]) |};
     body := {| fields := []; methods := [] |} |}.

Definition head_field : field_def :=
  {| assignability := RDA; ftype := tV |}.

Definition peek : method_def :=
  {| msignature :=
       {| mscope := ReadonlyState;
          mtparams := [];
          mqparams := 0;
          mret := ROObject;
          mname := 0;
          mreceiver := ROSortedE;
          mparams := [] |};
     mbody :=
       {| mbody_stmt :=
            SSeq (SLocal ROObject 1)
                 (SVarAss 1 (EField 0 0));
          mreturn := 1 |} |}.

Definition SortedDef : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := 3;
                     ctparams := [ROCompV];
                     super := Some (0, []) |};
     body := {| fields := [head_field]; methods := [peek] |} |}.

Definition CT : class_table := [ObjectDef; ComparableDef; ItemDef; SortedDef].

Definition prefix : stmt :=
  SSeq (SLocal MutItem 1)
  (SSeq (SLocal MutSorted 2)
  (SSeq (SLocal ROObject 3)
  (SSeq (SNew 1 Mut_c 2 [] [])
        (SNew 2 Mut_c 3 [ROItem] [1])))).

Definition callP : stmt := SCall 3 0 2 [] [] [].

Definition main : stmt := SSeq prefix callP.

Definition Δ0 : tv_env := mk_tv_env [] [] AbstractState 0.
Definition sΓ0 : s_env := [MutObject].
Definition sΓA : s_env := [MutObject; MutItem; MutSorted; ROObject].

(** The bound environment of peek: E bounded by @RO Comparable<E>. *)
Definition ΔP : tv_env := mk_tv_env [ROCompV] [] ReadonlyState 0.

Definition sΓPeek : s_env := [ROSortedE; ROObject].

(* ------------------SMALL TACTICS AND FACTS------------------*)

Ltac qs := (apply q_refl; discriminate) || apply q_rd || apply q_bot.

Lemma wf_plain : forall Δ top q0 C,
  C = 0 \/ C = 2 -> q0 <> Lost -> wf_stype CT Δ top (TClass q0 C []).
Proof.
  intros Δ top q0 C HC Hq.
  destruct HC as [-> | ->];
    (eapply wfs_class;
       [reflexivity | right | reflexivity | constructor | constructor]);
    destruct q0; cbn; try qs; congruence.
Qed.

Lemma wf_use : forall Δ q0 C,
  C = 0 \/ C = 2 -> q0 <> Lost -> wf_stypeuse CT Δ (TClass q0 C []).
Proof. intros. apply wf_plain; auto. Qed.

Ltac wfp := apply wf_use; [tauto | discriminate].

Ltac refl_sub :=
  apply qualified_type_subtype_refl_class; [cbn; lia | discriminate].

Ltac qual_sub :=
  apply qtype_qual; [cbn; lia | qs | apply Forall2_targ_sub_refl].

Ltac lf := cbn; intuition discriminate.

(** A readonly Item is a readonly Comparable of readonly Items: this is the
    extends clause of Item, read through a readonly head.  It holds in every
    mode. *)
Lemma sub_ROItem_ROCompItem : forall Δ,
  qualified_type_subtype CT Δ ROItem ROCompItem.
Proof.
  intros Δ. apply qtype_hier with (D := 1) (Vs := [ROItem]).
  eapply si_step; [reflexivity|].
  destruct (tv_mode Δ); cbn; apply si_refl.
Qed.

(** Inside a class whose parameter is bounded by a Comparable of itself, the
    parameter is a readonly Object: first to its bound, then up from
    Comparable to Object. *)
Lemma sub_tV_ROObject : forall mb mt kq,
  qualified_type_subtype CT (mk_tv_env [ROCompV] mb mt kq) tV ROObject.
Proof.
  intros mb mt kq. eapply qtype_trans.
  - apply qtype_var_bound with (B := ROCompV). reflexivity.
  - apply qtype_hier with (D := 0) (Vs := []).
    eapply si_step; [reflexivity|]. cbn. apply si_refl.
Qed.

(** The self-referential bound is a well-formed type in its own scope.  The
    argument check asks that the variable be below the bound of Comparable's
    parameter with the variable put in for that parameter, which is the
    variable's own declared bound. *)
Lemma wf_ROCompV : forall mb mt kq top,
  wf_stype CT (mk_tv_env [ROCompV] mb mt kq) top ROCompV.
Proof.
  intros mb mt kq top.
  eapply wfs_class; [reflexivity | right; cbn; qs | reflexivity | |].
  - constructor; [|constructor].
    eapply wfs_var; [reflexivity | left; reflexivity].
  - constructor; [|constructor]. intros m. cbn.
    apply qtype_var_bound. reflexivity.
Qed.

(** What the bound of Sorted's E reads as for the instantiation
    Sorted<@RO Item>: a readonly Comparable of readonly Items. *)
Lemma MutSorted_bound_read :
  member_type AbstractState Mut [ROItem] [] [] ROCompV = ROCompItem.
Proof. reflexivity. Qed.

(** A Sorted of readonly Items, with any head but the unknown one.  The
    argument @RO Item is compared, in every mode, with the bound
    @RO Comparable<@RO Item>. *)
Lemma wf_SortedItem : forall Δ top q0,
  q0 <> Lost -> wf_stype CT Δ top (TClass q0 3 [ROItem]).
Proof.
  intros Δ top q0 Hq.
  eapply wfs_class; [reflexivity | right | reflexivity | |].
  - destruct q0; cbn; try qs; congruence.
  - constructor; [apply wf_plain; [tauto | discriminate] | constructor].
  - constructor; [|constructor]. intros m.
    destruct q0; cbn; apply sub_ROItem_ROCompItem.
Qed.

(** The declared receiver of peek, @RO Sorted<E>.  The bound check is
    performed: E is below @RO Comparable<E> because that is its declared
    bound. *)
Lemma wf_ROSortedE_peek : wf_stypeuse CT ΔP ROSortedE.
Proof.
  eapply wfs_class; [reflexivity | right; cbn; qs | reflexivity | |].
  - constructor; [|constructor].
    eapply wfs_var; [reflexivity | right; discriminate].
  - constructor; [|constructor]. intros m. cbn.
    apply qtype_var_bound. reflexivity.
Qed.

Lemma wf_ROObject : forall Δ, wf_stypeuse CT Δ ROObject.
Proof. intros. wfp. Qed.
Lemma wf_MutObject : forall Δ, wf_stypeuse CT Δ MutObject.
Proof. intros. wfp. Qed.
Lemma wf_ROItem : forall Δ, wf_stypeuse CT Δ ROItem.
Proof. intros. wfp. Qed.
Lemma wf_MutItem : forall Δ, wf_stypeuse CT Δ MutItem.
Proof. intros. wfp. Qed.
Lemma wf_MutSorted : forall Δ, wf_stypeuse CT Δ MutSorted.
Proof. intros. apply wf_SortedItem. discriminate. Qed.

Create HintDb fdb.
Local Hint Resolve wf_ROObject wf_MutObject wf_ROItem wf_MutItem wf_MutSorted
  wf_ROSortedE_peek : fdb.

Ltac wfenv :=
  split; [cbn; lia |
          cbn; repeat (apply Forall_cons; [solve [auto with fdb]|]);
          apply Forall_nil].

Lemma collect_Object : CollectFields CT 0 [].
Proof. eapply CF_Object; reflexivity. Qed.

Lemma collect_Comparable : CollectFields CT 1 [].
Proof.
  change (CollectFields CT 1
            (map (subst_field []) [] ++ Syntax.fields (body ComparableDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

Lemma collect_Item : CollectFields CT 2 [].
Proof.
  change (CollectFields CT 2
            (map (subst_field [ROItem]) [] ++ Syntax.fields (body ItemDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Comparable.
Qed.

Lemma collect_Sorted : CollectFields CT 3 [head_field].
Proof.
  change (CollectFields CT 3
            (map (subst_field []) [] ++ Syntax.fields (body SortedDef))).
  eapply CF_Inherit; try reflexivity. apply collect_Object.
Qed.

(** Field 0 of Sorted, head, is receiver-dependent assignable. *)
Lemma head_is_rda : sf_assignability_rel CT 3 0 RDA.
Proof.
  exists head_field. split; [|reflexivity].
  eapply FL_Found; [apply collect_Sorted | reflexivity].
Qed.

Lemma no_method_in_Object : forall m D mdef,
  ~ FindMethodWithName CT 0 m D mdef.
Proof.
  intros m D mdef H. inversion H; subst.
  - cbn in Hfind. injection Hfind as <-. cbn in Hget_method. discriminate.
  - cbn in Hfind. injection Hfind as <-. cbn in Hsuper. discriminate.
Qed.

Lemma find_peek : FindMethodWithName CT 3 0 3 peek.
Proof. eapply FOM_Here; reflexivity. Qed.

Ltac ty_local :=
  eapply ST_Local;
    [wfenv | solve [auto with fdb] | reflexivity | reflexivity | reflexivity].

Ltac ty_seq := eapply ST_Seq; [wfenv | |].

Ltac fl H := eapply FL_Found; [apply H | reflexivity].

Ltac no_override :=
  let def := fresh "def" in
  let Hfind := fresh "Hfind" in
  let Hsuper := fresh "Hsuper" in
  let Hfm := fresh "Hfm" in
  intros def ? ? ? ? ? Hfind Hsuper Hfm _;
  cbn in Hfind; injection Hfind as <-; cbn in Hsuper;
  injection Hsuper as <- <-;
  exfalso; eapply no_method_in_Object; eauto.

(* ------------------NO MUTABLE POSITION THROUGH THE SELF-REFERENTIAL BOUND------------------*)

(** A variable bounded by a readonly Comparable of itself has no mutable
    position.  Reading the variable gives the bound, whose only argument is
    the variable again, so the walk never ends; it never meets a mutable
    position either. *)
Lemma no_mut_tV : forall mb mt kq,
  no_mut (mk_tv_env [ROCompV] mb mt kq) tV.
Proof.
  intros mb mt kq. cofix IH.
  eapply nm_var; [reflexivity|].
  apply nm_class; [discriminate|].
  constructor; [exact IH | constructor].
Qed.

Lemma no_mut_ROCompV : forall mb mt kq,
  no_mut (mk_tv_env [ROCompV] mb mt kq) ROCompV.
Proof.
  intros mb mt kq. apply nm_class; [discriminate|].
  constructor; [apply no_mut_tV | constructor].
Qed.

(* ------------------DELIVERABLE 1: THE CLASS TABLE------------------*)

(** *** Sorted.peek *)

(** r = this.head: through the @RO receiver the field reads as the bare
    variable E; E is below its bound @RO Comparable<E>, and that is a
    readonly Object. *)
Lemma peek_read_head :
  member_type ReadonlyState RO [tV] [] [] (ftype head_field) = tV /\
  qualified_type_subtype CT ΔP tV ROCompV /\
  qualified_type_subtype CT ΔP tV ROObject.
Proof.
  split; [reflexivity|]. split.
  - apply qtype_var_bound. reflexivity.
  - apply sub_tV_ROObject.
Qed.

Lemma peek_body_typed :
  stmt_typing CT ΔP [ROSortedE] ReadonlyState (mbody_stmt (mbody peek)) sΓPeek.
Proof.
  cbn. unfold sΓPeek.
  ty_seq; [ty_local|].
  cbn.
  eapply ST_VarAss with (Tx := ROObject) (Te := tV);
    [wfenv | | discriminate | reflexivity | ].
  - eapply ET_Field with (x := 0) (T := ROSortedE) (qx := RO) (C := 3)
      (Ts := [tV]) (fDef := head_field);
      [wfenv | reflexivity | reflexivity | fl collect_Sorted].
  - apply sub_tV_ROObject.
Qed.

(** The signature of peek has no mutable position, reading the type variable
    through its bound: the receiver is @RO Sorted<E>, and E is read as
    @RO Comparable<E>, again and again. *)
Lemma peek_no_mutable_roots :
  signature_has_no_mutable_roots ΔP (msignature peek).
Proof.
  split; [|constructor].
  cbn. apply nm_class; [discriminate|].
  constructor; [apply no_mut_tV | constructor].
Qed.

Lemma wf_peek : wf_method CT 3 peek.
Proof.
  unfold wf_method.
  change (method_tv_env CT 3 (msignature peek)) with ΔP.
  split; [apply receiver_plain_ok; left; exists RO; reflexivity|].
  split; [constructor|].
  split; [apply wf_ROObject|].
  split.
  { exists sΓPeek, ROObject. split; [|split].
    - apply peek_body_typed.
    - reflexivity.
    - refl_sub. }
  split; [no_override|].
  intros _. apply peek_no_mutable_roots.
Qed.

(** *** The classes *)

Ltac wf_other sc ss sd :=
  eapply WFOtherDef with (superC := sc) (Ss := ss) (super_def := sd);
    [reflexivity | cbn; lia | reflexivity
    | cbn | cbn | cbn | cbn | cbn | cbn | cbn | cbn].

Lemma wf_ObjectDef : wf_class CT ObjectDef.
Proof. apply WFObjectDef; reflexivity. Qed.

(** Comparable: its one bound mentions its own parameter. *)
Lemma wf_ComparableDef : wf_class CT ComparableDef.
Proof.
  wf_other 0 (@nil qualified_type) ObjectDef.
  - constructor; [|constructor]. split; [exact I | apply wf_ROCompV].
  - wfp.
  - constructor.
  - constructor.
  - left. reflexivity.
  - constructor.
  - constructor.
  - constructor.
Qed.

(** Item extends Comparable<@RO Item>.  The superclass argument @RO Item is
    compared with Comparable's bound with @RO Item put in for the parameter,
    which is @RO Comparable<@RO Item>: the extends clause itself. *)
Lemma wf_ItemDef : wf_class CT ItemDef.
Proof.
  wf_other 1 [ROItem] ComparableDef.
  - constructor.
  - eapply wfs_class; [reflexivity | right; cbn; qs | reflexivity | |].
    + constructor; [apply wf_plain; [tauto | discriminate] | constructor].
    + constructor; [|constructor]. intros m. cbn.
      apply sub_ROItem_ROCompItem.
  - constructor; [lf | constructor].
  - constructor; [|constructor]. cbn.
    split; [lf | intros m; apply sub_ROItem_ROCompItem].
  - left. reflexivity.
  - constructor.
  - constructor.
  - constructor.
Qed.

(** Sorted: its one bound mentions its own parameter, and it declares the
    readonly-state method. *)
Lemma wf_SortedDef : wf_class CT SortedDef.
Proof.
  wf_other 0 (@nil qualified_type) ObjectDef.
  - constructor; [|constructor]. split; [exact I | apply wf_ROCompV].
  - wfp.
  - constructor.
  - constructor.
  - left. reflexivity.
  - constructor; [|constructor]; unfold wf_field; cbn.
    eapply wfs_var; [reflexivity|]. right. discriminate.
  - constructor; [apply wf_peek | constructor].
  - constructor; [intros [] | constructor].
Qed.

Theorem fbound_ct_wf : wf_class_table CT.
Proof.
  unfold wf_class_table. split; [|split; [|split]].
  - constructor; [apply wf_ObjectDef|].
    constructor; [apply wf_ComparableDef|].
    constructor; [apply wf_ItemDef|].
    constructor; [apply wf_SortedDef | constructor].
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

(** The table does contain a bound that mentions its own variable, twice. *)
Lemma bounds_are_self_referential :
  nth_error (ctparams (signature ComparableDef)) 0
    = Some (TClass RO 1 [TVar TVSub ClassVar 0]) /\
  nth_error (ctparams (signature SortedDef)) 0
    = Some (TClass RO 1 [TVar TVSub ClassVar 0]).
Proof. split; reflexivity. Qed.

(* ------------------DELIVERABLE 2: THE CONDITIONS ON BOUNDS HOLD------------------*)

(** Every class type-parameter bound of this table is a class type with no
    mutable position.  There are two, the bound of Comparable's parameter and
    the bound of Sorted's, and both mention their own variable. *)
Lemma ct_bounds_nm : class_bounds_nm CT.
Proof.
  intros C def n B Hfind Hn.
  destruct C as [|[|[|[|C]]]]; cbn in Hfind;
    try (destruct C; discriminate);
    injection Hfind as <-; cbn in Hn.
  - destruct n; discriminate.
  - destruct n as [|[|n]]; cbn in Hn; try discriminate.
    injection Hn as <-. split; [exact I | apply no_mut_ROCompV].
  - destruct n; discriminate.
  - destruct n as [|[|n]]; cbn in Hn; try discriminate.
    injection Hn as <-. split; [exact I | apply no_mut_ROCompV].
Qed.

(** There is one readonly-state method, peek.  One type parameter is in its
    scope, with the bound @RO Comparable<E>. *)
Theorem fbound_ct_clean_bounds : clean_bounds_ct CT.
Proof.
  intros C def md Hfind Hin _.
  destruct C as [|[|[|[|C]]]]; cbn in Hfind;
    try (destruct C; discriminate);
    injection Hfind as <-; cbn in Hin.
  - destruct Hin.
  - destruct Hin.
  - destruct Hin.
  - destruct Hin as [<- | []].
    intros o n B Hb.
    destruct o; [destruct n as [|[|n]] | destruct n]; cbn in Hb;
      try discriminate.
    injection Hb as <-. split; [exact I | apply no_mut_ROCompV].
Qed.

(** The condition is not vacuous: peek is a readonly-state method of the
    table, its receiver mentions the type parameter, and the bound
    environment in which it is checked holds a bound that mentions its own
    variable. *)
Lemma peek_is_readonly_state :
  find_class CT 3 = Some SortedDef /\
  List.In peek (methods (body SortedDef)) /\
  readonly_state_method_scope (mscope (msignature peek)) /\
  mreceiver (msignature peek) = TClass RO 3 [TVar TVSub ClassVar 0].
Proof.
  split; [reflexivity|]. split; [left; reflexivity|].
  split; [left; reflexivity | reflexivity].
Qed.

Lemma peek_bound_of_E :
  tv_bound (method_tv_env CT 3 (msignature peek)) ClassVar 0
    = Some (TClass RO 1 [TVar TVSub ClassVar 0]).
Proof. reflexivity. Qed.

(** What the condition says about that bound. *)
Lemma peek_bound_checked :
  is_class_type (TClass RO 1 [TVar TVSub ClassVar 0]) /\
  no_mut (method_tv_env CT 3 (msignature peek))
    (TClass RO 1 [TVar TVSub ClassVar 0]).
Proof.
  exact (fbound_ct_clean_bounds 3 SortedDef peek eq_refl (or_introl eq_refl)
           (or_introl eq_refl) ClassVar 0 _ peek_bound_of_E).
Qed.

(* ------------------DELIVERABLE 3: CONFIGURATION, TYPING, RUN------------------*)

Lemma prefix_typed : stmt_typing CT Δ0 sΓ0 AbstractState prefix sΓA.
Proof.
  unfold prefix, sΓA, sΓ0, Δ0.
  ty_seq; [ty_local|]. ty_seq; [ty_local|]. ty_seq; [ty_local|].
  cbn.
  (* it = new @Mut Item() *)
  ty_seq.
  { eapply ST_New with (Tx := MutItem) (argtypes := []) (fds := []);
      [wfenv | reflexivity | reflexivity | reflexivity | discriminate
      | reflexivity | apply wf_MutItem | constructor | constructor
      | apply collect_Item | constructor | ].
    cbn. refl_sub. }
  (* s = new @Mut Sorted<@RO Item>(it).  The type argument @RO Item is
     compared with @RO Comparable<@RO Item>; the initialiser, a @Mut Item,
     fills the field head, which for this object reads @RO Item. *)
  eapply ST_New with (Tx := MutSorted) (argtypes := [MutItem]);
    [wfenv | reflexivity | reflexivity | reflexivity | discriminate
    | reflexivity | apply wf_MutSorted | | | apply collect_Sorted | | ].
  - constructor; [lf | constructor].
  - constructor; [|constructor]. cbn.
    split; [lf | intros m; apply sub_ROItem_ROCompItem].
  - constructor; [|constructor]; cbn.
    split; [qual_sub | lf].
  - cbn. refl_sub.
Qed.

(** The call, made from abstract-state code.  Through the mutable
    Sorted<@RO Item> the declared receiver @RO Sorted<E> reads
    @RO Sorted<@RO Item>. *)
Lemma callP_typed : stmt_typing CT Δ0 sΓA AbstractState callP sΓA.
Proof.
  unfold callP, sΓA, Δ0.
  eapply ST_Call with (Tx := ROObject) (Ty := MutSorted)
    (argtypes := [])
    (qy := Mut) (C := 3) (Ts := [ROItem]) (D := 3) (Vs := [ROItem])
    (mdef := peek);
    [wfenv | reflexivity | reflexivity | reflexivity | reflexivity
    | apply find_peek | apply si_refl | discriminate | constructor
    | constructor | reflexivity | constructor | | | constructor
    | apply method_rs_as | reflexivity | constructor | recv_known].
  - cbn. refl_sub.
  - cbn. split; [qual_sub | lf].
Qed.

Lemma main_typed : stmt_typing CT Δ0 sΓ0 AbstractState main sΓA.
Proof.
  unfold main.
  eapply ST_Seq; [unfold sΓ0; wfenv | apply prefix_typed | apply callP_typed].
Qed.

(** The states.  Location 0 is main's receiver, 1 is the Item, 2 is the
    Sorted that holds it. *)
Definition rΓ0 : r_env := mkr_env [Iot 0] [] [] [].
Definition h0 : heap := [mkObj (mkruntime_type Mut_r 0 []) []].

Definition rROItem : rtype := RClass RO 2 [].

Definition rΓA : r_env := mkr_env [Iot 0; Iot 1; Iot 2; Null_a] [] [] [].

Definition hA : heap :=
  [ mkObj (mkruntime_type Mut_r 0 []) [];
    mkObj (mkruntime_type Mut_r 2 []) [];
    mkObj (mkruntime_type Mut_r 3 [rROItem]) [Iot 1] ].

Ltac ev_local := eapply SBS_Seq; [apply SBS_Local; reflexivity|]; cbn.
Ltac ev_new := eapply SBS_Seq; [eapply SBS_New; reflexivity|]; cbn.

Lemma prefix_eval : eval_stmt CT rΓ0 h0 prefix OK rΓA hA.
Proof.
  unfold prefix, rΓ0, h0.
  ev_local. ev_local. ev_local.
  ev_new.
  eapply SBS_New; reflexivity.
Qed.

Lemma initial_config : wf_r_config CT Δ0 sΓ0 rΓ0 h0.
Proof.
  unfold Δ0, sΓ0, rΓ0, h0.
  refine (conj fbound_ct_wf
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

(** The initial configuration satisfies its bounds in the protected reading:
    the only object is of a class without type parameters, and main has no
    type parameter in scope. *)
Lemma initial_rsf : RSF CT Δ0 rΓ0 h0.
Proof.
  split.
  - apply rsfit_heap_intro. intros l o def Ho Hfc L o' n B Hb.
    destruct (tv_bound_class_env _ _ _ _ Hb) as [_ Hn].
    destruct l as [|l]; cbn in Ho; [injection Ho as <- | destruct l; discriminate].
    cbn in Hfc. injection Hfc as <-. cbn in Hn. destruct n; discriminate.
  - intros ι o _ _ L o' n B Hb. destruct o'; destruct n; discriminate.
Qed.

(** The configuration just before the call is well formed. *)
Theorem config_A : wf_r_config CT Δ0 sΓA rΓA hA.
Proof.
  eapply preservation_pico;
    eauto using prefix_eval, initial_config, prefix_typed.
Qed.

(** It also satisfies its bounds in the protected reading.  Here that says
    something: the heap now holds the Sorted, whose type argument @RO Item
    must fit a bound that mentions that same argument. *)
Theorem rsf_A : RSF CT Δ0 rΓA hA.
Proof.
  exact (rsf_preservation CT Δ0 sΓ0 AbstractState prefix sΓA rΓ0 h0 rΓA hA
           initial_config prefix_typed prefix_eval initial_rsf).
Qed.

(** The same in the payload form, which the theorem asks for.  The initial
    state has no type variable in scope and its only object is of a class
    without type parameters; every well-typed execution keeps the
    condition. *)
Lemma initial_rsfp : RSFp CT Δ0 rΓ0 h0.
Proof.
  apply RSFp_start; [exact initial_rsf | reflexivity | reflexivity |].
  intros l o def Ho Hfc.
  destruct l as [|l]; cbn in Ho; [injection Ho as <- | destruct l; discriminate].
  cbn in Hfc. injection Hfc as <-. reflexivity.
Qed.

Theorem rsfp_A : RSFp CT Δ0 rΓA hA.
Proof.
  exact (rsfp_preservation CT Δ0 sΓ0 AbstractState prefix sΓA rΓ0 h0 rΓA hA
           initial_config prefix_typed prefix_eval initial_rsfp).
Qed.

(** The activation of peek: receiver the Sorted, with its type argument
    resolved at run time. *)
Definition rΓpeek : r_env := mkr_env [Iot 2] [rROItem] [] [].
Definition rΓpeek' : r_env := mkr_env [Iot 2; Iot 1] [rROItem] [] [].

Definition rΓA' : r_env := mkr_env [Iot 0; Iot 1; Iot 2; Iot 1] [] [] [].

(** The body of peek, run on the Sorted. *)
Lemma peek_body_eval :
  eval_stmt CT rΓpeek hA (mbody_stmt (mbody peek)) OK rΓpeek' hA.
Proof.
  cbn. unfold rΓpeek.
  ev_local.
  match goal with
  | |- eval_stmt _ ?r ?h _ _ _ _ =>
      refine (SBS_Assign CT r h 1 _ Null_a (Iot 1) eq_refl _)
  end.
  eapply EBS_Field; reflexivity.
Qed.

Theorem callP_eval : eval_stmt CT rΓA hA callP OK rΓA' hA.
Proof.
  unfold callP, rΓA.
  eapply SBS_Call with (mdef := peek) (D := 3) (cy := 3)
    (rΓ' := rΓpeek) (rΓ'' := rΓpeek').
  - reflexivity.
  - reflexivity.
  - apply find_peek.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold callee_env. do 4 eexists.
    split; [reflexivity|]. split; [reflexivity|]. split; [split; reflexivity|].
    split; [apply rsi_refl | reflexivity].
  - apply peek_body_eval.
  - reflexivity.
  - reflexivity.
Qed.

Lemma main_eval : eval_stmt CT rΓ0 h0 main OK rΓA' hA.
Proof.
  unfold main. eapply SBS_Seq; [apply prefix_eval | apply callP_eval].
Qed.

(* ------------------DELIVERABLE 4: THE THEOREM APPLIED------------------*)

(** The readonly-state theorem applied to the call to peek, for any outcome
    of the call and any object of the entry heap. *)
Theorem callP_preserves : forall rΓ' h',
  eval_stmt CT rΓA hA callP OK rΓ' h' ->
  forall l qr C Rs vals f,
    runtime_getObj hA l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
    (sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA) ->
    exists vals',
      runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
      nth_error vals f = nth_error vals' f.
Proof.
  intros rΓ' h' Heval.
  eapply (readonly_state_preservation_final CT Δ0 sΓA AbstractState rΓA hA
            3 0 2 [] [] [] sΓA rΓ' h' 2 3 3 peek
            fbound_ct_clean_bounds config_A rsfp_A
            callP_typed Heval).
  - reflexivity.
  - reflexivity.
  - apply find_peek.
  - left. reflexivity.
Qed.

(** The Sorted (location 2) keeps its head. *)
Theorem callP_preserves_head : forall rΓ' h',
  eval_stmt CT rΓA hA callP OK rΓ' h' ->
  exists vals',
    runtime_getObj h' 2 =
      Some (mkObj (mkruntime_type Mut_r 3 [rROItem]) vals') /\
    nth_error vals' 0 = Some (Iot 1).
Proof.
  intros rΓ' h' Heval.
  destruct (callP_preserves rΓ' h' Heval 2 Mut_r 3 [rROItem] [Iot 1] 0
              eq_refl (or_intror head_is_rda))
    as (vals' & Hobj & Hnth).
  exists vals'. split; [exact Hobj|]. symmetry. exact Hnth.
Qed.

(** The same, for the run exhibited above. *)
Theorem callP_preserves_run :
  exists vals',
    runtime_getObj hA 2 =
      Some (mkObj (mkruntime_type Mut_r 3 [rROItem]) vals') /\
    nth_error vals' 0 = Some (Iot 1).
Proof. exact (callP_preserves_head rΓA' hA callP_eval). Qed.

(* ------------------DELIVERABLE 5: THE RUN DOES SOMETHING------------------*)

(** The call evaluates.  The receiver is the Sorted at location 2, an object
    of the class with the self-referential bound, carrying the type argument
    @RO Item at run time.  The body read its head and the call stored the
    result, the Item at location 1, into x (variable 3), which was null
    before. *)
Theorem callP_not_vacuous :
  eval_stmt CT rΓA hA callP OK rΓA' hA /\
  (exists o, runtime_getObj hA 2 = Some o /\
             rt_type o = mkruntime_type Mut_r 3 [rROItem] /\
             nth_error (fields_map o) 0 = Some (Iot 1)) /\
  runtime_getVal rΓA 2 = Some (Iot 2) /\
  runtime_getVal rΓA 3 = Some Null_a /\
  runtime_getVal rΓpeek' (mreturn (mbody peek)) = Some (Iot 1) /\
  runtime_getVal rΓA' 3 = Some (Iot 1) /\
  rΓA <> rΓA'.
Proof.
  split; [exact callP_eval|].
  split; [eexists; split; [reflexivity | split; reflexivity]|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  discriminate.
Qed.

Print Assumptions fbound_ct_wf.
Print Assumptions fbound_ct_clean_bounds.
Print Assumptions ct_bounds_nm.
Print Assumptions peek_bound_checked.
Print Assumptions config_A.
Print Assumptions rsf_A.
Print Assumptions main_typed.
Print Assumptions callP_eval.
Print Assumptions callP_not_vacuous.
Print Assumptions callP_preserves_head.
Print Assumptions callP_preserves.
