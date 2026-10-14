From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds.

(** Readonly-state and transitive-state preservation with type parameters.

    Covered here: protected code may be generic and may be instantiated by its
    caller with any type arguments, including mutable ones (a protected
    container with mutable payload).  The protected code itself must not write
    a mutable, receiver-dependent, or bottom qualifier inside a type argument
    or as a qualifier argument of a call, and the bounds of the type parameters in scope of a protected method must
    not be headed by one of those qualifiers.  Inside such code a type
    variable is opaque: nothing is known, and nothing needs to be known, about
    the world of a value whose static type is a bare type variable. *)

(* ------------------WRITTEN HEADS AND CLEAN ARGUMENTS------------------*)

(** The written outer qualifier of a type, if it has one. *)
Definition whead (T : qualified_type) : option q :=
  match T with
  | TClass q0 _ _ => Some q0
  | TVar (TVQual q0) _ _ => Some q0
  | TVar TVSub _ _ => None
  | TVar (TVPoly _) _ _ => None
  | THead _ _ _ => None
  end.

Definition clean_q (q0 : q) : Prop := q0 <> Mut /\ q0 <> RDM /\ q0 <> Bot.

(** A type that may stand in an argument position of protected code. *)
Fixpoint clean_arg (T : qualified_type) : Prop :=
  match T with
  | TClass q0 _ args =>
      clean_q q0 /\
      (fix go (l : list qualified_type) : Prop :=
         match l with
         | [] => True
         | t :: r => clean_arg t /\ go r
         end) args
  | TVar TVSub _ _ => True
  | TVar (TVQual q0) _ _ => clean_q q0
  | TVar (TVPoly _) _ _ => True
  | THead _ _ args =>
      (fix go (l : list qualified_type) : Prop :=
         match l with
         | [] => True
         | t :: r => clean_arg t /\ go r
         end) args
  end.

Lemma clean_arg_go_Forall : forall l,
  (fix go (l : list qualified_type) : Prop :=
     match l with
     | [] => True
     | t :: r => clean_arg t /\ go r
     end) l <-> Forall clean_arg l.
Proof.
  induction l; simpl; split; intros H; auto.
  - destruct H. constructor; auto. apply IHl; auto.
  - inversion H; subst. split; auto. apply IHl; auto.
Qed.

Lemma clean_arg_class : forall q0 C args,
  clean_arg (TClass q0 C args) <-> clean_q q0 /\ Forall clean_arg args.
Proof. intros. simpl. rewrite clean_arg_go_Forall. reflexivity. Qed.

Lemma clean_arg_head : forall n C args,
  clean_arg (THead n C args) <-> Forall clean_arg args.
Proof. intros. simpl. rewrite clean_arg_go_Forall. reflexivity. Qed.

(** A type whose arguments are clean; its own head is unrestricted. *)
Definition clean_top (T : qualified_type) : Prop :=
  match T with
  | TClass _ _ args => Forall clean_arg args
  | TVar _ _ _ => True
  | THead _ _ args => Forall clean_arg args
  end.

Definition whead_clean (T : qualified_type) : Prop :=
  forall q0, whead T = Some q0 -> clean_q q0.

Lemma clean_arg_whead : forall T, clean_arg T -> whead_clean T.
Proof.
  intros T H q0 Hh. destruct T as [q1 C args | [|q1|mp] o n | n C args].
  - apply clean_arg_class in H. destruct H as [H _].
    simpl in Hh. inversion Hh; subst. exact H.
  - simpl in Hh. discriminate.
  - simpl in Hh, H. inversion Hh; subst. exact H.
  - simpl in Hh. discriminate.
  - simpl in Hh. discriminate.
Qed.

Lemma default_type_clean : clean_arg default_type.
Proof. simpl. repeat split; discriminate. Qed.

(** With no qualifier argument, a use under a qualifier parameter reads as
    readonly. *)
Lemma whead_subst_pvar_nil : forall cs ms mp o n,
  whead_clean (subst cs ms [] (TVar (TVPoly mp) o n)).
Proof.
  intros cs ms mp o n q0 Hq0. simpl in Hq0.
  assert (Hnil : nth_error (@nil qarg) mp = None) by (destruct mp; reflexivity).
  rewrite Hnil in Hq0. simpl in Hq0.
  destruct (match tv_lookup o cs ms n with Some U => U | None => default_type end);
    simpl in Hq0; inversion Hq0; subst; repeat split; discriminate.
Qed.

Lemma tv_lookup_clean : forall o cs ms n,
  Forall clean_arg cs -> Forall clean_arg ms ->
  clean_arg match tv_lookup o cs ms n with Some U => U | None => default_type end.
Proof.
  intros o cs ms n Hc Hm. destruct (tv_lookup o cs ms n) as [U|] eqn:Hl.
  - exact (tv_lookup_Forall clean_arg o cs ms n U Hc Hm Hl).
  - apply default_type_clean.
Qed.

(** A qualifier argument that may be written in protected code. *)
Definition clean_qarg (a : qarg) : Prop :=
  match a with
  | QLit q0 => clean_q q0
  | QVar _ => True
  end.

Lemma qvar_args_clean : forall k, Forall clean_qarg (qvar_args k).
Proof.
  intros k. unfold qvar_args. apply Forall_forall. intros a Hin.
  apply in_map_iff in Hin. destruct Hin as (i & <- & _). exact I.
Qed.

(** A class type under a clean qualifier argument has a clean head or no
    written head at all. *)
Lemma whead_qhead_clean : forall Qs n C args,
  Forall clean_qarg Qs -> whead_clean (qhead (nth_error Qs n) C args).
Proof.
  intros Qs n C args HQ q0 Hh.
  destruct (nth_error Qs n) as [[q1|m]|] eqn:E; simpl in Hh;
    try discriminate; inversion Hh; subst.
  - rewrite Forall_forall in HQ. exact (HQ _ (nth_error_In _ _ E)).
  - repeat split; discriminate.
Qed.

Lemma clean_arg_qhead : forall Qs n C args,
  Forall clean_qarg Qs -> Forall clean_arg args ->
  clean_arg (qhead (nth_error Qs n) C args).
Proof.
  intros Qs n C args HQ Ha.
  destruct (nth_error Qs n) as [[q1|m]|] eqn:E; simpl qhead.
  - apply clean_arg_class. split; auto.
    rewrite Forall_forall in HQ. exact (HQ _ (nth_error_In _ _ E)).
  - apply clean_arg_head. exact Ha.
  - apply clean_arg_class. split; auto. repeat split; discriminate.
Qed.

(** The written head of a member type seen through a receiver. *)
Lemma whead_member_some : forall mt q0 Vs Us Qs F qF,
  whead F = Some qF ->
  whead (member_type mt q0 Vs Us Qs F) = Some (vpa_q mt q0 qF).
Proof.
  intros mt q0 Vs Us Qs F qF H. unfold member_type, adapt.
  destruct F as [q1 C args | [|q1|mp] o n | n C args]; simpl in *; inversion H; subst; auto.
  destruct (match tv_lookup o Vs Us n with Some U => U | None => default_type end);
    reflexivity.
Qed.

Lemma whead_member_var : forall mt q0 Vs Us Qs o n,
  Forall clean_arg Vs -> Forall clean_arg Us ->
  whead_clean (member_type mt q0 Vs Us Qs (TVar TVSub o n)).
Proof.
  intros mt q0 Vs Us Qs o n HV HU. unfold member_type, adapt. simpl.
  apply clean_arg_whead. apply tv_lookup_clean; auto.
Qed.

(* ------------------CLEAN BOUND ENVIRONMENTS------------------*)

(** Every declared bound is a class type with a clean head and clean
    arguments. *)
Definition clean_bounds (Δ : tv_env) : Prop :=
  forall o n B, tv_bound Δ o n = Some B ->
    exists qb C Ts, B = TClass qb C Ts /\ clean_q qb /\ Forall clean_arg Ts.

(** Subtyping into a mutable, receiver-dependent, or bottom head comes only
    from that head or from bottom. *)
Lemma sub_whead : forall CT Δ T U,
  qualified_type_subtype CT Δ T U ->
  clean_bounds Δ ->
  forall qU, whead U = Some qU -> ~ clean_q qU ->
  whead T = Some qU \/ whead T = Some Bot.
Proof.
  intros CT Δ T U H HΔ. induction H; intros qU HU Hnc.
  - simpl in *. inversion HU; subst. inversion Hqsub; subst; auto.
    exfalso. apply Hnc. repeat split; discriminate.
  - simpl in *. auto.
  - discriminate.
  - destruct (HΔ _ _ _ Hbound) as (qb & C & Ts & -> & Hcl & _).
    simpl in HU. inversion HU; subst. contradiction.
  - simpl in *. inversion HU; subst. inversion Hqsub; subst; auto.
    exfalso. apply Hnc. repeat split; discriminate.
  - simpl in HU. inversion HU; subst.
    exfalso. apply Hnc. repeat split; discriminate.
  - discriminate.
  - simpl in HU. inversion HU; subst.
    exfalso. apply Hnc. repeat split; discriminate.
  - simpl in *. auto.
  - simpl in HU. inversion HU; subst.
    exfalso. apply Hnc. repeat split; discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - destruct (IHqualified_type_subtype2 _ HU Hnc) as [H2 | H2].
    + exact (IHqualified_type_subtype1 _ H2 Hnc).
    + assert (Hb : ~ clean_q Bot) by (intros (_ & _ & Hx); congruence).
      destruct (IHqualified_type_subtype1 _ H2 Hb); auto.
Qed.

(** The class type through which members are looked up, and its relation to
    the written head. *)
Lemma ubound_whead : forall Δ T qx C Ts,
  clean_bounds Δ -> clean_top T ->
  ubound Δ T = Some (TClass qx C Ts) ->
  Forall clean_arg Ts /\
  (whead T = Some qx \/ (whead T = None /\ clean_q qx)).
Proof.
  intros Δ T qx C Ts HΔ HT H.
  destruct T as [q0 C0 Ts0 | [|q0|mp] o n | n C0 Ts0]; simpl in *.
  - inversion H; subst. auto.
  - destruct (tv_bound Δ o n) as [B|] eqn:Hb; [|discriminate].
    destruct (HΔ _ _ _ Hb) as (qb & Cb & Tb & -> & Hcl & Hargs).
    inversion H; subst. auto.
  - destruct (tv_bound Δ o n) as [B|] eqn:Hb; [|discriminate].
    destruct B as [qb Cb [|t r]| |]; try discriminate.
    inversion H; subst. auto.
  - destruct (tv_bound Δ o n) as [B|] eqn:Hb; [|discriminate].
    destruct B as [qb Cb [|t r]| |]; try discriminate.
    destruct (Nat.ltb mp (qparams Δ)); [|discriminate].
    inversion H; subst. split; auto. right. split; auto.
    repeat split; discriminate.
  - destruct (Nat.ltb n (qparams Δ)); [|discriminate].
    inversion H; subst. split; auto. right. split; auto.
    repeat split; discriminate.
Qed.

Lemma lost_free_whead : forall T, lost_free T -> whead T <> Some Lost.
Proof.
  intros T H Hh. destruct T as [q0 C args | [|q0|mp] o n | n C args]; simpl in *.
  - destruct H as [Hq _]. congruence.
  - discriminate.
  - congruence.
  - discriminate.
  - discriminate.
Qed.

(** A location never inhabits a type written with a bottom head; one that
    inhabits a type written immutable is an immutable object, one written
    mutable a mutable object. *)
Lemma typable_whead_obj : forall CT h loc T qctx ca ma ka q0,
  wf_r_typable CT h loc T qctx ca ma ka -> whead T = Some q0 ->
  exists o, runtime_getObj h loc = Some o /\
            head_ok (rqtype (rt_type o)) (dynq (qr2q qctx) q0).
Proof.
  intros CT h loc T qctx ca ma ka q0 H Hh.
  unfold wf_r_typable, loc_has_rtype in H.
  destruct (runtime_getObj h loc) as [o|]; [|contradiction].
  exists o. split; auto.
  destruct T as [q1 C args | [|q1|mp] o1 n | n C args]; simpl in *.
  - inversion Hh; subst. tauto.
  - discriminate.
  - inversion Hh; subst.
    destruct (match tv_lookup o1 ca ma n with Some R => R | None => default_rtype end).
    simpl in H. tauto.
  - discriminate.
  - discriminate.
Qed.

Lemma typable_whead_not_bot : forall CT h loc T qctx ca ma ka,
  wf_r_typable CT h loc T qctx ca ma ka -> whead T <> Some Bot.
Proof.
  intros CT h loc T qctx ca ma ka H Hh.
  destruct (typable_whead_obj _ _ _ _ _ _ _ _ _ H Hh) as (o & _ & Hk).
  simpl in Hk. eapply head_ok_not_bot; eauto.
Qed.

Lemma typable_whead_imm : forall CT h loc T qctx ca ma ka,
  wf_r_typable CT h loc T qctx ca ma ka -> whead T = Some Imm ->
  r_muttype h loc = Some Imm_r.
Proof.
  intros CT h loc T qctx ca ma ka H Hh.
  destruct (typable_whead_obj _ _ _ _ _ _ _ _ _ H Hh) as (o & Ho & Hk).
  simpl in Hk. unfold r_muttype. rewrite Ho. f_equal.
  unfold head_ok in Hk. destruct (rqtype (rt_type o)); auto.
  destruct Hk as [Hx | [Hx | Hx]]; discriminate.
Qed.

(* ------------------THE INVARIANT, WITH WRITTEN HEADS------------------*)


Record heapW (P : Loc -> Prop) (CT : class_table) (h : heap)
    (col : coloring) (L : list nat) (next : nat) : Prop := {
  (* a coloured object exists, is unprotected, and is really mutable *)
  hw_col : forall l w, col l = Some w ->
    l < dom h /\ ~ P l /\ r_muttype h l = Some Mut_r /\ w < next;
  (* mutable and receiver-dependent fields of a live-world object stay in
     its world *)
  hw_in : forall l w o fs f fd v,
    col l = Some w -> List.In w L ->
    runtime_getObj h l = Some o ->
    CollectFields CT (rctype (rt_type o)) fs ->
    nth_error fs f = Some fd ->
    nth_error (fields_map o) f = Some (Iot v) ->
    (whead (ftype fd) = Some Mut \/ whead (ftype fd) = Some RDM) ->
    col v = Some w;
  (* receiver-dependent fields of an object outside the live worlds stay
     outside them *)
  hw_out : forall l o fs f fd v,
    ~ live col L l ->
    runtime_getObj h l = Some o ->
    CollectFields CT (rctype (rt_type o)) fs ->
    nth_error fs f = Some fd ->
    nth_error (fields_map o) f = Some (Iot v) ->
    whead (ftype fd) = Some RDM ->
    ~ live col L v;
  hw_live : forall w, List.In w L -> w < next;
}.

Record frameW (CT : class_table) (sΓ : s_env) (rΓ : r_env)
    (col : coloring) (L : list nat) (wf : nat) (mode : bool) : Prop := {
  fw_live : List.In wf L;
  fw_this : mode = true ->
    exists ι, get_this_var_mapping (vars rΓ) = Some ι /\ col ι = Some wf;
  fw_mut : forall x T v,
    static_getType sΓ x = Some T ->
    runtime_getVal rΓ x = Some (Iot v) ->
    whead T = Some Mut ->
    col v = Some wf;
  fw_rdm : forall x T v,
    static_getType sΓ x = Some T ->
    runtime_getVal rΓ x = Some (Iot v) ->
    whead T = Some RDM ->
    if mode then col v = Some wf else ~ live col L v;
}.

Lemma not_live_of_immW : forall P CT h col L next l,
  heapW P CT h col L next -> r_muttype h l = Some Imm_r -> ~ live col L l.
Proof.
  intros P CT h col L next l HG Himm (w & Hc & _).
  destruct (hw_col _ _ _ _ _ _ HG _ _ Hc) as (_ & _ & Hm & _). congruence.
Qed.

Lemma frameW_update : forall CT sΓ rΓ col L wf mode x v Tx,
  frameW CT sΓ rΓ col L wf mode ->
  x <> 0 ->
  static_getType sΓ x = Some Tx ->
  (forall w q0, v = Iot w -> whead Tx = Some q0 -> good col L wf mode q0 w) ->
  frameW CT sΓ (set_vars rΓ (update x v (vars rΓ))) col L wf mode.
Proof.
  intros CT sΓ rΓ col L wf mode x v Tx HF Hx HTx Hnew.
  assert (Hget : forall y w, runtime_getVal (set_vars rΓ (update x v (vars rΓ))) y
                               = Some (Iot w) ->
                  (y = x /\ v = Iot w) \/ (y <> x /\ runtime_getVal rΓ y = Some (Iot w))).
  { intros y w Hv. unfold runtime_getVal in *. simpl in Hv.
    destruct (Nat.eq_dec x y) as [-> | Hne].
    - left. split; auto. apply nth_error_update_same_inv in Hv. congruence.
    - right. rewrite update_diff in Hv; auto. }
  constructor.
  - exact (fw_live _ _ _ _ _ _ _ HF).
  - intros Hm. destruct (fw_this _ _ _ _ _ _ _ HF Hm) as (ι & Hthis & Hc).
    exists ι. simpl. rewrite get_this_var_mapping_update; auto.
  - intros y T w HT Hv Hh.
    destruct (Hget y w Hv) as [[-> ->] | [Hne Hv']].
    + assert (T = Tx) by (unfold static_getType in *; congruence). subst T.
      exact (Hnew w Mut eq_refl Hh).
    + eapply (fw_mut _ _ _ _ _ _ _ HF); eauto.
  - intros y T w HT Hv Hh.
    destruct (Hget y w Hv) as [[-> ->] | [Hne Hv']].
    + assert (T = Tx) by (unfold static_getType in *; congruence). subst T.
      exact (Hnew w RDM eq_refl Hh).
    + eapply (fw_rdm _ _ _ _ _ _ _ HF); eauto.
Qed.

Lemma heapW_update : forall P CT h col L next lx ox fsO f0 fd vy,
  heapW P CT h col L next ->
  runtime_getObj h lx = Some ox ->
  CollectFields CT (rctype (rt_type ox)) fsO ->
  nth_error fsO f0 = Some fd ->
  (forall w wv, col lx = Some w -> List.In w L -> vy = Iot wv ->
     (whead (ftype fd) = Some Mut \/ whead (ftype fd) = Some RDM) ->
     col wv = Some w) ->
  (forall wv, ~ live col L lx -> vy = Iot wv ->
     whead (ftype fd) = Some RDM -> ~ live col L wv) ->
  heapW P CT (update_field h lx f0 vy) col L next.
Proof.
  intros P CT h col L next lx ox fsO f0 fd vy HG Hox HcfO HnO HO1 HO2.
  constructor.
  - intros l w Hc. destruct (hw_col _ _ _ _ _ _ HG _ _ Hc) as (H1 & H2 & H3 & H4).
    rewrite update_field_length. rewrite update_field_r_muttype. auto.
  - intros l w o fs f fd0 v Hc Hin Hobj Hcf Hn Hval Hh.
    destruct (Nat.eq_dec lx l) as [-> | Hne].
    + rewrite (update_field_getObj_same _ _ _ _ _ Hox) in Hobj.
      inversion Hobj; subst o. simpl in *.
      assert (fs = fsO) by eauto using collect_fields_deterministic_rel. subst fs.
      destruct (Nat.eq_dec f0 f) as [-> | Hnf].
      * apply nth_error_update_same_inv in Hval. subst vy.
        assert (fd0 = fd) by congruence. subst fd0. eapply HO1; eauto.
      * rewrite update_diff in Hval; auto.
        eapply (hw_in _ _ _ _ _ _ HG); eauto.
    + rewrite update_field_getObj_diff in Hobj; auto.
      eapply (hw_in _ _ _ _ _ _ HG); eauto.
  - intros l o fs f fd0 v Hnl Hobj Hcf Hn Hval Hh.
    destruct (Nat.eq_dec lx l) as [-> | Hne].
    + rewrite (update_field_getObj_same _ _ _ _ _ Hox) in Hobj.
      inversion Hobj; subst o. simpl in *.
      assert (fs = fsO) by eauto using collect_fields_deterministic_rel. subst fs.
      destruct (Nat.eq_dec f0 f) as [-> | Hnf].
      * apply nth_error_update_same_inv in Hval. subst vy.
        assert (fd0 = fd) by congruence. subst fd0. eapply HO2; eauto.
      * rewrite update_diff in Hval; auto.
        eapply (hw_out _ _ _ _ _ _ HG); eauto.
    + rewrite update_field_getObj_diff in Hobj; auto.
      eapply (hw_out _ _ _ _ _ _ HG); eauto.
  - exact (hw_live _ _ _ _ _ _ HG).
Qed.

Lemma frameW_agree : forall CT sΓ rΓ h col col' L wf mode,
  frameW CT sΓ rΓ col L wf mode ->
  wf_renv CT rΓ h ->
  (forall l, l < dom h -> col' l = col l) ->
  frameW CT sΓ rΓ col' L wf mode.
Proof.
  intros CT sΓ rΓ h col col' L wf mode HF Hrenv Hag.
  constructor.
  - exact (fw_live _ _ _ _ _ _ _ HF).
  - intros Hm. destruct (fw_this _ _ _ _ _ _ _ HF Hm) as (ι & Hth & Hc).
    exists ι. split; auto. rewrite Hag; auto.
    destruct Hrenv as (_ & (i & Hi & Hd) & _). congruence.
  - intros x T v HT Hv Hh. rewrite Hag; [eapply var_value_dom; eauto|].
    eapply (fw_mut _ _ _ _ _ _ _ HF); eauto.
  - intros x T v HT Hv Hh.
    pose proof (fw_rdm _ _ _ _ _ _ _ HF _ _ _ HT Hv Hh) as Hr.
    assert (Hvd : v < dom h) by (eapply var_value_dom; eauto).
    destruct mode.
    + rewrite Hag; auto.
    + unfold live in *. rewrite Hag; auto.
Qed.

Lemma frameW_local : forall CT sΓ rΓ col L wf mode T,
  dom sΓ = dom (vars rΓ) ->
  frameW CT sΓ rΓ col L wf mode ->
  frameW CT (sΓ ++ [T]) (set_vars rΓ (vars rΓ ++ [Null_a])) col L wf mode.
Proof.
  intros CT sΓ rΓ col L wf mode T Hlen HF.
  assert (Hold : forall x T0 v,
            static_getType (sΓ ++ [T]) x = Some T0 ->
            runtime_getVal (set_vars rΓ (vars rΓ ++ [Null_a])) x = Some (Iot v) ->
            static_getType sΓ x = Some T0 /\ runtime_getVal rΓ x = Some (Iot v)).
  { intros x T0 v HT Hv. unfold static_getType, runtime_getVal in *. simpl in Hv.
    destruct (Nat.lt_ge_cases x (dom sΓ)) as [Hlt | Hge].
    - rewrite nth_error_app1 in HT; auto.
      rewrite nth_error_app1 in Hv; [lia|]. auto.
    - rewrite nth_error_app2 in Hv; [lia|].
      destruct (x - dom (vars rΓ)) as [|k]; simpl in Hv; [discriminate|].
      destruct k; discriminate. }
  constructor.
  - exact (fw_live _ _ _ _ _ _ _ HF).
  - intros Hm. destruct (fw_this _ _ _ _ _ _ _ HF Hm) as (ι & Hth & Hc).
    exists ι. simpl. rewrite get_this_var_mapping_app_null_last. auto.
  - intros x T0 v HT Hv Hh. destruct (Hold _ _ _ HT Hv).
    eapply (fw_mut _ _ _ _ _ _ _ HF); eauto.
  - intros x T0 v HT Hv Hh. destruct (Hold _ _ _ HT Hv).
    eapply (fw_rdm _ _ _ _ _ _ _ HF); eauto.
Qed.

Lemma heapW_push : forall P CT h col L next,
  heapW P CT h col L next ->
  heapW P CT h col (next :: L) (S next).
Proof.
  intros P CT h col L next HG.
  assert (Hnc : forall l, col l <> Some next).
  { intros l Hc. destruct (hw_col _ _ _ _ _ _ HG _ _ Hc) as (_ & _ & _ & Hlt). lia. }
  assert (Hlv : forall v, live col (next :: L) v <-> live col L v).
  { intros v. unfold live. split; intros (w & Hc & Hin).
    - destruct Hin as [<- | Hin]; [exfalso; eapply Hnc; eauto | eauto].
    - exists w. split; auto. right. auto. }
  constructor.
  - intros l w Hc. destruct (hw_col _ _ _ _ _ _ HG _ _ Hc) as (H1 & H2 & H3 & H4).
    repeat split; auto.
  - intros l w o fs f fd v Hc Hin. destruct Hin as [<- | Hin].
    + exfalso. eapply Hnc; eauto.
    + eapply (hw_in _ _ _ _ _ _ HG); eauto.
  - intros l o fs f fd v Hnl Ho Hcf Hn Hval Hh.
    rewrite Hlv in Hnl. rewrite Hlv.
    eapply (hw_out _ _ _ _ _ _ HG); eauto.
  - intros w [<- | Hin]; [lia|].
    pose proof (hw_live _ _ _ _ _ _ HG _ Hin). lia.
Qed.

Lemma heapW_pop : forall P CT h col L w0 next,
  heapW P CT h col (w0 :: L) next ->
  ~ List.In w0 L ->
  heapW P CT h col L next.
Proof.
  intros P CT h col L w0 next HG Hnin.
  constructor.
  - exact (hw_col _ _ _ _ _ _ HG).
  - intros l w o fs f fd v Hc Hin.
    eapply (hw_in _ _ _ _ _ _ HG); eauto. right. auto.
  - intros l o fs f fd v Hnl Ho Hcf Hn Hval Hh.
    destruct (live_dec col (w0 :: L) l) as [(w & Hc & Hin) | Hnl'].
    + destruct Hin as [<- | Hin]; [|exfalso; apply Hnl; exists w; auto].
      assert (Hcv : col v = Some w0).
      { eapply (hw_in _ _ _ _ _ _ HG); eauto; simpl; auto. }
      intros (w' & Hc' & Hin'). congruence.
    + pose proof (hw_out _ _ _ _ _ _ HG _ _ _ _ _ _ Hnl' Ho Hcf Hn Hval Hh) as Hv.
      intros (w' & Hc' & Hin'). apply Hv. exists w'. split; auto. right. auto.
  - intros w Hin. apply (hw_live _ _ _ _ _ _ HG). right. auto.
Qed.

Lemma live_pushW : forall P CT h col L next v,
  heapW P CT h col L next ->
  (live col (next :: L) v <-> live col L v).
Proof.
  intros P CT h col L next v HG. unfold live. split; intros (w & Hc & Hin).
  - destruct Hin as [<- | Hin]; [|eauto].
    destruct (hw_col _ _ _ _ _ _ HG _ _ Hc) as (_ & _ & _ & Hlt). lia.
  - exists w. split; auto. right. auto.
Qed.

(* ------------------CLEAN CLASS TABLES AND STATEMENTS------------------*)

Fixpoint clean_stmt (s : stmt) : Prop :=
  match s with
  | SLocal T _ => clean_top T
  | SNew _ _ _ Ts _ => Forall clean_arg Ts
  | SCall _ _ _ Us Qs _ => Forall clean_arg Us /\ Forall clean_qarg Qs
  | SSeq s1 s2 => clean_stmt s1 /\ clean_stmt s2
  | _ => True
  end.

Definition supers_clean (CT : class_table) : Prop :=
  forall C P Ss, parent_lookup CT C = Some (P, Ss) -> Forall clean_arg Ss.

Record clean_ct (CT : class_table) : Prop := {
  cc_supers : supers_clean CT;
  cc_methods : forall C def mdef,
    find_class CT C = Some def ->
    List.In mdef (methods (body def)) ->
    readonly_state_method_scope (mscope (msignature mdef)) ->
    clean_bounds (method_tv_env CT C (msignature mdef)) /\
    Forall clean_top (mreceiver (msignature mdef) :: mparams (msignature mdef)) /\
    clean_stmt (mbody_stmt (mbody mdef));
}.

(* ------------------FIELDS ACROSS INHERITANCE------------------*)

Lemma whead_requalify : forall q0 U, whead (requalify q0 U) = Some q0.
Proof. intros q0 [q1 C a|u o n| ? ? ?]; reflexivity. Qed.

Lemma whead_subst_some : forall cs ms ks F q0,
  whead F = Some q0 -> whead (subst cs ms ks F) = Some q0.
Proof.
  intros cs ms ks F q0 H. destruct F as [q1 C a | [|q1|mp] o n | n C a]; simpl in *;
    inversion H; subst; auto. apply whead_requalify.
Qed.

Lemma whead_subst_var : forall cs ms ks o n,
  Forall clean_arg cs -> Forall clean_arg ms ->
  whead_clean (subst cs ms ks (TVar TVSub o n)).
Proof.
  intros. simpl. apply clean_arg_whead. apply tv_lookup_clean; auto.
Qed.

(** A field found through a superclass view is, in the object's own class, at
    the same index with the same assignability; its written head is the same
    when it has one, and is clean when the declaration is a bare type
    variable. *)
Lemma field_in_objectW : forall CT qh Co Ro C Vs,
  supers_clean CT ->
  rsuper_inst CT qh Co Ro C Vs ->
  forall fsC fsO f fd,
    CollectFields CT C fsC -> CollectFields CT Co fsO ->
    nth_error fsC f = Some fd ->
    exists fd',
      nth_error fsO f = Some fd' /\
      assignability fd' = assignability fd /\
      (forall q0, whead (ftype fd) = Some q0 -> whead (ftype fd') = Some q0) /\
      (whead (ftype fd) = None -> whead_clean (ftype fd')).
Proof.
  intros CT qh Co Ro C Vs Hsc H.
  induction H; intros fsC fsO f fd HcfC HcfO Hn.
  - assert (fsO = fsC) by eauto using collect_fields_deterministic_rel.
    subst. exists fd. repeat split; auto; intros Hnone q0 Hq; congruence.
  - destruct (CollectFields_inherit_inv _ _ _ _ _ Hparent HcfO)
      as (def & pfs & Hfind & Hpcf & ->).
    destruct (IHrsuper_inst fsC pfs f fd HcfC Hpcf Hn)
      as (fdP & HnP & Ha & Hsome & Hnone).
    exists (subst_field Ss fdP). refine (conj _ (conj Ha (conj _ _))).
    + rewrite nth_error_app1.
      * rewrite length_map. apply nth_error_Some. congruence.
      * rewrite nth_error_map. rewrite HnP. reflexivity.
    + intros q0 Hq. simpl. apply whead_subst_some. auto.
    + intros Hq. specialize (Hnone Hq). simpl.
      pose proof (Hsc _ _ _ Hparent) as HSs.
      destruct (ftype fdP) as [q1 C1 a1 | [|q1|mp] o1 n1 | n1 C1 a1] eqn:HfP.
      * intros q0 Hq0. simpl in Hq0. inversion Hq0; subst.
        apply Hnone. reflexivity.
      * apply whead_subst_var; auto.
      * intros q0 Hq0.
        rewrite (whead_subst_some Ss [] [] (TVar (TVQual q1) o1 n1) q1 eq_refl) in Hq0.
        inversion Hq0; subst. apply Hnone. reflexivity.
      * intros q0 Hq0. simpl in Hq0.
        assert (Hnil : nth_error (@nil qarg) mp = None) by (destruct mp; reflexivity).
        rewrite Hnil in Hq0. simpl in Hq0.
        destruct (match tv_lookup o1 Ss [] n1 with Some U => U | None => default_type end);
          simpl in Hq0; inversion Hq0; subst; repeat split; discriminate.
      * simpl subst. apply whead_qhead_clean. constructor.
Qed.

(* ------------------WHAT A STATIC TYPE SAYS ABOUT A VALUE------------------*)

Definition goodT (col : coloring) (L : list nat) (wf : nat) (mode : bool)
    (T : qualified_type) (v : Loc) : Prop :=
  forall q0, whead T = Some q0 -> good col L wf mode q0 v.

Lemma good_clean : forall P CT h col L next wf mode loc T qctx ca ma ka q0,
  heapW P CT h col L next ->
  wf_r_typable CT h loc T qctx ca ma ka ->
  whead T = Some q0 -> clean_q q0 ->
  good col L wf mode q0 loc.
Proof.
  intros P CT h col L next wf mode loc T qctx ca ma ka q0 HG Hty Hh (H1 & H2 & H3).
  destruct q0; simpl; auto; try congruence.
  eapply not_live_of_immW; eauto using typable_whead_imm.
Qed.

Lemma not_clean_cases : forall q0, ~ clean_q q0 \/ clean_q q0.
Proof.
  intros q0. destruct q0;
    try (right; repeat split; discriminate);
    left; intros (H1 & H2 & H3); congruence.
Qed.

Section FrameW.
  Variables (P : Loc -> Prop) (CT : class_table) (Δ : tv_env).
  Variables (sΓ : s_env) (rΓ : r_env) (h : heap).
  Variables (col : coloring) (L : list nat) (next wf : nat) (mode : bool).
  Variables (ι : Loc) (o : Obj).
  Hypothesis HΔ : clean_bounds Δ.
  Hypothesis Hwf : wf_r_config CT Δ sΓ rΓ h.
  Hypothesis HG : heapW P CT h col L next.
  Hypothesis HF : frameW CT sΓ rΓ col L wf mode.
  Hypothesis Hthis : get_this_var_mapping (vars rΓ) = Some ι.
  Hypothesis Hobj : runtime_getObj h ι = Some o.
  Hypothesis Hfb :
    frame_bounds_ok CT Δ (qr2q (rqtype (rt_type o))) (cargs rΓ) (margs rΓ) (qargs rΓ).

  Lemma var_goodT : forall x T v,
    static_getType sΓ x = Some T ->
    runtime_getVal rΓ x = Some (Iot v) ->
    goodT col L wf mode T v.
  Proof.
    intros x T v HT Hv q0 Hh.
    pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj HT) as Hty.
    rewrite Hv in Hty.
    destruct q0; simpl; auto.
    - eapply (fw_mut _ _ _ _ _ _ _ HF); eauto.
    - eapply not_live_of_immW; eauto using typable_whead_imm.
    - eapply (fw_rdm _ _ _ _ _ _ _ HF); eauto.
  Qed.

  Lemma goodT_sub : forall T U v,
    qualified_type_subtype CT Δ T U ->
    wf_r_typable CT h v T (rqtype (rt_type o)) (cargs rΓ) (margs rΓ) (qargs rΓ) ->
    goodT col L wf mode T v ->
    goodT col L wf mode U v.
  Proof.
    intros T U v Hsub Hty Hg qU HU.
    destruct (not_clean_cases qU) as [Hnc | Hc].
    - destruct (sub_whead _ _ _ _ Hsub HΔ _ HU Hnc) as [HT | HT].
      + apply Hg; auto.
      + exfalso. eapply typable_whead_not_bot; eauto.
    - assert (HtyU : wf_r_typable CT h v U (rqtype (rt_type o))
                       (cargs rΓ) (margs rΓ) (qargs rΓ)).
      { eapply wf_r_typable_subtype; [exact Hfb | exact Hsub | exact Hty]. }
      exact (good_clean P CT h col L next wf mode v U _ _ _ _ qU HG HtyU HU Hc).
  Qed.

  (** The receiver of a member access, seen at the class type through which
      the member is looked up. *)
  Lemma recv_good : forall T v qx C Ts,
    clean_top T ->
    ubound Δ T = Some (TClass qx C Ts) ->
    wf_r_typable CT h v T (rqtype (rt_type o)) (cargs rΓ) (margs rΓ) (qargs rΓ) ->
    goodT col L wf mode T v ->
    good col L wf mode qx v /\ Forall clean_arg Ts /\ qx <> Bot /\
    wf_r_typable CT h v (TClass qx C Ts) (rqtype (rt_type o)) (cargs rΓ) (margs rΓ) (qargs rΓ).
  Proof.
    intros T v qx C Ts HT Hub Hty Hg.
    destruct (ubound_whead _ _ _ _ _ HΔ HT Hub) as [Hcl Hh].
    pose proof (wf_r_typable_ubound _ _ _ _ _ _ _ _ _ _ Hfb Hub Hty) as Hty'.
    refine (conj _ (conj Hcl (conj _ Hty'))).
    - destruct Hh as [Hh | [_ Hc]].
      + apply Hg; auto.
      + exact (good_clean P CT h col L next wf mode v (TClass qx C Ts) _ _ _ _ qx
                 HG Hty' eq_refl Hc).
    - intros ->. eapply (typable_whead_not_bot _ _ _ _ _ _ _ _ Hty'). reflexivity.
  Qed.
End FrameW.

(* ------------------EXPRESSIONS, ASSIGNMENT, CAST------------------*)

Lemma obj_fieldW : forall CT h loc qx C Ts qctx ca ma ka f fd,
  supers_clean CT -> wf_heap CT h ->
  wf_r_typable CT h loc (TClass qx C Ts) qctx ca ma ka ->
  sf_def_rel CT C f fd ->
  exists o fsO fd',
    runtime_getObj h loc = Some o /\
    CollectFields CT (rctype (rt_type o)) fsO /\
    nth_error fsO f = Some fd' /\
    assignability fd' = assignability fd /\
    (forall q0, whead (ftype fd) = Some q0 -> whead (ftype fd') = Some q0) /\
    (whead (ftype fd) = None -> whead_clean (ftype fd')).
Proof.
  intros CT h loc qx C Ts qctx ca ma ka f fd Hsc Hheap Hty Hfld.
  destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ _ Hty)
    as (o & Vs & Hobj & _ & Hsup & _).
  pose proof (Hheap loc (runtime_getObj_dom _ _ _ Hobj)) as Hwfo.
  unfold wf_obj in Hwfo. rewrite Hobj in Hwfo.
  destruct Hwfo as (_ & fsO & HcfO & _).
  inversion Hfld as [? ? fsC ? ? HcfC HgetC]; subst.
  destruct (field_in_objectW _ _ _ _ _ _ Hsc Hsup _ _ _ _ HcfC HcfO HgetC)
    as (fd' & H1 & H2 & H3 & H4).
  exists o, fsO, fd'.
  exact (conj Hobj (conj HcfO (conj H1 (conj H2 (conj H3 H4))))).
Qed.

Lemma senv_clean : forall (sΓ : s_env) x T,
  Forall clean_top sΓ -> static_getType sΓ x = Some T -> clean_top T.
Proof.
  intros sΓ x T H Hx. rewrite Forall_forall in H. apply H.
  unfold static_getType in Hx. eapply nth_error_In; eauto.
Qed.

Lemma expr_goodT : forall P CT Δ sΓ rΓ h col L next wf mode mt e Te w ι o,
  supers_clean CT -> clean_bounds Δ -> Forall clean_top sΓ ->
  readonly_state_method_scope mt ->
  wf_r_config CT Δ sΓ rΓ h ->
  heapW P CT h col L next ->
  frameW CT sΓ rΓ col L wf mode ->
  get_this_var_mapping (vars rΓ) = Some ι ->
  runtime_getObj h ι = Some o ->
  frame_bounds_ok CT Δ (qr2q (rqtype (rt_type o))) (cargs rΓ) (margs rΓ) (qargs rΓ) ->
  expr_has_type CT Δ sΓ mt e Te ->
  eval_expr CT rΓ h e (Iot w) OK rΓ h ->
  goodT col L wf mode Te w.
Proof.
  intros P CT Δ sΓ rΓ h col L next wf mode mt e Te w ι o
    Hsc HΔ Hcl Hrs Hwf HG HF Hthis Hobj Hfb Htype Heval.
  pose proof (expr_eval_typable _ _ _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hfb Htype Heval)
    as Hty. simpl in Hty.
  inversion Htype; subst; inversion Heval; subst.
  - eapply var_goodT; eauto.
  - pose proof Hwf as (Hct & Hheap & _).
    pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_x) as Hyty.
    rewrite Hval in Hyty.
    pose proof (var_goodT P CT Δ sΓ rΓ h col L next wf mode ι o Hwf HG HF
                  Hthis Hobj _ _ _ Hget_x Hval) as Hgy.
    destruct (recv_good P CT Δ rΓ h col L next wf mode o HΔ HG Hfb
                _ _ _ _ _ (senv_clean _ _ _ Hcl Hget_x) Hub Hyty Hgy)
      as (Hgx & HTs & _ & Hyty').
    destruct (obj_fieldW _ _ _ _ _ _ _ _ _ _ _ _ Hsc Hheap Hyty' Hfld_def)
      as (oy & fsO & fd' & Hoy & HcfO & HnO & _ & Hsome & Hnone).
    rewrite Hobj0 in Hoy. inversion Hoy; subst oy. clear Hoy.
    intros q0 Hh.
    destruct (whead (ftype fDef)) as [qF|] eqn:HqF.
    + rewrite (whead_member_some _ _ _ _ _ _ _ HqF) in Hh. inversion Hh; subst q0.
      destruct (rs_vpa_cases mt qx qF Hrs) as [Hmut Hrdm].
      destruct (vpa_q mt qx qF) eqn:Hv; simpl; auto.
      * destruct (Hmut eq_refl) as [-> HqF']. simpl in Hgx.
        eapply (hw_in _ _ _ _ _ _ HG _ _ _ _ _ _ _ Hgx
                  (fw_live _ _ _ _ _ _ _ HF) Hobj0 HcfO HnO Hfield).
        rewrite (Hsome _ eq_refl). destruct HqF' as [-> | ->]; auto.
      * eapply not_live_of_immW; eauto.
        eapply typable_whead_imm; eauto.
        rewrite (whead_member_some _ _ _ _ _ _ _ HqF). rewrite Hv. reflexivity.
      * destruct (Hrdm eq_refl) as [-> ->]. simpl in Hgx.
        destruct mode.
        -- eapply (hw_in _ _ _ _ _ _ HG _ _ _ _ _ _ _ Hgx
                     (fw_live _ _ _ _ _ _ _ HF) Hobj0 HcfO HnO Hfield).
           rewrite (Hsome _ eq_refl). auto.
        -- eapply (hw_out _ _ _ _ _ _ HG _ _ _ _ _ _ Hgx Hobj0 HcfO HnO Hfield).
           apply Hsome. reflexivity.
    + destruct (ftype fDef) as [q1 C1 a1 | [|q1|mp] o1 n1 | n1 C1 a1] eqn:HF0;
        simpl in HqF; try discriminate.
      * eapply good_clean; eauto.
        eapply (whead_member_var mt qx Ts [] [] o1 n1); eauto.
      * assert (Hwc : whead_clean (member_type mt qx Ts [] [] (TVar (TVPoly mp) o1 n1))).
        { unfold member_type, adapt. simpl map_qual. apply whead_subst_pvar_nil. }
        eapply good_clean; eauto.
      * assert (Hwc : whead_clean (member_type mt qx Ts [] [] (THead n1 C1 a1))).
        { unfold member_type, adapt. simpl.
          apply whead_qhead_clean. constructor. }
        eapply good_clean; eauto.
Qed.

Lemma rg_assign : forall P CT Δ sΓ rΓ h col L next wf mode mt x e v sΓ',
  supers_clean CT -> clean_bounds Δ -> Forall clean_top sΓ ->
  readonly_state_method_scope mt ->
  wf_r_config CT Δ sΓ rΓ h ->
  heapW P CT h col L next ->
  frameW CT sΓ rΓ col L wf mode ->
  stmt_typing CT Δ sΓ mt (SVarAss x e) sΓ' ->
  eval_expr CT rΓ h e v OK rΓ h ->
  frameW CT sΓ' (set_vars rΓ (update x v (vars rΓ))) col L wf mode.
Proof.
  intros P CT Δ sΓ rΓ h col L next wf mode mt x e v sΓ'
    Hsc HΔ Hcl Hrs Hwf HG HF Htype Heval.
  inversion Htype; subst.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & _ & _ & _ & Hfb).
  eapply frameW_update; eauto.
  intros w q0 -> HhTx.
  pose proof (expr_eval_typable _ _ _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hfb Htype_e Heval)
    as Hty. simpl in Hty.
  eapply (goodT_sub P CT Δ rΓ h col L next wf mode o HΔ HG Hfb _ _ _ Hsub Hty);
    auto.
  eapply expr_goodT; eauto.
Qed.

Lemma rg_cast : forall P CT Δ sΓ rΓ h col L next wf mode mt x T y v sΓ',
  clean_bounds Δ ->
  readonly_state_method_scope mt ->
  wf_r_config CT Δ sΓ rΓ h ->
  heapW P CT h col L next ->
  frameW CT sΓ rΓ col L wf mode ->
  stmt_typing CT Δ sΓ mt (SCast x T y) sΓ' ->
  runtime_getVal rΓ y = Some v ->
  frameW CT sΓ' (set_vars rΓ (update x v (vars rΓ))) col L wf mode.
Proof.
  intros P CT Δ sΓ rΓ h col L next wf mode mt x T y v sΓ'
    HΔ Hrs Hwf HG HF Htype Hval.
  inversion Htype; subst.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & _ & _ & _ & Hfb).
  eapply frameW_update; eauto.
  intros w q0 -> HhTx.
  assert (Hsub' : qualified_type_subtype CT Δ Ty Tx).
  { destruct Hsource as [Hs | Hnarrow].
    - eapply qtype_trans; eauto.
    - exfalso. destruct Hrs as [-> | ->]; simpl in Hscope; auto. }
  pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_y) as Hty.
  rewrite Hval in Hty.
  eapply (goodT_sub P CT Δ rΓ h col L next wf mode o HΔ HG Hfb _ _ _ Hsub' Hty);
    auto.
  eapply var_goodT; eauto.
Qed.

(* ------------------FIELD WRITE------------------*)

Lemma rg_fldwrite : forall P CT Δ sΓ rΓ h col L next wf mode mt x f0 y sΓ'
    lx ox a0 vf vy,
  supers_clean CT -> clean_bounds Δ -> Forall clean_top sΓ ->
  readonly_state_method_scope mt ->
  wf_r_config CT Δ sΓ rΓ h ->
  heapW P CT h col L next ->
  frameW CT sΓ rΓ col L wf mode ->
  stmt_typing CT Δ sΓ mt (SFldWrite x f0 y) sΓ' ->
  runtime_getVal rΓ x = Some (Iot lx) ->
  runtime_getObj h lx = Some ox ->
  getVal (fields_map ox) f0 = Some vf ->
  sf_assignability_rel CT (rctype (rt_type ox)) f0 a0 ->
  runtime_getVal rΓ y = Some vy ->
  heapW P CT (update_field h lx f0 vy) col L next /\
  prot_preserved P CT mt h (update_field h lx f0 vy).
Proof.
  intros P CT Δ sΓ rΓ h col L next wf mode mt x f0 y sΓ' lx ox a0 vf vy
    Hsc HΔ Hcl Hrs Hwf HG HF Htype Hvx Hox Hvf Hassign Hvy.
  inversion Htype; subst.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & _ & _ & _ & Hfb).
  pose proof Hwf as (Hct & Hheap & _).
  pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_x) as Hxty.
  rewrite Hvx in Hxty.
  pose proof (var_goodT P CT Δ sΓ' rΓ h col L next wf mode ι o Hwf HG HF
                Hthis Hobj _ _ _ Hget_x Hvx) as Hgx0.
  destruct (recv_good P CT Δ rΓ h col L next wf mode o HΔ HG Hfb
              _ _ _ _ _ (senv_clean _ _ _ Hcl Hget_x) Hub Hxty Hgx0)
    as (Hgx & HTs & Hqxb & Hxty').
  destruct (obj_fieldW _ _ _ _ _ _ _ _ _ _ _ _ Hsc Hheap Hxty' Hfld_def)
    as (ox' & fsO & fd' & Hox' & HcfO & HnO & Hassign_eq & Hsome & Hnone).
  rewrite Hox in Hox'. inversion Hox'; subst ox'. clear Hox'.
  destruct Hsub as [Hsub Hok].
  (* what the written field's head says about receiver and value *)
  assert (Hcase : forall wv qF',
            vy = Iot wv -> whead (ftype fd') = Some qF' ->
            qF' = Mut \/ qF' = RDM ->
            (forall w, col lx = Some w -> List.In w L -> col wv = Some w) /\
            (~ live col L lx -> qF' = RDM -> ~ live col L wv)).
  { intros wv qF' -> Hh' HqF'.
    pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_y) as Hyty.
    rewrite Hvy in Hyty.
    destruct (whead (ftype fieldT)) as [qF|] eqn:HqF.
    - rewrite (Hsome _ eq_refl) in Hh'. inversion Hh'; subst qF'.
      pose proof (whead_member_some mt qx Ts [] [] _ _ HqF) as Hmh.
      assert (Hnl : vpa_q mt qx qF <> Lost).
      { intros Hl. pose proof Hok as Hlf.
          apply (lost_free_whead _ Hlf). rewrite Hmh. rewrite Hl. reflexivity. }
      assert (Hgv : good col L wf mode (vpa_q mt qx qF) wv).
      { eapply (goodT_sub P CT Δ rΓ h col L next wf mode o HΔ HG Hfb
                  _ _ _ Hsub Hyty); auto.
        eapply var_goodT; eauto. }
      destruct (write_worlds mt qx qF col L wf mode lx wv Hrs Hnl Hqxb
                  (fw_live _ _ _ _ _ _ _ HF) Hgx Hgv) as [H1 H2].
      split; [intros w Hc Hin; apply H1; auto | exact H2].
    - exfalso. destruct (Hnone eq_refl _ Hh') as (H1 & H2 & _).
      destruct HqF'; congruence. }
  split.
  - eapply heapW_update; eauto.
    + intros w wv Hc Hin Hvyeq Hh.
      destruct Hh as [Hh | Hh];
        destruct (Hcase wv _ Hvyeq Hh) as [H1 _]; auto.
    + intros wv Hnlx Hvyeq Hh.
      destruct (Hcase wv _ Hvyeq Hh) as [_ H2]; auto.
  - intros l qr C0 Rs0 vals f HP Hl Hprot.
    destruct (Nat.eq_dec lx l) as [-> | Hne].
    + rewrite Hl in Hox. inversion Hox; subst ox. simpl in *.
      rewrite (update_field_getObj_same _ _ _ _ _ Hl). simpl.
      eexists. split; [reflexivity|].
      destruct (Nat.eq_dec f0 f) as [-> | Hnf].
      * exfalso.
        assert (Ha0 : a0 = assignability fieldT).
        { destruct Hassign as (fdO & HlookO & Ha).
          inversion HlookO as [? ? fs2 ? ? Hcf2 Hget2]; subst.
          assert (fs2 = fsO) by eauto using collect_fields_deterministic_rel.
          subst fs2. unfold gget in Hget2. congruence. }
        assert (Hqx : qx = Mut).
        { destruct Hprot as [Hp | [Hp | Hstrict]].
          - pose proof (sf_assignability_deterministic_rel _ _ _ _ _ Hassign Hp)
              as Heq.
            rewrite Ha0 in Heq. rewrite Heq in Hassignable.
            destruct mt, qx; simpl in Hassignable; discriminate.
          - pose proof (sf_assignability_deterministic_rel _ _ _ _ _ Hassign Hp)
              as Heq.
            rewrite Ha0 in Heq. rewrite Heq in Hassignable.
            destruct mt, qx; simpl in Hassignable; try discriminate; reflexivity.
          - destruct Hstrict as [-> | ->];
              destruct qx, (assignability fieldT); simpl in Hassignable;
              try discriminate; reflexivity. }
        subst qx. simpl in Hgx.
        destruct (hw_col _ _ _ _ _ _ HG _ _ Hgx) as (_ & HnP & _). auto.
      * symmetry. apply update_diff; auto.
    + rewrite update_field_getObj_diff; auto. exists vals. split; auto.
Qed.

(* ------------------OBJECT CREATION------------------*)

(** A supertype of a class type is a class type with a related head. *)
Lemma sub_class_head : forall CT Δ T U,
  qualified_type_subtype CT Δ T U ->
  forall q1 C Ts, T = TClass q1 C Ts -> q1 <> Bot ->
  exists qU D Us, U = TClass qU D Us /\ (q1 = qU \/ qU = RO \/ q1 = Bot).
Proof.
  intros CT Δ T U H. induction H; intros qa Ca Tsa HT Hnb; try discriminate.
  - inversion HT; subst. eexists _, _, _. split; [reflexivity|].
    inversion Hqsub; subst; auto.
  - inversion HT; subst. eauto 8.
  - inversion HT; subst. congruence.
  - destruct (IHqualified_type_subtype1 _ _ _ HT Hnb) as (q2 & D2 & U2 & -> & H12).
    assert (Hnb2 : q2 <> Bot).
    { destruct H12 as [<- | [-> | ->]]; congruence. }
    destruct (IHqualified_type_subtype2 _ _ _ eq_refl Hnb2)
      as (q3 & D3 & U3 & -> & H23).
    eexists _, _, _. split; [reflexivity|].
    destruct H12 as [-> | [-> | ->]]; auto.
    destruct H23 as [<- | [-> | H23]]; auto. congruence.
Qed.

Lemma rg_new : forall P CT Δ sΓ rΓ h col L next wf mode mt x qc C Ts ys sΓ'
    l1 qthisr vals,
  clean_bounds Δ ->
  wf_r_config CT Δ sΓ rΓ h ->
  heapW P CT h col L next ->
  frameW CT sΓ rΓ col L wf mode ->
  stmt_typing CT Δ sΓ mt (SNew x qc C Ts ys) sΓ' ->
  runtime_getVal rΓ 0 = Some (Iot l1) ->
  runtime_lookup_list rΓ ys = Some vals ->
  r_muttype h l1 = Some qthisr ->
  (forall l, P l -> l < dom h) ->
  let onew := mkObj
                (mkruntime_type (vpa_mutability_object_creation qthisr qc) C
                   (map (dyn (qr2q qthisr) (cargs rΓ) (margs rΓ) (qargs rΓ)) Ts)) vals in
  let col' := col_ext col (dom h) (new_color qc wf mode) in
  heapW P CT (h ++ [onew]) col' L next /\
  frameW CT sΓ' (set_vars rΓ (update x (Iot (dom h)) (vars rΓ))) col' L wf mode /\
  (forall l, l < dom h -> col' l = col l).
Proof.
  intros P CT Δ sΓ rΓ h col L next wf mode mt x qc C Ts ys sΓ' l1 qthisr vals
    HΔ Hwf HG HF Htype Hthis0 Hvals Hmut HPdom onew col'.
  inversion Htype; subst.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & Hmut' & _ & _ & Hfb).
  pose proof Hwf as (Hct & Hheap & Hrenv & _).
  apply get_this_runtime_getVal in Hthis0.
  assert (l1 = ι) by congruence. subst l1.
  pose proof (fw_live _ _ _ _ _ _ _ HF) as HwfL.
  assert (Hold : forall l, l < dom h -> col' l = col l).
  { intros l Hl. unfold col'. apply col_ext_other. lia. }
  assert (Hliveold : forall v, v < dom h -> (live col' L v <-> live col L v)).
  { intros v Hv. unfold col'. apply live_col_ext_other. lia. }
  assert (Hnew : col' (dom h) = new_color qc wf mode)
    by (unfold col'; apply col_ext_same).
  assert (Hcolored_dom : forall l w, col l = Some w -> l < dom h).
  { intros l w Hc. destruct (hw_col _ _ _ _ _ _ HG _ _ Hc); auto. }
  assert (Harg : forall f fd v,
            nth_error fds f = Some fd ->
            nth_error vals f = Some (Iot v) ->
            v < dom h /\
            forall qF, whead (ftype fd) = Some qF ->
              good col L wf mode (vpa_q AbstractState (qc2q qc) qF) v).
  { intros f fd v Hfd Hv.
    destruct (lookup_lists_nth _ _ _ _ _ _ _ Hget_args Hvals Hv)
      as (y & A & HyA & Hyv & HnA).
    pose proof (Forall2_nth_error_rel _ _ _ f Harg_sub) as Hrel.
    rewrite HnA in Hrel. rewrite Hfd in Hrel. destruct Hrel as [Hsub Hok].
    split; [eapply var_value_dom; eauto|].
    intros qF HqF.
    pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj HyA) as Hty.
    rewrite Hyv in Hty.
    pose proof (whead_member_some mt (qc2q qc) Ts [] [] _ _ HqF) as Hmh.
    assert (Hnl : vpa_q mt (qc2q qc) qF <> Lost).
    { intros Hl. pose proof Hok as Hlf.
        apply (lost_free_whead _ Hlf). rewrite Hmh. rewrite Hl. reflexivity. }
    rewrite <- (vpa_eq_as _ _ _ Hnl).
    eapply (goodT_sub P CT Δ rΓ h col L next wf mode o HΔ HG Hfb
              _ _ _ Hsub Hty).
    - eapply var_goodT; eauto.
    - exact Hmh. }
  assert (HG' : heapW P CT (h ++ [onew]) col' L next).
  { constructor.
    - intros l w Hc.
      destruct (Nat.eq_dec l (dom h)) as [-> | Hne].
      + rewrite Hnew in Hc.
        assert (Hw : w = wf).
        { destruct qc, mode; simpl in Hc; congruence. }
        subst w. refine (conj _ (conj _ (conj _ _))).
        * rewrite length_app. simpl. lia.
        * intros HP. apply HPdom in HP. lia.
        * unfold r_muttype, onew. rewrite runtime_getObj_last. simpl. f_equal.
          apply creation_mut.
          destruct qc, mode; simpl in Hc; try discriminate; auto.
          right. split; auto.
          destruct (fw_this _ _ _ _ _ _ _ HF eq_refl) as (ι0 & Hth0 & Hc0).
          assert (ι0 = ι) by congruence. subst ι0.
          destruct (hw_col _ _ _ _ _ _ HG _ _ Hc0) as (_ & _ & Hm & _). congruence.
        * exact (hw_live _ _ _ _ _ _ HG _ HwfL).
      + unfold col' in Hc. rewrite col_ext_other in Hc; auto.
        destruct (hw_col _ _ _ _ _ _ HG _ _ Hc) as (H1 & H2 & H3 & H4).
        refine (conj _ (conj H2 (conj _ H4))).
        * rewrite length_app. lia.
        * unfold r_muttype in *. unfold onew. rewrite runtime_getObj_last2; auto.
    - intros l w o0 fs f fd v Hc Hin Ho Hcf Hn Hval Hh.
      destruct (Nat.eq_dec l (dom h)) as [-> | Hne].
      + unfold onew in Ho. rewrite runtime_getObj_last in Ho.
        inversion Ho; subst o0. simpl in *.
        assert (fs = fds) by eauto using collect_fields_deterministic_rel. subst fs.
        destruct (Harg _ _ _ Hn Hval) as (Hvd & Hgood).
        rewrite Hold; auto. rewrite Hnew in Hc.
        destruct Hh as [Hh | Hh]; specialize (Hgood _ Hh);
          destruct qc, mode; simpl in *; try discriminate; congruence.
      + unfold col' in Hc. rewrite col_ext_other in Hc; auto.
        pose proof (Hcolored_dom _ _ Hc) as Hl.
        unfold onew in Ho. rewrite runtime_getObj_last2 in Ho; auto.
        rewrite Hold; [eapply heap_field_dom; eauto|].
        eapply (hw_in _ _ _ _ _ _ HG); eauto.
    - intros l o0 fs f fd v Hnl Ho Hcf Hn Hval Hh.
      destruct (Nat.eq_dec l (dom h)) as [-> | Hne].
      + unfold onew in Ho. rewrite runtime_getObj_last in Ho.
        inversion Ho; subst o0. simpl in *.
        assert (fs = fds) by eauto using collect_fields_deterministic_rel. subst fs.
        destruct (Harg _ _ _ Hn Hval) as (Hvd & Hgood).
        rewrite Hliveold; auto. specialize (Hgood _ Hh).
        assert (Hnc : new_color qc wf mode = None).
        { destruct (new_color qc wf mode) as [w|] eqn:Hnc; auto.
          exfalso. apply Hnl. exists w. split; [rewrite Hnew; auto|].
          destruct qc, mode; simpl in Hnc; try discriminate;
            inversion Hnc; subst; auto. }
        destruct qc, mode; simpl in *; try discriminate; auto.
      + assert (Hl : l < dom h).
        { apply runtime_getObj_dom in Ho. rewrite length_app in Ho. simpl in Ho. lia. }
        unfold onew in Ho. rewrite runtime_getObj_last2 in Ho; auto.
        rewrite Hliveold in Hnl; auto.
        rewrite Hliveold; [eapply heap_field_dom; eauto|].
        eapply (hw_out _ _ _ _ _ _ HG); eauto.
    - exact (hw_live _ _ _ _ _ _ HG). }
  refine (conj HG' (conj _ Hold)).
  assert (HF0 : frameW CT sΓ' rΓ col' L wf mode).
  { eapply frameW_agree; eauto. }
  eapply frameW_update; eauto.
  intros w q0 Hw HhTx. inversion Hw; subst w.
  destruct (sub_class_head _ _ _ _ Hresult_sub _ _ _ eq_refl
              ltac:(destruct qc; discriminate))
    as (qU & D & Us & -> & Hq).
  simpl in HhTx. inversion HhTx; subst q0.
  assert (Hnl : new_color qc wf mode = None -> ~ live col' L (dom h)).
  { intros Hnc (w & Hc & _). rewrite Hnew in Hc. congruence. }
  destruct Hq as [<- | [-> | Hq]].
  - destruct qc, mode; simpl in *; auto; try (rewrite Hnew; reflexivity).
  - simpl. exact I.
  - destruct qc; discriminate.
Qed.

(* ------------------CLEANLINESS IS KEPT------------------*)

Lemma clean_q_vpa : forall mt q0 q1, clean_q q1 -> vpa_q mt q0 q1 = q1.
Proof.
  intros mt q0 q1 (H1 & H2 & H3). destruct mt, q0, q1; simpl; congruence.
Qed.

Lemma clean_arg_adapt : forall mt q0 T, clean_arg T -> clean_arg (adapt mt q0 T).
Proof.
  intros mt q0 T. unfold adapt.
  induction T using qualified_type_ind'; intros Hc.
  - apply clean_arg_class in Hc. destruct Hc as [Hq Hargs].
    simpl map_qual. apply clean_arg_class. rewrite clean_q_vpa; auto.
    split; auto. clear Hq. induction H; simpl; constructor;
      inversion Hargs; subst; auto.
  - destruct u; simpl in *; auto. rewrite clean_q_vpa; auto.
  - apply clean_arg_head in Hc. simpl map_qual. apply clean_arg_head.
    induction H; simpl; constructor; inversion Hc; subst; auto.
Qed.

Lemma clean_arg_requalify : forall q0 U,
  clean_q q0 -> clean_arg U -> clean_arg (requalify q0 U).
Proof.
  intros q0 [q1 C a|u o n| ? ? ?] Hq HU; simpl requalify.
  - apply clean_arg_class in HU. apply clean_arg_class. tauto.
  - exact Hq.
  - apply clean_arg_head in HU. apply clean_arg_class. tauto.
Qed.

Lemma clean_arg_prequalify : forall m U,
  clean_arg U -> clean_arg (prequalify m U).
Proof.
  intros m [q1 C a|u o n| ? ? ?] HU; simpl prequalify.
  - apply clean_arg_class in HU. apply clean_arg_head. tauto.
  - exact I.
  - apply clean_arg_head in HU. apply clean_arg_head. exact HU.
Qed.

Lemma clean_arg_qrequalify : forall ks m U,
  Forall clean_qarg ks -> clean_arg U ->
  clean_arg (qrequalify (nth_error ks m) U).
Proof.
  intros ks m U Hk HU. destruct (nth_error ks m) as [[q0|m']|] eqn:E; simpl.
  - apply clean_arg_requalify; auto.
    eapply Forall_forall in Hk; [|eapply nth_error_In; exact E]. exact Hk.
  - apply clean_arg_prequalify; auto.
  - apply clean_arg_requalify; auto. repeat split; discriminate.
Qed.

Lemma whead_qrequalify_clean : forall ks m U,
  Forall clean_qarg ks -> whead_clean (qrequalify (nth_error ks m) U).
Proof.
  intros ks m U Hk q0 Hq0.
  destruct (nth_error ks m) as [[q1|m']|] eqn:E; simpl in Hq0.
  - destruct U; simpl in Hq0; inversion Hq0; subst;
      (eapply Forall_forall in Hk; [|eapply nth_error_In; exact E]; exact Hk).
  - destruct U; simpl in Hq0; discriminate.
  - destruct U; simpl in Hq0; inversion Hq0; subst; repeat split; discriminate.
Qed.

Lemma clean_arg_subst : forall cs ms ks T,
  Forall clean_arg cs -> Forall clean_arg ms -> Forall clean_qarg ks ->
  clean_arg T -> clean_arg (subst cs ms ks T).
Proof.
  intros cs ms ks T Hc Hm Hk.
  induction T using qualified_type_ind'; intros HT.
  - apply clean_arg_class in HT. destruct HT as [Hq Hargs].
    simpl subst. apply clean_arg_class. split; auto.
    clear Hq. induction H; simpl; constructor; inversion Hargs; subst; auto.
  - pose proof (tv_lookup_clean o cs ms n Hc Hm) as Hl.
    destruct u; simpl in *; auto;
      [apply clean_arg_requalify; auto | apply clean_arg_qrequalify; auto].
  - apply clean_arg_head in HT. simpl subst.
    apply clean_arg_qhead; [exact Hk|].
    induction H; simpl; constructor; inversion HT; subst; auto.
Qed.

Lemma super_inst_clean : forall CT mt q0 C Ts D Vs,
  supers_clean CT ->
  super_inst CT mt q0 C Ts D Vs ->
  Forall clean_arg Ts -> Forall clean_arg Vs.
Proof.
  intros CT mt q0 C Ts D Vs Hsc H. induction H; intros HTs; auto.
  apply IHsuper_inst.
  pose proof (Hsc _ _ _ Hparent) as HSs.
  clear - HTs HSs. induction HSs; simpl; constructor; auto.
  apply clean_arg_subst; auto. apply clean_arg_adapt; auto.
Qed.

Lemma class_var_types_clean : forall n, Forall clean_arg (class_var_types n).
Proof.
  intros n. unfold class_var_types. apply Forall_forall.
  intros T Hin. apply in_map_iff in Hin. destruct Hin as (i & <- & _). exact I.
Qed.

Lemma method_var_types_clean : forall n, Forall clean_arg (method_var_types n).
Proof.
  intros n. unfold method_var_types. apply Forall_forall.
  intros T Hin. apply in_map_iff in Hin. destruct Hin as (i & <- & _). exact I.
Qed.

Lemma typing_keeps_clean : forall CT Δ sΓ mt s sΓ',
  stmt_typing CT Δ sΓ mt s sΓ' ->
  clean_stmt s -> Forall clean_top sΓ -> Forall clean_top sΓ'.
Proof.
  intros CT Δ sΓ mt s sΓ' H. induction H; intros Hs Hc; auto.
  - subst. apply Forall_app. split; auto.
  - destruct Hs. auto.
Qed.

(* ------------------OVERRIDING------------------*)

Definition gref (qr : q_r) (sig' sig : method_sig) : Prop :=
  Forall2
    (fun P0 P' =>
       (whead P' = Some RDM -> whead P0 = Some RDM \/ whead P0 = Some Bot) /\
       (whead P' = Some Bot -> whead P0 = Some Bot))
    (mparams sig) (mparams sig') /\
  (whead (mret sig) = Some Mut ->
     whead (mret sig') = Some Mut \/ whead (mret sig') = Some Bot) /\
  (whead (mret sig) = Some RDM ->
     whead (mret sig') = Some RDM \/ whead (mret sig') = Some Mut \/
     whead (mret sig') = Some Bot \/ qr = Imm_r) /\
  (whead (mret sig) = Some Bot -> whead (mret sig') = Some Bot).

Definition gref_rel (qr : q_r) (mdef' mdef : method_def) : Prop :=
  mscope (msignature mdef') = mscope (msignature mdef) /\
  (readonly_state_method_scope (mscope (msignature mdef')) ->
   gref qr (msignature mdef') (msignature mdef)).

Lemma gref_rel_refl : forall qr m, gref_rel qr m m.
Proof.
  intros qr m. split; auto. intros _. unfold gref.
  refine (conj _ (conj _ (conj _ _))); auto.
  induction (mparams (msignature m)); constructor; auto.
Qed.

Lemma gref_rel_trans : forall qr a b c,
  gref_rel qr a b -> gref_rel qr b c -> gref_rel qr a c.
Proof.
  intros qr a b c [Hs1 H1] [Hs2 H2]. split; [congruence|].
  intros Hrs. destruct (H1 Hrs) as (Hp1 & Hm1 & Hr1 & Hb1).
  rewrite Hs1 in Hrs. destruct (H2 Hrs) as (Hp2 & Hm2 & Hr2 & Hb2).
  refine (conj _ (conj _ (conj _ _))).
  - eapply Forall2_compose; [exact Hp2 | exact Hp1 |].
    intros Pc Pb Pa [Ha Hb] [Hc Hd]. split.
    + intros H. destruct (Hc H) as [Hx | Hx]; auto.
    + intros H. auto.
  - intros H. destruct (Hm2 H) as [Hx | Hx]; auto.
  - intros H. destruct (Hr2 H) as [Hx | [Hx | [Hx | Hx]]]; auto.
    + destruct (Hm1 Hx) as [Hy | Hy]; auto.
  - intros H. auto.
Qed.

Lemma vpa_as_cases : forall qC q1,
  (vpa_q AbstractState (qc2q qC) q1 = RDM -> q1 = RDM) /\
  (vpa_q AbstractState (qc2q qC) q1 = Bot -> q1 = Bot).
Proof.
  intros qC q1. destruct qC, q1; simpl; split; intros H; congruence.
Qed.

Lemma gref_step : forall CT qr D' ca' def' mdef' P Ss D1 mdef1,
  wf_class_table CT -> clean_ct CT ->
  wf_rtypeuse CT (mkruntime_type qr D' ca') ->
  find_class CT D' = Some def' ->
  super (signature def') = Some (P, Ss) ->
  List.In mdef' (methods (body def')) ->
  wf_method CT D' mdef' ->
  FindMethodWithName CT P (mname (msignature mdef')) D1 mdef1 ->
  gref_rel qr mdef' mdef1.
Proof.
  intros CT qr D' ca' def' mdef' P Ss D1 mdef1
    Hct Hcc Hrt Hfind Hsuper Hin Hwm Hfm.
  unfold wf_rtypeuse in Hrt. simpl in Hrt. rewrite Hfind in Hrt.
  destruct Hrt as (Hagree & _).
  destruct (find_rsuper_exists _ _ _ _ _ Hfm Mut (map (dyn Mut [] [] []) Ss))
    as [Xs Hrs0].
  assert (Hrs : rsuper_inst CT Mut D' [] D1 Xs).
  { eapply rsi_step; [|exact Hrs0].
    unfold parent_lookup. rewrite Hfind. exact Hsuper. }
  destruct (super_inst_exists _ _ _ _ _ _ Hrs AbstractState
              (qc2q (class_qualifier (signature def')))
              (class_var_types (length (ctparams (signature def')))))
    as [Vs Hsi].
  pose proof (super_inst_clean _ _ _ _ _ _ _ (cc_supers _ Hcc) Hsi
                (class_var_types_clean _)) as HVs.
  pose proof Hwm as (_ & _ & _ & _ & Hovr & _).
  pose proof (Hovr def' P Ss D1 mdef1 Vs Hfind Hsuper Hfm Hsi) as Hcompat.
  destruct Hcompat as (_ & Hscope & _ & Hret & Hpar & _).
  split; [exact Hscope|]. intros Hrs'.
  destruct (cc_methods _ Hcc _ _ _ Hfind Hin Hrs') as (HΔ & _ & _).
  remember (class_qualifier (signature def')) as qC eqn:HqCdef.
  set (ms := method_var_types (length (mtparams (msignature mdef1)))) in *.
  set (ks := qvar_args (mqparams (msignature mdef1))) in *.
  assert (Hms : Forall clean_arg ms) by apply method_var_types_clean.
  assert (Hks : Forall clean_qarg ks) by apply qvar_args_clean.
  assert (Hnc_rdm : ~ clean_q RDM) by (intros (_ & H & _); congruence).
  assert (Hnc_bot : ~ clean_q Bot) by (intros (_ & _ & H); congruence).
  assert (Hnc_mut : ~ clean_q Mut) by (intros (H & _); congruence).
  (* the written head of an overridden type seen through the class *)
  assert (Hview : forall T qv,
            whead (member_type AbstractState (qc2q qC) Vs ms ks T) = Some qv ->
            ~ clean_q qv ->
            exists q1, whead T = Some q1 /\
                       vpa_q AbstractState (qc2q qC) q1 = qv).
  { intros T qv Hh Hnc.
    destruct (whead T) as [q1|] eqn:HT.
    - rewrite (whead_member_some _ _ _ _ _ _ _ HT) in Hh. inversion Hh. eauto.
    - destruct T as [qa Ca aa | [|qa|mp] oa na | na Ca aa]; simpl in HT;
        try discriminate.
      + exfalso. apply Hnc.
        exact (whead_member_var AbstractState (qc2q qC) Vs ms ks oa na HVs Hms _ Hh).
      + exfalso. apply Hnc.
        unfold member_type, adapt in Hh. simpl in Hh.
        eapply whead_qrequalify_clean; [|exact Hh]. exact Hks.
      + exfalso. apply Hnc.
        unfold member_type, adapt in Hh. simpl in Hh.
        eapply whead_qhead_clean; [|exact Hh]. exact Hks. }
  refine (conj _ (conj _ (conj _ _))).
  - eapply Forall2_impl; [|exact Hpar].
    intros P1 P' Hsub. simpl in Hsub. split; intros Hh.
    + destruct (sub_whead _ _ _ _ Hsub HΔ _ Hh Hnc_rdm) as [Hv | Hv].
      * destruct (Hview _ _ Hv Hnc_rdm) as (q1 & Hq1 & Hvq).
        apply (proj1 (vpa_as_cases qC q1)) in Hvq. subst. auto.
      * destruct (Hview _ _ Hv Hnc_bot) as (q1 & Hq1 & Hvq).
        apply (proj2 (vpa_as_cases qC q1)) in Hvq. subst. auto.
    + destruct (sub_whead _ _ _ _ Hsub HΔ _ Hh Hnc_bot) as [Hv | Hv];
        destruct (Hview _ _ Hv Hnc_bot) as (q1 & Hq1 & Hvq);
        apply (proj2 (vpa_as_cases qC q1)) in Hvq; subst; auto.
  - intros Hm.
    pose proof (whead_member_some AbstractState (qc2q qC) Vs ms ks _ _ Hm) as Hv.
    assert (Hvm : vpa_q AbstractState (qc2q qC) Mut = Mut)
      by (destruct qC; reflexivity).
    rewrite Hvm in Hv.
    exact (sub_whead _ _ _ _ Hret HΔ _ Hv Hnc_mut).
  - intros Hm.
    pose proof (whead_member_some AbstractState (qc2q qC) Vs ms ks _ _ Hm) as Hv.
    destruct qC; simpl in Hv.
    + destruct (sub_whead _ _ _ _ Hret HΔ _ Hv Hnc_mut); auto.
    + right. right. right.
      destruct qr; simpl in Hagree; auto; discriminate.
    + destruct (sub_whead _ _ _ _ Hret HΔ _ Hv Hnc_rdm); auto.
  - intros Hm.
    pose proof (whead_member_some AbstractState (qc2q qC) Vs ms ks _ _ Hm) as Hv.
    assert (Hvb : vpa_q AbstractState (qc2q qC) Bot = Bot)
      by (destruct qC; reflexivity).
    rewrite Hvb in Hv.
    destruct (sub_whead _ _ _ _ Hret HΔ _ Hv Hnc_bot); auto.
Qed.

Lemma no_mut_whead : forall Δ T, no_mut Δ T -> whead T <> Some Mut.
Proof.
  intros Δ T H Hh. destruct T as [q0 C Ts | [|q0|mp] o n | n C Ts]; simpl in Hh;
    try discriminate; inversion Hh; subst; inversion H; subst; congruence.
Qed.

(** The world of a call's result in the caller. *)
Lemma call_result_goodW : forall (col col'' : coloring) L wf mode Lc wc modec
    (qr : q_r) q0 qy qm rv ly,
  List.In wf L ->
  ((q0 = Mut -> qy = Mut /\ (qm = Mut \/ qm = RDM)) /\
   (q0 = RDM -> qy = RDM /\ qm = RDM)) ->
  ((qm = Mut -> good col'' Lc wc modec Mut rv) /\
   (qm = RDM -> good col'' Lc wc modec RDM rv \/ good col'' Lc wc modec Mut rv \/
                qr = Imm_r)) ->
  good col L wf mode qy ly ->
  (q0 = Imm -> ~ live col'' L rv) ->
  (qr = Imm_r -> qy = RDM -> q0 = RDM -> ~ live col'' L rv) ->
  ((col ly = Some wc /\ List.In wc L /\ Lc = L /\ modec = true /\ qr = Mut_r) \/
   (~ live col L ly /\ Lc = wc :: L /\ ~ List.In wc L /\ modec = false)) ->
  good col'' L wf mode q0 rv.
Proof.
  intros col col'' L wf mode Lc wc modec qr q0 qy qm rv ly
    HwfL [HsM HsR] [HcM HcR] Hgy Himm Himmr Hworld.
  destruct q0; simpl; auto.
  - destruct (HsM eq_refl) as [-> HqM]. simpl in Hgy.
    destruct Hworld as [(Hc & Hin & -> & -> & Hqr) | (Hnl & _)].
    + assert (wc = wf) by congruence. subst wc.
      destruct HqM as [-> | ->].
      * exact (HcM eq_refl).
      * destruct (HcR eq_refl) as [Hg | [Hg | Hg]]; simpl in Hg; auto; congruence.
    + exfalso. apply Hnl. exists wf. auto.
  - destruct (HsR eq_refl) as [-> ->]. simpl in Hgy.
    destruct Hworld as [(Hc & Hin & -> & -> & Hqr) | (Hnl & -> & Hnin & ->)].
    + destruct mode.
      * assert (wc = wf) by congruence. subst wc.
        destruct (HcR eq_refl) as [Hg | [Hg | Hg]]; simpl in Hg; auto; congruence.
      * exfalso. apply Hgy. exists wc. auto.
    + destruct mode.
      * exfalso. apply Hnl. exists wf. auto.
      * destruct (HcR eq_refl) as [Hg | [Hg | Hg]]; simpl in Hg.
        -- intros (w & Hc & Hin). apply Hg. exists w. split; auto. right. auto.
        -- intros (w & Hc & Hin). congruence.
        -- apply Himmr; auto.
Qed.

(* ------------------THE MAIN STEP------------------*)

Lemma call_typing_inv2 : forall CT Δ sΓ mt x m y Us Qs zs sΓ',
  stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
  exists argtypes Tx Ty qy C Ts D Vs mdef,
    sΓ' = sΓ /\
    static_getType sΓ x = Some Tx /\
    static_getType sΓ y = Some Ty /\
    static_getType_list sΓ zs = Some argtypes /\
    ubound Δ Ty = Some (TClass qy C Ts) /\
    FindMethodWithName CT C m D mdef /\
    super_inst CT mt qy C Ts D Vs /\
    x <> 0 /\
    qualified_type_subtype CT Δ
      (member_type mt qy Vs Us Qs (mret (msignature mdef))) Tx /\
    Forall2 (fun A P => assignable_to CT Δ A (member_type mt qy Vs Us Qs P))
      argtypes (mparams (msignature mdef)) /\
    method_scope_subtype (mscope (msignature mdef)) mt.
Proof.
  intros. inversion H; subst.
  do 9 eexists. repeat split; eauto.
Qed.

Lemma rs_vpa_bot : forall mt qy qm,
  readonly_state_method_scope mt -> qy <> Bot ->
  vpa_q mt qy qm = Bot -> qm = Bot.
Proof.
  intros mt qy qm [-> | ->] Hnb H; destruct qy, qm; simpl in H; congruence.
Qed.

Lemma imm_receiver_result : forall qo qv,
  head_ok Imm_r (dynq (qr2q qo) RDM) ->
  head_ok qv (dynq (qr2q qo) RDM) ->
  qv = Imm_r.
Proof.
  intros qo qv H1 H2. unfold head_ok in *.
  destruct qo, qv; simpl in *; auto;
    destruct H1 as [Hx | [Hx | Hx]]; try discriminate;
    destruct H2 as [Hy | [Hy | Hy]]; discriminate.
Qed.

Lemma rg_step : forall P CT,
  clean_ct CT ->
  forall rΓ h s res rΓ' h',
    eval_stmt CT rΓ h s res rΓ' h' ->
    res = OK ->
    forall Δ sΓ mt sΓ' col L next wf mode,
      clean_bounds Δ -> Forall clean_top sΓ -> clean_stmt s ->
      readonly_state_method_scope mt ->
      wf_r_config CT Δ sΓ rΓ h ->
      stmt_typing CT Δ sΓ mt s sΓ' ->
      heapW P CT h col L next ->
      frameW CT sΓ rΓ col L wf mode ->
      (forall l, P l -> l < dom h) ->
      exists col' next',
        heapW P CT h' col' L next' /\
        frameW CT sΓ' rΓ' col' L wf mode /\
        (forall l, l < dom h -> col' l = col l) /\
        next <= next' /\
        prot_preserved P CT mt h h'.
Proof.
  intros P CT Hcc rΓ h s res rΓ' h' Heval.
  pose proof (cc_supers _ Hcc) as Hsc.
  induction Heval;
    intros Hres Δ sΓ mt0 sΓ' col L next wf mode HΔ Hcl Hcs Hrs Hwf Htype HG HF HPdom;
    try discriminate.
  - inversion Htype; subst. exists col, next.
    auto using prot_preserved_refl.
  - inversion Htype; subst. exists col, next.
    refine (conj HG (conj _ (conj (fun l H => eq_refl) (conj (le_n _)
              (prot_preserved_refl _ _ _ _))))).
    apply frameW_local; auto.
    destruct Hwf as (_ & _ & _ & _ & _ & Hlen & _). exact Hlen.
  - exists col, next.
    refine (conj HG (conj _ (conj (fun l H => eq_refl) (conj (le_n _)
              (prot_preserved_refl _ _ _ _))))).
    eapply rg_assign; eauto.
  - subst. exists col, next.
    destruct (rg_fldwrite P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                Hsc HΔ Hcl Hrs Hwf HG HF Htype Hval_x Hobj Hfield Hassign Hval_y)
      as [HG' Hp].
    refine (conj HG' (conj _ (conj (fun l H => eq_refl) (conj (le_n _) Hp)))).
    inversion Htype; subst. exact HF.
  - subst.
    destruct (rg_new P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                HΔ Hwf HG HF Htype Hthis Hargs Hmut HPdom) as (HG' & HF' & Hag).
    eexists _, next.
    refine (conj HG' (conj HF' (conj Hag (conj (le_n _) _)))).
    intros l qr C0 Rs vals0 f HP Hl _.
    exists vals0. split; [|reflexivity].
    rewrite runtime_getObj_last2; [eapply runtime_getObj_dom; eauto | exact Hl].
  - (* call *)
    subst. simpl in Hcs. destruct Hcs as [Hcs HcQ].
    pose proof Hwf as (Hct & Hheap & Hrenv & _).
    destruct (call_typing_inv2 _ _ _ _ _ _ _ _ _ _ _ Htype)
      as (argtypes & Tx & Ty & qy & C & Ts & Ds & Vs & smdef & -> & Hget_x &
          Hget_y & Hget_args & Hub & Hfind_s & Hsuper_s & Hx & Hret_sub &
          Harg_sub & Hscope_s).
    destruct (call_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                _ Hwf Htype Hval_y Hbase Hfind Hargs Hframe)
      as (ι & o & oy & Tx' & Hthis & Hobj & Hoy & HTx' & _ & _ &
          Hfb & Hwm & Hcfg & Hthis' & Hretf & Hscope).
    assert (Tx' = Tx) by (unfold static_getType in *; congruence). subst Tx'.
    pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_y) as Hyty.
    rewrite Hval_y in Hyty.
    pose proof (var_goodT P CT Δ sΓ rΓ h col L next wf mode ι o Hwf HG HF
                  Hthis Hobj _ _ _ Hget_y Hval_y) as Hgy0.
    destruct (recv_good P CT Δ rΓ h col L next wf mode o HΔ HG Hfb
                _ _ _ _ _ (senv_clean _ _ _ Hcl Hget_y) Hub Hyty Hgy0)
      as (Hgy & HTs & Hqyb & Hyty').
    pose proof (super_inst_clean _ _ _ _ _ _ _ Hsc Hsuper_s HTs) as HVs.
    destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ _ Hyty')
      as (oy' & Rs1 & Hoy' & Hhead_y & Hsup1 & _).
    rewrite Hoy in Hoy'. inversion Hoy'; subst oy'. clear Hoy'.
    pose proof (Hheap ly (runtime_getObj_dom _ _ _ Hoy)) as Hwfo.
    unfold wf_obj in Hwfo. rewrite Hoy in Hwfo. destruct Hwfo as (Hrt_oy & _).
    unfold r_basetype in Hbase. rewrite Hoy in Hbase. inversion Hbase; subst cy.
    clear Hbase.
    destruct oy as [[qr Co Ro] fso]. simpl in *.
    destruct (lookup_chain CT qr (gref_rel qr) Hct (gref_rel_refl qr)
                (gref_rel_trans qr)
                (fun D' ca' def' mdef' P0 Ss D1 mdef1 H1 H2 H3 H4 H5 H6 =>
                   gref_step CT qr D' ca' def' mdef' P0 Ss D1 mdef1
                     Hct Hcc H1 H2 H3 H4 H5 H6)
                _ _ _ _ Hsup1 Hrt_oy _ _ _ _ _ Hfind Hfind_s)
      as [Hsc_eq Hgref0].
    assert (Hrs' : readonly_state_method_scope (mscope (msignature mdef))).
    { eapply readonly_state_submethod; eauto. }
    pose proof (Hgref0 Hrs') as Hgref.
    destruct (find_method_In _ _ _ _ _ Hfind) as (defD & HfD & HinD).
    destruct (cc_methods _ Hcc _ _ _ HfD HinD Hrs') as (HΔ' & Hcl' & Hcs').
    pose proof Hwm as
      (_ & _ & _ & (sΓb & Tb & Hbody & Hnthb & Hsubb) & _ & Hroots').
    destruct (Hroots' Hrs') as [Hnm_recv Hnm_par].
    pose proof (callee_env_targs _ _ _ _ _ _ _ _ _ Hframe) as Hvars'.
    pose proof (fw_live _ _ _ _ _ _ _ HF) as HwfL.
    assert (Hnc_bot : ~ clean_q Bot) by (intros (_ & _ & H); congruence).
    assert (Hnc_mut : ~ clean_q Mut) by (intros (H & _); congruence).
    assert (Hnc_rdm : ~ clean_q RDM) by (intros (_ & H & _); congruence).
    assert (Hnomut : forall x0 T,
              static_getType
                (mreceiver (msignature mdef) :: mparams (msignature mdef)) x0
                = Some T -> whead T <> Some Mut).
    { intros x0 T HT. eapply no_mut_whead. unfold static_getType in HT.
      destruct x0 as [|i]; simpl in HT.
      - inversion HT; subst. exact Hnm_recv.
      - rewrite Forall_forall in Hnm_par. apply Hnm_par.
        eapply nth_error_In; eauto. }
    assert (Hparam : forall i P' v,
              nth_error (mparams (msignature mdef)) i = Some P' ->
              nth_error vals i = Some (Iot v) ->
              whead P' = Some RDM ->
              (forall w, col ly = Some w -> List.In w L -> col v = Some w) /\
              (~ live col L ly -> ~ live col L v)).
    { intros i P' v HP' Hv Hh.
      destruct Hgref as (Hpar_w & _).
      pose proof (Forall2_nth_error_rel _ _ _ i Hpar_w) as Hrel.
      rewrite HP' in Hrel.
      destruct (nth_error (mparams (msignature smdef)) i) as [Ps|] eqn:HPs;
        [|contradiction].
      destruct Hrel as [Hrel _]. specialize (Hrel Hh).
      destruct (lookup_lists_nth _ _ _ _ _ _ _ Hget_args Hargs Hv)
        as (yi & A & HyA & Hyv & HnA).
      pose proof (Forall2_nth_error_rel _ _ _ i Harg_sub) as Hrel2.
      rewrite HnA in Hrel2. rewrite HPs in Hrel2. destruct Hrel2 as [Hsub Hok].
      pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj HyA) as Hty.
      rewrite Hyv in Hty.
      pose proof (var_goodT P CT Δ sΓ rΓ h col L next wf mode ι o Hwf HG HF
                    Hthis Hobj _ _ _ HyA Hyv) as HgA.
      pose proof (goodT_sub P CT Δ rΓ h col L next wf mode o HΔ HG Hfb
                    _ _ _ Hsub Hty HgA) as Hgm.
      destruct Hrel as [HqP | HqP].
      - pose proof (whead_member_some mt0 qy Vs Us Qs _ _ HqP) as Hmh.
        assert (Hnl : vpa_q mt0 qy RDM <> Lost).
        { intros Hl. pose proof Hok as Hlf.
            apply (lost_free_whead _ Hlf). rewrite Hmh. rewrite Hl. reflexivity. }
        destruct (write_worlds mt0 qy RDM col L wf mode ly v Hrs Hnl Hqyb
                    HwfL Hgy (Hgm _ Hmh)) as [H1 H2].
        split; [intros w Hc Hin; apply H1; auto | intros Hn; apply H2; auto].
      - exfalso.
        pose proof (whead_member_some mt0 qy Vs Us Qs _ _ HqP) as Hmh.
        rewrite vpa_bot in Hmh.
        destruct (sub_whead _ _ _ _ Hsub HΔ _ Hmh Hnc_bot) as [Hb | Hb];
          eapply (typable_whead_not_bot _ _ _ _ _ _ _ _ Hty); exact Hb. }
    assert (Hresult : forall col'' Lc wc modec next'' rΓe he,
              eval_stmt CT rΓ' h (mbody_stmt (mbody mdef)) OK rΓe he ->
              runtime_getVal rΓe (mreturn (mbody mdef)) = Some retval ->
              heapW P CT he col'' Lc next'' ->
              frameW CT sΓb rΓe col'' Lc wc modec ->
              heapW P CT he col'' L next'' ->
              ((col ly = Some wc /\ List.In wc L /\ Lc = L /\ modec = true /\
                qr = Mut_r) \/
               (~ live col L ly /\ Lc = wc :: L /\ ~ List.In wc L /\
                modec = false)) ->
              forall rv q0, retval = Iot rv -> whead Tx = Some q0 ->
                good col'' L wf mode q0 rv).
    { intros col'' Lc wc modec next'' rΓe he Hev Hrv HGc HFc HGL Hworld rv q0 -> Hh0.
      pose proof (preservation_pico _ _ _ _ _ _ _ Hev eq_refl _ _ _ _ Hcfg Hbody)
        as Hcfg''.
      destruct (wf_r_config_this _ _ _ _ _ Hcfg'')
        as (ι2 & o2 & Hth2 & Hobj2 & _ & _ & _ & Hfb2).
      pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hcfg'' Hth2 Hobj2 Hnthb) as Hrty.
      rewrite Hrv in Hrty.
      pose proof (var_goodT P CT _ sΓb rΓe he col'' Lc next'' wc modec ι2 o2
                    Hcfg'' HGc HFc Hth2 Hobj2 _ _ _ Hnthb Hrv) as HgT.
      (* the result is typed, in the caller, at the destination type *)
      assert (Hrt : wf_r_typable CT he rv Tx (rqtype (rt_type o))
                      (cargs rΓ) (margs rΓ) (qargs rΓ)).
      { apply (Hretf he (Iot rv)). simpl.
        destruct (eval_stmt_frame _ _ _ _ _ _ Hev _ _ _ _ Hbody)
          as (Hth_eq & Hca_eq & Hma_eq).
        pose proof (eval_stmt_qargs _ _ _ _ _ _ _ Hev eq_refl) as Hqa_eq.
        destruct (heap_ext_getObj _ _ _ _ (eval_stmt_heap_ext _ _ _ _ _ _ _ Hev) Hoy)
          as (oye & Hoye & Hrte).
        assert (ι2 = ly) by congruence. subst ι2.
        rewrite Hoye in Hobj2. inversion Hobj2; subst o2.
        rewrite Hrte in Hrty. simpl in Hrty.
        rewrite Hca_eq in Hrty. rewrite Hma_eq in Hrty. try rewrite Hqa_eq in Hrty.
        eapply wf_r_typable_subtype; [|exact Hsubb|exact Hrty].
        rewrite Hca_eq in Hfb2. rewrite Hma_eq in Hfb2. try rewrite Hqa_eq in Hfb2.
        rewrite Hrte in Hfb2. exact Hfb2. }
      assert (Himm : q0 = Imm -> ~ live col'' L rv).
      { intros ->. eapply not_live_of_immW; [exact HGL|].
        eapply typable_whead_imm; eauto. }
      assert (Himmr : qr = Imm_r -> qy = RDM -> q0 = RDM -> ~ live col'' L rv).
      { intros -> -> ->.
        destruct (typable_whead_obj _ _ _ _ _ _ _ _ _ Hrt Hh0) as (orv & Horv & Hk).
        pose proof (imm_receiver_result _ _ Hhead_y Hk) as Hqv.
        eapply not_live_of_immW; [exact HGL|].
        unfold r_muttype. rewrite Horv. congruence. }
      (* what a non-clean head of the callee's return type says *)
      assert (Hup : forall q', whead (mret (msignature mdef)) = Some q' ->
                      ~ clean_q q' -> q' <> Bot ->
                      good col'' Lc wc modec q' rv).
      { intros q' Hq' Hnc Hnb.
        destruct (sub_whead _ _ _ _ Hsubb HΔ' _ Hq' Hnc) as [Hb | Hb].
        - apply HgT; auto.
        - exfalso. exact (typable_whead_not_bot _ _ _ _ _ _ _ _ Hrty Hb). }
      assert (Hbot' : whead (mret (msignature mdef)) <> Some Bot).
      { intros Hq'.
        destruct (sub_whead _ _ _ _ Hsubb HΔ' _ Hq' Hnc_bot) as [Hb | Hb];
          exact (typable_whead_not_bot _ _ _ _ _ _ _ _ Hrty Hb). }
      destruct Hgref as (_ & HrM & HrR & HrB).
      destruct (whead (mret (msignature smdef))) as [qm|] eqn:Hqm.
      - pose proof (whead_member_some mt0 qy Vs Us Qs _ _ Hqm) as Hmh.
        assert (Hqmb : qm <> Bot).
        { intros ->. apply Hbot'. apply HrB. reflexivity. }
        assert (Hstat : (q0 = Mut -> qy = Mut /\ (qm = Mut \/ qm = RDM)) /\
                        (q0 = RDM -> qy = RDM /\ qm = RDM)).
        { destruct (rs_vpa_cases mt0 qy qm Hrs) as [Hmut Hrdm].
          split; intros ->.
          - destruct (sub_whead _ _ _ _ Hret_sub HΔ _ Hh0 Hnc_mut) as [Hb | Hb];
              rewrite Hmh in Hb; injection Hb as Hv.
            + exact (Hmut Hv).
            + exfalso. apply Hqmb. exact (rs_vpa_bot _ _ _ Hrs Hqyb Hv).
          - destruct (sub_whead _ _ _ _ Hret_sub HΔ _ Hh0 Hnc_rdm) as [Hb | Hb];
              rewrite Hmh in Hb; injection Hb as Hv.
            + exact (Hrdm Hv).
            + exfalso. apply Hqmb. exact (rs_vpa_bot _ _ _ Hrs Hqyb Hv). }
        assert (Hcal : (qm = Mut -> good col'' Lc wc modec Mut rv) /\
                       (qm = RDM -> good col'' Lc wc modec RDM rv \/
                                    good col'' Lc wc modec Mut rv \/ qr = Imm_r)).
        { split; intros ->.
          - destruct (HrM eq_refl) as [Hq' | Hq'].
            + apply Hup; auto; discriminate.
            + exfalso. exact (Hbot' Hq').
          - destruct (HrR eq_refl) as [Hq' | [Hq' | [Hq' | Hq']]].
            + left. apply Hup; auto; discriminate.
            + right. left. apply Hup; auto; discriminate.
            + exfalso. exact (Hbot' Hq').
            + right. right. exact Hq'. }
        exact (call_result_goodW col col'' L wf mode Lc wc modec qr q0 qy qm rv ly
                 HwfL Hstat Hcal Hgy Himm Himmr Hworld).
      - (* the static return type is a bare type variable *)
        assert (Hclm : whead_clean (member_type mt0 qy Vs Us Qs
                                      (mret (msignature smdef)))).
        { destruct (mret (msignature smdef)) as [qa Ca aa | [|qa|mp] oa na | na Ca aa];
            simpl in Hqm; try discriminate.
          - apply whead_member_var; auto.
          - unfold member_type, adapt. simpl.
            apply whead_qrequalify_clean. exact HcQ.
          - unfold member_type, adapt. simpl.
            apply whead_qhead_clean. exact HcQ. }
        destruct q0; simpl; auto.
        + exfalso.
          destruct (sub_whead _ _ _ _ Hret_sub HΔ _ Hh0 Hnc_mut) as [Hb | Hb].
          * apply Hnc_mut. exact (Hclm _ Hb).
          * apply Hnc_bot. exact (Hclm _ Hb).
        + exfalso.
          destruct (sub_whead _ _ _ _ Hret_sub HΔ _ Hh0 Hnc_rdm) as [Hb | Hb].
          * apply Hnc_rdm. exact (Hclm _ Hb).
          * apply Hnc_bot. exact (Hclm _ Hb). }
    pose proof (eval_stmt_heap_ext _ _ _ _ _ _ _ Heval) as Hext.
    assert (Hprot_up : forall C0 f,
              prot_cond CT C0 f mt0 ->
              prot_cond CT C0 f (mscope (msignature mdef))).
    { intros C0 f [Hp | [Hp | Hstrict]]; [left; auto | right; left; auto |].
      right. right. eapply concrete_assignability_submethod; eauto. }
    destruct (live_dec col L ly) as [(w & Hcw & HinW) | Hnlive].
    + assert (HF' : frameW CT
                      (mreceiver (msignature mdef) :: mparams (msignature mdef))
                      rΓ' col L w true).
      { constructor.
        - exact HinW.
        - intros _. exists ly. split; auto.
        - intros x0 T v HT Hv Hh. exfalso. eapply Hnomut; eauto.
        - intros x0 T v HT Hv Hh.
          unfold runtime_getVal in Hv. rewrite Hvars' in Hv.
          unfold static_getType in HT.
          destruct x0 as [|i]; simpl in HT, Hv.
          + inversion Hv; subst v. exact Hcw.
          + destruct (Hparam _ _ _ HT Hv Hh) as [H1 _]. apply H1; auto. }
      destruct (IHHeval Hcc Hsc eq_refl _ _ _ _ col L next w true
                  HΔ' Hcl' Hcs' Hrs' Hcfg Hbody HG HF' HPdom)
        as (col'' & next'' & HG'' & HF'' & Hag & Hle & Hprot).
      exists col'', next''.
      refine (conj HG'' (conj _ (conj Hag (conj Hle _)))).
      * eapply frameW_update; eauto.
        -- eapply frameW_agree; eauto.
        -- intros rv q0 Hrv Hh0.
           eapply (Hresult col'' L w true next'' _ _ Heval Hretval HG'' HF'' HG'');
             eauto.
           left. repeat split; auto.
           destruct (hw_col _ _ _ _ _ _ HG _ _ Hcw) as (_ & _ & Hm & _).
           unfold r_muttype in Hm. rewrite Hoy in Hm. simpl in Hm. congruence.
      * intros l qr0 C0 Rs0 vals0 f HP Hl Hp0. eapply Hprot; eauto.
    + pose proof (heapW_push _ _ _ _ _ _ HG) as HG1.
      assert (Hnin : ~ List.In next L).
      { intros Hin. pose proof (hw_live _ _ _ _ _ _ HG _ Hin). lia. }
      assert (HF' : frameW CT
                      (mreceiver (msignature mdef) :: mparams (msignature mdef))
                      rΓ' col (next :: L) next false).
      { constructor.
        - left. reflexivity.
        - discriminate.
        - intros x0 T v HT Hv Hh. exfalso. eapply Hnomut; eauto.
        - intros x0 T v HT Hv Hh.
          rewrite (live_pushW _ _ _ _ _ _ v HG).
          unfold runtime_getVal in Hv. rewrite Hvars' in Hv.
          unfold static_getType in HT.
          destruct x0 as [|i]; simpl in HT, Hv.
          + inversion Hv; subst v. exact Hnlive.
          + destruct (Hparam _ _ _ HT Hv Hh) as [_ H2]. apply H2; auto. }
      destruct (IHHeval Hcc Hsc eq_refl _ _ _ _ col (next :: L) (S next) next false
                  HΔ' Hcl' Hcs' Hrs' Hcfg Hbody HG1 HF' HPdom)
        as (col'' & next'' & HG'' & HF'' & Hag & Hle & Hprot).
      pose proof (heapW_pop _ _ _ _ _ _ _ HG'' Hnin) as HGL.
      exists col'', next''.
      refine (conj HGL (conj _ (conj Hag (conj _ _)))).
      * eapply frameW_update; eauto.
        -- eapply frameW_agree; eauto.
        -- intros rv q0 Hrv Hh0.
           eapply (Hresult col'' (next :: L) next false next'' _ _
                     Heval Hretval HG'' HF'' HGL); eauto.
      * lia.
      * intros l qr0 C0 Rs0 vals0 f HP Hl Hp0. eapply Hprot; eauto.
  - exists col, next.
    refine (conj HG (conj _ (conj (fun l H => eq_refl) (conj (le_n _)
              (prot_preserved_refl _ _ _ _))))).
    eapply rg_cast; eauto.
  - inversion Htype; subst. simpl in Hcs. destruct Hcs as [Hcs1 Hcs2].
    destruct (IHHeval1 Hcc Hsc eq_refl _ _ _ _ col L next wf mode
                HΔ Hcl Hcs1 Hrs Hwf Htype1 HG HF HPdom)
      as (col1 & next1 & HG1 & HF1 & Hag1 & Hle1 & HP1).
    pose proof (preservation_pico _ _ _ _ _ _ _ Heval1 eq_refl _ _ _ _ Hwf Htype1)
      as Hwf1.
    pose proof (eval_stmt_heap_ext _ _ _ _ _ _ _ Heval1) as [Hd1 _].
    assert (HPdom1 : forall l, P l -> l < dom h').
    { intros l HP. specialize (HPdom l HP). lia. }
    pose proof (typing_keeps_clean _ _ _ _ _ _ Htype1 Hcs1 Hcl) as Hcl1.
    destruct (IHHeval2 Hcc Hsc eq_refl _ _ _ _ col1 L next1 wf mode
                HΔ Hcl1 Hcs2 Hrs Hwf1 Htype2 HG1 HF1 HPdom1)
      as (col2 & next2 & HG2 & HF2 & Hag2 & Hle2 & HP2).
    exists col2, next2.
    refine (conj HG2 (conj HF2 (conj _ (conj _ _)))).
    + intros l Hl. rewrite Hag2; [lia|]. apply Hag1; auto.
    + lia.
    + intros l qr C Rs vals f HP Hl Hprot.
      destruct (HP1 l qr C Rs vals f HP Hl Hprot) as (vals1 & Hl1 & He1).
      destruct (HP2 l qr C Rs vals1 f HP Hl1 Hprot) as (vals2 & Hl2 & He2).
      exists vals2. split; auto. congruence.
Qed.

(* ------------------THE THEOREMS------------------*)

(** A call that selects a readonly-state or transitive-state method leaves
    the protected fields of every object of the entry heap unchanged.  The
    caller is unrestricted: it may instantiate the method, and the classes of
    the objects it passes, with any type arguments. *)
Theorem rs_ts_call_preservation_generic :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef,
    clean_ct CT ->
    wf_r_config CT Δ sΓ rΓ h ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us Qs zs) OK rΓ' h' ->
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m D mdef ->
    readonly_state_method_scope (mscope (msignature mdef)) ->
    forall l qr C Rs vals f,
      runtime_getObj h l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
      prot_cond CT C f (mscope (msignature mdef)) ->
      exists vals',
        runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
        nth_error vals f = nth_error vals' f.
Proof.
  intros CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef
    Hcc Hwf Htype Heval Hvy Hbase Hfind Hrs l qr C Rs vals f Hl Hprot.
  pose proof Hwf as (Hct & _).
  inversion Heval; subst.
  rewrite Hvy in Hval_y. inversion Hval_y; subst ly0. clear Hval_y.
  rewrite Hbase in Hbase0. inversion Hbase0; subst cy0. clear Hbase0.
  destruct (find_method_with_name_deterministic _ _ _ _ _ _ _ Hfind Hfind0)
    as [<- <-].
  destruct (call_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              _ Hwf Htype Hvy Hbase Hfind Hargs Hframe)
    as (ι & o & oy & Tx & _ & _ & _ & _ & _ & _ & _ & Hwm & Hcfg & _).
  destruct (find_method_In _ _ _ _ _ Hfind) as (defD & HfD & HinD).
  destruct (cc_methods _ Hcc _ _ _ HfD HinD Hrs) as (HΔ' & Hcl' & Hcs').
  pose proof Hwm as (_ & _ & _ & (sΓb & Tb & Hbody & _) & _ & Hroots).
  destruct (Hroots Hrs) as [Hnm_recv Hnm_par].
  set (P := fun l0 : Loc => l0 < dom h).
  set (col0 := fun _ : Loc => @None nat).
  assert (Hnl : forall v, ~ live col0 [0] v).
  { intros v (w & Hc & _). discriminate. }
  assert (HG : heapW P CT h col0 [0] 1).
  { constructor.
    - intros l0 w Hc. discriminate.
    - intros l0 w o0 fs f0 fd v Hc. discriminate.
    - intros; apply Hnl.
    - intros w [<- | []]. lia. }
  assert (HF : frameW CT
                 (mreceiver (msignature mdef) :: mparams (msignature mdef))
                 rΓ'0 col0 [0] 0 false).
  { constructor.
    - left. reflexivity.
    - discriminate.
    - intros x0 T v HT _ Hh. exfalso.
      eapply (no_mut_whead (method_tv_env CT D (msignature mdef)) T); eauto.
      unfold static_getType in HT. destruct x0 as [|i]; simpl in HT.
      + inversion HT; subst. exact Hnm_recv.
      + rewrite Forall_forall in Hnm_par. apply Hnm_par.
        eapply nth_error_In; eauto.
    - intros; apply Hnl. }
  destruct (rg_step P CT Hcc _ _ _ _ _ _ Heval_body eq_refl _ _ _ _
              col0 [0] 1 0 false HΔ' Hcl' Hcs' Hrs Hcfg Hbody HG HF (fun l0 H => H))
    as (col' & next' & _ & _ & _ & _ & Hpres).
  eapply Hpres; eauto.
  unfold P. eapply runtime_getObj_dom; eauto.
Qed.

(** Readonly-state preservation: non-assignable fields keep their values. *)
Corollary readonly_state_preservation_generic :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef,
    clean_ct CT ->
    wf_r_config CT Δ sΓ rΓ h ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us Qs zs) OK rΓ' h' ->
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m D mdef ->
    readonly_state_method_scope (mscope (msignature mdef)) ->
    forall l qr C Rs vals f,
      runtime_getObj h l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
      (sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA) ->
      exists vals',
        runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
        nth_error vals f = nth_error vals' f.
Proof.
  intros. eapply rs_ts_call_preservation_generic; eauto.
  unfold prot_cond. tauto.
Qed.

(** Transitive-state preservation: every field keeps its value. *)
Corollary transitive_state_preservation_generic :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef,
    clean_ct CT ->
    wf_r_config CT Δ sΓ rΓ h ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us Qs zs) OK rΓ' h' ->
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m D mdef ->
    mscope (msignature mdef) = TransitiveState ->
    forall l qr C Rs vals f,
      runtime_getObj h l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
      exists vals',
        runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
        nth_error vals f = nth_error vals' f.
Proof.
  intros until mdef. intros Hcc Hwf Htype Heval Hvy Hbase Hfind Hts.
  intros. eapply rs_ts_call_preservation_generic; eauto.
  - rewrite Hts. right. reflexivity.
  - rewrite Hts. right. right. right. reflexivity.
Qed.

Print Assumptions readonly_state_preservation_generic.
Print Assumptions transitive_state_preservation_generic.
