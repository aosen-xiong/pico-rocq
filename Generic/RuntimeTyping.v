From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas.

(** Soundness of static subtyping with respect to runtime types. *)

Lemma head_ok_head_sees : forall qo rq,
  head_ok qo rq <-> head_sees (qr2q qo) rq.
Proof. intros. unfold head_ok, head_sees. reflexivity. Qed.

(** Viewing a runtime type at a superclass is monotone in the head and in the
    arguments. *)
Lemma rsuper_inst_mono : forall CT qb C Rs D Vs,
  rsuper_inst CT qb C Rs D Vs ->
  forall qa Rs0,
    (forall q0, arg_q_sub (dynq qa q0) (dynq qb q0)) ->
    Forall2 rarg_sub Rs0 Rs ->
    exists Vs0, rsuper_inst CT qa C Rs0 D Vs0 /\ Forall2 rarg_sub Vs0 Vs.
Proof.
  intros CT qb C Rs D Vs H.
  induction H; intros qa Rs0 Hq Hargs.
  - exists Rs0. split; auto. apply rsi_refl.
  - destruct (IHrsuper_inst qa (map (dyn qa Rs0 []) Ss) Hq) as [Vs0 [Hsup Hle]].
    { apply map_dyn_mono; auto. }
    exists Vs0. split; auto. eapply rsi_step; eauto.
Qed.

(** A static superclass view is matched at runtime, up to forgotten
    positions. *)
Lemma super_inst_dyn : forall CT mt qh C Ts D Vs,
  super_inst CT mt qh C Ts D Vs ->
  forall qa qctx ca ma Rs,
    (forall q0, arg_q_sub (dynq qa q0)
                  (dynq qctx (vpa_q mt qh q0))) ->
    Forall2 rarg_sub Rs (map (dyn qctx ca ma) Ts) ->
    exists Vs0, rsuper_inst CT qa C Rs D Vs0 /\
                Forall2 rarg_sub Vs0 (map (dyn qctx ca ma) Vs).
Proof.
  intros CT mt qh C Ts D Vs H.
  induction H; intros qa qctx ca ma Rs Hq Hargs.
  - exists Rs. split; auto. apply rsi_refl.
  - destruct (IHsuper_inst qa qctx ca ma (map (dyn qa Rs []) Ss) Hq)
      as [Vs0 [Hsup Hle]].
    { rewrite map_dyn_subst. simpl map at 3.
      apply map_dyn_map_qual_mono; auto. }
    exists Vs0. split; auto. eapply rsi_step; eauto.
Qed.

Lemma rq_sub_dynq : forall q1 q2 q0,
  rq_sub q1 q2 -> arg_q_sub (dynq q1 q0) (dynq q2 q0).
Proof.
  intros q1 q2 q0 H. unfold rq_sub, arg_q_sub in *.
  destruct H as [-> | [-> | [-> [-> | ->]]]]; auto;
    destruct q0; simpl; auto; destruct q1; simpl; auto.
Qed.

Lemma rq_sub_trans : forall q1 q2 q3,
  rq_sub q1 q2 -> rq_sub q2 q3 -> rq_sub q1 q3.
Proof.
  unfold rq_sub. intros q1 q2 q3 H12 H23.
  destruct H12 as [-> | [-> | [-> H1]]]; auto;
    destruct H23 as [-> | [-> | [-> H2]]]; auto.
  destruct H2; discriminate.
Qed.

Lemma rtype_subtype_refl : forall CT R, rtype_subtype CT R R.
Proof.
  intros CT [q1 C Rs]. simpl. right. split; [left; reflexivity|].
  exists Rs. split; [apply rsi_refl | apply Forall2_rarg_sub_refl].
Qed.

Lemma Forall2_rarg_sub_trans : forall Rs Us Vs,
  Forall2 rarg_sub Rs Us -> Forall2 rarg_sub Us Vs -> Forall2 rarg_sub Rs Vs.
Proof.
  intros Rs Us Vs H. revert Vs.
  induction H; intros Vs H2; inversion H2; subst; constructor;
    eauto using rarg_sub_trans.
Qed.

(** Changing the head and the arguments keeps the shape of a superclass view. *)
Lemma rsuper_inst_rehead : forall CT qa C Rs D Vs,
  rsuper_inst CT qa C Rs D Vs ->
  forall qb Rs', length Rs' = length Rs ->
  exists Vs', rsuper_inst CT qb C Rs' D Vs' /\ length Vs' = length Vs.
Proof.
  intros CT qa C Rs D Vs H. induction H; intros qb Rs' Hlen.
  - exists Rs'. split; auto. apply rsi_refl.
  - destruct (IHrsuper_inst qb (map (dyn qb Rs' []) Ss)) as [Vs' [Hs Hl]].
    { rewrite !length_map. reflexivity. }
    exists Vs'. split; auto. eapply rsi_step; eauto.
Qed.

Lemma super_inst_rsuper_len : forall CT mt qh C Ts D Vs,
  super_inst CT mt qh C Ts D Vs ->
  forall qa Rs, length Rs = length Ts ->
  exists Vs0, rsuper_inst CT qa C Rs D Vs0 /\ length Vs0 = length Vs.
Proof.
  intros CT mt qh C Ts D Vs H. induction H; intros qa Rs Hlen.
  - exists Rs. split; auto. apply rsi_refl.
  - destruct (IHsuper_inst qa (map (dyn qa Rs []) Ss)) as [Vs0 [Hs Hl]].
    { rewrite !length_map. reflexivity. }
    exists Vs0. split; auto. eapply rsi_step; eauto.
Qed.

Lemma rtype_subtype_trans : forall CT R1 R2 R3,
  rtype_subtype CT R1 R2 -> rtype_subtype CT R2 R3 -> rtype_subtype CT R1 R3.
Proof.
  intros CT [q1 C Rs] [q2 D Us] [q3 E Ws] H12 H23. simpl in *.
  assert (H23' : exists qx Xs, rsuper_inst CT qx D Us E Xs /\ length Xs = length Ws).
  { destruct H23 as [(_ & Xs & Hs & Hl) | (_ & Xs & Hs & Hle)].
    - eauto.
    - exists q2, Xs. split; auto. apply (Forall2_length Hle). }
  assert (Hbot : forall Vs, q1 = Bot -> rsuper_inst CT q1 C Rs D Vs ->
                   length Vs = length Us ->
                   q1 = Bot /\ exists Xs, rsuper_inst CT Bot C Rs E Xs /\
                                          length Xs = length Ws).
  { intros Vs Hq Hs Hl. split; auto. subst q1.
    destruct H23' as (qx & Xs & Hs2 & Hl2).
    destruct (rsuper_inst_rehead _ _ _ _ _ _ Hs2 Bot Vs Hl) as (Xs' & Hs3 & Hl3).
    exists Xs'. split; [eapply rsuper_inst_trans; eauto | congruence]. }
  destruct H12 as [(Hq1 & Vs & Hs & Hl) | (Hq12 & Vs & Hsup12 & Hle12)].
  - left. subst q1. eapply Hbot; eauto.
  - destruct H23 as [(Hq2 & Xs & Hs2 & Hl2) | (Hq23 & Xs & Hsup23 & Hle23)].
    + subst q2. destruct Hq12 as [Hq | [Hq | [Hq _]]]; try discriminate.
      left. eapply Hbot; eauto. apply (Forall2_length Hle12).
    + right. split; [eauto using rq_sub_trans|].
      destruct (rsuper_inst_mono _ _ _ _ _ _ Hsup23 q1 Vs) as [Xs0 [Hsup Hle]];
        auto using rq_sub_dynq.
      exists Xs0. split; [eapply rsuper_inst_trans; eauto|].
      eapply Forall2_rarg_sub_trans; eauto.
Qed.

(** The runtime bounds an activation must respect: every declared type
    variable's runtime argument is below its dynamized bound. *)
Definition frame_bounds_ok (CT : class_table) (Δ : tv_env)
    (qctx : q) (ca ma : list rtype) : Prop :=
  forall o n B,
    tv_bound Δ o n = Some B ->
    rtype_subtype CT (dyn qctx ca ma (TVar TVSub o n)) (dyn qctx ca ma B).

Lemma frame_bounds_ok_of_rbounds : forall CT Δ qctx ca ma,
  rbounds_ok CT qctx ca ma ca (class_bounds Δ) ->
  rbounds_ok CT qctx ca ma ma (method_bounds Δ) ->
  frame_bounds_ok CT Δ qctx ca ma.
Proof.
  intros CT Δ qctx ca ma Hc Hm o n B Hb.
  unfold tv_bound in Hb. unfold rbounds_ok in *.
  destruct o; simpl in *.
  - pose proof (Forall2_nth_error_rel _ _ _ n Hc) as Hn.
    rewrite Hb in Hn. destruct (nth_error ca n); [exact Hn|contradiction].
  - pose proof (Forall2_nth_error_rel _ _ _ n Hm) as Hn.
    rewrite Hb in Hn. destruct (nth_error ma n); [exact Hn|contradiction].
Qed.

Lemma dynq_self_agree : forall mt qctx qh q0,
  concrete_q qctx -> qh <> Bot ->
  arg_q_sub (dynq (dynq qctx qh) q0)
    (dynq qctx (vpa_q mt qh q0)).
Proof.
  intros mt qctx qh q0 Hc Hnb. unfold arg_q_sub.
  destruct Hc as [-> | ->]; destruct mt, qh, q0; simpl; auto; congruence.
Qed.

(** The readonly view of a superclass declaration is valid whatever the
    runtime head turns out to be. *)
Lemma dynq_ro_agree : forall mt qctx h q0,
  concrete_q qctx ->
  arg_q_sub (dynq h q0) (dynq qctx (vpa_q mt RO q0)).
Proof.
  intros mt qctx h q0 Hc. unfold arg_q_sub.
  destruct Hc as [-> | ->]; destruct mt, h, q0; simpl; auto.
Qed.

Lemma q_subtype_rq_sub : forall qctx q1 q2,
  q_subtype q1 q2 -> q1 <> Bot -> rq_sub (dynq qctx q1) (dynq qctx q2).
Proof.
  intros qctx q1 q2 H Hnb. unfold rq_sub.
  inversion H; subst; auto. congruence.
Qed.

Lemma q_eq_dec : forall q1 q2 : q, {q1 = q2} + {q1 <> q2}.
Proof. decide equality. Qed.

(** Static subtyping is sound for dynamized types. *)
Lemma subtype_dyn : forall CT Δ qctx ca ma T U,
  concrete_q qctx ->
  frame_bounds_ok CT Δ qctx ca ma ->
  qualified_type_subtype CT Δ T U ->
  rtype_subtype CT (dyn qctx ca ma T) (dyn qctx ca ma U).
Proof.
  intros CT Δ qctx ca ma T U Hc Hframe H.
  induction H.
  - (* same class, widen qualifier *)
    simpl. destruct (q_eq_dec q1 Bot) as [-> | Hnb].
    + left. split; auto. exists (map (dyn qctx ca ma) Ts).
      split; [apply rsi_refl|]. rewrite !length_map. apply (Forall2_length Hargs).
    + right. split; [apply q_subtype_rq_sub; auto|].
      exists (map (dyn qctx ca ma) Ts). split.
      * apply rsi_refl.
      * apply map_dyn_targ_sub; auto.
  - (* up the hierarchy *)
    simpl. destruct (q_eq_dec q1 Bot) as [-> | Hnb].
    + left. split; auto.
      destruct (super_inst_rsuper_len _ _ _ _ _ _ _ Hsuper Bot
                  (map (dyn qctx ca ma) Ts)) as (Vs0 & Hs & Hl).
      { apply length_map. }
      exists Vs0. split; auto. rewrite length_map. exact Hl.
    + right. split; [left; reflexivity|].
      eapply super_inst_dyn; eauto using dynq_self_agree, Forall2_rarg_sub_refl.
  - apply rtype_subtype_refl.
  - apply Hframe; auto.
  - (* widen the written qualifier of a variable use *)
    simpl.
    destruct (match tv_lookup o ca ma n with Some R => R | None => default_rtype end)
      as [q0 C0 Rs0].
    simpl. destruct (q_eq_dec q1 Bot) as [-> | Hnb].
    + left. split; auto. exists Rs0. split; [apply rsi_refl | reflexivity].
    + right. split; [apply q_subtype_rq_sub; auto|].
      exists Rs0. split; [apply rsi_refl | apply Forall2_rarg_sub_refl].
  - (* view the supplied type as readonly *)
    simpl.
    destruct (match tv_lookup o ca ma n with Some R => R | None => default_rtype end)
      as [q0 C0 Rs0].
    simpl. right. split; [right; left; reflexivity|].
    exists Rs0. split; [apply rsi_refl | apply Forall2_rarg_sub_refl].
  - (* view a qualified variable use at an argument-free bound *)
    simpl in *.
    destruct (match tv_lookup o ca ma n with Some R => R | None => default_rtype end)
      as [q0 C0 Rs0].
    simpl.
    assert (Hsh : exists qx Vs, rsuper_inst CT qx C0 Rs0 C Vs /\ length Vs = 0).
    { destruct IHqualified_type_subtype as [(_ & Vs & Hs & Hl) | (_ & Vs & Hs & Hle)].
      - eauto.
      - exists q0, Vs. split; auto. inversion Hle; reflexivity. }
    destruct Hsh as (qx & Vs & Hs & Hl).
    destruct (rsuper_inst_rehead _ _ _ _ _ _ Hs (dynq qctx q1) Rs0 eq_refl)
      as (Vs' & Hs' & Hl').
    assert (Vs' = []) by (destruct Vs'; [reflexivity | simpl in Hl'; lia]).
    subst Vs'.
    destruct (q_eq_dec (dynq qctx q1) Bot) as [Hb | Hnb].
    + left. split; auto. rewrite Hb in Hs'. eauto.
    + right. split; [left; reflexivity|]. exists (@nil rtype). split; auto.
  - (* view a variable-headed class type as readonly *)
    simpl. right. split; [right; left; reflexivity|].
    exists (map (dyn qctx ca ma) Ts).
    split; [apply rsi_refl | apply map_dyn_targ_sub; auto].
  - (* compatible arguments under the same variable head *)
    simpl. right. split; [left; reflexivity|].
    exists (map (dyn qctx ca ma) Ts).
    split; [apply rsi_refl | apply map_dyn_targ_sub; auto].
  - (* up the hierarchy under the same variable head *)
    simpl. right. split; [left; reflexivity|].
    eapply super_inst_dyn; eauto using dynq_ro_agree, Forall2_rarg_sub_refl.
  - (* the bottom-qualified type of the class *)
    simpl. left. split; auto. exists (map (dyn qctx ca ma) Ts).
    split; [apply rsi_refl|]. rewrite !length_map. apply (Forall2_length Hargs).
  - eapply rtype_subtype_trans; eauto.
Qed.

(* ------------------LOCATIONS------------------*)

Lemma head_ok_rq_sub : forall qo q1 q2,
  head_ok qo q1 -> rq_sub q1 q2 -> head_ok qo q2.
Proof.
  unfold head_ok, rq_sub. intros qo q1 q2 H1 H2.
  destruct H2 as [-> | [-> | [-> _]]]; auto.
Qed.

Lemma head_ok_not_bot : forall qo, ~ head_ok qo Bot.
Proof.
  intros qo H. unfold head_ok in H.
  destruct H as [H | [H | H]]; try discriminate.
  destruct qo; discriminate.
Qed.

(** An object that inhabits a runtime type inhabits every runtime supertype. *)
Lemma loc_has_rtype_sub : forall CT h ι R R',
  loc_has_rtype CT h ι R ->
  rtype_subtype CT R R' ->
  loc_has_rtype CT h ι R'.
Proof.
  intros CT h ι [q1 D Us] [q2 E Xs] Hloc Hsub.
  unfold loc_has_rtype in *.
  destruct (runtime_getObj h ι) as [o|]; [|contradiction].
  destruct Hloc as [Hhead [Vs [Hsup Hle]]].
  simpl in Hsub. destruct Hsub as [[-> _] | [Hq [Ws [Hsup2 Hle2]]]].
  - exfalso. eapply head_ok_not_bot; eauto.
  - split; [eauto using head_ok_rq_sub|].
    destruct (rsuper_inst_mono _ _ _ _ _ _ Hsup2 (qr2q (rqtype (rt_type o))) Vs)
      as [Ws0 [Hsup3 Hle3]]; auto.
    { intros q0. apply dynq_head_agree; auto using qr2q_concrete. }
    exists Ws0. split; [eapply rsuper_inst_trans; eauto|].
    eapply Forall2_rarg_sub_trans; eauto.
Qed.

Lemma rarg_sub_rtype_subtype : forall CT R R',
  rarg_sub R R' -> rtype_subtype CT R R'.
Proof.
  intros CT R R' H. inversion H; subst. simpl. right. split.
  - unfold rq_sub. destruct Hq as [-> | [-> Hc]]; auto.
  - exists Rs. split; [apply rsi_refl | auto].
Qed.

Lemma loc_has_rtype_rarg_sub : forall CT h ι R R',
  loc_has_rtype CT h ι R -> rarg_sub R R' -> loc_has_rtype CT h ι R'.
Proof.
  intros. eapply loc_has_rtype_sub; eauto using rarg_sub_rtype_subtype.
Qed.

(** Subsumption for runtime typability. *)
Lemma wf_r_typable_subtype : forall CT Δ h ι T U qctx ca ma,
  frame_bounds_ok CT Δ (qr2q qctx) ca ma ->
  qualified_type_subtype CT Δ T U ->
  wf_r_typable CT h ι T qctx ca ma ->
  wf_r_typable CT h ι U qctx ca ma.
Proof.
  unfold wf_r_typable. intros.
  eapply loc_has_rtype_sub; eauto.
  eapply subtype_dyn; eauto using qr2q_concrete.
Qed.

(** Runtime typability depends on the heap only through the object's runtime
    type. *)
Lemma loc_has_rtype_heap_irrel : forall CT h h' ι R,
  r_type h ι = r_type h' ι ->
  loc_has_rtype CT h ι R -> loc_has_rtype CT h' ι R.
Proof.
  intros CT h h' ι R Heq H. unfold loc_has_rtype, r_type in *.
  destruct (runtime_getObj h ι) as [o|]; [|contradiction].
  destruct (runtime_getObj h' ι) as [o'|]; [|discriminate].
  inversion Heq as [Heq']. destruct R.
  first [exact H | rewrite Heq' in H; exact H | rewrite <- Heq' in H; exact H | rewrite <- Heq'; exact H].
Qed.

(** Reading a declared member type through a receiver.  The object [qo],
    seen through a client qualifier [qx] in an activation with mutability
    [qctx], with its class arguments [Vs] agreeing with the client's [Ws] and
    method arguments [Ms] agreeing with [Ms']: whatever inhabits the object's
    own reading of [T] inhabits the client's adapted reading. *)
Lemma loc_has_rtype_adapt : forall CT h ι mt qo qctx qx Vs Ws Ms Ms' T,
  head_ok qo (dynq (qr2q qctx) qx) ->
  Forall2 rarg_sub Vs Ws -> Forall2 rarg_sub Ms Ms' ->
  loc_has_rtype CT h ι (dyn (qr2q qo) Vs Ms T) ->
  loc_has_rtype CT h ι (dyn (qr2q qctx) Ws Ms' (adapt mt qx T)).
Proof.
  intros. eapply loc_has_rtype_rarg_sub; eauto.
  unfold adapt. apply dyn_map_qual_mono; auto.
  intros q0. apply dynq_vpa_q_agree; auto using qr2q_concrete.
Qed.

(** The converse direction, when the client's adapted reading is fully known:
    the two readings are then the same runtime type. *)
Lemma dyn_adapt_exact : forall mt qo qctx qx Vs Ws Ms Ms' T,
  head_ok qo (dynq (qr2q qctx) qx) ->
  Forall2 rarg_sub Vs Ws -> Forall2 rarg_sub Ms Ms' ->
  rlost_free (dyn (qr2q qctx) Ws Ms' (adapt mt qx T)) ->
  dyn (qr2q qo) Vs Ms T = dyn (qr2q qctx) Ws Ms' (adapt mt qx T).
Proof.
  intros. apply rarg_sub_lost_free_eq; auto.
  unfold adapt. apply dyn_map_qual_mono; auto.
  intros q0. apply dynq_vpa_q_agree; auto using qr2q_concrete.
Qed.
