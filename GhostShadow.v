From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  GhostLabels GhostTyping GhostFit.

(** Labelled types with every mutable qualifier forgotten.

    A qualified use [@Mut X] reads the supplied argument with a mutable head
    in the reading frame's world, while the argument's own mutable positions
    may be in other worlds.  The proof that such a use reads its bound's class
    consistently follows the class's declarations with a shadow in which no
    supplied mutable position is left.  This file provides the operation and
    the facts that subtyping and agreement survive it. *)

Definition kq (q0 : q) : q := match q0 with Mut => Lost | _ => q0 end.

Fixpoint lkill (A : ltype) : ltype :=
  match A with
  | LT q0 l C As => LT (kq q0) l C (map lkill As)
  end.

Lemma kq_not_mut : forall q0, kq q0 <> Mut.
Proof. intros []; simpl; discriminate. Qed.

Lemma lkill_rehead : forall h l A, lkill (lrehead h l A) = lrehead (kq h) l (lkill A).
Proof. intros h l [q0 l0 C As]. reflexivity. Qed.

Lemma lkill_default : lkill ldefault = ldefault.
Proof. reflexivity. Qed.

Lemma lagree_lkill : forall L A B, lagree L A B -> lagree L (lkill A) (lkill B).
Proof.
  intros L A B H. induction H using lagree_ind'. simpl. constructor.
  - unfold arg_q_sub in *. destruct H as [-> | [-> Hq]]; [left; reflexivity|].
    destruct q1; simpl; try (left; reflexivity); right; split; auto;
      destruct Hq as [Hx | [Hx | [Hx | [Hx | Hx]]]]; discriminate || auto.
  - right. left. apply kq_not_mut.
  - clear H H0 H1. induction H2; simpl; constructor; auto.
Qed.

Lemma Forall2_lagree_lkill : forall L As Bs,
  Forall2 (lagree L) As Bs -> Forall2 (lagree L) (map lkill As) (map lkill Bs).
Proof. intros L As Bs H. induction H; simpl; constructor; auto using lagree_lkill. Qed.

(** A head that forgets its mutability reads a declaration as the forgetful
    image of the original reading. *)
Lemma kq_tg : forall x q0, dynq (kq x) (tg (kq x) q0) = kq (dynq x (tg x q0)).
Proof. intros [] []; reflexivity. Qed.

Lemma kq_tg_not_mut : forall x q0, dynq (kq x) (tg (kq x) q0) <> Mut.
Proof. intros [] []; simpl; discriminate. Qed.

Lemma tv_lookup_map : forall (f : ltype -> ltype) o cs ms n,
  tv_lookup o (map f cs) (map f ms) n = option_map f (tv_lookup o cs ms n).
Proof. intros f [] cs ms n; simpl; apply nth_error_map. Qed.

Lemma ldyn_tframe_lkill : forall L x l As S,
  lagree L (ldyn (tframe (kq x) l (map lkill As)) (map_qual (tg (kq x)) S))
           (lkill (ldyn (tframe x l As) (map_qual (tg x) S))).
Proof.
  intros L x l As S. induction S using qualified_type_ind'.
  - cbn [map_qual ldyn lkill tframe lf_q]. constructor.
    + rewrite kq_tg. left. reflexivity.
    + right. left. apply kq_tg_not_mut.
    + rewrite !map_map. induction H; simpl; constructor; auto.
  - assert (HA : match tv_lookup o (map lkill As) [] n with
                 | Some A => A | None => ldefault end =
                 lkill (match tv_lookup o As [] n with
                        | Some A => A | None => ldefault end)).
    { destruct o; simpl; [rewrite nth_error_map; destruct (nth_error As n) |
                         destruct n]; reflexivity. }
    destruct u as [|q0|m]; cbn [map_qual ldyn tframe lf_q lf_cargs lf_margs lf_qargs];
      rewrite HA.
    + apply lagree_refl.
    + rewrite lkill_rehead. rewrite kq_tg.
      destruct (match tv_lookup o As [] n with
                | Some A => A | None => ldefault end) as [qa la Ca Aa].
      simpl. constructor; [left; reflexivity | right; left; apply kq_not_mut |].
      apply Forall2_lagree_refl.
    + rewrite lkill_rehead. destruct m; apply lagree_refl.
  - cbn [map_qual ldyn lkill tframe lf_qargs].
    replace (kq (fst (lqnth [] n))) with (fst (lqnth [] n)) by (destruct n; reflexivity).
    constructor.
    + left. reflexivity.
    + right. left. destruct n; discriminate.
    + rewrite !map_map. induction H; simpl; constructor; auto.
Qed.

Lemma tstep_lkill : forall L x l As As' Ss,
  Forall2 (lagree L) As' (map lkill As) ->
  Forall2 (lagree L) (tstep (kq x) l As' Ss) (map lkill (tstep x l As Ss)).
Proof.
  intros L x l As As' Ss Hle.
  eapply Forall2_lagree_trans.
  - unfold tstep. apply (map_ldyn_map_qual_agree2 L (tg (kq x)) (tg (kq x))
      (tframe (kq x) l As') (tframe (kq x) l (map lkill As))).
    + apply label_cond2_refl.
    + exact Hle.
    + constructor.
    + reflexivity.
  - unfold tstep. rewrite map_map. induction Ss as [|S Ss IH]; simpl; constructor; auto.
    apply ldyn_tframe_lkill.
Qed.

Lemma ltsuper_lkill : forall CT x l C As D Vs,
  ltsuper CT x l C As D Vs ->
  forall L As', Forall2 (lagree L) As' (map lkill As) ->
    exists Vs', ltsuper CT (kq x) l C As' D Vs' /\ Forall2 (lagree L) Vs' (map lkill Vs).
Proof.
  intros CT x l C As D Vs H. induction H as [C As | C As P Ss D Vs Hparent Hrest IH];
    intros L As' Hle.
  - exists As'. split; [apply lts_refl | exact Hle].
  - destruct (IH L (tstep (kq x) l As' Ss) (tstep_lkill L x l As As' Ss Hle))
      as (Vs' & Hv & Hl).
    exists Vs'. split; auto. eapply lts_step; eauto.
Qed.

(** The same for the bottom reader, with the bottom escape. *)
Lemma bagree_lkill : forall L A B, bagree L A B -> bagree L (lkill A) (lkill B).
Proof.
  intros L A B H. induction H using bagree_ind'. simpl. constructor.
  - destruct H as [[-> Hro] | Hq].
    + left. split; [reflexivity|]. destruct q2; simpl; congruence.
    + right. unfold arg_q_sub in *. destruct Hq as [-> | [-> Hq]]; [left; reflexivity|].
      destruct q1; simpl; try (left; reflexivity); right; split; auto;
        destruct Hq as [Hx | [Hx | [Hx | [Hx | Hx]]]]; discriminate || auto.
  - right. left. apply kq_not_mut.
  - clear H H0 H1. induction H2; simpl; constructor; auto.
Qed.

Lemma Forall2_bagree_lkill : forall L As Bs,
  Forall2 (bagree L) As Bs -> Forall2 (bagree L) (map lkill As) (map lkill Bs).
Proof. intros L As Bs H. induction H; simpl; constructor; auto using bagree_lkill. Qed.

Lemma kq_bq : forall q0, kq (dynq Bot (bq q0)) = dynq Bot (bq q0).
Proof. intros []; reflexivity. Qed.

Lemma ldyn_bframe_lkill : forall L As S,
  bagree L (ldyn (bframe (map lkill As)) (map_qual bq S))
           (lkill (ldyn (bframe As) (map_qual bq S))).
Proof.
  intros L As S. induction S using qualified_type_ind'.
  - cbn [map_qual ldyn lkill bframe lf_q]. constructor.
    + rewrite kq_bq. right. left. reflexivity.
    + right. left. apply bq_not_mut.
    + rewrite !map_map. induction H; simpl; constructor; auto.
  - assert (HA : match tv_lookup o (map lkill As) [] n with
                 | Some A => A | None => ldefault end =
                 lkill (match tv_lookup o As [] n with
                        | Some A => A | None => ldefault end)).
    { destruct o; simpl; [rewrite nth_error_map; destruct (nth_error As n) |
                         destruct n]; reflexivity. }
    destruct u as [|q0|m]; cbn [map_qual ldyn bframe lf_q lf_cargs lf_margs lf_qargs];
      rewrite HA.
    + apply bagree_refl.
    + rewrite lkill_rehead. rewrite kq_bq.
      destruct (match tv_lookup o As [] n with
                | Some A => A | None => ldefault end) as [qa la Ca Aa].
      simpl. constructor; [right; left; reflexivity | right; left; apply bq_not_mut |].
      apply Forall2_bagree_refl.
    + rewrite lkill_rehead. destruct m; apply bagree_refl.
  - cbn [map_qual ldyn lkill bframe lf_qargs].
    replace (kq (fst (lqnth [] n))) with (fst (lqnth [] n)) by (destruct n; reflexivity).
    constructor.
    + right. left. reflexivity.
    + right. left. destruct n; discriminate.
    + rewrite !map_map. induction H; simpl; constructor; auto.
Qed.

Lemma bstep_lkill : forall L As As' Ss,
  Forall2 (bagree L) As' (map lkill As) ->
  Forall2 (bagree L) (bstep As' Ss) (map lkill (bstep As Ss)).
Proof.
  intros L As As' Ss Hle.
  eapply Forall2_bagree_trans.
  - apply bstep_bstep. exact Hle.
  - unfold bstep. rewrite map_map. induction Ss as [|S Ss IH]; simpl; constructor; auto.
    apply ldyn_bframe_lkill.
Qed.

Lemma lbsuper_lkill : forall CT C As D Vs,
  lbsuper CT C As D Vs ->
  forall L As', Forall2 (bagree L) As' (map lkill As) ->
    exists Vs', lbsuper CT C As' D Vs' /\ Forall2 (bagree L) Vs' (map lkill Vs).
Proof.
  intros CT C As D Vs H.
  induction H as [C As | C As P Ss D Vs Hparent Hrest IH]; intros L As' Hle.
  - exists As'. split; [apply lbs_refl | exact Hle].
  - destruct (IH L (bstep As' Ss) (bstep_lkill L As As' Ss Hle)) as (Vs' & Hv & Hl).
    exists Vs'. split; auto. eapply lbs_step; eauto.
Qed.

Lemma ltsuper_any_lkill : forall CT C As D Vs,
  ltsuper_any CT C As D Vs ->
  forall L As', Forall2 (lagree L) As' (map lkill As) ->
    exists Vs', ltsuper_any CT C As' D Vs' /\ Forall2 (lagree L) Vs' (map lkill Vs).
Proof.
  intros CT C As D Vs H.
  induction H as [C As | qA lA C As P Ss D Vs Hparent Hrest IH]; intros L As' Hle.
  - exists As'. split; [apply lta_refl | exact Hle].
  - destruct (IH L (tstep (kq qA) lA As' Ss) (tstep_lkill L qA lA As As' Ss Hle))
      as (Vs' & Hv & Hl).
    exists Vs'. split; auto. eapply lta_step; eauto.
Qed.

(** Forgetting mutability keeps labelled subtyping. *)
Lemma rq_sub_kq : forall q1 q2, rq_sub q1 q2 -> rq_sub (kq q1) (kq q2).
Proof.
  intros q1 q2 H. unfold rq_sub in *.
  destruct H as [-> | [-> | [-> Hq]]]; [left; reflexivity | right; left; reflexivity|].
  destruct Hq as [-> | [-> | [-> | [-> | ->]]]]; simpl; auto 8.
Qed.

Lemma lsubt_lkill : forall CT L A B, lsubt CT L A B -> lsubt CT L (lkill A) (lkill B).
Proof.
  intros CT L [q1 l1 C As] [q2 l2 D Bs] H. simpl.
  destruct H as [(Hb & Vs & Hv & Hle) | (Hrq & Hl & Vs & Hv & Hle)].
  - left. subst q1. split; [reflexivity|].
    destruct (lbsuper_lkill _ _ _ _ _ Hv L (map lkill As)
                (Forall2_bagree_refl _ _)) as (Vs' & Hv' & Hl').
    exists Vs'. split; auto.
    eapply Forall2_bagree_trans; [exact Hl' | apply Forall2_bagree_lkill; exact Hle].
  - right. refine (conj (rq_sub_kq _ _ Hrq) (conj _ _)).
    + intros Hm. exfalso. exact (kq_not_mut _ Hm).
    + destruct (ltsuper_lkill _ _ _ _ _ _ _ Hv L (map lkill As)
                  (Forall2_lagree_refl _ _)) as (Vs' & Hv' & Hl').
      exists Vs'. split; auto.
      eapply Forall2_lagree_trans; [exact Hl' | apply Forall2_lagree_lkill; exact Hle].
Qed.

(* ------------------A FRAME WITH ITS MUTABILITY FORGOTTEN------------------*)

(** The frame read through a head that forgets receiver-dependent positions,
    with every mutable qualifier of its arguments forgotten. *)
Definition lfk (F : lframe) : lframe :=
  mk_lframe Lost (lf_mut F) (lf_rdm F) (map lkill (lf_cargs F))
    (map lkill (lf_margs F)) (map (fun p => (kq (fst p), snd p)) (lf_qargs F)).

Lemma lfk_lookup : forall F o n,
  match tv_lookup o (lf_cargs (lfk F)) (lf_margs (lfk F)) n with
  | Some A => A | None => ldefault end =
  lkill (match tv_lookup o (lf_cargs F) (lf_margs F) n with
         | Some A => A | None => ldefault end).
Proof.
  intros F o n. unfold lfk. cbn [lf_cargs lf_margs]. rewrite tv_lookup_map.
  destruct (tv_lookup o (lf_cargs F) (lf_margs F) n); reflexivity.
Qed.

Lemma lfk_qnth : forall F m,
  lqnth (lf_qargs (lfk F)) m =
  (kq (fst (lqnth (lf_qargs F) m)), snd (lqnth (lf_qargs F) m)).
Proof.
  intros F m. unfold lfk, lqnth. cbn [lf_qargs].
  change (RO, LOut) with ((fun p : q * lab => (kq (fst p), snd p)) (RO, LOut)).
  rewrite map_nth. reflexivity.
Qed.

(** A type that writes no mutable position reads, in the forgetful frame, as
    the forgetful image of its reading. *)
Lemma ldyn_lfk : forall L Δ F T,
  no_mut Δ T -> lagree L (lkill (ldyn F T)) (ldyn (lfk F) T).
Proof.
  intros L Δ F T. induction T using qualified_type_ind'; intros Hnm.
  - inversion Hnm; subst. cbn [ldyn lkill]. constructor.
    + destruct qual; try contradiction; simpl;
        unfold arg_q_sub; try (left; reflexivity); destruct (lf_q F); simpl;
        first [left; reflexivity | right; split; auto 6].
    + right. left. apply kq_not_mut.
    + rewrite map_map. clear Hq Hnm. revert Hargs.
      induction H; intros Hargs; simpl; constructor;
        inversion Hargs; subst; auto.
  - cbn [ldyn]. rewrite lfk_lookup.
    destruct (match tv_lookup o (lf_cargs F) (lf_margs F) n with
              | Some A => A | None => ldefault end) as [qa la Ca Aa].
    destruct u as [|q0|m].
    + apply lagree_refl.
    + inversion Hnm; subst. simpl. unfold lfk at 1. cbn [lf_q].
      constructor.
      * destruct q0; try contradiction; simpl;
          unfold arg_q_sub; try (left; reflexivity); destruct (lf_q F); simpl;
          first [left; reflexivity | right; split; auto 6].
      * right. left. apply kq_not_mut.
      * apply Forall2_lagree_refl.
    + rewrite lfk_qnth. simpl. apply lagree_refl.
  - inversion Hnm; subst. cbn [ldyn lkill]. rewrite lfk_qnth. simpl. constructor.
    + left. reflexivity.
    + right. left. apply kq_not_mut.
    + rewrite map_map. clear Hnm. revert Hargs.
      induction H; intros Hargs; simpl; constructor;
        inversion Hargs; subst; auto.
Qed.

Lemma frame_fits_lfk : forall CT L Δ F,
  frame_fits CT L Δ F ->
  (forall o n B, tv_bound Δ o n = Some B -> no_mut Δ B) ->
  frame_fits CT L Δ (lfk F).
Proof.
  intros CT L Δ F Hfit Hnm o n B Hb.
  assert (HX : ldyn (lfk F) (TVar TVSub o n) = lkill (ldyn F (TVar TVSub o n))).
  { cbn [ldyn]. apply lfk_lookup. }
  rewrite HX. eapply lsubt_agree_r.
  - apply lsubt_lkill. exact (Hfit o n B Hb).
  - eapply ldyn_lfk. exact (Hnm o n B Hb).
Qed.
