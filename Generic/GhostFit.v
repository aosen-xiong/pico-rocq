From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels GhostTyping
  GhostForget.

(* ------------------SMALL DEFINITIONS------------------*)

Definition olab (c : option nat) : lab :=
  match c with Some w => LIn w | None => LOut end.

(** A mutable object that has a birth world is in it.  An immutable object
    created during a protected call keeps that call's world as its birth world
    without being in any world. *)
Definition mutcL (CT : class_table) (h : heap) (G : ghost) : Prop :=
  forall l w o, g_birth G l = Some w ->
    runtime_getObj h l = Some o -> rqtype (rt_type o) = Mut_r ->
    g_col G l = Some w.

Lemma mutcL_olab : forall P CT h G L next l o,
  heapL P CT h G L next -> mutcL CT h G ->
  runtime_getObj h l = Some o -> rqtype (rt_type o) = Mut_r ->
  olab (g_birth G l) = olab (g_col G l).
Proof.
  intros P CT h G L next l o HG HM Ho Hq.
  destruct (g_birth G l) as [w|] eqn:Hb.
  - rewrite (HM l w o Hb Ho Hq). reflexivity.
  - destruct (g_col G l) as [w|] eqn:Hc; auto.
    destruct (hl_col _ _ _ _ _ _ HG _ _ Hc) as (_ & _ & _ & _ & Hb2). congruence.
Qed.

Lemma norm_olab_dead : forall L c,
  (forall w, c = Some w -> ~ List.In w L) -> norm L (olab c) = None.
Proof.
  intros L c H. destruct c as [w|]; unfold olab, norm; auto.
  destruct (in_dec Nat.eq_dec w L) as [Hin | Hnin]; auto.
  exfalso. exact (H w eq_refl Hin).
Qed.

Lemma headL_norm : forall L c l,
  match norm L l with
  | Some w => c = Some w
  | None => forall w, c = Some w -> ~ List.In w L
  end ->
  norm L (olab c) = norm L l.
Proof.
  intros L c l H. destruct (norm L l) as [w|] eqn:Hn.
  - subst c. simpl. apply norm_live. eapply norm_some_in; eauto.
  - apply norm_olab_dead. exact H.
Qed.

(** Subtyping between labelled types.  What a value of a labelled type looks
    like at a superclass is determined by the labelled type alone. *)

(* ------------------THE VIEW OF A LABELLED TYPE AT A SUPERCLASS------------------*)

(** How a qualifier written in a superclass argument reads for a type whose
    head is [qA]: a written [Mut] stays mutable only under a mutable head; a
    written [RDM] follows a mutable or immutable head. *)
Definition tg (qA : q) (q0 : q) : q :=
  match q0 with
  | Mut => match qA with Mut => Mut | _ => Lost end
  | RDM => match qA with Mut | Imm => RDM | Bot => Bot | _ => Lost end
  | _ => q0
  end.

Definition tframe (qA : q) (lA : lab) (As : list ltype) : lframe :=
  mk_lframe qA lA lA As [] [].

Definition tstep (qA : q) (lA : lab) (As : list ltype)
    (Ss : list qualified_type) : list ltype :=
  map (fun S => ldyn (tframe qA lA As) (map_qual (tg qA) S)) Ss.

Inductive ltsuper (CT : class_table) (qA : q) (lA : lab)
    : class_name -> list ltype -> class_name -> list ltype -> Prop :=
  | lts_refl : forall C As, ltsuper CT qA lA C As C As
  | lts_step : forall C As P Ss D Vs
      (Hparent : parent_lookup CT C = Some (P, Ss))
      (Hrest : ltsuper CT qA lA P (tstep qA lA As Ss) D Vs),
      ltsuper CT qA lA C As D Vs.

Definition lsubt (CT : class_table) (L : list nat) (A B : ltype) : Prop :=
  match A, B with
  | LT q1 l1 C As, LT q2 l2 D Bs =>
      (q1 = Bot /\
       exists Vs, ltsuper CT q1 l1 C As D Vs /\ length Vs = length Bs) \/
      (rq_sub q1 q2 /\
       (q2 = Mut -> norm L l1 = norm L l2) /\
       exists Vs, ltsuper CT q1 l1 C As D Vs /\ Forall2 (lagree L) Vs Bs)
  end.

(* ------------------SOUNDNESS------------------*)

(** The object's own reading against the labelled type's reading. *)
Lemma tview_label_cond : forall L qo b c As q1 l1 Bs,
  head_ok qo q1 ->
  (q1 = Mut -> norm L (olab b) = norm L l1 /\ norm L (olab c) = norm L l1) ->
  label_cond L (tg q1) (obj_frame qo b c As) (tframe q1 l1 Bs).
Proof.
  intros L qo b c As q1 l1 Bs Hhead Hl q0.
  unfold head_ok in Hhead.
  destruct Hhead as [-> | [-> | ->]]; destruct q0, qo;
    cbv [tg obj_frame tframe lf_q lab_of lf_mut lf_rdm qr2q dynq arg_q_sub];
    (split;
     [ solve [left; reflexivity] || solve [right; split; auto]
     | solve [left; reflexivity] || solve [right; left; discriminate]
       || solve [right; right; reflexivity]
       || solve [right; right; exact (proj1 (Hl eq_refl))]
       || solve [right; right; exact (proj2 (Hl eq_refl))] ]).
Qed.

Lemma obj_vs_type_view : forall CT qA lA C As D Vs,
  ltsuper CT qA lA C As D Vs ->
  forall L qo b c Vs0,
    label_cond L (tg qA) (obj_frame qo b c []) (tframe qA lA []) ->
    Forall2 (lagree L) Vs0 As ->
    exists Ws0, lsuper_inst CT qo b c C Vs0 D Ws0 /\ Forall2 (lagree L) Ws0 Vs.
Proof.
  intros CT qA lA C As D Vs H.
  induction H as [C As | C As P Ss D Vs Hparent Hrest IH];
    intros L qo b c Vs0 Hcond Hle.
  - exists Vs0. split; [apply lsi_refl | exact Hle].
  - destruct (IH L qo b c (map (ldyn (obj_frame qo b c Vs0)) Ss) Hcond)
      as (Ws0 & Hs & Hle').
    { unfold tstep. rewrite <- (map_map (map_qual (tg qA)) (ldyn (tframe qA lA As))).
      apply map_ldyn_map_qual_agree.
      - exact (label_cond_args L _ _ _ Vs0 [] As [] _ _ Hcond).
      - exact Hle.
      - constructor.
      - reflexivity. }
    exists Ws0. split; auto. eapply lsi_step; eauto.
Qed.



(** A value of a labelled type is a value of every labelled supertype. *)
Lemma lsubt_sound : forall P CT h G L next v A B,
  heapL P CT h G L next ->
  mutcL CT h G ->
  loc_has_rtype CT h v (erase A) ->
  lhas CT h G L v A ->
  lsubt CT L A B ->
  lhas CT h G L v B.
Proof.
  intros P CT h G L next v [q1 l1 C As] [q2 l2 D Bs] HG HM Hty Hl Hsub.
  destruct Hl as (o & Ho & Hh & Vs0 & Hs0 & Hle0).
  unfold loc_has_rtype in Hty. rewrite Ho in Hty. simpl in Hty.
  destruct Hty as [Hhead _].
  destruct Hsub as [[-> _] | (Hrq & Hlab & Vs & Hts & Hle)];
    [exfalso; exact (head_ok_not_bot _ Hhead)|].
  assert (Hcond : label_cond L (tg q1)
                    (obj_frame (rqtype (rt_type o)) (g_birth G v) (g_col G v) [])
                    (tframe q1 l1 [])).
  { apply tview_label_cond; auto.
    intros ->.
    assert (Hqo : rqtype (rt_type o) = Mut_r).
    { unfold head_ok in Hhead. destruct (rqtype (rt_type o)); auto.
      simpl in Hhead. destruct Hhead as [Hx | [Hx | Hx]]; discriminate. }
    rewrite (mutcL_olab P CT h G L next v o HG HM Ho Hqo).
    pose proof (headL_norm L (g_col G v) l1 (Hh eq_refl)) as Hn. auto. }
  destruct (obj_vs_type_view _ _ _ _ _ _ _ Hts L _ _ _ Vs0 Hcond Hle0)
    as (Ws0 & Hs & Hle').
  exists o. split; auto. split.
  - unfold headL. intros Hm. subst q2.
    assert (q1 = Mut).
    { unfold rq_sub in Hrq. destruct Hrq as [Hx | [Hx | [Hx _]]]; congruence. }
    subst q1. rewrite <- (Hlab eq_refl). exact (Hh eq_refl).
  - exists Ws0. split.
    + eapply lsuper_inst_trans; eauto.
    + eapply Forall2_lagree_trans; eauto.
Qed.

(* ------------------BASIC FACTS ABOUT LABELLED SUBTYPING------------------*)

Definition label_cond2 (L : list nat) (g f : q -> q) (Fo Fc : lframe) : Prop :=
  forall q0,
    arg_q_sub (dynq (lf_q Fo) (g q0)) (dynq (lf_q Fc) (f q0)) /\
    (dynq (lf_q Fc) (f q0) = Lost \/ dynq (lf_q Fo) (g q0) <> Mut \/
     norm L (lab_of Fo (g q0)) = norm L (lab_of Fc (f q0))).

Lemma ldyn_map_qual_agree2 : forall L g f Fo Fc T,
  label_cond2 L g f Fo Fc ->
  Forall2 (lagree L) (lf_cargs Fo) (lf_cargs Fc) ->
  Forall2 (lagree L) (lf_margs Fo) (lf_margs Fc) ->
  lf_qargs Fo = lf_qargs Fc ->
  lagree L (ldyn Fo (map_qual g T)) (ldyn Fc (map_qual f T)).
Proof.
  intros L g f Fo Fc T Hq Hc Hm Hqs.
  induction T using qualified_type_ind'.
  - simpl. destruct (Hq qual) as [H1 H2]. constructor; auto.
    induction H; simpl; constructor; auto.
  - pose proof (tv_lookup_Forall2 (lagree L) o _ _ _ _ n Hc Hm) as Hl.
    assert (HA : lagree L
              match tv_lookup o (lf_cargs Fo) (lf_margs Fo) n with
              | Some A => A | None => ldefault end
              match tv_lookup o (lf_cargs Fc) (lf_margs Fc) n with
              | Some A => A | None => ldefault end).
    { destruct (tv_lookup o (lf_cargs Fo) (lf_margs Fo) n),
               (tv_lookup o (lf_cargs Fc) (lf_margs Fc) n);
        try contradiction; auto using lagree_default. }
    destruct u as [|qual|m]; simpl; auto.
    + destruct (Hq qual) as [H1 H2].
      inversion HA; subst. simpl. constructor; auto.
    + rewrite Hqs. inversion HA; subst. simpl.
      constructor; auto; left; reflexivity.
  - simpl. rewrite Hqs. constructor; [left; reflexivity | auto |].
    induction H; simpl; constructor; auto.
Qed.

Lemma map_ldyn_map_qual_agree2 : forall L g f Fo Fc Ss,
  label_cond2 L g f Fo Fc ->
  Forall2 (lagree L) (lf_cargs Fo) (lf_cargs Fc) ->
  Forall2 (lagree L) (lf_margs Fo) (lf_margs Fc) ->
  lf_qargs Fo = lf_qargs Fc ->
  Forall2 (lagree L) (map (fun S => ldyn Fo (map_qual g S)) Ss)
    (map (fun S => ldyn Fc (map_qual f S)) Ss).
Proof.
  intros. induction Ss; simpl; constructor; auto using ldyn_map_qual_agree2.
Qed.

Lemma ltsuper_trans : forall CT q0 l0 C As D Vs,
  ltsuper CT q0 l0 C As D Vs ->
  forall E Ws, ltsuper CT q0 l0 D Vs E Ws -> ltsuper CT q0 l0 C As E Ws.
Proof.
  intros CT q0 l0 C As D Vs H. induction H; intros E Ws H2; auto.
  eapply lts_step; eauto.
Qed.

(** The classes and lengths of a view do not depend on the head. *)
Lemma ltsuper_len : forall CT q0 l0 C As D Vs,
  ltsuper CT q0 l0 C As D Vs ->
  forall q' l' As', length As' = length As ->
    exists Vs', ltsuper CT q' l' C As' D Vs' /\ length Vs' = length Vs.
Proof.
  intros CT q0 l0 C As D Vs H.
  induction H as [C As | C As P Ss D Vs Hparent Hrest IH]; intros q' l' As' Hlen.
  - exists As'. split; [apply lts_refl | exact Hlen].
  - destruct (IH q' l' (tstep q' l' As' Ss)) as (Vs' & Hv & Hl).
    { unfold tstep. rewrite length_map. rewrite length_map. reflexivity. }
    exists Vs'. split; auto. eapply lts_step; eauto.
Qed.

(** A weaker head gives a weaker view. *)
Lemma mono_cond : forall L q1 l1 q2 l2,
  q1 <> Bot -> rq_sub q1 q2 ->
  (q2 = Mut -> norm L l1 = norm L l2) ->
  forall As Bs,
    label_cond2 L (tg q1) (tg q2) (tframe q1 l1 As) (tframe q2 l2 Bs).
Proof.
  intros L q1 l1 q2 l2 Hnb Hrq Hl As Bs q0.
  unfold rq_sub in Hrq.
  destruct q1; try congruence;
    destruct Hrq as [Hx | [Hx | [Hx [Hy | Hy]]]]; subst; try discriminate;
    destruct q0;
    cbv [tg tframe lf_q lab_of lf_mut lf_rdm dynq arg_q_sub];
    (split;
     [ solve [left; reflexivity] || solve [right; split; auto]
     | solve [left; reflexivity] || solve [right; left; discriminate]
       || solve [right; right; reflexivity]
       || solve [right; right; exact (Hl eq_refl)] ]).
Qed.

Lemma ltsuper_mono : forall CT q2 l2 D Bs E Ws,
  ltsuper CT q2 l2 D Bs E Ws ->
  forall L q1 l1 Vs,
    (forall As Bs0,
       label_cond2 L (tg q1) (tg q2) (tframe q1 l1 As) (tframe q2 l2 Bs0)) ->
    Forall2 (lagree L) Vs Bs ->
    exists Ws', ltsuper CT q1 l1 D Vs E Ws' /\ Forall2 (lagree L) Ws' Ws.
Proof.
  intros CT q2 l2 D Bs E Ws H.
  induction H as [C As | C As P Ss D Vs0 Hparent Hrest IH];
    intros L q1 l1 Vs Hcond Hle.
  - exists Vs. split; [apply lts_refl | exact Hle].
  - destruct (IH L q1 l1 (tstep q1 l1 Vs Ss) Hcond) as (Ws' & Hv & Hl).
    { unfold tstep. apply map_ldyn_map_qual_agree2; auto; constructor. }
    exists Ws'. split; auto. eapply lts_step; eauto.
Qed.

Lemma lsubt_refl : forall CT L A, lsubt CT L A A.
Proof.
  intros CT L [q0 l C As]. right. refine (conj _ (conj (fun _ => eq_refl) _)).
  - left. reflexivity.
  - exists As. split; [apply lts_refl | apply Forall2_lagree_refl].
Qed.

Lemma lsubt_trans : forall CT L A B C,
  lsubt CT L A B -> lsubt CT L B C -> lsubt CT L A C.
Proof.
  intros CT L [q1 l1 C1 As] [q2 l2 D Bs] [q3 l3 E Cs] H12 H23.
  assert (H23v : exists Ws, ltsuper CT q2 l2 D Bs E Ws /\ length Ws = length Cs).
  { destruct H23 as [(_ & Ws & Hw & Hl) | (_ & _ & Ws & Hw & Hl)].
    - eauto.
    - exists Ws. split; auto. apply (Forall2_length Hl). }
  assert (Hbot : q1 = Bot ->
            forall Vs, ltsuper CT q1 l1 C1 As D Vs -> length Vs = length Bs ->
            lsubt CT L (LT q1 l1 C1 As) (LT q3 l3 E Cs)).
  { intros Hq Vs Hv Hlen. destruct H23v as (Ws & Hw & Hl).
    destruct (ltsuper_len _ _ _ _ _ _ _ Hw q1 l1 Vs Hlen) as (Ws' & Hw' & Hl').
    left. split; auto. exists Ws'. split.
    - eapply ltsuper_trans; eauto.
    - congruence. }
  destruct H12 as [(Hq & Vs & Hv & Hlen) | (Hrq & Hlab & Vs & Hv & Hle)].
  - eapply Hbot; eauto.
  - destruct (q_eq_dec q1 Bot) as [Hq | Hnb].
    + eapply Hbot; eauto. apply (Forall2_length Hle).
    + destruct H23 as [(Hq2 & _) | (Hrq2 & Hlab2 & Ws & Hw & Hle2)].
      * exfalso. subst q2. unfold rq_sub in Hrq.
        destruct Hrq as [Hx | [Hx | [Hx _]]]; congruence.
      * right. refine (conj (rq_sub_trans _ _ _ Hrq Hrq2) (conj _ _)).
        -- intros Hm. rewrite <- (Hlab2 Hm). apply Hlab.
           subst q3. unfold rq_sub in Hrq2.
           destruct Hrq2 as [Hx | [Hx | [Hx _]]]; congruence.
        -- destruct (ltsuper_mono _ _ _ _ _ _ _ Hw L q1 l1 Vs
                       (mono_cond L q1 l1 q2 l2 Hnb Hrq Hlab) Hle)
             as (Ws' & Hw' & Hle').
           exists Ws'. split.
           ++ eapply ltsuper_trans; eauto.
           ++ eapply Forall2_lagree_trans; eauto.
Qed.

(* ------------------STATIC SUBTYPING GIVES LABELLED SUBTYPING------------------*)

(** The view of a labelled reading against the reading of the static view,
    in a protected mode. *)
Lemma hier_cond : forall L mt F q1 As cs ms ks,
  readonly_state_method_scope mt ->
  (lf_q F = Mut \/ lf_q F = Imm) ->
  label_cond2 L (tg (dynq (lf_q F) q1)) (vpa_q mt q1)
    (tframe (dynq (lf_q F) q1) (lab_of F q1) As) (lf_with_args F cs ms ks).
Proof.
  intros L mt [qF lm lr c0 m0 k0] q1 As cs ms ks Hrs Hq q0. simpl in Hq.
  destruct Hrs as [-> | ->]; destruct Hq as [-> | ->]; destruct q1, q0;
    cbv [tg tframe lf_with_args lf_q lab_of lf_mut lf_rdm dynq arg_q_sub vpa_q
         vpa_mutability_qq_readonly_state];
    (split;
     [ solve [left; reflexivity] || solve [right; split; auto]
     | solve [left; reflexivity] || solve [right; left; discriminate]
       || solve [right; right; reflexivity] ]).
Qed.

Lemma type_vs_static_view : forall CT mt qh C Ts D Vs,
  super_inst CT mt qh C Ts D Vs ->
  forall L F As,
    readonly_state_method_scope mt ->
    (lf_q F = Mut \/ lf_q F = Imm) ->
    Forall2 (lagree L) As (map (ldyn F) Ts) ->
    exists Vs', ltsuper CT (dynq (lf_q F) qh) (lab_of F qh) C As D Vs' /\
                Forall2 (lagree L) Vs' (map (ldyn F) Vs).
Proof.
  intros CT mt qh C Ts D Vs H.
  induction H; intros L F As Hrs Hq Hargs.
  - exists As. split; [apply lts_refl | exact Hargs].
  - destruct (IHsuper_inst L F
                (tstep (dynq (lf_q F) qh) (lab_of F qh) As Ss) Hrs Hq)
      as (Vs' & Hv & Hle).
    { assert (Heq : map (ldyn F) (map (subst Ts [] []) (map (adapt mt qh) Ss)) =
                    map (fun S => ldyn (lf_with_args F (map (ldyn F) Ts) [] [])
                                    (map_qual (vpa_q mt qh) S)) Ss).
      { clear. induction Ss as [|S Ss IH]; simpl; auto.
        f_equal; auto. rewrite ldyn_subst. reflexivity. }
      rewrite Heq. unfold tstep.
      apply map_ldyn_map_qual_agree2.
      - apply hier_cond; auto.
      - exact Hargs.
      - constructor.
      - reflexivity. }
    exists Vs'. split; auto. eapply lts_step; eauto.
Qed.

(** The same for any head whose reading of a superclass declaration is no
    more precise than the static reading. *)
Lemma type_vs_static_view_g : forall CT mt qh C Ts D Vs,
  super_inst CT mt qh C Ts D Vs ->
  forall L F qa la As,
    (forall As0 cs ms ks,
       label_cond2 L (tg qa) (vpa_q mt qh)
         (tframe qa la As0) (lf_with_args F cs ms ks)) ->
    Forall2 (lagree L) As (map (ldyn F) Ts) ->
    exists Vs', ltsuper CT qa la C As D Vs' /\
                Forall2 (lagree L) Vs' (map (ldyn F) Vs).
Proof.
  intros CT mt qh C Ts D Vs H.
  induction H; intros L F qa la As Hcond Hargs.
  - exists As. split; [apply lts_refl | exact Hargs].
  - destruct (IHsuper_inst L F qa la (tstep qa la As Ss) Hcond)
      as (Vs' & Hv & Hle).
    { assert (Heq : map (ldyn F) (map (subst Ts [] []) (map (adapt mt qh) Ss)) =
                    map (fun S => ldyn (lf_with_args F (map (ldyn F) Ts) [] [])
                                    (map_qual (vpa_q mt qh) S)) Ss).
      { clear. induction Ss as [|S Ss IH]; simpl; auto.
        f_equal; auto. rewrite ldyn_subst. reflexivity. }
      rewrite Heq. unfold tstep.
      apply map_ldyn_map_qual_agree2.
      - apply Hcond.
      - exact Hargs.
      - constructor.
      - reflexivity. }
    exists Vs'. split; auto. eapply lts_step; eauto.
Qed.

(** A head that is not the bottom qualifier reads a superclass declaration
    no more precisely than the readonly view does. *)
Lemma head_ro_cond : forall L mt F qa la As cs ms ks,
  readonly_state_method_scope mt ->
  (lf_q F = Mut \/ lf_q F = Imm) ->
  qa <> Bot ->
  label_cond2 L (tg qa) (vpa_q mt RO) (tframe qa la As) (lf_with_args F cs ms ks).
Proof.
  intros L mt [qF lm lr c0 m0 k0] qa la As cs ms ks Hrs Hq Hnb q0. simpl in Hq.
  destruct Hrs as [-> | ->]; destruct Hq as [-> | ->]; destruct qa, q0;
    try congruence;
    cbv [tg tframe lf_with_args lf_q lab_of lf_mut lf_rdm dynq arg_q_sub vpa_q
         vpa_mutability_qq_readonly_state];
    (split;
     [ solve [left; reflexivity] || solve [right; split; auto]
     | solve [left; reflexivity] || solve [right; left; discriminate]
       || solve [right; right; reflexivity] ]).
Qed.

(** Every type variable's supplied type is a labelled subtype of the reading
    of its bound. *)
Definition frame_fits (CT : class_table) (L : list nat) (Δ : tv_env)
    (F : lframe) : Prop :=
  forall o n B, tv_bound Δ o n = Some B ->
    lsubt CT L (ldyn F (TVar TVSub o n)) (ldyn F B).

Lemma sub_lsubt : forall CT Δ L F,
  readonly_state_method_scope (tv_mode Δ) ->
  (lf_q F = Mut \/ lf_q F = Imm) ->
  frame_fits CT L Δ F ->
  forall T U, qualified_type_subtype CT Δ T U ->
    lsubt CT L (ldyn F T) (ldyn F U).
Proof.
  intros CT Δ L F Hrs Hq Hfit T U Hsub.
  induction Hsub.
  - (* same class *)
    cbn [ldyn].
    assert (Hv : ltsuper CT (dynq (lf_q F) q1) (lab_of F q1) C (map (ldyn F) Ts)
                   C (map (ldyn F) Ts)) by apply lts_refl.
    assert (Hle : Forall2 (lagree L) (map (ldyn F) Ts) (map (ldyn F) Us))
      by (apply map_ldyn_targ_sub; auto).
    inversion Hqsub; subst.
    + right. refine (conj _ (conj (fun _ => eq_refl) _)); [left; reflexivity|].
      eauto.
    + right. refine (conj _ (conj _ _)).
      * right. left. reflexivity.
      * intros Hm. discriminate.
      * eauto.
    + left. split; [reflexivity|]. eexists. split; [exact Hv|].
      apply (Forall2_length Hle).
  - (* up the hierarchy *)
    cbn [ldyn]. right. refine (conj _ (conj (fun _ => eq_refl) _)).
    + left. reflexivity.
    + apply (type_vs_static_view _ _ _ _ _ _ _ Hsuper L F _ Hrs Hq).
      apply Forall2_lagree_refl.
  - apply lsubt_refl.
  - exact (Hfit _ _ _ Hbound).
  - (* widen the written qualifier of a variable use *)
    cbn [ldyn].
    destruct (match tv_lookup o (lf_cargs F) (lf_margs F) n with
              | Some A => A | None => ldefault end) as [qa la Ca Aa].
    simpl lrehead.
    inversion Hqsub; subst.
    + apply lsubt_refl.
    + right. refine (conj _ (conj _ _)).
      * right. left. reflexivity.
      * intros Hm. discriminate.
      * exists Aa. split; [apply lts_refl | apply Forall2_lagree_refl].
    + left. split; [reflexivity|]. exists Aa. split; [apply lts_refl | reflexivity].
  - (* view the supplied type as readonly *)
    cbn [ldyn].
    destruct (match tv_lookup o (lf_cargs F) (lf_margs F) n with
              | Some A => A | None => ldefault end) as [qa la Ca Aa].
    simpl lrehead. right. refine (conj _ (conj _ _)).
    + right. left. reflexivity.
    + intros Hm. discriminate.
    + exists Aa. split; [apply lts_refl | apply Forall2_lagree_refl].
  - apply lsubt_refl.
  - (* a use under a qualifier parameter, viewed as readonly *)
    cbn [ldyn].
    destruct (match tv_lookup o (lf_cargs F) (lf_margs F) n with
              | Some A => A | None => ldefault end) as [qa la Ca Aa].
    simpl lrehead. right. refine (conj _ (conj _ _)).
    + right. left. reflexivity.
    + intros Hm. discriminate.
    + exists Aa. split; [apply lts_refl | apply Forall2_lagree_refl].
  - (* a qualified variable use at an argument-free bound *)
    cbn [ldyn] in *.
    destruct (match tv_lookup o (lf_cargs F) (lf_margs F) n with
              | Some A => A | None => ldefault end) as [qa la Ca Aa].
    simpl lrehead. simpl map in IHHsub.
    assert (Hv : exists Vs, ltsuper CT qa la Ca Aa C Vs /\ length Vs = 0).
    { destruct IHHsub as [(_ & Vs & Hv & Hl) | (_ & _ & Vs & Hv & Hl)].
      - eauto.
      - exists Vs. split; auto. apply (Forall2_length Hl). }
    destruct Hv as (Vs & Hv & Hl).
    destruct (ltsuper_len _ _ _ _ _ _ _ Hv (dynq (lf_q F) q1) (lab_of F q1) Aa
                eq_refl) as (Vs' & Hv' & Hl').
    assert (Vs' = []) by (destruct Vs'; simpl in *; [reflexivity | lia]).
    subst Vs'.
    right. refine (conj _ (conj (fun _ => eq_refl) _)); [left; reflexivity|].
    exists (@nil ltype). split; [exact Hv' | constructor].
  - (* a variable-headed class type viewed as readonly *)
    cbn [ldyn].
    remember (fst (lqnth (lf_qargs F) n)) as qa eqn:Hqa0.
    remember (snd (lqnth (lf_qargs F) n)) as la eqn:Hla0.
    idtac. right. refine (conj _ (conj _ _)).
    + right. left. reflexivity.
    + intros Hm. discriminate.
    + exists (map (ldyn F) Ts). split; [apply lts_refl|].
      apply map_ldyn_targ_sub; auto.
  - (* compatible arguments under the same variable head *)
    cbn [ldyn].
    remember (fst (lqnth (lf_qargs F) n)) as qa eqn:Hqa0.
    remember (snd (lqnth (lf_qargs F) n)) as la eqn:Hla0.
    idtac. right. refine (conj _ (conj (fun _ => eq_refl) _)).
    + left. reflexivity.
    + exists (map (ldyn F) Ts). split; [apply lts_refl|].
      apply map_ldyn_targ_sub; auto.
  - (* up the hierarchy under the same variable head *)
    cbn [ldyn].
    remember (fst (lqnth (lf_qargs F) n)) as qa eqn:Hqa0.
    remember (snd (lqnth (lf_qargs F) n)) as la eqn:Hla0.
    idtac.
    destruct (q_eq_dec qa Bot) as [-> | Hnb].
    + left. split; [reflexivity|].
      destruct (type_vs_static_view _ _ _ _ _ _ _ Hsuper L F (map (ldyn F) Ts)
                  Hrs Hq (Forall2_lagree_refl _ _)) as (Vs' & Hv & Hle).
      destruct (ltsuper_len _ _ _ _ _ _ _ Hv Bot la (map (ldyn F) Ts) eq_refl)
        as (Vs'' & Hv'' & Hl'').
      exists Vs''. split; auto. rewrite Hl''. apply (Forall2_length Hle).
    + right. refine (conj _ (conj (fun _ => eq_refl) _)); [left; reflexivity|].
      apply (type_vs_static_view_g _ _ _ _ _ _ _ Hsuper L F qa la).
      * intros As0 cs ms ks. apply head_ro_cond; auto.
      * apply Forall2_lagree_refl.
  - (* the bottom-qualified type of the class *)
    cbn [ldyn].
    remember (fst (lqnth (lf_qargs F) n)) as qa eqn:Hqa0.
    remember (snd (lqnth (lf_qargs F) n)) as la eqn:Hla0.
    idtac. left. split; [reflexivity|].
    exists (map (ldyn F) Ts). split; [apply lts_refl|].
    rewrite !length_map. apply (Forall2_length Hargs).
  - eapply lsubt_trans; eauto.
Qed.

(* ------------------USING THE FIT------------------*)

(** Bounds in scope are class types with no [Mut] anywhere. *)
Definition nomut_bounds (Δ : tv_env) : Prop :=
  forall o n B, tv_bound Δ o n = Some B -> is_class_type B /\ no_mut Δ B.

Lemma nomut_bounds_head : forall Δ o n B,
  nomut_bounds Δ -> tv_bound Δ o n = Some B -> whead B <> Some Mut.
Proof.
  intros Δ o n B H Hb Hw. destruct (H _ _ _ Hb) as [Hc Hn].
  destruct B as [q0 C Ts| |]; [|contradiction..].
  simpl in Hw. inversion Hw; subst. inversion Hn; congruence.
Qed.

(** A type variable used at its bound, from the fit. *)
Lemma vb_of_fits : forall P CT Δ h G L next F ca ma ka qthis,
  heapL P CT h G L next ->
  mutcL CT h G ->
  frame_fits CT L Δ F ->
  lf_q F = qr2q qthis ->
  map erase (lf_cargs F) = ca -> map erase (lf_margs F) = ma -> map fst (lf_qargs F) = ka ->
  forall o n B v,
    tv_bound Δ o n = Some B ->
    wf_r_typable CT h v (TVar TVSub o n) qthis ca ma ka ->
    lhas CT h G L v (ldyn F (TVar TVSub o n)) ->
    lhas CT h G L v (ldyn F B).
Proof.
  intros P CT Δ h G L next F ca ma ka qthis HG HM Hfit Hq Hec Hem Hek o n B v Hb Hty Hl.
  eapply lsubt_sound; eauto.
  rewrite erase_ldyn. rewrite Hq. rewrite Hec. rewrite Hem. try rewrite Hek. exact Hty.
Qed.

(** A labelled supertype may be replaced by one it agrees into. *)
Lemma lsubt_agree_r : forall CT L A B B',
  lsubt CT L A B -> lagree L B B' -> lsubt CT L A B'.
Proof.
  intros CT L [q1 l1 C As] [q2 l2 D Bs] [q2' l2' D' Bs'] Hs Ha.
  inversion Ha as [? ? ? ? ? ? ? Hq Hlab Hargs]; subst.
  destruct Hs as [(Hb & Vs & Hv & Hlen) | (Hrq & Hl & Vs & Hv & Hle)].
  - left. split; auto. exists Vs. split; auto.
    rewrite Hlen. apply (Forall2_length Hargs).
  - right. refine (conj _ (conj _ _)).
    + unfold rq_sub in *. unfold arg_q_sub in Hq. clear - Hrq Hq.
      destruct q1, q2, q2'; intuition congruence.
    + intros Hm. subst q2'.
      unfold arg_q_sub in Hq. destruct Hq as [Hx | [Hx _]]; [|discriminate].
      subst q2. rewrite (Hl eq_refl).
      destruct Hlab as [Hx | [Hx | Hx]]; congruence.
    + exists Vs. split; auto. eapply Forall2_lagree_trans; eauto.
Qed.

(* ------------------WORLDS OPENING AND CLOSING------------------*)

Lemma lagree_pop_list : forall L w0 As Bs,
  Forall2 (lagree (w0 :: L)) As Bs -> Forall2 (lagree L) As Bs.
Proof.
  intros L w0 As Bs H. induction H; constructor; eauto using lagree_pop.
Qed.

Lemma lsubt_pop : forall CT L w0 A B,
  lsubt CT (w0 :: L) A B -> lsubt CT L A B.
Proof.
  intros CT L w0 [q1 l1 C As] [q2 l2 D Bs] H.
  destruct H as [H | (Hrq & Hl & Vs & Hv & Hle)]; [left; exact H|].
  right. refine (conj Hrq (conj _ _)).
  - intros Hm. eapply norm_pop. exact (Hl Hm).
  - exists Vs. split; auto. eapply lagree_pop_list; eauto.
Qed.

Lemma ltsuper_lbound : forall CT q0 l0 C As D Vs n,
  ltsuper CT q0 l0 C As D Vs ->
  lab_bound n l0 -> Forall (lbound n) As -> Forall (lbound n) Vs.
Proof.
  intros CT q0 l0 C As D Vs n H Hl.
  induction H as [C As | C As P Ss D Vs Hparent Hrest IH]; intros HAs; auto.
  apply IH. unfold tstep.
  apply Forall_forall. intros A HA. apply in_map_iff in HA.
  destruct HA as (S & <- & _). apply ldyn_lbound.
  unfold frame_bound, tframe. simpl. auto.
Qed.

Lemma lsubt_push : forall CT L n A B,
  lsubt CT L A B -> lbound n A -> lbound n B -> lsubt CT (n :: L) A B.
Proof.
  intros CT L n [q1 l1 C As] [q2 l2 D Bs] H HA HB.
  apply lbound_node in HA. destruct HA as [Hl1 HAs].
  apply lbound_node in HB. destruct HB as [Hl2 HBs].
  destruct H as [H | (Hrq & Hl & Vs & Hv & Hle)]; [left; exact H|].
  right. refine (conj Hrq (conj _ _)).
  - intros Hm. rewrite (norm_push L n l1 Hl1). rewrite (norm_push L n l2 Hl2).
    exact (Hl Hm).
  - exists Vs. split; auto.
    pose proof (ltsuper_lbound _ _ _ _ _ _ _ n Hv Hl1 HAs) as HVs.
    clear - Hle HVs HBs. induction Hle; constructor;
      inversion HVs; inversion HBs; subst; auto using lagree_push.
Qed.

(* ------------------TYPES WITH NO MUT------------------*)

Lemma no_mut_map_qual_eq : forall Δ T f g,
  no_mut Δ T -> (forall q0, q0 <> Mut -> f q0 = g q0) ->
  map_qual f T = map_qual g T.
Proof.
  intros Δ T f g. induction T using qualified_type_ind'; intros Hnm Hfg.
  - inversion Hnm; subst. simpl. f_equal; [apply Hfg; auto|].
    clear Hnm Hq. induction H; simpl; auto.
    inversion Hargs; subst. f_equal; auto.
  - inversion Hnm; subst; simpl; auto. rewrite Hfg; auto.
  - inversion Hnm; subst. simpl. f_equal.
    clear Hnm. induction H; simpl; auto.
    inversion Hargs; subst. f_equal; auto.
Qed.

(** A qualifier map with the image of [Mut] forgotten; on a type that writes
    no [Mut] it is the same map. *)
Definition unm (f : q -> q) (q0 : q) : q :=
  match q0 with Mut => Lost | _ => f q0 end.

Lemma no_mut_unm : forall Δ T f,
  no_mut Δ T -> map_qual f T = map_qual (unm f) T.
Proof.
  intros Δ T f H. apply (no_mut_map_qual_eq Δ T f (unm f) H).
  intros q0 Hq. destruct q0; simpl; congruence.
Qed.
