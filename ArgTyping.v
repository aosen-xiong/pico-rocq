From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels ArgViews GhostTyping
  GhostFit.

(** Values and labelled subtyping over payload views.

    A value has a labelled type when its colour agrees with a mutable head and
    its own view at the type's class agrees with the type's arguments.  No
    world of creation is recorded for an object: what a mutable position in a
    class header means is read off the object's arguments. *)

(* ------------------VALUES------------------*)

(** The escape: the type's head is not a live mutable claim. *)
Definition dead (L : list nat) (q0 : q) (l : lab) : Prop :=
  q0 = Mut -> norm L l <> None -> False.

(** The object at [v] inhabits a labelled type: its colour agrees with the
    head, and the type's arguments agree, node by node, with the object's
    payload view at the type's class or, where the head is not a live mutable
    claim, with its plain view. *)
Definition lhasp (CT : class_table) (h : heap) (G : ghost) (L : list nat)
    (v : Loc) (A : ltype) : Prop :=
  exists o, runtime_getObj h v = Some o /\
    match A with
    | LT q0 l D Us =>
        headL L (g_col G v) q0 l /\
        exists Vr Vp,
          oview CT (rqtype (rt_type o)) (olab (g_col G v))
            (rctype (rt_type o)) (g_args G v) D Vr /\
          oplain CT (rqtype (rt_type o)) (olab (g_col G v))
            (rctype (rt_type o)) (g_args G v) D Vp /\
          Forall3 (xagree L (dead L q0 l)) Vr Vp Us
    end.

Lemma dead_agree : forall L q1 l1 q2 l2,
  arg_q_sub q1 q2 -> (q2 = Lost \/ q1 <> Mut \/ norm L l1 = norm L l2) ->
  dead L q1 l1 -> dead L q2 l2.
Proof.
  intros L q1 l1 q2 l2 Hq Hlab Hd Hm Hn. subst q2.
  unfold arg_q_sub in Hq. destruct Hq as [Hx | [Hx _]]; [|congruence]. subst q1.
  destruct Hlab as [Hx | [Hx | Hx]]; [congruence | congruence |].
  apply (Hd eq_refl). rewrite Hx. exact Hn.
Qed.

Lemma lhasp_agree : forall CT h G L v A B,
  lhasp CT h G L v A -> lagree L A B -> lhasp CT h G L v B.

(** Place in the proof: values and labelled subtyping over payload views.  A
    labelled type against a static view, where the payload is from a fit,
    classes that have no objects, world identifiers in views, soundness of the
    payload-view fit, what a typing derivation gives, and a qualified use of a
    type variable at its bound's class.
    Counterpart in the non-generic proof (ReadonlyWorlds.v): "what a static
    head says about a value" and the Frame section, over payload views. *)
Proof.
  intros CT h G L v [q1 l1 C As] [q2 l2 D Bs]
    (o & Ho & Hh & Vr & Vp & Hvr & Hvp & Hle) Ha.
  inversion Ha as [? ? ? ? ? ? ? Hq Hlab Hargs]; subst.
  assert (Hqm : q2 = Mut -> q1 = Mut).
  { intros ->. unfold arg_q_sub in Hq. destruct Hq as [Hx | [Hx _]]; congruence. }
  exists o. split; auto. split.
  - unfold headL in *. intros Hm. pose proof (Hqm Hm). subst q1 q2.
    specialize (Hh eq_refl).
    destruct Hlab as [Hx | [Hx | Hx]]; try congruence.
    rewrite <- Hx. exact Hh.
  - exists Vr, Vp. split; auto. split; auto.
    eapply Forall3_xagree_trans_r; [|exact Hargs].
    eapply Forall3_xagree_mono; [|exact Hle].
    intros Hd. eapply dead_agree; eauto.
Qed.

(* ------------------LABELLED SUBTYPING------------------*)

(** Subtyping between labelled types, through the payload view. *)
Definition lsubtp (CT : class_table) (L : list nat) (A B : ltype) : Prop :=
  match A, B with
  | LT q1 l1 C As, LT q2 l2 D Bs =>
      (q1 = Bot /\
       exists Vs, tview CT q1 l1 C As D Vs /\ length Vs = length Bs) \/
      (rq_sub q1 q2 /\
       (q2 = Mut -> norm L l1 = norm L l2) /\
       exists Vs, tview CT q1 l1 C As D Vs /\ Forall2 (lagree L) Vs Bs)
  end.

(* ------------------A LABELLED TYPE AGAINST A STATIC VIEW------------------*)

(** The payloads along the views of a labelled type agree with one label.
    Asked only of types read from a type written mutable, where the
    protected-mode view keeps written mutable positions mutable. *)
Definition pcoh (CT : class_table) (L : list nat) (q0 : q) (l : lab)
    (C : class_name) (As : list ltype) (lm : lab) : Prop :=
  forall C' As', tview CT q0 l C As C' As' ->
    match pclassf CT C' As' with
    | Some (Lost, _) => False
    | Some (Mut, l') => norm L l' = norm L lm
    | _ => True
    end.

Lemma pcoh_step : forall CT L q0 l C As lm P Ss,
  pcoh CT L q0 l C As lm ->
  parent_lookup CT C = Some (P, Ss) ->
  pcoh CT L q0 l P (hstep true q0 (ArgViews.tg q0) l None As Ss) lm.
Proof.
  intros CT L q0 l C As lm P Ss H Hparent C' As' Hv.
  apply H. unfold tview in *. eapply v_step; eauto.
Qed.

(** One step: the type's reading of a header, with its payload, against the
    reading of the protected-mode view in a frame. *)
Lemma tstatic_step_cond : forall L mt F q0 l qh pn As cs ms ks,
  readonly_state_method_scope mt ->
  (forall As0,
     label_cond2 L (ArgViews.tg q0) (vpa_q mt qh)
       (mk_lframe q0 l l As0 [] []) (lf_with_args F cs ms ks)) ->
  (qh = Mut ->
   match pn with
   | Some (Lost, _) => False
   | Some (Mut, l') => norm L l' = norm L (lf_mut F)
   | _ => True
   end) ->
  lc2 L (rd_map true (ArgViews.tg q0) pn) (vpa_q mt qh)
    (hframe q0 l pn As) (lf_with_args F cs ms ks).
Proof.
  intros L mt F q0 l qh pn As cs ms ks Hrs Hbase Hpay q1.
  destruct (Hbase As q1) as [H1 H2]. cbn [hframe lf_q lf_with_args] in H1, H2 |- *.
  destruct (q_eq_dec q1 Mut) as [-> | Hne].
  - destruct (q_eq_dec qh Mut) as [-> | Hqh].
    + (* the static view keeps the written mutable position *)
      specialize (Hpay eq_refl).
      assert (Hst : vpa_q mt Mut Mut = Mut)
        by (destruct Hrs as [-> | ->]; reflexivity).
      rewrite Hst in H1, H2 |- *. simpl dynq in H1, H2 |- *.
      destruct pn as [[qp lp]|].
      * destruct (q_eq_dec qp Lost) as [-> | Hnl]; [contradiction|].
        rewrite (rd_map_keep true (ArgViews.tg q0) qp lp Hnl).
        split; [exact H1|].
        destruct H2 as [H2 | [H2 | H2]]; auto.
        destruct (q_eq_dec (dynq q0 (ArgViews.tg q0 Mut)) Mut) as [Hs | Hs]; [|auto].
        right. right.
        assert (Htg : ArgViews.tg q0 Mut = Mut)
          by (destruct q0; simpl in Hs |- *; congruence).
        rewrite Htg in H1, H2 |- *. cbn [lab_of lf_mut lf_with_args] in H2 |- *.
        destruct (q_eq_dec qp Mut) as [-> | Hqp].
        -- unfold hframe. cbn [lf_mut rd_lab]. exact Hpay.
        -- unfold hframe. cbn [lf_mut]. rewrite (rd_lab_other l qp lp Hqp). exact H2.
      * simpl rd_map. split; [exact H1|]. exact H2.
    + (* the static view leaves it open *)
      assert (Hst : vpa_q mt qh Mut = Lost)
        by (destruct Hrs as [-> | ->]; destruct qh; simpl; congruence).
      rewrite Hst. change (dynq (lf_q F) Lost) with Lost.
      split; [|left; reflexivity].
      assert (Hsrc : dynq q0 (rd_map true (ArgViews.tg q0) pn Mut) = Mut \/
                     dynq q0 (rd_map true (ArgViews.tg q0) pn Mut) = Lost).
      { destruct pn as [[[] lp]|]; destruct q0; simpl; auto. }
      destruct Hsrc as [E | E]; rewrite E; unfold arg_q_sub; auto.
  - rewrite (rd_map_other true (ArgViews.tg q0) pn q1 Hne).
    split; [exact H1|].
    destruct H2 as [H2 | [H2 | H2]]; auto.
    right. right.
    assert (Hlab : lab_of (mk_lframe q0 (rd_lab l pn) l As [] []) (ArgViews.tg q0 q1) =
                   lab_of (mk_lframe q0 l l As [] []) (ArgViews.tg q0 q1)).
    { destruct q1, q0; simpl; try reflexivity; congruence. }
    rewrite Hlab. exact H2.
Qed.

(** The payload view of a labelled type against the reading of a static
    protected-mode view. *)
Lemma tview_vs_static : forall CT mt qh C Ts D Vs,
  super_inst CT mt qh C Ts D Vs ->
  forall L F q0 l As,
    readonly_state_method_scope mt ->
    (forall As0 cs ms ks,
       label_cond2 L (ArgViews.tg q0) (vpa_q mt qh)
         (mk_lframe q0 l l As0 [] []) (lf_with_args F cs ms ks)) ->
    (qh = Mut -> pcoh CT L q0 l C As (lf_mut F)) ->
    Forall2 (lagree L) As (map (ldyn F) Ts) ->
    exists Vs', tview CT q0 l C As D Vs' /\
                Forall2 (lagree L) Vs' (map (ldyn F) Vs).
Proof.
  intros CT mt qh C Ts D Vs H.
  induction H; intros L F q0 l As Hrs Hbase Hpc Hargs.
  - exists As. split; [apply v_refl | exact Hargs].
  - destruct (IHsuper_inst L F q0 l
                (hstep true q0 (ArgViews.tg q0) l None As Ss)
                Hrs Hbase) as (Vs' & Hv & Hle).
    { intros Hqh. exact (pcoh_step _ _ _ _ _ _ _ _ _ (Hpc Hqh) Hparent). }
    { assert (Heq : map (ldyn F) (map (subst Ts [] []) (map (adapt mt qh) Ss)) =
                    map (fun S => ldyn (lf_with_args F (map (ldyn F) Ts) [] [])
                                    (map_qual (vpa_q mt qh) S)) Ss).
      { clear. induction Ss as [|S Ss IH]; simpl; auto.
        f_equal; auto. rewrite ldyn_subst. reflexivity. }
      rewrite Heq. unfold hstep.
      clear IHsuper_inst H Heq. generalize Ss as Ss0.
      induction Ss0 as [|S Ss0 IH]; simpl; [constructor|].
      constructor; [|exact IH].
      apply ldyn_agree2.
      - apply (tstatic_step_cond L mt F q0 l qh None As
                 (map (ldyn F) Ts) [] _ Hrs).
        + intros As0. apply Hbase.
        + intros _. exact I.
      - exact Hargs.
      - constructor.
      - reflexivity. }
    exists Vs'. split; auto. unfold tview. eapply v_step; eauto.
Qed.

(* ------------------WHERE THE PAYLOAD IS, FROM A FIT------------------*)

Lemma tg_same : GhostFit.tg = ArgViews.tg.
Proof. reflexivity. Qed.

Lemma tstep_hstep : forall q0 l As Ss,
  tstep q0 l As Ss = hstep true q0 (ArgViews.tg q0) l None As Ss.
Proof. reflexivity. Qed.

Lemma ltsuper_le : forall CT q0 l C As D Vs,
  wf_class_table CT -> ltsuper CT q0 l C As D Vs -> D <= C.
Proof.
  intros CT q0 l C As D Vs Hwf H. induction H; auto.
  pose proof (parent_lt _ _ _ _ Hwf Hparent). lia.
Qed.

Lemma tviewf_mono : forall CT n q0 l C As D Vs,
  tviewf CT n q0 l C As D = Some Vs ->
  forall m, n <= m -> tviewf CT m q0 l C As D = Some Vs.
Proof.
  intros CT n. induction n as [|n IH]; intros q0 l C As D Vs H m Hle;
    [discriminate|].
  destruct m as [|m]; [lia|]. simpl in *.
  destruct (Nat.eqb C D); auto.
  destruct (parent_lookup CT C) as [[P Ss]|]; [|discriminate].
  apply IH; auto. lia.
Qed.

(** The head view, as a function, is the head view of the earlier layer. *)
Lemma tviewf_of_ltsuper : forall CT q0 l C As D Vs,
  wf_class_table CT ->
  ltsuper CT q0 l C As D Vs ->
  tviewf CT (S C) q0 l C As D = Some Vs.
Proof.
  intros CT q0 l C As D Vs Hwf H. induction H.
  - simpl. rewrite Nat.eqb_refl. reflexivity.
  - pose proof (parent_lt _ _ _ _ Hwf Hparent) as Hlt.
    pose proof (ltsuper_le _ _ _ _ _ _ _ Hwf H) as Hle.
    simpl. assert (Hne : Nat.eqb C D = false) by (apply Nat.eqb_neq; lia).
    rewrite Hne. rewrite Hparent. rewrite <- tstep_hstep.
    apply (tviewf_mono CT (S P)); [exact IHltsuper | lia].
Qed.

(* ------------------THE BOTTOM READER OF THE EARLIER LAYER------------------*)

Lemma tgb_bq : forall q0, ArgViews.tgb q0 = bq q0.
Proof. intros []; reflexivity. Qed.

Lemma lab_of_bq : forall l l' As q0, lab_of (mk_lframe Bot l l' As [] []) (bq q0) = LOut.
Proof. intros l l' As []; reflexivity. Qed.

Lemma ldyn_bframe_lab : forall l l' As S,
  ldyn (mk_lframe Bot l l' As [] []) (map_qual ArgViews.tgb S) =
  ldyn (bframe As) (map_qual bq S).
Proof.
  intros l l' As S. induction S using qualified_type_ind'.
  - cbn [map_qual ldyn]. rewrite tgb_bq. rewrite lab_of_bq.
    unfold bframe. rewrite lab_of_bq. f_equal.
    rewrite !map_map. induction H; simpl; f_equal; auto.
  - destruct u as [|q0|m]; cbn [map_qual ldyn bframe lf_cargs lf_margs lf_qargs lf_q];
      [reflexivity | | reflexivity].
    rewrite tgb_bq. rewrite lab_of_bq. unfold bframe. rewrite lab_of_bq. reflexivity.
  - cbn [map_qual ldyn bframe lf_qargs]. f_equal.
    rewrite !map_map. induction H; simpl; f_equal; auto.
Qed.

Lemma hstep_bstep : forall l As Ss,
  hstep true Bot ArgViews.tgb l None As Ss = bstep As Ss.
Proof.
  intros l As Ss. unfold hstep, bstep. apply map_ext. intros S.
  change (rd_map true ArgViews.tgb None) with ArgViews.tgb.
  unfold hframe. cbn [rd_lab]. apply ldyn_bframe_lab.
Qed.

Lemma lbsuper_le : forall CT C As D Vs,
  wf_class_table CT -> lbsuper CT C As D Vs -> D <= C.
Proof.
  intros CT C As D Vs Hwf H. induction H; auto.
  pose proof (parent_lt _ _ _ _ Hwf Hparent). lia.
Qed.

Lemma tviewg_mono_b : forall CT n l C As D Vs,
  tviewg CT n Bot ArgViews.tgb l C As D = Some Vs ->
  forall m, n <= m -> tviewg CT m Bot ArgViews.tgb l C As D = Some Vs.
Proof.
  intros CT n. induction n as [|n IH]; intros l C As D Vs H m Hle;
    [discriminate|].
  destruct m as [|m]; [lia|]. simpl in *.
  destruct (Nat.eqb C D); auto.
  destruct (parent_lookup CT C) as [[P Ss]|]; [|discriminate].
  apply IH; auto. lia.
Qed.

(** The bottom reader's view, as a function, is the bottom reader's view of
    the earlier layer. *)
Lemma tviewg_of_lbsuper : forall CT C As D Vs,
  wf_class_table CT ->
  lbsuper CT C As D Vs ->
  forall l, tviewg CT (S C) Bot ArgViews.tgb l C As D = Some Vs.
Proof.
  intros CT C As D Vs Hwf H. induction H; intros l.
  - simpl. rewrite Nat.eqb_refl. reflexivity.
  - pose proof (parent_lt _ _ _ _ Hwf Hparent) as Hlt.
    pose proof (lbsuper_le _ _ _ _ _ Hwf H) as Hle.
    simpl. assert (Hne : Nat.eqb C D = false) by (apply Nat.eqb_neq; lia).
    rewrite Hne. rewrite Hparent. rewrite hstep_bstep.
    apply (tviewg_mono_b CT (S P)); [exact (IHlbsuper l) | lia].
Qed.

(** An argument that agrees into the reading of a bound, with the bottom
    escape, holds at the bound's first written mutable position a mutable
    node of the reading frame's world: a bottom node is never reported, and
    the search descends into it as into any class position. *)
Lemma bwalk_agree : forall CT L F f B V q0 l,
  f Mut = Mut ->
  bagree L V (ldyn F (map_qual f B)) ->
  pwalk CT B V = Some (q0, l) ->
  q0 = Mut /\ norm L l = norm L (lf_mut F).
Proof.
  intros CT L F f B. induction B using qualified_type_ind';
    intros V q0 l Hf Hle Hp.
  - destruct V as [q1 l1 C0 As0]. cbn [ldyn map_qual] in Hle.
    inversion Hle as [? ? ? ? ? ? ? Hq Hlab Hargs]; subst.
    assert (Hdesc : pwalk CT (TClass qual C args) (LT q1 l1 C As0) =
                    match tviewg CT (S C) q1 (prd q1) l1 C As0 C with
                    | Some Vs => pwalks CT args Vs | None => None end ->
                    q0 = Mut /\ norm L l = norm L (lf_mut F)).
    { intros Hpw. rewrite Hpw in Hp.
      simpl in Hp. rewrite Nat.eqb_refl in Hp.
      clear Hq Hlab Hle Hpw. revert As0 Hargs Hp.
      induction H as [|B Bs HB HBs IH]; intros As0 Hargs Hp;
        simpl in Hp; [discriminate|].
      destruct As0 as [|A0 As0]; [discriminate|].
      simpl in Hargs. inversion Hargs as [|? ? ? ? HA Hrest]; subst.
      destruct (pwalk CT B A0) as [[qx lx]|] eqn:Hx.
      * inversion Hp; subst. eapply HB; eauto.
      * eapply IH; eauto. }
    destruct (q_eq_dec qual Mut) as [-> | Hqb].
    + destruct (q_eq_dec q1 Bot) as [-> | Hb1].
      * apply Hdesc. apply pwalk_class. right. reflexivity.
      * rewrite Hf in Hq, Hlab. simpl in Hq, Hlab.
        assert (q1 = Mut).
        { destruct Hq as [[Hx _] | Hq]; [congruence|].
          unfold arg_q_sub in Hq. destruct Hq as [Hx | [Hx _]]; congruence. }
        subst q1.
        rewrite (pwalk_mut CT C args Mut l1 C As0 Hb1) in Hp. apply pnode_some in Hp.
        destruct Hp as (_ & -> & ->). split; auto.
        destruct Hlab as [Hx | [Hx | Hx]]; congruence.
    + apply Hdesc. apply pwalk_class. left. exact Hqb.
  - destruct V as [q1 l1 C0 As0].
    destruct u as [|qv|mp]; [simpl in Hp; discriminate| |simpl in Hp; discriminate].
    destruct (q_eq_dec qv Mut) as [-> | Hqv];
      [|destruct qv; simpl in Hp; congruence].
    cbn [pwalk] in Hp. apply pnode_some in Hp. destruct Hp as (Hnb & -> & ->).
    cbn [ldyn map_qual] in Hle. rewrite Hf in Hle.
    destruct (match tv_lookup o (lf_cargs F) (lf_margs F) n with
              | Some A => A | None => ldefault end) as [qa la Ca Aa].
    simpl lrehead in Hle.
    inversion Hle as [? ? ? ? ? ? ? Hq Hlab Hargs]; subst.
    assert (q1 = Mut).
    { destruct Hq as [[Hx _] | Hq]; [congruence|].
      unfold arg_q_sub in Hq. destruct Hq as [Hx | [Hx _]]; congruence. }
    subst q1. split; auto.
    destruct Hlab as [Hx | [Hx | Hx]]; congruence.
  - destruct V as [q1 l1 C0 As0]. cbn [ldyn map_qual] in Hle.
    inversion Hle as [? ? ? ? ? ? ? Hq Hlab Hargs]; subst.
    rewrite (pwalk_head CT n C args q1 l1 C As0) in Hp.
    simpl in Hp. rewrite Nat.eqb_refl in Hp.
    clear Hq Hlab Hle. revert As0 Hargs Hp.
    induction H as [|B Bs HB HBs IH]; intros As0 Hargs Hp;
      simpl in Hp; [discriminate|].
    destruct As0 as [|A0 As0]; [discriminate|].
    simpl in Hargs. inversion Hargs as [|? ? ? ? HA Hrest]; subst.
    destruct (pwalk CT B A0) as [[qx lx]|] eqn:Hx.
    + inversion Hp; subst. eapply HB; eauto.
    + eapply IH; eauto.
Qed.

Lemma bwalks_agree : forall CT L F f Bs Vs q0 l,
  f Mut = Mut ->
  Forall2 (bagree L) Vs (map (ldyn F) (map (map_qual f) Bs)) ->
  pwalks CT Bs Vs = Some (q0, l) ->
  q0 = Mut /\ norm L l = norm L (lf_mut F).
Proof.
  intros CT L F f Bs. induction Bs as [|B Bs IH]; intros Vs q0 l Hf Hle Hp;
    simpl in Hp; [discriminate|].
  destruct Vs as [|V Vs]; [discriminate|].
  simpl in Hle. inversion Hle as [|? ? ? ? HV Hrest]; subst.
  destruct (pwalk CT B V) as [[qx lx]|] eqn:Hx.
  - inversion Hp; subst. eapply bwalk_agree; eauto.
  - eapply IH; eauto.
Qed.

(** An argument that agrees into the reading of a bound holds, at the
    bound's first written mutable position, a mutable node of the reading
    frame's world.  The bound may be read through any qualifier map that
    keeps written mutable positions. *)
Lemma walk_agree : forall CT L F f B V q0 l,
  f Mut = Mut ->
  lagree L V (ldyn F (map_qual f B)) ->
  pwalk CT B V = Some (q0, l) ->
  q0 = Mut /\ norm L l = norm L (lf_mut F).
Proof.
  intros CT L F f B. induction B using qualified_type_ind';
    intros V q0 l Hf Hle Hp.
  - destruct V as [q1 l1 C0 As0]. cbn [ldyn map_qual] in Hle.
    inversion Hle as [? ? ? ? ? ? ? Hq Hlab Hargs]; subst.
    destruct (q_eq_dec qual Mut) as [-> | Hqb].
    + rewrite Hf in Hq, Hlab. simpl in Hq, Hlab.
      assert (q1 = Mut).
      { unfold arg_q_sub in Hq. destruct Hq as [Hx | [Hx _]]; congruence. }
      subst q1.
      assert (Hnb : Mut <> Bot) by discriminate.
      rewrite (pwalk_mut CT C args Mut l1 C As0 Hnb) in Hp. apply pnode_some in Hp.
      destruct Hp as (_ & -> & ->). split; auto.
      destruct Hlab as [Hx | [Hx | Hx]]; congruence.
    + rewrite (pwalk_class CT qual C args q1 l1 C As0 (or_introl Hqb)) in Hp.
      simpl in Hp. rewrite Nat.eqb_refl in Hp.
      clear Hq Hlab Hle. revert As0 Hargs Hp.
      induction H as [|B Bs HB HBs IH]; intros As0 Hargs Hp;
        simpl in Hp; [discriminate|].
      destruct As0 as [|A0 As0]; [discriminate|].
      simpl in Hargs. inversion Hargs as [|? ? ? ? HA Hrest]; subst.
      destruct (pwalk CT B A0) as [[qx lx]|] eqn:Hx.
      * inversion Hp; subst. eapply HB; eauto.
      * eapply IH; eauto.
  - destruct V as [q1 l1 C0 As0].
    destruct u as [|qv|mp]; [simpl in Hp; discriminate| |simpl in Hp; discriminate].
    destruct (q_eq_dec qv Mut) as [-> | Hqv];
      [|destruct qv; simpl in Hp; congruence].
    cbn [pwalk] in Hp. apply pnode_some in Hp. destruct Hp as (_ & -> & ->).
    cbn [ldyn map_qual] in Hle. rewrite Hf in Hle.
    destruct (match tv_lookup o (lf_cargs F) (lf_margs F) n with
              | Some A => A | None => ldefault end) as [qa la Ca Aa].
    simpl lrehead in Hle.
    inversion Hle as [? ? ? ? ? ? ? Hq Hlab Hargs]; subst.
    assert (q1 = Mut).
    { unfold arg_q_sub in Hq. destruct Hq as [Hx | [Hx _]]; congruence. }
    subst q1. split; auto.
    destruct Hlab as [Hx | [Hx | Hx]]; congruence.
  - destruct V as [q1 l1 C0 As0]. cbn [ldyn map_qual] in Hle.
    inversion Hle as [? ? ? ? ? ? ? Hq Hlab Hargs]; subst.
    rewrite (pwalk_head CT n C args q1 l1 C As0) in Hp.
    simpl in Hp. rewrite Nat.eqb_refl in Hp.
    clear Hq Hlab Hle. revert As0 Hargs Hp.
    induction H as [|B Bs HB HBs IH]; intros As0 Hargs Hp;
      simpl in Hp; [discriminate|].
    destruct As0 as [|A0 As0]; [discriminate|].
    simpl in Hargs. inversion Hargs as [|? ? ? ? HA Hrest]; subst.
    destruct (pwalk CT B A0) as [[qx lx]|] eqn:Hx.
    + inversion Hp; subst. eapply HB; eauto.
    + eapply IH; eauto.
Qed.

Lemma walks_agree : forall CT L F f Bs Vs q0 l,
  f Mut = Mut ->
  Forall2 (lagree L) Vs (map (ldyn F) (map (map_qual f) Bs)) ->
  pwalks CT Bs Vs = Some (q0, l) ->
  q0 = Mut /\ norm L l = norm L (lf_mut F).
Proof.
  intros CT L F f Bs. induction Bs as [|B Bs IH]; intros Vs q0 l Hf Hle Hp;
    simpl in Hp; [discriminate|].
  destruct Vs as [|V Vs]; [discriminate|].
  simpl in Hle. inversion Hle as [|? ? ? ? HV Hrest]; subst.
  destruct (pwalk CT B V) as [[qx lx]|] eqn:Hx.
  - inversion Hp; subst. eapply walk_agree; eauto.
  - eapply IH; eauto.
Qed.

(** The same from a fit in the head view: an argument below the reading of
    a class-type bound.  A bottom-headed argument fits through the bottom
    reader with the escape, which is what the search walks. *)
Lemma walk_fit : forall CT L F f qb D Bs A q0 l,
  wf_class_table CT ->
  f Mut = Mut ->
  rlost_free (erase A) ->
  lsubt CT L A (ldyn F (map_qual f (TClass qb D Bs))) ->
  pfindf CT (TClass qb D Bs) A = Some (q0, l) ->
  q0 = Mut /\ norm L l = norm L (lf_mut F).
Proof.
  intros CT L F f qb D Bs [q1 l1 C As] q0 l Hwf Hf Hlf Hs Hp.
  destruct (q_eq_dec q1 Bot) as [-> | Hq1].
  { cbn [ldyn map_qual] in Hs.
    destruct (lsubt_lb _ _ _ _ _ _ _ _ _ _ Hs) as (Vs & Hv & Hle).
    cbn [pfindf popen] in Hp.
    rewrite (pwalk_class CT qb D Bs Bot l1 C As (or_intror eq_refl)) in Hp.
    change (prd Bot) with ArgViews.tgb in Hp.
    rewrite (tviewg_of_lbsuper _ _ _ _ _ Hwf Hv l1) in Hp.
    eapply bwalks_agree; eauto. }
  assert (Hq1l : q1 <> Lost) by (apply rlost_free_class in Hlf; tauto).
  rewrite (pfindf_known CT _ q1 l1 C As Hq1 Hq1l) in Hp.
  cbn [ldyn map_qual] in Hs. unfold lsubt in Hs.
  destruct Hs as [[Hb _] | (Hrq & Hl & Vs & Hv & Hle)]; [congruence|].
  destruct (q_eq_dec qb Mut) as [-> | Hqb].
  - rewrite (pwalk_mut CT D Bs q1 l1 C As Hq1) in Hp. apply pnode_some in Hp.
    destruct Hp as (_ & -> & ->).
    rewrite Hf in Hrq, Hl. simpl in Hrq, Hl.
    assert (q1 = Mut).
    { unfold rq_sub in Hrq. destruct Hrq as [Hx | [Hx | [Hx _]]]; congruence. }
    subst q1. split; auto.
  - rewrite (pwalk_class_nb CT qb D Bs q1 l1 C As Hqb Hq1) in Hp.
    rewrite (tviewf_of_ltsuper _ _ _ _ _ _ _ Hwf Hv) in Hp.
    eapply walks_agree; eauto.
Qed.

(** The payload of a class whose arguments fit its bounds, each bound read
    in one frame: a mutable node of that frame's world. *)
Lemma pclassf_fit : forall CT L F f C def As q0 l,
  wf_class_table CT ->
  f Mut = Mut ->
  find_class CT C = Some def ->
  Forall is_class_type (ctparams (signature def)) ->
  Forall2 (fun A B => lsubt CT L A (ldyn F (map_qual f B)))
    As (ctparams (signature def)) ->
  Forall rlost_free (map erase As) ->
  pclassf CT C As = Some (q0, l) ->
  q0 = Mut /\ norm L l = norm L (lf_mut F).
Proof.
  intros CT L F f C def As q0 l Hwf Hf Hfind Hcls Hfits Hlfs Hp.
  unfold pclassf in Hp. rewrite Hfind in Hp.
  revert Hcls Hlfs Hp. induction Hfits as [|A B As Bs HAB Hrest IH];
    intros Hcls Hlfs Hp; simpl in Hp; [discriminate|].
  inversion Hcls as [| ? HB HBs]; subst. inversion Hlfs; subst.
  destruct (pfindf CT B A) as [[qx lx]|] eqn:Hx.
  - inversion Hp; subst.
    destruct B as [qb D Bs0|u o n| ? ? ?]; [|contradiction..].
    eapply walk_fit; eauto.
  - apply IH; auto.
Qed.

(* ------------------WHEN A PAYLOAD EXISTS------------------*)

(** A mutable position is written somewhere in a type. *)
Fixpoint has_mut (T : qualified_type) : bool :=
  match T with
  | TClass q0 _ args =>
      (if q_eq_dec q0 Mut then true else false) ||
      (fix go (l : list qualified_type) : bool :=
         match l with
         | [] => false
         | t :: r => has_mut t || go r
         end) args
  | TVar (TVQual Mut) _ _ => true
  | TVar _ _ _ => false
  | THead _ _ args =>
      (fix go (l : list qualified_type) : bool :=
         match l with
         | [] => false
         | t :: r => has_mut t || go r
         end) args
  end.

Fixpoint has_muts (l : list qualified_type) : bool :=
  match l with
  | [] => false
  | t :: r => has_mut t || has_muts r
  end.

Lemma has_mut_class : forall q0 C args,
  has_mut (TClass q0 C args) =
  (if q_eq_dec q0 Mut then true else false) || has_muts args.
Proof.
  intros q0 C args. cbn [has_mut]. f_equal;
    induction args as [|t r IH]; simpl; auto; rewrite IH; reflexivity.
Qed.

Lemma has_mut_head : forall n C args,
  has_mut (THead n C args) = has_muts args.
Proof.
  intros n C args. cbn [has_mut].
  induction args as [|t r IH]; simpl; auto; rewrite IH; reflexivity.
Qed.

(** A type that writes no mutable position reads the same when written
    mutable positions are forgotten. *)
Lemma no_mut_lit_unm : forall f T,
  has_mut T = false -> map_qual f T = map_qual (unm f) T.
Proof.
  intros f T. induction T using qualified_type_ind'; intros Hn.
  - rewrite has_mut_class in Hn. apply orb_false_iff in Hn.
    destruct Hn as [Hq Hargs].
    destruct (q_eq_dec qual Mut) as [|Hne]; [discriminate|].
    simpl. f_equal; [destruct qual; simpl; congruence|].
    clear Hq. induction H as [|t r Ht Hr IH]; simpl; auto.
    simpl in Hargs. apply orb_false_iff in Hargs. destruct Hargs as [H1 H2].
    f_equal; auto.
  - destruct u as [|qv|mp]; simpl; auto.
    destruct qv; simpl in Hn |- *; auto; discriminate.
  - rewrite has_mut_head in Hn. simpl. f_equal.
    induction H as [|t r Ht Hr IH]; simpl; auto.
    simpl in Hn. apply orb_false_iff in Hn. destruct Hn as [H1 H2].
    f_equal; auto.
Qed.

(** When the bound writes a mutable position, an argument that agrees into
    its reading has a node there. *)
Lemma walk_ex : forall CT L F f B V,
  lagree L V (ldyn F (map_qual f B)) ->
  has_mut B = true -> f Mut = Mut -> pwalk CT B V <> None.
Proof.
  intros CT L F f B. induction B using qualified_type_ind'; intros V Hle Hm Hf.
  - destruct V as [q1 l1 C0 As0]. cbn [ldyn map_qual] in Hle.
    inversion Hle as [? ? ? ? ? ? ? Hq Hlab Hargs]; subst.
    destruct (q_eq_dec qual Mut) as [-> | Hqb].
    + rewrite Hf in Hq. simpl in Hq.
      assert (q1 = Mut).
      { unfold arg_q_sub in Hq. destruct Hq as [Hx | [Hx _]]; congruence. }
      subst q1.
      assert (Hnb : Mut <> Bot) by discriminate.
      rewrite (pwalk_mut CT C args Mut l1 C As0 Hnb). simpl. discriminate.
    + rewrite (pwalk_class CT qual C args q1 l1 C As0 (or_introl Hqb)).
      simpl. rewrite Nat.eqb_refl.
      rewrite has_mut_class in Hm.
      destruct (q_eq_dec qual Mut) as [Hy | Hy]; [contradiction|]. simpl in Hm. clear Hy.
      clear Hq Hlab Hle. revert As0 Hargs Hm.
      induction H as [|B Bs HB HBs IH]; intros As0 Hargs Hm;
        simpl in Hm; [discriminate|].
      destruct As0 as [|A0 As0]; simpl in Hargs; [inversion Hargs|].
      inversion Hargs as [|? ? ? ? HA Hrest]; subst. simpl.
      destruct (pwalk CT B A0) as [x|] eqn:Hx; [discriminate|].
      apply orb_true_iff in Hm. destruct Hm as [Hm | Hm].
      * exfalso. exact (HB A0 HA Hm Hf Hx).
      * apply IH; auto.
  - destruct V as [q1 l1 C0 As0].
    destruct u as [|qv|mp]; [simpl in Hm; discriminate| |simpl in Hm; discriminate].
    destruct qv; simpl in Hm; try discriminate.
    cbn [ldyn map_qual] in Hle. rewrite Hf in Hle.
    destruct (match tv_lookup o (lf_cargs F) (lf_margs F) n with
              | Some A => A | None => ldefault end) as [qa la Ca Aa].
    simpl lrehead in Hle.
    inversion Hle as [? ? ? ? ? ? ? Hq Hlab Hargs]; subst.
    assert (q1 = Mut).
    { unfold arg_q_sub in Hq. destruct Hq as [Hx | [Hx _]]; congruence. }
    subst q1. simpl. discriminate.
  - destruct V as [q1 l1 C0 As0]. cbn [ldyn map_qual] in Hle.
    inversion Hle as [? ? ? ? ? ? ? Hq Hlab Hargs]; subst.
    rewrite (pwalk_head CT n C args q1 l1 C As0).
    simpl. rewrite Nat.eqb_refl.
    rewrite has_mut_head in Hm.
    clear Hq Hlab Hle. revert As0 Hargs Hm.
    induction H as [|B Bs HB HBs IH]; intros As0 Hargs Hm;
      simpl in Hm; [discriminate|].
    destruct As0 as [|A0 As0]; simpl in Hargs; [inversion Hargs|].
    inversion Hargs as [|? ? ? ? HA Hrest]; subst. simpl.
    destruct (pwalk CT B A0) as [x|] eqn:Hx; [discriminate|].
    apply orb_true_iff in Hm. destruct Hm as [Hm | Hm].
    + exfalso. exact (HB A0 HA Hm Hf Hx).
    + apply IH; auto.
Qed.

Lemma walks_ex : forall CT L F f Bs Vs,
  Forall2 (lagree L) Vs (map (ldyn F) (map (map_qual f) Bs)) ->
  has_muts Bs = true -> f Mut = Mut -> pwalks CT Bs Vs <> None.
Proof.
  intros CT L F f Bs. induction Bs as [|B Bs IH]; intros Vs Hle Hm Hf;
    simpl in Hm; [discriminate|].
  destruct Vs as [|V Vs]; simpl in Hle; [inversion Hle|].
  inversion Hle as [|? ? ? ? HV Hrest]; subst. simpl.
  destruct (pwalk CT B V) as [x|] eqn:Hx; [discriminate|].
  apply orb_true_iff in Hm. destruct Hm as [Hm | Hm].
  - exfalso. exact (walk_ex CT L F f B V HV Hm Hf Hx).
  - apply IH; auto.
Qed.

Lemma popen_ne_none : forall q0 l r, r <> None -> popen q0 l r <> None.
Proof. intros q0 l [x|] H; [destruct q0; discriminate | congruence]. Qed.

Lemma fit_ex : forall CT L F f qb D Bs A,
  wf_class_table CT ->
  lsubt CT L A (ldyn F (map_qual f (TClass qb D Bs))) ->
  (match A with LT q1 _ _ _ => q1 <> Bot end) ->
  has_mut (TClass qb D Bs) = true ->
  f Mut = Mut ->
  pfindf CT (TClass qb D Bs) A <> None.
Proof.
  intros CT L F f qb D Bs [q1 l1 C As] Hwf Hs Hq1 Hm Hf.
  rewrite (pfindf_notbot CT _ q1 l1 C As Hq1). apply popen_ne_none.
  cbn [ldyn map_qual] in Hs. unfold lsubt in Hs.
  destruct Hs as [[Hb _] | (Hrq & Hl & Vs & Hv & Hle)]; [congruence|].
  destruct (q_eq_dec qb Mut) as [-> | Hqb].
  - rewrite (pwalk_mut CT D Bs q1 l1 C As Hq1). rewrite (pnode_nb q1 l1 Hq1). discriminate.
  - rewrite (pwalk_class_nb CT qb D Bs q1 l1 C As Hqb Hq1).
    rewrite (tviewf_of_ltsuper _ _ _ _ _ _ _ Hwf Hv).
    rewrite has_mut_class in Hm.
    destruct (q_eq_dec qb Mut) as [Hy | Hy]; [contradiction|]. simpl in Hm.
    eapply walks_ex; eauto.
Qed.

(* ------------------BASIC FACTS ABOUT LABELLED SUBTYPING------------------*)

(** A weaker head reads a header no more fully. *)
Lemma tg_rrel_rq : forall L q1 l1 q2 l2,
  q1 <> Bot -> rq_sub q1 q2 ->
  (q2 = Mut -> norm L l1 = norm L l2) ->
  rrel L q1 (ArgViews.tg q1) l1 q2 (ArgViews.tg q2) l2.
Proof.
  intros L q1 l1 q2 l2 Hnb Hrq Hl q0. unfold rq_sub in Hrq.
  destruct Hrq as [-> | [-> | [-> Hm]]].
  - split; [left; reflexivity|].
    destruct (q_eq_dec q1 Mut) as [-> | Hne].
    + right. right. apply Hl. reflexivity.
    + right. left. destruct q1, q0; simpl; congruence.
  - destruct q1; try congruence; destruct q0; simpl; unfold arg_q_sub;
      (split; [auto | auto]); try (right; left; discriminate).
  - destruct Hm as [-> | [-> | [-> | [-> | ->]]]]; try congruence;
      destruct q0; simpl; unfold arg_q_sub;
      (split; [auto 6 | auto]); try (right; left; discriminate).
Qed.

(** The classes and lengths of a view do not depend on the reader. *)
Lemma view_len : forall CT k hq g d C As D Vs,
  view CT k hq g d C As D Vs ->
  forall k' hq' g' d' As', length As' = length As ->
    exists Vs', view CT k' hq' g' d' C As' D Vs' /\ length Vs' = length Vs.
Proof.
  intros CT k hq g d C As D Vs H.
  induction H; intros k' hq' g' d' As' Hlen.
  - exists As'. split; [apply v_refl | exact Hlen].
  - destruct (IHview k' hq' g' d'
                (hstep k' hq' g' d' (vpay k' CT C As') As' Ss)) as (Vs' & Hv & Hl).
    { unfold hstep. rewrite !length_map. reflexivity. }
    exists Vs'. split; auto. eapply v_step; eauto.
Qed.

Lemma lsubtp_refl : forall CT L A, lsubtp CT L A A.
Proof.
  intros CT L [q0 l C As]. right. refine (conj _ (conj (fun _ => eq_refl) _)).
  - left. reflexivity.
  - exists As. split; [apply v_refl | apply Forall2_lagree_refl].
Qed.

(** A labelled supertype may be replaced by one it agrees into. *)
Lemma lsubtp_agree_r : forall CT L A B B',
  lsubtp CT L A B -> lagree L B B' -> lsubtp CT L A B'.
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

Lemma lsubtp_trans : forall CT L A B C,
  wf_class_table CT ->
  lsubtp CT L A B -> lsubtp CT L B C -> lsubtp CT L A C.
Proof.
  intros CT L [q1 l1 C1 As] [q2 l2 D Bs] [q3 l3 E Cs] Hwf H12 H23.
  assert (H23v : exists Ws, tview CT q2 l2 D Bs E Ws /\ length Ws = length Cs).
  { destruct H23 as [(_ & Ws & Hw & Hl) | (_ & _ & Ws & Hw & Hl)].
    - eauto.
    - exists Ws. split; auto. apply (Forall2_length Hl). }
  destruct H23v as (Ws & Hw & HlW).
  assert (Hbot : q1 = Bot -> lsubtp CT L (LT q1 l1 C1 As) (LT q3 l3 E Cs)).
  { intros ->. left. split; [reflexivity|].
    assert (H12v : exists Vs, tview CT Bot l1 C1 As D Vs /\ length Vs = length Bs).
    { destruct H12 as [(_ & Vs & Hv & Hl) | (_ & _ & Vs & Hv & Hl)].
      - eauto.
      - exists Vs. split; auto. apply (Forall2_length Hl). }
    destruct H12v as (Vs & Hv & HlV).
    destruct (view_len _ _ _ _ _ _ _ _ _ Hw true Bot (ArgViews.tg Bot) l1 Vs HlV)
      as (Ws' & Hw' & HlW').
    exists Ws'. split.
    - unfold tview in *. eapply view_trans; eauto.
    - congruence. }
  destruct (q_eq_dec q1 Bot) as [Hq1 | Hq1]; [auto|].
  destruct H12 as [(Hb & _) | (Hrq12 & Hl12 & Vs & Hv & Hle)]; [contradiction|].
  destruct H23 as [(Hb & _) | (Hrq23 & Hl23 & Ws2 & Hw2 & Hle2)].
  - (* the middle type is bottom-headed: so is the first *)
    exfalso. subst q2. unfold rq_sub in Hrq12.
    destruct Hrq12 as [Hx | [Hx | [Hx _]]]; congruence.
  - right. refine (conj _ (conj _ _)).
    + exact (rq_sub_trans _ _ _ Hrq12 Hrq23).
    + intros Hm. subst q3.
      assert (q2 = Mut).
      { unfold rq_sub in Hrq23. destruct Hrq23 as [Hx | [Hx | [Hx _]]]; congruence. }
      subst q2. rewrite (Hl12 eq_refl). exact (Hl23 eq_refl).
    + pose proof (tg_rrel_rq L q1 l1 q2 l2 Hq1 Hrq12 Hl12) as Hr.
      unfold tview in *.
      destruct (view_transfer _ _ _ _ _ _ _ _ Hw2 true q1 (ArgViews.tg q1) l1 Vs) as (Ws' & Hw').
      exists Ws'. split.
      * eapply view_trans; eauto.
      * eapply Forall2_lagree_trans; [|exact Hle2].
        exact (view_agree _ _ _ _ _ _ _ _ _ Hwf Hw' L _ _ _ _ _ (gok_tg _)
                 (gok_tg _) Hr (vpok_type _ _ _ _ _ _ _ _ _ _) Hle Hw2).
Qed.

(* ------------------CLASSES THAT HAVE NO OBJECTS------------------*)

(** A class one of whose bounds leaves a position open can be neither
    allocated nor extended, so its types have no values.  Fits are stated up
    to such classes. *)
Definition livec (CT : class_table) (C : class_name) : Prop :=
  forall def, find_class CT C = Some def ->
    Forall lost_free (ctparams (signature def)).

(** A class use that can have objects: bounds that leave nothing open and as
    many arguments as parameters. *)
Definition clsok (CT : class_table) (C : class_name) (n : nat) : Prop :=
  livec CT C /\
  forall def, find_class CT C = Some def ->
    length (ctparams (signature def)) = n.

Definition deadA (CT : class_table) (A : ltype) : Prop :=
  match A with LT _ _ C As => ~ clsok CT C (length As) end.

(** A labelled type headed mutable at a class declared immutable has no
    values either; it arises when a variable supplied with an immutable
    class is used requalified. *)
Definition insaneA (CT : class_table) (A : ltype) : Prop :=
  match A with
  | LT q0 _ C _ =>
      q0 = Mut /\ exists def, find_class CT C = Some def /\
                              class_qualifier (signature def) = Imm_c
  end.

Lemma lost_free_qhead_args : forall a C args,
  lost_free (qhead a C args) -> Forall lost_free args.
Proof.
  intros [[q0|m]|] C args H; simpl qhead in H.
  - apply lost_free_class in H. tauto.
  - apply lost_free_head in H. exact H.
  - apply lost_free_class in H. tauto.
Qed.

Lemma lost_free_dec : forall T, lost_free T \/ ~ lost_free T.
Proof.
  induction T using qualified_type_ind'.
  - assert (Hargs : Forall lost_free args \/ ~ Forall lost_free args).
    { induction H as [|t r Ht Hr IH]; [left; constructor|].
      destruct Ht as [Ht | Ht].
      - destruct IH as [IH | IH].
        + left. constructor; auto.
        + right. intros Hx. inversion Hx; auto.
      - right. intros Hx. inversion Hx; auto. }
    destruct (q_eq_dec qual Lost) as [-> | Hq].
    + right. intros Hx. apply lost_free_class in Hx. destruct Hx; congruence.
    + destruct Hargs as [Ha | Ha].
      * left. apply lost_free_class. auto.
      * right. intros Hx. apply lost_free_class in Hx. destruct Hx; auto.
  - destruct u as [|qv|mp]; simpl; auto.
    destruct (q_eq_dec qv Lost) as [-> | Hq]; auto.
  - assert (Hargs : Forall lost_free args \/ ~ Forall lost_free args).
    { induction H as [|t r Ht Hr IH]; [left; constructor|].
      destruct Ht as [Ht | Ht].
      - destruct IH as [IH | IH].
        + left. constructor; auto.
        + right. intros Hx. inversion Hx; auto.
      - right. intros Hx. inversion Hx; auto. }
    destruct Hargs as [Ha | Ha].
    + left. apply lost_free_head. exact Ha.
    + right. intros Hx. apply lost_free_head in Hx. auto.
Qed.

Lemma Forall_lost_free_dec : forall l,
  Forall lost_free l \/ ~ Forall lost_free l.
Proof.
  induction l as [|t r IH]; [left; constructor|].
  destruct (lost_free_dec t) as [Ht | Ht].
  - destruct IH as [IH | IH].
    + left. constructor; auto.
    + right. intros Hx. inversion Hx; auto.
  - right. intros Hx. inversion Hx; auto.
Qed.

Lemma livec_dec : forall CT C, livec CT C \/ ~ livec CT C.
Proof.
  intros CT C. unfold livec.
  destruct (find_class CT C) as [def|] eqn:Hf.
  - destruct (Forall_lost_free_dec (ctparams (signature def))) as [H | H].
    + left. intros d Hd. inversion Hd; subst. exact H.
    + right. intros Hx. apply H. apply Hx. reflexivity.
  - left. intros d Hd. discriminate.
Qed.

(** An instance of a type that leaves nothing open comes from a type that
    leaves nothing open. *)
Lemma lost_free_inst_inv : forall f Ss Us Qs T,
  f Lost = Lost ->
  lost_free (subst Ss Us Qs (map_qual f T)) -> lost_free T.
Proof.
  intros f Ss Us Qs T Hf. induction T using qualified_type_ind'; intros Hl.
  - cbn [subst map_qual] in Hl. apply lost_free_class in Hl.
    destruct Hl as [Hq Hargs].
    apply (lost_free_class qual C args). split.
    + intros ->. congruence.
    + clear Hq. revert Hargs.
      induction H as [|t r Ht Hr IH]; intros Hargs; [constructor|].
      simpl in Hargs. inversion Hargs; subst.
      constructor; [apply Ht; assumption | apply IH; assumption].
  - destruct u as [|qv|mp]; simpl; auto.
    intros ->. simpl in Hl. rewrite Hf in Hl.
    destruct (match tv_lookup o Ss Us n with Some U => U | None => default_type end)
      as [q1 C1 a1 | u1 o1 n1 | n1 C1 a1]; simpl in Hl.
    + destruct Hl as [Hx _]. congruence.
    + congruence.
    + destruct Hl as [Hx _]. congruence.
  - cbn [subst map_qual] in Hl. apply lost_free_qhead_args in Hl.
    apply lost_free_head.
    revert Hl. induction H as [|t r Ht Hr IH]; intros Hargs; [constructor|].
    simpl in Hargs. inversion Hargs; subst.
    constructor; [apply Ht; assumption | apply IH; assumption].
Qed.

Lemma lost_free_inst : forall f Ss T,
  (forall q0, q0 <> Lost -> f q0 <> Lost) ->
  Forall lost_free Ss ->
  lost_free T -> lost_free (subst Ss [] [] (map_qual f T)).
Proof.
  intros f Ss T Hf HSs. induction T using qualified_type_ind'; intros Hl.
  - apply lost_free_class in Hl. destruct Hl as [Hq Hargs].
    simpl. apply (lost_free_class (f qual) C (map (subst Ss [] []) (map (map_qual f) args))).
    split; auto.
    clear Hq. revert Hargs.
    induction H as [|t r Ht Hr IH]; intros Hargs; simpl; [constructor|].
    inversion Hargs; subst.
    constructor; [apply Ht; assumption | apply IH; assumption].
  - assert (HU : lost_free
              match tv_lookup o Ss [] n with Some U => U | None => default_type end).
    { destruct (tv_lookup o Ss [] n) as [U|] eqn:Hlk.
      - destruct o; simpl in Hlk.
        + rewrite Forall_forall in HSs. apply HSs. eapply nth_error_In; eauto.
        + destruct n; discriminate.
      - simpl. split; [discriminate | exact I]. }
    destruct u as [|qv|mp]; simpl; auto.
    + simpl in Hl.
      destruct (match tv_lookup o Ss [] n with Some U => U | None => default_type end)
        as [q1 C1 a1 | u1 o1 n1 | n1 C1 a1]; simpl.
      * simpl in HU. destruct HU as [_ Ha]. split; auto.
      * auto.
      * simpl in HU. split; auto.
    + replace (nth_error (@nil qarg) mp) with (@None qarg) by (destruct mp; reflexivity).
      simpl.
      destruct (match tv_lookup o Ss [] n with Some U => U | None => default_type end)
        as [q1 C1 a1 | u1 o1 n1 | n1 C1 a1]; simpl.
      * simpl in HU. destruct HU as [_ Ha]. split; [discriminate | auto].
      * discriminate.
      * simpl in HU. split; [discriminate | auto].
  - apply lost_free_head in Hl. cbn [subst map_qual nth_error qhead].
    replace (nth_error (@nil qarg) n) with (@None qarg) by (destruct n; reflexivity).
    cbn [qhead]. apply lost_free_class. split; [discriminate|].
    revert Hl. induction H as [|t r Ht Hr IH]; intros Hargs; simpl; [constructor|].
    inversion Hargs; subst.
    constructor; [apply Ht; assumption | apply IH; assumption].
Qed.

(** A class that has a subclass has bounds that leave nothing open. *)
Lemma live_parent : forall CT C D Ss,
  wf_class_table CT -> parent_lookup CT C = Some (D, Ss) -> livec CT D.
Proof.
  intros CT C D Ss Hwf Hparent. unfold parent_lookup in Hparent.
  destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
  destruct (wf_class_super_inv _ _ _ _ _ Hwf Hfind Hparent)
    as (sd & Hsd & _ & _ & Hb & _).
  intros d Hd. rewrite Hsd in Hd. inversion Hd; subst d.
  clear - Hb. induction Hb as [|T B Ts Bs [Hlf _] Hrest IH]; constructor; auto.
  unfold member_type, adapt in Hlf.
  eapply lost_free_inst_inv; [|exact Hlf].
  destruct (class_qualifier (signature def)); reflexivity.
Qed.

Lemma view_live : forall CT k hq g d C As D Vs,
  wf_class_table CT -> view CT k hq g d C As D Vs -> C <> D -> livec CT D.
Proof.
  intros CT k hq g d C As D Vs Hwf H. induction H; intros Hne; [congruence|].
  destruct (Nat.eq_dec P D) as [-> | HPD].
  - eapply live_parent; eauto.
  - auto.
Qed.

Lemma clsok_dec : forall CT C n, clsok CT C n \/ ~ clsok CT C n.
Proof.
  intros CT C n. unfold clsok.
  destruct (livec_dec CT C) as [Hl | Hl]; [|right; intros (Hx & _); auto].
  destruct (find_class CT C) as [def|] eqn:Hf.
  - destruct (Nat.eq_dec (length (ctparams (signature def))) n) as [Hn | Hn].
    + left. split; auto. intros d Hd. inversion Hd; subst. auto.
    + right. intros (_ & Hx). apply Hn. auto.
  - left. split; auto. intros d Hd. discriminate.
Qed.

Lemma deadA_dec : forall CT A, deadA CT A \/ ~ deadA CT A.
Proof.
  intros CT [q0 l C As]. simpl.
  destruct (clsok_dec CT C (length As)) as [H | H]; [right | left]; auto.
Qed.

Lemma qc_eq_dec : forall a b : q_c, {a = b} + {a <> b}.
Proof. decide equality. Qed.

Lemma insaneA_dec : forall CT A, insaneA CT A \/ ~ insaneA CT A.
Proof.
  intros CT [q0 l C As]. simpl.
  destruct (q_eq_dec q0 Mut) as [-> | Hq]; [|right; intros (Hx & _); auto].
  destruct (find_class CT C) as [def|] eqn:Hf.
  - destruct (qc_eq_dec (class_qualifier (signature def)) Imm_c) as [Hi | Hi].
    + left. split; auto. eauto.
    + right. intros (_ & d & Hd & Hx). inversion Hd; subst. auto.
  - right. intros (_ & d & Hd & _). discriminate.
Qed.

(** Below a class declared immutable there are only classes declared
    immutable. *)
Lemma view_imm : forall CT k hq g d C As D Vs,
  wf_class_table CT -> view CT k hq g d C As D Vs ->
  forall dd, find_class CT D = Some dd ->
    class_qualifier (signature dd) = Imm_c ->
    exists dc, find_class CT C = Some dc /\
               class_qualifier (signature dc) = Imm_c.
Proof.
  intros CT k hq g d C As D Vs Hwf H. induction H; intros dd Hdd Hi; eauto.
  destruct (IHview dd Hdd Hi) as (dp & Hdp & Hip).
  unfold parent_lookup in Hparent.
  destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
  destruct (wf_class_super_inv _ _ _ _ _ Hwf Hfind Hparent)
    as (sd' & Hsd' & _ & _ & _ & Hqq & _).
  rewrite Hdp in Hsd'. inversion Hsd'; subst sd'.
  exists def. split; auto. destruct Hqq as [Hx | Hx]; congruence.
Qed.

(** A view has as many arguments as its class has parameters. *)
Lemma view_arity : forall CT k hq g d C As D Vs,
  wf_class_table CT -> view CT k hq g d C As D Vs ->
  (forall def, find_class CT C = Some def ->
     length (ctparams (signature def)) = length As) ->
  forall def, find_class CT D = Some def ->
    length (ctparams (signature def)) = length Vs.
Proof.
  intros CT k hq g d C As D Vs Hwf H. induction H; intros Hlen; auto.
  apply IHview. intros sd Hsd.
  unfold parent_lookup in Hparent.
  destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
  destruct (wf_class_super_inv _ _ _ _ _ Hwf Hfind Hparent)
    as (sd' & Hsd' & _ & _ & Hb & _).
  rewrite Hsd in Hsd'. inversion Hsd'; subst sd'.
  unfold hstep. rewrite length_map. symmetry. exact (Forall2_length Hb).
Qed.

(** Above a class use that can have objects there are only such uses. *)
Lemma lsubtp_dead : forall CT L A B,
  wf_class_table CT -> lsubtp CT L A B -> deadA CT B -> ~ deadA CT A -> False.
Proof.
  intros CT L [q1 l1 C As] [q2 l2 D Bs] Hwf H HB HA. simpl in *.
  apply HA. intros (Hlv & Har). apply HB.
  assert (Hv : exists Vs, view CT true q1 (ArgViews.tg q1) l1 C As D Vs /\
                          length Vs = length Bs).
  { destruct H as [(Hb & Vs & Hv & Hl) | (Hrq & _ & Vs & Hv & Hle)]; eauto.
    exists Vs. split; auto. exact (Forall2_length Hle). }
  destruct Hv as (Vs & Hv & Hlen).
  split.
  - destruct (Nat.eq_dec C D) as [<- | Hne]; auto. eapply view_live; eauto.
  - intros dd Hdd. rewrite <- Hlen.
    eapply (view_arity _ _ _ _ _ _ _ _ _ Hwf Hv); eauto.
Qed.

(** The same type headed by the bottom qualifier. *)
Definition lbot (A : ltype) : ltype := lrehead Bot LOut A.

Lemma lsubtp_lbot : forall CT L A B,
  lsubtp CT L A B -> lsubtp CT L (lbot A) B.
Proof.
  intros CT L [q1 l1 C As] [q2 l2 D Bs] H. simpl. left. split; auto.
  assert (Hv : exists Vs, tview CT q1 l1 C As D Vs /\ length Vs = length Bs).
  { destruct H as [(Hb & Vs & Hv & Hl) | (Hrq & _ & Vs & Hv & Hle)]; eauto.
    exists Vs. split; auto. exact (Forall2_length Hle). }
  destruct Hv as (Vs & Hv & Hlen).
  destruct (view_len _ _ _ _ _ _ _ _ _ Hv true Bot (ArgViews.tg Bot) LOut As
              eq_refl) as (Ws & Hw & HlW).
  exists Ws. split; auto. congruence.
Qed.

(* ------------------WORLD IDENTIFIERS IN VIEWS------------------*)

Lemma rd_lab_bound : forall n d pn,
  lab_bound n d ->
  (forall q0 l, pn = Some (q0, l) -> lab_bound n l) ->
  lab_bound n (rd_lab d pn).
Proof.
  intros n d pn Hd Hp. destruct pn as [[q0 l]|]; simpl; auto.
  destruct q0; auto. apply (Hp Mut l). reflexivity.
Qed.

Lemma hstep_lbound : forall n k hq g d pn As Ss,
  lab_bound n d ->
  (forall q0 l, pn = Some (q0, l) -> lab_bound n l) ->
  Forall (lbound n) As ->
  Forall (lbound n) (hstep k hq g d pn As Ss).
Proof.
  intros n k hq g d pn As Ss Hd Hp HAs. unfold hstep.
  assert (HF : frame_bound n (hframe hq d pn As)).
  { unfold frame_bound, hframe. simpl. repeat split; auto.
    apply rd_lab_bound; auto. }
  induction Ss; simpl; constructor; auto using ldyn_lbound.
Qed.

Lemma tviewf_lbound : forall CT n m q0 l C As D Vs,
  lab_bound n l -> Forall (lbound n) As ->
  tviewf CT m q0 l C As D = Some Vs -> Forall (lbound n) Vs.
Proof.
  intros CT n m. induction m as [|m IH]; intros q0 l C As D Vs Hl HAs H;
    [discriminate|].
  simpl in H. destruct (Nat.eqb C D); [inversion H; subst; auto|].
  destruct (parent_lookup CT C) as [[P Ss]|]; [|discriminate].
  eapply IH; [exact Hl | | exact H].
  apply hstep_lbound; auto. intros q1 l1 Hx. discriminate.
Qed.

Lemma tviewg_lbound : forall CT n m q0 g l C As D Vs,
  lab_bound n l -> Forall (lbound n) As ->
  tviewg CT m q0 g l C As D = Some Vs -> Forall (lbound n) Vs.
Proof.
  intros CT n m. induction m as [|m IH]; intros q0 g l C As D Vs Hl HAs H;
    [discriminate|].
  simpl in H. destruct (Nat.eqb C D); [inversion H; subst; auto|].
  destruct (parent_lookup CT C) as [[P Ss]|]; [|discriminate].
  eapply IH; [exact Hl | | exact H].
  apply hstep_lbound; auto. intros q1 l1 Hx. discriminate.
Qed.

Lemma pwalk_lbound : forall CT n B A q0 l,
  lbound n A -> pwalk CT B A = Some (q0, l) -> lab_bound n l.
Proof.
  intros CT n B. induction B using qualified_type_ind'; intros A q0 l HA Hp.
  - destruct A as [q1 l1 C0 As0]. apply lbound_node in HA.
    destruct HA as [Hl1 HAs].
    destruct (pdir qual q1) eqn:Hpd.
    + rewrite (pwalk_dir CT qual C args q1 l1 C0 As0 Hpd) in Hp. apply pnode_some in Hp.
      destruct Hp as (_ & _ & ->). exact Hl1.
    + rewrite (pwalk_ndir CT qual C args q1 l1 C0 As0 Hpd) in Hp.
      destruct (tviewg CT (S C0) q1 (prd q1) l1 C0 As0 C) as [Vs|] eqn:Hv;
        [|discriminate].
      pose proof (tviewg_lbound _ _ _ _ _ _ _ _ _ _ Hl1 HAs Hv) as HVs.
      clear Hv. revert Vs HVs Hp.
      induction H as [|B Bs HB HBs IH]; intros Vs HVs Hp; simpl in Hp;
        [discriminate|].
      destruct Vs as [|V Vs]; [discriminate|].
      inversion HVs; subst.
      destruct (pwalk CT B V) as [[qx lx]|] eqn:Hx.
      * inversion Hp; subst. eapply HB; eauto.
      * eapply IH; eauto.
  - destruct A as [q1 l1 C0 As0]. apply lbound_node in HA.
    destruct HA as [Hl1 _].
    destruct u as [|qv|mp]; [simpl in Hp; discriminate| |simpl in Hp; discriminate].
    destruct qv; simpl in Hp; try discriminate. apply pnode_some in Hp.
    destruct Hp as (_ & _ & ->). exact Hl1.
  - destruct A as [q1 l1 C0 As0]. apply lbound_node in HA.
    destruct HA as [Hl1 HAs].
    rewrite (pwalk_head CT n0 C args q1 l1 C0 As0) in Hp.
    destruct (tviewg CT (S C0) q1 (prd q1) l1 C0 As0 C) as [Vs|] eqn:Hv;
      [|discriminate].
    pose proof (tviewg_lbound _ _ _ _ _ _ _ _ _ _ Hl1 HAs Hv) as HVs.
    clear Hv. revert Vs HVs Hp.
    induction H as [|B Bs HB HBs IH]; intros Vs HVs Hp; simpl in Hp;
      [discriminate|].
    destruct Vs as [|V Vs]; [discriminate|].
    inversion HVs; subst.
    destruct (pwalk CT B V) as [[qx lx]|] eqn:Hx.
    + inversion Hp; subst. eapply HB; eauto.
    + eapply IH; eauto.
Qed.

Lemma pclassf_lbound : forall CT n C As q0 l,
  Forall (lbound n) As -> pclassf CT C As = Some (q0, l) -> lab_bound n l.
Proof.
  intros CT n C As q0 l HAs Hp. unfold pclassf in Hp.
  destruct (find_class CT C) as [def|]; [|discriminate].
  revert As HAs Hp.
  induction (ctparams (signature def)) as [|B Bs IH]; intros As HAs Hp;
    simpl in Hp; [discriminate|].
  destruct As as [|A As]; [discriminate|]. inversion HAs as [|? ? HA HAs']; subst.
  destruct (pfindf CT B A) as [[qx lx]|] eqn:Hx.
  - inversion Hp; subst. destruct A as [q1 l1 C1 As1].
    cbn [pfindf] in Hx.
    destruct (q_eq_dec q1 Lost) as [-> | Hql].
    + destruct (pwalk CT B (LT Lost l1 C1 As1)); simpl in Hx; [|discriminate].
      inversion Hx; subst. apply lbound_node in HA. tauto.
    + rewrite (popen_keep q1 l1 _ Hql) in Hx. eapply pwalk_lbound; eauto.
  - eapply IH; eauto.
Qed.

Lemma view_lbound : forall CT k hq g d C As D Vs n,
  view CT k hq g d C As D Vs ->
  lab_bound n d -> Forall (lbound n) As -> Forall (lbound n) Vs.
Proof.
  intros CT k hq g d C As D Vs n H Hd. induction H; intros HAs; auto.
  apply IHview. apply hstep_lbound; auto.
  intros q0 l Hp. destruct k; simpl in Hp; [discriminate | eapply pclassf_lbound; eauto].
Qed.

(* ------------------SOUNDNESS OF THE PAYLOAD-VIEW FIT------------------*)

(** The payloads along an object's chain are nodes of one world, stated for
    the object behind a location. *)
Lemma opay_trans : forall CT L qo c C As D Vs lm,
  oview CT qo c C As D Vs -> opay CT L qo c C As lm -> opay CT L qo c D Vs lm.
Proof.
  intros CT L qo c C As D Vs lm Hv Hp E Ws Hw. apply Hp. eapply oview_trans; eauto.
Qed.

Lemma opay_lm : forall CT L qo c C As lm lm',
  norm L lm = norm L lm' -> opay CT L qo c C As lm -> opay CT L qo c C As lm'.
Proof. intros CT L qo c C As lm lm' Hn Hp D Vs Hv w Hw. rewrite <- Hn. eapply Hp; eauto. Qed.

(** The payloads of the object behind a mutable-headed labelled type are
    nodes of the type's world when that world is live: a coloured object's
    payloads are in its colour, which the head agreement ties to the label.
    A dead label asks nothing. *)
Lemma lpay_of_heap : forall CT h G L v o l,
  runtime_getObj h v = Some o ->
  (forall w, g_col G v = Some w ->
     opay CT L (rqtype (rt_type o)) (LIn w) (rctype (rt_type o)) (g_args G v) (LIn w)) ->
  headL L (g_col G v) Mut l ->
  norm L l = None \/
  opay CT L (rqtype (rt_type o)) (olab (g_col G v)) (rctype (rt_type o)) (g_args G v) l.
Proof.
  intros CT h G L v o l Ho Hpay Hh.
  unfold headL in Hh. specialize (Hh eq_refl).
  destruct (g_col G v) as [w|] eqn:Hc.
  - right. simpl. eapply opay_lm; [|exact (Hpay w eq_refl)].
    destruct (norm L l) as [w'|] eqn:Hn.
    + inversion Hh; subst w'. apply norm_live. eapply norm_some_in. exact Hn.
    + apply norm_dead. apply (Hh w eq_refl).
  - left. destruct (norm L l) as [w'|] eqn:Hn; [discriminate Hh | reflexivity].
Qed.

(** A value of a labelled type is a value of every labelled supertype: the
    object's two views exist along the type's chain and agree with the
    type's view, which agrees with the supertype's arguments. *)
Theorem lsubtp_sound : forall CT h G L v A B,
  wf_class_table CT ->
  loc_has_rtype CT h v (erase A) ->
  (forall o w, runtime_getObj h v = Some o -> g_col G v = Some w ->
     opay CT L (rqtype (rt_type o)) (LIn w) (rctype (rt_type o)) (g_args G v) (LIn w)) ->
  lhasp CT h G L v A ->
  lsubtp CT L A B ->
  lhasp CT h G L v B.
Proof.
  intros CT h G L v [q1 l1 C As] [q2 l2 D Bs] Hwf Hty Hpay Hl Hsub.
  destruct Hl as (o & Ho & Hh & Vr0 & Vp0 & Hr0 & Hp0 & Hle0).
  unfold loc_has_rtype in Hty. rewrite Ho in Hty. simpl in Hty.
  destruct Hty as [Hhead _].
  destruct Hsub as [[-> _] | (Hrq & Hlab & Vt & Hts & Hle)];
    [exfalso; exact (head_ok_not_bot _ Hhead)|].
  assert (Hq1 : q2 = Mut -> q1 = Mut).
  { intros ->. unfold rq_sub in Hrq. destruct Hrq as [Hx | [Hx | [Hx _]]]; congruence. }
  assert (HheadB : headL L (g_col G v) q2 l2).
  { unfold headL. intros Hm. pose proof (Hq1 Hm). subst q1 q2.
    rewrite <- (Hlab eq_refl). exact (Hh eq_refl). }
  destruct (view_xagree3 CT q1 l1 C As D Vt Hwf Hts L (dead L q1 l1)
              (rqtype (rt_type o)) (olab (g_col G v)) Vr0 Vp0 Hhead)
    as (Vr & Vp & Hvr & Hvp & Hle3).
  { intros ->. exact (headL_norm L (g_col G v) l1 (Hh eq_refl)). }
  { intros ->.
    destruct (lpay_of_heap CT h G L v o l1 Ho (fun w Hc => Hpay o w Ho Hc) Hh)
      as [Hd | Hp].
    - left. intros _ Hn. exact (Hn Hd).
    - right. eapply opay_trans; [exact Hr0 | exact Hp]. }
  { exact Hle0. }
  exists o. split; auto. split; [exact HheadB|].
  exists Vr, Vp. split; [eapply oview_trans; eauto|].
  split; [eapply oplain_trans; eauto|].
  eapply Forall3_xagree_trans_r; [|exact Hle].
  eapply Forall3_xagree_mono; [|exact Hle3].
  intros Hd Hm Hn. pose proof (Hq1 Hm). subst q1 q2.
  apply (Hd eq_refl). rewrite (Hlab eq_refl). exact Hn.
Qed.

(* ------------------FROM A TYPING DERIVATION------------------*)

Lemma lc2_trans : forall L g h f Fo Fm Fc,
  label_cond2 L g h Fo Fm -> label_cond2 L h f Fm Fc ->
  label_cond2 L g f Fo Fc.
Proof.
  intros L g h f Fo Fm Fc H1 H2 q0.
  destruct (H1 q0) as [Ha1 Hb1]. destruct (H2 q0) as [Ha2 Hb2].
  split; [eapply arg_q_sub_trans; eauto|].
  destruct Hb2 as [Hx | [Hx | Hx]]; auto.
  - destruct (q_eq_dec (dynq (lf_q Fo) (g q0)) Mut) as [Hs | Hs]; auto.
    left. rewrite Hs in Ha1. unfold arg_q_sub in Ha1, Ha2.
    destruct Ha1 as [Hy | [Hy _]]; [congruence|].
    rewrite Hy in Ha2. destruct Ha2 as [Hz | [Hz _]]; auto.
  - destruct Hb1 as [Hy | [Hy | Hy]]; auto.
    + left. rewrite Hy in Ha2. unfold arg_q_sub in Ha2.
      destruct Ha2 as [Hz | [Hz _]]; auto.
    + destruct (q_eq_dec (dynq (lf_q Fo) (g q0)) Mut) as [Hs | Hs]; auto.
      destruct (q_eq_dec (dynq (lf_q Fc) (f q0)) Lost) as [Ht | Ht]; auto.
      right. right. rewrite Hy. exact Hx.
Qed.

Lemma pcoh_view : forall CT L q0 l C As lm D Vs,
  pcoh CT L q0 l C As lm -> tview CT q0 l C As D Vs ->
  pcoh CT L q0 l D Vs lm.
Proof.
  intros CT L q0 l C As lm D Vs H Hv C' As' Hv'.
  apply H. unfold tview in *. eapply view_trans; eauto.
Qed.

Lemma static_view_len : forall CT mt qh C Ts D Vs,
  super_inst CT mt qh C Ts D Vs ->
  forall k hq g d As, length As = length Ts ->
    exists Vs', view CT k hq g d C As D Vs' /\ length Vs' = length Vs.
Proof.
  intros CT mt qh C Ts D Vs H.
  induction H; intros k hq g d As Hlen.
  - exists As. split; [apply v_refl | exact Hlen].
  - destruct (IHsuper_inst k hq g d (hstep k hq g d (vpay k CT C As) As Ss))
      as (Vs' & Hv & Hl).
    { unfold hstep. rewrite !length_map. reflexivity. }
    exists Vs'. split; auto. eapply v_step; eauto.
Qed.

(** Weakening the written head of the supertype, with arguments that
    agree. *)
Lemma lsubtp_head : forall CT L F A q1 q2 C Bs Bs',
  lsubtp CT L A (LT (dynq (lf_q F) q1) (lab_of F q1) C Bs) ->
  q_subtype q1 q2 ->
  Forall2 (lagree L) Bs Bs' ->
  lsubtp CT L A (LT (dynq (lf_q F) q2) (lab_of F q2) C Bs').
Proof.
  intros CT L F [qA lA CA AsA] q1 q2 C Bs Bs' H Hq Hle.
  assert (Hv : exists Vs, tview CT qA lA CA AsA C Vs /\ length Vs = length Bs').
  { destruct H as [(_ & Vs & Hv & Hl) | (_ & _ & Vs & Hv & Hl)].
    - exists Vs. split; auto. rewrite Hl. apply (Forall2_length Hle).
    - exists Vs. split; auto. rewrite (Forall2_length Hl).
      apply (Forall2_length Hle). }
  inversion Hq; subst.
  - eapply lsubtp_agree_r; [exact H|].
    constructor; [left; reflexivity | right; right; reflexivity | exact Hle].
  - destruct H as [(Hb & _) | (Hrq & Hl & Vs & Hvs & Hles)].
    + left. split; auto.
    + right. refine (conj _ (conj _ _)).
      * right. left. reflexivity.
      * intros Hm. discriminate.
      * exists Vs. split; auto. eapply Forall2_lagree_trans; eauto.
  - left. split; [|exact Hv].
    simpl in H. destruct H as [(Hb & _) | (Hrq & _)]; auto.
    unfold rq_sub in Hrq. destruct Hrq as [Hx | [Hx | [Hx _]]]; congruence.
Qed.

(** The labelled source of a derivation: when it is headed mutable in the
    frame's own world, its payloads are of that world. *)
Definition cohA (CT : class_table) (L : list nat) (F : lframe) (A : ltype)
    : Prop :=
  match A with
  | LT q0 l C As =>
      q0 = Mut -> norm L l = norm L (lf_mut F) ->
      pcoh CT L Mut l C As (lf_mut F)
  end.

Definition frame_fitsp (CT : class_table) (L : list nat) (Δ : tv_env)
    (F : lframe) : Prop :=
  forall o n B, tv_bound Δ o n = Some B ->
    lsubtp CT L (ldyn F (TVar TVSub o n)) (ldyn F B) \/
    deadA CT (ldyn F (TVar TVSub o n)) \/
    (insaneA CT (ldyn F (TVar TVSub o n)) /\
     lsubtp CT L (lbot (ldyn F (TVar TVSub o n))) (ldyn F B)).

(** The static types from which a type written mutable can be derived: a
    class type written mutable or bottom, a variable whose bound is one, and
    a variable use requalified so. *)
Definition headmb (T : qualified_type) : Prop :=
  match T with
  | TClass q0 _ _ => q0 = Mut \/ q0 = Bot
  | TVar _ _ _ => False
  | THead _ _ _ => False
  end.

Definition reachm (Δ : tv_env) (T : qualified_type) : Prop :=
  match T with
  | TClass q0 _ _ => q0 = Mut \/ q0 = Bot
  | TVar TVSub o n => exists B, tv_bound Δ o n = Some B /\ headmb B
  | TVar (TVQual q0) _ _ => q0 = Mut \/ q0 = Bot
  | TVar (TVPoly _) _ _ => False
  | THead _ _ _ => False
  end.

Lemma q_subtype_mb : forall q1 q2,
  q_subtype q1 q2 -> q2 = Mut \/ q2 = Bot -> q1 = Mut \/ q1 = Bot.
Proof. intros q1 q2 H [-> | ->]; inversion H; subst; auto. Qed.

Lemma reachm_sub : forall CT Δ T U,
  (forall o n B, tv_bound Δ o n = Some B -> is_class_type B) ->
  qualified_type_subtype CT Δ T U -> reachm Δ U -> reachm Δ T.
Proof.
  intros CT Δ T U Hbc H. induction H; intros Hm; simpl in Hm |- *; auto.
  - eapply q_subtype_mb; eauto.
  - exists B. split; auto.
    pose proof (Hbc _ _ _ Hbound) as Hc.
    destruct B as [qb Cb Bsb|u0 o0 n0| ? ? ?]; [exact Hm | contradiction..].
  - eapply q_subtype_mb; eauto.
  - destruct Hm; discriminate.
  - destruct Hm; discriminate.
  - destruct Hm; discriminate.
Qed.

(** What the hierarchy steps of a derivation need of the labelled source,
    stated at the type the derivation has reached: when the source is headed
    mutable in the frame's own world, its payloads above that type's class
    are of that world.  For a qualified use of a variable it is asked at every
    class the variable reaches. *)
Definition cohT (CT : class_table) (L : list nat) (Δ : tv_env) (F : lframe)
    (A : ltype) (T : qualified_type) : Prop :=
  match A with
  | LT q0 l CA AsA =>
      q0 = Mut -> norm L l = norm L (lf_mut F) ->
      match T with
      | TClass _ C _ =>
          forall Va, tview CT Mut l CA AsA C Va ->
            pcoh CT L Mut l C Va (lf_mut F)
      | TVar (TVQual _) o n =>
          forall qb C Ts, qualified_type_subtype CT Δ (TVar TVSub o n) (TClass qb C Ts) ->
          forall Va, tview CT Mut l CA AsA C Va ->
            pcoh CT L Mut l C Va (lf_mut F)
      | TVar (TVPoly _) _ _ =>
          forall C, tview CT Mut l CA AsA C [] ->
            pcoh CT L Mut l C [] (lf_mut F)
      | TVar TVSub _ _ => True
      | THead _ _ _ => True
      end
  end.

(** Coherence is kept when the arguments are replaced by arguments that
    agree into them and the head label by an equal one. *)
Lemma pcoh_agree : forall CT L l l' C As As' lm,
  wf_class_table CT -> norm L l = norm L l' -> Forall2 (lagree L) As As' ->
  pcoh CT L Mut l' C As' lm -> pcoh CT L Mut l C As lm.
Proof.
  intros CT L l l' C As As' lm Hwf Hl Hle Hp C' V Hv. unfold tview in Hv.
  assert (Hr : rrel L Mut (ArgViews.tg Mut) l Mut (ArgViews.tg Mut) l').
  { apply tg_rrel; [left; reflexivity | right; right; exact Hl]. }
  destruct (view_len _ _ _ _ _ _ _ _ _ Hv true Mut (ArgViews.tg Mut) l' As'
              (eq_sym (Forall2_length Hle))) as (V' & Hv' & _).
  pose proof (view_agree _ _ _ _ _ _ _ _ _ Hwf Hv L _ _ _ _ _ (gok_tg _)
                (gok_tg _) Hr (vpok_type _ _ _ _ _ _ _ _ _ _) Hle Hv') as HVV.
  pose proof (pclassf_agree CT L C' V V' HVV) as Hn.
  pose proof (Hp C' V' Hv') as Hp'.
  destruct (pclassf CT C' V) as [[q1 l1]|]; destruct (pclassf CT C' V') as [[q2 l2]|];
    simpl in Hn; try contradiction; auto.
  destruct Hn as [Hq Hn].
  destruct (q_eq_dec q2 Lost) as [-> | Hq2]; [contradiction|].
  assert (q2 = q1).
  { unfold arg_q_sub in Hq. destruct Hq as [Hx | [Hx _]]; congruence. }
  subst q2. destruct q1; auto.
  destruct Hn as [Hx | [Hx | Hx]]; congruence.
Qed.

Lemma pcoh_lm : forall CT L q0 l C As lm lm',
  norm L lm = norm L lm' -> pcoh CT L q0 l C As lm -> pcoh CT L q0 l C As lm'.
Proof.
  intros CT L q0 l C As lm lm' He Hp C' As' Hv. specialize (Hp C' As' Hv).
  destruct (pclassf CT C' As') as [[q' l']|]; auto. destruct q'; auto.
  rewrite <- He. exact Hp.
Qed.

(** A labelled type headed mutable whose payloads, seen from class [K] up,
    are of its own head label. *)
Definition scoh (CT : class_table) (L : list nat) (A : ltype) (K : class_name)
    : Prop :=
  match A with
  | LT q0 l CA AsA =>
      q0 = Mut -> forall Va, tview CT Mut l CA AsA K Va -> pcoh CT L Mut l K Va l
  end.

(** The arguments supplied under bounds written mutable are coherent at the
    bound's class, unless they are types no value can have. *)
Definition fcoh (CT : class_table) (L : list nat) (Δ : tv_env) (F : lframe)
    : Prop :=
  forall o n C Bs, tv_bound Δ o n = Some (TClass Mut C Bs) ->
    ~ deadA CT (ldyn F (TVar TVSub o n)) ->
    ~ insaneA CT (ldyn F (TVar TVSub o n)) ->
    scoh CT L (ldyn F (TVar TVSub o n)) C.

(** Then so is every labelled type below such an argument. *)
Lemma hvb_of_coh : forall CT L Δ F,
  wf_class_table CT ->
  (forall o n B, tv_bound Δ o n = Some B -> is_class_type B) ->
  frame_fitsp CT L Δ F -> fcoh CT L Δ F ->
  forall o n B A, tv_bound Δ o n = Some B -> headmb B ->
    ~ deadA CT A -> ~ insaneA CT A ->
    lsubtp CT L A (ldyn F (TVar TVSub o n)) -> cohT CT L Δ F A B.
Proof.
  intros CT L Δ F Hwf Hbc Hfit Hcoh o n B A Hb Hmb Hnd Hsn H.
  destruct B as [qb K Bs|u0 o0 n0| ? ? ?]; [|contradiction..].
  destruct A as [qA lA CA AsA]. simpl. intros -> HlA Va Hva.
  pose proof (Hfit o n _ Hb) as Hf. pose proof (Hcoh o n K Bs) as Hc.
  destruct (ldyn F (TVar TVSub o n)) as [qx lx Cx Asx] eqn:HX.
  pose proof H as HAX.
  destruct H as [(Hx & _) | (Hrq & Hl & Va' & Hva' & Hle)]; [discriminate|].
  destruct Hf as [Hf | [Hd | [Hi _]]].
  - cbn [ldyn] in Hf.
    destruct Hf as [(Hx & _) | (Hrq2 & Hl2 & Vx & Hvx & Hle2)].
    + subst qx. exfalso. unfold rq_sub in Hrq.
      destruct Hrq as [Hx | [Hx | [Hx _]]]; discriminate.
    + destruct Hmb as [-> | ->].
      * assert (qx = Mut).
        { unfold rq_sub in Hrq2. simpl in Hrq2.
          destruct Hrq2 as [Hx | [Hx | [Hx _]]]; congruence. }
        subst qx. simpl in Hl2.
        assert (HnX : ~ deadA CT (LT Mut lx Cx Asx)).
        { intros Hd. exact (lsubtp_dead CT L _ _ Hwf HAX Hd Hnd). }
        assert (HsX : ~ insaneA CT (LT Mut lx Cx Asx)).
        { intros (_ & di & Hdi & Himm). apply Hsn. split; auto.
          exact (view_imm _ _ _ _ _ _ _ _ _ Hwf Hva' di Hdi Himm). }
        specialize (Hc Hb HnX HsX). simpl in Hc.
        pose proof (pcoh_lm _ _ _ _ _ _ _ _ (Hl2 eq_refl) (Hc eq_refl Vx Hvx)) as Hp.
        assert (Hr : rrel L Mut (ArgViews.tg Mut) lA Mut (ArgViews.tg Mut) lx).
        { apply tg_rrel; [left; reflexivity | right; right; exact (Hl eq_refl)]. }
        unfold tview in *.
        destruct (view_transfer _ _ _ _ _ _ _ _ Hvx true Mut (ArgViews.tg Mut) lA Va')
          as (W & Hw).
        assert (Va = W).
        { exact (view_deterministic _ _ _ _ _ _ _ _ _ Hwf Hva _
                   (view_trans _ _ _ _ _ _ _ _ _ Hva' _ _ Hw)). }
        subst Va.
        eapply pcoh_agree; [exact Hwf | exact (Hl eq_refl) | | exact Hp].
        exact (view_agree _ _ _ _ _ _ _ _ _ Hwf Hw L _ _ _ _ _ (gok_tg _)
                 (gok_tg _) Hr (vpok_type _ _ _ _ _ _ _ _ _ _) Hle Hvx).
      * exfalso. simpl in Hrq2. unfold rq_sub in Hrq2, Hrq.
        destruct Hrq2 as [Hx | [Hx | [Hx _]]]; try discriminate. subst qx.
        destruct Hrq as [Hx | [Hx | [Hx _]]]; discriminate.
  - exfalso. exact (lsubtp_dead CT L _ _ Hwf HAX Hd Hnd).
  - exfalso. destruct Hi as (_ & di & Hdi & Himm). apply Hsn. split; auto.
    exact (view_imm _ _ _ _ _ _ _ _ _ Hwf Hva' di Hdi Himm).
Qed.

(** One static subtyping fact, read for a labelled source: it fits, or it is
    a type no value can have. *)
Definition fit3p (CT : class_table) (L : list nat) (A X : ltype) : Prop :=
  lsubtp CT L A X \/ deadA CT A \/ (insaneA CT A /\ lsubtp CT L (lbot A) X).

Lemma fit3p_agree : forall CT L A X Y,
  fit3p CT L A X -> lagree L X Y -> fit3p CT L A Y.
Proof.
  intros CT L A X Y [H | [H | [Hi H]]] Hxy.
  - left. eapply lsubtp_agree_r; eauto.
  - right. left. exact H.
  - right. right. split; auto. eapply lsubtp_agree_r; eauto.
Qed.

Lemma deadA_lbot : forall CT A, deadA CT (lbot A) -> deadA CT A.
Proof. intros CT [q0 l C As] H. exact H. Qed.

Lemma insaneA_lbot : forall CT A, ~ insaneA CT (lbot A).
Proof. intros CT [q0 l C As] (Hx & _). discriminate. Qed.

Lemma cohT_lbot : forall CT L Δ F A T, cohT CT L Δ F (lbot A) T.
Proof. intros CT L Δ F [q0 l C As] T. simpl. intros Hx. discriminate. Qed.

(* ------------------A QUALIFIED USE AT ITS BOUND'S CLASS------------------*)

(** Readonly positions of one reading are readonly in another. *)
Inductive lro : ltype -> ltype -> Prop :=
  | lro_node : forall q1 l1 q2 l2 C As Bs
      (Hq : q2 = RO -> q1 = RO)
      (Hargs : Forall2 lro As Bs),
      lro (LT q1 l1 C As) (LT q2 l2 C Bs).

Lemma lagree_lro : forall L A B, lagree L A B -> lro A B.
Proof.
  intros L A B H. induction H using lagree_ind'. constructor.
  - intros ->. unfold arg_q_sub in H. destruct H as [Hx | [Hx _]]; congruence.
  - induction H2; constructor; auto.
Qed.

Lemma lro_refl : forall A, lro A A.
Proof.
  intros A. induction A using ltype_ind'. constructor; auto.
  induction H; constructor; auto.
Qed.

Lemma lro_node_q : forall qA pn lA h lh q0 C As Bs Xs Ys,
  Forall2 lro As Bs ->
  lro (LT (dynq qA (rd_map true (ArgViews.tg qA) pn q0))
          (lab_of (hframe qA lA pn Xs) (rd_map true (ArgViews.tg qA) pn q0)) C As)
      (LT (dynq h (tg h q0)) (lab_of (tframe h lh Ys) (tg h q0)) C Bs).
Proof.
  intros qA pn lA h lh q0 C As Bs Xs Ys Hargs. constructor; auto. intros Hro.
  assert (q0 = RO) by (destruct q0, h; simpl in Hro; congruence). subst q0.
  destruct pn as [[qp lp]|]; [destruct qp|]; destruct qA; reflexivity.
Qed.

Lemma lro_ldyn : forall qA lA pn h lh As Bs S,
  Forall2 lro As Bs ->
  lro (ldyn (hframe qA lA pn As) (map_qual (rd_map true (ArgViews.tg qA) pn) S))
      (ldyn (tframe h lh Bs) (map_qual (tg h) S)).
Proof.
  intros qA lA pn h lh As Bs S Hargs. induction S using qualified_type_ind'.
  - cbn [map_qual ldyn hframe tframe lf_q]. apply lro_node_q.
    rewrite !map_map. induction H; simpl; constructor; auto.
  - assert (HA : lro
              match tv_lookup o As [] n with Some A => A | None => ldefault end
              match tv_lookup o Bs [] n with Some A => A | None => ldefault end).
    { pose proof (tv_lookup_Forall2 lro o As Bs [] [] n Hargs (Forall2_nil _)) as Hx.
      destruct (tv_lookup o As [] n), (tv_lookup o Bs [] n); try contradiction;
        auto using lro_refl. }
    destruct u as [|q0|m]; cbn [ldyn hframe tframe lf_q lf_cargs lf_margs lf_qargs map_qual].
    + exact HA.
    + destruct (match tv_lookup o As [] n with Some A => A | None => ldefault end)
        as [q1 l1 C1 As1].
      destruct (match tv_lookup o Bs [] n with Some A => A | None => ldefault end)
        as [q2 l2 C2 As2].
      inversion HA; subst. simpl. apply lro_node_q; auto.
    + destruct (match tv_lookup o As [] n with Some A => A | None => ldefault end)
        as [q1 l1 C1 As1].
      destruct (match tv_lookup o Bs [] n with Some A => A | None => ldefault end)
        as [q2 l2 C2 As2].
      inversion HA; subst. destruct m; simpl; constructor; auto.
  - cbn [ldyn hframe tframe lf_qargs map_qual]. destruct n; simpl; constructor; auto;
      rewrite !map_map; induction H; simpl; constructor; auto.
Qed.

Lemma lro_step : forall qA lA pn h lh As Bs Ss,
  Forall2 lro As Bs ->
  Forall2 lro (hstep true qA (ArgViews.tg qA) lA pn As Ss) (tstep h lh Bs Ss).
Proof. intros. unfold hstep, tstep. induction Ss; simpl; constructor; auto using lro_ldyn. Qed.

Lemma lta_le : forall CT C As D Vs,
  wf_class_table CT -> ltsuper_any CT C As D Vs -> D <= C.
Proof.
  intros CT C As D Vs Hwf H. induction H; auto.
  pose proof (parent_lt _ _ _ _ Hwf Hparent). lia.
Qed.

Lemma lro_view : forall CT qA lA C As D Va,
  wf_class_table CT ->
  view CT true qA (ArgViews.tg qA) lA C As D Va ->
  forall Bs Vs, ltsuper_any CT C Bs D Vs -> Forall2 lro As Bs -> Forall2 lro Va Vs.
Proof.
  intros CT qA lA C As D Va Hwf H.
  induction H; intros Bs Ws H2 Hr.
  - inversion H2; subst; auto.
    exfalso. pose proof (lta_le _ _ _ _ _ Hwf Hrest) as Hle.
    pose proof (parent_lt _ _ _ _ Hwf Hparent). lia.
  - inversion H2; subst.
    + exfalso. pose proof (view_le _ _ _ _ _ _ _ _ _ Hwf H) as Hle.
      pose proof (parent_lt _ _ _ _ Hwf Hparent). lia.
    + rewrite Hparent in Hparent0. inversion Hparent0; subst.
      eapply IHview; eauto. apply lro_step; auto.
Qed.

(** A view along a chain another reader follows, for arguments of the same
    number. *)
Lemma view_of_lta : forall CT C Bs D Vs,
  ltsuper_any CT C Bs D Vs ->
  forall k hq g d As, length As = length Bs ->
    exists Va, view CT k hq g d C As D Va /\ length Va = length Vs.
Proof.
  intros CT C Bs D Vs H. induction H; intros k hq g d As0 Hlen.
  - exists As0. split; [apply v_refl | exact Hlen].
  - destruct (IHltsuper_any k hq g d (hstep k hq g d (vpay k CT C As0) As0 Ss))
      as (Va & Hv & Hl).
    { unfold hstep, tstep. rewrite !length_map. reflexivity. }
    exists Va. split; auto. eapply v_step; eauto.
Qed.

(* ------------------THE SAME ALONG THE BOTTOM READER------------------*)

Lemma lro_node_b : forall qA pn lA q0 C As Bs Xs Ys,
  Forall2 lro As Bs ->
  lro (LT (dynq qA (rd_map true (ArgViews.tg qA) pn q0))
          (lab_of (hframe qA lA pn Xs) (rd_map true (ArgViews.tg qA) pn q0)) C As)
      (LT (dynq Bot (bq q0)) (lab_of (bframe Ys) (bq q0)) C Bs).
Proof.
  intros qA pn lA q0 C As Bs Xs Ys Hargs. constructor; auto. intros Hro.
  assert (q0 = RO) by (destruct q0; simpl in Hro; congruence). subst q0.
  destruct pn as [[qp lp]|]; [destruct qp|]; destruct qA; reflexivity.
Qed.

Lemma lro_ldyn_b : forall qA lA pn As Bs S,
  Forall2 lro As Bs ->
  lro (ldyn (hframe qA lA pn As) (map_qual (rd_map true (ArgViews.tg qA) pn) S))
      (ldyn (bframe Bs) (map_qual bq S)).
Proof.
  intros qA lA pn As Bs S Hargs. induction S using qualified_type_ind'.
  - cbn [map_qual ldyn hframe bframe lf_q]. apply lro_node_b.
    rewrite !map_map. induction H; simpl; constructor; auto.
  - assert (HA : lro
              match tv_lookup o As [] n with Some A => A | None => ldefault end
              match tv_lookup o Bs [] n with Some A => A | None => ldefault end).
    { pose proof (tv_lookup_Forall2 lro o As Bs [] [] n Hargs (Forall2_nil _)) as Hx.
      destruct (tv_lookup o As [] n), (tv_lookup o Bs [] n); try contradiction;
        auto using lro_refl. }
    destruct u as [|q0|m]; cbn [ldyn hframe bframe lf_q lf_cargs lf_margs lf_qargs map_qual].
    + exact HA.
    + destruct (match tv_lookup o As [] n with Some A => A | None => ldefault end)
        as [q1 l1 C1 As1].
      destruct (match tv_lookup o Bs [] n with Some A => A | None => ldefault end)
        as [q2 l2 C2 As2].
      inversion HA; subst. simpl. apply lro_node_b; auto.
    + destruct (match tv_lookup o As [] n with Some A => A | None => ldefault end)
        as [q1 l1 C1 As1].
      destruct (match tv_lookup o Bs [] n with Some A => A | None => ldefault end)
        as [q2 l2 C2 As2].
      inversion HA; subst. destruct m; simpl; constructor; auto.
  - cbn [ldyn hframe bframe lf_qargs map_qual]. destruct n; simpl; constructor; auto;
      rewrite !map_map; induction H; simpl; constructor; auto.
Qed.

Lemma lro_step_b : forall qA lA pn As Bs Ss,
  Forall2 lro As Bs ->
  Forall2 lro (hstep true qA (ArgViews.tg qA) lA pn As Ss) (bstep Bs Ss).
Proof. intros. unfold hstep, bstep. induction Ss; simpl; constructor; auto using lro_ldyn_b. Qed.

Lemma lbs_le : forall CT C As D Vs,
  wf_class_table CT -> lbsuper CT C As D Vs -> D <= C.
Proof.
  intros CT C As D Vs Hwf H. induction H; auto.
  pose proof (parent_lt _ _ _ _ Hwf Hparent). lia.
Qed.

Lemma lro_view_b : forall CT qA lA C As D Va,
  wf_class_table CT ->
  view CT true qA (ArgViews.tg qA) lA C As D Va ->
  forall Bs Vs, lbsuper CT C Bs D Vs -> Forall2 lro As Bs -> Forall2 lro Va Vs.
Proof.
  intros CT qA lA C As D Va Hwf H.
  induction H; intros Bs Ws H2 Hr.
  - inversion H2; subst; auto.
    exfalso. pose proof (lbs_le _ _ _ _ _ Hwf Hrest) as Hle.
    pose proof (parent_lt _ _ _ _ Hwf Hparent). lia.
  - inversion H2; subst.
    + exfalso. pose proof (view_le _ _ _ _ _ _ _ _ _ Hwf H) as Hle.
      pose proof (parent_lt _ _ _ _ Hwf Hparent). lia.
    + rewrite Hparent in Hparent0. inversion Hparent0; subst.
      eapply IHview; eauto. apply lro_step_b; auto.
Qed.

Lemma view_of_lbs : forall CT C Bs D Vs,
  lbsuper CT C Bs D Vs ->
  forall k hq g d As, length As = length Bs ->
    exists Va, view CT k hq g d C As D Va /\ length Va = length Vs.
Proof.
  intros CT C Bs D Vs H. induction H; intros k hq g d As0 Hlen.
  - exists As0. split; [apply v_refl | exact Hlen].
  - destruct (IHlbsuper k hq g d (hstep k hq g d (vpay k CT C As0) As0 Ss))
      as (Va & Hv & Hl).
    { unfold hstep, bstep. rewrite !length_map. reflexivity. }
    exists Va. split; auto. eapply v_step; eauto.
Qed.

(** The payload view of a labelled type is the head view of the earlier
    layer, which takes no payload either. *)
Lemma tview_of_ltsuper : forall CT q0 l C As D Vs,
  ltsuper CT q0 l C As D Vs -> tview CT q0 l C As D Vs.
Proof.
  intros CT q0 l C As D Vs H. unfold tview. induction H.
  - apply v_refl.
  - eapply v_step; [exact Hparent|]. cbn [vpay]. rewrite <- tstep_hstep. exact IHltsuper.
Qed.

Lemma lsubtp_of_lsubt : forall CT L A B, lsubt CT L A B -> lsubtp CT L A B.
Proof.
  intros CT L [q1 l1 C As] [q2 l2 D Bs] H.
  destruct H as [(-> & Vs & Hv & Hle) | (Hrq & Hl & Vs & Hv & Hle)].
  - left. split; [reflexivity|].
    destruct (view_of_lbs _ _ _ _ _ Hv true Bot (ArgViews.tg Bot) l1 As eq_refl)
      as (Va & Hva & Hlen).
    exists Va. split; [exact Hva|]. rewrite Hlen. exact (Forall2_length Hle).
  - right. refine (conj Hrq (conj Hl _)).
    exists Vs. split; [apply tview_of_ltsuper; exact Hv | exact Hle].
Qed.

(** Forgetting a bound's arguments covers every reading readonly where the
    bound's argument is, with the bottom escape. *)
Lemma lro_bwiden : forall L L' F T a s,
  class_only_b T = true ->
  lro a s -> bagree L' s (ldyn F T) ->
  lagree L a (ldyn F (widen_args T)).
Proof.
  intros L L' F T. induction T using qualified_type_ind';
    intros a s Hco Hro Hle; simpl in Hco; try discriminate.
  cbn [ldyn widen_args] in Hle |- *.
  destruct a as [q1 l1 C1 As1]. destruct s as [q2 l2 C2 As2].
  inversion Hle as [? ? ? ? ? ? ? Hq Hlab Hargs]; subst.
  inversion Hro as [? ? ? ? ? ? ? Hq' Hargs']; subst.
  assert (Htgt : dynq (lf_q F) (widen_q qual) = Lost \/
                 (qual = RO /\ dynq (lf_q F) (widen_q qual) = RO)).
  { destruct qual; simpl; auto. }
  assert (Hro1 : qual = RO -> q1 = RO).
  { intros ->. apply Hq'. simpl in Hq.
    destruct Hq as [[_ Hx] | Hq]; [congruence|].
    unfold arg_q_sub in Hq. destruct Hq as [Hx | [Hx _]]; congruence. }
  constructor.
  - destruct Htgt as [-> | [-> ->]].
    + unfold arg_q_sub. destruct q1; auto 8.
    + rewrite (Hro1 eq_refl). left. reflexivity.
  - destruct Htgt as [-> | [-> ->]]; [left; reflexivity|].
    right. left. rewrite (Hro1 eq_refl). discriminate.
  - clear Hle Hro Hq Hlab Hq' Htgt Hro1. revert As1 As2 Hargs Hargs'.
    induction H; intros As1 As2 H1 H2; simpl in *.
    + inversion H1; subst. inversion H2; subst. constructor.
    + apply andb_prop in Hco as [Hx Hl]. inversion H1; subst. inversion H2; subst.
      constructor; eauto.
Qed.

(** Forgetting a bound's arguments covers every reading readonly where the
    bound's argument is. *)
Lemma lro_widen : forall L L' F T a s,
  class_only_b T = true ->
  lro a s -> lagree L' s (ldyn F T) ->
  lagree L a (ldyn F (widen_args T)).
Proof.
  intros L L' F T. induction T using qualified_type_ind';
    intros a s Hco Hro Hle; simpl in Hco; try discriminate.
  cbn [ldyn widen_args] in Hle |- *.
  destruct a as [q1 l1 C1 As1]. destruct s as [q2 l2 C2 As2].
  inversion Hle as [? ? ? ? ? ? ? Hq Hlab Hargs]; subst.
  inversion Hro as [? ? ? ? ? ? ? Hq' Hargs']; subst.
  constructor.
  - destruct qual; simpl;
      first [ assert (q2 = RO) by (unfold arg_q_sub in Hq; destruct Hq as [Hx | [Hx _]];
                                   simpl in Hx; congruence);
              rewrite (Hq' H0); left; reflexivity
            | unfold arg_q_sub; destruct q1; first [left; reflexivity | right; split; auto 6] ].
  - destruct qual; simpl; try (left; reflexivity).
    right. left. rewrite (Hq' ltac:(unfold arg_q_sub in Hq; destruct Hq as [Hx | [Hx _]];
                                    simpl in Hx; congruence)). discriminate.
  - clear Hle Hro Hq Hlab Hq'. revert As1 As2 Hargs Hargs'.
    induction H; intros As1 As2 H1 H2; simpl in *.
    + inversion H1; subst. inversion H2; subst. constructor.
    + apply andb_prop in Hco as [Hx Hl]. inversion H1; subst. inversion H2; subst.
      constructor; eauto.
Qed.

(** A typing derivation, followed from a labelled source that is kept
    throughout: steps that forget part of a type cannot lose what a later
    step up the hierarchy needs.  The coherence of the source is asked only
    where a type written mutable can be derived, and is handed on. *)
Lemma sub_lsubtp : forall CT Δ L F,
  wf_class_table CT ->
  readonly_state_method_scope (tv_mode Δ) ->
  (lf_q F = Mut \/ lf_q F = Imm) ->
  (forall o n B, tv_bound Δ o n = Some B -> is_class_type B) ->
  frame_fits CT L Δ F ->
  frame_fitsp CT L Δ F ->
  (forall o n B A, tv_bound Δ o n = Some B -> headmb B ->
     ~ deadA CT A -> ~ insaneA CT A ->
     lsubtp CT L A (ldyn F (TVar TVSub o n)) -> cohT CT L Δ F A B) ->
  forall T U, qualified_type_subtype CT Δ T U ->
    forall A, ~ deadA CT A -> ~ insaneA CT A ->
      (reachm Δ T -> cohT CT L Δ F A T) ->
      lsubtp CT L A (ldyn F T) ->
      lsubtp CT L A (ldyn F U) /\ (reachm Δ U -> cohT CT L Δ F A U).
Proof.
  intros CT Δ L F Hwf Hrs Hq Hbc Hfits0 Hfit Hvb T U Hsub.
  induction Hsub; intros A Hnd Hsn Hc H.
  - (* same class *)
    split.
    + cbn [ldyn] in H |- *. eapply lsubtp_head; eauto.
      apply map_ldyn_targ_sub. exact Hargs.
    + intros Hr. destruct A as [qA lA CA AsA]. simpl in Hr |- *.
      exact (Hc (q_subtype_mb _ _ Hqsub Hr)).
  - (* up the hierarchy *)
    cbn [ldyn] in H. destruct A as [qA lA CA AsA].
    destruct (q_eq_dec qA Bot) as [-> | HqA].
    + split; [|intros _ Hx; discriminate].
      cbn [ldyn]. left. split; [reflexivity|].
      assert (Hv : exists Va, tview CT Bot lA CA AsA C Va /\
                              length Va = length Ts).
      { destruct H as [(_ & Va & Hva & Hl) | (_ & _ & Va & Hva & Hl)].
        - exists Va. split; auto. rewrite Hl. apply length_map.
        - exists Va. split; auto. rewrite (Forall2_length Hl). apply length_map. }
      destruct Hv as (Va & Hva & Hl).
      destruct (static_view_len _ _ _ _ _ _ _ Hsuper true Bot (ArgViews.tg Bot)
                  lA Va Hl) as (Vs' & Hv' & Hl').
      exists Vs'. split.
      * unfold tview in *. eapply view_trans; eauto.
      * rewrite Hl'. symmetry. apply length_map.
    + destruct H as [(Hb & _) | (Hrq & Hl & Va & Hva & Hle)]; [contradiction|].
      assert (Hpc : q1 = Mut -> qA = Mut /\ norm L lA = norm L (lf_mut F) /\
                    pcoh CT L qA lA C Va (lf_mut F)).
      { intros ->. simpl in Hrq, Hl.
        assert (qA = Mut).
        { unfold rq_sub in Hrq. destruct Hrq as [Hx | [Hx | [Hx _]]]; congruence. }
        subst qA. pose proof (Hc (or_introl eq_refl)) as Hc'. simpl in Hc'.
        refine (conj eq_refl (conj (Hl eq_refl) _)).
        exact (Hc' eq_refl (Hl eq_refl) Va Hva). }
      destruct (tview_vs_static _ _ _ _ _ _ _ Hsuper L F qA lA Va Hrs)
        as (V' & Hv' & Hle'); auto.
      * intros As0 cs ms ks.
        eapply lc2_trans.
        -- exact (mono_cond L qA lA (dynq (lf_q F) q1) (lab_of F q1) HqA Hrq Hl
                    As0 As0).
        -- exact (hier_cond L (tv_mode Δ) F q1 As0 cs ms _ Hrs Hq).
      * intros Hm. exact (proj2 (proj2 (Hpc Hm))).
      * split.
        -- cbn [ldyn]. right. refine (conj Hrq (conj Hl _)).
           exists V'. split; auto. unfold tview in *. eapply view_trans; eauto.
        -- intros Hr. simpl in Hr |- *. intros HqM HlM Vd Hvd.
           subst qA.
           assert (Hq1 : q1 = Mut).
           { destruct Hr as [Hx | Hx]; auto. subst q1. simpl in Hrq.
             unfold rq_sub in Hrq. destruct Hrq as [Hx | [Hx | [Hx _]]]; discriminate. }
           destruct (Hpc Hq1) as (_ & _ & Hp).
           assert (Vd = V').
           { unfold tview in *.
             exact (view_deterministic _ _ _ _ _ _ _ _ _ Hwf Hvd _
                      (view_trans _ _ _ _ _ _ _ _ _ Hva _ _ Hv')). }
           subst Vd. eapply pcoh_view; eauto.
  - split; [exact H | exact Hc].
  - (* a type variable at its bound *)
    split.
    + destruct (Hfit _ _ _ Hbound) as [Hf | [Hd | [Hi Hf]]].
      * eapply lsubtp_trans; [exact Hwf | exact H | exact Hf].
      * exfalso. exact (lsubtp_dead CT L _ _ Hwf H Hd Hnd).
      * (* the supplied type has no values: the source is headed bottom *)
        destruct A as [qA lA CA AsA].
        destruct (ldyn F (TVar TVSub o n)) as [qa la Ca Aa].
        destruct Hi as (-> & di & Hdi & Himm).
        assert (HqA : qA = Bot).
        { destruct H as [(Hb & _) | (Hrq & _ & Va & Hva & _)]; auto.
          exfalso. apply Hsn. simpl.
          assert (qA = Mut).
          { unfold rq_sub in Hrq. destruct Hrq as [Hx | [Hx | [Hx _]]]; congruence. }
          split; auto.
          exact (view_imm _ _ _ _ _ _ _ _ _ Hwf Hva di Hdi Himm). }
        subst qA.
        eapply lsubtp_trans; [exact Hwf | | exact Hf].
        simpl. left. split; auto.
        destruct H as [(_ & Va & Hva & Hl) | (_ & _ & Va & Hva & Hl)].
        -- eauto.
        -- exists Va. split; auto. exact (Forall2_length Hl).
    + intros Hr. apply (Hvb _ _ _ A Hbound); auto.
      pose proof (Hbc _ _ _ Hbound) as Hcl.
      destruct B as [qb Cb Bsb|u0 o0 n0| ? ? ?]; [exact Hr | contradiction..].
  - (* widen the written qualifier of a variable use *)
    split.
    + cbn [ldyn] in H |- *.
      destruct (match tv_lookup o (lf_cargs F) (lf_margs F) n with
                | Some A0 => A0 | None => ldefault end) as [qa la Ca Aa].
      simpl lrehead in H |- *.
      eapply lsubtp_head; eauto. apply Forall2_lagree_refl.
    + intros Hr. destruct A as [qA lA CA AsA]. simpl in Hr |- *.
      exact (Hc (q_subtype_mb _ _ Hqsub Hr)).
  - (* view the supplied type as readonly *)
    split; [|intros Hr; simpl in Hr; destruct Hr; discriminate].
    cbn [ldyn] in H |- *.
    destruct (match tv_lookup o (lf_cargs F) (lf_margs F) n with
              | Some A0 => A0 | None => ldefault end) as [qa la Ca Aa].
    simpl lrehead. destruct A as [qA lA CA AsA].
    destruct H as [(Hb & Vs & Hv & Hlen) | (Hrq & Hl & Vs & Hv & Hle)].
    + left. split; auto. exists Vs. split; auto.
    + right. refine (conj _ (conj _ _)).
      * right. left. reflexivity.
      * intros Hm. discriminate.
      * exists Vs. split; auto.
  - split; [exact H | exact Hc].
  - (* a use under a qualifier parameter, viewed as readonly *)
    split; [|intros Hr; simpl in Hr; destruct Hr; discriminate].
    cbn [ldyn] in H |- *.
    destruct (match tv_lookup o (lf_cargs F) (lf_margs F) n with
              | Some A0 => A0 | None => ldefault end) as [qa la Ca Aa].
    simpl lrehead in H |- *. destruct A as [qA lA CA AsA].
    destruct H as [(Hb & Vs & Hv & Hlen) | (Hrq & Hl & Vs & Hv & Hle)].
    + left. split; auto. exists Vs. split; auto.
    + right. refine (conj _ (conj _ _)).
      * right. left. reflexivity.
      * intros Hm. discriminate.
      * exists Vs. split; auto.
  - (* a qualified variable use at a bound, forgetting its arguments *)
    cbn [ldyn] in H |- *.
    destruct (match tv_lookup o (lf_cargs F) (lf_margs F) n with
              | Some A0 => A0 | None => ldefault end) as [qa la Ca Aa] eqn:HA0.
    simpl lrehead in H.
    (* the supplied argument's view at the bound's class *)
    pose proof (sub_lsubt CT Δ L F Hrs Hq Hfits0 _ _ Hsub) as Hsl.
    cbn [ldyn] in Hsl. rewrite HA0 in Hsl. unfold lsubt in Hsl.
    destruct (lsubt_lb _ _ _ _ _ _ _ _ _ _ Hsl) as (Vs & Hvs & Hle).
    destruct A as [qA lA CA AsA].
    split.
    + destruct H as [(Hb & Vca & Hvca & Hlen) | (Hrq & Hl & Vca & Hvca & Hlea)].
      * left. split; auto.
        destruct (view_of_lbs _ _ _ _ _ Hvs true qA (ArgViews.tg qA) lA Vca
                    (eq_trans Hlen eq_refl)) as (Va & Hva & HlVa).
        exists Va. split.
        -- unfold tview in *. eapply view_trans; eauto.
        -- rewrite HlVa. rewrite (Forall2_length Hle). rewrite !length_map. reflexivity.
      * right. refine (conj Hrq (conj Hl _)).
        destruct (view_of_lbs _ _ _ _ _ Hvs true qA (ArgViews.tg qA) lA Vca
                    (Forall2_length Hlea)) as (Va & Hva & _).
        exists Va. split.
        -- unfold tview in *. eapply view_trans; eauto.
        -- assert (Hlro : Forall2 lro Vca Aa).
           { eapply Forall2_impl; [|exact Hlea]. intros a b Hab. eapply lagree_lro; eauto. }
           pose proof (lro_view_b _ _ _ _ _ _ _ Hwf Hva Aa Vs Hvs Hlro) as Hro.
           clear - Hro Hle Hcls. revert Va Vs Hro Hle.
           induction Ts as [|T Ts IH]; intros Va Vs Hro Hle; simpl in *.
           ++ inversion Hle; subst. inversion Hro; subst. constructor.
           ++ apply andb_prop in Hcls as [HT HTs]. inversion Hle; subst.
              inversion Hro; subst. constructor; [eapply lro_bwiden; eauto | eapply IH; eauto].
    + intros Hr. simpl. intros HqM HlM Va Hva.
      exact (Hc Hr HqM HlM qb C Ts Hsub Va Hva).
  - (* a variable-headed class type viewed as readonly *)
    split; [|intros Hr; simpl in Hr; destruct Hr; discriminate].
    cbn [ldyn] in H |- *.
    remember (fst (lqnth (lf_qargs F) n)) as qa eqn:Hqa0.
    remember (snd (lqnth (lf_qargs F) n)) as la eqn:Hla0.
    idtac. destruct A as [qA lA CA AsA].
    assert (Hlen : length (map (ldyn F) Ts) = length (map (ldyn F) Us)).
    { rewrite !length_map. apply (Forall2_length Hargs). }
    destruct H as [(Hb & Vs & Hv & Hl) | (Hrq & Hl & Vs & Hv & Hle)].
    + left. split; auto. exists Vs. split; auto. congruence.
    + right. refine (conj _ (conj _ _)).
      * right. left. reflexivity.
      * intros Hm. discriminate.
      * exists Vs. split; auto.
        eapply Forall2_lagree_trans; [exact Hle|].
        apply map_ldyn_targ_sub. exact Hargs.
  - (* compatible arguments under the same variable head *)
    split; [|intros Hr; simpl in Hr; contradiction].
    cbn [ldyn] in H |- *.
    remember (fst (lqnth (lf_qargs F) n)) as qa eqn:Hqa0.
    remember (snd (lqnth (lf_qargs F) n)) as la eqn:Hla0.
    idtac.
    eapply lsubtp_agree_r; [exact H|].
    constructor; [left; reflexivity | right; right; reflexivity |].
    apply map_ldyn_targ_sub. exact Hargs.
  - (* up the hierarchy under the same variable head *)
    split; [|intros Hr; simpl in Hr; contradiction].
    cbn [ldyn] in H |- *.
    remember (fst (lqnth (lf_qargs F) n)) as qa eqn:Hqa0.
    remember (snd (lqnth (lf_qargs F) n)) as la eqn:Hla0.
    idtac. destruct A as [qA lA CA AsA].
    destruct (q_eq_dec qA Bot) as [-> | HqA].
    + left. split; [reflexivity|].
      assert (Hv : exists Va, tview CT Bot lA CA AsA C Va /\
                              length Va = length Ts).
      { destruct H as [(_ & Va & Hva & Hl) | (_ & _ & Va & Hva & Hl)].
        - exists Va. split; auto. rewrite Hl. apply length_map.
        - exists Va. split; auto. rewrite (Forall2_length Hl). apply length_map. }
      destruct Hv as (Va & Hva & Hl).
      destruct (static_view_len _ _ _ _ _ _ _ Hsuper true Bot (ArgViews.tg Bot)
                  lA Va Hl) as (Vs' & Hv' & Hl').
      exists Vs'. split.
      * unfold tview in *. eapply view_trans; eauto.
      * rewrite Hl'. symmetry. apply length_map.
    + destruct H as [(Hb & _) | (Hrq & Hl & Va & Hva & Hle)]; [contradiction|].
      destruct (tview_vs_static _ _ _ _ _ _ _ Hsuper L F qA lA Va Hrs)
        as (V' & Hv' & Hle'); auto.
      * intros As0 cs ms ks.
        exact (head_ro_cond L (tv_mode Δ) F qA lA As0 cs ms _ Hrs Hq HqA).
      * intros Hm. discriminate.
      * right. refine (conj Hrq (conj Hl _)).
        exists V'. split; auto. unfold tview in *. eapply view_trans; eauto.
  - (* the bottom-qualified type of the class *)
    split; [|intros Hr; simpl in Hr; contradiction].
    cbn [ldyn] in H |- *.
    remember (fst (lqnth (lf_qargs F) n)) as qa eqn:Hqa0.
    remember (snd (lqnth (lf_qargs F) n)) as la eqn:Hla0.
    idtac. destruct A as [qA lA CA AsA].
    assert (Hlen : length (map (ldyn F) Ts) = length (map (ldyn F) Us)).
    { rewrite !length_map. apply (Forall2_length Hargs). }
    assert (HqA : qA = Bot).
    { destruct H as [(Hb & _) | (Hrq & _)]; auto.
      unfold rq_sub in Hrq. simpl in Hrq.
      destruct Hrq as [Hx | [Hx | [Hx _]]]; congruence. }
    subst qA. left. split; [reflexivity|].
    destruct H as [(_ & Va & Hva & Hl) | (_ & _ & Va & Hva & Hl)].
    + exists Va. split; auto. congruence.
    + exists Va. split; auto. rewrite (Forall2_length Hl). exact Hlen.
  - (* transitivity *)
    assert (Hc1 : reachm Δ T1 -> cohT CT L Δ F A T1) by exact Hc.
    destruct (IHHsub1 A Hnd Hsn Hc1 H) as [H2 Hc2].
    exact (IHHsub2 A Hnd Hsn Hc2 H2).
Qed.

Print Assumptions lsubtp_sound.
Print Assumptions tview_vs_static.
Print Assumptions pclassf_fit.
Print Assumptions fit_ex.
Print Assumptions lsubtp_trans.
Print Assumptions sub_lsubtp.
