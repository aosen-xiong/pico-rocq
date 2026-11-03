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

(** Place in the proof: an object fits its class bounds in the labelled
    reading.  The view of a labelled type at a superclass, the bottom reader,
    soundness, labelled subtyping, fits against opened bounds, and killing (the
    closing of a world) as a static homomorphism.
    Counterpart in the non-generic proof (ReadonlyWorlds.v): "transport of the
    invariant", the opening and closing of worlds. *)
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

(** A view in which every inheritance step may read the header through its
    own head and label.  A bottom-headed type, which only null inhabits, is
    below every type that some such view reaches. *)
Inductive ltsuper_any (CT : class_table)
    : class_name -> list ltype -> class_name -> list ltype -> Prop :=
  | lta_refl : forall C As, ltsuper_any CT C As C As
  | lta_step : forall qA lA C As P Ss D Vs
      (Hparent : parent_lookup CT C = Some (P, Ss))
      (Hrest : ltsuper_any CT P (tstep qA lA As Ss) D Vs),
      ltsuper_any CT C As D Vs.

(* ------------------THE BOTTOM READER------------------*)

(** A bottom-headed type has no object behind it.  Its view reads a header's
    written mutable and receiver-dependent positions as bottom: they hold
    nothing. *)
Definition bq (q0 : q) : q :=
  match q0 with Mut | RDM => Bot | _ => q0 end.

Definition bframe (As : list ltype) : lframe := mk_lframe Bot LOut LOut As [] [].

Definition bstep (As : list ltype) (Ss : list qualified_type) : list ltype :=
  map (fun S => ldyn (bframe As) (map_qual bq S)) Ss.

Inductive lbsuper (CT : class_table)
    : class_name -> list ltype -> class_name -> list ltype -> Prop :=
  | lbs_refl : forall C As, lbsuper CT C As C As
  | lbs_step : forall C As P Ss D Vs
      (Hparent : parent_lookup CT C = Some (P, Ss))
      (Hrest : lbsuper CT P (bstep As Ss) D Vs),
      lbsuper CT C As D Vs.

Lemma lbsuper_trans : forall CT C As D Vs E Ws,
  lbsuper CT C As D Vs -> lbsuper CT D Vs E Ws -> lbsuper CT C As E Ws.
Proof.
  intros CT C As D Vs E Ws H. revert E Ws. induction H; intros E0 Ws0 H2; auto.
  eapply lbs_step; eauto.
Qed.

(** Agreement with a bottom escape: a bottom-headed node stands for nothing
    and agrees with any node of its class that is not readonly; every other
    node agrees as in [lagree]. *)
Inductive bagree (L : list nat) : ltype -> ltype -> Prop :=
  | ba_node : forall q1 l1 q2 l2 C As Bs
      (Hq : (q1 = Bot /\ q2 <> RO) \/ arg_q_sub q1 q2)
      (Hlab : q2 = Lost \/ q1 <> Mut \/ norm L l1 = norm L l2)
      (Hargs : Forall2 (bagree L) As Bs),
      bagree L (LT q1 l1 C As) (LT q2 l2 C Bs).

Section bagree_ind'.
  Variable L : list nat.
  Variable P : ltype -> ltype -> Prop.
  Hypothesis Hnode : forall q1 l1 q2 l2 C As Bs,
    ((q1 = Bot /\ q2 <> RO) \/ arg_q_sub q1 q2) ->
    (q2 = Lost \/ q1 <> Mut \/ norm L l1 = norm L l2) ->
    Forall2 (bagree L) As Bs ->
    Forall2 P As Bs ->
    P (LT q1 l1 C As) (LT q2 l2 C Bs).

  Fixpoint bagree_ind' A B (H : bagree L A B) : P A B :=
    match H with
    | ba_node _ q1 l1 q2 l2 C As Bs Hq Hlab Hargs =>
        Hnode q1 l1 q2 l2 C As Bs Hq Hlab Hargs
          ((fix go As Bs (Hl : Forall2 (bagree L) As Bs) : Forall2 P As Bs :=
              match Hl with
              | Forall2_nil _ => Forall2_nil P
              | Forall2_cons t u Ht Hr =>
                  Forall2_cons t u (bagree_ind' t u Ht) (go _ _ Hr)
              end) As Bs Hargs)
    end.
End bagree_ind'.

Lemma lagree_bagree : forall L A B, lagree L A B -> bagree L A B.
Proof. intros L A B H. induction H using lagree_ind'. constructor; auto. Qed.

Lemma Forall2_lagree_bagree : forall L As Bs,
  Forall2 (lagree L) As Bs -> Forall2 (bagree L) As Bs.
Proof. intros L As Bs H. induction H; constructor; auto using lagree_bagree. Qed.

Lemma bagree_refl : forall L A, bagree L A A.
Proof. intros L A. apply lagree_bagree. apply lagree_refl. Qed.

Lemma Forall2_bagree_refl : forall L As, Forall2 (bagree L) As As.
Proof. induction As; constructor; auto using bagree_refl. Qed.

Lemma bagree_trans : forall L A B,
  bagree L A B -> forall C, bagree L B C -> bagree L A C.
Proof.
  intros L A B H. induction H using bagree_ind'. intros C0 H23.
  inversion H23; subst. constructor.
  - destruct H as [[-> Hro] | Hq12].
    + left. split; [reflexivity|].
      destruct Hq as [[_ Hr] | Hq23]; [exact Hr|].
      unfold arg_q_sub in Hq23. destruct Hq23 as [-> | [-> _]]; [exact Hro | discriminate].
    + destruct Hq as [[-> Hr] | Hq23].
      * left. split; [|exact Hr].
        unfold arg_q_sub in Hq12. destruct Hq12 as [Hx | [Hx _]]; congruence.
      * right. eauto using arg_q_sub_trans.
  - destruct (q_eq_dec q1 Mut) as [-> | Hne]; [|right; left; exact Hne].
    destruct H as [[Hx _] | Hq12]; [discriminate|].
    unfold arg_q_sub in Hq12.
    destruct Hq12 as [-> | [-> _]].
    + destruct Hq as [[Hx _] | Hq23]; [discriminate|].
      unfold arg_q_sub in Hq23.
      destruct Hq23 as [-> | [-> _]]; [|left; reflexivity].
      right. right.
      destruct H0 as [Hx | [Hx | Hx]]; try congruence.
      destruct Hlab as [Hy | [Hy | Hy]]; congruence.
    + destruct Hq as [[Hx _] | Hq23]; [discriminate|].
      unfold arg_q_sub in Hq23.
      destruct Hq23 as [-> | [-> _]]; left; reflexivity.
  - clear H H0 Hq Hlab H23. generalize dependent Bs0.
    induction H2; intros Bs0 Hargs; inversion Hargs; subst; constructor; eauto.
    apply IHForall2; auto. inversion H1; auto.
Qed.

Lemma Forall2_bagree_trans : forall L As Bs Cs,
  Forall2 (bagree L) As Bs -> Forall2 (bagree L) Bs Cs -> Forall2 (bagree L) As Cs.
Proof.
  intros L As Bs Cs H. revert Cs.
  induction H; intros Cs H2; inversion H2; subst; constructor; eauto using bagree_trans.
Qed.

Lemma Forall2_bagree_trans_l : forall L As Bs Cs,
  Forall2 (bagree L) As Bs -> Forall2 (lagree L) Bs Cs -> Forall2 (bagree L) As Cs.
Proof.
  intros L As Bs Cs H1 H2. eapply Forall2_bagree_trans; eauto using Forall2_lagree_bagree.
Qed.

Lemma bagree_pop : forall L w0 A B, bagree (w0 :: L) A B -> bagree L A B.
Proof.
  intros L w0 A B H. induction H using bagree_ind'.
  constructor; auto.
  destruct H0 as [H0 | [H0 | H0]]; auto.
  right. right. eapply norm_pop; eauto.
Qed.

Lemma Forall2_bagree_pop : forall L w0 As Bs,
  Forall2 (bagree (w0 :: L)) As Bs -> Forall2 (bagree L) As Bs.
Proof. intros L w0 As Bs H. induction H; constructor; eauto using bagree_pop. Qed.

Lemma bagree_push : forall L n A B,
  bagree L A B -> lbound n A -> lbound n B -> bagree (n :: L) A B.
Proof.
  intros L n A B H. induction H using bagree_ind'. intros HA HB.
  apply lbound_node in HA. apply lbound_node in HB.
  destruct HA as [Hl1 HAs]. destruct HB as [Hl2 HBs].
  constructor; auto.
  - destruct H0 as [Hx | [Hx | Hx]]; auto.
    right. right. rewrite (norm_push _ _ _ Hl1). rewrite (norm_push _ _ _ Hl2).
    exact Hx.
  - clear H H0 Hl1 Hl2. induction H2; constructor;
      inversion HAs; inversion HBs; subst; auto.
    apply IHForall2; auto. inversion H1; auto.
Qed.

(** Readers that leave the qualifiers other than [Mut] and [RDM] alone, and
    never read [Mut] or [RDM] as readonly. *)
Definition plainr (hq : q) (g : q -> q) : Prop :=
  forall q0, q0 <> Mut -> q0 <> RDM -> dynq hq (g q0) = q0.

Definition nror (hq : q) (g : q -> q) : Prop :=
  dynq hq (g Mut) <> RO /\ dynq hq (g RDM) <> RO.

Lemma plainr_bq : plainr Bot bq.
Proof. intros q0 Hm Hr. destruct q0; try congruence; reflexivity. Qed.

Lemma nror_bq : nror Bot bq.
Proof. split; discriminate. Qed.

Lemma bq_not_mut : forall q0, dynq Bot (bq q0) <> Mut.
Proof. intros q0. destruct q0; discriminate. Qed.

Lemma lqnth_nil : forall m, lqnth [] m = (RO, LOut).
Proof. intros m. unfold lqnth. destruct m; reflexivity. Qed.

(** The bottom reader's step of a header against any plain reader's step of
    the same header, on arguments that agree. *)
Lemma bstep_ldyn_g : forall L hq g lm lr Vs Bs S,
  plainr hq g -> nror hq g ->
  Forall2 (bagree L) Vs Bs ->
  bagree L (ldyn (bframe Vs) (map_qual bq S))
           (ldyn (mk_lframe hq lm lr Bs [] []) (map_qual g S)).
Proof.
  intros L hq g lm lr Vs Bs S Hpl [Hnm Hnr] Hle.
  assert (Hhead : forall q0,
            (dynq Bot (bq q0) = Bot /\ dynq hq (g q0) <> RO) \/
            arg_q_sub (dynq Bot (bq q0)) (dynq hq (g q0))).
  { intros q0.
    destruct (q_eq_dec q0 Mut) as [-> | Hm]; [left; split; [reflexivity | exact Hnm]|].
    destruct (q_eq_dec q0 RDM) as [-> | Hr]; [left; split; [reflexivity | exact Hnr]|].
    right. rewrite (plainr_bq q0 Hm Hr). rewrite (Hpl q0 Hm Hr).
    left. reflexivity. }
  induction S using qualified_type_ind'.
  - cbn [map_qual ldyn bframe lf_q]. constructor.
    + exact (Hhead qual).
    + right. left. apply bq_not_mut.
    + rewrite !map_map. induction H; simpl; constructor; auto.
  - pose proof (tv_lookup_Forall2 (bagree L) o Vs Bs [] [] n Hle (Forall2_nil _)) as Hl.
    destruct u as [|qual|m]; cbn [map_qual ldyn bframe lf_q lf_cargs lf_margs lf_qargs];
      destruct (tv_lookup o Vs [] n) as [[qa la Ca Aa]|],
               (tv_lookup o Bs [] n) as [[qb lb Cb Ab]|]; try contradiction.
    + exact Hl.
    + apply bagree_refl.
    + inversion Hl; subst. simpl.
      constructor; [exact (Hhead qual) | right; left; apply bq_not_mut | exact Hargs].
    + unfold ldefault. simpl. constructor; [exact (Hhead qual) | right; left; apply bq_not_mut | constructor].
    + inversion Hl; subst. rewrite !lqnth_nil. simpl.
      constructor; [right; left; reflexivity | right; left; discriminate | exact Hargs].
    + unfold ldefault. rewrite !lqnth_nil. simpl.
      constructor; [right; left; reflexivity | right; left; discriminate | constructor].
  - cbn [map_qual ldyn bframe lf_qargs]. rewrite !lqnth_nil. simpl fst. simpl snd. constructor.
    + right. left. reflexivity.
    + right. left. discriminate.
    + rewrite !map_map. induction H; simpl; constructor; auto.
Qed.

Lemma plainr_tg : forall qA, plainr qA (tg qA).
Proof. intros qA q0 Hm Hr. destruct q0; try congruence; destruct qA; reflexivity. Qed.

Lemma nror_tg : forall qA, nror qA (tg qA).
Proof. intros qA. split; destruct qA; discriminate. Qed.

Lemma bstep_tstep : forall L qA lA Vs Bs Ss,
  Forall2 (bagree L) Vs Bs ->
  Forall2 (bagree L) (bstep Vs Ss) (tstep qA lA Bs Ss).
Proof.
  intros L qA lA Vs Bs Ss Hle. unfold bstep, tstep, tframe.
  induction Ss; simpl; constructor; auto.
  apply bstep_ldyn_g; auto using plainr_tg, nror_tg.
Qed.

Lemma bstep_bstep : forall L Vs Bs Ss,
  Forall2 (bagree L) Vs Bs ->
  Forall2 (bagree L) (bstep Vs Ss) (bstep Bs Ss).
Proof.
  intros L Vs Bs Ss Hle. unfold bstep, bframe.
  induction Ss as [|S Ss IH]; simpl; constructor; auto.
  exact (bstep_ldyn_g L Bot bq LOut LOut Vs Bs S plainr_bq nror_bq Hle).
Qed.

Lemma lbsuper_mono_t : forall CT qA lA D Bs E Ws,
  ltsuper CT qA lA D Bs E Ws ->
  forall L Vs, Forall2 (bagree L) Vs Bs ->
    exists Ws', lbsuper CT D Vs E Ws' /\ Forall2 (bagree L) Ws' Ws.
Proof.
  intros CT qA lA D Bs E Ws H.
  induction H as [C As | C As P Ss D Vs0 Hparent Hrest IH]; intros L Vs Hle.
  - exists Vs. split; [apply lbs_refl | exact Hle].
  - destruct (IH L (bstep Vs Ss)) as (Ws' & Hv & Hl).
    { apply bstep_tstep. exact Hle. }
    exists Ws'. split; auto. eapply lbs_step; eauto.
Qed.

Lemma lbsuper_mono : forall CT D Bs E Ws,
  lbsuper CT D Bs E Ws ->
  forall L Vs, Forall2 (bagree L) Vs Bs ->
    exists Ws', lbsuper CT D Vs E Ws' /\ Forall2 (bagree L) Ws' Ws.
Proof.
  intros CT D Bs E Ws H.
  induction H as [C As | C As P Ss D Vs0 Hparent Hrest IH]; intros L Vs Hle.
  - exists Vs. split; [apply lbs_refl | exact Hle].
  - destruct (IH L (bstep Vs Ss)) as (Ws' & Hv & Hl).
    { apply bstep_bstep. exact Hle. }
    exists Ws'. split; auto. eapply lbs_step; eauto.
Qed.

Lemma lbsuper_of_ltsuper : forall CT L qA lA C As D Vs,
  ltsuper CT qA lA C As D Vs ->
  exists Vs', lbsuper CT C As D Vs' /\ Forall2 (bagree L) Vs' Vs.
Proof.
  intros CT L qA lA C As D Vs H.
  apply (lbsuper_mono_t _ _ _ _ _ _ _ H L As (Forall2_bagree_refl L As)).
Qed.

Lemma lbsuper_lbound : forall CT C As D Vs n,
  lbsuper CT C As D Vs -> Forall (lbound n) As -> Forall (lbound n) Vs.
Proof.
  intros CT C As D Vs n H.
  induction H as [C As | C As P Ss D Vs Hparent Hrest IH]; intros HAs; auto.
  apply IH. unfold bstep.
  apply Forall_forall. intros A HA. apply in_map_iff in HA.
  destruct HA as (S & <- & _). apply ldyn_lbound.
  unfold frame_bound, bframe. simpl. auto.
Qed.

(** Only null has a bottom-headed type, so the bottom case compares the
    bottom reader's view with the bottom escape: a header-written mutable
    position holds nothing and agrees with the bound's mutable node, while
    the nodes the type carries agree with their labels. *)
Definition lsubt (CT : class_table) (L : list nat) (A B : ltype) : Prop :=
  match A, B with
  | LT q1 l1 C As, LT q2 l2 D Bs =>
      (q1 = Bot /\
       exists Vs, lbsuper CT C As D Vs /\ Forall2 (bagree L) Vs Bs) \/
      (rq_sub q1 q2 /\
       (q2 = Mut -> norm L l1 = norm L l2) /\
       exists Vs, ltsuper CT q1 l1 C As D Vs /\ Forall2 (lagree L) Vs Bs)
  end.

(** Either case gives the bottom reader's view, with the escape. *)
Lemma lsubt_lb : forall CT L q1 l1 C As q2 l2 D Bs,
  lsubt CT L (LT q1 l1 C As) (LT q2 l2 D Bs) ->
  exists Vs, lbsuper CT C As D Vs /\ Forall2 (bagree L) Vs Bs.
Proof.
  intros CT L q1 l1 C As q2 l2 D Bs H.
  destruct H as [(_ & Vs & Hv & Hle) | (_ & _ & Vs & Hv & Hle)]; [eauto|].
  destruct (lbsuper_of_ltsuper _ L _ _ _ _ _ _ Hv) as (Vs' & Hv' & Hle').
  exists Vs'. split; auto. eapply Forall2_bagree_trans_l; eauto.
Qed.

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

Lemma ltsuper_any_of : forall CT qA lA C As D Vs,
  ltsuper CT qA lA C As D Vs -> ltsuper_any CT C As D Vs.
Proof.
  intros CT qA lA C As D Vs H. induction H; [apply lta_refl | eapply lta_step; eauto].
Qed.

Lemma label_cond2_refl : forall L qA lA As Bs,
  label_cond2 L (tg qA) (tg qA) (tframe qA lA As) (tframe qA lA Bs).
Proof.
  intros L qA lA As Bs q0. split; [left; reflexivity|].
  right. right. reflexivity.
Qed.

(** Two views through different heads differ in their heads only where neither
    is readonly. *)
Inductive lclose : ltype -> ltype -> Prop :=
  | lc_node : forall q1 l1 q2 l2 C As Bs
      (Hq : q1 = q2 \/ (q1 <> RO /\ q2 <> RO))
      (Hargs : Forall2 lclose As Bs),
      lclose (LT q1 l1 C As) (LT q2 l2 C Bs).

Lemma lclose_refl : forall A, lclose A A.
Proof.
  intros A. induction A using ltype_ind'.
  constructor; [left; reflexivity|]. induction H; constructor; auto.
Qed.

Lemma Forall2_lclose_refl : forall As, Forall2 lclose As As.
Proof. induction As; constructor; auto using lclose_refl. Qed.

Lemma tg_head_ro : forall x t, dynq x (tg x t) = RO <-> t = RO.
Proof. intros x t. destruct x, t; simpl; split; congruence. Qed.

Lemma tg_head_close : forall x y t,
  dynq x (tg x t) = dynq y (tg y t) \/
  (dynq x (tg x t) <> RO /\ dynq y (tg y t) <> RO).
Proof.
  intros x y t. destruct (q_eq_dec t RO) as [-> | Hne]; [left; reflexivity|].
  right. split; intros H; apply tg_head_ro in H; congruence.
Qed.

Lemma lclose_rehead : forall q1 l1 q2 l2 A A',
  q1 = q2 \/ (q1 <> RO /\ q2 <> RO) -> lclose A A' ->
  lclose (lrehead q1 l1 A) (lrehead q2 l2 A').
Proof.
  intros q1 l1 q2 l2 [qa la Ca Aa] [qb lb Cb Ab] Hq H. inversion H; subst.
  simpl. constructor; auto.
Qed.

Lemma Forall2_nth_lclose : forall As As' n,
  Forall2 lclose As As' ->
  (nth_error As n = None /\ nth_error As' n = None) \/
  (exists A A', nth_error As n = Some A /\ nth_error As' n = Some A' /\ lclose A A').
Proof.
  intros As As' n H. revert n. induction H; intros n.
  - left. destruct n; split; reflexivity.
  - destruct n; simpl; [right; exists x, y; auto | apply IHForall2].
Qed.

Lemma ldyn_close : forall qa la qb lb As As' S,
  Forall2 lclose As As' ->
  lclose (ldyn (tframe qa la As) (map_qual (tg qa) S))
         (ldyn (tframe qb lb As') (map_qual (tg qb) S)).
Proof.
  intros qa la qb lb As As' S Hc. induction S using qualified_type_ind'.
  - cbn [map_qual ldyn tframe lf_q]. constructor; [apply tg_head_close|].
    rewrite !map_map. induction H; simpl; constructor; auto.
  - assert (Hl : lclose
              (match tv_lookup o As [] n with Some A => A | None => ldefault end)
              (match tv_lookup o As' [] n with Some A => A | None => ldefault end)).
    { destruct o; simpl;
        first [ destruct (Forall2_nth_lclose _ _ n Hc)
                  as [[-> ->] | (A & A' & -> & -> & Hx)];
                [apply lclose_refl | exact Hx]
              | destruct n; apply lclose_refl ]. }
    destruct u as [|t|m]; cbn [map_qual ldyn tframe lf_q lf_cargs lf_margs lf_qargs];
      auto.
    + apply lclose_rehead; auto. apply tg_head_close.
    + apply lclose_rehead; auto.
  - cbn [map_qual ldyn tframe lf_qargs]. constructor; [left; reflexivity|].
    rewrite !map_map. induction H; simpl; constructor; auto.
Qed.

(** A mixed view and the view through any one head are close. *)
Lemma ltsuper_any_close : forall CT C As D Vs,
  ltsuper_any CT C As D Vs ->
  forall qb lb As', Forall2 lclose As As' ->
  exists Vs', ltsuper CT qb lb C As' D Vs' /\ Forall2 lclose Vs Vs'.
Proof.
  intros CT C As D Vs H. induction H; intros qb lb As' Hc.
  - exists As'. split; [apply lts_refl | exact Hc].
  - destruct (IHltsuper_any qb lb (tstep qb lb As' Ss)) as (Vs' & Hv & Hl).
    { unfold tstep. clear - Hc. induction Ss; simpl; constructor; auto using ldyn_close. }
    exists Vs'. split; auto. eapply lts_step; eauto.
Qed.

Lemma bq_head_close : forall y t,
  dynq Bot (bq t) = dynq y (tg y t) \/
  (dynq Bot (bq t) <> RO /\ dynq y (tg y t) <> RO).
Proof.
  intros y t. destruct (q_eq_dec t RO) as [-> | Hne]; [left; destruct y; reflexivity|].
  right. split; [destruct t; simpl; congruence|].
  intros H. apply tg_head_ro in H. congruence.
Qed.

Lemma ldyn_bclose : forall qb lb As As' S,
  Forall2 lclose As As' ->
  lclose (ldyn (bframe As) (map_qual bq S))
         (ldyn (tframe qb lb As') (map_qual (tg qb) S)).
Proof.
  intros qb lb As As' S Hc. induction S using qualified_type_ind'.
  - cbn [map_qual ldyn bframe tframe lf_q]. constructor; [apply bq_head_close|].
    rewrite !map_map. induction H; simpl; constructor; auto.
  - assert (Hl : lclose
              (match tv_lookup o As [] n with Some A => A | None => ldefault end)
              (match tv_lookup o As' [] n with Some A => A | None => ldefault end)).
    { destruct o; simpl;
        first [ destruct (Forall2_nth_lclose _ _ n Hc)
                  as [[-> ->] | (A & A' & -> & -> & Hx)];
                [apply lclose_refl | exact Hx]
              | destruct n; apply lclose_refl ]. }
    destruct u as [|t|m]; cbn [map_qual ldyn bframe tframe lf_q lf_cargs lf_margs lf_qargs];
      auto.
    + apply lclose_rehead; auto. apply bq_head_close.
    + apply lclose_rehead; auto.
  - cbn [map_qual ldyn bframe tframe lf_qargs]. constructor; [left; reflexivity|].
    rewrite !map_map. induction H; simpl; constructor; auto.
Qed.

(** The bottom reader's view and the view through any one head are close. *)
Lemma lbsuper_close : forall CT C As D Vs,
  lbsuper CT C As D Vs ->
  forall qb lb As', Forall2 lclose As As' ->
  exists Vs', ltsuper CT qb lb C As' D Vs' /\ Forall2 lclose Vs Vs'.
Proof.
  intros CT C As D Vs H. induction H; intros qb lb As' Hc.
  - exists As'. split; [apply lts_refl | exact Hc].
  - destruct (IHlbsuper qb lb (tstep qb lb As' Ss)) as (Vs' & Hv & Hl).
    { unfold bstep, tstep. clear - Hc. induction Ss; simpl; constructor; auto using ldyn_bclose. }
    exists Vs'. split; auto. eapply lts_step; eauto.
Qed.

(** Forgetting a bound's arguments covers every close view, with the bottom
    escape too: a forgotten argument is read as unknown, and an escape only
    happens against a node that is not readonly, so not against a kept one. *)
Lemma bclose_widen : forall L L0 F T V V',
  class_only_b T = true ->
  bagree L0 V (ldyn F T) -> lclose V V' ->
  lagree L V' (ldyn F (widen_args T)).
Proof.
  intros L L0 F T. induction T using qualified_type_ind';
    intros V V' Hco Hle Hc; simpl in Hco; try discriminate.
  cbn [ldyn widen_args] in Hle |- *.
  inversion Hle as [v lv ? ? C0 Vs Us Hq Hlab Hargs]; subst.
  inversion Hc as [? ? v' lv' ? ? Vs' Hq' Hargs']; subst.
  assert (Htgt : dynq (lf_q F) (widen_q qual) = Lost \/
                 (qual = RO /\ dynq (lf_q F) (widen_q qual) = RO)).
  { destruct qual; simpl; auto. }
  constructor.
  - destruct Htgt as [-> | [-> ->]].
    + unfold arg_q_sub. destruct v'; auto 8.
    + simpl in Hq. destruct Hq as [[_ Hro] | Hq]; [congruence|].
      unfold arg_q_sub in Hq. destruct Hq as [Hq | [Hq _]]; [|discriminate]. subst v.
      destruct Hq' as [<- | [Hr _]]; [left; reflexivity | congruence].
  - destruct Htgt as [-> | [-> ->]]; [left; reflexivity|].
    simpl in Hq. destruct Hq as [[_ Hro] | Hq]; [congruence|].
    unfold arg_q_sub in Hq. destruct Hq as [Hq | [Hq _]]; [|discriminate]. subst v.
    destruct Hq' as [<- | [Hr _]]; [right; left; discriminate | congruence].
  - clear Hle Hc Hlab Hq Hq' Htgt. revert Vs Vs' Hargs Hargs'.
    induction H; intros Vs Vs' H1 H2; simpl in *.
    + inversion H1; subst. inversion H2; subst. constructor.
    + apply andb_prop in Hco as [Hx Hl]. inversion H1; subst. inversion H2; subst.
      constructor; eauto.
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
  assert (Hbot : forall Vs, lbsuper CT C1 As D Vs -> Forall2 (bagree L) Vs Bs ->
            exists Ws, lbsuper CT C1 As E Ws /\ Forall2 (bagree L) Ws Cs).
  { intros Vs Hv Hle.
    destruct (lsubt_lb _ _ _ _ _ _ _ _ _ _ H23) as (Ws & Hw & Hl).
    destruct (lbsuper_mono _ _ _ _ _ Hw L Vs Hle) as (Ws' & Hw' & Hl').
    exists Ws'. split; [eapply lbsuper_trans; eauto | eapply Forall2_bagree_trans; eauto]. }
  destruct H12 as [(Hq & Vs & Hv & Hle) | (Hrq & Hlab & Vs & Hv & Hle)].
  - left. split; auto. eapply Hbot; eauto.
  - destruct (q_eq_dec q1 Bot) as [Hq | Hnb].
    + left. split; auto.
      destruct (lbsuper_of_ltsuper _ L _ _ _ _ _ _ Hv) as (Vs' & Hv' & Hle').
      eapply Hbot; [exact Hv' | eapply Forall2_bagree_trans_l; eauto].
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

(** The same conditions for a frame headed [Lost], which forgets every
    receiver-dependent position. *)
Lemma hier_cond_l : forall L mt F q1 As cs ms ks,
  readonly_state_method_scope mt ->
  (lf_q F = Mut \/ lf_q F = Imm \/ lf_q F = Lost) ->
  label_cond2 L (tg (dynq (lf_q F) q1)) (vpa_q mt q1)
    (tframe (dynq (lf_q F) q1) (lab_of F q1) As) (lf_with_args F cs ms ks).
Proof.
  intros L mt [qF lm lr c0 m0 k0] q1 As cs ms ks Hrs Hq q0. simpl in Hq.
  destruct Hrs as [-> | ->]; destruct Hq as [-> | [-> | ->]]; destruct q1, q0;
    cbv [tg tframe lf_with_args lf_q lab_of lf_mut lf_rdm dynq arg_q_sub vpa_q
         vpa_mutability_qq_readonly_state];
    (split;
     [ solve [left; reflexivity] || solve [right; split; auto]
     | solve [left; reflexivity] || solve [right; left; discriminate]
       || solve [right; right; reflexivity] ]).
Qed.

Lemma head_ro_cond_l : forall L mt F qa la As cs ms ks,
  readonly_state_method_scope mt ->
  (lf_q F = Mut \/ lf_q F = Imm \/ lf_q F = Lost) ->
  qa <> Bot ->
  label_cond2 L (tg qa) (vpa_q mt RO) (tframe qa la As) (lf_with_args F cs ms ks).
Proof.
  intros L mt [qF lm lr c0 m0 k0] qa la As cs ms ks Hrs Hq Hnb q0. simpl in Hq.
  destruct Hrs as [-> | ->]; destruct Hq as [-> | [-> | ->]]; destruct qa, q0;
    try congruence;
    cbv [tg tframe lf_with_args lf_q lab_of lf_mut lf_rdm dynq arg_q_sub vpa_q
         vpa_mutability_qq_readonly_state];
    (split;
     [ solve [left; reflexivity] || solve [right; split; auto]
     | solve [left; reflexivity] || solve [right; left; discriminate]
       || solve [right; right; reflexivity] ]).
Qed.

Lemma type_vs_static_view_l : forall CT mt qh C Ts D Vs,
  super_inst CT mt qh C Ts D Vs ->
  forall L F As,
    readonly_state_method_scope mt ->
    (lf_q F = Mut \/ lf_q F = Imm \/ lf_q F = Lost) ->
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
      - apply hier_cond_l; auto.
      - exact Hargs.
      - constructor.
      - reflexivity. }
    exists Vs'. split; auto. eapply lts_step; eauto.
Qed.

(** Every type variable's supplied type is a labelled subtype of the reading
    of its bound. *)
Definition frame_fits (CT : class_table) (L : list nat) (Δ : tv_env)
    (F : lframe) : Prop :=
  forall o n B, tv_bound Δ o n = Some B ->
    lsubt CT L (ldyn F (TVar TVSub o n)) (ldyn F B).

Lemma sub_lsubt_g : forall CT Δ L F,
  readonly_state_method_scope (tv_mode Δ) ->
  (lf_q F = Mut \/ lf_q F = Imm \/ lf_q F = Lost) ->
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
    + left. split; [reflexivity|]. eexists. split; [apply lbs_refl|].
      exact (Forall2_lagree_bagree _ _ _ Hle).
  - (* up the hierarchy *)
    cbn [ldyn]. right. refine (conj _ (conj (fun _ => eq_refl) _)).
    + left. reflexivity.
    + apply (type_vs_static_view_l _ _ _ _ _ _ _ Hsuper L F _ Hrs Hq).
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
    + left. split; [reflexivity|]. exists Aa. split; [apply lbs_refl | apply Forall2_bagree_refl].
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
  - (* a qualified variable use at a bound, forgetting its arguments *)
    cbn [ldyn] in *.
    destruct (match tv_lookup o (lf_cargs F) (lf_margs F) n with
              | Some A => A | None => ldefault end) as [qa la Ca Aa].
    simpl lrehead.
    destruct (lsubt_lb _ _ _ _ _ _ _ _ _ _ IHHsub) as (Vs & Hv & Hle).
    destruct (lbsuper_close _ _ _ _ _ Hv (dynq (lf_q F) q1) (lab_of F q1) Aa
                (Forall2_lclose_refl Aa)) as (Vs' & Hv' & Hc').
    right. refine (conj _ (conj (fun _ => eq_refl) _)); [left; reflexivity|].
    exists Vs'. split; [exact Hv'|].
    clear - Hle Hc' Hcls. revert Vs Vs' Hle Hc'.
    induction Ts as [|T Ts IH]; intros Vs Vs' Hle Hc'; simpl in *.
    + inversion Hle; subst. inversion Hc'; subst. constructor.
    + apply andb_prop in Hcls as [HT HTs]. inversion Hle; subst. inversion Hc'; subst.
      constructor; [eapply bclose_widen; eauto | eapply IH; eauto].
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
      destruct (type_vs_static_view_l _ _ _ _ _ _ _ Hsuper L F (map (ldyn F) Ts)
                  Hrs Hq (Forall2_lagree_refl _ _)) as (Vs' & Hv & Hle).
      destruct (lbsuper_of_ltsuper _ L _ _ _ _ _ _ Hv) as (Ws & Hw & Hle').
      exists Ws. split; [exact Hw | eapply Forall2_bagree_trans_l; eauto].
    + right. refine (conj _ (conj (fun _ => eq_refl) _)); [left; reflexivity|].
      apply (type_vs_static_view_g _ _ _ _ _ _ _ Hsuper L F qa la).
      * intros As0 cs ms ks. apply head_ro_cond_l; auto.
      * apply Forall2_lagree_refl.
  - (* the bottom-qualified type of the class *)
    cbn [ldyn].
    remember (fst (lqnth (lf_qargs F) n)) as qa eqn:Hqa0.
    remember (snd (lqnth (lf_qargs F) n)) as la eqn:Hla0.
    idtac. left. split; [reflexivity|].
    exists (map (ldyn F) Ts). split; [apply lbs_refl|].
    apply Forall2_lagree_bagree. apply map_ldyn_targ_sub; auto.
  - eapply lsubt_trans; eauto.
Qed.

(** The form for a frame read through a concrete head. *)
Lemma sub_lsubt : forall CT Δ L F,
  readonly_state_method_scope (tv_mode Δ) ->
  (lf_q F = Mut \/ lf_q F = Imm) ->
  frame_fits CT L Δ F ->
  forall T U, qualified_type_subtype CT Δ T U ->
    lsubt CT L (ldyn F T) (ldyn F U).
Proof.
  intros CT Δ L F Hrs Hq. apply sub_lsubt_g; auto. destruct Hq; auto.
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
    eapply Forall2_bagree_trans_l; eauto.
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
  destruct H as [(Hb & Vs & Hv & Hle) | (Hrq & Hl & Vs & Hv & Hle)].
  { left. split; auto. exists Vs. split; auto. eapply Forall2_bagree_pop; eauto. }
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
  destruct H as [(Hb & Vs & Hv & Hle) | (Hrq & Hl & Vs & Hv & Hle)].
  { left. split; auto. exists Vs. split; auto.
    pose proof (lbsuper_lbound _ _ _ _ _ n Hv HAs) as HVs.
    clear - Hle HVs HBs. induction Hle; constructor;
      inversion HVs; inversion HBs; subst; auto using bagree_push. }
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

(* ------------------FITS AGAINST OPENED BOUNDS------------------*)

(** An object outside every world makes no claim about which world its
    header-written mutable positions belong to, so a bound read in its header
    frame has every written mutable position read as unknown.  Static
    subtyping in a class environment, read in such a frame with those weaker
    fits, still gives labelled subtyping, with the target read the same way.
    The proof kills both sides: killing is a static homomorphism in protected
    modes, and the plain reading of a type agrees into its killed reading. *)

(* ------------------KILLING------------------*)

Definition killq (q0 : q) : q := match q0 with Mut => Lost | _ => q0 end.
Definition kill (T : qualified_type) : qualified_type := map_qual killq T.
Arguments kill T /.

Definition kill_env (Δ : tv_env) : tv_env :=
  mk_tv_env (map kill (class_bounds Δ)) (map kill (method_bounds Δ))
    (tv_mode Δ) (qparams Δ).

Definition frame_fits_k (CT : class_table) (L : list nat) (Δ : tv_env)
    (F : lframe) : Prop :=
  forall o n B, tv_bound Δ o n = Some B ->
    lsubt CT L (ldyn F (TVar TVSub o n)) (ldyn F (kill B)).

Lemma tv_lookup_map : forall (A B : Type) (f : A -> B) o (cs ms : list A) n,
  tv_lookup o (map f cs) (map f ms) n = option_map f (tv_lookup o cs ms n).
Proof. intros A B f [] cs ms n; simpl; apply nth_error_map. Qed.

Lemma tv_lookup_map0 : forall (A B : Type) (f : A -> B) o (cs : list A) n,
  tv_lookup o (map f cs) [] n = option_map f (tv_lookup o cs [] n).
Proof. intros A B f [] cs n; simpl; [apply nth_error_map | destruct n; reflexivity]. Qed.

Lemma frame_fits_kill_env : forall CT L Δ F,
  frame_fits_k CT L Δ F -> frame_fits CT L (kill_env Δ) F.
Proof.
  intros CT L Δ F H o n Bk Hb.
  unfold tv_bound in Hb. cbn [kill_env class_bounds method_bounds] in Hb.
  rewrite tv_lookup_map in Hb.
  destruct (tv_lookup o (class_bounds Δ) (method_bounds Δ) n) as [B|] eqn:E;
    [|discriminate].
  inversion Hb; subst Bk. apply H. exact E.
Qed.

(* ------------------KILLING IS A STATIC HOMOMORPHISM------------------*)

Lemma killq_subtype : forall q1 q2, q_subtype q1 q2 -> q_subtype (killq q1) (killq q2).
Proof.
  intros q1 q2 H. inversion H; subst; [apply q_refl | apply q_rd | apply q_bot].
Qed.

Lemma killq_arg_sub : forall q1 q2, arg_q_sub q1 q2 -> arg_q_sub (killq q1) (killq q2).
Proof.
  unfold arg_q_sub. intros q1 q2 [-> | [-> H]]; [left; reflexivity|].
  destruct H as [-> | [-> | [-> | [-> | ->]]]]; simpl; auto 8.
Qed.

Lemma targ_sub_kill : forall T U, targ_sub T U -> targ_sub (kill T) (kill U).
Proof.
  intros T U H. induction H using targ_sub_ind'.
  - destruct u; simpl; constructor.
  - simpl. constructor; [apply killq_arg_sub; auto|].
    clear H0. induction H1; simpl; constructor; auto.
  - simpl. constructor. clear H. induction H0; simpl; constructor; auto.
  - simpl. apply tas_qvar_lost.
Qed.

Lemma Forall2_targ_sub_kill : forall Ts Us,
  Forall2 targ_sub Ts Us -> Forall2 targ_sub (map kill Ts) (map kill Us).
Proof. intros Ts Us H. induction H; simpl; constructor; auto using targ_sub_kill. Qed.

Lemma map_qual_map_qual : forall f g T,
  map_qual f (map_qual g T) = map_qual (fun x => f (g x)) T.
Proof.
  intros f g T. induction T using qualified_type_ind'.
  - simpl. f_equal. rewrite map_map. apply map_ext_in. intros a Ha.
    rewrite Forall_forall in H. apply H. exact Ha.
  - destruct u; reflexivity.
  - simpl. f_equal. rewrite map_map. apply map_ext_in. intros a Ha.
    rewrite Forall_forall in H. apply H. exact Ha.
Qed.

Lemma map_qual_ext : forall f g T,
  (forall x, f x = g x) -> map_qual f T = map_qual g T.
Proof.
  intros f g T Hfg. induction T using qualified_type_ind'.
  - simpl. rewrite Hfg. f_equal. apply map_ext_in. intros a Ha.
    rewrite Forall_forall in H. apply H. exact Ha.
  - destruct u; simpl; auto. rewrite Hfg. reflexivity.
  - simpl. f_equal. apply map_ext_in. intros a Ha.
    rewrite Forall_forall in H. apply H. exact Ha.
Qed.

(** In protected modes, adapting through a killed head is killing after
    adapting. *)
Lemma killq_vpa : forall mt q1 q0,
  readonly_state_method_scope mt ->
  killq (vpa_q mt q1 q0) = vpa_q mt (killq q1) q0.
Proof. intros mt q1 q0 [-> | ->]; destruct q1, q0; reflexivity. Qed.

Lemma kill_adapt : forall mt q1 S,
  readonly_state_method_scope mt ->
  kill (adapt mt q1 S) = adapt mt (killq q1) S.
Proof.
  intros mt q1 S Hrs. unfold kill, adapt. rewrite map_qual_map_qual.
  apply map_qual_ext. intros x. apply killq_vpa. exact Hrs.
Qed.

Lemma kill_requalify : forall q0 U,
  kill (requalify q0 U) = requalify (killq q0) (kill U).
Proof. intros q0 [| u o n |]; simpl; try destruct u; reflexivity. Qed.

Lemma kill_subst : forall Ts S,
  kill (subst Ts [] [] S) = subst (map kill Ts) [] [] (kill S).
Proof.
  intros Ts S. induction S using qualified_type_ind'.
  - simpl. f_equal. rewrite !map_map. apply map_ext_in. intros a Ha.
    rewrite Forall_forall in H. apply H. exact Ha.
  - destruct u as [|q0|m]; cbn; rewrite tv_lookup_map0;
      destruct (tv_lookup o Ts [] n) as [U|]; cbn;
      first [reflexivity | apply kill_requalify
            | destruct m; cbn; first [reflexivity | apply kill_requalify]].
  - cbn. destruct n; cbn; f_equal; rewrite !map_map; apply map_ext_in; intros a Ha;
      rewrite Forall_forall in H; apply H; exact Ha.
Qed.

Lemma super_inst_kill : forall CT mt q1 C Ts D Vs,
  readonly_state_method_scope mt ->
  super_inst CT mt q1 C Ts D Vs ->
  super_inst CT mt (killq q1) C (map kill Ts) D (map kill Vs).
Proof.
  intros CT mt q1 C Ts D Vs Hrs H. induction H.
  - apply si_refl.
  - eapply si_step; [exact Hparent|].
    assert (Heq : map kill (map (subst Ts [] []) (map (adapt mt q1) Ss)) =
                  map (subst (map kill Ts) [] []) (map (adapt mt (killq q1)) Ss)).
    { rewrite !map_map. apply map_ext. intros S.
      rewrite kill_subst. rewrite kill_adapt; auto. }
    rewrite <- Heq. exact IHsuper_inst.
Qed.

Lemma widen_q_killq : forall q0, widen_q (killq q0) = widen_q q0.
Proof. intros []; reflexivity. Qed.

Lemma class_only_kill : forall T, class_only_b (kill T) = class_only_b T.
Proof.
  intros T. induction T using qualified_type_ind'.
  - simpl. induction H as [|a r Ha Hr IH]; simpl; auto. rewrite Ha. rewrite IH. reflexivity.
  - destruct u; reflexivity.
  - reflexivity.
Qed.

Lemma widen_kill : forall T, class_only_b T = true ->
  widen_args (kill T) = widen_args T /\ kill (widen_args T) = widen_args T.
Proof.
  intros T. induction T using qualified_type_ind'; intros Hc.
  - simpl in Hc. simpl. rewrite widen_q_killq.
    assert (Hargs : map widen_args (map kill args) = map widen_args args /\
                    map kill (map widen_args args) = map widen_args args).
    { induction H as [|a r Ha Hr IH]; simpl in *; [split; reflexivity|].
      apply andb_prop in Hc. destruct Hc as [Hca Hcr].
      destruct (Ha Hca) as [H1 H2]. destruct (IH Hcr) as [H3 H4].
      split; f_equal; auto. }
    destruct Hargs as [H1 H2]. split.
    + rewrite map_map in H1 |- *. f_equal. exact H1.
    + simpl. f_equal.
      * destruct qual; reflexivity.
      * rewrite map_map in H2 |- *. exact H2.
  - discriminate.
  - discriminate.
Qed.

Lemma map_widen_kill : forall Ts, forallb class_only_b Ts = true ->
  map kill (map widen_args Ts) = map widen_args (map kill Ts).
Proof.
  induction Ts as [|T Ts IH]; intros Hc; simpl in *; auto.
  apply andb_prop in Hc. destruct Hc as [HT HTs].
  destruct (widen_kill T HT) as [H1 H2].
  f_equal; [transitivity (widen_args T); [exact H2 | symmetry; exact H1] | auto].
Qed.

Lemma forallb_class_only_kill : forall Ts,
  forallb class_only_b (map kill Ts) = forallb class_only_b Ts.
Proof.
  induction Ts as [|T Ts IH]; simpl; auto. rewrite class_only_kill. rewrite IH. reflexivity.
Qed.

Lemma tv_bound_kill : forall Δ o n B,
  tv_bound Δ o n = Some B -> tv_bound (kill_env Δ) o n = Some (kill B).
Proof.
  intros Δ o n B H. unfold tv_bound in *. cbn [kill_env class_bounds method_bounds].
  rewrite tv_lookup_map. rewrite H. reflexivity.
Qed.

(** Static subtyping survives killing, in an environment with killed bounds. *)
Lemma kill_sub : forall CT Δ T U,
  readonly_state_method_scope (tv_mode Δ) ->
  qualified_type_subtype CT Δ T U ->
  qualified_type_subtype CT (kill_env Δ) (kill T) (kill U).
Proof.
  intros CT Δ T U Hrs H. induction H.
  - simpl. apply qtype_qual; auto using killq_subtype, Forall2_targ_sub_kill.
  - simpl. apply qtype_hier. apply super_inst_kill; auto.
  - apply qtype_var_refl.
  - apply qtype_var_bound. apply tv_bound_kill. exact Hbound.
  - simpl. apply qtype_qvar_qual. apply killq_subtype. exact Hqsub.
  - simpl. apply qtype_var_ro.
  - apply qtype_pvar_refl.
  - simpl. apply qtype_pvar_ro.
  - (* the widened rule *)
    simpl in IHqualified_type_subtype. simpl.
    pose proof (map_widen_kill Ts Hcls) as Hmw. rewrite Hmw.
    apply (qtype_qvar_bound CT (kill_env Δ) (killq q1) o n (killq qb) C (map kill Ts) IHqualified_type_subtype).
    rewrite forallb_class_only_kill. exact Hcls.
  - simpl. apply qtype_head_ro; auto using Forall2_targ_sub_kill.
  - simpl. apply qtype_head_args; auto using Forall2_targ_sub_kill.
  - simpl. apply qtype_head_hier.
    change RO with (killq RO). apply super_inst_kill; auto.
  - simpl. apply qtype_head_bot; auto using Forall2_targ_sub_kill.
  - eapply qtype_trans; eauto.
Qed.

(* ------------------THE LABELLED SIDE------------------*)

(** A reading agrees into its killed reading. *)
Lemma label_cond_kill : forall L F, label_cond L killq F F.
Proof.
  intros L F q0. destruct q0; cbn [killq dynq]; unfold arg_q_sub; split; auto 8.
Qed.

Lemma lagree_kill : forall L F T, lagree L (ldyn F T) (ldyn F (kill T)).
Proof.
  intros L F T. apply ldyn_map_qual_agree; auto using label_cond_kill, Forall2_lagree_refl.
Qed.

Lemma lsubt_of_lagree : forall CT L A B, lagree L A B -> lsubt CT L A B.
Proof.
  intros CT L [q1 l1 C As] [q2 l2 D Bs] H.
  inversion H as [? ? ? ? ? ? ? Hq Hlab Hargs]; subst.
  right. refine (conj _ (conj _ _)).
  - unfold arg_q_sub in Hq. destruct Hq as [-> | [-> Hm]]; [left; reflexivity|].
    right. right. split; [reflexivity | exact Hm].
  - intros ->.
    assert (q1 = Mut) by (unfold arg_q_sub in Hq; destruct Hq as [Hx | [Hx _]]; congruence).
    subst q1. destruct Hlab as [Hx | [Hx | Hx]]; congruence || exact Hx.
  - exists As. split; [apply lts_refl | exact Hargs].
Qed.

Lemma frame_fits_k_of_fits : forall CT L Δ F,
  frame_fits CT L Δ F -> frame_fits_k CT L Δ F.
Proof.
  intros CT L Δ F H o n B Hb. eapply lsubt_agree_r; [apply H; exact Hb | apply lagree_kill].
Qed.

(** The lemma. *)
Theorem sub_lsubt_k : forall CT Δ L F,
  readonly_state_method_scope (tv_mode Δ) ->
  (lf_q F = Mut \/ lf_q F = Imm \/ lf_q F = Lost) ->
  frame_fits_k CT L Δ F ->
  forall T U, qualified_type_subtype CT Δ T U ->
    lsubt CT L (ldyn F T) (ldyn F (kill U)).
Proof.
  intros CT Δ L F Hrs Hq Hfit T U Hsub.
  eapply lsubt_trans; [apply lsubt_of_lagree; apply lagree_kill|].
  apply (sub_lsubt_g CT (kill_env Δ) L F).
  - exact Hrs.
  - exact Hq.
  - apply frame_fits_kill_env. exact Hfit.
  - apply kill_sub; auto.
Qed.

