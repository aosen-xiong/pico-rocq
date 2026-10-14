From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels.

(** Label typing: superclass views, values, and soundness of subtyping. *)

(** The ghost state: the world of each object, the world each object was born
    in, and each object's labelled type arguments. *)
Record ghost := mk_ghost {
  g_col : coloring;
  g_birth : Loc -> option nat;
  g_args : Loc -> list ltype;
}.

(* ------------------LABELLED SUPERCLASS VIEWS------------------*)

Inductive lsuper_inst (CT : class_table) (qo : q_r) (b c : option nat)
    : class_name -> list ltype -> class_name -> list ltype -> Prop :=
  | lsi_refl : forall C As,
      lsuper_inst CT qo b c C As C As
  | lsi_step : forall C As P Ss D Vs
      (Hparent : parent_lookup CT C = Some (P, Ss))
      (Hrest : lsuper_inst CT qo b c P
                 (map (ldyn (obj_frame qo b c As)) Ss) D Vs),
      lsuper_inst CT qo b c C As D Vs.

Lemma lsuper_inst_trans : forall CT qo b c C As D Vs,
  lsuper_inst CT qo b c C As D Vs ->
  forall E Ws, lsuper_inst CT qo b c D Vs E Ws ->
  lsuper_inst CT qo b c C As E Ws.
Proof.
  intros CT qo b c C As D Vs H. induction H; intros E Ws H2; auto.
  eapply lsi_step; eauto.
Qed.

Lemma map_erase_obj_frame : forall qo b c As Ss,
  map erase (map (ldyn (obj_frame qo b c As)) Ss) =
  map (dyn (qr2q qo) (map erase As) [] []) Ss.
Proof. intros. rewrite map_erase_ldyn. reflexivity. Qed.

(** A labelled view erases to the ordinary view, and every ordinary view has
    a labelled one. *)
Lemma lsuper_inst_erase : forall CT qo b c C As D Vs,
  lsuper_inst CT qo b c C As D Vs ->
  rsuper_inst CT (qr2q qo) C (map erase As) D (map erase Vs).
Proof.
  intros CT qo b c C As D Vs H. induction H.
  - apply rsi_refl.
  - eapply rsi_step; eauto. rewrite <- (map_erase_obj_frame qo b c). exact IHlsuper_inst.
Qed.

Lemma lsuper_inst_exists : forall CT qh C Rs D Rs',
  rsuper_inst CT qh C Rs D Rs' ->
  forall qo b c As, qh = qr2q qo -> map erase As = Rs ->
  exists Vs, lsuper_inst CT qo b c C As D Vs /\ map erase Vs = Rs'.
Proof.
  intros CT qh C Rs D Rs' H. induction H; intros qo b c As Hq HAs.
  - exists As. split; [apply lsi_refl | exact HAs].
  - subst qh Rs.
    destruct (IHrsuper_inst qo b c (map (ldyn (obj_frame qo b c As)) Ss) eq_refl)
      as [Vs0 [Hs He]].
    { apply map_erase_obj_frame. }
    exists Vs0. split; auto. eapply lsi_step; eauto.
Qed.

Lemma lsuper_inst_deterministic : forall CT qo b c C As D Vs1,
  wf_class_table CT ->
  lsuper_inst CT qo b c C As D Vs1 ->
  forall Vs2, lsuper_inst CT qo b c C As D Vs2 -> Vs1 = Vs2.
Proof.
  intros CT qo b c C As D Vs1 Hwf H. induction H; intros Vs2 H2.
  - inversion H2; subst; auto.
    exfalso.
    pose proof (rsuper_inst_le _ _ _ _ _ _ Hwf (lsuper_inst_erase _ _ _ _ _ _ _ _ Hrest))
      as Hle.
    unfold parent_lookup in Hparent.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
    destruct (wf_class_super_inv _ _ _ _ _ Hwf Hfind Hparent) as (sd & _ & Hlt & _).
    lia.
  - inversion H2; subst.
    + exfalso.
      pose proof (rsuper_inst_le _ _ _ _ _ _ Hwf (lsuper_inst_erase _ _ _ _ _ _ _ _ H))
        as Hle.
      unfold parent_lookup in Hparent.
      destruct (find_class CT D) as [def|] eqn:Hfind; [|discriminate].
      destruct (wf_class_super_inv _ _ _ _ _ Hwf Hfind Hparent) as (sd & _ & Hlt & _).
      lia.
    + rewrite Hparent in Hparent0. inversion Hparent0; subst.
      apply IHlsuper_inst; auto.
Qed.

Lemma label_cond_args : forall L f Fo Fc a1 a2 a3 a4 a5 a6,
  label_cond L f Fo Fc ->
  label_cond L f (lf_with_args Fo a1 a2 a5) (lf_with_args Fc a3 a4 a6).
Proof. intros L f Fo Fc a1 a2 a3 a4 a5 a6 H q0. exact (H q0). Qed.

(** A static superclass view is matched by the object's labelled view. *)
Lemma super_inst_ldyn : forall CT mt qh C Ts D Vs,
  super_inst CT mt qh C Ts D Vs ->
  forall L qo b c Fc As,
    label_cond L (vpa_q mt qh) (obj_frame qo b c []) Fc ->
    Forall2 (lagree L) As (map (ldyn Fc) Ts) ->
    exists Vs0, lsuper_inst CT qo b c C As D Vs0 /\
                Forall2 (lagree L) Vs0 (map (ldyn Fc) Vs).
Proof.
  intros CT mt qh C Ts D Vs H.
  induction H; intros L qo b c Fc As Hcond Hargs.
  - exists As. split; [apply lsi_refl | exact Hargs].
  - destruct (IHsuper_inst L qo b c Fc (map (ldyn (obj_frame qo b c As)) Ss) Hcond)
      as [Vs0 [Hs Hle]].
    { assert (Heq : map (ldyn Fc) (map (subst Ts [] []) (map (adapt mt qh) Ss)) =
                    map (ldyn (lf_with_args Fc (map (ldyn Fc) Ts) [] []))
                      (map (map_qual (vpa_q mt qh)) Ss)).
      { clear. induction Ss as [|S Ss IH]; simpl; auto.
        f_equal; auto. rewrite ldyn_subst. reflexivity. }
      rewrite Heq.
      apply map_ldyn_map_qual_agree.
      - apply (label_cond_args L _ _ _ As [] (map (ldyn Fc) Ts) [] _ _ Hcond).
      - exact Hargs.
      - constructor.
      - reflexivity. }
    exists Vs0. split; auto. eapply lsi_step; eauto.
Qed.

(* ------------------VALUES------------------*)

(** What a label at a mutable head says about an object's world. *)
Definition headL (L : list nat) (c : option nat) (q0 : q) (l : lab) : Prop :=
  q0 = Mut ->
  match norm L l with
  | Some w => c = Some w
  | None => forall w, c = Some w -> ~ List.In w L
  end.

(** The object at [v] inhabits a labelled type. *)
Definition lhas (CT : class_table) (h : heap) (G : ghost) (L : list nat)
    (v : Loc) (A : ltype) : Prop :=
  exists o, runtime_getObj h v = Some o /\
    match A with
    | LT q0 l D Us =>
        headL L (g_col G v) q0 l /\
        exists Vs,
          lsuper_inst CT (rqtype (rt_type o)) (g_birth G v) (g_col G v)
            (rctype (rt_type o)) (g_args G v) D Vs /\
          Forall2 (lagree L) Vs Us
    end.

Lemma lhas_agree : forall CT h G L v A B,
  lhas CT h G L v A -> lagree L A B -> lhas CT h G L v B.
Proof.
  intros CT h G L v A B (o & Ho & HA) Hag.
  exists o. split; auto.
  inversion Hag; subst.
  destruct HA as (Hh & Vs & Hs & Hle).
  split.
  - intros ->. unfold headL in Hh.
    assert (q1 = Mut).
    { unfold arg_q_sub in Hq. destruct Hq as [Hx | [Hx _]]; congruence. }
    subst q1.
    destruct Hlab as [Hx | [Hx | Hx]]; try congruence.
    rewrite <- Hx. apply Hh. reflexivity.
  - exists Vs. split; auto. eapply Forall2_lagree_trans; eauto.
Qed.

(* ------------------BOUNDS WITHOUT MUTABLE POSITIONS------------------*)

Fixpoint closed_clean (T : qualified_type) : Prop :=
  match T with
  | TClass q0 _ args =>
      clean_q q0 /\
      (fix go (l : list qualified_type) : Prop :=
         match l with
         | [] => True
         | t :: r => closed_clean t /\ go r
         end) args
  | TVar _ _ _ => False
  | THead _ _ _ => False
  end.

Fixpoint nomut_l (A : ltype) : Prop :=
  match A with
  | LT q0 _ _ args =>
      q0 <> Mut /\
      (fix go (ls : list ltype) : Prop :=
         match ls with
         | [] => True
         | t :: r => nomut_l t /\ go r
         end) args
  end.

Lemma closed_clean_go : forall l,
  (fix go (l : list qualified_type) : Prop :=
     match l with
     | [] => True
     | t :: r => closed_clean t /\ go r
     end) l <-> Forall closed_clean l.
Proof.
  induction l; simpl; split; intros H; auto.
  - destruct H. constructor; auto. apply IHl; auto.
  - inversion H; subst. split; auto. apply IHl; auto.
Qed.

Lemma nomut_l_go : forall l,
  (fix go (ls : list ltype) : Prop :=
     match ls with
     | [] => True
     | t :: r => nomut_l t /\ go r
     end) l <-> Forall nomut_l l.
Proof.
  induction l; simpl; split; intros H; auto.
  - destruct H. constructor; auto. apply IHl; auto.
  - inversion H; subst. split; auto. apply IHl; auto.
Qed.

Lemma ldyn_closed_clean_nomut : forall F T,
  closed_clean T -> nomut_l (ldyn F T).
Proof.
  intros F T. induction T using qualified_type_ind'; intros Hc.
  - simpl in Hc. destruct Hc as [(H1 & H2 & H3) Hargs].
    apply closed_clean_go in Hargs.
    simpl. split.
    + destruct qual; simpl; congruence.
    + apply nomut_l_go. clear H1 H2 H3.
      induction H; simpl; constructor; inversion Hargs; subst; auto.
  - contradiction.
  - contradiction.
Qed.

(** Against a type with no mutable position, ordinary agreement is label
    agreement. *)
Lemma lagree_of_rarg_nomut : forall L A B,
  rarg_sub (erase A) (erase B) -> nomut_l B -> lagree L A B.
Proof.
  intros L A. induction A using ltype_ind'. intros [q2 l2 C2 Bs] Hr Hn.
  simpl in Hr. inversion Hr; subst.
  simpl in Hn. destruct Hn as [Hq2 Hnargs]. apply nomut_l_go in Hnargs.
  constructor; auto.
  - unfold arg_q_sub in Hq. destruct Hq as [-> | [-> _]]; auto.
  - assert (Hall : forall Bs0,
              Forall2 rarg_sub (map erase args) (map erase Bs0) ->
              Forall nomut_l Bs0 -> Forall2 (lagree L) args Bs0).
    { clear - H. induction H; intros Bs0 Hr' Hn'; destruct Bs0 as [|B Bs0];
        simpl in Hr'; inversion Hr'; subst; constructor;
        inversion Hn'; subst; auto. }
    apply Hall; auto.
Qed.

Lemma Forall2_lagree_of_rarg_nomut : forall L As Bs,
  Forall2 rarg_sub (map erase As) (map erase Bs) -> Forall nomut_l Bs ->
  Forall2 (lagree L) As Bs.
Proof.
  intros L As. induction As as [|A As IH]; intros [|B Bs] H Hn; simpl in H;
    inversion H; subst; constructor; inversion Hn; subst;
    auto using lagree_of_rarg_nomut.
Qed.

Definition closed_clean_bounds (Δ : tv_env) : Prop :=
  forall o n B, tv_bound Δ o n = Some B ->
    exists qb C Ts, B = TClass qb C Ts /\ qb <> Mut /\ Forall closed_clean Ts.

(* ------------------WORLD IDENTIFIERS IN LABELS ARE BOUNDED------------------*)

Definition lab_bound (n : nat) (l : lab) : Prop :=
  match l with
  | LIn w => w < n
  | LOut => True
  end.

Fixpoint lbound (n : nat) (A : ltype) : Prop :=
  match A with
  | LT _ l _ args =>
      lab_bound n l /\
      (fix go (ls : list ltype) : Prop :=
         match ls with
         | [] => True
         | t :: r => lbound n t /\ go r
         end) args
  end.

Lemma lbound_go : forall n ls,
  (fix go (ls : list ltype) : Prop :=
     match ls with
     | [] => True
     | t :: r => lbound n t /\ go r
     end) ls <-> Forall (lbound n) ls.
Proof.
  induction ls; simpl; split; intros H; auto.
  - destruct H. constructor; auto. apply IHls; auto.
  - inversion H; subst. split; auto. apply IHls; auto.
Qed.

Lemma lbound_node : forall n q0 l C args,
  lbound n (LT q0 l C args) <-> lab_bound n l /\ Forall (lbound n) args.
Proof. intros. simpl. rewrite lbound_go. reflexivity. Qed.

Lemma lab_bound_mono : forall n n' l, n <= n' -> lab_bound n l -> lab_bound n' l.
Proof. intros n n' [w|] Hle H; simpl in *; auto. lia. Qed.

Lemma lbound_mono : forall n n' A, n <= n' -> lbound n A -> lbound n' A.
Proof.
  intros n n' A Hle. induction A using ltype_ind'. intros Hb.
  apply lbound_node in Hb. destruct Hb as [Hl Hargs]. apply lbound_node.
  split; [eapply lab_bound_mono; eauto|].
  induction H; constructor; inversion Hargs; subst; auto.
Qed.

Lemma Forall_lbound_mono : forall n n' As,
  n <= n' -> Forall (lbound n) As -> Forall (lbound n') As.
Proof.
  intros. eapply Forall_impl; [|eassumption]. intros. eapply lbound_mono; eauto.
Qed.

Definition frame_bound (n : nat) (F : lframe) : Prop :=
  lab_bound n (lf_mut F) /\ lab_bound n (lf_rdm F) /\
  Forall (lbound n) (lf_cargs F) /\ Forall (lbound n) (lf_margs F) /\
  Forall (fun p => lab_bound n (snd p)) (lf_qargs F).

Lemma lab_of_bound : forall n F q0, frame_bound n F -> lab_bound n (lab_of F q0).
Proof.
  intros n F q0 (H1 & H2 & _). destruct q0; simpl; auto.
Qed.

Lemma ldyn_lbound : forall n F T, frame_bound n F -> lbound n (ldyn F T).
Proof.
  intros n F T HF. induction T using qualified_type_ind'.
  - simpl ldyn. apply lbound_node. split; [apply lab_of_bound; auto|].
    induction H; simpl; constructor; auto.
  - destruct HF as (H1 & H2 & Hc & Hm & Hk).
    assert (HA : lbound n
              match tv_lookup o (lf_cargs F) (lf_margs F) n0 with
              | Some A => A | None => ldefault end).
    { destruct (tv_lookup o (lf_cargs F) (lf_margs F) n0) as [A|] eqn:Hl.
      - exact (tv_lookup_Forall (lbound n) o _ _ n0 A Hc Hm Hl).
      - simpl. auto. }
    simpl. destruct u as [|qual|m]; auto;
      destruct (match tv_lookup o (lf_cargs F) (lf_margs F) n0 with
                | Some A => A | None => ldefault end) as [qa la Ca Aa];
      apply lbound_node in HA; destruct HA as [_ HAa].
    + change (lbound n (LT (dynq (lf_q F) qual) (lab_of F qual) Ca Aa)).
      apply lbound_node. split; [|exact HAa].
      apply lab_of_bound. repeat split; auto.
    + simpl lrehead. apply lbound_node. split; [|exact HAa].
      unfold lqnth. clear - Hk. revert m. induction Hk; intros [|m]; simpl; auto.
  - simpl ldyn. apply lbound_node. split.
    + destruct HF as (_ & _ & _ & _ & Hk). unfold lqnth.
      clear - Hk. revert n0. induction Hk; intros [|n0]; simpl; auto.
    + induction H; simpl; constructor; auto.
Qed.

Lemma map_ldyn_lbound : forall n F Ts,
  frame_bound n F -> Forall (lbound n) (map (ldyn F) Ts).
Proof.
  intros. induction Ts; simpl; constructor; auto using ldyn_lbound.
Qed.

Lemma obj_frame_bound : forall n qo b c As,
  (forall w, b = Some w -> w < n) -> (forall w, c = Some w -> w < n) ->
  Forall (lbound n) As -> frame_bound n (obj_frame qo b c As).
Proof.
  intros n qo b c As Hb Hc HAs. unfold frame_bound, obj_frame. simpl.
  repeat split; auto.
  - destruct b; simpl; auto.
  - destruct c; simpl; auto.
Qed.

Lemma lsuper_inst_lbound : forall CT qo b c C As D Vs n,
  lsuper_inst CT qo b c C As D Vs ->
  (forall w, b = Some w -> w < n) -> (forall w, c = Some w -> w < n) ->
  Forall (lbound n) As -> Forall (lbound n) Vs.
Proof.
  intros CT qo b c C As D Vs n H Hb Hc. induction H; intros HAs; auto.
  apply IHlsuper_inst. apply map_ldyn_lbound. apply obj_frame_bound; auto.
Qed.

(** A fresh world identifier does not change the normal form of a bounded
    label, so opening a world keeps agreement between bounded types. *)
Lemma norm_push : forall L n l, lab_bound n l -> norm (n :: L) l = norm L l.
Proof.
  intros L n [w|] Hb; simpl in Hb; [|reflexivity]. unfold norm.
  destruct (in_dec Nat.eq_dec w (n :: L)) as [[Heq | i]|ni];
    destruct (in_dec Nat.eq_dec w L) as [i'|ni']; auto; try lia; try contradiction.
  exfalso. apply ni. right. exact i'.
Qed.

Lemma lagree_push : forall L n A B,
  lagree L A B -> lbound n A -> lbound n B -> lagree (n :: L) A B.
Proof.
  intros L n A B H. induction H using lagree_ind'. intros HA HB.
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

Lemma Forall2_lagree_push : forall L n As Bs,
  Forall2 (lagree L) As Bs -> Forall (lbound n) As -> Forall (lbound n) Bs ->
  Forall2 (lagree (n :: L)) As Bs.
Proof.
  intros L n As Bs H. induction H; intros HA HB; constructor;
    inversion HA; inversion HB; subst; auto using lagree_push.
Qed.

(* ------------------THE HEAP PART OF THE INVARIANT------------------*)

Record heapL (P : Loc -> Prop) (CT : class_table) (h : heap) (G : ghost)
    (L : list nat) (next : nat) : Prop := {
  (* an object in a world exists, is unprotected, is really mutable, and was
     born in that world *)
  hl_col : forall l w, g_col G l = Some w ->
    l < dom h /\ ~ P l /\ r_muttype h l = Some Mut_r /\ w < next /\
    g_birth G l = Some w;
  (* the labelled type arguments are a labelling of the stored ones *)
  hl_erase : forall l o, runtime_getObj h l = Some o ->
    map erase (g_args G l) = rtargs (rt_type o);
  (* every field value inhabits the field's declared type as the object
     itself reads it *)
  hl_fields : forall l o fs f fd v,
    runtime_getObj h l = Some o ->
    CollectFields CT (rctype (rt_type o)) fs ->
    nth_error fs f = Some fd ->
    nth_error (fields_map o) f = Some (Iot v) ->
    lhas CT h G L v
      (ldyn (obj_frame (rqtype (rt_type o)) (g_birth G l) (g_col G l)
               (g_args G l)) (ftype fd));
  hl_live : forall w, List.In w L -> w < next;
  (* world identifiers in the ghost state are below the next fresh one *)
  hl_bound : forall l,
    Forall (lbound next) (g_args G l) /\
    (forall w, g_birth G l = Some w -> w < next);
}.

(** The label side condition for a member access through a receiver, from
    the receiver's ordinary and label typing. *)
Lemma recv_label_cond : forall P CT h G L next mt v o qx C Ts qthis wf mode
    lc lm lk ca ma ka,
  heapL P CT h G L next ->
  List.In wf L ->
  readonly_state_method_scope mt ->
  runtime_getObj h v = Some o ->
  wf_r_typable CT h v (TClass qx C Ts) qthis ca ma ka ->
  lhas CT h G L v (ldyn (act_frame qthis wf mode lc lm lk) (TClass qx C Ts)) ->
  label_cond L (vpa_q mt qx)
    (obj_frame (rqtype (rt_type o)) (g_birth G v) (g_col G v) [])
    (act_frame qthis wf mode lc lm lk).
Proof.
  intros P CT h G L next mt v o qx C Ts qthis wf mode lc lm lk ca ma ka
    HG HwfL Hrs Ho Hty Hl.
  destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ _ Hty)
    as (o' & Vs & Ho' & Hhead & _).
  rewrite Ho in Ho'. inversion Ho'; subst o'. clear Ho'.
  assert (Hnb : qx <> Bot).
  { intros ->. exact (typable_head_not_bot _ _ _ _ _ _ _ _ Hty eq_refl). }
  destruct Hl as (o' & Ho' & Hh & _).
  change (headL L (g_col G v) (dynq (qr2q qthis) qx)
            (lab_of (act_frame qthis wf mode lc lm lk) qx)) in Hh.
  unfold headL in Hh.
  apply rs_label_cond; auto.
  - intros ->. specialize (Hh eq_refl).
    change (lab_of (act_frame qthis wf mode lc lm lk) Mut) with (LIn wf) in Hh.
    rewrite (norm_live _ _ HwfL) in Hh. split; auto.
    destruct (hl_col _ _ _ _ _ _ HG _ _ Hh) as (_ & _ & _ & _ & Hb). exact Hb.
  - intros -> Hqo. rewrite Hqo in Hhead.
    assert (qthis = Mut_r).
    { destruct qthis; auto. unfold head_ok in Hhead. simpl in Hhead.
      destruct Hhead as [Hx | [Hx | Hx]]; discriminate. }
    subst qthis. specialize (Hh eq_refl).
    change (lab_of (act_frame Mut_r wf mode lc lm lk) RDM)
      with (if mode then LIn wf else LOut) in Hh.
    destruct mode.
    + rewrite (norm_live _ _ HwfL) in Hh. exact Hh.
    + exact Hh.
Qed.

(* ------------------SOUNDNESS OF SUBTYPING FOR LABELS------------------*)

(** Label side of the bounds: when a type variable's bound reads as mutable
    in a view, the argument supplied for it carries, at its head, the label
    that the view gives to the bound's head. *)
Definition frame_lbounds (L : list nat) (Δ : tv_env) (F : lframe) : Prop :=
  forall o n qb C Ts lA CA AsA,
    tv_bound Δ o n = Some (TClass qb C Ts) ->
    ldyn F (TVar TVSub o n) = LT Mut lA CA AsA ->
    dynq (lf_q F) qb = Mut ->
    norm L lA = norm L (lab_of F qb).

(** The object is in world [wf] and was born there. *)
Definition exact (G : ghost) (wf : nat) (v : Loc) : Prop :=
  g_col G v = Some wf /\ g_birth G v = Some wf.

(** A value held at a type written mutable is exactly in the world. *)
Definition hexT (G : ghost) (wf : nat) (T : qualified_type) (v : Loc) : Prop :=
  whead T = Some Mut -> exact G wf v.

Lemma rs_label_cond2 : forall L mt qo b c oargs qthis wf mode cs ms ks qx,
  readonly_state_method_scope mt ->
  head_ok qo (dynq (qr2q qthis) qx) ->
  qx <> Bot ->
  (qx = Mut -> c = Some wf /\ b = Some wf) ->
  (qx = RDM -> qo = Mut_r ->
     if mode then c = Some wf else forall w, c = Some w -> ~ List.In w L) ->
  label_cond L (vpa_q mt qx) (obj_frame qo b c oargs)
    (act_frame qthis wf mode cs ms ks).
Proof.
  intros L mt qo b c oargs qthis wf mode cs ms ks qx Hrs Hhead Hnb Hmut Hrdm q0.
  split.
  - unfold obj_frame, act_frame. simpl lf_q.
    apply dynq_vpa_q_agree; [apply qr2q_concrete | apply qr2q_concrete | exact Hhead].
  - unfold obj_frame, act_frame. simpl lf_q.
    unfold head_ok in Hhead.
    destruct Hrs as [-> | ->];
      destruct q0, qx; simpl;
      try (left; reflexivity);
      try (right; left; destruct qo; simpl; discriminate);
      try congruence;
      try (destruct (Hmut eq_refl) as [-> ->]; right; right; reflexivity);
      destruct qo; simpl;
      try (right; left; discriminate);
      try (destruct qthis; simpl in Hhead;
           destruct Hhead as [Hx | [Hx | Hx]]; discriminate);
      destruct qthis; simpl in *;
      try (left; reflexivity);
      try (destruct Hhead as [Hx | [Hx | Hx]]; discriminate);
      specialize (Hrdm eq_refl eq_refl); right; right;
      destruct mode; subst; simpl; auto;
      destruct c as [w|]; simpl; auto;
      apply norm_dead; apply Hrdm; reflexivity.
Qed.

(** A type variable used at its bound. *)
Lemma lhas_var_bound : forall P CT Δ h G L next qthis wf mode lc lm lk ca ma ka o n B v,
  heapL P CT h G L next ->
  closed_clean_bounds Δ ->
  frame_lbounds L Δ (act_frame qthis wf mode lc lm lk) ->
  frame_bounds_ok CT Δ (qr2q qthis) ca ma ka ->
  map erase lc = ca -> map erase lm = ma -> map fst lk = ka ->
  tv_bound Δ o n = Some B ->
  wf_r_typable CT h v (TVar TVSub o n) qthis ca ma ka ->
  lhas CT h G L v (ldyn (act_frame qthis wf mode lc lm lk) (TVar TVSub o n)) ->
  lhas CT h G L v (ldyn (act_frame qthis wf mode lc lm lk) B).
Proof.
  intros P CT Δ h G L next qthis wf mode lc lm lk ca ma ka o n B v
    HG Hcb Hfl Hfb Hec Hem Hek Hbound Hty Hl.
  set (Fc := act_frame qthis wf mode lc lm lk) in *.
  destruct (Hcb _ _ _ Hbound) as (qb & Cb & Tb & -> & Hqb & Hclargs).
  pose proof (wf_r_typable_subtype _ _ _ _ _ _ _ _ _ _ Hfb
                (qtype_var_bound CT Δ o n _ Hbound) Hty) as Hty'.
  destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ _ Hty')
    as (ob & Rs' & Hob & _ & Hrs' & Hle').
  destruct (lsuper_inst_exists _ _ _ _ _ _ Hrs' (rqtype (rt_type ob))
              (g_birth G v) (g_col G v) (g_args G v) eq_refl
              (hl_erase _ _ _ _ _ _ HG _ _ Hob)) as (Vs & Hs & He).
  exists ob. split; auto. cbn [ldyn]. split.
  - unfold headL. intros Hm.
    assert (Hq : qb = RDM /\ qthis = Mut_r).
    { change (lf_q Fc) with (qr2q qthis) in Hm.
      destruct qb; simpl in Hm; try discriminate; try congruence.
      destruct qthis; simpl in Hm; try discriminate; auto. }
    destruct Hq as [-> ->].
    destruct (ldyn Fc (TVar TVSub o n)) as [qA lA CA AsA] eqn:HA.
    assert (He0 : dyn (qr2q Mut_r) ca ma ka (TVar TVSub o n) =
                  RClass qA CA (map erase AsA)).
    { rewrite <- Hec. rewrite <- Hem. try rewrite <- Hek.
      change (dyn (qr2q Mut_r) (map erase lc) (map erase lm) (map fst lk) (TVar TVSub o n))
        with (dyn (lf_q Fc) (map erase (lf_cargs Fc)) (map erase (lf_margs Fc))
                (map fst (lf_qargs Fc))
                (TVar TVSub o n)).
      rewrite <- erase_ldyn. rewrite HA. reflexivity. }
    pose proof (Hfb _ _ _ Hbound) as Hsub. rewrite He0 in Hsub.
    cbn [dyn] in Hsub. unfold rtype_subtype in Hsub.
    unfold wf_r_typable in Hty. rewrite He0 in Hty.
    unfold loc_has_rtype in Hty. rewrite Hob in Hty. destruct Hty as [Hhd _].
    assert (HqA : qA = Mut).
    { destruct Hsub as [[Hbot _] | [Hrq _]].
      - subst qA. exfalso. exact (head_ok_not_bot _ Hhd).
      - simpl in Hrq. unfold rq_sub in Hrq.
        destruct Hrq as [Hx | [Hx | [Hx _]]]; congruence. }
    subst qA.
    pose proof (Hfl _ _ _ _ _ _ _ _ Hbound HA eq_refl) as Hn.
    destruct Hl as (ob' & Hob' & Hh & _).
    rewrite <- Hn. exact (Hh eq_refl).
  - exists Vs. split; auto.
    apply Forall2_lagree_of_rarg_nomut.
    + rewrite He. rewrite map_erase_ldyn. simpl. rewrite Hec. rewrite Hem. try rewrite Hek.
      exact Hle'.
    + clear - Hclargs. induction Hclargs; simpl; constructor;
        auto using ldyn_closed_clean_nomut.
Qed.

(** Subtyping keeps labels.  The activation's world need not be live when
    the activation does not count its receiver as in the world; what is
    needed instead is that a value held at a type written mutable is exactly
    in that world, and this is kept too. *)
Lemma lhas_subtype_ex : forall P CT Δ h G L next mt qthis wf mode lc lm lk ca ma ka,
  heapL P CT h G L next ->
  (mode = true -> List.In wf L) ->
  readonly_state_method_scope mt ->
  tv_mode Δ = mt ->
  (forall o n B v,
     tv_bound Δ o n = Some B ->
     wf_r_typable CT h v (TVar TVSub o n) qthis ca ma ka ->
     lhas CT h G L v (ldyn (act_frame qthis wf mode lc lm lk) (TVar TVSub o n)) ->
     lhas CT h G L v (ldyn (act_frame qthis wf mode lc lm lk) B)) ->
  (forall o n B, tv_bound Δ o n = Some B -> whead B <> Some Mut) ->
  frame_bounds_ok CT Δ (qr2q qthis) ca ma ka ->
  map erase lc = ca -> map erase lm = ma -> map fst lk = ka ->
  forall T U,
    qualified_type_subtype CT Δ T U ->
    forall v,
      wf_r_typable CT h v T qthis ca ma ka ->
      hexT G wf T v ->
      lhas CT h G L v (ldyn (act_frame qthis wf mode lc lm lk) T) ->
      lhas CT h G L v (ldyn (act_frame qthis wf mode lc lm lk) U) /\
      hexT G wf U v.
Proof.
  intros P CT Δ h G L next mt qthis wf mode lc lm lk ca ma ka
    HG HwfL Hrs Hmode Hcb Hfl Hfb Hec Hem Hek T U Hsub.
  set (Fc := act_frame qthis wf mode lc lm lk).
  induction Hsub; intros v Hty Hex Hl.
  - (* same class, widen the qualifier *)
    split.
    + destruct Hl as (o & Ho & Hh & Vs & Hs & Hle).
      exists o. split; auto. simpl. split.
      * unfold headL. intros Hm. inversion Hqsub; subst.
        -- apply Hh. exact Hm.
        -- simpl in Hm. discriminate.
        -- exfalso. exact (typable_head_not_bot _ _ _ _ _ _ _ _ Hty eq_refl).
      * exists Vs. split; auto.
        eapply Forall2_lagree_trans; [exact Hle|].
        apply map_ldyn_targ_sub; auto.
    + intros Hw. simpl in Hw. inversion Hw; subst q2. inversion Hqsub; subst.
      * apply Hex. reflexivity.
      * exfalso. exact (typable_head_not_bot _ _ _ _ _ _ _ _ Hty eq_refl).
  - (* up the hierarchy *)
    split; [|exact Hex].
    pose proof Hl as (o & Ho & Hh & As & Hs & Hle).
    rewrite Hmode in Hsuper.
    assert (Hcond : label_cond L (vpa_q mt q1)
                      (obj_frame (rqtype (rt_type o)) (g_birth G v) (g_col G v) [])
                      Fc).
    { destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ _ Hty)
        as (o' & Vs' & Ho' & Hhead & _).
      rewrite Ho in Ho'. inversion Ho'; subst o'. clear Ho'.
      assert (Hnb : q1 <> Bot).
      { intros ->. exact (typable_head_not_bot _ _ _ _ _ _ _ _ Hty eq_refl). }
      change (headL L (g_col G v) (dynq (qr2q qthis) q1) (lab_of Fc q1)) in Hh.
      unfold headL in Hh.
      apply rs_label_cond2; auto.
      - intros ->. destruct (Hex eq_refl) as [Hc Hb]. auto.
      - intros -> Hqo. rewrite Hqo in Hhead.
        assert (qthis = Mut_r).
        { destruct qthis; auto. unfold head_ok in Hhead. simpl in Hhead.
          destruct Hhead as [Hx | [Hx | Hx]]; discriminate. }
        subst qthis. specialize (Hh eq_refl).
        change (lab_of Fc RDM) with (if mode then LIn wf else LOut) in Hh.
        destruct mode.
        + rewrite (norm_live _ _ (HwfL eq_refl)) in Hh. exact Hh.
        + exact Hh. }
    destruct (super_inst_ldyn _ _ _ _ _ _ _ Hsuper L _ _ _ Fc As Hcond Hle)
      as (Vs0 & Hs0 & Hle0).
    exists o. split; auto. simpl. split; [exact Hh|].
    exists Vs0. split; auto. eapply lsuper_inst_trans; eauto.
  - split; assumption.
  - (* a type variable at its bound *)
    split.
    + eapply Hcb; eauto.
    + intros Hw. exfalso. exact (Hfl _ _ _ Hbound Hw).
  - (* widen the written qualifier of a variable use *)
    split.
    + destruct Hl as (ob & Hob & Hl). exists ob. split; auto.
      simpl in *.
      destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
        as [qa la Ca Aa].
      simpl in *. destruct Hl as (Hh & Vs & Hs & Hle).
      split; [|eauto].
      unfold headL. intros Hm. inversion Hqsub; subst.
      * apply Hh. exact Hm.
      * simpl in Hm. discriminate.
      * exfalso. eapply (typable_whead_not_bot _ _ _ _ _ _ _ _ Hty). reflexivity.
    + intros Hw. simpl in Hw. inversion Hw; subst q2. inversion Hqsub; subst.
      * apply Hex. reflexivity.
      * exfalso. eapply (typable_whead_not_bot _ _ _ _ _ _ _ _ Hty). reflexivity.
  - (* view the supplied type as readonly *)
    split; [|intros Hw; simpl in Hw; discriminate].
    destruct Hl as (ob & Hob & Hl). exists ob. split; auto.
    simpl in *.
    destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
      as [qa la Ca Aa].
    simpl in *. destruct Hl as (Hh & Vs & Hs & Hle).
    split; [|eauto]. unfold headL. intros Hm. discriminate.
  - split; assumption.
  - (* a use under a qualifier parameter, viewed as readonly *)
    split; [|intros Hw; simpl in Hw; discriminate].
    destruct Hl as (ob & Hob & Hl). exists ob. split; auto.
    simpl in *.
    destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
      as [qa la Ca Aa].
    simpl in *. destruct Hl as (Hh & Vs & Hs & Hle).
    split; [|eauto]. unfold headL. intros Hm. discriminate.
  - (* a qualified variable use at an argument-free bound *)
    split; [|exact Hex].
    pose proof (wf_r_typable_subtype _ _ _ _ _ _ _ _ _ _ Hfb
                  (qtype_qvar_bound CT Δ q1 o n qb C Hsub) Hty) as Hty'.
    destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ _ Hty')
      as (ob & Rs' & Hob & _ & Hrs' & Hle').
    simpl in Hle'. inversion Hle'; subst.
    destruct (lsuper_inst_exists _ _ _ _ _ _ Hrs' (rqtype (rt_type ob))
                (g_birth G v) (g_col G v) (g_args G v) eq_refl
                (hl_erase _ _ _ _ _ _ HG _ _ Hob)) as (Vs & Hs & He).
    apply map_eq_nil in He. subst Vs.
    destruct Hl as (ob' & Hob' & Hl).
    exists ob. split; auto. simpl. split.
    + simpl in Hl.
      destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
        as [qa la Ca Aa].
      simpl in Hl. tauto.
    + exists (@nil ltype). split; [exact Hs | constructor].
  - (* a variable-headed class type viewed as readonly *)
    split; [|intros Hw; simpl in Hw; discriminate].
    destruct Hl as (ob & Hob & Hl). exists ob. split; auto.
    simpl in *.
    simpl in *. destruct Hl as (Hh & Vs & Hs & Hle).
    split; [unfold headL; intros Hm; discriminate|].
    exists Vs. split; auto.
    eapply Forall2_lagree_trans; [exact Hle|].
    apply map_ldyn_targ_sub; auto.
  - (* compatible arguments under the same variable head *)
    split; [|intros Hw; simpl in Hw; discriminate].
    destruct Hl as (ob & Hob & Hl). exists ob. split; auto.
    simpl in *.
    simpl in *. destruct Hl as (Hh & Vs & Hs & Hle).
    split; [exact Hh|].
    exists Vs. split; auto.
    eapply Forall2_lagree_trans; [exact Hle|].
    apply map_ldyn_targ_sub; auto.
  - (* up the hierarchy under the same variable head *)
    split; [|intros Hw; simpl in Hw; discriminate].
    rewrite Hmode in Hsuper.
    destruct Hl as (ob & Hob & Hl).
    assert (Hcond : label_cond L (vpa_q mt RO)
                      (obj_frame (rqtype (rt_type ob)) (g_birth G v) (g_col G v) [])
                      Fc).
    { apply rs_label_cond2; auto; try discriminate.
      unfold head_ok. left. reflexivity. }
    exists ob. split; auto.
    cbn [ldyn map_qual] in Hl |- *.
destruct Hl as (Hh & As & Hs & Hle).
    destruct (super_inst_ldyn _ _ _ _ _ _ _ Hsuper L _ _ _ Fc As Hcond Hle)
      as (Vs0 & Hs0 & Hle0).
    split; [exact Hh|].
    exists Vs0. split; auto. eapply lsuper_inst_trans; eauto.
  - (* the bottom-qualified type of the class *)
    exfalso. exact (typable_head_not_bot _ _ _ _ _ _ _ _ Hty eq_refl).
  - (* transitivity *)
    destruct (IHHsub1 v Hty Hex Hl) as [Hl2 Hex2].
    apply IHHsub2; auto.
    eapply wf_r_typable_subtype; eauto.
Qed.

(** In a live world, a value held at a type written mutable is exactly in
    it. *)
Lemma hex_of_live : forall P CT h G L next qthis wf mode lc lm lk T v,
  heapL P CT h G L next -> List.In wf L ->
  lhas CT h G L v (ldyn (act_frame qthis wf mode lc lm lk) T) ->
  hexT G wf T v.
Proof.
  intros P CT h G L next qthis wf mode lc lm lk T v HG HwfL Hl Hw.
  assert (Hc : g_col G v = Some wf).
  { destruct T as [q0 C args | [|q0|mp] o n | n C args]; simpl in Hw;
      inversion Hw; subst.
    - destruct Hl as (ob & _ & Hh & _). specialize (Hh eq_refl).
      change (lab_of (act_frame qthis wf mode lc lm lk) Mut) with (LIn wf) in Hh.
      rewrite (norm_live _ _ HwfL) in Hh. exact Hh.
    - destruct Hl as (ob & _ & Hl). simpl in Hl.
      destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
        as [qa la Ca Aa].
      simpl in Hl. destruct Hl as (Hh & _). specialize (Hh eq_refl).
      rewrite (norm_live _ _ HwfL) in Hh. exact Hh. }
  split; auto.
  destruct (hl_col _ _ _ _ _ _ HG _ _ Hc) as (_ & _ & _ & _ & Hb). exact Hb.
Qed.

Lemma lhas_subtype : forall P CT Δ h G L next mt qthis wf mode lc lm lk ca ma ka,
  heapL P CT h G L next ->
  List.In wf L ->
  readonly_state_method_scope mt ->
  tv_mode Δ = mt ->
  (forall o n B v,
     tv_bound Δ o n = Some B ->
     wf_r_typable CT h v (TVar TVSub o n) qthis ca ma ka ->
     lhas CT h G L v (ldyn (act_frame qthis wf mode lc lm lk) (TVar TVSub o n)) ->
     lhas CT h G L v (ldyn (act_frame qthis wf mode lc lm lk) B)) ->
  (forall o n B, tv_bound Δ o n = Some B -> whead B <> Some Mut) ->
  frame_bounds_ok CT Δ (qr2q qthis) ca ma ka ->
  map erase lc = ca -> map erase lm = ma -> map fst lk = ka ->
  forall T U,
    qualified_type_subtype CT Δ T U ->
    forall v,
      wf_r_typable CT h v T qthis ca ma ka ->
      lhas CT h G L v (ldyn (act_frame qthis wf mode lc lm lk) T) ->
      lhas CT h G L v (ldyn (act_frame qthis wf mode lc lm lk) U).
Proof.
  intros P CT Δ h G L next mt qthis wf mode lc lm lk ca ma ka
    HG HwfL Hrs Hmode Hcb Hfl Hfb Hec Hem Hek T U Hsub v Hty Hl.
  destruct (lhas_subtype_ex P CT Δ h G L next mt qthis wf mode lc lm lk ca ma ka
              HG (fun _ => HwfL) Hrs Hmode Hcb Hfl Hfb Hec Hem Hek T U Hsub v Hty
              (hex_of_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG HwfL Hl) Hl) as [H _].
  exact H.
Qed.

(* ------------------FIELDS ACROSS INHERITANCE------------------*)

(** A field found through a superclass view is, in the object's own class, at
    the same index with the same assignability, and the object reads its
    declared type to the same labelled type either way. *)
Lemma lfield_inherit : forall CT qo b c Co Ao C Vs,
  lsuper_inst CT qo b c Co Ao C Vs ->
  forall fsC fsO f fd,
    CollectFields CT C fsC ->
    CollectFields CT Co fsO ->
    nth_error fsC f = Some fd ->
    exists fd',
      nth_error fsO f = Some fd' /\
      assignability fd' = assignability fd /\
      ldyn (obj_frame qo b c Ao) (ftype fd') =
      ldyn (obj_frame qo b c Vs) (ftype fd).
Proof.
  intros CT qo b c Co Ao C Vs H.
  induction H; intros fsC fsO f fd HcfC HcfO Hnth.
  - assert (fsO = fsC) by eauto using collect_fields_deterministic_rel.
    subst. eauto.
  - destruct (CollectFields_inherit_inv _ _ _ _ _ Hparent HcfO)
      as (def & pfs & Hfind & Hpcf & ->).
    destruct (IHlsuper_inst fsC pfs f fd HcfC Hpcf Hnth)
      as (fdP & HnthP & Hassign & Hdyn).
    exists (subst_field Ss fdP). split; [|split].
    + rewrite nth_error_app1.
      * rewrite length_map. apply nth_error_Some. congruence.
      * rewrite nth_error_map. rewrite HnthP. reflexivity.
    + exact Hassign.
    + simpl. rewrite ldyn_subst. simpl. exact Hdyn.
Qed.
