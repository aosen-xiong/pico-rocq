From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping PreservationCases PreservationCall ReadonlyFlat ReadonlyWorlds GhostLabels.

(** Superclass views that read a class header off the type arguments.

    A mutable position written in a class's header (its bounds and its
    superclass arguments) is not given one world per object.  It is read as
    the label found in the type arguments at the position where one of the
    class's bounds writes a mutable position (the payload); a class with no
    such bound reads it as the reader's own label.  An object and a labelled
    type that agree on their arguments therefore agree on every view. *)

(* ------------------READERS------------------*)

(** How a labelled type's head reads the qualifiers written in a superclass
    argument.  An object reads them as written. *)
Definition tg (qA : q) (q0 : q) : q :=
  match q0 with
  | Mut => match qA with Mut => Mut | _ => Lost end
  | RDM => match qA with Mut | Imm => RDM | Bot => Bot | _ => Lost end
  | _ => q0
  end.

(** A reader with an open payload reads written mutable positions as
    unknown. *)
Definition kill (g : q -> q) (q0 : q) : q :=
  match q0 with Mut => Lost | _ => g q0 end.

(** The qualifier map and the mutable label selected by a payload node.  A
    labelled type leaves written mutable positions open when its payload is
    open ([k = true]); an object keeps reading them through its own label. *)
Definition rd_map (k : bool) (g : q -> q) (pn : option (q * lab)) : q -> q :=
  match pn with
  | Some (Lost, _) => if k then kill g else g
  | _ => g
  end.

Definition rd_lab (d : lab) (pn : option (q * lab)) : lab :=
  match pn with
  | Some (Mut, l) => l
  | _ => d
  end.

(** The frame through which a reader with head [hq], own label [d] and
    arguments [As] reads its class's header. *)
Definition hframe (hq : q) (d : lab) (pn : option (q * lab)) (As : list ltype)
    : lframe :=
  mk_lframe hq (rd_lab d pn) d As [] [].

Definition hstep (k : bool) (hq : q) (g : q -> q) (d : lab)
    (pn : option (q * lab)) (As : list ltype) (Ss : list qualified_type)
    : list ltype :=
  map (fun S => ldyn (hframe hq d pn As) (map_qual (rd_map k g pn) S)) Ss.

(* ------------------THE PAYLOAD------------------*)

(** A labelled type at a superclass, reading every header through the
    type's own head.  This is only used to locate the payload. *)
Fixpoint tviewf (CT : class_table) (n : nat) (q0 : q) (l : lab)
    (C : class_name) (As : list ltype) (D : class_name)
    : option (list ltype) :=
  match n with
  | 0 => None
  | S n' =>
      if Nat.eqb C D then Some As
      else match parent_lookup CT C with
           | Some (P, Ss) =>
               tviewf CT n' q0 l P (hstep true q0 (tg q0) l None As Ss) D
           | None => None
           end
  end.

(** The node of a labelled argument at the first mutable position written in
    a bound.  The argument is viewed at the bound's class; below that, the
    bound and the view are walked together. *)
Fixpoint pwalk (CT : class_table) (B : qualified_type) (A : ltype)
    : option (q * lab) :=
  match B, A with
  | TVar (TVQual Mut) _ _, LT q0 l _ _ => Some (q0, l)
  | TVar _ _ _, _ => None
  | TClass qb D Bs, LT q0 l C As =>
      match qb with
      | Mut => Some (q0, l)
      | _ =>
          match tviewf CT (S C) q0 l C As D with
          | Some Vs =>
              (fix go (Bs : list qualified_type) (Vs : list ltype)
                 : option (q * lab) :=
                 match Bs, Vs with
                 | B' :: Bs', V :: Vs' =>
                     match pwalk CT B' V with
                     | Some x => Some x
                     | None => go Bs' Vs'
                     end
                 | _, _ => None
                 end) Bs Vs
          | None => None
          end
      end
  | THead _ D Bs, LT q0 l C As =>
      match tviewf CT (S C) q0 l C As D with
      | Some Vs =>
          (fix go (Bs : list qualified_type) (Vs : list ltype)
             : option (q * lab) :=
             match Bs, Vs with
             | B' :: Bs', V :: Vs' =>
                 match pwalk CT B' V with
                 | Some x => Some x
                 | None => go Bs' Vs'
                 end
             | _, _ => None
             end) Bs Vs
      | None => None
      end
  end.

Fixpoint pwalks (CT : class_table) (Bs : list qualified_type)
    (Vs : list ltype) : option (q * lab) :=
  match Bs, Vs with
  | B' :: Bs', V :: Vs' =>
      match pwalk CT B' V with
      | Some x => Some x
      | None => pwalks CT Bs' Vs'
      end
  | _, _ => None
  end.

(** An argument that no value can have (the type of null only) says nothing
    about the payload. *)
Definition pfindf (CT : class_table) (B : qualified_type) (A : ltype)
    : option (q * lab) :=
  match A with
  | LT Bot _ _ _ => None
  | _ => pwalk CT B A
  end.

Fixpoint pfindsf (CT : class_table) (Bs : list qualified_type)
    (Vs : list ltype) : option (q * lab) :=
  match Bs, Vs with
  | B' :: Bs', V :: Vs' =>
      match pfindf CT B' V with
      | Some x => Some x
      | None => pfindsf CT Bs' Vs'
      end
  | _, _ => None
  end.

(** The payload node of a class for given arguments. *)
Definition pclassf (CT : class_table) (C : class_name) (As : list ltype)
    : option (q * lab) :=
  match find_class CT C with
  | Some def => pfindsf CT (ctparams (signature def)) As
  | None => None
  end.

(* ------------------VIEWS------------------*)

(** The arguments at a superclass, each header read through the payload. *)
Inductive view (CT : class_table) (k : bool) (hq : q) (g : q -> q) (d : lab)
    : class_name -> list ltype -> class_name -> list ltype -> Prop :=
  | v_refl : forall C As, view CT k hq g d C As C As
  | v_step : forall C As P Ss D Vs
      (Hparent : parent_lookup CT C = Some (P, Ss))
      (Hrest : view CT k hq g d P
                 (hstep k hq g d (pclassf CT C As) As Ss) D Vs),
      view CT k hq g d C As D Vs.

(** What an object reads, and what a labelled type reads. *)
Definition oview (CT : class_table) (qo : q_r) (c : lab) :=
  view CT false (qr2q qo) (fun q0 => q0) c.

Definition tview (CT : class_table) (qA : q) (lA : lab) :=
  view CT true qA (tg qA) lA.

(* ------------------BASIC FACTS------------------*)

Lemma view_le : forall CT k hq g d C As D Vs,
  wf_class_table CT -> view CT k hq g d C As D Vs -> D <= C.
Proof.
  intros CT k hq g d C As D Vs Hwf H. induction H; auto.
  unfold parent_lookup in Hparent.
  destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
  destruct (wf_class_super_inv _ _ _ _ _ Hwf Hfind Hparent) as (sd & _ & Hlt & _).
  lia.
Qed.

Lemma parent_lt : forall CT C P Ss,
  wf_class_table CT -> parent_lookup CT C = Some (P, Ss) -> P < C.
Proof.
  intros CT C P Ss Hwf Hparent. unfold parent_lookup in Hparent.
  destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
  destruct (wf_class_super_inv _ _ _ _ _ Hwf Hfind Hparent) as (sd & _ & Hlt & _).
  lia.
Qed.

Lemma view_deterministic : forall CT k hq g d C As D Vs,
  wf_class_table CT -> view CT k hq g d C As D Vs ->
  forall Vs', view CT k hq g d C As D Vs' -> Vs = Vs'.
Proof.
  intros CT k hq g d C As D Vs Hwf H. induction H; intros Vs' H2.
  - inversion H2; subst; auto.
    exfalso. pose proof (view_le _ _ _ _ _ _ _ _ _ Hwf Hrest) as Hle.
    pose proof (parent_lt _ _ _ _ Hwf Hparent). lia.
  - inversion H2; subst.
    + exfalso. pose proof (view_le _ _ _ _ _ _ _ _ _ Hwf H) as Hle.
      pose proof (parent_lt _ _ _ _ Hwf Hparent). lia.
    + rewrite Hparent in Hparent0. inversion Hparent0; subst.
      apply IHview. exact Hrest.
Qed.

Lemma view_trans : forall CT k hq g d C As D Vs,
  view CT k hq g d C As D Vs ->
  forall E Ws, view CT k hq g d D Vs E Ws -> view CT k hq g d C As E Ws.
Proof.
  intros CT k hq g d C As D Vs H. induction H; intros E Ws H2; auto.
  eapply v_step; eauto.
Qed.

(* ------------------AGREEMENT------------------*)

(** A qualifier map of a reader: a written mutable position stays mutable or
    becomes unknown; any other qualifier stays, becomes unknown, or becomes
    the bottom qualifier. *)
Definition gok (g : q -> q) : Prop :=
  (g Mut = Mut \/ g Mut = Lost) /\
  forall q0, q0 <> Mut -> g q0 = q0 \/ g q0 = Lost \/ g q0 = Bot.

(** Two readers of the same class header: the second reads no more than the
    first, and where both read a mutable position their own labels agree. *)
Definition rrel (L : list nat) (hq : q) (g : q -> q) (d : lab)
    (hq' : q) (g' : q -> q) (d' : lab) : Prop :=
  forall q0,
    arg_q_sub (dynq hq (g q0)) (dynq hq' (g' q0)) /\
    (dynq hq' (g' q0) = Lost \/ dynq hq (g q0) <> Mut \/
     norm L d = norm L d').

(** Two payload nodes: the second is the first, or leaves it open. *)
Definition nrel (L : list nat) (pn pn' : option (q * lab)) : Prop :=
  match pn, pn' with
  | None, None => True
  | Some (q1, l1), Some (q2, l2) =>
      arg_q_sub q1 q2 /\ (q2 = Lost \/ q1 <> Mut \/ norm L l1 = norm L l2)
  | _, _ => False
  end.

Definition lc2 (L : list nat) (g f : q -> q) (Fo Fc : lframe) : Prop :=
  forall q0,
    arg_q_sub (dynq (lf_q Fo) (g q0)) (dynq (lf_q Fc) (f q0)) /\
    (dynq (lf_q Fc) (f q0) = Lost \/ dynq (lf_q Fo) (g q0) <> Mut \/
     norm L (lab_of Fo (g q0)) = norm L (lab_of Fc (f q0))).

Lemma ldyn_agree2 : forall L g f Fo Fc T,
  lc2 L g f Fo Fc ->
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

Lemma gok_id : gok (fun q0 => q0).
Proof. split; auto. Qed.

Lemma gok_tg : forall qA, gok (tg qA).
Proof.
  intros qA. split.
  - destruct qA; simpl; auto.
  - intros q0 Hne. destruct q0, qA; simpl; auto; congruence.
Qed.


Lemma rd_map_other : forall k g pn q0, q0 <> Mut -> rd_map k g pn q0 = g q0.
Proof.
  intros k g pn q0 Hne. destruct pn as [[q1 l1]|]; simpl; auto.
  destruct q1; simpl; auto. destruct k; auto.
  destruct q0; simpl; auto. congruence.
Qed.

Lemma rd_map_keep : forall k g q1 l1,
  q1 <> Lost -> rd_map k g (Some (q1, l1)) = g.
Proof. intros k g q1 l1 Hne. destruct q1; simpl; auto. congruence. Qed.

Lemma rd_lab_other : forall d q1 l1, q1 <> Mut -> rd_lab d (Some (q1, l1)) = d.
Proof. intros d q1 l1 Hne. destruct q1; simpl; auto. congruence. Qed.

(** The readers of one step, after the payload is taken into account.  The
    second reader is a labelled type. *)
Lemma step_cond : forall L k hq g d hq' g' d' pn pn' As As',
  gok g -> gok g' -> rrel L hq g d hq' g' d' -> nrel L pn pn' ->
  lc2 L (rd_map k g pn) (rd_map true g' pn')
    (hframe hq d pn As) (hframe hq' d' pn' As').
Proof.
  intros L k hq g d hq' g' d' pn pn' As As' [Hgm Hgo] [Hgm' Hgo'] Hr Hn q0.
  cbn [hframe lf_q].
  destruct (q_eq_dec q0 Mut) as [-> | Hne].
  - (* a written mutable position *)
    assert (Hbase : forall lm lm',
              norm L lm = norm L lm' \/
              (lm = d /\ lm' = d') ->
              arg_q_sub (dynq hq (g Mut)) (dynq hq' (g' Mut)) /\
              (dynq hq' (g' Mut) = Lost \/ dynq hq (g Mut) <> Mut \/
               norm L (lab_of (mk_lframe hq lm d As [] []) (g Mut)) =
               norm L (lab_of (mk_lframe hq' lm' d' As' [] []) (g' Mut)))).
    { intros lm lm' Hlm. destruct (Hr Mut) as [H1 H2]. split; [exact H1|].
      destruct Hgm as [E | E]; rewrite E in H1, H2 |- *;
        [|right; left; simpl; discriminate].
      destruct Hgm' as [E' | E']; rewrite E' in H1, H2 |- *;
        [|left; reflexivity].
      destruct H2 as [H2 | [H2 | H2]]; auto.
      right. right. simpl.
      destruct Hlm as [Hlm | [-> ->]]; auto. }
    destruct pn as [[q1 l1]|], pn' as [[q2 l2]|]; simpl in Hn; try contradiction.
    + destruct Hn as [Hq Hl].
      destruct (q_eq_dec q2 Lost) as [-> | Hn2].
      * (* the second payload is open *)
        assert (Htgt : rd_map true g' (Some (Lost, l2)) Mut = Lost)
          by reflexivity.
        rewrite Htgt. split; [|left; reflexivity].
        assert (Hsrc : dynq hq (rd_map k g (Some (q1, l1)) Mut) = Mut \/
                       dynq hq (rd_map k g (Some (q1, l1)) Mut) = Lost).
        { destruct q1, k; simpl; destruct Hgm as [E | E]; try rewrite E;
            simpl; auto. }
        change (dynq hq' Lost) with Lost.
        destruct Hsrc as [E | E]; rewrite E; unfold arg_q_sub; auto.
      * assert (q2 = q1).
        { unfold arg_q_sub in Hq. destruct Hq as [Hx | [Hx _]]; congruence. }
        subst q2.
        rewrite (rd_map_keep k g q1 l1 Hn2).
        rewrite (rd_map_keep true g' q1 l2 Hn2).
        unfold hframe.
        destruct (q_eq_dec q1 Mut) as [-> | Hq1].
        -- simpl rd_lab. apply Hbase. left.
           destruct Hl as [Hx | [Hx | Hx]]; congruence.
        -- rewrite (rd_lab_other d q1 l1 Hq1). rewrite (rd_lab_other d' q1 l2 Hq1).
           apply Hbase. right. auto.
    + simpl rd_map. unfold hframe. simpl rd_lab. apply Hbase. right. auto.
  - (* any other written qualifier *)
    rewrite (rd_map_other k g pn q0 Hne). rewrite (rd_map_other true g' pn' q0 Hne).
    destruct (Hr q0) as [H1 H2]. split; [exact H1|].
    destruct H2 as [H2 | [H2 | H2]]; auto.
    destruct (q_eq_dec (dynq hq (g q0)) Mut) as [Hs | Hs]; [|auto].
    destruct (q_eq_dec (dynq hq' (g' q0)) Lost) as [Ht | Ht]; [auto|].
    right. right.
    destruct (Hgo q0 Hne) as [E | [E | E]]; rewrite E in H1, Hs |- *;
      try (simpl in Hs; discriminate).
    assert (q0 = RDM) by (destruct q0; simpl in Hs; congruence).
    subst q0. rewrite Hs in H1.
    destruct (Hgo' RDM Hne) as [E' | [E' | E']]; rewrite E' in H1, Ht |- *.
    + simpl. exact H2.
    + simpl in Ht. congruence.
    + simpl in H1. unfold arg_q_sub in H1.
      destruct H1 as [Hx | [Hx _]]; discriminate.
Qed.

(** Two labelled types that agree at the head read a header compatibly. *)
Lemma tg_rrel : forall L q0 l q0' l',
  arg_q_sub q0 q0' ->
  (q0' = Lost \/ q0 <> Mut \/ norm L l = norm L l') ->
  rrel L q0 (tg q0) l q0' (tg q0') l'.
Proof.
  intros L q0 l q0' l' Hq Hl q1. unfold arg_q_sub in Hq.
  destruct Hq as [-> | [-> Hm]].
  - split; [left; reflexivity|].
    destruct (q_eq_dec q0 Mut) as [-> | Hne].
    + destruct Hl as [Hx | [Hx | Hx]]; try congruence. auto.
    + right. left. destruct q0, q1; simpl; congruence.
  - destruct Hm as [-> | [-> | ->]]; destruct q1; simpl; unfold arg_q_sub;
      (split; [auto | auto]); try (right; left; discriminate).
Qed.

Lemma hstep_agree : forall L k hq g d hq' g' d' pn pn' As As' Ss,
  gok g -> gok g' -> rrel L hq g d hq' g' d' -> nrel L pn pn' ->
  Forall2 (lagree L) As As' ->
  Forall2 (lagree L) (hstep k hq g d pn As Ss) (hstep true hq' g' d' pn' As' Ss).
Proof.
  intros L k hq g d hq' g' d' pn pn' As As' Ss Hg Hg' Hr Hn Hle.
  unfold hstep. induction Ss as [|S Ss IH]; simpl; constructor; auto.
  apply ldyn_agree2.
  - apply step_cond; auto.
  - exact Hle.
  - constructor.
  - reflexivity.
Qed.

(* ------------------THE PAYLOAD RESPECTS AGREEMENT------------------*)

Definition orel (L : list nat) (o1 o2 : option (list ltype)) : Prop :=
  match o1, o2 with
  | Some Vs, Some Vs' => Forall2 (lagree L) Vs Vs'
  | None, None => True
  | _, _ => False
  end.

Lemma tviewf_agree : forall CT L n q0 l q0' l' C As As' D,
  arg_q_sub q0 q0' ->
  (q0' = Lost \/ q0 <> Mut \/ norm L l = norm L l') ->
  Forall2 (lagree L) As As' ->
  orel L (tviewf CT n q0 l C As D) (tviewf CT n q0' l' C As' D).
Proof.
  intros CT L n q0 l q0' l' C As As' D Hq Hl.
  revert C As As'. induction n as [|n IH]; intros C As As' Hle; simpl; auto.
  destruct (Nat.eqb C D); [exact Hle|].
  destruct (parent_lookup CT C) as [[P Ss]|]; simpl; auto.
  apply IH. apply hstep_agree; auto using gok_tg, tg_rrel. exact I.
Qed.

Lemma pfindf_bot : forall CT B l C As, pfindf CT B (LT Bot l C As) = None.
Proof. reflexivity. Qed.

Lemma pfindf_notbot : forall CT B q0 l C As,
  q0 <> Bot -> pfindf CT B (LT q0 l C As) = pwalk CT B (LT q0 l C As).
Proof. intros CT B q0 l C As Hq. destruct q0; try congruence; reflexivity. Qed.

Lemma pwalk_mut : forall CT D Bs q0 l C As,
  pwalk CT (TClass Mut D Bs) (LT q0 l C As) = Some (q0, l).
Proof. reflexivity. Qed.

Lemma pwalk_class : forall CT qb D Bs q0 l C As,
  qb <> Mut ->
  pwalk CT (TClass qb D Bs) (LT q0 l C As) =
  match tviewf CT (S C) q0 l C As D with
  | Some Vs => pwalks CT Bs Vs
  | None => None
  end.
Proof.
  intros CT qb D Bs q0 l C As Hqb.
  assert (Hgo : forall Bs0 Vs0,
            (fix go (Bs : list qualified_type) (Vs : list ltype)
               : option (q * lab) :=
               match Bs, Vs with
               | B' :: Bs', V :: Vs' =>
                   match pwalk CT B' V with
                   | Some x => Some x
                   | None => go Bs' Vs'
                   end
               | _, _ => None
               end) Bs0 Vs0 = pwalks CT Bs0 Vs0).
  { induction Bs0 as [|B0 Bs0 IH]; intros [|V0 Vs0]; simpl; auto.
    destruct (pwalk CT B0 V0); auto. }
  destruct qb; try congruence; cbn [pwalk];
    destruct (tviewf CT (S C) q0 l C As D); auto.
Qed.

Lemma pwalk_head : forall CT n D Bs q0 l C As,
  pwalk CT (THead n D Bs) (LT q0 l C As) =
  match tviewf CT (S C) q0 l C As D with
  | Some Vs => pwalks CT Bs Vs
  | None => None
  end.
Proof.
  intros CT n D Bs q0 l C As.
  assert (Hgo : forall Bs0 Vs0,
            (fix go (Bs : list qualified_type) (Vs : list ltype)
               : option (q * lab) :=
               match Bs, Vs with
               | B' :: Bs', V :: Vs' =>
                   match pwalk CT B' V with
                   | Some x => Some x
                   | None => go Bs' Vs'
                   end
               | _, _ => None
               end) Bs0 Vs0 = pwalks CT Bs0 Vs0).
  { induction Bs0 as [|B0 Bs0 IH]; intros [|V0 Vs0]; simpl; auto.
    destruct (pwalk CT B0 V0); auto. }
  cbn [pwalk]. destruct (tviewf CT (S C) q0 l C As D); auto.
Qed.

Lemma nrel_none : forall L, nrel L None None.
Proof. intros. exact I. Qed.

Lemma pwalks_agree : forall CT L Bs,
  Forall (fun B => forall A A', lagree L A A' ->
                     nrel L (pwalk CT B A) (pwalk CT B A')) Bs ->
  forall Vs Vs', Forall2 (lagree L) Vs Vs' ->
    nrel L (pwalks CT Bs Vs) (pwalks CT Bs Vs').
Proof.
  intros CT L Bs HBs. induction HBs as [|B Bs HB HBs IH];
    intros Vs Vs' Hle; simpl; [exact I|].
  destruct Hle as [|V V' Vs Vs' HV Hrest]; [exact I|].
  pose proof (HB V V' HV) as Hn.
  destruct (pwalk CT B V) as [[q1 l1]|], (pwalk CT B V') as [[q2 l2]|];
    simpl in Hn; try contradiction.
  - exact Hn.
  - apply IH. exact Hrest.
Qed.

Lemma pwalk_agree : forall CT L B A A',
  lagree L A A' -> nrel L (pwalk CT B A) (pwalk CT B A').
Proof.
  intros CT L B. induction B using qualified_type_ind'; intros A A' Hle.
  - inversion Hle as [q1 l1 q2 l2 C0 As As' Hq Hlab Hargs]; subst.
    destruct (q_eq_dec qual Mut) as [-> | Hqb].
    + simpl. split; auto.
    + rewrite (pwalk_class CT qual C args q1 l1 C0 As Hqb).
      rewrite (pwalk_class CT qual C args q2 l2 C0 As' Hqb).
      pose proof (tviewf_agree CT L (S C0) q1 l1 q2 l2 C0 As As' C Hq Hlab Hargs)
        as Hv.
      destruct (tviewf CT (S C0) q1 l1 C0 As C) as [Vs|],
               (tviewf CT (S C0) q2 l2 C0 As' C) as [Vs'|];
        simpl in Hv; try contradiction; [|exact I].
      apply pwalks_agree; auto.
  - inversion Hle as [q1 l1 q2 l2 C0 As As' Hq Hlab Hargs]; subst.
    destruct u as [|[]|]; simpl; try exact I. split; auto.
  - inversion Hle as [q1 l1 q2 l2 C0 As As' Hq Hlab Hargs]; subst.
    rewrite (pwalk_head CT n C args q1 l1 C0 As).
    rewrite (pwalk_head CT n C args q2 l2 C0 As').
    pose proof (tviewf_agree CT L (S C0) q1 l1 q2 l2 C0 As As' C Hq Hlab Hargs)
      as Hv.
    destruct (tviewf CT (S C0) q1 l1 C0 As C) as [Vs|],
             (tviewf CT (S C0) q2 l2 C0 As' C) as [Vs'|];
      simpl in Hv; try contradiction; [|exact I].
    apply pwalks_agree; auto.
Qed.

Lemma pfindf_agree : forall CT L B A A',
  lagree L A A' -> nrel L (pfindf CT B A) (pfindf CT B A').
Proof.
  intros CT L B A A' Hle.
  inversion Hle as [q1 l1 q2 l2 C0 As As' Hq Hlab Hargs]; subst.
  destruct (q_eq_dec q1 Bot) as [-> | Hq1].
  - assert (q2 = Bot).
    { unfold arg_q_sub in Hq. destruct Hq as [Hx | [_ [Hx | [Hx | Hx]]]]; congruence. }
    subst q2. exact I.
  - assert (Hq2 : q2 <> Bot).
    { unfold arg_q_sub in Hq. destruct Hq as [Hx | [Hx _]]; congruence. }
    rewrite (pfindf_notbot CT B q1 l1 C0 As Hq1).
    rewrite (pfindf_notbot CT B q2 l2 C0 As' Hq2).
    apply pwalk_agree. exact Hle.
Qed.

Lemma pfindsf_agree : forall CT L Bs Vs Vs',
  Forall2 (lagree L) Vs Vs' ->
  nrel L (pfindsf CT Bs Vs) (pfindsf CT Bs Vs').
Proof.
  intros CT L Bs. induction Bs as [|B Bs IH]; intros Vs Vs' Hle; simpl;
    [exact I|].
  destruct Hle as [|V V' Vs Vs' HV Hrest]; [exact I|].
  pose proof (pfindf_agree CT L B V V' HV) as Hn.
  destruct (pfindf CT B V) as [[q1 l1]|], (pfindf CT B V') as [[q2 l2]|];
    simpl in Hn; try contradiction.
  - exact Hn.
  - apply IH. exact Hrest.
Qed.

Lemma pclassf_agree : forall CT L C As As',
  Forall2 (lagree L) As As' ->
  nrel L (pclassf CT C As) (pclassf CT C As').
Proof.
  intros CT L C As As' Hle. unfold pclassf.
  destruct (find_class CT C) as [def|]; [|exact I].
  apply pfindsf_agree; auto.
Qed.

(* ------------------VIEWS RESPECT AGREEMENT------------------*)

(** Readers that read a header compatibly, on arguments that agree, see
    views that agree. *)
Lemma view_agree : forall CT k hq g d C As D Vs,
  wf_class_table CT ->
  view CT k hq g d C As D Vs ->
  forall L hq' g' d' As' Vs',
    gok g -> gok g' -> rrel L hq g d hq' g' d' ->
    Forall2 (lagree L) As As' ->
    view CT true hq' g' d' C As' D Vs' -> Forall2 (lagree L) Vs Vs'.
Proof.
  intros CT k hq g d C As D Vs Hwf H.
  induction H; intros L hq' g' d' As' Vs' Hg Hg' Hr Hle H2.
  - inversion H2; subst; auto.
    exfalso. pose proof (view_le _ _ _ _ _ _ _ _ _ Hwf Hrest) as Hle2.
    pose proof (parent_lt _ _ _ _ Hwf Hparent). lia.
  - inversion H2; subst.
    + exfalso. pose proof (view_le _ _ _ _ _ _ _ _ _ Hwf H) as Hle2.
      pose proof (parent_lt _ _ _ _ Hwf Hparent). lia.
    + rewrite Hparent in Hparent0. inversion Hparent0; subst.
      eapply (IHview L hq' g' d'); eauto.
      apply hstep_agree; auto. apply pclassf_agree. exact Hle.
Qed.

(** A view that a labelled type has is had by any reader that reads at
    least as much, on arguments that agree into the type's. *)
Lemma view_transfer : forall CT hq' g' d' C As' D Vs',
  view CT true hq' g' d' C As' D Vs' ->
  forall L k hq g d As,
    gok g -> gok g' -> rrel L hq g d hq' g' d' ->
    Forall2 (lagree L) As As' ->
    exists Vs, view CT k hq g d C As D Vs.
Proof.
  intros CT hq' g' d' C As' D Vs' H.
  induction H; intros L k hq g d As0 Hg Hg' Hr Hle.
  - exists As0. constructor.
  - destruct (IHview L k hq g d
                (hstep k hq g d (pclassf CT C As0) As0 Ss) Hg Hg' Hr)
      as (Vs0 & Hv).
    { apply hstep_agree; auto. apply pclassf_agree. exact Hle. }
    exists Vs0. eapply v_step; eauto.
Qed.

(* ------------------AN OBJECT AGAINST A LABELLED TYPE------------------*)

(** An object reads a header at least as fully as a labelled type whose head
    it may be seen through, when its own label agrees with a mutable head. *)
Lemma obj_type_rrel : forall L qo c qA lA,
  head_ok qo qA ->
  (qA = Mut -> norm L c = norm L lA) ->
  rrel L (qr2q qo) (fun q0 => q0) c qA (tg qA) lA.
Proof.
  intros L qo c qA lA Hhead Hl q0. unfold head_ok in Hhead.
  destruct Hhead as [-> | [-> | ->]].
  - destruct qo, q0; simpl; unfold arg_q_sub; split; auto;
      try (right; left; discriminate).
  - destruct qo, q0; simpl; unfold arg_q_sub; split; auto;
      try (right; left; discriminate).
  - destruct qo; simpl in *.
    + split; [destruct q0; simpl; left; reflexivity|].
      right. right. apply Hl. reflexivity.
    + destruct q0; simpl; unfold arg_q_sub; split; auto;
        try (right; left; discriminate).
Qed.

(** The view of an object and the view of a labelled type it inhabits agree,
    and the object's view exists whenever the type's does.  Nothing is asked
    of the world the object was created in. *)
Theorem obj_vs_type : forall CT L qo c Ao qA lA As C D Vt,
  wf_class_table CT ->
  head_ok qo qA ->
  (qA = Mut -> norm L c = norm L lA) ->
  Forall2 (lagree L) Ao As ->
  tview CT qA lA C As D Vt ->
  exists Vo, oview CT qo c C Ao D Vo /\ Forall2 (lagree L) Vo Vt.
Proof.
  intros CT L qo c Ao qA lA As C D Vt Hwf Hhead Hl Hle Hv.
  unfold tview in Hv. unfold oview.
  pose proof (obj_type_rrel L qo c qA lA Hhead Hl) as Hr.
  destruct (view_transfer _ _ _ _ _ _ _ _ Hv L false (qr2q qo) (fun q0 => q0)
              c Ao gok_id (gok_tg _) Hr Hle) as (Vo & Hvo).
  exists Vo. split; auto.
  exact (view_agree _ _ _ _ _ _ _ _ _ Hwf Hvo L _ _ _ _ _ gok_id (gok_tg _)
           Hr Hle Hv).
Qed.

(* ------------------OBJECT VIEWS AND ORDINARY VIEWS------------------*)

Lemma rd_map_obj : forall pn, rd_map false (fun q0 : q => q0) pn = (fun q0 => q0).
Proof. intros [[[] l]|]; reflexivity. Qed.

Lemma map_erase_hstep_obj : forall qo c pn As Ss,
  map erase (hstep false (qr2q qo) (fun q0 => q0) c pn As Ss) =
  map (dyn (qr2q qo) (map erase As) [] []) Ss.
Proof.
  intros qo c pn As Ss. unfold hstep. rewrite rd_map_obj.
  rewrite map_map. apply map_ext. intros S.
  rewrite map_qual_id. rewrite erase_ldyn. reflexivity.
Qed.

(** An object's view erases to its ordinary view, and every ordinary view
    has one. *)
Lemma oview_erase : forall CT qo c C As D Vs,
  oview CT qo c C As D Vs ->
  rsuper_inst CT (qr2q qo) C (map erase As) D (map erase Vs).
Proof.
  intros CT qo c C As D Vs H. unfold oview in H. induction H.
  - apply rsi_refl.
  - eapply rsi_step; eauto.
    rewrite <- (map_erase_hstep_obj qo c (pclassf CT C As)). exact IHview.
Qed.

Lemma oview_exists : forall CT qh C Rs D Rs',
  rsuper_inst CT qh C Rs D Rs' ->
  forall qo c As, qh = qr2q qo -> map erase As = Rs ->
  exists Vs, oview CT qo c C As D Vs /\ map erase Vs = Rs'.
Proof.
  intros CT qh C Rs D Rs' H. induction H; intros qo c As Hq HAs.
  - exists As. split; [apply v_refl | exact HAs].
  - subst qh Rs.
    destruct (IHrsuper_inst qo c
                (hstep false (qr2q qo) (fun q0 => q0) c (pclassf CT C As) As Ss)
                eq_refl) as [Vs0 [Hs He]].
    { apply map_erase_hstep_obj. }
    exists Vs0. split; auto. unfold oview. eapply v_step; eauto.
Qed.

Lemma oview_deterministic : forall CT qo c C As D Vs1,
  wf_class_table CT -> oview CT qo c C As D Vs1 ->
  forall Vs2, oview CT qo c C As D Vs2 -> Vs1 = Vs2.
Proof. intros. eapply view_deterministic; eauto. Qed.

Lemma oview_trans : forall CT qo c C As D Vs,
  oview CT qo c C As D Vs ->
  forall E Ws, oview CT qo c D Vs E Ws -> oview CT qo c C As E Ws.
Proof. intros. eapply view_trans; eauto. Qed.

Print Assumptions obj_vs_type.
Print Assumptions oview_exists.
