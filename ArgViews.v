From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping PreservationCases PreservationCall ReadonlyFlat ReadonlyWorlds GhostLabels.

(** Place in the proof: superclass views that read a class header off an
    object's type arguments, the payload (the first mutable position a view
    reaches) and the readers that find it, agreement between views, and the
    plain view used by the object clauses of the invariant.
    Counterpart in the non-generic proof (ReadonlyWorlds.v): "what a static
    head says about a value", extended from the head to the arguments. *)

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

(** The same search with the header qualifiers read by an explicit map. *)
Fixpoint tviewg (CT : class_table) (n : nat) (q0 : q) (g : q -> q) (l : lab)
    (C : class_name) (As : list ltype) (D : class_name)
    : option (list ltype) :=
  match n with
  | 0 => None
  | S n' =>
      if Nat.eqb C D then Some As
      else match parent_lookup CT C with
           | Some (P, Ss) =>
               tviewg CT n' q0 g l P (hstep true q0 g l None As Ss) D
           | None => None
           end
  end.

(** A bottom-headed argument has no object behind it, so the mutable
    positions written in its class chain hold nothing: the payload search
    reads them as bottom.  Only the nodes the argument carries in its own
    type arguments keep their qualifiers. *)
Definition tgb (q0 : q) : q :=
  match q0 with Mut => Bot | _ => tg Bot q0 end.

Definition prd (qA : q) : q -> q :=
  match qA with Bot => tgb | _ => tg qA end.

(** An unknown argument does not say which world the mutable position it
    covers belongs to: a node found in it is reported as unknown. *)
Definition popen (q0 : q) (l : lab) (r : option (q * lab)) : option (q * lab) :=
  match q0, r with
  | Lost, Some _ => Some (Lost, l)
  | _, _ => r
  end.

(** The node of a labelled argument at the first mutable position written in
    a bound.  The argument is viewed at the bound's class; below that, the
    bound and the view are walked together.  A bottom node says nothing, and
    the search moves on. *)
Definition pnode (q0 : q) (l : lab) : option (q * lab) :=
  match q0 with Bot => None | _ => Some (q0, l) end.

(** At a bound position written mutable, a node that is not bottom is the
    payload candidate itself.  A bottom node there is the bottom reader's
    rendering of a re-headed copy ([@Mut E] with a bottom argument), so the
    search descends into it as at any other class position. *)
Definition pdir (qb q0 : q) : bool :=
  match qb, q0 with
  | Mut, Bot => false
  | Mut, _ => true
  | _, _ => false
  end.

Fixpoint pwalk (CT : class_table) (B : qualified_type) (A : ltype)
    : option (q * lab) :=
  match B, A with
  | TVar (TVQual Mut) _ _, LT q0 l _ _ => pnode q0 l
  | TVar _ _ _, _ => None
  | TClass qb D Bs, LT q0 l C As =>
      if pdir qb q0 then pnode q0 l
      else
        match tviewg CT (S C) q0 (prd q0) l C As D with
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
  | THead _ D Bs, LT q0 l C As =>
      match tviewg CT (S C) q0 (prd q0) l C As D with
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

Definition pfindf (CT : class_table) (B : qualified_type) (A : ltype)
    : option (q * lab) :=
  match A with
  | LT q0 l _ _ => popen q0 l (pwalk CT B A)
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

(** The arguments at a superclass.  An object ([k = false]) reads each
    header's written mutable positions through its payload; a labelled type
    ([k = true]) reads them with its own label and nothing else. *)
Definition vpay (k : bool) (CT : class_table) (C : class_name) (As : list ltype)
    : option (q * lab) :=
  if k then None else pclassf CT C As.

Inductive view (CT : class_table) (k : bool) (hq : q) (g : q -> q) (d : lab)
    : class_name -> list ltype -> class_name -> list ltype -> Prop :=
  | v_refl : forall C As, view CT k hq g d C As C As
  | v_step : forall C As P Ss D Vs
      (Hparent : parent_lookup CT C = Some (P, Ss))
      (Hrest : view CT k hq g d P
                 (hstep k hq g d (vpay k CT C As) As Ss) D Vs),
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
  (g Mut = Mut \/ g Mut = Lost \/ g Mut = Bot) /\
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
  | None, Some (Lost, _) => True
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

(* ------------------AGREEMENT WITH A DEAD CLAIM------------------*)

(** A labelled type whose mutable node carries a dead label claims nothing
    about the world of that node: an object it types may hold a node of any
    world there.  Agreement of an object's reading into such a type is
    [lagree] with that one escape. *)
Inductive dagree (L : list nat) : ltype -> ltype -> Prop :=
  | da_node : forall q1 l1 q2 l2 C As Bs
      (Hq : arg_q_sub q1 q2)
      (Hlab : q2 = Lost \/ q1 <> Mut \/ norm L l2 = None \/ norm L l1 = norm L l2)
      (Hargs : Forall2 (dagree L) As Bs),
      dagree L (LT q1 l1 C As) (LT q2 l2 C Bs).

Section dagree_ind'.
  Variable L : list nat.
  Variable P : ltype -> ltype -> Prop.
  Hypothesis Hnode : forall q1 l1 q2 l2 C As Bs,
    arg_q_sub q1 q2 ->
    (q2 = Lost \/ q1 <> Mut \/ norm L l2 = None \/ norm L l1 = norm L l2) ->
    Forall2 (dagree L) As Bs ->
    Forall2 P As Bs ->
    P (LT q1 l1 C As) (LT q2 l2 C Bs).

  Fixpoint dagree_ind' A B (H : dagree L A B) : P A B :=
    match H with
    | da_node _ q1 l1 q2 l2 C As Bs Hq Hlab Hargs =>
        Hnode q1 l1 q2 l2 C As Bs Hq Hlab Hargs
          ((fix go As Bs (Hl : Forall2 (dagree L) As Bs) : Forall2 P As Bs :=
              match Hl with
              | Forall2_nil _ => Forall2_nil P
              | Forall2_cons t u Ht Hr =>
                  Forall2_cons t u (dagree_ind' t u Ht) (go _ _ Hr)
              end) As Bs Hargs)
    end.
End dagree_ind'.

Lemma lagree_dagree : forall L A B, lagree L A B -> dagree L A B.
Proof.
  intros L A B H. induction H using lagree_ind'. constructor; auto.
  destruct H0 as [H0 | [H0 | H0]]; auto 6.
Qed.

Lemma dagree_refl : forall L A, dagree L A A.
Proof. intros L A. apply lagree_dagree. apply lagree_refl. Qed.

(** Every mutable node of a labelled type carries a live label. *)
Fixpoint mlive (L : list nat) (A : ltype) : Prop :=
  match A with
  | LT q0 l _ args =>
      (q0 = Mut -> norm L l <> None) /\
      (fix go (ls : list ltype) : Prop :=
         match ls with
         | [] => True
         | t :: r => mlive L t /\ go r
         end) args
  end.

(** The per-qualifier condition for [dagree] between two readings. *)
Definition lc2d (L : list nat) (g f : q -> q) (Fo Fc : lframe) : Prop :=
  forall q0,
    arg_q_sub (dynq (lf_q Fo) (g q0)) (dynq (lf_q Fc) (f q0)) /\
    (dynq (lf_q Fc) (f q0) = Lost \/ dynq (lf_q Fo) (g q0) <> Mut \/
     norm L (lab_of Fc (f q0)) = None \/
     norm L (lab_of Fo (g q0)) = norm L (lab_of Fc (f q0))).

Lemma lc2_lc2d : forall L g f Fo Fc, lc2 L g f Fo Fc -> lc2d L g f Fo Fc.
Proof.
  intros L g f Fo Fc H q0. destruct (H q0) as [H1 H2]. split; auto.
  destruct H2 as [H2 | [H2 | H2]]; auto 6.
Qed.

Lemma ldyn_dagree2 : forall L g f Fo Fc T,
  lc2d L g f Fo Fc ->
  Forall2 (dagree L) (lf_cargs Fo) (lf_cargs Fc) ->
  Forall2 (dagree L) (lf_margs Fo) (lf_margs Fc) ->
  lf_qargs Fo = lf_qargs Fc ->
  dagree L (ldyn Fo (map_qual g T)) (ldyn Fc (map_qual f T)).
Proof.
  intros L g f Fo Fc T Hq Hc Hm Hqs.
  induction T using qualified_type_ind'.
  - simpl. destruct (Hq qual) as [H1 H2]. constructor; auto.
    induction H; simpl; constructor; auto.
  - pose proof (tv_lookup_Forall2 (dagree L) o _ _ _ _ n Hc Hm) as Hl.
    assert (HA : dagree L
              match tv_lookup o (lf_cargs Fo) (lf_margs Fo) n with
              | Some A => A | None => ldefault end
              match tv_lookup o (lf_cargs Fc) (lf_margs Fc) n with
              | Some A => A | None => ldefault end).
    { destruct (tv_lookup o (lf_cargs Fo) (lf_margs Fo) n),
               (tv_lookup o (lf_cargs Fc) (lf_margs Fc) n);
        try contradiction; auto using dagree_refl. }
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

(** A payload of the first reader is acceptable to the second: it is a node
    of the second's own world, or the second does not read written mutable
    positions as mutable, or the first does not. *)
Definition pok (L : list nat) (hq : q) (g : q -> q) (hq' : q) (g' : q -> q)
    (d' : lab) (pn : option (q * lab)) : Prop :=
  forall w, pn = Some (Mut, w) ->
    norm L w = norm L d' \/ dynq hq' (g' Mut) = Lost \/ dynq hq (g Mut) <> Mut.

(** The readers of one step at a qualifier other than [Mut]. *)
Lemma step_cond_other : forall L k hq g d hq' g' d' pn As As',
  gok g -> gok g' -> rrel L hq g d hq' g' d' ->
  forall q0, q0 <> Mut ->
    arg_q_sub (dynq (lf_q (hframe hq d pn As)) (rd_map k g pn q0))
      (dynq (lf_q (hframe hq' d' None As')) (rd_map true g' None q0)) /\
    (dynq (lf_q (hframe hq' d' None As')) (rd_map true g' None q0) = Lost \/
     dynq (lf_q (hframe hq d pn As)) (rd_map k g pn q0) <> Mut \/
     norm L (lab_of (hframe hq d pn As) (rd_map k g pn q0)) =
     norm L (lab_of (hframe hq' d' None As') (rd_map true g' None q0))).
Proof.
  intros L k hq g d hq' g' d' pn As As' [Hgm Hgo] [Hgm' Hgo'] Hr q0 Hne.
  cbn [hframe lf_q].
  rewrite (rd_map_other k g pn q0 Hne). rewrite (rd_map_other true g' None q0 Hne).
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

(** The readers of one step.  The second reader is a labelled type, which
    takes no payload. *)
Lemma step_cond : forall L k hq g d hq' g' d' pn As As',
  gok g -> gok g' -> rrel L hq g d hq' g' d' ->
  (k = true -> pn = None) -> pok L hq g hq' g' d' pn ->
  lc2 L (rd_map k g pn) (rd_map true g' None)
    (hframe hq d pn As) (hframe hq' d' None As').
Proof.
  intros L k hq g d hq' g' d' pn As As' Hg Hg' Hr Hk Hp q0.
  pose proof Hg as [Hgm Hgo]. pose proof Hg' as [Hgm' Hgo'].
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
      destruct Hgm as [E | [E | E]]; rewrite E in H1, H2 |- *;
        [|right; left; simpl; discriminate..].
      destruct Hgm' as [E' | [E' | E']]; rewrite E' in H1, H2 |- *;
        [|left; reflexivity|].
      2:{ exfalso. simpl in H1. unfold arg_q_sub in H1.
          destruct H1 as [Hx | [Hx _]]; discriminate. }
      destruct H2 as [H2 | [H2 | H2]]; auto.
      right. right. simpl.
      destruct Hlm as [Hlm | [-> ->]]; auto. }
    cbn [rd_map rd_lab].
    destruct pn as [[q1 l1]|].
    + destruct (q_eq_dec q1 Lost) as [-> | Hn1].
      * (* an open payload: only an object carries one *)
        destruct k; [discriminate (Hk eq_refl)|]. simpl rd_map. unfold hframe.
        simpl rd_lab. apply Hbase. right. auto.
      * rewrite (rd_map_keep k g q1 l1 Hn1). unfold hframe.
        destruct (q_eq_dec q1 Mut) as [-> | Hq1].
        -- simpl rd_lab.
           destruct (Hp l1 eq_refl) as [Hw | [Hw | Hw]].
           ++ apply Hbase. left. exact Hw.
           ++ destruct (Hr Mut) as [H1 _]. split; [exact H1 | left; exact Hw].
           ++ destruct (Hr Mut) as [H1 _]. split; [exact H1 | right; left; exact Hw].
        -- rewrite (rd_lab_other d q1 l1 Hq1). apply Hbase. right. auto.
    + simpl rd_map. unfold hframe. simpl rd_lab. apply Hbase. right. auto.
  - exact (step_cond_other L k hq g d hq' g' d' pn As As' Hg Hg' Hr q0 Hne).
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
  - destruct Hm as [-> | [-> | [-> | [-> | ->]]]]; destruct q1; simpl; unfold arg_q_sub;
      (split; [auto 8 | auto 8]); try (right; left; discriminate).
Qed.

Lemma hstep_agree : forall L k hq g d hq' g' d' pn As As' Ss,
  gok g -> gok g' -> rrel L hq g d hq' g' d' ->
  (k = true -> pn = None) -> pok L hq g hq' g' d' pn ->
  Forall2 (lagree L) As As' ->
  Forall2 (lagree L) (hstep k hq g d pn As Ss) (hstep true hq' g' d' None As' Ss).
Proof.
  intros L k hq g d hq' g' d' pn As As' Ss Hg Hg' Hr Hk Hp Hle.
  unfold hstep. induction Ss as [|S Ss IH]; simpl; constructor; auto.
  apply ldyn_agree2.
  - apply step_cond; auto.
  - exact Hle.
  - constructor.
  - reflexivity.
Qed.

(* ------------------THE SAME WITH THE DEAD ESCAPE------------------*)

(** A payload of the first reader is acceptable to the second with the
    escape: as before, or the second's own label is dead. *)
Definition pokd (L : list nat) (hq : q) (g : q -> q) (hq' : q) (g' : q -> q)
    (d' : lab) (pn : option (q * lab)) : Prop :=
  forall w, pn = Some (Mut, w) ->
    norm L w = norm L d' \/ norm L d' = None \/
    dynq hq' (g' Mut) = Lost \/ dynq hq (g Mut) <> Mut.

Lemma lift3 : forall (A P Q R S : Prop), A /\ (P \/ Q \/ R) -> A /\ (P \/ Q \/ S \/ R).
Proof. intros A P Q R S [H1 [H2 | [H2 | H2]]]; auto 6. Qed.

Lemma step_cond_d : forall L k hq g d hq' g' d' pn As As',
  gok g -> gok g' -> rrel L hq g d hq' g' d' ->
  (k = true -> pn = None) -> pokd L hq g hq' g' d' pn ->
  lc2d L (rd_map k g pn) (rd_map true g' None)
    (hframe hq d pn As) (hframe hq' d' None As').
Proof.
  intros L k hq g d hq' g' d' pn As As' Hg Hg' Hr Hk Hp q0.
  destruct (q_eq_dec q0 Mut) as [-> | Hne];
    [| apply lift3; exact (step_cond_other L k hq g d hq' g' d' pn As As' Hg Hg' Hr q0 Hne)].
  destruct pn as [[q1 l1]|].
  - destruct (q_eq_dec q1 Mut) as [-> | Hq1].
    + destruct (Hp l1 eq_refl) as [Hw | [Hw | [Hw | Hw]]].
      * apply lift3. apply (step_cond L k hq g d hq' g' d' (Some (Mut, l1)) As As' Hg Hg' Hr Hk).
        intros w Hw'. inversion Hw'; subst. left. exact Hw.
      * (* the second reader's label is dead: the escape *)
        cbn [hframe lf_q lab_of].
        rewrite (rd_map_keep k g Mut l1 ltac:(discriminate)).
        change (rd_map true g' None) with g'.
        destruct (Hr Mut) as [H1 _]. split; [exact H1|].
        destruct Hg' as [[E | [E | E]] _]; rewrite E.
        -- right. right. left. cbn [lab_of lf_mut rd_lab]. exact Hw.
        -- left. reflexivity.
        -- right. right. left. reflexivity.
      * apply lift3. apply (step_cond L k hq g d hq' g' d' (Some (Mut, l1)) As As' Hg Hg' Hr Hk).
        intros w Hw'. inversion Hw'; subst. right. left. exact Hw.
      * apply lift3. apply (step_cond L k hq g d hq' g' d' (Some (Mut, l1)) As As' Hg Hg' Hr Hk).
        intros w Hw'. inversion Hw'; subst. right. right. exact Hw.
    + apply lift3. apply (step_cond L k hq g d hq' g' d' (Some (q1, l1)) As As' Hg Hg' Hr Hk).
      intros w Hw'. inversion Hw'; subst. congruence.
  - apply lift3. apply (step_cond L k hq g d hq' g' d' None As As' Hg Hg' Hr Hk).
    intros w Hw'. discriminate Hw'.
Qed.

Lemma hstep_agree_d : forall L k hq g d hq' g' d' pn As As' Ss,
  gok g -> gok g' -> rrel L hq g d hq' g' d' ->
  (k = true -> pn = None) -> pokd L hq g hq' g' d' pn ->
  Forall2 (dagree L) As As' ->
  Forall2 (dagree L) (hstep k hq g d pn As Ss) (hstep true hq' g' d' None As' Ss).
Proof.
  intros L k hq g d hq' g' d' pn As As' Ss Hg Hg' Hr Hk Hp Hle.
  unfold hstep. induction Ss as [|S Ss IH]; simpl; constructor; auto.
  apply ldyn_dagree2.
  - apply step_cond_d; auto.
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

Lemma pok_none : forall L hq g hq' g' d', pok L hq g hq' g' d' None.
Proof. intros L hq g hq' g' d' w H. discriminate H. Qed.

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
  apply IH. apply hstep_agree; auto using gok_tg, tg_rrel, pok_none.
Qed.

Lemma tviewg_agree : forall CT L n q0 g l q0' g' l' C As As' D,
  gok g -> gok g' -> rrel L q0 g l q0' g' l' ->
  Forall2 (lagree L) As As' ->
  orel L (tviewg CT n q0 g l C As D) (tviewg CT n q0' g' l' C As' D).
Proof.
  intros CT L n q0 g l q0' g' l' C As As' D Hg Hg' Hr.
  revert C As As'. induction n as [|n IH]; intros C As As' Hle; simpl; auto.
  destruct (Nat.eqb C D); [exact Hle|].
  destruct (parent_lookup CT C) as [[P Ss]|]; simpl; auto.
  apply IH. apply hstep_agree; auto using pok_none.
Qed.

Lemma tviewg_tg : forall CT n q0 l C As D,
  tviewg CT n q0 (tg q0) l C As D = tviewf CT n q0 l C As D.
Proof.
  intros CT n. induction n as [|n IH]; intros; simpl; auto.
  destruct (Nat.eqb C D); auto.
  destruct (parent_lookup CT C) as [[P Ss]|]; auto.
Qed.

Lemma prd_nb : forall q0, q0 <> Bot -> prd q0 = tg q0.
Proof. intros q0 H. destruct q0; simpl; congruence. Qed.

Lemma gok_prd : forall qA, gok (prd qA).
Proof.
  intros qA. destruct qA; try apply gok_tg.
  split; [simpl; auto|]. intros q0 Hne. destruct q0; simpl; auto; congruence.
Qed.

(** Two labelled types that agree at the head search their headers
    compatibly. *)
Lemma prd_rrel : forall L q0 l q0' l',
  arg_q_sub q0 q0' ->
  (q0' = Lost \/ q0 <> Mut \/ norm L l = norm L l') ->
  rrel L q0 (prd q0) l q0' (prd q0') l'.
Proof.
  intros L q0 l q0' l' Hq Hl.
  destruct (q_eq_dec q0 Bot) as [-> | Hb].
  - intros q1. unfold arg_q_sub in Hq. destruct Hq as [-> | [-> _]];
      destruct q1; simpl; unfold arg_q_sub; split; auto 8;
      right; left; discriminate.
  - assert (Hb' : q0' <> Bot).
    { unfold arg_q_sub in Hq. destruct Hq as [-> | [-> _]]; congruence. }
    rewrite (prd_nb q0 Hb). rewrite (prd_nb q0' Hb'). apply tg_rrel; auto.
Qed.

Lemma pnode_nrel : forall L q1 l1 q2 l2,
  arg_q_sub q1 q2 -> (q2 = Lost \/ q1 <> Mut \/ norm L l1 = norm L l2) ->
  nrel L (pnode q1 l1) (pnode q2 l2).
Proof.
  intros L q1 l1 q2 l2 Hq Hl. unfold arg_q_sub in Hq.
  destruct Hq as [-> | [-> Hm]].
  - destruct q1; simpl; auto. all: split; [left; reflexivity | exact Hl].
  - destruct Hm as [-> | [-> | [-> | [-> | ->]]]]; simpl; auto;
      split; unfold arg_q_sub; auto 8.
Qed.

Lemma pfindf_notbot : forall CT B q0 l C As,
  q0 <> Bot -> pfindf CT B (LT q0 l C As) = popen q0 l (pwalk CT B (LT q0 l C As)).
Proof. reflexivity. Qed.

Lemma popen_keep : forall q0 l r, q0 <> Lost -> popen q0 l r = r.
Proof. intros q0 l r Hq. destruct q0, r; simpl; auto; congruence. Qed.

Lemma pfindf_known : forall CT B q0 l C As,
  q0 <> Bot -> q0 <> Lost -> pfindf CT B (LT q0 l C As) = pwalk CT B (LT q0 l C As).
Proof.
  intros CT B q0 l C As Hb Hl. rewrite (pfindf_notbot CT B q0 l C As Hb).
  apply popen_keep; exact Hl.
Qed.

(** Reporting unknown arguments as unknown keeps payloads related. *)
Lemma popen_nrel : forall L q1 l1 r q2 l2 r',
  arg_q_sub q1 q2 -> nrel L r r' -> nrel L (popen q1 l1 r) (popen q2 l2 r').
Proof.
  intros L q1 l1 r q2 l2 r' Hq Hn. unfold arg_q_sub in Hq.
  destruct Hq as [-> | [-> _]].
  - destruct (q_eq_dec q1 Lost) as [-> | Hne].
    + destruct r as [[a b]|], r' as [[c d]|]; simpl in *; auto;
        unfold arg_q_sub; auto.
    + rewrite (popen_keep q1 l1 r Hne). rewrite (popen_keep q1 l2 r' Hne). exact Hn.
  - destruct (q_eq_dec q1 Lost) as [-> | Hne].
    + destruct r as [[a b]|], r' as [[c d]|]; simpl in *; auto;
        unfold arg_q_sub; auto.
    + rewrite (popen_keep q1 l1 r Hne).
      destruct r as [[a b]|], r' as [[c d]|]; simpl in *; auto;
        try contradiction.
      split; [unfold arg_q_sub; destruct a; auto 8 | left; reflexivity].
Qed.

Lemma pwalk_mut : forall CT D Bs q0 l C As,
  q0 <> Bot ->
  pwalk CT (TClass Mut D Bs) (LT q0 l C As) = pnode q0 l.
Proof. intros CT D Bs q0 l C As Hb. destruct q0; simpl; congruence. Qed.

Lemma pdir_false : forall qb q0, qb <> Mut \/ q0 = Bot -> pdir qb q0 = false.
Proof.
  intros qb q0 [H | ->]; [destruct qb; simpl; congruence | destruct qb; reflexivity].
Qed.

Lemma pdir_true : forall qb q0, pdir qb q0 = true -> qb = Mut /\ q0 <> Bot.
Proof. intros qb q0 H. destruct qb, q0; simpl in H; try discriminate; split; congruence. Qed.

Lemma pwalk_dir : forall CT qb D Bs q0 l C As,
  pdir qb q0 = true ->
  pwalk CT (TClass qb D Bs) (LT q0 l C As) = pnode q0 l.
Proof. intros CT qb D Bs q0 l C As H. cbn [pwalk]. rewrite H. reflexivity. Qed.

Lemma pnode_some : forall q0 l q1 l1,
  pnode q0 l = Some (q1, l1) -> q0 <> Bot /\ q1 = q0 /\ l1 = l.
Proof.
  intros q0 l q1 l1 H. destruct q0; simpl in H; inversion H; subst;
    repeat split; auto; discriminate.
Qed.

Lemma pnode_nb : forall q0 l, q0 <> Bot -> pnode q0 l = Some (q0, l).
Proof. intros q0 l H. destruct q0; simpl; congruence. Qed.

Lemma pwalk_class : forall CT qb D Bs q0 l C As,
  qb <> Mut \/ q0 = Bot ->
  pwalk CT (TClass qb D Bs) (LT q0 l C As) =
  match tviewg CT (S C) q0 (prd q0) l C As D with
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
  cbn [pwalk]. rewrite (pdir_false qb q0 Hqb).
  destruct (tviewg CT (S C) q0 (prd q0) l C As D); auto.
Qed.

Lemma pwalk_ndir : forall CT qb D Bs q0 l C As,
  pdir qb q0 = false ->
  pwalk CT (TClass qb D Bs) (LT q0 l C As) =
  match tviewg CT (S C) q0 (prd q0) l C As D with
  | Some Vs => pwalks CT Bs Vs
  | None => None
  end.
Proof.
  intros CT qb D Bs q0 l C As H. apply pwalk_class.
  destruct qb; try (left; discriminate).
  destruct q0; simpl in H; try discriminate. right. reflexivity.
Qed.

Lemma pwalk_head : forall CT n D Bs q0 l C As,
  pwalk CT (THead n D Bs) (LT q0 l C As) =
  match tviewg CT (S C) q0 (prd q0) l C As D with
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
  cbn [pwalk]. destruct (tviewg CT (S C) q0 (prd q0) l C As D); auto.
Qed.

Lemma pwalk_class_nb : forall CT qb D Bs q0 l C As,
  qb <> Mut -> q0 <> Bot ->
  pwalk CT (TClass qb D Bs) (LT q0 l C As) =
  match tviewf CT (S C) q0 l C As D with
  | Some Vs => pwalks CT Bs Vs
  | None => None
  end.
Proof.
  intros CT qb D Bs q0 l C As Hqb Hb.
  rewrite (pwalk_class CT qb D Bs q0 l C As (or_introl Hqb)). rewrite (prd_nb q0 Hb). rewrite tviewg_tg.
  reflexivity.
Qed.

Lemma pwalk_head_nb : forall CT n D Bs q0 l C As,
  q0 <> Bot ->
  pwalk CT (THead n D Bs) (LT q0 l C As) =
  match tviewf CT (S C) q0 l C As D with
  | Some Vs => pwalks CT Bs Vs
  | None => None
  end.
Proof.
  intros CT n D Bs q0 l C As Hb.
  rewrite (pwalk_head CT n D Bs q0 l C As). rewrite (prd_nb q0 Hb). rewrite tviewg_tg.
  reflexivity.
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
  - (* the second stops at an open node *)
    destruct q2; simpl in Hn; try contradiction.
    destruct (pwalks CT Bs Vs) as [[q l]|]; simpl;
      [split; [unfold arg_q_sub; destruct q; auto 8 | left; reflexivity] | exact I].
  - apply IH. exact Hrest.
Qed.

Lemma pwalk_agree : forall CT L B A A',
  lagree L A A' -> nrel L (pwalk CT B A) (pwalk CT B A').
Proof.
  intros CT L B. induction B using qualified_type_ind'; intros A A' Hle.
  - inversion Hle as [q1 l1 q2 l2 C0 As As' Hq Hlab Hargs]; subst.
    assert (Hdesc : nrel L
      (match tviewg CT (S C0) q1 (prd q1) l1 C0 As C with
       | Some Vs => pwalks CT args Vs | None => None end)
      (match tviewg CT (S C0) q2 (prd q2) l2 C0 As' C with
       | Some Vs => pwalks CT args Vs | None => None end)).
    { pose proof (tviewg_agree CT L (S C0) q1 (prd q1) l1 q2 (prd q2) l2 C0 As As' C
                    (gok_prd q1) (gok_prd q2) (prd_rrel L q1 l1 q2 l2 Hq Hlab) Hargs)
        as Hv.
      destruct (tviewg CT (S C0) q1 (prd q1) l1 C0 As C) as [Vs|],
               (tviewg CT (S C0) q2 (prd q2) l2 C0 As' C) as [Vs'|];
        simpl in Hv; try contradiction; [|exact I].
      apply pwalks_agree; auto. }
    destruct (q_eq_dec qual Mut) as [-> | Hqb].
    + destruct (q_eq_dec q1 Bot) as [-> | Hb1].
      * unfold arg_q_sub in Hq. destruct Hq as [-> | [-> _]].
        -- rewrite (pwalk_class CT Mut C args Bot l1 C0 As (or_intror eq_refl)).
           rewrite (pwalk_class CT Mut C args Bot l2 C0 As' (or_intror eq_refl)).
           exact Hdesc.
        -- rewrite (pwalk_class CT Mut C args Bot l1 C0 As (or_intror eq_refl)).
           assert (Hnb : Lost <> Bot) by discriminate.
           rewrite (pwalk_mut CT C args Lost l2 C0 As' Hnb).
           cbn [pnode].
           destruct (tviewg CT (S C0) Bot (prd Bot) l1 C0 As C) as [Vs|]; [|exact I].
           destruct (pwalks CT args Vs) as [[qx lx]|]; [|exact I].
           split; [unfold arg_q_sub; destruct qx; auto 8 | left; reflexivity].
      * assert (Hb2 : q2 <> Bot).
        { unfold arg_q_sub in Hq. destruct Hq as [-> | [-> _]]; [exact Hb1 | discriminate]. }
        rewrite (pwalk_mut CT C args q1 l1 C0 As Hb1).
        rewrite (pwalk_mut CT C args q2 l2 C0 As' Hb2).
        apply pnode_nrel; auto.
    + rewrite (pwalk_class CT qual C args q1 l1 C0 As (or_introl Hqb)).
      rewrite (pwalk_class CT qual C args q2 l2 C0 As' (or_introl Hqb)).
      exact Hdesc.
  - inversion Hle as [q1 l1 q2 l2 C0 As As' Hq Hlab Hargs]; subst.
    destruct u as [|[]|]; cbn [pwalk]; try exact I. apply pnode_nrel; auto.
  - inversion Hle as [q1 l1 q2 l2 C0 As As' Hq Hlab Hargs]; subst.
    rewrite (pwalk_head CT n C args q1 l1 C0 As).
    rewrite (pwalk_head CT n C args q2 l2 C0 As').
    pose proof (tviewg_agree CT L (S C0) q1 (prd q1) l1 q2 (prd q2) l2 C0 As As' C
                  (gok_prd q1) (gok_prd q2) (prd_rrel L q1 l1 q2 l2 Hq Hlab) Hargs)
      as Hv.
    destruct (tviewg CT (S C0) q1 (prd q1) l1 C0 As C) as [Vs|],
             (tviewg CT (S C0) q2 (prd q2) l2 C0 As' C) as [Vs'|];
      simpl in Hv; try contradiction; [|exact I].
    apply pwalks_agree; auto.
Qed.

Lemma pfindf_agree : forall CT L B A A',
  lagree L A A' -> nrel L (pfindf CT B A) (pfindf CT B A').
Proof.
  intros CT L B A A' Hle.
  inversion Hle as [q1 l1 q2 l2 C0 As As' Hq Hlab Hargs]; subst.
  cbn [pfindf]. apply popen_nrel; [exact Hq | apply pwalk_agree; exact Hle].
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
  - (* the second stops at an open node *)
    destruct q2; simpl in Hn; try contradiction.
    destruct (pfindsf CT Bs Vs) as [[q l]|]; simpl;
      [split; [unfold arg_q_sub; destruct q; auto 8 | left; reflexivity] | exact I].
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

(** The payloads met along a reader's chain are acceptable to a second
    reader. *)
Definition vpok (CT : class_table) (L : list nat) (k : bool) (hq : q) (g : q -> q)
    (d : lab) (C : class_name) (As : list ltype) (hq' : q) (g' : q -> q) (d' : lab)
    : Prop :=
  forall C' As', view CT k hq g d C As C' As' ->
    pok L hq g hq' g' d' (vpay k CT C' As').

Lemma vpok_step : forall CT L k hq g d C As hq' g' d' P Ss,
  vpok CT L k hq g d C As hq' g' d' ->
  parent_lookup CT C = Some (P, Ss) ->
  vpok CT L k hq g d P (hstep k hq g d (vpay k CT C As) As Ss) hq' g' d'.
Proof.
  intros CT L k hq g d C As hq' g' d' P Ss Hv Hparent C' As' H.
  apply Hv. eapply v_step; eauto.
Qed.

Lemma vpok_type : forall CT L hq g d C As hq' g' d',
  vpok CT L true hq g d C As hq' g' d'.
Proof. intros CT L hq g d C As hq' g' d' C' As' _ w H. discriminate H. Qed.

(** Readers that read a header compatibly, on arguments that agree, see
    views that agree. *)
Lemma view_agree : forall CT k hq g d C As D Vs,
  wf_class_table CT ->
  view CT k hq g d C As D Vs ->
  forall L hq' g' d' As' Vs',
    gok g -> gok g' -> rrel L hq g d hq' g' d' ->
    vpok CT L k hq g d C As hq' g' d' ->
    Forall2 (lagree L) As As' ->
    view CT true hq' g' d' C As' D Vs' -> Forall2 (lagree L) Vs Vs'.
Proof.
  intros CT k hq g d C As D Vs Hwf H.
  induction H; intros L hq' g' d' As' Vs' Hg Hg' Hr Hp Hle H2.
  - inversion H2; subst; auto.
    exfalso. pose proof (view_le _ _ _ _ _ _ _ _ _ Hwf Hrest) as Hle2.
    pose proof (parent_lt _ _ _ _ Hwf Hparent). lia.
  - inversion H2; subst.
    + exfalso. pose proof (view_le _ _ _ _ _ _ _ _ _ Hwf H) as Hle2.
      pose proof (parent_lt _ _ _ _ Hwf Hparent). lia.
    + rewrite Hparent in Hparent0. inversion Hparent0; subst.
      eapply (IHview L hq' g' d'); eauto.
      * eapply vpok_step; eauto.
      * apply hstep_agree; auto.
        -- intros ->. reflexivity.
        -- apply Hp. constructor.
Qed.

(** A view that a labelled type has is had by any reader that reads at
    least as much, on arguments that agree into the type's. *)
Lemma view_transfer : forall CT hq' g' d' C As' D Vs',
  view CT true hq' g' d' C As' D Vs' ->
  forall k hq g d As,
    exists Vs, view CT k hq g d C As D Vs.
Proof.
  intros CT hq' g' d' C As' D Vs' H.
  induction H; intros k hq g d As0.
  - exists As0. constructor.
  - destruct (IHview k hq g d (hstep k hq g d (vpay k CT C As0) As0 Ss))
      as (Vs0 & Hv).
    exists Vs0. eapply v_step; eauto.
Qed.

(** The same with the escape: the payloads met along the first reader's chain
    are acceptable to the second with the escape. *)
Definition vpokd (CT : class_table) (L : list nat) (k : bool) (hq : q) (g : q -> q)
    (d : lab) (C : class_name) (As : list ltype) (hq' : q) (g' : q -> q) (d' : lab)
    : Prop :=
  forall C' As', view CT k hq g d C As C' As' ->
    pokd L hq g hq' g' d' (vpay k CT C' As').

Lemma vpokd_step : forall CT L k hq g d C As hq' g' d' P Ss,
  vpokd CT L k hq g d C As hq' g' d' ->
  parent_lookup CT C = Some (P, Ss) ->
  vpokd CT L k hq g d P (hstep k hq g d (vpay k CT C As) As Ss) hq' g' d'.
Proof.
  intros CT L k hq g d C As hq' g' d' P Ss Hv Hparent C' As' H.
  apply Hv. eapply v_step; eauto.
Qed.

Lemma view_agree_d : forall CT k hq g d C As D Vs,
  wf_class_table CT ->
  view CT k hq g d C As D Vs ->
  forall L hq' g' d' As' Vs',
    gok g -> gok g' -> rrel L hq g d hq' g' d' ->
    vpokd CT L k hq g d C As hq' g' d' ->
    Forall2 (dagree L) As As' ->
    view CT true hq' g' d' C As' D Vs' -> Forall2 (dagree L) Vs Vs'.
Proof.
  intros CT k hq g d C As D Vs Hwf H.
  induction H; intros L hq' g' d' As' Vs' Hg Hg' Hr Hp Hle H2.
  - inversion H2; subst; auto.
    exfalso. pose proof (view_le _ _ _ _ _ _ _ _ _ Hwf Hrest) as Hle2.
    pose proof (parent_lt _ _ _ _ Hwf Hparent). lia.
  - inversion H2; subst.
    + exfalso. pose proof (view_le _ _ _ _ _ _ _ _ _ Hwf H) as Hle2.
      pose proof (parent_lt _ _ _ _ Hwf Hparent). lia.
    + rewrite Hparent in Hparent0. inversion Hparent0; subst.
      eapply (IHview L hq' g' d'); eauto.
      * eapply vpokd_step; eauto.
      * apply hstep_agree_d; auto.
        -- intros ->. reflexivity.
        -- apply Hp. constructor.
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

(** The payloads along an object's chain are nodes of one world. *)
Definition opay (CT : class_table) (L : list nat) (qo : q_r) (c : lab)
    (C : class_name) (As : list ltype) (lm : lab) : Prop :=
  forall D Vs, oview CT qo c C As D Vs ->
    forall w, pclassf CT D Vs = Some (Mut, w) -> norm L w = norm L lm.

Lemma opay_vpok : forall CT L qo c C As qA lA,
  (qA = Mut -> opay CT L qo c C As lA) ->
  vpok CT L false (qr2q qo) (fun q0 => q0) c C As qA (tg qA) lA.
Proof.
  intros CT L qo c C As qA lA Hp D Vs Hv w Hw.
  destruct (q_eq_dec qA Mut) as [-> | Hne].
  - left. exact (Hp eq_refl D Vs Hv w Hw).
  - right. left. destruct qA; simpl; congruence.
Qed.

(** The view of an object and the view of a labelled type it inhabits agree,
    and the object's view exists whenever the type's does.  Under a mutable
    head, the object's payloads are asked to be nodes of the type's world. *)
Theorem obj_vs_type : forall CT L qo c Ao qA lA As C D Vt,
  wf_class_table CT ->
  head_ok qo qA ->
  (qA = Mut -> norm L c = norm L lA) ->
  (qA = Mut -> opay CT L qo c C Ao lA) ->
  Forall2 (lagree L) Ao As ->
  tview CT qA lA C As D Vt ->
  exists Vo, oview CT qo c C Ao D Vo /\ Forall2 (lagree L) Vo Vt.
Proof.
  intros CT L qo c Ao qA lA As C D Vt Hwf Hhead Hl Hp Hle Hv.
  unfold tview in Hv. unfold oview.
  pose proof (obj_type_rrel L qo c qA lA Hhead Hl) as Hr.
  destruct (view_transfer _ _ _ _ _ _ _ _ Hv false (qr2q qo) (fun q0 => q0)
              c Ao) as (Vo & Hvo).
  exists Vo. split; auto.
  exact (view_agree _ _ _ _ _ _ _ _ _ Hwf Hvo L _ _ _ _ _ gok_id (gok_tg _)
           Hr (opay_vpok CT L qo c C Ao qA lA Hp) Hle Hv).
Qed.

(** With the escape: under a mutable head, the object's payloads are asked to
    be nodes of the type's world only when that world is live. *)
Lemma opay_vpokd : forall CT L qo c C As qA lA,
  (qA = Mut -> norm L lA = None \/ opay CT L qo c C As lA) ->
  vpokd CT L false (qr2q qo) (fun q0 => q0) c C As qA (tg qA) lA.
Proof.
  intros CT L qo c C As qA lA Hp D Vs Hv w Hw.
  destruct (q_eq_dec qA Mut) as [-> | Hne].
  - destruct (Hp eq_refl) as [Hd | Ho]; [right; left; exact Hd | left; exact (Ho D Vs Hv w Hw)].
  - right. right. left. destruct qA; simpl; congruence.
Qed.

Theorem obj_vs_type_d : forall CT L qo c Ao qA lA As C D Vt,
  wf_class_table CT ->
  head_ok qo qA ->
  (qA = Mut -> norm L c = norm L lA) ->
  (qA = Mut -> norm L lA = None \/ opay CT L qo c C Ao lA) ->
  Forall2 (dagree L) Ao As ->
  tview CT qA lA C As D Vt ->
  exists Vo, oview CT qo c C Ao D Vo /\ Forall2 (dagree L) Vo Vt.
Proof.
  intros CT L qo c Ao qA lA As C D Vt Hwf Hhead Hl Hp Hle Hv.
  unfold tview in Hv. unfold oview.
  pose proof (obj_type_rrel L qo c qA lA Hhead Hl) as Hr.
  destruct (view_transfer _ _ _ _ _ _ _ _ Hv false (qr2q qo) (fun q0 => q0)
              c Ao) as (Vo & Hvo).
  exists Vo. split; auto.
  exact (view_agree_d _ _ _ _ _ _ _ _ _ Hwf Hvo L _ _ _ _ _ gok_id (gok_tg _)
           Hr (opay_vpokd CT L qo c C Ao qA lA Hp) Hle Hv).
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
    rewrite <- (map_erase_hstep_obj qo c (vpay false CT C As)). exact IHview.
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
                (hstep false (qr2q qo) (fun q0 => q0) c (vpay false CT C As) As Ss)
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

(* ------------------THE PLAIN VIEW------------------*)

(** The object's reading without payload: a header-written mutable position
    reads with the object's colour label.  It is the view a labelled type
    with the object's head and label would compute, the qualifier map being
    the identity. *)
Definition oplain (CT : class_table) (qo : q_r) (c : lab) :=
  view CT true (qr2q qo) (fun q0 => q0) c.

Lemma view_transfer_any : forall CT k' hq' g' d' C As' D Vs',
  view CT k' hq' g' d' C As' D Vs' ->
  forall k hq g d As, exists Vs, view CT k hq g d C As D Vs.
Proof.
  intros CT k' hq' g' d' C As' D Vs' H.
  induction H; intros k hq g d As0.
  - exists As0. constructor.
  - destruct (IHview k hq g d (hstep k hq g d (vpay k CT C As0) As0 Ss))
      as (Vs0 & Hv).
    exists Vs0. eapply v_step; eauto.
Qed.

Lemma oplain_exists : forall CT qo c C As D Vs,
  oview CT qo c C As D Vs -> forall c', exists Vp, oplain CT qo c' C As D Vp.
Proof. intros CT qo c C As D Vs H c'. eapply view_transfer_any; eauto. Qed.

Lemma oplain_deterministic : forall CT qo c C As D Vs1,
  wf_class_table CT -> oplain CT qo c C As D Vs1 ->
  forall Vs2, oplain CT qo c C As D Vs2 -> Vs1 = Vs2.
Proof. intros. eapply view_deterministic; eauto. Qed.

Lemma oplain_trans : forall CT qo c C As D Vs,
  oplain CT qo c C As D Vs ->
  forall E Ws, oplain CT qo c D Vs E Ws -> oplain CT qo c C As E Ws.
Proof. intros. eapply view_trans; eauto. Qed.

(* ------------------LABEL VARIANTS------------------*)

(** Two labelled types of the same shape: the same qualifiers and classes,
    labels free. *)
Inductive lvar : ltype -> ltype -> Prop :=
  | lv_node : forall q0 l l' C As As'
      (Hargs : Forall2 lvar As As'),
      lvar (LT q0 l C As) (LT q0 l' C As').

Lemma lvar_refl : forall A, lvar A A.
Proof.
  intros A. induction A using ltype_ind'. constructor.
  induction H; constructor; auto.
Qed.

Lemma Forall2_lvar_refl : forall As, Forall2 lvar As As.
Proof. intros As. induction As; constructor; auto using lvar_refl. Qed.

Lemma lvar_lrehead : forall q0 l l' A A',
  lvar A A' -> lvar (lrehead q0 l A) (lrehead q0 l' A').
Proof. intros q0 l l' A A' H. inversion H; subst. simpl. constructor. auto. Qed.

Lemma ldyn_lvar : forall F F' T,
  lf_q F = lf_q F' ->
  Forall2 lvar (lf_cargs F) (lf_cargs F') ->
  Forall2 lvar (lf_margs F) (lf_margs F') ->
  map fst (lf_qargs F) = map fst (lf_qargs F') ->
  lvar (ldyn F T) (ldyn F' T).
Proof.
  intros F F' T Hq Hc Hm Hk.
  induction T using qualified_type_ind'.
  - simpl. rewrite Hq. constructor. induction H; simpl; constructor; auto.
  - pose proof (tv_lookup_Forall2 lvar o _ _ _ _ n Hc Hm) as Hl.
    assert (HA : lvar
              match tv_lookup o (lf_cargs F) (lf_margs F) n with
              | Some A => A | None => ldefault end
              match tv_lookup o (lf_cargs F') (lf_margs F') n with
              | Some A => A | None => ldefault end).
    { destruct (tv_lookup o (lf_cargs F) (lf_margs F) n),
               (tv_lookup o (lf_cargs F') (lf_margs F') n);
        try contradiction; auto using lvar_refl. }
    destruct u as [|qual|m]; simpl.
    + exact HA.
    + rewrite Hq. apply lvar_lrehead. exact HA.
    + assert (E : fst (lqnth (lf_qargs F) m) = fst (lqnth (lf_qargs F') m)).
      { unfold lqnth.
        rewrite <- (map_nth fst (lf_qargs F) (RO, LOut) m).
        rewrite <- (map_nth fst (lf_qargs F') (RO, LOut) m).
        rewrite Hk. reflexivity. }
      rewrite E. apply lvar_lrehead. exact HA.
  - simpl.
    assert (E : fst (lqnth (lf_qargs F) n) = fst (lqnth (lf_qargs F') n)).
    { unfold lqnth.
      rewrite <- (map_nth fst (lf_qargs F) (RO, LOut) n).
      rewrite <- (map_nth fst (lf_qargs F') (RO, LOut) n).
      rewrite Hk. reflexivity. }
    rewrite E. constructor. induction H; simpl; constructor; auto.
Qed.

(** The payload reading and the plain reading of one header step are label
    variants of each other. *)
Lemma hstep_lvar : forall hq d d' pn As As' Ss,
  Forall2 lvar As As' ->
  Forall2 lvar (hstep false hq (fun q0 => q0) d pn As Ss)
    (hstep true hq (fun q0 => q0) d' None As' Ss).
Proof.
  intros hq d d' pn As As' Ss Hl. unfold hstep. rewrite rd_map_obj. simpl rd_map.
  induction Ss as [|S Ss IH]; simpl; constructor; auto.
  rewrite !map_qual_id. apply ldyn_lvar; simpl; auto.
Qed.

Lemma view_lvar : forall CT qo c C As D Vs,
  wf_class_table CT ->
  oview CT qo c C As D Vs ->
  forall c' As' Vs', oplain CT qo c' C As' D Vs' ->
    Forall2 lvar As As' -> Forall2 lvar Vs Vs'.
Proof.
  intros CT qo c C As D Vs Hwf H. unfold oview in H.
  induction H; intros c' As' Vs' H2 Hle.
  - inversion H2; subst; auto.
    exfalso. pose proof (view_le _ _ _ _ _ _ _ _ _ Hwf Hrest) as Hle2.
    pose proof (parent_lt _ _ _ _ Hwf Hparent). lia.
  - inversion H2; subst.
    + exfalso. pose proof (view_le _ _ _ _ _ _ _ _ _ Hwf H) as Hle2.
      pose proof (parent_lt _ _ _ _ Hwf Hparent). lia.
    + rewrite Hparent in Hparent0. inversion Hparent0; subst.
      eapply IHview; eauto. apply hstep_lvar. exact Hle.
Qed.

(* ------------------THREE-PLACE AGREEMENT------------------*)

Inductive Forall3 {A B C : Type} (R : A -> B -> C -> Prop)
    : list A -> list B -> list C -> Prop :=
  | Forall3_nil : Forall3 R [] [] []
  | Forall3_cons : forall x y z xs ys zs,
      R x y z -> Forall3 R xs ys zs -> Forall3 R (x :: xs) (y :: ys) (z :: zs).

Lemma Forall3_length13 : forall {A B C} (R : A -> B -> C -> Prop) xs ys zs,
  Forall3 R xs ys zs -> length xs = length zs.
Proof. intros A B C R xs ys zs H. induction H; simpl; auto. Qed.

(** How an object's two readings of a position agree into a type's
    argument, node by node: the type's label agrees with the payload
    reading's, or, under the escape [esc] (the type's head is not a live
    mutable claim), with the plain reading's. *)
Inductive xagree (L : list nat) (esc : Prop) : ltype -> ltype -> ltype -> Prop :=
  | xa_node : forall q1 l1 l1' q2 l2 C As As' Bs
      (Hq : arg_q_sub q1 q2)
      (Hlab : q2 = Lost \/ q1 <> Mut \/ norm L l1 = norm L l2 \/
              (esc /\ norm L l1' = norm L l2))
      (Hargs : Forall3 (xagree L esc) As As' Bs),
      xagree L esc (LT q1 l1 C As) (LT q1 l1' C As') (LT q2 l2 C Bs).

Section xagree_ind'.
  Variable L : list nat.
  Variable esc : Prop.
  Variable P : ltype -> ltype -> ltype -> Prop.
  Hypothesis Hnode : forall q1 l1 l1' q2 l2 C As As' Bs,
    arg_q_sub q1 q2 ->
    (q2 = Lost \/ q1 <> Mut \/ norm L l1 = norm L l2 \/
     (esc /\ norm L l1' = norm L l2)) ->
    Forall3 (xagree L esc) As As' Bs ->
    Forall3 P As As' Bs ->
    P (LT q1 l1 C As) (LT q1 l1' C As') (LT q2 l2 C Bs).

  Fixpoint xagree_ind' A A' B (H : xagree L esc A A' B) : P A A' B :=
    match H with
    | xa_node _ _ q1 l1 l1' q2 l2 C As As' Bs Hq Hlab Hargs =>
        Hnode q1 l1 l1' q2 l2 C As As' Bs Hq Hlab Hargs
          ((fix go As As' Bs (Hl : Forall3 (xagree L esc) As As' Bs)
              : Forall3 P As As' Bs :=
              match Hl with
              | Forall3_nil _ => Forall3_nil P
              | Forall3_cons _ t t' u ts ts' us Ht Hr =>
                  Forall3_cons P t t' u ts ts' us (xagree_ind' t t' u Ht) (go _ _ _ Hr)
              end) As As' Bs Hargs)
    end.
End xagree_ind'.

(** From an exact agreement of the payload reading. *)
Lemma xagree_of_lagree : forall L esc A A' B,
  lvar A A' -> lagree L A B -> xagree L esc A A' B.
Proof.
  intros L esc A A' B Hv H. revert A' Hv.
  induction H using lagree_ind'; intros A' Hv. inversion Hv; subst.
  constructor; auto.
  - destruct H0 as [Hx | [Hx | Hx]]; auto.
  - clear H H0 H1 Hv. revert As' Hargs.
    induction H2 as [|a b As Bs Hab Hrest IH]; intros As' Hargs;
      inversion Hargs; subst; constructor; auto.
Qed.

Lemma Forall3_xagree_of_lagree : forall L esc As As' Bs,
  Forall2 lvar As As' -> Forall2 (lagree L) As Bs -> Forall3 (xagree L esc) As As' Bs.
Proof.
  intros L esc As As' Bs Hv H. revert As' Hv.
  induction H as [|a b As Bs Hab Hrest IH]; intros As' Hv; inversion Hv; subst;
    constructor; auto using xagree_of_lagree.
Qed.

(** The escape may be weakened. *)
Lemma xagree_mono : forall L esc esc' A A' B,
  (esc -> esc') -> xagree L esc A A' B -> xagree L esc' A A' B.
Proof.
  intros L esc esc' A A' B Hi H. induction H using xagree_ind'. constructor; [exact H | |].
  - destruct H0 as [Hx | [Hx | [Hx | [He Hx]]]]; auto 6.
  - clear - H2. induction H2; constructor; auto.
Qed.

Lemma Forall3_xagree_mono : forall L esc esc' As As' Bs,
  (esc -> esc') -> Forall3 (xagree L esc) As As' Bs -> Forall3 (xagree L esc') As As' Bs.
Proof. intros L esc esc' As As' Bs Hi H. induction H; constructor; eauto using xagree_mono. Qed.

(** Through an exact agreement on the type's side. *)
Lemma xagree_trans_r : forall L esc A A' B C,
  xagree L esc A A' B -> lagree L B C -> xagree L esc A A' C.
Proof.
  intros L esc A A' B C H. revert C.
  induction H using xagree_ind'; intros C0 Hbc.
  inversion Hbc as [? ? ? ? ? ? ? Hq' Hlab' Hargs']; subst.
  constructor.
  - eapply arg_q_sub_trans; eauto.
  - destruct Hlab' as [Hx | [Hx | Hx]]; auto.
    + destruct (q_eq_dec q1 Mut) as [-> | Hne]; auto.
      unfold arg_q_sub in H. destruct H as [Hy | [Hy _]]; [congruence|].
      rewrite Hy in Hq'. unfold arg_q_sub in Hq'.
      destruct Hq' as [Hz | [Hz _]]; auto.
    + destruct H0 as [Hy | [Hy | [Hy | [He Hy]]]]; auto.
      * left. rewrite Hy in Hq'. unfold arg_q_sub in Hq'.
        destruct Hq' as [Hz | [Hz _]]; auto.
      * right. right. left. rewrite Hy. exact Hx.
      * right. right. right. split; auto. rewrite Hy. exact Hx.
  - clear - H2 Hargs'. revert Bs0 Hargs'.
    induction H2 as [|a a' b As As' Bs Hab Hrest IH]; intros Cs Hargs';
      inversion Hargs'; subst; constructor; auto.
Qed.

Lemma Forall3_xagree_trans_r : forall L esc As As' Bs Cs,
  Forall3 (xagree L esc) As As' Bs -> Forall2 (lagree L) Bs Cs ->
  Forall3 (xagree L esc) As As' Cs.
Proof.
  intros L esc As As' Bs Cs H. revert Cs.
  induction H as [|a a' b As As' Bs Hab Hrest IH]; intros Cs Hbc;
    inversion Hbc; subst; constructor; eauto using xagree_trans_r.
Qed.

(** Closing a world. *)
Lemma xagree_pop : forall L w0 esc A A' B,
  xagree (w0 :: L) esc A A' B -> xagree L esc A A' B.
Proof.
  intros L w0 esc A A' B H. induction H using xagree_ind'. constructor; [exact H | |].
  - destruct H0 as [Hx | [Hx | [Hx | [He Hx]]]]; auto.
    + right. right. left. eapply norm_pop; eauto.
    + right. right. right. split; auto. eapply norm_pop; eauto.
  - clear - H2. induction H2; constructor; auto.
Qed.

Lemma Forall3_xagree_pop : forall L w0 esc As As' Bs,
  Forall3 (xagree (w0 :: L) esc) As As' Bs -> Forall3 (xagree L esc) As As' Bs.
Proof. intros L w0 esc As As' Bs H. induction H; constructor; eauto using xagree_pop. Qed.

(** An object's own reading of a position, as a type's argument. *)
Lemma Forall3_xagree_refl : forall L esc As As',
  Forall2 lvar As As' -> Forall3 (xagree L esc) As As' As.
Proof.
  intros L esc As As' Hv. apply Forall3_xagree_of_lagree; auto.
  apply Forall2_lagree_refl.
Qed.

(** The plain view of an object and the view of a labelled type it inhabits
    agree, the type's head label being the object's colour when mutable. *)
Theorem plain_vs_type : forall CT L qo c Ao qA lA As C D Vt,
  wf_class_table CT ->
  head_ok qo qA ->
  (qA = Mut -> norm L c = norm L lA) ->
  Forall2 (lagree L) Ao As ->
  tview CT qA lA C As D Vt ->
  exists Vp, oplain CT qo c C Ao D Vp /\ Forall2 (lagree L) Vp Vt.
Proof.
  intros CT L qo c Ao qA lA As C D Vt Hwf Hhead Hl Hle Hv.
  unfold tview in Hv. unfold oplain.
  pose proof (obj_type_rrel L qo c qA lA Hhead Hl) as Hr.
  destruct (view_transfer _ _ _ _ _ _ _ _ Hv true (qr2q qo) (fun q0 => q0)
              c Ao) as (Vp & Hvp).
  exists Vp. split; auto.
  exact (view_agree _ _ _ _ _ _ _ _ _ Hwf Hvp L _ _ _ _ _ gok_id (gok_tg _)
           Hr (vpok_type CT L _ _ _ _ _ _ _ _) Hle Hv).
Qed.

Print Assumptions plain_vs_type.

(* ------------------THREE-PLACE STEP AGREEMENT------------------*)

Lemma Forall3_nth_error : forall {A B C : Type} (R : A -> B -> C -> Prop) xs ys zs,
  Forall3 R xs ys zs ->
  forall n,
    match nth_error xs n, nth_error ys n, nth_error zs n with
    | Some x, Some y, Some z => R x y z
    | None, None, None => True
    | _, _, _ => False
    end.
Proof.
  intros A B C R xs ys zs H.
  induction H as [|x y z xs ys zs Hr Hrest IH]; intros [|n]; simpl;
    [exact I | exact I | exact Hr | apply IH].
Qed.

Lemma tv_lookup_Forall3 : forall {A B C : Type} (R : A -> B -> C -> Prop)
    o cs cs' cs'' ms ms' ms'' n,
  Forall3 R cs cs' cs'' -> Forall3 R ms ms' ms'' ->
  match tv_lookup o cs ms n, tv_lookup o cs' ms' n, tv_lookup o cs'' ms'' n with
  | Some x, Some y, Some z => R x y z
  | None, None, None => True
  | _, _, _ => False
  end.
Proof. intros. destruct o; simpl; apply Forall3_nth_error; auto. Qed.

Lemma xagree_refl : forall L esc A, xagree L esc A A A.
Proof. intros. apply xagree_of_lagree; auto using lvar_refl, lagree_refl. Qed.

(** The readers of one header step, three at a time: the object's payload
    reading, its plain reading (the same head, no payload) and a third
    reader's. *)
Definition lc3 (L : list nat) (esc : Prop) (g f : q -> q) (Fo Fp Fc : lframe) : Prop :=
  lf_q Fo = lf_q Fp /\
  forall q0,
    arg_q_sub (dynq (lf_q Fo) (g q0)) (dynq (lf_q Fc) (f q0)) /\
    (dynq (lf_q Fc) (f q0) = Lost \/ dynq (lf_q Fo) (g q0) <> Mut \/
     norm L (lab_of Fo (g q0)) = norm L (lab_of Fc (f q0)) \/
     (esc /\ norm L (lab_of Fp (g q0)) = norm L (lab_of Fc (f q0)))).

Lemma lc2_lc3 : forall L esc g f Fo Fp Fc,
  lc2 L g f Fo Fc -> lf_q Fo = lf_q Fp -> lc3 L esc g f Fo Fp Fc.
Proof.
  intros L esc g f Fo Fp Fc H Hq. split; [exact Hq|]. intros q0.
  destruct (H q0) as [H1 H2]. split; [exact H1|].
  destruct H2 as [H2 | [H2 | H2]]; auto.
Qed.

Lemma ldyn_xagree3 : forall L esc g f Fo Fp Fc T,
  lc3 L esc g f Fo Fp Fc ->
  Forall3 (xagree L esc) (lf_cargs Fo) (lf_cargs Fp) (lf_cargs Fc) ->
  Forall3 (xagree L esc) (lf_margs Fo) (lf_margs Fp) (lf_margs Fc) ->
  lf_qargs Fo = lf_qargs Fp -> lf_qargs Fp = lf_qargs Fc ->
  xagree L esc (ldyn Fo (map_qual g T)) (ldyn Fp (map_qual g T)) (ldyn Fc (map_qual f T)).
Proof.
  intros L esc g f Fo Fp Fc T [Hqq Hq] Hc Hm Hk1 Hk2.
  induction T using qualified_type_ind'.
  - simpl. destruct (Hq qual) as [H1 H2]. rewrite <- Hqq.
    constructor; auto.
    induction H; simpl; constructor; auto.
  - pose proof (tv_lookup_Forall3 (xagree L esc) o _ _ _ _ _ _ n Hc Hm) as Hl.
    assert (HA : xagree L esc
              match tv_lookup o (lf_cargs Fo) (lf_margs Fo) n with
              | Some A => A | None => ldefault end
              match tv_lookup o (lf_cargs Fp) (lf_margs Fp) n with
              | Some A => A | None => ldefault end
              match tv_lookup o (lf_cargs Fc) (lf_margs Fc) n with
              | Some A => A | None => ldefault end).
    { destruct (tv_lookup o (lf_cargs Fo) (lf_margs Fo) n),
               (tv_lookup o (lf_cargs Fp) (lf_margs Fp) n),
               (tv_lookup o (lf_cargs Fc) (lf_margs Fc) n);
        try contradiction; auto using xagree_refl. }
    destruct u as [|qual|m]; simpl; auto.
    + destruct (Hq qual) as [H1 H2].
      inversion HA; subst. simpl. rewrite <- Hqq. constructor; auto.
    + rewrite Hk1. rewrite Hk2. inversion HA; subst. simpl.
      constructor; auto; left; reflexivity.
  - simpl. rewrite Hk1. rewrite Hk2. constructor; [left; reflexivity | auto |].
    induction H; simpl; constructor; auto.
Qed.

(** One header step, the third reader a labelled type.  Where the header
    writes a mutable position and the type's head is mutable, the type's
    label is the payload's (the payload condition) or, under the escape, the
    object's own. *)
Lemma step_cond3 : forall L esc hq d pn As Ap qA lA At,
  rrel L hq (fun q0 => q0) d qA (tg qA) lA ->
  (qA = Mut -> norm L d = norm L lA) ->
  (forall w, pn = Some (Mut, w) -> qA = Mut -> esc \/ norm L w = norm L lA) ->
  lc3 L esc (fun q0 => q0) (tg qA) (hframe hq d pn As) (hframe hq d None Ap)
    (hframe qA lA None At).
Proof.
  intros L esc hq d pn As Ap qA lA At Hr Hl Hp. split; [reflexivity|].
  intros q0. destruct (q_eq_dec q0 Mut) as [-> | Hne].
  - destruct (Hr Mut) as [H1 H2]. cbn [hframe lf_q]. split; [exact H1|].
    destruct (q_eq_dec (dynq qA (tg qA Mut)) Lost) as [HL | HL]; [left; exact HL|].
    destruct (q_eq_dec (dynq hq Mut) Mut) as [HM | HM]; [|right; left; exact HM].
    assert (HqA : qA = Mut).
    { destruct qA; simpl in HL; try congruence. }
    subst qA. simpl in HL |- *. cbn [lab_of lf_mut hframe].
    destruct pn as [[q1 l1]|].
    + destruct (q_eq_dec q1 Mut) as [-> | Hq1].
      * simpl rd_lab. destruct (Hp l1 eq_refl eq_refl) as [He | Hw].
        -- right. right. right. split; auto.
        -- right. right. left. exact Hw.
      * rewrite (rd_lab_other d q1 l1 Hq1). right. right. left. apply Hl. reflexivity.
    + simpl rd_lab. right. right. left. apply Hl. reflexivity.
  - pose proof (step_cond_other L false hq (fun q0 => q0) d qA (tg qA) lA pn As At
                  gok_id (gok_tg _) Hr q0 Hne) as [H1 H2].
    rewrite rd_map_obj in H1, H2. cbn [rd_map] in H1, H2.
    cbn [hframe lf_q] in H1, H2 |- *. split; [exact H1|].
    destruct H2 as [H2 | [H2 | H2]]; auto.
Qed.

Lemma hstep_xagree3 : forall L esc hq d pn As Ap qA lA At Ss,
  rrel L hq (fun q0 => q0) d qA (tg qA) lA ->
  (qA = Mut -> norm L d = norm L lA) ->
  (forall w, pn = Some (Mut, w) -> qA = Mut -> esc \/ norm L w = norm L lA) ->
  Forall3 (xagree L esc) As Ap At ->
  Forall3 (xagree L esc) (hstep false hq (fun q0 => q0) d pn As Ss)
    (hstep true hq (fun q0 => q0) d None Ap Ss)
    (hstep true qA (tg qA) lA None At Ss).
Proof.
  intros L esc hq d pn As Ap qA lA At Ss Hr Hl Hp Hle.
  unfold hstep. rewrite rd_map_obj. cbn [rd_map].
  induction Ss as [|S Ss IH]; simpl; constructor; auto.
  apply ldyn_xagree3; simpl; auto using step_cond3; constructor.
Qed.

Lemma opay_step : forall CT L qo c C As lm P Ss,
  opay CT L qo c C As lm ->
  parent_lookup CT C = Some (P, Ss) ->
  opay CT L qo c P (hstep false (qr2q qo) (fun q0 => q0) c (pclassf CT C As) As Ss) lm.
Proof.
  intros CT L qo c C As lm P Ss H Hparent D Vs Hv. apply H.
  unfold oview in *. eapply v_step; eauto.
Qed.

(** The object's two views and the view of a labelled type it inhabits,
    along the type's chain. *)
Theorem view_xagree3 : forall CT qA lA C As D Vt,
  wf_class_table CT ->
  tview CT qA lA C As D Vt ->
  forall L esc qo c Ao Ap,
    head_ok qo qA ->
    (qA = Mut -> norm L c = norm L lA) ->
    (qA = Mut -> esc \/ opay CT L qo c C Ao lA) ->
    Forall3 (xagree L esc) Ao Ap As ->
    exists Vr Vp,
      oview CT qo c C Ao D Vr /\ oplain CT qo c C Ap D Vp /\
      Forall3 (xagree L esc) Vr Vp Vt.
Proof.
  intros CT qA lA C As D Vt Hwf Hv. unfold tview in Hv.
  induction Hv; intros L esc qo c Ao Ap Hhead Hl Hp Hle.
  - exists Ao, Ap. split; [constructor|]. split; [constructor|]. exact Hle.
  - destruct (IHHv L esc qo c
                (hstep false (qr2q qo) (fun q0 => q0) c (pclassf CT C Ao) Ao Ss)
                (hstep true (qr2q qo) (fun q0 => q0) c None Ap Ss) Hhead Hl)
      as (Vr & Vp & Hvr & Hvp & Hle').
    { intros Hm. destruct (Hp Hm) as [He | Ho]; [left; exact He | right].
      eapply opay_step; eauto. }
    { apply hstep_xagree3; auto.
      - apply obj_type_rrel; auto.
      - intros w Hw Hm. destruct (Hp Hm) as [He | Ho]; [left; exact He | right].
        exact (Ho C Ao (v_refl _ _ _ _ _ _ _) w Hw). }
    exists Vr, Vp. split; [eapply v_step; eauto|]. split; [eapply v_step; eauto|].
    exact Hle'.
Qed.

Print Assumptions view_xagree3.
