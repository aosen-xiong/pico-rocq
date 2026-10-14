From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ReadonlyFlat ReadonlyWorlds.

(** World labels inside type arguments.

    For protected code that writes a mutable or receiver-dependent qualifier
    inside a type argument, the mutability of a value can come from a type
    argument, so each mutable position of each runtime type argument needs a
    world.  This file defines labelled runtime types, the labelled counterpart
    of dynamization, agreement between labelled types, and the laws relating
    them to substitution and adaptation. *)

(** The world of the values at a mutable position: exactly this world, or
    outside every live world. *)
Inductive lab : Type :=
  | LIn (w : nat)
  | LOut.

(** A runtime type with a label at every node.  Only the labels at mutable
    nodes carry information. *)
Inductive ltype : Type :=
  | LT : q -> lab -> class_name -> list ltype -> ltype.

Section ltype_ind'.
  Variable P : ltype -> Prop.
  Hypothesis Hnode : forall q0 l C args, Forall P args -> P (LT q0 l C args).

  Fixpoint ltype_ind' (A : ltype) : P A :=
    match A with
    | LT q0 l C args =>
        Hnode q0 l C args
          ((fix go (ls : list ltype) : Forall P ls :=
              match ls with
              | [] => Forall_nil P
              | t :: r => Forall_cons t (ltype_ind' t) (go r)
              end) args)
    end.
End ltype_ind'.

Fixpoint erase (A : ltype) : rtype :=
  match A with
  | LT q0 _ C args => RClass q0 C (map erase args)
  end.

(** The labelled view of an activation, or of an object reading its own
    declarations: the mutability through which [RDM] is read, the label of a
    position written mutable, the label of a position written
    receiver-dependent, the labelled class and method type arguments, and the
    labelled qualifier arguments. *)
Record lframe := mk_lframe {
  lf_q : q;
  lf_mut : lab;
  lf_rdm : lab;
  lf_cargs : list ltype;
  lf_margs : list ltype;
  lf_qargs : list (q * lab); (* qualifier arguments, each with its label *)
}.

Definition lab_of (F : lframe) (q0 : q) : lab :=
  match q0 with
  | Mut => lf_mut F
  | RDM => lf_rdm F
  | _ => LOut
  end.

Definition ldefault : ltype := LT RO LOut 0 [].

Definition lrehead (q0 : q) (l : lab) (A : ltype) : ltype :=
  match A with
  | LT _ _ C args => LT q0 l C args
  end.

(** A labelled qualifier argument; a missing one reads as readonly. *)
Definition lqnth (qs : list (q * lab)) (n : nat) : q * lab := nth n qs (RO, LOut).

(** Labelled dynamization. *)
Fixpoint ldyn (F : lframe) (T : qualified_type) : ltype :=
  match T with
  | TClass q0 C args =>
      LT (dynq (lf_q F) q0) (lab_of F q0) C (map (ldyn F) args)
  | TVar u o n =>
      let A := match tv_lookup o (lf_cargs F) (lf_margs F) n with
               | Some A => A
               | None => ldefault
               end in
      match u with
      | TVSub => A
      | TVQual q0 => lrehead (dynq (lf_q F) q0) (lab_of F q0) A
      | TVPoly m =>
          lrehead (fst (lqnth (lf_qargs F) m)) (snd (lqnth (lf_qargs F) m)) A
      end
  | THead n C args =>
      LT (fst (lqnth (lf_qargs F) n)) (snd (lqnth (lf_qargs F) n)) C
        (map (ldyn F) args)
  end.

(** The labelled value of a qualifier argument, in the caller's view. *)
Definition lqarg (F : lframe) (a : qarg) : q * lab :=
  match a with
  | QLit q0 => (dynq (lf_q F) q0, lab_of F q0)
  | QVar m => lqnth (lf_qargs F) m
  end.

Lemma qnth_map_fst : forall qs n, qnth (map fst qs) n = fst (lqnth qs n).
Proof.
  intros qs n. unfold qnth, lqnth.
  change RO with (fst (RO, LOut)). apply map_nth.
Qed.

Lemma lqnth_map : forall (f : qarg -> q * lab) Qs n,
  lqnth (map f Qs) n =
  match nth_error Qs n with Some a => f a | None => (RO, LOut) end.
Proof.
  intros f Qs. unfold lqnth.
  induction Qs as [|a Qs IH]; intros [|n]; simpl; auto.
Qed.

Lemma erase_lrehead : forall q0 l A,
  erase (lrehead q0 l A) = rrequalify q0 (erase A).
Proof. intros q0 l [q1 l1 C args]. reflexivity. Qed.


(** Forgetting the labels of a labelled dynamization gives the ordinary
    one. *)
Lemma erase_ldyn : forall F T,
  erase (ldyn F T) =
  dyn (lf_q F) (map erase (lf_cargs F)) (map erase (lf_margs F))
    (map fst (lf_qargs F)) T.
Proof.
  intros F T. induction T using qualified_type_ind'.
  - simpl. f_equal. rewrite map_map.
    induction H; simpl; auto. f_equal; auto.
  - simpl. rewrite tv_lookup_map.
    destruct (tv_lookup o (lf_cargs F) (lf_margs F) n) as [A|]; simpl;
      destruct u; auto using erase_lrehead;
      rewrite ?erase_lrehead; rewrite qnth_map_fst; reflexivity.
  - assert (Hargs : map erase (map (ldyn F) args) =
              map (dyn (lf_q F) (map erase (lf_cargs F)) (map erase (lf_margs F))
    (map fst (lf_qargs F))) args).
    { rewrite map_map. induction H; simpl; auto. f_equal; auto. }
    simpl. rewrite Hargs. rewrite qnth_map_fst. reflexivity.
Qed.

Lemma map_erase_ldyn : forall F Ts,
  map erase (map (ldyn F) Ts) =
  map (dyn (lf_q F) (map erase (lf_cargs F)) (map erase (lf_margs F))
    (map fst (lf_qargs F))) Ts.
Proof.
  intros. rewrite map_map. apply map_ext. intros. apply erase_ldyn.
Qed.

Definition lf_with_args (F : lframe) (cs ms : list ltype)
    (qs : list (q * lab)) : lframe :=
  mk_lframe (lf_q F) (lf_mut F) (lf_rdm F) cs ms qs.

(** Labelled dynamization of a type whose outer qualifier was replaced. *)
Lemma ldyn_requalify : forall F q0 U,
  ldyn F (requalify q0 U) =
  lrehead (dynq (lf_q F) q0) (lab_of F q0) (ldyn F U).
Proof.
  intros F q0 U.
  destruct U as [q1 C1 args1|u1 o1 n1|n1 C1 args1]; simpl; auto.
  destruct (tv_lookup o1 (lf_cargs F) (lf_margs F) n1) as [A1|];
    destruct u1; simpl; auto; try (destruct A1; reflexivity).
Qed.

Lemma ldyn_prequalify : forall F m U,
  ldyn F (prequalify m U) =
  lrehead (fst (lqnth (lf_qargs F) m)) (snd (lqnth (lf_qargs F) m)) (ldyn F U).
Proof.
  intros F m U.
  destruct U as [q1 C1 args1|u1 o1 n1|n1 C1 args1]; simpl; auto.
  destruct (tv_lookup o1 (lf_cargs F) (lf_margs F) n1) as [A1|];
    destruct u1; simpl; auto; try (destruct A1; reflexivity).
Qed.

Lemma ldyn_qrequalify : forall F a U,
  ldyn F (qrequalify a U) =
  lrehead (fst (match a with Some x => lqarg F x | None => (RO, LOut) end))
          (snd (match a with Some x => lqarg F x | None => (RO, LOut) end))
          (ldyn F U).
Proof.
  intros F a U. destruct a as [[q0|m]|]; simpl.
  - apply ldyn_requalify.
  - apply ldyn_prequalify.
  - apply (ldyn_requalify F RO U).
Qed.

(** Labelled dynamization of a substituted type is labelled dynamization
    with labelled arguments. *)
Lemma ldyn_subst : forall F Ts Us Qs T,
  ldyn F (subst Ts Us Qs T) =
  ldyn (lf_with_args F (map (ldyn F) Ts) (map (ldyn F) Us)
         (map (lqarg F) Qs)) T.
Proof.
  intros F Ts Us Qs T. induction T using qualified_type_ind'.
  - simpl. f_equal. rewrite map_map.
    induction H; simpl; auto. f_equal; auto.
  - simpl. rewrite tv_lookup_map.
    destruct (tv_lookup o Ts Us n) as [U|]; simpl.
    + destruct u as [|q0|m]; auto.
      * exact (ldyn_requalify F q0 U).
      * cbn [lf_with_args lf_qargs]. rewrite lqnth_map.
        exact (ldyn_qrequalify F _ U).
    + destruct u as [|q0|m]; try reflexivity.
      cbn [lf_with_args lf_qargs]. rewrite lqnth_map.
      destruct (nth_error Qs m) as [[q0|m']|]; reflexivity.
  - assert (Hargs : map (ldyn F) (map (subst Ts Us Qs) args) =
              map (ldyn (lf_with_args F (map (ldyn F) Ts) (map (ldyn F) Us)
         (map (lqarg F) Qs))) args).
    { rewrite map_map. induction H; simpl; auto. f_equal; auto. }
    cbn [subst ldyn lf_with_args lf_qargs]. rewrite lqnth_map.
    destruct (nth_error Qs n) as [[q0|m]|]; cbn [qhead ldyn lqarg fst snd];
      rewrite Hargs; reflexivity.
Qed.

(** Normal form of a label relative to the live worlds: a world that is no
    longer live counts as outside. *)
Definition norm (L : list nat) (l : lab) : option nat :=
  match l with
  | LIn w => if in_dec Nat.eq_dec w L then Some w else None
  | LOut => None
  end.

Lemma norm_live : forall L w, List.In w L -> norm L (LIn w) = Some w.
Proof.
  intros L w H. unfold norm.
  destruct (in_dec Nat.eq_dec w L); [reflexivity | contradiction].
Qed.

Lemma norm_dead : forall L w, ~ List.In w L -> norm L (LIn w) = None.
Proof.
  intros L w H. unfold norm.
  destruct (in_dec Nat.eq_dec w L); [contradiction | reflexivity].
Qed.

Lemma norm_some_in : forall L l w, norm L l = Some w -> List.In w L.
Proof.
  intros L [w0|] w H; unfold norm in H; [|discriminate].
  destruct (in_dec Nat.eq_dec w0 L); inversion H; subst; auto.
Qed.

Lemma norm_pop : forall L w0 l1 l2,
  norm (w0 :: L) l1 = norm (w0 :: L) l2 -> norm L l1 = norm L l2.
Proof.
  intros L w0 l1 l2 H.
  assert (Hcase : forall l, norm L l = norm (w0 :: L) l \/
                            (norm L l = None /\ norm (w0 :: L) l = Some w0 /\
                             ~ List.In w0 L)).
  { intros [w|]; [|left; reflexivity]. unfold norm.
    destruct (in_dec Nat.eq_dec w L) as [i|n];
      destruct (in_dec Nat.eq_dec w (w0 :: L)) as [i'|n']; auto.
    - exfalso. apply n'. right. exact i.
    - destruct i' as [-> | i']; [auto | contradiction]. }
  destruct (Hcase l1) as [H1 | (H1 & H1' & Hn1)];
    destruct (Hcase l2) as [H2 | (H2 & H2' & Hn2)]; try congruence.
  - exfalso. apply Hn2. apply (norm_some_in L l1). congruence.
  - exfalso. apply Hn1. apply (norm_some_in L l2). congruence.
Qed.

(** Agreement of labelled types: the same shape up to positions written
    [Lost] on the right, and the same normalized label at every mutable
    position the right side does not leave open. *)
Inductive lagree (L : list nat) : ltype -> ltype -> Prop :=
  | la_node : forall q1 l1 q2 l2 C As Bs
      (Hq : arg_q_sub q1 q2)
      (Hlab : q2 = Lost \/ q1 <> Mut \/ norm L l1 = norm L l2)
      (Hargs : Forall2 (lagree L) As Bs),
      lagree L (LT q1 l1 C As) (LT q2 l2 C Bs).

Section lagree_ind'.
  Variable L : list nat.
  Variable P : ltype -> ltype -> Prop.
  Hypothesis Hnode : forall q1 l1 q2 l2 C As Bs,
    arg_q_sub q1 q2 ->
    (q2 = Lost \/ q1 <> Mut \/ norm L l1 = norm L l2) ->
    Forall2 (lagree L) As Bs ->
    Forall2 P As Bs ->
    P (LT q1 l1 C As) (LT q2 l2 C Bs).

  Fixpoint lagree_ind' A B (H : lagree L A B) : P A B :=
    match H with
    | la_node _ q1 l1 q2 l2 C As Bs Hq Hlab Hargs =>
        Hnode q1 l1 q2 l2 C As Bs Hq Hlab Hargs
          ((fix go As Bs (Hl : Forall2 (lagree L) As Bs) : Forall2 P As Bs :=
              match Hl with
              | Forall2_nil _ => Forall2_nil P
              | Forall2_cons t u Ht Hr =>
                  Forall2_cons t u (lagree_ind' t u Ht) (go _ _ Hr)
              end) As Bs Hargs)
    end.
End lagree_ind'.

Lemma lagree_refl : forall L A, lagree L A A.
Proof.
  intros L A. induction A using ltype_ind'.
  constructor; [left; reflexivity | auto |].
  induction H; constructor; auto.
Qed.

Lemma Forall2_lagree_refl : forall L As, Forall2 (lagree L) As As.
Proof. induction As; constructor; auto using lagree_refl. Qed.

Lemma lagree_trans : forall L A B,
  lagree L A B -> forall C, lagree L B C -> lagree L A C.
Proof.
  intros L A B H. induction H using lagree_ind'. intros C0 H23.
  inversion H23; subst.
  constructor.
  - eauto using arg_q_sub_trans.
  - destruct (q_eq_dec q1 Mut) as [-> | Hne]; auto.
    destruct (q_eq_dec q3 Lost) as [-> | Hnl]; auto.
    right. right.
    assert (q2 = Mut).
    { unfold arg_q_sub in *.
      destruct H as [-> | [-> _]]; auto.
      destruct Hq as [-> | [-> _]]; congruence. }
    subst q2.
    destruct H0 as [Hx | [Hx | Hx]]; try congruence.
    destruct Hlab as [Hy | [Hy | Hy]]; congruence.
  - clear H H0 Hq Hlab H23. generalize dependent Bs0.
    induction H2; intros Bs0 Hargs; inversion Hargs; subst; constructor; eauto.
    apply IHForall2; auto. inversion H1; auto.
Qed.

Lemma Forall2_lagree_trans : forall L As Bs Cs,
  Forall2 (lagree L) As Bs -> Forall2 (lagree L) Bs Cs ->
  Forall2 (lagree L) As Cs.
Proof.
  intros L As Bs Cs H. revert Cs.
  induction H; intros Cs H2; inversion H2; subst; constructor;
    eauto using lagree_trans.
Qed.

(** Agreement forgets to ordinary agreement of the erased types. *)
Lemma lagree_erase : forall L A B, lagree L A B -> rarg_sub (erase A) (erase B).
Proof.
  intros L A B H. induction H using lagree_ind'.
  simpl. constructor; auto.
  clear H H0 H1. induction H2; simpl; constructor; auto.
Qed.

Lemma Forall2_lagree_erase : forall L As Bs,
  Forall2 (lagree L) As Bs -> Forall2 rarg_sub (map erase As) (map erase Bs).
Proof.
  intros L As Bs H. induction H; simpl; constructor; eauto using lagree_erase.
Qed.

(** When the right side leaves no position open, agreement is symmetric. *)
Lemma lagree_sym : forall L A B,
  lagree L A B -> rlost_free (erase B) -> lagree L B A.
Proof.
  intros L A B H. induction H using lagree_ind'. intros Hlf.
  change (erase (LT q2 l2 C Bs)) with (RClass q2 C (map erase Bs)) in Hlf.
  apply rlost_free_class in Hlf. destruct Hlf as [Hq2 Hargs].
  assert (q2 = q1).
  { unfold arg_q_sub in H. destruct H as [-> | [-> _]]; congruence. }
  subst q2. constructor.
  - left. reflexivity.
  - destruct H0 as [Hx | [Hx | Hx]]; try congruence; auto.
  - clear H H0 Hq2 H1.
    induction H2 as [|a b As' Bs' Hab Hrest IH]; constructor;
      simpl in Hargs; inversion Hargs; subst.
    + apply Hab; auto.
    + apply IH; auto.
Qed.

Lemma Forall2_lagree_sym : forall L As Bs,
  Forall2 (lagree L) As Bs -> Forall rlost_free (map erase Bs) ->
  Forall2 (lagree L) Bs As.
Proof.
  intros L As Bs H. induction H; intros Hlf; constructor;
    simpl in Hlf; inversion Hlf; subst; auto using lagree_sym.
Qed.

(** Fewer live worlds keep agreement. *)
Lemma lagree_pop : forall L w0 A B,
  lagree (w0 :: L) A B -> lagree L A B.
Proof.
  intros L w0 A B H. induction H using lagree_ind'.
  constructor; auto.
  destruct H0 as [H0 | [H0 | H0]]; auto.
  right. right. eapply norm_pop; eauto.
Qed.

Lemma Forall2_lagree_pop : forall L w0 As Bs,
  Forall2 (lagree (w0 :: L)) As Bs -> Forall2 (lagree L) As Bs.
Proof.
  intros L w0 As Bs H. induction H; constructor; eauto using lagree_pop.
Qed.

(* ------------------SUBTYPING OF ARGUMENTS AND ADAPTATION------------------*)

Lemma lagree_default : forall L, lagree L ldefault ldefault.
Proof. intros. apply lagree_refl. Qed.

(** Static argument compatibility is kept by labelled dynamization. *)
Lemma ldyn_targ_sub : forall L F T U,
  targ_sub T U -> lagree L (ldyn F T) (ldyn F U).
Proof.
  intros L F T U H. induction H using targ_sub_ind'.
  - apply lagree_refl.
  - simpl. constructor.
    + destruct H as [-> | [-> [-> | [-> | ->]]]]; [left; reflexivity| | |];
        right; simpl; auto.
    + destruct H as [-> | [-> _]]; auto.
    + clear H H0. induction H1; simpl; constructor; auto.
  - simpl. constructor; [left; reflexivity | auto |].
    clear H. induction H0; simpl; constructor; auto.
Qed.

Lemma map_ldyn_targ_sub : forall L F Ts Us,
  Forall2 targ_sub Ts Us ->
  Forall2 (lagree L) (map (ldyn F) Ts) (map (ldyn F) Us).
Proof.
  intros. induction H; simpl; constructor; auto using ldyn_targ_sub.
Qed.

(** Reading a declared type in one labelled view agrees with reading its
    qualifier-mapped version in another, provided the two views relate every
    written qualifier compatibly and their type arguments agree. *)
Definition label_cond (L : list nat) (f : q -> q) (Fo Fc : lframe) : Prop :=
  forall q0,
    arg_q_sub (dynq (lf_q Fo) q0) (dynq (lf_q Fc) (f q0)) /\
    (dynq (lf_q Fc) (f q0) = Lost \/ dynq (lf_q Fo) q0 <> Mut \/
     norm L (lab_of Fo q0) = norm L (lab_of Fc (f q0))).

Lemma ldyn_map_qual_agree : forall L f Fo Fc T,
  label_cond L f Fo Fc ->
  Forall2 (lagree L) (lf_cargs Fo) (lf_cargs Fc) ->
  Forall2 (lagree L) (lf_margs Fo) (lf_margs Fc) ->
  lf_qargs Fo = lf_qargs Fc ->
  lagree L (ldyn Fo T) (ldyn Fc (map_qual f T)).
Proof.
  intros L f Fo Fc T Hq Hc Hm Hqs.
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

Lemma map_ldyn_map_qual_agree : forall L f Fo Fc Ts,
  label_cond L f Fo Fc ->
  Forall2 (lagree L) (lf_cargs Fo) (lf_cargs Fc) ->
  Forall2 (lagree L) (lf_margs Fo) (lf_margs Fc) ->
  lf_qargs Fo = lf_qargs Fc ->
  Forall2 (lagree L) (map (ldyn Fo) Ts) (map (ldyn Fc) (map (map_qual f) Ts)).
Proof.
  intros. induction Ts; simpl; constructor; auto using ldyn_map_qual_agree.
Qed.

(** The labelled view an object has of its own declarations.  A position
    written mutable belongs to the world the object was born in, and is
    outside the live worlds for an object that predates the protected call.
    A position written receiver-dependent belongs to the object's world when
    the object is in one, and is outside the live worlds otherwise. *)
Definition obj_frame (qo : q_r) (birth c : option nat) (args : list ltype)
    : lframe :=
  mk_lframe (qr2q qo)
    (match birth with Some w => LIn w | None => LOut end)
    (match c with Some w => LIn w | None => LOut end)
    args [] [].

(** The labelled view of an activation working in world [wf]. *)
Definition act_frame (qthis : q_r) (wf : nat) (mode : bool)
    (cs ms : list ltype) (ks : list (q * lab)) : lframe :=
  mk_lframe (qr2q qthis) (LIn wf) (if mode then LIn wf else LOut) cs ms ks.

(** The label side condition for reading a member in readonly-state or
    transitive-state code through a receiver with static qualifier [qx]. *)
Lemma rs_label_cond : forall L mt qo b c oargs qthis wf mode cs ms ks qx,
  readonly_state_method_scope mt ->
  head_ok qo (dynq (qr2q qthis) qx) ->
  qx <> Bot ->
  List.In wf L ->
  (qx = Mut -> c = Some wf /\ b = Some wf) ->
  (qx = RDM -> qo = Mut_r ->
     if mode then c = Some wf else forall w, c = Some w -> ~ List.In w L) ->
  label_cond L (vpa_q mt qx) (obj_frame qo b c oargs)
    (act_frame qthis wf mode cs ms ks).
Proof.
  intros L mt qo b c oargs qthis wf mode cs ms ks qx Hrs Hhead Hnb HwfL Hmut Hrdm q0.
  split.
  - unfold obj_frame, act_frame. simpl lf_q.
    apply dynq_vpa_q_agree; [apply qr2q_concrete | apply qr2q_concrete | exact Hhead].
  - unfold obj_frame, act_frame. simpl lf_q.
    pose proof (norm_live _ _ HwfL) as Hnl.
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
