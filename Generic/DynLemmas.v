From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping.

(** Facts relating substitution, adaptation, and dynamization. *)

Lemma tv_lookup_map : forall {A B : Type} (f : A -> B) o cs ms n,
  tv_lookup o (map f cs) (map f ms) n = option_map f (tv_lookup o cs ms n).
Proof.
  intros. destruct o; simpl; apply nth_error_map.
Qed.

Lemma tv_lookup_Forall : forall {A : Type} (P : A -> Prop) o cs ms n x,
  Forall P cs -> Forall P ms -> tv_lookup o cs ms n = Some x -> P x.
Proof.
  intros A P o cs ms n x Hc Hm Hl.
  rewrite Forall_forall in Hc. rewrite Forall_forall in Hm.
  destruct o; simpl in Hl; [apply Hc | apply Hm]; eapply nth_error_In; eauto.
Qed.

Lemma Forall2_nth_error_rel : forall {A B : Type} (P : A -> B -> Prop) l1 l2 n,
  Forall2 P l1 l2 ->
  match nth_error l1 n, nth_error l2 n with
  | Some x, Some y => P x y
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros A B P l1 l2 n H. revert n.
  induction H; intros [|n]; simpl; auto.
  apply IHForall2.
Qed.

Lemma tv_lookup_Forall2 : forall {A B : Type} (P : A -> B -> Prop) o cs cs' ms ms' n,
  Forall2 P cs cs' -> Forall2 P ms ms' ->
  match tv_lookup o cs ms n, tv_lookup o cs' ms' n with
  | Some x, Some y => P x y
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros. destruct o; simpl; apply Forall2_nth_error_rel; auto.
Qed.

(** Dynamizing a substituted type is dynamizing the type with dynamized
    arguments. *)
Lemma dyn_subst : forall qctx ca ma Ts Us T,
  dyn qctx ca ma (subst Ts Us T) =
  dyn qctx (map (dyn qctx ca ma) Ts) (map (dyn qctx ca ma) Us) T.
Proof.
  intros qctx ca ma Ts Us T.
  induction T using qualified_type_ind'.
  - simpl. f_equal. rewrite map_map.
    induction H; simpl; auto. f_equal; auto.
  - simpl. rewrite tv_lookup_map.
    destruct (tv_lookup o Ts Us n) as [U|]; simpl.
    + destruct u; auto.
      destruct U as [q1 C1 args1 | u1 o1 n1 | o1 n1 C1 args1]; simpl; auto.
      destruct (tv_lookup o1 ca ma n1) as [R1|]; destruct u1; simpl; auto;
        try (destruct R1; reflexivity).
    + destruct u; reflexivity.
  - assert (Hargs : map (dyn qctx ca ma) (map (subst Ts Us) args) =
              map (dyn qctx (map (dyn qctx ca ma) Ts) (map (dyn qctx ca ma) Us)) args).
    { rewrite map_map. induction H; simpl; auto. f_equal; auto. }
    simpl. rewrite tv_lookup_map.
    destruct (tv_lookup o Ts Us n) as [U|]; simpl.
    + destruct U as [q1 C1 args1 | u1 o1 n1 | o1 n1 C1 args1]; simpl;
        try (rewrite Hargs; reflexivity).
      destruct u1; simpl; rewrite Hargs; auto.
      destruct (tv_lookup o1 ca ma n1) as [R1|]; simpl; auto.
      destruct R1; reflexivity.
    + rewrite Hargs. reflexivity.
Qed.

Lemma map_dyn_subst : forall qctx ca ma Ts Us l,
  map (dyn qctx ca ma) (map (subst Ts Us) l) =
  map (dyn qctx (map (dyn qctx ca ma) Ts) (map (dyn qctx ca ma) Us)) l.
Proof.
  intros. rewrite map_map. apply map_ext. intros. apply dyn_subst.
Qed.

(** Agreement with a fully known runtime type is equality. *)
Lemma rarg_sub_lost_free_eq : forall R U,
  rarg_sub R U -> rlost_free U -> R = U.
Proof.
  intros R U H. induction H using rarg_sub_ind'. intros Hlf.
  apply rlost_free_class in Hlf. destruct Hlf as [Hq Hargs].
  destruct H as [-> | [-> _]]; [|congruence].
  f_equal.
  clear H0 Hq. induction H1; auto.
  inversion Hargs; subst. f_equal; auto.
Qed.

Lemma Forall2_rarg_sub_lost_free_eq : forall Rs Us,
  Forall2 rarg_sub Rs Us -> Forall rlost_free Us -> Rs = Us.
Proof.
  intros Rs Us H. induction H; intros Hlf; auto.
  inversion Hlf; subst. f_equal; auto using rarg_sub_lost_free_eq.
Qed.

Definition concrete_q (q0 : q) : Prop := q0 = Mut \/ q0 = Imm.

Lemma qr2q_concrete : forall qr, concrete_q (qr2q qr).
Proof. destruct qr; [left|right]; reflexivity. Qed.

(** Dynamizing a fully known static type in a fully known activation gives a
    fully known runtime type. *)
Lemma dyn_lost_free : forall qctx ca ma T,
  concrete_q qctx ->
  Forall rlost_free ca -> Forall rlost_free ma ->
  lost_free T -> rlost_free (dyn qctx ca ma T).
Proof.
  intros qctx ca ma T Hq Hca Hma.
  induction T using qualified_type_ind'; intros Hlf.
  - apply lost_free_class in Hlf. destruct Hlf as [Hhead Hargs].
    simpl dyn. apply rlost_free_class. split.
    + destruct qual; simpl; try congruence.
      destruct Hq as [-> | ->]; discriminate.
    + clear Hhead. induction H; simpl; constructor; inversion Hargs; subst; auto.
  - simpl.
    assert (HR : rlost_free
              match tv_lookup o ca ma n with
              | Some R => R
              | None => default_rtype
              end).
    { destruct (tv_lookup o ca ma n) eqn:Hl.
      - eapply (tv_lookup_Forall rlost_free); [exact Hca|exact Hma|exact Hl].
      - simpl. split; [discriminate|exact I]. }
    destruct u; auto.
    destruct (match tv_lookup o ca ma n with Some R => R | None => default_rtype end)
      as [q1 C1 args1].
    apply rlost_free_class in HR. destruct HR as [_ HR].
    simpl rrequalify. apply rlost_free_class. split; auto.
    simpl in Hlf. destruct qual; simpl; try congruence.
    destruct Hq as [-> | ->]; discriminate.
  - apply lost_free_head in Hlf. simpl dyn.
    assert (HR : rlost_free
              match tv_lookup o ca ma n with
              | Some R => R
              | None => default_rtype
              end).
    { destruct (tv_lookup o ca ma n) eqn:Hl.
      - eapply (tv_lookup_Forall rlost_free); [exact Hca|exact Hma|exact Hl].
      - simpl. split; [discriminate|exact I]. }
    destruct (match tv_lookup o ca ma n with Some R => R | None => default_rtype end)
      as [q1 C1 args1].
    apply rlost_free_class in HR. destruct HR as [HR _].
    apply rlost_free_class. split; [exact HR|].
    induction H; simpl; constructor; inversion Hlf; subst; auto.
Qed.

Lemma map_dyn_lost_free : forall qctx ca ma Ts,
  concrete_q qctx ->
  Forall rlost_free ca -> Forall rlost_free ma ->
  Forall lost_free Ts -> Forall rlost_free (map (dyn qctx ca ma) Ts).
Proof.
  intros. induction H2; simpl; constructor; auto using dyn_lost_free.
Qed.

(** Static argument compatibility is preserved by dynamization. *)
Lemma dyn_targ_sub : forall qctx ca ma T U,
  targ_sub T U -> rarg_sub (dyn qctx ca ma T) (dyn qctx ca ma U).
Proof.
  intros qctx ca ma T U H. induction H using targ_sub_ind'.
  - apply rarg_sub_refl.
  - simpl. apply ras_class.
    + destruct H as [-> | [-> [-> | ->]]]; [left; reflexivity| |];
        right; simpl; auto.
    + clear H H0. induction H1; simpl; constructor; auto.
  - simpl. apply ras_class; [left; reflexivity|].
    clear H. induction H0; simpl; constructor; auto.
Qed.

Lemma map_dyn_targ_sub : forall qctx ca ma Ts Us,
  Forall2 targ_sub Ts Us ->
  Forall2 rarg_sub (map (dyn qctx ca ma) Ts) (map (dyn qctx ca ma) Us).
Proof.
  intros. induction H; simpl; constructor; auto using dyn_targ_sub.
Qed.

(** Monotonicity of dynamization: reading a declared type directly in one
    activation agrees, up to forgotten positions, with reading its
    qualifier-mapped version in another, provided the qualifiers and the type
    arguments of the two activations are related the same way. *)
Lemma dyn_map_qual_mono : forall f qa qb ca cb ma mb T,
  (forall q0, arg_q_sub (dynq qa q0) (dynq qb (f q0))) ->
  Forall2 rarg_sub ca cb -> Forall2 rarg_sub ma mb ->
  rarg_sub (dyn qa ca ma T) (dyn qb cb mb (map_qual f T)).
Proof.
  intros f qa qb ca cb ma mb T Hq Hc Hm.
  induction T using qualified_type_ind'.
  - simpl. apply ras_class; auto.
    induction H; simpl; constructor; auto.
  - pose proof (tv_lookup_Forall2 rarg_sub o ca cb ma mb n Hc Hm) as Hl.
    assert (HR : rarg_sub
              match tv_lookup o ca ma n with Some R => R | None => default_rtype end
              match tv_lookup o cb mb n with Some R => R | None => default_rtype end).
    { destruct (tv_lookup o ca ma n), (tv_lookup o cb mb n);
        try contradiction; auto using rarg_sub_refl. }
    destruct u; simpl; auto.
    inversion HR; subst. simpl. apply ras_class; auto.
  - pose proof (tv_lookup_Forall2 rarg_sub o ca cb ma mb n Hc Hm) as Hl.
    assert (HR : rarg_sub
              match tv_lookup o ca ma n with Some R => R | None => default_rtype end
              match tv_lookup o cb mb n with Some R => R | None => default_rtype end).
    { destruct (tv_lookup o ca ma n), (tv_lookup o cb mb n);
        try contradiction; auto using rarg_sub_refl. }
    simpl. inversion HR; subst. simpl. apply ras_class; auto.
    induction H; simpl; constructor; auto.
Qed.

Lemma map_dyn_map_qual_mono : forall f qa qb ca cb ma mb Ts,
  (forall q0, arg_q_sub (dynq qa q0) (dynq qb (f q0))) ->
  Forall2 rarg_sub ca cb -> Forall2 rarg_sub ma mb ->
  Forall2 rarg_sub (map (dyn qa ca ma) Ts)
    (map (dyn qb cb mb) (map (map_qual f) Ts)).
Proof.
  intros. induction Ts; simpl; constructor; auto using dyn_map_qual_mono.
Qed.

Lemma map_qual_id : forall T, map_qual (fun q0 => q0) T = T.
Proof.
  induction T using qualified_type_ind'.
  - simpl. f_equal. induction H; simpl; auto. f_equal; auto.
  - destruct u; reflexivity.
  - simpl. f_equal. induction H; simpl; auto. f_equal; auto.
Qed.

Lemma dyn_mono : forall qa qb ca cb ma mb T,
  (forall q0, arg_q_sub (dynq qa q0) (dynq qb q0)) ->
  Forall2 rarg_sub ca cb -> Forall2 rarg_sub ma mb ->
  rarg_sub (dyn qa ca ma T) (dyn qb cb mb T).
Proof.
  intros. rewrite <- (map_qual_id T) at 2.
  apply dyn_map_qual_mono; auto.
Qed.

Lemma map_dyn_mono : forall qa qb ca cb ma mb Ts,
  (forall q0, arg_q_sub (dynq qa q0) (dynq qb q0)) ->
  Forall2 rarg_sub ca cb -> Forall2 rarg_sub ma mb ->
  Forall2 rarg_sub (map (dyn qa ca ma) Ts) (map (dyn qb cb mb) Ts).
Proof.
  intros. induction Ts; simpl; constructor; auto using dyn_mono.
Qed.

(** An object of mutability [qo] may be seen through a runtime head [rq]. *)
Definition head_sees (qo rq : q) : Prop :=
  rq = RO \/ rq = Lost \/ rq = qo.

(** The qualifier side condition of [dyn_map_qual_mono] for viewpoint
    adaptation: the object's own reading of a written qualifier agrees with
    the client's reading of the adapted qualifier. *)
Lemma dynq_vpa_q_agree : forall mt qo qctx qx q0,
  concrete_q qo -> concrete_q qctx ->
  head_sees qo (dynq qctx qx) ->
  arg_q_sub (dynq qo q0) (dynq qctx (vpa_q mt qx q0)).
Proof.
  intros mt qo qctx qx q0 Hqo Hqctx Hsee.
  unfold arg_q_sub, head_sees in *.
  destruct Hqo as [-> | ->]; destruct Hqctx as [-> | ->];
    destruct mt, qx, q0; simpl in *;
    try (left; reflexivity);
    try (right; split; [reflexivity|auto]; fail);
    destruct Hsee as [Hs | [Hs | Hs]]; discriminate.
Qed.

(** A head that sees the object dynamizes [RDM] no more precisely than the
    object itself does. *)
Lemma dynq_head_agree : forall qo rq q0,
  concrete_q qo -> head_sees qo rq ->
  arg_q_sub (dynq qo q0) (dynq rq q0).
Proof.
  intros qo rq q0 Hqo Hsee. unfold arg_q_sub, head_sees in *.
  destruct Hqo as [-> | ->]; destruct Hsee as [-> | [-> | ->]];
    destruct q0; simpl; auto.
Qed.
