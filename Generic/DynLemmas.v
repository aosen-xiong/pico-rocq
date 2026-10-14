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

Lemma qnth_map : forall (f : qarg -> q) Qs n,
  qnth (map f Qs) n =
  match nth_error Qs n with Some a => f a | None => RO end.
Proof.
  intros f Qs. unfold qnth.
  induction Qs as [|a Qs IH]; intros [|n]; simpl; auto.
Qed.

(** Dynamizing a type whose outer qualifier was replaced. *)
Lemma dyn_requalify : forall qctx ca ma ka q0 U,
  dyn qctx ca ma ka (requalify q0 U) =
  rrequalify (dynq qctx q0) (dyn qctx ca ma ka U).
Proof.
  intros qctx ca ma ka q0 U.
  destruct U as [q1 C1 args1 | u1 o1 n1 | n1 C1 args1]; simpl; auto.
  destruct (tv_lookup o1 ca ma n1) as [R1|]; destruct u1; simpl; auto;
    try (destruct R1; reflexivity).
Qed.

Lemma dyn_prequalify : forall qctx ca ma ka m U,
  dyn qctx ca ma ka (prequalify m U) =
  rrequalify (qnth ka m) (dyn qctx ca ma ka U).
Proof.
  intros qctx ca ma ka m U.
  destruct U as [q1 C1 args1 | u1 o1 n1 | n1 C1 args1]; simpl; auto.
  destruct (tv_lookup o1 ca ma n1) as [R1|]; destruct u1; simpl; auto;
    try (destruct R1; reflexivity).
Qed.

Lemma dyn_qrequalify : forall qctx ca ma ka a U,
  dyn qctx ca ma ka (qrequalify a U) =
  rrequalify (match a with Some x => rqarg qctx ka x | None => RO end)
    (dyn qctx ca ma ka U).
Proof.
  intros qctx ca ma ka a U. destruct a as [[q0|m]|]; simpl.
  - apply dyn_requalify.
  - apply dyn_prequalify.
  - apply (dyn_requalify qctx ca ma ka RO U).
Qed.

(** Dynamizing a substituted type is dynamizing the type with dynamized
    arguments. *)
Lemma dyn_subst : forall qctx ca ma ka Ts Us Qs T,
  dyn qctx ca ma ka (subst Ts Us Qs T) =
  dyn qctx (map (dyn qctx ca ma ka) Ts) (map (dyn qctx ca ma ka) Us)
    (map (rqarg qctx ka) Qs) T.
Proof.
  intros qctx ca ma ka Ts Us Qs T.
  induction T using qualified_type_ind'.
  - simpl. f_equal. rewrite map_map.
    induction H; simpl; auto. f_equal; auto.
  - simpl. rewrite tv_lookup_map.
    destruct (tv_lookup o Ts Us n) as [U|]; simpl.
    + destruct u as [|q0|m]; auto.
      * apply dyn_requalify.
      * rewrite qnth_map. apply dyn_qrequalify.
    + destruct u as [|q0|m]; try reflexivity.
      rewrite qnth_map. destruct (nth_error Qs m) as [[q0|m']|]; reflexivity.
  - assert (Hargs : map (dyn qctx ca ma ka) (map (subst Ts Us Qs) args) =
              map (dyn qctx (map (dyn qctx ca ma ka) Ts) (map (dyn qctx ca ma ka) Us)
    (map (rqarg qctx ka) Qs)) args).
    { rewrite map_map. induction H; simpl; auto. f_equal; auto. }
    transitivity (RClass
                    (match nth_error Qs n with
                     | Some a => rqarg qctx ka a | None => RO end) C
                    (map (dyn qctx (map (dyn qctx ca ma ka) Ts)
                            (map (dyn qctx ca ma ka) Us)
                            (map (rqarg qctx ka) Qs)) args));
      [|simpl; rewrite qnth_map; reflexivity].
    simpl. destruct (nth_error Qs n) as [[q0|m]|]; simpl; rewrite Hargs;
      reflexivity.
Qed.

Lemma map_dyn_subst : forall qctx ca ma ka Ts Us Qs l,
  map (dyn qctx ca ma ka) (map (subst Ts Us Qs) l) =
  map (dyn qctx (map (dyn qctx ca ma ka) Ts) (map (dyn qctx ca ma ka) Us)
    (map (rqarg qctx ka) Qs)) l.
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

Lemma qnth_not_lost : forall ka n,
  Forall (fun q0 => q0 <> Lost) ka -> qnth ka n <> Lost.
Proof.
  intros ka n H. unfold qnth. revert n.
  induction H; intros [|n]; simpl; auto; discriminate.
Qed.

(** Dynamizing a fully known static type in a fully known activation gives a
    fully known runtime type. *)
Lemma dyn_lost_free : forall qctx ca ma ka T,
  concrete_q qctx ->
  Forall rlost_free ca -> Forall rlost_free ma ->
  Forall (fun q0 => q0 <> Lost) ka ->
  lost_free T -> rlost_free (dyn qctx ca ma ka T).
Proof.
  intros qctx ca ma ka T Hq Hca Hma Hka.
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
    destruct u as [|qual|m]; auto;
      destruct (match tv_lookup o ca ma n with Some R => R | None => default_rtype end)
        as [q1 C1 args1];
      apply rlost_free_class in HR; destruct HR as [_ HR];
      simpl rrequalify; apply rlost_free_class; (split; [|exact HR]).
    + simpl in Hlf. destruct qual; simpl; try congruence.
      destruct Hq as [-> | ->]; discriminate.
    + apply qnth_not_lost; exact Hka.
  - apply lost_free_head in Hlf. simpl dyn.
    apply rlost_free_class. split; [apply qnth_not_lost; exact Hka|].
    induction H; simpl; constructor; inversion Hlf; subst; auto.
Qed.

Lemma map_dyn_lost_free : forall qctx ca ma ka Ts,
  concrete_q qctx ->
  Forall rlost_free ca -> Forall rlost_free ma ->
  Forall (fun q0 => q0 <> Lost) ka ->
  Forall lost_free Ts -> Forall rlost_free (map (dyn qctx ca ma ka) Ts).
Proof.
  intros qctx ca ma ka Ts Hq Hca Hma Hka HTs.
  induction HTs; simpl; constructor; auto using dyn_lost_free.
Qed.

(** Static argument compatibility is preserved by dynamization. *)
Lemma dyn_targ_sub : forall qctx ca ma ka T U,
  targ_sub T U -> rarg_sub (dyn qctx ca ma ka T) (dyn qctx ca ma ka U).
Proof.
  intros qctx ca ma ka T U H. induction H using targ_sub_ind'.
  - apply rarg_sub_refl.
  - simpl. apply ras_class.
    + destruct H as [-> | [-> [-> | [-> | ->]]]]; [left; reflexivity| | |];
        right; simpl; auto.
    + clear H H0. induction H1; simpl; constructor; auto.
  - simpl. apply ras_class; [left; reflexivity|].
    clear H. induction H0; simpl; constructor; auto.
Qed.

Lemma map_dyn_targ_sub : forall qctx ca ma ka Ts Us,
  Forall2 targ_sub Ts Us ->
  Forall2 rarg_sub (map (dyn qctx ca ma ka) Ts) (map (dyn qctx ca ma ka) Us).
Proof.
  intros. induction H; simpl; constructor; auto using dyn_targ_sub.
Qed.

(** Monotonicity of dynamization: reading a declared type directly in one
    activation agrees, up to forgotten positions, with reading its
    qualifier-mapped version in another, provided the qualifiers and the type
    arguments of the two activations are related the same way. *)
Lemma dyn_map_qual_mono : forall f qa qb ca cb ma mb ka T,
  (forall q0, arg_q_sub (dynq qa q0) (dynq qb (f q0))) ->
  Forall2 rarg_sub ca cb -> Forall2 rarg_sub ma mb ->
  rarg_sub (dyn qa ca ma ka T) (dyn qb cb mb ka (map_qual f T)).
Proof.
  intros f qa qb ca cb ma mb ka T Hq Hc Hm.
  induction T using qualified_type_ind'.
  - simpl. apply ras_class; auto.
    induction H; simpl; constructor; auto.
  - pose proof (tv_lookup_Forall2 rarg_sub o ca cb ma mb n Hc Hm) as Hl.
    assert (HR : rarg_sub
              match tv_lookup o ca ma n with Some R => R | None => default_rtype end
              match tv_lookup o cb mb n with Some R => R | None => default_rtype end).
    { destruct (tv_lookup o ca ma n), (tv_lookup o cb mb n);
        try contradiction; auto using rarg_sub_refl. }
    destruct u; simpl; auto;
      (inversion HR; subst; simpl; apply ras_class; auto; left; reflexivity).
  - simpl. apply ras_class; [left; reflexivity|].
    induction H; simpl; constructor; auto.
Qed.

Lemma map_dyn_map_qual_mono : forall f qa qb ca cb ma mb ka Ts,
  (forall q0, arg_q_sub (dynq qa q0) (dynq qb (f q0))) ->
  Forall2 rarg_sub ca cb -> Forall2 rarg_sub ma mb ->
  Forall2 rarg_sub (map (dyn qa ca ma ka) Ts)
    (map (dyn qb cb mb ka) (map (map_qual f) Ts)).
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

Lemma dyn_mono : forall qa qb ca cb ma mb ka T,
  (forall q0, arg_q_sub (dynq qa q0) (dynq qb q0)) ->
  Forall2 rarg_sub ca cb -> Forall2 rarg_sub ma mb ->
  rarg_sub (dyn qa ca ma ka T) (dyn qb cb mb ka T).
Proof.
  intros. rewrite <- (map_qual_id T) at 2.
  apply dyn_map_qual_mono; auto.
Qed.

Lemma map_dyn_mono : forall qa qb ca cb ma mb ka Ts,
  (forall q0, arg_q_sub (dynq qa q0) (dynq qb q0)) ->
  Forall2 rarg_sub ca cb -> Forall2 rarg_sub ma mb ->
  Forall2 rarg_sub (map (dyn qa ca ma ka) Ts) (map (dyn qb cb mb ka) Ts).
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
