From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases
  PreservationCall ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels
  GhostTyping.

(** Forgetting the mutable positions of a type: a written [Mut] becomes
    [Lost].  Subtyping in readonly-state and transitive-state code keeps
    labels on the forgotten types even when the labels at the forgotten
    positions are not known. *)

Definition fl (q0 : q) : q := match q0 with Mut => Lost | _ => q0 end.
Notation fT := (map_qual fl).

Lemma fl_ne : forall q0, q0 <> Mut -> fl q0 = q0.
Proof. intros q0 H. destruct q0; simpl; congruence. Qed.

Lemma map_qual_comp : forall f g T,
  map_qual f (map_qual g T) = map_qual (fun q0 => f (g q0)) T.
Proof.
  intros f g T. induction T using qualified_type_ind'.
  - simpl. f_equal. rewrite map_map. induction H; simpl; auto. f_equal; auto.
  - destruct u; reflexivity.
  - simpl. f_equal. rewrite map_map. induction H; simpl; auto. f_equal; auto.
Qed.

Lemma fT_requalify : forall q0 U, fT (requalify q0 U) = requalify (fl q0) (fT U).
Proof. intros q0 [q1 C a | [|q1|mp] o n | n C a]; reflexivity. Qed.

(** Forgetting a written mutable qualifier argument. *)
Definition fQ (a : qarg) : qarg :=
  match a with
  | QLit q0 => QLit (fl q0)
  | QVar m => QVar m
  end.

Lemma fQ_qvar_args : forall k, map fQ (qvar_args k) = qvar_args k.
Proof. intros. unfold qvar_args. rewrite map_map. reflexivity. Qed.

Lemma fT_prequalify : forall m U, fT (prequalify m U) = prequalify m (fT U).
Proof. intros m [q1 C a | [|q1|mp] o n | n C a]; reflexivity. Qed.

Lemma fT_qrequalify : forall a U,
  fT (qrequalify a U) = qrequalify (option_map fQ a) (fT U).
Proof.
  intros [[q0|m]|] U; simpl;
    [apply fT_requalify | apply fT_prequalify | apply (fT_requalify RO U)].
Qed.

Lemma fT_subst : forall Ts Us Qs T,
  fT (subst Ts Us Qs T) = subst (map fT Ts) (map fT Us) (map fQ Qs) (fT T).

(** Place in the proof: forgetting the mutable positions of a type (a written
    Mut becomes Lost) and what labelled conditions and subtyping become under
    it; used by overriding and by qualified uses of type variables.
    Counterpart in the non-generic proof (ReadonlyWorlds.v): none; a device of
    the labelled proof. *)
Proof.
  intros Ts Us Qs T. induction T using qualified_type_ind'.
  - simpl. f_equal. rewrite map_map. rewrite map_map.
    induction H; simpl; auto. f_equal; auto.
  - assert (Hl : match tv_lookup o (map fT Ts) (map fT Us) n with
                 | Some U => U | None => default_type end =
                 fT (match tv_lookup o Ts Us n with
                     | Some U => U | None => default_type end)).
    { destruct o; simpl; rewrite nth_error_map;
        destruct (nth_error _ n); reflexivity. }
    destruct u as [|qv|mp].
    + change (fT (match tv_lookup o Ts Us n with
                  | Some U => U | None => default_type end) =
              match tv_lookup o (map fT Ts) (map fT Us) n with
              | Some U => U | None => default_type end).
      symmetry. exact Hl.
    + change (fT (requalify qv
                    (match tv_lookup o Ts Us n with
                     | Some U => U | None => default_type end)) =
              requalify (fl qv)
                (match tv_lookup o (map fT Ts) (map fT Us) n with
                 | Some U => U | None => default_type end)).
      rewrite Hl. apply fT_requalify.
    + change (fT (qrequalify (nth_error Qs mp)
                    (match tv_lookup o Ts Us n with
                     | Some U => U | None => default_type end)) =
              qrequalify (nth_error (map fQ Qs) mp)
                (match tv_lookup o (map fT Ts) (map fT Us) n with
                 | Some U => U | None => default_type end)).
      rewrite Hl. rewrite nth_error_map. apply fT_qrequalify.
  - assert (Hargs : map fT (map (subst Ts Us Qs) args) =
              map (subst (map fT Ts) (map fT Us) (map fQ Qs)) (map fT args)).
    { rewrite !map_map. induction H; simpl; auto. f_equal; auto. }
    cbn [subst map_qual]. rewrite nth_error_map.
    destruct (nth_error Qs n) as [[q0|m]|]; cbn [option_map qhead fQ map_qual];
      rewrite Hargs; reflexivity.
Qed.

Lemma targ_sub_fl : forall T U, targ_sub T U -> targ_sub (fT T) (fT U).
Proof.
  intros T U H. induction H using targ_sub_ind'.
  - destruct u; constructor.
  - simpl. constructor.
    + destruct H as [-> | [-> [-> | [-> | [-> | [-> | ->]]]]]]; unfold arg_q_sub; simpl; auto 8.
    + clear H H0. induction H1; simpl; constructor; auto.
  - simpl. constructor.
    clear H. induction H0; simpl; constructor; auto.
  - simpl. apply tas_qvar_lost.
Qed.

Lemma no_mut_fT : forall Δ T, no_mut Δ T -> fT T = T.
Proof.
  intros Δ T. induction T using qualified_type_ind'; intros Hnm.
  - inversion Hnm; subst. simpl. f_equal; [apply fl_ne; auto|].
    clear Hnm Hq. induction H; simpl; auto.
    inversion Hargs; subst. f_equal; auto.
  - inversion Hnm; subst; simpl; auto. rewrite fl_ne; auto.
  - inversion Hnm; subst. simpl. f_equal.
    clear Hnm. induction H; simpl; auto.
    inversion Hargs; subst. f_equal; auto.
Qed.

(* ------------------LABEL CONDITIONS UNDER FORGETTING------------------*)

Lemma label_cond_fl : forall L f Fo Fc,
  label_cond L f Fo Fc -> label_cond L (fun q0 => fl (f q0)) Fo Fc.
Proof.
  intros L f Fo Fc H q0. destruct (H q0) as [Ha Hb].
  destruct (q_eq_dec (f q0) Mut) as [E | E].
  - rewrite E in Ha. rewrite E. simpl in Ha. simpl.
    split; [|left; reflexivity].
    destruct Ha as [Ha | [Ha _]]; [|discriminate].
    rewrite <- Ha. right. split; auto.
  - rewrite (fl_ne _ E). split; auto.
Qed.

Lemma fl_label_cond_mut : forall L mt qo b c As qthis wf mode lc lm lk,
  readonly_state_method_scope mt ->
  label_cond L (fun q0 => fl (vpa_q mt Mut q0)) (obj_frame qo b c As)
    (act_frame qthis wf mode lc lm lk).
Proof.
  intros L mt qo b c As qthis wf mode lc lm lk Hrs q0.
  destruct Hrs as [-> | ->]; destruct q0, qo, qthis; simpl; unfold arg_q_sub;
    (split; [ solve [left; reflexivity] || solve [right; split; auto]
            | solve [left; reflexivity] || solve [right; left; discriminate] ]).
Qed.

(* ------------------SUBTYPING ON FORGOTTEN TYPES------------------*)

(** Forgetting mutable positions leaves a forgotten bound unchanged. *)
Lemma fl_widen : forall T, class_only_b T = true -> fT (widen_args T) = widen_args T.
Proof.
  intros T. induction T using qualified_type_ind'; intros Hco; simpl in *;
    try discriminate.
  f_equal; [destruct qual; reflexivity|].
  rewrite map_map. revert Hco. induction H; intros Hco; simpl in *; auto.
  apply andb_prop in Hco as [H1 H2]. f_equal; auto.
Qed.

Lemma map_fl_widen : forall Ts, forallb class_only_b Ts = true ->
  map fT (map widen_args Ts) = map widen_args Ts.
Proof.
  induction Ts as [|T Ts IH]; intros Hco; simpl in *; auto.
  apply andb_prop in Hco as [H1 H2]. f_equal; auto using fl_widen.
Qed.

