From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels GhostTyping
  GhostForget GhostFit GhostInvariant GhostOverride.

(** Method calls for the label invariant. *)

(* ------------------SMALL FACTS------------------*)

Lemma headL_of_norm : forall L c l,
  norm L (olab c) = norm L l ->
  match norm L l with
  | Some w => c = Some w
  | None => forall w, c = Some w -> ~ List.In w L
  end.
Proof.
  intros L c l H. rewrite <- H. destruct c as [w|]; unfold olab, norm.
  - destruct (in_dec Nat.eq_dec w L) as [Hin | Hnin]; [reflexivity|].
    intros w' Hw. inversion Hw; subst. exact Hnin.
  - intros w Hw. discriminate.
Qed.



Lemma lab_of_with_args : forall F cs ms q0,
  lab_of (lf_with_args F cs ms) q0 = lab_of F q0.
Proof. intros. destruct q0; reflexivity. Qed.



Lemma Forall2_lagree_lift : forall L Lc n As Bs,
  (forall A B, lagree L A B -> lbound n A -> lbound n B -> lagree Lc A B) ->
  Forall2 (lagree L) As Bs ->
  Forall (lbound n) As -> Forall (lbound n) Bs ->
  Forall2 (lagree Lc) As Bs.
Proof.
  intros L Lc n As Bs Hl H. induction H; intros HA HB; constructor;
    inversion HA; inversion HB; subst; auto.
Qed.

Lemma mutcL_update : forall CT h G lx ox f0 vy,
  mutcL CT h G -> runtime_getObj h lx = Some ox ->
  mutcL CT (update_field h lx f0 vy) G.
Proof.
  intros CT h G lx ox f0 vy HM Hox l w o Hb Ho Hq.
  destruct (Nat.eq_dec l lx) as [-> | Hne].
  - rewrite (update_field_getObj_same _ _ f0 vy _ Hox) in Ho.
    inversion Ho; subst o. destruct ox as [rt fs]. simpl in Hq.
    exact (HM lx w _ Hb Hox Hq).
  - rewrite update_field_getObj_diff in Ho; auto. exact (HM l w o Hb Ho Hq).
Qed.

(** Before the call: the callee's reading of an overridden parameter type
    against the caller's reading of the adapted one.  Written mutable
    positions do not occur in such a type. *)
Lemma lc_call_pre : forall L Lc next a qr b c Fc wf' m0 cs ms cs' ms',
  label_cond L a (obj_frame qr b c []) Fc ->
  (forall l, lab_bound next l -> norm Lc l = norm L l) ->
  lab_bound next (olab c) -> frame_bound next Fc ->
  (qr = Mut_r -> norm Lc (olab c) = norm Lc (if m0 then LIn wf' else LOut)) ->
  label_cond Lc (fun q0 => match q0 with Mut => Lost | _ => a q0 end)
    (act_frame qr wf' m0 cs ms) (lf_with_args Fc cs' ms').
Proof.
  intros L Lc next a qr b c Fc wf' m0 cs ms cs' ms' Hc W13 Hbc HFb W4 q0.
  destruct (Hc q0) as [Ha Hb]. rewrite lab_of_with_args.
  destruct (q_eq_dec q0 Mut) as [-> | Hnm].
  - split; [simpl; unfold arg_q_sub; right; split; auto | left; reflexivity].
  - assert (Heq : match q0 with Mut => Lost | _ => a q0 end = a q0)
      by (destruct q0; congruence).
    rewrite Heq. split; [exact Ha|].
    destruct Hb as [H | [H | H]]; [left; exact H | right; left; exact H |].
    destruct (q_eq_dec q0 RDM) as [-> | Hnr].
    + destruct qr; [|right; left; simpl; discriminate].
      right. right.
      change (lab_of (act_frame Mut_r wf' m0 cs ms) RDM)
        with (if m0 then LIn wf' else LOut).
      rewrite <- (W4 eq_refl). rewrite (W13 _ Hbc).
      rewrite (W13 (lab_of Fc (a RDM)) (lab_of_bound _ _ _ HFb)). exact H.
    + right. left. destruct q0; simpl; congruence.
Qed.

(** After the call. *)
Lemma lc_call_post : forall L a qr b c Fc wf' mtop cs ms cs' ms',
  label_cond L a (obj_frame qr b c []) Fc ->
  norm L (olab b) = norm L (LIn wf') ->
  (qr = Mut_r -> norm L (olab c) = norm L (if mtop then LIn wf' else LOut)) ->
  label_cond L a (act_frame qr wf' mtop cs ms) (lf_with_args Fc cs' ms').
Proof.
  intros L a qr b c Fc wf' mtop cs ms cs' ms' Hc N1 N2 q0.
  destruct (Hc q0) as [Ha Hb]. rewrite lab_of_with_args.
  split; [exact Ha|].
  destruct Hb as [H | [H | H]]; [left; exact H | right; left; exact H |].
  destruct (q_eq_dec q0 Mut) as [-> | Hnm].
  - right. right.
    change (lab_of (act_frame qr wf' mtop cs ms) Mut) with (LIn wf').
    rewrite <- N1. exact H.
  - destruct (q_eq_dec q0 RDM) as [-> | Hnr].
    + destruct qr; [|right; left; simpl; discriminate].
      right. right.
      change (lab_of (act_frame Mut_r wf' mtop cs ms) RDM)
        with (if mtop then LIn wf' else LOut).
      rewrite <- (N2 eq_refl). exact H.
    + right. left. destruct q0; simpl; congruence.
Qed.

Lemma label_cond_unm : forall L f Fo Fc,
  label_cond L f Fo Fc -> label_cond L (unm f) Fo Fc.
Proof.
  intros L f Fo Fc H q0. destruct q0; try exact (H _).
  simpl. split; [unfold arg_q_sub; right; split; auto | left; reflexivity].
Qed.
