From Stdlib Require Import List Lia Bool PeanoNat.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels ArgViews
  GhostTyping GhostForget GhostFit ArgTyping GhostInvariant ArgFit ArgInvariant
  ArgCases ArgClean GhostOverride ArgOverride RecvRdm.

(** Deciding the receiver part of the override check.

    The override rule asks that every object the overridden receiver admits
    is admitted by the overriding receiver, for every runtime mutability the
    class allows and every list of runtime type arguments.  Whether a
    receiver admits an object depends only on the object's mutability and on
    the head qualifiers of its type arguments, so the condition is decided by
    going through the finitely many lists of head qualifiers.  This file
    defines that procedure and proves it equivalent to the condition. *)

(* ------------------LISTS------------------*)

Lemma Forall2_of_nth : forall (A B : Type) (P : A -> B -> Prop) l l',
  length l = length l' ->
  (forall i x y, nth_error l i = Some x -> nth_error l' i = Some y -> P x y) ->
  Forall2 P l l'.
Proof.
  intros A B P l. induction l as [|x l IH]; intros [|y l'] Hlen Hp;
    simpl in Hlen; try discriminate; constructor.
  - apply (Hp 0); reflexivity.
  - apply IH; [lia|]. intros i. apply (Hp (S i)).
Qed.

Lemma forallb_combine_nth : forall (A B : Type) (f : A * B -> bool) l l',
  forallb f (combine l l') = true <->
  (forall i x y, nth_error l i = Some x -> nth_error l' i = Some y -> f (x, y) = true).
Proof.
  intros A B f l. induction l as [|x l IH]; intros l'; simpl.
  - split; [intros _ [|i] a b H; discriminate | reflexivity].
  - destruct l' as [|y l']; simpl.
    + split; [intros _ [|i] a b _ H; discriminate | reflexivity].
    + rewrite andb_true_iff. rewrite IH. split.
      * intros [H0 Hr] [|i] a b Ha Hb; simpl in *.
        -- inversion Ha; inversion Hb; subst. exact H0.
        -- eauto.
      * intros H. split; [apply (H 0); reflexivity | intros i; apply (H (S i))].
Qed.

(* ------------------HEAD QUALIFIERS------------------*)

Definition arg_q_sub_b (x y : q) : bool :=
  match x, y with
  | Mut, Mut | Imm, Imm | RDM, RDM | RO, RO | Lost, Lost | Bot, Bot => true
  | Mut, Lost | Imm, Lost | RO, Lost => true
  | _, _ => false
  end.

Lemma arg_q_sub_b_iff : forall x y, arg_q_sub_b x y = true <-> arg_q_sub x y.
Proof.
  intros x y. unfold arg_q_sub. split.
  - destruct x, y; simpl; intros H; try discriminate; auto 6.
  - intros [-> | [-> [-> | [-> | ->]]]]; [destruct x|..]; reflexivity.
Qed.

(** What one receiver asks of a list of head qualifiers, in a call with
    qualifier arguments [ka]: each argument that the receiver writes with a
    qualifier has that qualifier, read through the object's mutability, and
    each argument that it writes under a qualifier parameter has the
    qualifier argument for that parameter. *)
Definition adm_b (qr : q) (ka heads : list q) (args : list qualified_type) : bool :=
  forallb (fun p => match snd p with
                    | TVar (TVQual w) _ _ => arg_q_sub_b (fst p) (dynq qr w)
                    | TVar (TVPoly m) _ _ => arg_q_sub_b (fst p) (qnth ka m)
                    | _ => true
                    end) (combine heads args).

(** A receiver admits an object exactly when it accepts the head qualifiers
    of the object's type arguments. *)
Lemma radmit_adm : forall qr ca ka R,
  recv_args (length ca) (targs R) ->
  (radmit qr ca ka R <-> adm_b qr ka (map rhead ca) (targs R) = true).
Proof.
  intros qr ca ka R [Hlen Hsh]. unfold adm_b. rewrite forallb_combine_nth. split.
  - intros Hadm i x T Hx HT.
    rewrite nth_error_map in Hx.
    destruct (nth_error ca i) as [r|] eqn:Hr; [|discriminate]. inversion Hx; subst x.
    destruct (Hsh i T HT) as [u ->]. simpl.
    destruct u as [|w|mw]; [reflexivity| |].
    + apply arg_q_sub_b_iff. apply rarg_sub_requalify_iff.
      assert (Hy : nth_error (map (dyn qr ca [] ka) (targs R)) i =
                   Some (rrequalify (dynq qr w) r)).
      { rewrite nth_error_map. rewrite HT. simpl. rewrite Hr. reflexivity. }
      exact (Forall2_nth _ _ _ _ _ (Hadm []) i _ _ Hr Hy).
    + apply arg_q_sub_b_iff. apply rarg_sub_requalify_iff.
      assert (Hy : nth_error (map (dyn qr ca [] ka) (targs R)) i =
                   Some (rrequalify (qnth ka mw) r)).
      { rewrite nth_error_map. rewrite HT. simpl. rewrite Hr. reflexivity. }
      exact (Forall2_nth _ _ _ _ _ (Hadm []) i _ _ Hr Hy).
  - intros H ma. apply Forall2_of_nth.
    + rewrite length_map. symmetry. exact Hlen.
    + intros i r y Hr Hy. rewrite nth_error_map in Hy.
      destruct (nth_error (targs R) i) as [T|] eqn:HT; [|discriminate].
      inversion Hy; subst y. clear Hy.
      assert (Hx : nth_error (map rhead ca) i = Some (rhead r)).
      { rewrite nth_error_map. rewrite Hr. reflexivity. }
      destruct (Hsh i T HT) as [u ->].
      pose proof (H i _ _ Hx HT) as Hi. simpl in Hi.
      destruct u as [|w|mw]; simpl; rewrite Hr.
      * apply rarg_sub_refl.
      * apply rarg_sub_requalify_iff. apply arg_q_sub_b_iff. exact Hi.
      * apply rarg_sub_requalify_iff. apply arg_q_sub_b_iff. exact Hi.
Qed.

(** The head of a superclass argument, from the heads of the subclass's
    arguments. *)
Definition vhead (qr : q) (hs : list q) (V : qualified_type) : q :=
  match V with
  | TVar TVSub ClassVar k => nth k hs RO
  | _ => rhead (dyn qr [] [] [] V)
  end.

Lemma rhead_dyn_vhead : forall qr ca V,
  rhead (dyn qr ca [] [] V) = vhead qr (map rhead ca) V.
Proof.
  intros qr ca V. destruct V as [q0 C a | u o k | k C a]; simpl; try reflexivity.
  destruct u as [|w|mp].
  - destruct o; simpl.
    + destruct (nth_error ca k) as [r|] eqn:E.
      * symmetry. apply nth_error_nth. rewrite nth_error_map. rewrite E. reflexivity.
      * assert (Hle : length (map rhead ca) <= k).
        { apply nth_error_None. rewrite nth_error_map. rewrite E. reflexivity. }
        rewrite (nth_overflow (map rhead ca) RO Hle). reflexivity.
    + destruct k; reflexivity.
  - rewrite !rhead_rrequalify. reflexivity.
  - rewrite !rhead_rrequalify. reflexivity.
Qed.

(* ------------------THE PROCEDURE------------------*)

Definition q_all : list q := [Mut; Imm; RDM; RO; Lost; Bot].

Lemma q_all_complete : forall x : q, List.In x q_all.
Proof. intros []; simpl; auto 7. Qed.

(** Every list of head qualifiers of a given length. *)
Fixpoint lists_of (n : nat) : list (list q) :=
  match n with
  | 0 => [[]]
  | S k => flat_map (fun l => map (fun x => x :: l) q_all) (lists_of k)
  end.

Lemma lists_of_complete : forall hs, List.In hs (lists_of (length hs)).
Proof.
  induction hs as [|x hs IH]; simpl; [auto|].
  apply in_flat_map. exists hs. split; [exact IH|].
  destruct x; simpl; auto 7.
Qed.

Lemma lists_of_length : forall n hs, List.In hs (lists_of n) -> length hs = n.
Proof.
  induction n as [|n IH]; intros hs H; simpl in H.
  - destruct H as [<- | []]. reflexivity.
  - apply in_flat_map in H. destruct H as (l & Hl & Hx).
    simpl in Hx. specialize (IH l Hl).
    repeat (destruct Hx as [<- | Hx]; [simpl; f_equal; exact IH|]). destruct Hx.
Qed.

Definition compat_b (qc : q_c) (qr : q_r) : bool :=
  match qc, qr with
  | Mut_c, Imm_r => false
  | Imm_c, Mut_r => false
  | _, _ => true
  end.

Lemma compat_b_iff : forall qc qr,
  compat_b qc qr = true <-> ((qc = Mut_c -> qr = Mut_r) /\ (qc = Imm_c -> qr = Imm_r)).
Proof.
  intros [] []; simpl; split; try discriminate; try (intros _; split; congruence);
    try reflexivity; intros [H1 H2];
    try (specialize (H1 eq_refl); discriminate);
    try (specialize (H2 eq_refl); discriminate).
Qed.

(** The check: for each mutability the class allows, each list of head
    qualifiers, and each list of qualifier arguments, if the overridden
    receiver accepts the heads seen at its class, the overriding receiver
    accepts the heads. *)
Definition recv_admit_b (qc : q_c) (n k : nat) (Vs args1 args' : list qualified_type)
    : bool :=
  forallb (fun qr =>
    implb (compat_b qc qr)
      (forallb (fun hs =>
         forallb (fun ka =>
           implb (adm_b (qr2q qr) ka (map (vhead (qr2q qr) hs) Vs) args1)
                 (adm_b (qr2q qr) ka hs args'))
           (lists_of k))
       (lists_of n)))
    [Mut_r; Imm_r].

(** The procedure decides the receiver part of the override check, for a
    class with [n] type parameters and methods with [k] qualifier
    parameters. *)
Theorem recv_admit_b_correct : forall qc n k Vs R1 R',
  recv_args (length Vs) (targs R1) ->
  recv_args n (targs R') ->
  (recv_admit_b qc n k Vs (targs R1) (targs R') = true <->
   forall (qr : q_r) (ca : list rtype) (ka : list q),
     (qc = Mut_c -> qr = Mut_r) -> (qc = Imm_c -> qr = Imm_r) ->
     length ca = n ->
     length ka = k ->
     radmit (qr2q qr) (map (dyn (qr2q qr) ca [] []) Vs) ka R1 ->
     radmit (qr2q qr) ca ka R').
Proof.
  intros qc n k Vs R1 R' Hsh1 Hsh'.
  assert (Hpt : forall (qr : q_r) ca ka, length ca = n ->
            (radmit (qr2q qr) (map (dyn (qr2q qr) ca [] []) Vs) ka R1 <->
             adm_b (qr2q qr) ka (map (vhead (qr2q qr) (map rhead ca)) Vs) (targs R1) = true) /\
            (radmit (qr2q qr) ca ka R' <->
             adm_b (qr2q qr) ka (map rhead ca) (targs R') = true)).
  { intros qr ca ka Hl. split.
    - assert (Hs : recv_args (length (map (dyn (qr2q qr) ca [] []) Vs)) (targs R1)).
      { rewrite length_map. exact Hsh1. }
      pose proof (radmit_adm (qr2q qr) _ ka R1 Hs) as He.
      rewrite map_map in He.
      rewrite (map_ext _ _ (fun V => rhead_dyn_vhead (qr2q qr) ca V)) in He. exact He.
    - apply radmit_adm. rewrite Hl. exact Hsh'. }
  unfold recv_admit_b. split.
  - intros Hb qr ca ka Hm Hi Hl Hk Hadm.
    rewrite forallb_forall in Hb.
    assert (Hin : List.In qr [Mut_r; Imm_r]) by (destruct qr; simpl; auto).
    pose proof (Hb qr Hin) as Hq.
    rewrite (proj2 (compat_b_iff qc qr) (conj Hm Hi)) in Hq. simpl in Hq.
    rewrite forallb_forall in Hq.
    assert (Hhs : List.In (map rhead ca) (lists_of n)).
    { rewrite <- Hl. rewrite <- (length_map rhead ca). apply lists_of_complete. }
    pose proof (Hq _ Hhs) as Hx.
    rewrite forallb_forall in Hx.
    assert (Hks : List.In ka (lists_of k)).
    { rewrite <- Hk. apply lists_of_complete. }
    pose proof (Hx _ Hks) as Hy.
    destruct (Hpt qr ca ka Hl) as [H1 H2].
    apply H2. rewrite (proj1 H1 Hadm) in Hy. exact Hy.
  - intros Hsem. apply forallb_forall. intros qr _.
    destruct (compat_b qc qr) eqn:Ec; [|reflexivity]. simpl.
    apply compat_b_iff in Ec. destruct Ec as [Hm Hi].
    apply forallb_forall. intros hs Hhs.
    apply forallb_forall. intros ka Hks.
    pose proof (lists_of_length _ _ Hhs) as Hlen.
    pose proof (lists_of_length _ _ Hks) as Hklen.
    set (ca := map (fun x => RClass x 0 []) hs).
    assert (Hca : map rhead ca = hs).
    { unfold ca. rewrite map_map. simpl. apply map_id. }
    assert (Hl : length ca = n) by (unfold ca; rewrite length_map; exact Hlen).
    destruct (Hpt qr ca ka Hl) as [H1 H2]. rewrite Hca in H1, H2.
    destruct (adm_b (qr2q qr) ka (map (vhead (qr2q qr) hs) Vs) (targs R1)) eqn:E1;
      [|reflexivity].
    simpl. apply H2. apply (Hsem qr ca ka Hm Hi Hl Hklen). apply H1. reflexivity.
Qed.

(** The two receivers of the override example: [@RO Child<@Mut E>] over
    [@RO Parent<E>] is rejected, [@RO Child<E>] is accepted. *)
Example override_narrowing_decided :
  recv_admit_b RDM_c 1 0 [TVar TVSub ClassVar 0]
    [TVar TVSub ClassVar 0] [TVar (TVQual Mut) ClassVar 0] = false.
Proof. reflexivity. Qed.

Example override_plain_decided :
  recv_admit_b RDM_c 1 0 [TVar TVSub ClassVar 0]
    [TVar TVSub ClassVar 0] [TVar TVSub ClassVar 0] = true.
Proof. reflexivity. Qed.

(** With one qualifier parameter: a receiver that writes its class's
    parameter under the qualifier parameter may override one that does the
    same, and may not override one that writes it plainly. *)
Example override_poly_same_decided :
  recv_admit_b RDM_c 1 1 [TVar TVSub ClassVar 0]
    [TVar (TVPoly 0) ClassVar 0] [TVar (TVPoly 0) ClassVar 0] = true.
Proof. reflexivity. Qed.

Example override_poly_narrowing_decided :
  recv_admit_b RDM_c 1 1 [TVar TVSub ClassVar 0]
    [TVar TVSub ClassVar 0] [TVar (TVPoly 0) ClassVar 0] = false.
Proof. reflexivity. Qed.

Print Assumptions recv_admit_b_correct.
