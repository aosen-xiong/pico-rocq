From Stdlib Require Import List Lia Bool PeanoNat.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels ArgViews
  GhostTyping GhostForget GhostFit ArgTyping GhostInvariant ArgFit ArgInvariant
  ArgCases ArgClean GhostOverride ArgOverride.

(** A declared receiver that requalifies a type parameter of its class as
    receiver-dependent, in a readonly-state or transitive-state method.

    Such an argument, on a mutable receiver, is mutable, so its label must be
    the receiver's own.  The caller knows this for the declaration it sees;
    this file carries the fact to the declaration that runs. *)

(* ------------------LISTS------------------*)

Lemma Forall2_nth : forall (A B : Type) (P : A -> B -> Prop) l l',
  Forall2 P l l' ->
  forall i x y, nth_error l i = Some x -> nth_error l' i = Some y -> P x y.
Proof.
  intros A B P l l' H. induction H; intros [|i] a b Ha Hb; simpl in *;
    try discriminate.
  - inversion Ha; inversion Hb; subst. assumption.
  - eauto.
Qed.

Lemma Forall2_map2_nth : forall (A B C D C' D' : Type)
    (P : C -> D -> Prop) (Q : C' -> D' -> Prop)
    (f : A -> C) (g : B -> D) (f0 : A -> C') (g0 : B -> D') l a,
  Forall2 P (map f l) (map g a) ->
  (forall i x y, nth_error l i = Some x -> nth_error a i = Some y ->
     P (f x) (g y) -> Q (f0 x) (g0 y)) ->
  Forall2 Q (map f0 l) (map g0 a).
Proof.
  intros A B C D C' D' P Q f g f0 g0 l. induction l as [|x l IH];
    intros [|y a] H Hp; simpl in H; inversion H; subst; simpl; constructor.
  - apply (Hp 0); auto.
  - apply IH; auto. intros i. apply (Hp (S i)).
Qed.

(* ------------------HEADS------------------*)

Lemma rhead_rrequalify : forall q0 R, rhead (rrequalify q0 R) = q0.
Proof. intros q0 [q1 C a]. reflexivity. Qed.

Lemma rarg_sub_requalify_iff : forall R q0,
  rarg_sub R (rrequalify q0 R) <-> arg_q_sub (rhead R) q0.
Proof.
  intros [q1 C a] q0. simpl. split.
  - intros H. inversion H; subst. assumption.
  - intros H. apply ras_class; [exact H | apply Forall2_rarg_sub_refl].
Qed.

(** A mutable qualifier argument forgotten to [Lost]. *)
Definition unmq (q0 : q) : q := match q0 with Mut => Lost | _ => q0 end.

Lemma qnth_map_unmq : forall ka n, qnth (map unmq ka) n = unmq (qnth ka n).
Proof.
  intros ka n. unfold qnth. change RO with (unmq RO) at 1. apply map_nth.
Qed.

Lemma arg_q_sub_unmq : forall h x, arg_q_sub h x -> arg_q_sub h (unmq x).
Proof.
  intros h x [-> | [-> H]]; unfold arg_q_sub.
  - destruct h; simpl; auto.
  - simpl. auto.
Qed.

Lemma arg_q_sub_unmq_imm : forall x, arg_q_sub Mut x -> arg_q_sub Imm (unmq x).
Proof.
  intros x [-> | [-> _]]; unfold arg_q_sub; simpl; auto.
Qed.

Lemma plain_dec : forall (T : qualified_type) j,
  {T = TVar TVSub ClassVar j} + {T <> TVar TVSub ClassVar j}.
Proof.
  intros [q0 C a | [|q0|mp] [|] n | n C a] j; try (right; discriminate).
  destruct (Nat.eq_dec n j) as [-> | Hne]; [left; reflexivity|].
  right. intros H. inversion H. contradiction.
Qed.

(** The head of a resolved type does not depend on a class argument that the
    type is not a plain use of. *)
Lemma dyn_head_other : forall qctx ca ca0 ma ka j T,
  (forall k, k <> j -> nth_error ca0 k = nth_error ca k) ->
  T <> TVar TVSub ClassVar j ->
  rhead (dyn qctx ca0 ma ka T) = rhead (dyn qctx ca ma ka T).
Proof.
  intros qctx ca ca0 ma ka j T Hk HT.
  destruct T as [q0 C a | u o n | n C a]; simpl; try reflexivity.
  destruct u as [|q0|mp].
  - destruct o; simpl; [|reflexivity].
    assert (Hn : n <> j) by (intros ->; apply HT; reflexivity).
    rewrite (Hk n Hn). reflexivity.
  - rewrite !rhead_rrequalify. reflexivity.
  - rewrite !rhead_rrequalify. reflexivity.
Qed.

(* ------------------WHERE A RECEIVER-DEPENDENT ARGUMENT COMES FROM------------------*)

Definition is_src (j : nat) (V a : qualified_type) : bool :=
  match V, a with
  | TVar TVSub ClassVar k, TVar (TVQual RDM) ClassVar _ => Nat.eqb k j
  | _, _ => false
  end.

Lemma is_src_true : forall j V a,
  is_src j V a = true ->
  V = TVar TVSub ClassVar j /\ exists i, a = TVar (TVQual RDM) ClassVar i.
Proof.
  intros j V a H.
  destruct V as [q0 C l | u o k | n C l]; simpl in H; try discriminate.
  destruct u; try discriminate. destruct o; try discriminate.
  destruct a as [q1 C1 l1 | u1 o1 i | n1 C1 l1]; try discriminate.
  destruct u1 as [|q1|mp]; try discriminate.
  destruct q1; try discriminate. destruct o1; try discriminate.
  apply Nat.eqb_eq in H. subst. eauto.
Qed.

Lemma find_src : forall j Vs args1,
  (exists i V a, nth_error Vs i = Some V /\ nth_error args1 i = Some a /\
                 is_src j V a = true) \/
  (forall i V a, nth_error Vs i = Some V -> nth_error args1 i = Some a ->
                 is_src j V a = false).
Proof.
  intros j Vs. induction Vs as [|V Vs IH]; intros args1.
  - right. intros [|i] V a H; discriminate.
  - destruct args1 as [|a args1].
    + right. intros [|i] V0 a0 _ H; discriminate.
    + destruct (is_src j V a) eqn:E.
      * left. exists 0, V, a. auto.
      * destruct (IH args1) as [(i & V0 & a0 & H1 & H2 & H3) | Hnone].
        -- left. exists (S i), V0, a0. auto.
        -- right. intros [|i] V0 a0 H1 H2; simpl in *.
           ++ inversion H1; inversion H2; subst. exact E.
           ++ eauto.
Qed.

(** If an override requalifies its class's [j]-th parameter as
    receiver-dependent, and accepts every object the overridden receiver
    accepts, then the overridden receiver requalifies as receiver-dependent a
    parameter that receives the [j]-th parameter unchanged.  The overridden
    receiver requalifies nothing as mutable. *)
Lemma recv_rdm_source : forall n n1 Vs args1 args' ca ka j Cj aj R1 R',
  targs R1 = args1 -> targs R' = args' ->
  recv_args n1 args1 -> recv_args n args' ->
  length Vs = n1 -> length ca = n ->
  (forall i u, nth_error args1 i = Some (TVar (TVQual u) ClassVar i) -> u <> Mut) ->
  (forall ka0 ca0, length ka0 = length ka -> length ca0 = n ->
     radmit Mut (map (dyn Mut ca0 [] []) Vs) ka0 R1 -> radmit Mut ca0 ka0 R') ->
  radmit Mut (map (dyn Mut ca [] []) Vs) ka R1 ->
  nth_error args' j = Some (TVar (TVQual RDM) ClassVar j) ->
  nth_error ca j = Some (RClass Mut Cj aj) ->
  exists i, nth_error Vs i = Some (TVar TVSub ClassVar j) /\
            nth_error args1 i = Some (TVar (TVQual RDM) ClassVar i).
Proof.
  intros n n1 Vs args1 args' ca ka j Cj aj R1 R' Hta1 Hta' [Hl1 Hsh1] [Hl' Hsh']
    HlV Hlca Hnomut Hadm Hact Hj Hcaj.
  destruct (find_src j Vs args1) as [(i & V & a & HV & Ha & Hs) | Hnone].
  { destruct (is_src_true _ _ _ Hs) as [-> [i' ->]].
    destruct (Hsh1 i _ Ha) as [u E]. inversion E; subst. eauto. }
  exfalso.
  set (ca0 := update j (RClass Imm Cj aj) ca).
  assert (Hjlt : j < length ca).
  { apply nth_error_Some. rewrite Hcaj. discriminate. }
  assert (Hca0j : nth_error ca0 j = Some (RClass Imm Cj aj)).
  { unfold ca0. apply update_same. exact Hjlt. }
  assert (Hca0k : forall k, k <> j -> nth_error ca0 k = nth_error ca k).
  { intros k Hk. unfold ca0. apply update_diff. auto. }
  assert (H0 : radmit Mut (map (dyn Mut ca0 [] []) Vs) (map unmq ka) R1).
  { intros ma. rewrite Hta1. specialize (Hact ma). rewrite Hta1 in Hact.
    eapply Forall2_map2_nth; [exact Hact|].
    intros i V a HV Ha Hrel.
    destruct (Hsh1 i a Ha) as [u ->].
    destruct u as [|u|mu].
    - simpl. rewrite nth_error_map. rewrite HV. simpl. apply rarg_sub_refl.
    - simpl in Hrel. rewrite nth_error_map in Hrel. rewrite HV in Hrel.
      simpl in Hrel. apply rarg_sub_requalify_iff in Hrel.
      simpl. rewrite nth_error_map. rewrite HV. simpl.
      apply rarg_sub_requalify_iff.
      destruct (plain_dec V j) as [-> | Hne].
      + pose proof (Hnone i _ _ HV Ha) as Hf. simpl in Hf.
        rewrite Nat.eqb_refl in Hf.
        assert (Hu : u <> Mut) by (eapply Hnomut; eauto).
        simpl. rewrite Hca0j. simpl.
        simpl in Hrel. rewrite Hcaj in Hrel. simpl in Hrel.
        destruct u; simpl in *; try discriminate; try congruence;
          destruct Hrel as [Hx | [Hx _]]; try discriminate.
        right. split; auto.
      + rewrite (dyn_head_other Mut ca ca0 [] [] j V Hca0k Hne). exact Hrel.
    - (* under a qualifier parameter: with every mutable qualifier argument
         forgotten, the changed argument is still admitted *)
      simpl in Hrel. rewrite nth_error_map in Hrel. rewrite HV in Hrel.
      simpl in Hrel. apply rarg_sub_requalify_iff in Hrel.
      simpl. rewrite nth_error_map. rewrite HV. simpl.
      apply rarg_sub_requalify_iff. rewrite qnth_map_unmq.
      destruct (plain_dec V j) as [-> | Hne].
      + simpl. rewrite Hca0j. simpl.
        simpl in Hrel. rewrite Hcaj in Hrel. simpl in Hrel.
        apply arg_q_sub_unmq_imm. exact Hrel.
      + rewrite (dyn_head_other Mut ca ca0 [] [] j V Hca0k Hne).
        apply arg_q_sub_unmq. exact Hrel. }
  assert (Hl0 : length ca0 = n).
  { unfold ca0. rewrite update_length. exact Hlca. }
  pose proof (Hadm (map unmq ka) ca0 (length_map _ _) Hl0 H0 []) as H'.
  rewrite Hta' in H'.
  assert (Hy : nth_error (map (dyn Mut ca0 [] (map unmq ka)) args') j =
               Some (RClass Mut Cj aj)).
  { rewrite nth_error_map. rewrite Hj. simpl. rewrite Hca0j. reflexivity. }
  pose proof (Forall2_nth _ _ _ _ _ H' j _ _ Hca0j Hy) as Hr.
  inversion Hr; subst. destruct Hq as [Hq | [Hq _]]; discriminate.
Qed.

(* ------------------A RECEIVER ARGUMENT UNDER A QUALIFIER PARAMETER------------------*)

Lemma find_pair : forall (f : qualified_type -> qualified_type -> bool) Vs args1,
  (exists i V a, nth_error Vs i = Some V /\ nth_error args1 i = Some a /\
                 f V a = true) \/
  (forall i V a, nth_error Vs i = Some V -> nth_error args1 i = Some a ->
                 f V a = false).
Proof.
  intros f Vs. induction Vs as [|V Vs IH]; intros args1.
  - right. intros [|i] V a H; discriminate.
  - destruct args1 as [|a args1].
    + right. intros [|i] V0 a0 _ H; discriminate.
    + destruct (f V a) eqn:E.
      * left. exists 0, V, a. auto.
      * destruct (IH args1) as [(i & V0 & a0 & H1 & H2 & H3) | Hnone].
        -- left. exists (S i), V0, a0. auto.
        -- right. intros [|i] V0 a0 H1 H2; simpl in *.
           ++ inversion H1; inversion H2; subst. exact E.
           ++ eauto.
Qed.

(** The overridden receiver writes, under the qualifier parameter [m], a
    parameter that receives the overriding class's [j]-th parameter
    unchanged. *)
Definition is_psrc (m j : nat) (V a : qualified_type) : bool :=
  match V, a with
  | TVar TVSub ClassVar k, TVar (TVPoly m') _ _ => Nat.eqb k j && Nat.eqb m' m
  | _, _ => false
  end.

Lemma is_psrc_true : forall m j V a,
  is_psrc m j V a = true ->
  V = TVar TVSub ClassVar j /\ exists o i, a = TVar (TVPoly m) o i.
Proof.
  intros m j V a H.
  destruct V as [q0 C l | u o k | n C l]; simpl in H; try discriminate.
  destruct u; try discriminate. destruct o; try discriminate.
  destruct a as [q1 C1 l1 | u1 o1 i | n1 C1 l1]; try discriminate.
  destruct u1 as [|q1|m1]; try discriminate.
  apply andb_true_iff in H. destruct H as [H1 H2].
  apply Nat.eqb_eq in H1. apply Nat.eqb_eq in H2. subst. eauto.
Qed.

(** The overridden receiver writes such a parameter with a qualifier that is
    mutable on this object. *)
Definition is_qsrc (qr : q) (j : nat) (V a : qualified_type) : bool :=
  match V, a with
  | TVar TVSub ClassVar k, TVar (TVQual u) _ _ =>
      if q_eq_dec (dynq qr u) Mut then Nat.eqb k j else false
  | _, _ => false
  end.

Lemma is_qsrc_true : forall qr j V a,
  is_qsrc qr j V a = true ->
  V = TVar TVSub ClassVar j /\ exists u o i, a = TVar (TVQual u) o i /\ dynq qr u = Mut.
Proof.
  intros qr j V a H.
  destruct V as [q0 C l | u o k | n C l]; simpl in H; try discriminate.
  destruct u; try discriminate. destruct o; try discriminate.
  destruct a as [q1 C1 l1 | u1 o1 i | n1 C1 l1]; try discriminate.
  destruct u1 as [|q1|m1]; try discriminate.
  destruct (q_eq_dec (dynq qr q1) Mut) as [E|]; [|discriminate].
  apply Nat.eqb_eq in H. subst. eauto 6.
Qed.

Lemma qnth_nth_error : forall l n,
  qnth l n = match nth_error l n with Some x => x | None => RO end.
Proof.
  unfold qnth. induction l as [|x l IH]; intros [|n]; simpl; auto.
Qed.

Lemma qnth_lt : forall l n, qnth l n <> RO -> n < length l.
Proof.
  intros l n H. rewrite qnth_nth_error in H.
  destruct (nth_error l n) eqn:E; [|congruence].
  apply nth_error_Some. congruence.
Qed.

Lemma qnth_update_same : forall l n v, n < length l -> qnth (update n v l) n = v.
Proof.
  intros l n v H. rewrite qnth_nth_error. rewrite update_same; auto.
Qed.

Lemma qnth_update_diff : forall l n k v, n <> k -> qnth (update n v l) k = qnth l k.
Proof.
  intros l n k v H. rewrite !qnth_nth_error. rewrite update_diff; auto.
Qed.

(** If an override writes its class's [j]-th parameter under a qualifier
    parameter, the stored argument is mutable and the call supplies a mutable
    qualifier for that parameter, then the overridden receiver constrains the
    same stored argument: under the same qualifier parameter, or with a
    written qualifier that is mutable on this object. *)
Lemma recv_poly_source : forall qr n n1 Vs args1 args' ca ka j m Cj aj R1 R',
  targs R1 = args1 -> targs R' = args' ->
  recv_args n1 args1 -> recv_args n args' ->
  length Vs = n1 -> length ca = n ->
  (forall ka0 ca0, length ka0 = length ka -> length ca0 = n ->
     radmit qr (map (dyn qr ca0 [] []) Vs) ka0 R1 -> radmit qr ca0 ka0 R') ->
  radmit qr (map (dyn qr ca [] []) Vs) ka R1 ->
  nth_error args' j = Some (TVar (TVPoly m) ClassVar j) ->
  nth_error ca j = Some (RClass Mut Cj aj) ->
  qnth ka m = Mut ->
  (exists i, nth_error Vs i = Some (TVar TVSub ClassVar j) /\
             nth_error args1 i = Some (TVar (TVPoly m) ClassVar i)) \/
  (exists i u, nth_error Vs i = Some (TVar TVSub ClassVar j) /\
               nth_error args1 i = Some (TVar (TVQual u) ClassVar i) /\
               dynq qr u = Mut).
Proof.
  intros qr n n1 Vs args1 args' ca ka j m Cj aj R1 R' Hta1 Hta' [Hl1 Hsh1] [Hl' Hsh']
    HlV Hlca Hadm Hact Hj Hcaj Hkm.
  destruct (find_pair (is_psrc m j) Vs args1) as [(i & V & a & HV & Ha & Hs) | Hnp].
  { left. destruct (is_psrc_true _ _ _ _ Hs) as [-> (o & i' & ->)].
    destruct (Hsh1 i _ Ha) as [u E]. inversion E; subst. eauto. }
  destruct (find_pair (is_qsrc qr j) Vs args1) as [(i & V & a & HV & Ha & Hs) | Hnq].
  { right. destruct (is_qsrc_true _ _ _ _ Hs) as [-> (u0 & o & i' & -> & Hd)].
    destruct (Hsh1 i _ Ha) as [u E]. inversion E; subst. eauto. }
  exfalso.
  set (ca0 := update j (RClass Imm Cj aj) ca).
  set (ka0 := update m Mut (map unmq ka)).
  assert (Hjlt : j < length ca).
  { apply nth_error_Some. rewrite Hcaj. discriminate. }
  assert (Hca0j : nth_error ca0 j = Some (RClass Imm Cj aj)).
  { unfold ca0. apply update_same. exact Hjlt. }
  assert (Hca0k : forall k, k <> j -> nth_error ca0 k = nth_error ca k).
  { intros k Hk. unfold ca0. apply update_diff. auto. }
  assert (Hmlt : m < length (map unmq ka)).
  { rewrite length_map. apply qnth_lt. rewrite Hkm. discriminate. }
  assert (Hk0m : qnth ka0 m = Mut).
  { unfold ka0. apply qnth_update_same. exact Hmlt. }
  assert (Hk0k : forall k, k <> m -> qnth ka0 k = unmq (qnth ka k)).
  { intros k Hk. unfold ka0. rewrite qnth_update_diff; auto. apply qnth_map_unmq. }
  assert (H0 : radmit qr (map (dyn qr ca0 [] []) Vs) ka0 R1).
  { intros ma. rewrite Hta1. specialize (Hact ma). rewrite Hta1 in Hact.
    eapply Forall2_map2_nth; [exact Hact|].
    intros i V a HV Ha Hrel.
    destruct (Hsh1 i a Ha) as [u ->].
    destruct u as [|u|mu].
    - simpl. rewrite nth_error_map. rewrite HV. simpl. apply rarg_sub_refl.
    - simpl in Hrel. rewrite nth_error_map in Hrel. rewrite HV in Hrel.
      simpl in Hrel. apply rarg_sub_requalify_iff in Hrel.
      simpl. rewrite nth_error_map. rewrite HV. simpl.
      apply rarg_sub_requalify_iff.
      destruct (plain_dec V j) as [-> | Hne].
      + pose proof (Hnq i _ _ HV Ha) as Hf. simpl in Hf.
        destruct (q_eq_dec (dynq qr u) Mut) as [E | Hnm].
        { rewrite Nat.eqb_refl in Hf. discriminate. }
        simpl. rewrite Hca0j. simpl.
        simpl in Hrel. rewrite Hcaj in Hrel. simpl in Hrel.
        destruct Hrel as [Hx | [Hx _]]; [congruence|].
        rewrite Hx. right. split; auto.
      + rewrite (dyn_head_other qr ca ca0 [] [] j V Hca0k Hne). exact Hrel.
    - simpl in Hrel. rewrite nth_error_map in Hrel. rewrite HV in Hrel.
      simpl in Hrel. apply rarg_sub_requalify_iff in Hrel.
      simpl. rewrite nth_error_map. rewrite HV. simpl.
      apply rarg_sub_requalify_iff.
      destruct (Nat.eq_dec mu m) as [-> | Hmu].
      + rewrite Hk0m. rewrite Hkm in Hrel.
        destruct (plain_dec V j) as [-> | Hne].
        * pose proof (Hnp i _ _ HV Ha) as Hf. simpl in Hf.
          rewrite !Nat.eqb_refl in Hf. discriminate.
        * rewrite (dyn_head_other qr ca ca0 [] [] j V Hca0k Hne). exact Hrel.
      + rewrite (Hk0k mu Hmu).
        destruct (plain_dec V j) as [-> | Hne].
        * simpl. rewrite Hca0j. simpl.
          simpl in Hrel. rewrite Hcaj in Hrel. simpl in Hrel.
          apply arg_q_sub_unmq_imm. exact Hrel.
        * rewrite (dyn_head_other qr ca ca0 [] [] j V Hca0k Hne).
          apply arg_q_sub_unmq. exact Hrel. }
  assert (Hl0 : length ca0 = n).
  { unfold ca0. rewrite update_length. exact Hlca. }
  assert (Hlk0 : length ka0 = length ka).
  { unfold ka0. rewrite update_length. apply length_map. }
  pose proof (Hadm ka0 ca0 Hlk0 Hl0 H0 []) as H'. rewrite Hta' in H'.
  assert (Hy : nth_error (map (dyn qr ca0 [] ka0) args') j =
               Some (RClass (qnth ka0 m) Cj aj)).
  { rewrite nth_error_map. rewrite Hj. simpl. rewrite Hca0j. reflexivity. }
  pose proof (Forall2_nth _ _ _ _ _ H' j _ _ Hca0j Hy) as Hr.
  rewrite Hk0m in Hr.
  inversion Hr; subst. destruct Hq as [Hq | [Hq _]]; discriminate.
Qed.

Lemma existsb_combine_nth : forall (A B : Type) (f : A -> B -> bool) l l',
  existsb (fun p => f (fst p) (snd p)) (combine l l') = true <->
  exists i x y, nth_error l i = Some x /\ nth_error l' i = Some y /\ f x y = true.
Proof.
  intros A B f l. induction l as [|x l IH]; intros l'; simpl.
  - split; [discriminate | intros ([|i] & a & b & H & _); discriminate].
  - destruct l' as [|y l']; simpl.
    + split; [discriminate | intros ([|i] & a & b & _ & H & _); discriminate].
    + rewrite orb_true_iff. rewrite IH. split.
      * intros [H | (i & a & b & H1 & H2 & H3)].
        -- exists 0, x, y. repeat split; auto.
        -- exists (S i), a, b. repeat split; auto.
      * intros ([|i] & a & b & H1 & H2 & H3); simpl in *.
        -- inversion H1; inversion H2; subst. left. exact H3.
        -- right. exists i, a, b. repeat split; auto.
Qed.

(** Replace by [Imm] the head of every argument selected by [F]. *)
Fixpoint flip_from (F : nat -> bool) (k : nat) (ca : list rtype) : list rtype :=
  match ca with
  | [] => []
  | r :: ca' => (if F k then rrequalify Imm r else r) :: flip_from F (S k) ca'
  end.

Lemma nth_error_flip_from : forall F ca k i,
  nth_error (flip_from F k ca) i =
  option_map (fun r => if F (k + i) then rrequalify Imm r else r) (nth_error ca i).
Proof.
  intros F ca. induction ca as [|r ca IH]; intros k [|i]; simpl; auto.
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IH. rewrite Nat.add_succ_r. reflexivity.
Qed.

Lemma length_flip_from : forall F ca k, length (flip_from F k ca) = length ca.
Proof. intros F ca. induction ca; intros k; simpl; auto. Qed.

Lemma plainvar_dec : forall T : qualified_type,
  {k | T = TVar TVSub ClassVar k} + {forall k, T <> TVar TVSub ClassVar k}.
Proof.
  intros [q0 C a | [|q0|mp] [|] n | n C a]; try (right; intros k; discriminate).
  left. exists n. reflexivity.
Qed.

(** The head of a resolved type that is not a plain use of a class parameter
    does not depend on the heads of the class arguments. *)
Lemma dyn_head_nonplain : forall qctx F ca ma ka T,
  (forall k, T <> TVar TVSub ClassVar k) ->
  rhead (dyn qctx (flip_from F 0 ca) ma ka T) = rhead (dyn qctx ca ma ka T).
Proof.
  intros qctx F ca ma ka T HT.
  destruct T as [q0 C a | u o n | n C a]; simpl; try reflexivity.
  destruct u as [|q0|mp].
  - destruct o; simpl; [|reflexivity]. exfalso. exact (HT n eq_refl).
  - rewrite !rhead_rrequalify. reflexivity.
  - rewrite !rhead_rrequalify. reflexivity.
Qed.

(** The same situation when the overridden receiver has no such argument
    under the same qualifier parameter.  Then it puts, under that parameter,
    an argument whose head is fixed as mutable: one that is not a plain
    parameter of the overriding class, or a parameter that it also writes
    with a qualifier that is mutable on this object. *)
Lemma recv_poly_pinned : forall qr n n1 Vs args1 args' ca ka j m Cj aj R1 R',
  targs R1 = args1 -> targs R' = args' ->
  recv_args n1 args1 -> recv_args n args' ->
  length Vs = n1 -> length ca = n ->
  (forall ka0 ca0, length ka0 = length ka -> length ca0 = n ->
     radmit qr (map (dyn qr ca0 [] []) Vs) ka0 R1 -> radmit qr ca0 ka0 R') ->
  radmit qr (map (dyn qr ca [] []) Vs) ka R1 ->
  nth_error args' j = Some (TVar (TVPoly m) ClassVar j) ->
  nth_error ca j = Some (RClass Mut Cj aj) ->
  qnth ka m = Mut ->
  (forall i, nth_error Vs i = Some (TVar TVSub ClassVar j) ->
             nth_error args1 i <> Some (TVar (TVPoly m) ClassVar i)) ->
  exists i V, nth_error args1 i = Some (TVar (TVPoly m) ClassVar i) /\
    nth_error Vs i = Some V /\
    (((forall k, V <> TVar TVSub ClassVar k) /\ rhead (dyn qr ca [] [] V) = Mut) \/
     (exists j2 i2 u, V = TVar TVSub ClassVar j2 /\
        nth_error Vs i2 = Some (TVar TVSub ClassVar j2) /\
        nth_error args1 i2 = Some (TVar (TVQual u) ClassVar i2) /\
        dynq qr u = Mut)).
Proof.
  intros qr n n1 Vs args1 args' ca ka j m Cj aj R1 R' Hta1 Hta' [Hl1 Hsh1] [Hl' Hsh']
    HlV Hlca Hadm Hact Hj Hcaj Hkm Hnosrc.
  set (qsrcb := fun j2 =>
         existsb (fun p => is_qsrc qr j2 (fst p) (snd p)) (combine Vs args1)).
  set (bad := fun V a =>
         match a with
         | TVar (TVPoly m') _ _ =>
             Nat.eqb m' m &&
             match plainvar_dec V with
             | inleft (exist _ j2 _) => qsrcb j2
             | inright _ =>
                 if q_eq_dec (rhead (dyn qr ca [] [] V)) Mut then true else false
             end
         | _ => false
         end).
  destruct (find_pair bad Vs args1) as [(i & V & a & HV & Ha & Hb) | Hnone].
  { destruct (Hsh1 i a Ha) as [u ->].
    destruct u as [|u|mu]; unfold bad in Hb; simpl in Hb; try discriminate.
    apply andb_true_iff in Hb. destruct Hb as [Hm Hb].
    apply Nat.eqb_eq in Hm. subst mu.
    exists i, V. split; [exact Ha|]. split; [exact HV|].
    destruct (plainvar_dec V) as [[j2 ->] | Hnp].
    - right. unfold qsrcb in Hb. apply existsb_combine_nth in Hb.
      destruct Hb as (i2 & V2 & a2 & H1 & H2 & H3).
      destruct (is_qsrc_true _ _ _ _ H3) as [-> (u0 & o & i' & -> & Hd)].
      destruct (Hsh1 i2 _ H2) as [u E]. inversion E; subst.
      exists j2, i2, u0. auto.
    - left. split; [exact Hnp|].
      destruct (q_eq_dec (rhead (dyn qr ca [] [] V)) Mut); [assumption | discriminate]. }
  exfalso.
  set (F := fun j2 =>
         existsb (fun p => is_psrc m j2 (fst p) (snd p)) (combine Vs args1)).
  set (ca0 := flip_from F 0 ca).
  set (ka0 := update m Imm (map unmq ka)).
  assert (HFsrc : forall j2, F j2 = true ->
            exists i', nth_error Vs i' = Some (TVar TVSub ClassVar j2) /\
                       nth_error args1 i' = Some (TVar (TVPoly m) ClassVar i')).
  { intros j2 HF. unfold F in HF. apply existsb_combine_nth in HF.
    destruct HF as (i' & V' & a' & H1 & H2 & H3).
    destruct (is_psrc_true _ _ _ _ H3) as [-> (o & k & ->)].
    destruct (Hsh1 i' _ H2) as [u E]. inversion E; subst. eauto. }
  assert (HFmut : forall j2, F j2 = true ->
            rhead (dyn qr ca [] [] (TVar TVSub ClassVar j2)) = Mut).
  { intros j2 HF. destruct (HFsrc j2 HF) as (i' & HV' & Ha').
    pose proof (Hact []) as Ha0. rewrite Hta1 in Ha0.
    assert (Hx : nth_error (map (dyn qr ca [] []) Vs) i' =
                 Some (dyn qr ca [] [] (TVar TVSub ClassVar j2))).
    { rewrite nth_error_map. rewrite HV'. reflexivity. }
    assert (Hy : nth_error (map (dyn qr (map (dyn qr ca [] []) Vs) [] ka) args1) i' =
                 Some (rrequalify (qnth ka m)
                         (dyn qr ca [] [] (TVar TVSub ClassVar j2)))).
    { rewrite nth_error_map. rewrite Ha'. simpl. rewrite nth_error_map.
      rewrite HV'. reflexivity. }
    pose proof (Forall2_nth _ _ _ _ _ Ha0 i' _ _ Hx Hy) as Hr.
    apply rarg_sub_requalify_iff in Hr. rewrite Hkm in Hr.
    destruct Hr as [Hr | [Hr _]]; [symmetry; exact Hr | discriminate]. }
  assert (HnF : F j = false).
  { destruct (F j) eqn:E; auto. destruct (HFsrc j E) as (i' & H1 & H2).
    exfalso. exact (Hnosrc i' H1 H2). }
  assert (Hca0 : forall k, nth_error ca0 k =
            option_map (fun r => if F k then rrequalify Imm r else r) (nth_error ca k)).
  { intros k. unfold ca0. rewrite nth_error_flip_from. reflexivity. }
  assert (Hflip : forall j2, F j2 = true ->
            rhead (dyn qr ca0 [] [] (TVar TVSub ClassVar j2)) = Imm).
  { intros j2 HF. pose proof (HFmut j2 HF) as Hm. simpl in Hm. simpl.
    rewrite (Hca0 j2). destruct (nth_error ca j2) as [r|]; simpl.
    - rewrite HF. apply rhead_rrequalify.
    - simpl in Hm. discriminate. }
  assert (Hkeep : forall j2, F j2 = false ->
            rhead (dyn qr ca0 [] [] (TVar TVSub ClassVar j2)) =
            rhead (dyn qr ca [] [] (TVar TVSub ClassVar j2))).
  { intros j2 HF. simpl. rewrite (Hca0 j2).
    destruct (nth_error ca j2) as [r|]; simpl; [rewrite HF|]; reflexivity. }
  assert (Hmlt : m < length (map unmq ka)).
  { rewrite length_map. apply qnth_lt. rewrite Hkm. discriminate. }
  assert (Hk0m : qnth ka0 m = Imm).
  { unfold ka0. apply qnth_update_same. exact Hmlt. }
  assert (Hk0k : forall k, k <> m -> qnth ka0 k = unmq (qnth ka k)).
  { intros k Hk. unfold ka0. rewrite qnth_update_diff; auto. apply qnth_map_unmq. }
  assert (H0 : radmit qr (map (dyn qr ca0 [] []) Vs) ka0 R1).
  { intros ma. rewrite Hta1. specialize (Hact ma). rewrite Hta1 in Hact.
    eapply Forall2_map2_nth; [exact Hact|].
    intros i V a HV Ha Hrel.
    destruct (Hsh1 i a Ha) as [u ->].
    destruct u as [|u|mu].
    - simpl. rewrite nth_error_map. rewrite HV. simpl. apply rarg_sub_refl.
    - simpl in Hrel. rewrite nth_error_map in Hrel. rewrite HV in Hrel.
      simpl in Hrel. apply rarg_sub_requalify_iff in Hrel.
      simpl. rewrite nth_error_map. rewrite HV. simpl.
      apply rarg_sub_requalify_iff.
      destruct (plainvar_dec V) as [[j2 ->] | Hnp].
      + destruct (F j2) eqn:EF.
        * rewrite (Hflip j2 EF). rewrite (HFmut j2 EF) in Hrel.
          destruct Hrel as [Hx | [Hx _]].
          -- exfalso. destruct (HFsrc j2 EF) as (i' & HV' & Ha').
             pose proof (Hnone i' _ _ HV' Ha') as Hb. unfold bad in Hb. simpl in Hb.
             rewrite Nat.eqb_refl in Hb. simpl in Hb.
             destruct (plainvar_dec (TVar TVSub ClassVar j2)) as [[k E] | Hn];
               [|exact (Hn j2 eq_refl)].
             inversion E; subst k.
             assert (Hq : qsrcb j2 = true).
             { unfold qsrcb. apply existsb_combine_nth.
               exists i, (TVar TVSub ClassVar j2), (TVar (TVQual u) ClassVar i).
               repeat split; auto. simpl.
               destruct (q_eq_dec (dynq qr u) Mut); [apply Nat.eqb_refl | congruence]. }
             congruence.
          -- rewrite Hx. right. split; auto.
        * rewrite (Hkeep j2 EF). exact Hrel.
      + unfold ca0. rewrite dyn_head_nonplain; auto.
    - simpl in Hrel. rewrite nth_error_map in Hrel. rewrite HV in Hrel.
      simpl in Hrel. apply rarg_sub_requalify_iff in Hrel.
      simpl. rewrite nth_error_map. rewrite HV. simpl.
      apply rarg_sub_requalify_iff.
      destruct (Nat.eq_dec mu m) as [-> | Hmu].
      + rewrite Hk0m. rewrite Hkm in Hrel.
        destruct (plainvar_dec V) as [[j2 ->] | Hnp].
        * assert (EF : F j2 = true).
          { unfold F. apply existsb_combine_nth.
            exists i, (TVar TVSub ClassVar j2), (TVar (TVPoly m) ClassVar i).
            repeat split; auto. simpl. rewrite !Nat.eqb_refl. reflexivity. }
          rewrite (Hflip j2 EF). left. reflexivity.
        * exfalso. pose proof (Hnone i _ _ HV Ha) as Hb. unfold bad in Hb. simpl in Hb.
          rewrite Nat.eqb_refl in Hb. simpl in Hb.
          destruct (plainvar_dec V) as [[k E] | _]; [exact (Hnp k E)|].
          destruct (q_eq_dec (rhead (dyn qr ca [] [] V)) Mut) as [|Hne];
            [discriminate|].
          apply Hne. destruct Hrel as [Hx | [Hx _]]; [symmetry; exact Hx | discriminate].
      + rewrite (Hk0k mu Hmu).
        destruct (plainvar_dec V) as [[j2 ->] | Hnp].
        * destruct (F j2) eqn:EF.
          -- rewrite (Hflip j2 EF). rewrite (HFmut j2 EF) in Hrel.
             apply arg_q_sub_unmq_imm. exact Hrel.
          -- rewrite (Hkeep j2 EF). apply arg_q_sub_unmq. exact Hrel.
        * unfold ca0. rewrite dyn_head_nonplain; auto.
          apply arg_q_sub_unmq. exact Hrel. }
  assert (Hl0 : length ca0 = n).
  { unfold ca0. rewrite length_flip_from. exact Hlca. }
  assert (Hlk0 : length ka0 = length ka).
  { unfold ka0. rewrite update_length. apply length_map. }
  pose proof (Hadm ka0 ca0 Hlk0 Hl0 H0 []) as H'. rewrite Hta' in H'.
  assert (Hca0j : nth_error ca0 j = Some (RClass Mut Cj aj)).
  { rewrite Hca0. rewrite Hcaj. simpl. rewrite HnF. reflexivity. }
  assert (Hy : nth_error (map (dyn qr ca0 [] ka0) args') j =
               Some (RClass (qnth ka0 m) Cj aj)).
  { rewrite nth_error_map. rewrite Hj. simpl. rewrite Hca0j. reflexivity. }
  pose proof (Forall2_nth _ _ _ _ _ H' j _ _ Hca0j Hy) as Hr.
  rewrite Hk0m in Hr.
  inversion Hr; subst. destruct Hq as [Hq | [Hq _]]; discriminate.
Qed.

(* ------------------THE VIEW OF A PLAIN PARAMETER------------------*)

Lemma subst_adapt_plain : forall mt qh Ts S j,
  subst Ts [] [] (adapt mt qh S) = TVar TVSub ClassVar j ->
  exists m, S = TVar TVSub ClassVar m /\
            nth_error Ts m = Some (TVar TVSub ClassVar j).
Proof.
  intros mt qh Ts S j H.
  destruct S as [q0 C a | u o n | n C a]; unfold adapt in H; simpl in H;
    try discriminate.
  - destruct u as [|q0|mp]; simpl in H.
    + destruct o; simpl in H.
      * destruct (nth_error Ts n) as [U|] eqn:E; [|discriminate].
        subst U. eauto.
      * destruct n; discriminate.
    + destruct (match tv_lookup o Ts [] n with
                | Some U => U | None => default_type end); discriminate.
    + replace (nth_error (@nil qarg) mp) with (@None qarg) in H
        by (destruct mp; reflexivity).
      simpl in H.
      destruct (match tv_lookup o Ts [] n with
                | Some U => U | None => default_type end); discriminate.
  - destruct n; discriminate.
Qed.

(** A superclass parameter that receives a parameter of the subclass
    unchanged has, in every labelled view, that parameter's argument. *)
Lemma view_plain_var : forall CT mt qh C Ts D Vs,
  wf_class_table CT ->
  super_inst CT mt qh C Ts D Vs ->
  forall k hq g d As A0 lcD,
    view CT k hq g d C As D lcD ->
    (forall i j, nth_error Ts i = Some (TVar TVSub ClassVar j) ->
       exists A, nth_error As i = Some A /\ nth_error A0 j = Some A) ->
    forall i j, nth_error Vs i = Some (TVar TVSub ClassVar j) ->
      exists A, nth_error lcD i = Some A /\ nth_error A0 j = Some A.
Proof.
  intros CT mt qh C Ts D Vs Hct H.
  induction H as [C Ts | C Ts P Ss D Vs Hparent Hrest IH];
    intros k hq g d As A0 lcD Hv Hinv i j Hi.
  - assert (lcD = As).
    { symmetry. eapply view_deterministic; [exact Hct | apply v_refl | exact Hv]. }
    subst. auto.
  - inversion Hv as [| ? ? P0 Ss0 ? ? Hparent0 Hrest0]; subst.
    + exfalso.
      pose proof Hparent as Hp. unfold parent_lookup in Hp.
      destruct (find_class CT D) as [def|] eqn:Hfind; [|discriminate].
      destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hp) as (sd & Hsd & Hlt & _).
      assert (Hle : D <= P).
      { eapply base_subtype_le; [exact Hct|].
        eapply super_inst_base; [| |exact Hrest].
        - intros C0 P0 Ss0 Hp0. unfold parent_lookup in Hp0.
          destruct (find_class CT C0) as [d0|] eqn:Hf0; [|discriminate].
          destruct (wf_class_super_inv _ _ _ _ _ Hct Hf0 Hp0) as (sd0 & Hsd0 & _).
          eapply find_class_dom; eauto.
        - eapply find_class_dom; eauto. }
      simpl in Hlt. lia.
    + assert (HE : (P0, Ss0) = (P, Ss)) by congruence.
      inversion HE; subst P0 Ss0. clear HE.
      eapply IH; [exact Hrest0 | | exact Hi].
      intros i0 j0 Hi0.
      rewrite nth_error_map in Hi0. rewrite nth_error_map in Hi0.
      destruct (nth_error Ss i0) as [S|] eqn:ES; [|discriminate].
      simpl in Hi0. inversion Hi0 as [Hi1].
      destruct (subst_adapt_plain _ _ _ _ _ Hi1) as (m & -> & Hm).
      destruct (Hinv m j0 Hm) as (A & HA & HA0).
      exists A. split; [|exact HA0].
      unfold hstep. rewrite nth_error_map. rewrite ES. simpl.
      rewrite HA. reflexivity.
Qed.

(* ------------------THE VIEW OF AN ARGUMENT THAT IS NOT A PLAIN PARAMETER------------------*)

(** A labelled argument whose head, when mutable, carries the label [l]. *)
Definition ownhead (L : list nat) (l : lab) (A : ltype) : Prop :=
  match A with
  | LT q0 l0 _ _ => q0 = Mut -> norm L l0 = norm L l
  end.

(** From a class whose payloads are of the object's own label upwards, a
    superclass argument that is not one of the class's own parameters, passed
    on unchanged, is headed by the object's own label when it is mutable: its
    head was written in a class header, and the object reads every header
    through its own label. *)
Lemma oview_nonplain_own : forall CT L mt qh qo l C Ts D Vs,
  wf_class_table CT ->
  super_inst CT mt qh C Ts D Vs ->
  forall As lcD,
    oview CT qo l C As D lcD ->
    hinv CT L qo l C As -> pown CT L l C As ->
    (forall i A, nth_error As i = Some A ->
       (exists j, nth_error Ts i = Some (TVar TVSub ClassVar j)) \/ ownhead L l A) ->
    forall i A, nth_error lcD i = Some A ->
      (exists j, nth_error Vs i = Some (TVar TVSub ClassVar j)) \/ ownhead L l A.
Proof.
  intros CT L mt qh qo l C Ts D Vs Hct H.
  induction H as [C Ts | C Ts P Ss D Vs Hparent Hrest IH];
    intros As lcD Hv Hi Hk Hinv i A HA.
  - assert (lcD = As).
    { symmetry. eapply view_deterministic; [exact Hct | apply v_refl | exact Hv]. }
    subst. auto.
  - unfold oview in Hv.
    inversion Hv as [| ? ? P0 Ss0 ? ? Hparent0 Hrest0]; subst.
    + exfalso.
      pose proof Hparent as Hp. unfold parent_lookup in Hp.
      destruct (find_class CT D) as [def|] eqn:Hfind; [|discriminate].
      destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hp) as (sd & Hsd & Hlt & _).
      assert (Hle : D <= P).
      { eapply base_subtype_le; [exact Hct|].
        eapply super_inst_base; [| |exact Hrest].
        - intros C0 P0 Ss0 Hp0. unfold parent_lookup in Hp0.
          destruct (find_class CT C0) as [d0|] eqn:Hf0; [|discriminate].
          destruct (wf_class_super_inv _ _ _ _ _ Hct Hf0 Hp0) as (sd0 & Hsd0 & _).
          eapply find_class_dom; eauto.
        - eapply find_class_dom; eauto. }
      simpl in Hlt. lia.
    + assert (HE : (P0, Ss0) = (P, Ss)) by congruence.
      inversion HE; subst P0 Ss0. clear HE.
      rewrite hstep_obj in Hrest0.
      change (hframe (qr2q qo) l (pclassf CT C As) As) with (hfr CT qo l C As) in Hrest0.
      destruct (hinv_step CT L qo l C As P Ss Hct Hi Hparent) as [HiP HkP].
      pose proof (pown_hdr CT L qo l C As Hk) as Hmutl.
      eapply (IH _ lcD Hrest0 HiP (HkP Hk)); [|exact HA].
      intros i0 A0 HA0.
      rewrite nth_error_map in HA0.
      destruct (nth_error Ss i0) as [S|] eqn:ES; [|discriminate].
      simpl in HA0. inversion HA0; subst A0. clear HA0.
      rewrite !nth_error_map. rewrite ES. simpl.
      destruct S as [q0 C0 a0 | u o k | n0 C0 a0].
      * right. simpl. intros Hq.
        destruct q0; simpl in Hq; try discriminate.
        -- exact Hmutl.
        -- reflexivity.
      * destruct u as [|q0|mp].
        -- destruct o.
           ++ simpl. destruct (nth_error As k) as [A'|] eqn:EA.
              ** destruct (Hinv k A' EA) as [[j Hj] | Ho].
                 --- left. exists j. unfold adapt. simpl. rewrite Hj. reflexivity.
                 --- right. exact Ho.
              ** right. simpl. intros Hx. discriminate.
           ++ right. simpl. destruct k; simpl; intros Hx; discriminate.
        -- right. simpl.
           destruct (match tv_lookup o As [] k with Some A0 => A0 | None => ldefault end)
             as [qa la Ca Aa].
           simpl. intros Hq.
           destruct q0; simpl in Hq; try discriminate.
           ++ exact Hmutl.
           ++ reflexivity.
        -- right. simpl.
           destruct (match tv_lookup o As [] k with Some A0 => A0 | None => ldefault end)
             as [qa la Ca Aa].
           unfold lqnth. destruct mp; simpl; intros Hx; discriminate.
      * right. simpl. unfold lqnth. destruct n0; simpl; intros Hx; discriminate.
Qed.

(* ------------------ALONG THE LOOKUP CHAIN------------------*)

(** On a mutable receiver, every argument that the declared receiver [R]
    requalifies as receiver-dependent carries the receiver's own label. *)
Definition lrecv_ok (L : list nat) (qr : q_r) (c : option nat)
    (lc : list ltype) (R : qualified_type) : Prop :=
  qr = Mut_r ->
  forall j l1 C As,
    nth_error (targs R) j = Some (TVar (TVQual RDM) ClassVar j) ->
    nth_error lc j = Some (LT Mut l1 C As) ->
    norm L l1 = norm L (olab c).

Lemma nth_class_var_types : forall n i T,
  nth_error (class_var_types n) i = Some T -> T = TVar TVSub ClassVar i /\ i < n.
Proof.
  intros n i T H. unfold class_var_types in H. rewrite nth_error_map in H.
  destruct (nth_error (seq 0 n) i) as [k|] eqn:Hk; [|discriminate].
  assert (Hlt : i < length (seq 0 n)) by (apply nth_error_Some; congruence).
  rewrite length_seq in Hlt.
  apply (nth_error_nth _ _ 0) in Hk.
  assert (Hs : nth i (seq 0 n) 0 = 0 + i) by (apply seq_nth; exact Hlt).
  rewrite Hs in Hk. simpl in Hk. subst k. simpl in H. inversion H. auto.
Qed.

(** The arguments of a receiver type that has no mutable position are not
    requalified as mutable. *)
Lemma no_mut_recv_args : forall Δ R i u o n,
  no_mut Δ R ->
  nth_error (targs R) i = Some (TVar (TVQual u) o n) -> u <> Mut.
Proof.
  intros Δ R i u o n Hnm Hi.
  assert (Hall : Forall (no_mut Δ) (targs R)).
  { inversion Hnm; subst; simpl; auto; simpl in Hi; destruct i; discriminate. }
  rewrite Forall_forall in Hall.
  pose proof (Hall _ (nth_error_In _ _ Hi)) as Hx. inversion Hx; subst. assumption.
Qed.

Lemma lookup_lref_recvp : forall CT qr c Co Ro C Rs1,
  wf_class_table CT ->
  rsuper_inst CT (qr2q qr) Co Ro C Rs1 ->
  wf_rtypeuse CT (mkruntime_type qr Co Ro) ->
  forall Ao, erases Ao Ro ->
  forall mth D' mdef' D mdef ca' ca lc' lc,
    FindMethodWithName CT Co mth D' mdef' ->
    FindMethodWithName CT C mth D mdef ->
    rsuper_inst CT (qr2q qr) Co Ro D' ca' ->
    rsuper_inst CT (qr2q qr) Co Ro D ca ->
    oview CT qr (olab c) Co Ao D' lc' ->
    oview CT qr (olab c) Co Ao D lc ->
    readonly_state_method_scope (mscope (msignature mdef')) ->
    forall L ka,
      length ka = mqparams (msignature mdef) ->
      radmit (qr2q qr) ca ka (mreceiver (msignature mdef)) ->
      lrecv_ok L qr c lc (mreceiver (msignature mdef)) ->
      lrecv_ok L qr c lc' (mreceiver (msignature mdef')).
Proof.
  intros CT qr c Co Ro C Rs1 Hct H.
  remember (qr2q qr) as qo eqn:Hqo.
  induction H as [C Rs | C Rs P Ss D0 Vs Hparent Hrest IH];
    intros Hrt Ao HeA mth D' mdef' D mdef ca' ca lc' lc Hf' Hf Hs' Hs Hl' Hl
      Hrsc L ka Hk Hadm Hok.
  - destruct (find_method_with_name_deterministic _ _ _ _ _ _ _ Hf' Hf) as [-> ->].
    assert (lc' = lc) by (eapply oview_deterministic; eauto). subst lc'.
    exact Hok.
  - subst qo.
    pose proof (rsuper_inst_le _ _ _ _ _ _ Hct Hrest) as HleC.
    pose proof Hparent as Hparent'. unfold parent_lookup in Hparent'.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
    destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hparent') as (sd & _ & HltP & _).
    pose proof (base_subtype_le _ _ _ Hct (find_method_with_name_base _ _ _ _ _ Hf))
      as HleD.
    assert (HsD : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs [] []) Ss) D ca).
    { inversion Hs; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    assert (HrtP : wf_rtypeuse CT
                     (mkruntime_type qr P (map (dyn (qr2q qr) Rs [] []) Ss))).
    { eapply rsuper_wf; [exact Hct | | exact Hrt].
      eapply rsi_step; eauto. apply rsi_refl. }
    assert (HeAP : erases (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss)
                     (map (dyn (qr2q qr) Rs [] []) Ss)).
    { unfold erases. rewrite map_erase_hstep_obj. unfold erases in HeA.
      rewrite HeA. reflexivity. }
    assert (HlD : oview CT qr (olab c) P
                       (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss) D lc).
    { inversion Hl; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    inversion Hf'; subst.
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      assert (ca' = Rs).
      { eapply rsuper_inst_deterministic; [exact Hct | exact Hs' | apply rsi_refl]. }
      subst ca'.
      assert (lc' = Ao).
      { eapply oview_deterministic; [exact Hct | exact Hl' | apply v_refl]. }
      subst lc'.
      destruct (find_from_subclass _ _ _ _ _ _ Hrest _ _ _ Hf) as (D1 & mdef1 & HfP).
      destruct (find_rsuper_exists _ _ _ _ _ HfP (qr2q qr)
                  (map (dyn (qr2q qr) Rs [] []) Ss)) as [ca1 Hs1].
      destruct (oview_exists _ _ _ _ _ _ Hs1 qr (olab c) _ eq_refl HeAP)
        as (lc1 & Hl1 & He1).
      pose proof (find_method_wf _ _ _ _ _ Hct Hf') as Hwm.
      assert (HfP' : FindMethodWithName CT P (mname (msignature mdef')) D1 mdef1).
      { rewrite (gget_method_name_consistent _ _ _ Hget_method). exact HfP. }
      assert (Hs1' : rsuper_inst CT (qr2q qr) D' Rs D1 ca1)
        by (eapply rsi_step; eauto).
      destruct (override_data CT qr D' Rs def mdef' P Ss D1 mdef1 ca1
                  Hct Hrt Hfind Hparent' Hwm HfP' Hs1')
        as (Vs0 & Hag & Hsi & Hcompat & Hca1 & _).
      pose proof (lookup_refines _ _ _ _ _ _ Hct Hrest HrtP _ _ _ _ _ _ _
                    HfP Hf Hs1 HsD) as (_ & ([_ Hadmr] & _ & Hmq1) & _).
      assert (Hrsc1 : readonly_state_method_scope (mscope (msignature mdef1))).
      { destruct Hcompat as (_ & Hscope & _). rewrite <- Hscope. exact Hrsc. }
      pose proof (IH HrtP _ HeAP _ _ _ _ _ _ _ lc1 lc HfP Hf Hs1 HsD Hl1 HlD
                    Hrsc1 L ka Hk Hadm Hok) as Htop.
      pose proof (find_method_wf _ _ _ _ _ Hct HfP) as Hwm1.
      intros Hqr j l1 Cj Asj Hj HAj. subst qr.
      (* shapes and lengths *)
      destruct Hwm as ((Hsh' & _) & _).
      destruct Hsh' as (args' & Hra' & Hcase').
      assert (Hta' : targs (mreceiver (msignature mdef')) = args').
      { destruct Hcase' as [[qx Hx] | [nx Hx]]; rewrite Hx; reflexivity. }
      pose proof Hwm1 as ((Hsh1 & _) & _ & _ & _ & _ & Hroots1).
      destruct Hsh1 as (args1 & Hra1 & Hcase1).
      assert (Hta1 : targs (mreceiver (msignature mdef1)) = args1).
      { destruct Hcase1 as [[qx Hx] | [nx Hx]]; rewrite Hx; reflexivity. }
      assert (HlenRs : length Rs = length (class_tparams CT D')).
      { unfold wf_rtypeuse in Hrt. simpl in Hrt. rewrite Hfind in Hrt.
        destruct Hrt as (_ & _ & Hbnd). unfold class_tparams. rewrite Hfind.
        apply (Forall2_length Hbnd). }
      assert (HlenVs : length Vs0 = length (class_tparams CT D1)).
      { pose proof (rsuper_wf _ _ _ _ _ _ Hct Hs1' Hrt) as Hw1.
        unfold wf_rtypeuse in Hw1. simpl in Hw1. unfold class_tparams.
        destruct (find_class CT D1) as [d1|]; [|contradiction].
        destruct Hw1 as (_ & _ & Hbnd1).
        rewrite <- (Forall2_length Hbnd1). rewrite (Hca1 [] []).
        rewrite length_map. reflexivity. }
      assert (HAoj : nth_error Rs j = Some (RClass Mut Cj (map erase Asj))).
      { unfold erases in HeA. rewrite <- HeA. rewrite nth_error_map. rewrite HAj.
        reflexivity. }
      assert (Hnomut1 : forall i u,
                nth_error args1 i = Some (TVar (TVQual u) ClassVar i) -> u <> Mut).
      { intros i u Hi.
        destruct (Hroots1 Hrsc1) as [Hnm1 _].
        eapply no_mut_recv_args; [exact Hnm1|]. rewrite Hta1. exact Hi. }
      assert (Hadm1 : forall ka0 ca0, length ka0 = length ka ->
                length ca0 = length (class_tparams CT D') ->
                radmit Mut (map (dyn Mut ca0 [] []) Vs0) ka0 (mreceiver (msignature mdef1)) ->
                radmit Mut ca0 ka0 (mreceiver (msignature mdef'))).
      { intros ka0 ca0 Hlk0 Hl0 Hadm0.
        destruct Hcompat as (_ & _ & _ & _ & _ & _ & Hadmc).
        apply (Hadmc Mut_r ca0 ka0).
        - reflexivity.
        - intros Hq. rewrite Hq in Hag. simpl in Hag. discriminate.
        - simpl. exact Hl0.
        - rewrite Hlk0. rewrite Hk. symmetry. exact Hmq1.
        - exact Hadm0. }
      assert (Hact1 : radmit Mut (map (dyn Mut Rs [] []) Vs0) ka
                        (mreceiver (msignature mdef1))).
      { pose proof (Hadmr ka Hk Hadm) as Hx. rewrite (Hca1 [] []) in Hx. exact Hx. }
      assert (Hj' : nth_error args' j = Some (TVar (TVQual RDM) ClassVar j)).
      { rewrite <- Hta'. exact Hj. }
      destruct (recv_rdm_source (length (class_tparams CT D'))
                  (length (class_tparams CT D1)) Vs0 args1 args' Rs ka j Cj
                  (map erase Asj) _ _ Hta1 Hta' Hra1 Hra' HlenVs HlenRs
                  Hnomut1 Hadm1 Hact1 Hj' HAoj)
        as (i & HVi & Hai).
      (* the labelled argument is the same at the overridden class *)
      assert (Hbase : forall i0 j0,
                nth_error (class_var_types (length Rs)) i0 = Some (TVar TVSub ClassVar j0) ->
                exists A, nth_error Ao i0 = Some A /\ nth_error Ao j0 = Some A).
      { intros i0 j0 Hi0.
        destruct (nth_class_var_types _ _ _ Hi0) as [E Hlt]. inversion E; subst j0.
        assert (Hlt' : i0 < length Ao).
        { unfold erases in HeA. rewrite <- HeA in Hlt. rewrite length_map in Hlt.
          exact Hlt. }
        destruct (nth_error Ao i0) as [A|] eqn:EA.
        - exists A. auto.
        - apply nth_error_None in EA. lia. }
      destruct (view_plain_var _ _ _ _ _ _ _ Hct Hsi false Mut (fun q0 => q0)
                  (olab c) Ao Ao lc1
                  (v_step CT false Mut (fun q0 => q0) (olab c) D' Ao P Ss D1 lc1
                     Hparent Hl1) Hbase i j HVi) as (A & HA1 & HA0).
      rewrite HAj in HA0. inversion HA0; subst A.
      eapply (Htop eq_refl i); [rewrite Hta1; exact Hai | exact HA1].
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      rewrite Hsuper in Hparent'. inversion Hparent'; subst.
      pose proof (base_subtype_le _ _ _ Hct
                    (find_method_with_name_base _ _ _ _ _ Hparent_fmn)) as HleD'.
      assert (HsD' : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs [] []) Ss) D' ca').
      { inversion Hs'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      assert (HlD' : oview CT qr (olab c) P
                       (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss) D' lc').
      { inversion Hl'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      exact (IH HrtP _ HeAP _ _ _ _ _ _ _ lc' lc Hparent_fmn Hf HsD' HsD HlD' HlD
               Hrsc L ka Hk Hadm Hok).
Qed.

(* ------------------AT THE CALL------------------*)

Lemma ldyn_member_recv_args : forall F qy Vs Us Qs R,
  (exists q1 C1 a1, R = TClass q1 C1 a1) \/ (exists n1 C1 a1, R = THead n1 C1 a1) ->
  exists q2 l2 C0,
    ((exists q0, R = TClass q0 C0 (targs R)) \/ (exists n, R = THead n C0 (targs R))) /\
    ldyn F (member_recv qy Vs Us Qs R) =
    LT q2 l2 C0
      (map (fun T => ldyn F (subst Vs Us Qs (map_qual (vpa_recv qy) T))) (targs R)).
Proof.
  intros F qy Vs Us Qs R [(q1 & C1 & a1 & ->) | (n1 & C1 & a1 & ->)].
  - unfold member_recv. cbn [map_qual subst ldyn targs].
    do 3 eexists. split; [left; eexists; reflexivity|].
    rewrite !map_map. reflexivity.
  - unfold member_recv. cbn [map_qual subst targs].
    destruct (nth_error Qs n1) as [[ql | m]|]; unfold qhead; cbn [ldyn];
      do 3 eexists; (split; [right; eexists; reflexivity|]);
      rewrite !map_map; reflexivity.
Qed.

Lemma ldyn_requalify_head : forall F q0 U,
  exists C a, ldyn F (requalify q0 U) = LT (dynq (lf_q F) q0) (lab_of F q0) C a.
Proof.
  intros F q0 [q1 C a | u o n | n C a]; simpl.
  - eauto.
  - destruct (match tv_lookup o (lf_cargs F) (lf_margs F) n with
              | Some A => A | None => ldefault end) as [qa la Ca aa].
    simpl. eauto.
  - eauto.
Qed.

Lemma norm_some : forall L l w, norm L l = Some w -> l = LIn w /\ List.In w L.
Proof.
  intros L [w0|] w H; simpl in H; [|discriminate].
  destruct (in_dec Nat.eq_dec w0 L); inversion H; subst. auto.
Qed.

(** A mutable head label is the label of the object. *)
Lemma headL_norm : forall L c l,
  headL L c Mut l -> norm L l = norm L (olab c).
Proof.
  intros L c l H. specialize (H eq_refl).
  destruct (norm L l) as [w|] eqn:E.
  - subst c. destruct (norm_some _ _ _ E) as [_ Hin]. simpl.
    symmetry. apply norm_live. exact Hin.
  - destruct c as [w|]; simpl; [|reflexivity].
    symmetry. apply norm_dead. apply H. reflexivity.
Qed.

Print Assumptions lookup_lref_recvp.

(** On a receiver of either mutability, every mutable argument that the
    declared receiver [R] writes under a qualifier parameter carries the
    label of the qualifier argument, when that argument is mutable. *)
Definition lrecv_okp (L : list nat) (lk : list (q * lab)) (lc : list ltype)
    (R : qualified_type) : Prop :=
  forall j m l1 C As,
    nth_error (targs R) j = Some (TVar (TVPoly m) ClassVar j) ->
    nth_error lc j = Some (LT Mut l1 C As) ->
    fst (lqnth lk m) = Mut ->
    norm L l1 = norm L (snd (lqnth lk m)).

Lemma class_var_types_nth : forall n i,
  i < n -> nth_error (class_var_types n) i = Some (TVar TVSub ClassVar i).
Proof.
  intros n i H. unfold class_var_types. rewrite nth_error_map.
  assert (Hlt : i < length (seq 0 n)) by (rewrite length_seq; exact H).
  rewrite (nth_error_nth' (seq 0 n) 0 Hlt). rewrite seq_nth; try exact H. reflexivity.
Qed.

Lemma radmit_qual_head : forall qr ca ka R i u r,
  radmit qr ca ka R ->
  nth_error (targs R) i = Some (TVar (TVQual u) ClassVar i) ->
  nth_error ca i = Some r ->
  arg_q_sub (rhead r) (dynq qr u).
Proof.
  intros qr ca ka R i u r H HT Hr.
  assert (Hy : nth_error (map (dyn qr ca [] ka) (targs R)) i =
               Some (rrequalify (dynq qr u) r)).
  { rewrite nth_error_map. rewrite HT. simpl. rewrite Hr. reflexivity. }
  pose proof (Forall2_nth _ _ _ _ _ (H []) i _ _ Hr Hy) as Hx.
  apply rarg_sub_requalify_iff in Hx. exact Hx.
Qed.

(** The same along the lookup chain: the fact for the declaration the caller
    sees carries to the declaration that runs. *)
Lemma lookup_lref_recvq : forall CT qr c Co Ro C Rs1,
  wf_class_table CT ->
  clean_bounds_ct CT ->
  rsuper_inst CT (qr2q qr) Co Ro C Rs1 ->
  wf_rtypeuse CT (mkruntime_type qr Co Ro) ->
  forall Ao, erases Ao Ro ->
  forall mth D' mdef' D mdef ca' ca lc' lc,
    FindMethodWithName CT Co mth D' mdef' ->
    FindMethodWithName CT C mth D mdef ->
    rsuper_inst CT (qr2q qr) Co Ro D' ca' ->
    rsuper_inst CT (qr2q qr) Co Ro D ca ->
    oview CT qr (olab c) Co Ao D' lc' ->
    oview CT qr (olab c) Co Ao D lc ->
    readonly_state_method_scope (mscope (msignature mdef')) ->
    forall L lk,
      hinv CT L qr (olab c) Co Ao ->
      length lk = mqparams (msignature mdef) ->
      radmit (qr2q qr) ca (map fst lk) (mreceiver (msignature mdef)) ->
      lrecv_ok L qr c lc (mreceiver (msignature mdef)) ->
      lrecv_okp L lk lc (mreceiver (msignature mdef)) ->
      lrecv_okp L lk lc' (mreceiver (msignature mdef')).
Proof.
  intros CT qr c Co Ro C Rs1 Hct Hclean H.
  remember (qr2q qr) as qo eqn:Hqo.
  induction H as [C Rs | C Rs P Ss D0 Vs Hparent Hrest IH];
    intros Hrt Ao HeA mth D' mdef' D mdef ca' ca lc' lc Hf' Hf Hs' Hs Hl' Hl
      Hrsc L lk Hinv0 Hlk Hadm Hok Hokp.
  - destruct (find_method_with_name_deterministic _ _ _ _ _ _ _ Hf' Hf) as [-> ->].
    assert (lc' = lc) by (eapply oview_deterministic; eauto). subst lc'.
    exact Hokp.
  - subst qo.
    pose proof (rsuper_inst_le _ _ _ _ _ _ Hct Hrest) as HleC.
    pose proof Hparent as Hparent'. unfold parent_lookup in Hparent'.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
    destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hparent') as (sd & _ & HltP & _).
    pose proof (base_subtype_le _ _ _ Hct (find_method_with_name_base _ _ _ _ _ Hf))
      as HleD.
    assert (HsD : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs [] []) Ss) D ca).
    { inversion Hs; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    assert (HrtP : wf_rtypeuse CT
                     (mkruntime_type qr P (map (dyn (qr2q qr) Rs [] []) Ss))).
    { eapply rsuper_wf; [exact Hct | | exact Hrt].
      eapply rsi_step; eauto. apply rsi_refl. }
    assert (HeAP : erases (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss)
                     (map (dyn (qr2q qr) Rs [] []) Ss)).
    { unfold erases. rewrite map_erase_hstep_obj. unfold erases in HeA.
      rewrite HeA. reflexivity. }
    assert (HlD : oview CT qr (olab c) P
                       (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss) D lc).
    { inversion Hl; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    assert (Hk : length (map fst lk) = mqparams (msignature mdef)).
    { rewrite length_map. exact Hlk. }
    assert (HinvP : hinv CT L qr (olab c) P
                      (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss)).
    { rewrite hstep_obj.
      exact (proj1 (hinv_step CT L qr (olab c) C Ao P Ss Hct Hinv0 Hparent)). }
    inversion Hf'; subst.
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      assert (ca' = Rs).
      { eapply rsuper_inst_deterministic; [exact Hct | exact Hs' | apply rsi_refl]. }
      subst ca'.
      assert (lc' = Ao).
      { eapply oview_deterministic; [exact Hct | exact Hl' | apply v_refl]. }
      subst lc'.
      destruct (find_from_subclass _ _ _ _ _ _ Hrest _ _ _ Hf) as (D1 & mdef1 & HfP).
      destruct (find_rsuper_exists _ _ _ _ _ HfP (qr2q qr)
                  (map (dyn (qr2q qr) Rs [] []) Ss)) as [ca1 Hs1].
      destruct (oview_exists _ _ _ _ _ _ Hs1 qr (olab c) _ eq_refl HeAP)
        as (lc1 & Hl1 & He1).
      pose proof (find_method_wf _ _ _ _ _ Hct Hf') as Hwm.
      assert (HfP' : FindMethodWithName CT P (mname (msignature mdef')) D1 mdef1).
      { rewrite (gget_method_name_consistent _ _ _ Hget_method). exact HfP. }
      assert (Hs1' : rsuper_inst CT (qr2q qr) D' Rs D1 ca1)
        by (eapply rsi_step; eauto).
      destruct (override_data CT qr D' Rs def mdef' P Ss D1 mdef1 ca1
                  Hct Hrt Hfind Hparent' Hwm HfP' Hs1')
        as (Vs0 & Hag & Hsi & Hcompat & Hca1 & _).
      pose proof (lookup_refines _ _ _ _ _ _ Hct Hrest HrtP _ _ _ _ _ _ _
                    HfP Hf Hs1 HsD) as (_ & ([_ Hadmr] & _ & Hmq1) & _).
      assert (Hrsc1 : readonly_state_method_scope (mscope (msignature mdef1))).
      { destruct Hcompat as (_ & Hscope & _). rewrite <- Hscope. exact Hrsc. }
      pose proof (IH HrtP _ HeAP _ _ _ _ _ _ _ lc1 lc HfP Hf Hs1 HsD Hl1 HlD
                    Hrsc1 L lk HinvP Hlk Hadm Hok Hokp) as Htop.
      pose proof (lookup_lref_recvp CT qr c P _ D0 Vs Hct Hrest HrtP _ HeAP
                    _ _ _ _ _ _ _ lc1 lc HfP Hf Hs1 HsD Hl1 HlD
                    Hrsc1 L (map fst lk) Hk Hadm Hok) as Htop_r.
      pose proof (find_method_wf _ _ _ _ _ Hct HfP) as Hwm1.
      (* the class that declares the method that runs has no mutable
         position in its bounds, so the object reads every class header from
         there upwards through its own label *)
      assert (Hin' : List.In mdef' (methods (body def))).
      { eapply gget_method_In; eauto. }
      pose proof (Hclean D' def mdef' Hfind Hin' Hrsc) as Hnb.
      assert (Hpn : pclassf CT D' Ao = None).
      { apply pclassf_clean. intros d Hd. rewrite Hfind in Hd. inversion Hd; subst d.
        eapply nomut_bounds_clean; eauto. }
      assert (Hown : pown CT L (olab c) D' Ao).
      { intros q' l' Hx. rewrite Hpn in Hx. discriminate. }
      intros j m l1 Cj Asj Hj HAj Hkq.
      (* shapes and lengths *)
      destruct Hwm as ((Hsh' & _) & _).
      destruct Hsh' as (args' & Hra' & Hcase').
      assert (Hta' : targs (mreceiver (msignature mdef')) = args').
      { destruct Hcase' as [[qx Hx] | [nx Hx]]; rewrite Hx; reflexivity. }
      pose proof Hwm1 as ((Hsh1 & _) & _ & _ & _ & _ & Hroots1).
      destruct Hsh1 as (args1 & Hra1 & Hcase1).
      assert (Hta1 : targs (mreceiver (msignature mdef1)) = args1).
      { destruct Hcase1 as [[qx Hx] | [nx Hx]]; rewrite Hx; reflexivity. }
      assert (HlenRs : length Rs = length (class_tparams CT D')).
      { unfold wf_rtypeuse in Hrt. simpl in Hrt. rewrite Hfind in Hrt.
        destruct Hrt as (_ & _ & Hbnd). unfold class_tparams. rewrite Hfind.
        apply (Forall2_length Hbnd). }
      assert (HlenVs : length Vs0 = length (class_tparams CT D1)).
      { pose proof (rsuper_wf _ _ _ _ _ _ Hct Hs1' Hrt) as Hw1.
        unfold wf_rtypeuse in Hw1. simpl in Hw1. unfold class_tparams.
        destruct (find_class CT D1) as [d1|]; [|contradiction].
        destruct Hw1 as (_ & _ & Hbnd1).
        rewrite <- (Forall2_length Hbnd1). rewrite (Hca1 [] []).
        rewrite length_map. reflexivity. }
      assert (HAoj : nth_error Rs j = Some (RClass Mut Cj (map erase Asj))).
      { unfold erases in HeA. rewrite <- HeA. rewrite nth_error_map. rewrite HAj.
        reflexivity. }
      assert (Hnomut1 : forall i u,
                nth_error args1 i = Some (TVar (TVQual u) ClassVar i) -> u <> Mut).
      { intros i u Hi.
        destruct (Hroots1 Hrsc1) as [Hnm1 _].
        eapply no_mut_recv_args; [exact Hnm1|]. rewrite Hta1. exact Hi. }
      assert (Hadm1 : forall ka0 ca0, length ka0 = length (map fst lk) ->
                length ca0 = length (class_tparams CT D') ->
                radmit (qr2q qr) (map (dyn (qr2q qr) ca0 [] []) Vs0) ka0
                  (mreceiver (msignature mdef1)) ->
                radmit (qr2q qr) ca0 ka0 (mreceiver (msignature mdef'))).
      { intros ka0 ca0 Hlk0 Hl0 Hadm0.
        destruct Hcompat as (_ & _ & _ & _ & _ & _ & Hadmc).
        apply (Hadmc qr ca0 ka0).
        - intros Hq. rewrite Hq in Hag.
          destruct qr; simpl in Hag; [reflexivity | discriminate].
        - intros Hq. rewrite Hq in Hag.
          destruct qr; simpl in Hag; [discriminate | reflexivity].
        - simpl. exact Hl0.
        - rewrite Hlk0. rewrite Hk. symmetry. exact Hmq1.
        - exact Hadm0. }
      assert (Hact1' : radmit (qr2q qr) ca1 (map fst lk) (mreceiver (msignature mdef1))).
      { exact (Hadmr (map fst lk) Hk Hadm). }
      assert (Hact1 : radmit (qr2q qr) (map (dyn (qr2q qr) Rs [] []) Vs0) (map fst lk)
                        (mreceiver (msignature mdef1))).
      { pose proof Hact1' as Hx. rewrite (Hca1 [] []) in Hx. exact Hx. }
      assert (Hj' : nth_error args' j = Some (TVar (TVPoly m) ClassVar j)).
      { rewrite <- Hta'. exact Hj. }
      assert (Hkm : qnth (map fst lk) m = Mut).
      { rewrite qnth_map_fst. exact Hkq. }
      assert (Hbase : forall i0 j0,
                nth_error (class_var_types (length Rs)) i0 = Some (TVar TVSub ClassVar j0) ->
                exists A, nth_error Ao i0 = Some A /\ nth_error Ao j0 = Some A).
      { intros i0 j0 Hi0.
        destruct (nth_class_var_types _ _ _ Hi0) as [E Hlt]. inversion E; subst j0.
        assert (Hlt' : i0 < length Ao).
        { unfold erases in HeA. rewrite <- HeA in Hlt. rewrite length_map in Hlt.
          exact Hlt. }
        destruct (nth_error Ao i0) as [A|] eqn:EA.
        - exists A. auto.
        - apply nth_error_None in EA. lia. }
      assert (Hview1 : view CT false (qr2q qr) (fun q0 => q0) (olab c) D' Ao D1 lc1).
      { eapply v_step; [exact Hparent | exact Hl1]. }
      pose proof Hra1 as [_ Hshp1].
      destruct (find_pair (is_psrc m j) Vs0 args1) as [(i & V & a & HV & Ha & Hsb) | Hnp].
      { (* the overridden receiver writes the same stored argument under the
           same qualifier parameter *)
        destruct (is_psrc_true _ _ _ _ Hsb) as [-> (o & i' & ->)].
        destruct (Hshp1 i _ Ha) as [u E]. injection E as Eu Eo Ei. subst u o i'.
        destruct (view_plain_var _ _ _ _ _ _ _ Hct Hsi false (qr2q qr) (fun q0 => q0)
                    (olab c) Ao Ao lc1 Hview1 Hbase i j HV) as (A & HA1 & HA0).
        rewrite HAj in HA0. inversion HA0; subst A.
        eapply (Htop i m l1); [rewrite Hta1; exact Ha | exact HA1 | exact Hkq]. }
      assert (Hnosrc : forall i, nth_error Vs0 i = Some (TVar TVSub ClassVar j) ->
                nth_error args1 i <> Some (TVar (TVPoly m) ClassVar i)).
      { intros i HV Ha. pose proof (Hnp i _ _ HV Ha) as Hfx. simpl in Hfx.
        rewrite !Nat.eqb_refl in Hfx. discriminate. }
      destruct (recv_poly_source (qr2q qr) (length (class_tparams CT D'))
                  (length (class_tparams CT D1)) Vs0 args1 args' Rs (map fst lk) j m Cj
                  (map erase Asj) _ _ Hta1 Hta' Hra1 Hra' HlenVs HlenRs
                  Hadm1 Hact1 Hj' HAoj Hkm)
        as [(i & HVi & Hai) | (i & u & HVi & Hai & Hdu)].
      { exfalso. exact (Hnosrc i HVi Hai). }
      (* the stored argument is written receiver-dependent by the overridden
         receiver, on a mutable object: it carries the object's own label *)
      assert (Hu : u = RDM /\ qr = Mut_r).
      { pose proof (Hnomut1 i u Hai) as Hne.
        destruct u; simpl in Hdu; try discriminate; try congruence.
        destruct qr; simpl in Hdu; try discriminate. auto. }
      destruct Hu as [-> Hqr].
      assert (Hl1c : norm L l1 = norm L (olab c)).
      { destruct (view_plain_var _ _ _ _ _ _ _ Hct Hsi false (qr2q qr) (fun q0 => q0)
                    (olab c) Ao Ao lc1 Hview1 Hbase i j HVi) as (A & HA1 & HA0).
        rewrite HAj in HA0. inversion HA0; subst A.
        eapply (Htop_r Hqr i); [rewrite Hta1; exact Hai | exact HA1]. }
      destruct (recv_poly_pinned (qr2q qr) (length (class_tparams CT D'))
                  (length (class_tparams CT D1)) Vs0 args1 args' Rs (map fst lk) j m Cj
                  (map erase Asj) _ _ Hta1 Hta' Hra1 Hra' HlenVs HlenRs
                  Hadm1 Hact1 Hj' HAoj Hkm Hnosrc)
        as (i3 & V3 & Ha3 & HV3 &
            [[Hnp3 Hh3] | (j2 & i2 & u2 & -> & HV2 & Ha2 & Hd2)]).
      * (* under the same parameter the overridden receiver has an argument
           that is not a plain parameter of this class and is mutable: its
           label is the object's own, and the label of the qualifier
           argument *)
        assert (HA3 : exists A3, nth_error lc1 i3 = Some A3 /\
                                 erase A3 = dyn (qr2q qr) Rs [] [] V3).
        { assert (Hc1 : nth_error ca1 i3 = Some (dyn (qr2q qr) Rs [] [] V3)).
          { rewrite (Hca1 [] []). rewrite nth_error_map. rewrite HV3. reflexivity. }
          rewrite <- He1 in Hc1. rewrite nth_error_map in Hc1.
          destruct (nth_error lc1 i3) as [A3|]; [|discriminate].
          inversion Hc1. eauto. }
        destruct HA3 as (A3 & HA3 & HeA3).
        destruct A3 as [q3 l3 C3 As3]. simpl in HeA3. rewrite <- HeA3 in Hh3.
        simpl in Hh3. subst q3.
        assert (Hl3k : norm L l3 = norm L (snd (lqnth lk m))).
        { eapply (Htop i3 m l3); [rewrite Hta1; exact Ha3 | exact HA3 | exact Hkq]. }
        assert (Hl3c : norm L l3 = norm L (olab c)).
        { assert (HbaseN : forall i0 A, nth_error Ao i0 = Some A ->
                    (exists j0, nth_error (class_var_types (length Rs)) i0 =
                                Some (TVar TVSub ClassVar j0)) \/
                    ownhead L (olab c) A).
          { intros i0 A HA. left. exists i0. apply class_var_types_nth.
            unfold erases in HeA. rewrite <- HeA. rewrite length_map.
            apply nth_error_Some. congruence. }
          destruct (oview_nonplain_own CT L AbstractState _ qr (olab c) D' _ D1 Vs0
                      Hct Hsi Ao lc1 Hview1 Hinv0 Hown HbaseN i3 _ HA3)
            as [[j3 Hj3] | Ho].
          - exfalso. rewrite HV3 in Hj3. inversion Hj3 as [E3]. exact (Hnp3 j3 E3).
          - simpl in Ho. exact (Ho eq_refl). }
        rewrite Hl1c. rewrite <- Hl3c. exact Hl3k.
      * (* under the same parameter the overridden receiver has a parameter
           of this class that it also writes receiver-dependent *)
        destruct (view_plain_var _ _ _ _ _ _ _ Hct Hsi false (qr2q qr) (fun q0 => q0)
                    (olab c) Ao Ao lc1 Hview1 Hbase i3 j2 HV3) as (A & HA1 & HA0).
        destruct (view_plain_var _ _ _ _ _ _ _ Hct Hsi false (qr2q qr) (fun q0 => q0)
                    (olab c) Ao Ao lc1 Hview1 Hbase i2 j2 HV2) as (A' & HA1' & HA0').
        rewrite HA0 in HA0'. inversion HA0'; subst A'.
        destruct A as [qA lA CA AsA].
        assert (Hu2 : u2 = RDM).
        { pose proof (Hnomut1 i2 u2 Ha2) as Hne. subst qr.
          destruct u2; simpl in Hd2; try discriminate; try congruence. }
        subst u2.
        assert (HqA : qA = Mut).
        { assert (Hc : nth_error ca1 i2 = Some (erase (LT qA lA CA AsA))).
          { rewrite <- He1. rewrite nth_error_map. rewrite HA1'. reflexivity. }
          assert (HT2 : nth_error (targs (mreceiver (msignature mdef1))) i2 =
                        Some (TVar (TVQual RDM) ClassVar i2)).
          { rewrite Hta1. exact Ha2. }
          pose proof (radmit_qual_head _ _ _ _ _ _ _ Hact1' HT2 Hc) as Hx.
          rewrite Hqr in Hx. simpl in Hx.
          destruct Hx as [Hx | [Hx _]]; [symmetry; exact Hx | discriminate]. }
        subst qA.
        assert (HlAk : norm L lA = norm L (snd (lqnth lk m))).
        { eapply (Htop i3 m lA); [rewrite Hta1; exact Ha3 | exact HA1 | exact Hkq]. }
        assert (HlAc : norm L lA = norm L (olab c)).
        { eapply (Htop_r Hqr i2); [rewrite Hta1; exact Ha2 | exact HA1']. }
        rewrite Hl1c. rewrite <- HlAc. exact HlAk.
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      rewrite Hsuper in Hparent'. inversion Hparent'; subst.
      pose proof (base_subtype_le _ _ _ Hct
                    (find_method_with_name_base _ _ _ _ _ Hparent_fmn)) as HleD'.
      assert (HsD' : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs [] []) Ss) D' ca').
      { inversion Hs'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      assert (HlD' : oview CT qr (olab c) P
                       (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss) D' lc').
      { inversion Hl'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      exact (IH HrtP _ HeAP _ _ _ _ _ _ _ lc' lc Hparent_fmn Hf HsD' HsD HlD' HlD
               Hrsc L lk HinvP Hlk Hadm Hok Hokp).
Qed.

Print Assumptions lookup_lref_recvq.
