From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require String.
Require Import Stdlib.Sets.Ensembles.
Require Import Stdlib.Classes.RelationClasses.
Import ListNotations.
Require Import Syntax Typing Subtyping ViewpointAdaptation Helpers.

Inductive reachable (h : heap) : Loc -> Loc -> Prop :=

  | rch_heap : forall l
      (Hdom : l < dom h),
      reachable h l l

  | rch_step : forall l0 l1 obj f
      (Hdom    : l1 < dom h)
      (Hobj    : runtime_getObj h l0 = Some obj)
      (Hfield  : getVal obj.(fields_map) f = Some (Iot l1)),
      reachable h l0 l1

  | rch_trans : forall l0 l1 l2
      (Hreach1 : reachable h l0 l1)
      (Hreach2 : reachable h l1 l2),
      reachable h l0 l2.

(** A single heap edge, factored out of [reachable] for constructive search. *)
Definition heap_edge (h : heap) (l0 l1 : Loc) : Prop :=
  exists obj f,
    runtime_getObj h l0 = Some obj /\
    getVal obj.(fields_map) f = Some (Iot l1) /\
    l1 < dom h.

Lemma heap_edge_reachable : forall h l0 l1,
  heap_edge h l0 l1 -> reachable h l0 l1.
Proof.
  intros h l0 l1 [obj [f [Hobj [Hfield Hdom]]]].
  eapply rch_step; eauto.
Qed.

Lemma heap_edge_target_dom : forall h l0 l1,
  heap_edge h l0 l1 -> l1 < dom h.
Proof.
  intros h l0 l1 [_ [_ [_ [_ Hdom]]]]. exact Hdom.
Qed.

Lemma reachable_source_dom : forall h l0 l1,
  reachable h l0 l1 -> l0 < dom h.
Proof.
  intros h l0 l1 Hreach.
  induction Hreach.
  - exact Hdom.
  - apply runtime_getObj_dom in Hobj. exact Hobj.
  - exact IHHreach1.
Qed.

Lemma reachable_target_dom : forall h l0 l1,
  reachable h l0 l1 -> l1 < dom h.
Proof.
  intros h l0 l1 Hreach.
  induction Hreach.
  - exact Hdom.
  - exact Hdom.
  - exact IHHreach2.
Qed.

Inductive edge_path (h : heap) : Loc -> Loc -> list Loc -> Prop :=
  | edge_path_nil : forall l,
      edge_path h l l []
  | edge_path_cons : forall l0 l1 l2 nodes,
      heap_edge h l0 l1 ->
      edge_path h l1 l2 nodes ->
      edge_path h l0 l2 (l1 :: nodes).

Lemma edge_path_app : forall h l0 l1 l2 nodes1 nodes2,
  edge_path h l0 l1 nodes1 ->
  edge_path h l1 l2 nodes2 ->
  edge_path h l0 l2 (nodes1 ++ nodes2).
Proof.
  intros h l0 l1 l2 nodes1 nodes2 Hpath1 Hpath2.
  induction Hpath1.
  - simpl. exact Hpath2.
  - simpl. econstructor; eauto.
Qed.

Lemma edge_path_tail : forall h l0 l1 next nodes,
  edge_path h l0 l1 (next :: nodes) ->
  edge_path h next l1 nodes.
Proof.
  intros h l0 l1 next nodes Hpath.
  inversion Hpath; subst. assumption.
Qed.

Lemma reachable_edge_path : forall h l0 l1,
  reachable h l0 l1 -> exists nodes, edge_path h l0 l1 nodes.
Proof.
  intros h l0 l1 Hreach.
  induction Hreach.
  - exists ([] : list Loc). constructor.
  - exists [l1]. econstructor.
    + exists obj, f. repeat split; assumption.
    + constructor.
  - destruct IHHreach1 as [nodes1 Hpath1].
    destruct IHHreach2 as [nodes2 Hpath2].
    exists (nodes1 ++ nodes2).
    eapply edge_path_app; eauto.
Qed.

Lemma edge_path_suffix : forall h l0 l1 nodes prefix middle suffix,
  edge_path h l0 l1 nodes ->
  l0 :: nodes = prefix ++ middle :: suffix ->
  edge_path h middle l1 suffix.
Proof.
  intros h l0 l1 nodes prefix.
  generalize dependent l0.
  generalize dependent nodes.
  induction prefix as [|p prefix IH]; intros nodes l0 middle suffix Hpath Heq.
  - simpl in Heq. injection Heq as Hl0 Hnodes. subst middle nodes. exact Hpath.
  - simpl in Heq. injection Heq as Hl0 Hnodes. subst p.
    subst nodes.
    destruct (prefix ++ middle :: suffix) as [|next tail] eqn:Hlist.
    { exfalso.
      apply (f_equal (@List.length Loc)) in Hlist.
      rewrite List.length_app in Hlist. simpl in Hlist. lia. }
    have Htailpath := edge_path_tail h l0 l1 next tail Hpath.
    eapply IH; [exact Htailpath|].
    symmetry. exact Hlist.
Qed.

Lemma edge_path_simplify : forall h l0 l1 nodes,
  edge_path h l0 l1 nodes ->
  exists nodes', edge_path h l0 l1 nodes' /\ NoDup (l0 :: nodes').
Proof.
  intros h l0 l1 nodes Hpath.
  induction Hpath.
  - exists ([] : list Loc). split; [constructor|constructor; [simpl; tauto|constructor]].
  - destruct IHHpath as [nodes' [Hpath' Hnodup]].
    destruct (in_dec Nat.eq_dec l0 (l1 :: nodes')) as [Hin|Hnotin].
    + apply in_split in Hin.
      destruct Hin as [prefix [suffix Heq]].
      exists suffix.
      split.
      * eapply edge_path_suffix; eauto.
      * rewrite Heq in Hnodup.
        eapply NoDup_app_remove_l. exact Hnodup.
    + exists (l1 :: nodes').
      split.
      * econstructor; eauto.
      * constructor; assumption.
Qed.

Lemma edge_path_nodes_dom : forall h l0 l1 nodes,
  edge_path h l0 l1 nodes ->
  l0 < dom h ->
  Forall (fun l => l < dom h) (l0 :: nodes).
Proof.
  intros h l0 l1 nodes Hpath.
  induction Hpath; intro Hdom0.
  - constructor; [exact Hdom0|constructor].
  - constructor; [exact Hdom0|].
    apply IHHpath.
    eapply heap_edge_target_dom; eauto.
Qed.

Lemma simple_edge_path_length : forall h l0 l1 nodes,
  edge_path h l0 l1 nodes ->
  NoDup (l0 :: nodes) ->
  l0 < dom h ->
  length nodes < dom h.
Proof.
  intros h l0 l1 nodes Hpath Hnodup Hdom0.
  have Hnodes_dom := edge_path_nodes_dom h l0 l1 nodes Hpath Hdom0.
  assert (Hincl : incl (l0 :: nodes) (seq 0 (dom h))).
  {
    intros l Hin.
    eapply Forall_forall in Hnodes_dom; eauto.
    apply in_seq. lia.
  }
  have Hlen := NoDup_incl_length Hnodup Hincl.
  rewrite List.length_seq in Hlen. simpl in Hlen. lia.
Qed.

Fixpoint reachable_in (h : heap) (fuel : nat) (l0 l1 : Loc) : Prop :=
  match fuel with
  | 0 => l0 = l1
  | S fuel' =>
      l0 = l1 \/
      exists next, heap_edge h l0 next /\ reachable_in h fuel' next l1
  end.

Lemma edge_path_reachable_in : forall h l0 l1 nodes fuel,
  edge_path h l0 l1 nodes ->
  length nodes <= fuel ->
  reachable_in h fuel l0 l1.
Proof.
  intros h l0 l1 nodes fuel Hpath.
  generalize dependent fuel.
  induction Hpath; intros fuel Hlen.
  - destruct fuel; simpl; auto.
  - destruct fuel as [|fuel]; [simpl in Hlen; lia|].
    simpl. right. exists l1. split; [assumption|].
    apply IHHpath. simpl in Hlen. lia.
Qed.

Lemma reachable_in_reachable : forall h fuel l0 l1,
  l0 < dom h ->
  reachable_in h fuel l0 l1 ->
  reachable h l0 l1.
Proof.
  intros h fuel.
  induction fuel as [|fuel IH]; intros l0 l1 Hdom0 Hreach.
  - simpl in Hreach. subst l1. constructor. exact Hdom0.
  - simpl in Hreach. destruct Hreach as [Heq | [next [Hedge Htail]]].
    + subst l1. constructor. exact Hdom0.
    + eapply rch_trans.
      * apply heap_edge_reachable. exact Hedge.
      * eapply IH; eauto. eapply heap_edge_target_dom; eauto.
Qed.

Lemma exists_in_list_dec : forall {A : Type} (P : A -> Prop)
  (P_dec : forall x, {P x} + {~ P x}) (xs : list A),
  {exists x, List.In x xs /\ P x} + {~ exists x, List.In x xs /\ P x}.
Proof.
  intros A P P_dec xs.
  induction xs as [|x xs IH].
  - right. intros [y [Hin _]]. inversion Hin.
  - destruct (P_dec x) as [HP|HnotP].
    + left. exists x. split; [left; reflexivity|exact HP].
    + destruct IH as [Hex|Hnone].
      * left. destruct Hex as [y [Hin HPy]].
        exists y. split; [right; exact Hin|exact HPy].
      * right. intros [y [[Heq|Hin] HPy]].
        -- subst y. contradiction.
        -- apply Hnone. exists y. split; assumption.
Qed.

Lemma value_eq_dec : forall v1 v2 : value, {v1 = v2} + {v1 <> v2}.
Proof. decide equality; apply Nat.eq_dec. Qed.

Fixpoint field_ref_dec (fields : list value) (l : Loc) :
  {f | nth_error fields f = Some (Iot l)} +
  {forall f, nth_error fields f <> Some (Iot l)}.
Proof.
  destruct fields as [|v fields].
  - right. intros f Hfield. destruct f; discriminate.
  - destruct (value_eq_dec v (Iot l)) as [Heq|Hneq].
    + left. exists 0. simpl. now rewrite Heq.
    + destruct (field_ref_dec fields l) as [Hex|Hnone].
      * left. destruct Hex as [f Hfield]. exists (S f). exact Hfield.
      * right. intros f Hfield. destruct f as [|f].
        -- simpl in Hfield. injection Hfield as Heq. contradiction.
        -- apply (Hnone f). exact Hfield.
Defined.

Lemma heap_edge_dec : forall h l0 l1,
  {heap_edge h l0 l1} + {~ heap_edge h l0 l1}.
Proof.
  intros h l0 l1.
  destruct (runtime_getObj h l0) as [obj|] eqn:Hobj.
  2:{ right. intros [obj' [f [Hobj' _]]]. rewrite Hobj in Hobj'. discriminate. }
  destruct (lt_dec l1 (dom h)) as [Hdom|Hnotdom].
  2:{ right. intros [_ [_ [_ [_ Hdom]]]]. contradiction. }
  destruct (field_ref_dec obj.(fields_map) l1) as [Hex|Hnone].
  - destruct Hex as [f Hfield].
    left. exists obj, f. repeat split; assumption.
  - right. intros [obj' [f [Hobj' [Hfield _]]]].
    rewrite Hobj in Hobj'. injection Hobj' as <-.
    apply (Hnone f). exact Hfield.
Qed.

Fixpoint reachable_in_dec (h : heap) (fuel : nat) (l0 l1 : Loc) :
  {reachable_in h fuel l0 l1} + {~ reachable_in h fuel l0 l1}.
Proof.
  destruct fuel as [|fuel].
  - simpl. apply Nat.eq_dec.
  - simpl.
    destruct (Nat.eq_dec l0 l1) as [Heq|Hneq].
    + left. left. exact Heq.
    + destruct (exists_in_list_dec
        (fun next => heap_edge h l0 next /\ reachable_in h fuel next l1)
        (fun next =>
          match heap_edge_dec h l0 next, reachable_in_dec h fuel next l1 with
          | left Hedge, left Hreach => left (conj Hedge Hreach)
          | right Hnotedge, _ => right (fun H => Hnotedge (proj1 H))
          | _, right Hnotreach => right (fun H => Hnotreach (proj2 H))
          end)
        (seq 0 (dom h))) as [Hex|Hnone].
      * left. right. destruct Hex as [next [_ Hnext]]. exists next. exact Hnext.
      * right. intros [Heq|[next [Hedge Hreach]]]; [contradiction|].
        apply Hnone. exists next. split.
        -- apply in_seq. split; [lia|]. eapply heap_edge_target_dom; eauto.
        -- split; assumption.
Defined.

Theorem reachable_dec : forall h l0 l1,
  {reachable h l0 l1} + {~ reachable h l0 l1}.
Proof.
  intros h l0 l1.
  destruct (lt_dec l0 (dom h)) as [Hdom0|Hnotdom].
  2:{ right. intro Hreach. apply Hnotdom. eapply reachable_source_dom; eauto. }
  destruct (reachable_in_dec h (dom h) l0 l1) as [Hbounded|Hnotbounded].
  - left. eapply reachable_in_reachable; eauto.
  - right. intro Hreach.
    destruct (reachable_edge_path h l0 l1 Hreach) as [nodes Hpath].
    destruct (edge_path_simplify h l0 l1 nodes Hpath)
      as [nodes' [Hpath' Hsimple]].
    apply Hnotbounded.
    eapply edge_path_reachable_in; eauto.
    have Hlen := simple_edge_path_length h l0 l1 nodes' Hpath' Hsimple Hdom0.
    lia.
Defined.


Inductive reachable_abs (CT : class_table) (h : heap) : Loc -> Loc -> Prop :=

  | reachable_abs_heap : forall l
      (Hdom : l < dom h),
      reachable_abs CT h l l

  | reachable_abs_step : forall l0 l1 any C vals k
      (Hdom        : l1 < dom h)
      (Hobj        : runtime_getObj h l0 = Some (mkObj (mkruntime_type any C) vals))
      (Hfield      : nth_error vals k = Some (Iot l1))
      (Hmut_abs    : sf_mutability_rel CT C k RDM_f \/ sf_mutability_rel CT C k Imm_f)
      (Hassign_abs : sf_assignability_rel CT C k RDA \/ sf_assignability_rel CT C k Final),
      reachable_abs CT h l0 l1

  | reachable_abs_trans : forall l0 l1 l2
      (Hreach1 : reachable_abs CT h l0 l1)
      (Hreach2 : reachable_abs CT h l1 l2),
      reachable_abs CT h l0 l2.

Definition protected_locset
  (CT : class_table) (h : heap) (l_root : Loc) : Ensembles.Ensemble Loc :=
  fun l_target => reachable_abs CT h l_root l_target.
