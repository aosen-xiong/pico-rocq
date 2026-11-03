From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall.

(** Types with no non-null values.

    A class declared mutable has only mutable objects, and so has every
    subclass of it; likewise for a class declared immutable.  A reference
    type that pairs such a class with the other mutability is therefore
    inhabited by no object: only null has it.  Requalifying a type-variable
    use produces such types, for example [@Imm E] with [E := @Mut Buffer]. *)

(** A subclass keeps a mutability that its superclass fixes. *)
Lemma rsuper_pinned : forall CT qh C Rs D Vs,
  wf_class_table CT ->
  rsuper_inst CT qh C Rs D Vs ->
  forall dD dC,
    find_class CT D = Some dD -> find_class CT C = Some dC ->
    class_qualifier (signature dD) <> RDM_c ->
    class_qualifier (signature dC) = class_qualifier (signature dD).
Proof.
  intros CT qh C Rs D Vs Hct H.
  induction H as [C Rs | C Rs P Ss D Vs Hparent Hrest IH]; intros dD dC HD HC Hp.
  - rewrite HD in HC. inversion HC. reflexivity.
  - pose proof Hparent as Hparent'. unfold parent_lookup in Hparent'.
    rewrite HC in Hparent'.
    destruct (wf_class_super_inv _ _ _ _ _ Hct HC Hparent')
      as (sd & Hsd & _ & _ & _ & Hpin & _).
    pose proof (IH dD sd HD Hsd Hp) as HP.
    destruct Hpin as [Hq | Hq]; congruence.
Qed.

Theorem pinned_class_uninhabited : forall CT h l C Rs def q0,
  wf_class_table CT -> wf_heap CT h ->
  find_class CT C = Some def ->
  (class_qualifier (signature def) = Mut_c /\ q0 = Imm) \/
  (class_qualifier (signature def) = Imm_c /\ q0 = Mut) ->
  ~ loc_has_rtype CT h l (RClass q0 C Rs).
Proof.
  intros CT h l C Rs def q0 Hct Hheap HfC Hcase Hl.
  unfold loc_has_rtype in Hl.
  destruct (runtime_getObj h l) as [o|] eqn:Ho; [|contradiction].
  destruct Hl as (Hhead & Vs & Hsup & _).
  pose proof (Hheap l (runtime_getObj_dom _ _ _ Ho)) as Hwfo.
  unfold wf_obj in Hwfo. rewrite Ho in Hwfo. destruct Hwfo as (Hrt & _).
  unfold wf_rtypeuse in Hrt.
  destruct (find_class CT (rctype (rt_type o))) as [dC|] eqn:HfO; [|contradiction].
  destruct Hrt as (Hagree & _).
  assert (Hpin : class_qualifier (signature def) <> RDM_c)
    by (destruct Hcase as [[E _] | [E _]]; rewrite E; discriminate).
  pose proof (rsuper_pinned _ _ _ _ _ _ Hct Hsup def dC HfC HfO Hpin) as Heq.
  rewrite Heq in Hagree. unfold head_ok in Hhead.
  destruct Hcase as [[E ->] | [E ->]]; rewrite E in Hagree;
    destruct (rqtype (rt_type o)); simpl in Hagree, Hhead; try discriminate;
    destruct Hhead as [Hx | [Hx | Hx]]; discriminate.
Qed.

Print Assumptions pinned_class_uninhabited.
