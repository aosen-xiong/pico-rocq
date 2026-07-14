Require Import Syntax Subtyping Typing Bigstep MutableCapability.
From Stdlib Require Import Sets.Ensembles.

(** A proof-only authority context records whether [RDM] denotes mutable
    authority in the current frame. It is intentionally independent of the
    receiver object's runtime mutability. *)
Definition authority_context_sound
  (h : heap) (rGamma : r_env) (authority : q_r) : Prop :=
  authority = Mut_r ->
  exists this,
    get_this_var_mapping (vars rGamma) = Some this /\
    r_muttype h this = Some Mut_r.

Lemma nonnull_subtype_preserves_authority_capability :
  forall CT rGamma h l T1 T2 qcontext authority,
    wf_r_typable CT rGamma h l T1 qcontext ->
    qualified_type_subtype CT T1 T2 ->
    capability_in_context authority (sqtype T2) ->
    capability_in_context authority (sqtype T1).
Proof.
  intros CT rGamma h l T1 T2 qcontext authority Htyp Hsub Hcap.
  apply qualified_type_subtype_q_subtype in Hsub.
  unfold capability_in_context in *.
  destruct Hcap as [Hmut | [Hrdm Hauthority]].
  - rewrite Hmut in Hsub.
    inversion Hsub; subst; auto.
    exfalso. eapply typable_nonnull_not_bot; eauto.
  - rewrite Hrdm in Hsub.
    inversion Hsub; subst; auto.
    exfalso. eapply typable_nonnull_not_bot; eauto.
Qed.

Definition extend_authority_capability
  (M : Ensemble Loc) (authority : q_r) (qc : q_c) (fresh : Loc) :
  Ensemble Loc :=
  fun l => In Loc M l \/
    (capability_in_context authority (qc2q qc) /\ l = fresh).
