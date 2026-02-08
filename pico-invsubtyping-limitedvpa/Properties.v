Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation.

From Stdlib Require Import List.
From Stdlib Require String.
Import ListNotations.
From RecordUpdate Require Import RecordUpdate.

Lemma q_subtype_RO_Imm_false : RO ⊑ Imm -> False.
Proof.
  intro H; inversion H; subst; auto.
Qed.

Lemma q_subtype_RO_Mut_false : RO ⊑ Mut -> False.
Proof.
  intro H; inversion H; subst; auto.
Qed.

Lemma q_subtype_RO_Lost_false : RO ⊑ Lost -> False.
Proof.
  intro H; inversion H; subst; auto.
Qed.

Lemma q_subtype_RO_RDM_false : RO ⊑ RDM -> False.
Proof.
  intro H; inversion H; subst; auto.
Qed.

Lemma q_subtype_RO_Bot_false : RO ⊑ Bot -> False.
Proof.
  intro H; inversion H; subst; auto.
Qed.
Hint Resolve q_subtype_RO_Imm_false
             q_subtype_RO_Mut_false
             q_subtype_RO_Lost_false
             q_subtype_RO_RDM_false
             q_subtype_RO_Bot_false
  : qsub_wrong.


Lemma q_subtype_Imm_Mut_false : Imm ⊑ Mut -> False.
Proof.
  intro H; inversion H; subst; auto.
Qed.

Lemma q_subtype_Imm_RDM_false : Imm ⊑ RDM -> False.
Proof.
  intro H; inversion H; subst; auto.
Qed.

Lemma q_subtype_Imm_Lost_false : Imm ⊑ Lost -> False.
Proof.
  intro H; inversion H; subst; auto.
Qed.

Lemma q_subtype_Imm_Bot_false : Imm ⊑ Bot -> False.
Proof.
  intro H; inversion H; subst; auto.
Qed.

Hint Resolve q_subtype_Imm_Mut_false
             q_subtype_Imm_RDM_false
             q_subtype_Imm_Lost_false
             q_subtype_Imm_Bot_false
  : qsub_wrong.

Lemma q_subtype_Mut_Imm_false : Mut ⊑ Imm -> False.
Proof.
  intro H; inversion H; subst; auto.
Qed.

Lemma q_subtype_Mut_RDM_false : Mut ⊑ RDM -> False.
Proof.
  intro H; inversion H; subst; auto.
Qed.

Lemma q_subtype_Mut_Lost_false : Mut ⊑ Lost -> False.
Proof.
  intro H; inversion H; subst; auto.
Qed.

Lemma q_subtype_Mut_Bot_false : Mut ⊑ Bot -> False.
Proof.
  intro H; inversion H; subst; auto.
Qed.

Hint Resolve q_subtype_Mut_Imm_false
             q_subtype_Mut_RDM_false
             q_subtype_Mut_Lost_false
             q_subtype_Mut_Bot_false
  : qsub_wrong.

Lemma q_subtype_RDM_Imm_false : RDM ⊑ Imm -> False.  
Proof.
  intro H; inversion H; subst; auto.
Qed.  

Lemma q_subtype_RDM_Mut_false : RDM ⊑ Mut -> False.
Proof.
  intro H; inversion H; subst; auto.    
Qed.

Lemma q_subtype_RDM_Lost_false : RDM ⊑ Lost -> False.
Proof.
  intro H; inversion H; subst; auto.
Qed.

Lemma q_subtype_RDM_Bot_false : RDM ⊑ Bot -> False.
Proof.
  intro H; inversion H; subst; auto.
Qed.

Hint Resolve q_subtype_RDM_Imm_false
             q_subtype_RDM_Mut_false
             q_subtype_RDM_Lost_false
             q_subtype_RDM_Bot_false
  : qsub_wrong.

Lemma q_subtype_Lost_Imm_false : Lost ⊑ Imm -> False.
Proof.
  intro H; inversion H; subst; auto.
Qed.

Lemma q_subtype_Lost_Mut_false : Lost ⊑ Mut -> False.
Proof.
  intro H; inversion H; subst; auto.
Qed.

Lemma q_subtype_Lost_RDM_false : Lost ⊑ RDM -> False.
Proof.
  intro H; inversion H; subst; auto.
Qed.

Lemma q_subtype_Lost_Bot_false : Lost ⊑ Bot -> False.
Proof.
  intro H; inversion H; subst; auto.
Qed.

Lemma q_subtype_Lost_Lost_false : Lost ⊑ Lost -> False.
Proof.
  intro H; inversion H; subst; auto.
Qed.

Hint Resolve q_subtype_Lost_Imm_false
             q_subtype_Lost_Mut_false
             q_subtype_Lost_RDM_false
             q_subtype_Lost_Bot_false
             q_subtype_Lost_Lost_false
  : qsub_wrong.

Ltac solve_q_subtype_wrong :=
  lazymatch goal with
  | [ H : q_subtype RO Imm |- _ ] => exfalso; eauto with qsub_wrong
  | [ H : q_subtype RO Mut |- _ ] => exfalso; eauto with qsub_wrong
  | [ H : q_subtype RO RDM |- _ ] => exfalso; eauto with qsub_wrong
  | [ H : q_subtype RO Lost |- _ ] => exfalso; eauto with qsub_wrong
  | [ H : q_subtype RO Bot  |- _ ] => exfalso; eauto with qsub_wrong
  | [ H : q_subtype Imm Mut  |- _ ] => exfalso; eauto with qsub_wrong
  | [ H : q_subtype Imm RDM |- _ ] => exfalso; eauto with qsub_wrong
  | [ H : q_subtype Imm Lost |- _ ] => exfalso; eauto with qsub_wrong
  | [ H : q_subtype Imm Bot  |- _ ] => exfalso; eauto with qsub_wrong
  | [ H : q_subtype Mut Imm  |- _ ] => exfalso; eauto with qsub_wrong
  | [ H : q_subtype Mut RDM |- _ ] => exfalso; eauto with qsub_wrong
  | [ H : q_subtype Mut Lost |- _ ] => exfalso; eauto with qsub_wrong
  | [ H : q_subtype Mut Bot  |- _ ] => exfalso; eauto with qsub_wrong
  | [ H : q_subtype RDM Imm  |- _ ] => exfalso; eauto with qsub_wrong
  | [ H : q_subtype RDM Mut  |- _ ] => exfalso; eauto with qsub_wrong
  | [ H : q_subtype RDM Lost |- _ ] => exfalso; eauto with qsub_wrong
  | [ H : q_subtype RDM Bot  |- _ ] => exfalso; eauto with qsub_wrong
  | [ H : q_subtype Lost Lost |- _ ] => exfalso; eauto with qsub_wrong
  | [ H : q_subtype Lost Imm |- _ ] => exfalso; eauto with qsub_wrong
  | [ H : q_subtype Lost Mut |- _ ] => exfalso; eauto with qsub_wrong
  | [ H : q_subtype Lost RDM |- _ ] => exfalso; eauto with qsub_wrong
  | [ H : q_subtype Lost Bot  |- _ ] => exfalso; eauto with qsub_wrong
  | _ => idtac
  end.

Lemma q_subtype_Bot_RO_true : Bot ⊑ RO.
Proof.
  constructor.
Qed.

Lemma q_subtype_Bot_Imm_true : Bot ⊑ Imm.
Proof.
  constructor.
Qed.

Lemma q_subtype_Bot_Mut_true : Bot ⊑ Mut.
Proof.
  constructor.
Qed.

Lemma q_subtype_Bot_RDM_true : Bot ⊑ RDM.
Proof.
  constructor.
Qed.

Lemma q_subtype_Bot_Lost_true : Bot ⊑ Lost.
Proof.
  constructor.
Qed.

Lemma q_subtype_Bot_Bot_true : Bot ⊑ Bot.
Proof.
  constructor.
  easy.
Qed.

Hint Resolve q_subtype_Bot_RO_true
             q_subtype_Bot_Imm_true
             q_subtype_Bot_Mut_true
             q_subtype_Bot_RDM_true
             q_subtype_Bot_Lost_true
             q_subtype_Bot_Bot_true
  : qsub_correct.

Lemma q_subtype_Imm_Imm_true : Imm ⊑ Imm.
Proof.
  constructor.
  easy.
Qed.

Lemma q_subtype_Imm_RO_true : Imm ⊑ RO.
Proof.
  constructor.
Qed.

Lemma q_subtype_Mut_Mut_true : Mut ⊑ Mut.
Proof.
  constructor.
  easy.
Qed.

Lemma q_subtype_Mut_RO_true : Mut ⊑ RO.
Proof.
  constructor.
Qed.

Lemma q_subtype_RDM_RDM_true : RDM ⊑ RDM.
Proof.
  constructor.
  easy.
Qed.

Lemma q_subtype_RDM_RO_true : RDM ⊑ RO.
Proof.
  constructor.  
Qed.

Lemma q_subtype_Lost_RO_true : Lost ⊑ RO.
Proof.
  constructor.  
Qed.

Lemma q_subtype_RO_RO_true : RO ⊑ RO.
Proof.
  constructor.
  easy.
Qed.

Hint Resolve q_subtype_Imm_Imm_true
             q_subtype_Imm_RO_true
             q_subtype_Mut_Mut_true
             q_subtype_Mut_RO_true
             q_subtype_RDM_RDM_true
             q_subtype_RDM_RO_true
             q_subtype_Lost_RO_true
             q_subtype_RO_RO_true
  : qsub_correct.

Lemma qualifier_typable_context_Imm_r_Mut_Mut_r_false : 
  qualifier_typable_context Imm_r (Mut) Mut_r -> False.
Proof.
  intro H; unfold qualifier_typable_context in H.
  simpl in H.
  inversion H; subst; auto.
Qed.

Lemma qualifier_typable_context_Imm_r_RDM_Mut_r_false : 
  qualifier_typable_context Imm_r (RDM) Mut_r -> False.
Proof.
  intro H; unfold qualifier_typable_context in H.
  simpl in H.
  inversion H; subst; auto.
Qed.

Lemma qualifier_typable_context_Imm_r_Bot_Mut_r_false : 
  qualifier_typable_context Imm_r (Bot) Mut_r -> False.
Proof.
  intro H; unfold qualifier_typable_context in H.
  simpl in H.
  inversion H; subst; auto.
Qed.

Lemma qualifier_typable_context_Imm_r_Mut_Imm_r_false : 
  qualifier_typable_context Imm_r (Mut) Imm_r -> False.
Proof.
  intro H; unfold qualifier_typable_context in H.
  simpl in H.
  inversion H; subst; auto.
Qed.

Lemma qualifier_typable_context_Imm_r_Bot_Imm_r_false : 
  qualifier_typable_context Imm_r (Bot) Imm_r -> False.
Proof.
  intro H; unfold qualifier_typable_context in H.
  simpl in H.
  inversion H; subst; auto.
Qed.

Hint Resolve qualifier_typable_context_Imm_r_Mut_Mut_r_false
             qualifier_typable_context_Imm_r_RDM_Mut_r_false
             qualifier_typable_context_Imm_r_Bot_Mut_r_false
             qualifier_typable_context_Imm_r_Mut_Imm_r_false
             qualifier_typable_context_Imm_r_Bot_Imm_r_false
  : qtypable_wrong.

Lemma qualifier_typable_context_Mut_r_Imm_Mut_r_false : 
  qualifier_typable_context Mut_r (Imm) Mut_r -> False.
Proof.
  intro H; unfold qualifier_typable_context in H.
  simpl in H.
  inversion H; subst; auto.
Qed.

Lemma qualifier_typable_context_Mut_r_Bot_Mut_r_false : 
  qualifier_typable_context Mut_r (Bot) Mut_r -> False.
Proof.
  intro H; unfold qualifier_typable_context in H.
  simpl in H.
  inversion H; subst; auto.
Qed.

Lemma qualifier_typable_context_Mut_r_Imm_Imm_r_false : 
  qualifier_typable_context Mut_r (Imm) Imm_r -> False.
Proof.
  intro H; unfold qualifier_typable_context in H.
  simpl in H.
  inversion H; subst; auto.
Qed.

Lemma qualifier_typable_context_Mut_r_RDM_Imm_r_false : 
  qualifier_typable_context Mut_r (RDM) Imm_r -> False.
Proof.
  intro H; unfold qualifier_typable_context in H.
  simpl in H.
  inversion H; subst; auto.
Qed.

Lemma qualifier_typable_context_Mut_r_Bot_Imm_r_false : 
  qualifier_typable_context Mut_r (Bot) Imm_r -> False.
Proof.
  intro H; unfold qualifier_typable_context in H.
  simpl in H.
  inversion H; subst; auto.
Qed.

Hint Resolve qualifier_typable_context_Mut_r_Imm_Mut_r_false
             qualifier_typable_context_Mut_r_Bot_Mut_r_false
             qualifier_typable_context_Mut_r_Imm_Imm_r_false
             qualifier_typable_context_Mut_r_RDM_Imm_r_false
             qualifier_typable_context_Mut_r_Bot_Imm_r_false
  : qtypable_wrong.

Ltac solve_qualifier_typable_wrong_concrete :=
  lazymatch goal with
  | [ H : qualifier_typable_context Imm_r Mut Mut_r |- _ ] =>
      exfalso; eauto with qtypable_wrong
  | [ H : qualifier_typable_context Imm_r RDM Mut_r |- _ ] =>
      exfalso; eauto with qtypable_wrong
  | [ H : qualifier_typable_context Imm_r Bot Mut_r |- _ ] =>
      exfalso; eauto with qtypable_wrong
  | [ H : qualifier_typable_context Imm_r Mut Imm_r |- _ ] =>
      exfalso; eauto with qtypable_wrong
  | [ H : qualifier_typable_context Imm_r Bot Imm_r |- _ ] =>
      exfalso; eauto with qtypable_wrong
  | [ H : qualifier_typable_context Mut_r Imm Mut_r |- _ ] =>
      exfalso; eauto with qtypable_wrong
  | [ H : qualifier_typable_context Mut_r Bot Mut_r |- _ ] =>
      exfalso; eauto with qtypable_wrong
  | [ H : qualifier_typable_context Mut_r Imm Imm_r |- _ ] =>
      exfalso; eauto with qtypable_wrong
  | [ H : qualifier_typable_context Mut_r RDM Imm_r |- _ ] =>
      exfalso; eauto with qtypable_wrong
  | [ H : qualifier_typable_context Mut_r Bot Imm_r |- _ ] =>
      exfalso; eauto with qtypable_wrong
    | [ H : qualifier_typable_context Imm_r Imm Mut_r |- _ ] =>
      clear H
  | [ H : qualifier_typable_context Imm_r RO  Mut_r |- _ ] =>
      clear H
  | [ H : qualifier_typable_context Imm_r Lost Mut_r |- _ ] =>
      clear H
  | [ H : qualifier_typable_context Imm_r RO  Imm_r |- _ ] =>
      clear H
  | [ H : qualifier_typable_context Imm_r Imm Imm_r |- _ ] =>
      clear H
  | [ H : qualifier_typable_context Imm_r Lost Imm_r |- _ ] =>
      clear H
  | [ H : qualifier_typable_context Imm_r RDM Imm_r |- _ ] =>
      clear H

  | [ H : qualifier_typable_context Mut_r Mut Mut_r |- _ ] =>
      clear H
  | [ H : qualifier_typable_context Mut_r RO  Mut_r |- _ ] =>
      clear H
  | [ H : qualifier_typable_context Mut_r Lost Mut_r |- _ ] =>
      clear H
  | [ H : qualifier_typable_context Mut_r RDM Mut_r |- _ ] =>
      clear H
  | [ H : qualifier_typable_context Mut_r RO  Imm_r |- _ ] =>
      clear H
  | [ H : qualifier_typable_context Mut_r Mut Imm_r |- _ ] =>
      clear H
  | [ H : qualifier_typable_context Mut_r Lost Imm_r |- _ ] =>
      clear H

  | _ => idtac    
  end.

Lemma qualifier_typable_context_Imm_r_Imm_Mut_r_true : 
  qualifier_typable_context Imm_r (Imm) Mut_r.
Proof.
  easy.
Qed.

Lemma qualifier_typable_context_Imm_r_RO_Mut_r_true : 
  qualifier_typable_context Imm_r (RO) Mut_r.
Proof.
  easy.
Qed.

Lemma qualifier_typable_context_Imm_r_Lost_Mut_r_true : 
  qualifier_typable_context Imm_r (Lost) Mut_r.
Proof.
  easy.
Qed.

Lemma qualifier_typable_context_Imm_r_RO_Imm_r_true : 
  qualifier_typable_context Imm_r (RO) Imm_r.
Proof.
  easy.
Qed.

Lemma qualifier_typable_context_Imm_r_Imm_Imm_r_true : 
  qualifier_typable_context Imm_r (Imm) Imm_r.
Proof.
  easy.
Qed.

Lemma qualifier_typable_context_Imm_r_Lost_Imm_r_true : 
  qualifier_typable_context Imm_r (Lost) Imm_r.
Proof.
  easy.
Qed.

Lemma qualifier_typable_context_Imm_r_RDM_Imm_r_true : 
  qualifier_typable_context Imm_r (RDM) Imm_r.
Proof.
  easy.
Qed.

Hint Resolve qualifier_typable_context_Imm_r_Imm_Mut_r_true
             qualifier_typable_context_Imm_r_RO_Mut_r_true
             qualifier_typable_context_Imm_r_Lost_Mut_r_true
             qualifier_typable_context_Imm_r_RO_Imm_r_true
             qualifier_typable_context_Imm_r_Imm_Imm_r_true
             qualifier_typable_context_Imm_r_Lost_Imm_r_true
             qualifier_typable_context_Imm_r_RDM_Imm_r_true
  : qtypable_correct.

Lemma qualifier_typable_context_Mut_r_Mut_Mut_r_true : 
  qualifier_typable_context Mut_r (Mut) Mut_r.
Proof.
  easy.
Qed.

Lemma qualifier_typable_context_Mut_r_RO_Mut_r_true : 
  qualifier_typable_context Mut_r (RO) Mut_r.
Proof.
  easy.
Qed.

Lemma qualifier_typable_context_Mut_r_Lost_Mut_r_true : 
  qualifier_typable_context Mut_r (Lost) Mut_r.
Proof.
  easy.
Qed.

Lemma qualifier_typable_context_Mut_r_RDM_Mut_r_true : 
  qualifier_typable_context Mut_r (RDM) Mut_r.
Proof.
  easy.
Qed.


Lemma qualifier_typable_context_Mut_r_RO_Imm_r_true : 
  qualifier_typable_context Mut_r (RO) Imm_r.
Proof.
  easy.
Qed.

Lemma qualifier_typable_context_Mut_r_Mut_Imm_r_true : 
  qualifier_typable_context Mut_r (Mut) Imm_r.
Proof.
  easy.
Qed.

Lemma qualifier_typable_context_Mut_r_Lost_Imm_r_true : 
  qualifier_typable_context Mut_r (Lost) Imm_r.
Proof.
  easy.
Qed.

Hint Resolve qualifier_typable_context_Mut_r_Mut_Mut_r_true
             qualifier_typable_context_Mut_r_RO_Mut_r_true
             qualifier_typable_context_Mut_r_Lost_Mut_r_true
             qualifier_typable_context_Mut_r_RDM_Mut_r_true
             qualifier_typable_context_Mut_r_RO_Imm_r_true
             qualifier_typable_context_Mut_r_Mut_Imm_r_true
             qualifier_typable_context_Mut_r_Lost_Imm_r_true
  : qtypable_correct.

Ltac solve_qualifier_typable_correct_concrete :=
  lazymatch goal with
  (* --- goal is a "correct" concrete qualifier_typable_context --- *)
  | |- qualifier_typable_context Imm_r Imm Mut_r =>
      eauto with qtypable_correct
  | |- qualifier_typable_context Imm_r RO Mut_r =>
      eauto with qtypable_correct
  | |- qualifier_typable_context Imm_r Lost Mut_r =>
      eauto with qtypable_correct
  | |- qualifier_typable_context Imm_r RO Imm_r =>
      eauto with qtypable_correct
  | |- qualifier_typable_context Imm_r Imm Imm_r =>
      eauto with qtypable_correct
  | |- qualifier_typable_context Imm_r Lost Imm_r =>
      eauto with qtypable_correct
  | |- qualifier_typable_context Imm_r RDM Imm_r =>
      eauto with qtypable_correct

  | |- qualifier_typable_context Mut_r Mut Mut_r =>
      eauto with qtypable_correct
  | |- qualifier_typable_context Mut_r RO Mut_r =>
      eauto with qtypable_correct
  | |- qualifier_typable_context Mut_r Lost Mut_r =>
      eauto with qtypable_correct
  | |- qualifier_typable_context Mut_r RDM Mut_r =>
      eauto with qtypable_correct
  | |- qualifier_typable_context Mut_r RO Imm_r =>
      eauto with qtypable_correct
  | |- qualifier_typable_context Mut_r Mut Imm_r =>
      eauto with qtypable_correct
  | |- qualifier_typable_context Mut_r Lost Imm_r =>
      eauto with qtypable_correct
  end.

Lemma collect_methods_exists : forall CT C,
  wf_class_table CT ->
  C < dom CT ->
  exists methods, CollectMethods CT C methods.
Proof.
  intros CT C Hwf_ct Hdom.
  induction C as [C IH] using lt_wf_ind.
  assert (Hexists_class : exists class_def, find_class CT C = Some class_def).
  {
    apply find_class_Some.
    exact Hdom.
  }
  destruct Hexists_class as [class_def Hfind_class].
  assert (Hwf_class : wf_class CT class_def).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  inversion Hwf_class; subst.
    - (* WFObjectDef: no parent *)
    exists (methods (body class_def)).
    eapply CM_Object; eauto.
  - (* WFOtherDef: has parent *)
    assert (Hdom_parent : superC < dom CT).
    {
      unfold wf_class_table in Hwf_ct.
      destruct Hwf_ct as [_ [_ [Hotherclasses Hcname_consistent]]].
      assert (Hcname_eq : cname (signature class_def) = C).
      {
        apply Hcname_consistent.
        exact Hfind_class.
      }
      rewrite Hcname_eq in H1.
      (* Use H2: C > superC *)
      lia.
    }
    (* Apply strong induction hypothesis *)
    assert (IH_parent : exists parent_methods, CollectMethods CT superC parent_methods).
    {
      apply IH.
      (* Need to prove superC < C *)
      unfold wf_class_table in Hwf_ct.
      destruct Hwf_ct as [_ [_ [_ Hcname_consistent]]].
      assert (Hcname_eq : cname (signature class_def) = C).
      {
        apply Hcname_consistent.
        exact Hfind_class.
      }
      rewrite Hcname_eq in H1.
      exact H1.
      exact Hdom_parent.
    }
    destruct IH_parent as [parent_methods Hcollect_parent].
    exists (override parent_methods (methods (body class_def))).
    eapply CM_Inherit; eauto.
Qed.

Lemma override_parent_method_in : forall parent_methods own_methods m mdef,
  gget_method (override parent_methods own_methods) m = Some mdef ->
  gget_method own_methods m = None ->
  In mdef parent_methods /\ 
  eq_method_name (mname (msignature mdef)) m = true.
Proof.
  intros parent_methods own_methods m mdef Hoverride Hown.
  unfold override, gget_method in Hoverride.
  unfold gget_method in Hown.
  apply find_some in Hoverride.
  destruct Hoverride as [Hin Heq].
  apply in_app_or in Hin.
  destruct Hin as [Hin_own | Hin_filtered].
  - (* mdef is in own_methods - contradiction *)
    exfalso.
    (* If mdef is in own_methods and matches m, then find should return Some *)
    assert (Hfind_some : exists x, find (fun mdef => eq_method_name (mname (msignature mdef)) m) own_methods = Some x).
    {
      apply find_some_iff.
      exists mdef.
      split; [exact Hin_own | exact Heq].
    }
    destruct Hfind_some as [x Hx].
    rewrite Hx in Hown.
    discriminate.
  - (* mdef is in filtered parent_methods *)
    apply filter_In in Hin_filtered.
    destruct Hin_filtered as [Hin_parent _].
    split; [exact Hin_parent | exact Heq].
Qed.

Lemma gget_method_from_in : forall methods m mdef,
  In mdef methods ->
  eq_method_name (mname (msignature mdef)) m = true ->
  exists mdef', gget_method methods m = Some mdef' /\ 
                eq_method_name (mname (msignature mdef')) m = true.
Proof.
  intros methods m mdef Hin Heq.
  unfold gget_method.
  induction methods as [|h t IH].
  - (* methods = [] *)
    contradiction.
  - (* methods = h :: t *)
    simpl.
    destruct (eq_method_name (mname (msignature h)) m) eqn:Heq_h.
    + (* h matches m *)
      exists h.
      split; [reflexivity | exact Heq_h].
    + (* h doesn't match m *)
      simpl in Hin.
      destruct Hin as [Heq_mdef | Hin_t].
      * (* mdef = h - contradiction *)
        subst h.
        rewrite Heq in Heq_h.
        discriminate.
      * (* mdef in t *)
        apply IH.
        exact Hin_t.
Qed.

Lemma method_body_well_typed : forall CT C cdef mdef,
  wf_class_table CT ->
  C < dom CT ->
  find_class CT C = Some cdef ->
  In mdef (methods (body cdef)) ->
  exists sΓ', stmt_typing CT (mreceiver (msignature mdef) :: mparams (msignature mdef)) 
                           (mbody_stmt (mbody mdef)) 
                           sΓ'.
Proof.
  intros CT C cdef mdef Hwf_ct Hdom HfindC Hlookup.
  assert (Hwf_class : wf_class CT cdef).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }

  assert (Hwf_mdef : wf_method CT C mdef).
  {
    eapply method_lookup_wf_class; eauto.
  }
  inversion Hwf_mdef; subst.
  destruct H as [sΓ' [Htyping _]].
  exists x.
  exact Htyping.
Qed.

Lemma method_body_well_typed_by_find : forall CT C m mdef,
  wf_class_table CT ->
  C < dom CT ->
  FindMethodWithName CT C m mdef ->
  exists sΓ', stmt_typing CT (mreceiver (msignature mdef) :: mparams (msignature mdef)) 
                           (mbody_stmt (mbody mdef)) 
                           sΓ'.
Proof.
  intros CT C m mdef Hwf_ct Hdom Hlookup.
  assert (Hexists_class : exists class_def, find_class CT C = Some class_def).
  {
    apply find_class_Some.
    exact Hdom.
  }
  destruct Hexists_class as [class_def Hfind_class].
  assert (Hwf_class : wf_class CT class_def).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  assert (Hcname_eq : cname (signature class_def) = C).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [_ [_ Hcname_consistent]].
    destruct Hcname_consistent as [_ Hcname_eq].
    apply Hcname_eq.
    exact Hfind_class.
  }

  assert (Hwf_inherited : exists D ddef, base_subtype CT C D /\ find_class CT D = Some ddef /\ In mdef (methods (body ddef)) /\ wf_method CT D mdef).
  {
    eapply method_lookup_in_wellformed_inherited; eauto.
  }
  destruct Hwf_inherited as [D [ddef [Hsub [Hfind_D [Hin_D Hwf_D]]]]].

  (* Extract the statement typing from wf_method *)
  inversion Hwf_D; subst.
  destruct H as [sΓ' [Htyping _]].
  exists x.
  exact Htyping.
Qed.

Lemma wf_method_sig_types : forall CT C mdef,
  wf_method CT C mdef ->
  wf_stypeuse CT (sqtype (mreceiver (msignature mdef))) (sctype (mreceiver (msignature mdef))) /\
  Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) (mparams (msignature mdef)).
Proof.
  intros CT C mdef Hwf_method.
  inversion Hwf_method; subst.
  destruct H as [mreturn [Htyping _]].
  assert (Hwf_env : wf_senv CT (mreceiver (msignature mdef) :: mparams (msignature mdef))).
  {
    eapply stmt_typing_wf_env; eauto.
  }
  (* unfold sΓ, msig in Hwf_env. *)
  inversion Hwf_env; subst.
  split.
  - (* Receiver well-formedness *)
    apply Forall_inv in H0.
    exact H0.
  - (* Parameters well-formedness *)
    apply Forall_inv_tail in H0.
    exact H0.
Qed.

Lemma method_sig_wf_reciever : forall CT C cdef mdef,
  wf_class_table CT ->
  C < dom CT ->
  find_class CT C = Some cdef ->
  In mdef (methods (body cdef)) ->
  wf_stypeuse CT (sqtype (mreceiver (msignature mdef))) (sctype (mreceiver (msignature mdef))).
Proof.
  intros CT C cdef mdef Hwf_ct Hdom HfindC Hlookup.
  assert (Hwf_class : wf_class CT cdef).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  assert (Hwf_mdef : wf_method CT C mdef).
  {
    eapply method_lookup_wf_class; eauto.
  }

  eapply wf_method_sig_types; eauto.
Qed.

Lemma method_sig_wf_parameters : forall CT C cdef mdef,
  wf_class_table CT ->
  C < dom CT ->
  find_class CT C = Some cdef ->
  In mdef (methods (body cdef)) ->
  Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) (mparams (msignature mdef)).
Proof.
  intros CT C cdef mdef Hwf_ct Hdom HfindC Hlookup.
  assert (Hwf_class : wf_class CT cdef).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  assert (Hwf_mdef : wf_method CT C mdef).
  {
    eapply method_lookup_wf_class; eauto.
  }

  eapply wf_method_sig_types; eauto.
Qed.

Lemma method_sig_wf_receiver_by_find : forall CT C m mdef,
  wf_class_table CT ->
  C < dom CT ->
  FindMethodWithName CT C m mdef ->
  wf_stypeuse CT (sqtype (mreceiver (msignature mdef))) (sctype (mreceiver (msignature mdef))).
Proof.
  intros CT C m mdef Hwf_ct Hdom Hlookup.
  assert (Hwf_inherited : exists D ddef, base_subtype CT C D /\ find_class CT D = Some ddef /\ In mdef (methods (body ddef)) /\ wf_method CT D mdef).
  {
    eapply method_lookup_in_wellformed_inherited; eauto.
  }
  destruct Hwf_inherited as [D [ddef [Hsub [Hfind_D [Hin_D Hwf_D]]]]].
  eapply wf_method_sig_types; eauto.
Qed.

Lemma method_sig_wf_parameters_by_find : forall CT C m mdef,
  wf_class_table CT ->
  C < dom CT ->
  FindMethodWithName CT C m mdef ->
  Forall (fun T => wf_stypeuse CT (sqtype T) (sctype T)) (mparams (msignature mdef)).
Proof.
  intros CT C m mdef Hwf_ct Hdom Hlookup.
  assert (Hwf_inherited : exists D ddef, base_subtype CT C D /\ find_class CT D = Some ddef /\ In mdef (methods (body ddef)) /\ wf_method CT D mdef).
  {
    eapply method_lookup_in_wellformed_inherited; eauto.
  }
  destruct Hwf_inherited as [D [ddef [Hsub [Hfind_D [Hin_D Hwf_D]]]]].
  eapply wf_method_sig_types; eauto.
Qed.

Lemma In_gget_method_unique : forall method_list mdef m,
  NoDup (map (fun mdef => mname (msignature mdef)) method_list) ->
  In mdef method_list ->
  mname (msignature mdef) = m ->
  gget_method method_list m = Some mdef.
Proof.
  intros method_list mdef m Hnodup Hin Hname.
  unfold gget_method.
  induction method_list as [|hd tl IH].
  - contradiction Hin.
  - simpl in Hin.
    destruct Hin as [Heq | Hin_tl].
    + subst hd.
      simpl.
      unfold eq_method_name.
      rewrite Hname.
      rewrite Nat.eqb_refl.
      reflexivity.
    + simpl.
      unfold eq_method_name.
      destruct (Nat.eqb (mname (msignature hd)) m) eqn:Heqb.
      * (* Contradiction with NoDup *)
        exfalso.
        apply Nat.eqb_eq in Heqb.
        simpl in Hnodup.
        inversion Hnodup; subst.
        apply H1.
        apply in_map_iff.
        exists mdef.
        split; [symmetry; exact Heqb | exact Hin_tl].
      * (* Use IH *)
        apply IH.
        -- simpl in Hnodup.
           inversion Hnodup; auto.
        -- exact Hin_tl.
Qed.

Lemma In_gget_method_unique_class : forall CT C cdef mdef m,
  wf_class_table CT ->
  find_class CT C = Some cdef ->
  In mdef (methods (body cdef)) ->
  mname (msignature mdef) = m ->
  gget_method (methods (body cdef)) m = Some mdef.
Proof.
  intros CT C cdef mdef m Hwf_ct Hfind Hin Hname.
  assert (Hwf_class : wf_class CT cdef).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  apply In_gget_method_unique.
  - (* Extract NoDup from wf_class *)
    inversion Hwf_class; subst.
    + (* WFObjectDef case *)
      rewrite H2.
      simpl.
      constructor.
    + (* WFOtherDef case *)
      destruct H2 as [_ [_ [Hnodup _]]].
      unfold bod in Hnodup.
      exact Hnodup.
  - exact Hin.
  - exact Hname.
Qed.

Lemma constructor_params_field_count : forall CT C ctor csig fields,
  wf_class_table CT ->
  C < dom CT ->
  constructor_def_lookup CT C = Some ctor ->
  csig = csignature ctor ->
  CollectFields CT C fields ->
  List.length (cparams csig) = List.length fields.
Proof.
  intros CT C ctor csig fields Hwf_ct Hdom Hctor_lookup Hcsig Hcollect.
  subst csig.
  
  (* Move the quantified variables inside the induction *)
  revert ctor fields Hctor_lookup Hcollect.
  
  (* Strong induction on C *)
  induction C as [C IH] using lt_wf_ind.
  
  intros ctor fields Hctor_lookup Hcollect.
  (* Get the class definition *)
  assert (Hclass_exists : exists cdef, find_class CT C = Some cdef).
  {
    apply nth_error_Some_exists.
    exact Hdom.
  }
  destruct Hclass_exists as [cdef Hfind_class].
  
  (* Extract well-formedness of the class *)
  assert (Hwf_class : wf_class CT cdef).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  
  (* Extract constructor well-formedness *)
  assert (Hctor_eq : constructor (body cdef) = ctor).
  {
    unfold constructor_def_lookup in Hctor_lookup.
    rewrite Hfind_class in Hctor_lookup.
    injection Hctor_lookup as Hctor_eq.
    exact Hctor_eq.
  }
  
  (* Case analysis on class structure *)
  inversion Hwf_class; subst.
  - (* Object class case *)
    inversion Hcollect; subst.
    destruct (find_class CT C).
    easy.
    easy.
    unfold wf_constructor_object in H4.
    destruct H4 as [_  [_ Hcparams]].
    destruct Hcparams as [_ [Hcparams _]].
    rewrite Hcparams.
    reflexivity.

    exfalso.
    assert (cdef = def) by (rewrite Hfind_class in H3; injection H3; auto).
    subst def.
    rewrite H in H7.
    discriminate.
  - (* Regular class case with superclass *)
    destruct H2 as [Hwf_ctor [Hnodup_methods [Hforall_methods Hforall_fields]]].

    (* Extract class name consistency *)
    assert (Hcname_eq : cname sig = C).
    {
      apply find_class_cname_consistent in Hfind_class; auto.
    }
    unfold wf_constructor in Hwf_ctor.
    subst C0.
    destruct Hwf_ctor as [_ [_ [field_defs [Hcollect_field_defs [Hparams_eq _]]]]].
    assert (field_defs = fields).
    {
      eapply collect_fields_deterministic_rel; eauto.
      rewrite Hcname_eq.
      exact Hcollect.
    }
    subst field_defs.
    exact Hparams_eq.
Qed.

Lemma constructor_lookup_wf : forall CT C ctor,
  wf_class_table CT ->
  C < dom CT ->
  constructor_sig_lookup CT C = Some ctor ->
  wf_constructor CT C ctor.
Proof.
  intros CT C ctor Hwf_ct Hdom Hctor_lookup.
  assert (Hexists_class : exists cdef, find_class CT C = Some cdef).
  {
    apply find_class_Some. exact Hdom.
  }
  destruct Hexists_class as [cdef Hfind_class].
  assert (Hwf_class : wf_class CT cdef).
  {
    unfold wf_class_table in Hwf_ct.
    destruct Hwf_ct as [Hforall_wf _].
    eapply Forall_nth_error; eauto.
  }
  inversion Hwf_class; subst.
  unfold wf_constructor.
  unfold wf_constructor.
  unfold wf_constructor_object in H4.
  destruct H4 as [Hbound [H2314 [Hcparams [Hcollect_fields H2341]]]].
  assert (Hcname: cname (signature cdef) = C).
  { eapply find_class_cname_consistent; eauto. }
  unfold constructor_sig_lookup in Hctor_lookup.
  unfold constructor_def_lookup in Hctor_lookup.
  rewrite Hfind_class in Hctor_lookup.
  injection Hctor_lookup as Hctor_eq.
  subst ctor.
  simpl.
  repeat split.
  - rewrite Hcname in Hcparams. symmetry. exact Hcparams.
  - rewrite Hcollect_fields. constructor.
  - exists (@nil field_def).
  split.
  -- rewrite Hcname in H2341. exact H2341.
  -- split.
  + rewrite Hcollect_fields. reflexivity.
  + rewrite Hcollect_fields. constructor.
  -

  destruct H2 as [Hwf_ctor _].
  assert (C0 = C) by (unfold C0; eapply find_class_cname_consistent; eauto).
  subst C0.
  unfold constructor_sig_lookup in Hctor_lookup.
  unfold constructor_def_lookup in Hctor_lookup.
  rewrite Hfind_class in Hctor_lookup.
  injection Hctor_lookup as Hctor_eq.
  rewrite <- Hctor_eq.
  fold bod.
  rewrite <- H0.
  exact Hwf_ctor.
Qed.

Lemma eval_stmt_preserves_heap_domain_simple : forall CT rΓ h stmt rΓ' h',
  eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h' ->
  dom h <= dom h'.
Proof.
  intros CT rΓ h stmt rΓ' h' Heval.
  remember OK as ok.
  induction Heval; try reflexivity; try discriminate.
  - (* FldWrite: h' = update_field h lx f v2 *)
    rewrite H3.
    unfold update_field.
    rewrite H0.
    rewrite update_length.
    reflexivity.
  - (* New: h' = h ++ [new_obj] *)
    rewrite H4.
    rewrite length_app.
    simpl.
    lia.
  - (* Call: use IH *)
    apply IHHeval. reflexivity.
  - (* Seq: transitivity *)
    apply Nat.le_trans with (dom h').
    + apply IHHeval1. reflexivity.
    + apply IHHeval2. reflexivity.
Qed.

Lemma runtime_getObj_app_left : forall h h_ext loc obj,
  loc < dom h ->
  runtime_getObj h loc = Some obj ->
  runtime_getObj (h ++ [h_ext]) loc = Some obj.
Proof.
  intros h h_ext loc obj Hloc_dom Hobj.
  unfold runtime_getObj in *.
  rewrite nth_error_app1.
  - exact Hloc_dom.
  - exact Hobj.
Qed.

(* Not just length, there is no statement can do strong update. *)
Lemma eval_stmt_preserves_r_type : 
  forall CT rΓ h stmt rΓ' h' loc rqt,
    eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h' ->
    r_type h loc = Some rqt ->
    loc < dom h ->
    r_type h' loc = Some rqt.
Proof.
  intros CT rΓ h stmt rΓ' h' loc rqt Heval Hrtype Hloc_dom.
  remember OK as ok.
  induction Heval; try discriminate; try (subst; exact Hrtype).
  - (* FldWrite: only fields change, not type *)
    subst h'.
    unfold r_type in Hrtype |- *.
    unfold update_field.
    destruct (runtime_getObj h loc_x) as [ox|] eqn:Hlx; [|exact Hrtype].
    destruct (Nat.eq_dec loc loc_x) as [Heq|Hneq].
    + (* loc = lx: type preserved *)
      subst loc.
      rewrite runtime_getObj_update_same.
      * apply runtime_getObj_dom in Hlx. exact Hlx.
      * simpl. unfold r_type in Hrtype.
        rewrite Hlx in Hrtype. exact Hrtype.
    + (* loc ≠ lx: unchanged *)
      rewrite runtime_getObj_update_diff.
      * symmetry. exact Hneq.
      * exact Hrtype.
  - (* New: existing objects unchanged *)
    subst h'.
    unfold r_type in Hrtype |- *.
    destruct (runtime_getObj h loc) as [obj_loc|] eqn:Hobj_loc; [|discriminate].
    injection Hrtype as Hrtype_eq.
    subst rqt.
    erewrite runtime_getObj_app_left; eauto.
  - (* Call: use IH *)
    eapply IHHeval; eauto.
  - (* Seq: transitivity *)
    assert (Hloc_dom' : loc < dom h').
    {
      have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓ h s1 rΓ' h' Heval1.
      lia.
    }
    assert (Hrtype' : r_type h' loc = Some rqt).
    {
      eapply IHHeval1; eauto.
    }
    eapply IHHeval2; eauto.
Qed.

Lemma eval_stmt_preserves_r_muttype : 
  forall CT rΓ h stmt rΓ' h' loc q,
    eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h' ->
    r_muttype h loc = Some q ->
    loc < dom h ->
    r_muttype h' loc = Some q.
Proof.
  intros CT rΓ h stmt rΓ' h' loc q Heval Hmut Hloc_dom.
  remember OK as ok.
  induction Heval; try discriminate; try (subst; exact Hmut).
  - (* FldWrite: only fields change, not mutability type *)
    subst h'.
    unfold update_field.
    destruct (runtime_getObj h loc_x) as [ox|] eqn:Hlx; [|exact Hmut].
    destruct (Nat.eq_dec loc loc_x) as [Heq|Hneq].
    + (* loc = lx: mutability type preserved *)
      subst loc.
      unfold r_muttype in Hmut |- *.
      unfold update_field.
      injection H0 as H0_eq.
      subst ox.
      rewrite runtime_getObj_update_same.
      * exact Hloc_dom.
      * simpl. rewrite Hlx in Hmut. exact Hmut.
    + (* loc ≠ lx: unchanged *)
      unfold r_muttype in Hmut |- *.
      unfold update_field.
      injection H0 as H0_eq.
      subst ox.
      rewrite runtime_getObj_update_diff.
      * symmetry. exact Hneq.
      * exact Hmut.
  - (* New: existing objects unchanged *)
    subst h'.
    destruct (runtime_getObj h loc) as [obj_loc|] eqn:Hobj_loc.
    2:{
      unfold r_muttype in Hmut.
      rewrite Hobj_loc in Hmut.
        discriminate Hmut.
    }
    unfold r_muttype in Hmut |- *.
    rewrite Hobj_loc in Hmut.
    injection Hmut as Hmut_eq.
    subst q.
    erewrite runtime_getObj_app_left; eauto.
  - (* Call: use IH *)
    eapply IHHeval; eauto.
  - (* Seq: transitivity *)
    assert (Hloc_dom' : loc < dom h').
    {
      have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓ h s1 rΓ' h' Heval1.
      lia.
    }
    assert (Hmut' : r_muttype h' loc = Some q).
    {
      eapply IHHeval1; eauto.
    }
    eapply IHHeval2; eauto.
Qed.

Lemma wf_r_typable_env_independent : forall CT rΓ1 rΓ2 h loc qt l qcontext,
  get_this_var_mapping (vars rΓ1) = Some l ->
  get_this_var_mapping (vars rΓ1) = get_this_var_mapping (vars rΓ2) ->
  r_muttype h l = Some qcontext ->
  wf_r_typable CT rΓ1 h loc qt qcontext->
  wf_r_typable CT rΓ2 h loc qt qcontext.
Proof.
  intros CT rΓ1 rΓ2 h loc qt l qcontext Hreceiveraddr Henvsame Hreceiverrmut Hsame_this.
  unfold wf_r_typable in *.
  destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
  (* rewrite <- Hsame_this. *)
  (* destruct (get_this_var_mapping (vars rΓ1)) as [ι'|] eqn:Hthis; [|contradiction]. *)
  (* destruct (r_muttype h ι') as [q|] eqn:Hmut; [|contradiction]. *)
  exact Hsame_this.
Qed.

Lemma r_basetype_in_dom : forall CT h loc cy,
  wf_heap CT h->
  r_basetype h loc = Some cy ->
  cy < dom CT.
Proof.
  intros CT h loc cy Hwf_heap Hr_basetype.
  unfold r_basetype in Hr_basetype.
  destruct (runtime_getObj h loc) as [obj|] eqn:Hobj; [|discriminate].
  injection Hr_basetype as Heq.
  subst cy.
  destruct obj as [rt_obj fields_obj].
  destruct rt_obj as [rq_obj rc_obj].
  simpl.
  unfold wf_heap in Hwf_heap.
  assert (Hloc_dom : loc < dom h) by (apply runtime_getObj_dom in Hobj; exact Hobj).
  specialize (Hwf_heap loc Hloc_dom).
  unfold wf_obj in Hwf_heap.
  rewrite Hobj in Hwf_heap.
  destruct Hwf_heap as [Hwf_rtypeuse _].
  unfold wf_rtypeuse in Hwf_rtypeuse.
  simpl in Hwf_rtypeuse.
  destruct (bound CT rc_obj) as [qc|] eqn:Hbound.
  - destruct Hwf_rtypeuse as [Hwf_rtypeuse _]. exact Hwf_rtypeuse.
  - contradiction.
Qed.

Lemma tt2qq : forall T1 T2, 
  exists T3,
    vpa_mutabilty_tt T1 T2 = T3 ->
    vpa_mutabilty_qq (sqtype T1) (sqtype T2) = sqtype T3.
Proof.
  intros T1 T2.
  (* Take T3 to be the result of vpa_mutabilty_tt *)
  exists (vpa_mutabilty_tt T1 T2).
  intros Htt.
  (* subst T3. *)
  (* Now both sides are functions of sqtype T1 and sqtype T2 *)
  unfold vpa_mutabilty_tt, vpa_mutabilty_qq.
  destruct T1 as [q1 c1].
  destruct T2 as [q2 c2].
  simpl.
  (* Case analyze on the two qualifiers *)
  destruct q1; destruct q2; simpl; try reflexivity.
Qed.

Lemma sq_vpa_tt_eq_qq :
  forall T1 T2,
    sqtype (vpa_mutabilty_tt T1 T2)
    = vpa_mutabilty_qq (sqtype T1) (sqtype T2).
Proof.
  intros T1 T2.
  destruct T1 as [q1 c1], T2 as [q2 c2].
  unfold vpa_mutabilty_tt, vpa_mutabilty_qq.
  simpl.
  destruct q1; destruct q2; reflexivity.
Qed.

(* Lemma vpa_qualified_type_sctype : forall q T,
  sctype (vpa_qualified_type q T) = sctype T.
Proof.
  intros q T.
  unfold vpa_qualified_type.
  destruct T as [sq sc].
  simpl.
  reflexivity.
Qed. *)

Lemma collect_fields_consistent_through_runtime_static : forall CT C D fields1 fields2 f fdef1 fdef2,
  wf_class_table CT ->
  base_subtype CT C D ->
  CollectFields CT C fields1 ->
  CollectFields CT D fields2 ->
  gget fields1 f = Some fdef1 ->
  gget fields2 f = Some fdef2 ->
  fdef1 = fdef2.
Proof.
  intros CT C D fields1 fields2 f fdef1 fdef2 Hwf_ct Hsub Hcf1 Hcf2 Hget1 Hget2.
  
  (* Generalize everything that varies *)
  revert fields1 fields2 f fdef1 fdef2 Hcf1 Hcf2 Hget1 Hget2.
  
  (* Now induct on Hsub *)
  induction Hsub; intros fields1 fields2 f fdef1 fdef2 Hcf1 Hcf2 Hget1 Hget2.
  
  - (* Reflexive: C = D *)
    assert (fields1 = fields2) by (eapply collect_fields_deterministic_rel; eauto).
    subst fields2.
    congruence.
    
  - (* Transitive: C <: D <: E *)
    (* Get fields for D *)
    assert (Hexists_D : exists fields_D, CollectFields CT D fields_D).
    { 
      (* D must be in CT domain since D <: E *)
      assert (HD_dom : D < dom CT).
      {
        eapply base_subtype_domain; eauto.
      }
      (* Use collect_fields_exists *)
      eapply collect_fields_exists; eauto.
    }
    destruct Hexists_D as [fields_D HcfD].
    
    (* Get field at f in D *)
    assert (Hget_D : exists fdef_D, gget fields_D f = Some fdef_D).
    {
      assert (Hlookup_E : FieldLookup CT E f fdef2).
      { apply FL_Found with fields2; auto. }
      assert (Hlookup_D : FieldLookup CT D f fdef2).
      { apply (field_inheritance_subtyping CT D E f fdef2); auto. }
      inversion Hlookup_D as [? ? fields_D' ? ? HcfD' HgetD'].
      assert (fields_D = fields_D') by (eapply collect_fields_deterministic_rel; eauto).
      subst fields_D'.
      exists fdef2.
      exact HgetD'.
    }
    destruct Hget_D as [fdef_D HgetD].
    
    (* Apply IH1: C <: D *)
    assert (fdef1 = fdef_D) by (eapply IHHsub1; eauto).
    
    (* Apply IH2: D <: E *)
    assert (fdef_D = fdef2) by (eapply IHHsub2; eauto).
    
    congruence.
    -
    assert (Hlookup1 : FieldLookup CT C f fdef1).
    { apply FL_Found with fields1; auto. }
    assert (Hlookup2 : FieldLookup CT D f fdef2).
    { apply FL_Found with fields2; auto. }
    assert (Hlookup_in_C : FieldLookup CT C f fdef2).
    { unfold parent_lookup in H1.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
    eapply field_inheritance_preserves_type; eauto.
    }
    eapply field_lookup_deterministic_rel; eauto.
Qed.

Lemma sf_assignability_consistent_subtype : forall CT C D f a1 a2,
  wf_class_table CT ->
  base_subtype CT C D ->
  sf_assignability_rel CT C f a1 ->
  sf_assignability_rel CT D f a2 ->
  a1 = a2.
Proof.
  intros CT C D f a1 a2 Hwf_ct Hsub Ha1 Ha2.
  unfold sf_assignability_rel in *.
  destruct Ha1 as [fdef1 [Hlookup1 Hassign1]].
  destruct Ha2 as [fdef2 [Hlookup2 Hassign2]].
  inversion Hlookup1 as [? ? fields1 ? ? Hcf1 Hget1]; subst.
  inversion Hlookup2 as [? ? fields2 ? ? Hcf2 Hget2]; subst.
  assert (fdef1 = fdef2) by (eapply collect_fields_consistent_through_runtime_static; eauto).
  subst. congruence.
Qed.

Lemma correspondence_to_typable : forall CT sΓ rΓ h i sqt loc ι qcontext,
  get_this_var_mapping (vars rΓ) = Some ι ->
  (r_muttype h ι) = Some qcontext ->
  (forall i : nat,
   i < dom sΓ ->
   forall sqt : qualified_type,
   nth_error sΓ i = Some sqt ->
   match runtime_getVal rΓ i with
   | Some Null_a => True
   | Some (Iot loc) => wf_r_typable CT rΓ h loc sqt qcontext
   | None => False
   end) ->
  i < dom sΓ ->
  nth_error sΓ i = Some sqt ->
  runtime_getVal rΓ i = Some (Iot loc) ->
  wf_r_typable CT rΓ h loc sqt qcontext.
Proof.
  intros CT sΓ rΓ h i sqt loc ι qcontext Hreceiveraddr Hreceiverrmut Hcorr Hi Hnth Hval.
  specialize (Hcorr i Hi sqt Hnth).
  rewrite Hval in Hcorr.
  exact Hcorr.
Qed.

Lemma typable_to_base_and_qualifier : forall CT rΓ h loc sqt rq_obj rc_obj ι qcontext,
  get_this_var_mapping (vars rΓ) = Some ι ->
  r_muttype h ι = Some qcontext ->
  wf_r_typable CT rΓ h loc sqt qcontext ->
  r_type h loc = Some {| rqtype := rq_obj; rctype := rc_obj |} ->
  base_subtype CT rc_obj (sctype sqt) /\
  qualifier_typable_context rq_obj (  (sqtype sqt)) qcontext.
Proof.
  intros CT rΓ h loc sqt rq_obj rc_obj ι qcontext Hreceiveraddr Hreceiverrmut Hwf_typable Hrtype.
  unfold wf_r_typable in Hwf_typable.
  rewrite Hrtype in Hwf_typable.
  exact Hwf_typable.
Qed.

Lemma qualifier_typable_subtype_receiver : forall rq Ty1 Ty2 qcontext,
  qualifier_typable_context rq (sqtype Ty1) qcontext ->
  sqtype Ty1 ⊑ sqtype Ty2 ->
  qualifier_typable_context rq (sqtype Ty2) qcontext.
Proof.
  intros rq Ty1 Ty2 qcontext Hqual_ty1 Hsubtype.
  unfold qualifier_typable_context in *.
  destruct rq as [|]; destruct (sqtype Ty1); destruct (sqtype Ty2);
  simpl in *; auto;
  try (inversion Hsubtype; auto);
  try unfold vpa_mutabilty_rs in *;
  try destruct qcontext;
  try reflexivity;
  try easy.
Qed.

Lemma gget_method_in : forall methods m mdef,
  gget_method methods m = Some mdef ->
  In mdef methods.
Proof.
  intros methods m mdef Hget.
  unfold gget_method in Hget.
  apply find_some in Hget.
  destruct Hget as [Hin _].
  exact Hin.
Qed.

Lemma gget_method_in_iff : forall methods m mdef,
  NoDup (map (fun mdef => mname (msignature mdef)) methods) ->
  (gget_method methods m = Some mdef <-> 
   In mdef methods /\ mname (msignature mdef) = m).
Proof.
  intros methods m mdef Hnodup.
  split.
  - (* gget_method -> In /\ name match *)
    intro Hget.
    split.
    + eapply gget_method_in; eauto.
    + eapply gget_method_name_consistent; eauto.
  - (* In /\ name match -> gget_method *)
    intros [Hin Hname].
    eapply In_gget_method_unique; eauto.
Qed.

Lemma qualifier_typable_trans_subtype : forall rq T1 T2 T3 qcontext,
  qualifier_typable_context rq (sqtype T1) qcontext ->
  sqtype T1 ⊑ sqtype T2 ->
  sqtype T2 ⊑ sqtype T3 ->
  qualifier_typable_context rq (sqtype T3) qcontext.
Proof.
  intros rq T1 T2 T3 qcontext Hqual H12 H23.
  eapply qualifier_typable_subtype_receiver; [|exact H23].
  eapply qualifier_typable_subtype_receiver; [exact Hqual|exact H12].
Qed.

Lemma Forall2_from_nth : forall {A B} (P : A -> B -> Prop) l1 l2,
  List.length l1 = List.length l2 ->
  (forall i a b, i < List.length l1 -> nth_error l1 i = Some a -> nth_error l2 i = Some b -> P a b) ->
  Forall2 P l1 l2.
Proof.
  intros A B P l1 l2 Hlen Hprop.
  generalize dependent l2.
  induction l1 as [|a1 l1' IH]; intros l2 Hlen Hprop.
  - (* Base case: l1 = [] *)
    destruct l2; [constructor | discriminate].
  - (* Inductive case: l1 = a1 :: l1' *)
    destruct l2 as [|a2 l2']; [discriminate|].
    constructor.
    + (* Show P a1 a2 *)
        specialize (Hprop 0 a1 a2).
  apply Hprop.
  -- simpl. lia.
  -- reflexivity.
  -- reflexivity.
    + (* Show Forall2 P l1' l2' *)
      apply IH.
      * simpl in Hlen. lia.
      * intros i a b Hi Ha Hb.
        apply Hprop with (S i); [simpl; lia | exact Ha | exact Hb].
Qed.

Lemma get_this_var_mapping_update_nonzero : forall vs x v,
  x <> 0 ->
  get_this_var_mapping (update x v vs) = get_this_var_mapping vs.
Proof.
  intros vs x v Hx.
  unfold get_this_var_mapping.
  destruct vs as [|v0 vs']; simpl.
  - (* vs = [] *)
    destruct x as [|x']; [contradiction|].
    simpl. reflexivity.
  - (* vs = v0 :: vs' *)
    destruct x as [|x']; [contradiction|].
    simpl. reflexivity.
Qed.

Lemma get_this_var_mapping_update_vars_nonzero : forall rΓ x v,
  x <> 0 ->
  get_this_var_mapping (vars (rΓ <| vars := update x v (vars rΓ) |>))
  = get_this_var_mapping (vars rΓ).
Proof.
  intros rΓ x v Hx.
  simpl.
  apply get_this_var_mapping_update_nonzero.
  exact Hx.
Qed.

Lemma eval_stmt_preserves_receiver_addr_typed :
  forall CT sΓ rΓ h stmt sΓ' rΓ' h' ι,
    stmt_typing CT sΓ stmt sΓ' ->
    eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h' ->
    get_this_var_mapping (vars rΓ) = Some ι ->
    get_this_var_mapping (vars rΓ') = Some ι.
Proof.
  intros CT sΓ rΓ h stmt sΓ' rΓ' h' ι Htyp Heval Hthis.
  remember OK as ok eqn:Hok.
  revert sΓ sΓ' Htyp Hthis.
  induction Heval; intros sΓ sΓ' Htyp Hthis; subst; try discriminate;
    inversion Htyp; subst; simpl in *.
  - (* Skip *)
    assumption.
  - (* Local: vars rΓ' = vars rΓ ++ [Null_a] *)
    (* record-update on rΓ: vars-projection just adds at the tail *)
    simpl.
    unfold get_this_var_mapping in *.
    destruct (vars rΓ) as [|v0 vs]; [discriminate|].
    (* head unchanged *)
    assumption.
  - (* VarAss x e *)
    simpl.
    destruct x as [|x']; simpl in *.
    + 
      exfalso.
      (* from the typing rule: x <> 0 *)
      easy.
    + (* x = S x' *)
      destruct (vars rΓ) as [|h0 l'] eqn:Hvars; simpl in *.
      * (* vars rΓ = [] *)
        (* Impossible, since Hthis = Some ι *)
        unfold get_this_var_mapping in Hthis.
        simpl in Hthis.
        discriminate.
      * (* vars rΓ = h0 :: l' *)
        exact Hthis.
  - (* FldWrite *)
    (* only heap changes, vars unchanged *)
    assumption.
  - (* New x q c ys *)
    simpl.
    destruct x as [|x']; simpl in *.
    + (* x = 0 is forbidden by typing (H10 : x <> 0) *)
      exfalso. easy.
    + (* non-zero index update does not change 'this' *)
      destruct (vars rΓ) as [|h0 l'] eqn:Hvars; simpl in *.
      * (* vars rΓ = [] *)
        (* Impossible, since Hthis = Some ι *)
        unfold get_this_var_mapping in Hthis.
        simpl in Hthis.
        discriminate.
      * (* vars rΓ = h0 :: l' *)
        exact Hthis.
  - (* Call x m y zs *)
    simpl.
    destruct x as [|x']; simpl in *.
    + (* x = 0 is forbidden by typing (H10 : x <> 0) *)
      exfalso. easy.
    + (* non-zero index update does not change 'this' *)
      destruct (vars rΓ) as [|h0 l'] eqn:Hvars; simpl in *.
      * (* vars rΓ = [] *)
        (* Impossible, since Hthis = Some ι *)
        unfold get_this_var_mapping in Hthis.
        simpl in Hthis.
        discriminate.
      * (* vars rΓ = h0 :: l' *)
        exact Hthis.
  - (* Seq s1 s2 *)
    eapply IHHeval2; eauto.
Qed.

Lemma eval_stmt_preserves_receiver_addr_typed_backwards :
  forall CT sΓ rΓ h stmt sΓ' rΓ' h' ι,
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ stmt sΓ' ->
    eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h' ->
    get_this_var_mapping (vars rΓ') = Some ι ->
    get_this_var_mapping (vars rΓ) = Some ι.
Proof.
  intros CT sΓ rΓ h stmt sΓ' rΓ' h' ι Hwf Htyp Heval Hthis'.
  (* get some initial receiver address ι0 *)
  assert (Hthis : exists ι0, get_this_var_mapping (vars rΓ) = Some ι0).
  { 
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [Hrenv _]]].
    destruct Hrenv as [Hlen [Hreceiverval _]].
    destruct Hreceiverval as [ι0 Hthis0].
    exists ι0.
    destruct Hthis0 as [Hthis0 Hthisldom].
    exact Hthis0.
  }
  destruct Hthis as [ι0 Hthis0].
  (* forward preservation gives 'ι0' also at the end *)
  pose proof (eval_stmt_preserves_receiver_addr_typed
                CT sΓ rΓ h stmt sΓ' rΓ' h' ι0
                Htyp Heval Hthis0) as Hthis0'.
  (* uniqueness of Some _ *)
  rewrite Hthis' in Hthis0'.
  inversion Hthis0'; subst ι0.
  assumption.
Qed.

Lemma eval_stmt_preserves_receiver_addr_mapping_eq :
  forall CT sΓ rΓ h stmt sΓ' rΓ' h',
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ stmt sΓ' ->
    eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h' ->
    get_this_var_mapping (vars rΓ) =
    get_this_var_mapping (vars rΓ').
Proof.
  intros CT sΓ rΓ h stmt sΓ' rΓ' h' Hwf Htyp Heval.
  (* get some initial receiver address ι₀ from wf_r_config *)
  assert (Hthis : exists ι0, get_this_var_mapping (vars rΓ) = Some ι0).
  { 
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [Hrenv _]]].
    destruct Hrenv as [Hlen [Hreceiverval _]].
    destruct Hreceiverval as [ι0 Hthis0].
    exists ι0.
    destruct Hthis0 as [Hthis0 Hthisldom].
    exact Hthis0.
  }
  destruct Hthis as [ι0 Hthis0].
  pose proof (eval_stmt_preserves_receiver_addr_typed
                CT sΓ rΓ h stmt sΓ' rΓ' h' ι0
                Htyp Heval Hthis0) as Hthis0'.
  rewrite Hthis0.
  symmetry.
  exact Hthis0'.
Qed.

Corollary eval_stmt_preserves_receiver_addr_eq_loc' :
  forall CT sΓ rΓ h stmt sΓ' rΓ' h' ι1 ι2,
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ stmt sΓ' ->
    eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h' ->
    get_this_var_mapping (vars rΓ)  = Some ι1 ->
    get_this_var_mapping (vars rΓ') = Some ι2 ->
    ι1 = ι2.
Proof.
  intros CT sΓ rΓ h stmt sΓ' rΓ' h' ι1 ι2
         Hwf Htyp Heval Hthis1 Hthis2.
  pose proof (eval_stmt_preserves_receiver_addr_mapping_eq
               CT sΓ rΓ h stmt sΓ' rΓ' h' Hwf Htyp Heval) as Heq.
  rewrite Hthis1 in Heq.
  rewrite Hthis2 in Heq.
  inversion Heq; reflexivity.
Qed.

Lemma eval_stmt_preserves_receiver_r_type_typed :
  forall CT sΓ rΓ h stmt sΓ' rΓ' h' ι rqt,
    stmt_typing CT sΓ stmt sΓ' ->
    eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h' ->
    get_this_var_mapping (vars rΓ) = Some ι ->
    r_type h ι = Some rqt ->
    ι < dom h ->
    r_type h' ι = Some rqt.
Proof.
  intros CT sΓ rΓ h stmt sΓ' rΓ' h' ι rqt Htyp Heval Hthis Hrtype Hι_dom.
  (* receiver address is preserved *)
  pose proof (eval_stmt_preserves_receiver_addr_typed
                CT sΓ rΓ h stmt sΓ' rΓ' h' ι
                Htyp Heval Hthis) as Hthis'.
  (* heap domain grows *)
  pose proof (eval_stmt_preserves_heap_domain_simple CT rΓ h stmt rΓ' h' Heval)
    as Hdom_le.
  assert (Hι_dom' : ι < dom h') by lia.
  (* type invariant on that fixed loc *)
  eapply eval_stmt_preserves_r_type; eauto.
Qed.

Lemma eval_stmt_preserves_receiver_r_muttype_typed :
  forall CT sΓ rΓ h stmt sΓ' rΓ' h' ι q,
    stmt_typing CT sΓ stmt sΓ' ->
    eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h' ->
    get_this_var_mapping (vars rΓ) = Some ι ->
    r_muttype h ι = Some q ->
    ι < dom h ->
    r_muttype h' ι = Some q.
Proof.
  intros CT sΓ rΓ h stmt sΓ' rΓ' h' ι q Htyp Heval Hthis Hmut Hι_dom.
  (* receiver address is preserved *)
  pose proof (eval_stmt_preserves_receiver_addr_typed
                CT sΓ rΓ h stmt sΓ' rΓ' h' ι
                Htyp Heval Hthis) as Hthis'.
  (* heap domain grows *)
  pose proof (eval_stmt_preserves_heap_domain_simple CT rΓ h stmt rΓ' h' Heval)
    as Hdom_le.
  assert (Hι_dom' : ι < dom h') by lia.
  (* mutability invariant on that fixed loc *)
  eapply eval_stmt_preserves_r_muttype; eauto.
Qed.

Lemma eval_stmt_preserves_r_type_backwards : 
  forall CT rΓ h stmt rΓ' h' loc rqt,
    eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h' ->
    r_type h' loc = Some rqt ->
    loc < dom h ->
    r_type h loc = Some rqt.
Proof.
  intros CT rΓ h stmt rΓ' h' loc rqt Heval Hrtype' Hloc_dom.
  (* Case on r_type h loc *)
  destruct (r_type h loc) as [rqt0|] eqn:Hrtype0.
  - (* Some rqt0; use forward lemma and equality *)
    specialize (eval_stmt_preserves_r_type CT rΓ h stmt rΓ' h' loc rqt0 Heval Hrtype0 Hloc_dom)
      as Hforward.
    rewrite Hforward in Hrtype'.
    inversion Hrtype'; subst rqt0.
    assumption.
  - (* None: impossible, because then no obj at loc in h but there is one in h' *)
    unfold r_type in Hrtype0.
    destruct (runtime_getObj h loc) as [o|] eqn:Hobj; [discriminate|].
    exfalso.
    apply runtime_getObj_not_dom in Hobj.
    lia.
Qed.

Lemma eval_stmt_preserves_receiver_r_type_typed_backwards :
  forall CT sΓ rΓ h stmt sΓ' rΓ' h' ι rqt,
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ stmt sΓ' ->
    eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h' ->
    get_this_var_mapping (vars rΓ') = Some ι ->
    r_type h' ι = Some rqt ->
    ι < dom h ->
    r_type h ι = Some rqt.
Proof.
  intros CT sΓ rΓ h stmt sΓ' rΓ' h' ι rqt
         Hwf Htyp Heval Hthis' Hrtype' Hι_dom.
  (* get initial receiver address ι0 from wf_r_config *)
  assert (Hthis : exists ι0, get_this_var_mapping (vars rΓ) = Some ι0).
  { 
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [Hrenv _]]].
    destruct Hrenv as [Hlen [Hreceiverval _]].
    destruct Hreceiverval as [ι0 Hthis0].
    exists ι0.
    destruct Hthis0 as [Hthis0 Hthisldom].
    exact Hthis0.
  }
  destruct Hthis as [ι0 Hthis0].
  (* receiver addr is preserved forward, so at end we also have ι0 *)
  pose proof (eval_stmt_preserves_receiver_addr_typed
                CT sΓ rΓ h stmt sΓ' rΓ' h' ι0
                Htyp Heval Hthis0) as Hthis0'.
  rewrite Hthis' in Hthis0'.
  inversion Hthis0'; subst ι0.
  (* now ι is same initial receiver; apply backward r_type lemma *)
  eapply eval_stmt_preserves_r_type_backwards; eauto.
Qed.

Lemma eval_stmt_preserves_r_muttype_backwards : 
  forall CT rΓ h stmt rΓ' h' loc q,
    eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h' ->
    r_muttype h' loc = Some q ->
    loc < dom h ->
    r_muttype h loc = Some q.
Proof.
  intros CT rΓ h stmt rΓ' h' loc q Heval Hmut' Hloc_dom.
  destruct (r_muttype h loc) as [q0|] eqn:Hmut0.
  - specialize (eval_stmt_preserves_r_muttype CT rΓ h stmt rΓ' h' loc q0
               Heval Hmut0 Hloc_dom) as Hforward.
    rewrite Hforward in Hmut'.
    inversion Hmut'; subst q0.
    assumption.
  - unfold r_muttype in Hmut0.
    destruct (runtime_getObj h loc) as [o|] eqn:Hobj; [discriminate|].
    exfalso.
    apply runtime_getObj_not_dom in Hobj.
    lia.
Qed.

Lemma eval_stmt_preserves_receiver_r_muttype_typed_backwards :
  forall CT sΓ rΓ h stmt sΓ' rΓ' h' ι q,
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ stmt sΓ' ->
    eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h' ->
    get_this_var_mapping (vars rΓ') = Some ι ->
    r_muttype h' ι = Some q ->
    ι < dom h ->
    r_muttype h ι = Some q.
Proof.
  intros CT sΓ rΓ h stmt sΓ' rΓ' h' ι q
         Hwf Htyp Heval Hthis' Hmut' Hι_dom.
  (* same receiver address argument as in type lemma *)
  assert (Hthis : exists ι0, get_this_var_mapping (vars rΓ) = Some ι0).
  { 
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [Hrenv _]]].
    destruct Hrenv as [Hlen [Hreceiverval _]].
    destruct Hreceiverval as [ι0 Hthis0].
    exists ι0.
    destruct Hthis0 as [Hthis0 Hthisldom].
    exact Hthis0.
  }
  destruct Hthis as [ι0 Hthis0].
  pose proof (eval_stmt_preserves_receiver_addr_typed
                CT sΓ rΓ h stmt sΓ' rΓ' h' ι0
                Htyp Heval Hthis0) as Hthis0'.
  rewrite Hthis' in Hthis0'.
  inversion Hthis0'; subst ι0.
  eapply eval_stmt_preserves_r_muttype_backwards; eauto.
Qed.

Lemma preservation_skip :
  forall CT sΓ rΓ h sΓ',
    stmt_typing CT sΓ SSkip sΓ' ->
    wf_r_config CT sΓ rΓ h ->
    wf_r_config CT sΓ' rΓ h.
Proof.
  intros CT sΓ rΓ h sΓ' Htyping Hwf.
  inversion Htyping; subst; exact Hwf.
Qed.

Lemma preservation_local_ok :
  forall CT sΓ rΓ h T x sΓ',
    OK = OK ->
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ (SLocal T x) sΓ' ->
    runtime_getVal rΓ x = None ->
    wf_r_config CT sΓ' (rΓ <| vars := vars rΓ ++ [Null_a] |>) h.
Proof.
    intros CT sΓ rΓ h T rΓ' h' sΓ' Hwf Htyping Heval.
    inversion Htyping; subst.
    unfold wf_r_config in *.
    destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) 
    unfold  wf_class_table in Hclass. destruct Hclass as [Hclass _]. exact Hclass.
    + (* Object wellformedness *)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [Hobject _]]. exact Hobject.
    + (* All other classes have super class*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[Hotherclasses _]]]. exact Hotherclasses.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
    + (* wellformed heap *) exact Hheap.
    + (* Length of runtime environment greater than 0 *)
    simpl. rewrite length_app. simpl. lia.
    + (* The first element of runtime environment is not null *)
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      destruct Hreceiverval as [iot Hiot].
      exists iot.
      simpl.
      unfold gget in *.
      destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
      * (* Case: vars rΓ = [] *)
        exfalso.
        (* rewrite Hvars in HrEnvLen. *)
        simpl in HrEnvLen.
        lia.
      * (* Case: vars rΓ = v0 :: vs *)
        simpl.
        exact Hiot.
    + (* wellformed runtime environment *)  
    unfold wf_renv in *.
    simpl.
    apply Forall_app.
    split.
    * destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]]. exact Hallvals.
    * constructor.
      -- trivial.
      -- constructor.  
    + (* Length of static environment greater than 0 *)
    destruct Hsenv as [HsenvLength HsenvWellTyped]. rewrite length_app.
    simpl. lia.
    + (* wellformed static environment *)
      unfold wf_senv in *. apply Forall_app. split.
      * destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvWellTyped.
      *
        constructor.
        -- exact H2. (* assuming H is the wellformedness of T *)
        -- constructor. (* empty tail is well-typed *)
    + (* length equality *)
      simpl. rewrite length_app. simpl. rewrite Hlen. rewrite length_app. simpl. lia.
    + (* correspondence between static and runtime environments *)
      intros ι qcontext HreceiverAddr Hreceivermut i Hi sqt Hnth.
      destruct (Nat.eq_dec i (dom sΓ)) as [Heq | Hneq].
      * (* Case: i = dom sΓ (new variable) *)
        subst i.
        unfold runtime_getVal.
        simpl.
        rewrite nth_error_app2.
        -- rewrite Hlen.
           trivial.
        -- rewrite Hlen.
           assert (dom (vars rΓ) - dom (vars rΓ) = 0) by lia.
            rewrite H.
            simpl.
            trivial.
      * (* Case: i < dom sΓ (existing variable) *)
        assert (Hi_old : i < dom sΓ).
        {
          simpl in Hi. rewrite length_app in Hi. simpl in Hi.
          lia.
        }
        assert (Hnth_old : nth_error sΓ i = Some sqt).
        {
          have Happ := nth_error_app1 sΓ [T] Hi_old.
          rewrite Happ in Hnth.
          exact Hnth.
        }
        rewrite (get_this_var_mapping_update_vars_app_null rΓ) in HreceiverAddr.
        specialize (Hcorr ι qcontext HreceiverAddr Hreceivermut i Hi_old sqt Hnth_old).
        unfold runtime_getVal in *.
        simpl.
        rewrite nth_error_app1.
        -- rewrite <- Hlen. exact Hi_old.
        --
           destruct (nth_error (vars rΓ) i) as [v|] eqn:Hgetval.
           ++ (* Case: nth_error (vars rΓ) i = Some v *)
              destruct v as [|loc].
              ** trivial.
              ** unfold wf_r_typable in *. simpl.
              assert (get_this_var_mapping (vars rΓ ++ [Null_a]) = get_this_var_mapping (vars rΓ)).
              {
                unfold get_this_var_mapping.
                destruct (vars rΓ) as [|v0 vs]; reflexivity.
              }
              (* rewrite H0. *)
              exact Hcorr.
           ++ (* Case: nth_error (vars rΓ) i = None *)
              exfalso.
              apply nth_error_None in Hgetval.
              rewrite <- Hlen in Hgetval.
              lia.
Qed.

Lemma preservation_varass_ok :
  forall P CT sΓ rΓ h x e v2 sΓ',
    OK = OK ->
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ (SVarAss x e) sΓ' ->
    eval_expr OK P CT rΓ h e v2 OK P rΓ h ->
    runtime_getVal rΓ x <> None ->
    wf_r_config CT sΓ' (rΓ <| vars := update x v2 (vars rΓ) |>) h.
Proof.
    intros P CT sΓ rΓ h x e v2 sΓ' HOK Hwf Htyping Heval Hruntime_getVal.
    inversion Htyping; subst.
    have Hwfcopy := Hwf.
    revert Hwfcopy.
    unfold wf_r_config in Hwf.
    intros.
    unfold wf_r_config.
    destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) 
    unfold  wf_class_table in Hclass. destruct Hclass as [Hclass _]. exact Hclass.
    + (* Object wellformedness *)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [Hobject _]]. exact Hobject.
    + (* All other classes have super class*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[Hotherclasses _]]]. exact Hotherclasses.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
    + (* wellformed heap *) exact Hheap.
    + (* Length of runtime environment greater than 0 *)
      simpl. destruct Hsenv as [HsenvLength HsenvWellTyped].      
      rewrite update_length.
      rewrite <- Hlen.
      exact HsenvLength.
    + (* The first element of runtime environment is not null *)
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      destruct Hreceiverval as [iot Hiot].
      exists iot.
      simpl.
      unfold gget in *.
      destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
      * (* Case: vars rΓ = [] *)
        exfalso.
        (* rewrite Hvars in HrEnvLen. *)
        simpl in HrEnvLen.
        lia.
      * (* Case: vars rΓ = v0 :: vs *)
        destruct x as [|x'].
           -- (* x = 0 *) contradiction.
           -- (* x = S x' *)
              simpl. (* update (S x') v2 (v0 :: vs) = v0 :: update x' v2 vs *)
              exact Hiot.
    + (* wellformed runtime environment *)
    unfold wf_renv in *.
    destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
    simpl.
    apply Forall_update.
    * exact Hallvals.
    * destruct v2 as [|loc].
      -- trivial.
      -- inversion Heval; subst.
        (* assert (Hloc_in_vars : exists i, nth_error (vars rΓ) i = Some (Iot loc)). *)
        ++ 
        assert (Hx0_bound : x0 < dom (vars rΓ)).
        {
          apply runtime_getVal_dom in H.
          exact H.
        }
        assert (Hloc_wf : match runtime_getObj h loc with Some _ => True | None => False end).
        {
          unfold runtime_getVal in H.
          assert (Hnth_loc : nth_error (vars rΓ) x0 = Some (Iot loc)) by exact H.
          eapply Forall_nth_error in Hallvals; eauto.
          simpl in Hallvals.
          exact Hallvals.
        }
        exact Hloc_wf.
        ++ 
        assert (Hv_bound : v < dom h).
        {
          apply runtime_getVal_dom in H.
          unfold runtime_getVal in H.
          apply runtime_getObj_dom in H0.
          exact H0.
        }
        specialize (Hheap v Hv_bound).
        unfold wf_obj in Hheap.
        rewrite H0 in Hheap.
        destruct Hheap as [_ [field_defs [Hcollect [Hlen_eq Hforall2]]]].
        assert (Hf_bound : f < List.length (fields_map o)).
        {
          apply nth_error_Some.
          unfold getVal in H5.
          rewrite H5.
          discriminate.
        }
        rewrite Hlen_eq in Hf_bound.
        assert (Hfield_def : exists fdef, nth_error field_defs f = Some fdef).
        {
          apply nth_error_Some_exists.
          exact Hf_bound.
        }
        destruct Hfield_def as [fdef Hfdef].
        unfold getVal in H5.
        eapply Forall2_nth_error in Hforall2; eauto.
        simpl in Hforall2.
        destruct (runtime_getObj h loc) as [obj|] eqn:Hloc_obj.
        --- (* Case: runtime_getObj h loc = Some obj *)
          trivial.
        --- (* Case: runtime_getObj h loc = None *)
          contradiction Hforall2.
    * assert(exists v, nth_error (vars rΓ) x = Some v).
      {
        unfold runtime_getVal in Hruntime_getVal.
        apply nth_error_Some in Hruntime_getVal.
        apply nth_error_Some_exists in Hruntime_getVal.
        exact Hruntime_getVal.
      }
      destruct H as [v Hnth].
      apply runtime_getVal_dom in Hnth.
      exact Hnth.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvLength. 
    + (* wellformed static environment *)
      destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvWellTyped.
    + (* length equality *)
      simpl.
      rewrite update_length.
      exact Hlen.
    + (* correspondence between static and runtime environments *)
      intros ι qcontext HreceiverAddr Hreceivermut i Hi sqt Hnth.
      destruct (Nat.eq_dec i x) as [Heq | Hneq].
      * (* Case: i = x (updated variable) *)
        subst i.
        unfold runtime_getVal.
        simpl.
        rewrite update_same.
        rewrite <- Hlen; exact Hi.
        destruct v2 as [|loc] eqn: Hv2.
        -- (* Case: v2 = Null_a *)
          trivial.
        -- (* Case: v2 = Iot loc *)
          (* Use subtyping to convert from T to sqt *)
          assert (Hsubtype_preserved : wf_r_typable CT (rΓ <| vars := update x (Iot loc) (vars rΓ) |>) h loc sqt qcontext).
          {
            assert (Hsqt_eq : sqt = Tx).
          {
            unfold static_getType in H7.
            rewrite H7 in Hnth.
            injection Hnth as Hsqt_eq.
            symmetry. exact Hsqt_eq.
          }
          subst sqt.
          assert (H_loc_Te : wf_r_typable CT rΓ h loc Te qcontext).
          {
            (* Apply expression evaluation preservation lemma *)
            apply (expr_eval_preservation P CT sΓ' rΓ h e (Iot loc) rΓ h Te ι).
            auto.
            - rewrite get_this_var_mapping_update_vars_nonzero in HreceiverAddr. exact H4. exact HreceiverAddr.
            - exact Hreceivermut.
            - exact Hwfcopy.
            - exact H2.
            - exact Heval.
          }
          eapply wf_r_typable_subtype with (T1:=Te)(T2:=Tx); eauto.
          }
          unfold wf_r_typable in *.
          exact Hsubtype_preserved.
      * (* Case: i ≠ x (unchanged variable) *)
        {
          unfold runtime_getVal.
          simpl.
          rewrite update_diff.
          - symmetry. exact Hneq.
          -
            rewrite get_this_var_mapping_update_vars_nonzero in HreceiverAddr. exact H4.
            assert (Hcorr_orig := Hcorr ι qcontext HreceiverAddr Hreceivermut i Hi sqt Hnth).
            unfold runtime_getVal in Hcorr_orig.
            destruct (nth_error (vars rΓ) i) as [v|] eqn:Hval.
            + destruct v as [|loc].
              * trivial.
              * unfold wf_r_typable in Hcorr_orig |- *.
                destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
                exact Hcorr_orig.
            + contradiction.
        }
Qed.

Lemma get_this_exists_from_wf_r_config :
  forall CT sΓ rΓ h,
    wf_r_config CT sΓ rΓ h ->
    exists ι, get_this_var_mapping (vars rΓ) = Some ι.
Proof.
  intros CT sΓ rΓ h Hwf.
  destruct Hwf as [_ [_ [Hrenv _]]].
  destruct Hrenv as [_ [Hrecv _]].
  destruct Hrecv as [ι [Hthis _]].
  now exists ι.
Qed.

Lemma receiver_mutability_exists_wf_renv :
  forall CT rΓ h ι,
    wf_renv CT rΓ h ->
    get_this_var_mapping (vars rΓ) = Some ι ->
    exists qcontext, r_muttype h ι = Some qcontext.
Proof.
  intros CT rΓ h ι [HrLen [Hrecv Hall]] Hthis.
  unfold get_this_var_mapping in Hthis.
  destruct (vars rΓ) as [|v vs]; [discriminate|].
  destruct v as [|loc]; try discriminate.
  simpl in Hthis. inversion Hthis; subst loc.
  apply Forall_inv in Hall.
  simpl in Hall.
  destruct (runtime_getObj h ι) as [o|] eqn:Hobj; [|contradiction].
  unfold r_muttype. rewrite Hobj. eauto.
Qed.

Lemma rqtype_update_field_invariant : forall o f v,
  rqtype (rt_type (o <| fields_map := update f v (fields_map o) |>))
  = rqtype (rt_type o).
Proof.
  intros [rt fm] f v; simpl; reflexivity.
Qed.

Lemma r_muttype_update_field_preserve :
  forall h locx f v loc,
    r_muttype (update_field h locx f v) loc
  = r_muttype h loc.
Proof.
  intros h locx f v loc.
  unfold r_muttype, update_field.
  destruct (runtime_getObj h locx) as [o_x|] eqn:Hobjx.
  - destruct (Nat.eq_dec loc locx) as [Heq|Hneq].
    + subst loc.
      rewrite runtime_getObj_update_same.
      * f_equal. apply runtime_getObj_dom in Hobjx.
        exact Hobjx.
      * rewrite Hobjx.
        simpl.
        reflexivity.
    + rewrite runtime_getObj_update_diff; [symmetry; exact Hneq|].
      reflexivity.
  - reflexivity.
Qed.

Lemma preservation_fldwrite_ok :
  forall CT sΓ rΓ h x f y loc_x o vf val_y h' sΓ',
    OK = OK ->
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ (SFldWrite x f y) sΓ' ->
    runtime_getVal rΓ x = Some (Iot loc_x) ->
    runtime_getObj h loc_x = Some o ->
    getVal (fields_map o) f = Some vf ->
    runtime_getVal rΓ y = Some val_y ->
    h' = update_field h loc_x f val_y ->
    wf_r_config CT sΓ' rΓ h'.
Proof.
    intros CT sΓ rΓ h x f y loc_x o vf val_y h' sΓ'.
    intros HOK Hwf Htyping Hgetx Hgetobj Hgetf Hgety Heq_h'.
    have Hwfcopy := Hwf.
    inversion Htyping; subst.
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) 
    unfold  wf_class_table in Hclass. destruct Hclass as [Hclass _]. exact Hclass.
    + (* Object wellformedness *)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [Hobject _]]. exact Hobject.
    + (* All other classes have super class*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[Hotherclasses _]]]. exact Hotherclasses.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
    + (* wellformed heap *) 
    unfold wf_heap in *.
    intros ι0 Hdom.
    unfold update_field in *.
    destruct (runtime_getObj h loc_x) as [o_x|] eqn:Hobj.
    * (* Case: object exists at lx *)
      destruct (Nat.eq_dec ι0 loc_x) as [Heq | Hneq].
      -- (* Case: ι = lx (the updated object) *)
        subst ι0.
        unfold wf_obj.
        simpl.
        specialize (Hheap loc_x).
        rewrite update_length in Hdom.
        specialize (Hheap Hdom).
        unfold wf_obj in Hheap.
        rewrite Hobj in Hheap.
        destruct Hheap as [Hrtypeuse [Hlen_fields Hwf_fields]].
        unfold runtime_getObj.
        rewrite update_same.
        ++ exact Hdom.
        ++ repeat split.
          ** exact Hrtypeuse.
          ** simpl. rewrite update_length. 
          exists Hlen_fields.
          destruct Hwf_fields as [Hcollect [Hlen_eq Hforall2]].
          split.
          --- exact Hcollect.
          --- split.
            +++ exact Hlen_eq.
            +++ 
            {
              apply Forall2_update.
              eapply Forall2_impl; [|exact Hforall2].
              intros v fdef Hv_fdef.
              destruct v as [|loc]; [trivial|].
              destruct (runtime_getObj h loc) as [obj_at_loc|] eqn:Hobj_at_loc; [|contradiction Hv_fdef].
              destruct Hv_fdef as [rqt [Hrtype Hsubtype]].
              destruct (Nat.eq_dec loc loc_x) as [Heq_loc | Hneq_loc].
              (* Case: loc = lx *)
                subst loc.
                unfold update_field.
                simpl.
                rewrite update_same.
                apply runtime_getObj_dom in Hobj_at_loc.
                exact Hobj_at_loc.
                exists rqt.
                split.
              unfold r_type.
                simpl.
                rewrite runtime_getObj_update_same.
                simpl.
                apply runtime_getObj_dom in Hobj_at_loc.
                exact Hobj_at_loc.
                simpl.
                unfold r_type in Hrtype.
                rewrite Hobj_at_loc in Hrtype.
                injection Hrtype as Hrqt_eq.
                rewrite Hobj in Hobj_at_loc.
                injection Hobj_at_loc as Heq_objs.
                subst obj_at_loc.
                rewrite Hrqt_eq.
                reflexivity.
              exact Hsubtype.

              (* Case: loc ≠ lx *)
              rewrite update_diff; [symmetry; exact Hneq_loc |].
              unfold runtime_getObj in Hobj_at_loc.
              rewrite Hobj_at_loc.
              exists rqt.
              split.
              unfold r_type.
                rewrite runtime_getObj_update_diff; [symmetry; exact Hneq_loc|].
                unfold r_type in Hrtype.
                exact Hrtype.
              exact Hsubtype.
              assert (Hf_valid : f < dom (fields_map o_x)).
              {
                injection Hgetobj as Ho_eq. subst o_x.
                apply getVal_dom in Hgetf. exact Hgetf.
              }
              rewrite <- Hlen_eq. exact Hf_valid.

              intros b Hnth_b.
              destruct val_y as [|loc_y]; [trivial|].

              assert (Hx_dom : x < dom sΓ').
              {
                apply static_getType_dom in H3. exact H3.
              }

              assert (Hy_dom : y < dom sΓ').
              {
                apply static_getType_dom in H4. exact H4.
              }
              have Hcorrcopy := Hcorr.
              assert (exists ι, get_this_var_mapping (vars rΓ) = Some ι).
              {
                eapply get_this_exists_from_wf_r_config; eauto.
              }
              destruct H as [ι HreceiverAddr].
              assert (exists qcontext, r_muttype h ι = Some qcontext).
              {
                eapply receiver_mutability_exists_wf_renv; eauto.
              }
              destruct H as [qcontext Hreceivermut].
              have Hcorropy := Hcorr.
              specialize (Hcorr ι qcontext HreceiverAddr Hreceivermut x Hx_dom Tx H3).
              destruct (runtime_getVal rΓ x) as [val_x|] eqn:Hx_val; [|contradiction].
              injection Hgetx as H_val_eq.
              subst val_x.
              unfold update_field.
              destruct (runtime_getObj h loc_x) as [o_lx|] eqn:Hobj_lx; [|easy].
              destruct (Nat.eq_dec loc_y loc_x) as [Heq_loc2_lx | Hneq_loc2_lx].
              specialize (Hcorrcopy ι qcontext HreceiverAddr Hreceivermut y Hy_dom Ty H4).
              destruct (runtime_getVal rΓ y) as [val_y|] eqn:Hy_val; [|contradiction].
              injection Hgety as H_val_eq.
              subst val_y.
              unfold update_field.
              (* subst loc_y. *)
              destruct (runtime_getObj h loc_y) as [o_ly|] eqn:Hobj_ly.
              2:{
                subst loc_y.
                rewrite Hobj_lx in Hobj_ly.
                easy.
              }
                (* Case: loc_y = loc_x *)
                subst loc_y.
                unfold runtime_getObj.
                rewrite update_same; [exact Hdom|].
                unfold wf_r_typable in Hcorr.
                destruct (r_type h loc_x) as [rqt_x|] eqn:Hrtype_x; [|contradiction Hcorr].
                destruct Hcorr as [Hbase_sub Hqual_typable].
                exists rqt_x.
                split.
                  unfold r_type.
                  unfold runtime_getObj.
                  rewrite update_same; [exact Hdom|].
                  simpl.
                  unfold r_type in Hrtype_x.
                  rewrite Hobj_lx in Hrtype_x.
                  injection Hobj as Ho_eq.
                  injection Hgetobj as Ho_eq2.
                  subst o_lx o_x.
                  exact Hrtype_x.
                  injection Hobj as Ho_lx_eq.
                  injection Hgetobj as Ho_x_eq.
                  subst o_lx o_x.
                  assert (Hrt_type_eq : rt_type o = rqt_x).
                  {
                    unfold r_type in Hrtype_x.
                    rewrite Hobj_lx in Hrtype_x.
                    injection Hrtype_x as Heq.
                    exact Heq.
                  }

                  rewrite Hrt_type_eq in Hcollect.
                  assert (fieldT = b). {
                    unfold sf_def_rel in H6.
                    inversion H6; subst.
                    symmetry.
                    eapply collect_fields_consistent_through_runtime_static with (C:=(rctype (rt_type o)))(fields1:=Hlen_fields)(fields2:=fields)(fdef1:=b)(fdef2:=fieldT); eauto.
                  }

                  subst b.
                  (* Case: loc2 ≠ lx *)
                  rewrite Hobj_lx in Hobj_ly.
                  inversion Hobj_ly.
                  subst o_ly.
                  unfold wf_r_typable in Hcorrcopy.
                  rewrite Hrtype_x in Hcorrcopy.
                  destruct Hcorrcopy as [Hxybase Hxyqualifer].
                  {
                  constructor.
                  (* Base type *)
                  apply qualified_type_subtype_base_subtype in H11.
                  (* apply vpa_preserve_basetype_subtype in H11. *)
                  simpl in H11.
                  eapply base_trans; eauto.

                  (* Qualifier *)
                  apply get_this_qualified_type_nth_error in H5.
                  unfold wf_senv in Hsenv;
                  destruct Hsenv as [Hsenvdom _];
                  apply qualified_type_subtype_q_subtype in H11.
                  simpl in H11.
                  unfold qualifier_typable_heap.
                  move H11 at bottom.
                  move Hqual_typable at bottom.
                  unfold vpa_mutabilty_rec_fld; unfold vpa_mutabilty_stype_fld in H11.
                  subst rqt_x.

                  clear - H11 Hqual_typable Hxyqualifer.
                  all: destruct (rqtype (rt_type o)) eqn: rq;
                  destruct (mutability (ftype fieldT)) eqn: HfieldMut;
                  simpl;
                  simpl in H11; try trivial.
                  all: 
                  destruct (sqtype Tx) eqn: qx;
                  destruct (sqtype Ty) eqn: qy;
                  simpl in H11;
                  try solve_q_subtype_wrong.
                  all:
                  destruct qcontext eqn: Hqcontext;
                  try solve_qualifier_typable_wrong_concrete.
            }

            have H11copy := H11.
            apply qualified_type_subtype_q_subtype in H11. 
            destruct (nth_error h loc_y) as [obj_y|] eqn:Hnth_y.
            - (* loc_y exists in original heap *)
              assert (Hnth_updated : nth_error (update loc_x (o_x <| fields_map := update f (Iot loc_y) (fields_map o_x) |>) h) loc_y = Some obj_y).
              {
                rewrite nth_error_update_neq; [symmetry; exact Hneq_loc2_lx | exact Hnth_y].
              }
              rewrite Hnth_updated.
              specialize (Hcorrcopy ι qcontext HreceiverAddr Hreceivermut y Hy_dom Ty H4).
              rewrite Hgety in Hcorrcopy.
              unfold wf_r_typable in Hcorrcopy.
              destruct (r_type h loc_y) as [rqt_y|] eqn:Hrtype_y; [|contradiction].
              destruct Hcorrcopy as [Hbase_y Hqual_y].

              exists rqt_y.
              split.

              unfold r_type.
              unfold runtime_getObj.
              rewrite Hnth_updated.
              unfold r_type in Hrtype_y.
              unfold runtime_getObj in Hrtype_y.
              rewrite Hnth_y in Hrtype_y.
              exact Hrtype_y.
              assert (fieldT = b). {
                unfold sf_def_rel in H6.
                inversion H6; subst.
                symmetry.
                eapply collect_fields_consistent_through_runtime_static with (C:=(rctype (rt_type o_x)))(fields1:=Hlen_fields)(fields2:=fields)(fdef1:=b)(fdef2:=fieldT); eauto.
                apply qualified_type_subtype_base_subtype in H11copy.
                simpl in H11copy.
                unfold wf_r_typable in Hcorr.
                unfold r_type in Hcorr.
                rewrite Hobj_lx in Hcorr.
                destruct Hcorr as [Hbase_sub Hqual_typable].
                inversion Hobj.
                subst o_lx.
                exact Hbase_sub.
              }
              subst b.
              split.
              + (* Base type equality *)
                apply qualified_type_subtype_base_subtype in H11copy.
                (* apply vpa_preserve_basetype_subtype in H11copy. *)
                simpl in H11copy.
                eapply base_trans; eauto.
              + (* Qualifier typable *)
                apply get_this_qualified_type_nth_error in H5.
                unfold wf_senv in Hsenv;
                destruct Hsenv as [Hsenvdom _];
                move H11 at bottom.
                inversion Hlen.
                inversion Hobj.
                subst.
                unfold qualifier_typable_heap.
                unfold qualifier_typable_context in Hqual_y.
                unfold wf_r_typable in Hcorr.
                unfold r_type in Hcorr.
                rewrite Hobj_lx in Hcorr.
                destruct Hcorr as [_ Hqualifiertypablex].
                inversion Hgetobj; subst o.
                unfold vpa_mutabilty_stype_fld in H11.
                unfold vpa_mutabilty_rec_fld.
                unfold vpa_mutabilty_rs in Hqual_y.
                clear - Hqual_y H11 Hqualifiertypablex.
                all:
                destruct (rqtype rqt_y) eqn: Hrqy;
                destruct (rqtype (rt_type o_x)) eqn: Hrqx;
                destruct (mutability (ftype fieldT)) eqn: Hfield;
                try trivial.

                all:
                destruct (sqtype Ty) eqn: Hsqy;
                destruct qcontext eqn: Hqcontext;
                simpl in Hqual_y;
                try solve_q_subtype_wrong.

                all:
                destruct (sqtype Tx) eqn: Hsqx;
                simpl in H11;
                try solve_q_subtype_wrong;
                try solve_qualifier_typable_wrong_concrete.

                all: try easy.
            - (* loc_y doesn't exist - contradiction *)
              assert (Hnth_updated : nth_error (update loc_x (o_x <| fields_map := update f (Iot loc_y) (fields_map o_x) |>) h) loc_y = None).
              {
                rewrite nth_error_update_neq; [symmetry; exact Hneq_loc2_lx | exact Hnth_y].
              }
              rewrite Hnth_updated.
              exfalso.
              specialize (Hcorrcopy ι qcontext HreceiverAddr Hreceivermut y Hy_dom Ty H4).
              rewrite Hgety in Hcorrcopy.
              unfold wf_r_typable in Hcorrcopy.
              unfold r_type in Hcorrcopy.
              unfold runtime_getObj in Hcorrcopy.
              rewrite Hnth_y in Hcorrcopy.
              easy.
            }
        -- unfold wf_obj, runtime_getObj.
           rewrite update_diff.
        ** rewrite update_length in Hdom.
           symmetry. exact Hneq.
        **
        rewrite update_length in Hdom.
        destruct (nth_error h ι0) eqn:Htest.
        2:{
          exfalso.
          apply nth_error_None in Htest.
          lia.
        }
        split.
        specialize (Hheap ι0 Hdom).
        unfold wf_obj in Hheap.
        destruct (runtime_getObj h ι0) as [objl|] eqn: Hobjl; [| easy].
        destruct Hheap as [Hwfobjtypeuse _].
        unfold runtime_getObj in Hobjl.
        rewrite Htest in Hobjl.
        inversion Hobjl.
        subst.
        exact Hwfobjtypeuse.

        specialize (Hheap ι0 Hdom).
        unfold wf_obj in Hheap.
        destruct (runtime_getObj h ι0) as [objl|] eqn: Hobjl; [| easy].
        destruct Hheap as [Hwfobjtypeuse Hwfobjfields].
        unfold runtime_getObj in Hobjl.
        rewrite Htest in Hobjl.
        inversion Hobjl.
        subst.
        destruct Hwfobjfields as [field_defs [Hcollect [Hlen_eq Hforall2]]].

        exists field_defs.
        {
          split.
          exact Hcollect.
          split.
          exact Hlen_eq.
          eapply Forall2_impl; [|exact Hforall2].
          intros v fdef Hv_fdef.
          destruct v as [|loc]; [trivial|].
          (* First check if the object exists in the updated heap *)
          unfold update_field.
          destruct (runtime_getObj h loc_x) as [o_lx|] eqn:Hobj_lx.
          destruct (Nat.eq_dec loc loc_x) as [Heq | Hneq_loc].
          subst loc.
          rewrite Hobj_lx in Hv_fdef.
          destruct Hv_fdef as [rqt [Hrtype_loc Hsubtype]].
          unfold runtime_getObj.
          rewrite update_same.
          unfold r_type in Hrtype_loc.
          unfold r_type in Hrtype_loc.
          destruct (runtime_getObj h loc_x) as [oxx|] eqn:Hobj_lxx; [|discriminate Hrtype_loc].
          apply runtime_getObj_dom in Hobj_lxx.
          exact Hobj_lxx.
          exists rqt.
          split.
            unfold r_type.
            rewrite runtime_getObj_update_same.
            apply runtime_getObj_dom in Hobj_lx. exact Hobj_lx.
            simpl.
            unfold r_type in Hrtype_loc.
            rewrite Hobj_lx in Hrtype_loc.
            injection Hobj as Ho_new_eq.
            subst o_x.
            injection Hrtype_loc as Hrqt_eq.
            subst rqt.
            reflexivity.
            exact Hsubtype.

            destruct (runtime_getObj h loc) as [obj_loc|] eqn:Hobj_loc; [|contradiction Hv_fdef].
            destruct Hv_fdef as [rqt [Hrtype_loc Hsubtype]].
            unfold runtime_getObj.
            rewrite update_diff.
            symmetry. exact Hneq_loc.
            unfold runtime_getObj in Hobj_loc.
            destruct (nth_error h loc) as [obj|] eqn:Hnth_loc; [|discriminate Hobj_loc].
            injection Hobj_loc as Hobj_eq.
            subst obj.
            exists rqt.
            split.
            unfold r_type.
            rewrite runtime_getObj_update_diff.
            symmetry. exact Hneq_loc.
            exact Hrtype_loc.
            exact Hsubtype.
            exfalso.
            discriminate Hobj.
        }
        * exfalso.
          discriminate Hgetobj.
    + destruct Hrenv as [HrEnvLen [Hreceiver Hallvals]]. exact HrEnvLen.
    + destruct Hrenv as [HrEnvLen [Hreceiver Hallvals]]. destruct Hreceiver as [Hreceiverval Hreceivervaldom].
      exists Hreceiverval.
      split.
      * exact (proj1 Hreceivervaldom).
      * rewrite update_field_length.
        exact (proj2 Hreceivervaldom).
    + 
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      eapply Forall_impl; [| exact Hallvals].
      intros v Hv.
      destruct v as [|loc]; [trivial|].
      unfold update_field in Hv |- *.
      destruct (runtime_getObj h loc_x) as [o'|] eqn:Hobj'; [| exact Hv].
      destruct (Nat.eq_dec loc loc_x) as [Heq | Hneq].
      * subst loc. rewrite runtime_getObj_update_same; [trivial | ].
        apply runtime_getObj_dom in Hobj'. exact Hobj'. trivial.
      * 
      unfold runtime_getObj.
      rewrite update_diff.
      -- symmetry. exact Hneq.
      -- auto.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvLength.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. exact HsenvWellTyped.
    + exact Hlen.
    + 
    intros ι qcontext HreceiverAddr Hreceivermut i Hi sqt Hnth.
      assert (r_muttype h ι = Some qcontext) as Hreceivermut_orig.
      {
        rewrite (r_muttype_update_field_preserve h loc_x f val_y ι) in Hreceivermut.
        exact Hreceivermut.
      }
      assert (Hcorr_orig := Hcorr ι qcontext HreceiverAddr Hreceivermut_orig i Hi sqt Hnth).
      destruct (runtime_getVal rΓ i) as [v|] eqn:Hval; [|exact Hcorr_orig].
      destruct v as [|loc]; [trivial|].
      unfold wf_r_typable in Hcorr_orig |- *.
      destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
      assert (Hrtype_preserved : r_type (update_field h loc_x f val_y) loc = Some rqt).
      {
        unfold r_type.
        unfold update_field.
        remember (runtime_getObj h loc_x) as obj_result eqn:Hobj_eq.
        destruct obj_result as [o'|].
        - destruct (Nat.eq_dec loc loc_x) as [Heq | Hneq].
          + subst loc. 
            rewrite runtime_getObj_update_same.
            * simpl. unfold r_type in Hrtype.
              destruct (runtime_getObj h loc_x) as [o_lx|] eqn:Hobj_lx; [|discriminate Hrtype].
              apply runtime_getObj_dom in Hobj_lx.
              exact Hobj_lx.
            * 
            have Hobj_eq_copy := Hobj_eq.
            symmetry in Hobj_eq.
            apply runtime_getObj_dom in Hobj_eq.
            simpl.
            unfold r_type in Hrtype.
            destruct (runtime_getObj h loc_x) as [o_lx|] eqn:Hobj_lx; [|discriminate Hrtype].
            injection Hrtype as Hrtype_eq.
            rewrite <- Hrtype_eq.
            f_equal.
            injection Hobj_eq_copy as Ho_eq.
            rewrite Ho_eq.
            reflexivity.
          + rewrite runtime_getObj_update_diff.
            * symmetry. exact Hneq.
            * exact Hrtype.
        - exact Hrtype.
      }
      rewrite Hrtype_preserved.
      (* rewrite Hmut_preserved. *)
      exact Hcorr_orig. 
Qed.

Lemma r_muttype_app_preserve_old :
  forall h h_ext loc,
    loc < dom h ->
    r_muttype (h ++ [h_ext]) loc = r_muttype h loc.
Proof.
  intros h h_ext loc Hlt.
  unfold r_muttype.
  (* Since loc < dom h, the lookup in h is Some o *)
  destruct (runtime_getObj h loc) as [o|] eqn:Hobj.
  - rewrite (runtime_getObj_app_left h h_ext loc o Hlt Hobj). reflexivity.
  - (* impossible under loc < dom h *)
    exfalso.
    apply runtime_getObj_not_dom in Hobj. lia.
Qed.

Lemma r_muttype_app_preserve_old_Some :
  forall h h_ext loc q,
    loc < dom h ->
    r_muttype (h ++ [h_ext]) loc = Some q ->
    r_muttype h loc = Some q.
Proof.
  intros h h_ext loc q Hlt Hext.
  rewrite (r_muttype_app_preserve_old h h_ext loc Hlt) in Hext.
  exact Hext.
Qed.

Lemma preservation_new_ok :
  forall CT sΓ rΓ h x q_c c ys l1 qthisr vals o qadapted rΓ' h' sΓ',
    OK = OK ->
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ (SNew x q_c c ys) sΓ' ->
    runtime_getVal rΓ 0 = Some (Iot l1) ->
    runtime_lookup_list rΓ ys = Some vals ->
    r_muttype h l1 = Some qthisr ->
    vpa_mutabilty_object_creation qthisr q_c = qadapted ->
    o = {| rt_type := {| rqtype := qadapted; rctype := c |}; fields_map := vals |} ->
    h' = h ++ [o] ->
    rΓ' = rΓ <| vars := update x (Iot (dom h)) (vars rΓ) |> ->
    wf_r_config CT sΓ' rΓ' h'.
Proof.
  intros CT sΓ rΓ h x q_c c ys l1 qthisr vals o qadapted rΓ' h' sΓ'.
  intros HOK Hwf Htyping Hgetthis Hlookupvals HgetthisRuntimeType Hmutadapted Heq_o Heq_h' Heq_rΓ'.
    inversion Htyping.
    have Hwf_copy := Hwf.
    unfold wf_r_config.
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
    repeat split.
    + (* wellformed class *) 
    unfold  wf_class_table in Hclass. destruct Hclass as [Hclass _]. exact Hclass.
    + (* Object wellformedness *)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [Hobject _]]. exact Hobject.
    + (* All other classes have super class*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[Hotherclasses _]]]. exact Hotherclasses.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
    + (* Class identifier match*)
    unfold  wf_class_table in Hclass. destruct Hclass as [_ [_[_ Hclassnamematch]]]. apply Hclassnamematch.
    + (* wellformed heap *) 
    unfold wf_heap.
    intros ι0 Hι.
    subst.
    rewrite length_app in Hι.
    simpl in Hι.
    destruct (Nat.eq_dec ι0 (dom h)) as [Heq | Hneq].
    * (* ι = dom h (new object) *)
      subst.
      unfold wf_obj.
      rewrite runtime_getObj_last.
      split.
      -- (* wf_rtypeuse for new object *)
        simpl.
        unfold wf_rtypeuse.
        destruct (bound CT c) as [q_c_val|] eqn:Hbound.
        ++ unfold constructor_def_lookup in H10.
        destruct (find_class CT c) as [def|] eqn:Hfind.
        ** apply find_class_dom in Hfind.
          split.
          exact Hfind.
          unfold vpa_mutabilty_runtime_bound_agree.
          assert (Hwf_ctor : wf_constructor CT c consig).
          {
            eapply constructor_lookup_wf; eauto.
          }
          inversion Hwf_ctor; subst.
          rewrite Hbound in H.
          inversion H.
          destruct H0 as [Hparamswf [field_defs [Hcollect_H1 [Hdom_eq Hfieldtypematch]]]].
          unfold vpa_mutabilty_object_creation.
          destruct q_c_val eqn: Hnewobjctqualifier; destruct (cqualifier consig) eqn: Hcbound;
          destruct qthisr eqn: Hqthis;
          simpl in *; try easy.
        ** exfalso.
        unfold bound in Hbound.
        rewrite Hfind in Hbound.
        discriminate Hbound.
        ++ 
          unfold constructor_sig_lookup in H7.
          destruct (constructor_def_lookup CT c) as [ctor|] eqn:Hctor.
          ** unfold constructor_def_lookup in Hctor.
            destruct (find_class CT c) as [def|] eqn:Hfind.
            --- unfold bound in Hbound.
              rewrite Hfind in Hbound.
              discriminate Hbound.
            --- discriminate Hctor.
          ** easy.
      --
        {
          assert (Hc_dom : c < dom CT).
   {
     apply constructor_sig_lookup_dom in H7.
     exact H7.
   }
   
   (* Collect fields for class c *)
   assert (Hexists_fields : exists field_defs, CollectFields CT c field_defs).
   {
     eapply collect_fields_exists; eauto.
   }
   destruct Hexists_fields as [field_defs Hcollect_fields].
   
   exists field_defs.
   split.
   + (* CollectFields CT c field_defs *)
     exact Hcollect_fields.
   + split.
     * (* Length equality: dom vals = dom field_defs *)
       (* This follows from constructor well-formedness *)
       (* The constructor should ensure vals has the right length *)
       simpl.
       apply Forall2_length in H13.
       apply runtime_lookup_list_preserves_length in Hlookupvals.
       apply static_getType_list_preserves_length in H5.
      rewrite Hlookupvals.
      rewrite <- H5.
      rewrite H13.
      eapply constructor_sig_lookup_implies_def in H7; eauto.
      destruct H7 as [cdef Hcedflookup].
      destruct Hcedflookup as [Hcedflookup Hcdefcsig].
      eapply constructor_params_field_count; eauto.
     * (* Forall2 property *)
      assert (exists ι, get_this_var_mapping (vars rΓ) = Some ι).
      {
        eapply get_this_exists_from_wf_r_config; eauto.
      }
      destruct H as [ι HreceiverAddr].
      assert (exists qcontext, r_muttype h ι = Some qcontext).
      {
        eapply receiver_mutability_exists_wf_renv; eauto.
      }
      destruct H as [qcontext Hreceivermut].
       apply runtime_lookup_list_preserves_typing with (ι:= ι) (qcontext:=qcontext) (CT:= CT) (h := h) (sΓ := sΓ') (args := ys) (argtypes := argtypes) in Hlookupvals; auto.
       simpl.
        assert (Hwf_ctor : wf_constructor CT c consig).
        {
          eapply constructor_lookup_wf; eauto.
        }
        inversion Hwf_ctor; subst.
        unfold wf_heap in Hheap.
        unfold wf_obj in Hheap.
        eapply Forall2_from_nth.
        - (* Show lengths are equal *)
        apply Forall2_length in Hlookupvals.
        rewrite Hlookupvals.
        destruct H0 as [Hparamswf [field_defs_exists [Hcollect_H1 [Hdom_eq Hfieldtypematch]]]].
        apply Forall2_length in H13.
        rewrite H13.
        assert (field_defs_exists = field_defs). {
          eapply collect_fields_deterministic_rel; eauto.
        }
        subst field_defs_exists.
        exact Hdom_eq.
        - (* Show pointwise property *)
          intros i v fdef Hi Hv Hfdef.
          destruct v; [easy|].
          {
            assert (Hargtype : exists argtype, nth_error argtypes i = Some argtype).
        {
          apply Forall2_length in Hlookupvals.
          rewrite Hlookupvals in Hi.
          apply nth_error_Some_exists in Hi.
          exact Hi.
        }
        destruct Hargtype as [argtype Hargtype].
        eapply Forall2_nth_error in Hlookupvals; [|exact Hv|exact Hargtype].
        simpl in Hlookupvals.
        unfold wf_r_typable in Hlookupvals.
        destruct (r_type h l) as [rqt|] eqn:Hrtype; [|contradiction].
        assert (Hl_dom : l < dom h).
        {
          unfold r_type in Hrtype.
          destruct (runtime_getObj h l) as [obj|] eqn:Hobj; [|discriminate].
          apply runtime_getObj_dom in Hobj.
          exact Hobj.
        }
        rewrite runtime_getObj_last2; auto.
        destruct (runtime_getObj h l) eqn: Hl.
        2:{apply runtime_getObj_not_dom in Hl. lia.
        }
        exists rqt.
        split.
        - unfold r_type.
          rewrite runtime_getObj_last2; auto.
        - destruct H0 as [Hparamswf [field_defs_exists [Hcollect_H1 [Hdom_eq Hfieldtypematch]]]].
        assert (field_defs_exists = field_defs). {
          eapply collect_fields_deterministic_rel; eauto.
        }
        subst field_defs_exists.
        split.
          +
        destruct Hlookupvals as [Hrctype _].
        destruct (nth_error (cparams consig) i) as [paramtype|] eqn: Hparamtype.
        2:{
          apply nth_error_None in Hparamtype.
          assert (Hi_fdef : i < dom field_defs).
        {
          apply nth_error_Some.
          rewrite Hfdef.
          discriminate.
        }
        rewrite <- Hdom_eq in Hi_fdef.
        lia.
        }
        eapply Forall2_nth_error with (i:=i) (b:=fdef) (a:=paramtype) in Hfieldtypematch.
        apply qualified_type_subtype_base_subtype in Hfieldtypematch.
        simpl in Hfieldtypematch.
        eapply Forall2_nth_error with (i:=i) (b:=paramtype) (a:=argtype) in H13.
        apply qualified_type_subtype_base_subtype in H13.
        (* apply vpa_preserve_basetype_subtype in H13. *)
        eapply base_trans; eauto.
        eapply base_trans; eauto.
        exact Hargtype.
        exact Hparamtype.
        exact Hparamtype.
        exact Hfdef.
        + 
          destruct Hlookupvals as [Hrctype Hqctype].
            destruct (nth_error (cparams consig) i) as [paramtype|] eqn: Hparamtype.
            2:{
              apply nth_error_None in Hparamtype.
              assert (Hi_fdef : i < dom field_defs).
              {
                apply nth_error_Some.
                rewrite Hfdef.
                discriminate.
              }
              rewrite <- Hdom_eq in Hi_fdef.
              lia.
            }
            eapply Forall2_nth_error with (i:=i) (b:=fdef) (a:=paramtype) in Hfieldtypematch.
            apply qualified_type_subtype_q_subtype in Hfieldtypematch.
            eapply Forall2_nth_error with (i:=i) (b:=paramtype) (a:=argtype) in H13.
            apply qualified_type_subtype_q_subtype in H13.
            apply qualified_type_subtype_q_subtype in H14.
            
            2: exact Hargtype.
            2: exact Hparamtype.
            2: exact Hparamtype.
            2: exact Hfdef.
            simpl in Hfieldtypematch.
            move Hqctype at bottom.
            move Hfieldtypematch at bottom.
            unfold wf_senv in Hsenv;
            destruct Hsenv as [Hsenvdom _];
            destruct (r_type h ι) as [rqt_receiver|] eqn: Hrtype_receiver.
            assert(H100: qcontext = rqtype rqt_receiver).
            {
              unfold r_muttype in Hreceivermut.
              unfold r_type in Hrtype_receiver.
              destruct (runtime_getObj h ι) eqn: save; [|easy].
              inversion Hreceivermut; subst.
              inversion Hrtype_receiver; reflexivity.
            }
            2:{
              unfold r_type in Hrtype_receiver.
              unfold r_muttype in Hreceivermut.
              destruct (runtime_getObj h ι) eqn: save; [|easy].
              discriminate Hrtype_receiver.
            }
            unfold qualifier_typable_heap.
            unfold vpa_mutabilty_rec_fld.
            unfold vpa_mutabilty_constructor_fld in Hfieldtypematch.
            unfold vpa_mutabilty_object_creation.
            unfold qc2q in H14.
            simpl in H14.
            assert (l1 = ι). {
              apply get_this_var_mapping_runtime_getVal in HreceiverAddr.
              rewrite Hgetthis in HreceiverAddr.
              injection HreceiverAddr as Heq.
              exact Heq.
            }
            subst l1.
            assert (qthisr = qcontext). {
              rewrite Hreceivermut in HgetthisRuntimeType.
              inversion HgetthisRuntimeType; reflexivity.
            }
            subst qthisr.
            clear - Hfieldtypematch Hqctype H13.
            destruct (rqtype rqt) eqn: Hrqtq;
            destruct qcontext eqn: Hqthis;
            destruct (cqualifier consig) eqn: Hconstructoreturnq;
            destruct (mutability (ftype fdef)) eqn: Hfieldq; 
            try easy.
            all: destruct (sqtype paramtype) eqn: Hparamq;
            try solve_q_subtype_wrong.
            all: 
            destruct (sqtype argtype) eqn: Hargq;
            try solve_q_subtype_wrong;
            destruct qcontext eqn: Hqcontext;
            try solve_qualifier_typable_wrong_concrete.
          }
      }
    * (* ι < dom h (existing object) *)
      assert (ι0 < dom h) by lia.
      unfold wf_obj.
      rewrite runtime_getObj_last2; auto.
      {
        unfold wf_heap in Hheap.
        specialize (Hheap ι0 H).
        unfold wf_obj in Hheap |- *.
        destruct (runtime_getObj h ι0) as [o|] eqn:Hobj; [|contradiction].
          destruct Hheap as [Hrtypeuse [Hfields_len Hforall2]].
          repeat split.
          + exact Hrtypeuse.
          + 
          {
          exists Hfields_len.
          destruct Hforall2 as [Hcollect [Hlen_eq Hforall2_prop]].
          split.
          - exact Hcollect.
          - split.
            + exact Hlen_eq.
            + eapply Forall2_impl; [|exact Hforall2_prop].
              intros v fdef Hprop.
              destruct v as [|loc]; [trivial|].
              destruct (runtime_getObj h loc) as [obj_loc|] eqn:Hobj_loc.
              * (* loc exists in original heap *)
                destruct Hprop as [rqt [Hrtype_orig Hsubtype_orig]].
                assert (loc < dom h). {
                  (apply runtime_getObj_dom in Hobj_loc).
                  exact Hobj_loc.
                }
                rewrite runtime_getObj_last2; auto.
                rewrite Hobj_loc.
                exists rqt.
                split.
                -- unfold r_type in Hrtype_orig |- *.
                  rewrite runtime_getObj_last2; auto.
                -- exact Hsubtype_orig.
              * contradiction Hprop.
              }
       }
    + (* Length of runtime environment greater than 0 *)
      simpl. destruct Hsenv as [HsenvLength HsenvWellTyped].
      subst.
      rewrite update_length. rewrite <- Hlen.
      exact HsenvLength.
    +
      destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
      destruct Hreceiverval as [iot Hiot].
      destruct Hiot as [Hiot Hiot_dom].
      exists iot.
      simpl.
      unfold gget in *.
      destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
      * (* Case: vars rΓ = [] *)
        exfalso.
        (* rewrite Hvars in HrEnvLen. *)
        simpl in HrEnvLen.
        lia.
      * (* Case: vars rΓ = v0 :: vs *)
        destruct x as [|x'].
           -- (* x = S x' *)
              {
                split.
                - (* Show update preserves position 0 *)
                  simpl. 
                  exfalso. easy.
                - (* Show iot is still in extended heap domain *)
                  subst.
                  rewrite length_app. simpl.
                  lia.
              }
           --
            split.   
            subst.
            exact Hiot.
            rewrite Heq_h'.
            rewrite length_app.
            simpl.
            lia.
    + 
    destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
    simpl.
    subst.
    apply Forall_update.
    * eapply Forall_impl; [| exact Hallvals].
      intros v Hv.
      destruct v as [|loc]; [trivial|].
      destruct (runtime_getObj h loc) as [obj|] eqn:Hobj; [| contradiction].
      assert (Hloc_dom : loc < dom h) by (apply runtime_getObj_dom in Hobj; exact Hobj).
    rewrite runtime_getObj_last2.
    -- exact Hloc_dom.
    -- rewrite Hobj. trivial.
    * (* Show new object is well-formed *)
      assert (dom h + 1 = S (dom h)) by lia.
      unfold runtime_getObj.
      simpl.
      assert (Hlen_extended: dom (h ++ [{| rt_type := {| rqtype := vpa_mutabilty_object_creation
qthisr (cqualifier consig); rctype := c |}; fields_map := vals |}]) = dom h + 1).
      -- rewrite length_app. simpl. lia.
      -- rewrite nth_error_app2.
      ** lia.
      ** replace (dom h - dom h) with 0 by lia.
        simpl. reflexivity.
      * assert (Hx_dom : x < dom sΓ') by (apply static_getType_dom in H4; exact H4).
      rewrite <- Hlen; exact Hx_dom.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. rewrite <- H11. exact HsenvLength.
    + destruct Hsenv as [HsenvLength HsenvWellTyped]. rewrite <- H11. exact HsenvWellTyped.
    + subst. rewrite update_length. rewrite <- Hlen. lia.
    + 
    {
      intros ι qcontext HreceiverAddr Hreceivermut i Hi sqt Hnth.
      destruct (Nat.eq_dec i x) as [Heq | Hneq].
      - (* Case: i = x (newly assigned variable) *)
        subst i.
        simpl.
        unfold runtime_getVal.
        subst.
        rewrite update_same.
        + assert (x < dom sΓ') by (apply static_getType_dom in H4; exact H4).
          rewrite <- Hlen. exact H.
        + (* Show wf_r_typable for the new object *)
          {
            unfold wf_r_typable.
            unfold r_type.
            rewrite runtime_getObj_last.
            simpl.
            unfold get_this_var_mapping.
            simpl.
            destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
            - exfalso.
              unfold wf_renv in Hrenv.
              destruct Hrenv as [HrEnvLen _].
              rewrite Hvars in HrEnvLen.
              simpl in HrEnvLen.
              lia.
            - unfold r_muttype.
            destruct x as [|x'].
            + (* Case: x = 0 *)
              easy.
            + (* Case: x = S x' *)
              simpl.
              unfold r_muttype.
              unfold static_getType in H4.
              rewrite H4 in Hnth.
              inversion Hnth.
              subst sqt.
              split.
              apply qualified_type_subtype_base_subtype in H14.
              unfold qc2q in H14.
              simpl in H14.
              
              (* apply vpa_preserve_basetype_subtype in H14. *)
              (* apply vpa_mutabilty_tt_sctype *)
              exact H14.
              apply qualified_type_subtype_q_subtype in H14.
              simpl in H14.
              unfold wf_senv in Hsenv;
              destruct Hsenv as [Hsenvdom _];
              destruct (r_type h ι) as [rqt_receiver|] eqn: Hrtype_receiver.
              assert(H100: qcontext = rqtype rqt_receiver).
              {
                unfold r_muttype in Hreceivermut.
                unfold r_type in Hrtype_receiver.
                destruct (runtime_getObj h ι) eqn: save; [|easy].
                inversion Hreceivermut; subst.
                inversion Hrtype_receiver.
                destruct
                (
                runtime_getObj
                  (h ++
                  [{|
                      rt_type :=
                        {|
                          rqtype :=
                            vpa_mutabilty_object_creation qthisr (cqualifier consig);
                          rctype := c
                        |};
                      fields_map := vals
                    |}])
                ι) as [o'|] eqn:Hobj_ι; [|discriminate].
                assert (Ho_eq : o = o').
                {
                  unfold runtime_getObj in save, Hobj_ι.
                  rewrite nth_error_app1 in Hobj_ι.
                  - (* ι < dom h *)
                    assert (Hι_dom : ι < dom h).
                    {
                      apply runtime_getObj_dom in save.
                      exact save.
                    }
                    exact Hι_dom.
                  - (* Conclude o = o' *)
                    rewrite save in Hobj_ι.
                    injection Hobj_ι as Ho_eq.
                    exact Ho_eq.
                }
                subst o'.
                injection H0 as H0_eq.
                symmetry.
                exact H0_eq.
              }
              2:{
                unfold r_type in Hrtype_receiver.
                unfold r_muttype in Hreceivermut.
                simpl in HreceiverAddr.
                destruct v0 as [|]; [easy|].
                inversion HreceiverAddr; subst.
                destruct (runtime_getObj h ι) eqn: save.
                2:{
                  destruct Hrenv as [HrEnvLen [Hrecv Hallvals]].
                  destruct Hrecv as [ι0 [Hthis Hι0_dom]].
                  rewrite Hvars in Hthis. simpl in Hthis. inversion Hthis; subst ι0.
                  (* now Hι0_dom : ι < dom h *)

                  exfalso.
                  apply runtime_getObj_not_dom in save.
                  lia.
                }
                discriminate Hrtype_receiver.
              }
              unfold r_type in Hrtype_receiver.
              destruct (runtime_getObj h ι) eqn: save; [|easy].
              have save_copy := save.
              apply runtime_getObj_dom in save.
              apply r_muttype_app_preserve_old_Some in Hreceivermut; auto.
              rewrite (get_this_var_mapping_update_nonzero (v0 :: vs) (S x') (Iot (dom h))) in HreceiverAddr.
              discriminate.
              specialize (Hcorr ι qcontext HreceiverAddr Hreceivermut 0 Hsenvdom Tthis H6).
              rewrite Hgetthis in Hcorr.
              unfold wf_r_typable in Hcorr.
              unfold r_type in Hcorr.
              assert (l1 = ι).
              {
                rewrite <- Hvars in HreceiverAddr.
                pose proof (get_this_var_mapping_runtime_getVal rΓ ι HreceiverAddr) as Hthis_rt.
                rewrite Hgetthis in Hthis_rt.
                inversion Hthis_rt; inversion H0; subst; reflexivity.
              }
              subst l1.
              rewrite save_copy in Hcorr.
              destruct Hcorr as [_ Hqual_receiver].
              inversion Hrtype_receiver.
              subst rqt_receiver.
              rewrite <- H100 in Hqual_receiver.
              assert (qcontext = qthisr).
              {
                rewrite HgetthisRuntimeType in Hreceivermut.
                inversion Hreceivermut; reflexivity.
              }
              subst qthisr.
              unfold qualifier_typable_context in *.
              unfold vpa_mutabilty_object_creation in *.
              unfold vpa_mutabilty_rs in *;
              unfold qc2q in *;
              unfold vpa_mutabilty_tt in *.
              destruct (cqualifier consig) eqn: Hcbound;
              destruct qcontext eqn: Hqcontext;
              destruct (rqtype (rt_type o)) eqn: Hrqtq;
              destruct (sqtype Tx) eqn: Htxq; try easy.
              all: destruct (sqtype Tthis) eqn: Hqthisr; try rewrite Htxq in H14; simpl in H14; try inversion H14; try easy.
          }
      - (* Case: i ≠ x (existing variable) *)
        simpl.
        unfold runtime_getVal.
        subst.
        rewrite update_diff; auto.
        rewrite get_this_var_mapping_update_vars_nonzero in HreceiverAddr; auto.
        (* Show that the original wf_r_typable holds *)
        assert (r_muttype h ι = Some qcontext) as Hreceivermut_orig.
        {
          eapply r_muttype_app_preserve_old_Some in Hreceivermut; eauto.
          destruct Hrenv as [HrEnvLen [Hrecv Hallvals]].
          destruct Hrecv as [ι0 [Hthis Hι0_dom]].
          rewrite Hthis in HreceiverAddr. inversion HreceiverAddr; subst ι.
          exact Hι0_dom.
        }
        assert (Hcorr_orig := Hcorr ι qcontext HreceiverAddr Hreceivermut_orig i Hi sqt Hnth).
        destruct (runtime_getVal rΓ i) as [v|] eqn:Hval.
      + (* Case: runtime_getVal rΓ i = Some v *)
        destruct v as [|loc].
        * (* Case: v = Null_a *)
        unfold runtime_getVal in Hval.
        rewrite Hval.
        trivial.
        * (* Case: v = Iot loc *)
        unfold runtime_getVal in Hval.
        rewrite Hval.
        unfold wf_r_typable in Hcorr_orig |- *.
        destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
          assert (Hrtype_ext : r_type (h ++ [{| rt_type := {| rqtype := vpa_mutabilty_object_creation qthisr
(cqualifier consig); rctype := c |}; fields_map := vals |}]) loc = Some rqt).
          {
            unfold r_type in Hrtype |- *.
            rewrite heap_extension_preserves_objects; auto.
            destruct (runtime_getObj h loc) as [obj|] eqn:Hobj; [|discriminate].
            apply runtime_getObj_dom in Hobj. exact Hobj.
          }
          rewrite Hrtype_ext.
          exact Hcorr_orig.
          + contradiction Hcorr_orig.
          }
Admitted.

Lemma vpa_mutabilty_tt_sctype :
  forall Tthis T : qualified_type,
    sctype (vpa_mutabilty_tt Tthis T) = sctype T.
Proof.
  intros Tthis [q c].
  unfold vpa_mutabilty_tt.    
  simpl.
  destruct (sqtype Tthis); simpl; try reflexivity.
  all: destruct q; simpl; reflexivity.
Qed.

Lemma receiver_mutability_exists_from_bound :
  forall h ι,
    ι < dom h ->
    exists q, r_muttype h ι = Some q.
Proof.
  intros h ι Hlt.
  unfold r_muttype.
  destruct (runtime_getObj h ι) as [o|] eqn:Hobj.
  - eexists. reflexivity.
  - exfalso.
    apply runtime_getObj_not_dom in Hobj.
    lia.
Qed.

Lemma static_getType_list_index_strong :
  forall sΓ zs argtypes i j argtype,
    mapM (fun x => static_getType sΓ x) zs = Some argtypes ->
    nth_error zs i = Some j ->
    nth_error argtypes i = Some argtype ->
    static_getType sΓ j = Some argtype.
Proof.
  intros sΓ zs.
  induction zs as [|z zs' IH]; intros argtypes i j argtype Hmap Hzs Hargs.
  - (* zs = [] *)
    simpl in Hmap.
    inversion Hmap; subst argtypes.
    simpl in Hargs.
    inversion Hzs.
    exfalso.
    rewrite nth_error_nil in Hzs.
    discriminate Hzs.
  - (* zs = z :: zs' *)
    simpl in Hmap.
    destruct (static_getType sΓ z) as [Tz|] eqn:HTz; try discriminate.
    destruct (mapM (fun x : Loc => static_getType sΓ x) zs')
      as [argtypes'|] eqn:Hrec; try discriminate.
    inversion Hmap; subst argtypes; clear Hmap.
    destruct i as [|i'].
    + (* i = 0 *)
      simpl in Hzs, Hargs.
      inversion Hzs; subst j.
      inversion Hargs; subst argtype.
      exact HTz.
    + (* i = S i' *)
      simpl in Hzs, Hargs.
      eapply IH; eauto.
Qed.

Lemma static_getType_list_nth_zs :
  forall sΓ zs argtypes i argtype,
    static_getType_list sΓ zs = Some argtypes ->
    nth_error argtypes i = Some argtype ->
    exists j,
      nth_error zs i = Some j /\
      static_getType sΓ j = Some argtype.
Proof.
  intros sΓ zs.
  induction zs as [|z zs' IH]; intros argtypes i argtype Hlist Hnth.
  - (* zs = [] *)
    simpl in Hlist.
    inversion Hlist; subst argtypes.
    simpl in Hnth.
    rewrite nth_error_nil in Hnth.
    discriminate.
  - (* zs = z :: zs' *)
    simpl in Hlist.
    destruct (static_getType sΓ z) as [Tz|] eqn:HTz.
    2:{ 
      exfalso. 
      unfold static_getType_list in Hlist.
      simpl in Hlist.
      rewrite HTz in Hlist.
      discriminate Hlist.
      }
    destruct (mapM (fun x : Loc => static_getType sΓ x) zs')
      as [argtypes'|] eqn:Hrec. 
      2:{
        unfold static_getType_list in Hlist.
        simpl in Hlist.
        rewrite HTz in Hlist.
        rewrite Hrec in Hlist.
        discriminate Hlist.
      }
    (* inversion Hlist; subst argtypes; clear Hlist. *)
    destruct i as [|i'].
    + (* i = 0 *)
      unfold static_getType_list in Hlist.
      simpl in Hlist.
      rewrite HTz in Hlist.
      rewrite Hrec in Hlist.
      inversion Hlist; subst argtypes; clear Hlist.

      simpl in Hnth.
      inversion Hnth; subst argtype; clear Hnth.

      exists z.
      split; [simpl; reflexivity | exact HTz].
    + (* i = S i' *)
      simpl in Hnth.
      unfold static_getType_list in Hlist.
      simpl in Hlist.
      rewrite HTz in Hlist.
      rewrite Hrec in Hlist.
      inversion Hlist as [Heq_argtypes]; subst argtypes; clear Hlist.
      simpl in Hnth.
      (* nth_error (Tz :: argtypes') (S i') = nth_error argtypes' i' *)
      destruct (IH argtypes' i' argtype Hrec Hnth) as [j [Hnth_zs Hj]].
      exists j.
      split; simpl; assumption.
Qed.

Lemma runtime_lookup_list_nth_zs :
  forall rΓ zs vals i v,
    runtime_lookup_list rΓ zs = Some vals ->
    nth_error vals i = Some v ->
    exists j,
      nth_error zs i = Some j /\
      runtime_getVal rΓ j = Some v.
Proof.
  intros rΓ zs.
  induction zs as [|z zs' IH]; intros vals i v Hlist Hnth.
  - (* zs = [] *)
    simpl in Hlist.
    inversion Hlist; subst vals.
    simpl in Hnth.
    rewrite nth_error_nil in Hnth.
    discriminate.
  - (* zs = z :: zs' *)
    simpl in Hlist.
    destruct (runtime_getVal rΓ z) as [Vz|] eqn:HVz.
    2:{
      exfalso.
      unfold runtime_lookup_list in Hlist.
      simpl in Hlist.
      rewrite HVz in Hlist.
      discriminate Hlist.
    }
    destruct (mapM (fun x : Loc => runtime_getVal rΓ x) zs')
      as [vals'|] eqn:Hrec.
    2:{
      unfold runtime_lookup_list in Hlist.
      simpl in Hlist.
      rewrite HVz in Hlist.
      rewrite Hrec in Hlist.
      discriminate Hlist.
    }
    destruct i as [|i'].
    + (* i = 0 *)
      unfold runtime_lookup_list in Hlist.
      simpl in Hlist.
      rewrite HVz in Hlist.
      rewrite Hrec in Hlist.
      inversion Hlist; subst vals; clear Hlist.

      simpl in Hnth.
      inversion Hnth; subst v; clear Hnth.

      exists z.
      split; [simpl; reflexivity | exact HVz].
    + (* i = S i' *)
      simpl in Hnth.
      unfold runtime_lookup_list in Hlist.
      simpl in Hlist.
      rewrite HVz in Hlist.
      rewrite Hrec in Hlist.
      inversion Hlist as [Heq_vals]; subst vals; clear Hlist.
      simpl in Hnth.
      (* nth_error (Vz :: vals') (S i') = nth_error vals' i' *)
      destruct (IH vals' i' v Hrec Hnth) as [j [Hnth_zs Hj]].
      exists j.
      split; simpl; assumption.
Qed.

(* ------------------------------------------------------------- *)
(* Soundness properties for PICO *)
Theorem preservation_pico :
  forall CT sΓ rΓ h stmt rΓ' h' sΓ',
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ stmt sΓ' -> 
    eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h' -> 
    wf_r_config CT sΓ' rΓ' h'.
Proof.
  intros CT sΓ rΓ h stmt rΓ' h' sΓ' Hwf Htyping Heval.
  generalize dependent sΓ.
  generalize dependent sΓ'.
  remember OK as ok.
  have Heval_copy := Heval.
  induction Heval; intros; try (discriminate; inversion Htyping; subst; exact Hwf).
  6:
    {
      have Htyping_copy := Htyping.
      inversion Htyping; subst.
      destruct H1 as [mdeflookup getmbody].
      remember (msignature mdef) as msig.
      have mdeflookupcopy := mdeflookup.
      have Hwfcopy := Hwf.
      unfold wf_r_config in Hwf.
      destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
      (* apply method_lookup_wf_class_by_find in mdeflookup; auto. *)
      inversion mdeflookup; revert getmbody; subst; intro getmbody.
      assert (wf_method CT cy mdef).
      {
        eapply method_lookup_wf_class; eauto.
        eapply r_basetype_in_dom; eauto.
        unfold gget_method in H3.
        apply find_some in H3.
        destruct H3.
        exact H2.
      }
      inversion H2; subst.
      destruct H5 as [mrettype Htyping_method].
      destruct Htyping_method as [Htyping_method Hmethodret].
      remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit.
      remember {| vars := Iot ly :: vals |} as rΓmethodinit.
      destruct (r_muttype h ly) eqn: Hinnerthis.
      2:{
        unfold r_muttype in Hinnerthis.
        unfold r_basetype in H0.
        destruct (runtime_getObj h ly).
        discriminate Hinnerthis.
        discriminate H0.
      }
      remember (rΓ <| vars := update x retval (vars rΓ) |>) as rΓ'''.
      assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
      { (* Method inner config wellformed.*)

        have Hclasstable := Hclass.
        unfold  wf_class_table in Hclass.
        destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
        repeat split.
        exact Hclass.
        exact Hobj.
        exact Hotherclasses.
        apply Hcname_consistent.
        apply Hcname_consistent.
        exact Hheap.
        rewrite HeqrΓmethodinit.
        simpl.
        lia.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
        exists ly.
        split.
        rewrite HeqrΓmethodinit.
        simpl.
        reflexivity.
        unfold runtime_getVal in H.
        destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
        injection H as H1_eq.
        subst v.
        eapply Forall_nth_error in Hallvals; eauto.
        simpl in Hallvals.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjly; [|contradiction].
        apply runtime_getObj_dom in Hobjly.
        exact Hobjly.

        (* Inner runtime env is wellformed*)
        rewrite HeqrΓmethodinit.
        simpl.
        constructor.
        simpl.
        unfold runtime_getVal in H.
        destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
        injection H as H1_eq.
        subst v.
        unfold runtime_getVal in Hnth_y.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [_ Hallvals]].
        eapply Forall_nth_error in Hallvals; eauto.
        simpl in Hallvals.
        exact Hallvals.
        eapply runtime_lookup_list_preserves_wf_values; eauto.

        rewrite HeqsΓmethodinit.
        simpl.
        lia.

        (* Inner static env's elements are wellformed typeuse *)
        rewrite HeqsΓmethodinit.
        constructor.
        subst.

        (* Receiver type is well-formed *)
        eapply method_sig_wf_receiver_by_find; eauto.
        unfold r_basetype in H0.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H0 as H2_eq.
        (* subst cy. *)
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].
        simpl.
        unfold wf_heap in Hheap.
        assert (Hly_dom : ly < dom h) by (apply runtime_getObj_dom in Hobjy; exact Hobjy).
        specialize (Hheap ly Hly_dom).
        unfold wf_obj in Hheap.
        rewrite Hobjy in Hheap.
        destruct Hheap as [Hwf_rtypeuse _].
        unfold wf_rtypeuse in Hwf_rtypeuse.
        simpl in Hwf_rtypeuse.
        destruct (bound CT rc_obj) as [class_def|] eqn:Hbound.
        subst cy.
        simpl.
        destruct Hwf_rtypeuse as [Hwf_rtypeuse _].
        exact Hwf_rtypeuse.
        contradiction.

        eapply method_sig_wf_parameters_by_find; eauto.
        unfold r_basetype in H0.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H0 as H2_eq.
        subst cy.
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].
        simpl.
        unfold wf_heap in Hheap.
        assert (Hly_dom : ly < dom h) by (apply runtime_getObj_dom in Hobjy; exact Hobjy).
        specialize (Hheap ly Hly_dom).
        unfold wf_obj in Hheap.
        rewrite Hobjy in Hheap.
        destruct Hheap as [Hwf_rtypeuse _].
        unfold wf_rtypeuse in Hwf_rtypeuse.
        simpl in Hwf_rtypeuse.
        destruct (bound CT rc_obj) as [class_def|] eqn:Hbound.
        simpl.
        destruct Hwf_rtypeuse as [Hwf_rtypeuse _].
        exact Hwf_rtypeuse.
        contradiction.

        apply static_getType_list_preserves_length in H15.
        apply runtime_lookup_list_preserves_length in H4.
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        simpl.
        f_equal.
        apply Forall2_length in H24.
        assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H14.
          exact H14.
        }
        unfold wf_renv in Hrenv.
        destruct Hrenv as [OutterDom [OutterReceiver OutterCorrespond]].
        destruct OutterReceiver as [OutterReceiverAddr OutterReceiver].
        destruct OutterReceiver as [OutterReceiverGetAddr OutterReceiverAddrBound].
        assert (exists qrout, r_muttype h OutterReceiverAddr = Some qrout).
        {
          eapply receiver_mutability_exists_from_bound.
          exact OutterReceiverAddrBound.
        }
        
        destruct H5 as [qrout H5].
        assert (get_this_var_mapping (vars rΓmethodinit) = Some ly).
        {
          unfold get_this_var_mapping.
          rewrite HeqrΓmethodinit.
          simpl.
          auto.
        }
        assert (Hytypable: wf_r_typable CT rΓ h ly Ty qrout). {
        eapply correspondence_to_typable; eauto.

          specialize (Hcorr OutterReceiverAddr qrout OutterReceiverGetAddr H5).
          exact Hcorr.  
        }

        (* Extract subtyping from wf_r_typable *)
        unfold wf_r_typable in Hytypable.
        unfold r_basetype in H0.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H0 as Hcy_eq.
        subst cy.
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].
        unfold get_this_var_mapping.

        unfold r_type in Hytypable.
        rewrite Hobjy in Hytypable.
        simpl in Hytypable.
        destruct Hytypable as [Hsubtype _].
        
        rewrite <- H4 in H15.
        rewrite <- H15.
        rewrite H24.
        assert (Hsigeq: msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        rewrite <- Hsigeq in H22.
        rewrite <- Hsigeq in H23.
        rewrite <- Hsigeq in H24.
        rewrite Hsigeq.
        reflexivity.

        assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H14.
          exact H14.
        }
        unfold wf_renv in Hrenv.
        destruct Hrenv as [OutterDom [OutterReceiver OutterCorrespond]].
        destruct OutterReceiver as [OutterReceiverAddr OutterReceiver].
        destruct OutterReceiver as [OutterReceiverGetAddr OutterReceiverAddrBound].
        assert (exists qrout, r_muttype h OutterReceiverAddr = Some qrout).
        {
          unfold r_muttype.
          destruct (runtime_getObj h OutterReceiverAddr) eqn: Hobjaddr. 
          2:{
            apply runtime_getObj_not_dom in Hobjaddr.
            lia.
          }
          eexists.
          reflexivity.
        }
        
        destruct H5 as [qrout H5].
        assert (get_this_var_mapping (vars rΓmethodinit) = Some ly).
        {
          unfold get_this_var_mapping.
          rewrite HeqrΓmethodinit.
          simpl.
          auto.
        }
        assert (Hytypable: wf_r_typable CT rΓ h ly Ty qrout). 
        {
          eapply correspondence_to_typable; eauto.
          specialize (Hcorr OutterReceiverAddr qrout OutterReceiverGetAddr H5).
          exact Hcorr.
        }
        intros ι qcontext getThisAddr getqcontext i Hi sqt Hnth.
        rewrite HeqsΓmethodinit in Hnth, Hi.
        rewrite HeqrΓmethodinit.
        simpl in *.
        destruct i as [|i'].
        (* Reciever *)
        simpl in Hnth.
        injection Hnth as Hsqt_eq.
        subst sqt.
        simpl.
        unfold wf_r_typable.
        unfold r_type.
        destruct (runtime_getObj h ly) as [objy|] eqn:Hobj_ly.
        2:{
          unfold r_basetype in H0.
          rewrite Hobj_ly in H0.
          discriminate.
        }
        (* Get the runtime type *)
        simpl.
        destruct (r_muttype h ly) as [qy|] eqn:Hq_ly.
        2:{
          unfold r_muttype in Hq_ly.
          rewrite Hobj_ly in Hq_ly.
          discriminate.
        }
        split.
          (* receiver base type subtype preserved *)
          apply qualified_type_subtype_base_subtype in H22.
          unfold wf_r_typable in Hytypable.
            unfold r_basetype in H0.
            unfold r_type.
            destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
            injection H0 as Hcy_eq.
            subst cy.
            destruct obj as [rt_obj fields_obj].
            destruct rt_obj as [rq_obj rc_obj].
            destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].

            unfold r_type in Hytypable.
            rewrite Hobjy in Hytypable.
            simpl in Hytypable.
            destruct Hytypable as [Hsubtype _].
            simpl in Hobj_ly.
            injection Hobj_ly as Hobjy_eq.
          assert (msignature mdef = msignature mdef0).
          {
            eapply method_signature_consistent_subtype; eauto.
          }
          rewrite <- H0 in H22.
          rewrite <- H0 in H23.
          rewrite <- H0 in H24.
          subst objy.
          simpl in *.
          (* apply vpa_preserve_basetype_subtype in H22. *)
          apply qualified_type_subtype_base_subtype in H23.
          (* rewrite (vpa_mutabilty_tt_sctype Tthis Ty) in H23. *)
          rewrite (vpa_mutabilty_tt_sctype Ty
         (mreceiver (msignature mdef))) in H23.
          eapply base_trans; eauto.

        (* receiver qualifier type subtype preserved *)
        apply qualified_type_subtype_q_subtype in H23.
        assert (msignature mdef = msignature mdef0).
        {
          unfold wf_r_typable in Hytypable.
          unfold r_basetype in H0.
          unfold r_type.
          destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
          injection H0 as Hcy_eq.
          subst cy.
          destruct obj as [rt_obj fields_obj].
          destruct rt_obj as [rq_obj rc_obj].
          destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].

          unfold r_type in Hytypable.
          rewrite Hobjy in Hytypable.
          simpl in Hytypable.
          destruct Hytypable as [Hsubtype _].
          eapply method_signature_consistent_subtype; eauto.
        }
        rewrite H8.
        1:
        {
          have Hcorrcopy := Hcorr.
          specialize (Hcorr OutterReceiverAddr qrout OutterReceiverGetAddr H5).
          unfold static_getType in H14.
          specialize (Hcorr y Hy_dom Ty H14).
          unfold wf_r_typable in Hcorr.
          rewrite H in Hcorr.
          unfold r_type in Hcorr.
          rewrite Hobj_ly in Hcorr.
          destruct Hcorr as [_ HInnerReceiverQualifier].

          specialize (Hcorrcopy OutterReceiverAddr qrout OutterReceiverGetAddr H5).
          unfold wf_senv in Hsenv.
          destruct Hsenv as [Hsenvdom _].
          apply get_this_qualified_type_nth_error in H16.
          specialize (Hcorrcopy 0 Hsenvdom Tthis H16).
          apply get_this_var_mapping_runtime_getVal in OutterReceiverGetAddr.
          rewrite OutterReceiverGetAddr in Hcorrcopy.
          unfold wf_r_typable in Hcorrcopy.
          unfold r_type in Hcorrcopy.
          unfold r_muttype in H5.
          destruct (runtime_getObj h OutterReceiverAddr) as [outterreceiverobj|] eqn:Houtterobj; [|discriminate].
          inversion H5; subst qrout.
          destruct Hcorrcopy as [_ Houtterqualifier].
          (* unfold vpa_mutabilty_tt in H23. *)
          rewrite sq_vpa_tt_eq_qq in H23.
          assert (ly = ι).
          {
            rewrite H7 in getThisAddr.
            inversion getThisAddr; subst; reflexivity.
          }
          subst ι.
          assert ((rqtype (rt_type objy)) = qcontext).
          {
            unfold r_muttype in getqcontext.
            rewrite Hobj_ly in getqcontext.
            simpl in getqcontext.
            inversion getqcontext; subst qcontext.
            reflexivity.
          }
          subst qcontext.
          clear - Houtterqualifier HInnerReceiverQualifier H23.
          destruct (rqtype (rt_type objy)) eqn:Hrqtq;
          destruct (sqtype (mreceiver (msignature mdef0))) eqn:Hreceiverq;
          try solve_qualifier_typable_correct_concrete.
          all: destruct (sqtype Ty) eqn:Htyq;
          simpl in H23;
          try solve_q_subtype_wrong.
          all: 
          destruct (rqtype (rt_type outterreceiverobj)) eqn:Hrqtoutter;
          try solve_qualifier_typable_wrong_concrete.
        }

  (* -------------------------------------------------- *)
        apply qualified_type_subtype_q_subtype in H22.
        rewrite H7 in getThisAddr.
        inversion getThisAddr; subst.
        destruct (runtime_getObj h ι) as [objι|] eqn:Hobj_ι.
        2:{
          unfold r_basetype in H0.
          rewrite Hobj_ι in H0.
          discriminate.
        }
        simpl.
        (* Hcorr is used to extract method call receiver dependency *)
        (* Hcorrcopy is used to extract outter receiver dependency *)
        (* Hcorrcopy2 will be used extract method parameter and argument dependency *)
        have Hcorrcopy := Hcorr.
        have Hcorrcopy2 := Hcorr.
          specialize (Hcorr OutterReceiverAddr qrout OutterReceiverGetAddr H5).
          unfold static_getType in H14.
          specialize (Hcorr y Hy_dom Ty H14).
          unfold wf_r_typable in Hcorr.
          rewrite H in Hcorr.
          unfold r_type in Hcorr.
          rewrite Hobj_ι in Hcorr.
          destruct Hcorr as [_ HInnerReceiverQualifier].

          specialize (Hcorrcopy OutterReceiverAddr qrout OutterReceiverGetAddr H5).
          unfold wf_senv in Hsenv.
          destruct Hsenv as [Hsenvdom _].
          apply get_this_qualified_type_nth_error in H16.
          specialize (Hcorrcopy 0 Hsenvdom Tthis H16).
          have OutterReceiverGetAddr_copy := OutterReceiverGetAddr.
          have H5_copy := H5.
          apply get_this_var_mapping_runtime_getVal in OutterReceiverGetAddr.
          rewrite OutterReceiverGetAddr in Hcorrcopy.
          unfold wf_r_typable in Hcorrcopy.
          unfold r_type in Hcorrcopy.
          unfold r_muttype in H5.
          destruct (runtime_getObj h OutterReceiverAddr) as [outterreceiverobj|] eqn:Houtterobj; [|discriminate].
          destruct Hcorrcopy as [_ Houtterqualifier].

          assert (msignature mdef = msignature mdef0).
          {
            unfold wf_r_typable in Hytypable.
            unfold r_basetype in H0.
            unfold r_type.
            unfold r_type in Hytypable.
            rewrite Hobj_ι in Hytypable.
            destruct (runtime_getObj h ι) as [obj|] eqn:Hobjy; [|discriminate].
            injection H0 as Hcy_eq.
            subst cy.
            destruct objι as [rt_obj fields_obj].
            destruct rt_obj as [rq_obj rc_obj].
            destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
            {
              rewrite Hlen in Hsenvdom.
              easy.
            }
            simpl in Hytypable.
            destruct Hytypable as [Hsubtype _].
            eapply method_signature_consistent_subtype; eauto.
            inversion Hobj_ι; subst.
            simpl in *.
            assumption.
          }

          unfold runtime_getVal.
          simpl.
          destruct (nth_error vals i') as [v|] eqn:Hval_i.
          - (* Parameter i' exists *)
            destruct v as [|loc]; [trivial|].
            (* Use H23 to get the subtyping relationship *)
            assert (Hi'_bound : i' < List.length argtypes).
            {
              apply Forall2_length in H24.
              simpl in Hi.
              simpl in Hnth.
              assert (Hi_mparams : i' < dom (mparams (msignature mdef))).
              { apply nth_error_Some. rewrite Hnth. discriminate. }
              rewrite H8 in Hi_mparams.  (* msig mdef = msig mdef0 *)
              rewrite <- H24 in Hi_mparams.
              exact Hi_mparams.
            }
            assert (Harg_type : exists argtype, nth_error argtypes i' = Some argtype).
            {
              apply nth_error_Some_exists.
              exact Hi'_bound.
            }
            destruct Harg_type as [argtype Hargtype].
            rewrite H8 in Hnth.
            eapply Forall2_nth_error in H24; eauto.
            unfold wf_r_typable.
            unfold r_type.
            assert (loc < dom h).
            {
              assert (Hvals_wf :
              Forall
                (fun v =>
                  match v with
                  | Null_a => True
                  | Iot loc =>
                      match runtime_getObj h loc with
                      | Some _ => True
                      | None => False
                      end
                  end) vals).
              {
                unfold wf_r_config in Hwfcopy.
                destruct Hwfcopy as [_ [_ [Hrenv [_ _]]]].
                eapply runtime_lookup_list_preserves_wf_values; eauto.
              }
              eapply Forall_nth_error in Hvals_wf; eauto.
              simpl in Hvals_wf.
              destruct (runtime_getObj h loc) as [obj_loc|] eqn:Hobj_loc; [|contradiction].
              apply runtime_getObj_dom in Hobj_loc.
              exact Hobj_loc.
            }
            destruct (runtime_getObj h loc) as [obj_loc|] eqn:Hobj_loc.
            2:{apply runtime_getObj_not_dom in Hobj_loc. lia. }
            assert (HargtypeFromsEnv :
              exists iArgInSenv,
                nth_error sΓ' iArgInSenv = Some argtype
            /\ nth_error zs i' = Some iArgInSenv).
            {
              destruct (static_getType_list_nth_zs sΓ' zs argtypes i' argtype H15 Hargtype)
                as [j [Hzs_j Hst_j]].
              exists j.
              split.
              - (* from static_getType to nth_error sΓ' *)
                unfold static_getType in Hst_j; exact Hst_j.
              - (* keep the zs fact *)
                exact Hzs_j.
            }
            destruct HargtypeFromsEnv as [iArgInSenv [HargtypeFromsEnv Hzs_iArg]].

            assert (Hi'dom : iArgInSenv < dom sΓ').
            {
              apply nth_error_Some.
              rewrite HargtypeFromsEnv; discriminate.
            }

            assert (HargtypeFromrEnv :
                      nth_error (vars rΓ) iArgInSenv = Some (Iot loc)).
            {
              destruct (runtime_lookup_list_nth_zs rΓ zs vals i' (Iot loc) H4 Hval_i)
                as [j [Hzs_j Hget_j]].
              assert (HiEq : iArgInSenv = j).
              {
                (* zs[i'] = Some iArgInSenv and zs[i'] = Some j ⇒ iArgInSenv = j *)
                rewrite Hzs_iArg in Hzs_j.
                inversion Hzs_j; reflexivity.
              }
              subst iArgInSenv.
              unfold runtime_getVal in Hget_j.
              exact Hget_j.
            }
            specialize (Hcorrcopy2 OutterReceiverAddr qrout OutterReceiverGetAddr_copy H5_copy).
            specialize (Hcorrcopy2 iArgInSenv Hi'dom argtype HargtypeFromsEnv).
            unfold runtime_getVal in Hcorrcopy2.
            rewrite HargtypeFromrEnv in Hcorrcopy2.
            unfold wf_r_typable in Hcorrcopy2.
            unfold r_type in Hcorrcopy2.
            rewrite Hobj_loc in Hcorrcopy2.
            destruct Hcorrcopy2 as [Harg_base_subtype Harg_qual_subtype].
            split.

            (* Base type subtype *)
            apply qualified_type_subtype_base_subtype in H24.
            (* rewrite (vpa_mutabilty_tt_sctype Tthis argtype) in H24. *)
            rewrite (vpa_mutabilty_tt_sctype Ty) in H24.
            eapply base_trans; eauto.

            (* Quliafier type correspondence *)
            assert (Hqcontext_eq: qcontext = rqtype (rt_type objι)).
            {
              unfold r_muttype in getqcontext.
              rewrite Hobj_ι in getqcontext.
              inversion getqcontext; subst qcontext.
              reflexivity.
            }
            subst qcontext.
            assert (HOutterReceiverRuntimeMutabilityEq: qrout = rqtype (rt_type outterreceiverobj)).
            {
              inversion H5; subst; reflexivity.
            }
            subst qrout.
            apply qualified_type_subtype_q_subtype in H24.
            apply qualified_type_subtype_q_subtype in H23.
            clear H22. clear Hmethodret.
            clear - Harg_qual_subtype Houtterqualifier HInnerReceiverQualifier H24.

            rewrite sq_vpa_tt_eq_qq in H24.
            (* rewrite sq_vpa_tt_eq_qq in H24. *)
            (* rewrite sq_vpa_tt_eq_qq in H24. *)

            destruct (rqtype (rt_type obj_loc)) eqn:HArgMutability;
            destruct (rqtype (rt_type objι)) eqn:HInnerReceiverMutability;
            destruct (sqtype sqt) eqn:HParameterStaticDeclearedMutability;
            try solve_qualifier_typable_correct_concrete.
            all: 
            destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            destruct (sqtype Ty) eqn:HyStaticMutability;
            try solve_qualifier_typable_wrong_concrete.
            all:
            destruct (sqtype argtype) eqn:Hargqtype;
            try solve_qualifier_typable_wrong_concrete.

            all: destruct (sqtype Tthis) eqn:HOutterReceiverStaticMutability;
            simpl in H24;
            try solve_qualifier_typable_wrong_concrete;
            try solve_q_subtype_wrong.

          - (* Parameter i' doesn't exist - contradiction *)
            exfalso.
            apply nth_error_None in Hval_i.
            apply runtime_lookup_list_preserves_length in H4.
            apply static_getType_list_preserves_length in H15.
            apply Forall2_length in H24.
            rewrite H4 in Hval_i.
            rewrite <- H15 in Hval_i.
            rewrite H24 in Hval_i.
            simpl in Hi.
            simpl in Hnth.
            simpl in Hnth.
            rewrite <- H8 in Hval_i.
            lia.
      }
      rename x0 into sΓmethodend.
      assert (wf_r_config CT sΓmethodend rΓ'' h'). 
      {
        eapply IHHeval with (sΓ := sΓmethodinit) (sΓ' := sΓmethodend); eauto.
      }
      
      {
        (* Method call resulting config is wellformed *)
        have H5copy := H5.
        unfold wf_r_config.
        unfold wf_r_config in H5.
        destruct H5 as [_ [Hheapinit [Hrenvinit [Hsenvinit [Hleninit Hcorrinit]]]]].
        have Hrenvcopy := Hrenv.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [HrEnvLen [Hreceiver Hrenvval]].
        destruct Hclass as [Hclass_ [Hobj_ [Hcname_consistent_ Hfind_consistent_]]].
        repeat split.
        exact Hclass_.
        exact Hobj_.
        apply Hcname_consistent_.
        apply Hfind_consistent_.
        apply Hfind_consistent_.
        exact Hheapinit.
        rewrite HeqrΓ'''.
        simpl.
        rewrite update_length.
        simpl.
        lia.
        destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
        exists iot.
        split.
        rewrite HeqrΓ'''.
        simpl.
        unfold gget in *.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
        discriminate Hget_iot.
        unfold get_this_var_mapping in Hget_iot.
        (* injection Hget_iot as Hv0_eq. *)
        (* subst v0. *)
        unfold update.
        destruct x as [|x'].
        easy.
        simpl.
        destruct v0 as [|loc]; [trivial|].
        exact Hget_iot.
        (* rewrite <- getmbody in Htyping_method. *)
        have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓmethodinit h (mbody_stmt (mbody mdef)) rΓ'' h' Heval.
        lia.

        (* Outter runtime env is wellformed*)
        rewrite HeqrΓ'''.
        simpl.
        eapply Forall_update; eauto.
        eapply Forall_impl; [|exact Hrenvval].
        intros v Hv.
        destruct v as [|loc]; [trivial|].
        destruct (runtime_getObj h loc) as [obj|] eqn:Hobjloc; [|contradiction].
        (* rewrite <- getmbody in Htyping_method. *)
        have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓmethodinit h (mbody_stmt (mbody mdef)) rΓ'' h' Heval.
        assert (Hloc_dom : loc < dom h) by (apply runtime_getObj_dom in Hobjloc; exact Hobjloc).
        assert (Hloc_dom' : loc < dom h') by lia.
        destruct (runtime_getObj h' loc) as [obj'|] eqn:Hobj'.
        trivial.
        exfalso. apply runtime_getObj_not_dom in Hobj'. lia.
        unfold runtime_getVal in H6.
        destruct retval as [|loc]; [trivial|].
        unfold wf_renv in Hrenvinit.
        destruct Hrenvinit as [_ [_ Hrenv_wf]].
        eapply Forall_nth_error in Hrenv_wf; eauto.
        simpl in Hrenv_wf.
        destruct (runtime_getObj h' loc) as [obj|] eqn:Hobjloc; [trivial|].
        contradiction.
        apply static_getType_dom in H13.
        rewrite Hlen in H13.
        exact H13.

        (* Length constraint *)
        rewrite Hlen.
        exact HrEnvLen.

        (* Type use is wellformed *)
        unfold wf_senv in Hsenv.
        destruct Hsenv as [Hsenvpdom Hsenvptypeuse].
        exact Hsenvptypeuse.

        (* Length constraint *)
        rewrite Hlen.
        rewrite HeqrΓ'''.
        simpl.
        rewrite update_length.
        easy.

        (* Correspondence holds for resulting variable environment *)
        intros ι qcontext HreceiverAddr Hqcontext i Hi sqt Hnth.
        destruct (Nat.eq_dec i x) as [Heq | Hneq].
        - (* Case: i = x (updated variable) *)
          subst i.
          rewrite HeqrΓ'''.
          simpl.
          unfold runtime_getVal.
          rewrite update_same.
          + apply static_getType_dom in H13.
            rewrite Hlen in H13.
            exact H13.
          + (* Show wf_r_typable for retval *)
            assert (Hnth_x : nth_error sΓ' x = Some Tx).
            {
              unfold static_getType in H13.
              exact H13.
            }
            rewrite Hnth_x in Hnth.
            injection Hnth as Hsqt_eq.
            subst sqt.
            (* Use the fact that retval is well-typed from method return *)
            unfold runtime_getVal in H6.
            destruct retval as [|loc]; [trivial|].
            assert (Hret_dom : mreturn (mbody mdef) < dom (vars rΓ'')).
            {
              apply nth_error_Some.
              rewrite H6.
              discriminate.
            }
            rewrite <- Hleninit in Hret_dom.
            assert (wf_class_table CT). {
              unfold wf_r_config in H5copy.
              destruct H5copy as [Hclass1 _].
              exact Hclass1.
            }
            destruct Hmethodret as [Hmbodyretvar_dom [Hnth_mbodyret Hsubtype_ret]].
            have Hcorr_copy := Hcorr.
            destruct Hreceiver as [recv_iot [Hget_recv_iot Hrecv_iot_dom]].
            assert (HreceiverAddrInit : get_this_var_mapping (vars rΓ'') = Some ly).
            {
              eapply eval_stmt_preserves_receiver_addr_typed; eauto.
              unfold get_this_var_mapping.
              rewrite HeqrΓmethodinit.
              easy.
            }
            assert (HInnerReceiverEndFrame : r_muttype h' ly = Some q).
            {
              eapply eval_stmt_preserves_r_muttype; eauto.
              unfold r_muttype in Hinnerthis.
              destruct (runtime_getObj h ly) as [innerthisobj|] eqn:Hinnerobj; [|discriminate].
              apply runtime_getObj_dom in Hinnerobj.
              exact Hinnerobj.
            }
            have Hcorrinit_copy := Hcorrinit.
            specialize (Hcorrinit ly q HreceiverAddrInit HInnerReceiverEndFrame (mreturn (mbody mdef)) Hret_dom mrettype Hnth_mbodyret).
            destruct (runtime_getVal rΓ'' (mreturn (mbody mdef))) eqn: Hmet_val; [|easy].
            destruct v.
            2:{
              assert (Hy_dom : y < dom sΓ').
              {
                apply static_getType_dom in H14.
                exact H14.
              }
              assert (exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
              {
                eapply get_this_exists_from_wf_r_config; eauto.
              }
              destruct H7 as [lOutterReceiver HOutterReceiverAddr].
              assert (exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
              {
                eapply receiver_mutability_exists_wf_renv with (CT:=CT); eauto.
              }
              destruct H7 as [OutterReceiverMutability HOutterReceiverMutabilityType].

              have Hcorrcopy := Hcorr.
              specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H14).
              unfold wf_r_typable in Hcorr.
              unfold r_basetype in H0.
              unfold r_type.
              destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
              injection H0 as Hcy_eq.
              subst cy.
              destruct obj as [rt_obj fields_obj].
              destruct rt_obj as [rq_obj rc_obj].

              unfold r_type in Hcorr.
              rewrite H in Hcorr.
              rewrite Hobjy in Hcorr.
              simpl in Hcorr.
              destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
              assert (Hmsigeq: msignature mdef = msignature mdef0).
              {
                eapply method_signature_consistent_subtype; eauto.
              }
              unfold runtime_getVal in Hmet_val.
              rewrite Hmet_val in H6.
              inversion H6.
              unfold wf_r_typable.
              unfold r_type.
              unfold runtime_getObj.
              subst loc.
              unfold wf_r_typable in Hcorrinit.
              unfold r_type in Hcorrinit.
              unfold runtime_getObj in Hcorrinit.
              destruct (nth_error h' l) eqn: Hobjh'; [|easy].
              destruct Hcorrinit as [Hrorettypebase Hrorettypequalifier].
              split.

              (* Base type subtyping *)
              destruct Hsubtype_ret as [Hsubtype_ret Hmethodoveride].
              apply qualified_type_subtype_base_subtype in Hsubtype_ret.
              apply qualified_type_subtype_base_subtype in H22.
              (* rewrite (vpa_mutabilty_tt_sctype Tthis Tx) in H22. *)
              (* rewrite (vpa_mutabilty_tt Ty (mret (msignature mdef0))) in H22. *)
              rewrite (vpa_mutabilty_tt_sctype Ty (mret (msignature mdef0))) in H22.
              (* rewrite (vpa_mutabilty_tt_sctype (mreceiver (msignature mdef)) mrettype) in Hsubtype_ret.
              rewrite (vpa_mutabilty_tt_sctype (mreceiver (msignature mdef)) (mret (msignature mdef))) in Hsubtype_ret. *)
              rewrite <- Hmsigeq in H22.
              eapply base_trans; eauto.
              eapply base_trans; eauto.

              (* Qualfier typability *)
              assert(HOutterReceiverAddrInit: get_this_var_mapping (vars rΓ) = Some ι).
              {
                eapply eval_stmt_preserves_receiver_addr_typed_backwards; eauto.
              }

              assert (HOutterReceiverMutabilityInit: r_muttype h ι = Some qcontext).
              {
                eapply eval_stmt_preserves_r_muttype_backwards; eauto.
              }

              rename q into qinner.
              rename qcontext into qoutter.
              assert(lOutterReceiver = ι). {
                rewrite HOutterReceiverAddrInit in HOutterReceiverAddr.
                inversion HOutterReceiverAddr; reflexivity.
              }
              subst ι.
              assert(OutterReceiverMutability = qoutter). {
                rewrite HOutterReceiverMutabilityType in HOutterReceiverMutabilityInit.
                inversion HOutterReceiverMutabilityInit; reflexivity.
              }
              subst qoutter.
              assert (rq_obj = qinner). {
                unfold r_muttype in Hinnerthis.
                rewrite Hobjy in Hinnerthis.
                simpl in Hinnerthis.
                inversion Hinnerthis; subst qinner.
                reflexivity.
              }
              subst rq_obj.

              specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddrInit HOutterReceiverMutabilityInit).
              specialize (Hcorr_copy lOutterReceiver OutterReceiverMutability HOutterReceiverAddrInit HOutterReceiverMutabilityInit).
              apply get_this_qualified_type_nth_error in H16.
              unfold wf_senv in Hsenv.
              destruct Hsenv as [Hsenvdom _].
              specialize (Hcorrcopy 0 Hsenvdom Tthis H16).
              apply get_this_var_mapping_runtime_getVal in HOutterReceiverAddrInit.
              rewrite HOutterReceiverAddrInit in Hcorrcopy.
              unfold wf_r_typable in Hcorrcopy.
              unfold r_type in Hcorrcopy.
              unfold r_muttype in HOutterReceiverMutabilityType.
              destruct (runtime_getObj h lOutterReceiver) as [outterreceiverobj|] eqn:Houtterobj; [|discriminate].
              destruct Hcorrcopy as [_ HOutterReceiverQualifierTypablility].

              assert (Hx_dom : x < dom sΓ').
              {
                apply static_getType_dom in H13.
                exact H13.
              }

              destruct Hsubtype_ret as [Hsubtype_ret _].
              apply qualified_type_subtype_q_subtype in Hsubtype_ret.
              move Hsubtype_ret at bottom.
              apply qualified_type_subtype_q_subtype in H22.
              move H22 at bottom.
              apply qualified_type_subtype_q_subtype in H23.
              move H23 at bottom.
              rewrite Hmsigeq in Hsubtype_ret.
              move HyQualifierTypablility at bottom.
              remember (mret (msignature mdef0)) as Hreturntype.
              remember (mreceiver (msignature mdef0)) as HreceiverType.

              clear IHHeval.
              inversion HOutterReceiverMutabilityType; subst OutterReceiverMutability.
              subst.
              rewrite sq_vpa_tt_eq_qq in H23.
              rewrite sq_vpa_tt_eq_qq in H22.

              clear - Hsubtype_ret H22 H23 HyQualifierTypablility HOutterReceiverQualifierTypablility Hrorettypequalifier.
              destruct (rqtype (rt_type o)) eqn:HretObjectMutability; move HretObjectMutability at bottom;
              destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverRuntimeMutability; move HOutterReceiverRuntimeMutability at bottom;
              destruct (sqtype Tx) eqn:HTxStaticMutability; move HTxStaticMutability at bottom;
              try solve_qualifier_typable_correct_concrete.
              all:
              destruct (sqtype Ty) eqn:HTyStaticMutability; move HTyStaticMutability at bottom;
              destruct (sqtype (mreceiver (msignature mdef0))) eqn: HMethodReceiverDeclaredType;
              simpl in H23;
              try solve_q_subtype_wrong.
              all:
              destruct (sqtype (mret (msignature mdef0))) eqn:HMethodDeclaredReturnType;
              simpl in H22;
              try solve_q_subtype_wrong.
              all:
              destruct (sqtype mrettype) eqn:HMethodReturnType; move HMethodReturnType at bottom;
              simpl in Hsubtype_ret;
              try solve_q_subtype_wrong.
              all:
              destruct qinner eqn:HInnerReceiverRuntimeMutability; move HInnerReceiverRuntimeMutability at bottom;
              try solve_qualifier_typable_wrong_concrete.
            }
            unfold runtime_getVal in Hmet_val.
            rewrite H6 in Hmet_val.
            easy.
        - (* Case: i ≠ x (unchanged variable) *)
          rewrite HeqrΓ'''.
          simpl.
          unfold runtime_getVal.
          rewrite update_diff; [symmetry; exact Hneq|].
          destruct Hreceiver as [outterreceiveriot [Hget_outter_iot Houtter_iot_dom]].
          assert (HoutreceiverMutabilityType: exists qrout, r_muttype h outterreceiveriot = Some qrout).
          {
            eapply receiver_mutability_exists_from_bound; eauto.
          }
          destruct HoutreceiverMutabilityType as [qrout HoutreceiverMutabilityType].
          specialize (Hcorr outterreceiveriot qrout Hget_outter_iot HoutreceiverMutabilityType i Hi sqt Hnth).
          unfold runtime_getVal in Hcorr.
          destruct (nth_error (vars rΓ) i) as [v|] eqn:Hgetval; [|exact Hcorr].
          destruct v as [|loc]; [trivial|].
          (* Need to show wf_r_typable is preserved when changing runtime environment and heap *)
          unfold wf_r_typable in Hcorr |- *.
          destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
          assert (Hrtype_preserved : r_type h' loc = Some rqt).
          {
            eapply eval_stmt_preserves_r_type; eauto.
            unfold r_type in Hrtype.
            destruct (runtime_getObj h loc) as [obj|] eqn:Hobjloc; [|discriminate].
            apply runtime_getObj_dom in Hobjloc.
            exact Hobjloc.
          }
          {
            unfold update.
            destruct x as [|x'].
            contradiction Hneq.
            easy.
            simpl.
            rewrite Hrtype_preserved.
            assert (outterreceiveriot = ι).
            {
              eapply eval_stmt_preserves_receiver_addr_eq_loc' with (rΓ:=rΓ)(rΓ':=rΓ''')(h':=h'); eauto.
            }
            subst ι.
            assert (HOutterReceiverMutabilityInit: r_muttype h outterreceiveriot = Some qcontext).
            {
              eapply eval_stmt_preserves_r_muttype_backwards; eauto.
            }
            rewrite HOutterReceiverMutabilityInit in HoutreceiverMutabilityType.
            inversion HoutreceiverMutabilityType; subst qrout.
            exact Hcorr.
          }
      }
      assert (exists D ddef, base_subtype CT cy D /\ find_class CT D = Some ddef /\ In mdef (methods (body ddef)) /\ wf_method CT D mdef).
      {
        eapply method_lookup_in_wellformed_inherited; eauto.
        eapply r_basetype_in_dom; eauto.
      }
      destruct H2 as [D H2].
      destruct H2 as [ddef H2].
      destruct H2 as [Hbasecyd [HfindD [HmdefinD H2]]].

      inversion H2; subst.
      destruct H8 as [mrettype Htyping_method].
      destruct Htyping_method as [Htyping_method Hmethodret].
      remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit.
      remember {| vars := Iot ly :: vals |} as rΓmethodinit.
      remember (rΓ <| vars := update x retval (vars rΓ) |>) as rΓ'''.
      assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
      { 
        (* Method inner config wellformed.*)
        have Hclasstable := Hclass.
        unfold  wf_class_table in Hclass.
        destruct Hclass as [Hclass [Hobj [Hotherclasses Hcname_consistent]]].
        repeat split.
        exact Hclass.
        exact Hobj.
        exact Hotherclasses.
        apply Hcname_consistent.
        apply Hcname_consistent.
        exact Hheap.
        rewrite HeqrΓmethodinit.
        simpl.
        lia.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
        exists ly.
        split.
        rewrite HeqrΓmethodinit.
        simpl.
        reflexivity.
        unfold runtime_getVal in H.
        destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
        injection H as H1_eq.
        subst v.
        eapply Forall_nth_error in Hallvals; eauto.
        simpl in Hallvals.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjly; [|contradiction].
        apply runtime_getObj_dom in Hobjly.
        exact Hobjly.

        (* Inner runtime env is wellformed *)
        rewrite HeqrΓmethodinit.
        simpl.
        constructor.
        simpl.
        unfold runtime_getVal in H.
        destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
        injection H as H1_eq.
        subst v.
        unfold runtime_getVal in Hnth_y.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [_ Hallvals]].
        eapply Forall_nth_error in Hallvals; eauto.
        simpl in Hallvals.
        exact Hallvals.
        eapply runtime_lookup_list_preserves_wf_values; eauto.

        (* Inner Static Environment's length is more than 0 *)
        rewrite HeqsΓmethodinit.
        simpl.
        lia.

        (* Inner static env's elements are wellformed typeuse *)
        rewrite HeqsΓmethodinit.
        constructor.
        subst.
        assert (parent < dom CT). {
          assert (cy < dom CT). {
            eapply find_class_dom; eauto.
          }
          assert (parent < cy). {
            eapply parent_implies_strict_ordering with (C:= cy) (D:=parent); eauto.
          }
          lia.
        }

        (* Receiver type is well-formed *)
        eapply method_sig_wf_receiver_by_find; eauto.
        assert (parent < dom CT). {
          assert (cy < dom CT). {
            eapply find_class_dom; eauto.
          }
          assert (parent < cy). {
            eapply parent_implies_strict_ordering with (C:= cy) (D:=parent); eauto.
          }
          lia.
        }
        eapply method_sig_wf_parameters_by_find; eauto.

        apply static_getType_list_preserves_length in H15.
        apply runtime_lookup_list_preserves_length in H4.
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        simpl.
        f_equal.
        apply Forall2_length in H24.
        assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H14.
          exact H14.
        }
        assert (exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
        {
          eapply get_this_exists_from_wf_r_config; eauto.
        }
        destruct H8 as [lOutterReceiver HOutterReceiverAddr].
        assert (exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
        {
          eapply receiver_mutability_exists_wf_renv; eauto.
        }
        destruct H8 as [OutterReceiverMutability HOutterReceiverMutabilityType].

        have Hcorrcopy := Hcorr.
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H14).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H0.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H0 as Hcy_eq.
        subst cy.
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot _]].
        unfold get_this_var_mapping.
        unfold gget in Hget_iot.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].

        unfold r_type in Hcorr.
        rewrite H in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
        assert (msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        rewrite H0.
        rewrite H4.
        rewrite <- H24.
        exact H15.

        (* Correspondence holds for inner environment *)
        intros ι qinner HreceiverAddr Hqcontext i Hi sqt Hnth.
        rewrite HeqsΓmethodinit in Hnth, Hi.
        rewrite HeqrΓmethodinit.
        simpl in *.
        assert (Hy_dom : y < dom sΓ').
        {
          apply static_getType_dom in H14.
          exact H14.
        }
        assert (exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
        {
          eapply get_this_exists_from_wf_r_config; eauto.
        }
        destruct H8 as [lOutterReceiver HOutterReceiverAddr].
        assert (exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
        {
          eapply receiver_mutability_exists_wf_renv; eauto.
        }
        destruct H8 as [OutterReceiverMutability HOutterReceiverMutabilityType].

        have Hcorrcopy := Hcorr.
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H14).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H0.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H0 as Hcy_eq.
        subst cy.
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        have Hrenvcopy := Hrenv.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot _]].
        unfold get_this_var_mapping.
        unfold gget in Hget_iot.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].

        unfold r_type in Hcorr.
        rewrite H in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
        
        assert (Hmsigeq: msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        destruct i as [|i'].

        (* Reciever index - 0 *)
        simpl in Hnth.
        injection Hnth as Hsqt_eq.
        subst sqt.
        simpl.
        unfold wf_r_typable.
        unfold r_type.

        rewrite Hobjy.
        simpl.
        split.

        (* Base type subtyping *)
        rewrite Hmsigeq.
        apply qualified_type_subtype_base_subtype in H23.
        (* rewrite (vpa_mutabilty_tt_sctype Tthis Ty) in H23. *)
        rewrite (vpa_mutabilty_tt_sctype Ty (mreceiver (msignature mdef0))) in H23.
        eapply base_trans; eauto.

        (* Qualifier typbility *)
        1: 
        {
          apply qualified_type_subtype_q_subtype in H23.
          specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
          apply get_this_qualified_type_nth_error in H16.
          unfold wf_senv in Hsenv.
          destruct Hsenv as [Hsenvdom _].
          specialize (Hcorrcopy 0 Hsenvdom Tthis H16).
          rewrite <- Hvars in HOutterReceiverAddr.
          apply get_this_var_mapping_runtime_getVal in HOutterReceiverAddr.
          rewrite HOutterReceiverAddr in Hcorrcopy.
          unfold wf_r_typable in Hcorrcopy.
          unfold r_type in Hcorrcopy.
          destruct (runtime_getObj h lOutterReceiver) as [outterreceiverobj|] eqn:Houtterobj; [|easy].
          destruct Hcorrcopy as [_ Houtter_qualifier_typable].

          assert (rqtype (rt_type outterreceiverobj) = OutterReceiverMutability).
          {
            unfold r_muttype in HOutterReceiverMutabilityType.
            rewrite Houtterobj in HOutterReceiverMutabilityType.
            simpl in HOutterReceiverMutabilityType.
            inversion HOutterReceiverMutabilityType; subst OutterReceiverMutability.
            reflexivity.
          }
          subst OutterReceiverMutability.

          assert (ly = ι). 
          {
            rewrite HeqrΓmethodinit in HreceiverAddr.
            unfold get_this_var_mapping in HreceiverAddr.
            simpl in HreceiverAddr.
            inversion HreceiverAddr; reflexivity.
          }
          subst ι.

          assert (r_muttype h ly = Some rq_obj).
          {
            unfold r_muttype.
            rewrite Hobjy.
            simpl.
            reflexivity.
          }

          assert (rq_obj = qinner).
          {
            rewrite H0 in Hqcontext.
            inversion Hqcontext; subst qinner.
            reflexivity.
          }
          subst rq_obj.

          unfold qualifier_typable_context.
          unfold qualifier_typable_context in HyQualifierTypablility.
          unfold qualifier_typable_context in Houtter_qualifier_typable.
          unfold vpa_mutabilty_rs.
          unfold vpa_mutabilty_rs in HyQualifierTypablility.
          unfold vpa_mutabilty_rs in Houtter_qualifier_typable.
          unfold vpa_mutabilty_tt in H23.
          rewrite <- Hmsigeq in H23.

          destruct qinner eqn:HInnerReceiverMutability;
          destruct (sqtype (mreceiver (msignature mdef))) eqn:HMethodReceiverDeclaredType;
          try trivial.
          all: destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
          destruct (sqtype Ty) eqn:HTyStaticMutability;
          try trivial.
          all: destruct (sqtype Tthis) eqn:HTthisStaticMutability;
          try rewrite HTyStaticMutability in H23;
          simpl in H23;
          try rewrite HMethodReceiverDeclaredType in H23;
          try inversion H23; try trivial.
          all: try inversion H23; try easy.
        }
        (* clear_dups. amazing.... *)

  (* -------------------------------------------------- *)
  (* Other index - > 1 *)
        apply qualified_type_subtype_q_subtype in H22.
        unfold runtime_getVal.
        simpl.
        destruct (nth_error vals i') as [v|] eqn:Hval_i.
          - (* Parameter i' exists *)
            destruct v as [|loc]; [trivial|].
            (* Use H23 to get the subtyping relationship *)
            assert (Hi'_bound : i' < List.length argtypes).
            {
              apply Forall2_length in H24.
              simpl in Hi.
              simpl in Hnth.
              rewrite Hmsigeq in Hnth.
              rewrite H24.
              apply nth_error_Some.
              intros Hnone.
              rewrite Hnth in Hnone.
              discriminate.
            }
            assert (Harg_type : exists argtype, nth_error argtypes i' = Some argtype).
            {
              apply nth_error_Some_exists.
              exact Hi'_bound.
            }
            assert (loc < dom h).
            {
              assert (Hvals_wf :
              Forall
                (fun v =>
                  match v with
                  | Null_a => True
                  | Iot loc =>
                      match runtime_getObj h loc with
                      | Some _ => True
                      | None => False
                      end
                  end) vals).
              {
                eapply runtime_lookup_list_preserves_wf_values; eauto.
              }
              eapply Forall_nth_error in Hvals_wf; eauto.
              simpl in Hvals_wf.
              destruct (runtime_getObj h loc) as [argobj|] eqn:Hargobjloc; [|contradiction].
              apply runtime_getObj_dom in Hargobjloc.
              exact Hargobjloc.
            }
            destruct Harg_type as [argtype Hargtype].
            unfold wf_r_typable.
            unfold r_type.
            destruct (runtime_getObj h loc) as [argobj|] eqn:Hargobjloc; [|apply runtime_getObj_not_dom in Hargobjloc; lia].
            assert (HargtypeFromsEnv :
              exists iArgInSenv,
                nth_error sΓ' iArgInSenv = Some argtype
            /\ nth_error zs i' = Some iArgInSenv).
            {
              destruct (static_getType_list_nth_zs sΓ' zs argtypes i' argtype H15 Hargtype)
                as [j [Hzs_j Hst_j]].
              exists j.
              split.
              - (* from static_getType to nth_error sΓ' *)
                unfold static_getType in Hst_j; exact Hst_j.
              - (* keep the zs fact *)
                exact Hzs_j.
            }
            destruct HargtypeFromsEnv as [iArgInSenv [HargtypeFromsEnv Hzs_iArg]].

            assert (Hi'dom : iArgInSenv < dom sΓ').
            {
              apply nth_error_Some.
              rewrite HargtypeFromsEnv; discriminate.
            }
            assert (HargtypeFromrEnv :
                      nth_error (vars rΓ) iArgInSenv = Some (Iot loc)).
            {
              destruct (runtime_lookup_list_nth_zs rΓ zs vals i' (Iot loc) H4 Hval_i)
                as [j [Hzs_j Hget_j]].
              assert (HiEq : iArgInSenv = j).
              {
                (* zs[i'] = Some iArgInSenv and zs[i'] = Some j ⇒ iArgInSenv = j *)
                rewrite Hzs_iArg in Hzs_j.
                inversion Hzs_j; reflexivity.
              }
              subst iArgInSenv.
              unfold runtime_getVal in Hget_j.
              exact Hget_j.
            }
            have Hcorrcopy_2 := Hcorrcopy.
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType iArgInSenv Hi'dom argtype HargtypeFromsEnv).
            unfold runtime_getVal in Hcorrcopy.
            rewrite HargtypeFromrEnv in Hcorrcopy.
            unfold wf_r_typable in Hcorrcopy.
            unfold r_type in Hcorrcopy.
            rewrite Hargobjloc in Hcorrcopy.
            destruct Hcorrcopy as [Harg_basesubtype Harg_qualifiertypability].
            split.

            (* base subtype *)
            rewrite nth_error_cons_succ in Hnth.
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in H24; eauto.
            apply qualified_type_subtype_base_subtype in H24.
            rewrite (vpa_mutabilty_tt_sctype Ty sqt) in H24.
            eapply base_trans; eauto.

            (* Qualifier Typability *)
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in H24; eauto.
            apply qualified_type_subtype_q_subtype in H24.
            rewrite sq_vpa_tt_eq_qq in H24.
            specialize (Hcorrcopy_2 lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            apply get_this_qualified_type_nth_error in H16.
            specialize (Hcorrcopy_2 0 Hsenvdom Tthis H16).
            rewrite <- Hvars in Hget_iot.
            apply get_this_var_mapping_runtime_getVal in Hget_iot.
            rewrite Hget_iot in Hcorrcopy_2.
            unfold wf_r_typable in Hcorrcopy_2.
            unfold r_type in Hcorrcopy_2.
            destruct (runtime_getObj h iot) as [outterreceiverobj|] eqn:Houtterobj; [|easy].
            destruct Hcorrcopy_2 as [_ HOutterReceiverQualifierTypablility].
            assert (rqtype (rt_type outterreceiverobj) = OutterReceiverMutability).
            {
              clear - Houtterobj HOutterReceiverMutabilityType HOutterReceiverAddr Hget_iot Hvars.
              rewrite <- Hvars in HOutterReceiverAddr.
              apply get_this_var_mapping_runtime_getVal in HOutterReceiverAddr.
              rewrite Hget_iot in HOutterReceiverAddr.
              inversion HOutterReceiverAddr; subst lOutterReceiver.
              unfold r_muttype in HOutterReceiverMutabilityType.
              rewrite Houtterobj in HOutterReceiverMutabilityType.
              simpl in HOutterReceiverMutabilityType.
              inversion HOutterReceiverMutabilityType; reflexivity.
            }
            subst OutterReceiverMutability.
            assert (ι = ly).
            {
              unfold get_this_var_mapping in HreceiverAddr.
              rewrite HeqrΓmethodinit in HreceiverAddr.
              simpl in HreceiverAddr.
              inversion HreceiverAddr; reflexivity.
            }
            subst ι.
            assert(rq_obj = qinner).
            {
              unfold r_muttype in Hqcontext.
              rewrite Hobjy in Hqcontext.
              simpl in Hqcontext.
              inversion Hqcontext.
              easy.
            }
            subst rq_obj.
            clear - H24 Harg_qualifiertypability HyQualifierTypablility HOutterReceiverQualifierTypablility.

            destruct (rqtype (rt_type argobj)) eqn:Hargobjmutability; move Hargobjmutability at bottom;
            destruct (sqtype sqt) eqn:HParameterStaticDeclearedMutability; move HParameterStaticDeclearedMutability at bottom;
            destruct qinner eqn:HInnerReceiverMutability; move HInnerReceiverMutability at bottom;
            try solve_qualifier_typable_correct_concrete.

            all: destruct (sqtype Ty) eqn:HTyStaticMutability;
            destruct (sqtype argtype) eqn:HArgTypeStaticMutability;
            simpl in H24;
            try solve_q_subtype_wrong.

            all: 
            destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            try solve_qualifier_typable_wrong_concrete.

          - (* Parameter i' doesn't exist - contradiction *)
            exfalso.
            apply nth_error_None in Hval_i.
            apply runtime_lookup_list_preserves_length in H4.
            apply static_getType_list_preserves_length in H15.
            apply Forall2_length in H24.
            rewrite H4 in Hval_i.
            rewrite <- H15 in Hval_i.
            rewrite H24 in Hval_i.
            simpl in Hi.
            simpl in Hnth.
            rewrite <- Hmsigeq in Hval_i.
            lia.
      }
      rename x0 into sΓmethodend.
      assert (wf_r_config CT sΓmethodend rΓ'' h'). 
      {
        eapply IHHeval with (sΓ := sΓmethodinit) (sΓ' := sΓmethodend); eauto.
      }
      
      { (* Method call resulting config is wellformed *)
        have H8copy := H8.
        unfold wf_r_config.
        unfold wf_r_config in H8.
        destruct H8 as [_ [Hheapinit [Hrenvinit [Hsenvinit [Hleninit Hcorrinit]]]]].
        unfold wf_renv in Hrenv.
        destruct Hrenv as [HrEnvLen [Hreceiver Hrenvval]].
        destruct Hclass as [Hclass_ [Hobj_ [Hcname_consistent_ Hfind_consistent_]]].
        repeat split.
        exact Hclass_.
        exact Hobj_.
        apply Hcname_consistent_.
        apply Hfind_consistent_.
        apply Hfind_consistent_.
        exact Hheapinit.
        rewrite HeqrΓ'''.
        simpl.
        rewrite update_length.
        simpl.
        lia.

        destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
        exists iot.
        split.
        rewrite HeqrΓ'''.
        simpl.
        unfold gget in *.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars.
        discriminate Hget_iot.
        (* injection Hget_iot as Hv0_eq. *)
        (* subst v0. *)
        unfold update.
        destruct x as [|x'].
        easy.
        simpl.
        destruct v0 as [|loc]; [trivial|].
        unfold get_this_var_mapping in Hget_iot.
        exact Hget_iot.

        (* length constraint *)
        have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓmethodinit h (mbody_stmt (mbody mdef)) rΓ'' h' Heval.
        lia.

        (* Outter runtime env is wellformed*)
        rewrite HeqrΓ'''.
        simpl.
        eapply Forall_update; eauto.
        eapply Forall_impl; [|exact Hrenvval].
        intros v Hv.
        destruct v as [|loc]; [trivial|].
        destruct (runtime_getObj h loc) as [obj|] eqn:Hobjloc; [|contradiction].
        (* rewrite <- getmbody in Htyping_method. *)
        have Hdom_le := eval_stmt_preserves_heap_domain_simple CT rΓmethodinit h (mbody_stmt (mbody mdef)) rΓ'' h' Heval.
        assert (Hloc_dom : loc < dom h) by (apply runtime_getObj_dom in Hobjloc; exact Hobjloc).
        assert (Hloc_dom' : loc < dom h') by lia.
        destruct (runtime_getObj h' loc) as [obj'|] eqn:Hobj'.
        trivial.
        exfalso. apply runtime_getObj_not_dom in Hobj'. lia.
        unfold runtime_getVal in H6.
        destruct retval as [|loc]; [trivial|].
        unfold wf_renv in Hrenvinit.
        destruct Hrenvinit as [_ [_ Hrenv_wf]].
        eapply Forall_nth_error in Hrenv_wf; eauto.
        simpl in Hrenv_wf.
        destruct (runtime_getObj h' loc) as [obj|] eqn:Hobjloc; [trivial|].
        contradiction.
        apply static_getType_dom in H13.
        rewrite Hlen in H13.
        exact H13.

        rewrite Hlen.
        exact HrEnvLen.
        unfold wf_senv in Hsenv.
        destruct Hsenv as [Hsenvpdom Hsenvptypeuse].
        exact Hsenvptypeuse.

        rewrite Hlen.
        rewrite HeqrΓ'''.
        simpl.
        rewrite update_length.
        easy.

        intros ι qoutter HOutterReceiverAddr HOutterReceiverMutability i Hi sqt Hnth.
        destruct (Nat.eq_dec i x) as [Heq | Hneq].
        - (* Case: i = x (updated variable) *)
          subst i.
          rewrite HeqrΓ'''.
          simpl.
          unfold runtime_getVal.
          rewrite update_same.
          + apply static_getType_dom in H13.
            rewrite Hlen in H13.
            exact H13.
          + (* Show wf_r_typable for retval *)
            assert (Hnth_x : nth_error sΓ' x = Some Tx).
            {
              unfold static_getType in H13.
              exact H13.
            }
            rewrite Hnth_x in Hnth.
            injection Hnth as Hsqt_eq.
            subst sqt.
            (* Use the fact that retval is well-typed from method return *)
            unfold runtime_getVal in H6.
            destruct retval as [|loc]; [trivial|].
            assert (Hret_dom : mreturn (mbody mdef) < dom (vars rΓ'')).
            {
              apply nth_error_Some.
              rewrite H6.
              discriminate.
            }
            rewrite <- Hleninit in Hret_dom.
            assert (wf_class_table CT). {
              unfold wf_r_config in H8copy.
              destruct H8copy as [Hclass1 _].
              exact Hclass1.
            }
            destruct Hmethodret as [Hmbodyretvar_dom [Hnth_mbodyret Hsubtype_ret]].
            have Hcorr_copy := Hcorr.

            assert (HInnerReceiverAddr: get_this_var_mapping (vars rΓ'') = Some ly).
            {
              eapply eval_stmt_preserves_receiver_addr_typed with (rΓ:=rΓmethodinit)(rΓ':=rΓ''); eauto.
              unfold get_this_var_mapping.
              rewrite HeqrΓmethodinit.
              easy.
            }
            assert (HInnerReceiverMutability: exists InnerReceiverMutability, r_muttype h' ly = Some InnerReceiverMutability).
            {
              eapply receiver_mutability_exists_from_bound; eauto.
              unfold r_basetype in H0.
              destruct (runtime_getObj h ly) as [objly|] eqn:Hobj; [|discriminate].
              apply runtime_getObj_dom in Hobj.
              assert (dom h <= dom h'). {
                eapply eval_stmt_preserves_heap_domain_simple; eauto.
              }
              lia.
            }
            assert (HOutterReceiverAddrInit: get_this_var_mapping (vars rΓ) = Some ι).
            {
              eapply eval_stmt_preserves_receiver_addr_typed_backwards; eauto.
            }
            destruct Hreceiver as [outterreceiveinitriot [Hget_outter_iot Houtter_iot_dom]].
            assert (outterreceiveinitriot = ι).
            {
              eapply eval_stmt_preserves_receiver_addr_eq_loc' with (rΓ:=rΓ)(rΓ':=rΓ''')(h':=h'); eauto.
            }
            assert (HOutterReceiverMutabilityInit: r_muttype h outterreceiveinitriot = Some qoutter).
            {
              eapply eval_stmt_preserves_r_muttype_backwards; eauto.
            }
            subst ι.
            destruct HInnerReceiverMutability as [InnerReceiverMutability HInnerReceiverMutability].
            specialize (Hcorrinit ly InnerReceiverMutability HInnerReceiverAddr HInnerReceiverMutability).
            specialize (Hcorrinit (mreturn (mbody mdef)) Hret_dom mrettype Hnth_mbodyret).
            unfold wf_r_typable.
            unfold r_type.
            destruct (runtime_getObj h' loc) as [retobj|] eqn:HReturnObject.
            2:{
              unfold runtime_getVal in Hcorrinit.
              rewrite H6 in Hcorrinit.
              unfold wf_r_typable in Hcorrinit.
              unfold r_type in Hcorrinit.
              rewrite HReturnObject in Hcorrinit.
              easy.
            }
            specialize (Hcorr outterreceiveinitriot qoutter Hget_outter_iot HOutterReceiverMutabilityInit).
            have H14copy := H14.
            apply static_getType_dom in H14.
            specialize (Hcorr y H14 Ty H14copy).
            rewrite H in Hcorr.
            unfold wf_r_typable in Hcorr; unfold r_type in Hcorr.
            destruct (runtime_getObj h ly) as [objly|] eqn:Hobj; [|contradiction].
            destruct Hcorr as [HyBasetype HyQualifierTypability].
            assert (rctype (rt_type objly) = cy).
            {
              unfold r_basetype in H0.
              rewrite Hobj in H0.
              simpl in H0.
              inversion H0; subst cy.
              reflexivity.
            }
            subst cy.
            assert (Hmsigeq: msignature mdef = msignature mdef0).
            {
              eapply method_signature_consistent_subtype; eauto.
            }
            rewrite Hleninit in Hmbodyretvar_dom.
            destruct (runtime_getVal rΓ'' (mreturn (mbody mdef))) eqn: Hmet_val; [|easy].
            destruct v.
            2:{
              unfold runtime_getVal in Hmet_val.
              rewrite Hmet_val in H6.
              inversion H6.
              unfold wf_r_typable.
              unfold r_type.
              unfold runtime_getObj.
              subst loc.
              unfold wf_r_typable in Hcorrinit.
              unfold r_type in Hcorrinit.
              unfold runtime_getObj in Hcorrinit.
              destruct (nth_error h' l) eqn: Hobjh'; [|contradiction].
              assert (o = retobj).
              {
                unfold runtime_getObj in HReturnObject.
                rewrite Hobjh' in HReturnObject.
                inversion HReturnObject; subst retobj.
                reflexivity.
              }
              subst o.
              destruct Hcorrinit as [Hrorettypebase Hrorettypequalifier].
              destruct Hsubtype_ret as [Hsubtype_ret Hmethodoveride].
            
              split.
              (* Base type subtyping *)
              apply qualified_type_subtype_base_subtype in H22.
              (* rewrite (vpa_mutabilty_tt_sctype Tthis Tx) in H22. *)
              rewrite (vpa_mutabilty_tt_sctype Ty (mret (msignature mdef0))) in H22.
              (* rewrite (vpa_mutabilty_tt_sctype Ty (mret (msignature mdef0))) in H22. *)
              rewrite Hmsigeq in Hsubtype_ret.
              apply qualified_type_subtype_base_subtype in Hsubtype_ret.
              (* rewrite (vpa_mutabilty_tt_sctype (mreceiver (msignature mdef0)) mrettype) in Hsubtype_ret. *)
              (* rewrite (vpa_mutabilty_tt_sctype (mreceiver (msignature mdef0)) (mret (msignature mdef0))) in Hsubtype_ret. *)
              eapply base_trans; eauto.
              eapply base_trans; eauto.

              (* Qualifier Typability *)
              move Hrorettypequalifier at bottom.
              apply qualified_type_subtype_q_subtype in H22.
              move H22 at bottom.
              move Hcorr_copy at bottom.
              specialize (Hcorr_copy outterreceiveinitriot qoutter Hget_outter_iot HOutterReceiverMutabilityInit).
              unfold wf_senv in Hsenv.
              destruct Hsenv as [Hsenvdom _].
              apply get_this_qualified_type_nth_error in H16.
              specialize (Hcorr_copy 0 Hsenvdom Tthis H16).
              apply get_this_var_mapping_runtime_getVal in Hget_outter_iot.
              rewrite Hget_outter_iot in Hcorr_copy.
              unfold wf_r_typable in Hcorr_copy.
              unfold r_type in Hcorr_copy.
              destruct (runtime_getObj h outterreceiveinitriot) as [outterreceiverobj|] eqn:Houtterobj; [|easy].
              destruct Hcorr_copy as [_ Houtter_qualifier_typable].
              assert (rqtype (rt_type outterreceiverobj) = qoutter).
              {
                unfold r_muttype in HOutterReceiverMutabilityInit.
                rewrite Houtterobj in HOutterReceiverMutabilityInit.
                simpl in HOutterReceiverMutabilityInit.
                inversion HOutterReceiverMutabilityInit; subst qoutter.
                reflexivity.
              }
              subst qoutter.
              assert (rqtype (rt_type objly) = InnerReceiverMutability).
              {
                assert (r_muttype h ly = Some InnerReceiverMutability).
                {
                  eapply eval_stmt_preserves_r_muttype_backwards; eauto.
                  apply runtime_getObj_dom in Hobj.
                  lia.
                }
                unfold r_muttype in H9.
                rewrite Hobj in H9.
                simpl in H9.
                inversion H9; subst InnerReceiverMutability.
                reflexivity.
              }
              subst InnerReceiverMutability.
              move Hsubtype_ret at bottom.
              move H23 at bottom.
              apply qualified_type_subtype_q_subtype in Hsubtype_ret.
              apply qualified_type_subtype_q_subtype in H23.
              rewrite <- Hmsigeq in H22.
              rewrite <- Hmsigeq in H23.

              clear - Hrorettypequalifier H22 Houtter_qualifier_typable Hsubtype_ret H23 HyQualifierTypability.
              rewrite sq_vpa_tt_eq_qq in H22.
              rewrite sq_vpa_tt_eq_qq in H23.
              destruct (rqtype (rt_type retobj)) eqn:Hrorettypemutability; move Hrorettypequalifier at bottom;
              destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutabilityValue; move HOutterReceiverMutabilityValue at bottom;
              destruct (sqtype Tx) eqn:HTxStaticMutability; move HTxStaticMutability at bottom;
              try solve_qualifier_typable_correct_concrete.

              all:
              destruct ((sqtype (mreceiver (msignature mdef)))) eqn:HMethodReceiverDeclaredType;
              destruct (sqtype Ty) eqn:HTyStaticMutability;
              simpl in H23;
              try solve_q_subtype_wrong.
              
              all:
              destruct (sqtype (mret (msignature mdef))) eqn:HMethodRetDeclaredType;
              simpl in H22;
              try solve_q_subtype_wrong.

              all:
              destruct (sqtype mrettype) eqn: HMethodRetType;
              simpl in Hsubtype_ret;
              try solve_q_subtype_wrong.

              all:
              destruct (rqtype (rt_type objly)) eqn:HInnerReceiverMutabilityValue;
              try solve_qualifier_typable_wrong_concrete.
            }
            unfold runtime_getVal in Hmet_val.
            rewrite H6 in Hmet_val.
            easy.
        - (* Case: i ≠ x (unchanged variable) *)
          rewrite HeqrΓ'''.
          simpl.
          unfold runtime_getVal.
          rewrite update_diff; [symmetry; exact Hneq|].
          destruct Hreceiver as [outterreceiveinitriot [Hget_outter_iot Houtter_iot_dom]].
          assert (outterreceiveinitriot = ι).
          {
            eapply eval_stmt_preserves_receiver_addr_eq_loc' with (rΓ:=rΓ)(rΓ':=rΓ''')(h':=h'); eauto.
          }
          subst ι.
          assert (HOutterReceiverMutabilityInit: r_muttype h outterreceiveinitriot = Some qoutter).
          {
            eapply eval_stmt_preserves_r_muttype_backwards; eauto.
          }
          specialize (Hcorr outterreceiveinitriot qoutter Hget_outter_iot HOutterReceiverMutabilityInit i Hi sqt Hnth).
          unfold runtime_getVal in Hcorr.
          destruct (nth_error (vars rΓ) i) as [v|] eqn:Hgetval; [|exact Hcorr].
          destruct v as [|loc]; [trivial|].
          (* Need to show wf_r_typable is preserved when changing runtime environment and heap *)
          unfold wf_r_typable in Hcorr |- *.
          destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
          assert (Hrtype_preserved : r_type h' loc = Some rqt).
          {
            eapply eval_stmt_preserves_r_type; eauto.
            unfold r_type in Hrtype.
            destruct (runtime_getObj h loc) as [obj|] eqn:Hobjloc; [|discriminate].
            apply runtime_getObj_dom in Hobjloc.
            exact Hobjloc.
          }
          {
            unfold update.
            destruct x as [|x'].
            contradiction Hneq.
            easy.
            simpl.
            rewrite Hrtype_preserved.
            exact Hcorr.
          }
      }
    }
  - (* Case: stmt = Skip *)
    eapply preservation_skip; eauto.
  - (* Case: stmt = Local *)
    eapply preservation_local_ok; eauto.
  - (* Case: stmt = VarAss *)
    eapply preservation_varass_ok; eauto.
  - (* Case: stmt = FldWrite *)
    eapply preservation_fldwrite_ok; eauto.
  - (* Case: stmt = New *)
    eapply preservation_new_ok; eauto.
  - (* Case: stmt = Seq *)
    intros. inversion Htyping; subst.
    specialize (IHHeval1 eq_refl Heval1 sΓ'0 sΓ Hwf H4) as IH1.
    specialize (IHHeval2 eq_refl Heval2 sΓ' sΓ'0 IH1 H6) as IH2.
    exact IH2.
Qed.

Notation "l [ i ]" := (nth_error l i) (at level 50).
