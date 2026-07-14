From Stdlib Require Import List.
Import ListNotations.

Require Import Syntax Helpers ViewpointAdaptation Bigstep Properties.

(** Regression for the former protected-set mismatch in sequences.

    Allocation changes both the heap and the runtime environment.  The
    following [skip] must nevertheless execute under the same arbitrary ghost
    set [P], rather than recomputing a set from the intermediate state. *)
Example allocation_then_skip_threads_fixed_protected_set :
  forall P CT rGamma h x qc c args receiver receiver_q values object
    adapted rGamma' h',
    runtime_getVal rGamma 0 = Some (Iot receiver) ->
    runtime_lookup_list rGamma args = Some values ->
    r_muttype h receiver = Some receiver_q ->
    vpa_mutability_object_creation receiver_q qc = adapted ->
    object = mkObj (mkruntime_type adapted c) values ->
    h' = h ++ [object] ->
    rGamma' = set_vars rGamma
      (update x (Iot (dom h)) rGamma.(vars)) ->
    eval_stmt OK P CT rGamma h (SSeq (SNew x qc c args) SSkip)
      OK P rGamma' h'.
Proof.
  intros P CT rGamma h x qc c args receiver receiver_q values object
    adapted rGamma' h' Hreceiver Hargs Hmut Hadapt Hobject Hheap Henv.
  eapply SBS_Seq with (rΓ' := rGamma') (h' := h').
  - eapply SBS_New; eauto.
  - apply SBS_Skip.
Qed.

(** The ghost set neither enables nor disables any expression execution. *)
Example expression_execution_redecorates :
  forall input_result P Q CT rGamma h expression value output_result
    rGamma' h',
    eval_expr input_result P CT rGamma h expression value output_result P
      rGamma' h' ->
    eval_expr input_result Q CT rGamma h expression value output_result Q
      rGamma' h'.
Proof.
  intros. eapply eval_expr_protected_set_irrelevant; eauto.
Qed.

(** Redecoration also covers exceptional statement outcomes, because the
    result is universally quantified. *)
Example statement_execution_redecorates :
  forall input_result P Q CT rGamma h statement output_result rGamma' h',
    eval_stmt input_result P CT rGamma h statement output_result P
      rGamma' h' ->
    eval_stmt input_result Q CT rGamma h statement output_result Q
      rGamma' h'.
Proof.
  intros. eapply eval_stmt_protected_set_irrelevant; eauto.
Qed.
