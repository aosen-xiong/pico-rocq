From Stdlib Require Import List.
Import ListNotations.

Require Import Syntax Helpers ViewpointAdaptation Typing Bigstep Properties.

(** Allocation changes both the heap and the runtime environment. The following
    regression checks that ordinary execution composes the allocation with the
    subsequent [skip]. *)
Example allocation_then_skip_executes :
  forall CT rGamma h x qc c args receiver receiver_q values object
    adapted rGamma' h',
    runtime_getVal rGamma 0 = Some (Iot receiver) ->
    runtime_lookup_list rGamma args = Some values ->
    r_muttype h receiver = Some receiver_q ->
    vpa_mutability_object_creation receiver_q qc = adapted ->
    object = mkObj (mkruntime_type adapted c) values ->
    h' = h ++ [object] ->
    rGamma' = set_vars rGamma
      (update x (Iot (dom h)) rGamma.(vars)) ->
    eval_stmt CT rGamma h (SSeq (SNew x qc c args) SSkip)
      OK rGamma' h'.
Proof.
  intros CT rGamma h x qc c args receiver receiver_q values object
    adapted rGamma' h' Hreceiver Hargs Hmut Hadapt Hobject Hheap Henv.
  eapply SBS_Seq with (rΓ' := rGamma') (h' := h').
  - eapply SBS_New; eauto.
  - apply SBS_Skip.
Qed.

(** Direct null dereferences still produce [NPE]. *)
Example field_write_npe_executes :
  forall CT rGamma h x f y,
    runtime_getVal rGamma x = Some Null_a ->
    eval_stmt CT rGamma h (SFldWrite x f y) NPE rGamma h.
Proof.
  intros. apply SBS_FldWrite_NPE. assumption.
Qed.

(** A first-statement [NPE] propagates through sequencing. *)
Example sequence_propagates_npe :
  forall CT rGamma h s1 s2 rGamma' h',
    eval_stmt CT rGamma h s1 NPE rGamma' h' ->
    eval_stmt CT rGamma h (SSeq s1 s2) NPE rGamma' h'.
Proof.
  intros. apply SBS_Seq_NPE_first. assumption.
Qed.

(** A non-assignable field write produces [MUTATIONEXP] without changing the
    environment or heap. *)
Example field_write_mutation_exception_executes :
  forall CT rGamma h x f y loc_x object assignability old_value new_value,
    runtime_getVal rGamma x = Some (Iot loc_x) ->
    runtime_getObj h loc_x = Some object ->
    getVal object.(fields_map) f = Some old_value ->
    sf_assignability_rel CT (rctype (rt_type object)) f assignability ->
    runtime_getVal rGamma y = Some new_value ->
    runtime_vpa_assignability (rqtype (rt_type object)) assignability = Final ->
    eval_stmt CT rGamma h (SFldWrite x f y) MUTATIONEXP rGamma h.
Proof.
  intros. eapply SBS_FldWrite_MUTATIONEXP; eauto.
Qed.

(** A first-statement mutation exception propagates through sequencing. *)
Example sequence_propagates_mutation_exception :
  forall CT rGamma h s1 s2 rGamma' h',
    eval_stmt CT rGamma h s1 MUTATIONEXP rGamma' h' ->
    eval_stmt CT rGamma h (SSeq s1 s2) MUTATIONEXP rGamma' h'.
Proof.
  intros. apply SBS_Seq_MUTATIONEXP_first. assumption.
Qed.
