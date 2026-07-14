From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import ownp.

Require Import Syntax Helpers Typing Subtyping Bigstep.
Require Import Core.GenericCacheProtocol Core.GenericDerivedCache.
Require Import Iris.GenericCacheGhostState.
Require Import Examples.PicoIfZeroCacheExamples.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage
  PICOBridge.PicoIrisCoreInvariant PICOBridge.PicoIrisTypingSupport
  PICOBridge.PicoIrisTypingFundamental
  PICOBridge.PicoIrisSemImmOperations
  PICOBridge.PicoIrisSemImmLogicalRelation PICOBridge.PicoIrisSemanticAPI
  PICOBridge.PicoCacheTyping.

(** * Hash Cache as a Bespoke Semantic API

    The local-copy trace proof supplies the functional half of the API
    boundary.  A concrete source method is exported only after its body has
    also been proved to inhabit the Iris method contract below. *)

Definition pico_hash_decode_args (_ : r_env) : option unit := Some tt.

Definition pico_hash_decode_result (v : value) : option value := Some v.

Definition pico_hash_method_contract_for
    (receiver_ok : Loc -> Prop) (H : nat) :
    PicoSemanticMethodContract :=
  {| psmc_pre := fun entry _ =>
       exists receiver,
         runtime_getVal entry cache_receiver = Some (Iot receiver) /\
         receiver_ok receiver;
     psmc_post := fun _ result =>
       pcv_result result = OK /\
       exists returned,
         runtime_getVal (pcv_env result) cache_result = Some returned /\
         pico_hash_decode_result returned = Some (hash_pure_result H tt) |}.

Definition pico_hash_method_contract (H : nat) : PicoSemanticMethodContract :=
  pico_hash_method_contract_for (fun _ => True) H.

Definition pico_hash_method_contract_at (receiver : Loc) (H : nat) :
    PicoSemanticMethodContract :=
  pico_hash_method_contract_for (fun loc => loc = receiver) H.

Definition pico_hash_compute_stmt (H : nat) : stmt :=
  SVarAss cache_tmp (EInt H).

Definition pico_hash_method_core_stmt_with (compute : stmt) : stmt :=
  pico_local_copy_cache_stmt compute.

Definition pico_hash_method_core_stmt (H : nat) : stmt :=
  pico_hash_method_core_stmt_with (pico_hash_compute_stmt H).

Definition pico_hash_method_stmt_with (compute : stmt) : stmt :=
  SSeq (SLocal int_type cache_tmp)
    (SSeq (SLocal int_type cache_result)
      (pico_hash_method_core_stmt_with compute)).

Definition pico_hash_method_stmt (H : nat) : stmt :=
  pico_hash_method_stmt_with (pico_hash_compute_stmt H).

Definition pico_hash_method_signature
    (receiver_type : qualified_type) (method : method_name) : method_sig :=
  {| mtype := AbstractImm;
     mret := int_type;
     mname := method;
     mreceiver := receiver_type;
     mparams := [] |}.

Definition pico_hash_method_def_with
    (receiver_type : qualified_type) (method : method_name) (compute : stmt) :
    method_def :=
  {| msignature := pico_hash_method_signature receiver_type method;
     mbody := {| mbody_stmt := pico_hash_method_stmt_with compute;
                 mreturn := cache_result |} |}.

Definition pico_hash_method_def
    (receiver_type : qualified_type) (method : method_name) (H : nat) :
    method_def :=
  pico_hash_method_def_with receiver_type method (pico_hash_compute_stmt H).

Definition pico_double_read_hash_method_stmt (H : nat) : stmt :=
  SSeq (SLocal int_type cache_tmp)
    (SSeq (SLocal int_type cache_result)
      (pico_double_read_cache_stmt (pico_hash_compute_stmt H))).

Definition pico_double_read_hash_method_def
    (receiver_type : qualified_type) (method : method_name) (H : nat) :
    method_def :=
  {| msignature := pico_hash_method_signature receiver_type method;
     mbody := {| mbody_stmt := pico_double_read_hash_method_stmt H;
                 mreturn := cache_result |} |}.

Lemma pico_double_read_hash_method_def_wf : forall
    CT C receiver_type method H
    (Htyping : stmt_typing CT [receiver_type] AbstractImm
      (pico_double_read_hash_method_stmt H)
      [receiver_type; int_type; int_type])
    (Hoverride : forall parent_def parent mdef_parent,
      find_class CT C = Some parent_def ->
      super (signature parent_def) = Some parent ->
      FindMethodWithName CT parent method mdef_parent ->
      msignature mdef_parent = pico_hash_method_signature receiver_type method),
    wf_method CT C (pico_double_read_hash_method_def receiver_type method H).
Proof.
  intros CT C receiver_type method H Htyping Hoverride.
  unfold wf_method; simpl.
  exists [receiver_type; int_type; int_type], int_type.
  split; [exact Htyping |].
  split; [unfold cache_result; simpl; lia |].
  split; [unfold cache_result; reflexivity |].
  split.
  - apply qtype_sub; simpl.
    + reflexivity.
    + reflexivity.
    + constructor; discriminate.
    + constructor.
  - intros parent_def parent mdef_parent Hclass Hsuper Hfind.
    eapply Hoverride; eauto.
Qed.

Lemma pico_hash_method_typing_parts_with : forall CT receiver_type compute,
  stmt_typing CT [receiver_type] AbstractImm
    (pico_hash_method_stmt_with compute)
    [receiver_type; int_type; int_type] ->
  stmt_typing CT [receiver_type] AbstractImm
      (SLocal int_type cache_tmp) [receiver_type; int_type] /\
  stmt_typing CT [receiver_type; int_type] AbstractImm
      (SLocal int_type cache_result)
      [receiver_type; int_type; int_type] /\
  stmt_typing CT [receiver_type; int_type; int_type] AbstractImm
      (pico_hash_method_core_stmt_with compute)
      [receiver_type; int_type; int_type].
Proof.
  intros CT receiver_type compute Htyping.
  unfold pico_hash_method_stmt_with in Htyping.
  inversion Htyping; subst.
  inversion Htype1; subst.
  inversion Htype2; subst.
  inversion Htype0; subst.
  split; [econstructor; eauto |].
  split; [econstructor; eauto | assumption].
Qed.

Lemma pico_hash_method_final_assign_typing : forall CT receiver_type compute,
  stmt_typing CT [receiver_type] AbstractImm
    (pico_hash_method_stmt_with compute)
    [receiver_type; int_type; int_type] ->
  stmt_typing CT [receiver_type; int_type; int_type] AbstractImm
    (SVarAss cache_result (EVar cache_tmp))
    [receiver_type; int_type; int_type].
Proof.
  intros CT receiver_type compute Htyping.
  destruct (pico_hash_method_typing_parts_with CT receiver_type compute Htyping)
    as (_ & _ & Hcore).
  unfold pico_hash_method_core_stmt_with, pico_local_copy_cache_stmt in Hcore.
  inversion Hcore; subst.
  inversion Htype1; subst.
  inversion Htype2; subst.
  unfold pico_local_copy_cache_branch in Htype0.
  inversion Htype0; subst.
  inversion H10; subst.
  exact Htype3.
Qed.

Lemma pico_hash_method_cache_write_typing : forall CT receiver_type compute,
  stmt_typing CT [receiver_type] AbstractImm
    (pico_hash_method_stmt_with compute)
    [receiver_type; int_type; int_type] ->
  stmt_typing CT [receiver_type; int_type; int_type] AbstractImm
    (SFldWrite cache_receiver hash_cache_field cache_tmp)
    [receiver_type; int_type; int_type].
Proof.
  intros CT receiver_type compute Htyping.
  destruct (pico_hash_method_typing_parts_with CT receiver_type compute Htyping)
    as (_ & _ & Hcore).
  unfold pico_hash_method_core_stmt_with, pico_local_copy_cache_stmt in Hcore.
  inversion Hcore; subst.
  inversion Htype1; subst.
  inversion Htype2; subst.
  unfold pico_local_copy_cache_branch in Htype0.
  inversion Htype0; subst.
  inversion H10; subst.
  inversion H9; subst.
  inversion Htype5; subst.
  exact Htype5.
Qed.

Lemma pico_hash_same_state_return_evidence : forall
    `{Hmem : CacheMemoryModel}
    CT receiver_type method compute hash_value h sigma loc rGamma,
  stmt_typing CT [receiver_type] AbstractImm
    (pico_hash_method_stmt_with compute)
    [receiver_type; int_type; int_type] ->
  pico_core_typed_env CT [receiver_type; int_type; int_type] rGamma h ->
  runtime_getVal rGamma cache_receiver = Some (Iot loc) ->
  runtime_getVal rGamma cache_tmp = Some (Int hash_value) ->
  pico_core_lr_state CT (mkPicoCoreState h sigma) ->
  PicoCallableReturnEvidence CT h loc
    (pico_hash_method_def_with receiver_type method compute)
    (set_vars rGamma
      (update cache_result (Int hash_value) (vars rGamma)))
    (mkPicoCoreState h sigma) (Int hash_value).
Proof.
  intros Hmem CT receiver_type method compute hash_value h sigma loc rGamma
    Htyping Henv Hreceiver Htmp Hstate.
  assert (Hassign_typing : stmt_typing CT
    [receiver_type; int_type; int_type] AbstractImm
    (SVarAss cache_result (EVar cache_tmp))
    [receiver_type; int_type; int_type]).
  { eapply pico_hash_method_final_assign_typing; eauto. }
  assert (Henv_done : pico_core_typed_env CT
    [receiver_type; int_type; int_type]
    (set_vars rGamma
      (update cache_result (Int hash_value) (vars rGamma))) h).
  { eapply pico_core_typed_env_after_assign_var; eauto. }
  exists [receiver_type; int_type; int_type], int_type.
  split; [reflexivity |].
  split.
  - apply qtype_refl; [reflexivity | discriminate].
  - split; [exact Henv_done |].
    split.
    + unfold get_this_var_mapping, runtime_getVal, cache_receiver,
        cache_result, set_vars in *.
      destruct (vars rGamma) as [|head vars_tail]; simpl in *;
        try discriminate.
      destruct head; simpl in *; try discriminate; congruence.
    + split; [apply pico_core_heap_types_extend_refl |].
      split; [exact Hstate |].
      unfold runtime_getVal, set_vars.
      apply update_same.
      pose proof (pico_core_typed_env_wf_config CT
        [receiver_type; int_type; int_type] rGamma h Henv) as Hconfig.
      destruct Hconfig as (_ & _ & _ & _ & Hlength & _).
      change (3 = length (vars rGamma)) in Hlength.
      change (cache_result < length (vars rGamma)).
      unfold cache_result. lia.
Qed.

Lemma pico_hash_typed_env_set_tmp_int : forall CT receiver_type rGamma h n,
  pico_core_typed_env CT [receiver_type; int_type; int_type] rGamma h ->
  pico_core_typed_env CT [receiver_type; int_type; int_type]
    (set_vars rGamma (update cache_tmp (Int n) (vars rGamma))) h.
Proof.
  intros CT receiver_type rGamma h n Henv.
  eapply pico_core_typed_env_update_value with (Tx := int_type).
  - exact Henv.
  - reflexivity.
  - unfold cache_tmp. discriminate.
  - intros qcontext receiver Hreceiver Hqcontext.
    apply pico_core_typed_value_int.
Qed.

Lemma pico_hash_method_def_with_wf : forall
    CT C receiver_type method compute
    (Htyping : stmt_typing CT [receiver_type] AbstractImm
      (pico_hash_method_stmt_with compute)
      [receiver_type; int_type; int_type])
    (Hoverride : forall parent_def parent mdef_parent,
      find_class CT C = Some parent_def ->
      super (signature parent_def) = Some parent ->
      FindMethodWithName CT parent method mdef_parent ->
      msignature mdef_parent = pico_hash_method_signature receiver_type method),
    wf_method CT C (pico_hash_method_def_with receiver_type method compute).
Proof.
  intros CT C receiver_type method compute Htyping Hoverride.
  unfold wf_method; simpl.
  exists [receiver_type; int_type; int_type], int_type.
  split; [exact Htyping |].
  split; [unfold cache_result; simpl; lia |].
  split; [unfold cache_result; reflexivity |].
  split.
  - apply qtype_sub; simpl.
    + reflexivity.
    + reflexivity.
    + constructor; discriminate.
    + constructor.
  - intros parent_def parent mdef_parent Hclass Hsuper Hfind.
    eapply Hoverride; eauto.
Qed.

Section pico_hash_semantic_api.
  Context `{Hmem : CacheMemoryModel}.
  Context `{Hprogress : CacheMemoryModelProgress}.
  Context (CT : class_table).
  Context `{!ownPGS (pico_core_language CT) Sigma}.
  Context `{!genericCacheG hash_cache_protocol Sigma}.

  Definition PicoHashCacheFieldAdapter
      (A : PicoCoreCacheAdapter hash_cache_protocol)
      (receiver_type : qualified_type) : Prop :=
    forall rGamma h loc,
      pico_core_typed_env CT [receiver_type; int_type; int_type] rGamma h ->
      runtime_getVal rGamma cache_receiver = Some (Iot loc) ->
      pico_core_cache_field hash_cache_protocol A
        (loc, hash_cache_field) = Some HashField.

  Definition PicoHashCacheValueAdapter
      (A : PicoCoreCacheAdapter hash_cache_protocol) : Prop :=
    forall v,
      pico_core_cache_value hash_cache_protocol A HashField v = Some v.

  Definition PicoHashCacheRuntimeAssignable
      (receiver_type : qualified_type) : Prop :=
    forall rGamma h loc,
      pico_core_typed_env CT [receiver_type; int_type; int_type] rGamma h ->
      runtime_getVal rGamma cache_receiver = Some (Iot loc) ->
      exists o assign,
        runtime_getObj h loc = Some o /\
        sf_assignability_rel CT (rctype (rt_type o))
          hash_cache_field assign /\
        runtime_vpa_assignability (rqtype (rt_type o)) assign = Assignable.

  Definition pico_hash_method_postI
      (R : pico_core_state -> iProp Sigma)
      (entry : r_env) (hash_value : nat)
      (result : pico_core_val) : iProp Sigma :=
    ∃ final_state,
      ownP final_state ∗
      R final_state ∗
      ⌜psmc_post (pico_hash_method_contract hash_value) entry result⌝.

  Lemma pico_hash_same_state_step_wpI
      (R : pico_core_state -> iProp Sigma)
      (Phi : pico_core_val -> iProp Sigma)
      e e' state
      (Hstep : pico_core_step CT e state e' state)
      (Hunique : forall next state',
        pico_core_step CT e state next state' ->
        next = e' /\ state' = state) :
    R state -∗
    ownP state -∗
    ▷ (R state -∗ ownP state -∗ WP e' @ NotStuck; top {{ Phi }}) -∗
    WP e @ NotStuck; top {{ Phi }}.
  Proof.
    iIntros "HR Hown Hnext".
    assert (Hready : exists next state',
      pico_core_step CT e state next state').
    { eauto. }
    iApply (pico_core_ownP_wp_from_direct_step_contI
      CT top Phi e state Hready with "Hown [HR Hnext]").
    iNext.
    iIntros (next state') "%Hactual Hown".
    destruct (Hunique next state' Hactual) as [-> ->].
    iApply ("Hnext" with "HR Hown").
  Qed.

  Lemma pico_hash_same_state_step_wpEI
      (R : pico_core_state -> iProp Sigma)
      (Phi : pico_core_val -> iProp Sigma)
      E e e' state
      (Hstep : pico_core_step CT e state e' state)
      (Hunique : forall next state',
        pico_core_step CT e state next state' ->
        next = e' /\ state' = state) :
    R state -∗ ownP state -∗
    ▷ (R state -∗ ownP state -∗ WP e' @ NotStuck; E {{ Phi }}) -∗
    WP e @ NotStuck; E {{ Phi }}.
  Proof.
    iIntros "HR Hown Hnext".
    assert (Hready : exists next state',
      pico_core_step CT e state next state') by eauto.
    iApply (pico_core_ownP_wp_from_direct_step_contI
      CT E Phi e state Hready with "Hown [HR Hnext]").
    iNext. iIntros (next state') "%Hactual Hown".
    destruct (Hunique next state' Hactual) as [-> ->].
    iApply ("Hnext" with "HR Hown").
  Qed.

  Lemma pico_hash_literal_computationI R hash_value :
    ⊢ pico_derived_computationI CT R
      (pico_hash_compute_stmt hash_value) cache_tmp (Int hash_value).
  Proof.
    unfold pico_derived_computationI.
    iModIntro.
    iIntros (rGamma state V K E Phi old) "%Htmp HR Hown Hnext".
    assert (Hstep : pico_core_step CT
      (CoreRun rGamma (pico_hash_compute_stmt hash_value) V K) state
      (CoreRun
        (set_vars rGamma (update cache_tmp (Int hash_value) (vars rGamma)))
        SSkip V K) state).
    { unfold pico_hash_compute_stmt. eapply PCS_AssignInt. exact Htmp. }
    assert (Hready : exists next state', pico_core_step CT
      (CoreRun rGamma (pico_hash_compute_stmt hash_value) V K) state
      next state') by eauto.
    iApply (pico_core_ownP_wp_from_direct_step_contI CT E Phi
      (CoreRun rGamma (pico_hash_compute_stmt hash_value) V K)
      state Hready with "Hown [HR Hnext]").
    iNext. iIntros (next state') "%Hactual Hown".
    inversion Hactual; subst; try discriminate; try congruence.
    iApply ("Hnext" $! V with "HR Hown").
  Qed.

  Lemma pico_hash_literal_ts_computationI R receiver_type hash_value :
    ⊢ pico_ts_derived_computationI CT R ts_no_calls
      [receiver_type; int_type; int_type]
      [receiver_type; int_type; int_type]
      (pico_hash_compute_stmt hash_value) cache_tmp (Int hash_value).
  Proof.
    unfold pico_ts_derived_computationI.
    iSplit.
    - iPureIntro. constructor. constructor.
    - iApply pico_hash_literal_computationI.
  Qed.

  Lemma pico_hash_ts_computation_direct_write_freeI
      R receiver_type compute hash_value :
    pico_ts_derived_computationI CT R ts_no_calls
      [receiver_type; int_type; int_type]
      [receiver_type; int_type; int_type]
      compute cache_tmp (Int hash_value) -∗
    ⌜direct_shared_write_free compute⌝.
  Proof.
    iApply pico_ts_derived_computation_direct_write_freeI.
  Qed.

  Lemma pico_hash_finish_wpI
      (R : pico_core_state -> iProp Sigma)
      (entry : r_env) (state : pico_core_state) (rGamma : r_env)
      (V : view) hash_value old_result
      (Htmp : runtime_getVal rGamma cache_tmp = Some (Int hash_value))
      (Hresult : runtime_getVal rGamma cache_result = Some old_result) :
    R state -∗
    ownP state -∗
    WP CoreRun rGamma
      (SVarAss cache_result (EVar cache_tmp)) V [] @ NotStuck; top
      {{ result, pico_hash_method_postI R entry hash_value result }}.
  Proof.
    iIntros "HR Hown".
    set (rGamma' :=
      set_vars rGamma
        (update cache_result (Int hash_value) (vars rGamma))).
    assert (Hassign_ready : exists e' state',
      pico_core_step CT
        (CoreRun rGamma
          (SVarAss cache_result (EVar cache_tmp)) V [])
        state e' state').
    {
      exists (CoreRun rGamma' SSkip V []), state.
      unfold rGamma'.
      eapply PCS_AssignVar; eauto.
    }
    iApply
      (pico_core_ownP_wp_from_direct_step_contI
        CT top (pico_hash_method_postI R entry hash_value)
        (CoreRun rGamma
          (SVarAss cache_result (EVar cache_tmp)) V [])
        state Hassign_ready with "Hown [HR]").
    iNext.
    iIntros (e' state') "%Hstep Hown".
    inversion Hstep; subst; try discriminate; try congruence.
    assert (val_y = Int hash_value) by congruence.
    subst val_y.
    assert (Hdone_ready : exists e'' state'',
      pico_core_step CT (CoreRun rGamma' SSkip V []) state' e'' state'').
    {
      exists (CoreDone OK rGamma' V), state'.
      apply PCS_SkipDone.
    }
    iApply
      (pico_core_ownP_wp_from_direct_step_contI
        CT top (pico_hash_method_postI R entry hash_value)
        (CoreRun rGamma' SSkip V []) state' Hdone_ready
        with "Hown [HR]").
    iNext.
    iIntros (e'' state'') "%Hdone Hown".
    inversion Hdone; subst.
    iApply
      (@wp_value'
        _ (pico_core_language CT) Sigma _ NotStuck top
        (pico_hash_method_postI R entry hash_value)
        (mkPicoCoreVal OK rGamma' V)).
    unfold pico_hash_method_postI.
    iExists state''.
    iFrame.
    iPureIntro.
    unfold pico_hash_method_contract; simpl.
    split; [reflexivity |].
    exists (Int hash_value).
    split.
    - unfold rGamma', runtime_getVal, set_vars.
      apply update_same.
      eapply runtime_getVal_dom; eauto.
    - reflexivity.
  Qed.

  Lemma pico_hash_finish_callable_wpI
      (R : pico_core_state -> iProp Sigma)
      (entry caller : r_env) (target : var)
      (entry_heap : heap) (entry_receiver : Loc) (mdef : method_def)
      (state : pico_core_state) (rGamma : r_env)
      (V : view) (K : pico_core_cont) E Phi hash_value old_result
      (Htmp : runtime_getVal rGamma cache_tmp = Some (Int hash_value))
      (Hresult : runtime_getVal rGamma cache_result = Some old_result)
      (Hevidence : PicoCallableReturnEvidence CT entry_heap entry_receiver mdef
        (set_vars rGamma
          (update cache_result (Int hash_value) (vars rGamma)))
        state (Int hash_value)) :
    R state -∗
    ownP state -∗
    ▷ (∀ callee_done final_state V' returned,
      ⌜PicoCallableReturnEvidence CT entry_heap entry_receiver mdef
        callee_done final_state returned⌝ -∗
      ⌜psmc_post (pico_hash_method_contract hash_value) entry
        (mkPicoCoreVal OK callee_done V')⌝ -∗
      R final_state -∗
      ownP final_state -∗
      WP CoreRun
        (set_vars caller (update target returned (vars caller)))
        SSkip V' K @ NotStuck; E {{ Phi }}) -∗
    WP CoreRun rGamma (SVarAss cache_result (EVar cache_tmp)) V
      (KCall caller target cache_result :: K)
      @ NotStuck; E {{ Phi }}.
  Proof.
    iIntros "HR Hown Hcontinue".
    set (rGamma' := set_vars rGamma
      (update cache_result (Int hash_value) (vars rGamma))).
    assert (Hassign : pico_core_step CT
      (CoreRun rGamma (SVarAss cache_result (EVar cache_tmp)) V
        (KCall caller target cache_result :: K)) state
      (CoreRun rGamma' SSkip V
        (KCall caller target cache_result :: K)) state).
    { unfold rGamma'. eapply PCS_AssignVar; eauto. }
    assert (Hready : exists next state',
      pico_core_step CT
        (CoreRun rGamma (SVarAss cache_result (EVar cache_tmp)) V
          (KCall caller target cache_result :: K)) state next state') by eauto.
    iApply (pico_core_ownP_wp_from_direct_step_contI
      CT E Phi
      (CoreRun rGamma (SVarAss cache_result (EVar cache_tmp)) V
        (KCall caller target cache_result :: K)) state Hready
      with "Hown [HR Hcontinue]").
    iNext. iIntros (next state') "%Hactual Hown".
    inversion Hactual; subst; try discriminate; try congruence.
    assert (val_y = Int hash_value) by congruence. subst val_y.
    iApply (pico_callable_skip_call_wpI CT R
      rGamma' caller target cache_result V K E Phi state'
      (Int hash_value) with "HR Hown [Hcontinue]").
    - unfold rGamma', runtime_getVal, set_vars.
      apply update_same. eapply runtime_getVal_dom; eauto.
    - iNext. iIntros "HR Hown".
      iApply ("Hcontinue" $! rGamma' state' V (Int hash_value)
        with "[] [] HR Hown").
      + iPureIntro. unfold rGamma'. exact Hevidence.
      + iPureIntro. unfold pico_hash_method_contract; simpl.
        split; [reflexivity |]. exists (Int hash_value).
        split.
        * unfold rGamma', runtime_getVal, set_vars.
          apply update_same. eapply runtime_getVal_dom; eauto.
        * reflexivity.
  Qed.

  Lemma pico_hash_hit_branch_wpI
      (R : pico_core_state -> iProp Sigma)
      compute entry state rGamma V hash_value old_result
      (Hnonzero : hash_value <> 0)
      (Htmp : runtime_getVal rGamma cache_tmp = Some (Int hash_value))
      (Hresult : runtime_getVal rGamma cache_result = Some old_result) :
    R state -∗
    ownP state -∗
    WP CoreRun rGamma
      (pico_local_copy_cache_branch compute)
      V [KSeq (SVarAss cache_result (EVar cache_tmp))]
      @ NotStuck; top
      {{ result, pico_hash_method_postI R entry hash_value result }}.
  Proof.
    iIntros "HR Hown".
    destruct hash_value as [|hash_pred]; [contradiction |].
    set (return_stmt := SVarAss cache_result (EVar cache_tmp)).
    set (return_cont := [KSeq return_stmt]).
    set (branch := pico_local_copy_cache_branch compute).
    assert (Hif : pico_core_step CT
      (CoreRun rGamma branch V return_cont) state
      (CoreRun rGamma SSkip V return_cont) state).
    {
      unfold branch, pico_local_copy_cache_branch.
      apply PCS_IfNonzero with (n := hash_pred).
      exact Htmp.
    }
    iApply (pico_hash_same_state_step_wpI
      R (pico_hash_method_postI R entry (S hash_pred))
      (CoreRun rGamma branch V return_cont)
      (CoreRun rGamma SSkip V return_cont) state Hif
      with "HR Hown").
    - intros next state' Hactual.
      inversion Hactual; subst; try discriminate; try congruence.
      split; reflexivity.
    - iNext.
      iIntros "HR Hown".
      assert (Hskip : pico_core_step CT
        (CoreRun rGamma SSkip V return_cont) state
        (CoreRun rGamma return_stmt V []) state).
      { unfold return_cont. apply PCS_SkipSeq. }
      iApply (pico_hash_same_state_step_wpI
        R (pico_hash_method_postI R entry (S hash_pred))
        (CoreRun rGamma SSkip V return_cont)
        (CoreRun rGamma return_stmt V []) state Hskip
        with "HR Hown").
      + intros next state' Hactual.
        inversion Hactual; subst; try discriminate; try congruence.
        split; reflexivity.
      + iNext.
        iIntros "HR Hown".
        unfold return_stmt.
        iApply (pico_hash_finish_wpI
          R entry state rGamma V (S hash_pred) old_result
          Htmp Hresult with "HR Hown").
  Qed.

  Lemma pico_hash_hit_branch_callable_wpI
      (R : pico_core_state -> iProp Sigma)
      compute entry caller target entry_heap entry_receiver mdef
      state rGamma V K E Phi
      hash_value old_result
      (Hnonzero : hash_value <> 0)
      (Htmp : runtime_getVal rGamma cache_tmp = Some (Int hash_value))
      (Hresult : runtime_getVal rGamma cache_result = Some old_result)
      (Hevidence : PicoCallableReturnEvidence CT entry_heap entry_receiver mdef
        (set_vars rGamma
          (update cache_result (Int hash_value) (vars rGamma)))
        state (Int hash_value)) :
    R state -∗ ownP state -∗
    ▷ (∀ callee_done final_state V' returned,
      ⌜PicoCallableReturnEvidence CT entry_heap entry_receiver mdef
        callee_done final_state returned⌝ -∗
      ⌜psmc_post (pico_hash_method_contract hash_value) entry
        (mkPicoCoreVal OK callee_done V')⌝ -∗
      R final_state -∗ ownP final_state -∗
      WP CoreRun (set_vars caller (update target returned (vars caller)))
        SSkip V' K @ NotStuck; E {{ Phi }}) -∗
    WP CoreRun rGamma (pico_local_copy_cache_branch compute) V
      (KSeq (SVarAss cache_result (EVar cache_tmp)) ::
        KCall caller target cache_result :: K)
      @ NotStuck; E {{ Phi }}.
  Proof.
    iIntros "HR Hown Hcontinue".
    destruct hash_value as [|hash_pred]; [contradiction |].
    set (return_stmt := SVarAss cache_result (EVar cache_tmp)).
    set (return_cont := KSeq return_stmt ::
      KCall caller target cache_result :: K).
    set (branch := pico_local_copy_cache_branch compute).
    assert (Hif : pico_core_step CT
      (CoreRun rGamma branch V return_cont) state
      (CoreRun rGamma SSkip V return_cont) state).
    { unfold branch, pico_local_copy_cache_branch.
      apply PCS_IfNonzero with (n := hash_pred). exact Htmp. }
    iApply (pico_hash_same_state_step_wpEI R Phi E
      (CoreRun rGamma branch V return_cont)
      (CoreRun rGamma SSkip V return_cont) state Hif
      with "HR Hown [Hcontinue]").
    - intros next state' Hactual. inversion Hactual; subst;
        try discriminate; try congruence; split; reflexivity.
    - iNext. iIntros "HR Hown".
      assert (Hskip : pico_core_step CT
        (CoreRun rGamma SSkip V return_cont) state
        (CoreRun rGamma return_stmt V
          (KCall caller target cache_result :: K)) state).
      { unfold return_cont. apply PCS_SkipSeq. }
      iApply (pico_hash_same_state_step_wpEI R Phi E
        (CoreRun rGamma SSkip V return_cont)
        (CoreRun rGamma return_stmt V
          (KCall caller target cache_result :: K)) state Hskip
        with "HR Hown [Hcontinue]").
      + intros next state' Hactual. inversion Hactual; subst;
          try discriminate; try congruence; split; reflexivity.
      + iNext. iIntros "HR Hown". unfold return_stmt.
        iApply (pico_hash_finish_callable_wpI
          R entry caller target entry_heap entry_receiver mdef
          state rGamma V K E Phi
          (S hash_pred) old_result Htmp Hresult Hevidence
          with "HR Hown Hcontinue").
  Qed.

  Lemma pico_hash_miss_prefix_wpI
      (R : pico_core_state -> iProp Sigma)
      (Phi : pico_core_val -> iProp Sigma)
      compute state rGamma V hash_value
      (Htmp : runtime_getVal rGamma cache_tmp = Some (Int 0)) :
    let rGamma_hash :=
      set_vars rGamma
        (update cache_tmp (Int hash_value) (vars rGamma)) in
    pico_derived_computationI CT R compute cache_tmp (Int hash_value) -∗
    R state -∗
    ownP state -∗
    ▷ (∀ V', R state -∗ ownP state -∗
      WP CoreRun rGamma_hash
        (SFldWrite cache_receiver hash_cache_field cache_tmp)
        V' [KSeq (SVarAss cache_result (EVar cache_tmp))]
        @ NotStuck; top {{ Phi }}) -∗
    WP CoreRun rGamma
      (pico_local_copy_cache_branch compute)
      V [KSeq (SVarAss cache_result (EVar cache_tmp))]
      @ NotStuck; top {{ Phi }}.
  Proof.
    simpl.
    iIntros "#Hcompute HR Hown Hwrite".
    set (return_stmt := SVarAss cache_result (EVar cache_tmp)).
    set (write_stmt :=
      SFldWrite cache_receiver hash_cache_field cache_tmp).
    set (compute_stmt := compute).
    set (return_cont := [KSeq return_stmt]).
    set (compute_cont := KSeq write_stmt :: return_cont).
    set (rGamma_hash :=
      set_vars rGamma
        (update cache_tmp (Int hash_value) (vars rGamma))).
    set (branch := pico_local_copy_cache_branch compute_stmt).
    assert (Hif : pico_core_step CT
      (CoreRun rGamma branch V return_cont) state
      (CoreRun rGamma (SSeq compute_stmt write_stmt) V return_cont) state).
    {
      unfold branch, pico_local_copy_cache_branch.
      apply PCS_IfZero.
      exact Htmp.
    }
    iApply (pico_hash_same_state_step_wpI R Phi
      (CoreRun rGamma branch V return_cont)
      (CoreRun rGamma (SSeq compute_stmt write_stmt) V return_cont)
      state Hif with "HR Hown").
    - intros next state' Hactual.
      inversion Hactual; subst; try discriminate; try congruence.
      split; reflexivity.
    - iNext. iIntros "HR Hown".
      assert (Hseq : pico_core_step CT
        (CoreRun rGamma (SSeq compute_stmt write_stmt) V return_cont) state
        (CoreRun rGamma compute_stmt V compute_cont) state).
      { unfold compute_cont. apply PCS_Seq. }
      iApply (pico_hash_same_state_step_wpI R Phi
        (CoreRun rGamma (SSeq compute_stmt write_stmt) V return_cont)
        (CoreRun rGamma compute_stmt V compute_cont) state Hseq
        with "HR Hown").
      + intros next state' Hactual.
        inversion Hactual; subst; try discriminate; try congruence.
        split; reflexivity.
      + iNext. iIntros "HR Hown".
        unfold compute_stmt.
        iApply ("Hcompute" $! rGamma state V compute_cont top Phi (Int 0)
          with "[] HR Hown [Hwrite]").
        * iPureIntro. exact Htmp.
        * iNext. iIntros (V') "HR Hown".
          assert (Hskip : pico_core_step CT
            (CoreRun rGamma_hash SSkip V' compute_cont) state
            (CoreRun rGamma_hash write_stmt V' return_cont) state).
          { unfold compute_cont. apply PCS_SkipSeq. }
          iApply (pico_hash_same_state_step_wpI R Phi
            (CoreRun rGamma_hash SSkip V' compute_cont)
            (CoreRun rGamma_hash write_stmt V' return_cont) state Hskip
            with "HR Hown").
          -- intros next state' Hactual.
             inversion Hactual; subst; try discriminate; try congruence.
             split; reflexivity.
          -- iNext. iIntros "HR Hown".
             unfold write_stmt, return_cont, rGamma_hash.
             iApply ("Hwrite" $! V' with "HR Hown").
  Qed.

  Lemma pico_hash_miss_prefix_callable_wpI
      (R : pico_core_state -> iProp Sigma)
      (Phi : pico_core_val -> iProp Sigma)
      E compute state rGamma V caller target K hash_value
      (Htmp : runtime_getVal rGamma cache_tmp = Some (Int 0)) :
    let rGamma_hash := set_vars rGamma
      (update cache_tmp (Int hash_value) (vars rGamma)) in
    pico_derived_computationI CT R compute cache_tmp (Int hash_value) -∗
    R state -∗ ownP state -∗
    ▷ (∀ V', R state -∗ ownP state -∗
      WP CoreRun rGamma_hash
        (SFldWrite cache_receiver hash_cache_field cache_tmp) V'
        (KSeq (SVarAss cache_result (EVar cache_tmp)) ::
          KCall caller target cache_result :: K)
        @ NotStuck; E {{ Phi }}) -∗
    WP CoreRun rGamma (pico_local_copy_cache_branch compute) V
      (KSeq (SVarAss cache_result (EVar cache_tmp)) ::
        KCall caller target cache_result :: K)
      @ NotStuck; E {{ Phi }}.
  Proof.
    simpl. iIntros "#Hcompute HR Hown Hwrite".
    set (return_stmt := SVarAss cache_result (EVar cache_tmp)).
    set (write_stmt := SFldWrite cache_receiver hash_cache_field cache_tmp).
    set (compute_stmt := compute).
    set (return_cont := KSeq return_stmt ::
      KCall caller target cache_result :: K).
    set (compute_cont := KSeq write_stmt :: return_cont).
    set (rGamma_hash := set_vars rGamma
      (update cache_tmp (Int hash_value) (vars rGamma))).
    set (branch := pico_local_copy_cache_branch compute_stmt).
    assert (Hif : pico_core_step CT
      (CoreRun rGamma branch V return_cont) state
      (CoreRun rGamma (SSeq compute_stmt write_stmt) V return_cont) state).
    { unfold branch, pico_local_copy_cache_branch.
      apply PCS_IfZero. exact Htmp. }
    iApply (pico_hash_same_state_step_wpEI R Phi E
      (CoreRun rGamma branch V return_cont)
      (CoreRun rGamma (SSeq compute_stmt write_stmt) V return_cont)
      state Hif with "HR Hown [Hwrite]").
    - intros next state' Hactual. inversion Hactual; subst;
        try discriminate; try congruence; split; reflexivity.
    - iNext. iIntros "HR Hown".
      assert (Hseq : pico_core_step CT
        (CoreRun rGamma (SSeq compute_stmt write_stmt) V return_cont) state
        (CoreRun rGamma compute_stmt V compute_cont) state).
      { unfold compute_cont. apply PCS_Seq. }
      iApply (pico_hash_same_state_step_wpEI R Phi E
        (CoreRun rGamma (SSeq compute_stmt write_stmt) V return_cont)
        (CoreRun rGamma compute_stmt V compute_cont) state Hseq
        with "HR Hown [Hwrite]").
      + intros next state' Hactual. inversion Hactual; subst;
          try discriminate; try congruence; split; reflexivity.
      + iNext. iIntros "HR Hown". unfold compute_stmt.
        iApply ("Hcompute" $! rGamma state V compute_cont E Phi (Int 0)
          with "[] HR Hown [Hwrite]").
        * iPureIntro. exact Htmp.
        * iNext. iIntros (V') "HR Hown".
          assert (Hskip : pico_core_step CT
            (CoreRun rGamma_hash SSkip V' compute_cont) state
            (CoreRun rGamma_hash write_stmt V' return_cont) state).
          { unfold compute_cont. apply PCS_SkipSeq. }
          iApply (pico_hash_same_state_step_wpEI R Phi E
            (CoreRun rGamma_hash SSkip V' compute_cont)
            (CoreRun rGamma_hash write_stmt V' return_cont) state Hskip
            with "HR Hown [Hwrite]").
          -- intros next state' Hactual. inversion Hactual; subst;
               try discriminate; try congruence; split; reflexivity.
          -- iNext. iIntros "HR Hown".
             unfold write_stmt, return_cont, rGamma_hash.
             iApply ("Hwrite" $! V' with "HR Hown").
  Qed.

  Lemma pico_hash_write_then_finish_wpI
      (A : PicoCoreCacheAdapter hash_cache_protocol)
      hash_value
      (M : PicoCoreSemImmInstantiation CT hash_cache_protocol
        pico_hash_stable_abs hash_value A)
      entry h sigma rGamma V old_result loc o assign
      (Hreceiver : runtime_getVal rGamma cache_receiver = Some (Iot loc))
      (Htmp : runtime_getVal rGamma cache_tmp = Some (Int hash_value))
      (Hresult : runtime_getVal rGamma cache_result = Some old_result)
      (Hobj : runtime_getObj h loc = Some o)
      (Hassign : sf_assignability_rel CT (rctype (rt_type o))
        hash_cache_field assign)
      (Hassignable : runtime_vpa_assignability
        (rqtype (rt_type o)) assign = Assignable)
      (Hfield : pico_core_cache_field hash_cache_protocol A
        (loc, hash_cache_field) = Some HashField)
      (Hvalue : pico_core_cache_value hash_cache_protocol A HashField
        (Int hash_value) = Some (Int hash_value)) :
    pico_core_semimm_worldI CT hash_cache_protocol
      pico_hash_stable_abs hash_value A M (mkPicoCoreState h sigma) -∗
    ownP (mkPicoCoreState h sigma) -∗
    WP CoreRun rGamma
      (SFldWrite cache_receiver hash_cache_field cache_tmp)
      V [KSeq (SVarAss cache_result (EVar cache_tmp))]
      @ NotStuck; top
      {{ result,
        pico_hash_method_postI
          (pico_core_semimm_worldI CT hash_cache_protocol
            pico_hash_stable_abs hash_value A M)
          entry hash_value result }}.
  Proof.
    iIntros "Hworld Hown".
    set (h' := update_field h loc hash_cache_field (Int hash_value)).
    set (sigma' := append_write_msg sigma (loc, hash_cache_field)
      (mkWriteMsg (Int hash_value)
        (length (history_of sigma (loc, hash_cache_field))) V)).
    assert (Hwrite : wm_write sigma sigma' V V
      (loc, hash_cache_field) (Int hash_value)).
    { unfold sigma'. split; reflexivity. }
    assert (Hstep : pico_core_step CT
      (CoreRun rGamma
        (SFldWrite cache_receiver hash_cache_field cache_tmp)
        V [KSeq (SVarAss cache_result (EVar cache_tmp))])
      (mkPicoCoreState h sigma)
      (CoreRun rGamma SSkip V
        [KSeq (SVarAss cache_result (EVar cache_tmp))])
      (mkPicoCoreState h' sigma')).
    {
      unfold h'.
      eapply PCS_FldWrite with (o := o) (a := assign); eauto.
    }
    assert (Hready : exists e' state',
      pico_core_step CT
        (CoreRun rGamma
          (SFldWrite cache_receiver hash_cache_field cache_tmp)
          V [KSeq (SVarAss cache_result (EVar cache_tmp))])
        (mkPicoCoreState h sigma) e' state').
    { eauto. }
    iApply (pico_core_ownP_wp_from_direct_step_contI
      CT top
      (pico_hash_method_postI
        (pico_core_semimm_worldI CT hash_cache_protocol
          pico_hash_stable_abs hash_value A M) entry hash_value)
      (CoreRun rGamma
        (SFldWrite cache_receiver hash_cache_field cache_tmp)
        V [KSeq (SVarAss cache_result (EVar cache_tmp))])
      (mkPicoCoreState h sigma) Hready with "Hown [Hworld]").
    iNext.
    iIntros (e' state') "%Hactual Hown".
    inversion Hactual; subst; try discriminate; try congruence.
    - match goal with
    | Hloc_actual : runtime_getVal rGamma cache_receiver =
        Some (Iot ?loc_actual) |- _ =>
        assert (loc_actual = loc) by congruence; subst loc_actual
    end.
    match goal with
    | Hvalue_actual : runtime_getVal rGamma cache_tmp = Some ?value_actual
        |- _ =>
        assert (value_actual = Int hash_value) by congruence;
        subst value_actual
    end.
    match goal with
    | Hwrite_actual : wm_write sigma ?sigma_actual V ?view_actual
        (loc, hash_cache_field) (Int hash_value) |- _ =>
        destruct Hwrite_actual as [-> ->]
    end.
    iMod (pico_core_semimm_admissible_write_ruleI
      CT hash_cache_protocol pico_hash_stable_abs hash_value A M
      h (update_field h loc hash_cache_field (Int hash_value))
      sigma sigma' V V loc hash_cache_field (Int hash_value)
      eq_refl Hwrite with "Hworld") as "Hworld".
    + right. exists HashField, (Int hash_value).
      split; [exact Hfield |].
      split; [exact Hvalue |].
      unfold hash_cache_valid.
      destruct hash_value as [|hash_value].
      * left. reflexivity.
      * right. split; [reflexivity | discriminate].
    + assert (Hskip : pico_core_step CT
        (CoreRun rGamma SSkip V
          [KSeq (SVarAss cache_result (EVar cache_tmp))])
        (mkPicoCoreState (update_field h loc hash_cache_field
          (Int hash_value)) sigma')
        (CoreRun rGamma (SVarAss cache_result (EVar cache_tmp)) V [])
        (mkPicoCoreState (update_field h loc hash_cache_field
          (Int hash_value)) sigma')).
      { apply PCS_SkipSeq. }
      iApply (pico_hash_same_state_step_wpI
        (pico_core_semimm_worldI CT hash_cache_protocol
          pico_hash_stable_abs hash_value A M)
        (pico_hash_method_postI
          (pico_core_semimm_worldI CT hash_cache_protocol
            pico_hash_stable_abs hash_value A M) entry hash_value)
        (CoreRun rGamma SSkip V
          [KSeq (SVarAss cache_result (EVar cache_tmp))])
        (CoreRun rGamma (SVarAss cache_result (EVar cache_tmp)) V [])
        (mkPicoCoreState (update_field h loc hash_cache_field
          (Int hash_value)) sigma') Hskip with "Hworld Hown").
      * intros next state'' Hactual'.
        inversion Hactual'; subst; try discriminate; try congruence.
        split; reflexivity.
      * iNext. iIntros "Hworld Hown".
        iApply (pico_hash_finish_wpI
          (pico_core_semimm_worldI CT hash_cache_protocol
            pico_hash_stable_abs hash_value A M)
          entry
          (mkPicoCoreState (update_field h loc hash_cache_field
            (Int hash_value)) sigma')
          rGamma V hash_value old_result Htmp Hresult
          with "Hworld Hown").
    - assert (loc_x = loc) by congruence.
      subst loc_x.
      assert (o0 = o) by congruence.
      subst o0.
      assert (a = assign) by
        (eapply sf_assignability_deterministic_rel; eauto).
      subst a.
      congruence.
  Qed.

  Lemma pico_hash_valid_write_wpI
      (A : PicoCoreCacheAdapter hash_cache_protocol) hash_value
      (M : PicoCoreSemImmInstantiation CT hash_cache_protocol
        pico_hash_stable_abs hash_value A)
      h sigma rGamma V K E Phi loc o assign
      (Hreceiver : runtime_getVal rGamma cache_receiver = Some (Iot loc))
      (Htmp : runtime_getVal rGamma cache_tmp = Some (Int hash_value))
      (Hobj : runtime_getObj h loc = Some o)
      (Hassign : sf_assignability_rel CT (rctype (rt_type o))
        hash_cache_field assign)
      (Hassignable : runtime_vpa_assignability
        (rqtype (rt_type o)) assign = Assignable)
      (Hfield : pico_core_cache_field hash_cache_protocol A
        (loc, hash_cache_field) = Some HashField)
      (Hvalue : pico_core_cache_value hash_cache_protocol A HashField
        (Int hash_value) = Some (Int hash_value)) :
    pico_core_semimm_worldI CT hash_cache_protocol
      pico_hash_stable_abs hash_value A M (mkPicoCoreState h sigma) -∗
    ownP (mkPicoCoreState h sigma) -∗
    ▷ (∀ h' sigma',
      ⌜h' = update_field h loc hash_cache_field (Int hash_value) /\
        wm_write sigma sigma' V V
          (loc, hash_cache_field) (Int hash_value)⌝ -∗
      pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M (mkPicoCoreState h' sigma') -∗
      ownP (mkPicoCoreState h' sigma') -∗
      WP CoreRun rGamma SSkip V K @ NotStuck; E {{ Phi }}) -∗
    WP CoreRun rGamma
      (SFldWrite cache_receiver hash_cache_field cache_tmp) V K
      @ NotStuck; E {{ Phi }}.
  Proof.
    iIntros "Hworld Hown Hnext".
    set (h' := update_field h loc hash_cache_field (Int hash_value)).
    set (sigma' := append_write_msg sigma (loc, hash_cache_field)
      (mkWriteMsg (Int hash_value)
        (length (history_of sigma (loc, hash_cache_field))) V)).
    assert (Hwrite : wm_write sigma sigma' V V
      (loc, hash_cache_field) (Int hash_value)).
    { unfold sigma'. split; reflexivity. }
    assert (Hready : exists next state', pico_core_step CT
      (CoreRun rGamma
        (SFldWrite cache_receiver hash_cache_field cache_tmp) V K)
      (mkPicoCoreState h sigma) next state').
    { exists (CoreRun rGamma SSkip V K), (mkPicoCoreState h' sigma').
      unfold h'. eapply PCS_FldWrite with (o := o) (a := assign); eauto. }
    iApply (pico_core_ownP_wp_from_direct_step_contI CT E Phi
      (CoreRun rGamma
        (SFldWrite cache_receiver hash_cache_field cache_tmp) V K)
      (mkPicoCoreState h sigma) Hready with "Hown [Hworld Hnext]").
    iNext. iIntros (next state') "%Hactual Hown".
    inversion Hactual; subst; try discriminate; try congruence.
    - match goal with
      | Hloc_actual : runtime_getVal rGamma cache_receiver =
          Some (Iot ?loc_actual) |- _ =>
          assert (loc_actual = loc) by congruence; subst loc_actual
      end.
      match goal with
      | Hvalue_actual : runtime_getVal rGamma cache_tmp = Some ?value_actual
          |- _ => assert (value_actual = Int hash_value) by congruence;
          subst value_actual
      end.
      match goal with
      | Hwrite_actual : wm_write sigma ?sigma_actual V ?view_actual
          (loc, hash_cache_field) (Int hash_value) |- _ =>
          destruct Hwrite_actual as [-> ->]
      end.
      iMod (pico_core_semimm_admissible_write_ruleI
        CT hash_cache_protocol pico_hash_stable_abs hash_value A M
        h (update_field h loc hash_cache_field (Int hash_value))
        sigma sigma' V V loc hash_cache_field (Int hash_value)
        eq_refl Hwrite with "Hworld") as "Hworld".
      + right. exists HashField, (Int hash_value).
        split; [exact Hfield |]. split; [exact Hvalue |].
        unfold hash_cache_valid. destruct hash_value as [|hash_value].
        * left. reflexivity.
        * right. split; [reflexivity | discriminate].
      + iApply ("Hnext" $!
          (update_field h loc hash_cache_field (Int hash_value)) sigma'
          with "[] Hworld Hown").
        iPureIntro. split; [reflexivity | exact Hwrite].
    - assert (loc_x = loc) by congruence. subst loc_x.
      assert (o0 = o) by congruence. subst o0.
      assert (a = assign) by
        (eapply sf_assignability_deterministic_rel; eauto).
      subst a. congruence.
  Qed.

  Lemma pico_hash_write_then_finish_callable_wpI
      (A : PicoCoreCacheAdapter hash_cache_protocol) hash_value
      (M : PicoCoreSemImmInstantiation CT hash_cache_protocol
        pico_hash_stable_abs hash_value A)
      receiver_type method compute entry caller target h sigma rGamma
      V K E Phi old_result loc o assign
      (Hreceiver : runtime_getVal rGamma cache_receiver = Some (Iot loc))
      (Htmp : runtime_getVal rGamma cache_tmp = Some (Int hash_value))
      (Hresult : runtime_getVal rGamma cache_result = Some old_result)
      (Hobj : runtime_getObj h loc = Some o)
      (Hassign : sf_assignability_rel CT (rctype (rt_type o))
        hash_cache_field assign)
      (Hassignable : runtime_vpa_assignability
        (rqtype (rt_type o)) assign = Assignable)
      (Hfield : pico_core_cache_field hash_cache_protocol A
        (loc, hash_cache_field) = Some HashField)
      (Hvalue : pico_core_cache_value hash_cache_protocol A HashField
        (Int hash_value) = Some (Int hash_value))
      (Htyping : stmt_typing CT [receiver_type] AbstractImm
        (pico_hash_method_stmt_with compute)
        [receiver_type; int_type; int_type])
      (Henv : pico_core_typed_env CT
        [receiver_type; int_type; int_type] rGamma h)
      (Hlrstate : pico_core_lr_state CT (mkPicoCoreState h sigma)) :
    pico_core_semimm_worldI CT hash_cache_protocol
      pico_hash_stable_abs hash_value A M (mkPicoCoreState h sigma) -∗
    ownP (mkPicoCoreState h sigma) -∗
    ▷ (∀ callee_done final_state V' returned,
      ⌜PicoCallableReturnEvidence CT h loc
        (pico_hash_method_def_with receiver_type method compute)
        callee_done final_state returned⌝ -∗
      ⌜psmc_post (pico_hash_method_contract hash_value) entry
        (mkPicoCoreVal OK callee_done V')⌝ -∗
      pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M final_state -∗
      ownP final_state -∗
      WP CoreRun (set_vars caller (update target returned (vars caller)))
        SSkip V' K @ NotStuck; E {{ Phi }}) -∗
    WP CoreRun rGamma
      (SFldWrite cache_receiver hash_cache_field cache_tmp) V
      (KSeq (SVarAss cache_result (EVar cache_tmp)) ::
        KCall caller target cache_result :: K)
      @ NotStuck; E {{ Phi }}.
  Proof.
    iIntros "Hworld Hown Hcontinue".
    set (return_stmt := SVarAss cache_result (EVar cache_tmp)).
    set (tail := KCall caller target cache_result :: K).
    set (write_cont := KSeq return_stmt :: tail).
    iApply (pico_hash_valid_write_wpI A hash_value M
      h sigma rGamma V write_cont E Phi loc o assign
      Hreceiver Htmp Hobj Hassign Hassignable Hfield Hvalue
      with "Hworld Hown [Hcontinue]").
    iNext. iIntros (h' sigma') "%Hwrite_facts Hworld Hown".
    destruct Hwrite_facts as [Hheap Hwrite].
    assert (Hwrite_typing : stmt_typing CT
      [receiver_type; int_type; int_type] AbstractImm
      (SFldWrite cache_receiver hash_cache_field cache_tmp)
      [receiver_type; int_type; int_type]).
    { eapply pico_hash_method_cache_write_typing; eauto. }
    assert (Henv_write : pico_core_typed_env CT
      [receiver_type; int_type; int_type] rGamma h').
    { eapply pico_core_typed_env_after_fldwrite_success with
        (loc := loc) (o := o) (a := assign) (value := Int hash_value);
        eauto. }
    assert (Hassign_typing : stmt_typing CT
      [receiver_type; int_type; int_type] AbstractImm
      (SVarAss cache_result (EVar cache_tmp))
      [receiver_type; int_type; int_type]).
    { eapply pico_hash_method_final_assign_typing; eauto. }
    set (rGamma_done := set_vars rGamma
      (update cache_result (Int hash_value) (vars rGamma))).
    assert (Henv_done : pico_core_typed_env CT
      [receiver_type; int_type; int_type] rGamma_done h').
    { unfold rGamma_done.
      eapply pico_core_typed_env_after_assign_var; eauto. }
    assert (Hreceiver_done :
      get_this_var_mapping (vars rGamma_done) = Some loc).
    { unfold rGamma_done, get_this_var_mapping, runtime_getVal,
        cache_receiver, cache_result, set_vars in *.
      destruct (vars rGamma) as [|head vars_tail]; simpl in *;
        try discriminate.
      destruct head; simpl in *; try discriminate; congruence. }
    assert (Hextend : pico_core_heap_types_extend h h').
    { rewrite Hheap. eapply pico_core_heap_types_extend_write; eauto. }
    assert (Hlrstate' : pico_core_lr_state CT
      (mkPicoCoreState h' sigma')).
    { unfold pico_core_lr_state.
      rewrite Hheap.
      eapply pico_core_state_wf_write; eauto. }
    assert (Hevidence : PicoCallableReturnEvidence CT h loc
      (pico_hash_method_def_with receiver_type method compute)
      rGamma_done (mkPicoCoreState h' sigma') (Int hash_value)).
    { exists [receiver_type; int_type; int_type], int_type.
      split; [reflexivity |].
      split.
      - apply qtype_refl; [reflexivity | discriminate].
      - split; [exact Henv_done |].
        split; [exact Hreceiver_done |].
        split; [exact Hextend |].
        split; [exact Hlrstate' |].
        unfold rGamma_done, runtime_getVal, set_vars.
        apply update_same. eapply runtime_getVal_dom; eauto. }
    assert (Hskip : pico_core_step CT
      (CoreRun rGamma SSkip V write_cont) (mkPicoCoreState h' sigma')
      (CoreRun rGamma return_stmt V tail) (mkPicoCoreState h' sigma')).
    { unfold write_cont. apply PCS_SkipSeq. }
    iApply (pico_hash_same_state_step_wpEI
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M) Phi E
      (CoreRun rGamma SSkip V write_cont)
      (CoreRun rGamma return_stmt V tail)
      (mkPicoCoreState h' sigma') Hskip with "Hworld Hown [Hcontinue]").
    - intros next state' Hactual. inversion Hactual; subst;
        try discriminate; try congruence; split; reflexivity.
    - iNext. iIntros "Hworld Hown".
      unfold return_stmt, tail.
      iApply (pico_hash_finish_callable_wpI
        (pico_core_semimm_worldI CT hash_cache_protocol
          pico_hash_stable_abs hash_value A M)
        entry caller target h loc
        (pico_hash_method_def_with receiver_type method compute)
        (mkPicoCoreState h' sigma') rGamma V K E Phi
        hash_value old_result Htmp Hresult Hevidence
        with "Hworld Hown Hcontinue").
  Qed.

  Lemma pico_hash_after_read_wpI
      (A : PicoCoreCacheAdapter hash_cache_protocol)
      hash_value
      (M : PicoCoreSemImmInstantiation CT hash_cache_protocol
        pico_hash_stable_abs hash_value A)
      compute entry h sigma rGamma V old_result loc observed o assign
      (Hreceiver : runtime_getVal rGamma cache_receiver = Some (Iot loc))
      (Htmp : runtime_getVal rGamma cache_tmp = Some observed)
      (Hresult : runtime_getVal rGamma cache_result = Some old_result)
      (Hvalid : hash_cache_valid hash_value HashField observed)
      (Hobj : runtime_getObj h loc = Some o)
      (Hassign : sf_assignability_rel CT (rctype (rt_type o))
        hash_cache_field assign)
      (Hassignable : runtime_vpa_assignability
        (rqtype (rt_type o)) assign = Assignable)
      (Hfield : pico_core_cache_field hash_cache_protocol A
        (loc, hash_cache_field) = Some HashField)
      (Hvalue : pico_core_cache_value hash_cache_protocol A HashField
        (Int hash_value) = Some (Int hash_value)) :
    pico_derived_computationI CT
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      compute cache_tmp (Int hash_value) -∗
    pico_core_semimm_worldI CT hash_cache_protocol
      pico_hash_stable_abs hash_value A M (mkPicoCoreState h sigma) -∗
    ownP (mkPicoCoreState h sigma) -∗
    WP CoreRun rGamma
      (pico_local_copy_cache_branch compute)
      V [KSeq (SVarAss cache_result (EVar cache_tmp))]
      @ NotStuck; top
      {{ result,
        pico_hash_method_postI
          (pico_core_semimm_worldI CT hash_cache_protocol
            pico_hash_stable_abs hash_value A M)
          entry hash_value result }}.
  Proof.
    iIntros "#Hcompute Hworld Hown".
    destruct (hash_valid_value_shape hash_value observed Hvalid)
      as [Hzero | [Hhit Hnonzero]].
    - subst observed.
      iApply (pico_hash_miss_prefix_wpI
        (pico_core_semimm_worldI CT hash_cache_protocol
          pico_hash_stable_abs hash_value A M)
        (pico_hash_method_postI
          (pico_core_semimm_worldI CT hash_cache_protocol
            pico_hash_stable_abs hash_value A M) entry hash_value)
        compute
        (mkPicoCoreState h sigma) rGamma V hash_value Htmp
        with "Hcompute Hworld Hown").
      iNext. iIntros (Vcompute) "Hworld Hown".
      set (rGamma_hash := set_vars rGamma
        (update cache_tmp (Int hash_value) (vars rGamma))).
      assert (Hreceiver_hash : runtime_getVal rGamma_hash cache_receiver =
        Some (Iot loc)).
      {
        unfold rGamma_hash, runtime_getVal, set_vars.
        rewrite update_diff; [exact Hreceiver | discriminate].
      }
      assert (Htmp_hash : runtime_getVal rGamma_hash cache_tmp =
        Some (Int hash_value)).
      {
        unfold rGamma_hash, runtime_getVal, set_vars.
        apply update_same.
        eapply runtime_getVal_dom; eauto.
      }
      assert (Hresult_hash : runtime_getVal rGamma_hash cache_result =
        Some old_result).
      {
        unfold rGamma_hash, runtime_getVal, set_vars.
        rewrite update_diff; [exact Hresult | discriminate].
      }
      unfold rGamma_hash.
      iApply (pico_hash_write_then_finish_wpI
        A hash_value M entry h sigma
        (set_vars rGamma
          (update cache_tmp (Int hash_value) (vars rGamma)))
        Vcompute old_result loc o assign
        Hreceiver_hash Htmp_hash Hresult_hash Hobj Hassign Hassignable
        Hfield Hvalue
        with "Hworld Hown").
    - subst observed.
      iApply (pico_hash_hit_branch_wpI
        (pico_core_semimm_worldI CT hash_cache_protocol
          pico_hash_stable_abs hash_value A M)
        compute entry (mkPicoCoreState h sigma) rGamma V hash_value old_result
        Hnonzero Htmp Hresult with "Hworld Hown").
  Qed.

  Lemma pico_hash_after_read_callable_wpI
      (A : PicoCoreCacheAdapter hash_cache_protocol) hash_value
      (M : PicoCoreSemImmInstantiation CT hash_cache_protocol
        pico_hash_stable_abs hash_value A)
      receiver_type method compute entry caller target h sigma rGamma V K E Phi
      old_result loc observed o assign
      (Hreceiver : runtime_getVal rGamma cache_receiver = Some (Iot loc))
      (Htmp : runtime_getVal rGamma cache_tmp = Some observed)
      (Hresult : runtime_getVal rGamma cache_result = Some old_result)
      (Hvalid : hash_cache_valid hash_value HashField observed)
      (Hobj : runtime_getObj h loc = Some o)
      (Hassign : sf_assignability_rel CT (rctype (rt_type o))
        hash_cache_field assign)
      (Hassignable : runtime_vpa_assignability
        (rqtype (rt_type o)) assign = Assignable)
      (Hfield : pico_core_cache_field hash_cache_protocol A
        (loc, hash_cache_field) = Some HashField)
      (Hvalue : pico_core_cache_value hash_cache_protocol A HashField
        (Int hash_value) = Some (Int hash_value))
      (Htyping : stmt_typing CT [receiver_type] AbstractImm
        (pico_hash_method_stmt_with compute)
        [receiver_type; int_type; int_type])
      (Henv : pico_core_typed_env CT
        [receiver_type; int_type; int_type] rGamma h)
      (Hlrstate : pico_core_lr_state CT (mkPicoCoreState h sigma)) :
    pico_derived_computationI CT
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      compute cache_tmp (Int hash_value) -∗
    pico_core_semimm_worldI CT hash_cache_protocol
      pico_hash_stable_abs hash_value A M (mkPicoCoreState h sigma) -∗
    ownP (mkPicoCoreState h sigma) -∗
    ▷ (∀ callee_done final_state V' returned,
      ⌜PicoCallableReturnEvidence CT h loc
        (pico_hash_method_def_with receiver_type method compute)
        callee_done final_state returned⌝ -∗
      ⌜psmc_post (pico_hash_method_contract hash_value) entry
        (mkPicoCoreVal OK callee_done V')⌝ -∗
      pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M final_state -∗
      ownP final_state -∗
      WP CoreRun (set_vars caller (update target returned (vars caller)))
        SSkip V' K @ NotStuck; E {{ Phi }}) -∗
    WP CoreRun rGamma (pico_local_copy_cache_branch compute) V
      (KSeq (SVarAss cache_result (EVar cache_tmp)) ::
        KCall caller target cache_result :: K)
      @ NotStuck; E {{ Phi }}.
  Proof.
    iIntros "#Hcompute Hworld Hown Hcontinue".
    destruct (hash_valid_value_shape hash_value observed Hvalid)
      as [Hzero | [Hhit Hnonzero]].
    - subst observed.
      iApply (pico_hash_miss_prefix_callable_wpI
        (pico_core_semimm_worldI CT hash_cache_protocol
          pico_hash_stable_abs hash_value A M) Phi E compute
        (mkPicoCoreState h sigma) rGamma V caller target K hash_value Htmp
        with "Hcompute Hworld Hown [Hcontinue]").
      iNext. iIntros (Vcompute) "Hworld Hown".
      set (rGamma_hash := set_vars rGamma
        (update cache_tmp (Int hash_value) (vars rGamma))).
      assert (Hreceiver_hash : runtime_getVal rGamma_hash cache_receiver =
        Some (Iot loc)).
      { unfold rGamma_hash, runtime_getVal, set_vars.
        rewrite update_diff; [exact Hreceiver | discriminate]. }
      assert (Htmp_hash : runtime_getVal rGamma_hash cache_tmp =
        Some (Int hash_value)).
      { unfold rGamma_hash, runtime_getVal, set_vars. apply update_same.
        eapply runtime_getVal_dom; eauto. }
      assert (Hresult_hash : runtime_getVal rGamma_hash cache_result =
        Some old_result).
      { unfold rGamma_hash, runtime_getVal, set_vars.
        rewrite update_diff; [exact Hresult | discriminate]. }
      assert (Henv_hash : pico_core_typed_env CT
        [receiver_type; int_type; int_type] rGamma_hash h).
      { unfold rGamma_hash. eapply pico_hash_typed_env_set_tmp_int; eauto. }
      unfold rGamma_hash.
      iApply (pico_hash_write_then_finish_callable_wpI
        A hash_value M receiver_type method compute entry caller target h sigma
        (set_vars rGamma
          (update cache_tmp (Int hash_value) (vars rGamma)))
        Vcompute K E Phi old_result loc o assign
        Hreceiver_hash Htmp_hash Hresult_hash Hobj Hassign Hassignable
        Hfield Hvalue Htyping Henv_hash Hlrstate
        with "Hworld Hown Hcontinue").
    - subst observed.
      assert (Hevidence : PicoCallableReturnEvidence CT h loc
        (pico_hash_method_def_with receiver_type method compute)
        (set_vars rGamma
          (update cache_result (Int hash_value) (vars rGamma)))
        (mkPicoCoreState h sigma) (Int hash_value)).
      { eapply pico_hash_same_state_return_evidence; eauto. }
      iApply (pico_hash_hit_branch_callable_wpI
        (pico_core_semimm_worldI CT hash_cache_protocol
          pico_hash_stable_abs hash_value A M)
        compute entry caller target h loc
        (pico_hash_method_def_with receiver_type method compute)
        (mkPicoCoreState h sigma) rGamma V
        K E Phi hash_value old_result Hnonzero Htmp Hresult Hevidence
        with "Hworld Hown Hcontinue").
  Qed.

  Lemma pico_hash_read_then_finish_wpI
      (A : PicoCoreCacheAdapter hash_cache_protocol)
      hash_value
      (M : PicoCoreSemImmInstantiation CT hash_cache_protocol
        pico_hash_stable_abs hash_value A)
      compute entry h sigma rGamma V old_tmp old_result loc o assign
      (Hreceiver : runtime_getVal rGamma cache_receiver = Some (Iot loc))
      (Htmp : runtime_getVal rGamma cache_tmp = Some old_tmp)
      (Hresult : runtime_getVal rGamma cache_result = Some old_result)
      (Hobj : runtime_getObj h loc = Some o)
      (Hassign : sf_assignability_rel CT (rctype (rt_type o))
        hash_cache_field assign)
      (Hassignable : runtime_vpa_assignability
        (rqtype (rt_type o)) assign = Assignable)
      (Hfield : pico_core_cache_field hash_cache_protocol A
        (loc, hash_cache_field) = Some HashField)
      (Hvalue : forall v,
        pico_core_cache_value hash_cache_protocol A HashField v = Some v)
      (Hread_ready : exists v V',
        wm_read sigma V (loc, hash_cache_field) v V') :
    pico_derived_computationI CT
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      compute cache_tmp (Int hash_value) -∗
    pico_core_semimm_worldI CT hash_cache_protocol
      pico_hash_stable_abs hash_value A M (mkPicoCoreState h sigma) -∗
    ownP (mkPicoCoreState h sigma) -∗
    WP CoreRun rGamma
      (pico_hash_method_core_stmt_with compute) V []
      @ NotStuck; top
      {{ result,
        pico_hash_method_postI
          (pico_core_semimm_worldI CT hash_cache_protocol
            pico_hash_stable_abs hash_value A M)
          entry hash_value result }}.
  Proof.
    iIntros "#Hcompute Hworld Hown".
    set (tail := SSeq
      (pico_local_copy_cache_branch compute)
      (SVarAss cache_result (EVar cache_tmp))).
    assert (Hseq : pico_core_step CT
      (CoreRun rGamma (pico_hash_method_core_stmt_with compute) V [])
      (mkPicoCoreState h sigma)
      (CoreRun rGamma
        (SVarAss cache_tmp (EField cache_receiver hash_cache_field)) V
        [KSeq tail])
      (mkPicoCoreState h sigma)).
    { unfold pico_hash_method_core_stmt_with, pico_local_copy_cache_stmt, tail.
      apply PCS_Seq. }
    iApply (pico_hash_same_state_step_wpI
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      (pico_hash_method_postI
        (pico_core_semimm_worldI CT hash_cache_protocol
          pico_hash_stable_abs hash_value A M) entry hash_value)
      _ _ _ Hseq with "Hworld Hown").
    - intros next state' Hactual.
      inversion Hactual; subst; try discriminate; try congruence.
      split; reflexivity.
    - iNext. iIntros "Hworld Hown".
      assert (Hready : exists next state', pico_core_step CT
        (CoreRun rGamma
          (SVarAss cache_tmp (EField cache_receiver hash_cache_field)) V
          [KSeq tail])
        (mkPicoCoreState h sigma) next state').
      {
        destruct Hread_ready as (v & V' & Hread).
        exists (CoreRun
          (set_vars rGamma (update cache_tmp v (vars rGamma))) SSkip V'
          [KSeq tail]), (mkPicoCoreState h sigma).
        eapply PCS_AssignField; eauto.
      }
      iApply (pico_core_ownP_wp_from_direct_step_contI CT top
        (pico_hash_method_postI
          (pico_core_semimm_worldI CT hash_cache_protocol
            pico_hash_stable_abs hash_value A M) entry hash_value)
        _ _ Hready with "Hown [Hworld]").
      iNext. iIntros (next state') "%Hread_step Hown".
      inversion Hread_step; subst; try discriminate; try congruence.
      match goal with
      | Hreceiver' : runtime_getVal rGamma cache_receiver = Some (Iot ?loc') |- _ =>
          assert (loc' = loc) by congruence; subst loc'
      end.
      unfold pico_core_semimm_worldI at 1.
      iDestruct "Hworld" as (gamma) "[%Hstate Hsem]".
      match goal with
      | Hactual_read : wm_read sigma V (loc, hash_cache_field) v V' |- _ =>
          pose proof (pico_core_semimm_cache_read_from_history
            CT hash_cache_protocol pico_hash_stable_abs hash_value A M
            (mkPicoCoreState h sigma) V (loc, hash_cache_field) v V'
            HashField Hstate Hactual_read Hfield) as Hcache_read
      end.
      iPoseProof (pico_core_cache_read_semimmI
        hash_cache_protocol A pico_hash_stable_abs gamma
        (pcsi_object CT hash_cache_protocol pico_hash_stable_abs hash_value A M
          (mkPicoCoreState h sigma)) hash_value
        (pcsi_snapshot CT hash_cache_protocol pico_hash_stable_abs hash_value A M
          (mkPicoCoreState h sigma))
        (loc, hash_cache_field) v with "Hsem []") as "[Hsem Hvalid]".
      { iPureIntro. exact Hcache_read. }
      iDestruct "Hvalid" as (k cv) "%Hvalid".
      destruct Hvalid as (Hfield' & Hvalue' & Hvalid & Hpublished).
      rewrite Hfield in Hfield'. inversion Hfield'; subst k.
      rewrite Hvalue in Hvalue'. inversion Hvalue'; subst cv.
      iAssert (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M (mkPicoCoreState h sigma))
        with "[Hsem]" as "Hworld".
      { iExists gamma. iFrame. iPureIntro. exact Hstate. }
      set (rGamma_read := set_vars rGamma
        (update cache_tmp v (vars rGamma))).
      assert (Htmp_read : runtime_getVal rGamma_read cache_tmp = Some v).
      { unfold rGamma_read, runtime_getVal, set_vars.
        apply update_same. eapply runtime_getVal_dom; eauto. }
      assert (Hreceiver_read : runtime_getVal rGamma_read cache_receiver =
        Some (Iot loc)).
      { unfold rGamma_read, runtime_getVal, set_vars.
        rewrite update_diff; [exact Hreceiver | discriminate]. }
      assert (Hresult_read : runtime_getVal rGamma_read cache_result =
        Some old_result).
      { unfold rGamma_read, runtime_getVal, set_vars.
        rewrite update_diff; [exact Hresult | discriminate]. }
      assert (Hskip : pico_core_step CT
        (CoreRun rGamma_read SSkip V' [KSeq tail])
        (mkPicoCoreState h sigma)
        (CoreRun rGamma_read tail V' [])
        (mkPicoCoreState h sigma)).
      { apply PCS_SkipSeq. }
      iApply (pico_hash_same_state_step_wpI
        (pico_core_semimm_worldI CT hash_cache_protocol
          pico_hash_stable_abs hash_value A M)
        (pico_hash_method_postI
          (pico_core_semimm_worldI CT hash_cache_protocol
            pico_hash_stable_abs hash_value A M) entry hash_value)
        _ _ _ Hskip with "Hworld Hown").
      + intros next' state'' Hactual.
        inversion Hactual; subst; try discriminate; try congruence.
        split; reflexivity.
      + iNext. iIntros "Hworld Hown".
        assert (Htail : pico_core_step CT
          (CoreRun rGamma_read tail V' []) (mkPicoCoreState h sigma)
          (CoreRun rGamma_read
            (pico_local_copy_cache_branch compute) V'
            [KSeq (SVarAss cache_result (EVar cache_tmp))])
          (mkPicoCoreState h sigma)).
        { unfold tail. apply PCS_Seq. }
        iApply (pico_hash_same_state_step_wpI
          (pico_core_semimm_worldI CT hash_cache_protocol
            pico_hash_stable_abs hash_value A M)
          (pico_hash_method_postI
            (pico_core_semimm_worldI CT hash_cache_protocol
              pico_hash_stable_abs hash_value A M) entry hash_value)
          _ _ _ Htail with "Hworld Hown").
        * intros next' state'' Hactual.
          inversion Hactual; subst; try discriminate; try congruence.
          split; reflexivity.
        * iNext. iIntros "Hworld Hown".
          iApply (pico_hash_after_read_wpI A hash_value M compute entry h sigma
            rGamma_read V' old_result loc v o assign Hreceiver_read
            Htmp_read Hresult_read Hvalid Hobj Hassign Hassignable
            Hfield (Hvalue (Int hash_value))
            with "Hcompute Hworld Hown").
  Qed.

  Lemma pico_hash_read_then_finish_callable_wpI
      (A : PicoCoreCacheAdapter hash_cache_protocol) hash_value
      (M : PicoCoreSemImmInstantiation CT hash_cache_protocol
        pico_hash_stable_abs hash_value A)
      receiver_type method compute entry caller target h sigma rGamma V K E Phi
      old_tmp old_result loc o assign
      (Hreceiver : runtime_getVal rGamma cache_receiver = Some (Iot loc))
      (Htmp : runtime_getVal rGamma cache_tmp = Some old_tmp)
      (Hresult : runtime_getVal rGamma cache_result = Some old_result)
      (Hobj : runtime_getObj h loc = Some o)
      (Hassign : sf_assignability_rel CT (rctype (rt_type o))
        hash_cache_field assign)
      (Hassignable : runtime_vpa_assignability
        (rqtype (rt_type o)) assign = Assignable)
      (Hfield : pico_core_cache_field hash_cache_protocol A
        (loc, hash_cache_field) = Some HashField)
      (Hvalue : forall v,
        pico_core_cache_value hash_cache_protocol A HashField v = Some v)
      (Hread_ready : exists v V',
        wm_read sigma V (loc, hash_cache_field) v V')
      (Htyping : stmt_typing CT [receiver_type] AbstractImm
        (pico_hash_method_stmt_with compute)
        [receiver_type; int_type; int_type])
      (Henv : pico_core_typed_env CT
        [receiver_type; int_type; int_type] rGamma h)
      (Hlrstate : pico_core_lr_state CT (mkPicoCoreState h sigma)) :
    pico_derived_computationI CT
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      compute cache_tmp (Int hash_value) -∗
    pico_core_semimm_worldI CT hash_cache_protocol
      pico_hash_stable_abs hash_value A M (mkPicoCoreState h sigma) -∗
    ownP (mkPicoCoreState h sigma) -∗
    ▷ (∀ callee_done final_state V' returned,
      ⌜PicoCallableReturnEvidence CT h loc
        (pico_hash_method_def_with receiver_type method compute)
        callee_done final_state returned⌝ -∗
      ⌜psmc_post (pico_hash_method_contract hash_value) entry
        (mkPicoCoreVal OK callee_done V')⌝ -∗
      pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M final_state -∗
      ownP final_state -∗
      WP CoreRun (set_vars caller (update target returned (vars caller)))
        SSkip V' K @ NotStuck; E {{ Phi }}) -∗
    WP CoreRun rGamma (pico_hash_method_core_stmt_with compute) V
      (KCall caller target cache_result :: K)
      @ NotStuck; E {{ Phi }}.
  Proof.
    iIntros "#Hcompute Hworld Hown Hcontinue".
    set (tail := SSeq (pico_local_copy_cache_branch compute)
      (SVarAss cache_result (EVar cache_tmp))).
    set (call_cont := KCall caller target cache_result :: K).
    set (read_cont := KSeq tail :: call_cont).
    assert (Hseq : pico_core_step CT
      (CoreRun rGamma (pico_hash_method_core_stmt_with compute) V call_cont)
      (mkPicoCoreState h sigma)
      (CoreRun rGamma
        (SVarAss cache_tmp (EField cache_receiver hash_cache_field)) V
        read_cont) (mkPicoCoreState h sigma)).
    { unfold pico_hash_method_core_stmt_with, pico_local_copy_cache_stmt,
        read_cont. apply PCS_Seq. }
    iApply (pico_hash_same_state_step_wpEI
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M) Phi E _ _ _ Hseq
      with "Hworld Hown [Hcontinue]").
    - intros next state' Hactual. inversion Hactual; subst;
        try discriminate; try congruence; split; reflexivity.
    - iNext. iIntros "Hworld Hown".
      assert (Hready : exists next state', pico_core_step CT
        (CoreRun rGamma
          (SVarAss cache_tmp (EField cache_receiver hash_cache_field)) V
          read_cont) (mkPicoCoreState h sigma) next state').
      { destruct Hread_ready as (v & V' & Hread).
        exists (CoreRun
          (set_vars rGamma (update cache_tmp v (vars rGamma))) SSkip V'
          read_cont), (mkPicoCoreState h sigma).
        eapply PCS_AssignField; eauto. }
      iApply (pico_core_ownP_wp_from_direct_step_contI CT E Phi
        _ _ Hready with "Hown [Hworld Hcontinue]").
      iNext. iIntros (next state') "%Hread_step Hown".
      inversion Hread_step; subst; try discriminate; try congruence.
      match goal with
      | Hreceiver' : runtime_getVal rGamma cache_receiver = Some (Iot ?loc') |- _ =>
          assert (loc' = loc) by congruence; subst loc'
      end.
      unfold pico_core_semimm_worldI at 1.
      iDestruct "Hworld" as (gamma) "[%Hstate Hsem]".
      match goal with
      | Hactual_read : wm_read sigma V (loc, hash_cache_field) v V' |- _ =>
          pose proof (pico_core_semimm_cache_read_from_history
            CT hash_cache_protocol pico_hash_stable_abs hash_value A M
            (mkPicoCoreState h sigma) V (loc, hash_cache_field) v V'
            HashField Hstate Hactual_read Hfield) as Hcache_read
      end.
      iPoseProof (pico_core_cache_read_semimmI
        hash_cache_protocol A pico_hash_stable_abs gamma
        (pcsi_object CT hash_cache_protocol pico_hash_stable_abs hash_value A M
          (mkPicoCoreState h sigma)) hash_value
        (pcsi_snapshot CT hash_cache_protocol pico_hash_stable_abs hash_value A M
          (mkPicoCoreState h sigma))
        (loc, hash_cache_field) v with "Hsem []") as "[Hsem Hvalid]".
      { iPureIntro. exact Hcache_read. }
      iDestruct "Hvalid" as (k cv) "%Hvalid".
      destruct Hvalid as (Hfield' & Hvalue' & Hvalid & Hpublished).
      rewrite Hfield in Hfield'. inversion Hfield'; subst k.
      rewrite Hvalue in Hvalue'. inversion Hvalue'; subst cv.
      iAssert (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M (mkPicoCoreState h sigma))
        with "[Hsem]" as "Hworld".
      { iExists gamma. iFrame. iPureIntro. exact Hstate. }
      set (rGamma_read := set_vars rGamma
        (update cache_tmp v (vars rGamma))).
      assert (Htmp_read : runtime_getVal rGamma_read cache_tmp = Some v).
      { unfold rGamma_read, runtime_getVal, set_vars. apply update_same.
        eapply runtime_getVal_dom; eauto. }
      assert (Hreceiver_read : runtime_getVal rGamma_read cache_receiver =
        Some (Iot loc)).
      { unfold rGamma_read, runtime_getVal, set_vars.
        rewrite update_diff; [exact Hreceiver | discriminate]. }
      assert (Hresult_read : runtime_getVal rGamma_read cache_result =
        Some old_result).
      { unfold rGamma_read, runtime_getVal, set_vars.
        rewrite update_diff; [exact Hresult | discriminate]. }
      assert (Hskip : pico_core_step CT
        (CoreRun rGamma_read SSkip V' read_cont)
        (mkPicoCoreState h sigma)
        (CoreRun rGamma_read tail V' call_cont)
        (mkPicoCoreState h sigma)).
      { unfold read_cont. apply PCS_SkipSeq. }
      iApply (pico_hash_same_state_step_wpEI
        (pico_core_semimm_worldI CT hash_cache_protocol
          pico_hash_stable_abs hash_value A M) Phi E _ _ _ Hskip
        with "Hworld Hown [Hcontinue]").
      + intros next' state'' Hactual. inversion Hactual; subst;
          try discriminate; try congruence; split; reflexivity.
      + iNext. iIntros "Hworld Hown".
        assert (Htail : pico_core_step CT
          (CoreRun rGamma_read tail V' call_cont)
          (mkPicoCoreState h sigma)
          (CoreRun rGamma_read (pico_local_copy_cache_branch compute) V'
            (KSeq (SVarAss cache_result (EVar cache_tmp)) :: call_cont))
          (mkPicoCoreState h sigma)).
        { unfold tail. apply PCS_Seq. }
        iApply (pico_hash_same_state_step_wpEI
          (pico_core_semimm_worldI CT hash_cache_protocol
            pico_hash_stable_abs hash_value A M) Phi E _ _ _ Htail
          with "Hworld Hown [Hcontinue]").
        * intros next' state'' Hactual. inversion Hactual; subst;
            try discriminate; try congruence; split; reflexivity.
        * iNext. iIntros "Hworld Hown".
          assert (Henv_read : pico_core_typed_env CT
            [receiver_type; int_type; int_type] rGamma_read h).
          { unfold rGamma_read.
            destruct (hash_valid_value_shape hash_value v Hvalid)
              as [-> | [-> _]];
              eapply pico_hash_typed_env_set_tmp_int; eauto. }
          unfold call_cont.
          iApply (pico_hash_after_read_callable_wpI
            A hash_value M receiver_type method compute
            entry caller target h sigma rGamma_read V'
            K E Phi old_result loc v o assign Hreceiver_read Htmp_read
            Hresult_read Hvalid Hobj Hassign Hassignable Hfield
            (Hvalue (Int hash_value)) Htyping Henv_read Hlrstate
            with "Hcompute Hworld Hown Hcontinue").
  Qed.

  Lemma pico_hash_locals_wpI
      (R : pico_core_state -> iProp Sigma)
      (Phi : pico_core_val -> iProp Sigma)
      receiver_type compute rGamma state V
      (Henv : pico_core_typed_env CT [receiver_type] rGamma
        (pcs_heap state))
      (Htyping : stmt_typing CT [receiver_type] AbstractImm
        (pico_hash_method_stmt_with compute)
        [receiver_type; int_type; int_type]) :
    let rGamma1 := set_vars rGamma (vars rGamma ++ [Int 0]) in
    let rGamma2 := set_vars rGamma1 (vars rGamma1 ++ [Int 0]) in
    R state -∗ ownP state -∗
    ▷ (R state -∗ ownP state -∗
      WP CoreRun rGamma2 (pico_hash_method_core_stmt_with compute) V []
        @ NotStuck; top {{ Phi }}) -∗
    WP CoreRun rGamma (pico_hash_method_stmt_with compute) V []
      @ NotStuck; top {{ Phi }}.
  Proof.
    simpl.
    iIntros "HR Hown Hcore".
    destruct (pico_hash_method_typing_parts_with CT receiver_type compute Htyping)
      as (Hlocal1 & Hlocal2 & _).
    pose proof (pico_core_typed_env_real_lr_env
      CT [receiver_type] rGamma (pcs_heap state) Henv) as Hreal.
    inversion Hlocal1; subst.
    pose proof (pico_typed_runtime_env_local_runtime_absent
      CT [receiver_type] rGamma (pcs_heap state) cache_tmp Hreal Hnone)
      as Hruntime_none1.
    assert (Hdefault : default_value int_type = Int 0) by reflexivity.
    set (tail1 := SSeq (SLocal int_type cache_result)
      (pico_hash_method_core_stmt_with compute)).
    set (rGamma1 := set_vars rGamma (vars rGamma ++ [Int 0])).
    set (rGamma2 := set_vars rGamma1 (vars rGamma1 ++ [Int 0])).
    assert (Hseq1 : pico_core_step CT
      (CoreRun rGamma (pico_hash_method_stmt_with compute) V []) state
      (CoreRun rGamma (SLocal int_type cache_tmp) V [KSeq tail1]) state).
    { unfold pico_hash_method_stmt_with, tail1. apply PCS_Seq. }
    iApply (pico_hash_same_state_step_wpI R Phi _ _ state Hseq1
      with "HR Hown").
    - intros next state' Hstep. inversion Hstep; subst;
        try discriminate; try congruence; split; reflexivity.
    - iNext. iIntros "HR Hown".
      assert (Hdecl1 : pico_core_step CT
        (CoreRun rGamma (SLocal int_type cache_tmp) V [KSeq tail1]) state
        (CoreRun rGamma1 SSkip V [KSeq tail1]) state).
      { unfold rGamma1. rewrite <- Hdefault. apply PCS_Local.
        exact Hruntime_none1. }
      iApply (pico_hash_same_state_step_wpI R Phi _ _ state Hdecl1
        with "HR Hown").
      + intros next state' Hstep. inversion Hstep; subst;
          try discriminate; try congruence; split; reflexivity.
      + iNext. iIntros "HR Hown".
        assert (Hskip1 : pico_core_step CT
          (CoreRun rGamma1 SSkip V [KSeq tail1]) state
          (CoreRun rGamma1 tail1 V []) state) by apply PCS_SkipSeq.
        iApply (pico_hash_same_state_step_wpI R Phi _ _ state Hskip1
          with "HR Hown").
        * intros next state' Hstep. inversion Hstep; subst;
            try discriminate; try congruence; split; reflexivity.
        * iNext. iIntros "HR Hown".
          assert (Hseq2 : pico_core_step CT
            (CoreRun rGamma1 tail1 V []) state
            (CoreRun rGamma1 (SLocal int_type cache_result) V
              [KSeq (pico_hash_method_core_stmt_with compute)]) state).
          { unfold tail1. apply PCS_Seq. }
          iApply (pico_hash_same_state_step_wpI R Phi _ _ state Hseq2
            with "HR Hown").
          -- intros next state' Hstep. inversion Hstep; subst;
               try discriminate; try congruence; split; reflexivity.
          -- iNext. iIntros "HR Hown".
             assert (Henv1 : pico_core_typed_env CT
               [receiver_type; int_type] rGamma1 (pcs_heap state)).
             { unfold rGamma1. rewrite <- Hdefault.
               eapply pico_core_typed_env_after_local; eauto. }
             pose proof (pico_core_typed_env_real_lr_env
               CT [receiver_type; int_type] rGamma1 (pcs_heap state) Henv1)
               as Hreal1.
             inversion Hlocal2; subst.
             pose proof (pico_typed_runtime_env_local_runtime_absent
               CT [receiver_type; int_type] rGamma1 (pcs_heap state)
               cache_result Hreal1 Hnone0) as Hruntime_none2.
             assert (Hdecl2 : pico_core_step CT
               (CoreRun rGamma1 (SLocal int_type cache_result) V
                 [KSeq (pico_hash_method_core_stmt_with compute)]) state
               (CoreRun rGamma2 SSkip V
                 [KSeq (pico_hash_method_core_stmt_with compute)]) state).
             { unfold rGamma2. rewrite <- Hdefault.
               apply PCS_Local. exact Hruntime_none2. }
             iApply (pico_hash_same_state_step_wpI R Phi _ _ state Hdecl2
               with "HR Hown").
             ++ intros next state' Hstep. inversion Hstep; subst;
                  try discriminate; try congruence; split; reflexivity.
             ++ iNext. iIntros "HR Hown".
                assert (Hskip2 : pico_core_step CT
                  (CoreRun rGamma2 SSkip V
                    [KSeq (pico_hash_method_core_stmt_with compute)]) state
                  (CoreRun rGamma2 (pico_hash_method_core_stmt_with compute)
                    V []) state) by apply PCS_SkipSeq.
                iApply (pico_hash_same_state_step_wpI R Phi _ _ state Hskip2
                  with "HR Hown").
                ** intros next state' Hstep. inversion Hstep; subst;
                     try discriminate; try congruence; split; reflexivity.
                ** iNext. iIntros "HR Hown".
                   unfold rGamma1, rGamma2.
                   iApply ("Hcore" with "HR Hown").
  Qed.

  Lemma pico_hash_locals_callable_wpI
      (R : pico_core_state -> iProp Sigma)
      (Phi : pico_core_val -> iProp Sigma)
      E receiver_type compute rGamma state V caller target K
      (Henv : pico_core_typed_env CT [receiver_type] rGamma
        (pcs_heap state))
      (Htyping : stmt_typing CT [receiver_type] AbstractImm
        (pico_hash_method_stmt_with compute)
        [receiver_type; int_type; int_type]) :
    let rGamma1 := set_vars rGamma (vars rGamma ++ [Int 0]) in
    let rGamma2 := set_vars rGamma1 (vars rGamma1 ++ [Int 0]) in
    R state -∗ ownP state -∗
    ▷ (R state -∗ ownP state -∗
      WP CoreRun rGamma2 (pico_hash_method_core_stmt_with compute) V
        (KCall caller target cache_result :: K)
        @ NotStuck; E {{ Phi }}) -∗
    WP CoreRun rGamma (pico_hash_method_stmt_with compute) V
      (KCall caller target cache_result :: K)
      @ NotStuck; E {{ Phi }}.
  Proof.
    simpl. iIntros "HR Hown Hcore".
    destruct (pico_hash_method_typing_parts_with CT receiver_type compute Htyping)
      as (Hlocal1 & Hlocal2 & _).
    pose proof (pico_core_typed_env_real_lr_env
      CT [receiver_type] rGamma (pcs_heap state) Henv) as Hreal.
    inversion Hlocal1; subst.
    pose proof (pico_typed_runtime_env_local_runtime_absent
      CT [receiver_type] rGamma (pcs_heap state) cache_tmp Hreal Hnone)
      as Hruntime_none1.
    assert (Hdefault : default_value int_type = Int 0) by reflexivity.
    set (call_cont := KCall caller target cache_result :: K).
    set (tail1 := SSeq (SLocal int_type cache_result)
      (pico_hash_method_core_stmt_with compute)).
    set (rGamma1 := set_vars rGamma (vars rGamma ++ [Int 0])).
    set (rGamma2 := set_vars rGamma1 (vars rGamma1 ++ [Int 0])).
    assert (Hseq1 : pico_core_step CT
      (CoreRun rGamma (pico_hash_method_stmt_with compute) V call_cont) state
      (CoreRun rGamma (SLocal int_type cache_tmp) V
        (KSeq tail1 :: call_cont)) state).
    { unfold pico_hash_method_stmt_with, tail1. apply PCS_Seq. }
    iApply (pico_hash_same_state_step_wpEI R Phi E _ _ state Hseq1
      with "HR Hown [Hcore]").
    - intros next state' Hstep. inversion Hstep; subst;
        try discriminate; try congruence; split; reflexivity.
    - iNext. iIntros "HR Hown".
      assert (Hdecl1 : pico_core_step CT
        (CoreRun rGamma (SLocal int_type cache_tmp) V
          (KSeq tail1 :: call_cont)) state
        (CoreRun rGamma1 SSkip V (KSeq tail1 :: call_cont)) state).
      { unfold rGamma1. rewrite <- Hdefault. apply PCS_Local.
        exact Hruntime_none1. }
      iApply (pico_hash_same_state_step_wpEI R Phi E _ _ state Hdecl1
        with "HR Hown [Hcore]").
      + intros next state' Hstep. inversion Hstep; subst;
          try discriminate; try congruence; split; reflexivity.
      + iNext. iIntros "HR Hown".
        assert (Hskip1 : pico_core_step CT
          (CoreRun rGamma1 SSkip V (KSeq tail1 :: call_cont)) state
          (CoreRun rGamma1 tail1 V call_cont) state) by apply PCS_SkipSeq.
        iApply (pico_hash_same_state_step_wpEI R Phi E _ _ state Hskip1
          with "HR Hown [Hcore]").
        * intros next state' Hstep. inversion Hstep; subst;
            try discriminate; try congruence; split; reflexivity.
        * iNext. iIntros "HR Hown".
          assert (Hseq2 : pico_core_step CT
            (CoreRun rGamma1 tail1 V call_cont) state
            (CoreRun rGamma1 (SLocal int_type cache_result) V
              (KSeq (pico_hash_method_core_stmt_with compute) :: call_cont))
            state).
          { unfold tail1. apply PCS_Seq. }
          iApply (pico_hash_same_state_step_wpEI R Phi E _ _ state Hseq2
            with "HR Hown [Hcore]").
          -- intros next state' Hstep. inversion Hstep; subst;
               try discriminate; try congruence; split; reflexivity.
          -- iNext. iIntros "HR Hown".
             assert (Henv1 : pico_core_typed_env CT
               [receiver_type; int_type] rGamma1 (pcs_heap state)).
             { unfold rGamma1. rewrite <- Hdefault.
               eapply pico_core_typed_env_after_local; eauto. }
             pose proof (pico_core_typed_env_real_lr_env
               CT [receiver_type; int_type] rGamma1 (pcs_heap state) Henv1)
               as Hreal1.
             inversion Hlocal2; subst.
             pose proof (pico_typed_runtime_env_local_runtime_absent
               CT [receiver_type; int_type] rGamma1 (pcs_heap state)
               cache_result Hreal1 Hnone0) as Hruntime_none2.
             assert (Hdecl2 : pico_core_step CT
               (CoreRun rGamma1 (SLocal int_type cache_result) V
                 (KSeq (pico_hash_method_core_stmt_with compute) :: call_cont))
               state
               (CoreRun rGamma2 SSkip V
                 (KSeq (pico_hash_method_core_stmt_with compute) :: call_cont))
               state).
             { unfold rGamma2. rewrite <- Hdefault.
               apply PCS_Local. exact Hruntime_none2. }
             iApply (pico_hash_same_state_step_wpEI R Phi E _ _ state Hdecl2
               with "HR Hown [Hcore]").
             ++ intros next state' Hstep. inversion Hstep; subst;
                  try discriminate; try congruence; split; reflexivity.
             ++ iNext. iIntros "HR Hown".
                assert (Hskip2 : pico_core_step CT
                  (CoreRun rGamma2 SSkip V
                    (KSeq (pico_hash_method_core_stmt_with compute) :: call_cont))
                  state
                  (CoreRun rGamma2 (pico_hash_method_core_stmt_with compute) V
                    call_cont) state) by apply PCS_SkipSeq.
                iApply (pico_hash_same_state_step_wpEI R Phi E _ _ state Hskip2
                  with "HR Hown [Hcore]").
                ** intros next state' Hstep. inversion Hstep; subst;
                     try discriminate; try congruence; split; reflexivity.
                ** iNext. iIntros "HR Hown".
                   unfold rGamma1, rGamma2, call_cont.
                   iApply ("Hcore" with "HR Hown").
  Qed.

  Theorem pico_hash_method_semantic_for_with_computationI
      (A : PicoCoreCacheAdapter hash_cache_protocol)
      hash_value (receiver_ok : Loc -> Prop)
      (M : PicoCoreSemImmInstantiation CT hash_cache_protocol
        pico_hash_stable_abs hash_value A)
      receiver_type method compute
      (Htyping : stmt_typing CT [receiver_type] AbstractImm
        (pico_hash_method_stmt_with compute)
        [receiver_type; int_type; int_type])
      (Hfield : forall rGamma h loc,
        pico_core_typed_env CT [receiver_type; int_type; int_type] rGamma h ->
        runtime_getVal rGamma cache_receiver = Some (Iot loc) ->
        receiver_ok loc ->
        pico_core_cache_field hash_cache_protocol A
          (loc, hash_cache_field) = Some HashField)
      (Hvalue : PicoHashCacheValueAdapter A)
      (Hcache_runtime : PicoHashCacheRuntimeAssignable receiver_type) :
    pico_ts_derived_computationI CT
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      ts_no_calls
      [receiver_type; int_type; int_type]
      [receiver_type; int_type; int_type]
      compute cache_tmp (Int hash_value) -∗
    pico_semantic_methodI CT
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      (pico_hash_method_contract_for receiver_ok hash_value)
      (pico_hash_method_def_with receiver_type method compute).
  Proof.
    iIntros "#Hts_compute".
    iPoseProof (pico_hash_ts_computation_direct_write_freeI
      _ receiver_type compute hash_value with "Hts_compute") as "%Hwrite_free".
    iDestruct "Hts_compute" as "[_ #Hcompute]".
    unfold pico_semantic_methodI; simpl.
    iModIntro.
    iIntros (rGamma h sigma V) "%Henv %Hlrstate %Hpre Hworld Hown".
    destruct Hpre as (loc & Hreceiver & Hreceiver_ok).
    destruct (pico_hash_method_typing_parts_with CT receiver_type compute Htyping)
      as (Hlocal1 & Hlocal2 & _).
    set (rGamma1 := set_vars rGamma (vars rGamma ++ [Int 0])).
    set (rGamma2 := set_vars rGamma1 (vars rGamma1 ++ [Int 0])).
    assert (Henv1 : pico_core_typed_env CT [receiver_type; int_type]
      rGamma1 h).
    { unfold rGamma1. change (Int 0) with (default_value int_type).
      eapply pico_core_typed_env_after_local; eauto. }
    assert (Henv2 : pico_core_typed_env CT
      [receiver_type; int_type; int_type] rGamma2 h).
    { unfold rGamma2. change (Int 0) with (default_value int_type).
      eapply pico_core_typed_env_after_local; eauto. }
    pose proof (pico_core_typed_env_wf_config
      CT [receiver_type] rGamma h Henv) as Hconfig.
    unfold wf_r_config in Hconfig.
    destruct Hconfig as [_ [_ [_ [_ [Hlength _]]]]].
    assert (Hlength1 : length (vars rGamma) = 1).
    { unfold dom in Hlength. simpl in Hlength. lia. }
    change (List.length (vars rGamma) = 1) in Hlength1.
    assert (Hreceiver2 : runtime_getVal rGamma2 cache_receiver =
      Some (Iot loc)).
    { unfold rGamma2, rGamma1, runtime_getVal, set_vars, cache_receiver.
      rewrite nth_error_app1.
      - rewrite nth_error_app1; [exact Hreceiver | rewrite Hlength1; lia].
      - rewrite length_app. rewrite Hlength1. simpl. lia. }
    assert (Htmp2 : runtime_getVal rGamma2 cache_tmp = Some (Int 0)).
    { unfold rGamma2, rGamma1, runtime_getVal, set_vars, cache_tmp.
      rewrite nth_error_app1.
      - rewrite nth_error_app2; [| lia].
        replace (1 - List.length (vars rGamma)) with 0 by lia.
        reflexivity.
      - rewrite length_app. simpl. lia. }
    assert (Hresult2 : runtime_getVal rGamma2 cache_result = Some (Int 0)).
    { unfold rGamma2, runtime_getVal, set_vars, cache_result.
      rewrite nth_error_app2; [| unfold rGamma1; rewrite length_app;
        simpl; lia].
      unfold rGamma1. rewrite length_app.
      change (nth_error [Int 0]
        (2 - (List.length (vars rGamma) + 1)) = Some (Int 0)).
      rewrite Hlength1. reflexivity. }
    destruct (Hcache_runtime rGamma2 h loc Henv2 Hreceiver2)
      as (o & assign & Hobj & Hassign & Hassignable).
    pose proof Hassign as Hassign_lookup.
    unfold sf_assignability_rel in Hassign_lookup.
    destruct Hassign_lookup as (fdef & Hfield_lookup & _).
    pose proof (pico_core_typed_env_wf_config CT
      [receiver_type; int_type; int_type] rGamma2 h Henv2) as Hconfig2.
    destruct Hconfig2 as [_ [Hheap _]].
    assert (Hloc_bound : loc < length h) by
      (eapply runtime_getObj_dom; eauto).
    specialize (Hheap loc Hloc_bound).
    unfold wf_obj in Hheap. rewrite Hobj in Hheap.
    destruct Hheap as [_ (field_defs & Hcollect & Hfields_length & _)].
    unfold sf_def_rel in Hfield_lookup.
    inversion Hfield_lookup as
      [CT' C' collected f' fdef' Hcollect' Hlookup]; subst.
    assert (Hcollected : collected = field_defs) by
      (eapply collect_fields_deterministic_rel; eauto).
    subst collected.
    unfold gget in Hlookup.
    assert (Hfield_bound : hash_cache_field < length (fields_map o)).
    { rewrite Hfields_length. apply nth_error_Some.
      rewrite Hlookup. discriminate. }
    destruct (nth_error (fields_map o) hash_cache_field)
      as [current |] eqn:Hcurrent; [| apply nth_error_None in Hcurrent; lia].
    assert (Hread_ready : exists observed V',
      wm_read sigma V (loc, hash_cache_field) observed V').
    { eapply pico_core_state_wf_read_exists; eauto. }
    iApply (pico_hash_locals_wpI
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      (pico_hash_method_postI
        (pico_core_semimm_worldI CT hash_cache_protocol
          pico_hash_stable_abs hash_value A M) rGamma hash_value)
      receiver_type compute rGamma (mkPicoCoreState h sigma) V
      Henv Htyping with "Hworld Hown").
    iNext. iIntros "Hworld Hown".
    unfold rGamma1, rGamma2 in Hreceiver2, Htmp2, Hresult2, Henv2 |- *.
    iApply (pico_hash_read_then_finish_wpI A hash_value M
      compute rGamma h sigma
      (set_vars (set_vars rGamma (vars rGamma ++ [Int 0]))
        (vars (set_vars rGamma (vars rGamma ++ [Int 0])) ++ [Int 0]))
      V (Int 0) (Int 0) loc o assign Hreceiver2 Htmp2 Hresult2
      Hobj Hassign Hassignable
      (Hfield rGamma2 h loc Henv2 Hreceiver2 Hreceiver_ok) Hvalue Hread_ready
      with "Hcompute Hworld Hown").
  Qed.

  Theorem pico_hash_method_semantic_with_computationI
      (A : PicoCoreCacheAdapter hash_cache_protocol)
      hash_value
      (M : PicoCoreSemImmInstantiation CT hash_cache_protocol
        pico_hash_stable_abs hash_value A)
      receiver_type method compute
      (Htyping : stmt_typing CT [receiver_type] AbstractImm
        (pico_hash_method_stmt_with compute)
        [receiver_type; int_type; int_type])
      (Hfield : PicoHashCacheFieldAdapter A receiver_type)
      (Hvalue : PicoHashCacheValueAdapter A)
      (Hcache_runtime : PicoHashCacheRuntimeAssignable receiver_type) :
    pico_ts_derived_computationI CT
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      ts_no_calls [receiver_type; int_type; int_type]
      [receiver_type; int_type; int_type]
      compute cache_tmp (Int hash_value) -∗
    pico_semantic_methodI CT
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      (pico_hash_method_contract hash_value)
      (pico_hash_method_def_with receiver_type method compute).
  Proof.
    iIntros "Hcompute".
    assert (Hfield_true : forall rGamma h loc,
      pico_core_typed_env CT [receiver_type; int_type; int_type] rGamma h ->
      runtime_getVal rGamma cache_receiver = Some (Iot loc) ->
      True -> pico_core_cache_field hash_cache_protocol A
        (loc, hash_cache_field) = Some HashField).
    { intros rGamma h loc Henv Hreceiver _. eapply Hfield; eauto. }
    iApply (pico_hash_method_semantic_for_with_computationI A hash_value
      (fun _ => True) M receiver_type method compute Htyping Hfield_true Hvalue
      Hcache_runtime with "Hcompute").
  Qed.

  Theorem pico_hash_method_callable_for_with_computationI
      (A : PicoCoreCacheAdapter hash_cache_protocol)
      hash_value (receiver_ok : Loc -> Prop)
      (M : PicoCoreSemImmInstantiation CT hash_cache_protocol
        pico_hash_stable_abs hash_value A)
      receiver_type method compute
      (Htyping : stmt_typing CT [receiver_type] AbstractImm
        (pico_hash_method_stmt_with compute)
        [receiver_type; int_type; int_type])
      (Hfield : forall rGamma h loc,
        pico_core_typed_env CT [receiver_type; int_type; int_type] rGamma h ->
        runtime_getVal rGamma cache_receiver = Some (Iot loc) ->
        receiver_ok loc ->
        pico_core_cache_field hash_cache_protocol A
          (loc, hash_cache_field) = Some HashField)
      (Hvalue : PicoHashCacheValueAdapter A)
      (Hcache_runtime : PicoHashCacheRuntimeAssignable receiver_type) :
    pico_ts_derived_computationI CT
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      ts_no_calls
      [receiver_type; int_type; int_type]
      [receiver_type; int_type; int_type]
      compute cache_tmp (Int hash_value) -∗
    pico_callable_methodI CT
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      (pico_hash_method_contract_for receiver_ok hash_value)
      (pico_hash_method_def_with receiver_type method compute).
  Proof.
    iIntros "#Hts_compute".
    iPoseProof (pico_hash_ts_computation_direct_write_freeI
      _ receiver_type compute hash_value with "Hts_compute") as "%Hwrite_free".
    iDestruct "Hts_compute" as "[_ #Hcompute]".
    unfold pico_callable_methodI; simpl.
    iModIntro.
    iIntros (callee caller target entry_receiver h sigma V K E Phi)
      "%Henv %Hentry %Hlrstate %Hpre Hworld Hown Hcontinue".
    destruct Hpre as (loc & Hreceiver & Hreceiver_ok).
    assert (entry_receiver = loc).
    { unfold get_this_var_mapping, runtime_getVal, cache_receiver in *.
      destruct (vars callee) as [|head tail]; simpl in *; try discriminate.
      destruct head; simpl in *; try discriminate; congruence. }
    subst entry_receiver.
    destruct (pico_hash_method_typing_parts_with CT receiver_type compute Htyping)
      as (Hlocal1 & Hlocal2 & _).
    set (rGamma1 := set_vars callee (vars callee ++ [Int 0])).
    set (rGamma2 := set_vars rGamma1 (vars rGamma1 ++ [Int 0])).
    assert (Henv1 : pico_core_typed_env CT [receiver_type; int_type]
      rGamma1 h).
    { unfold rGamma1. change (Int 0) with (default_value int_type).
      eapply pico_core_typed_env_after_local; eauto. }
    assert (Henv2 : pico_core_typed_env CT
      [receiver_type; int_type; int_type] rGamma2 h).
    { unfold rGamma2. change (Int 0) with (default_value int_type).
      eapply pico_core_typed_env_after_local; eauto. }
    pose proof (pico_core_typed_env_wf_config
      CT [receiver_type] callee h Henv) as Hconfig.
    unfold wf_r_config in Hconfig.
    destruct Hconfig as [_ [_ [_ [_ [Hlength _]]]]].
    assert (Hlength1 : length (vars callee) = 1).
    { unfold dom in Hlength. simpl in Hlength. lia. }
    change (List.length (vars callee) = 1) in Hlength1.
    assert (Hreceiver2 : runtime_getVal rGamma2 cache_receiver =
      Some (Iot loc)).
    { unfold rGamma2, rGamma1, runtime_getVal, set_vars, cache_receiver.
      rewrite nth_error_app1.
      - rewrite nth_error_app1; [exact Hreceiver | rewrite Hlength1; lia].
      - rewrite length_app. rewrite Hlength1. simpl. lia. }
    assert (Htmp2 : runtime_getVal rGamma2 cache_tmp = Some (Int 0)).
    { unfold rGamma2, rGamma1, runtime_getVal, set_vars, cache_tmp.
      rewrite nth_error_app1.
      - rewrite nth_error_app2; [| lia].
        replace (1 - List.length (vars callee)) with 0 by lia.
        reflexivity.
      - rewrite length_app. simpl. lia. }
    assert (Hresult2 : runtime_getVal rGamma2 cache_result = Some (Int 0)).
    { unfold rGamma2, runtime_getVal, set_vars, cache_result.
      rewrite nth_error_app2; [| unfold rGamma1; rewrite length_app;
        simpl; lia].
      unfold rGamma1. rewrite length_app.
      change (nth_error [Int 0]
        (2 - (List.length (vars callee) + 1)) = Some (Int 0)).
      rewrite Hlength1. reflexivity. }
    destruct (Hcache_runtime rGamma2 h loc Henv2 Hreceiver2)
      as (o & assign & Hobj & Hassign & Hassignable).
    pose proof Hassign as Hassign_lookup.
    unfold sf_assignability_rel in Hassign_lookup.
    destruct Hassign_lookup as (fdef & Hfield_lookup & _).
    pose proof (pico_core_typed_env_wf_config CT
      [receiver_type; int_type; int_type] rGamma2 h Henv2) as Hconfig2.
    destruct Hconfig2 as [_ [Hheap _]].
    assert (Hloc_bound : loc < length h) by
      (eapply runtime_getObj_dom; eauto).
    specialize (Hheap loc Hloc_bound).
    unfold wf_obj in Hheap. rewrite Hobj in Hheap.
    destruct Hheap as [_ (field_defs & Hcollect & Hfields_length & _)].
    unfold sf_def_rel in Hfield_lookup.
    inversion Hfield_lookup as
      [CT' C' collected f' fdef' Hcollect' Hlookup]; subst.
    assert (Hcollected : collected = field_defs) by
      (eapply collect_fields_deterministic_rel; eauto).
    subst collected.
    unfold gget in Hlookup.
    assert (Hfield_bound : hash_cache_field < length (fields_map o)).
    { rewrite Hfields_length. apply nth_error_Some.
      rewrite Hlookup. discriminate. }
    destruct (nth_error (fields_map o) hash_cache_field)
      as [current |] eqn:Hcurrent; [| apply nth_error_None in Hcurrent; lia].
    assert (Hread_ready : exists observed V',
      wm_read sigma V (loc, hash_cache_field) observed V').
    { eapply pico_core_state_wf_read_exists; eauto. }
    iApply (pico_hash_locals_callable_wpI
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      Phi E receiver_type compute callee (mkPicoCoreState h sigma) V
      caller target K Henv Htyping with "Hworld Hown [Hcontinue]").
    iNext. iIntros "Hworld Hown".
    unfold rGamma1, rGamma2 in Hreceiver2, Htmp2, Hresult2, Henv2 |- *.
    iApply (pico_hash_read_then_finish_callable_wpI A hash_value M
      receiver_type method compute callee caller target h sigma
      (set_vars (set_vars callee (vars callee ++ [Int 0]))
        (vars (set_vars callee (vars callee ++ [Int 0])) ++ [Int 0]))
      V K E Phi (Int 0) (Int 0) loc o assign
      Hreceiver2 Htmp2 Hresult2 Hobj Hassign Hassignable
      (Hfield rGamma2 h loc Henv2 Hreceiver2 Hreceiver_ok) Hvalue Hread_ready
      Htyping Henv2 Hlrstate
      with "Hcompute Hworld Hown Hcontinue").
  Qed.

  Theorem pico_hash_method_callable_with_computationI
      (A : PicoCoreCacheAdapter hash_cache_protocol)
      hash_value
      (M : PicoCoreSemImmInstantiation CT hash_cache_protocol
        pico_hash_stable_abs hash_value A)
      receiver_type method compute
      (Htyping : stmt_typing CT [receiver_type] AbstractImm
        (pico_hash_method_stmt_with compute)
        [receiver_type; int_type; int_type])
      (Hfield : PicoHashCacheFieldAdapter A receiver_type)
      (Hvalue : PicoHashCacheValueAdapter A)
      (Hcache_runtime : PicoHashCacheRuntimeAssignable receiver_type) :
    pico_ts_derived_computationI CT
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      ts_no_calls [receiver_type; int_type; int_type]
      [receiver_type; int_type; int_type]
      compute cache_tmp (Int hash_value) -∗
    pico_callable_methodI CT
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      (pico_hash_method_contract hash_value)
      (pico_hash_method_def_with receiver_type method compute).
  Proof.
    iIntros "Hcompute".
    assert (Hfield_true : forall rGamma h loc,
      pico_core_typed_env CT [receiver_type; int_type; int_type] rGamma h ->
      runtime_getVal rGamma cache_receiver = Some (Iot loc) ->
      True -> pico_core_cache_field hash_cache_protocol A
        (loc, hash_cache_field) = Some HashField).
    { intros rGamma h loc Henv Hreceiver _. eapply Hfield; eauto. }
    iApply (pico_hash_method_callable_for_with_computationI A hash_value
      (fun _ => True) M receiver_type method compute Htyping Hfield_true Hvalue
      Hcache_runtime with "Hcompute").
  Qed.

  Theorem pico_hash_method_semanticI
      (A : PicoCoreCacheAdapter hash_cache_protocol)
      hash_value
      (M : PicoCoreSemImmInstantiation CT hash_cache_protocol
        pico_hash_stable_abs hash_value A)
      receiver_type method
      (Htyping : stmt_typing CT [receiver_type] AbstractImm
        (pico_hash_method_stmt hash_value)
        [receiver_type; int_type; int_type])
      (Hfield : PicoHashCacheFieldAdapter A receiver_type)
      (Hvalue : PicoHashCacheValueAdapter A)
      (Hcache_runtime : PicoHashCacheRuntimeAssignable receiver_type) :
    ⊢ pico_semantic_methodI CT
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      (pico_hash_method_contract hash_value)
      (pico_hash_method_def receiver_type method hash_value).
  Proof.
    change (⊢ pico_semantic_methodI CT
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      (pico_hash_method_contract hash_value)
      (pico_hash_method_def_with receiver_type method
        (pico_hash_compute_stmt hash_value))).
    iApply (pico_hash_method_semantic_with_computationI A hash_value M
      receiver_type method (pico_hash_compute_stmt hash_value)
      Htyping Hfield Hvalue Hcache_runtime).
    iApply pico_hash_literal_ts_computationI.
  Qed.

  Theorem pico_hash_method_callableI
      (A : PicoCoreCacheAdapter hash_cache_protocol) hash_value
      (M : PicoCoreSemImmInstantiation CT hash_cache_protocol
        pico_hash_stable_abs hash_value A)
      receiver_type method
      (Htyping : stmt_typing CT [receiver_type] AbstractImm
        (pico_hash_method_stmt hash_value)
        [receiver_type; int_type; int_type])
      (Hfield : PicoHashCacheFieldAdapter A receiver_type)
      (Hvalue : PicoHashCacheValueAdapter A)
      (Hcache_runtime : PicoHashCacheRuntimeAssignable receiver_type) :
    ⊢ pico_callable_methodI CT
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      (pico_hash_method_contract hash_value)
      (pico_hash_method_def receiver_type method hash_value).
  Proof.
    change (⊢ pico_callable_methodI CT
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      (pico_hash_method_contract hash_value)
      (pico_hash_method_def_with receiver_type method
        (pico_hash_compute_stmt hash_value))).
    iApply (pico_hash_method_callable_with_computationI A hash_value M
      receiver_type method (pico_hash_compute_stmt hash_value)
      Htyping Hfield Hvalue Hcache_runtime).
    iApply pico_hash_literal_ts_computationI.
  Qed.

  Theorem pico_hash_callable_and_exported_with_computationI
      (A : PicoCoreCacheAdapter hash_cache_protocol) hash_value
      (M : PicoCoreSemImmInstantiation CT hash_cache_protocol
        pico_hash_stable_abs hash_value A)
      receiver_type method compute
      (Htyping : stmt_typing CT [receiver_type] AbstractImm
        (pico_hash_method_stmt_with compute)
        [receiver_type; int_type; int_type])
      (Hfield : PicoHashCacheFieldAdapter A receiver_type)
      (Hvalue : PicoHashCacheValueAdapter A)
      (Hcache_runtime : PicoHashCacheRuntimeAssignable receiver_type) :
    pico_ts_derived_computationI CT
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      ts_no_calls [receiver_type; int_type; int_type]
      [receiver_type; int_type; int_type]
      compute cache_tmp (Int hash_value) -∗
    pico_callable_methodI CT
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      (pico_hash_method_contract hash_value)
      (pico_hash_method_def_with receiver_type method compute) ∗
    pico_exported_methodI CT
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      (pico_hash_method_contract hash_value)
      (pico_hash_method_def_with receiver_type method compute).
  Proof.
    iIntros "#Hcompute".
    iPoseProof (pico_hash_method_callable_with_computationI A hash_value M
      receiver_type method compute Htyping Hfield Hvalue Hcache_runtime
      with "Hcompute") as "#Hcallable".
    iSplit; [iExact "Hcallable" |].
    iApply pico_callable_method_exportI. iExact "Hcallable".
  Qed.

  (** Generic public installation: source typing and the verified computation
      are combined with the cache-control WP at the ordinary [wf_method]
      boundary. *)
  Theorem pico_hash_verified_computation_api_wfI
      (A : PicoCoreCacheAdapter hash_cache_protocol)
      hash_value
      (M : PicoCoreSemImmInstantiation CT hash_cache_protocol
        pico_hash_stable_abs hash_value A)
      C receiver_type method compute
      (Htyping : stmt_typing CT [receiver_type] AbstractImm
        (pico_hash_method_stmt_with compute)
        [receiver_type; int_type; int_type])
      (Hoverride : forall parent_def parent mdef_parent,
        find_class CT C = Some parent_def ->
        super (signature parent_def) = Some parent ->
        FindMethodWithName CT parent method mdef_parent ->
        msignature mdef_parent =
          pico_hash_method_signature receiver_type method)
      (Hfield : PicoHashCacheFieldAdapter A receiver_type)
      (Hvalue : PicoHashCacheValueAdapter A)
      (Hcache_runtime : PicoHashCacheRuntimeAssignable receiver_type) :
    pico_ts_derived_computationI CT
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      ts_no_calls
      [receiver_type; int_type; int_type]
      [receiver_type; int_type; int_type]
      compute cache_tmp (Int hash_value) -∗
    pico_callable_method_wfI CT
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      C (pico_hash_method_def_with receiver_type method compute)
      (pico_hash_method_contract hash_value).
  Proof.
    iIntros "#Hcompute".
    iApply pico_callable_method_wf_introI.
    - eapply pico_hash_method_def_with_wf; eauto.
    - iApply (pico_hash_method_callable_with_computationI A hash_value M
        receiver_type method compute Htyping Hfield Hvalue Hcache_runtime
        with "Hcompute").
  Qed.

  (** The literal computation is one corollary of the generic installation.
      Its
      remaining parameters are semantic-object adapter/admissibility laws,
      not a pre-proved semantic method contract. *)
  Theorem pico_hash_literal_model_api_wfI
      (A : PicoCoreCacheAdapter hash_cache_protocol)
      hash_value
      (M : PicoCoreSemImmInstantiation CT hash_cache_protocol
        pico_hash_stable_abs hash_value A)
      C receiver_type method
      (Htyping : stmt_typing CT
        [receiver_type]
        AbstractImm (pico_hash_method_stmt hash_value)
        [receiver_type; int_type; int_type])
      (Hoverride : forall parent_def parent mdef_parent,
        find_class CT C = Some parent_def ->
        super (signature parent_def) = Some parent ->
        FindMethodWithName CT parent method mdef_parent ->
        msignature mdef_parent =
          pico_hash_method_signature receiver_type method)
      (Hfield : PicoHashCacheFieldAdapter A receiver_type)
      (Hvalue : PicoHashCacheValueAdapter A)
      (Hcache_runtime : PicoHashCacheRuntimeAssignable receiver_type) :
    ⊢ pico_callable_method_wfI CT
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      C (pico_hash_method_def receiver_type method hash_value)
      (pico_hash_method_contract hash_value).
  Proof.
    change (⊢ pico_callable_method_wfI CT
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      C (pico_hash_method_def_with receiver_type method
        (pico_hash_compute_stmt hash_value))
      (pico_hash_method_contract hash_value)).
    iApply (pico_hash_verified_computation_api_wfI A hash_value M C
      receiver_type method (pico_hash_compute_stmt hash_value)
      Htyping Hoverride Hfield Hvalue Hcache_runtime).
    iApply pico_hash_literal_ts_computationI.
  Qed.

  (** The pure trace-level rejection remains useful independently of the
      concrete CESK/adequacy rejection in [PicoHashExecutionTrace]. *)
  Theorem pico_double_read_hash_trace_contract_refuted
      hash_value (Hnonzero : hash_value <> 0) :
    ~ CacheSafeMethod hash_cache_protocol hash_pure_result
        pico_double_read_hash_run.
  Proof.
    exact (pico_double_read_hash_not_cache_safe hash_value Hnonzero).
  Qed.
End pico_hash_semantic_api.
