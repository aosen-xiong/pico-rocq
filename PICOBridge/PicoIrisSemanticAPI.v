From iris.program_logic Require Import weakestpre ownp.
From iris.proofmode Require Import proofmode.

Require Import Syntax Helpers Subtyping Typing Bigstep.
Require Import Core.GenericCacheProtocol.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage
  PICOBridge.PicoIrisCoreInvariant PICOBridge.PicoIrisCoreWP
  PICOBridge.PicoIrisResourceLogicalRelation
  PICOBridge.PicoIrisTypingFundamental PICOBridge.PicoCacheTyping.

(** * Semantic API Boundaries for PICO

    Ordinary PICO typing proves the fundamental safety theorem.  Exported APIs
    may advertise stronger behavior by proving that their implementation
    inhabits a bespoke Iris method contract.  This is the same separation used
    by logical approaches to type soundness: clients use the semantic contract,
    while an unsafe or concurrent implementation is verified once at the API
    boundary. *)

Record PicoSemanticMethodContract : Type := {
  psmc_pre : r_env -> pico_core_state -> Prop;
  psmc_post : r_env -> pico_core_val -> Prop;
}.

(** Evidence exported at a successful callable-method return.  This is the
    normalized bridge between a method-specific functional contract and the
    ordinary PICO return-transfer theorem. *)
Definition PicoCallableReturnEvidence
    (CT : class_table) (entry_heap : heap) (entry_receiver : Loc)
    (mdef : method_def) (callee_done : r_env)
    (final_state : pico_core_state) (returned : value) : Prop :=
  exists body_sGamma' body_ret_type,
    static_getType body_sGamma' (mreturn (mbody mdef)) =
      Some body_ret_type /\
    qualified_type_subtype CT body_ret_type (mret (msignature mdef)) /\
    pico_core_typed_env CT body_sGamma' callee_done
      (pcs_heap final_state) /\
    get_this_var_mapping (vars callee_done) = Some entry_receiver /\
    pico_core_heap_types_extend entry_heap (pcs_heap final_state) /\
    pico_core_lr_state CT final_state /\
    runtime_getVal callee_done (mreturn (mbody mdef)) = Some returned.

Section pico_semantic_api.
  Context `{Hmem : CacheMemoryModel}.
  Context `{Hprogress : CacheMemoryModelProgress}.
  Context (CT : class_table).
  Context `{!ownPGS (pico_core_language CT) Sigma}.

  (** A method implementation inhabits a semantic contract when every
      well-typed call frame satisfying the contract precondition has a
      [NotStuck] WP, returns the semantic resource, and establishes the
      contract postcondition.  The postcondition is interpreted relative to
      the entry environment so it can relate arguments to the result. *)
  Definition pico_semantic_methodI
      (R : pico_core_state -> iProp Sigma)
      (contract : PicoSemanticMethodContract)
      (mdef : method_def) : iProp Sigma :=
    let msig := msignature mdef in
    let body := mbody mdef in
    let sGamma := mreceiver msig :: mparams msig in
    (□ ∀ rGamma h sigma V,
      ⌜pico_core_typed_env CT sGamma rGamma h⌝ -∗
      ⌜pico_core_lr_state CT (mkPicoCoreState h sigma)⌝ -∗
      ⌜psmc_pre contract rGamma (mkPicoCoreState h sigma)⌝ -∗
      R (mkPicoCoreState h sigma) -∗
      ownP (mkPicoCoreState h sigma) -∗
      WP CoreRun rGamma (mbody_stmt body) V [] @ NotStuck; top
        {{ result,
          ∃ final_state,
            ownP final_state ∗
            R final_state ∗
            ⌜psmc_post contract rGamma result⌝ }})%I.

  (** Callable contracts expose the method-return boundary rather than waiting
      for the caller's continuation to terminate.  The client continuation is
      resumed only after the callee postcondition has been established. *)
  Definition pico_callable_methodI
      (R : pico_core_state -> iProp Sigma)
      (contract : PicoSemanticMethodContract)
      (mdef : method_def) : iProp Sigma :=
    let msig := msignature mdef in
    let body := mbody mdef in
    let sGamma := mreceiver msig :: mparams msig in
    □ ∀ callee caller target entry_receiver h sigma V K E Phi,
      ⌜pico_core_typed_env CT sGamma callee h⌝ -∗
      ⌜get_this_var_mapping (vars callee) = Some entry_receiver⌝ -∗
      ⌜pico_core_lr_state CT (mkPicoCoreState h sigma)⌝ -∗
      ⌜psmc_pre contract callee (mkPicoCoreState h sigma)⌝ -∗
      R (mkPicoCoreState h sigma) -∗
      ownP (mkPicoCoreState h sigma) -∗
      ▷ (∀ callee_done final_state V' returned,
        ⌜PicoCallableReturnEvidence CT h entry_receiver mdef
          callee_done final_state returned⌝ -∗
        ⌜psmc_post contract callee
          (mkPicoCoreVal OK callee_done V')⌝ -∗
        R final_state -∗
        ownP final_state -∗
        WP CoreRun
          (set_vars caller (update target returned (vars caller)))
          SSkip V' K @ NotStuck; E {{ Phi }}) -∗
      WP CoreRun callee (mbody_stmt body) V
        (KCall caller target (mreturn body) :: K)
        @ NotStuck; E {{ Phi }}.

  (** Public clients consume the same continuation-aware contract as source
      calls.  The empty-continuation contract above is retained only for
      closed-execution adequacy tests. *)
  Definition pico_exported_methodI
      (R : pico_core_state -> iProp Sigma)
      (contract : PicoSemanticMethodContract)
      (mdef : method_def) : iProp Sigma :=
    pico_callable_methodI R contract mdef.

  Lemma pico_callable_method_exportI R contract mdef :
    pico_callable_methodI R contract mdef -∗
    pico_exported_methodI R contract mdef.
  Proof. iIntros "Hmethod". iExact "Hmethod". Qed.

  Lemma pico_callable_skip_call_wpI
      (R : pico_core_state -> iProp Sigma)
      callee caller target ret V K E Phi state returned
      (Hreturn : runtime_getVal callee ret = Some returned) :
    R state -∗
    ownP state -∗
    ▷ (R state -∗ ownP state -∗
      WP CoreRun
        (set_vars caller (update target returned (vars caller)))
        SSkip V K @ NotStuck; E {{ Phi }}) -∗
    WP CoreRun callee SSkip V (KCall caller target ret :: K)
      @ NotStuck; E {{ Phi }}.
  Proof.
    iIntros "HR Hown Hnext".
    assert (Hstep : pico_core_step CT
      (CoreRun callee SSkip V (KCall caller target ret :: K)) state
      (CoreRun (set_vars caller (update target returned (vars caller)))
        SSkip V K) state).
    { apply PCS_SkipCall. exact Hreturn. }
    assert (Hready : exists next state',
      pico_core_step CT
        (CoreRun callee SSkip V (KCall caller target ret :: K)) state
        next state') by eauto.
    iApply (pico_core_ownP_wp_from_direct_step_contI
      CT E Phi
      (CoreRun callee SSkip V (KCall caller target ret :: K))
      state Hready with "Hown [HR Hnext]").
    iNext. iIntros (next state') "%Hactual Hown".
    inversion Hactual; subst; try discriminate; try congruence.
    replace retval with returned by congruence.
    iApply ("Hnext" with "HR Hown").
  Qed.

  (** Semantic method well-formedness combines the ordinary source-level
      method obligations with the stronger, manually established API
      contract. *)
  Definition pico_semantic_method_wfI
      (R : pico_core_state -> iProp Sigma)
      (C : class_name) (mdef : method_def)
      (contract : PicoSemanticMethodContract) : iProp Sigma :=
    (⌜wf_method CT C mdef⌝ ∗ pico_semantic_methodI R contract mdef)%I.

  Definition pico_callable_method_wfI
      (R : pico_core_state -> iProp Sigma)
      (C : class_name) (mdef : method_def)
      (contract : PicoSemanticMethodContract) : iProp Sigma :=
    (⌜wf_method CT C mdef⌝ ∗ pico_callable_methodI R contract mdef)%I.

  Definition PicoSemanticMethodEnv : Type :=
    class_name -> method_name -> option PicoSemanticMethodContract.

  Definition pico_singleton_semantic_method_env
      (C : class_name) (m : method_name)
      (contract : PicoSemanticMethodContract) : PicoSemanticMethodEnv :=
    fun C' m' =>
      if (Nat.eqb C C' && Nat.eqb m m')%bool
      then Some contract
      else None.

  Lemma pico_singleton_semantic_method_env_lookup :
    forall C m contract C' m',
      pico_singleton_semantic_method_env C m contract C' m' =
        Some contract <->
      C' = C /\ m' = m.
  Proof.
    intros C m contract C' m'.
    unfold pico_singleton_semantic_method_env.
    destruct (Nat.eqb C C') eqn:HC;
      destruct (Nat.eqb m m') eqn:Hm; simpl.
    - apply Nat.eqb_eq in HC. apply Nat.eqb_eq in Hm.
      subst C' m'. split; [intros; auto | intros; reflexivity].
    - split; [discriminate |]. intros [_ ->].
      rewrite Nat.eqb_refl in Hm. discriminate.
    - split; [discriminate |]. intros [-> _].
      rewrite Nat.eqb_refl in HC. discriminate.
    - split; [discriminate |]. intros [-> ->].
      rewrite Nat.eqb_refl in HC. discriminate.
  Qed.

  (** Source effect summary induced by the Iris method environment.  A TS
      call is permitted only when the receiver has a reference type and that
      class/method pair has an installed semantic contract. *)
  Definition pico_ts_call_summary
      (Psi : PicoSemanticMethodEnv) : ts_call_summary :=
    fun sGamma _ receiver method _ =>
      exists T C contract,
        static_getType sGamma receiver = Some T /\
        sbase T = TRef C /\
        Psi C method = Some contract /\
        forall D mdef,
          class_subtype CT D C ->
          FindMethodWithName CT D method mdef ->
          Psi D method = Some contract.

  Lemma pico_ts_call_summary_dynamic_contract :
    forall Psi sGamma target receiver method args T C D mdef,
      pico_ts_call_summary Psi sGamma target receiver method args ->
      static_getType sGamma receiver = Some T ->
      sbase T = TRef C ->
      class_subtype CT D C ->
      FindMethodWithName CT D method mdef ->
      exists contract,
        Psi C method = Some contract /\
        Psi D method = Some contract.
  Proof.
    intros Psi sGamma target receiver method args T C D mdef
      Hsummary Htype Hbase Hsub Hfind.
    destruct Hsummary as (T' & C' & advertised & Htype' & Hbase' &
      Hstatic & Hoverrides).
    assert (T' = T) by congruence. subst T'.
    assert (C' = C) by congruence. subst C'.
    exists advertised. split; [exact Hstatic |].
    eapply Hoverrides; eauto.
  Qed.

  (** A semantic class environment is sound when every advertised contract is
      implemented by the dynamically resolved method body.  Ordinary methods
      need not appear in this environment; they continue to use the ordinary
      PICO LR. *)
  Definition pico_semantic_method_env_wfI
      (R : pico_core_state -> iProp Sigma)
      (Psi : PicoSemanticMethodEnv) : iProp Sigma :=
    □ ∀ C m contract mdef,
      ⌜Psi C m = Some contract⌝ -∗
      ⌜FindMethodWithName CT C m mdef⌝ -∗
      pico_callable_method_wfI R C mdef contract.

  Lemma pico_singleton_semantic_method_env_wfI
      R C m contract mdef
      (Hresolved : FindMethodWithName CT C m mdef) :
    pico_callable_method_wfI R C mdef contract -∗
    pico_semantic_method_env_wfI R
      (pico_singleton_semantic_method_env C m contract).
  Proof.
    iIntros "#Hmethod".
    iModIntro.
    iIntros (C' m' contract' mdef') "%Hspec %Hfind".
    unfold pico_singleton_semantic_method_env in Hspec.
    destruct (Nat.eqb C C') eqn:HC;
      destruct (Nat.eqb m m') eqn:Hm; simpl in Hspec; try discriminate.
    apply Nat.eqb_eq in HC. apply Nat.eqb_eq in Hm.
    subst C' m'. inversion Hspec; subst contract'.
    assert (mdef' = mdef) by
      (eapply find_method_with_name_deterministic; eauto).
    subst mdef'. iExact "Hmethod".
  Qed.

  Lemma pico_semantic_method_env_lookupI R Psi C m contract mdef :
    pico_semantic_method_env_wfI R Psi -∗
    ⌜Psi C m = Some contract⌝ -∗
    ⌜FindMethodWithName CT C m mdef⌝ -∗
    pico_callable_method_wfI R C mdef contract.
  Proof.
    iIntros "#Henv %Hspec %Hfind".
    iApply ("Henv" $! C m contract mdef); iPureIntro; assumption.
  Qed.

  Lemma pico_semantic_method_env_lookup_callableI
      R Psi C m contract mdef :
    pico_semantic_method_env_wfI R Psi -∗
    ⌜Psi C m = Some contract⌝ -∗
    ⌜FindMethodWithName CT C m mdef⌝ -∗
    pico_callable_methodI R contract mdef.
  Proof.
    iIntros "#Henv %Hspec %Hfind".
    iPoseProof (pico_semantic_method_env_lookupI R Psi C m contract mdef
      with "Henv [] []") as "[_ #Hcallable]";
      [iPureIntro; exact Hspec | iPureIntro; exact Hfind |].
    iExact "Hcallable".
  Qed.

  (** Public call boundary for an advertised semantic method.  The ordinary
      resource LR continues to handle unadvertised calls; clients that rely on
      a stronger functional contract resolve it through [Psi] and receive the
      continuation-aware exported specification here. *)
  Lemma pico_semantic_method_env_lookup_exportedI
      R Psi C m contract mdef :
    pico_semantic_method_env_wfI R Psi -∗
    ⌜Psi C m = Some contract⌝ -∗
    ⌜FindMethodWithName CT C m mdef⌝ -∗
    pico_exported_methodI R contract mdef.
  Proof.
    iIntros "#Henv %Hspec %Hfind".
    iApply pico_callable_method_exportI.
    iApply (pico_semantic_method_env_lookup_callableI
      R Psi C m contract mdef with "Henv [] []");
      iPureIntro; assumption.
  Qed.

  (** Semantic-contract-aware source call.  Unlike the lookup lemmas above,
      this rule executes the concrete [SCall] transition, installs its [KCall]
      frame, and invokes the dynamically resolved callable contract. *)
  Lemma pico_semantic_method_env_call_wpI
      R Psi contract mdef
      caller callee x y m args vals loc C body h sigma V K E Phi
      (Hspec : Psi C m = Some contract)
      (Hreceiver : runtime_getVal caller y = Some (Iot loc))
      (Hbase : r_basetype h loc = Some C)
      (Hfind : FindMethodWithName CT C m mdef)
      (Hbody : body = mbody mdef)
      (Hargs : runtime_lookup_list caller args = Some vals)
      (Hcallee : callee = mkr_env (Iot loc :: vals))
      (Hcallee_typed : pico_core_typed_env CT
        (mreceiver (msignature mdef) :: mparams (msignature mdef)) callee h)
      (Hstate : pico_core_lr_state CT (mkPicoCoreState h sigma))
      (Hpre : psmc_pre contract callee (mkPicoCoreState h sigma)) :
    pico_semantic_method_env_wfI R Psi -∗
    R (mkPicoCoreState h sigma) -∗
    ownP (mkPicoCoreState h sigma) -∗
    ▷ (∀ callee_done final_state V' returned,
      ⌜PicoCallableReturnEvidence CT h loc mdef
        callee_done final_state returned⌝ -∗
      ⌜psmc_post contract callee (mkPicoCoreVal OK callee_done V')⌝ -∗
      R final_state -∗
      ownP final_state -∗
      WP CoreRun
        (set_vars caller (update x returned (vars caller)))
        SSkip V' K @ NotStuck; E {{ Phi }}) -∗
    WP CoreRun caller (SCall x y m args) V K
      @ NotStuck; E {{ Phi }}.
  Proof.
    iIntros "#Henv HR Hown Hcontinue".
    assert (Hcall : pico_core_step CT
      (CoreRun caller (SCall x y m args) V K)
      (mkPicoCoreState h sigma)
      (CoreRun callee (mbody_stmt body) V
        (KCall caller x (mreturn body) :: K))
      (mkPicoCoreState h sigma)).
    {
      subst callee.
      eapply PCS_Call with (mdef := mdef) (body := body); eauto.
    }
    assert (Hready : exists next state',
      pico_core_step CT
        (CoreRun caller (SCall x y m args) V K)
        (mkPicoCoreState h sigma) next state') by eauto.
    iApply (pico_core_ownP_wp_from_direct_step_contI
      CT E Phi
      (CoreRun caller (SCall x y m args) V K)
      (mkPicoCoreState h sigma) Hready with "Hown [HR Hcontinue]").
    iNext. iIntros (next state') "%Hactual Hown".
    inversion Hactual; subst; try discriminate; try congruence.
    iPoseProof (pico_semantic_method_env_lookup_callableI
      R Psi C m contract mdef with "Henv [] []") as "#Hmethod".
    { iPureIntro. exact Hspec. }
    { iPureIntro. exact Hfind. }
    iPoseProof
      ("Hmethod" $! (mkr_env (Iot loc :: vals)) caller x loc
        h sigma V K E Phi with "[] [] [] [] HR Hown Hcontinue") as "Hwp".
    - iPureIntro. exact Hcallee_typed.
    - iPureIntro. reflexivity.
    - iPureIntro. exact Hstate.
    - iPureIntro. exact Hpre.
    - assert (loc_y = loc) by congruence. subst loc_y.
      assert (C0 = C) by congruence. subst C0.
      assert (mdef0 = mdef) by
        (eapply find_method_with_name_deterministic; eauto).
      subst mdef0.
      assert (vals0 = vals) by congruence. subst vals0.
      iExact "Hwp".
  Qed.

  (** Combined semantic and typed rule for a successfully resolved source
      call.  The callable implementation supplies normalized return evidence;
      this rule consumes that evidence with PICO's return-transfer theorem and
      exposes a typed caller frame at the continuation boundary. *)
  Lemma pico_semantic_typed_call_wpI
      R Psi sGamma sGamma' mt caller x y m args loc C mdef vals
      h sigma V K E Phi
      (Htyping : stmt_typing CT sGamma mt (SCall x y m args) sGamma')
      (Hsummary : pico_ts_call_summary Psi sGamma x y m args)
      (Henv : pico_core_typed_env CT sGamma caller h)
      (Hreceiver : runtime_getVal caller y = Some (Iot loc))
      (Hbase : r_basetype h loc = Some C)
      (Hfind : FindMethodWithName CT C m mdef)
      (Hargs : runtime_lookup_list caller args = Some vals)
      (Hstate : pico_core_lr_state CT (mkPicoCoreState h sigma))
      (Hpre : forall contract,
        Psi C m = Some contract ->
        psmc_pre contract (mkr_env (Iot loc :: vals))
          (mkPicoCoreState h sigma)) :
    pico_semantic_method_env_wfI R Psi -∗
    R (mkPicoCoreState h sigma) -∗
    ownP (mkPicoCoreState h sigma) -∗
    (▷ ∀ contract callee_done final_state V' returned,
      ⌜Psi C m = Some contract⌝ -∗
      ⌜pico_core_typed_env CT sGamma'
        (set_vars caller (update x returned (vars caller)))
        (pcs_heap final_state)⌝ -∗
      ⌜pico_core_lr_state CT final_state⌝ -∗
      ⌜pico_core_heap_types_extend h (pcs_heap final_state)⌝ -∗
      ⌜psmc_post contract (mkr_env (Iot loc :: vals))
        (mkPicoCoreVal OK callee_done V')⌝ -∗
      R final_state -∗
      ownP final_state -∗
      WP CoreRun
        (set_vars caller (update x returned (vars caller)))
        SSkip V' K @ NotStuck; E {{ Phi }}) -∗
    WP CoreRun caller (SCall x y m args) V K
      @ NotStuck; E {{ Phi }}.
  Proof.
    iIntros "#Hsemantic HR Hown Hcontinue".
    destruct Hsummary as
      (Tstatic & Cstatic & contract & Hget_y & Href & Hspec_static & Hoverrides).
    destruct (pico_core_typed_resolved_method_static
      CT sGamma sGamma' caller h mt x y m args loc C mdef vals
      Htyping Henv Hreceiver Hbase Hfind Hargs) as
      (Ty & Cstatic' & argtypes & mdef_static & declaring_class &
       Hget_y' & Href' & Hget_args & Hfind_static & Hsub & Hsignature & Hwf).
    assert (Tstatic = Ty) by congruence. subst Tstatic.
    assert (Cstatic = Cstatic') by congruence. subst Cstatic'.
    assert (Hspec : Psi C m = Some contract).
    { eapply Hoverrides; eauto. }
    assert (Hcallee_typed : pico_core_typed_env CT
      (mreceiver (msignature mdef) :: mparams (msignature mdef))
      (mkr_env (Iot loc :: vals)) h).
    { eapply pico_core_typed_resolved_method_frame; eauto. }
    iApply (pico_semantic_method_env_call_wpI
      R Psi contract mdef caller (mkr_env (Iot loc :: vals))
      x y m args vals loc C (mbody mdef) h sigma V K E Phi
      Hspec Hreceiver Hbase Hfind eq_refl Hargs eq_refl
      Hcallee_typed Hstate (Hpre contract Hspec)
      with "Hsemantic HR Hown [Hcontinue]").
    iNext.
    iIntros (callee_done final_state V' returned)
      "%Hreturn %Hpost HR Hown".
    destruct Hreturn as
      (body_sGamma' & body_ret_type & Hret_static & Hret_sub &
       Hcallee_typed_done & Hcallee_receiver & Hextend & Hstate_final &
       Hreturned).
    assert (Hcaller_typed : pico_core_typed_env CT sGamma'
      (set_vars caller (update x returned (vars caller)))
      (pcs_heap final_state)).
    {
      eapply pico_core_typed_resolved_method_return; eauto.
    }
    iApply ("Hcontinue" $! contract callee_done final_state V' returned
      with "[] [] [] [] [] HR Hown"); iPureIntro; assumption.
  Qed.

  (** A contract can be installed in a semantic environment only after its
      implementation proof has been established.  This is the module/class
      boundary consumed by clients. *)
  Lemma pico_callable_method_wf_introI R C mdef contract
      (Hwf : wf_method CT C mdef) :
    pico_callable_methodI R contract mdef -∗
    pico_callable_method_wfI R C mdef contract.
  Proof.
    iIntros "Hmethod".
    iSplit; [iPureIntro; exact Hwf | iExact "Hmethod"].
  Qed.

  (** A TS annotation is a checked source effect, while [contract] remains an
      Iris pre/postcondition.  This package deliberately does not add a result
      specification to PICO syntax. *)
  Definition pico_ts_semantic_method_wfI
      (R : pico_core_state -> iProp Sigma)
      (Psi : PicoSemanticMethodEnv)
      (C : class_name) (mdef : method_def)
      (contract : PicoSemanticMethodContract) : iProp Sigma :=
    let msig := msignature mdef in
    let body := mbody mdef in
    let sGamma := mreceiver msig :: mparams msig in
    (∃ sGamma',
      ⌜ts_stmt CT (pico_ts_call_summary Psi)
        sGamma (mbody_stmt body) sGamma'⌝ ∗
      pico_callable_method_wfI R C mdef contract)%I.

  Lemma pico_ts_semantic_method_wf_introI
      R Psi C mdef contract sGamma'
      (Hwf : wf_method CT C mdef)
      (Hts : ts_stmt CT (pico_ts_call_summary Psi)
        (mreceiver (msignature mdef) :: mparams (msignature mdef))
        (mbody_stmt (mbody mdef)) sGamma') :
    pico_callable_methodI R contract mdef -∗
    pico_ts_semantic_method_wfI R Psi C mdef contract.
  Proof.
    iIntros "Hmethod".
    unfold pico_ts_semantic_method_wfI.
    iExists sGamma'. iSplit; [iPureIntro; exact Hts |].
    iSplit; [iPureIntro; exact Hwf | iExact "Hmethod"].
  Qed.

  (** A verified read-only derived computation is continuation-aware: it may
      advance the thread view while reading stable state, but it leaves the
      heap/history state unchanged, changes only [target], and resumes the
      caller's CESK continuation from [SSkip].  This is the reusable boundary
      between immutable-state computation and cache-control reasoning. *)
  Definition pico_derived_computationI
      (R : pico_core_state -> iProp Sigma)
      (compute : stmt) (target : var) (derived : value) : iProp Sigma :=
    □ ∀ rGamma state V K E Phi old,
      ⌜runtime_getVal rGamma target = Some old⌝ -∗
      R state -∗
      ownP state -∗
      ▷ (∀ V',
        R state -∗
        ownP state -∗
        WP CoreRun
          (set_vars rGamma (update target derived (vars rGamma)))
          SSkip V' K @ NotStuck; E {{ Phi }}) -∗
      WP CoreRun rGamma compute V K @ NotStuck; E {{ Phi }}.

  (** Source TS effect plus Iris functional specification for a derived
      computation.  TS excludes cache reads/shared writes; the Iris component
      proves the actual derived result. *)
  Definition pico_ts_derived_computationI
      (R : pico_core_state -> iProp Sigma)
      (CallOK : ts_call_summary)
      (sGamma sGamma' : s_env) (compute : stmt)
      (target : var) (derived : value) : iProp Sigma :=
    (⌜ts_stmt CT CallOK sGamma compute sGamma'⌝ ∗
      pico_derived_computationI R compute target derived)%I.

  Lemma pico_ts_derived_computation_elimI
      R CallOK sGamma sGamma' compute target derived :
    pico_ts_derived_computationI
      R CallOK sGamma sGamma' compute target derived -∗
    pico_derived_computationI R compute target derived.
  Proof. iIntros "[_ Hcompute]". iExact "Hcompute". Qed.

  Lemma pico_ts_derived_computation_direct_write_freeI
      R CallOK sGamma sGamma' compute target derived :
    pico_ts_derived_computationI
      R CallOK sGamma sGamma' compute target derived -∗
    ⌜direct_shared_write_free compute⌝.
  Proof.
    iIntros "[%Hts _]". iPureIntro.
    eapply ts_stmt_direct_shared_write_free. exact Hts.
  Qed.
End pico_semantic_api.

(** Pure result contract used by derived-cache APIs.  [decode_args] and
    [decode_result] keep this boundary independent of a particular cache value
    representation.  A concrete method may establish this contract directly
    by WP or through a separately proved execution-to-trace refinement. *)
Definition pico_pure_result_method_contract
    {Args Result : Type}
    (decode_args : r_env -> option Args)
    (decode_result : value -> option Result)
    (return_var : var)
    (F : Args -> Result) : PicoSemanticMethodContract :=
  {| psmc_pre := fun entry _ => exists args, decode_args entry = Some args;
     psmc_post := fun entry result =>
       pcv_result result = OK /\
       exists args returned,
         decode_args entry = Some args /\
         runtime_getVal (pcv_env result) return_var = Some returned /\
         decode_result returned = Some (F args) |}.
