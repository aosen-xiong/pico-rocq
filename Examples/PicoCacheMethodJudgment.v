From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping Bigstep Properties Reachability.
Require Import Core.GenericCacheProtocol Core.GenericDerivedCache.
Require Import Examples.PicoIfZeroCache Examples.PicoHashMethod
  Examples.PicoConcreteHashProvider.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoCacheTyping PICOBridge.PicoDerivationCache
  PICOBridge.PicoCoreLanguage PICOBridge.PicoCoreSemImm
  PICOBridge.PicoDerivationNoninterference PICOBridge.PicoDerivationSmallStep
  PICOBridge.PicoDerivationPrefix PICOBridge.PicoCoreTraceRobust.

(** * The Cache-Method Judgment over PICO Statements

    A cache method reads the cache field once into a local, returns it on a
    hit, and on a miss runs an initializer, writes its result to the cache
    field and returns it.  The initializer is derivation code: it reads only
    abstract state.  Its value is the one the protocol is defined by, namely
    what it evaluates to sequentially in the reference heap.

    This file proves that a call to such a method is trace robust on the core
    machine for the derivation-defined provider, for every class table,
    receiver, value and initializer.  No analysis of the particular method is
    needed beyond the judgment. *)

Section cache_method_judgment.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table) (D : method_def -> Prop).
  Context (receiver : Loc) (m : method_name) (h0 : heap) (H : nat).
  Context (compute : stmt) (mc : method_name) (mdef : method_def).
  Context (Trecv : qualified_type) (sGamma' : s_env) (mt : method_scope).
  Context (rt0 : runtime_type) (fs0 : fields_mapping).
  Context (caller : r_env) (x y : var).

  Let footprint := reachable_abs CT h0 receiver.
  Let rho1 := mkr_env [Iot receiver].
  Let rho2 := mkr_env [Iot receiver; Int 0].
  Definition env_tmp (v : value) : r_env := mkr_env [Iot receiver; v; Int 0].
  Let rho3 := env_tmp (Int 0).
  Let rho_done := mkr_env [Iot receiver; Int H; Int H].
  Let sGamma3 : s_env := [Trecv; int_type; int_type].

  (** ** The judgment *)

  (** The method has the local-copy shape with initializer [compute]. *)
  Hypothesis Hbody :
    mbody_stmt (mbody mdef) = pico_hash_method_stmt_with compute.
  Hypothesis Hret : mreturn (mbody mdef) = cache_result.

  (** The initializer is derivation code, typed in the method's frame. *)
  Hypothesis Htable : derivation_table CT D.
  Hypothesis Hderiv : deriv_stmt CT D sGamma3 compute sGamma'.
  Hypothesis Htyped : stmt_typing CT sGamma3 mt compute sGamma'.
  Hypothesis Hwf3 : wf_r_config CT sGamma3 rho3 h0.

  (** Evaluated sequentially in the reference heap, the initializer leaves
      the protocol's value in the local. *)
  Hypothesis Hcompute :
    forall rGamma1,
      eval_stmt CT rho3 h0 compute OK rGamma1 h0 ->
      runtime_getVal rGamma1 cache_tmp = Some (Int H).

  (** The receiver's class declares the cache field and resolves the call to
      this method; the caller holds the receiver and has a result slot. *)
  Hypothesis Hobj0 : runtime_getObj h0 receiver = Some (mkObj rt0 fs0).
  Hypothesis Hcachefield :
    derived_cache_field CT (rctype rt0) hash_cache_field.
  Hypothesis Hfind : FindMethodWithName CT (rctype rt0) mc mdef.
  Hypothesis Hy : runtime_getVal caller y = Some (Iot receiver).
  Hypothesis Hx : x < dom (vars caller).

  Notation hash_machine := (pico_concrete_hash_semimm CT receiver m h0 H).
  Notation hash_inv :=
    (machine_inv hash_cache_protocol pico_hash_stable_abs H
       (pico_hash_cache_adapter receiver) hash_machine).
  Notation hash_run :=
    (thread_run CT hash_cache_protocol pico_hash_stable_abs H
       (pico_hash_cache_adapter receiver) hash_machine).

  (** The result contract of the call: if it returns normally, the caller's
      result slot holds the protocol's value. *)
  Definition cache_call_result_ok (r : pico_core_val) : Prop :=
    pcv_result r = OK ->
    runtime_getVal (pcv_env r) x = Some (Int H).

  Let read_stmt : stmt := SVarAss cache_tmp (EField cache_receiver hash_cache_field).
  Let write_stmt : stmt := SFldWrite cache_receiver hash_cache_field cache_tmp.
  Let final_stmt : stmt := SVarAss cache_result (EVar cache_tmp).
  Let branch : stmt := pico_local_copy_cache_branch compute.
  Let core : stmt := pico_local_copy_cache_stmt compute.
  Let Kc : pico_core_cont := [KCall caller x cache_result].
  Let caller_done : r_env := set_vars caller (update x (Int H) (vars caller)).

  Definition valid_read (v : value) : Prop :=
    v = Int 0 \/ (v = Int H /\ H <> 0).

  (** ** Basic facts *)

  Lemma receiver_in_footprint : footprint receiver.
  Proof.
    apply reachable_abs_heap. eapply runtime_getObj_dom. exact Hobj0.
  Qed.

  Lemma footprint_dom :
    forall l, footprint l ->
      exists rt fs, runtime_getObj h0 l = Some (mkObj rt fs).
  Proof.
    intros l Hl.
    have Hdom := reachable_abs_target_dom CT h0 receiver l Hl.
    unfold runtime_getObj.
    destruct (nth_error h0 l) as [[rt fs] |] eqn:Hnth.
    - eauto.
    - apply nth_error_None in Hnth. lia.
  Qed.

  Lemma rho3_in_footprint : env_in footprint rho3.
  Proof.
    intros z l Hz.
    destruct z as [| [| [| z]]]; simpl in Hz; try discriminate.
    - injection Hz as <-. exact receiver_in_footprint.
    - destruct z; discriminate.
  Qed.

  Lemma hash_inv_footprint_state :
    forall S, hash_inv S -> footprint_state CT footprint h0 S.
  Proof.
    intros S [Hprov _].
    split.
    - destruct Hprov as (_ & (_ & _ & Habs & _) & _). exact Habs.
    - exact (pico_hash_provider_footprint_stable CT receiver m h0 H S Hprov).
  Qed.

  Lemma hash_inv_receiver_class :
    forall S, hash_inv S ->
      r_basetype (pcs_heap S) receiver = Some (rctype rt0).
  Proof.
    intros S Hinv.
    destruct (hash_inv_footprint_state S Hinv) as [Hagree _].
    rewrite (abs_agree_basetype CT footprint h0 (pcs_heap S) receiver Hagree
      receiver_in_footprint).
    unfold r_basetype. rewrite Hobj0. reflexivity.
  Qed.

  Lemma update_hit :
    forall (l : list value) i v, i < length l -> nth_error (update i v l) i = Some v.
  Proof. intros l i v Hi. apply update_same. exact Hi. Qed.

  (** ** After the initializer

      Once the initializer has finished with environment [rGamma1], the rest
      of the call is a fixed chain of controls. *)
  Inductive tail_chain (rGamma1 : r_env) : pico_core_expr -> Prop :=
    | Chain_Exit : forall V,
        tail_chain rGamma1
          (CoreRun rGamma1 SSkip V (KSeq write_stmt :: KSeq final_stmt :: Kc))
    | Chain_Write : forall V,
        tail_chain rGamma1 (CoreRun rGamma1 write_stmt V (KSeq final_stmt :: Kc))
    | Chain_AfterWrite : forall V,
        tail_chain rGamma1 (CoreRun rGamma1 SSkip V (KSeq final_stmt :: Kc))
    | Chain_Final : forall V,
        tail_chain rGamma1 (CoreRun rGamma1 final_stmt V Kc)
    | Chain_AfterFinal : forall V rGamma2,
        runtime_getVal rGamma2 cache_result = Some (Int H) ->
        tail_chain rGamma1 (CoreRun rGamma2 SSkip V Kc)
    | Chain_Resume : forall V,
        tail_chain rGamma1 (CoreRun caller_done SSkip V [])
    | Chain_Done : forall V,
        tail_chain rGamma1 (CoreDone OK caller_done V)
    | Chain_Failed : forall r rGamma V,
        r <> OK ->
        tail_chain rGamma1 (CoreDone r rGamma V).

  Lemma tail_chain_step :
    forall rGamma1 c S c' S',
      runtime_getVal rGamma1 cache_tmp = Some (Int H) ->
      tail_chain rGamma1 c ->
      pico_core_step CT c S c' S' ->
      tail_chain rGamma1 c'.
  Proof.
    intros rGamma1 c S c' S' Htmp Hchain Hstep.
    destruct Hchain.
    - inversion Hstep; subst. apply Chain_Write.
    - inversion Hstep; subst.
      + apply Chain_AfterWrite.
      + apply Chain_Failed. discriminate.
      + apply Chain_Failed. discriminate.
    - inversion Hstep; subst. apply Chain_Final.
    - inversion Hstep; subst.
      match goal with
      | Hval : runtime_getVal rGamma1 cache_tmp = Some ?val |- _ =>
          rewrite Htmp in Hval; injection Hval as <-
      end.
      apply Chain_AfterFinal.
      unfold runtime_getVal, set_vars. cbn [vars].
      apply update_hit.
      match goal with
      | Hold : runtime_getVal rGamma1 cache_result = Some _ |- _ =>
          apply nth_error_Some; unfold runtime_getVal in Hold; congruence
      end.
    - inversion Hstep; subst.
      match goal with
      | Hval : runtime_getVal rGamma2 cache_result = Some ?val,
        Hret' : runtime_getVal rGamma2 cache_result = Some ?retval |- _ =>
          rewrite Hval in Hret'; injection Hret' as <-
      end.
      apply Chain_Resume.
    - inversion Hstep; subst. apply Chain_Done.
    - inversion Hstep.
    - inversion Hstep.
  Qed.

  Lemma tail_chain_steps :
    forall rGamma1 k c e,
      runtime_getVal rGamma1 cache_tmp = Some (Int H) ->
      footprint_steps CT footprint h0 k c e ->
      tail_chain rGamma1 c ->
      tail_chain rGamma1 e.
  Proof.
    intros rGamma1 k c e Htmp Hsteps.
    induction Hsteps; intros Hchain.
    - exact Hchain.
    - apply IHHsteps. eapply tail_chain_step; eassumption.
  Qed.

  Let Kw : pico_core_cont := KSeq write_stmt :: KSeq final_stmt :: Kc.
  Let body : stmt :=
    SSeq (SLocal int_type cache_tmp) (SSeq (SLocal int_type cache_result) core).

  (** A run of the initializer under interference is still running
      derivation code, has failed, or has finished with the protocol's value
      in the local and continues along the chain. *)
  Lemma tail_classify :
    forall n V e,
      footprint_steps CT footprint h0 n (CoreRun rho3 compute V Kw) e ->
      deriv_running CT footprint h0 e \/
      deriv_failed e \/
      exists rGamma1,
        runtime_getVal rGamma1 cache_tmp = Some (Int H) /\
        runtime_getVal rGamma1 cache_receiver = Some (Iot receiver) /\
        tail_chain rGamma1 e.
  Proof.
    intros n V e Hsteps.
    destruct (deriv_prefix CT D footprint h0 Htable footprint_dom n n rho3
      compute V Kw sGamma3 sGamma' mt e (le_n n) Hsteps Hderiv Htyped Hwf3
      rho3_in_footprint)
      as [Hrun | [(rGamma1 & V1 & k & _ & Heval & _ & Htail) | Hfail]].
    - left. exact Hrun.
    - right. right. exists rGamma1.
      have Htmp := Hcompute rGamma1 Heval.
      split; [exact Htmp |]. split.
      + have Hthis := eval_stmt_preserves_receiver_addr_typed CT sGamma3 mt
          rho3 h0 compute sGamma' rGamma1 h0 receiver Htyped Heval eq_refl.
        unfold get_this_var_mapping in Hthis.
        unfold runtime_getVal, cache_receiver.
        destruct (vars rGamma1) as [| [| l | k0] rest]; try discriminate.
        injection Hthis as ->. reflexivity.
      + eapply tail_chain_steps; [exact Htmp | exact Htail | apply Chain_Exit].
    - right. left. exact Hfail.
  Qed.

  (** ** The phases of a call *)
  Inductive call_phase : pico_core_expr -> Prop :=
    | Ph_Call : forall V,
        call_phase (CoreRun caller (SCall x mc y []) V [])
    | Ph_Body : forall V,
        call_phase (CoreRun rho1 body V Kc)
    | Ph_LocalTmp : forall V,
        call_phase (CoreRun rho1 (SLocal int_type cache_tmp) V
          (KSeq (SSeq (SLocal int_type cache_result) core) :: Kc))
    | Ph_AfterLocalTmp : forall V,
        call_phase (CoreRun rho2 SSkip V
          (KSeq (SSeq (SLocal int_type cache_result) core) :: Kc))
    | Ph_ResultSeq : forall V,
        call_phase (CoreRun rho2 (SSeq (SLocal int_type cache_result) core) V Kc)
    | Ph_LocalResult : forall V,
        call_phase (CoreRun rho2 (SLocal int_type cache_result) V
          (KSeq core :: Kc))
    | Ph_AfterLocalResult : forall V,
        call_phase (CoreRun rho3 SSkip V (KSeq core :: Kc))
    | Ph_Core : forall V,
        call_phase (CoreRun rho3 core V Kc)
    | Ph_Read : forall V,
        call_phase (CoreRun rho3 read_stmt V
          (KSeq (SSeq branch final_stmt) :: Kc))
    | Ph_AfterRead : forall V v,
        valid_read v ->
        call_phase (CoreRun (env_tmp v) SSkip V
          (KSeq (SSeq branch final_stmt) :: Kc))
    | Ph_BranchSeq : forall V v,
        valid_read v ->
        call_phase (CoreRun (env_tmp v) (SSeq branch final_stmt) V Kc)
    | Ph_Branch : forall V v,
        valid_read v ->
        call_phase (CoreRun (env_tmp v) branch V (KSeq final_stmt :: Kc))
    | Ph_Miss : forall V,
        call_phase (CoreRun rho3 (SSeq compute write_stmt) V
          (KSeq final_stmt :: Kc))
    | Ph_Tail : forall n V e,
        footprint_steps CT footprint h0 n (CoreRun rho3 compute V Kw) e ->
        call_phase e
    | Ph_HitSkip : forall V,
        call_phase (CoreRun (env_tmp (Int H)) SSkip V (KSeq final_stmt :: Kc))
    | Ph_Final : forall V,
        call_phase (CoreRun (env_tmp (Int H)) final_stmt V Kc)
    | Ph_AfterFinal : forall V,
        call_phase (CoreRun rho_done SSkip V Kc)
    | Ph_Resume : forall V,
        call_phase (CoreRun caller_done SSkip V [])
    | Ph_Done : forall V,
        call_phase (CoreDone OK caller_done V).

  Lemma read_is_cache_read :
    forall V K,
      cache_read_control hash_cache_protocol (pico_hash_cache_adapter receiver)
        (CoreRun rho3 read_stmt V K).
  Proof.
    intros V K.
    exists rho3; exists cache_tmp; exists cache_receiver;
      exists hash_cache_field; exists V; exists K; exists receiver;
      exists HashField.
    split; [reflexivity |]. split; [reflexivity |].
    apply pico_concrete_hash_adapter_at.
  Qed.

  Lemma call_phase_step :
    forall e S e' S',
      call_phase e ->
      ~ cache_read_control hash_cache_protocol
          (pico_hash_cache_adapter receiver) e ->
      hash_inv S ->
      pico_core_step CT e S e' S' ->
      call_phase e'.
  Proof.
    intros e S e' S' Hphase Hnoread Hinv Hstep.
    destruct Hphase.
    - (* call *)
      inversion Hstep; subst.
      + match goal with
        | Hyl : runtime_getVal caller y = Some (Iot ?l),
          Hb : r_basetype _ ?l = Some ?C,
          Hf : FindMethodWithName CT ?C mc ?md,
          Ha : runtime_lookup_list caller [] = Some ?vs |- _ =>
            rewrite Hy in Hyl; injection Hyl as <-;
            have Hcls := hash_inv_receiver_class _ Hinv;
            simpl in Hcls; rewrite Hcls in Hb; injection Hb as <-;
            have Hmd := find_method_with_name_deterministic CT _ _ _ _ Hf Hfind;
            subst md; simpl in Ha; injection Ha as <-
        end.
        rewrite Hbody Hret. apply Ph_Body.
      + congruence.
    - inversion Hstep; subst. apply Ph_LocalTmp.
    - inversion Hstep; subst. apply Ph_AfterLocalTmp.
    - inversion Hstep; subst. apply Ph_ResultSeq.
    - inversion Hstep; subst. apply Ph_LocalResult.
    - inversion Hstep; subst. apply Ph_AfterLocalResult.
    - inversion Hstep; subst. apply Ph_Core.
    - inversion Hstep; subst. apply Ph_Read.
    - exfalso. apply Hnoread. apply read_is_cache_read.
    - inversion Hstep; subst. apply Ph_BranchSeq. assumption.
    - inversion Hstep; subst. apply Ph_Branch. assumption.
    - (* branch on the value read *)
      match goal with Hv : valid_read _ |- _ => rename Hv into Hvalid end.
      inversion Hstep; subst.
      + match goal with
        | Hz : runtime_getVal (env_tmp _) cache_tmp = Some (Int 0) |- _ =>
            simpl in Hz; injection Hz as ->
        end.
        apply Ph_Miss.
      + match goal with
        | Hz : runtime_getVal (env_tmp _) cache_tmp = Some (Int (Datatypes.S ?k)) |- _ =>
            simpl in Hz; injection Hz as ->
        end.
        destruct Hvalid as [Hzero | [Hhash _]]; [discriminate |].
        rewrite Hhash. apply Ph_HitSkip.
      + match goal with
        | Hz : runtime_getVal (env_tmp _) cache_tmp = Some Null_a |- _ =>
            simpl in Hz; injection Hz as ->
        end.
        destruct Hvalid as [Hzero | [Hhash _]]; discriminate.
    - inversion Hstep; subst.
      eapply Ph_Tail with (n := 0). constructor.
    - eapply Ph_Tail.
      eapply footprint_steps_snoc;
        [eassumption | apply hash_inv_footprint_state; exact Hinv | exact Hstep].
    - inversion Hstep; subst. apply Ph_Final.
    - inversion Hstep; subst.
      match goal with
      | Hval : runtime_getVal (env_tmp (Int H)) cache_tmp = Some _ |- _ =>
          simpl in Hval; injection Hval as <-
      end.
      apply Ph_AfterFinal.
    - inversion Hstep; subst.
      match goal with
      | Hval : runtime_getVal rho_done cache_result = Some _ |- _ =>
          simpl in Hval; injection Hval as <-
      end.
      apply Ph_Resume.
    - inversion Hstep; subst. apply Ph_Done.
    - inversion Hstep.
  Qed.

  Lemma tail_not_cache_read :
    forall n V0 rGamma x' y' V K,
      footprint_steps CT footprint h0 n (CoreRun rho3 compute V0 Kw)
        (CoreRun rGamma (SVarAss x' (EField y' hash_cache_field)) V K) ->
      runtime_getVal rGamma y' = Some (Iot receiver) ->
      False.
  Proof.
    intros n V0 rGamma x' y' V K Hsteps Hrecv.
    destruct (tail_classify n V0 _ Hsteps)
      as [Hrunning | [Hfailed | (rGamma1 & _ & _ & Hchain)]].
    - destruct Hrunning as (rG & s & V1 & K1 & Heq & _ & Hread).
      injection Heq as <- <- <- <-.
      destruct (Hread x' y' hash_cache_field receiver eq_refl Hrecv)
        as (_ & rt & fs & Hobj & Habs).
      rewrite Hobj0 in Hobj. injection Hobj as <- <-.
      exact (derived_cache_field_not_abstract CT _ _ Hcachefield Habs).
    - destruct Hfailed as (r & rG & V1 & Heq & _). discriminate.
    - inversion Hchain.
  Qed.

  Lemma call_run_phase :
    forall V0 tr e,
      hash_run (CoreRun caller (SCall x mc y []) V0 []) tr e ->
      ValidTrace hash_cache_protocol H tr ->
      call_phase e.
  Proof.
    intros V0 tr e Hrun.
    induction Hrun as
      [| tr rGamma x' y' f V V' K old loc k v cv sigma Hrun IH Hxo Hyo Hread
           Hfield Hvalue
       | tr e S e' S' Hrun IH Hnoread Hinv Hstep];
      intros Hvalid.
    - apply Ph_Call.
    - apply Forall_app in Hvalid. destruct Hvalid as [Hvalid Hobs].
      have Hphase := IH Hvalid.
      destruct (pico_hash_cache_adapter_some _ _ _ Hfield) as [Haddr ->].
      injection Haddr as -> ->.
      simpl in Hvalue. injection Hvalue as <-.
      inversion Hobs as [| ? ? Hcv _]; subst.
      unfold ValidObs in Hcv. simpl in Hcv. unfold hash_cache_valid in Hcv.
      inversion Hphase; subst.
      + exact (Ph_AfterRead V' v Hcv).
      + exfalso. eapply tail_not_cache_read; eassumption.
    - exact (call_phase_step e S e' S' (IH Hvalid) Hnoread Hinv Hstep).
  Qed.

  (** ** Soundness of the judgment *)
  Theorem cache_method_call_trace_robust :
    forall V0,
      machine_cache_safe CT hash_cache_protocol pico_hash_stable_abs H
        (pico_hash_cache_adapter receiver) hash_machine
        cache_call_result_ok
        (CoreRun caller (SCall x mc y []) V0 []).
  Proof.
    intros V0 tr e Hrun Hvalid.
    have Hphase := call_run_phase V0 tr e Hrun Hvalid.
    assert (Hdone : forall V,
      cache_call_result_ok (mkPicoCoreVal OK caller_done V)).
    { intros V _. simpl. unfold caller_done, runtime_getVal, set_vars.
      cbn [vars]. apply update_hit. exact Hx. }
    split.
    - intros rGamma x' f y' V K loc v -> Hx' Hy'.
      inversion Hphase; subst.
      match goal with
      | Hsteps : footprint_steps _ _ _ _ _ _ |- _ =>
          destruct (tail_classify _ _ _ Hsteps)
            as [Hrunning | [Hfailed | (rGamma1 & Htmp & Hthis & Hchain)]]
      end.
      + destruct Hrunning as (rG & s & Vr & Kr & Heq & Hnowrite & _).
        injection Heq as <- <- <- <-.
        exfalso. eapply Hnowrite. reflexivity.
      + destruct Hfailed as (rf & rG & Vr & Heq & _). discriminate.
      + inversion Hchain; subst.
        rewrite Hthis in Hx'. injection Hx' as <-.
        rewrite Htmp in Hy'. injection Hy' as <-.
        right. exists HashField, (Int H).
        split; [apply pico_concrete_hash_adapter_at |].
        split; [reflexivity |].
        simpl. unfold hash_cache_valid.
        destruct (Nat.eq_dec H 0) as [Hz | Hnz].
        * left. rewrite Hz. reflexivity.
        * right. split; [reflexivity | exact Hnz].
    - intros r rGamma V ->.
      inversion Hphase; subst.
      + match goal with
        | Hsteps : footprint_steps _ _ _ _ _ _ |- _ =>
            destruct (tail_classify _ _ _ Hsteps)
              as [Hrunning | [Hfailed | (rGamma1 & _ & _ & Hchain)]]
        end.
        * destruct Hrunning as (rG & s & Vr & Kr & Heq & _). discriminate.
        * destruct Hfailed as (r' & rG & Vr & Heq & Hr).
          injection Heq as <- <- <-.
          intros Hok. simpl in Hok. contradiction.
        * inversion Hchain; subst.
          -- apply Hdone.
          -- intros Hok. simpl in Hok. contradiction.
      + apply Hdone.
  Qed.
End cache_method_judgment.

(** ** The initializer that calls the derivation method

    When the miss branch calls the derivation method that defines the
    protocol, the judgment has no semantic premise about the initializer:
    the protocol's value is, by definition, what that method returns on the
    receiver in the reference heap. *)
Section derivation_call_initializer.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table) (D : method_def -> Prop).
  Context (receiver : Loc) (m : method_name) (h0 : heap) (H : nat).
  Context (mc : method_name) (mdef : method_def).
  Context (Trecv : qualified_type) (sGamma' : s_env) (mt : method_scope).
  Context (rt0 : runtime_type) (fs0 : fields_mapping).
  Context (caller : r_env) (x y : var).

  Let compute : stmt := SCall cache_tmp m cache_receiver [].

  Lemma derivation_call_value :
    derived_by CT m h0 receiver (Int H) ->
    forall rGamma1,
      eval_stmt CT (env_tmp receiver (Int 0)) h0 compute OK rGamma1 h0 ->
      runtime_getVal rGamma1 cache_tmp = Some (Int H).
  Proof.
    intros (cy0 & mdef0 & rG0 & Hbase0 & Hfind0 & Heval0 & Hret0)
      rGamma1 Heval.
    unfold compute in Heval. inversion Heval; subst.
    match goal with
    | Hv : runtime_getVal (env_tmp receiver (Int 0)) cache_receiver =
             Some (Iot ?l) |- _ =>
        cbv in Hv; injection Hv as <-
    end.
    match goal with
    | Hb : r_basetype h0 receiver = Some ?c,
      Hf : FindMethodWithName CT ?c m ?md /\ _,
      Ha : runtime_lookup_list _ [] = Some ?vs,
      Hbody : eval_stmt CT _ h0 _ OK ?rG h0,
      Hr : runtime_getVal ?rG _ = Some ?rv |- _ =>
        rewrite Hbase0 in Hb; injection Hb as <-;
        destruct Hf as [Hf ->];
        have Hmd := find_method_with_name_deterministic CT _ _ _ _ Hf Hfind0;
        subst md; simpl in Ha; injection Ha as <-;
        destruct (eval_stmt_deterministic _ _ _ _ _ _ _ _ _ _ Hbody Heval0)
          as (_ & HrG & _);
        subst rG; rewrite Hret0 in Hr; injection Hr as <-
    end.
    reflexivity.
  Qed.

  Theorem derivation_call_cache_method_trace_robust :
    mbody_stmt (mbody mdef) = pico_hash_method_stmt_with compute ->
    mreturn (mbody mdef) = cache_result ->
    derivation_table CT D ->
    deriv_stmt CT D [Trecv; int_type; int_type] compute sGamma' ->
    stmt_typing CT [Trecv; int_type; int_type] mt compute sGamma' ->
    wf_r_config CT [Trecv; int_type; int_type] (env_tmp receiver (Int 0)) h0 ->
    derived_by CT m h0 receiver (Int H) ->
    runtime_getObj h0 receiver = Some (mkObj rt0 fs0) ->
    derived_cache_field CT (rctype rt0) hash_cache_field ->
    FindMethodWithName CT (rctype rt0) mc mdef ->
    runtime_getVal caller y = Some (Iot receiver) ->
    x < dom (vars caller) ->
    forall V0,
      machine_cache_safe CT hash_cache_protocol pico_hash_stable_abs H
        (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver m h0 H)
        (cache_call_result_ok H x)
        (CoreRun caller (SCall x mc y []) V0 []).
  Proof.
    intros Hbody Hret Htable Hderiv Htyped Hwf3 Hderived Hobj0 Hcachefield
      Hfind Hy Hx V0.
    eapply (cache_method_call_trace_robust CT D receiver m h0 H compute mc
      mdef Trecv sGamma' mt rt0 fs0 caller x y); eauto.
    exact (derivation_call_value Hderived).
  Qed.
End derivation_call_initializer.
