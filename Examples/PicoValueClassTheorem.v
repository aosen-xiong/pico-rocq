From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping Bigstep Properties Reachability.
Require Import Core.GenericCacheProtocol Core.GenericDerivedCache.
Require Import Examples.PicoIfZeroCache Examples.PicoHashMethod
  Examples.PicoConcreteHashProvider Examples.PicoCacheMethodJudgment
  Examples.PicoValueClasses.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoCacheTyping
  PICOBridge.PicoCoreLanguage PICOBridge.PicoCoreSemImm
  PICOBridge.PicoDerivationNoninterference PICOBridge.PicoDerivationSmallStep
  PICOBridge.PicoDerivationCache PICOBridge.PicoDerivationPrefix
  PICOBridge.PicoSemanticConcurrency PICOBridge.PicoCoreTraceRobust.

(** * Semantic Value Classes: the Class-Level Theorem

    A PICO class is a semantic value class when its state is complete, every
    field being abstract state or a declared derived field, transitively, and
    every one of its methods is either a cache method for the derived field
    or a derivation method.

    For an object of such a class, any number of threads may call any of its
    methods: the object stays semantically immutable, and every call that
    returns normally returns a value determined by the reference heap, that
    is, by the object's abstract state. *)

(** ** Calls to derivation methods *)

Section derivation_call.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table) (D : method_def -> Prop).
  Context (receiver : Loc) (m : method_name) (h0 : heap) (H : nat).
  Context (mn : method_name) (md : method_def).
  Context (sGammab' : s_env) (mtb : method_scope).
  Context (rt0 : runtime_type) (fs0 : fields_mapping).
  Context (caller : r_env) (x y : var).

  Let footprint := reachable_abs CT h0 receiver.
  Let rhob := mkr_env [Iot receiver].
  Let body := mbody_stmt (mbody md).
  Let ret := mreturn (mbody md).
  Let Kb : pico_core_cont := [KCall caller x ret].

  Hypothesis Htable : derivation_table CT D.
  Hypothesis Hderivb :
    deriv_stmt CT D [mreceiver (msignature md)] body sGammab'.
  Hypothesis Htypedb :
    stmt_typing CT [mreceiver (msignature md)] mtb body sGammab'.
  Hypothesis Hwfb :
    wf_r_config CT [mreceiver (msignature md)] rhob h0.
  Hypothesis Hobj0 : runtime_getObj h0 receiver = Some (mkObj rt0 fs0).
  Hypothesis Hcachefield :
    derived_cache_field CT (rctype rt0) hash_cache_field.
  Hypothesis Hfind : FindMethodWithName CT (rctype rt0) mn md.
  Hypothesis Hy : runtime_getVal caller y = Some (Iot receiver).

  Notation hash_machine := (pico_concrete_hash_semimm CT receiver m h0 H).
  Notation hash_inv :=
    (machine_inv hash_cache_protocol pico_hash_stable_abs H
       (pico_hash_cache_adapter receiver) hash_machine).
  Notation hash_run :=
    (thread_run CT hash_cache_protocol pico_hash_stable_abs H
       (pico_hash_cache_adapter receiver) hash_machine).

  (** The value the method denotes: what its body evaluates to on the
      receiver, sequentially, in the reference heap. *)
  Definition method_denotes (v : value) : Prop :=
    exists rGamma1,
      eval_stmt CT rhob h0 body OK rGamma1 h0 /\
      runtime_getVal rGamma1 ret = Some v.

  (** If the call returns normally, the caller's result slot holds the value
      the method denotes. *)
  Definition deriv_call_result_ok (r : pico_core_val) : Prop :=
    pcv_result r = OK ->
    exists v, method_denotes v /\ runtime_getVal (pcv_env r) x = Some v.

  Lemma dc_footprint_dom :
    forall l, footprint l ->
      exists rt fs, runtime_getObj h0 l = Some (mkObj rt fs).
  Proof.
    intros l Hl.
    have Hdom := reachable_abs_target_dom CT h0 receiver l Hl.
    unfold runtime_getObj.
    destruct (nth_error h0 l) as [[rt fs] |] eqn:Hnth; [eauto |].
    apply nth_error_None in Hnth. lia.
  Qed.

  Lemma dc_receiver_footprint : footprint receiver.
  Proof.
    apply reachable_abs_heap. eapply runtime_getObj_dom. exact Hobj0.
  Qed.

  Lemma dc_env_footprint : env_in footprint rhob.
  Proof.
    intros z l Hz. destruct z as [| z]; simpl in Hz.
    - injection Hz as <-. exact dc_receiver_footprint.
    - destruct z; discriminate.
  Qed.

  (** The controls after the body has finished. *)
  Inductive dc_chain (rGamma1 : r_env) : pico_core_expr -> Prop :=
    | DcChain_Exit : forall V,
        dc_chain rGamma1 (CoreRun rGamma1 SSkip V Kb)
    | DcChain_Resume : forall V retval,
        runtime_getVal rGamma1 ret = Some retval ->
        dc_chain rGamma1
          (CoreRun (set_vars caller (update x retval (vars caller))) SSkip V [])
    | DcChain_Done : forall V retval,
        runtime_getVal rGamma1 ret = Some retval ->
        dc_chain rGamma1
          (CoreDone OK (set_vars caller (update x retval (vars caller))) V).

  Lemma dc_chain_steps :
    forall rGamma1 k c e,
      footprint_steps CT footprint h0 k c e ->
      dc_chain rGamma1 c ->
      dc_chain rGamma1 e.
  Proof.
    intros rGamma1 k c e Hsteps. induction Hsteps; intros Hchain.
    - exact Hchain.
    - apply IHHsteps.
      match goal with Hst : pico_core_step _ _ _ _ _ |- _ => rename Hst into Hstep end.
      destruct Hchain; inversion Hstep; subst.
      + eapply DcChain_Resume. eassumption.
      + eapply DcChain_Done. eassumption.
  Qed.

  Lemma dc_classify :
    forall n V e,
      footprint_steps CT footprint h0 n (CoreRun rhob body V Kb) e ->
      deriv_running CT footprint h0 Kb e \/
      deriv_failed e \/
      exists rGamma1,
        eval_stmt CT rhob h0 body OK rGamma1 h0 /\ dc_chain rGamma1 e.
  Proof.
    intros n V e Hsteps.
    destruct (deriv_prefix CT D footprint h0 Htable dc_footprint_dom n n rhob
      body V Kb _ sGammab' mtb e (le_n n) Hsteps Hderivb Htypedb Hwfb
      dc_env_footprint)
      as [Hrun | [(rGamma1 & V1 & k & _ & Heval & _ & Htail) | Hfail]].
    - left. exact Hrun.
    - right. right. exists rGamma1. split; [exact Heval |].
      eapply dc_chain_steps; [exact Htail | apply DcChain_Exit].
    - right. left. exact Hfail.
  Qed.

  (** The phases of the call. *)
  Inductive dc_phase : pico_core_expr -> Prop :=
    | DcPh_Call : forall V,
        dc_phase (CoreRun caller (SCall x mn y []) V [])
    | DcPh_Body : forall n V e,
        footprint_steps CT footprint h0 n (CoreRun rhob body V Kb) e ->
        dc_phase e.

  Lemma dc_run_phase :
    forall V0 tr e,
      hash_run (CoreRun caller (SCall x mn y []) V0 []) tr e ->
      dc_phase e.
  Proof.
    intros V0 tr e Hrun.
    induction Hrun as
      [| tr rGamma x' y' f V V' K old loc k v cv sigma Hrun IH Hxo Hyo Hread
           Hfield Hvalue
       | tr e S e' S' Hrun IH Hnoread Hinv Hstep].
    - apply DcPh_Call.
    - (* derivation code never reads the cache field *)
      exfalso.
      destruct (pico_hash_cache_adapter_some _ _ _ Hfield) as [Haddr _].
      injection Haddr as -> ->.
      inversion IH as [V1 Heq | n V1 e1 Hsteps Heq]; subst.
      destruct (dc_classify n V1 _ Hsteps)
        as [Hrunning | [Hfailed | (rGamma1 & _ & Hchain)]].
      + destruct Hrunning as (rG & s & V2 & K2 & Heq & _ & _ & _ & Hreadc).
        injection Heq as <- <- <- <-.
        destruct (Hreadc x' y' hash_cache_field receiver eq_refl Hyo)
          as (_ & rt & fs & Hobj & Habs).
        rewrite Hobj0 in Hobj. injection Hobj as <- <-.
        exact (derived_cache_field_not_abstract CT _ _ Hcachefield Habs).
      + destruct Hfailed as (r & rG & V2 & Heq & _). discriminate.
      + inversion Hchain.
    - inversion IH as [V1 Heq | n V1 e1 Hsteps Heq]; subst.
      + inversion Hstep; subst; [| congruence].
        match goal with
        | Hyl : runtime_getVal caller y = Some (Iot ?l),
          Hb : r_basetype _ ?l = Some ?C,
          Hf : FindMethodWithName CT ?C mn ?md',
          Ha : runtime_lookup_list caller [] = Some ?vs |- _ =>
            rewrite Hy in Hyl; injection Hyl as <-;
            have Hcls := hash_inv_receiver_class CT receiver m h0 H rt0 fs0
              Hobj0 _ Hinv;
            simpl in Hcls; rewrite Hcls in Hb; injection Hb as <-;
            have Hmd := find_method_with_name_deterministic CT _ _ _ _ Hf Hfind;
            subst md'; simpl in Ha; injection Ha as <-
        end.
        eapply DcPh_Body with (n := 0). constructor.
      + eapply DcPh_Body.
        eapply footprint_steps_snoc;
          [exact Hsteps
          | exact (hash_inv_footprint_state CT receiver m h0 H _ Hinv)
          | exact Hstep].
  Qed.

  Hypothesis Hx : x < dom (vars caller).

  (** A call to a derivation method is trace robust on the machine: it
      writes nothing, and it returns the value the method denotes. *)
  Theorem derivation_call_trace_robust :
    forall V0,
      machine_cache_safe CT hash_cache_protocol pico_hash_stable_abs H
        (pico_hash_cache_adapter receiver) hash_machine
        deriv_call_result_ok
        (CoreRun caller (SCall x mn y []) V0 []).
  Proof.
    intros V0 tr e Hrun _.
    have Hphase := dc_run_phase V0 tr e Hrun.
    split.
    - intros rGamma x' f y' V K loc v -> Hx' Hy'.
      inversion Hphase as [V1 Heq | n V1 e1 Hsteps Heq]; subst.
      destruct (dc_classify n V1 _ Hsteps)
        as [Hrunning | [Hfailed | (rGamma1 & _ & Hchain)]].
      + destruct Hrunning as (rG & s & V2 & K2 & Heq & _ & Hnowrite & _).
        injection Heq as <- <- <- <-.
        exfalso. eapply Hnowrite. reflexivity.
      + destruct Hfailed as (r & rG & V2 & Heq & _). discriminate.
      + inversion Hchain.
    - intros r rGamma V ->.
      inversion Hphase as [V1 Heq | n V1 e1 Hsteps Heq]; subst.
      destruct (dc_classify n V1 _ Hsteps)
        as [Hrunning | [Hfailed | (rGamma1 & Heval & Hchain)]].
      + destruct Hrunning as (rG & s & V2 & K2 & Heq & _). discriminate.
      + destruct Hfailed as (r' & rG & V2 & Heq & Hr).
        injection Heq as <- <- <-.
        intros Hok. simpl in Hok. contradiction.
      + inversion Hchain; subst.
        intros _. exists retval.
        split; [exists rGamma1; split; assumption |].
        simpl. unfold runtime_getVal, set_vars. cbn [vars].
        apply update_same. exact Hx.
  Qed.
End derivation_call.

(** ** A parallel rule with one assertion per thread

    The threads of a pool may carry different assertions, for example
    different result contracts.  The rule is the parallel rule with the
    assertions indexed by thread position. *)

Lemma Forall2_update_right :
  forall {A B : Type} (R : A -> B -> Prop) l1 l2 tid b',
    Forall2 R l1 l2 ->
    (forall a, nth_error l1 tid = Some a -> R a b') ->
    Forall2 R l1 (update tid b' l2).
Proof.
  intros A B R l1 l2 tid b' Hall. revert tid.
  induction Hall as [| a b l1 l2 Hab Hrest IH]; intros tid Hnew.
  - destruct tid; constructor.
  - destruct tid as [| tid]; simpl.
    + constructor; [apply Hnew; reflexivity | exact Hrest].
    + constructor; [exact Hab |]. apply IH.
      intros a0 Hnth. apply Hnew. exact Hnth.
Qed.

Section indexed_pool.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table).
  Context {Spec : Type}.
  Context (Inv : pico_core_state -> Prop).
  Context (Local : Spec -> pico_core_expr -> pico_core_state -> Prop).

  Hypothesis own_step : forall sp e S e' S',
    Inv S -> Local sp e S -> pico_core_step CT e S e' S' ->
    Inv S' /\ Local sp e' S'.
  Hypothesis local_stable : forall sp e S S',
    Local sp e S -> Local sp e S'.

  Definition indexed_pool_inv (specs : list Spec) (cfg : pico_pool_config)
      : Prop :=
    Inv (pool_state cfg) /\
    Forall2 (fun sp e => Local sp e (pool_state cfg)) specs (pool_threads cfg).

  Theorem indexed_pool_steps :
    forall specs cfg cfg',
      indexed_pool_inv specs cfg ->
      pico_pool_steps CT cfg cfg' ->
      indexed_pool_inv specs cfg'.
  Proof.
    intros specs cfg cfg' Hinit Hsteps.
    induction Hsteps as [cfg0 | cfg1 cfg2 cfg3 Hstep _ IH]; [exact Hinit |].
    apply IH. destruct Hinit as [Hinv Hlocal].
    inversion Hstep as [S S' threads threads' tid e e' Hnth Hcore Hupd];
      subst; simpl in *.
    assert (Hsel : exists sp, nth_error specs tid = Some sp /\ Local sp e S).
    { clear -Hlocal Hnth. revert tid Hnth.
      induction Hlocal as [| sp e0 specs threads Hsp Hrest IH]; intros tid Hnth.
      - destruct tid; discriminate.
      - destruct tid as [| tid]; simpl in Hnth.
        + injection Hnth as ->. exists sp. split; [reflexivity | exact Hsp].
        + exact (IH tid Hnth). }
    destruct Hsel as (sp & Hsp & Hloc).
    destruct (own_step sp e S e' S' Hinv Hloc Hcore) as [Hinv' Hloc'].
    split; [exact Hinv' |].
    apply Forall2_update_right.
    - eapply Forall2_impl; [| exact Hlocal].
      intros sp0 e0 Hl. exact (local_stable sp0 e0 S S' Hl).
    - intros sp0 Hsp0. rewrite Hsp in Hsp0. injection Hsp0 as <-. exact Hloc'.
  Qed.
End indexed_pool.

Lemma machine_cache_safe_weaken :
  forall `{Hmem : CacheMemoryModel} (CT : class_table) {AbsVal Obj : Type}
    (P : CacheProtocol AbsVal) (Stable : StableAbs Obj AbsVal) (a : AbsVal)
    (A : PicoCoreCacheAdapter P) (M : PicoCoreSemImmInstantiation P Stable a A)
    (R1 R2 : pico_core_val -> Prop) e0,
    (forall r, R1 r -> R2 r) ->
    machine_cache_safe CT P Stable a A M R1 e0 ->
    machine_cache_safe CT P Stable a A M R2 e0.
Proof.
  intros Hmem CT AbsVal Obj P Stable a A M R1 R2 e0 Himpl Hsafe tr e Hrun Hvalid.
  destruct (Hsafe tr e Hrun Hvalid) as [Hwrite Hresult].
  split; [exact Hwrite |].
  intros r rGamma V Heq. apply Himpl. exact (Hresult r rGamma V Heq).
Qed.

(** ** The class-level theorem *)

Section value_class_theorem.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table) (D : method_def -> Prop).
  Context (receiver : Loc) (m : method_name) (h0 : heap) (H : nat).
  Context (rt0 : runtime_type) (fs0 : fields_mapping).
  Context (derived : class_name -> var -> Prop).

  Hypothesis Htable : derivation_table CT D.
  Hypothesis Hobj0 : runtime_getObj h0 receiver = Some (mkObj rt0 fs0).
  Hypothesis Hcachefield :
    derived_cache_field CT (rctype rt0) hash_cache_field.

  (** A cache method for the derived field: the local-copy shape with a
      derivation initializer that computes the protocol's value. *)
  Definition is_cache_method (md : method_def) : Prop :=
    exists compute Trecv sGamma' mt,
      mbody_stmt (mbody md) = pico_hash_method_stmt_with compute /\
      mreturn (mbody md) = cache_result /\
      deriv_stmt CT D [Trecv; int_type; int_type] compute sGamma' /\
      stmt_typing CT [Trecv; int_type; int_type] mt compute sGamma' /\
      wf_r_config CT [Trecv; int_type; int_type]
        (env_tmp receiver (Int 0)) h0 /\
      (forall rGamma1,
         eval_stmt CT (env_tmp receiver (Int 0)) h0 compute OK rGamma1 h0 ->
         runtime_getVal rGamma1 cache_tmp = Some (Int H)).

  (** A derivation method: its body is derivation code, typed in a frame that
      holds only the receiver. *)
  Definition is_derivation_method (md : method_def) : Prop :=
    exists sGammab' mtb,
      deriv_stmt CT D [mreceiver (msignature md)] (mbody_stmt (mbody md))
        sGammab' /\
      stmt_typing CT [mreceiver (msignature md)] mtb (mbody_stmt (mbody md))
        sGammab' /\
      wf_r_config CT [mreceiver (msignature md)] (mkr_env [Iot receiver]) h0.

  (** The class of the receiver is a semantic value class: its state is
      complete, transitively, and every method is a cache method or a
      derivation method. *)
  Definition pico_semantic_value_class : Prop :=
    transitive_value_class CT derived (rctype rt0) /\
    forall mn md,
      FindMethodWithName CT (rctype rt0) mn md ->
      is_cache_method md \/ is_derivation_method md.

  (** One call: who calls, where the result goes, and which method. *)
  Record call_spec : Type := mkCallSpec {
    cs_caller : r_env;
    cs_target : var;
    cs_receiver : var;
    cs_method : method_name;
    cs_def : method_def;
    cs_view : view
  }.

  Definition call_control (sp : call_spec) : pico_core_expr :=
    CoreRun (cs_caller sp)
      (SCall (cs_target sp) (cs_method sp) (cs_receiver sp) []) (cs_view sp) [].

  Definition call_ok (sp : call_spec) : Prop :=
    FindMethodWithName CT (rctype rt0) (cs_method sp) (cs_def sp) /\
    runtime_getVal (cs_caller sp) (cs_receiver sp) = Some (Iot receiver) /\
    cs_target sp < dom (vars (cs_caller sp)).

  (** The value a method returns, as a function of the reference heap: the
      protocol's value for a cache method, and for a derivation method what
      its body evaluates to on the receiver. *)
  Definition method_value (md : method_def) (v : value) : Prop :=
    (is_cache_method md /\ v = Int H) \/
    method_denotes CT receiver h0 md v.

  Definition call_result_ok (sp : call_spec) (r : pico_core_val) : Prop :=
    pcv_result r = OK ->
    exists v,
      method_value (cs_def sp) v /\
      runtime_getVal (pcv_env r) (cs_target sp) = Some v.

  Notation hash_machine := (pico_concrete_hash_semimm CT receiver m h0 H).
  Notation hash_inv :=
    (machine_inv hash_cache_protocol pico_hash_stable_abs H
       (pico_hash_cache_adapter receiver) hash_machine).

  (** Every call to a method of a semantic value class is trace robust. *)
  Lemma value_class_call_safe :
    forall sp,
      pico_semantic_value_class ->
      call_ok sp ->
      machine_cache_safe CT hash_cache_protocol pico_hash_stable_abs H
        (pico_hash_cache_adapter receiver) hash_machine
        (call_result_ok sp) (call_control sp).
  Proof.
    intros sp [_ Hmethods] (Hfind & Hy & Hx).
    destruct (Hmethods _ _ Hfind)
      as [Hcache | (sGb & mtb & Hderivb & Htypedb & Hwfb)].
    - pose proof Hcache
        as (compute & Trecv & sG' & mt & Hbody & Hret & Hderiv & Htyped & Hwf3
            & Hcompute).
      eapply machine_cache_safe_weaken;
        [| eapply (cache_method_call_trace_robust CT D receiver m h0 H compute
             (cs_method sp) (cs_def sp) Trecv sG' mt rt0 fs0 (cs_caller sp)
             (cs_target sp) (cs_receiver sp)); eassumption].
      intros r Hr Hok. exists (Int H).
      split; [left; split; [exact Hcache | reflexivity] | exact (Hr Hok)].
    - eapply machine_cache_safe_weaken;
        [| eapply (derivation_call_trace_robust CT D receiver m h0 H
             (cs_method sp) (cs_def sp) sGb mtb rt0 fs0 (cs_caller sp)
             (cs_target sp) (cs_receiver sp)); eassumption].
      intros r Hr Hok. destruct (Hr Hok) as (v & Hden & Hv).
      exists v. split; [right; exact Hden | exact Hv].
  Qed.

  (** The class-level theorem.  For an object of a semantic value class, any
      number of threads may call any of its methods.  In every reachable
      pool the object is semantically immutable, and every call that has
      returned normally returned the value of its method, which is a
      function of the reference heap. *)
  Theorem semantic_value_class_sound :
    forall specs S0 cfg,
      pico_semantic_value_class ->
      Forall call_ok specs ->
      hash_inv S0 ->
      pico_pool_steps CT
        (mkPicoPoolConfig S0 (map call_control specs)) cfg ->
      hash_inv (pool_state cfg) /\
      Forall2
        (fun sp e =>
           forall r rGamma V,
             e = CoreDone r rGamma V ->
             call_result_ok sp (mkPicoCoreVal r rGamma V))
        specs (pool_threads cfg).
  Proof.
    intros specs S0 cfg Hclass Hcalls Hinv Hsteps.
    set (Local := fun (sp : call_spec) (e : pico_core_expr)
        (S : pico_core_state) =>
      machine_local CT hash_cache_protocol pico_hash_stable_abs H
        (pico_hash_cache_adapter receiver) hash_machine (call_result_ok sp) e S).
    assert (Hstart : indexed_pool_inv hash_inv Local specs
      (mkPicoPoolConfig S0 (map call_control specs))).
    { clear Hsteps. split; [exact Hinv |]. simpl.
      induction Hcalls as [| sp specs Hsp _ IH]; simpl; constructor.
      - apply machine_local_start.
        exact (value_class_call_safe sp Hclass Hsp).
      - exact IH. }
    destruct (indexed_pool_steps CT hash_inv Local
      (fun sp e S e' S' Hi Hl Hs =>
         machine_own_step CT hash_cache_protocol pico_hash_stable_abs H
           (pico_hash_cache_adapter receiver) hash_machine (call_result_ok sp)
           e S e' S' Hi Hl Hs)
      (fun sp e S S' Hl => Hl)
      specs _ cfg Hstart Hsteps) as [Hinv' Hlocal].
    split; [exact Hinv' |].
    eapply Forall2_impl; [| exact Hlocal].
    intros sp e Hl r rGamma V ->.
    exact (machine_local_result CT hash_cache_protocol pico_hash_stable_abs H
      (pico_hash_cache_adapter receiver) hash_machine (call_result_ok sp)
      r rGamma V (pool_state cfg) Hl).
  Qed.
End value_class_theorem.
