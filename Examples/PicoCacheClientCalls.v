From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping Bigstep Properties Reachability.
Require Import Core.GenericCacheProtocol Core.GenericDerivedCache.
Require Import Examples.PicoIfZeroCache Examples.PicoHashMethod
  Examples.PicoConcreteHashProvider Examples.PicoCacheMethodJudgment.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoCacheTyping
  PICOBridge.PicoCoreLanguage PICOBridge.PicoCoreFrame
  PICOBridge.PicoCoreSemImm
  PICOBridge.PicoDerivationNoninterference PICOBridge.PicoDerivationCache
  PICOBridge.PicoCoreTraceRobust.

(** * Client Code that Calls the Cache Method

    A thread may interleave its own code with calls to the cache method on
    the cached object.  Client code declares locals, assigns them, reads
    fields (including the cache field), allocates, branches, and calls the
    cache method through a variable that holds the object and is never
    reassigned.  It has no field write of its own.

    Every such thread is trace robust on the machine.  At each point the
    thread is either in client code or inside one call, and a call behaves
    inside the client's continuation exactly as it does alone, because steps
    do not inspect the rest of the continuation. *)

Section client_calls.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table) (D : method_def -> Prop).
  Context (receiver : Loc) (m : method_name) (h0 : heap) (H : nat).
  Context (compute : stmt) (mc : method_name) (mdef : method_def).
  Context (Trecv : qualified_type) (sGamma' : s_env) (mt : method_scope).
  Context (rt0 : runtime_type) (fs0 : fields_mapping).
  Context (y0 : var).

  (** The cache-method judgment for [mdef]. *)
  Hypothesis Hbody :
    mbody_stmt (mbody mdef) = pico_hash_method_stmt_with compute.
  Hypothesis Hret : mreturn (mbody mdef) = cache_result.
  Hypothesis Htable : derivation_table CT D.
  Hypothesis Hderiv :
    deriv_stmt CT D [Trecv; int_type; int_type] compute sGamma'.
  Hypothesis Htyped :
    stmt_typing CT [Trecv; int_type; int_type] mt compute sGamma'.
  Hypothesis Hwf3 :
    wf_r_config CT [Trecv; int_type; int_type]
      (env_tmp receiver (Int 0)) h0.
  Hypothesis Hcompute :
    forall rGamma1,
      eval_stmt CT (env_tmp receiver (Int 0)) h0 compute OK rGamma1 h0 ->
      runtime_getVal rGamma1 cache_tmp = Some (Int H).
  Hypothesis Hobj0 : runtime_getObj h0 receiver = Some (mkObj rt0 fs0).
  Hypothesis Hcachefield :
    derived_cache_field CT (rctype rt0) hash_cache_field.
  Hypothesis Hfind : FindMethodWithName CT (rctype rt0) mc mdef.

  Notation hash_machine := (pico_concrete_hash_semimm CT receiver m h0 H).
  Notation hash_inv :=
    (machine_inv hash_cache_protocol pico_hash_stable_abs H
       (pico_hash_cache_adapter receiver) hash_machine).
  Notation hash_run :=
    (thread_run CT hash_cache_protocol pico_hash_stable_abs H
       (pico_hash_cache_adapter receiver) hash_machine).
  Notation hash_cache_read :=
    (cache_read_control hash_cache_protocol (pico_hash_cache_adapter receiver)).

  (** ** Client code *)
  Inductive client_stmt : stmt -> Prop :=
    | Client_Skip :
        client_stmt SSkip
    | Client_Local : forall T x,
        client_stmt (SLocal T x)
    | Client_VarAss : forall x e,
        x <> y0 ->
        client_stmt (SVarAss x e)
    | Client_New : forall x qc C args,
        x <> y0 ->
        client_stmt (SNew x qc C args)
    | Client_Seq : forall s1 s2,
        client_stmt s1 -> client_stmt s2 ->
        client_stmt (SSeq s1 s2)
    | Client_IfZero : forall x s1 s2,
        client_stmt s1 -> client_stmt s2 ->
        client_stmt (SIfZero x s1 s2)
    | Client_Call : forall x,
        x <> y0 ->
        client_stmt (SCall x mc y0 []).

  Definition client_frame (fr : pico_core_frame) : Prop :=
    exists s, fr = KSeq s /\ client_stmt s.

  Definition client_cont (K : pico_core_cont) : Prop :=
    Forall client_frame K.

  Definition holds_receiver (rGamma : r_env) : Prop :=
    runtime_getVal rGamma y0 = Some (Iot receiver).

  (** The thread is in client code. *)
  Definition client_ctl (e : pico_core_expr) : Prop :=
    (exists rGamma s V K,
       e = CoreRun rGamma s V K /\
       holds_receiver rGamma /\ client_stmt s /\ client_cont K) \/
    (exists r rGamma V, e = CoreDone r rGamma V).

  (** The thread is inside a call made by client code: its control is a
      control of the call run alone, above the client's continuation. *)
  Definition in_call (e : pico_core_expr) : Prop :=
    exists caller x K V0 tr1 e1,
      holds_receiver caller /\
      x <> y0 /\
      client_cont K /\
      hash_run (CoreRun caller (SCall x mc y0 []) V0 []) tr1 e1 /\
      ValidTrace hash_cache_protocol H tr1 /\
      e = append_cont K e1.

  Definition mixed (e : pico_core_expr) : Prop := client_ctl e \/ in_call e.

  Lemma holds_receiver_update :
    forall rGamma x v,
      x <> y0 ->
      holds_receiver rGamma ->
      holds_receiver (set_vars rGamma (update x v (vars rGamma))).
  Proof.
    intros rGamma x v Hneq Hrecv.
    unfold holds_receiver, runtime_getVal, set_vars in *. cbn [vars].
    rewrite update_diff; assumption.
  Qed.

  Lemma holds_receiver_append :
    forall rGamma v,
      holds_receiver rGamma ->
      holds_receiver (set_vars rGamma (vars rGamma ++ [v])).
  Proof.
    intros rGamma v Hrecv.
    unfold holds_receiver, runtime_getVal, set_vars in *. cbn [vars].
    rewrite nth_error_app1; [exact Hrecv |].
    apply nth_error_Some. congruence.
  Qed.

  Lemma client_run :
    forall rGamma s V K,
      holds_receiver rGamma -> client_stmt s -> client_cont K ->
      mixed (CoreRun rGamma s V K).
  Proof.
    intros rGamma s V K Hrecv Hs HK. left. left.
    exists rGamma, s, V, K. repeat split; assumption.
  Qed.

  Lemma client_done :
    forall r rGamma V, mixed (CoreDone r rGamma V).
  Proof. intros r rGamma V. left. right. exists r, rGamma, V. reflexivity. Qed.

  Lemma call_not_cache_read :
    forall caller x V,
      ~ hash_cache_read (CoreRun caller (SCall x mc y0 []) V []).
  Proof.
    intros caller x V (rG & x1 & y1 & f1 & V1 & K1 & loc & k & Heq & _).
    discriminate.
  Qed.

  (** A step of client code. *)
  Lemma client_step :
    forall e S e' S',
      client_ctl e ->
      hash_inv S ->
      pico_core_step CT e S e' S' ->
      mixed e'.
  Proof.
    intros e S e' S'
      [(rGamma & s & V & K & -> & Hrecv & Hs & HK) | (r & rGamma & V & ->)]
      Hinv Hstep; [| inversion Hstep].
    destruct Hs.
    - (* skip *)
      inversion Hstep; subst.
      + apply client_done.
      + inversion HK as [| fr K' Hfr HK']; subst.
        destruct Hfr as (s & Heq & Hs). injection Heq as <-.
        apply client_run; assumption.
      + inversion HK as [| fr K' Hfr HK']; subst.
        destruct Hfr as (s & Heq & _). discriminate.
    - inversion Hstep; subst.
      apply client_run; [apply holds_receiver_append; exact Hrecv | constructor | exact HK].
    - inversion Hstep; subst;
        try (apply client_run;
             [apply holds_receiver_update; assumption | constructor | exact HK]).
      apply client_done.
    - inversion Hstep; subst.
      apply client_run;
        [apply holds_receiver_update; assumption | constructor | exact HK].
    - inversion Hstep; subst.
      apply client_run; [exact Hrecv | assumption |].
      constructor; [| exact HK]. eexists. split; [reflexivity | assumption].
    - inversion Hstep; subst; apply client_run; assumption.
    - (* a call to the cache method *)
      inversion Hstep; subst; [| apply client_done].
      match goal with
      | Hyl : runtime_getVal rGamma y0 = Some (Iot ?l),
        Hb : r_basetype _ ?l = Some ?C,
        Hf : FindMethodWithName CT ?C mc ?md,
        Ha : runtime_lookup_list rGamma [] = Some ?vs |- _ =>
          unfold holds_receiver in Hrecv;
          rewrite Hrecv in Hyl; injection Hyl as <-;
          have Hcls := hash_inv_receiver_class CT receiver m h0 H rt0 fs0
            Hobj0 _ Hinv;
          simpl in Hcls; rewrite Hcls in Hb; injection Hb as <-;
          have Hmd := find_method_with_name_deterministic CT _ _ _ _ Hf Hfind;
          subst md; simpl in Ha; injection Ha as <-
      end.
      right.
      exists rGamma, x, K, V, (@nil (CacheObs hash_cache_protocol)),
        (CoreRun (mkr_env [Iot receiver]) (mbody_stmt (mbody mdef)) V
           [KCall rGamma x (mreturn (mbody mdef))]).
      split; [exact Hrecv |]. split; [assumption |]. split; [exact HK |].
      split; [| split; [constructor | reflexivity]].
      eapply ThreadRun_Step;
        [apply ThreadRun_Start | apply call_not_cache_read | exact Hinv |].
      eapply PCS_Call; eauto.
  Qed.

  Lemma cache_read_under_cont :
    forall K rGamma s V K1,
      hash_cache_read (CoreRun rGamma s V K1) ->
      hash_cache_read (CoreRun rGamma s V (K1 ++ K)).
  Proof.
    intros K rGamma s V K1 (rG & x1 & y1 & f1 & V1 & K2 & loc & k & Heq & Hy & Hf).
    injection Heq as -> -> -> ->.
    exists rG; exists x1; exists y1; exists f1; exists V1; exists (K2 ++ K);
      exists loc; exists k.
    split; [reflexivity |]. split; assumption.
  Qed.

  (** A step inside a call. *)
  Lemma in_call_step :
    forall e S e' S',
      in_call e ->
      ~ hash_cache_read e ->
      hash_inv S ->
      pico_core_step CT e S e' S' ->
      mixed e'.
  Proof.
    intros e S e' S'
      (caller & x & K & V0 & tr1 & e1 & Hrecv & Hx & HK & Hrun & Hvalid & ->)
      Hnoread Hinv Hstep.
    destruct e1 as [rGamma1 s1 V1 K1 | r rGamma1 V1];
      [| simpl in Hstep; inversion Hstep].
    simpl in Hstep, Hnoread.
    assert (Hexit : (s1 = SSkip /\ K1 = []) \/ ~ (s1 = SSkip /\ K1 = [])).
    { destruct s1; try (right; intros [Hs _]; discriminate).
      destruct K1; [left; split; reflexivity | right; intros [_ HK1]; discriminate]. }
    destruct Hexit as [[-> ->] | Hnot].
    - (* the call has returned: back in client code *)
      assert (Henv : rGamma1 =
        set_vars caller (update x (Int H) (vars caller))).
      { eapply cache_method_call_exit; [.. | exact Hrun | exact Hvalid];
          first [eassumption | exact Hrecv]. }
      subst rGamma1. simpl in Hstep.
      eapply client_step; [| exact Hinv | exact Hstep].
      left. do 4 eexists. split; [reflexivity |].
      split; [apply holds_receiver_update; assumption |].
      split; [constructor | exact HK].
    - destruct (step_under_cont CT K rGamma1 s1 V1 K1 S e' S' Hstep Hnot)
        as (e1' & Hstep1 & ->).
      right. exists caller, x, K, V0, tr1, e1'.
      split; [exact Hrecv |]. split; [exact Hx |]. split; [exact HK |].
      split; [| split; [exact Hvalid | reflexivity]].
      eapply ThreadRun_Step; [exact Hrun | | exact Hinv | exact Hstep1].
      intros Hread. apply Hnoread. apply cache_read_under_cont. exact Hread.
  Qed.

  Lemma client_run_mixed :
    forall e0 tr e,
      hash_run e0 tr e ->
      ValidTrace hash_cache_protocol H tr ->
      client_ctl e0 ->
      mixed e.
  Proof.
    intros e0 tr e Hrun.
    induction Hrun as
      [| tr rGamma x' y' f V V' K0 old loc k v cv sigma Hrun IH Hxo Hyo Hread
           Hfield Hvalue
       | tr e S e' S' Hrun IH Hnoread Hinv Hstep];
      intros Hvalid Hclient.
    - left. exact Hclient.
    - apply Forall_app in Hvalid. destruct Hvalid as [Hvalid Hobs].
      destruct (IH Hvalid Hclient)
        as [[(rG & s & V1 & K1 & Heq & Hrecv & Hs & HK) | (r & rG & V1 & Heq)]
           | (caller & x & K & V0 & tr1 & e1 & Hrecv & Hx & HK & Hrun1
              & Hvalid1 & Heq)].
      + injection Heq as <- <- <- <-.
        inversion Hs; subst.
        apply client_run;
          [apply holds_receiver_update; assumption | constructor | exact HK].
      + discriminate.
      + destruct e1 as [rGamma1 s1 V1 K1 | r rGamma1 V1];
          simpl in Heq; [| discriminate].
        injection Heq as <- <- <- ->.
        right.
        exists caller, x, K, V0,
          (tr1 ++ [{| obs_field := k; obs_value := cv |}]),
          (CoreRun (set_vars rGamma (update x' v (vars rGamma))) SSkip V' K1).
        split; [exact Hrecv |]. split; [exact Hx |]. split; [exact HK |].
        split; [| split; [| reflexivity]].
        * eapply ThreadRun_CacheRead; eassumption.
        * apply Forall_app. split; [exact Hvalid1 | exact Hobs].
    - destruct (IH Hvalid Hclient) as [Hc | Hin].
      + exact (client_step e S e' S' Hc Hinv Hstep).
      + exact (in_call_step e S e' S' Hin Hnoread Hinv Hstep).
  Qed.

  (** ** Client code is trace robust *)
  Theorem client_code_trace_robust :
    forall rGamma s V,
      holds_receiver rGamma ->
      client_stmt s ->
      machine_cache_safe CT hash_cache_protocol pico_hash_stable_abs H
        (pico_hash_cache_adapter receiver) hash_machine
        (fun _ => True)
        (CoreRun rGamma s V []).
  Proof.
    intros rGamma s V Hrecv Hs tr e Hrun Hvalid.
    split; [| intros; exact I].
    intros rG x' f y' V1 K0 loc v -> Hx' Hy'.
    assert (Hstart : client_ctl (CoreRun rGamma s V [])).
    { left. exists rGamma, s, V, (@nil pico_core_frame).
      repeat split; try assumption. constructor. }
    destruct (client_run_mixed _ tr _ Hrun Hvalid Hstart)
      as [[(rG1 & s1 & V2 & K1 & Heq & _ & Hs1 & _) | (r & rG1 & V2 & Heq)]
         | (caller & x & K & V0 & tr1 & e1 & Hrecv1 & Hx & HK & Hrun1
            & Hvalid1 & Heq)].
    - injection Heq as <- <- <- <-. inversion Hs1.
    - discriminate.
    - destruct e1 as [rGamma1 s1 V2 K1 | r rGamma1 V2];
        simpl in Heq; [| discriminate].
      injection Heq as <- <- <- ->.
      eapply cache_method_call_write_ok;
        [.. | exact Hrun1 | exact Hvalid1 | exact Hx' | exact Hy'];
        first [eassumption | exact Hrecv1].
  Qed.
End client_calls.
