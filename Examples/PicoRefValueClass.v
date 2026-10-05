From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping Bigstep Properties Reachability
  ViewpointAdaptation.
Require Import Examples.PicoIfZeroCache Examples.PicoRefCacheJudgment
  Examples.PicoConcreteHashProvider Examples.PicoRefViewExample
  Examples.PicoValueClasses Examples.PicoValueClassTheorem.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoCacheTyping
  PICOBridge.PicoCoreLanguage PICOBridge.PicoCoreInvariant
  PICOBridge.PicoDerivationNoninterference PICOBridge.PicoDerivationSmallStep
  PICOBridge.PicoDerivationPrefix PICOBridge.PicoSemanticConcurrency.

(** * Semantic Value Classes with a Reference Cache

    The class-level theorem for a class whose derived field is a reference
    cache.  Every method of the class is a reference-cache method or a
    derivation method.  Any number of threads may call any of them on an
    object: the shared invariant is preserved, a cache method returns a
    valid reference, and a derivation method returns the value it denotes. *)

(** ** A parallel rule with one assertion per thread and a guarantee *)

Section indexed_guar_pool.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table).
  Context {Spec : Type}.
  Context (Inv : pico_core_state -> Prop).
  Context (Guar : pico_core_state -> pico_core_state -> Prop).
  Context (Local : Spec -> pico_core_expr -> pico_core_state -> Prop).

  Hypothesis own_step : forall sp e S e' S',
    Inv S -> Local sp e S -> pico_core_step CT e S e' S' ->
    Guar S S' /\ Local sp e' S'.
  Hypothesis guar_inv : forall S S', Inv S -> Guar S S' -> Inv S'.
  Hypothesis local_stable : forall sp e S S',
    Local sp e S -> Guar S S' -> Local sp e S'.

  Definition indexed_guar_inv (specs : list Spec) (cfg : pico_pool_config)
      : Prop :=
    Inv (pool_state cfg) /\
    Forall2 (fun sp e => Local sp e (pool_state cfg)) specs (pool_threads cfg).

  Theorem indexed_guar_pool_steps :
    forall specs cfg cfg',
      indexed_guar_inv specs cfg ->
      pico_pool_steps CT cfg cfg' ->
      indexed_guar_inv specs cfg'.
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
    destruct (own_step sp e S e' S' Hinv Hloc Hcore) as [Hguar Hloc'].
    split; [exact (guar_inv S S' Hinv Hguar) |].
    apply Forall2_update_right.
    - eapply Forall2_impl; [| exact Hlocal].
      intros sp0 e0 Hl. exact (local_stable sp0 e0 S S' Hl Hguar).
    - intros sp0 Hsp0. rewrite Hsp in Hsp0. injection Hsp0 as <-. exact Hloc'.
  Qed.
End indexed_guar_pool.

Section ref_value_class.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table) (D : method_def -> Prop).
  Context (receiver : Loc) (h0 : heap).
  Context (cf : var) (Cv : class_name) (vals0 : list value).
  Context (rt0 : runtime_type) (fs0 : fields_mapping).
  Context (derived : class_name -> var -> Prop).

  Let footprint := reachable_abs CT h0 receiver.

  Hypothesis Himm : forall l, footprint l ->
    exists C vals,
      runtime_getObj h0 l = Some (mkObj (mkruntime_type Imm_r C) vals).
  Hypothesis Htable : derivation_table CT D.
  Hypothesis Hobj0 : runtime_getObj h0 receiver = Some (mkObj rt0 fs0).

  Notation vok := (view_ok CT Cv vals0).
  Notation inv := (ref_inv CT receiver h0 cf Cv vals0).
  Notation guar := (ref_guar CT receiver h0 cf Cv vals0).

  (** A reference-cache method for the derived field [cf]. *)
  Definition is_ref_cache_method (md : method_def) : Prop :=
    exists qc zs s_args Trecv Tv sGamma' mt,
      mbody_stmt (mbody md) = ref_cache_body cf Cv qc zs s_args Tv /\
      mreturn (mbody md) = cache_result /\
      default_value Tv = Null_a /\
      deriv_stmt CT D [Trecv; Tv; Tv] s_args sGamma' /\
      stmt_typing CT [Trecv; Tv; Tv] mt s_args sGamma' /\
      wf_r_config CT [Trecv; Tv; Tv] (env_ref receiver Null_a) h0 /\
      (forall rGamma1,
         eval_stmt CT (env_ref receiver Null_a) h0 s_args OK rGamma1 h0 ->
         runtime_lookup_list rGamma1 zs = Some vals0 /\
         cache_result < dom (vars rGamma1)) /\
      vpa_mutability_object_creation (rqtype rt0) qc = Imm_r.

  (** The class of the receiver is a semantic value class with a reference
      cache. *)
  Definition pico_ref_value_class : Prop :=
    transitive_value_class CT derived (rctype rt0) /\
    forall mn md,
      FindMethodWithName CT (rctype rt0) mn md ->
      is_ref_cache_method md \/ is_derivation_method CT D receiver h0 md.

  (** The assertion about one call. *)
  Definition ref_call_local
      (sp : call_spec) (e : pico_core_expr) (S : pico_core_state) : Prop :=
    (exists qc zs s_args Tv,
       ref_phase CT receiver h0 cf Cv vals0 qc zs s_args (cs_method sp) Tv
         (cs_caller sp) (cs_target sp) (cs_receiver sp) S e /\
       exists Trecv sGamma' mt,
         mbody_stmt (mbody (cs_def sp)) = ref_cache_body cf Cv qc zs s_args Tv /\
         mreturn (mbody (cs_def sp)) = cache_result /\
         default_value Tv = Null_a /\
         deriv_stmt CT D [Trecv; Tv; Tv] s_args sGamma' /\
         stmt_typing CT [Trecv; Tv; Tv] mt s_args sGamma' /\
         wf_r_config CT [Trecv; Tv; Tv] (env_ref receiver Null_a) h0 /\
         (forall rGamma1,
            eval_stmt CT (env_ref receiver Null_a) h0 s_args OK rGamma1 h0 ->
            runtime_lookup_list rGamma1 zs = Some vals0 /\
            cache_result < dom (vars rGamma1)) /\
         vpa_mutability_object_creation (rqtype rt0) qc = Imm_r) \/
    (is_derivation_method CT D receiver h0 (cs_def sp) /\
     dc_phase CT receiver h0 (cs_method sp) (cs_def sp)
       (cs_caller sp) (cs_target sp) (cs_receiver sp) e).

  (** One step of a call to a derivation method preserves the invariant. *)
  Lemma ref_derivation_call_step :
    forall sp e S e' S',
      call_ok CT receiver rt0 sp ->
      is_derivation_method CT D receiver h0 (cs_def sp) ->
      inv S ->
      dc_phase CT receiver h0 (cs_method sp) (cs_def sp)
        (cs_caller sp) (cs_target sp) (cs_receiver sp) e ->
      pico_core_step CT e S e' S' ->
      inv S' /\
      dc_phase CT receiver h0 (cs_method sp) (cs_def sp)
        (cs_caller sp) (cs_target sp) (cs_receiver sp) e'.
  Proof.
    intros sp e S e' S' (Hfind & Hy & _)
      (sGb & mtb & Hderivb & Htypedb & Hwfb) Hinv Hphase Hstep.
    split.
    - eapply (ref_inv_step CT receiver h0 cf Cv vals0 Himm e S e' S' Hinv Hstep).
      intros rG x' y' V K v -> _ _.
      exfalso.
      inversion Hphase as [V1 Heq | n V1 e1 Hsteps Heq]; subst.
      destruct (dc_classify CT D receiver h0 (cs_def sp) sGb mtb rt0 fs0
        (cs_caller sp) (cs_target sp) Htable Hderivb Htypedb Hwfb Hobj0
        n V1 _ Hsteps)
        as [Hrunning | [Hfailed | (rGamma1 & _ & Hchain)]].
      + destruct Hrunning as (rG0 & s & V2 & K2 & Heq & _ & Hnowrite & _).
        injection Heq as <- <- <- <-. eapply Hnowrite. reflexivity.
      + destruct Hfailed as (r & rG0 & V2 & Heq & _). discriminate.
      + inversion Hchain.
    - inversion Hphase as [V1 Heq | n V1 e1 Hsteps Heq]; subst.
      + inversion Hstep; subst; [| congruence].
        match goal with
        | Hyl : runtime_getVal (cs_caller sp) (cs_receiver sp) = Some (Iot ?l),
          Hb : r_basetype _ ?l = Some ?C,
          Hf : FindMethodWithName CT ?C (cs_method sp) ?md',
          Ha : runtime_lookup_list (cs_caller sp) [] = Some ?vs |- _ =>
            rewrite Hy in Hyl; injection Hyl as <-;
            destruct (inv_receiver_type CT receiver h0 cf Cv vals0 rt0 fs0
              Hobj0 _ Hinv) as [fsr Hobjr];
            simpl in Hobjr; unfold r_basetype in Hb; rewrite Hobjr in Hb;
            injection Hb as <-;
            have Hmd := find_method_with_name_deterministic CT _ _ _ _ Hf Hfind;
            subst md'; simpl in Ha; injection Ha as <-
        end.
        eapply DcPh_Body with (n := 0). constructor.
      + eapply DcPh_Body.
        eapply footprint_steps_snoc;
          [exact Hsteps | destruct Hinv as (_ & Hfs & _); exact Hfs | exact Hstep].
  Qed.

  Lemma ref_call_own_step :
    forall sp e S e' S',
      call_ok CT receiver rt0 sp ->
      inv S ->
      ref_call_local sp e S ->
      pico_core_step CT e S e' S' ->
      guar S S' /\ ref_call_local sp e' S'.
  Proof.
    intros sp e S e' S' Hok Hinv Hlocal Hstep.
    pose proof Hok as (Hfind & Hy & _).
    destruct Hlocal as
      [(qc & zs & s_args & Tv & Hphase & Trecv & sG' & mt & Hbody & Hret
        & Hdefault & Hderiv & Htyped & Hwf3 & Hargs & Hqimm)
      | (Hderivm & Hphase)].
    - destruct (ref_own_step CT D receiver h0 cf Cv vals0 qc zs s_args
        (cs_method sp) (cs_def sp) Trecv Tv sG' mt rt0 fs0 (cs_caller sp)
        (cs_target sp) (cs_receiver sp) Himm Hbody Hret Hdefault Htable Hderiv
        Htyped Hwf3 Hargs Hobj0 Hqimm Hfind Hy e S e' S' Hinv Hphase Hstep)
        as [Hguar Hphase'].
      split; [exact Hguar |].
      left. exists qc, zs, s_args, Tv. split; [exact Hphase' |].
      exists Trecv, sG', mt.
      exact (conj Hbody (conj Hret (conj Hdefault (conj Hderiv (conj Htyped
        (conj Hwf3 (conj Hargs Hqimm))))))).
    - destruct (ref_derivation_call_step sp e S e' S' Hok Hderivm Hinv Hphase
        Hstep) as [Hinv' Hphase'].
      split.
      + split; [| exact Hinv'].
        intros l Hl. destruct Hinv as (Hagree & _).
        eapply view_ok_step; eassumption.
      + right. split; assumption.
  Qed.

  Lemma ref_call_local_stable :
    forall sp e S S',
      ref_call_local sp e S -> guar S S' -> ref_call_local sp e S'.
  Proof.
    intros sp e S S' Hlocal [Hmono _].
    destruct Hlocal as
      [(qc & zs & s_args & Tv & Hphase & Hrest) | Hderivm].
    - left. exists qc, zs, s_args, Tv. split; [| exact Hrest].
      eapply ref_phase_mono; eassumption.
    - right. exact Hderivm.
  Qed.

  (** What a finished call returned. *)
  Definition ref_call_result
      (S : pico_core_state) (sp : call_spec) (rG : r_env) : Prop :=
    (is_ref_cache_method (cs_def sp) /\
     exists l, runtime_getVal rG (cs_target sp) = Some (Iot l) /\ vok S l) \/
    (exists v,
       method_denotes CT receiver h0 (cs_def sp) v /\
       runtime_getVal rG (cs_target sp) = Some v).

  (** The class-level theorem for reference caches. *)
  Theorem ref_value_class_sound :
    forall specs S0 cfg,
      pico_ref_value_class ->
      Forall (call_ok CT receiver rt0) specs ->
      inv S0 ->
      pico_pool_steps CT (mkPicoPoolConfig S0 (map call_control specs)) cfg ->
      inv (pool_state cfg) /\
      Forall2
        (fun sp e =>
           forall rG V,
             e = CoreDone OK rG V ->
             ref_call_result (pool_state cfg) sp rG)
        specs (pool_threads cfg).
  Proof.
    intros specs S0 cfg [_ Hmethods] Hcalls Hinv Hsteps.
    set (Local := fun sp e S => call_ok CT receiver rt0 sp /\ ref_call_local sp e S).
    assert (Hstart : indexed_guar_inv inv Local specs
      (mkPicoPoolConfig S0 (map call_control specs))).
    { clear Hsteps. split; [exact Hinv |]. simpl.
      induction Hcalls as [| sp specs Hsp _ IH]; simpl; constructor;
        [| exact IH].
      split; [exact Hsp |].
      destruct Hsp as (Hfind & _).
      destruct (Hmethods _ _ Hfind)
        as [(qc & zs & s_args & Trecv & Tv & sG' & mt & Hrest) | Hderivm].
      - left. exists qc, zs, s_args, Tv.
        split; [apply RPh_Call | exists Trecv, sG', mt; exact Hrest].
      - right. split; [exact Hderivm | apply DcPh_Call]. }
    destruct (indexed_guar_pool_steps CT inv guar Local
      (fun sp e S e' S' Hi Hl Hs =>
         match ref_call_own_step sp e S e' S' (proj1 Hl) Hi (proj2 Hl) Hs with
         | conj Hg Hl' => conj Hg (conj (proj1 Hl) Hl')
         end)
      (fun S S' _ Hg => proj2 Hg)
      (fun sp e S S' Hl Hg =>
         conj (proj1 Hl) (ref_call_local_stable sp e S S' (proj2 Hl) Hg))
      specs _ cfg Hstart Hsteps) as [Hinv' Hlocal].
    split; [exact Hinv' |].
    eapply Forall2_impl; [| exact Hlocal].
    intros sp e [(Hfind & Hy & Hx) Hl] rG V ->.
    destruct Hl as
      [(qc & zs & s_args & Tv & Hphase & Trecv & sG' & mt & Hrest)
      | ((sGb & mtb & Hderivb & Htypedb & Hwfb) & Hphase)].
    - left. split.
      + exists qc; exists zs; exists s_args; exists Trecv; exists Tv;
          exists sG'; exists mt. exact Hrest.
      + inversion Hphase; subst; [| contradiction].
        exists l. split; [| assumption].
        unfold runtime_getVal, set_vars. cbn [vars].
        apply update_same. exact Hx.
    - right.
      inversion Hphase as [V1 Heq | n V1 e1 Hbsteps Heq]; subst.
      destruct (dc_classify CT D receiver h0 (cs_def sp) sGb mtb rt0 fs0
        (cs_caller sp) (cs_target sp) Htable Hderivb Htypedb Hwfb Hobj0
        n V1 _ Hbsteps)
        as [Hrunning | [Hfailed | (rGamma1 & Heval & Hchain)]].
      + destruct Hrunning as (rG0 & s & V2 & K2 & Heq & _). discriminate.
      + destruct Hfailed as (r & rG0 & V2 & Heq & Hr).
        injection Heq as <- <- <-. contradiction.
      + inversion Hchain; subst.
        exists retval. split; [exists rGamma1; split; assumption |].
        unfold runtime_getVal, set_vars. cbn [vars].
        apply update_same. exact Hx.
  Qed.
End ref_value_class.

(** ** The class with a cached view is a semantic value class *)

Lemma rv_method_is_ref_cache_method :
  @is_ref_cache_method rv_CT (fun _ => False) rv_receiver rv_heap
    rv_cache_field rv_view_class [Iot rv_receiver]
    (mkruntime_type Imm_r rv_class) rv_method_def.
Proof.
  exists Imm_c; exists [cache_receiver]; exists SSkip; exists rv_receiver_type;
    exists rv_view_type; exists rv_senv3; exists AbstractState.
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [apply DS_Skip |].
  split; [apply ST_Skip; exact rv_wf_env3 |].
  split; [exact rv_frame_config_wf |].
  split; [| reflexivity].
  intros rGamma1 Heval. inversion Heval; subst.
  split; [reflexivity | simpl; unfold cache_result; lia].
Qed.

Lemma rv_class_methods :
  forall mn md,
    FindMethodWithName rv_CT rv_class mn md -> md = rv_method_def.
Proof.
  intros mn md Hfind.
  inversion Hfind as
    [CT C def own m mdef Hclass Hown Hget
    | CT C def parent m mdef own Hclass Hown Hnot Hsuper Hparent]; subst.
  - assert (def = rv_class_def)
      by (unfold find_class, gget in Hclass; simpl in Hclass; congruence).
    subst def.
    unfold gget_method in Hget. simpl in Hget.
    repeat match type of Hget with
           | context [if ?c then _ else _] => destruct c
           end;
      try discriminate; injection Hget as <-; reflexivity.
  - assert (def = rv_class_def)
      by (unfold find_class, gget in Hclass; simpl in Hclass; congruence).
    subst def.
    simpl in Hsuper. injection Hsuper as <-.
    inversion Hparent as
      [CT C def own m mdef Hclass0 Hown0 Hget0
      | CT C def parent m mdef own Hclass0 Hown0 Hnot0 Hsuper0 Hparent0]; subst.
    + assert (def = pico_hash_witness_root_def)
        by (unfold find_class, gget in Hclass0; simpl in Hclass0; congruence).
      subst def. unfold gget_method in Hget0. simpl in Hget0. discriminate.
    + assert (def = pico_hash_witness_root_def)
        by (unfold find_class, gget in Hclass0; simpl in Hclass0; congruence).
      subst def. simpl in Hsuper0. discriminate.
Qed.

Theorem rv_class_is_ref_value_class :
  @pico_ref_value_class rv_CT (fun _ => False) rv_receiver rv_heap
    rv_cache_field rv_view_class [Iot rv_receiver]
    (mkruntime_type Imm_r rv_class)
    (fun C f => C = rv_class /\ f = rv_cache_field).
Proof.
  split; [exact rv_class_transitive |].
  intros mn md Hfind. rewrite (rv_class_methods mn md Hfind).
  left. exact rv_method_is_ref_cache_method.
Qed.

(** Any number of threads calling the accessor: the invariant is preserved
    and each call returns a view whose owner is the receiver. *)
Theorem rv_class_calls_sound :
  forall specs cfg,
    Forall (call_ok rv_CT rv_receiver (mkruntime_type Imm_r rv_class)) specs ->
    @pico_pool_steps history_cache_memory_model rv_CT
      (mkPicoPoolConfig rv_state (map call_control specs)) cfg ->
    ref_inv rv_CT rv_receiver rv_heap rv_cache_field rv_view_class
      [Iot rv_receiver] (pool_state cfg) /\
    Forall2
      (fun sp e =>
         forall rG V,
           e = CoreDone OK rG V ->
           @ref_call_result rv_CT (fun _ => False) rv_receiver rv_heap
             rv_cache_field rv_view_class [Iot rv_receiver]
             (mkruntime_type Imm_r rv_class) (pool_state cfg) sp rG)
      specs (pool_threads cfg).
Proof.
  intros specs cfg Hcalls Hsteps.
  eapply (@ref_value_class_sound history_cache_memory_model rv_CT
    (fun _ => False) rv_receiver rv_heap rv_cache_field rv_view_class
    [Iot rv_receiver] (mkruntime_type Imm_r rv_class) [Null_a]
    (fun C f => C = rv_class /\ f = rv_cache_field)
    rv_footprint_immutable (fun mdef (Hfalse : False) => match Hfalse with end)
    eq_refl specs rv_state cfg rv_class_is_ref_value_class Hcalls
    rv_initial_inv Hsteps).
Qed.
