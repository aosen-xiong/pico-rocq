From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping Bigstep Properties Reachability
  ViewpointAdaptation.
Require Import Examples.PicoIfZeroCache.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoCacheTyping
  PICOBridge.PicoCoreLanguage PICOBridge.PicoCoreFrame
  PICOBridge.PicoCoreInvariant
  PICOBridge.PicoDerivationNoninterference PICOBridge.PicoDerivationSmallStep
  PICOBridge.PicoDerivationPrefix PICOBridge.PicoSemanticConcurrency.

(** * Reference-Valued Caches

    A reference cache holds [null] until some thread stores a reference to a
    freshly allocated object.  Different threads may allocate different
    objects, so the cached value is not determined; what is determined is
    what such an object represents.  A cached reference is valid when it
    points to an immutable object of the view class whose abstract fields
    hold the values the initializer computes in the reference heap, and whose
    histories for those fields contain nothing else.

    Validity depends on the heap, so it is part of the shared invariant: every
    value in the history of the cache field is [null] or a valid reference.
    The invariant is preserved by every step of every thread except a write
    of an invalid value to the cache field. *)

Section ref_cache.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table).
  Context (receiver : Loc) (h0 : heap).
  Context (cf : var) (Cv : class_name) (vals0 : list value).

  Let footprint := reachable_abs CT h0 receiver.

  Hypothesis Himm : forall l, footprint l ->
    exists C vals,
      runtime_getObj h0 l = Some (mkObj (mkruntime_type Imm_r C) vals).

  (** ** Valid references *)
  Definition view_ok (S : pico_core_state) (l : Loc) : Prop :=
    exists fs,
      runtime_getObj (pcs_heap S) l =
        Some (mkObj (mkruntime_type Imm_r Cv) fs) /\
      forall f,
        abstract_field CT Cv f ->
        nth_error fs f = nth_error vals0 f /\
        forall v0 w,
          nth_error vals0 f = Some v0 ->
          List.In w (values_written_to (pcs_weak S) (l, f)) ->
          w = v0.

  Definition val_ok (S : pico_core_state) (v : value) : Prop :=
    v = Null_a \/ exists l, v = Iot l /\ view_ok S l.

  (** ** The shared invariant *)
  Definition ref_inv (S : pico_core_state) : Prop :=
    heap_wm_type_agree (pcs_heap S) (pcs_weak S) /\
    footprint_state CT footprint h0 S /\
    (exists o, runtime_getObj (pcs_heap S) receiver = Some o) /\
    forall v,
      List.In v (values_written_to (pcs_weak S) (receiver, cf)) ->
      val_ok S v.

  Lemma getObj_update_field_same :
    forall h l rt fs f v,
      runtime_getObj h l = Some (mkObj rt fs) ->
      runtime_getObj (update_field h l f v) l =
        Some (mkObj rt (update f v fs)).
  Proof.
    intros h l rt fs f v Hobj.
    unfold update_field. rewrite Hobj. simpl.
    apply runtime_getObj_update_same. eapply runtime_getObj_dom. exact Hobj.
  Qed.

  Lemma imm_abstract_not_assignable :
    forall C f a,
      abstract_field CT C f ->
      sf_assignability_rel CT C f a ->
      runtime_vpa_assignability Imm_r a = Assignable ->
      False.
  Proof.
    intros C f a [_ [Hrda | Hfinal]] Hassign Hrun.
    - have Heq := sf_assignability_deterministic_rel CT C f a RDA Hassign Hrda.
      subst a. discriminate.
    - have Heq := sf_assignability_deterministic_rel CT C f a Final Hassign Hfinal.
      subst a. discriminate.
  Qed.

  (** A valid reference stays valid across every step of every thread. *)
  Lemma view_ok_step :
    forall e S e' S' l,
      heap_wm_type_agree (pcs_heap S) (pcs_weak S) ->
      view_ok S l ->
      pico_core_step CT e S e' S' ->
      view_ok S' l.
  Proof.
    intros e S e' S' l Hagree (fs & Hobj & Hfields) Hstep.
    inversion Hstep; subst; try (exists fs; split; assumption).
    - (* field write *)
      simpl in *.
      destruct (Nat.eq_dec loc_x l) as [-> | Hneq].
      + match goal with
        | Ho : runtime_getObj h l = Some ?ob |- _ =>
            rewrite Hobj in Ho; injection Ho as <-
        end.
        exists (update f val_y fs).
        split; [apply getObj_update_field_same; exact Hobj |].
        intros g Habs.
        assert (Hgf : f <> g).
        { intros ->. eapply imm_abstract_not_assignable; eassumption. }
        destruct (Hfields g Habs) as [Hval Hhist].
        split; [rewrite update_diff; assumption |].
        intros v0 w Hv0 Hin. eapply Hhist; [exact Hv0 |].
        match goal with
        | Hw : wm_write _ _ _ _ _ _ |- _ => destruct Hw as [-> _]
        end.
        unfold values_written_to in *.
        rewrite history_of_append_write_other in Hin; [exact Hin |].
        intros Heq. injection Heq as Heq. congruence.
      + exists fs.
        split; [rewrite runtime_getObj_update_field_other_general; assumption |].
        intros g Habs. destruct (Hfields g Habs) as [Hval Hhist].
        split; [exact Hval |].
        intros v0 w Hv0 Hin. eapply Hhist; [exact Hv0 |].
        match goal with
        | Hw : wm_write _ _ _ _ _ _ |- _ => destruct Hw as [-> _]
        end.
        unfold values_written_to in *.
        rewrite history_of_append_write_other in Hin; [exact Hin |].
        intros Heq. injection Heq as Heq _. congruence.
    - (* allocation *)
      simpl in *.
      have Hl := runtime_getObj_dom _ _ _ Hobj.
      exists fs.
      split; [rewrite runtime_getObj_last2; assumption |].
      intros g Habs. destruct (Hfields g Habs) as [Hval Hhist].
      split; [exact Hval |].
      intros v0 w Hv0 Hin. eapply Hhist; [exact Hv0 |].
      unfold values_written_to, history_of, pico_core_alloc_weak in Hin.
      simpl in Hin.
      destruct Hagree as [Hlen _].
      assert (Hneq : Nat.eqb l (length (wm_objs sigma)) = false)
        by (apply Nat.eqb_neq; lia).
      rewrite Hneq in Hin. exact Hin.
  Qed.

  Lemma val_ok_step :
    forall e S e' S' v,
      heap_wm_type_agree (pcs_heap S) (pcs_weak S) ->
      val_ok S v ->
      pico_core_step CT e S e' S' ->
      val_ok S' v.
  Proof.
    intros e S e' S' v Hagree [-> | (l & -> & Hview)] Hstep.
    - left. reflexivity.
    - right. exists l. split; [reflexivity |].
      eapply view_ok_step; eassumption.
  Qed.

  (** A value new in the cache field's history was written there by this
      step. *)
  Lemma cache_history_step :
    forall e S e' S' v,
      ref_inv S ->
      pico_core_step CT e S e' S' ->
      List.In v (values_written_to (pcs_weak S') (receiver, cf)) ->
      List.In v (values_written_to (pcs_weak S) (receiver, cf)) \/
      exists rGamma x y V K,
        e = CoreRun rGamma (SFldWrite x cf y) V K /\
        runtime_getVal rGamma x = Some (Iot receiver) /\
        runtime_getVal rGamma y = Some v.
  Proof.
    intros e S e' S' v (Hagree & _ & [o Hrecv] & _) Hstep Hin.
    inversion Hstep; subst; try (left; exact Hin).
    - (* field write *)
      simpl in *.
      destruct (Nat.eq_dec loc_x receiver) as [-> | Hneq];
        [destruct (Nat.eq_dec f cf) as [-> | Hneqf] |].
      + match goal with
        | Hw : wm_write _ _ _ _ _ _ |- _ =>
            have Hhist := wm_write_history_same _ _ _ _ _ _ Hw
        end.
        unfold values_written_to in *. rewrite Hhist in Hin.
        rewrite map_app in Hin. apply in_app_or in Hin.
        destruct Hin as [Hold | [<- | []]]; [left; exact Hold |].
        right. do 5 eexists. split; [reflexivity |]. split; eassumption.
      + left.
        match goal with
        | Hw : wm_write _ _ _ _ _ _ |- _ => destruct Hw as [-> _]
        end.
        unfold values_written_to in *.
        rewrite history_of_append_write_other in Hin; [exact Hin |].
        intros Heq. injection Heq as Heq. congruence.
      + left.
        match goal with
        | Hw : wm_write _ _ _ _ _ _ |- _ => destruct Hw as [-> _]
        end.
        unfold values_written_to in *.
        rewrite history_of_append_write_other in Hin; [exact Hin |].
        intros Heq. injection Heq as Heq _. congruence.
    - (* allocation *)
      left. simpl in *.
      have Hl := runtime_getObj_dom _ _ _ Hrecv.
      unfold values_written_to, history_of, pico_core_alloc_weak in Hin.
      simpl in Hin.
      destruct Hagree as [Hlen _].
      assert (Hneq : Nat.eqb receiver (length (wm_objs sigma)) = false)
        by (apply Nat.eqb_neq; lia).
      rewrite Hneq in Hin. exact Hin.
  Qed.

  (** Every step preserves the invariant, provided a write to the cache
      field stores a valid value. *)
  Theorem ref_inv_step :
    forall e S e' S',
      ref_inv S ->
      pico_core_step CT e S e' S' ->
      (forall rGamma x y V K v,
         e = CoreRun rGamma (SFldWrite x cf y) V K ->
         runtime_getVal rGamma x = Some (Iot receiver) ->
         runtime_getVal rGamma y = Some v ->
         val_ok S v) ->
      ref_inv S'.
  Proof.
    intros e S e' S' Hinv Hstep Hwrite.
    pose proof Hinv as (Hagree & [Habs Hst] & [o Hrecv] & Hhist).
    destruct S as [h sigma]. simpl in *.
    destruct (core_step_preserves_footprint CT footprint h0 Himm e h sigma e' S'
      Habs Hagree Hstep) as [Habs' Hst'].
    split; [eapply (pico_core_step_preserves_heap_wm_type_agree CT e
      (mkPicoCoreState h sigma)); eassumption |].
    split; [split; [exact Habs' | exact (Hst' Hst)] |].
    split.
    - destruct (pico_core_step_preserves_heap_types CT e _ e' S' Hstep)
        as [_ Hty].
      specialize (Hty receiver (rt_type o)). simpl in Hty.
      unfold r_type in Hty. rewrite Hrecv in Hty. specialize (Hty eq_refl).
      destruct (runtime_getObj (pcs_heap S') receiver) as [o' |];
        [eauto | discriminate].
    - intros v Hin.
      destruct (cache_history_step e (mkPicoCoreState h sigma) e' S' v Hinv
        Hstep Hin) as [Hold | (rG & x & y & V & K & -> & Hx & Hy)].
      + eapply (val_ok_step _ (mkPicoCoreState h sigma));
          [exact Hagree | exact (Hhist v Hold) | exact Hstep].
      + eapply (val_ok_step _ (mkPicoCoreState h sigma));
          [exact Hagree | | exact Hstep].
        eapply Hwrite; [reflexivity | exact Hx | exact Hy].
  Qed.
End ref_cache.

(** * The Cache-Method Judgment for Reference Caches

    The method reads the cache field once into a local.  If the local is
    [null] it runs derivation code that computes the constructor arguments,
    allocates one object of the view class, stores the reference in the cache
    field, and returns it; otherwise it returns the reference it read.

    Any number of concurrent calls preserve the invariant, and every call
    that returns normally returns a valid reference. *)

Section ref_cache_method.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table) (D : method_def -> Prop).
  Context (receiver : Loc) (h0 : heap).
  Context (cf : var) (Cv : class_name) (vals0 : list value).
  Context (qc : q_c) (zs : list var) (s_args : stmt).
  Context (mc : method_name) (mdef : method_def).
  Context (Trecv Tv : qualified_type) (sGamma' : s_env) (mt : method_scope).
  Context (rt0 : runtime_type) (fs0 : fields_mapping).
  Context (caller : r_env) (x y : var).

  Let footprint := reachable_abs CT h0 receiver.
  Let rho1 := mkr_env [Iot receiver].
  Let rho2 := mkr_env [Iot receiver; Null_a].
  Definition env_ref (v : value) : r_env := mkr_env [Iot receiver; v; Null_a].
  Let rho3 := env_ref Null_a.
  Let sGamma3 : s_env := [Trecv; Tv; Tv].

  Let read_stmt : stmt := SVarAss cache_tmp (EField cache_receiver cf).
  Let new_stmt : stmt := SNew cache_tmp qc Cv zs.
  Let write_stmt : stmt := SFldWrite cache_receiver cf cache_tmp.
  Let final_stmt : stmt := SVarAss cache_result (EVar cache_tmp).
  Let miss : stmt := SSeq s_args (SSeq new_stmt write_stmt).
  Let branch : stmt := SIfZero cache_tmp miss SSkip.
  Let core : stmt := SSeq read_stmt (SSeq branch final_stmt).
  Definition ref_cache_body : stmt :=
    SSeq (SLocal Tv cache_tmp) (SSeq (SLocal Tv cache_result) core).
  Let Kc : pico_core_cont := [KCall caller x cache_result].
  Let Kt : pico_core_cont :=
    KSeq (SSeq new_stmt write_stmt) :: KSeq final_stmt :: Kc.

  (** ** The judgment *)
  Hypothesis Himm : forall l, footprint l ->
    exists C vals,
      runtime_getObj h0 l = Some (mkObj (mkruntime_type Imm_r C) vals).
  Hypothesis Hbody : mbody_stmt (mbody mdef) = ref_cache_body.
  Hypothesis Hret : mreturn (mbody mdef) = cache_result.
  Hypothesis Hdefault : default_value Tv = Null_a.
  Hypothesis Htable : derivation_table CT D.
  Hypothesis Hderiv : deriv_stmt CT D sGamma3 s_args sGamma'.
  Hypothesis Htyped : stmt_typing CT sGamma3 mt s_args sGamma'.
  Hypothesis Hwf3 : wf_r_config CT sGamma3 rho3 h0.

  (** Evaluated sequentially in the reference heap, the argument code
      produces the constructor arguments and keeps the frame's locals. *)
  Hypothesis Hargs :
    forall rGamma1,
      eval_stmt CT rho3 h0 s_args OK rGamma1 h0 ->
      runtime_lookup_list rGamma1 zs = Some vals0 /\
      cache_result < dom (vars rGamma1).

  (** The view is allocated immutable. *)
  Hypothesis Hobj0 : runtime_getObj h0 receiver = Some (mkObj rt0 fs0).
  Hypothesis Hqimm :
    vpa_mutability_object_creation (rqtype rt0) qc = Imm_r.
  Hypothesis Hfind : FindMethodWithName CT (rctype rt0) mc mdef.
  Hypothesis Hy : runtime_getVal caller y = Some (Iot receiver).

  Notation vok := (view_ok CT Cv vals0).
  Notation valok := (val_ok CT Cv vals0).
  Notation inv := (ref_inv CT receiver h0 cf Cv vals0).

  Definition init_result (rGamma1 : r_env) : Prop :=
    eval_stmt CT rho3 h0 s_args OK rGamma1 h0.

  Lemma ref_receiver_in_footprint : footprint receiver.
  Proof.
    apply reachable_abs_heap. eapply runtime_getObj_dom. exact Hobj0.
  Qed.

  Lemma ref_footprint_dom :
    forall l, footprint l ->
      exists rt fs, runtime_getObj h0 l = Some (mkObj rt fs).
  Proof.
    intros l Hl. destruct (Himm l Hl) as (C & vals & Hobj). eauto.
  Qed.

  Lemma rho3_footprint : env_in footprint rho3.
  Proof.
    intros z l Hz.
    destruct z as [| [| [| z]]]; simpl in Hz; try discriminate.
    - injection Hz as <-. exact ref_receiver_in_footprint.
    - destruct z; discriminate.
  Qed.

  Lemma init_result_this :
    forall rGamma1,
      init_result rGamma1 ->
      runtime_getVal rGamma1 cache_receiver = Some (Iot receiver).
  Proof.
    intros rGamma1 Heval.
    have Hthis := eval_stmt_preserves_receiver_addr_typed CT sGamma3 mt
      rho3 h0 s_args sGamma' rGamma1 h0 receiver Htyped Heval eq_refl.
    unfold get_this_var_mapping in Hthis.
    unfold runtime_getVal, cache_receiver.
    destruct (vars rGamma1) as [| [| l | k0] rest]; try discriminate.
    injection Hthis as ->. reflexivity.
  Qed.

  Lemma inv_receiver_type :
    forall S, inv S ->
      exists fs, runtime_getObj (pcs_heap S) receiver = Some (mkObj rt0 fs).
  Proof.
    intros S (_ & [Habs _] & _).
    destruct (Habs receiver ref_receiver_in_footprint)
      as (rt & fs1 & fs2 & Hobj1 & Hobj2 & _).
    rewrite Hobj0 in Hobj1. injection Hobj1 as <- <-. eauto.
  Qed.

  (** ** After the argument code

      The controls that follow the end of the argument code, described
      without reference to the state. *)
  Inductive post_chain : pico_core_expr -> Prop :=
    | Post_NewSeq : forall r V,
        post_chain (CoreRun r (SSeq new_stmt write_stmt) V (KSeq final_stmt :: Kc))
    | Post_New : forall r V,
        post_chain (CoreRun r new_stmt V
          (KSeq write_stmt :: KSeq final_stmt :: Kc))
    | Post_AfterNew : forall r V,
        post_chain (CoreRun r SSkip V
          (KSeq write_stmt :: KSeq final_stmt :: Kc))
    | Post_Write : forall r V,
        post_chain (CoreRun r write_stmt V (KSeq final_stmt :: Kc))
    | Post_AfterWrite : forall r V,
        post_chain (CoreRun r SSkip V (KSeq final_stmt :: Kc))
    | Post_Final : forall r V,
        post_chain (CoreRun r final_stmt V Kc)
    | Post_AfterFinal : forall r V,
        post_chain (CoreRun r SSkip V Kc)
    | Post_Resume : forall r V,
        post_chain (CoreRun r SSkip V [])
    | Post_Done : forall res r V,
        post_chain (CoreDone res r V).

  Lemma post_chain_step :
    forall c S c' S',
      post_chain c -> pico_core_step CT c S c' S' -> post_chain c'.
  Proof.
    intros c S c' S' Hpost Hstep.
    destruct Hpost; inversion Hstep; subst; constructor.
  Qed.

  Lemma post_chain_steps :
    forall k c e,
      footprint_steps CT footprint h0 k c e -> post_chain c -> post_chain e.
  Proof.
    intros k c e Hsteps. induction Hsteps; intros Hpost.
    - exact Hpost.
    - apply IHHsteps. eapply post_chain_step; eassumption.
  Qed.

  Lemma post_chain_no_suffix :
    forall r s V Kabove,
      post_chain (CoreRun r s V (Kabove ++ Kt)) -> False.
  Proof.
    intros r s V Kabove Hpost.
    inversion Hpost as
      [r0 V0 Hk | r0 V0 Hk | r0 V0 Hk | r0 V0 Hk | r0 V0 Hk | r0 V0 Hk
       | r0 V0 Hk | r0 V0 Hk | ];
      destruct Kabove as [| a [| b [| c [| d Kabove]]]];
      simpl in *; try discriminate;
      match goal with
      | Heq : _ = _ :: _ |- _ => inversion Heq
      | Heq : _ :: _ = _ |- _ => inversion Heq
      | Heq : [] = _ :: _ |- _ => discriminate Heq
      end.
  Qed.

  Lemma exit_steps :
    forall k rGamma1 V1 e,
      footprint_steps CT footprint h0 k (CoreRun rGamma1 SSkip V1 Kt) e ->
      (k = 0 /\ e = CoreRun rGamma1 SSkip V1 Kt) \/ post_chain e.
  Proof.
    intros k rGamma1 V1 e Hsteps.
    inversion Hsteps as [| n e0 S0 e1 S1 e2 HS Hstep Htail]; subst.
    - left. split; reflexivity.
    - right. eapply post_chain_steps; [exact Htail |].
      inversion Hstep; subst. constructor.
  Qed.

  (** A control reached by running the argument code, still above its base
      continuation, is either its end, with the big-step result, or is
      executing derivation code. *)
  Lemma init_classify :
    forall n V rGamma s V' Kabove,
      footprint_steps CT footprint h0 n (CoreRun rho3 s_args V Kt)
        (CoreRun rGamma s V' (Kabove ++ Kt)) ->
      (s = SSkip /\ Kabove = [] -> init_result rGamma) /\
      (~ (s = SSkip /\ Kabove = []) -> forall x' f y', s <> SFldWrite x' f y').
  Proof.
    intros n V rGamma s V' Kabove Hsteps.
    destruct (deriv_prefix CT D footprint h0 Htable ref_footprint_dom n n rho3
      s_args V Kt sGamma3 sGamma' mt _ (le_n n) Hsteps Hderiv Htyped Hwf3
      rho3_footprint)
      as [Hrun | [(rGamma1 & V1 & k & _ & Heval & _ & Htail) | Hfail]].
    - destruct Hrun as (rG & s1 & V1 & K1 & Heq & (Ka & HK & Hnotexit) & Hnow & _).
      injection Heq as <- <- <- <-.
      apply app_inv_tail in HK. subst Ka.
      split; [intros Hexit; contradiction | intros _; exact Hnow].
    - destruct (exit_steps k rGamma1 V1 _ Htail) as [[_ Heq] | Hpost].
      + injection Heq as -> -> -> HK.
        assert (HKa : Kabove = []).
        { apply (app_inv_tail Kt Kabove []). exact HK. }
        subst Kabove.
        split; [intros _; exact Heval | intros Hnot; exfalso; apply Hnot; auto].
      + exfalso. eapply post_chain_no_suffix. exact Hpost.
    - destruct Hfail as (r & rG & V1 & Heq & _). discriminate.
  Qed.

  (** ** The phases of a call

      The assertion about one call, relative to the shared state. *)
  Definition holds_view (S : pico_core_state) (rG : r_env) (z : var) (l : Loc)
      : Prop :=
    runtime_getVal rG z = Some (Iot l) /\ vok S l.

  Inductive ref_phase (S : pico_core_state) : pico_core_expr -> Prop :=
    | RPh_Call : forall V,
        ref_phase S (CoreRun caller (SCall x mc y []) V [])
    | RPh_Body : forall V,
        ref_phase S (CoreRun rho1 ref_cache_body V Kc)
    | RPh_LocalTmp : forall V,
        ref_phase S (CoreRun rho1 (SLocal Tv cache_tmp) V
          (KSeq (SSeq (SLocal Tv cache_result) core) :: Kc))
    | RPh_AfterLocalTmp : forall V,
        ref_phase S (CoreRun rho2 SSkip V
          (KSeq (SSeq (SLocal Tv cache_result) core) :: Kc))
    | RPh_ResultSeq : forall V,
        ref_phase S (CoreRun rho2 (SSeq (SLocal Tv cache_result) core) V Kc)
    | RPh_LocalResult : forall V,
        ref_phase S (CoreRun rho2 (SLocal Tv cache_result) V (KSeq core :: Kc))
    | RPh_AfterLocalResult : forall V,
        ref_phase S (CoreRun rho3 SSkip V (KSeq core :: Kc))
    | RPh_Core : forall V,
        ref_phase S (CoreRun rho3 core V Kc)
    | RPh_Read : forall V,
        ref_phase S (CoreRun rho3 read_stmt V
          (KSeq (SSeq branch final_stmt) :: Kc))
    | RPh_AfterRead : forall V v,
        valok S v ->
        ref_phase S (CoreRun (env_ref v) SSkip V
          (KSeq (SSeq branch final_stmt) :: Kc))
    | RPh_BranchSeq : forall V v,
        valok S v ->
        ref_phase S (CoreRun (env_ref v) (SSeq branch final_stmt) V Kc)
    | RPh_Branch : forall V v,
        valok S v ->
        ref_phase S (CoreRun (env_ref v) branch V (KSeq final_stmt :: Kc))
    | RPh_Miss : forall V,
        ref_phase S (CoreRun rho3 miss V (KSeq final_stmt :: Kc))
    | RPh_Init : forall n V0 rG s V Kabove,
        footprint_steps CT footprint h0 n (CoreRun rho3 s_args V0 Kt)
          (CoreRun rG s V (Kabove ++ Kt)) ->
        ~ (s = SSkip /\ Kabove = []) ->
        ref_phase S (CoreRun rG s V (Kabove ++ Kt))
    | RPh_Exit : forall rG V,
        init_result rG ->
        ref_phase S (CoreRun rG SSkip V Kt)
    | RPh_NewSeq : forall rG V,
        init_result rG ->
        ref_phase S (CoreRun rG (SSeq new_stmt write_stmt) V
          (KSeq final_stmt :: Kc))
    | RPh_New : forall rG V,
        init_result rG ->
        ref_phase S (CoreRun rG new_stmt V
          (KSeq write_stmt :: KSeq final_stmt :: Kc))
    | RPh_AfterNew : forall rG V l,
        holds_view S rG cache_tmp l ->
        runtime_getVal rG cache_receiver = Some (Iot receiver) ->
        ref_phase S (CoreRun rG SSkip V
          (KSeq write_stmt :: KSeq final_stmt :: Kc))
    | RPh_Write : forall rG V l,
        holds_view S rG cache_tmp l ->
        runtime_getVal rG cache_receiver = Some (Iot receiver) ->
        ref_phase S (CoreRun rG write_stmt V (KSeq final_stmt :: Kc))
    | RPh_AfterWrite : forall rG V l,
        holds_view S rG cache_tmp l ->
        ref_phase S (CoreRun rG SSkip V (KSeq final_stmt :: Kc))
    | RPh_Final : forall rG V l,
        holds_view S rG cache_tmp l ->
        ref_phase S (CoreRun rG final_stmt V Kc)
    | RPh_AfterFinal : forall rG V l,
        holds_view S rG cache_result l ->
        ref_phase S (CoreRun rG SSkip V Kc)
    | RPh_Resume : forall V l,
        vok S l ->
        ref_phase S
          (CoreRun (set_vars caller (update x (Iot l) (vars caller))) SSkip V [])
    | RPh_Done : forall V l,
        vok S l ->
        ref_phase S
          (CoreDone OK (set_vars caller (update x (Iot l) (vars caller))) V)
    | RPh_Failed : forall r rG V,
        r <> OK ->
        ref_phase S (CoreDone r rG V).

  (** The assertion is stable when valid references stay valid. *)
  Lemma ref_phase_mono :
    forall S S' e,
      (forall l, vok S l -> vok S' l) ->
      ref_phase S e ->
      ref_phase S' e.
  Proof.
    intros S S' e Hmono Hphase.
    assert (Hval : forall v, valok S v -> valok S' v).
    { intros v [-> | (l & -> & Hl)]; [left; reflexivity |].
      right. exists l. split; [reflexivity | exact (Hmono l Hl)]. }
    assert (Hhold : forall rG z l, holds_view S rG z l -> holds_view S' rG z l).
    { intros rG z l [Hz Hl]. split; [exact Hz | exact (Hmono l Hl)]. }
    destruct Hphase; try (econstructor; eauto; fail).
  Qed.

  Lemma init_arrive :
    forall S n V0 rG s V K1,
      footprint_steps CT footprint h0 n (CoreRun rho3 s_args V0 Kt)
        (CoreRun rG s V (K1 ++ Kt)) ->
      ref_phase S (CoreRun rG s V (K1 ++ Kt)).
  Proof.
    intros S n V0 rG s V K1 Hsteps.
    assert (Hexit : (s = SSkip /\ K1 = []) \/ ~ (s = SSkip /\ K1 = [])).
    { destruct s; try (right; intros [Hs _]; discriminate).
      destruct K1; [left; split; reflexivity | right; intros [_ HK]; discriminate]. }
    destruct Hexit as [[-> ->] | Hnot].
    - simpl. apply RPh_Exit.
      exact (proj1 (init_classify n V0 rG SSkip V [] Hsteps) (conj eq_refl eq_refl)).
    - eapply RPh_Init; eassumption.
  Qed.

  Lemma step_done_ok :
    forall rG s V K S r' V' S',
      pico_core_step CT (CoreRun rG s V K) S (CoreDone OK r' V') S' ->
      s = SSkip /\ K = [].
  Proof.
    intros rG s V K S r' V' S' Hstep.
    inversion Hstep; subst. split; reflexivity.
  Qed.

  (** A write to the cache field by a call stores a valid reference. *)
  Lemma ref_phase_write_ok :
    forall S rG x' y' V K v,
      ref_phase S (CoreRun rG (SFldWrite x' cf y') V K) ->
      runtime_getVal rG y' = Some v ->
      valok S v.
  Proof.
    intros S rG x' y' V K v Hphase Hy'.
    inversion Hphase; subst.
    - match goal with
      | Hsteps : footprint_steps _ _ _ _ _ _, Hnot : ~ (_ /\ _) |- _ =>
          exfalso;
          exact (proj2 (init_classify _ _ _ _ _ _ Hsteps) Hnot _ _ _ eq_refl)
      end.
    - match goal with
      | Hh : holds_view S rG cache_tmp ?l |- _ =>
          destruct Hh as [Htmp Hl]; rewrite Htmp in Hy'; injection Hy' as <-;
          right; exists l; split; [reflexivity | exact Hl]
      end.
  Qed.

  (** One step of a call. *)
  Lemma ref_phase_step :
    forall e S e' S',
      inv S ->
      ref_phase S e ->
      pico_core_step CT e S e' S' ->
      (forall l, vok S l -> vok S' l) ->
      ref_phase S' e'.
  Proof.
    intros e S e' S' Hinv Hphase Hstep Hmono.
    assert (Hval : forall v, valok S v -> valok S' v).
    { intros v [-> | (l & -> & Hl)]; [left; reflexivity |].
      right. exists l. split; [reflexivity | exact (Hmono l Hl)]. }
    assert (Hhold : forall rG z l, holds_view S rG z l -> holds_view S' rG z l).
    { intros rG z l [Hz Hl]. split; [exact Hz | exact (Hmono l Hl)]. }
    destruct Hphase.
    - (* call *)
      inversion Hstep; subst; [| congruence].
      match goal with
      | Hyl : runtime_getVal caller y = Some (Iot ?l),
        Hb : r_basetype _ ?l = Some ?C,
        Hf : FindMethodWithName CT ?C mc ?md,
        Ha : runtime_lookup_list caller [] = Some ?vs |- _ =>
          rewrite Hy in Hyl; injection Hyl as <-;
          destruct (inv_receiver_type _ Hinv) as [fsr Hobjr];
          simpl in Hobjr; unfold r_basetype in Hb; rewrite Hobjr in Hb;
          injection Hb as <-;
          have Hmd := find_method_with_name_deterministic CT _ _ _ _ Hf Hfind;
          subst md; simpl in Ha; injection Ha as <-
      end.
      rewrite Hbody Hret. apply RPh_Body.
    - inversion Hstep; subst. apply RPh_LocalTmp.
    - inversion Hstep; subst. rewrite Hdefault. apply RPh_AfterLocalTmp.
    - inversion Hstep; subst. apply RPh_ResultSeq.
    - inversion Hstep; subst. apply RPh_LocalResult.
    - inversion Hstep; subst. rewrite Hdefault. apply RPh_AfterLocalResult.
    - inversion Hstep; subst. apply RPh_Core.
    - inversion Hstep; subst. apply RPh_Read.
    - (* the read of the cache field *)
      inversion Hstep; subst.
      + match goal with
        | Hyl : runtime_getVal rho3 cache_receiver = Some (Iot ?l),
          Hr : wm_read _ _ (?l, cf) _ _ |- _ =>
            simpl in Hyl; injection Hyl as <-;
            destruct (wm_read_from_history _ _ _ _ _ Hr) as (msg & Hin & <-)
        end.
        apply (RPh_AfterRead _ V' (msg_val msg)).
        destruct Hinv as (_ & _ & _ & Hhist). apply Hhist.
        unfold values_written_to. apply in_map. exact Hin.
      + match goal with
        | Hn : runtime_getVal rho3 cache_receiver = Some Null_a |- _ =>
            simpl in Hn; discriminate
        end.
    - inversion Hstep; subst. apply RPh_BranchSeq. auto.
    - inversion Hstep; subst. apply RPh_Branch. auto.
    - (* branch on the value read *)
      match goal with Hv : valok S _ |- _ => rename Hv into Hvalid end.
      inversion Hstep; subst;
        match goal with
        | Hz : runtime_getVal (env_ref _) cache_tmp = Some _ |- _ =>
            simpl in Hz; injection Hz as ->
        end.
      + destruct Hvalid as [Hc | (l & Hc & _)]; discriminate.
      + destruct Hvalid as [Hc | (l & Hc & _)]; discriminate.
      + apply RPh_Miss.
      + destruct Hvalid as [Hc | (l & Hc & Hl)]; [discriminate |].
        injection Hc as <-.
        apply (RPh_AfterWrite _ _ _ loc). split; [reflexivity | auto].
    - (* enter the argument code *)
      inversion Hstep; subst.
      exact (init_arrive _ 0 V rho3 s_args V []
        (FootprintStepsRefl CT footprint h0 _)).
    - (* inside the argument code *)
      match goal with
      | Hsteps0 : footprint_steps _ _ _ _ _ _ |- _ => rename Hsteps0 into Hsteps
      end.
      match goal with
      | Hnot0 : ~ (_ /\ _) |- _ => rename Hnot0 into Hnot
      end.
      destruct (step_under_cont CT Kt rG s V Kabove S e' S' Hstep Hnot)
        as (e1' & Hstep1 & Heq).
      subst e'.
      assert (Hfs : footprint_state CT footprint h0 S)
        by (destruct Hinv as (_ & Hfs & _); exact Hfs).
      have Hsteps' := footprint_steps_snoc CT footprint h0 _ _ _ S _ S'
        Hsteps Hfs Hstep.
      destruct e1' as [rG' s' V'' K1' | r rG' V''].
      + exact (init_arrive _ _ _ _ _ _ _ Hsteps').
      + apply RPh_Failed. intros ->.
        destruct (step_done_ok _ _ _ _ _ _ _ _ Hstep1) as [Hs HK].
        apply Hnot. split; assumption.
    - inversion Hstep; subst. apply RPh_NewSeq. assumption.
    - inversion Hstep; subst. apply RPh_New. assumption.
    - (* the allocation *)
      match goal with Hr : init_result _ |- _ => rename Hr into Hres end.
      inversion Hstep; subst.
      have Hthis := init_result_this _ Hres.
      destruct (Hargs _ Hres) as [Hlook Hlen].
      destruct (inv_receiver_type _ Hinv) as [fsr Hobjr]. simpl in Hobjr.
      match goal with
      | Hx0 : runtime_getVal rG 0 = Some (Iot ?lt),
        Ha : runtime_lookup_list rG zs = Some ?vs,
        Hm : r_muttype h ?lt = Some ?q |- _ =>
          unfold cache_receiver in Hthis; rewrite Hthis in Hx0;
          injection Hx0 as <-;
          rewrite Hlook in Ha; injection Ha as <-;
          unfold r_muttype in Hm; rewrite Hobjr in Hm; injection Hm as <-
      end.
      cbn [rt_type]. rewrite Hqimm.
      apply (RPh_AfterNew _ _ _ (dom h)).
      + split.
        * unfold runtime_getVal, set_vars. cbn [vars].
          apply update_same. unfold cache_tmp, cache_result in *. lia.
        * exists vals0. split; [apply runtime_getObj_last |].
          intros f Habs. split; [reflexivity |].
          intros v0 w Hv0 Hin.
          unfold values_written_to, history_of, pico_core_alloc_weak in Hin.
          simpl in Hin.
          destruct Hinv as ([Hlen' _] & _). simpl in Hlen'.
          rewrite <- Hlen' in Hin. rewrite Nat.eqb_refl in Hin.
          rewrite Hv0 in Hin. simpl in Hin.
          destruct Hin as [<- | []]. reflexivity.
      + unfold runtime_getVal, set_vars. cbn [vars].
        rewrite update_diff; [exact Hthis | discriminate].
    - inversion Hstep; subst. eapply RPh_Write; eauto.
    - (* the cache write *)
      inversion Hstep; subst.
      + eapply RPh_AfterWrite. eauto.
      + congruence.
      + apply RPh_Failed. discriminate.
    - inversion Hstep; subst. eapply RPh_Final. eauto.
    - (* copy to the result *)
      match goal with Hh : holds_view S _ _ _ |- _ => destruct Hh as [Htmp Hl] end.
      inversion Hstep; subst.
      match goal with
      | Hval' : runtime_getVal rG cache_tmp = Some ?vy |- _ =>
          rewrite Htmp in Hval'; injection Hval' as <-
      end.
      apply (RPh_AfterFinal _ _ _ l). split; [| auto].
      unfold runtime_getVal, set_vars. cbn [vars].
      apply update_same.
      match goal with
      | Hold : runtime_getVal rG cache_result = Some _ |- _ =>
          apply nth_error_Some; unfold runtime_getVal in Hold; congruence
      end.
    - (* return to the caller *)
      match goal with Hh : holds_view S _ _ _ |- _ => destruct Hh as [Hres Hl] end.
      inversion Hstep; subst.
      match goal with
      | Hret' : runtime_getVal rG cache_result = Some ?rv |- _ =>
          rewrite Hres in Hret'; injection Hret' as <-
      end.
      apply RPh_Resume. auto.
    - inversion Hstep; subst. apply RPh_Done. auto.
    - inversion Hstep.
    - inversion Hstep.
  Qed.

  (** ** Soundness: any number of calls *)

  (** The guarantee of every step: valid references stay valid and the
      invariant holds afterwards. *)
  Definition ref_guar (S S' : pico_core_state) : Prop :=
    (forall l, vok S l -> vok S' l) /\ inv S'.

  Definition ref_local (e : pico_core_expr) (S : pico_core_state) : Prop :=
    ref_phase S e.

  Lemma ref_own_step :
    forall e S e' S',
      inv S ->
      ref_local e S ->
      pico_core_step CT e S e' S' ->
      ref_guar S S' /\ ref_local e' S'.
  Proof.
    intros e S e' S' Hinv Hphase Hstep.
    assert (Hmono : forall l, vok S l -> vok S' l).
    { intros l Hl. destruct Hinv as (Hagree & _).
      eapply view_ok_step; eassumption. }
    split; [split; [exact Hmono |] |].
    - eapply (ref_inv_step CT receiver h0 cf Cv vals0 Himm e S e' S' Hinv Hstep).
      intros rG x' y' V K v -> _ Hy'.
      eapply ref_phase_write_ok; eassumption.
    - exact (ref_phase_step e S e' S' Hinv Hphase Hstep Hmono).
  Qed.

  Definition ref_pool (cfg : pico_pool_config) : Prop :=
    pool_rg_inv inv ref_local cfg.

  Theorem ref_cache_pool :
    forall cfg cfg',
      ref_pool cfg ->
      pico_pool_steps CT cfg cfg' ->
      ref_pool cfg'.
  Proof.
    intros cfg cfg' Hpool Hsteps.
    exact (pool_rely_guarantee CT inv ref_local ref_guar
      ref_own_step
      (fun S S' _ Hg => proj2 Hg)
      (fun e S S' _ Hl Hg => ref_phase_mono S S' e (proj1 Hg) Hl)
      cfg cfg' Hpool Hsteps).
  Qed.

  Definition ref_call_pool (S0 : pico_core_state) (V0 : view) (n : nat)
      : pico_pool_config :=
    mkPicoPoolConfig S0 (repeat (CoreRun caller (SCall x mc y []) V0 []) n).

  (** Any number of concurrent calls preserve the invariant, and every call
      that returns normally returns a valid reference. *)
  Theorem ref_cache_calls_sound :
    forall S0 V0 n cfg,
      inv S0 ->
      x < dom (vars caller) ->
      pico_pool_steps CT (ref_call_pool S0 V0 n) cfg ->
      inv (pool_state cfg) /\
      forall rG V,
        List.In (CoreDone OK rG V) (pool_threads cfg) ->
        exists l,
          runtime_getVal rG x = Some (Iot l) /\ vok (pool_state cfg) l.
  Proof.
    intros S0 V0 n cfg Hinv Hx Hsteps.
    assert (Hstart : ref_pool (ref_call_pool S0 V0 n)).
    { split; [exact Hinv |]. simpl. apply Forall_forall.
      intros e Hin. apply repeat_spec in Hin. subst e. apply RPh_Call. }
    destruct (ref_cache_pool _ cfg Hstart Hsteps) as [Hinv' Hlocal].
    split; [exact Hinv' |].
    intros rG V Hin.
    rewrite Forall_forall in Hlocal.
    have Hphase := Hlocal _ Hin.
    unfold ref_local in Hphase. inversion Hphase; subst.
    - exists l. split; [| assumption].
      unfold runtime_getVal, set_vars. cbn [vars].
      apply update_same. exact Hx.
    - contradiction.
  Qed.
End ref_cache_method.
