From Stdlib Require Import List Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping Bigstep Properties Preservation.
Require Import Reachability AbstractStatePreservation.
Require DerivedCache.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoCacheTyping
  PICOBridge.PicoCoreLanguage PICOBridge.PicoCoreInvariant
  PICOBridge.PicoDerivationNoninterference PICOBridge.PicoDerivationSmallStep.

(** * Derivation Code under Interference

    [PicoDerivationSmallStep] relates a complete run of derivation code in
    one fixed state to its big-step evaluation in a reference heap.  Here
    every step of the run may start from a different state, as when other
    threads step in between, and the run may stop anywhere.  Each of those
    states agrees with the reference heap on the footprint and has stable
    footprint histories.

    Such a run has one of three outcomes: it is still running derivation
    code, which never writes a field and reads only abstract fields of
    footprint objects; it has finished the statement with the environment
    that the big-step evaluation in the reference heap produces; or it has
    ended with an exception. *)

Section derivation_prefix.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table) (D : method_def -> Prop) (P : Loc -> Prop).
  Context (h1 : heap).
  Context (Htable : derivation_table CT D).
  Context (Hdom : forall l, P l ->
    exists rt fs, runtime_getObj h1 l = Some (mkObj rt fs)).

  Definition footprint_state (S : pico_core_state) : Prop :=
    abs_agree CT P h1 (pcs_heap S) /\
    footprint_stable CT P (pcs_heap S) (pcs_weak S).

  (** Steps of one thread, each from some footprint state. *)
  Inductive footprint_steps : nat -> pico_core_expr -> pico_core_expr -> Prop :=
    | FootprintStepsRefl : forall e,
        footprint_steps 0 e e
    | FootprintStepsStep : forall n e S e1 S1 e2,
        footprint_state S ->
        pico_core_step CT e S e1 S1 ->
        footprint_steps n e1 e2 ->
        footprint_steps (Datatypes.S n) e e2.

  Lemma footprint_steps_done_inv :
    forall n o r V e,
      footprint_steps n (CoreDone o r V) e ->
      n = 0 /\ e = CoreDone o r V.
  Proof.
    intros n o r V e Hrun. inversion Hrun; subst.
    - auto.
    - exfalso. eapply core_done_no_step; eassumption.
  Qed.

  Lemma footprint_steps_snoc :
    forall n e e1 S e2 S2,
      footprint_steps n e e1 ->
      footprint_state S ->
      pico_core_step CT e1 S e2 S2 ->
      footprint_steps (Datatypes.S n) e e2.
  Proof.
    intros n e e1 S e2 S2 Hrun HS Hstep.
    revert Hstep. induction Hrun; intros Hstep.
    - exact (FootprintStepsStep 0 e S e2 S2 e2 HS Hstep
        (FootprintStepsRefl e2)).
    - exact (FootprintStepsStep _ _ _ _ _ _ H H0 (IHHrun Hstep)).
  Qed.

  (** The control is running derivation code above the continuation
      [Kbase]. *)
  Definition deriv_running (Kbase : pico_core_cont) (e : pico_core_expr) : Prop :=
    exists rΓ s V K,
      e = CoreRun rΓ s V K /\
      (exists Kabove, K = Kabove ++ Kbase /\ ~ (s = SSkip /\ Kabove = [])) /\
      (forall x f y, s <> SFldWrite x f y) /\
      (forall x qc C args, s <> SNew x qc C args) /\
      (forall x y f ly,
         s = SVarAss x (EField y f) ->
         runtime_getVal rΓ y = Some (Iot ly) ->
         P ly /\
         exists rt fs,
           runtime_getObj h1 ly = Some (mkObj rt fs) /\
           abstract_field CT (rctype rt) f).

  Definition deriv_failed (e : pico_core_expr) : Prop :=
    exists r rΓ V, e = CoreDone r rΓ V /\ r <> OK.

  Definition deriv_outcome
      (n : nat) (rΓ : r_env) (s : stmt) (K : pico_core_cont)
      (e : pico_core_expr) : Prop :=
    deriv_running K e \/
    (exists rΓ1 V1 k,
       k <= n /\
       eval_stmt CT rΓ h1 s OK rΓ1 h1 /\
       env_in P rΓ1 /\
       footprint_steps k (CoreRun rΓ1 SSkip V1 K) e) \/
    deriv_failed e.

  Lemma skip_running :
    forall rΓ V fr Kbase,
      deriv_running Kbase (CoreRun rΓ SSkip V (fr :: Kbase)).
  Proof.
    intros rΓ V fr Kbase. exists rΓ, SSkip, V, (fr :: Kbase).
    split; [reflexivity |].
    split; [exists [fr]; split; [reflexivity | intros [_ Hnil]; discriminate] |].
    split; [intros; discriminate |]. split; intros; discriminate.
  Qed.

  Lemma deriv_running_frame :
    forall fr Kbase e,
      deriv_running (fr :: Kbase) e -> deriv_running Kbase e.
  Proof.
    intros fr Kbase e (rΓ & s & V & K & Heq & (Kabove & HK & _) & Hw & Hr).
    exists rΓ, s, V, K. split; [exact Heq |].
    split; [| split; assumption].
    exists (Kabove ++ [fr]). split; [rewrite <- app_assoc; exact HK |].
    intros [_ Hnil]. apply app_eq_nil in Hnil. destruct Hnil as [_ Hnil].
    discriminate.
  Qed.

  Lemma deriv_start :
    forall rΓ s V K sΓ sΓ' mt,
      s <> SSkip ->
      deriv_stmt CT D sΓ s sΓ' ->
      stmt_typing CT sΓ mt s sΓ' ->
      wf_r_config CT sΓ rΓ h1 ->
      env_in P rΓ ->
      deriv_running K (CoreRun rΓ s V K).
  Proof.
    intros rΓ s V K sΓ sΓ' mt Hnotskip Hderiv Htyp Hwf Henv.
    exists rΓ, s, V, K. split; [reflexivity |].
    split; [exists (@nil pico_core_frame);
            split; [reflexivity | intros [Hs _]; contradiction] |].
    split; [intros x f y Heq; subst s; inversion Hderiv |].
    split; [intros x qc C args Heq; subst s; inversion Hderiv |].
    intros x y f ly Heq Hy. subst s.
    {
      inversion Hderiv; subst.
      inversion Hexpr as [| | | | y0 f0 T C Hget Href Habs]; subst.
      have Hly := Henv y ly Hy.
      split; [exact Hly |].
      destruct (Hdom ly Hly) as (rt & fs & Hobj).
      exists rt, fs. split; [exact Hobj |].
      eapply abstract_field_subtype; [| exact Habs].
      eapply runtime_value_class_subtype;
        [exact Hwf | exact Hget | exact Href | exact Hy |].
      unfold r_basetype. rewrite Hobj. reflexivity.
    }
  Qed.

  Lemma failed_tail :
    forall n r rΓ V e,
      r <> OK ->
      footprint_steps n (CoreDone r rΓ V) e ->
      deriv_failed e.
  Proof.
    intros n r rΓ V e Hr Htail.
    destruct (footprint_steps_done_inv _ _ _ _ _ Htail) as [_ ->].
    exists r, rΓ, V. split; [reflexivity | exact Hr].
  Qed.

  (** A run of no steps: finished if the statement is [skip], running
      otherwise. *)
  Lemma deriv_no_steps :
    forall rΓ s V K sΓ sΓ' mt,
      deriv_stmt CT D sΓ s sΓ' ->
      stmt_typing CT sΓ mt s sΓ' ->
      wf_r_config CT sΓ rΓ h1 ->
      env_in P rΓ ->
      deriv_outcome 0 rΓ s K (CoreRun rΓ s V K).
  Proof.
    intros rΓ s V K sΓ sΓ' mt Hderiv Htyp Hwf Henv.
    assert (Hskip : s = SSkip \/ s <> SSkip)
      by (destruct s; (left; reflexivity) || (right; discriminate)).
    destruct Hskip as [-> | Hnot].
    - right. left. exists rΓ, V, 0. split; [lia |].
      split; [constructor |]. split; [exact Henv | constructor].
    - left. eapply deriv_start; eassumption.
  Qed.

  Theorem deriv_prefix :
    forall N n rΓ s V K sΓ sΓ' mt e,
      n <= N ->
      footprint_steps n (CoreRun rΓ s V K) e ->
      deriv_stmt CT D sΓ s sΓ' ->
      stmt_typing CT sΓ mt s sΓ' ->
      wf_r_config CT sΓ rΓ h1 ->
      env_in P rΓ ->
      deriv_outcome n rΓ s K e.
  Proof.
    induction N as [| N IH];
      intros n rΓ s V K sΓ sΓ' mt e Hle Hrun Hderiv Htyp Hwf Henv.
    - assert (n = 0) by lia. subst n. inversion Hrun; subst.
      eapply deriv_no_steps; eassumption.
    - inversion Hrun as [| n' e0 S0 e1 S1 e2 HS Hstep Htail]; subst.
      { eapply deriv_no_steps; eassumption. }
      destruct HS as [Hagree Hst].
      destruct S0 as [h2 sigma2]. simpl in Hagree, Hst.
      inversion Hderiv; subst.
      + (* skip *)
        right. left. exists rΓ, V, (Datatypes.S n'). split; [lia |].
        split; [constructor |]. split; [exact Henv | exact Hrun].
      + (* local declaration *)
        inversion Hstep; subst.
        right. left. eexists _, _, n'. split; [lia |].
        split; [apply SBS_Local; assumption |].
        split; [apply env_in_append_default; exact Henv | exact Htail].
      + (* assignment *)
        inversion Hstep; subst.
        * right. left. eexists _, _, n'. split; [lia |].
          split; [eapply SBS_Assign; [eassumption | constructor] |].
          split; [| exact Htail].
          apply env_in_update; [exact Henv |]. intros l Hl; discriminate.
        * right. left. eexists _, _, n'. split; [lia |].
          split; [eapply SBS_Assign; [eassumption | constructor; eassumption] |].
          split; [| exact Htail].
          apply env_in_update; [exact Henv |].
          intros l ->. eapply Henv. eassumption.
        * right. left. eexists _, _, n'. split; [lia |].
          split; [eapply SBS_Assign; [eassumption | constructor] |].
          split; [| exact Htail].
          apply env_in_update; [exact Henv |]. intros l Hl; discriminate.
        * (* field read *)
          inversion Hexpr as [| | | | y0 f0 T C Hget Href Habs]; subst.
          match goal with
          | Hy : runtime_getVal rΓ y = Some (Iot ?ly),
            Hr : wm_read _ _ (?ly, f) ?v _ |- _ =>
              destruct (deriv_read_transfer CT P h1 h2 sigma2 Hagree Hst
                sΓ' rΓ y f T C ly Hwf Henv Hget
                Href Habs Hy) as (rt & fs1 & Hobj1 & _ & Honly & Hclosed);
              have Hv := Honly v (values_written_to_read _ _ _ _ _ Hr);
              right; left; eexists _, _, n'; split; [lia |];
              split; [eapply SBS_Assign;
                [eassumption | eapply EBS_Field; [exact Hy | exact Hobj1 | exact Hv]] |];
              split; [| exact Htail];
              apply env_in_update; [exact Henv |];
              intros l Hl; subst v; exact (Hclosed l Hv)
          end.
        * right. right. eapply failed_tail; [| exact Htail]. discriminate.
        * (* integer operation *)
          right. left. eexists _, _, n'. split; [lia |].
          split; [eapply SBS_Assign;
            [eassumption | eapply EBS_Bin; eassumption] |].
          split; [| exact Htail].
          apply env_in_update; [exact Henv |]. intros l Hl; discriminate.
      + (* sequence *)
        inversion Hstep; subst.
        inversion Htyp; subst.
        have Hmid := deriv_stmt_typing_env CT D _ _ _ _ _ Hderiv1 Htype1.
        subst.
        destruct (IH n' rΓ s1 V (KSeq s2 :: K) sΓ _ mt e ltac:(lia) Htail
          Hderiv1 Htype1 Hwf Henv)
          as [Hrunning | [(rΓ1 & V1 & k1 & Hk1 & Heval1 & Henv1 & Htail1)
                         | Hfailed]].
        * left. eapply deriv_running_frame. exact Hrunning.
        * inversion Htail1 as [| k1' e3 S3 e4 S4 e5 HS1 Hstep1 Htail2]; subst.
          { left. apply (skip_running rΓ1 V1 (KSeq s2) K). }
          inversion Hstep1; subst.
          have Hwf1 := preservation_pico CT sΓ mt rΓ h1 s1 rΓ1 h1 _ Hwf Htype1 Heval1.
          destruct (IH k1' rΓ1 s2 V1 K _ sΓ' mt e ltac:(lia) Htail2
            Hderiv2 Htype2 Hwf1 Henv1)
            as [Hrunning | [(rΓ2 & V2 & k2 & Hk2 & Heval2 & Henv2 & Htail3)
                           | Hfailed]].
          -- left. exact Hrunning.
          -- right. left. exists rΓ2, V2, k2. split; [lia |].
             split; [eapply SBS_Seq; eassumption |].
             split; [exact Henv2 | exact Htail3].
          -- right. right. exact Hfailed.
        * right. right. exact Hfailed.
      + (* zero test *)
        inversion Htyp; subst.
        inversion Hstep; subst.
        * destruct (IH n' rΓ s_zero V K sΓ sΓ' mt e ltac:(lia) Htail
            Hzero ltac:(eassumption) Hwf Henv)
            as [Hrunning | [(rΓ1 & V1 & k & Hk & Heval & Henv1 & Htail1)
                           | Hfailed]].
          -- left. exact Hrunning.
          -- right. left. exists rΓ1, V1, k. split; [lia |].
             split; [eapply SBS_IfZero; eassumption |].
             split; [exact Henv1 | exact Htail1].
          -- right. right. exact Hfailed.
        * destruct (IH n' rΓ s_nonzero V K sΓ sΓ' mt e ltac:(lia) Htail
            Hnonzero ltac:(eassumption) Hwf Henv)
            as [Hrunning | [(rΓ1 & V1 & k & Hk & Heval & Henv1 & Htail1)
                           | Hfailed]].
          -- left. exact Hrunning.
          -- right. left. exists rΓ1, V1, k. split; [lia |].
             split; [eapply SBS_IfNonzero; eassumption |].
             split; [exact Henv1 | exact Htail1].
          -- right. right. exact Hfailed.
        * destruct (IH n' rΓ s_zero V K sΓ sΓ' mt e ltac:(lia) Htail
            Hzero ltac:(eassumption) Hwf Henv)
            as [Hrunning | [(rΓ1 & V1 & k & Hk & Heval & Henv1 & Htail1)
                           | Hfailed]].
          -- left. exact Hrunning.
          -- right. left. exists rΓ1, V1, k. split; [lia |].
             split; [eapply SBS_IfNull; eassumption |].
             split; [exact Henv1 | exact Htail1].
          -- right. right. exact Hfailed.
        * destruct (IH n' rΓ s_nonzero V K sΓ sΓ' mt e ltac:(lia) Htail
            Hnonzero ltac:(eassumption) Hwf Henv)
            as [Hrunning | [(rΓ1 & V1 & k & Hk & Heval & Henv1 & Htail1)
                           | Hfailed]].
          -- left. exact Hrunning.
          -- right. left. exists rΓ1, V1, k. split; [lia |].
             split; [eapply SBS_IfRef; eassumption |].
             split; [exact Henv1 | exact Htail1].
          -- right. right. exact Hfailed.
      + (* call *)
        inversion Hstep; subst.
        * match goal with
          | Hy : runtime_getVal rΓ y = Some (Iot _),
            Hb : r_basetype h2 _ = Some _,
            Hf : FindMethodWithName CT _ m _,
            Ha : runtime_lookup_list rΓ args = Some _ |- _ =>
              rename Hy into Hy0; rename Hb into Hb0; rename Hf into Hf0;
              rename Ha into Ha0
          end.
          have Hly := Henv y loc_y Hy0.
          assert (Hb1 : r_basetype h1 loc_y = Some C).
          { rewrite <- (abs_agree_basetype CT P h1 h2 loc_y Hagree Hly).
            exact Hb0. }
          assert (Hsub : class_subtype CT C Cy).
          { eapply runtime_value_class_subtype;
              [exact Hwf | exact Hget_y | exact Href | exact Hy0 | exact Hb1]. }
          have HD := Hdispatch C mdef Hsub Hf0.
          destruct (Htable mdef HD) as [sΓd Hderivb].
          destruct (typed_call_has_wf_callee_frame CT sΓ' mt rΓ h1 x m y args
            sΓ' vals loc_y C mdef Hwf Htyp Hy0 Hb1 Hf0 Ha0)
            as (sΓb & Htypb & Hwfb).
          have Hsame := deriv_stmt_typing_env CT D _ _ _ _ _ Hderivb Htypb.
          subst sΓd.
          destruct (IH n' (mkr_env (Iot loc_y :: vals)) (mbody_stmt (mbody mdef))
            V (KCall rΓ x (mreturn (mbody mdef)) :: K) _ sΓb _ e
            ltac:(lia) Htail Hderivb Htypb Hwfb
            (env_in_call_frame P rΓ args vals loc_y Henv Hly Ha0))
            as [Hrunning | [(rΓb & Vb & kb & Hkb & Hevalb & Henvb & Htailb)
                           | Hfailed]].
          -- left. eapply deriv_running_frame. exact Hrunning.
          -- inversion Htailb as [| kb' e3 S3 e4 S4 e5 HSr Hstepr Htailr]; subst.
             { left.
               apply (skip_running rΓb Vb
                 (KCall rΓ x (mreturn (mbody mdef))) K). }
             inversion Hstepr; subst.
             match goal with
             | Hret : runtime_getVal rΓb (mreturn (mbody mdef)) = Some ?retval |- _ =>
                 right; left;
                 exists (set_vars rΓ (update x retval (vars rΓ))), Vb, kb';
                 split; [lia |];
                 split; [eapply SBS_Call; eauto |];
                 split; [| exact Htailr];
                 apply env_in_update; [exact Henv |];
                 intros l ->; exact (Henvb _ l Hret)
             end.
          -- right. right. exact Hfailed.
        * right. right. eapply failed_tail; [| exact Htail]. discriminate.
  Qed.
End derivation_prefix.
