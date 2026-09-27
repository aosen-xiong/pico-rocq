From Stdlib Require Import List Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping Bigstep Properties Preservation.
Require Import Reachability.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoCacheTyping
  PICOBridge.PicoIrisCoreLanguage PICOBridge.PicoIrisCoreInvariant
  PICOBridge.PicoDerivationNoninterference PICOBridge.PicoDerivationCache.

(** * Small-Step Noninterference for Derivation Methods

    [PicoDerivationNoninterference] proves noninterference for the big-step
    semantics.  This file proves it for the continuation-based core language
    used by the Iris model and the invocation-pool scheduler, where a field
    read returns a value from the field's weak history.

    Two facts drive the proof.  A derivation performs no field write and no
    allocation, so it never changes the core state.  And when every weak
    history of an abstract field in the footprint holds only the heap value,
    every read the derivation performs returns that heap value.  Runs in two
    states that agree on the footprint therefore proceed in lockstep, up to
    thread views.

    Derivation bodies may call other derivation methods.  Runs are related
    to big-step evaluations in a typed reference heap: a normally completing
    small-step run decomposes into a big-step evaluation of the current
    statement and a run of the rest of the continuation, and every big-step
    evaluation is realized by a small-step run.  The typing facts come from
    the big-step development. *)

Section small_step.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table) (P : Loc -> Prop).

  (** Every weak history of an abstract field of a footprint object holds
      only the heap value of that field, and is nonempty when the field has
      a value. *)
  Definition footprint_stable (h : heap) (sigma : wm_state) : Prop :=
    forall l rt fs f,
      P l ->
      runtime_getObj h l = Some (mkObj rt fs) ->
      abstract_field CT (rctype rt) f ->
      (forall v0, getVal fs f = Some v0 ->
        values_written_to sigma (l, f) <> @nil value) /\
      forall w, List.In w (values_written_to sigma (l, f)) ->
        getVal fs f = Some w.

  Lemma values_written_to_read :
    forall sigma V addr v V',
      wm_read sigma V addr v V' ->
      List.In v (values_written_to sigma addr).
  Proof.
    intros sigma V addr v V' Hread.
    destruct (wm_read_from_history _ _ _ _ _ Hread) as (msg & Hin & Hval).
    unfold values_written_to. rewrite <- Hval. apply List.in_map. exact Hin.
  Qed.

  Lemma wf_config_env_location :
    forall sΓ rΓ h y l,
      wf_r_config CT sΓ rΓ h ->
      runtime_getVal rΓ y = Some (Iot l) ->
      exists rt fs, runtime_getObj h l = Some (mkObj rt fs).
  Proof.
    intros sΓ rΓ h y l Hwf Hval.
    destruct Hwf as [_ [_ [[_ [_ Hforall]] _]]].
    have Hin := nth_error_In (vars rΓ) y Hval.
    have Hl := proj1 (Forall_forall _ _) Hforall _ Hin.
    simpl in Hl.
    destruct (runtime_getObj h l) as [[rt fs] |] eqn:Hobj; [| contradiction].
    exists rt, fs. reflexivity.
  Qed.

  Lemma env_in_receiver_frame :
    forall o, P o -> env_in P (mkr_env [Iot o]).
  Proof.
    intros o Ho x l Hx.
    destruct x as [| x]; simpl in Hx.
    - injection Hx as <-. exact Ho.
    - destruct x; discriminate.
  Qed.

  Lemma core_done_no_step :
    forall o r V S e S',
      pico_core_step CT (CoreDone o r V) S e S' -> False.
  Proof. intros o r V S e S' Hstep. inversion Hstep. Qed.

End small_step.

(** ** Small-step derived values *)

(** Calling derivation method [m] on receiver [o] with no arguments in core
    state [S] runs, in the core semantics, to a normal completion whose return
    variable holds [v]. *)
Definition derived_ss `{CacheMemoryModel} (CT : class_table)
    (m : method_name) (S : pico_core_state) (o : Loc) (v : value) : Prop :=
  exists cy mdef V rΓ' V' S',
    r_basetype (pcs_heap S) o = Some cy /\
    FindMethodWithName CT cy m mdef /\
    pico_core_steps CT
      (CoreRun (mkr_env [Iot o]) (mbody_stmt (mbody mdef)) V [])
      S (CoreDone OK rΓ' V') S' /\
    runtime_getVal rΓ' (mreturn (mbody mdef)) = Some v.

(** ** Derivations with calls

    For derivation bodies that may call other derivation methods, runs are
    related to big-step evaluations in a typed reference heap [h1].  A
    small-step run in a state that agrees with [h1] on [P] decomposes into a
    run of the current statement, which is a big-step evaluation in [h1], and
    a run of the rest of the continuation; conversely, every big-step
    evaluation in [h1] is realized by a small-step run in such a state.  The
    typing facts come from the big-step development, including the
    callee-frame lemma for calls. *)

Inductive core_nsteps `{CacheMemoryModel} (CT : class_table) :
    nat -> pico_core_expr -> pico_core_state ->
    pico_core_expr -> pico_core_state -> Prop :=
  | CoreNStepsRefl : forall e St,
      core_nsteps CT 0 e St e St
  | CoreNStepsStep : forall n e St e1 St1 e2 St2,
      pico_core_step CT e St e1 St1 ->
      core_nsteps CT n e1 St1 e2 St2 ->
      core_nsteps CT (S n) e St e2 St2.

Lemma core_steps_nsteps `{CacheMemoryModel} :
  forall CT e St e' St',
    pico_core_steps CT e St e' St' <-> exists n, core_nsteps CT n e St e' St'.
Proof.
  intros CT e St e' St'. split.
  - intros Hsteps. induction Hsteps as [e St | e St e1 St1 e2 St2 Hstep Htail IH].
    + exists 0. constructor.
    + destruct IH as [n Hn]. exists (S n). econstructor; eassumption.
  - intros [n Hn]. induction Hn; econstructor; eassumption.
Qed.

Lemma core_steps_trans `{CacheMemoryModel} :
  forall CT e1 S1 e2 S2 e3 S3,
    pico_core_steps CT e1 S1 e2 S2 ->
    pico_core_steps CT e2 S2 e3 S3 ->
    pico_core_steps CT e1 S1 e3 S3.
Proof.
  intros CT e1 S1 e2 S2 e3 S3 H12 H23.
  induction H12; [exact H23 | econstructor; eauto].
Qed.

Section small_step_calls.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table) (D : method_def -> Prop) (P : Loc -> Prop).
  Context (h1 h2 : heap) (sigma2 : wm_state).
  Context (Htable : derivation_table CT D).
  Context (Hagree : abs_agree CT P h1 h2).
  Context (Hst2 : footprint_stable CT P h2 sigma2).

  (** A field read of derivation code in the running state returns the value
      of an abstract field of a footprint object in the reference heap. *)
  Lemma deriv_read_transfer :
    forall sΓ rΓ y f T C ly,
      wf_r_config CT sΓ rΓ h1 ->
      env_in P rΓ ->
      static_getType sΓ y = Some T ->
      sbase T = TRef C ->
      abstract_field CT C f ->
      runtime_getVal rΓ y = Some (Iot ly) ->
      exists rt fs1,
        runtime_getObj h1 ly = Some (mkObj rt fs1) /\
        (forall v0, getVal fs1 f = Some v0 ->
          values_written_to sigma2 (ly, f) <> @nil value) /\
        (forall v, List.In v (values_written_to sigma2 (ly, f)) ->
          getVal fs1 f = Some v) /\
        (forall l', getVal fs1 f = Some (Iot l') -> P l').
  Proof.
    intros sΓ rΓ y f T C ly Hwf Henv Hget Href Habs Hval.
    have Hly := Henv y ly Hval.
    destruct (Hagree ly Hly) as (rt & fs1 & fs2 & Hobj1 & Hobj2 & Hfields).
    have Hsub : class_subtype CT (rctype rt) C.
    { eapply runtime_value_class_subtype;
        [exact Hwf | exact Hget | exact Href | exact Hval |].
      unfold r_basetype. rewrite Hobj1. reflexivity. }
    have Habs' := abstract_field_subtype CT (rctype rt) C f Hsub Habs.
    destruct (Hfields f Habs') as [Heq Hclosed].
    destruct (Hst2 ly rt fs2 f Hly Hobj2 Habs') as [Hnonempty Honly].
    exists rt, fs1.
    split; [exact Hobj1 |].
    split; [intros v0 Hv0; rewrite Heq in Hv0; exact (Hnonempty v0 Hv0) |].
    split; [| exact Hclosed].
    intros v Hin. rewrite Heq. exact (Honly v Hin).
  Qed.

  Lemma core_nsteps_done_inv :
    forall n o r V e S S',
      core_nsteps CT n (CoreDone o r V) S e S' ->
      n = 0 /\ e = CoreDone o r V /\ S' = S.
  Proof.
    intros n o r V e S S' Hrun. inversion Hrun; subst.
    - auto.
    - exfalso. eapply core_done_no_step; eassumption.
  Qed.

  (** Decomposition.  A normally completing run of derivation code splits
      into a big-step evaluation of the current statement in [h1] and a
      shorter run of the continuation. *)
  Lemma deriv_decompose :
    forall N n rΓ s V K sΓ sΓ' mt rf W S',
      n <= N ->
      core_nsteps CT n (CoreRun rΓ s V K) (mkPicoCoreState h2 sigma2)
        (CoreDone OK rf W) S' ->
      deriv_stmt CT D sΓ s sΓ' ->
      stmt_typing CT sΓ mt s sΓ' ->
      wf_r_config CT sΓ rΓ h1 ->
      env_in P rΓ ->
      exists rΓ1 V1 k,
        k <= n /\
        eval_stmt CT rΓ h1 s OK rΓ1 h1 /\
        env_in P rΓ1 /\
        core_nsteps CT k (CoreRun rΓ1 SSkip V1 K) (mkPicoCoreState h2 sigma2)
          (CoreDone OK rf W) S'.
  Proof.
    induction N as [| N IH];
      intros n rΓ s V K sΓ sΓ' mt rf W S' Hle Hrun Hderiv Htyp Hwf Henv.
    - (* a running control needs at least one step to complete *)
      assert (n = 0) by lia. subst n. inversion Hrun.
    - inversion Hderiv; subst.
      + (* skip *)
        exists rΓ, V, n. split; [lia |].
        split; [constructor |]. split; [exact Henv | exact Hrun].
      + (* local declaration *)
        inversion Hrun as [| n' e0 S0 e1 S1 e2 S2 Hstep Htail]; subst.
        inversion Hstep; subst.
        eexists _, _, n'. split; [lia |].
        split; [apply SBS_Local; assumption |].
        split; [apply env_in_append_default; exact Henv | exact Htail].
      + (* assignment *)
        inversion Hrun as [| n' e0 S0 e1 S1 e2 S2 Hstep Htail]; subst.
        inversion Hstep; subst.
        * eexists _, _, n'. split; [lia |].
          split; [eapply SBS_Assign; [eassumption | constructor] |].
          split; [| exact Htail].
          apply env_in_update; [exact Henv |]. intros l Hl; discriminate.
        * eexists _, _, n'. split; [lia |].
          split; [eapply SBS_Assign; [eassumption | constructor; eassumption] |].
          split; [| exact Htail].
          apply env_in_update; [exact Henv |].
          intros l ->. eapply Henv. eassumption.
        * eexists _, _, n'. split; [lia |].
          split; [eapply SBS_Assign; [eassumption | constructor] |].
          split; [| exact Htail].
          apply env_in_update; [exact Henv |]. intros l Hl; discriminate.
        * (* field read *)
          inversion Hexpr as [| | | y0 f0 T C Hget Href Habs]; subst.
          match goal with
          | Hy : runtime_getVal rΓ y = Some (Iot ?ly),
            Hr : wm_read sigma2 _ (?ly, f) ?v _ |- _ =>
              destruct (deriv_read_transfer sΓ' rΓ y f T C ly Hwf Henv Hget
                Href Habs Hy) as (rt & fs1 & Hobj1 & _ & Honly & Hclosed);
              have Hv := Honly v (values_written_to_read _ _ _ _ _ Hr);
              eexists _, _, n'; split; [lia |];
              split; [eapply SBS_Assign;
                [eassumption | eapply EBS_Field; [exact Hy | exact Hobj1 | exact Hv]] |];
              split; [| exact Htail];
              apply env_in_update; [exact Henv |];
              intros l Hl; subst v; exact (Hclosed l Hv)
          end.
        * (* null dereference cannot complete normally *)
          destruct (core_nsteps_done_inv _ _ _ _ _ _ _ Htail) as (_ & Heq & _).
          discriminate.
      + (* sequence *)
        inversion Hrun as [| n' e0 S0 e1 S1 e2 S2 Hstep Htail]; subst.
        inversion Hstep; subst.
        inversion Htyp; subst.
        have Hmid := deriv_stmt_typing_env CT D _ _ _ _ _ Hderiv1 Htype1.
        subst.
        destruct (IH n' rΓ s1 V (KSeq s2 :: K) sΓ _ mt rf W S' ltac:(lia) Htail
          Hderiv1 Htype1 Hwf Henv) as (rΓ1 & V1 & k1 & Hk1 & Heval1 & Henv1 & Htail1).
        inversion Htail1 as [| k1' e3 S3 e4 S4 e5 S5 Hstep1 Htail2]; subst.
        inversion Hstep1; subst.
        have Hwf1 := preservation_pico CT sΓ mt rΓ h1 s1 rΓ1 h1 _ Hwf Htype1 Heval1.
        destruct (IH k1' rΓ1 s2 V1 K _ sΓ' mt rf W S' ltac:(lia) Htail2
          Hderiv2 Htype2 Hwf1 Henv1) as (rΓ2 & V2 & k2 & Hk2 & Heval2 & Henv2 & Htail3).
        exists rΓ2, V2, k2. split; [lia |].
        split; [eapply SBS_Seq; eassumption |].
        split; [exact Henv2 | exact Htail3].
      + (* zero test *)
        inversion Hrun as [| n' e0 S0 e1 S1 e2 S2 Hstep Htail]; subst.
        inversion Htyp; subst.
        inversion Hstep; subst.
        * destruct (IH n' rΓ s_zero V K sΓ sΓ' mt rf W S' ltac:(lia) Htail
            Hzero ltac:(eassumption) Hwf Henv)
            as (rΓ1 & V1 & k & Hk & Heval & Henv1 & Htail1).
          exists rΓ1, V1, k. split; [lia |].
          split; [eapply SBS_IfZero; eassumption |].
          split; [exact Henv1 | exact Htail1].
        * destruct (IH n' rΓ s_nonzero V K sΓ sΓ' mt rf W S' ltac:(lia) Htail
            Hnonzero ltac:(eassumption) Hwf Henv)
            as (rΓ1 & V1 & k & Hk & Heval & Henv1 & Htail1).
          exists rΓ1, V1, k. split; [lia |].
          split; [eapply SBS_IfNonzero; eassumption |].
          split; [exact Henv1 | exact Htail1].
        * destruct (core_nsteps_done_inv _ _ _ _ _ _ _ Htail) as (_ & Heq & _).
          discriminate.
      + (* call *)
        inversion Hrun as [| n' e0 S0 e1 S1 e2 S2 Hstep Htail]; subst.
        inversion Hstep; subst.
        * (* enter the callee *)
          match goal with
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
            V (KCall rΓ x (mreturn (mbody mdef)) :: K) _ sΓb _ rf W S'
            ltac:(lia) Htail Hderivb Htypb Hwfb
            (env_in_call_frame P rΓ args vals loc_y Henv Hly Ha0))
            as (rΓb & Vb & kb & Hkb & Hevalb & Henvb & Htailb).
          inversion Htailb as [| kb' e3 S3 e4 S4 e5 S5 Hstepr Htailr]; subst.
          inversion Hstepr; subst.
          match goal with
          | Hret : runtime_getVal rΓb (mreturn (mbody mdef)) = Some ?retval |- _ =>
              exists (set_vars rΓ (update x retval (vars rΓ))), Vb, kb';
              split; [lia |];
              split; [eapply SBS_Call; eauto |];
              split; [| exact Htailr];
              apply env_in_update; [exact Henv |];
              intros l ->; exact (Henvb _ l Hret)
          end.
        * destruct (core_nsteps_done_inv _ _ _ _ _ _ _ Htail) as (_ & Heq & _).
          discriminate.
  Qed.
  Section with_progress.
    Context `{Hprogress : @CacheMemoryModelProgress Hmem}.

    (** Composition.  A big-step evaluation of derivation code in [h1] is
        realized by a small-step run in the agreeing state, which leaves the
        state unchanged. *)
    Lemma deriv_compose :
      forall rΓ hh s r rΓ1 hh',
        eval_stmt CT rΓ hh s r rΓ1 hh' ->
        forall sΓ sΓ' mt V K,
          hh = h1 ->
          r = OK ->
          deriv_stmt CT D sΓ s sΓ' ->
          stmt_typing CT sΓ mt s sΓ' ->
          wf_r_config CT sΓ rΓ h1 ->
          env_in P rΓ ->
          hh' = h1 /\
          exists V1,
            pico_core_steps CT (CoreRun rΓ s V K) (mkPicoCoreState h2 sigma2)
              (CoreRun rΓ1 SSkip V1 K) (mkPicoCoreState h2 sigma2).
    Proof.
      intros rΓ hh s r rΓ1 hh' Heval.
      remember CT as CTe eqn:HCT in Heval.
      induction Heval; intros sΓ0 sΓ0' mt0 V0 K0 Hh Hr Hderiv0 Htyp0 Hwf0 HenvP;
        subst; try discriminate; inversion Hderiv0; subst.
      - (* skip *)
        split; [reflexivity |]. exists V0. constructor.
      - (* local declaration *)
        split; [reflexivity |].
        exists V0. econstructor; [apply PCS_Local; eassumption | constructor].
      - (* assignment *)
        split; [reflexivity |].
        inversion Hexpr as [| y0 | n0 | y0 f0 T C Hget Href Habs]; subst;
          inversion Heval; subst.
        + exists V0. econstructor; [eapply PCS_AssignNull; eassumption | constructor].
        + exists V0. econstructor; [eapply PCS_AssignVar; eassumption | constructor].
        + exists V0. econstructor; [eapply PCS_AssignInt; eassumption | constructor].
        + match goal with
          | Hy : runtime_getVal rΓ y0 = Some (Iot ?ly),
            Ho : runtime_getObj h1 ?ly = Some ?o,
            Hf : getVal (fields_map ?o) f0 = Some ?v |- _ =>
              destruct (deriv_read_transfer sΓ0' rΓ y0 f0 T C ly Hwf0 HenvP Hget
                Href Habs Hy) as (rt & fs1 & Hobj1 & Hnonempty & Honly & _);
              rewrite Hobj1 in Ho; injection Ho as <-;
              simpl in Hf;
              assert (Hhist : history_of sigma2 (ly, f0) <> []);
              [ intros Hnil; apply (Hnonempty _ Hf); unfold values_written_to;
                rewrite Hnil; reflexivity |];
              destruct (wm_read_nonempty sigma2 V0 (ly, f0) Hhist)
                as (v' & V' & Hread);
              have Hv' := Honly v' (values_written_to_read _ _ _ _ _ Hread);
              rewrite Hf in Hv'; injection Hv' as <-;
              exists V'; econstructor;
              [eapply PCS_AssignField; eassumption | constructor]
          end.
      - (* call *)
        destruct Hfind as [Hfind Hmbody].
        have Hly := HenvP y ly Hval_y.
        assert (Hb2 : r_basetype h2 ly = Some cy).
        { rewrite (abs_agree_basetype CT P h1 h2 ly Hagree Hly). exact Hbase. }
        assert (Hsub : class_subtype CT cy Cy).
        { eapply runtime_value_class_subtype;
            [exact Hwf0 | exact Hget_y | exact Href | exact Hval_y | exact Hbase]. }
        have HD := Hdispatch cy mdef Hsub Hfind.
        destruct (Htable mdef HD) as [sΓd Hderivb].
        destruct (typed_call_has_wf_callee_frame CT sΓ0' mt0 rΓ h1 x m y zs
          sΓ0' vals ly cy mdef Hwf0 Htyp0 Hval_y Hbase Hfind Hargs)
          as (sΓb & Htypb & Hwfb).
        have Hsame := deriv_stmt_typing_env CT D _ _ _ _ _ Hderivb Htypb.
        subst sΓd.
        subst.
        destruct (IHHeval eq_refl _ _ _ V0 (KCall rΓ x (mreturn (Syntax.mbody mdef)) :: K0)
          eq_refl eq_refl Hderivb Htypb Hwfb
          (env_in_call_frame P rΓ zs vals ly HenvP Hly Hargs))
          as [Hh' [Vb Hstepsb]].
        split; [exact Hh' |].
        exists Vb.
        econstructor.
        { eapply PCS_Call; [exact Hval_y | exact Hb2 | exact Hfind
            | reflexivity | reflexivity | reflexivity | exact Hargs]. }
        eapply core_steps_trans; [exact Hstepsb |].
        econstructor; [apply PCS_SkipCall; exact Hretval | constructor].
      - (* sequence *)
        inversion Htyp0; subst.
        have Hmid := deriv_stmt_typing_env CT D _ _ _ _ _ Hderiv1 Htype1.
        subst.
        destruct (IHHeval1 eq_refl _ _ _ V0 (KSeq s2 :: K0) eq_refl eq_refl Hderiv1
          Htype1 Hwf0 HenvP) as [Hh' [V1 Hsteps1]].
        subst h'.
        destruct (derivation_simulation CT D Htable rΓ h1 s1 OK rΓ' h1 Heval1
          _ _ _ h2 P Hderiv1 Htype1 Hwf0 Hagree HenvP) as (_ & _ & Henv1).
        have Hwf1 := preservation_pico CT sΓ0 mt0 rΓ h1 s1 rΓ' h1 _ Hwf0 Htype1
          Heval1.
        destruct (IHHeval2 eq_refl _ _ _ V1 K0 eq_refl eq_refl Hderiv2 Htype2 Hwf1 Henv1)
          as [Hh'' [V2 Hsteps2]].
        split; [exact Hh'' |].
        exists V2.
        econstructor; [apply PCS_Seq |].
        eapply core_steps_trans; [exact Hsteps1 |].
        econstructor; [apply PCS_SkipSeq | exact Hsteps2].
      - (* zero test *)
        inversion Htyp0; subst.
        destruct (IHHeval eq_refl _ _ _ V0 K0 eq_refl eq_refl Hzero ltac:(eassumption)
          Hwf0 HenvP) as [Hh' [V1 Hsteps]].
        split; [exact Hh' |]. exists V1.
        econstructor; [apply PCS_IfZero; exact Hguard | exact Hsteps].
      - (* nonzero test *)
        inversion Htyp0; subst.
        destruct (IHHeval eq_refl _ _ _ V0 K0 eq_refl eq_refl Hnonzero ltac:(eassumption)
          Hwf0 HenvP) as [Hh' [V1 Hsteps]].
        split; [exact Hh' |]. exists V1.
        econstructor; [eapply PCS_IfNonzero; exact Hguard | exact Hsteps].
    Qed.
  End with_progress.
End small_step_calls.

(** ** Small-step derived values and noninterference *)

Section small_step_noninterference.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table) (D : method_def -> Prop) (P : Loc -> Prop).

  (** A normally completing small-step run of a derivation, in a state that
      agrees with the typed reference heap [h1], returns the value the
      big-step derivation returns in [h1]. *)
  Theorem derived_ss_derived_by :
    forall m h1 h2 sigma2 o v,
      derivation_table CT D ->
      derivation_ready CT D m h1 o ->
      P o ->
      abs_agree CT P h1 h2 ->
      footprint_stable CT P h2 sigma2 ->
      derived_ss CT m (mkPicoCoreState h2 sigma2) o v ->
      derived_by CT m h1 o v.
  Proof.
    intros m h1 h2 sigma2 o v Htable Hready Ho Hagree Hst2
      (cy & mdef & V & rΓ' & V' & S' & Hbase2 & Hfind & Hsteps & Hret).
    simpl in Hbase2.
    have Hbase1 : r_basetype h1 o = Some cy.
    { rewrite <- (abs_agree_basetype CT P h1 h2 o Hagree Ho). exact Hbase2. }
    destruct (derivation_ready_body CT D m h1 o cy mdef Htable Hready Hbase1 Hfind)
      as (sΓd & Hderiv & Htyping & Hwf).
    destruct (proj1 (core_steps_nsteps CT _ _ _ _) Hsteps) as [n Hn].
    destruct (deriv_decompose CT D P h1 h2 sigma2 Htable Hagree Hst2 n n
      (mkr_env [Iot o]) (mbody_stmt (mbody mdef)) V [] _ sΓd _ rΓ' V' S'
      ltac:(lia) Hn Hderiv Htyping Hwf (env_in_receiver_frame P o Ho))
      as (rΓ1 & V1 & k & _ & Heval & _ & Htail).
    inversion Htail as [| k' e0 S0 e1 S1 e2 S2 Hstep Htail']; subst.
    inversion Hstep; subst.
    destruct (core_nsteps_done_inv _ _ _ _ _ _ _ _ Htail') as (_ & Heq & _).
    injection Heq as Hr1 _. subst.
    exists cy, mdef. eexists.
    split; [exact Hbase1 |].
    split; [exact Hfind |].
    split; [exact Heval | exact Hret].
  Qed.

  Section with_progress.
    Context `{Hprogress : @CacheMemoryModelProgress Hmem}.

    (** Conversely, a big-step derived value in [h1] is the result of a
        small-step run in every agreeing, footprint-stable state. *)
    Theorem derived_by_derived_ss :
      forall m h1 h2 sigma2 o v,
        derivation_table CT D ->
        derivation_ready CT D m h1 o ->
        P o ->
        abs_agree CT P h1 h2 ->
        footprint_stable CT P h2 sigma2 ->
        derived_by CT m h1 o v ->
        derived_ss CT m (mkPicoCoreState h2 sigma2) o v.
    Proof.
      intros m h1 h2 sigma2 o v Htable Hready Ho Hagree Hst2
        (cy & mdef & rΓ' & Hbase1 & Hfind & Heval & Hret).
      have Hbase2 : r_basetype h2 o = Some cy.
      { rewrite (abs_agree_basetype CT P h1 h2 o Hagree Ho). exact Hbase1. }
      destruct (derivation_ready_body CT D m h1 o cy mdef Htable Hready Hbase1 Hfind)
        as (sΓd & Hderiv & Htyping & Hwf).
      destruct (deriv_compose CT D P h1 h2 sigma2 Htable Hagree Hst2
        (mkr_env [Iot o]) h1 (mbody_stmt (mbody mdef)) OK rΓ' h1 Heval
        _ sΓd _ 0 [] eq_refl eq_refl Hderiv Htyping Hwf
        (env_in_receiver_frame P o Ho)) as [_ [V1 Hsteps]].
      exists cy, mdef, 0, rΓ', V1, (mkPicoCoreState h2 sigma2).
      split; [exact Hbase2 |].
      split; [exact Hfind |].
      split; [| exact Hret].
      eapply core_steps_trans; [exact Hsteps |].
      econstructor; [apply PCS_SkipDone | constructor].
    Qed.

    (** Small-step noninterference.  In two core states whose heaps agree on a
        footprint [P] that contains the receiver and is closed in the first
        heap, and whose footprint histories hold only the heap values, a
        derivation method returns the same value: every result in the first
        state is a result in the second, and the second has no other
        result. *)
    Theorem derivation_noninterference_small_step :
      forall m h1 sigma1 h2 sigma2 o v,
        derivation_table CT D ->
        derivation_ready CT D m h1 o ->
        P o ->
        abs_agree CT P h1 h1 ->
        abs_agree CT P h1 h2 ->
        footprint_stable CT P h1 sigma1 ->
        footprint_stable CT P h2 sigma2 ->
        derived_ss CT m (mkPicoCoreState h1 sigma1) o v ->
        derived_ss CT m (mkPicoCoreState h2 sigma2) o v /\
        (forall w, derived_ss CT m (mkPicoCoreState h2 sigma2) o w -> w = v).
    Proof.
      intros m h1 sigma1 h2 sigma2 o v Htable Hready Ho Hclosed Hagree Hst1 Hst2
        Hss1.
      have Hby := derived_ss_derived_by m h1 h1 sigma1 o v Htable Hready Ho
        Hclosed Hst1 Hss1.
      split.
      - exact (derived_by_derived_ss m h1 h2 sigma2 o v Htable Hready Ho Hagree
          Hst2 Hby).
      - intros w Hss2.
        have Hby2 := derived_ss_derived_by m h1 h2 sigma2 o w Htable Hready Ho
          Hagree Hst2 Hss2.
        destruct Hby as (cy & mdef & rΓ & Hbase & Hfind & Heval & Hret).
        destruct Hby2 as (cy2 & mdef2 & rΓ2 & Hbase2 & Hfind2 & Heval2 & Hret2).
        rewrite Hbase in Hbase2. injection Hbase2 as <-.
        have Hmdef := find_method_with_name_deterministic CT cy m mdef2 mdef
          Hfind2 Hfind.
        subst mdef2.
        destruct (eval_stmt_deterministic CT _ _ _ _ _ _ _ _ _ Heval Heval2)
          as (_ & <- & _).
        congruence.
    Qed.
  End with_progress.
End small_step_noninterference.
