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

    This file covers call-free derivation bodies. *)

(** ** Call-free statements *)

Fixpoint stmt_call_free (s : stmt) : Prop :=
  match s with
  | SCall _ _ _ _ => False
  | SSeq s1 s2 => stmt_call_free s1 /\ stmt_call_free s2
  | SIfZero _ s1 s2 => stmt_call_free s1 /\ stmt_call_free s2
  | _ => True
  end.

(** Two controls are equal up to thread views. *)
Definition core_upto_view (e1 e2 : pico_core_expr) : Prop :=
  match e1, e2 with
  | CoreRun r1 s1 _ K1, CoreRun r2 s2 _ K2 => r1 = r2 /\ s1 = s2 /\ K1 = K2
  | CoreDone o1 r1 _, CoreDone o2 r2 _ => o1 = o2 /\ r1 = r2
  | _, _ => False
  end.

Section small_step.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table) (D : method_def -> Prop) (P : Loc -> Prop).

  (** Every weak history of an abstract field of a footprint object is
      nonempty and holds only the heap value of that field. *)
  Definition footprint_stable (h : heap) (sigma : wm_state) : Prop :=
    forall l rt fs f,
      P l ->
      runtime_getObj h l = Some (mkObj rt fs) ->
      abstract_field CT (rctype rt) f ->
      values_written_to sigma (l, f) <> @nil value /\
      forall w, List.In w (values_written_to sigma (l, f)) ->
        getVal fs f = Some w.

  (** Continuations of a call-free derivation: sequence frames only. *)
  Inductive deriv_cont : s_env -> pico_core_cont -> Prop :=
    | DerivContNil : forall sΓ,
        deriv_cont sΓ []
    | DerivContSeq : forall sΓ sΓ' mt s K,
        deriv_stmt CT D sΓ s sΓ' ->
        stmt_typing CT sΓ mt s sΓ' ->
        stmt_call_free s ->
        deriv_cont sΓ' K ->
        deriv_cont sΓ (KSeq s :: K).

  (** A control running call-free derivation code in heap [h]. *)
  Definition deriv_control (h : heap) (e : pico_core_expr) : Prop :=
    match e with
    | CoreRun rΓ s _ K =>
        exists sΓ sΓ' mt,
          deriv_stmt CT D sΓ s sΓ' /\
          stmt_typing CT sΓ mt s sΓ' /\
          stmt_call_free s /\
          wf_r_config CT sΓ rΓ h /\
          env_in P rΓ /\
          deriv_cont sΓ' K
    | CoreDone _ _ _ => True
    end.

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

  (** The value of a field read of a derivation, in a footprint-stable state,
      is the heap value of an abstract field of a footprint object. *)
  Lemma deriv_field_read_value :
    forall h1 sigma1 sΓ rΓ y f T C ly V v V',
      footprint_stable h1 sigma1 ->
      wf_r_config CT sΓ rΓ h1 ->
      env_in P rΓ ->
      static_getType sΓ y = Some T ->
      sbase T = TRef C ->
      abstract_field CT C f ->
      runtime_getVal rΓ y = Some (Iot ly) ->
      wm_read sigma1 V (ly, f) v V' ->
      P ly /\
      exists rt fs,
        runtime_getObj h1 ly = Some (mkObj rt fs) /\
        abstract_field CT (rctype rt) f /\
        getVal fs f = Some v.
  Proof.
    intros h1 sigma1 sΓ rΓ y f T C ly V v V' Hstable Hwf Henv Hget Href
      Habs Hval Hread.
    have Hly := Henv y ly Hval.
    split; [exact Hly |].
    destruct (wf_config_env_location sΓ rΓ h1 y ly Hwf Hval)
      as [rt [fs Hobj]].
    have Hsub : class_subtype CT (rctype rt) C.
    { eapply runtime_value_class_subtype;
        [exact Hwf | exact Hget | exact Href | exact Hval |].
      unfold r_basetype. rewrite Hobj. reflexivity. }
    have Habs' := abstract_field_subtype CT (rctype rt) C f Hsub Habs.
    exists rt, fs.
    split; [exact Hobj |].
    split; [exact Habs' |].
    destruct (Hstable ly rt fs f Hly Hobj Habs') as [_ Honly].
    exact (Honly v (values_written_to_read _ _ _ _ _ Hread)).
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

  Ltac same_state := split; [reflexivity |]; split; [reflexivity |].

  Ltac deriv_close :=
    eexists _, _, _;
    split; [eassumption |]; split; [eassumption |];
    split; [eassumption |]; split; [eassumption |];
    split; eassumption.

  (** One step of call-free derivation code, taken in two footprint-agreeing
      states from controls that differ only in their views, leaves both
      states unchanged and yields controls that again differ only in their
      views. *)
  Lemma deriv_step_lockstep :
    forall h1 sigma1 h2 sigma2 rΓ s V1 V2 K e1 S1' e2 S2',
      abs_agree CT P h1 h2 ->
      footprint_stable h1 sigma1 ->
      footprint_stable h2 sigma2 ->
      deriv_control h1 (CoreRun rΓ s V1 K) ->
      pico_core_step CT (CoreRun rΓ s V1 K) (mkPicoCoreState h1 sigma1) e1 S1' ->
      pico_core_step CT (CoreRun rΓ s V2 K) (mkPicoCoreState h2 sigma2) e2 S2' ->
      S1' = mkPicoCoreState h1 sigma1 /\
      S2' = mkPicoCoreState h2 sigma2 /\
      core_upto_view e1 e2 /\
      deriv_control h1 e1.
  Proof.
    intros h1 sigma1 h2 sigma2 rΓ s V1 V2 K e1 S1' e2 S2' Hagree Hst1 Hst2
      (sΓ & sΓ' & mt & Hderiv & Htyp & Hcf & Hwf & Henv & Hcont) Hstep1 Hstep2.
    inversion Hderiv; subst.
    - (* skip *)
      destruct K as [| [s2 | caller x ret] K].
      + inversion Hstep1; subst. inversion Hstep2; subst.
        same_state. split; simpl; auto.
      + inversion Hstep1; subst. inversion Hstep2; subst.
        same_state. split; [simpl; auto |].
        inversion Hcont; subst. simpl. deriv_close.
      + inversion Hcont.
    - (* local declaration *)
      inversion Hstep1; subst. inversion Hstep2; subst.
      same_state. split; [simpl; auto |].
      have Hwf' := preservation_pico CT sΓ mt rΓ h1 (SLocal T x) _ h1
        (sΓ ++ [T]) Hwf Htyp (SBS_Local CT rΓ h1 T x ltac:(eassumption)).
      simpl. exists (sΓ ++ [T]), (sΓ ++ [T]), mt.
      split; [apply DS_Skip |].
      split; [apply ST_Skip; exact (proj1 (proj2 (proj2 (proj2 Hwf')))) |].
      split; [exact I |].
      split; [exact Hwf' |].
      split; [apply env_in_append_default; exact Henv | exact Hcont].
    - (* assignment *)
      destruct Hexpr as [| y | n | y f T C Hget Href Habs].
      + inversion Hstep1; subst. inversion Hstep2; subst.
        same_state. split; [simpl; auto |].
        have Hwf' := preservation_pico CT sΓ' mt rΓ h1 (SVarAss x ENull) _ h1
          sΓ' Hwf Htyp
          (SBS_Assign CT rΓ h1 x ENull _ Null_a ltac:(eassumption)
            (EBS_Null CT rΓ h1)).
        simpl. exists sΓ', sΓ', mt.
        split; [apply DS_Skip |].
        split; [apply ST_Skip; exact (proj1 (proj2 (proj2 (proj2 Hwf')))) |].
        split; [exact I |].
        split; [exact Hwf' |].
        split; [| exact Hcont].
        apply env_in_update; [exact Henv |]. intros l Hl; discriminate.
      + inversion Hstep1; subst. inversion Hstep2; subst.
        match goal with
        | H1 : runtime_getVal rΓ y = Some ?a,
          H2 : runtime_getVal rΓ y = Some ?b |- _ =>
            tryif constr_eq a b then fail
            else (rewrite H1 in H2; injection H2 as Hab; subst)
        end.
        same_state. split; [simpl; auto |].
        have Hwf' := preservation_pico CT sΓ' mt rΓ h1 (SVarAss x (EVar y)) _ h1
          sΓ' Hwf Htyp
          (SBS_Assign CT rΓ h1 x (EVar y) _ _ ltac:(eassumption)
            (EBS_Val CT rΓ h1 y _ ltac:(eassumption))).
        simpl. exists sΓ', sΓ', mt.
        split; [apply DS_Skip |].
        split; [apply ST_Skip; exact (proj1 (proj2 (proj2 (proj2 Hwf')))) |].
        split; [exact I |].
        split; [exact Hwf' |].
        split; [| exact Hcont].
        apply env_in_update; [exact Henv |].
        intros l ->. eapply Henv. eassumption.
      + inversion Hstep1; subst. inversion Hstep2; subst.
        same_state. split; [simpl; auto |].
        have Hwf' := preservation_pico CT sΓ' mt rΓ h1 (SVarAss x (EInt n)) _ h1
          sΓ' Hwf Htyp
          (SBS_Assign CT rΓ h1 x (EInt n) _ (Int n) ltac:(eassumption)
            (EBS_Int CT rΓ h1 n)).
        simpl. exists sΓ', sΓ', mt.
        split; [apply DS_Skip |].
        split; [apply ST_Skip; exact (proj1 (proj2 (proj2 (proj2 Hwf')))) |].
        split; [exact I |].
        split; [exact Hwf' |].
        split; [| exact Hcont].
        apply env_in_update; [exact Henv |]. intros l Hl; discriminate.
      + inversion Hstep1; subst; inversion Hstep2; subst; try congruence.
        * (* both runs read the field *)
          match goal with
          | Hy1 : runtime_getVal rΓ y = Some (Iot ?l1),
            Hy2 : runtime_getVal rΓ y = Some (Iot ?l2),
            Hr1 : wm_read sigma1 _ (?l1, f) ?v1 _,
            Hr2 : wm_read sigma2 _ (?l2, f) ?v2 _ |- _ =>
              assert (Hl : l2 = l1) by congruence; subst l2;
              destruct (deriv_field_read_value h1 sigma1 sΓ' rΓ y f T C l1
                _ v1 _ Hst1 Hwf Henv Hget Href Habs Hy1 Hr1)
                as (Hpub & rt & fs & Hobj1 & Habs' & Hv1);
              destruct (Hagree l1 Hpub)
                as (rt' & fs1 & fs2 & Hobj1' & Hobj2 & Hfields);
              rewrite Hobj1 in Hobj1'; injection Hobj1' as <- <-;
              destruct (Hst2 l1 rt fs2 f Hpub Hobj2 Habs') as [_ Honly2];
              have Hv2 := Honly2 v2 (values_written_to_read _ _ _ _ _ Hr2);
              destruct (Hfields f Habs') as [Heq Hclosed];
              assert (Hvv : v2 = v1) by congruence; subst v2;
              same_state;
              split; [simpl; auto |];
              have Hwf' := preservation_pico CT sΓ' mt rΓ h1
                (SVarAss x (EField y f)) _ h1 sΓ' Hwf Htyp
                (SBS_Assign CT rΓ h1 x (EField y f) _ v1 ltac:(eassumption)
                  (EBS_Field CT rΓ h1 y f l1 (mkObj rt fs) v1 Hy1 Hobj1 Hv1));
              simpl; exists sΓ', sΓ', mt;
              split; [apply DS_Skip |];
              split; [apply ST_Skip; exact (proj1 (proj2 (proj2 (proj2 Hwf')))) |];
              split; [exact I |];
              split; [exact Hwf' |];
              split; [| exact Hcont];
              apply env_in_update; [exact Henv |];
              intros l Hl; subst v1; exact (Hclosed l Hv1)
          end.
        * same_state. split; simpl; auto.
    - (* sequence *)
      inversion Hstep1; subst. inversion Hstep2; subst.
      same_state. split; [simpl; auto |].
      inversion Htyp; subst.
      have Hmid := deriv_stmt_typing_env CT D _ _ _ _ _ Hderiv1 Htype1.
      subst.
      simpl in Hcf. destruct Hcf as [Hcf1 Hcf2].
      simpl. eexists _, _, _.
      split; [exact Hderiv1 |].
      split; [exact Htype1 |].
      split; [exact Hcf1 |].
      split; [exact Hwf |].
      split; [exact Henv |].
      eapply DerivContSeq; eassumption.
    - (* zero test *)
      simpl in Hcf. destruct Hcf as [Hcf0 Hcf1].
      inversion Htyp; subst.
      inversion Hstep1; subst; inversion Hstep2; subst; try congruence;
        same_state; split; simpl; auto; deriv_close.
    - (* call *)
      simpl in Hcf. contradiction.
  Qed.
End small_step.

Section small_step_runs.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table) (D : method_def -> Prop) (P : Loc -> Prop).

  (** Runs of call-free derivation code in two footprint-agreeing states,
      from controls equal up to views, that both complete, complete with the
      same outcome and environment. *)
  Theorem deriv_steps_agree :
    forall h1 sigma1 h2 sigma2 e e' S1f S2f o1 r1 W1 o2 r2 W2,
      abs_agree CT P h1 h2 ->
      footprint_stable CT P h1 sigma1 ->
      footprint_stable CT P h2 sigma2 ->
      deriv_control CT D P h1 e ->
      core_upto_view e e' ->
      pico_core_steps CT e (mkPicoCoreState h1 sigma1) (CoreDone o1 r1 W1) S1f ->
      pico_core_steps CT e' (mkPicoCoreState h2 sigma2) (CoreDone o2 r2 W2) S2f ->
      o1 = o2 /\ r1 = r2.
  Proof.
    intros h1 sigma1 h2 sigma2 e e' S1f S2f o1 r1 W1 o2 r2 W2 Hagree Hst1 Hst2
      Hctl Hview Hsteps1.
    remember (mkPicoCoreState h1 sigma1) as S1 eqn:HS1.
    remember (CoreDone o1 r1 W1) as ef eqn:Hef.
    revert e' Hctl Hview.
    induction Hsteps1 as [e S | e S e1 S1' ef S1'' Hstep Htail IH];
      intros e' Hctl Hview Hsteps2; subst.
    - destruct e' as [rΓ s V K | o r V]; simpl in Hview; [contradiction |].
      destruct Hview as [<- <-].
      inversion Hsteps2; subst.
      + split; reflexivity.
      + exfalso. eapply core_done_no_step; eassumption.
    - destruct e as [rΓ s V1 K | o r V]; [| exfalso; eapply core_done_no_step; eassumption].
      destruct e' as [rΓ' s' V2 K' | o r V]; simpl in Hview; [| contradiction].
      destruct Hview as [<- [<- <-]].
      inversion Hsteps2 as [| e0 S0 e2 S2' ef' S2'' Hstep2 Htail2]; subst.
      destruct (deriv_step_lockstep CT D P h1 sigma1 h2 sigma2 rΓ s V1 V2 K
        e1 S1' e2 S2' Hagree Hst1 Hst2 Hctl Hstep Hstep2)
        as (-> & -> & Hview' & Hctl').
      exact (IH eq_refl eq_refl e2 Hctl' Hview' Htail2).
  Qed.

  Section with_progress.
    Context `{Hprogress : @CacheMemoryModelProgress Hmem}.

    (** Whenever derivation code steps in one state, the same code can step
        in any footprint-agreeing state. *)
    Lemma deriv_step_progress :
      forall h1 sigma1 h2 sigma2 rΓ s V1 V2 K e1 S1',
        abs_agree CT P h1 h2 ->
        footprint_stable CT P h1 sigma1 ->
        footprint_stable CT P h2 sigma2 ->
        deriv_control CT D P h1 (CoreRun rΓ s V1 K) ->
        pico_core_step CT (CoreRun rΓ s V1 K) (mkPicoCoreState h1 sigma1) e1 S1' ->
        exists e2 S2',
          pico_core_step CT (CoreRun rΓ s V2 K) (mkPicoCoreState h2 sigma2) e2 S2'.
    Proof.
      intros h1 sigma1 h2 sigma2 rΓ s V1 V2 K e1 S1' Hagree Hst1 Hst2
        Hctl Hstep1.
      inversion Hstep1; subst;
        try (eexists _, _; econstructor; eassumption);
        destruct Hctl as (sΓ & sΓ' & mt & Hderiv & _ & Hcf & Hwf & Henv & _);
        inversion Hderiv; subst; try (simpl in Hcf; contradiction).
      (* field read *)
      inversion Hexpr as [| | | y0 f0 T C Hget Href Habs]; subst.
      destruct (deriv_field_read_value CT P h1 sigma1 sΓ' rΓ y f T C loc_y
        _ v _ Hst1 Hwf Henv Hget Href Habs ltac:(eassumption) ltac:(eassumption))
        as (Hpub & rt & fs & Hobj1 & Habs' & _).
      destruct (Hagree loc_y Hpub) as (rt' & fs1 & fs2 & Hobj1' & Hobj2 & _).
      rewrite Hobj1 in Hobj1'. injection Hobj1' as <- <-.
      destruct (Hst2 loc_y rt fs2 f Hpub Hobj2 Habs') as [Hnonempty _].
      assert (Hhist : history_of sigma2 (loc_y, f) <> []).
      { intros Hnil. apply Hnonempty. unfold values_written_to.
        rewrite Hnil. reflexivity. }
      destruct (wm_read_nonempty sigma2 V2 (loc_y, f) Hhist) as (v2 & V2' & Hread).
      eexists _, _. eapply PCS_AssignField; eassumption.
    Qed.

    (** A completed run in one state is matched by a completed run with the
        same outcome and environment in any footprint-agreeing state. *)
    Theorem deriv_steps_simulation :
      forall h1 sigma1 h2 sigma2 e e' S1f o r W,
        abs_agree CT P h1 h2 ->
        footprint_stable CT P h1 sigma1 ->
        footprint_stable CT P h2 sigma2 ->
        deriv_control CT D P h1 e ->
        core_upto_view e e' ->
        pico_core_steps CT e (mkPicoCoreState h1 sigma1) (CoreDone o r W) S1f ->
        exists W',
          pico_core_steps CT e' (mkPicoCoreState h2 sigma2)
            (CoreDone o r W') (mkPicoCoreState h2 sigma2).
    Proof.
      intros h1 sigma1 h2 sigma2 e e' S1f o r W Hagree Hst1 Hst2 Hctl Hview
        Hsteps1.
      remember (mkPicoCoreState h1 sigma1) as S1 eqn:HS1.
      remember (CoreDone o r W) as ef eqn:Hef.
      revert e' Hctl Hview.
      induction Hsteps1 as [e S | e S e1 S1' ef S1'' Hstep Htail IH];
        intros e' Hctl Hview; subst.
      - destruct e' as [rΓ s V K | o' r' V']; simpl in Hview; [contradiction |].
        destruct Hview as [<- <-].
        exists V'. constructor.
      - destruct e as [rΓ s V1 K | o0 r0 V0];
          [| exfalso; eapply core_done_no_step; eassumption].
        destruct e' as [rΓ' s' V2 K' | o0 r0 V0]; simpl in Hview; [| contradiction].
        destruct Hview as [<- [<- <-]].
        destruct (deriv_step_progress h1 sigma1 h2 sigma2 rΓ s V1 V2 K e1 S1'
          Hagree Hst1 Hst2 Hctl Hstep) as (e2 & S2' & Hstep2).
        destruct (deriv_step_lockstep CT D P h1 sigma1 h2 sigma2 rΓ s V1 V2 K
          e1 S1' e2 S2' Hagree Hst1 Hst2 Hctl Hstep Hstep2)
          as (-> & -> & Hview' & Hctl').
        destruct (IH eq_refl eq_refl e2 Hctl' Hview') as (W' & Hsteps2).
        exists W'. econstructor; eassumption.
    Qed.
  End with_progress.
End small_step_runs.

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

(** The derivation selected for [o] has a call-free body. *)
Definition derivation_call_free (CT : class_table) (m : method_name)
    (h : heap) (o : Loc) : Prop :=
  forall cy mdef,
    r_basetype h o = Some cy ->
    FindMethodWithName CT cy m mdef ->
    stmt_call_free (mbody_stmt (mbody mdef)).

Section small_step_noninterference.
  Context `{Hmem : CacheMemoryModel}.
  Context `{Hprogress : @CacheMemoryModelProgress Hmem}.
  Context (CT : class_table) (D : method_def -> Prop) (P : Loc -> Prop).

  Lemma derivation_entry_control :
    forall m h o cy mdef V,
      derivation_table CT D ->
      derivation_ready CT D m h o ->
      derivation_call_free CT m h o ->
      P o ->
      r_basetype h o = Some cy ->
      FindMethodWithName CT cy m mdef ->
      deriv_control CT D P h
        (CoreRun (mkr_env [Iot o]) (mbody_stmt (mbody mdef)) V []).
  Proof.
    intros m h o cy mdef V Htable Hready Hcf Ho Hbase Hfind.
    destruct (derivation_ready_body CT D m h o cy mdef Htable Hready Hbase Hfind)
      as (sΓd & Hderiv & Htyping & Hwf).
    exists [mreceiver (msignature mdef)], sΓd, (mscope (msignature mdef)).
    split; [exact Hderiv |].
    split; [exact Htyping |].
    split; [exact (Hcf cy mdef Hbase Hfind) |].
    split; [exact Hwf |].
    split; [exact (env_in_receiver_frame P o Ho) |].
    constructor.
  Qed.

  (** Small-step noninterference.  In two core states that agree on a public
      footprint [P] containing the receiver, and whose footprint histories hold
      only the heap values, a call-free derivation method returns the same
      value: every result in the first state is a result in the second, and
      the second has no other result. *)
  Theorem derivation_noninterference_small_step :
    forall m h1 sigma1 h2 sigma2 o v,
      derivation_table CT D ->
      derivation_ready CT D m h1 o ->
      derivation_call_free CT m h1 o ->
      P o ->
      abs_agree CT P h1 h2 ->
      footprint_stable CT P h1 sigma1 ->
      footprint_stable CT P h2 sigma2 ->
      derived_ss CT m (mkPicoCoreState h1 sigma1) o v ->
      derived_ss CT m (mkPicoCoreState h2 sigma2) o v /\
      (forall w, derived_ss CT m (mkPicoCoreState h2 sigma2) o w -> w = v).
  Proof.
    intros m h1 sigma1 h2 sigma2 o v Htable Hready Hcf Ho Hagree Hst1 Hst2
      (cy & mdef & V & rΓ' & V' & S' & Hbase & Hfind & Hsteps & Hret).
    simpl in Hbase.
    have Hctl := derivation_entry_control m h1 o cy mdef V Htable Hready Hcf Ho
      Hbase Hfind.
    have Hbase2 : r_basetype h2 o = Some cy.
    { rewrite (abs_agree_basetype CT P h1 h2 o Hagree Ho). exact Hbase. }
    split.
    - destruct (deriv_steps_simulation CT D P h1 sigma1 h2 sigma2 _
        (CoreRun (mkr_env [Iot o]) (mbody_stmt (mbody mdef)) V [])
        S' OK rΓ' V' Hagree Hst1 Hst2 Hctl ltac:(simpl; auto) Hsteps)
        as (W' & Hsteps2).
      exists cy, mdef, V, rΓ', W', (mkPicoCoreState h2 sigma2).
      split; [exact Hbase2 |].
      split; [exact Hfind |].
      split; [exact Hsteps2 | exact Hret].
    - intros w (cy2 & mdef2 & V2 & rΓ2 & V2' & S2' & Hbase2' & Hfind2 & Hsteps2
        & Hret2).
      simpl in Hbase2'.
      rewrite Hbase2 in Hbase2'. injection Hbase2' as <-.
      have Hmdef := find_method_with_name_deterministic CT cy m mdef2 mdef
        Hfind2 Hfind.
      subst mdef2.
      destruct (deriv_steps_agree CT D P h1 sigma1 h2 sigma2 _
        (CoreRun (mkr_env [Iot o]) (mbody_stmt (mbody mdef)) V2 [])
        S' S2' OK rΓ' V' OK rΓ2 V2' Hagree Hst1 Hst2 Hctl ltac:(simpl; auto)
        Hsteps Hsteps2) as [_ <-].
      congruence.
  Qed.
End small_step_noninterference.
