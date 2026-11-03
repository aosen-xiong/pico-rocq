From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels ArgViews
  GhostTyping GhostForget GhostFit ArgTyping GhostInvariant ArgFit
  ArgInvariant ArgEntry ArgStatements ArgOverriding ArgCalls.

(** Place in the proof: the end of the chain.  The starting-state hypothesis
    in the payload reading (RSFp) is kept by every well-typed execution; the
    bound condition on protected methods is reduced to what the typing rules
    give; the final theorems, from a program start; and the same for every
    call of a run, at any depth.
    Counterpart in the non-generic proof (ReadonlyWorlds.v): "the theorems". *)

(** READING ORDER OF THE GENERIC PROOF.  After the language (Syntax to
    Bigstep), ordinary preservation and the non-generic proofs (ReadonlyFlat,
    ReadonlyWorlds), the files are read in this order:

    ReadonlyGeneric   the earlier generic proof for clean class tables; lemmas reused
    GhostLabels       world labels inside type arguments; agreement up to dead worlds
    ArgViews          superclass views off the type arguments; the payload; the plain view
    GhostTyping       the ghost state; labelled views; values; the ghost heap clause
    GhostForget       forgetting mutable positions (a written Mut becomes Lost)
    GhostFit          objects fit their class bounds in the labelled reading; killing
    ArgTyping         values and labelled subtyping over payload views
    GhostInvariant    the ghost invariant: activation part, transport, allocation data
    ArgFit            header-frame fits and their step to the parent class
    ArgInvariant      the invariant over payload views (heapP, frameP)
    ArgStatements     the statement cases; classes whose bounds write no mutable position
    ArgOverriding     overriding, at the level of labels and over payload views; a
                      receiver-dependent declared receiver
    ArgCalls          calls, at both levels, and the main step
    ArgEntry          the state at the start of a protected call, at both levels
    ArgTheorems       this file: the invariant is kept, the bound condition on
                      protected methods, the theorems, every call of a run

    Each of the last five files has one part per earlier layer, marked
    PART 1, PART 2, ...: the level of labels first, payload views after it.
    Outside the proof, kept for the probes: GhostShadow, OverrideCheck. *)

(* ------------------PART 1: THE INVARIANT IS KEPT------------------*)

(** The starting-state hypothesis in the payload reading is kept by every
    well-typed execution. *)

(* ------------------COHERENCE FOLLOWS FROM THE FITS------------------*)

(** What is used of a bound written mutable: its own arguments are fully
    known and satisfy its class's bounds. *)
Definition mbounds (CT : class_table) (Δ : tv_env) : Prop :=
  forall o n K Bs, tv_bound Δ o n = Some (TClass Mut K Bs) ->
    Forall lost_free Bs /\
    exists Δ0,
      readonly_state_method_scope (tv_mode Δ0) /\
      (forall o' n' B', tv_bound Δ0 o' n' = Some B' ->
         tv_bound Δ o' n' = Some B') /\
      forall def, find_class CT K = Some def ->
        Forall2
          (fun T B =>
             lost_free (subst Bs [] [] (adapt AbstractState Mut B)) ->
             bound_sub CT Δ0 T (subst Bs [] [] (adapt AbstractState Mut B)))
          Bs (ctparams (signature def)).

(* ------------------THE HEAP PART------------------*)

(** Every object's arguments fit its class's bounds in the payload reading,
    with every label outside, and its class can have objects. *)
Definition rsfitp_heap0 (CT : class_table) (h : heap) : Prop :=
  forall l o def,
    runtime_getObj h l = Some o ->
    find_class CT (rctype (rt_type o)) = Some def ->
    (forall L, frame_fitsp CT L (class_env def)
       (hfr CT (rqtype (rt_type o)) LOut (rctype (rt_type o))
          (map lift (rtargs (rt_type o))))) /\
    livec CT (rctype (rt_type o)).

Lemma class_mbounds : forall CT C def,
  wf_class_table CT -> find_class CT C = Some def -> livec CT C ->
  mbounds CT (with_mode (class_env def) ReadonlyState).
Proof.
  intros CT C def Hct Hfind Hlv o n K Bs Hb.
  destruct (tv_bound_class_env def o n _ Hb) as [-> Hnb].
  pose proof (class_bounds_wf _ _ _ Hct Hfind) as Hwfb.
  rewrite Forall_forall in Hwfb.
  pose proof (Hwfb _ (nth_error_In _ _ Hnb)) as HwB.
  pose proof (Hlv def Hfind) as Hlf. rewrite Forall_forall in Hlf.
  pose proof (Hlf _ (nth_error_In _ _ Hnb)) as HlB.
  apply lost_free_class in HlB. destruct HlB as [_ HlBs].
  split; [exact HlBs|].
  exists (with_mode (class_env def) ReadonlyState).
  refine (conj (or_introl eq_refl) (conj (fun _ _ _ H => H) _)).
  intros dK HdK.
  inversion HwB as [? ? ? dK' HfK' Hhead Hlen Hargs Hbounds| |]; subst.
  rewrite HdK in HfK'. inversion HfK'; subst dK'.
  eapply Forall2_impl; [|exact Hbounds]. intros a b Hab _. exact Hab.
Qed.

(** The per-object invariant of the starting heap. *)
Lemma obP_ofL : forall CT h,
  wf_class_table CT -> wf_heap CT h ->
  rsfit_heap CT h -> rsfitp_heap0 CT h ->
  forall L l o, runtime_getObj h l = Some o ->
    obP CT L (rqtype (rt_type o)) None (rctype (rt_type o))
      (map lift (rtargs (rt_type o))) /\
    livec CT (rctype (rt_type o)).
Proof.
  intros CT h Hct Hheap Hh Hp L l o Ho.
  pose proof (Hheap l (runtime_getObj_dom _ _ _ Ho)) as Hwfo.
  unfold wf_obj in Hwfo. rewrite Ho in Hwfo. destruct Hwfo as (Hrt & _).
  unfold wf_rtypeuse in Hrt.
  destruct (find_class CT (rctype (rt_type o))) as [def|] eqn:Hfind;
    [|contradiction].
  destruct Hrt as (Hag & Hlf & Hb).
  destruct (Hp l o def Ho Hfind) as [Hfp Hlv].
  assert (Hi : hinv CT L (rqtype (rt_type o)) LOut (rctype (rt_type o))
                 (map lift (rtargs (rt_type o)))).
  { refine (conj _ (conj _ _)).
    - intros d Hd. rewrite hfr_lift.
      exact (rsfit_heap_obj CT h l o d Hh Ho Hd L).
    - rewrite map_erase_lift. exact Hlf.
    - intros d Hd. rewrite Hfind in Hd. inversion Hd; subst d.
      split; [exact Hag|]. intros _. rewrite hfr_lift. reflexivity. }
  split; [|exact Hlv].
  refine (conj Hi (conj _ _)).
  - intros w Hc. discriminate.
  - intros D Vs dd Hv Hfd.
    exact (fitsp_oview CT L _ _ _ _ D Vs Hct Hv Hi dd Hfd).
Qed.

Lemma obP_of : forall CT h,
  wf_class_table CT -> wf_heap CT h ->
  rsfit_heap CT h -> rsfitp_heap0 CT h ->
  rsfitp_heap CT h.
Proof. intros CT h Hct Hheap Hh Hp l o Ho. eapply obP_ofL; eauto. Qed.

Print Assumptions obP_of.

(* ------------------ALLOCATION------------------*)

(** What is used of the bounds in scope. *)
Definition sbounds (CT : class_table) (Δ : tv_env) : Prop :=
  (forall o n B, tv_bound Δ o n = Some B -> is_class_type B) /\
  mbounds CT (with_mode Δ ReadonlyState).

(** Allocation keeps the heap part. *)
Lemma rsfp_new : forall CT Δ sΓ rΓ h mt x qc C Ts ys sΓ' l1 qthisr vals,
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt (SNew x qc C Ts ys) sΓ' ->
  runtime_getVal rΓ 0 = Some (Iot l1) ->
  r_muttype h l1 = Some qthisr ->
  RSF CT Δ rΓ h -> rsfitp_heap0 CT h -> rsfitp_frame CT Δ rΓ h ->
  sbounds CT Δ ->
  rsfitp_heap0 CT
    (h ++ [mkObj
             (mkruntime_type (vpa_mutability_object_creation qthisr qc) C
                (map (dyn (qr2q qthisr) (cargs rΓ) (margs rΓ) (qargs rΓ)) Ts))
             vals]).
Proof.
  intros CT Δ sΓ rΓ h mt x qc C Ts ys sΓ' l1 qthisr vals
    Hwf Htype Hthis0 Hmut HR Hp Hfrp Hsb.
  (* the ghost layer's fit of the new heap, read in the payload order *)
  pose proof (rsf_new CT Δ sΓ rΓ h mt x qc C Ts ys sΓ' l1 qthisr vals
                Hwf Htype Hthis0 Hmut HR) as Hh'.
  pose proof Hwf as (Hct & _).
  inversion Htype; subst.
  assert (Hlvc : Forall lost_free (ctparams (signature def))).
  { assert (Hgen : forall Xs Bs,
              Forall2
                (fun T B =>
                   lost_free (member_type AbstractState (qc2q qc) Ts [] [] B) /\
                   bound_sub CT Δ T (member_type AbstractState (qc2q qc) Ts [] [] B))
                Xs Bs -> Forall lost_free Bs).
    { intros Xs Bs HF2. induction HF2 as [|T B Xs Bs [Hlf _] _ IH];
        constructor; auto.
      apply (lost_free_inst_inv (vpa_q AbstractState (qc2q qc)) Ts [] [] B);
        [destruct qc; reflexivity | exact Hlf]. }
    exact (Hgen _ _ (alloc_bounds_mode_bridge _ _ _ _ _ _ Hbounds)). }
  intros l o0 def0 Ho Hfc. split.
  - intros L. rewrite hfr_lift. apply frame_fitsp_of_fits.
    exact (rsfit_heap_obj CT _ l o0 def0 Hh' Ho Hfc L).
  - destruct (Nat.eq_dec l (dom h)) as [-> | Hne].
    + rewrite runtime_getObj_last in Ho. inversion Ho; subst o0.
      cbn [rt_type rctype] in Hfc |- *.
      rewrite Hfind in Hfc. inversion Hfc; subst def0.
      intros d Hd. rewrite Hfind in Hd. inversion Hd; subst d. exact Hlvc.
    + assert (Hl : l < dom h).
      { apply runtime_getObj_dom in Ho. rewrite length_app in Ho. simpl in Ho. lia. }
      rewrite runtime_getObj_last2 in Ho; auto.
      exact (proj2 (Hp l o0 def0 Ho Hfc)).
Qed.

Print Assumptions rsfp_new.

(* ------------------THE BOUNDS IN SCOPE OF A CALLEE------------------*)

Lemma lost_free_of_dyn : forall qctx ca ma ka T,
  rlost_free (dyn qctx ca ma ka T) -> lost_free T.
Proof.
  intros qctx ca ma ka T. induction T using qualified_type_ind'; intros Hl.
  - cbn [dyn] in Hl. apply rlost_free_class in Hl. destruct Hl as [Hq Hargs].
    apply (lost_free_class qual C args). split.
    + intros ->. apply Hq. destruct qctx; reflexivity.
    + clear Hq. induction H as [|t r Ht _ IH]; constructor;
        simpl in Hargs; inversion Hargs; subst; auto.
  - destruct u as [|q0|mp]; simpl; auto.
    intros ->. cbn [dyn] in Hl.
    destruct (match tv_lookup o ca ma n with Some R => R | None => default_rtype end)
      as [q1 C1 args1].
    replace (dynq qctx Lost) with Lost in Hl by (destruct qctx; reflexivity).
    simpl in Hl. destruct Hl as [Hx _]. congruence.
  - cbn [dyn] in Hl. apply rlost_free_class in Hl. destruct Hl as [_ Hargs].
    apply lost_free_head.
    induction H as [|t r Ht _ IH]; constructor;
      simpl in Hargs; inversion Hargs; subst; auto.
Qed.

Lemma rsuper_live : forall CT qh C Rs D Vs,
  wf_class_table CT -> rsuper_inst CT qh C Rs D Vs -> livec CT C -> livec CT D.
Proof.
  intros CT qh C Rs D Vs Hct H. induction H; intros Hlv; auto.
  apply IHrsuper_inst. eapply live_parent; eauto.
Qed.

Lemma sbounds_callee : forall CT D' defD mdef',
  wf_class_table CT ->
  find_class CT D' = Some defD ->
  livec CT D' ->
  wf_method CT D' mdef' ->
  Forall lost_free (mtparams (msignature mdef')) ->
  sbounds CT (method_tv_env CT D' (msignature mdef')).
Proof.
  intros CT D' defD mdef' Hct Hfind Hlv Hwm Hlfm.
  pose proof Hwm as (_ & Hmb & _).
  assert (Hcv : forall n B,
            tv_bound (method_tv_env CT D' (msignature mdef')) ClassVar n = Some B ->
            nth_error (ctparams (signature defD)) n = Some B).
  { intros n B Hb. unfold tv_bound, method_tv_env, class_tparams in Hb.
    simpl in Hb. rewrite Hfind in Hb. exact Hb. }
  split.
  - intros o n B Hb. destruct o.
    + pose proof (class_bounds_class _ _ _ Hct Hfind) as Hall.
      rewrite Forall_forall in Hall. apply Hall.
      eapply nth_error_In. exact (Hcv n B Hb).
    + rewrite Forall_forall in Hmb.
      exact (proj1 (Hmb B (nth_error_In _ _ Hb))).
  - intros o n K Bs Hb. destruct o.
    + pose proof (Hcv n _ Hb) as HbC.
      destruct (class_mbounds CT D' defD Hct Hfind Hlv ClassVar n K Bs HbC)
        as [Hl (Δ0 & Hrs0 & Hsub0 & Hbs)].
      split; [exact Hl|]. exists Δ0. refine (conj Hrs0 (conj _ Hbs)).
      intros o' n' B' Hb'. apply Hsub0 in Hb'.
      destruct (tv_bound_class_env defD o' n' B' Hb') as [-> Hnb].
      unfold tv_bound, with_mode, method_tv_env, class_tparams. simpl.
      rewrite Hfind. exact Hnb.
    + assert (HbM : nth_error (mtparams (msignature mdef')) n =
                    Some (TClass Mut K Bs)) by exact Hb.
      rewrite Forall_forall in Hlfm.
      pose proof (Hlfm _ (nth_error_In _ _ HbM)) as HlB.
      apply lost_free_class in HlB. destruct HlB as [_ HlBs].
      split; [exact HlBs|].
      exists (with_mode (method_tv_env CT D' (msignature mdef')) ReadonlyState).
      refine (conj (or_introl eq_refl) (conj (fun _ _ _ H => H) _)).
      intros dK HdK.
      rewrite Forall_forall in Hmb.
      destruct (Hmb _ (nth_error_In _ _ HbM)) as [_ [HwB _]].
      inversion HwB as [? ? ? dK' HfK' Hhead Hlen Hargs Hbounds| |]; subst.
      rewrite HdK in HfK'. inversion HfK'; subst dK'.
      eapply Forall2_impl; [|exact Hbounds].
      intros a b Hab Hl m0. exact (Hab m0).
Qed.

(* ------------------CALLS------------------*)

(** At a call, the callee's activation fits its bounds in the payload
    reading. *)
Lemma rsfp_call : forall CT Δ sΓ rΓ h mt x m y Us Qs zs sΓ' ly cy D' mdef' vals rΓ',
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
  runtime_getVal rΓ y = Some (Iot ly) ->
  r_basetype h ly = Some cy ->
  FindMethodWithName CT cy m D' mdef' ->
  runtime_lookup_list rΓ zs = Some vals ->
  callee_env CT rΓ h ly D' Us Qs vals rΓ' ->
  RSF CT Δ rΓ h -> rsfitp_heap0 CT h -> rsfitp_frame CT Δ rΓ h ->
  sbounds CT Δ ->
  rsfitp_frame CT (method_tv_env CT D' (msignature mdef')) rΓ' h.
Proof.
  intros CT Δ sΓ rΓ h mt x m y Us Qs zs sΓ' ly cy D' mdef' vals rΓ'
    Hwf Htype Hvy Hbase Hfind Hvals Henv HR _ _ _.
  (* the ghost layer's fit of the callee's activation, read in the payload order *)
  pose proof (rsf_call CT Δ sΓ rΓ h mt x m y Us Qs zs sΓ' ly cy D' mdef' vals rΓ'
                Hwf Htype Hvy Hbase Hfind Hvals Henv HR) as Hfr.
  intros ι o Hth Ho L. apply frame_fitsp_of_fits. exact (Hfr ι o Hth Ho L).
Qed.

Print Assumptions rsfp_call.

Lemma rsfp_call_sb : forall CT Δ sΓ rΓ h mt x m y Us Qs zs sΓ' ly cy D' mdef' vals rΓ',
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
  runtime_getVal rΓ y = Some (Iot ly) ->
  r_basetype h ly = Some cy ->
  FindMethodWithName CT cy m D' mdef' ->
  runtime_lookup_list rΓ zs = Some vals ->
  callee_env CT rΓ h ly D' Us Qs vals rΓ' ->
  RSF CT Δ rΓ h -> rsfitp_heap0 CT h -> rsfitp_frame CT Δ rΓ h ->
  sbounds CT Δ ->
  sbounds CT (method_tv_env CT D' (msignature mdef')).
Proof.
  intros CT Δ sΓ rΓ h mt x m y Us Qs zs sΓ' ly cy D' mdef' vals rΓ'
    Hwf Htype Hvy Hbase Hfind Hvals Henv [Hh Hfr] Hp Hfrp Hsb.
  inversion Htype; subst.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & _ & Hlc & Hlm & Hfb).
  pose proof Hwf as (Hct & Hheap & _).
  pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_y) as Hyty.
  rewrite Hvy in Hyty.
  pose proof (wf_r_typable_ubound _ _ _ _ _ _ _ _ _ _ Hfb Hub Hyty) as Hyty'.
  destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ _ Hyty')
    as (oy & Rs1 & Hoy & Hhead & Hsup1 & Hle1).
  pose proof (Hheap ly (runtime_getObj_dom _ _ _ Hoy)) as Hwfo.
  unfold wf_obj in Hwfo. rewrite Hoy in Hwfo. destruct Hwfo as (Hrt_oy & _).
  unfold r_basetype in Hbase. rewrite Hoy in Hbase. inversion Hbase; subst cy.
  clear Hbase.
  destruct oy as [[qr Co Ro] fso]. simpl in *.
  destruct Henv as (lt & qt & oy' & ca' & Hlt & Hqt & Hoy' & Hsupc & ->).
  rewrite Hoy in Hoy'. inversion Hoy'; subst oy'. clear Hoy'. simpl in Hsupc.
  apply get_this_runtime_getVal in Hlt.
  assert (lt = ι) by congruence. subst lt.
  unfold r_muttype in Hqt. rewrite Hobj in Hqt. inversion Hqt; subst qt. clear Hqt.
  set (qctx := rqtype (rt_type o)) in *.
  set (margs' := map (dyn (qr2q qctx) (cargs rΓ) (margs rΓ) (qargs rΓ)) Us) in *.
  set (kargs' := map (rqarg (qr2q qctx) (qargs rΓ)) Qs) in *.
  destruct (super_inst_dyn _ _ _ _ _ _ _ Hsuper (qr2q qr) (qr2q qctx)
              (cargs rΓ) (margs rΓ) (qargs rΓ) Rs1) as (caD & HsupX & HleX); auto.
  { intros q0. apply dynq_vpa_q_agree; auto using qr2q_concrete. }
  pose proof (rsuper_inst_trans _ _ _ _ _ _ Hsup1 _ _ HsupX) as HsupD.
  pose proof (rsuper_wf _ _ _ _ _ _ Hct Hsupc Hrt_oy) as Hview.
  unfold wf_rtypeuse in Hview. simpl in Hview.
  destruct (find_class CT D') as [defD|] eqn:HfD; [|contradiction].
  assert (Hlm' : Forall rlost_free margs').
  { apply map_dyn_lost_free; auto using qr2q_concrete. }
  assert (Hmrefl : Forall2 rarg_sub margs' margs') by apply Forall2_rarg_sub_refl.
  assert (HbD : rbounds_ok CT (qr2q qr) caD margs' kargs' margs'
                  (mtparams (msignature mdef))).
  { unfold rbounds_ok. unfold margs' at 2.
    eapply Forall2_map_left; [exact Htargs_bnd|].
    intros U B0 [HlfB Hsub]. apply bound_sub_self in Hsub. simpl in HlfB, Hsub.
    pose proof (subtype_dyn _ _ _ _ _ _ _ _ (qr2q_concrete _) Hfb Hsub) as Hrs0.
    unfold member_type in Hrs0. rewrite dyn_subst in Hrs0.
    rewrite (dyn_adapt_exact mt qr qctx qy caD
               (map (dyn (qr2q qctx) (cargs rΓ) (margs rΓ) (qargs rΓ)) Vs)
               margs' margs' kargs' B0); auto.
    unfold margs', kargs'. rewrite <- dyn_subst.
    apply dyn_lost_free; auto using qr2q_concrete. }
  assert (Hklen : length kargs' = mqparams (msignature mdef)).
  { unfold kargs'. rewrite length_map. exact Hqargs_len. }
  assert (Hconc : lf_q (LF qctx (cargs rΓ) (margs rΓ) (qargs rΓ)) = Mut \/
                  lf_q (LF qctx (cargs rΓ) (margs rΓ) (qargs rΓ)) = Imm).
  { simpl. destruct qctx; auto. }
  apply (sbounds_callee CT D' defD mdef' Hct HfD).
  - apply (rsuper_live CT _ Co Ro D' ca' Hct Hsupc).
    pose proof Hrt_oy as Hrt0. unfold wf_rtypeuse in Hrt0. simpl in Hrt0.
    destruct (find_class CT Co) as [dCo|] eqn:HfCo; [|contradiction].
    exact (proj2 (Hp ly _ dCo Hoy HfCo)).
  - exact (find_method_wf _ _ _ _ _ Hct Hfind).
  - apply Forall_forall. intros B HB.
    apply In_nth_error in HB. destruct HB as [n HbM].
    pose proof (lookup_bounds_eq CT qr Co Ro C Rs1 Hct Hsup1 Hrt_oy _ _ _ _ _ _ _
                  margs' kargs' Hfind Hfind_m Hsupc HsupD Hklen HbD) as Heq.
    pose proof (f_equal (fun l => nth_error l n) Heq) as HnE. simpl in HnE.
    rewrite nth_error_map in HnE. rewrite nth_error_map in HnE.
    rewrite HbM in HnE.
    destruct (nth_error (mtparams (msignature mdef)) n) as [Bs|] eqn:HBs;
      simpl in HnE; [|discriminate].
    inversion HnE as [HdynEq].
    pose proof (Forall2_nth_error_rel _ _ _ n Htargs_bnd) as Hrel.
    rewrite HBs in Hrel.
    destruct (nth_error Us n) as [U|] eqn:HU; [|contradiction].
    destruct Hrel as [HlfB HsubB].
    apply (lost_free_of_dyn (qr2q qr) ca' margs' kargs'). rewrite HdynEq.
    rewrite (dyn_adapt_exact mt qr qctx qy caD
               (map (dyn (qr2q qctx) (cargs rΓ) (margs rΓ) (qargs rΓ)) Vs)
               margs' margs' kargs' Bs); auto;
      unfold margs', kargs'; rewrite <- dyn_subst;
      apply dyn_lost_free; auto using qr2q_concrete.
Qed.

Print Assumptions rsfp_call_sb.

(* ------------------THE INVARIANT------------------*)

(** The starting-state condition: the bounds are satisfied in the protected
    reading, in the earlier form and in the payload form, and the bounds in
    scope are well formed. *)
Definition RSFp (CT : class_table) (Δ : tv_env) (rΓ : r_env) (h : heap) : Prop :=
  RSF CT Δ rΓ h /\ rsfitp_heap0 CT h /\ rsfitp_frame CT Δ rΓ h /\ sbounds CT Δ.

Lemma rsfitp_heap0_update : forall CT h lx ox f0 vy,
  rsfitp_heap0 CT h -> runtime_getObj h lx = Some ox ->
  rsfitp_heap0 CT (update_field h lx f0 vy).
Proof.
  intros CT h lx ox f0 vy Hp Hox l o def Ho Hfc.
  destruct (Nat.eq_dec lx l) as [-> | Hne].
  - rewrite (update_field_getObj_same _ _ _ _ _ Hox) in Ho.
    inversion Ho; subst o. simpl in *. exact (Hp l ox def Hox Hfc).
  - rewrite update_field_getObj_diff in Ho; auto. exact (Hp l o def Ho Hfc).
Qed.

Lemma rsfitp_frame_step : forall CT Δ sΓ mt s sΓ' rΓ h rΓ' h',
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt s sΓ' ->
  eval_stmt CT rΓ h s OK rΓ' h' ->
  rsfitp_frame CT Δ rΓ h -> rsfitp_frame CT Δ rΓ' h'.
Proof.
  intros CT Δ sΓ mt s sΓ' rΓ h rΓ' h' Hwf Htype Heval Hfr ι o' Hth Ho' L.
  destruct (eval_stmt_frame _ _ _ _ _ _ Heval _ _ _ _ Htype) as (Hte & Hce & Hme).
  destruct (wf_r_config_this _ _ _ _ _ Hwf) as (ι0 & o & Hthis & Hobj & _).
  assert (ι = ι0) by congruence. subst ι0.
  destruct (heap_ext_getObj _ _ _ _ (eval_stmt_heap_ext _ _ _ _ _ _ _ Heval) Hobj)
    as (o2 & Ho2 & Hrt).
  rewrite Ho' in Ho2. inversion Ho2; subst o2.
  rewrite Hrt. rewrite Hce. rewrite Hme.
  rewrite (eval_stmt_qargs _ _ _ _ _ _ _ Heval eq_refl). exact (Hfr ι o Hthis Hobj L).
Qed.

(** Every well-typed statement, in any mode, keeps the heap part. *)
Lemma rsfitp_heap0_preservation : forall CT,
  forall rΓ h s res rΓ' h',
    eval_stmt CT rΓ h s res rΓ' h' ->
    res = OK ->
    forall Δ sΓ mt sΓ',
      wf_r_config CT Δ sΓ rΓ h ->
      stmt_typing CT Δ sΓ mt s sΓ' ->
      RSFp CT Δ rΓ h ->
      rsfitp_heap0 CT h'.
Proof.
  intros CT rΓ h s res rΓ' h' Heval.
  induction Heval; intros Hres Δ sΓ mt0 sΓ' Hwf Htype HR; try discriminate;
    try exact (proj1 (proj2 HR)).
  - (* field write *)
    subst. exact (rsfitp_heap0_update CT h _ _ _ _ (proj1 (proj2 HR)) Hobj).
  - (* new *)
    subst. destruct HR as (H1 & H2 & H3 & H4). eapply rsfp_new; eauto.
  - (* call *)
    subst.
    destruct (call_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                _ Hwf Htype Hval_y Hbase Hfind Hargs Hframe)
      as (ι & o & oy & Tx & _ & _ & _ & _ & _ & _ & _ & Hwm & Hcfg & _).
    pose proof Hwm as (_ & _ & _ & (sΓb & Tb & Hbody & _) & _).
    destruct HR as (H1 & H2 & H3 & H4).
    eapply (IHHeval eq_refl _ _ _ _ Hcfg Hbody).
    refine (conj (conj (proj1 H1) _) (conj H2 (conj _ _))).
    + exact (rsf_call CT Δ sΓ rΓ h mt0 x m y Us Qs zs sΓ' ly cy D mdef vals rΓ'
               Hwf Htype Hval_y Hbase Hfind Hargs Hframe H1).
    + exact (rsfp_call CT Δ sΓ rΓ h mt0 x m y Us Qs zs sΓ' ly cy D mdef vals rΓ'
               Hwf Htype Hval_y Hbase Hfind Hargs Hframe H1 H2 H3 H4).
    + exact (rsfp_call_sb CT Δ sΓ rΓ h mt0 x m y Us Qs zs sΓ' ly cy D mdef vals rΓ'
               Hwf Htype Hval_y Hbase Hfind Hargs Hframe H1 H2 H3 H4).
  - (* sequence *)
    inversion Htype; subst.
    pose proof (IHHeval1 eq_refl _ _ _ _ Hwf Htype1 HR) as Hh1.
    pose proof (preservation_pico _ _ _ _ _ _ _ Heval1 eq_refl _ _ _ _ Hwf Htype1)
      as Hwf1.
    destruct HR as (H1 & H2 & H3 & H4).
    eapply (IHHeval2 eq_refl _ _ _ _ Hwf1 Htype2).
    refine (conj _ (conj Hh1 (conj _ H4))).
    + exact (rsf_preservation CT Δ sΓ mt0 s1 _ rΓ h rΓ' h' Hwf Htype1 Heval1 H1).
    + exact (rsfitp_frame_step CT Δ sΓ mt0 s1 _ rΓ h rΓ' h' Hwf Htype1 Heval1 H3).
Qed.

(** THE STARTING-STATE CONDITION IS KEPT BY EVERY WELL-TYPED EXECUTION. *)
Theorem rsfp_preservation : forall CT Δ sΓ mt s sΓ' rΓ h rΓ' h',
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt s sΓ' ->
  eval_stmt CT rΓ h s OK rΓ' h' ->
  RSFp CT Δ rΓ h -> RSFp CT Δ rΓ' h'.
Proof.
  intros CT Δ sΓ mt s sΓ' rΓ h rΓ' h' Hwf Htype Heval HR.
  pose proof HR as (H1 & H2 & H3 & H4).
  refine (conj _ (conj _ (conj _ H4))).
  - eapply rsf_preservation; eauto.
  - eapply rsfitp_heap0_preservation; eauto.
  - eapply rsfitp_frame_step; eauto.
Qed.

(** A state with no type variable in scope whose objects are of classes
    without type parameters satisfies the condition as soon as it satisfies
    the earlier form. *)
Lemma RSFp_start : forall CT Δ rΓ h,
  RSF CT Δ rΓ h ->
  class_bounds Δ = [] -> method_bounds Δ = [] ->
  (forall l o def, runtime_getObj h l = Some o ->
     find_class CT (rctype (rt_type o)) = Some def ->
     ctparams (signature def) = []) ->
  RSFp CT Δ rΓ h.
Proof.
  intros CT Δ rΓ h HR Hc Hm Hobj.
  assert (Hnb : forall o n B, tv_bound Δ o n = Some B -> False).
  { intros o n B Hb. unfold tv_bound in Hb.
    destruct o; simpl in Hb; [rewrite Hc in Hb | rewrite Hm in Hb];
      destruct n; discriminate. }
  refine (conj HR (conj _ (conj _ (conj _ _)))).
  - intros l o def Ho Hfc. pose proof (Hobj l o def Ho Hfc) as Hp. split.
    + intros L o' n B Hb. destruct (tv_bound_class_env _ _ _ _ Hb) as [_ Hn].
      rewrite Hp in Hn. destruct n; discriminate.
    + intros d Hd. rewrite Hfc in Hd. inversion Hd; subst d. rewrite Hp.
      constructor.
  - intros ι o _ _ L o' n B Hb. exfalso. exact (Hnb o' n B Hb).
  - intros o n B Hb. exfalso. exact (Hnb o n B Hb).
  - intros o n K Bs Hb. exfalso. exact (Hnb o n _ Hb).
Qed.

(** The same with nothing assumed beyond the shape of the state: no type
    variable in scope, and every object of a class without type parameters.
    A program's first state, holding only the main object, is of this
    shape. *)
Lemma RSF_start : forall CT Δ rΓ h,
  class_bounds Δ = [] -> method_bounds Δ = [] ->
  (forall l o def, runtime_getObj h l = Some o ->
     find_class CT (rctype (rt_type o)) = Some def ->
     ctparams (signature def) = []) ->
  RSF CT Δ rΓ h.
Proof.
  intros CT Δ rΓ h Hc Hm Hobj. split.
  - apply rsfit_heap_intro. intros l o def Ho Hfc L o' n B Hb.
    destruct (tv_bound_class_env _ _ _ _ Hb) as [_ Hn].
    rewrite (Hobj l o def Ho Hfc) in Hn. destruct n; discriminate.
  - intros ι o _ _ L o' n B Hb. unfold tv_bound in Hb.
    destruct o'; simpl in Hb; [rewrite Hc in Hb | rewrite Hm in Hb];
      destruct n; discriminate.
Qed.

Corollary RSFp_start_plain : forall CT Δ rΓ h,
  class_bounds Δ = [] -> method_bounds Δ = [] ->
  (forall l o def, runtime_getObj h l = Some o ->
     find_class CT (rctype (rt_type o)) = Some def ->
     ctparams (signature def) = []) ->
  RSFp CT Δ rΓ h.
Proof. intros. apply RSFp_start; auto. apply RSF_start; auto. Qed.

(* ------------------THE THEOREMS------------------*)

(** A call that selects a readonly-state or transitive-state method leaves
    the protected fields of every object of the entry heap unchanged.  There
    is no condition on what protected code allocates.  The entry state
    satisfies [RSFp], which every well-typed execution keeps. *)
Theorem rs_ts_call_preservation_final :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef,
    clean_bounds_ct CT ->
    wf_r_config CT Δ sΓ rΓ h ->
    RSFp CT Δ rΓ h ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us Qs zs) OK rΓ' h' ->
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m D mdef ->
    readonly_state_method_scope (mscope (msignature mdef)) ->
    forall l qr C Rs vals f,
      runtime_getObj h l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
      prot_cond CT C f (mscope (msignature mdef)) ->
      exists vals',
        runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
        nth_error vals f = nth_error vals' f.
Proof.
  intros CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef
    Hcl Hwf (H1 & H2 & H3 & H4) Htype Heval Hvy Hbase Hfind Hrs.
  pose proof Hwf as (Hct & Hheap & _).
  eapply (rs_ts_call_preservation_payload CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h'
            ly cy D mdef Hcl Hwf H1); eauto.
  - exact (obP_of CT h Hct Hheap (proj1 H1) H2).
  - intros vals0 rΓc Hargs Hframe.
    exact (rsfp_call CT Δ sΓ rΓ h mt x m y Us Qs zs sΓ' ly cy D mdef vals0 rΓc
             Hwf Htype Hvy Hbase Hfind Hargs Hframe H1 H2 H3 H4).
Qed.

Corollary readonly_state_preservation_final :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef,
    clean_bounds_ct CT ->
    wf_r_config CT Δ sΓ rΓ h ->
    RSFp CT Δ rΓ h ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us Qs zs) OK rΓ' h' ->
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m D mdef ->
    readonly_state_method_scope (mscope (msignature mdef)) ->
    forall l qr C Rs vals f,
      runtime_getObj h l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
      (sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA) ->
      exists vals',
        runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
        nth_error vals f = nth_error vals' f.
Proof.
  intros. eapply rs_ts_call_preservation_final; eauto.
  unfold prot_cond. tauto.
Qed.

Corollary transitive_state_preservation_final :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef,
    clean_bounds_ct CT ->
    wf_r_config CT Δ sΓ rΓ h ->
    RSFp CT Δ rΓ h ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us Qs zs) OK rΓ' h' ->
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m D mdef ->
    mscope (msignature mdef) = TransitiveState ->
    forall l qr C Rs vals f,
      runtime_getObj h l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
      exists vals',
        runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
        nth_error vals f = nth_error vals' f.
Proof.
  intros until mdef. intros Hcc Hwf HR Htype Heval Hvy Hbase Hfind Hts.
  intros. eapply rs_ts_call_preservation_final; eauto.
  - rewrite Hts. right. reflexivity.
  - rewrite Hts. right. right. right. reflexivity.
Qed.

(** The same for a call that ends in any way: normally, in a null
    dereference, or in a rejected write. *)
Theorem rs_ts_call_preservation_final_any :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef res,
    clean_bounds_ct CT ->
    wf_r_config CT Δ sΓ rΓ h ->
    RSFp CT Δ rΓ h ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us Qs zs) res rΓ' h' ->
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m D mdef ->
    readonly_state_method_scope (mscope (msignature mdef)) ->
    forall l qr C Rs vals f,
      runtime_getObj h l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
      prot_cond CT C f (mscope (msignature mdef)) ->
      exists vals',
        runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
        nth_error vals f = nth_error vals' f.
Proof.
  intros CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef res
    Hcl Hwf (H1 & H2 & H3 & H4) Htype Heval Hvy Hbase Hfind Hrs.
  pose proof Hwf as (Hct & Hheap & _).
  eapply (rs_ts_call_preservation_payload_any CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h'
            ly cy D mdef res Hcl Hwf H1); eauto.
  - exact (obP_of CT h Hct Hheap (proj1 H1) H2).
  - intros vals0 rΓc Hargs Hframe.
    exact (rsfp_call CT Δ sΓ rΓ h mt x m y Us Qs zs sΓ' ly cy D mdef vals0 rΓc
             Hwf Htype Hvy Hbase Hfind Hargs Hframe H1 H2 H3 H4).
Qed.

Corollary readonly_state_preservation_final_any :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef res,
    clean_bounds_ct CT ->
    wf_r_config CT Δ sΓ rΓ h ->
    RSFp CT Δ rΓ h ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us Qs zs) res rΓ' h' ->
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m D mdef ->
    readonly_state_method_scope (mscope (msignature mdef)) ->
    forall l qr C Rs vals f,
      runtime_getObj h l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
      (sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA) ->
      exists vals',
        runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
        nth_error vals f = nth_error vals' f.
Proof.
  intros. eapply rs_ts_call_preservation_final_any; eauto.
  unfold prot_cond. tauto.
Qed.

Corollary transitive_state_preservation_final_any :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef res,
    clean_bounds_ct CT ->
    wf_r_config CT Δ sΓ rΓ h ->
    RSFp CT Δ rΓ h ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us Qs zs) res rΓ' h' ->
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m D mdef ->
    mscope (msignature mdef) = TransitiveState ->
    forall l qr C Rs vals f,
      runtime_getObj h l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
      exists vals',
        runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
        nth_error vals f = nth_error vals' f.
Proof.
  intros until res. intros Hcc Hwf HR Htype Heval Hvy Hbase Hfind Hts.
  intros. eapply rs_ts_call_preservation_final_any; eauto.
  - rewrite Hts. right. reflexivity.
  - rewrite Hts. right. right. right. reflexivity.
Qed.

Print Assumptions rsfp_preservation.
Print Assumptions readonly_state_preservation_final.
Print Assumptions transitive_state_preservation_final.
Print Assumptions readonly_state_preservation_final_any.
Print Assumptions transitive_state_preservation_final_any.
Print Assumptions RSFp_start_plain.

(* ------------------PART 2: THE BOUND CONDITION ON PROTECTED METHODS------------------*)

(** The bound condition on protected methods, reduced to what the typing
    rules do not already give.  A readonly-state or transitive-state method
    has a receiver and parameters with no mutable position, reading type
    variables through their bounds; the receiver mentions every type
    parameter of its class, so the class's bounds are covered.  What remains
    is the method's own type parameters. *)

Definition clean_method_bounds_ct (CT : class_table) : Prop :=
  forall C def md,
    find_class CT C = Some def -> List.In md (methods (body def)) ->
    readonly_state_method_scope (mscope (msignature md)) ->
    Forall (no_mut (method_tv_env CT C (msignature md)))
      (mtparams (msignature md)).

Lemma class_method_wf : forall CT C def md,
  wf_class_table CT -> find_class CT C = Some def ->
  List.In md (methods (body def)) -> wf_method CT C md.
Proof.
  intros CT C def md Hct Hfind Hin.
  pose proof (wf_class_table_class _ _ _ Hct Hfind) as Hc.
  destruct Hct as (_ & _ & _ & Hname).
  pose proof (Hname _ _ Hfind) as HC.
  inversion Hc; subst.
  - rewrite Hno_methods in Hin. contradiction.
  - match goal with
    | HH : Forall (wf_method CT _) _ |- _ =>
        rewrite Forall_forall in HH; exact (HH _ Hin)
    end.
Qed.

Lemma class_var_types_In : forall n i,
  i < n -> List.In (TVar TVSub ClassVar i) (class_var_types n).
Proof.
  intros n i Hi. unfold class_var_types.
  apply in_map_iff. exists i. split; auto. apply in_seq. lia.
Qed.

(** The method rule checks the bounds of the type parameters of every
    readonly-state and transitive-state method, so a well-formed class table
    satisfies the condition. *)
Lemma clean_method_bounds_of_wf : forall CT,
  wf_class_table CT -> clean_method_bounds_ct CT.
Proof.
  intros CT Hct C def md Hfind Hin Hrs.
  pose proof (class_method_wf _ _ _ _ Hct Hfind Hin) as Hwm.
  destruct Hwm as (_ & Hmb & _).
  eapply Forall_impl; [|exact Hmb].
  intros B (_ & _ & H). exact (H Hrs).
Qed.

Lemma clean_bounds_of_signature : forall CT,
  wf_class_table CT -> clean_method_bounds_ct CT -> clean_bounds_ct CT.
Proof.
  intros CT Hct Hcm C def md Hfind Hin Hrs o n B Hb.
  pose proof (class_method_wf _ _ _ _ Hct Hfind Hin) as Hwm.
  unfold wf_method in Hwm.
  destruct Hwm as (Hshape & Hmb & _ & _ & _ & Hroots).
  specialize (Hroots Hrs). destruct Hroots as (Hrecv & _ & Hcb).
  destruct o.
  - (* a class type parameter: the signature condition lists the class bounds *)
    assert (HbC : nth_error (ctparams (signature def)) n = Some B).
    { unfold tv_bound, method_tv_env, class_tparams in Hb. simpl in Hb.
      rewrite Hfind in Hb. exact Hb. }
    split.
    + pose proof (class_bounds_class _ _ _ Hct Hfind) as Hall.
      rewrite Forall_forall in Hall. apply Hall. eapply nth_error_In; eauto.
    + rewrite Forall_forall in Hcb. apply Hcb.
      unfold tv_bound in Hb. simpl in Hb. eapply nth_error_In; eauto.
  - (* a method type parameter *)
    assert (HbM : nth_error (mtparams (msignature md)) n = Some B).
    { unfold tv_bound, method_tv_env in Hb. simpl in Hb. exact Hb. }
    split.
    + rewrite Forall_forall in Hmb.
      exact (proj1 (Hmb _ (nth_error_In _ _ HbM))).
    + pose proof (Hcm _ _ _ Hfind Hin Hrs) as Hall.
      rewrite Forall_forall in Hall. apply Hall. eapply nth_error_In; eauto.
Qed.

Print Assumptions clean_bounds_of_signature.

(* ------------------PART 3: THE THEOREMS------------------*)

(** The final theorems.  They need no condition on the class table beyond
    its well-formedness: the method rule requires that the type parameters of
    a readonly-state or transitive-state method have bounds that reach no
    mutable position, and the same for the class's type parameters follows
    from the rule on the receiver type. *)

Corollary readonly_state_preservation_final_signature :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef,
    wf_r_config CT Δ sΓ rΓ h ->
    RSFp CT Δ rΓ h ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us Qs zs) OK rΓ' h' ->
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m D mdef ->
    readonly_state_method_scope (mscope (msignature mdef)) ->
    forall l qr C Rs vals f,
      runtime_getObj h l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
      (sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA) ->
      exists vals',
        runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
        nth_error vals f = nth_error vals' f.
Proof.
  intros CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef Hwf.
  pose proof Hwf as (Hct & _).
  pose proof (clean_method_bounds_of_wf _ Hct) as Hcm.
  apply readonly_state_preservation_final; auto.
  apply clean_bounds_of_signature; auto.
Qed.

Corollary transitive_state_preservation_final_signature :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef,
    wf_r_config CT Δ sΓ rΓ h ->
    RSFp CT Δ rΓ h ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us Qs zs) OK rΓ' h' ->
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m D mdef ->
    mscope (msignature mdef) = TransitiveState ->
    forall l qr C Rs vals f,
      runtime_getObj h l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
      exists vals',
        runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
        nth_error vals f = nth_error vals' f.
Proof.
  intros CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef Hwf.
  pose proof Hwf as (Hct & _).
  pose proof (clean_method_bounds_of_wf _ Hct) as Hcm.
  apply transitive_state_preservation_final; auto.
  apply clean_bounds_of_signature; auto.
Qed.

(** The same for a call that ends in any way. *)
Corollary readonly_state_preservation_final_signature_any :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef res,
    wf_r_config CT Δ sΓ rΓ h ->
    RSFp CT Δ rΓ h ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us Qs zs) res rΓ' h' ->
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m D mdef ->
    readonly_state_method_scope (mscope (msignature mdef)) ->
    forall l qr C Rs vals f,
      runtime_getObj h l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
      (sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA) ->
      exists vals',
        runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
        nth_error vals f = nth_error vals' f.
Proof.
  intros CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef res Hwf.
  pose proof Hwf as (Hct & _).
  pose proof (clean_method_bounds_of_wf _ Hct) as Hcm.
  apply readonly_state_preservation_final_any; auto.
  apply clean_bounds_of_signature; auto.
Qed.

Corollary transitive_state_preservation_final_signature_any :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef res,
    wf_r_config CT Δ sΓ rΓ h ->
    RSFp CT Δ rΓ h ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us Qs zs) res rΓ' h' ->
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m D mdef ->
    mscope (msignature mdef) = TransitiveState ->
    forall l qr C Rs vals f,
      runtime_getObj h l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
      exists vals',
        runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
        nth_error vals f = nth_error vals' f.
Proof.
  intros CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef res Hwf.
  pose proof Hwf as (Hct & _).
  pose proof (clean_method_bounds_of_wf _ Hct) as Hcm.
  apply transitive_state_preservation_final_any; auto.
  apply clean_bounds_of_signature; auto.
Qed.

(* ------------------FROM A PROGRAM START------------------*)

(** A start state: a well-formed state with no type variable in scope whose
    objects are all of classes without type parameters.  The first state of
    a program, holding only the main object, is one. *)
Definition start_state (CT : class_table) (Δ : tv_env) (sΓ : s_env)
    (rΓ : r_env) (h : heap) : Prop :=
  wf_r_config CT Δ sΓ rΓ h /\
  class_bounds Δ = [] /\ method_bounds Δ = [] /\
  (forall l o def, runtime_getObj h l = Some o ->
     find_class CT (rctype (rt_type o)) = Some def ->
     ctparams (signature def) = []).

(** The whole statement, with no condition in the vocabulary of the proof:
    run any well-typed statement [s] from a start state, then a call that
    selects a readonly-state or transitive-state method.  However the call
    ends, the protected fields of every object that exists when the call
    starts are unchanged. *)
Theorem rs_ts_preservation_from_start :
  forall CT Δ sΓ mt rΓ0 h0 s sΓ1 rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef res,
    start_state CT Δ sΓ rΓ0 h0 ->
    stmt_typing CT Δ sΓ mt s sΓ1 ->
    eval_stmt CT rΓ0 h0 s OK rΓ h ->
    stmt_typing CT Δ sΓ1 mt (SCall x m y Us Qs zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us Qs zs) res rΓ' h' ->
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m D mdef ->
    forall l qr C Rs vals f,
      runtime_getObj h l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
      (readonly_state_method_scope (mscope (msignature mdef)) /\
       (sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA)) \/
      mscope (msignature mdef) = TransitiveState ->
      exists vals',
        runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
        nth_error vals f = nth_error vals' f.
Proof.
  intros CT Δ sΓ mt rΓ0 h0 s sΓ1 rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef res
    (Hwf0 & Hc & Hm & Hobj) Hts Hes Htc Hec Hvy Hbase Hfind
    l qr C Rs vals f Hl Hcase.
  pose proof (preservation_pico _ _ _ _ _ _ _ Hes eq_refl _ _ _ _ Hwf0 Hts) as Hwf.
  pose proof (rsfp_preservation CT Δ sΓ mt s sΓ1 rΓ0 h0 rΓ h Hwf0 Hts Hes
                (RSFp_start_plain CT Δ rΓ0 h0 Hc Hm Hobj)) as HR.
  destruct Hcase as [[Hrs Hf] | Htsc].
  - exact (readonly_state_preservation_final_signature_any CT Δ sΓ1 mt rΓ h
             x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef res Hwf HR Htc Hec Hvy
             Hbase Hfind Hrs l qr C Rs vals f Hl Hf).
  - exact (transitive_state_preservation_final_signature_any CT Δ sΓ1 mt rΓ h
             x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef res Hwf HR Htc Hec Hvy
             Hbase Hfind Htsc l qr C Rs vals f Hl).
Qed.

Print Assumptions readonly_state_preservation_final_signature.
Print Assumptions transitive_state_preservation_final_signature.
Print Assumptions readonly_state_preservation_final_signature_any.
Print Assumptions transitive_state_preservation_final_signature_any.
Print Assumptions rs_ts_preservation_from_start.

(* ------------------PART 4: EVERY CALL OF A RUN------------------*)

(** Readonly-state and transitive-state preservation for every call of a run.

    [rs_ts_preservation_from_start] speaks about a call made by the statement
    that runs from the start state.  This file covers a call made anywhere
    during the run, at any depth of nested method bodies. *)

(* ------------------EVALUATIONS INSIDE AN EVALUATION------------------*)

(** [occurs CT rΓ h s rΓi hi si res rΓi' hi']: while [s] is evaluated from
    [rΓ] and [h], the statement [si] is evaluated from [rΓi] and [hi] and
    ends with [res] in [rΓi'] and [hi'].  The inner evaluation is the whole
    one, the first or the second part of a sequence, or lies in the body of
    a called method. *)
Inductive occurs (CT : class_table)
    : r_env -> heap -> stmt ->
      r_env -> heap -> stmt -> eval_result -> r_env -> heap -> Prop :=
  | occ_here : forall rΓ h s res rΓ' h'
      (Heval : eval_stmt CT rΓ h s res rΓ' h'),
      occurs CT rΓ h s rΓ h s res rΓ' h'
  | occ_seq_l : forall rΓ h s1 s2 rΓi hi si res rΓi' hi'
      (Hin : occurs CT rΓ h s1 rΓi hi si res rΓi' hi'),
      occurs CT rΓ h (SSeq s1 s2) rΓi hi si res rΓi' hi'
  | occ_seq_r : forall rΓ h s1 s2 rΓ1 h1 rΓi hi si res rΓi' hi'
      (Hfirst : eval_stmt CT rΓ h s1 OK rΓ1 h1)
      (Hin : occurs CT rΓ1 h1 s2 rΓi hi si res rΓi' hi'),
      occurs CT rΓ h (SSeq s1 s2) rΓi hi si res rΓi' hi'
  | occ_call : forall rΓ h x m y Us Qs zs ly cy D mdef vals rΓc
        rΓi hi si res rΓi' hi'
      (Hval_y : runtime_getVal rΓ y = Some (Iot ly))
      (Hbase  : r_basetype h ly = Some cy)
      (Hfind  : FindMethodWithName CT cy m D mdef)
      (Hargs  : runtime_lookup_list rΓ zs = Some vals)
      (Hframe : callee_env CT rΓ h ly D Us Qs vals rΓc)
      (Hin : occurs CT rΓc h (mbody_stmt (mbody mdef)) rΓi hi si res rΓi' hi'),
      occurs CT rΓ h (SCall x m y Us Qs zs) rΓi hi si res rΓi' hi'.

(** Every evaluation inside a well-typed evaluation from a well-formed state
    that satisfies the readonly-state invariant is itself a well-typed
    evaluation from such a state. *)
Lemma occurs_config : forall CT rΓ h s rΓi hi si res rΓi' hi',
  occurs CT rΓ h s rΓi hi si res rΓi' hi' ->
  forall Δ sΓ mt sΓ',
    wf_r_config CT Δ sΓ rΓ h ->
    RSFp CT Δ rΓ h ->
    stmt_typing CT Δ sΓ mt s sΓ' ->
    exists Δi sΓi mti sΓi',
      wf_r_config CT Δi sΓi rΓi hi /\
      RSFp CT Δi rΓi hi /\
      stmt_typing CT Δi sΓi mti si sΓi' /\
      eval_stmt CT rΓi hi si res rΓi' hi'.

Proof.
  intros CT rΓ h s rΓi hi si res rΓi' hi' H.
  induction H; intros Δ sΓ mt sΓ' Hwf HR Htype.
  - exists Δ, sΓ, mt, sΓ'. auto.
  - inversion Htype; subst. eapply IHoccurs; eauto.
  - inversion Htype; subst.
    eapply IHoccurs.
    + eapply preservation_pico; eauto.
    + eapply rsfp_preservation; eauto.
    + eauto.
  - destruct (call_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                _ Hwf Htype Hval_y Hbase Hfind Hargs Hframe)
      as (ι1 & o1 & oy1 & Tx1 & _ & _ & _ & _ & _ & _ &
          _ & Hwm & Hcfg & _).
    pose proof Hwm as (_ & _ & _ & (sΓb & Tb & Hbody & _) & _).
    destruct HR as (H1 & H2 & H3 & H4).
    eapply IHoccurs; [exact Hcfg | | exact Hbody].
    refine (conj (conj (proj1 H1) _) (conj H2 (conj _ _))).
    + exact (rsf_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hwf Htype Hval_y Hbase Hfind Hargs Hframe H1).
    + exact (rsfp_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hwf Htype Hval_y Hbase Hfind Hargs Hframe H1 H2 H3 H4).
    + exact (rsfp_call_sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hwf Htype Hval_y Hbase Hfind Hargs Hframe H1 H2 H3 H4).
Qed.

(* ------------------THE THEOREM------------------*)

(** Run any well-typed statement from a start state.  For every call that
    is evaluated during the run, at any depth, and that selects a
    readonly-state or transitive-state method: however the call ends, the
    protected fields of every object that exists when the call starts are
    unchanged. *)
Theorem rs_ts_preservation_all_calls :
  forall CT Δ sΓ mt rΓ0 h0 s sΓ1 rΓ h x m y Us Qs zs res rΓ' h' ly cy D mdef,
    start_state CT Δ sΓ rΓ0 h0 ->
    stmt_typing CT Δ sΓ mt s sΓ1 ->
    occurs CT rΓ0 h0 s rΓ h (SCall x m y Us Qs zs) res rΓ' h' ->
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m D mdef ->
    forall l qr C Rs vals f,
      runtime_getObj h l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
      (readonly_state_method_scope (mscope (msignature mdef)) /\
       (sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA)) \/
      mscope (msignature mdef) = TransitiveState ->
      exists vals',
        runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
        nth_error vals f = nth_error vals' f.
Proof.
  intros CT Δ sΓ mt rΓ0 h0 s sΓ1 rΓ h x m y Us Qs zs res rΓ' h' ly cy D mdef
    (Hwf0 & Hc & Hm & Hobj) Hts Hocc Hvy Hbase Hfind l qr C Rs vals f Hl Hcase.
  destruct (occurs_config _ _ _ _ _ _ _ _ _ _ Hocc Δ sΓ mt sΓ1 Hwf0
              (RSFp_start_plain CT Δ rΓ0 h0 Hc Hm Hobj) Hts)
    as (Δi & sΓi & mti & sΓi' & Hwf & HR & Htc & Hec).
  destruct Hcase as [[Hrs Hf] | Htsc].
  - exact (readonly_state_preservation_final_signature_any CT Δi sΓi mti rΓ h
             x m y Us Qs zs sΓi' rΓ' h' ly cy D mdef res Hwf HR Htc Hec Hvy
             Hbase Hfind Hrs l qr C Rs vals f Hl Hf).
  - exact (transitive_state_preservation_final_signature_any CT Δi sΓi mti rΓ h
             x m y Us Qs zs sΓi' rΓ' h' ly cy D mdef res Hwf HR Htc Hec Hvy
             Hbase Hfind Htsc l qr C Rs vals f Hl).
Qed.

(** The relation is not empty where it matters: the body of a called method
    is evaluated inside the call. *)
Example occurs_in_body : forall CT rΓ h x m y Us Qs zs ly cy D mdef vals rΓc
    rb rΓb hb,
  runtime_getVal rΓ y = Some (Iot ly) ->
  r_basetype h ly = Some cy ->
  FindMethodWithName CT cy m D mdef ->
  runtime_lookup_list rΓ zs = Some vals ->
  callee_env CT rΓ h ly D Us Qs vals rΓc ->
  eval_stmt CT rΓc h (mbody_stmt (mbody mdef)) rb rΓb hb ->
  occurs CT rΓ h (SCall x m y Us Qs zs) rΓc h (mbody_stmt (mbody mdef)) rb rΓb hb.
Proof. intros. eapply occ_call; eauto. apply occ_here. assumption. Qed.

Print Assumptions rs_ts_preservation_all_calls.
