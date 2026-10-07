From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels GhostTyping
  GhostForget GhostFit GhostInvariant.

(** Overriding at the level of labels: what a caller passes to the method it
    selected statically is accepted by the method that runs, and what that
    method returns is what the static one promised. *)

(* ------------------SMALL FACTS------------------*)

Lemma ldyn_class_var_types : forall F,
  map (ldyn F) (class_var_types (length (lf_cargs F))) = lf_cargs F.
Proof.
  intros. unfold class_var_types. rewrite map_map. simpl.
  apply map_nth_default_seq.
Qed.

Lemma ldyn_method_var_types : forall F,
  map (ldyn F) (method_var_types (length (lf_margs F))) = lf_margs F.
Proof.
  intros. unfold method_var_types. rewrite map_map. simpl.
  apply map_nth_default_seq.
Qed.

Lemma fT_class_var_types : forall n, map fT (class_var_types n) = class_var_types n.
Proof. intros. unfold class_var_types. rewrite map_map. reflexivity. Qed.

Lemma fT_method_var_types : forall n,
  map fT (method_var_types n) = method_var_types n.
Proof. intros. unfold method_var_types. rewrite map_map. reflexivity. Qed.

Lemma map_qual_ext : forall f g T,
  (forall q0, f q0 = g q0) -> map_qual f T = map_qual g T.
Proof.
  intros f g T Hfg. induction T using qualified_type_ind'.
  - simpl. rewrite Hfg. f_equal. induction H; simpl; auto. f_equal; auto.
  - destruct u; simpl; auto. rewrite Hfg. reflexivity.
  - simpl. f_equal. induction H; simpl; auto. f_equal; auto.
Qed.



(* ------------------LABEL CONDITIONS FOR THE CLASS VIEW------------------*)

Ltac lc_solve :=
  simpl; unfold arg_q_sub;
  (split; [ solve [left; reflexivity] || solve [right; split; auto]
          | solve [left; reflexivity] || solve [right; left; discriminate]
            || solve [right; right; reflexivity] ]).

(** Two readings in the same world of an overridden member type seen through
    the overriding class, with mutable positions forgotten. *)
Lemma lc_override_types : forall L qr qC wf m cs1 ms1 cs2 ms2,
  vpa_mutability_runtime_bound_agree qr qC = true ->
  label_cond L (fun q0 => fl (vpa_q AbstractState (qc2q qC) q0))
    (act_frame qr wf m cs1 ms1) (act_frame qr wf m cs2 ms2).
Proof.
  intros L qr qC wf m cs1 ms1 cs2 ms2 Hag q0.
  destruct qr, qC; try discriminate Hag; destruct q0; lc_solve.
Qed.

(** The receiver object's own reading against the callee's, forgotten. *)
Lemma lc_override_args : forall L qr qC b c As wf m cs ms,
  vpa_mutability_runtime_bound_agree qr qC = true ->
  (qr = Mut_r -> norm L (olab c) = norm L (if m then LIn wf else LOut)) ->
  label_cond L (fun q0 => fl (vpa_q AbstractState (qc2q qC) q0))
    (obj_frame qr b c As) (act_frame qr wf m cs ms).
Proof.
  intros L qr qC b c As wf m cs ms Hag Hn q0.
  destruct qr, qC; try discriminate Hag; destruct q0; try lc_solve.
  split; [left; reflexivity | right; right; exact (Hn eq_refl)].
Qed.

(** The receiver object's own reading against the callee's, once the
    callee's world agrees with the object's birth world. *)
Lemma lc_override_post : forall L qr qC b c As wf m cs ms,
  vpa_mutability_runtime_bound_agree qr qC = true ->
  norm L (olab b) = norm L (LIn wf) ->
  (qr = Mut_r -> norm L (olab c) = norm L (if m then LIn wf else LOut)) ->
  (qC = Mut_c -> norm L (olab c) = norm L (LIn wf)) ->
  label_cond L (vpa_q AbstractState (qc2q qC))
    (obj_frame qr b c As) (act_frame qr wf m cs ms).
Proof.
  intros L qr qC b c As wf m cs ms Hag N1 N2 N3 q0.
  destruct qr, qC; try discriminate Hag; destruct q0; try lc_solve;
    (split; [left; reflexivity
            | right; right;
              (solve [exact N1] || solve [exact (N2 eq_refl)]
               || solve [exact (N3 eq_refl)]) ]).
Qed.

(** Exact agreement of readings, used against the direction of the map. *)
Definition label_eq (L : list nat) (f : q -> q) (Fo Fc : lframe) : Prop :=
  forall q0,
    dynq (lf_q Fo) q0 = dynq (lf_q Fc) (f q0) /\
    (dynq (lf_q Fo) q0 <> Mut \/
     norm L (lab_of Fo q0) = norm L (lab_of Fc (f q0))).

Lemma ldyn_map_qual_agree_inv : forall L f Fo Fc T,
  label_eq L f Fo Fc ->
  Forall2 (lagree L) (lf_cargs Fc) (lf_cargs Fo) ->
  Forall2 (lagree L) (lf_margs Fc) (lf_margs Fo) ->
  lagree L (ldyn Fc (map_qual f T)) (ldyn Fo T).
Proof.
  intros L f Fo Fc T Hq Hc Hm.
  induction T using qualified_type_ind'.
  - simpl. destruct (Hq qual) as [H1 H2]. constructor.
    + left. exact H1.
    + right. destruct H2 as [H2 | H2]; [left; congruence | right; auto].
    + induction H; simpl; constructor; auto.
  - pose proof (tv_lookup_Forall2 (lagree L) o _ _ _ _ n Hc Hm) as Hl.
    assert (HA : lagree L
              match tv_lookup o (lf_cargs Fc) (lf_margs Fc) n with
              | Some A => A | None => ldefault end
              match tv_lookup o (lf_cargs Fo) (lf_margs Fo) n with
              | Some A => A | None => ldefault end).
    { destruct (tv_lookup o (lf_cargs Fo) (lf_margs Fo) n),
               (tv_lookup o (lf_cargs Fc) (lf_margs Fc) n);
        try contradiction; auto using lagree_default. }
    destruct u; simpl; auto.
    destruct (Hq qual) as [H1 H2].
    inversion HA; subst. simpl. constructor; auto.
    + left. exact H1.
    + right. destruct H2 as [H2 | H2]; [left; congruence | right; auto].
  - pose proof (tv_lookup_Forall2 (lagree L) o _ _ _ _ n Hc Hm) as Hl.
    assert (HA : lagree L
              match tv_lookup o (lf_cargs Fc) (lf_margs Fc) n with
              | Some A => A | None => ldefault end
              match tv_lookup o (lf_cargs Fo) (lf_margs Fo) n with
              | Some A => A | None => ldefault end).
    { destruct (tv_lookup o (lf_cargs Fo) (lf_margs Fo) n),
               (tv_lookup o (lf_cargs Fc) (lf_margs Fc) n);
        try contradiction; auto using lagree_default. }
    simpl. inversion HA; subst. simpl. constructor; auto.
    induction H; simpl; constructor; auto.
Qed.

Lemma lc_override_inv2 : forall L qr qC wf m cs1 ms1 cs2 ms2,
  vpa_mutability_runtime_bound_agree qr qC = true ->
  (qC = Mut_c -> norm L (if m then LIn wf else LOut) = norm L (LIn wf)) ->
  label_eq L (vpa_q AbstractState (qc2q qC))
    (act_frame qr wf m cs1 ms1) (act_frame qr wf m cs2 ms2).
Proof.
  intros L qr qC wf m cs1 ms1 cs2 ms2 Hag HN q0.
  destruct qr, qC; try discriminate Hag; destruct q0;
    (split; [reflexivity
            | solve [left; simpl; discriminate] || solve [right; reflexivity]
              || solve [right; exact (HN eq_refl)]]).
Qed.

Lemma Forall2_lagree_sym : forall L As Bs,
  Forall2 (lagree L) As Bs -> Forall rlost_free (map erase Bs) ->
  Forall2 (lagree L) Bs As.
Proof.
  intros L As Bs H. induction H; intros Hlf; simpl in *; constructor;
    inversion Hlf; subst; auto using lagree_sym.
Qed.

(** A type that is well formed where no method type variable is declared is
    read the same whatever the method type arguments are. *)
Lemma ldyn_no_method_vars : forall CT Δ top T,
  wf_stype CT Δ top T ->
  method_bounds Δ = [] ->
  forall F ms, ldyn (lf_with_args F (lf_cargs F) ms) T = ldyn F T.
Proof.
  intros CT Δ top T H. induction H using wf_stype_ind'; intros Hm F ms.
  - simpl. f_equal; try solve [destruct q0; reflexivity].
    induction H1; simpl; auto. inversion H0; subst. f_equal; auto.
  - unfold tv_bound in H. destruct o; simpl in *.
    + destruct u; simpl; auto;
        try (destruct (match nth_error (lf_cargs F) n with
                       | Some A => A | None => ldefault end) as [qa la Ca Aa];
             simpl; destruct q; reflexivity).
    + rewrite Hm in H. destruct n; discriminate.
  - specialize (IHwf_stype Hm F ms). cbn [ldyn] in IHwf_stype.
    inversion IHwf_stype as [Hargs]. cbn [ldyn]. rewrite Hargs.
    unfold tv_bound in H. destruct o; simpl in *.
    + reflexivity.
    + rewrite Hm in H. destruct n; discriminate.
Qed.

(** An object's reading against the reading of an activation running on it,
    for types that write no [Mut]. *)
Lemma obj_act_cond : forall L qr b c As cs ms wf m cs' ms',
  (qr = Mut_r -> norm L (olab c) = norm L (if m then LIn wf else LOut)) ->
  label_cond L (unm (fun q0 => q0))
    (lf_with_args (obj_frame qr b c As) cs ms) (act_frame qr wf m cs' ms').
Proof.
  intros L qr b c As cs ms wf m cs' ms' Hn q0.
  destruct q0; try lc_solve.
  destruct qr; [|lc_solve].
  split; [left; reflexivity | right; right; exact (Hn eq_refl)].
Qed.

(** The activation of a method of class [D'] fits its bounds: the class part
    comes from the receiver object, the method part is given. *)
Lemma act_fits : forall CT L qr b c wf m D' def' sig' lca lm,
  wf_class_table CT ->
  find_class CT D' = Some def' ->
  nomut_bounds (method_tv_env CT D' sig') ->
  frame_fits CT L (class_env def') (obj_frame qr b c lca) ->
  (qr = Mut_r -> norm L (olab c) = norm L (if m then LIn wf else LOut)) ->
  (forall n B,
     nth_error (mtparams sig') n = Some B ->
     lsubt CT L (ldyn (act_frame qr wf m lca lm) (TVar TVSub MethodVar n))
       (ldyn (act_frame qr wf m lca lm) B)) ->
  frame_fits CT L (method_tv_env CT D' sig') (act_frame qr wf m lca lm).
Proof.
  intros CT L qr b c wf m D' def' sig' lca lm Hct Hfind Hnb Hob Hn HMV o n B Hb.
  destruct o.
  - assert (HbC : nth_error (ctparams (signature def')) n = Some B).
    { unfold tv_bound, method_tv_env, class_tparams in Hb. simpl in Hb.
      rewrite Hfind in Hb. exact Hb. }
    pose proof (Hob ClassVar n B HbC) as Hs.
    change (ldyn (act_frame qr wf m lca lm) (TVar TVSub ClassVar n))
      with (ldyn (obj_frame qr b c lca) (TVar TVSub ClassVar n)).
    eapply lsubt_agree_r; [exact Hs|].
    destruct (Hnb _ _ _ Hb) as [_ HnmB].
    pose proof (class_bounds_wf _ _ _ Hct Hfind) as Hwfb.
    rewrite Forall_forall in Hwfb.
    pose proof (Hwfb _ (nth_error_In _ _ HbC)) as HwB.
    rewrite <- (ldyn_no_method_vars _ _ _ _ HwB eq_refl (obj_frame qr b c lca) lm).
    rewrite <- (map_qual_id B) at 2.
    rewrite (no_mut_unm _ _ (fun q0 => q0) HnmB).
    apply ldyn_map_qual_agree.
    + apply obj_act_cond. exact Hn.
    + simpl. apply Forall2_lagree_refl.
    + simpl. apply Forall2_lagree_refl.
  - apply HMV. exact Hb.
Qed.

(* ------------------ONE OVERRIDE STEP------------------*)

(** What the declared override check provides at run time for a receiver of
    class [D'] (or below) whose view at [D'] has arguments [ca']. *)
Lemma override_data : forall CT qr D' ca' def' mdef' Pc Ss D1 mdef1 ca1,
  wf_class_table CT ->
  wf_rtypeuse CT (mkruntime_type qr D' ca') ->
  find_class CT D' = Some def' ->
  super (signature def') = Some (Pc, Ss) ->
  wf_method CT D' mdef' ->
  FindMethodWithName CT Pc (mname (msignature mdef')) D1 mdef1 ->
  rsuper_inst CT (qr2q qr) D' ca' D1 ca1 ->
  let qC := class_qualifier (signature def') in
  let sig' := msignature mdef' in
  let sig1 := msignature mdef1 in
  exists Vs,
    vpa_mutability_runtime_bound_agree qr qC = true /\
    super_inst CT AbstractState (qc2q qC) D' (class_var_types (length ca')) D1 Vs /\
    method_override_compatible CT (method_tv_env CT D' sig') qC Vs sig' sig1 /\
    (forall ma, ca1 = map (dyn (qr2q qr) ca' ma) Vs) /\
    (forall ma T,
       length ma = length (mtparams sig1) ->
       dyn (qr2q qr) ca' ma
         (member_type AbstractState (qc2q qC) Vs
            (method_var_types (length (mtparams sig1))) T) =
       dyn (qr2q qr) ca1 ma T) /\
    (forall ma,
       rbounds_ok CT (qr2q qr) ca1 ma ma (mtparams sig1) ->
       frame_bounds_ok CT (method_tv_env CT D' sig') (qr2q qr) ca' ma).
Proof.
  intros CT qr D' ca' def' mdef' Pc Ss D1 mdef1 ca1
    Hct Hrt Hfind Hsuper Hwm Hfm Hrs qC sig' sig1.
  unfold wf_rtypeuse in Hrt. simpl in Hrt. rewrite Hfind in Hrt.
  destruct Hrt as (Hagree & Hlf & Hbnd). fold qC in Hagree.
  destruct (super_inst_exists _ _ _ _ _ _ Hrs AbstractState (qc2q qC)
              (class_var_types (length (ctparams (signature def')))))
    as [Vs Hsi].
  pose proof Hwm as (_ & _ & _ & _ & Hovr & _).
  pose proof (Hovr def' Pc Ss D1 mdef1 Vs Hfind Hsuper Hfm Hsi) as Hcompat.
  assert (Hlen_ca : length (ctparams (signature def')) = length ca').
  { symmetry. apply (Forall2_length Hbnd). }
  rewrite Hlen_ca in Hsi.
  assert (Hca1 : forall ma, ca1 = map (dyn (qr2q qr) ca' ma) Vs).
  { intros ma.
    pose proof (super_inst_dyn_exact _ _ _ _ _ _ _ Hsi (qr2q qr) ca' ma
                  (fun q0 => dynq_class_adapt qr qC q0 Hagree)) as Hex.
    rewrite dyn_class_var_types in Hex.
    eapply rsuper_inst_deterministic; eauto. }
  assert (Hview : forall ma T,
            length ma = length (mtparams sig1) ->
            dyn (qr2q qr) ca' ma
              (member_type AbstractState (qc2q qC) Vs
                 (method_var_types (length (mtparams sig1))) T) =
            dyn (qr2q qr) ca1 ma T).
  { intros ma T Hlen. unfold member_type. rewrite dyn_subst.
    rewrite <- Hlen. rewrite dyn_method_var_types. rewrite <- (Hca1 ma).
    apply dyn_class_adapt; auto. }
  exists Vs. refine (conj Hagree (conj Hsi (conj Hcompat (conj Hca1 (conj Hview _))))).
  intros ma Hb1.
  assert (Hlen : length ma = length (mtparams sig1))
    by apply (Forall2_length Hb1).
  destruct Hcompat as (_ & _ & Hmtp & _).
  apply frame_bounds_ok_of_rbounds; simpl.
  - unfold class_tparams. rewrite Hfind. unfold rbounds_ok in *.
    eapply Forall2_Forall_r_impl;
      [exact Hbnd | exact (class_bounds_wf _ _ _ Hct Hfind) |].
    intros R B HR HB. simpl in HR.
    rewrite (dyn_no_method_vars _ _ _ _ HB eq_refl). exact HR.
  - fold sig'. rewrite Hmtp. unfold rbounds_ok in *.
    eapply Forall2_map_right; [exact Hb1|].
    intros R B HR. simpl in *. rewrite Hview; auto.
Qed.

Lemma agree_mutc : forall qr,
  vpa_mutability_runtime_bound_agree qr Mut_c = true -> qr = Mut_r.
Proof. intros qr H. destruct qr; cbv in H; congruence. Qed.

Section Step.
  Variables (CT : class_table) (qr : q_r) (D' : class_name) (ca' : list rtype).
  Variables (qC : q_c) (sig' sig1 : method_sig) (D1 : class_name).
  Variables (ca1 : list rtype) (Vs : list qualified_type).
  Hypothesis Hct : wf_class_table CT.
  Hypothesis Hag : vpa_mutability_runtime_bound_agree qr qC = true.
  Hypothesis Hsi :
    super_inst CT AbstractState (qc2q qC) D' (class_var_types (length ca')) D1 Vs.
  Hypothesis Hcompat :
    method_override_compatible CT (method_tv_env CT D' sig') qC Vs sig' sig1.
  Hypothesis Hca1 : forall ma, ca1 = map (dyn (qr2q qr) ca' ma) Vs.
  Hypothesis Hview : forall ma T,
    length ma = length (mtparams sig1) ->
    dyn (qr2q qr) ca' ma
      (member_type AbstractState (qc2q qC) Vs
         (method_var_types (length (mtparams sig1))) T) =
    dyn (qr2q qr) ca1 ma T.
  Hypothesis Hfbf : forall ma,
    rbounds_ok CT (qr2q qr) ca1 ma ma (mtparams sig1) ->
    frame_bounds_ok CT (method_tv_env CT D' sig') (qr2q qr) ca' ma.
  Hypothesis Hrsc : readonly_state_method_scope (mscope sig').
  Hypothesis Hnb : nomut_bounds (method_tv_env CT D' sig').

  (** A type of the overridden declaration and its view from the overriding
      class, both with mutable positions forgotten, read in the two
      activations. *)
  Lemma view_agree_fl : forall L b c lca' lc1 wf m lm T,
    map erase lca' = ca' ->
    lsuper_inst CT qr b c D' lca' D1 lc1 ->
    (qr = Mut_r -> norm L (olab c) = norm L (if m then LIn wf else LOut)) ->
    length lm = length (mtparams sig1) ->
    lagree L (ldyn (act_frame qr wf m lc1 lm) (fT T))
      (ldyn (act_frame qr wf m lca' lm)
         (fT (member_type AbstractState (qc2q qC) Vs
                (method_var_types (length (mtparams sig1))) T))).
  Proof using All.
    intros L b c lca' lc1 wf m lm T Hec Hls Hn Hlen_lm.
    set (F' := act_frame qr wf m lca' lm).
    unfold member_type, adapt. rewrite fT_subst. rewrite fT_method_var_types.
    rewrite map_qual_comp. rewrite ldyn_subst.
    assert (Hm : map (ldyn F') (method_var_types (length (mtparams sig1))) = lm).
    { rewrite <- Hlen_lm. apply (ldyn_method_var_types F'). }
    fold F'. rewrite Hm.
    replace (map_qual (fun q0 => fl (vpa_q AbstractState (qc2q qC) q0)) T)
      with (map_qual (fun q0 => fl (vpa_q AbstractState (qc2q qC) q0)) (fT T)).
    2:{ rewrite map_qual_comp. apply map_qual_ext.
        intros q0. destruct q0, qC; reflexivity. }
    apply ldyn_map_qual_agree.
    - exact (lc_override_types L qr qC wf m lc1 lm
               (map (ldyn F') (map fT Vs)) lm Hag).
    - assert (Hcond : label_cond L
                (fun q0 => fl (vpa_q AbstractState (qc2q qC) q0))
                (obj_frame qr b c []) F').
      { apply lc_override_args; auto. }
      assert (Hrefl : Forall2 (lagree L) lca'
                (map (ldyn F') (map fT (class_var_types (length ca'))))).
      { rewrite fT_class_var_types.
        replace (length ca') with (length (lf_cargs F')).
        2:{ simpl. rewrite <- Hec. rewrite length_map. reflexivity. }
        rewrite ldyn_class_var_types. apply Forall2_lagree_refl. }
      destruct (super_inst_ldyn_fl _ _ _ _ _ _ _ Hsi L qr b c F' lca'
                  Hcond Hrefl) as (Vs0 & Hs0 & Hle0).
      assert (Vs0 = lc1) by (eapply lsuper_inst_deterministic; eauto).
      subst Vs0. exact Hle0.
    - simpl. apply Forall2_lagree_refl.
  Qed.

  (** Parameters: from the overridden method's reading to the overriding
      method's, both with mutable positions forgotten. *)
  Lemma lref_params_step : forall b c lca' lc1 wf m lm P h G L next,
    map erase lca' = ca' ->
    lsuper_inst CT qr b c D' lca' D1 lc1 ->
    heapL P CT h G L next -> mutcL CT h G -> List.In wf L ->
    (qr = Mut_r -> norm L (olab c) = norm L (if m then LIn wf else LOut)) ->
    rbounds_ok CT (qr2q qr) ca1 (map erase lm) (map erase lm) (mtparams sig1) ->
    frame_fits CT L (method_tv_env CT D' sig') (act_frame qr wf m lca' lm) ->
    Forall2
      (fun P1 P' => forall v,
         loc_has_rtype CT h v (dyn (qr2q qr) ca1 (map erase lm) P1) ->
         lhas CT h G L v (ldyn (act_frame qr wf m lc1 lm) (fT P1)) ->
         lhas CT h G L v (ldyn (act_frame qr wf m lca' lm) (fT P')))
      (mparams sig1) (mparams sig').
  Proof using All.
    intros b c lca' lc1 wf m lm P h G L next Hec Hls HG HM HwfL Hn Hb1 Hfit.
    assert (Hlen : length (map erase lm) = length (mtparams sig1))
      by apply (Forall2_length Hb1).
    assert (Hlen_lm : length lm = length (mtparams sig1)).
    { rewrite length_map in Hlen. exact Hlen. }
    destruct Hcompat as (_ & Hscope & Hmtp & Hret & Hpar & _).
    eapply Forall2_impl; [|exact Hpar].
    intros P1 P' Hsub v Hty Hl. simpl in Hsub.
    apply (lhas_subtype_fl P CT (method_tv_env CT D' sig') h G L next
             (mscope sig') qr wf m lca' lm ca' (map erase lm)
             HG HwfL Hrsc eq_refl
             (vb_of_fits P CT _ h G L next (act_frame qr wf m lca' lm) _ _ qr
                HG HM Hfit eq_refl Hec eq_refl)
             (fun o n B Hb => no_mut_fT _ _ (proj2 (Hnb o n B Hb)))
             (Hfbf _ Hb1) Hec eq_refl _ _ Hsub).
    - unfold wf_r_typable. rewrite Hview; auto.
    - eapply lhas_agree; [exact Hl|].
      apply (view_agree_fl L b c lca' lc1 wf m lm P1 Hec Hls Hn Hlen_lm).
  Qed.

  (** Result, after the call has returned: from the overriding method's
      reading to the overridden method's.  The callee's world may be closed
      by now. *)
  Lemma lref_result_step : forall b c lca' lc1 wf m lm P h G L next,
    map erase lca' = ca' ->
    lsuper_inst CT qr b c D' lca' D1 lc1 ->
    heapL P CT h G L next -> mutcL CT h G -> (m = true -> List.In wf L) ->
    norm L (olab b) = norm L (LIn wf) ->
    (qr = Mut_r -> norm L (olab c) = norm L (if m then LIn wf else LOut)) ->
    (qC = Mut_c -> norm L (olab c) = norm L (LIn wf)) ->
    rbounds_ok CT (qr2q qr) ca1 (map erase lm) (map erase lm) (mtparams sig1) ->
    frame_fits CT L (method_tv_env CT D' sig') (act_frame qr wf m lca' lm) ->
    Forall rlost_free ca1 ->
    forall v,
      loc_has_rtype CT h v (dyn (qr2q qr) ca' (map erase lm) (mret sig')) ->
      hexT G wf (mret sig') v ->
      lhas CT h G L v (ldyn (act_frame qr wf m lca' lm) (mret sig')) ->
      lhas CT h G L v (ldyn (act_frame qr wf m lc1 lm) (mret sig1)) /\
      hexT G wf (mret sig1) v.
  Proof using All.
    intros b c lca' lc1 wf m lm P h G L next Hec Hls HG HM HwfL N1 N2 N3 Hb1
      Hfit Hlf1 v Hty Hex Hl.
    assert (Hlen : length (map erase lm) = length (mtparams sig1))
      by apply (Forall2_length Hb1).
    assert (Hlen_lm : length lm = length (mtparams sig1)).
    { rewrite length_map in Hlen. exact Hlen. }
    destruct Hcompat as (_ & Hscope & Hmtp & Hret & Hpar & _).
    set (F' := act_frame qr wf m lca' lm).
    destruct (lhas_subtype_ex P CT (method_tv_env CT D' sig') h G L next
                (mscope sig') qr wf m lca' lm ca' (map erase lm)
                HG HwfL Hrsc eq_refl
                (vb_of_fits P CT _ h G L next (act_frame qr wf m lca' lm) _ _ qr
                   HG HM Hfit eq_refl Hec eq_refl)
                (fun o n B Hb => nomut_bounds_head _ o n B Hnb Hb)
                (Hfbf _ Hb1) Hec eq_refl _ _ Hret
                v Hty Hex Hl) as [Hv Hexv].
    split.
    - eapply lhas_agree; [exact Hv|].
      unfold member_type, adapt. rewrite ldyn_subst.
      assert (Hm : map (ldyn F') (method_var_types (length (mtparams sig1))) = lm).
      { rewrite <- Hlen_lm. apply (ldyn_method_var_types F'). }
      fold F'. rewrite Hm.
      apply ldyn_map_qual_agree_inv.
      + apply (lc_override_inv2 L qr qC wf m lc1 lm (map (ldyn F') Vs) lm Hag).
        intros HqC.
        assert (qr = Mut_r).
        { apply agree_mutc. rewrite <- HqC. exact Hag. }
        rewrite <- (N2 H). exact (N3 HqC).
      + simpl.
        assert (Hcond : label_cond L (vpa_q AbstractState (qc2q qC))
                          (obj_frame qr b c []) F').
        { apply lc_override_post; auto. }
        assert (Hargs : Forall2 (lagree L) lca'
                  (map (ldyn F') (class_var_types (length ca')))).
        { replace (length ca') with (length (lf_cargs F')).
          2:{ simpl. rewrite <- Hec. rewrite length_map. reflexivity. }
          rewrite ldyn_class_var_types. apply Forall2_lagree_refl. }
        destruct (super_inst_ldyn _ _ _ _ _ _ _ Hsi L qr b c F' lca' Hcond Hargs)
          as (Vs0 & Hs0 & Hle0).
        assert (Vs0 = lc1) by (eapply lsuper_inst_deterministic; eauto).
        subst Vs0.
        apply Forall2_lagree_sym; [exact Hle0|].
        rewrite map_erase_ldyn. simpl. rewrite Hec.
        rewrite <- (Hca1 (map erase lm)). exact Hlf1.
      + simpl. apply Forall2_lagree_refl.
    - intros Hw. apply Hexv.
      rewrite (whead_member_some _ _ _ _ _ _ Hw). destruct qC; reflexivity.
  Qed.
End Step.

(* ------------------ALONG THE LOOKUP CHAIN------------------*)

(** Type parameter bounds in scope of readonly-state and transitive-state
    methods are class types that mention no [Mut]. *)
Definition clean_bounds_ct (CT : class_table) : Prop :=
  forall C def md,
    find_class CT C = Some def -> List.In md (methods (body def)) ->
    readonly_state_method_scope (mscope (msignature md)) ->
    nomut_bounds (method_tv_env CT C (msignature md)).

Lemma Forall2_conj : forall {A B : Type} (R1 R2 : A -> B -> Prop) l1 l2,
  Forall2 R1 l1 l2 -> Forall2 R2 l1 l2 ->
  Forall2 (fun a b => R1 a b /\ R2 a b) l1 l2.
Proof.
  intros A B R1 R2 l1 l2 H. induction H; intros H2; inversion H2; subst;
    constructor; auto.
Qed.

Lemma Forall2_same : forall {A : Type} (R : A -> A -> Prop) l,
  (forall a, R a a) -> Forall2 R l l.
Proof. intros A R l H. induction l; constructor; auto. Qed.

(** Stated through a definition so that substitution leaves it alone. *)
Definition erases (As : list ltype) (Rs : list rtype) : Prop := map erase As = Rs.

(** The bounds of the method type parameters read the same at every
    declaration along the lookup chain. *)
Lemma lookup_bounds_eq : forall CT qr Co Ro C Rs1,
  wf_class_table CT ->
  rsuper_inst CT (qr2q qr) Co Ro C Rs1 ->
  wf_rtypeuse CT (mkruntime_type qr Co Ro) ->
  forall mth D' mdef' D mdef ca' ca ma,
    FindMethodWithName CT Co mth D' mdef' ->
    FindMethodWithName CT C mth D mdef ->
    rsuper_inst CT (qr2q qr) Co Ro D' ca' ->
    rsuper_inst CT (qr2q qr) Co Ro D ca ->
    rbounds_ok CT (qr2q qr) ca ma ma (mtparams (msignature mdef)) ->
    map (dyn (qr2q qr) ca' ma) (mtparams (msignature mdef')) =
    map (dyn (qr2q qr) ca ma) (mtparams (msignature mdef)).
Proof.
  intros CT qr Co Ro C Rs1 Hct H.
  remember (qr2q qr) as qo eqn:Hqo.
  induction H as [C Rs | C Rs P Ss D0 Vs Hparent Hrest IH];
    intros Hrt mth D' mdef' D mdef ca' ca ma Hf' Hf Hs' Hs Hb.
  - destruct (find_method_with_name_deterministic _ _ _ _ _ _ _ Hf' Hf) as [-> ->].
    assert (ca' = ca) by (eapply rsuper_inst_deterministic; eauto). subst ca'.
    reflexivity.
  - subst qo.
    pose proof (rsuper_inst_le _ _ _ _ _ _ Hct Hrest) as HleC.
    pose proof Hparent as Hparent'. unfold parent_lookup in Hparent'.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
    destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hparent') as (sd & _ & HltP & _).
    pose proof (base_subtype_le _ _ _ Hct (find_method_with_name_base _ _ _ _ _ Hf))
      as HleD.
    assert (HsD : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs []) Ss) D ca).
    { inversion Hs; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    assert (HrtP : wf_rtypeuse CT
                     (mkruntime_type qr P (map (dyn (qr2q qr) Rs []) Ss))).
    { eapply rsuper_wf; [exact Hct | | exact Hrt].
      eapply rsi_step; eauto. apply rsi_refl. }
    inversion Hf'; subst.
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      assert (ca' = Rs).
      { eapply rsuper_inst_deterministic; [exact Hct | exact Hs' | apply rsi_refl]. }
      subst ca'.
      destruct (find_from_subclass _ _ _ _ _ _ Hrest _ _ _ Hf) as (D1 & mdef1 & HfP).
      destruct (find_rsuper_exists _ _ _ _ _ HfP (qr2q qr)
                  (map (dyn (qr2q qr) Rs []) Ss)) as [ca1 Hs1].
      pose proof (find_method_wf _ _ _ _ _ Hct Hf') as Hwm.
      assert (HfP' : FindMethodWithName CT P (mname (msignature mdef')) D1 mdef1).
      { rewrite (gget_method_name_consistent _ _ _ Hget_method). exact HfP. }
      assert (Hs1' : rsuper_inst CT (qr2q qr) D' Rs D1 ca1)
        by (eapply rsi_step; eauto).
      destruct (override_data CT qr D' Rs def mdef' P Ss D1 mdef1 ca1
                  Hct Hrt Hfind Hparent' Hwm HfP' Hs1')
        as (Vs0 & Hag & Hsi & Hcompat & Hca1 & Hview & Hfbf).
      pose proof (lookup_refines _ _ _ _ _ _ Hct Hrest HrtP _ _ _ _ _ _ _
                    HfP Hf Hs1 HsD) as (Hsc & Hhd & Hma).
      destruct (Hma _ Hb) as (Hb1 & _ & _).
      rewrite <- (IH HrtP _ _ _ _ _ _ _ _ HfP Hf Hs1 HsD Hb).
      destruct Hcompat as (_ & _ & Hmtp & _).
      rewrite Hmtp. rewrite map_map. apply map_ext. intros B.
      apply Hview. apply (Forall2_length Hb1).
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      rewrite Hsuper in Hparent'. inversion Hparent'; subst.
      pose proof (base_subtype_le _ _ _ Hct
                    (find_method_with_name_base _ _ _ _ _ Hparent_fmn)) as HleD'.
      assert (HsD' : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs []) Ss) D' ca').
      { inversion Hs'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      exact (IH HrtP _ _ _ _ _ _ _ _ Hparent_fmn Hf HsD' HsD Hb).
Qed.

Lemma Forall2_map_self : forall {A B : Type} (R : A -> B -> Prop) (f : A -> B) l,
  (forall x, List.In x l -> R x (f x)) -> Forall2 R l (map f l).
Proof.
  intros A B R f l H. induction l; simpl; constructor.
  - apply H. left. reflexivity.
  - apply IHl. intros x Hx. apply H. right. exact Hx.
Qed.

(** For one class on the chain: its parent inherits the bound facts. *)
Lemma chain_parent_facts : forall CT L qr b c C Rs Ao def P Ss,
  wf_class_table CT ->
  find_class CT C = Some def ->
  super (signature def) = Some (P, Ss) ->
  wf_rtypeuse CT (mkruntime_type qr C Rs) ->
  erases Ao Rs ->
  (qr = Mut_r -> olab b = olab c) ->
  (forall d, find_class CT C = Some d ->
     frame_fits CT L (class_env d) (obj_frame qr b c Ao)) ->
  (forall d, find_class CT P = Some d ->
     frame_fits CT L (class_env d)
       (obj_frame qr b c (map (ldyn (obj_frame qr b c Ao)) Ss))) /\
  (forall d, find_class CT P = Some d ->
     class_qualifier (signature d) = Mut_c ->
     class_qualifier (signature def) = Mut_c).
Proof.
  intros CT L qr b c C Rs Ao def P Ss Hct Hfind Hsuper Hrt HeA Hbc Hobv.
  destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hsuper)
    as (sd & Hsd & _ & _ & _ & Hpin & _).
  split.
  - intros d Hd. rewrite Hsd in Hd. inversion Hd; subst d.
    apply (obF_step CT L qr b c C Ao def P Ss sd Hct Hfind Hsuper Hsd).
    + unfold erases in HeA. rewrite HeA. exact Hrt.
    + exact Hbc.
    + exact (Hobv def Hfind).
  - intros d Hd Hq. rewrite Hsd in Hd. inversion Hd; subst d.
    destruct Hpin as [Hp | Hp]; congruence.
Qed.

(** The bound facts of an object, seen at any superclass. *)
Lemma ob_view : forall CT L qr b c Co Ao D lcD,
  wf_class_table CT ->
  lsuper_inst CT qr b c Co Ao D lcD ->
  wf_rtypeuse CT (mkruntime_type qr Co (map erase Ao)) ->
  (qr = Mut_r -> olab b = olab c) ->
  (forall d, find_class CT Co = Some d ->
     frame_fits CT L (class_env d) (obj_frame qr b c Ao)) ->
  forall d, find_class CT D = Some d ->
    frame_fits CT L (class_env d) (obj_frame qr b c lcD).
Proof.
  intros CT L qr b c Co Ao D lcD Hct H.
  induction H as [C As | C As P Ss D Vs Hparent Hrest IH];
    intros Hrt Hbc Hobv d Hd.
  - exact (Hobv d Hd).
  - pose proof Hparent as Hparent'. unfold parent_lookup in Hparent'.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
    destruct (chain_parent_facts CT L qr b c C (map erase As) As def P Ss
                Hct Hfind Hparent' Hrt eq_refl Hbc
                (fun d0 Hd0 => Hobv d0 (eq_trans (eq_sym Hfind) Hd0)))
      as (HobvP & _).
    apply IH; auto.
    rewrite map_erase_obj_frame.
    eapply rsuper_wf; [exact Hct | | exact Hrt].
    eapply rsi_step; eauto. apply rsi_refl.
Qed.

(** The bounds of the method type parameters, read at the two ends of the
    lookup chain. *)
Lemma lookup_lref_bounds : forall CT qr b c wf m0 Co Ro C Rs1,
  wf_class_table CT -> clean_bounds_ct CT ->
  rsuper_inst CT (qr2q qr) Co Ro C Rs1 ->
  wf_rtypeuse CT (mkruntime_type qr Co Ro) ->
  forall Ao, erases Ao Ro ->
  forall mth D' mdef' D mdef ca' ca lc' lc,
    FindMethodWithName CT Co mth D' mdef' ->
    FindMethodWithName CT C mth D mdef ->
    rsuper_inst CT (qr2q qr) Co Ro D' ca' ->
    rsuper_inst CT (qr2q qr) Co Ro D ca ->
    lsuper_inst CT qr b c Co Ao D' lc' ->
    lsuper_inst CT qr b c Co Ao D lc ->
    readonly_state_method_scope (mscope (msignature mdef')) ->
    forall lm L,
      (qr = Mut_r -> norm L (olab c) = norm L (if m0 then LIn wf else LOut)) ->
      rbounds_ok CT (qr2q qr) ca (map erase lm) (map erase lm)
        (mtparams (msignature mdef)) ->
      Forall2
        (fun Bu Bl =>
           lagree L (ldyn (act_frame qr wf m0 lc lm) Bu)
             (ldyn (act_frame qr wf m0 lc' lm) Bl))
        (mtparams (msignature mdef)) (mtparams (msignature mdef')).
Proof.
  intros CT qr b c wf m0 Co Ro C Rs1 Hct Hcl H.
  remember (qr2q qr) as qo eqn:Hqo.
  induction H as [C Rs | C Rs P Ss D0 Vs Hparent Hrest IH];
    intros Hrt Ao HeA mth D' mdef' D mdef ca' ca lc' lc Hf' Hf Hs' Hs Hl' Hl
      Hrsc lm L Hn Hb.
  - destruct (find_method_with_name_deterministic _ _ _ _ _ _ _ Hf' Hf) as [-> ->].
    assert (lc' = lc) by (eapply lsuper_inst_deterministic; eauto). subst lc'.
    apply Forall2_same. intros a. apply lagree_refl.
  - subst qo.
    pose proof (rsuper_inst_le _ _ _ _ _ _ Hct Hrest) as HleC.
    pose proof Hparent as Hparent'. unfold parent_lookup in Hparent'.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
    destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hparent') as (sd & _ & HltP & _).
    pose proof (base_subtype_le _ _ _ Hct (find_method_with_name_base _ _ _ _ _ Hf))
      as HleD.
    assert (HsD : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs []) Ss) D ca).
    { inversion Hs; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    assert (HrtP : wf_rtypeuse CT
                     (mkruntime_type qr P (map (dyn (qr2q qr) Rs []) Ss))).
    { eapply rsuper_wf; [exact Hct | | exact Hrt].
      eapply rsi_step; eauto. apply rsi_refl. }
    assert (HeAP : erases (map (ldyn (obj_frame qr b c Ao)) Ss)
                     (map (dyn (qr2q qr) Rs []) Ss)).
    { unfold erases. rewrite map_erase_obj_frame. unfold erases in HeA.
      rewrite HeA. reflexivity. }
    assert (HlD : lsuper_inst CT qr b c P (map (ldyn (obj_frame qr b c Ao)) Ss) D lc).
    { inversion Hl; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    inversion Hf'; subst.
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      assert (ca' = Rs).
      { eapply rsuper_inst_deterministic; [exact Hct | exact Hs' | apply rsi_refl]. }
      subst ca'.
      assert (lc' = Ao).
      { eapply lsuper_inst_deterministic; [exact Hct | exact Hl' | apply lsi_refl]. }
      subst lc'.
      destruct (find_from_subclass _ _ _ _ _ _ Hrest _ _ _ Hf) as (D1 & mdef1 & HfP).
      destruct (find_rsuper_exists _ _ _ _ _ HfP (qr2q qr)
                  (map (dyn (qr2q qr) Rs []) Ss)) as [ca1 Hs1].
      destruct (lsuper_inst_exists _ _ _ _ _ _ Hs1 qr b c
                  (map (ldyn (obj_frame qr b c Ao)) Ss) eq_refl HeAP)
        as (lc1 & Hl1 & He1).
      pose proof (find_method_wf _ _ _ _ _ Hct Hf') as Hwm.
      assert (HfP' : FindMethodWithName CT P (mname (msignature mdef')) D1 mdef1).
      { rewrite (gget_method_name_consistent _ _ _ Hget_method). exact HfP. }
      assert (Hs1' : rsuper_inst CT (qr2q qr) D' Rs D1 ca1)
        by (eapply rsi_step; eauto).
      destruct (override_data CT qr D' Rs def mdef' P Ss D1 mdef1 ca1
                  Hct Hrt Hfind Hparent' Hwm HfP' Hs1')
        as (Vs0 & Hag & Hsi & Hcompat & Hca1 & Hview & Hfbf).
      pose proof (lookup_refines _ _ _ _ _ _ Hct Hrest HrtP _ _ _ _ _ _ _
                    HfP Hf Hs1 HsD) as (Hsc & Hhd & Hma).
      destruct (Hma _ Hb) as (Hb1 & _ & _).
      assert (Hlen_lm : length lm = length (mtparams (msignature mdef1))).
      { pose proof (Forall2_length Hb1) as Hx. rewrite length_map in Hx. exact Hx. }
      pose proof Hcompat as (_ & Hscope & Hmtp & _).
      assert (Hrsc1 : readonly_state_method_scope (mscope (msignature mdef1))).
      { rewrite <- Hscope. exact Hrsc. }
      assert (Hnb' : nomut_bounds (method_tv_env CT D' (msignature mdef'))).
      { destruct (find_method_In _ _ _ _ _ Hf') as (defD & HfD & Hin).
        eapply Hcl; eauto. }
      assert (Hnb1 : nomut_bounds (method_tv_env CT D1 (msignature mdef1))).
      { destruct (find_method_In _ _ _ _ _ HfP) as (defD & HfD & Hin).
        eapply Hcl; eauto. }
      pose proof (IH HrtP _ HeAP _ _ _ _ _ _ _ lc1 lc HfP Hf Hs1 HsD Hl1 HlD
                    Hrsc1 lm L Hn Hb) as Htop.
      eapply Forall2_compose; [exact Htop | |].
      2:{ intros Bu B1 Bl Ha Hbb. eapply lagree_trans; [exact Ha | exact Hbb]. }
      rewrite Hmtp. apply Forall2_map_self.
      intros B1 HinB.
      destruct (In_nth_error _ _ HinB) as [n HnB].
      assert (Hf1 : fT B1 = B1).
      { apply (no_mut_fT (method_tv_env CT D1 (msignature mdef1))).
        exact (proj2 (Hnb1 MethodVar n B1 HnB)). }
      set (vB := member_type AbstractState
                    (qc2q (class_qualifier (signature def))) Vs0
                    (method_var_types (length (mtparams (msignature mdef1)))) B1).
      assert (HnV : nth_error (mtparams (msignature mdef')) n = Some vB).
      { rewrite Hmtp. rewrite nth_error_map. rewrite HnB. reflexivity. }
      assert (Hf2 : fT vB = vB).
      { apply (no_mut_fT (method_tv_env CT D' (msignature mdef'))).
        exact (proj2 (Hnb' MethodVar n vB HnV)). }
      rewrite <- Hf1 at 1. rewrite <- Hf2.
      exact (view_agree_fl CT qr D' Rs _ _ _ D1 ca1 Vs0 Hct Hag Hsi Hcompat Hca1
               Hview Hfbf Hrsc Hnb' L b c Ao lc1 wf m0 lm B1 HeA
               (lsi_step CT qr b c D' Ao P Ss D1 lc1 Hparent Hl1) Hn Hlen_lm).
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      rewrite Hsuper in Hparent'. inversion Hparent'; subst.
      pose proof (base_subtype_le _ _ _ Hct
                    (find_method_with_name_base _ _ _ _ _ Hparent_fmn)) as HleD'.
      assert (HsD' : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs []) Ss) D' ca').
      { inversion Hs'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      assert (HlD' : lsuper_inst CT qr b c P
                       (map (ldyn (obj_frame qr b c Ao)) Ss) D' lc').
      { inversion Hl'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      exact (IH HrtP _ HeAP _ _ _ _ _ _ _ lc' lc Hparent_fmn Hf HsD' HsD HlD' HlD
               Hrsc lm L Hn Hb).
Qed.

Lemma lookup_lref_params : forall CT qr b c wf m0 Co Ro C Rs1,
  wf_class_table CT -> clean_bounds_ct CT ->
  rsuper_inst CT (qr2q qr) Co Ro C Rs1 ->
  wf_rtypeuse CT (mkruntime_type qr Co Ro) ->
  forall Ao, erases Ao Ro ->
  forall mth D' mdef' D mdef ca' ca lc' lc,
    FindMethodWithName CT Co mth D' mdef' ->
    FindMethodWithName CT C mth D mdef ->
    rsuper_inst CT (qr2q qr) Co Ro D' ca' ->
    rsuper_inst CT (qr2q qr) Co Ro D ca ->
    lsuper_inst CT qr b c Co Ao D' lc' ->
    lsuper_inst CT qr b c Co Ao D lc ->
    readonly_state_method_scope (mscope (msignature mdef')) ->
    forall lm P h G L next,
      heapL P CT h G L next -> mutcL CT h G -> List.In wf L ->
      (qr = Mut_r -> norm L (olab c) = norm L (if m0 then LIn wf else LOut)) ->
      rbounds_ok CT (qr2q qr) ca (map erase lm) (map erase lm)
        (mtparams (msignature mdef)) ->
      (qr = Mut_r -> olab b = olab c) ->
      (forall d, find_class CT Co = Some d ->
         frame_fits CT L (class_env d) (obj_frame qr b c Ao)) ->
      (forall n B,
         nth_error (mtparams (msignature mdef)) n = Some B ->
         lsubt CT L (ldyn (act_frame qr wf m0 lc lm) (TVar TVSub MethodVar n))
           (ldyn (act_frame qr wf m0 lc lm) B)) ->
      Forall2
        (fun Pu Pl => forall v,
           loc_has_rtype CT h v (dyn (qr2q qr) ca (map erase lm) Pu) ->
           lhas CT h G L v (ldyn (act_frame qr wf m0 lc lm) (fT Pu)) ->
           lhas CT h G L v (ldyn (act_frame qr wf m0 lc' lm) (fT Pl)))
        (mparams (msignature mdef)) (mparams (msignature mdef')).
Proof.
  intros CT qr b c wf m0 Co Ro C Rs1 Hct Hcl H.
  remember (qr2q qr) as qo eqn:Hqo.
  induction H as [C Rs | C Rs P Ss D0 Vs Hparent Hrest IH];
    intros Hrt Ao HeA mth D' mdef' D mdef ca' ca lc' lc Hf' Hf Hs' Hs Hl' Hl
      Hrsc lm P0 h G L next HG HM HwfL HN Hb Hbc Hobv HMV.
  - destruct (find_method_with_name_deterministic _ _ _ _ _ _ _ Hf' Hf) as [-> ->].
    assert (ca' = ca) by (eapply rsuper_inst_deterministic; eauto). subst ca'.
    assert (lc' = lc) by (eapply lsuper_inst_deterministic; eauto). subst lc'.
    apply Forall2_same. intros a v _ Hv. exact Hv.
  - subst qo.
    assert (Hfull : rsuper_inst CT (qr2q qr) C Rs D0 Vs) by (eapply rsi_step; eauto).
    pose proof (lookup_lref_bounds CT qr b c wf m0 C Rs D0 Vs Hct Hcl Hfull Hrt
                  Ao HeA _ _ _ _ _ _ _ _ _ Hf' Hf Hs' Hs Hl' Hl Hrsc lm L HN Hb)
      as Hbds.
    pose proof (rsuper_inst_le _ _ _ _ _ _ Hct Hrest) as HleC.
    pose proof Hparent as Hparent'. unfold parent_lookup in Hparent'.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
    destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hparent') as (sd & _ & HltP & _).
    destruct (chain_parent_facts CT L qr b c C Rs Ao def P Ss Hct Hfind
                Hparent' Hrt HeA Hbc
                (fun d Hd => Hobv d (eq_trans (eq_sym Hfind) Hd)))
      as (HobvP & HupP).
    pose proof (base_subtype_le _ _ _ Hct (find_method_with_name_base _ _ _ _ _ Hf))
      as HleD.
    assert (HsD : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs []) Ss) D ca).
    { inversion Hs; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    assert (HrtP : wf_rtypeuse CT
                     (mkruntime_type qr P (map (dyn (qr2q qr) Rs []) Ss))).
    { eapply rsuper_wf; [exact Hct | | exact Hrt].
      eapply rsi_step; eauto. apply rsi_refl. }
    assert (HeAP : erases (map (ldyn (obj_frame qr b c Ao)) Ss)
                     (map (dyn (qr2q qr) Rs []) Ss)).
    { unfold erases. rewrite map_erase_obj_frame. unfold erases in HeA.
      rewrite HeA. reflexivity. }
    assert (HlD : lsuper_inst CT qr b c P (map (ldyn (obj_frame qr b c Ao)) Ss) D lc).
    { inversion Hl; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    inversion Hf'; subst.
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      assert (ca' = Rs).
      { eapply rsuper_inst_deterministic; [exact Hct | exact Hs' | apply rsi_refl]. }
      subst ca'.
      assert (lc' = Ao).
      { eapply lsuper_inst_deterministic; [exact Hct | exact Hl' | apply lsi_refl]. }
      subst lc'.
      destruct (find_from_subclass _ _ _ _ _ _ Hrest _ _ _ Hf) as (D1 & mdef1 & HfP).
      destruct (find_rsuper_exists _ _ _ _ _ HfP (qr2q qr)
                  (map (dyn (qr2q qr) Rs []) Ss)) as [ca1 Hs1].
      destruct (lsuper_inst_exists _ _ _ _ _ _ Hs1 qr b c
                  (map (ldyn (obj_frame qr b c Ao)) Ss) eq_refl HeAP)
        as (lc1 & Hl1 & He1).
      pose proof (find_method_wf _ _ _ _ _ Hct Hf') as Hwm.
      assert (HfP' : FindMethodWithName CT P (mname (msignature mdef')) D1 mdef1).
      { rewrite (gget_method_name_consistent _ _ _ Hget_method). exact HfP. }
      assert (Hs1' : rsuper_inst CT (qr2q qr) D' Rs D1 ca1)
        by (eapply rsi_step; eauto).
      destruct (override_data CT qr D' Rs def mdef' P Ss D1 mdef1 ca1
                  Hct Hrt Hfind Hparent' Hwm HfP' Hs1')
        as (Vs0 & Hag & Hsi & Hcompat & Hca1 & Hview & Hfbf).
      pose proof (override_step CT qr D' Rs def mdef' P Ss D1 mdef1 ca1
                    Hct Hrt Hfind Hparent' Hwm HfP' Hs1') as (_ & _ & Hma1).
      pose proof (lookup_refines _ _ _ _ _ _ Hct Hrest HrtP _ _ _ _ _ _ _
                    HfP Hf Hs1 HsD) as (Hsc & Hhd & Hma).
      destruct (Hma _ Hb) as (Hb1 & Hp & Hr).
      destruct (Hma1 _ Hb1) as (_ & _ & Hr1).
      assert (Hrsc1 : readonly_state_method_scope (mscope (msignature mdef1))).
      { destruct Hcompat as (_ & Hscope & _). rewrite <- Hscope. exact Hrsc. }
      assert (Hnb' : nomut_bounds (method_tv_env CT D' (msignature mdef'))).
      { destruct (find_method_In _ _ _ _ _ Hf') as (defD & HfD & Hin).
        eapply Hcl; eauto. }
      assert (HMVb : forall n B,
                nth_error (mtparams (msignature mdef')) n = Some B ->
                lsubt CT L (ldyn (act_frame qr wf m0 Ao lm) (TVar TVSub MethodVar n))
                  (ldyn (act_frame qr wf m0 Ao lm) B)).
      { intros n B HnB.
        pose proof (Forall2_nth_error_rel _ _ _ n Hbds) as Hrel.
        rewrite HnB in Hrel.
        destruct (nth_error (mtparams (msignature mdef)) n) as [Bt|] eqn:HBt;
          [|contradiction].
        eapply lsubt_agree_r; [|exact Hrel].
        exact (HMV n Bt HBt). }
      assert (Hflv : frame_fits CT L (method_tv_env CT D' (msignature mdef'))
                       (act_frame qr wf m0 Ao lm)).
      { exact (act_fits CT L qr b c wf m0 D' def (msignature mdef') Ao lm
                 Hct Hfind Hnb' (Hobv def eq_refl) HN HMVb). }
      pose proof (IH HrtP _ HeAP _ _ _ _ _ _ _ lc1 lc HfP Hf Hs1 HsD Hl1 HlD
                    Hrsc1 lm P0 h G L next HG HM HwfL HN Hb Hbc HobvP HMV) as Htop.
      pose proof (lref_params_step CT qr D' Rs _ _ _ D1 ca1 Vs0 Hct Hag Hsi
                    Hcompat Hca1 Hview Hfbf Hrsc Hnb' b c Ao lc1 wf m0 lm P0 h G L
                    next HeA (lsi_step CT qr b c D' Ao P Ss D1 lc1 Hparent Hl1)
                    HG HM HwfL HN Hb1 Hflv) as Hstep.
      eapply Forall2_compose;
        [exact (Forall2_conj _ _ _ _ Htop Hp) | exact Hstep |].
      intros Pu P1 Pl [Ha Hty1] Hb2 v Hty Hl0.
      apply Hb2; [apply Hty1; exact Hty | apply Ha; auto].
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      rewrite Hsuper in Hparent'. inversion Hparent'; subst.
      pose proof (base_subtype_le _ _ _ Hct
                    (find_method_with_name_base _ _ _ _ _ Hparent_fmn)) as HleD'.
      assert (HsD' : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs []) Ss) D' ca').
      { inversion Hs'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      assert (HlD' : lsuper_inst CT qr b c P
                       (map (ldyn (obj_frame qr b c Ao)) Ss) D' lc').
      { inversion Hl'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      exact (IH HrtP _ HeAP _ _ _ _ _ _ _ lc' lc Hparent_fmn Hf HsD' HsD HlD' HlD
               Hrsc lm P0 h G L next HG HM HwfL HN Hb Hbc HobvP HMV).
Qed.

Lemma lookup_lref_result : forall CT qr b c wf m0 Co Ro C Rs1,
  wf_class_table CT -> clean_bounds_ct CT ->
  rsuper_inst CT (qr2q qr) Co Ro C Rs1 ->
  wf_rtypeuse CT (mkruntime_type qr Co Ro) ->
  forall Ao, erases Ao Ro ->
  forall mth D' mdef' D mdef ca' ca lc' lc,
    FindMethodWithName CT Co mth D' mdef' ->
    FindMethodWithName CT C mth D mdef ->
    rsuper_inst CT (qr2q qr) Co Ro D' ca' ->
    rsuper_inst CT (qr2q qr) Co Ro D ca ->
    lsuper_inst CT qr b c Co Ao D' lc' ->
    lsuper_inst CT qr b c Co Ao D lc ->
    readonly_state_method_scope (mscope (msignature mdef')) ->
    forall lm P h G L next,
      heapL P CT h G L next -> mutcL CT h G -> (m0 = true -> List.In wf L) ->
      norm L (olab b) = norm L (LIn wf) ->
      (qr = Mut_r -> norm L (olab c) = norm L (if m0 then LIn wf else LOut)) ->
      (forall d, find_class CT Co = Some d ->
         class_qualifier (signature d) = Mut_c ->
         norm L (olab c) = norm L (LIn wf)) ->
      rbounds_ok CT (qr2q qr) ca (map erase lm) (map erase lm)
        (mtparams (msignature mdef)) ->
      (qr = Mut_r -> olab b = olab c) ->
      (forall d, find_class CT Co = Some d ->
         frame_fits CT L (class_env d) (obj_frame qr b c Ao)) ->
      (forall n B,
         nth_error (mtparams (msignature mdef)) n = Some B ->
         lsubt CT L (ldyn (act_frame qr wf m0 lc lm) (TVar TVSub MethodVar n))
           (ldyn (act_frame qr wf m0 lc lm) B)) ->
      forall v,
        loc_has_rtype CT h v
          (dyn (qr2q qr) ca' (map erase lm) (mret (msignature mdef'))) ->
        hexT G wf (mret (msignature mdef')) v ->
        lhas CT h G L v (ldyn (act_frame qr wf m0 lc' lm) (mret (msignature mdef'))) ->
        lhas CT h G L v (ldyn (act_frame qr wf m0 lc lm) (mret (msignature mdef))) /\
        hexT G wf (mret (msignature mdef)) v.
Proof.
  intros CT qr b c wf m0 Co Ro C Rs1 Hct Hcl H.
  remember (qr2q qr) as qo eqn:Hqo.
  induction H as [C Rs | C Rs P Ss D0 Vs Hparent Hrest IH];
    intros Hrt Ao HeA mth D' mdef' D mdef ca' ca lc' lc Hf' Hf Hs' Hs Hl' Hl
      Hrsc lm P0 h G L next HG HM HwfL N1 HN N3 Hb Hbc Hobv HMV v Hty Hex Hlv.
  - destruct (find_method_with_name_deterministic _ _ _ _ _ _ _ Hf' Hf) as [-> ->].
    assert (ca' = ca) by (eapply rsuper_inst_deterministic; eauto). subst ca'.
    assert (lc' = lc) by (eapply lsuper_inst_deterministic; eauto). subst lc'.
    split; assumption.
  - subst qo.
    assert (Hfull : rsuper_inst CT (qr2q qr) C Rs D0 Vs) by (eapply rsi_step; eauto).
    pose proof (lookup_lref_bounds CT qr b c wf m0 C Rs D0 Vs Hct Hcl Hfull Hrt
                  Ao HeA _ _ _ _ _ _ _ _ _ Hf' Hf Hs' Hs Hl' Hl Hrsc lm L HN Hb)
      as Hbds.
    pose proof (rsuper_inst_le _ _ _ _ _ _ Hct Hrest) as HleC.
    pose proof Hparent as Hparent'. unfold parent_lookup in Hparent'.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
    destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hparent') as (sd & _ & HltP & _).
    destruct (chain_parent_facts CT L qr b c C Rs Ao def P Ss Hct Hfind
                Hparent' Hrt HeA Hbc
                (fun d Hd => Hobv d (eq_trans (eq_sym Hfind) Hd)))
      as (HobvP & HupP).
    pose proof (base_subtype_le _ _ _ Hct (find_method_with_name_base _ _ _ _ _ Hf))
      as HleD.
    assert (HsD : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs []) Ss) D ca).
    { inversion Hs; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    assert (HrtP : wf_rtypeuse CT
                     (mkruntime_type qr P (map (dyn (qr2q qr) Rs []) Ss))).
    { eapply rsuper_wf; [exact Hct | | exact Hrt].
      eapply rsi_step; eauto. apply rsi_refl. }
    assert (HeAP : erases (map (ldyn (obj_frame qr b c Ao)) Ss)
                     (map (dyn (qr2q qr) Rs []) Ss)).
    { unfold erases. rewrite map_erase_obj_frame. unfold erases in HeA.
      rewrite HeA. reflexivity. }
    assert (HlD : lsuper_inst CT qr b c P (map (ldyn (obj_frame qr b c Ao)) Ss) D lc).
    { inversion Hl; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    inversion Hf'; subst.
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      assert (ca' = Rs).
      { eapply rsuper_inst_deterministic; [exact Hct | exact Hs' | apply rsi_refl]. }
      subst ca'.
      assert (lc' = Ao).
      { eapply lsuper_inst_deterministic; [exact Hct | exact Hl' | apply lsi_refl]. }
      subst lc'.
      destruct (find_from_subclass _ _ _ _ _ _ Hrest _ _ _ Hf) as (D1 & mdef1 & HfP).
      destruct (find_rsuper_exists _ _ _ _ _ HfP (qr2q qr)
                  (map (dyn (qr2q qr) Rs []) Ss)) as [ca1 Hs1].
      destruct (lsuper_inst_exists _ _ _ _ _ _ Hs1 qr b c
                  (map (ldyn (obj_frame qr b c Ao)) Ss) eq_refl HeAP)
        as (lc1 & Hl1 & He1).
      pose proof (find_method_wf _ _ _ _ _ Hct Hf') as Hwm.
      assert (HfP' : FindMethodWithName CT P (mname (msignature mdef')) D1 mdef1).
      { rewrite (gget_method_name_consistent _ _ _ Hget_method). exact HfP. }
      assert (Hs1' : rsuper_inst CT (qr2q qr) D' Rs D1 ca1)
        by (eapply rsi_step; eauto).
      destruct (override_data CT qr D' Rs def mdef' P Ss D1 mdef1 ca1
                  Hct Hrt Hfind Hparent' Hwm HfP' Hs1')
        as (Vs0 & Hag & Hsi & Hcompat & Hca1 & Hview & Hfbf).
      pose proof (override_step CT qr D' Rs def mdef' P Ss D1 mdef1 ca1
                    Hct Hrt Hfind Hparent' Hwm HfP' Hs1') as (_ & _ & Hma1).
      pose proof (lookup_refines _ _ _ _ _ _ Hct Hrest HrtP _ _ _ _ _ _ _
                    HfP Hf Hs1 HsD) as (Hsc & Hhd & Hma).
      destruct (Hma _ Hb) as (Hb1 & Hp & Hr).
      destruct (Hma1 _ Hb1) as (_ & _ & Hr1).
      assert (Hrsc1 : readonly_state_method_scope (mscope (msignature mdef1))).
      { destruct Hcompat as (_ & Hscope & _). rewrite <- Hscope. exact Hrsc. }
      assert (Hnb' : nomut_bounds (method_tv_env CT D' (msignature mdef'))).
      { destruct (find_method_In _ _ _ _ _ Hf') as (defD & HfD & Hin).
        eapply Hcl; eauto. }
      assert (HMVb : forall n B,
                nth_error (mtparams (msignature mdef')) n = Some B ->
                lsubt CT L (ldyn (act_frame qr wf m0 Ao lm) (TVar TVSub MethodVar n))
                  (ldyn (act_frame qr wf m0 Ao lm) B)).
      { intros n B HnB.
        pose proof (Forall2_nth_error_rel _ _ _ n Hbds) as Hrel.
        rewrite HnB in Hrel.
        destruct (nth_error (mtparams (msignature mdef)) n) as [Bt|] eqn:HBt;
          [|contradiction].
        eapply lsubt_agree_r; [|exact Hrel].
        exact (HMV n Bt HBt). }
      assert (Hflv : frame_fits CT L (method_tv_env CT D' (msignature mdef'))
                       (act_frame qr wf m0 Ao lm)).
      { exact (act_fits CT L qr b c wf m0 D' def (msignature mdef') Ao lm
                 Hct Hfind Hnb' (Hobv def eq_refl) HN HMVb). }
      assert (N3P : forall d, find_class CT P = Some d ->
                class_qualifier (signature d) = Mut_c ->
                norm L (olab c) = norm L (LIn wf)).
      { intros d Hd Hq. exact (N3 def eq_refl (HupP d Hd Hq)). }
      assert (Hlf1 : Forall rlost_free ca1).
      { pose proof (rsuper_wf _ _ _ _ _ _ Hct Hs1' Hrt) as Hv1.
        unfold wf_rtypeuse in Hv1. simpl in Hv1.
        destruct (find_class CT D1); [|contradiction].
        destruct Hv1 as (_ & Hlf & _). exact Hlf. }
      destruct (lref_result_step CT qr D' Rs _ _ _ D1 ca1 Vs0 Hct Hag Hsi
                  Hcompat Hca1 Hview Hfbf Hrsc Hnb' b c Ao lc1 wf m0 lm P0 h G L
                  next HeA (lsi_step CT qr b c D' Ao P Ss D1 lc1 Hparent Hl1)
                  HG HM HwfL N1 HN (N3 def eq_refl) Hb1 Hflv Hlf1 v Hty Hex Hlv)
        as [Hlv1 Hex1].
      exact (IH HrtP _ HeAP _ _ _ _ _ _ _ lc1 lc HfP Hf Hs1 HsD Hl1 HlD
               Hrsc1 lm P0 h G L next HG HM HwfL N1 HN N3P Hb Hbc HobvP HMV
               v (Hr1 _ _ Hty) Hex1 Hlv1).
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      rewrite Hsuper in Hparent'. inversion Hparent'; subst.
      pose proof (base_subtype_le _ _ _ Hct
                    (find_method_with_name_base _ _ _ _ _ Hparent_fmn)) as HleD'.
      assert (HsD' : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs []) Ss) D' ca').
      { inversion Hs'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      assert (HlD' : lsuper_inst CT qr b c P
                       (map (ldyn (obj_frame qr b c Ao)) Ss) D' lc').
      { inversion Hl'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      assert (N3P : forall d, find_class CT P = Some d ->
                class_qualifier (signature d) = Mut_c ->
                norm L (olab c) = norm L (LIn wf)).
      { intros d Hd Hq. exact (N3 def eq_refl (HupP d Hd Hq)). }
      exact (IH HrtP _ HeAP _ _ _ _ _ _ _ lc' lc Hparent_fmn Hf HsD' HsD HlD' HlD
               Hrsc lm P0 h G L next HG HM HwfL N1 HN N3P Hb Hbc HobvP HMV
               v Hty Hex Hlv).
Qed.
