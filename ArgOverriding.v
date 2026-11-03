From Stdlib Require Import List Lia Bool PeanoNat.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels ArgViews
  GhostTyping GhostForget GhostFit ArgTyping GhostInvariant ArgFit
  ArgInvariant ArgStatements.

(** Place in the proof: overriding.  First at the level of labels (what a
    caller passes to the method it selected statically is accepted by the
    method that runs, and what that method returns is what the static one
    promised), then over payload views, then for a declared receiver that
    requalifies a class parameter as receiver-dependent.
    Counterpart in the non-generic proof (ReadonlyWorlds.v): "overriding". *)

(* ------------------PART 1: OVERRIDING AT THE LEVEL OF LABELS------------------*)

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
Lemma lc_override_types : forall L qr qC wf m cs1 ms1 ks1 cs2 ms2 ks2,
  vpa_mutability_runtime_bound_agree qr qC = true ->
  label_cond L (fun q0 => fl (vpa_q AbstractState (qc2q qC) q0))
    (act_frame qr wf m cs1 ms1 ks1) (act_frame qr wf m cs2 ms2 ks2).
Proof.
  intros L qr qC wf m cs1 ms1 ks1 cs2 ms2 ks2 Hag q0.
  destruct qr, qC; try discriminate Hag; destruct q0; lc_solve.
Qed.

(** The receiver object's own reading against the callee's, forgotten. *)
Lemma lc_override_args : forall L qr qC b c As wf m cs ms ks,
  vpa_mutability_runtime_bound_agree qr qC = true ->
  (qr = Mut_r -> norm L (olab c) = norm L (if m then LIn wf else LOut)) ->
  label_cond L (fun q0 => fl (vpa_q AbstractState (qc2q qC) q0))
    (obj_frame qr b c As) (act_frame qr wf m cs ms ks).
Proof.
  intros L qr qC b c As wf m cs ms ks Hag Hn q0.
  destruct qr, qC; try discriminate Hag; destruct q0; try lc_solve.
  split; [left; reflexivity | right; right; exact (Hn eq_refl)].
Qed.

(** The receiver object's own reading against the callee's, once the
    callee's world agrees with the object's birth world. *)
Lemma lc_override_post : forall L qr qC b c As wf m cs ms ks,
  vpa_mutability_runtime_bound_agree qr qC = true ->
  norm L (olab b) = norm L (LIn wf) ->
  (qr = Mut_r -> norm L (olab c) = norm L (if m then LIn wf else LOut)) ->
  (qC = Mut_c -> norm L (olab c) = norm L (LIn wf)) ->
  label_cond L (vpa_q AbstractState (qc2q qC))
    (obj_frame qr b c As) (act_frame qr wf m cs ms ks).
Proof.
  intros L qr qC b c As wf m cs ms ks Hag N1 N2 N3 q0.
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
  lf_qargs Fo = lf_qargs Fc ->
  lagree L (ldyn Fc (map_qual f T)) (ldyn Fo T).
Proof.
  intros L f Fo Fc T Hq Hc Hm Hqs.
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
    destruct u as [|qual|m]; simpl; auto.
    + destruct (Hq qual) as [H1 H2].
      inversion HA; subst. simpl. constructor; auto.
      * left. exact H1.
      * right. destruct H2 as [H2 | H2]; [left; congruence | right; auto].
    + rewrite Hqs. inversion HA; subst. simpl.
      constructor; auto; first [left; reflexivity | right; right; reflexivity].
  - simpl. rewrite Hqs. constructor; [left; reflexivity | auto |].
    induction H; simpl; constructor; auto.
Qed.

Lemma lc_override_inv2 : forall L qr qC wf m cs1 ms1 ks1 cs2 ms2 ks2,
  vpa_mutability_runtime_bound_agree qr qC = true ->
  (qC = Mut_c -> norm L (if m then LIn wf else LOut) = norm L (LIn wf)) ->
  label_eq L (vpa_q AbstractState (qc2q qC))
    (act_frame qr wf m cs1 ms1 ks1) (act_frame qr wf m cs2 ms2 ks2).
Proof.
  intros L qr qC wf m cs1 ms1 ks1 cs2 ms2 ks2 Hag HN q0.
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
Lemma ldyn_no_method_vars : forall CT Δ T,
  wf_stype CT Δ T ->
  (method_bounds Δ, qparams Δ) = ([], 0) ->
  forall F ms ks, ldyn (lf_with_args F (lf_cargs F) ms ks) T = ldyn F T.
Proof.
  intros CT Δ T H. induction H using wf_stype_ind'; intros Hmq F ms ks;
    pose proof Hmq as Hmq'; injection Hmq' as Hm Hq0.
  - simpl. f_equal; try solve [destruct q0; reflexivity].
    induction H1; simpl; auto. inversion H0; subst. f_equal; auto.
  - destruct u as [|qv|m];
      [| |exfalso; simpl in H0; rewrite Hq0 in H0; inversion H0];
      (unfold tv_bound in H; destruct o; simpl in *;
       [|rewrite Hm in H; destruct n; discriminate]);
      simpl; auto.
  - exfalso. rewrite Hq0 in H. inversion H.
Qed.

(** An object's reading against the reading of an activation running on it,
    for types that write no [Mut]. *)
Lemma obj_act_cond : forall L qr b c As cs ms ks wf m cs' ms' ks',
  (qr = Mut_r -> norm L (olab c) = norm L (if m then LIn wf else LOut)) ->
  label_cond L (unm (fun q0 => q0))
    (lf_with_args (obj_frame qr b c As) cs ms ks) (act_frame qr wf m cs' ms' ks').
Proof.
  intros L qr b c As cs ms ks wf m cs' ms' ks' Hn q0.
  destruct q0; try lc_solve.
  destruct qr; [|lc_solve].
  split; [left; reflexivity | right; right; exact (Hn eq_refl)].
Qed.

(** The activation of a method of class [D'] fits its bounds: the class part
    comes from the receiver object, the method part is given. *)
Lemma act_fits : forall CT L qr b c wf m D' def' sig' lca lm lk,
  wf_class_table CT ->
  find_class CT D' = Some def' ->
  nomut_bounds (method_tv_env CT D' sig') ->
  frame_fits CT L (class_env def') (obj_frame qr b c lca) ->
  (qr = Mut_r -> norm L (olab c) = norm L (if m then LIn wf else LOut)) ->
  (forall n B,
     nth_error (mtparams sig') n = Some B ->
     lsubt CT L (ldyn (act_frame qr wf m lca lm lk) (TVar TVSub MethodVar n))
       (ldyn (act_frame qr wf m lca lm lk) B)) ->
  frame_fits CT L (method_tv_env CT D' sig') (act_frame qr wf m lca lm lk).
Proof.
  intros CT L qr b c wf m D' def' sig' lca lm lk Hct Hfind Hnb Hob Hn HMV o n B Hb.
  destruct o.
  - assert (HbC : nth_error (ctparams (signature def')) n = Some B).
    { unfold tv_bound, method_tv_env, class_tparams in Hb. simpl in Hb.
      rewrite Hfind in Hb. exact Hb. }
    pose proof (Hob ClassVar n B HbC) as Hs.
    change (ldyn (act_frame qr wf m lca lm lk) (TVar TVSub ClassVar n))
      with (ldyn (obj_frame qr b c lca) (TVar TVSub ClassVar n)).
    eapply lsubt_agree_r; [exact Hs|].
    destruct (Hnb _ _ _ Hb) as [_ HnmB].
    pose proof (class_bounds_wf _ _ _ Hct Hfind) as Hwfb.
    rewrite Forall_forall in Hwfb.
    pose proof (Hwfb _ (nth_error_In _ _ HbC)) as HwB.
    rewrite <- (ldyn_no_method_vars _ _ _ HwB eq_refl (obj_frame qr b c lca) lm lk).
    rewrite <- (map_qual_id B) at 2.
    rewrite (no_mut_unm _ _ (fun q0 => q0) HnmB).
    apply ldyn_map_qual_agree.
    + apply obj_act_cond. exact Hn.
    + simpl. apply Forall2_lagree_refl.
    + simpl. apply Forall2_lagree_refl.
    + reflexivity.
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
    (forall ma ka, ca1 = map (dyn (qr2q qr) ca' ma ka) Vs) /\
    (forall ma ka T,
       length ma = length (mtparams sig1) ->
       length ka = mqparams sig1 ->
       dyn (qr2q qr) ca' ma ka
         (member_type AbstractState (qc2q qC) Vs
            (method_var_types (length (mtparams sig1))) (qvar_args (mqparams sig1)) T) =
       dyn (qr2q qr) ca1 ma ka T) /\
    (forall ma ka,
       length ka = mqparams sig1 ->
       rbounds_ok CT (qr2q qr) ca1 ma ka ma (mtparams sig1) ->
       frame_bounds_ok CT (method_tv_env CT D' sig') (qr2q qr) ca' ma ka).
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
  assert (Hca1 : forall ma ka, ca1 = map (dyn (qr2q qr) ca' ma ka) Vs).
  { intros ma ka.
    pose proof (super_inst_dyn_exact _ _ _ _ _ _ _ Hsi (qr2q qr) ca' ma ka
                  (fun q0 => dynq_class_adapt qr qC q0 Hagree)) as Hex.
    rewrite dyn_class_var_types in Hex.
    eapply rsuper_inst_deterministic; eauto. }
  assert (Hview : forall ma ka T,
            length ma = length (mtparams sig1) ->
            length ka = mqparams sig1 ->
            dyn (qr2q qr) ca' ma ka
              (member_type AbstractState (qc2q qC) Vs
                 (method_var_types (length (mtparams sig1))) (qvar_args (mqparams sig1)) T) =
            dyn (qr2q qr) ca1 ma ka T).
  { intros ma ka T Hlen Hlenk. unfold member_type. rewrite dyn_subst.
    rewrite <- Hlen. rewrite dyn_method_var_types.
    rewrite <- Hlenk. rewrite rqarg_qvar_args. rewrite <- (Hca1 ma ka).
    apply dyn_class_adapt; auto. }
  exists Vs. refine (conj Hagree (conj Hsi (conj Hcompat (conj Hca1 (conj Hview _))))).
  intros ma ka Hk Hb1.
  assert (Hlen : length ma = length (mtparams sig1))
    by apply (Forall2_length Hb1).
  destruct Hcompat as (_ & _ & [Hmtp _] & _).
  apply frame_bounds_ok_of_rbounds; simpl.
  - unfold class_tparams. rewrite Hfind. unfold rbounds_ok in *.
    eapply Forall2_Forall_r_impl;
      [exact Hbnd | exact (class_bounds_wf _ _ _ Hct Hfind) |].
    intros R B HR HB. simpl in HR.
    rewrite (dyn_no_method_vars _ _ _ HB eq_refl). exact HR.
  - fold sig'. rewrite Hmtp. unfold rbounds_ok in *.
    eapply Forall2_map_right; [exact Hb1|].
    intros R B HR. simpl in *. rewrite Hview; auto.
Qed.

Lemma agree_mutc : forall qr,
  vpa_mutability_runtime_bound_agree qr Mut_c = true -> qr = Mut_r.
Proof. intros qr H. destruct qr; cbv in H; congruence. Qed.


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
  forall mth D' mdef' D mdef ca' ca ma ka,
    FindMethodWithName CT Co mth D' mdef' ->
    FindMethodWithName CT C mth D mdef ->
    rsuper_inst CT (qr2q qr) Co Ro D' ca' ->
    rsuper_inst CT (qr2q qr) Co Ro D ca ->
    length ka = mqparams (msignature mdef) ->
    rbounds_ok CT (qr2q qr) ca ma ka ma (mtparams (msignature mdef)) ->
    map (dyn (qr2q qr) ca' ma ka) (mtparams (msignature mdef')) =
    map (dyn (qr2q qr) ca ma ka) (mtparams (msignature mdef)).
Proof.
  intros CT qr Co Ro C Rs1 Hct H.
  remember (qr2q qr) as qo eqn:Hqo.
  induction H as [C Rs | C Rs P Ss D0 Vs Hparent Hrest IH];
    intros Hrt mth D' mdef' D mdef ca' ca ma ka Hf' Hf Hs' Hs Hk Hb.
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
    assert (HsD : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs [] []) Ss) D ca).
    { inversion Hs; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    assert (HrtP : wf_rtypeuse CT
                     (mkruntime_type qr P (map (dyn (qr2q qr) Rs [] []) Ss))).
    { eapply rsuper_wf; [exact Hct | | exact Hrt].
      eapply rsi_step; eauto. apply rsi_refl. }
    inversion Hf'; subst.
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      assert (ca' = Rs).
      { eapply rsuper_inst_deterministic; [exact Hct | exact Hs' | apply rsi_refl]. }
      subst ca'.
      destruct (find_from_subclass _ _ _ _ _ _ Hrest _ _ _ Hf) as (D1 & mdef1 & HfP).
      destruct (find_rsuper_exists _ _ _ _ _ HfP (qr2q qr)
                  (map (dyn (qr2q qr) Rs [] []) Ss)) as [ca1 Hs1].
      pose proof (find_method_wf _ _ _ _ _ Hct Hf') as Hwm.
      assert (HfP' : FindMethodWithName CT P (mname (msignature mdef')) D1 mdef1).
      { rewrite (gget_method_name_consistent _ _ _ Hget_method). exact HfP. }
      assert (Hs1' : rsuper_inst CT (qr2q qr) D' Rs D1 ca1)
        by (eapply rsi_step; eauto).
      destruct (override_data CT qr D' Rs def mdef' P Ss D1 mdef1 ca1
                  Hct Hrt Hfind Hparent' Hwm HfP' Hs1')
        as (Vs0 & Hag & Hsi & Hcompat & Hca1 & Hview & Hfbf).
      pose proof (lookup_refines _ _ _ _ _ _ Hct Hrest HrtP _ _ _ _ _ _ _
                    HfP Hf Hs1 HsD) as (Hsc & (_ & _ & Hmq) & Hma).
      destruct (Hma _ _ Hk Hb) as (Hb1 & _ & _).
      rewrite <- (IH HrtP _ _ _ _ _ _ _ _ _ HfP Hf Hs1 HsD Hk Hb).
      destruct Hcompat as (_ & _ & [Hmtp _] & _).
      rewrite Hmtp. rewrite map_map. apply map_ext. intros B.
      apply Hview; [apply (Forall2_length Hb1) | congruence].
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      rewrite Hsuper in Hparent'. inversion Hparent'; subst.
      pose proof (base_subtype_le _ _ _ Hct
                    (find_method_with_name_base _ _ _ _ _ Hparent_fmn)) as HleD'.
      assert (HsD' : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs [] []) Ss) D' ca').
      { inversion Hs'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      exact (IH HrtP _ _ _ _ _ _ _ _ _ Hparent_fmn Hf HsD' HsD Hk Hb).
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

(* ------------------PART 2: OVERRIDING OVER PAYLOAD VIEWS------------------*)

(** Overriding at the level of labels, over payload views. *)

(* ------------------THE VIEW OF A CLASS FROM A SUBCLASS------------------*)

(** One step of an object's view against a reading of the static view in a
    frame, for an object whose payload at this class is of its own label. *)
Lemma ostatic_step_g : forall L f F hq l pn As cs ms ks,
  (forall As0,
     label_cond2 L (fun q0 => q0) f
       (mk_lframe hq l l As0 [] []) (lf_with_args F cs ms ks)) ->
  (dynq (lf_q F) (f Mut) = Lost \/
   forall l', pn = Some (Mut, l') -> norm L l' = norm L l) ->
  lc2 L (rd_map false (fun q0 => q0) pn) f
    (hframe hq l pn As) (lf_with_args F cs ms ks).
Proof.
  intros L f F hq l pn As cs ms ks Hbase Hpay q1.
  rewrite rd_map_obj.
  destruct (Hbase As q1) as [H1 H2]. cbn [hframe lf_q lf_with_args] in H1, H2 |- *.
  split; [exact H1|].
  destruct H2 as [H2 | [H2 | H2]]; auto.
  destruct (q_eq_dec q1 Mut) as [-> | Hne].
  - destruct Hpay as [Hpay | Hpay]; [left; exact Hpay|].
    right. right.
    assert (Hlab : norm L (lab_of (mk_lframe hq (rd_lab l pn) l As [] []) Mut) =
                   norm L (lab_of (mk_lframe hq l l As [] []) Mut)).
    { simpl. destruct pn as [[qp lp]|]; simpl; auto.
      destruct qp; simpl; auto. }
    rewrite Hlab. exact H2.
  - right. right.
    assert (Hlab : lab_of (mk_lframe hq (rd_lab l pn) l As [] []) q1 =
                   lab_of (mk_lframe hq l l As [] []) q1).
    { destruct q1; simpl; try reflexivity; congruence. }
    rewrite Hlab. exact H2.
Qed.

(** The view the typing rules compute, in any mode and after any further
    qualifier map [g], is one an object with payloads of its own label agrees
    into. *)
Lemma oview_vs_static_g : forall CT mt qh C Ts D Vs,
  super_inst CT mt qh C Ts D Vs ->
  forall L F g qo l As,
    g RO = RO ->
    (forall As0 cs ms ks,
       label_cond2 L (fun q0 => q0) (fun q0 => g (vpa_q mt qh q0))
         (mk_lframe (qr2q qo) l l As0 [] []) (lf_with_args F cs ms ks)) ->
    (dynq (lf_q F) (g (vpa_q mt qh Mut)) = Lost \/ opcoh CT L qo l C As l) ->
    Forall2 (lagree L) As (map (ldyn F) (map (map_qual g) Ts)) ->
    exists Vs', oview CT qo l C As D Vs' /\
                Forall2 (lagree L) Vs' (map (ldyn F) (map (map_qual g) Vs)).
Proof.
  intros CT mt qh C Ts D Vs H.
  induction H; intros L F g qo l As Hg Hbase Hpc Hargs.
  - exists As. split; [apply v_refl | exact Hargs].
  - destruct (IHsuper_inst L F g qo l
                (hstep false (qr2q qo) (fun q0 => q0) l (pclassf CT C As) As Ss)
                Hg Hbase) as (Vs' & Hv & Hle).
    { destruct Hpc as [Hpc | Hpc]; [left; exact Hpc | right].
      exact (opcoh_step _ _ _ _ _ _ _ _ _ Hpc Hparent). }
    { assert (Heq : map (ldyn F)
                      (map (map_qual g) (map (subst Ts [] []) (map (adapt mt qh) Ss))) =
                    map (fun S => ldyn (lf_with_args F
                                          (map (ldyn F) (map (map_qual g) Ts)) [] [])
                                    (map_qual (fun q0 => g (vpa_q mt qh q0)) S)) Ss).
      { clear - Hg. induction Ss as [|S Ss IH]; simpl; auto.
        f_equal; auto. rewrite (map_qual_subst g Ts [] [] _ Hg).
        rewrite ldyn_subst. unfold adapt. rewrite map_qual_comp. reflexivity. }
      rewrite Heq. unfold hstep.
      clear IHsuper_inst H Heq. generalize Ss as Ss0.
      induction Ss0 as [|S Ss0 IH]; simpl; [constructor|].
      constructor; [|exact IH].
      apply ldyn_agree2.
      - apply (ostatic_step_g L (fun q0 => g (vpa_q mt qh q0)) F (qr2q qo) l
                 (pclassf CT C As) As
                 (map (ldyn F) (map (map_qual g) Ts)) []).
        + intros As0. apply Hbase.
        + destruct Hpc as [Hpc | Hpc]; [left; exact Hpc | right].
          intros l' Hp. apply (Hpc C As); [apply v_refl | exact Hp].
      - exact Hargs.
      - constructor.
      - reflexivity. }
    exists Vs'. split; auto. unfold oview. eapply v_step; eauto.
Qed.


(** The same view, for both readings of an object: the view the typing rules
    compute, in any mode and after any further qualifier map [g], is one the
    payload reading and the plain reading of an object with payloads of its
    own label agree into, node by node, under any escape. *)
Lemma oview3_vs_static_g : forall CT mt qh C Ts D Vs,
  super_inst CT mt qh C Ts D Vs ->
  forall L esc F g qo l As Ap,
    g RO = RO ->
    (forall As0 cs ms ks,
       label_cond2 L (fun q0 => q0) (fun q0 => g (vpa_q mt qh q0))
         (mk_lframe (qr2q qo) l l As0 [] []) (lf_with_args F cs ms ks)) ->
    (dynq (lf_q F) (g (vpa_q mt qh Mut)) = Lost \/ opcoh CT L qo l C As l) ->
    Forall3 (xagree L esc) As Ap (map (ldyn F) (map (map_qual g) Ts)) ->
    exists Vs' Vp', oview CT qo l C As D Vs' /\ oplain CT qo l C Ap D Vp' /\
                    Forall3 (xagree L esc) Vs' Vp' (map (ldyn F) (map (map_qual g) Vs)).
Proof.
  intros CT mt qh C Ts D Vs H.
  induction H; intros L esc F g qo l As Ap Hg Hbase Hpc Hargs.
  - exists As, Ap. split; [apply v_refl|]. split; [apply v_refl|]. exact Hargs.
  - destruct (IHsuper_inst L esc F g qo l
                (hstep false (qr2q qo) (fun q0 => q0) l (pclassf CT C As) As Ss)
                (hstep true (qr2q qo) (fun q0 => q0) l None Ap Ss)
                Hg Hbase) as (Vs' & Vp' & Hv & Hvp & Hle).
    { destruct Hpc as [Hpc | Hpc]; [left; exact Hpc | right].
      exact (opcoh_step _ _ _ _ _ _ _ _ _ Hpc Hparent). }
    { assert (Heq : map (ldyn F)
                      (map (map_qual g) (map (subst Ts [] []) (map (adapt mt qh) Ss))) =
                    map (fun S => ldyn (lf_with_args F
                                          (map (ldyn F) (map (map_qual g) Ts)) [] [])
                                    (map_qual (fun q0 => g (vpa_q mt qh q0)) S)) Ss).
      { clear - Hg. induction Ss as [|S Ss IH]; simpl; auto.
        f_equal; auto. rewrite (map_qual_subst g Ts [] [] _ Hg).
        rewrite ldyn_subst. unfold adapt. rewrite map_qual_comp. reflexivity. }
      rewrite Heq. unfold hstep. rewrite rd_map_obj. cbn [rd_map].
      clear IHsuper_inst H Heq. generalize Ss as Ss0.
      induction Ss0 as [|S Ss0 IH]; simpl; [constructor|].
      constructor; [|exact IH].
      apply ldyn_xagree3; simpl; try constructor; try reflexivity.
      - apply lc2_lc3; [|reflexivity].
        pose proof (ostatic_step_g L (fun q0 => g (vpa_q mt qh q0)) F (qr2q qo) l
                      (pclassf CT C As) As
                      (map (ldyn F) (map (map_qual g) Ts)) [] []) as Hc.
        rewrite rd_map_obj in Hc. apply Hc.
        + intros As0. apply Hbase.
        + destruct Hpc as [Hpc | Hpc]; [left; exact Hpc | right].
          intros l' Hp. apply (Hpc C As); [apply v_refl | exact Hp].
      - exact Hargs. }
    exists Vs', Vp'. split; [unfold oview; eapply v_step; eauto|].
    split; [unfold oplain; eapply v_step; eauto|]. exact Hle.
Qed.

(* ------------------SUBTYPING WITH MUTABLE POSITIONS FORGOTTEN------------------*)

(** Subtyping of types whose written mutable positions are forgotten, for
    any value: nothing is asked of the value's payloads. *)
Lemma lhasp_subtype_fl : forall P CT Δ h G L next mt qthis wf mode lc lm lk ca ma ka,
  wf_class_table CT ->
  heapP P CT h G L next ->
  List.In wf L ->
  readonly_state_method_scope mt ->
  tv_mode Δ = mt ->
  (forall o n B v,
     tv_bound Δ o n = Some B ->
     wf_r_typable CT h v (TVar TVSub o n) qthis ca ma ka ->
     lhasp CT h G L v (ldyn (act_frame qthis wf mode lc lm lk) (TVar TVSub o n)) ->
     lhasp CT h G L v (ldyn (act_frame qthis wf mode lc lm lk) B)) ->
  (forall o n B, tv_bound Δ o n = Some B -> fT B = B) ->
  frame_bounds_ok CT Δ (qr2q qthis) ca ma ka ->
  map erase lc = ca -> map erase lm = ma -> map fst lk = ka ->
  forall T U,
    qualified_type_subtype CT Δ T U ->
    forall v,
      wf_r_typable CT h v T qthis ca ma ka ->
      lhasp CT h G L v (ldyn (act_frame qthis wf mode lc lm lk) (fT T)) ->
      lhasp CT h G L v (ldyn (act_frame qthis wf mode lc lm lk) (fT U)).
Proof.
  intros P CT Δ h G L next mt qthis wf mode lc lm lk ca ma ka
    Hwf HG HwfL Hrs Hmode Hcb Hfl Hfb Hec Hem Hek T U Hsub.
  set (Fc := act_frame qthis wf mode lc lm lk).
  induction Hsub; intros v Hty Hl.
  - (* same class, widen the qualifier *)
    destruct Hl as (o & Ho & Hh & Vr & Vp & Hvr & Hvp & Hle).
    exists o. split; auto. simpl. split.
    + unfold headL. intros Hm. inversion Hqsub; subst.
      * apply Hh. exact Hm.
      * simpl in Hm. discriminate.
      * exfalso. exact (typable_head_not_bot _ _ _ _ _ _ _ _ Hty eq_refl).
    + exists Vr, Vp. split; auto. split; auto.
      eapply Forall3_xagree_trans_r.
      * eapply Forall3_xagree_mono; [|exact Hle].
        intros Hd Hm Hn. inversion Hqsub; subst.
        -- exact (Hd Hm Hn).
        -- simpl in Hm. discriminate.
        -- exfalso. exact (typable_head_not_bot _ _ _ _ _ _ _ _ Hty eq_refl).
      * apply map_ldyn_targ_sub.
        clear - Hargs. induction Hargs; simpl; constructor; auto using targ_sub_fl.
  - (* up the hierarchy *)
    pose proof Hl as (o & Ho & Hh & As & Ap & Hs & Hsp & Hle).
    rewrite Hmode in Hsuper.
    assert (Hcond : forall As0 cs ms ks,
              label_cond L (fun q0 => fl (vpa_q mt q1 q0))
                (obj_frame (rqtype (rt_type o)) (g_col G v) (g_col G v) As0)
                (act_frame qthis wf mode cs ms ks)).
    { intros As0 cs ms ks.
      destruct (q_eq_dec q1 Mut) as [-> | Hne].
      - apply fl_label_cond_mut. exact Hrs.
      - apply label_cond_fl.
        destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ _ Hty)
          as (o' & Vs' & Ho' & Hhead & _).
        rewrite Ho in Ho'. inversion Ho'; subst o'. clear Ho'.
        assert (Hnb : q1 <> Bot).
        { intros ->. exact (typable_head_not_bot _ _ _ _ _ _ _ _ Hty eq_refl). }
        change (headL L (g_col G v) (dynq (qr2q qthis) (fl q1))
                  (lab_of Fc (fl q1))) in Hh.
        rewrite (fl_ne _ Hne) in Hh. unfold headL in Hh.
        apply rs_label_cond2; auto.
        + intros E. contradiction.
        + intros -> Hqo. rewrite Hqo in Hhead.
          assert (qthis = Mut_r).
          { destruct qthis; auto. unfold head_ok in Hhead. simpl in Hhead.
            destruct Hhead as [Hx | [Hx | Hx]]; discriminate. }
          subst qthis. specialize (Hh eq_refl).
          change (lab_of Fc RDM) with (if mode then LIn wf else LOut) in Hh.
          destruct mode.
          * rewrite (norm_live _ _ HwfL) in Hh. exact Hh.
          * exact Hh. }
    assert (Hpc : dynq (lf_q Fc) (fl (vpa_q mt q1 Mut)) = Lost \/
                  opcoh CT L (rqtype (rt_type o)) (olab (g_col G v)) C As (olab (g_col G v)))
      by (left; destruct Hrs as [-> | ->]; destruct q1; reflexivity).
    destruct (oview3_vs_static_g _ _ _ _ _ _ _ Hsuper L _ Fc fl
                (rqtype (rt_type o)) (olab (g_col G v)) As Ap eq_refl
                (fun As0 cs ms ks => Hcond As0 cs ms ks) Hpc Hle)
      as (Vs0 & Vp0 & Hs0 & Hp0 & Hle0).
    exists o. split; auto. simpl. split; [exact Hh|].
    exists Vs0, Vp0. split; [eapply oview_trans; eauto|].
    split; [eapply oplain_trans; eauto|]. exact Hle0.
  - exact Hl.
  - (* a type variable at its bound *)
    rewrite (Hfl _ _ _ Hbound).
    eapply Hcb; eauto.
  - (* widen the written qualifier of a variable use *)
    destruct Hl as (ob & Hob & Hl). exists ob. split; auto.
    simpl in *.
    destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
      as [qa la Ca Aa].
    simpl in *. destruct Hl as (Hh & Vr & Vp & Hvr & Hvp & Hle).
    split.
    + unfold headL. intros Hm. inversion Hqsub; subst.
      * apply Hh. exact Hm.
      * simpl in Hm. discriminate.
      * exfalso. eapply (typable_whead_not_bot _ _ _ _ _ _ _ _ Hty). reflexivity.
    + exists Vr, Vp. split; [exact Hvr|]. split; [exact Hvp|].
      eapply Forall3_xagree_mono; [|exact Hle].
      intros Hd Hm Hn. inversion Hqsub; subst.
      * exact (Hd Hm Hn).
      * simpl in Hm. discriminate.
      * exfalso. eapply (typable_whead_not_bot _ _ _ _ _ _ _ _ Hty). reflexivity.
  - (* view the supplied type as readonly *)
    destruct Hl as (ob & Hob & Hl). exists ob. split; auto.
    simpl in *.
    destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
      as [qa la Ca Aa].
    simpl in *. destruct Hl as (Hh & Vr & Vp & Hvr & Hvp & Hle).
    split; [unfold headL; intros Hm; discriminate|].
    exists Vr, Vp. split; [exact Hvr|]. split; [exact Hvp|].
    eapply Forall3_xagree_mono; [|exact Hle].
    intros _ Hm _. simpl in Hm. discriminate.
  - exact Hl.
  - (* a use under a qualifier parameter, viewed as readonly *)
    destruct Hl as (ob & Hob & Hl). exists ob. split; auto.
    simpl in *.
    destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
      as [qa la Ca Aa].
    simpl in *. destruct Hl as (Hh & Vr & Vp & Hvr & Hvp & Hle).
    split; [unfold headL; intros Hm; discriminate|].
    exists Vr, Vp. split; [exact Hvr|]. split; [exact Hvp|].
    eapply Forall3_xagree_mono; [|exact Hle].
    intros _ Hm _. simpl in Hm. discriminate.
  - (* a qualified variable use at a bound, forgetting the bound's arguments *)
    pose proof (wf_r_typable_subtype _ _ _ _ _ _ _ _ _ _ Hfb
                  (qtype_qvar_bound CT Δ q1 o n qb C Ts Hsub Hcls) Hty) as Hty'.
    destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ _ Hty')
      as (ob & Rs' & Hob & _ & Hrs' & Hle').
    destruct (oview_exists _ _ _ _ _ _ Hrs' (rqtype (rt_type ob))
                (olab (g_col G v)) (g_args G v) eq_refl
                (hp_erase _ _ _ _ _ _ HG _ _ Hob)) as (Vs & Hs & He).
    destruct Hl as (ob' & Hob' & Hl).
    exists ob. split; auto. simpl. rewrite (map_fl_widen _ Hcls). split.
    + simpl in Hl.
      destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
        as [qa la Ca Aa].
      simpl in Hl. tauto.
    + destruct (oplain_exists _ _ _ _ _ _ _ Hs (olab (g_col G v))) as (Vp & Hvp).
      exists Vs, Vp. split; [exact Hs|]. split; [exact Hvp|].
      subst Rs'.
      assert (Heq : map (dyn (qr2q qthis) ca ma ka) (map widen_args Ts) =
                    map erase (map (ldyn Fc) (map widen_args Ts))).
      { rewrite map_erase_ldyn. unfold Fc, act_frame. cbn [lf_q lf_cargs lf_margs lf_qargs].
        rewrite Hec. rewrite Hem. rewrite Hek. reflexivity. }
      rewrite Heq in Hle'.
      apply Forall3_xagree_of_lagree.
      { eapply view_lvar; [exact Hwf | exact Hs | exact Hvp | apply Forall2_lvar_refl]. }
      clear - Hle' Hcls. revert Vs Hle'.
      induction Ts as [|T Ts IH]; intros Vs Hle'; simpl in *.
      * destruct Vs; [constructor | inversion Hle'].
      * apply andb_prop in Hcls as [HT HTs]. destruct Vs as [|V Vs]; [inversion Hle'|].
        simpl in Hle'. inversion Hle'; subst.
        constructor; [eapply lagree_widen_of_rarg; eauto | apply IH; auto].
  - (* a variable-headed class type viewed as readonly *)
    destruct Hl as (ob & Hob & Hl). exists ob. split; auto.
    simpl in *.
    simpl in *. destruct Hl as (Hh & Vr & Vp & Hvr & Hvp & Hle).
    split; [unfold headL; intros Hm; discriminate|].
    exists Vr, Vp. split; auto. split; auto.
    eapply Forall3_xagree_trans_r.
    + eapply Forall3_xagree_mono; [|exact Hle]. intros _ Hm _. simpl in Hm. discriminate.
    + apply map_ldyn_targ_sub.
      clear - Hargs. induction Hargs; simpl; constructor; auto using targ_sub_fl.
  - (* compatible arguments under the same variable head *)
    destruct Hl as (ob & Hob & Hl). exists ob. split; auto.
    simpl in *.
    simpl in *. destruct Hl as (Hh & Vr & Vp & Hvr & Hvp & Hle).
    split; [exact Hh|].
    exists Vr, Vp. split; auto. split; auto.
    eapply Forall3_xagree_trans_r; [exact Hle|].
    apply map_ldyn_targ_sub.
    clear - Hargs. induction Hargs; simpl; constructor; auto using targ_sub_fl.
  - (* up the hierarchy under the same variable head *)
    rewrite Hmode in Hsuper.
    destruct Hl as (ob & Hob & Hl).
    assert (Hcond : forall As0 cs ms ks,
              label_cond L (fun q0 => fl (vpa_q mt RO q0))
                (obj_frame (rqtype (rt_type ob)) (g_col G v) (g_col G v) As0)
                (act_frame qthis wf mode cs ms ks)).
    { intros As0 cs ms ks. apply label_cond_fl.
      apply rs_label_cond2; auto; try discriminate.
      unfold head_ok. left. reflexivity. }
    exists ob. split; auto.
    cbn [ldyn map_qual] in Hl |- *.
    destruct Hl as (Hh & As & Ap & Hs & Hsp & Hle).
    assert (Hpc : dynq (lf_q Fc) (fl (vpa_q mt RO Mut)) = Lost \/
                  opcoh CT L (rqtype (rt_type ob)) (olab (g_col G v)) C As (olab (g_col G v)))
      by (left; destruct Hrs as [-> | ->]; reflexivity).
    destruct (oview3_vs_static_g _ _ _ _ _ _ _ Hsuper L _ Fc fl
                (rqtype (rt_type ob)) (olab (g_col G v)) As Ap eq_refl
                (fun As0 cs ms ks => Hcond As0 cs ms ks) Hpc Hle)
      as (Vs0 & Vp0 & Hs0 & Hp0 & Hle0).
    split; [exact Hh|].
    exists Vs0, Vp0. split; [eapply oview_trans; eauto|].
    split; [eapply oplain_trans; eauto|]. exact Hle0.
  - (* the bottom-qualified type of the class *)
    exfalso. exact (typable_head_not_bot _ _ _ _ _ _ _ _ Hty eq_refl).
  - (* transitivity *)
    apply IHHsub2.
    + eapply wf_r_typable_subtype; eauto.
    + apply IHHsub1; auto.
Qed.

Lemma map_map_qual_id : forall Ts, map (map_qual (fun q0 => q0)) Ts = Ts.
Proof.
  induction Ts as [|T Ts IH]; simpl; auto. rewrite map_qual_id. rewrite IH.
  reflexivity.
Qed.

Lemma oview_vs_static_id : forall CT mt qh C Ts D Vs,
  super_inst CT mt qh C Ts D Vs ->
  forall L F qo l As,
    (forall As0 cs ms ks,
       label_cond2 L (fun q0 => q0) (vpa_q mt qh)
         (mk_lframe (qr2q qo) l l As0 [] []) (lf_with_args F cs ms ks)) ->
    (dynq (lf_q F) (vpa_q mt qh Mut) = Lost \/ opcoh CT L qo l C As l) ->
    Forall2 (lagree L) As (map (ldyn F) Ts) ->
    exists Vs', oview CT qo l C As D Vs' /\
                Forall2 (lagree L) Vs' (map (ldyn F) Vs).
Proof.
  intros CT mt qh C Ts D Vs H L F qo l As Hbase Hpc Hargs.
  destruct (oview_vs_static_g _ _ _ _ _ _ _ H L F (fun q0 => q0) qo l As
              eq_refl Hbase Hpc) as (Vs' & Hv & Hle).
  - rewrite map_map_qual_id. exact Hargs.
  - exists Vs'. split; auto. rewrite map_map_qual_id in Hle. exact Hle.
Qed.

(* ------------------ONE OVERRIDE STEP------------------*)

Lemma map_lqnth_seq : forall lk, map (lqnth lk) (seq 0 (length lk)) = lk.
Proof.
  unfold lqnth. induction lk as [|a lk IH]; simpl; auto.
  f_equal. rewrite <- seq_shift. rewrite map_map. exact IH.
Qed.

(** The identity qualifier arguments read as the frame's own. *)
Lemma lqarg_qvar_args : forall F,
  map (lqarg F) (qvar_args (length (lf_qargs F))) = lf_qargs F.
Proof.
  intros F. unfold qvar_args. rewrite map_map. simpl. apply map_lqnth_seq.
Qed.

Section StepP.
  Variables (CT : class_table) (qr : q_r) (D' : class_name) (ca' : list rtype).
  Variables (qC : q_c) (sig' sig1 : method_sig) (D1 : class_name).
  Variables (ca1 : list rtype) (Vs : list qualified_type).
  Hypothesis Hct : wf_class_table CT.
  Hypothesis Hag : vpa_mutability_runtime_bound_agree qr qC = true.
  Hypothesis Hsi :
    super_inst CT AbstractState (qc2q qC) D' (class_var_types (length ca')) D1 Vs.
  Hypothesis Hcompat :
    method_override_compatible CT (method_tv_env CT D' sig') qC Vs sig' sig1.
  Hypothesis Hca1 : forall ma ka, ca1 = map (dyn (qr2q qr) ca' ma ka) Vs.
  Hypothesis Hview : forall ma ka T,
    length ma = length (mtparams sig1) ->
    length ka = mqparams sig1 ->
    dyn (qr2q qr) ca' ma ka
      (member_type AbstractState (qc2q qC) Vs
         (method_var_types (length (mtparams sig1))) (qvar_args (mqparams sig1)) T) =
    dyn (qr2q qr) ca1 ma ka T.
  Hypothesis Hfbf : forall ma ka,
    length ka = mqparams sig1 ->
    rbounds_ok CT (qr2q qr) ca1 ma ka ma (mtparams sig1) ->
    frame_bounds_ok CT (method_tv_env CT D' sig') (qr2q qr) ca' ma ka.
  Hypothesis Hrsc : readonly_state_method_scope (mscope sig').
  Hypothesis Hnb : nomut_bounds (method_tv_env CT D' sig').

  Lemma view_agree_flp : forall L c lca' lc1 wf m lm lk T,
    map erase lca' = ca' ->
    oview CT qr (olab c) D' lca' D1 lc1 ->
    (qr = Mut_r -> norm L (olab c) = norm L (if m then LIn wf else LOut)) ->
    length lm = length (mtparams sig1) ->
    length lk = mqparams sig1 ->
    lagree L (ldyn (act_frame qr wf m lc1 lm lk) (fT T))
      (ldyn (act_frame qr wf m lca' lm lk)
         (fT (member_type AbstractState (qc2q qC) Vs
                (method_var_types (length (mtparams sig1))) (qvar_args (mqparams sig1)) T))).
  Proof using All.
    intros L c lca' lc1 wf m lm lk T Hec Hls Hn Hlen_lm Hlen_lk.
    set (F' := act_frame qr wf m lca' lm lk).
    unfold member_type, adapt. rewrite fT_subst. rewrite fT_method_var_types.
    rewrite fQ_qvar_args.
    rewrite map_qual_comp. rewrite ldyn_subst.
    assert (Hm : map (ldyn F') (method_var_types (length (mtparams sig1))) = lm).
    { rewrite <- Hlen_lm. apply (ldyn_method_var_types F'). }
    assert (Hk : map (lqarg F') (qvar_args (mqparams sig1)) = lk).
    { rewrite <- Hlen_lk. apply (lqarg_qvar_args F'). }
    fold F'. rewrite Hm. rewrite Hk.
    replace (map_qual (fun q0 => fl (vpa_q AbstractState (qc2q qC) q0)) T)
      with (map_qual (fun q0 => fl (vpa_q AbstractState (qc2q qC) q0)) (fT T)).
    2:{ rewrite map_qual_comp. apply map_qual_ext.
        intros q0. destruct q0, qC; reflexivity. }
    apply ldyn_map_qual_agree.
    - exact (lc_override_types L qr qC wf m lc1 lm lk
               (map (ldyn F') (map fT Vs)) lm lk Hag).
    - assert (Hrefl : Forall2 (lagree L) lca'
                (map (ldyn F') (map fT (class_var_types (length ca'))))).
      { rewrite fT_class_var_types.
        replace (length ca') with (length (lf_cargs F')).
        2:{ simpl. rewrite <- Hec. rewrite length_map. reflexivity. }
        rewrite ldyn_class_var_types. apply Forall2_lagree_refl. }
      destruct (oview_vs_static_g _ _ _ _ _ _ _ Hsi L F' fl qr (olab c) lca'
                  eq_refl) as (Vs0 & Hs0 & Hle0).
      + intros As0 cs ms ks.
        exact (lc_override_args L qr qC c c As0 wf m cs ms ks Hag Hn).
      + left. destruct qC; reflexivity.
      + exact Hrefl.
      + assert (Vs0 = lc1) by (eapply oview_deterministic; eauto).
        subst Vs0. exact Hle0.
    - simpl. apply Forall2_lagree_refl.
    - reflexivity.
  Qed.

  Lemma lref_params_stepp : forall c lca' lc1 wf m lm lk P h G L next,
    map erase lca' = ca' ->
    oview CT qr (olab c) D' lca' D1 lc1 ->
    heapP P CT h G L next -> List.In wf L ->
    (qr = Mut_r -> norm L (olab c) = norm L (if m then LIn wf else LOut)) ->
    length lk = mqparams sig1 ->
    rbounds_ok CT (qr2q qr) ca1 (map erase lm) (map fst lk) (map erase lm) (mtparams sig1) ->
    ffit CT L (method_tv_env CT D' sig') (act_frame qr wf m lca' lm lk) ->
    Forall2
      (fun P1 P' => forall v,
         loc_has_rtype CT h v (dyn (qr2q qr) ca1 (map erase lm) (map fst lk) P1) ->
         lhasp CT h G L v (ldyn (act_frame qr wf m lc1 lm lk) (fT P1)) ->
         lhasp CT h G L v (ldyn (act_frame qr wf m lca' lm lk) (fT P')))
      (mparams sig1) (mparams sig').
  Proof using All.
    intros c lca' lc1 wf m lm lk P h G L next Hec Hls HG HwfL Hn Hlen_lk Hb1 Hfit.
    assert (Hlen : length (map erase lm) = length (mtparams sig1))
      by apply (Forall2_length Hb1).
    assert (Hlen_lm : length lm = length (mtparams sig1)).
    { rewrite length_map in Hlen. exact Hlen. }
    assert (Hlenk' : length (map fst lk) = mqparams sig1)
      by (rewrite length_map; exact Hlen_lk).
    destruct Hcompat as (_ & Hscope & Hmtp & Hret & Hpar & _).
    eapply Forall2_impl; [|exact Hpar].
    intros P1 P' Hsub v Hty Hl. simpl in Hsub.
    apply (lhasp_subtype_fl P CT (method_tv_env CT D' sig') h G L next
             (mscope sig') qr wf m lca' lm lk ca' (map erase lm)
             _ Hct HG HwfL Hrsc eq_refl
             (vbp_of_fits CT _ h G L (act_frame qr wf m lca' lm lk) _ _ _ qr
                Hct (hp_cls _ _ _ _ _ _ HG)
                (fun v0 ob def Hob Hdef =>
                   proj1 (proj2 (proj2 (proj1 (hp_obj _ _ _ _ _ _ HG v0 ob Hob)))
                            def Hdef))
                (heap_pay P CT h G L next Hct HG)
                (proj2 Hfit) eq_refl Hec eq_refl eq_refl)
             (fun o n B Hb => no_mut_fT _ _ (proj2 (Hnb o n B Hb)))
             (Hfbf _ _ Hlenk' Hb1) Hec eq_refl eq_refl _ _ Hsub).
    - unfold wf_r_typable. rewrite Hview; auto.
    - eapply lhasp_agree; [exact Hl|].
      apply (view_agree_flp L c lca' lc1 wf m lm lk P1 Hec Hls Hn Hlen_lm Hlen_lk).
  Qed.

  Lemma lref_result_stepp : forall c lca' lc1 wf m lm lk P h G L next,
    map erase lca' = ca' ->
    oview CT qr (olab c) D' lca' D1 lc1 ->
    heapP P CT h G L next -> (m = true -> List.In wf L) ->
    norm L (olab c) = norm L (LIn wf) ->
    (qr = Mut_r -> norm L (olab c) = norm L (if m then LIn wf else LOut)) ->
    (qC = Mut_c -> norm L (olab c) = norm L (LIn wf)) ->
    opcoh CT L qr (olab c) D' lca' (olab c) ->
    length lk = mqparams sig1 ->
    rbounds_ok CT (qr2q qr) ca1 (map erase lm) (map fst lk) (map erase lm) (mtparams sig1) ->
    ffit CT L (method_tv_env CT D' sig') (act_frame qr wf m lca' lm lk) ->
    Forall rlost_free ca1 ->
    forall v,
      loc_has_rtype CT h v (dyn (qr2q qr) ca' (map erase lm) (map fst lk) (mret sig')) ->
      hexTp G wf (mret sig') v ->
      lhasp CT h G L v (ldyn (act_frame qr wf m lca' lm lk) (mret sig')) ->
      lhasp CT h G L v (ldyn (act_frame qr wf m lc1 lm lk) (mret sig1)) /\
      hexTp G wf (mret sig1) v.
  Proof using All.
    intros c lca' lc1 wf m lm lk P h G L next Hec Hls HG HwfL N1 N2 N3 Hop Hlen_lk Hb1
      Hfit Hlf1 v Hty Hex Hl.
    assert (Hlen : length (map erase lm) = length (mtparams sig1))
      by apply (Forall2_length Hb1).
    assert (Hlen_lm : length lm = length (mtparams sig1)).
    { rewrite length_map in Hlen. exact Hlen. }
    assert (Hlenk' : length (map fst lk) = mqparams sig1)
      by (rewrite length_map; exact Hlen_lk).
    destruct Hcompat as (_ & Hscope & Hmtp & Hret & Hpar & _).
    set (F' := act_frame qr wf m lca' lm lk).
    destruct (lhasp_subtype_ex P CT (method_tv_env CT D' sig') h G L next
                (mscope sig') qr wf m lca' lm lk ca' (map erase lm)
                _ Hct HG HwfL Hrsc eq_refl
                (vbp_of_fits CT _ h G L (act_frame qr wf m lca' lm lk) _ _ _ qr
                   Hct (hp_cls _ _ _ _ _ _ HG)
                   (fun v0 ob def Hob Hdef =>
                      proj1 (proj2 (proj2 (proj1 (hp_obj _ _ _ _ _ _ HG v0 ob Hob)))
                               def Hdef))
                   (heap_pay P CT h G L next Hct HG)
                   (proj2 Hfit) eq_refl Hec eq_refl eq_refl)
                (fun o n B Hb => nomut_bounds_head _ o n B Hnb Hb)
                (Hfbf _ _ Hlenk' Hb1) Hec eq_refl eq_refl _ _ Hret
                v Hty Hex Hl) as [Hv Hexv].
    split.
    - eapply lhasp_agree; [exact Hv|].
      unfold member_type, adapt. rewrite ldyn_subst.
      assert (Hm : map (ldyn F') (method_var_types (length (mtparams sig1))) = lm).
      { rewrite <- Hlen_lm. apply (ldyn_method_var_types F'). }
      assert (Hk : map (lqarg F') (qvar_args (mqparams sig1)) = lk).
      { rewrite <- Hlen_lk. apply (lqarg_qvar_args F'). }
      fold F'. rewrite Hm. rewrite Hk.
      apply ldyn_map_qual_agree_inv.
      + apply (lc_override_inv2 L qr qC wf m lc1 lm lk (map (ldyn F') Vs) lm lk Hag).
        intros HqC.
        assert (qr = Mut_r).
        { apply agree_mutc. rewrite <- HqC. exact Hag. }
        rewrite <- (N2 H). exact (N3 HqC).
      + simpl.
        assert (Hargs : Forall2 (lagree L) lca'
                  (map (ldyn F') (class_var_types (length ca')))).
        { replace (length ca') with (length (lf_cargs F')).
          2:{ simpl. rewrite <- Hec. rewrite length_map. reflexivity. }
          rewrite ldyn_class_var_types. apply Forall2_lagree_refl. }
        destruct (oview_vs_static_id _ _ _ _ _ _ _ Hsi L F' qr (olab c) lca')
          as (Vs0 & Hs0 & Hle0).
        * intros As0 cs ms ks.
          exact (lc_override_post L qr qC c c As0 wf m cs ms ks Hag N1 N2 N3).
        * right. exact Hop.
        * exact Hargs.
        * assert (Vs0 = lc1) by (eapply oview_deterministic; eauto).
          subst Vs0.
          apply Forall2_lagree_sym; [exact Hle0|].
          rewrite map_erase_ldyn. simpl. rewrite Hec.
          rewrite <- (Hca1 (map erase lm) (map fst lk)). exact Hlf1.
      + simpl. apply Forall2_lagree_refl.
      + reflexivity.
    - intros Hw. apply Hexv.
      rewrite (whead_member_some _ _ _ _ _ _ _ Hw). destruct qC; reflexivity.
  Qed.
End StepP.


(* ------------------ALONG THE LOOKUP CHAIN------------------*)

(** What is used of the receiver object at a class [K] of its chain. *)
Definition ofacts (CT : class_table) (L : list nat) (qr : q_r) (l : lab)
    (K : class_name) (Vs : list ltype) (d : class_def) : Prop :=
  hinv CT L qr l K Vs /\ frame_fitsp CT L (class_env d) (hfr CT qr l K Vs).

Lemma hfr_as_obj : forall CT qo c C As,
  exists b, hfr CT qo (olab c) C As = obj_frame qo b c As.
Proof.
  intros CT qo c C As. unfold hfr, hframe, obj_frame.
  destruct (rd_lab (olab c) (pclassf CT C As)) as [w|] eqn:E.
  - exists (Some w). destruct c; reflexivity.
  - exists (@None nat). destruct c; reflexivity.
Qed.

(** The activation of a method of a class without mutable positions in its
    bounds fits its bounds in both senses. *)
Lemma act_ffit : forall CT L qr c wf m D' def' sig' lca lm lk,
  wf_class_table CT ->
  find_class CT D' = Some def' ->
  nomut_bounds (method_tv_env CT D' sig') ->
  ofacts CT L qr (olab c) D' lca def' ->
  (qr = Mut_r -> norm L (olab c) = norm L (if m then LIn wf else LOut)) ->
  (forall n B,
     nth_error (mtparams sig') n = Some B ->
     lsubt CT L (ldyn (act_frame qr wf m lca lm lk) (TVar TVSub MethodVar n))
       (ldyn (act_frame qr wf m lca lm lk) B) /\
     fit3p CT L (ldyn (act_frame qr wf m lca lm lk) (TVar TVSub MethodVar n))
       (ldyn (act_frame qr wf m lca lm lk) B)) ->
  ffit CT L (method_tv_env CT D' sig') (act_frame qr wf m lca lm lk).
Proof.
  intros CT L qr c wf m D' def' sig' lca lm lk Hct Hfind Hnb [Hi Hfp] Hn HMV.
  destruct (hfr_as_obj CT qr c D' lca) as [b Hb].
  destruct Hi as (Hfit & _).
  pose proof (Hfit def' Hfind) as Hob. rewrite Hb in Hob. rewrite Hb in Hfp.
  split.
  - apply (act_fits CT L qr b c wf m D' def' sig' lca lm lk Hct Hfind Hnb Hob Hn).
    intros n B HnB. exact (proj1 (HMV n B HnB)).
  - intros o n B Hbd. destruct o.
    + assert (HbC : nth_error (ctparams (signature def')) n = Some B).
      { unfold tv_bound, method_tv_env, class_tparams in Hbd. simpl in Hbd.
        rewrite Hfind in Hbd. exact Hbd. }
      pose proof (Hfp ClassVar n B HbC) as Hs.
      change (ldyn (act_frame qr wf m lca lm lk) (TVar TVSub ClassVar n))
        with (ldyn (obj_frame qr b c lca) (TVar TVSub ClassVar n)).
      apply (fit3p_agree CT L _ _ _ Hs).
      destruct (Hnb _ _ _ Hbd) as [_ HnmB].
      pose proof (class_bounds_wf _ _ _ Hct Hfind) as Hwfb.
      rewrite Forall_forall in Hwfb.
      pose proof (Hwfb _ (nth_error_In _ _ HbC)) as HwB.
      rewrite <- (ldyn_no_method_vars _ _ _ HwB eq_refl (obj_frame qr b c lca) lm lk).
      rewrite <- (map_qual_id B) at 2.
      rewrite (no_mut_unm _ _ (fun q0 => q0) HnmB).
      apply ldyn_map_qual_agree.
      * apply obj_act_cond. exact Hn.
      * simpl. apply Forall2_lagree_refl.
      * simpl. apply Forall2_lagree_refl.
      * reflexivity.
    + exact (proj2 (HMV n B Hbd)).
Qed.

Lemma lookup_lref_boundsp : forall CT qr c wf m0 Co Ro C Rs1,
  wf_class_table CT -> clean_bounds_ct CT ->
  rsuper_inst CT (qr2q qr) Co Ro C Rs1 ->
  wf_rtypeuse CT (mkruntime_type qr Co Ro) ->
  forall Ao, erases Ao Ro ->
  forall mth D' mdef' D mdef ca' ca lc' lc,
    FindMethodWithName CT Co mth D' mdef' ->
    FindMethodWithName CT C mth D mdef ->
    rsuper_inst CT (qr2q qr) Co Ro D' ca' ->
    rsuper_inst CT (qr2q qr) Co Ro D ca ->
    oview CT qr (olab c) Co Ao D' lc' ->
    oview CT qr (olab c) Co Ao D lc ->
    readonly_state_method_scope (mscope (msignature mdef')) ->
    forall lm lk L,
      (qr = Mut_r -> norm L (olab c) = norm L (if m0 then LIn wf else LOut)) ->
      length lk = mqparams (msignature mdef) ->
      rbounds_ok CT (qr2q qr) ca (map erase lm) (map fst lk) (map erase lm)
        (mtparams (msignature mdef)) ->
      Forall2
        (fun Bu Bl =>
           lagree L (ldyn (act_frame qr wf m0 lc lm lk) Bu)
             (ldyn (act_frame qr wf m0 lc' lm lk) Bl))
        (mtparams (msignature mdef)) (mtparams (msignature mdef')).
Proof.
  intros CT qr c wf m0 Co Ro C Rs1 Hct Hcl H.
  remember (qr2q qr) as qo eqn:Hqo.
  induction H as [C Rs | C Rs P Ss D0 Vs Hparent Hrest IH];
    intros Hrt Ao HeA mth D' mdef' D mdef ca' ca lc' lc Hf' Hf Hs' Hs Hl' Hl
      Hrsc lm lk L Hn Hlk0 Hb.
  - destruct (find_method_with_name_deterministic _ _ _ _ _ _ _ Hf' Hf) as [-> ->].
    assert (lc' = lc) by (eapply oview_deterministic; eauto). subst lc'.
    apply Forall2_same. intros a. apply lagree_refl.
  - subst qo.
    pose proof (rsuper_inst_le _ _ _ _ _ _ Hct Hrest) as HleC.
    pose proof Hparent as Hparent'. unfold parent_lookup in Hparent'.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
    destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hparent') as (sd & _ & HltP & _).
    pose proof (base_subtype_le _ _ _ Hct (find_method_with_name_base _ _ _ _ _ Hf))
      as HleD.
    assert (HsD : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs [] []) Ss) D ca).
    { inversion Hs; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    assert (HrtP : wf_rtypeuse CT
                     (mkruntime_type qr P (map (dyn (qr2q qr) Rs [] []) Ss))).
    { eapply rsuper_wf; [exact Hct | | exact Hrt].
      eapply rsi_step; eauto. apply rsi_refl. }
    assert (HeAP : erases (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss)
                     (map (dyn (qr2q qr) Rs [] []) Ss)).
    { unfold erases. rewrite map_erase_hstep_obj. unfold erases in HeA.
      rewrite HeA. reflexivity. }
    assert (HlD : oview CT qr (olab c) P
                       (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss) D lc).
    { inversion Hl; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    inversion Hf'; subst.
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      assert (ca' = Rs).
      { eapply rsuper_inst_deterministic; [exact Hct | exact Hs' | apply rsi_refl]. }
      subst ca'.
      assert (lc' = Ao).
      { eapply oview_deterministic; [exact Hct | exact Hl' | apply v_refl]. }
      subst lc'.
      destruct (find_from_subclass _ _ _ _ _ _ Hrest _ _ _ Hf) as (D1 & mdef1 & HfP).
      destruct (find_rsuper_exists _ _ _ _ _ HfP (qr2q qr)
                  (map (dyn (qr2q qr) Rs [] []) Ss)) as [ca1 Hs1].
      destruct (oview_exists _ _ _ _ _ _ Hs1 qr (olab c) _ eq_refl HeAP)
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
                    HfP Hf Hs1 HsD) as (Hsc & (Hhd & _ & Hmq) & Hma).
      destruct (Hma _ _ (eq_trans (length_map fst lk) Hlk0) Hb) as (Hb1 & _ & _).
      assert (Hlen_lm : length lm = length (mtparams (msignature mdef1))).
      { pose proof (Forall2_length Hb1) as Hx. rewrite length_map in Hx. exact Hx. }
      assert (Hlen_lk : length lk = mqparams (msignature mdef1)) by congruence.
      pose proof Hcompat as (_ & Hscope & [Hmtp _] & _).
      assert (Hrsc1 : readonly_state_method_scope (mscope (msignature mdef1))).
      { rewrite <- Hscope. exact Hrsc. }
      assert (Hnb' : nomut_bounds (method_tv_env CT D' (msignature mdef'))).
      { destruct (find_method_In _ _ _ _ _ Hf') as (defD & HfD & Hin).
        eapply Hcl; eauto. }
      assert (Hnb1 : nomut_bounds (method_tv_env CT D1 (msignature mdef1))).
      { destruct (find_method_In _ _ _ _ _ HfP) as (defD & HfD & Hin).
        eapply Hcl; eauto. }
      pose proof (IH HrtP _ HeAP _ _ _ _ _ _ _ lc1 lc HfP Hf Hs1 HsD Hl1 HlD
                    Hrsc1 lm lk L Hn Hlk0 Hb) as Htop.
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
                    (method_var_types (length (mtparams (msignature mdef1)))) (qvar_args (mqparams (msignature mdef1))) B1).
      assert (HnV : nth_error (mtparams (msignature mdef')) n = Some vB).
      { rewrite Hmtp. rewrite nth_error_map. rewrite HnB. reflexivity. }
      assert (Hf2 : fT vB = vB).
      { apply (no_mut_fT (method_tv_env CT D' (msignature mdef'))).
        exact (proj2 (Hnb' MethodVar n vB HnV)). }
      rewrite <- Hf1 at 1. rewrite <- Hf2.
      exact (view_agree_flp CT qr D' Rs _ _ _ D1 ca1 Vs0 Hct Hag Hsi Hcompat Hca1
               Hview Hfbf Hrsc Hnb' L c Ao lc1 wf m0 lm lk B1 HeA
               (v_step CT false (qr2q qr) (fun q0 => q0) (olab c) D' Ao P Ss D1 lc1 Hparent Hl1) Hn Hlen_lm Hlen_lk).
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      rewrite Hsuper in Hparent'. inversion Hparent'; subst.
      pose proof (base_subtype_le _ _ _ Hct
                    (find_method_with_name_base _ _ _ _ _ Hparent_fmn)) as HleD'.
      assert (HsD' : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs [] []) Ss) D' ca').
      { inversion Hs'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      assert (HlD' : oview CT qr (olab c) P
                       (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss) D' lc').
      { inversion Hl'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      exact (IH HrtP _ HeAP _ _ _ _ _ _ _ lc' lc Hparent_fmn Hf HsD' HsD HlD' HlD
               Hrsc lm lk L Hn Hlk0 Hb).
Qed.

Lemma lookup_lref_paramsp : forall CT qr c wf m0 Co Ro C Rs1,
  wf_class_table CT -> clean_bounds_ct CT ->
  rsuper_inst CT (qr2q qr) Co Ro C Rs1 ->
  wf_rtypeuse CT (mkruntime_type qr Co Ro) ->
  forall Ao, erases Ao Ro ->
  forall mth D' mdef' D mdef ca' ca lc' lc,
    FindMethodWithName CT Co mth D' mdef' ->
    FindMethodWithName CT C mth D mdef ->
    rsuper_inst CT (qr2q qr) Co Ro D' ca' ->
    rsuper_inst CT (qr2q qr) Co Ro D ca ->
    oview CT qr (olab c) Co Ao D' lc' ->
    oview CT qr (olab c) Co Ao D lc ->
    readonly_state_method_scope (mscope (msignature mdef')) ->
    forall lm lk P h G L next,
      heapP P CT h G L next -> List.In wf L ->
      (qr = Mut_r -> norm L (olab c) = norm L (if m0 then LIn wf else LOut)) ->
      length lk = mqparams (msignature mdef) ->
      rbounds_ok CT (qr2q qr) ca (map erase lm) (map fst lk) (map erase lm)
        (mtparams (msignature mdef)) ->
      (forall K Vs0 d, oview CT qr (olab c) Co Ao K Vs0 ->
         find_class CT K = Some d -> ofacts CT L qr (olab c) K Vs0 d) ->
      (forall n B,
         nth_error (mtparams (msignature mdef)) n = Some B ->
         lsubt CT L (ldyn (act_frame qr wf m0 lc lm lk) (TVar TVSub MethodVar n))
           (ldyn (act_frame qr wf m0 lc lm lk) B) /\
         fit3p CT L (ldyn (act_frame qr wf m0 lc lm lk) (TVar TVSub MethodVar n))
           (ldyn (act_frame qr wf m0 lc lm lk) B)) ->
      Forall2
        (fun Pu Pl => forall v,
           loc_has_rtype CT h v (dyn (qr2q qr) ca (map erase lm) (map fst lk) Pu) ->
           lhasp CT h G L v (ldyn (act_frame qr wf m0 lc lm lk) (fT Pu)) ->
           lhasp CT h G L v (ldyn (act_frame qr wf m0 lc' lm lk) (fT Pl)))
        (mparams (msignature mdef)) (mparams (msignature mdef')).
Proof.
  intros CT qr c wf m0 Co Ro C Rs1 Hct Hcl H.
  remember (qr2q qr) as qo eqn:Hqo.
  induction H as [C Rs | C Rs P Ss D0 Vs Hparent Hrest IH];
    intros Hrt Ao HeA mth D' mdef' D mdef ca' ca lc' lc Hf' Hf Hs' Hs Hl' Hl
      Hrsc lm lk P0 h G L next HG HwfL HN Hlk0 Hb Hall HMV.
  - destruct (find_method_with_name_deterministic _ _ _ _ _ _ _ Hf' Hf) as [-> ->].
    assert (ca' = ca) by (eapply rsuper_inst_deterministic; eauto). subst ca'.
    assert (lc' = lc) by (eapply oview_deterministic; eauto). subst lc'.
    apply Forall2_same. intros a v _ Hv. exact Hv.
  - subst qo.
    assert (Hfull : rsuper_inst CT (qr2q qr) C Rs D0 Vs) by (eapply rsi_step; eauto).
    pose proof (lookup_lref_boundsp CT qr c wf m0 C Rs D0 Vs Hct Hcl Hfull Hrt
                  Ao HeA _ _ _ _ _ _ _ _ _ Hf' Hf Hs' Hs Hl' Hl Hrsc lm lk L HN Hlk0 Hb)
      as Hbds.
    pose proof (rsuper_inst_le _ _ _ _ _ _ Hct Hrest) as HleC.
    pose proof Hparent as Hparent'. unfold parent_lookup in Hparent'.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
    destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hparent') as (sd & _ & HltP & _).
    assert (HallP : forall K Vs0 d,
              oview CT qr (olab c) P
                (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss)
                K Vs0 ->
              find_class CT K = Some d -> ofacts CT L qr (olab c) K Vs0 d).
    { intros K Vs0 d Hv Hd. apply (Hall K Vs0 d); auto.
      unfold oview in *. eapply v_step; eauto. }
    assert (HupP : forall d, find_class CT P = Some d ->
              class_qualifier (signature d) = Mut_c ->
              class_qualifier (signature def) = Mut_c).
    { intros d Hd Hq.
      destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hparent')
        as (sd0 & Hsd0 & _ & _ & _ & Hpin & _).
      rewrite Hsd0 in Hd. inversion Hd; subst d.
      destruct Hpin as [Hp | Hp]; congruence. }
    pose proof (base_subtype_le _ _ _ Hct (find_method_with_name_base _ _ _ _ _ Hf))
      as HleD.
    assert (HsD : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs [] []) Ss) D ca).
    { inversion Hs; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    assert (HrtP : wf_rtypeuse CT
                     (mkruntime_type qr P (map (dyn (qr2q qr) Rs [] []) Ss))).
    { eapply rsuper_wf; [exact Hct | | exact Hrt].
      eapply rsi_step; eauto. apply rsi_refl. }
    assert (HeAP : erases (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss)
                     (map (dyn (qr2q qr) Rs [] []) Ss)).
    { unfold erases. rewrite map_erase_hstep_obj. unfold erases in HeA.
      rewrite HeA. reflexivity. }
    assert (HlD : oview CT qr (olab c) P
                       (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss) D lc).
    { inversion Hl; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    inversion Hf'; subst.
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      assert (ca' = Rs).
      { eapply rsuper_inst_deterministic; [exact Hct | exact Hs' | apply rsi_refl]. }
      subst ca'.
      assert (lc' = Ao).
      { eapply oview_deterministic; [exact Hct | exact Hl' | apply v_refl]. }
      subst lc'.
      destruct (find_from_subclass _ _ _ _ _ _ Hrest _ _ _ Hf) as (D1 & mdef1 & HfP).
      destruct (find_rsuper_exists _ _ _ _ _ HfP (qr2q qr)
                  (map (dyn (qr2q qr) Rs [] []) Ss)) as [ca1 Hs1].
      destruct (oview_exists _ _ _ _ _ _ Hs1 qr (olab c) _ eq_refl HeAP)
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
                    HfP Hf Hs1 HsD) as (Hsc & (Hhd & _ & Hmq) & Hma).
      destruct (Hma _ _ (eq_trans (length_map fst lk) Hlk0) Hb) as (Hb1 & Hp & Hr).
      destruct (Hma1 _ _ (eq_trans (eq_trans (length_map fst lk) Hlk0) (eq_sym Hmq)) Hb1) as (_ & _ & Hr1).
      assert (Hrsc1 : readonly_state_method_scope (mscope (msignature mdef1))).
      { destruct Hcompat as (_ & Hscope & _). rewrite <- Hscope. exact Hrsc. }
      assert (Hnb' : nomut_bounds (method_tv_env CT D' (msignature mdef'))).
      { destruct (find_method_In _ _ _ _ _ Hf') as (defD & HfD & Hin).
        eapply Hcl; eauto. }
      assert (HMVb : forall n B,
                nth_error (mtparams (msignature mdef')) n = Some B ->
                lsubt CT L (ldyn (act_frame qr wf m0 Ao lm lk) (TVar TVSub MethodVar n))
                  (ldyn (act_frame qr wf m0 Ao lm lk) B) /\
                fit3p CT L (ldyn (act_frame qr wf m0 Ao lm lk) (TVar TVSub MethodVar n))
                  (ldyn (act_frame qr wf m0 Ao lm lk) B)).
      { intros n B HnB.
        pose proof (Forall2_nth_error_rel _ _ _ n Hbds) as Hrel.
        rewrite HnB in Hrel.
        destruct (nth_error (mtparams (msignature mdef)) n) as [Bt|] eqn:HBt;
          [|contradiction].
        destruct (HMV n Bt HBt) as [HM1 HM2]. split.
        - eapply lsubt_agree_r; [exact HM1 | exact Hrel].
        - eapply fit3p_agree; [exact HM2 | exact Hrel]. }
      assert (Hflv : ffit CT L (method_tv_env CT D' (msignature mdef'))
                       (act_frame qr wf m0 Ao lm lk)).
      { exact (act_ffit CT L qr c wf m0 D' def (msignature mdef') Ao lm lk
                 Hct Hfind Hnb'
                 (Hall D' Ao def (v_refl _ _ _ _ _ _ _) Hfind) HN HMVb). }
      pose proof (IH HrtP _ HeAP _ _ _ _ _ _ _ lc1 lc HfP Hf Hs1 HsD Hl1 HlD
                    Hrsc1 lm lk P0 h G L next HG HwfL HN Hlk0 Hb HallP HMV) as Htop.
      pose proof (lref_params_stepp CT qr D' Rs _ _ _ D1 ca1 Vs0 Hct Hag Hsi
                    Hcompat Hca1 Hview Hfbf Hrsc Hnb' c Ao lc1 wf m0 lm lk P0 h G L
                    next HeA (v_step CT false (qr2q qr) (fun q0 => q0) (olab c) D' Ao P Ss D1 lc1 Hparent Hl1)
                    HG HwfL HN (eq_trans Hlk0 (eq_sym Hmq)) Hb1 Hflv) as Hstep.
      eapply Forall2_compose;
        [exact (Forall2_conj _ _ _ _ Htop Hp) | exact Hstep |].
      intros Pu P1 Pl [Ha Hty1] Hb2 v Hty Hl0.
      apply Hb2; [apply Hty1; exact Hty | apply Ha; auto].
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      rewrite Hsuper in Hparent'. inversion Hparent'; subst.
      pose proof (base_subtype_le _ _ _ Hct
                    (find_method_with_name_base _ _ _ _ _ Hparent_fmn)) as HleD'.
      assert (HsD' : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs [] []) Ss) D' ca').
      { inversion Hs'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      assert (HlD' : oview CT qr (olab c) P
                       (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss) D' lc').
      { inversion Hl'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      exact (IH HrtP _ HeAP _ _ _ _ _ _ _ lc' lc Hparent_fmn Hf HsD' HsD HlD' HlD
               Hrsc lm lk P0 h G L next HG HwfL HN Hlk0 Hb HallP HMV).
Qed.

Lemma lookup_lref_resultp : forall CT qr c wf m0 Co Ro C Rs1,
  wf_class_table CT -> clean_bounds_ct CT ->
  rsuper_inst CT (qr2q qr) Co Ro C Rs1 ->
  wf_rtypeuse CT (mkruntime_type qr Co Ro) ->
  forall Ao, erases Ao Ro ->
  forall mth D' mdef' D mdef ca' ca lc' lc,
    FindMethodWithName CT Co mth D' mdef' ->
    FindMethodWithName CT C mth D mdef ->
    rsuper_inst CT (qr2q qr) Co Ro D' ca' ->
    rsuper_inst CT (qr2q qr) Co Ro D ca ->
    oview CT qr (olab c) Co Ao D' lc' ->
    oview CT qr (olab c) Co Ao D lc ->
    readonly_state_method_scope (mscope (msignature mdef')) ->
    forall lm lk P h G L next,
      heapP P CT h G L next -> (m0 = true -> List.In wf L) ->
      norm L (olab c) = norm L (LIn wf) ->
      (qr = Mut_r -> norm L (olab c) = norm L (if m0 then LIn wf else LOut)) ->
      (forall d, find_class CT Co = Some d ->
         class_qualifier (signature d) = Mut_c ->
         norm L (olab c) = norm L (LIn wf)) ->
      length lk = mqparams (msignature mdef) ->
      rbounds_ok CT (qr2q qr) ca (map erase lm) (map fst lk) (map erase lm)
        (mtparams (msignature mdef)) ->
      (forall K Vs0 d, oview CT qr (olab c) Co Ao K Vs0 ->
         find_class CT K = Some d -> ofacts CT L qr (olab c) K Vs0 d) ->
      (forall n B,
         nth_error (mtparams (msignature mdef)) n = Some B ->
         lsubt CT L (ldyn (act_frame qr wf m0 lc lm lk) (TVar TVSub MethodVar n))
           (ldyn (act_frame qr wf m0 lc lm lk) B) /\
         fit3p CT L (ldyn (act_frame qr wf m0 lc lm lk) (TVar TVSub MethodVar n))
           (ldyn (act_frame qr wf m0 lc lm lk) B)) ->
      forall v,
        loc_has_rtype CT h v
          (dyn (qr2q qr) ca' (map erase lm) (map fst lk) (mret (msignature mdef'))) ->
        hexTp G wf (mret (msignature mdef')) v ->
        lhasp CT h G L v (ldyn (act_frame qr wf m0 lc' lm lk) (mret (msignature mdef'))) ->
        lhasp CT h G L v (ldyn (act_frame qr wf m0 lc lm lk) (mret (msignature mdef))) /\
        hexTp G wf (mret (msignature mdef)) v.
Proof.
  intros CT qr c wf m0 Co Ro C Rs1 Hct Hcl H.
  remember (qr2q qr) as qo eqn:Hqo.
  induction H as [C Rs | C Rs P Ss D0 Vs Hparent Hrest IH];
    intros Hrt Ao HeA mth D' mdef' D mdef ca' ca lc' lc Hf' Hf Hs' Hs Hl' Hl
      Hrsc lm lk P0 h G L next HG HwfL N1 HN N3 Hlk0 Hb Hall HMV v Hty Hex Hlv.
  - destruct (find_method_with_name_deterministic _ _ _ _ _ _ _ Hf' Hf) as [-> ->].
    assert (ca' = ca) by (eapply rsuper_inst_deterministic; eauto). subst ca'.
    assert (lc' = lc) by (eapply oview_deterministic; eauto). subst lc'.
    split; assumption.
  - subst qo.
    assert (Hfull : rsuper_inst CT (qr2q qr) C Rs D0 Vs) by (eapply rsi_step; eauto).
    pose proof (lookup_lref_boundsp CT qr c wf m0 C Rs D0 Vs Hct Hcl Hfull Hrt
                  Ao HeA _ _ _ _ _ _ _ _ _ Hf' Hf Hs' Hs Hl' Hl Hrsc lm lk L HN Hlk0 Hb)
      as Hbds.
    pose proof (rsuper_inst_le _ _ _ _ _ _ Hct Hrest) as HleC.
    pose proof Hparent as Hparent'. unfold parent_lookup in Hparent'.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
    destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hparent') as (sd & _ & HltP & _).
    assert (HallP : forall K Vs0 d,
              oview CT qr (olab c) P
                (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss)
                K Vs0 ->
              find_class CT K = Some d -> ofacts CT L qr (olab c) K Vs0 d).
    { intros K Vs0 d Hv Hd. apply (Hall K Vs0 d); auto.
      unfold oview in *. eapply v_step; eauto. }
    assert (HupP : forall d, find_class CT P = Some d ->
              class_qualifier (signature d) = Mut_c ->
              class_qualifier (signature def) = Mut_c).
    { intros d Hd Hq.
      destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hparent')
        as (sd0 & Hsd0 & _ & _ & _ & Hpin & _).
      rewrite Hsd0 in Hd. inversion Hd; subst d.
      destruct Hpin as [Hp | Hp]; congruence. }
    pose proof (base_subtype_le _ _ _ Hct (find_method_with_name_base _ _ _ _ _ Hf))
      as HleD.
    assert (HsD : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs [] []) Ss) D ca).
    { inversion Hs; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    assert (HrtP : wf_rtypeuse CT
                     (mkruntime_type qr P (map (dyn (qr2q qr) Rs [] []) Ss))).
    { eapply rsuper_wf; [exact Hct | | exact Hrt].
      eapply rsi_step; eauto. apply rsi_refl. }
    assert (HeAP : erases (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss)
                     (map (dyn (qr2q qr) Rs [] []) Ss)).
    { unfold erases. rewrite map_erase_hstep_obj. unfold erases in HeA.
      rewrite HeA. reflexivity. }
    assert (HlD : oview CT qr (olab c) P
                       (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss) D lc).
    { inversion Hl; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    inversion Hf'; subst.
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      assert (ca' = Rs).
      { eapply rsuper_inst_deterministic; [exact Hct | exact Hs' | apply rsi_refl]. }
      subst ca'.
      assert (lc' = Ao).
      { eapply oview_deterministic; [exact Hct | exact Hl' | apply v_refl]. }
      subst lc'.
      destruct (find_from_subclass _ _ _ _ _ _ Hrest _ _ _ Hf) as (D1 & mdef1 & HfP).
      destruct (find_rsuper_exists _ _ _ _ _ HfP (qr2q qr)
                  (map (dyn (qr2q qr) Rs [] []) Ss)) as [ca1 Hs1].
      destruct (oview_exists _ _ _ _ _ _ Hs1 qr (olab c) _ eq_refl HeAP)
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
                    HfP Hf Hs1 HsD) as (Hsc & (Hhd & _ & Hmq) & Hma).
      destruct (Hma _ _ (eq_trans (length_map fst lk) Hlk0) Hb) as (Hb1 & Hp & Hr).
      destruct (Hma1 _ _ (eq_trans (eq_trans (length_map fst lk) Hlk0) (eq_sym Hmq)) Hb1) as (_ & _ & Hr1).
      assert (Hrsc1 : readonly_state_method_scope (mscope (msignature mdef1))).
      { destruct Hcompat as (_ & Hscope & _). rewrite <- Hscope. exact Hrsc. }
      assert (Hnb' : nomut_bounds (method_tv_env CT D' (msignature mdef'))).
      { destruct (find_method_In _ _ _ _ _ Hf') as (defD & HfD & Hin).
        eapply Hcl; eauto. }
      assert (HMVb : forall n B,
                nth_error (mtparams (msignature mdef')) n = Some B ->
                lsubt CT L (ldyn (act_frame qr wf m0 Ao lm lk) (TVar TVSub MethodVar n))
                  (ldyn (act_frame qr wf m0 Ao lm lk) B) /\
                fit3p CT L (ldyn (act_frame qr wf m0 Ao lm lk) (TVar TVSub MethodVar n))
                  (ldyn (act_frame qr wf m0 Ao lm lk) B)).
      { intros n B HnB.
        pose proof (Forall2_nth_error_rel _ _ _ n Hbds) as Hrel.
        rewrite HnB in Hrel.
        destruct (nth_error (mtparams (msignature mdef)) n) as [Bt|] eqn:HBt;
          [|contradiction].
        destruct (HMV n Bt HBt) as [HM1 HM2]. split.
        - eapply lsubt_agree_r; [exact HM1 | exact Hrel].
        - eapply fit3p_agree; [exact HM2 | exact Hrel]. }
      assert (Hflv : ffit CT L (method_tv_env CT D' (msignature mdef'))
                       (act_frame qr wf m0 Ao lm lk)).
      { exact (act_ffit CT L qr c wf m0 D' def (msignature mdef') Ao lm lk
                 Hct Hfind Hnb'
                 (Hall D' Ao def (v_refl _ _ _ _ _ _ _) Hfind) HN HMVb). }
      assert (N3P : forall d, find_class CT P = Some d ->
                class_qualifier (signature d) = Mut_c ->
                norm L (olab c) = norm L (LIn wf)).
      { intros d Hd Hq. exact (N3 def eq_refl (HupP d Hd Hq)). }
      assert (Hlf1 : Forall rlost_free ca1).
      { pose proof (rsuper_wf _ _ _ _ _ _ Hct Hs1' Hrt) as Hv1.
        unfold wf_rtypeuse in Hv1. simpl in Hv1.
        destruct (find_class CT D1); [|contradiction].
        destruct Hv1 as (_ & Hlf & _). exact Hlf. }
      assert (Hop : opcoh CT L qr (olab c) D' Ao (olab c)).
      { destruct (Hall D' Ao def (v_refl _ _ _ _ _ _ _) Hfind) as [Hi _].
        assert (Hpn : pclassf CT D' Ao = None).
        { apply pclassf_clean. intros d0 Hd0. rewrite Hfind in Hd0.
          inversion Hd0; subst d0.
          exact (nomut_bounds_clean CT D' _ def Hfind Hnb'). }
        apply opcoh_of_pown; auto.
        intros q' l' Hpx. rewrite Hpn in Hpx. discriminate. }
      destruct (lref_result_stepp CT qr D' Rs _ _ _ D1 ca1 Vs0 Hct Hag Hsi
                  Hcompat Hca1 Hview Hfbf Hrsc Hnb' c Ao lc1 wf m0 lm lk P0 h G L
                  next HeA (v_step CT false (qr2q qr) (fun q0 => q0) (olab c) D' Ao P Ss D1 lc1 Hparent Hl1)
                  HG HwfL N1 HN (N3 def eq_refl) Hop (eq_trans Hlk0 (eq_sym Hmq)) Hb1 Hflv Hlf1 v Hty Hex Hlv)
        as [Hlv1 Hex1].
      exact (IH HrtP _ HeAP _ _ _ _ _ _ _ lc1 lc HfP Hf Hs1 HsD Hl1 HlD
               Hrsc1 lm lk P0 h G L next HG HwfL N1 HN N3P Hlk0 Hb HallP HMV
               v (Hr1 _ _ Hty) Hex1 Hlv1).
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      rewrite Hsuper in Hparent'. inversion Hparent'; subst.
      pose proof (base_subtype_le _ _ _ Hct
                    (find_method_with_name_base _ _ _ _ _ Hparent_fmn)) as HleD'.
      assert (HsD' : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs [] []) Ss) D' ca').
      { inversion Hs'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      assert (HlD' : oview CT qr (olab c) P
                       (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss) D' lc').
      { inversion Hl'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      assert (N3P : forall d, find_class CT P = Some d ->
                class_qualifier (signature d) = Mut_c ->
                norm L (olab c) = norm L (LIn wf)).
      { intros d Hd Hq. exact (N3 def eq_refl (HupP d Hd Hq)). }
      exact (IH HrtP _ HeAP _ _ _ _ _ _ _ lc' lc Hparent_fmn Hf HsD' HsD HlD' HlD
               Hrsc lm lk P0 h G L next HG HwfL N1 HN N3P Hlk0 Hb HallP HMV
               v Hty Hex Hlv).
Qed.

Print Assumptions lookup_lref_paramsp.
Print Assumptions lookup_lref_resultp.

(* ------------------PART 3: A RECEIVER-DEPENDENT DECLARED RECEIVER------------------*)

(** A declared receiver that requalifies a type parameter of its class as
    receiver-dependent, in a readonly-state or transitive-state method.

    Such an argument, on a mutable receiver, is mutable, so its label must be
    the receiver's own.  The caller knows this for the declaration it sees;
    this file carries the fact to the declaration that runs. *)

(* ------------------LISTS------------------*)

Lemma Forall2_nth : forall (A B : Type) (P : A -> B -> Prop) l l',
  Forall2 P l l' ->
  forall i x y, nth_error l i = Some x -> nth_error l' i = Some y -> P x y.
Proof.
  intros A B P l l' H. induction H; intros [|i] a b Ha Hb; simpl in *;
    try discriminate.
  - inversion Ha; inversion Hb; subst. assumption.
  - eauto.
Qed.

Lemma Forall2_map2_nth : forall (A B C D C' D' : Type)
    (P : C -> D -> Prop) (Q : C' -> D' -> Prop)
    (f : A -> C) (g : B -> D) (f0 : A -> C') (g0 : B -> D') l a,
  Forall2 P (map f l) (map g a) ->
  (forall i x y, nth_error l i = Some x -> nth_error a i = Some y ->
     P (f x) (g y) -> Q (f0 x) (g0 y)) ->
  Forall2 Q (map f0 l) (map g0 a).
Proof.
  intros A B C D C' D' P Q f g f0 g0 l. induction l as [|x l IH];
    intros [|y a] H Hp; simpl in H; inversion H; subst; simpl; constructor.
  - apply (Hp 0); auto.
  - apply IH; auto. intros i. apply (Hp (S i)).
Qed.

(* ------------------HEADS------------------*)

Lemma rhead_rrequalify : forall q0 R, rhead (rrequalify q0 R) = q0.
Proof. intros q0 [q1 C a]. reflexivity. Qed.

Lemma rarg_sub_requalify_iff : forall R q0,
  rarg_sub R (rrequalify q0 R) <-> arg_q_sub (rhead R) q0.
Proof.
  intros [q1 C a] q0. simpl. split.
  - intros H. inversion H; subst. assumption.
  - intros H. apply ras_class; [exact H | apply Forall2_rarg_sub_refl].
Qed.

(** A mutable qualifier argument forgotten to [Lost]. *)
Definition unmq (q0 : q) : q := match q0 with Mut => Lost | _ => q0 end.

Lemma qnth_map_unmq : forall ka n, qnth (map unmq ka) n = unmq (qnth ka n).
Proof.
  intros ka n. unfold qnth. change RO with (unmq RO) at 1. apply map_nth.
Qed.

Lemma arg_q_sub_unmq : forall h x, arg_q_sub h x -> arg_q_sub h (unmq x).
Proof.
  intros h x [-> | [-> H]]; unfold arg_q_sub.
  - destruct h; simpl; auto.
  - simpl. auto.
Qed.

Lemma arg_q_sub_unmq_imm : forall x, arg_q_sub Mut x -> arg_q_sub Imm (unmq x).
Proof.
  intros x [-> | [-> _]]; unfold arg_q_sub; simpl; auto.
Qed.

Lemma plain_dec : forall (T : qualified_type) j,
  {T = TVar TVSub ClassVar j} + {T <> TVar TVSub ClassVar j}.
Proof.
  intros [q0 C a | [|q0|mp] [|] n | n C a] j; try (right; discriminate).
  destruct (Nat.eq_dec n j) as [-> | Hne]; [left; reflexivity|].
  right. intros H. inversion H. contradiction.
Qed.

(** The head of a resolved type does not depend on a class argument that the
    type is not a plain use of. *)
Lemma dyn_head_other : forall qctx ca ca0 ma ka j T,
  (forall k, k <> j -> nth_error ca0 k = nth_error ca k) ->
  T <> TVar TVSub ClassVar j ->
  rhead (dyn qctx ca0 ma ka T) = rhead (dyn qctx ca ma ka T).
Proof.
  intros qctx ca ca0 ma ka j T Hk HT.
  destruct T as [q0 C a | u o n | n C a]; simpl; try reflexivity.
  destruct u as [|q0|mp].
  - destruct o; simpl; [|reflexivity].
    assert (Hn : n <> j) by (intros ->; apply HT; reflexivity).
    rewrite (Hk n Hn). reflexivity.
  - rewrite !rhead_rrequalify. reflexivity.
  - rewrite !rhead_rrequalify. reflexivity.
Qed.

(* ------------------WHERE A RECEIVER-DEPENDENT ARGUMENT COMES FROM------------------*)

Definition is_src (j : nat) (V a : qualified_type) : bool :=
  match V, a with
  | TVar TVSub ClassVar k, TVar (TVQual RDM) ClassVar _ => Nat.eqb k j
  | _, _ => false
  end.

Lemma is_src_true : forall j V a,
  is_src j V a = true ->
  V = TVar TVSub ClassVar j /\ exists i, a = TVar (TVQual RDM) ClassVar i.
Proof.
  intros j V a H.
  destruct V as [q0 C l | u o k | n C l]; simpl in H; try discriminate.
  destruct u; try discriminate. destruct o; try discriminate.
  destruct a as [q1 C1 l1 | u1 o1 i | n1 C1 l1]; try discriminate.
  destruct u1 as [|q1|mp]; try discriminate.
  destruct q1; try discriminate. destruct o1; try discriminate.
  apply Nat.eqb_eq in H. subst. eauto.
Qed.

Lemma find_src : forall j Vs args1,
  (exists i V a, nth_error Vs i = Some V /\ nth_error args1 i = Some a /\
                 is_src j V a = true) \/
  (forall i V a, nth_error Vs i = Some V -> nth_error args1 i = Some a ->
                 is_src j V a = false).
Proof.
  intros j Vs. induction Vs as [|V Vs IH]; intros args1.
  - right. intros [|i] V a H; discriminate.
  - destruct args1 as [|a args1].
    + right. intros [|i] V0 a0 _ H; discriminate.
    + destruct (is_src j V a) eqn:E.
      * left. exists 0, V, a. auto.
      * destruct (IH args1) as [(i & V0 & a0 & H1 & H2 & H3) | Hnone].
        -- left. exists (S i), V0, a0. auto.
        -- right. intros [|i] V0 a0 H1 H2; simpl in *.
           ++ inversion H1; inversion H2; subst. exact E.
           ++ eauto.
Qed.

(** If an override requalifies its class's [j]-th parameter as
    receiver-dependent, and accepts every object the overridden receiver
    accepts, then the overridden receiver requalifies as receiver-dependent a
    parameter that receives the [j]-th parameter unchanged.  The overridden
    receiver requalifies nothing as mutable. *)
Lemma recv_rdm_source : forall n n1 Vs args1 args' ca ka j Cj aj R1 R',
  targs R1 = args1 -> targs R' = args' ->
  recv_args n1 args1 -> recv_args n args' ->
  length Vs = n1 -> length ca = n ->
  (forall i u, nth_error args1 i = Some (TVar (TVQual u) ClassVar i) -> u <> Mut) ->
  (forall ka0 ca0, length ka0 = length ka -> length ca0 = n ->
     radmit Mut (map (dyn Mut ca0 [] []) Vs) ka0 R1 -> radmit Mut ca0 ka0 R') ->
  radmit Mut (map (dyn Mut ca [] []) Vs) ka R1 ->
  nth_error args' j = Some (TVar (TVQual RDM) ClassVar j) ->
  nth_error ca j = Some (RClass Mut Cj aj) ->
  exists i, nth_error Vs i = Some (TVar TVSub ClassVar j) /\
            nth_error args1 i = Some (TVar (TVQual RDM) ClassVar i).
Proof.
  intros n n1 Vs args1 args' ca ka j Cj aj R1 R' Hta1 Hta' [Hl1 Hsh1] [Hl' Hsh']
    HlV Hlca Hnomut Hadm Hact Hj Hcaj.
  destruct (find_src j Vs args1) as [(i & V & a & HV & Ha & Hs) | Hnone].
  { destruct (is_src_true _ _ _ Hs) as [-> [i' ->]].
    destruct (Hsh1 i _ Ha) as [u E]. inversion E; subst. eauto. }
  exfalso.
  set (ca0 := update j (RClass Imm Cj aj) ca).
  assert (Hjlt : j < length ca).
  { apply nth_error_Some. rewrite Hcaj. discriminate. }
  assert (Hca0j : nth_error ca0 j = Some (RClass Imm Cj aj)).
  { unfold ca0. apply update_same. exact Hjlt. }
  assert (Hca0k : forall k, k <> j -> nth_error ca0 k = nth_error ca k).
  { intros k Hk. unfold ca0. apply update_diff. auto. }
  assert (H0 : radmit Mut (map (dyn Mut ca0 [] []) Vs) (map unmq ka) R1).
  { intros ma. rewrite Hta1. specialize (Hact ma). rewrite Hta1 in Hact.
    eapply Forall2_map2_nth; [exact Hact|].
    intros i V a HV Ha Hrel.
    destruct (Hsh1 i a Ha) as [u ->].
    destruct u as [|u|mu].
    - simpl. rewrite nth_error_map. rewrite HV. simpl. apply rarg_sub_refl.
    - simpl in Hrel. rewrite nth_error_map in Hrel. rewrite HV in Hrel.
      simpl in Hrel. apply rarg_sub_requalify_iff in Hrel.
      simpl. rewrite nth_error_map. rewrite HV. simpl.
      apply rarg_sub_requalify_iff.
      destruct (plain_dec V j) as [-> | Hne].
      + pose proof (Hnone i _ _ HV Ha) as Hf. simpl in Hf.
        rewrite Nat.eqb_refl in Hf.
        assert (Hu : u <> Mut) by (eapply Hnomut; eauto).
        simpl. rewrite Hca0j. simpl.
        simpl in Hrel. rewrite Hcaj in Hrel. simpl in Hrel.
        destruct u; simpl in *; try discriminate; try congruence;
          destruct Hrel as [Hx | [Hx _]]; try discriminate.
        right. split; auto.
      + rewrite (dyn_head_other Mut ca ca0 [] [] j V Hca0k Hne). exact Hrel.
    - (* under a qualifier parameter: with every mutable qualifier argument
         forgotten, the changed argument is still admitted *)
      simpl in Hrel. rewrite nth_error_map in Hrel. rewrite HV in Hrel.
      simpl in Hrel. apply rarg_sub_requalify_iff in Hrel.
      simpl. rewrite nth_error_map. rewrite HV. simpl.
      apply rarg_sub_requalify_iff. rewrite qnth_map_unmq.
      destruct (plain_dec V j) as [-> | Hne].
      + simpl. rewrite Hca0j. simpl.
        simpl in Hrel. rewrite Hcaj in Hrel. simpl in Hrel.
        apply arg_q_sub_unmq_imm. exact Hrel.
      + rewrite (dyn_head_other Mut ca ca0 [] [] j V Hca0k Hne).
        apply arg_q_sub_unmq. exact Hrel. }
  assert (Hl0 : length ca0 = n).
  { unfold ca0. rewrite update_length. exact Hlca. }
  pose proof (Hadm (map unmq ka) ca0 (length_map _ _) Hl0 H0 []) as H'.
  rewrite Hta' in H'.
  assert (Hy : nth_error (map (dyn Mut ca0 [] (map unmq ka)) args') j =
               Some (RClass Mut Cj aj)).
  { rewrite nth_error_map. rewrite Hj. simpl. rewrite Hca0j. reflexivity. }
  pose proof (Forall2_nth _ _ _ _ _ H' j _ _ Hca0j Hy) as Hr.
  inversion Hr; subst. destruct Hq as [Hq | [Hq _]]; discriminate.
Qed.

(* ------------------A RECEIVER ARGUMENT UNDER A QUALIFIER PARAMETER------------------*)

Lemma find_pair : forall (f : qualified_type -> qualified_type -> bool) Vs args1,
  (exists i V a, nth_error Vs i = Some V /\ nth_error args1 i = Some a /\
                 f V a = true) \/
  (forall i V a, nth_error Vs i = Some V -> nth_error args1 i = Some a ->
                 f V a = false).
Proof.
  intros f Vs. induction Vs as [|V Vs IH]; intros args1.
  - right. intros [|i] V a H; discriminate.
  - destruct args1 as [|a args1].
    + right. intros [|i] V0 a0 _ H; discriminate.
    + destruct (f V a) eqn:E.
      * left. exists 0, V, a. auto.
      * destruct (IH args1) as [(i & V0 & a0 & H1 & H2 & H3) | Hnone].
        -- left. exists (S i), V0, a0. auto.
        -- right. intros [|i] V0 a0 H1 H2; simpl in *.
           ++ inversion H1; inversion H2; subst. exact E.
           ++ eauto.
Qed.

(** The overridden receiver writes, under the qualifier parameter [m], a
    parameter that receives the overriding class's [j]-th parameter
    unchanged. *)
Definition is_psrc (m j : nat) (V a : qualified_type) : bool :=
  match V, a with
  | TVar TVSub ClassVar k, TVar (TVPoly m') _ _ => Nat.eqb k j && Nat.eqb m' m
  | _, _ => false
  end.

Lemma is_psrc_true : forall m j V a,
  is_psrc m j V a = true ->
  V = TVar TVSub ClassVar j /\ exists o i, a = TVar (TVPoly m) o i.
Proof.
  intros m j V a H.
  destruct V as [q0 C l | u o k | n C l]; simpl in H; try discriminate.
  destruct u; try discriminate. destruct o; try discriminate.
  destruct a as [q1 C1 l1 | u1 o1 i | n1 C1 l1]; try discriminate.
  destruct u1 as [|q1|m1]; try discriminate.
  apply andb_true_iff in H. destruct H as [H1 H2].
  apply Nat.eqb_eq in H1. apply Nat.eqb_eq in H2. subst. eauto.
Qed.

(** The overridden receiver writes such a parameter with a qualifier that is
    mutable on this object. *)
Definition is_qsrc (qr : q) (j : nat) (V a : qualified_type) : bool :=
  match V, a with
  | TVar TVSub ClassVar k, TVar (TVQual u) _ _ =>
      if q_eq_dec (dynq qr u) Mut then Nat.eqb k j else false
  | _, _ => false
  end.

Lemma is_qsrc_true : forall qr j V a,
  is_qsrc qr j V a = true ->
  V = TVar TVSub ClassVar j /\ exists u o i, a = TVar (TVQual u) o i /\ dynq qr u = Mut.
Proof.
  intros qr j V a H.
  destruct V as [q0 C l | u o k | n C l]; simpl in H; try discriminate.
  destruct u; try discriminate. destruct o; try discriminate.
  destruct a as [q1 C1 l1 | u1 o1 i | n1 C1 l1]; try discriminate.
  destruct u1 as [|q1|m1]; try discriminate.
  destruct (q_eq_dec (dynq qr q1) Mut) as [E|]; [|discriminate].
  apply Nat.eqb_eq in H. subst. eauto 6.
Qed.

Lemma qnth_nth_error : forall l n,
  qnth l n = match nth_error l n with Some x => x | None => RO end.
Proof.
  unfold qnth. induction l as [|x l IH]; intros [|n]; simpl; auto.
Qed.

Lemma qnth_lt : forall l n, qnth l n <> RO -> n < length l.
Proof.
  intros l n H. rewrite qnth_nth_error in H.
  destruct (nth_error l n) eqn:E; [|congruence].
  apply nth_error_Some. congruence.
Qed.

Lemma qnth_update_same : forall l n v, n < length l -> qnth (update n v l) n = v.
Proof.
  intros l n v H. rewrite qnth_nth_error. rewrite update_same; auto.
Qed.

Lemma qnth_update_diff : forall l n k v, n <> k -> qnth (update n v l) k = qnth l k.
Proof.
  intros l n k v H. rewrite !qnth_nth_error. rewrite update_diff; auto.
Qed.

(** If an override writes its class's [j]-th parameter under a qualifier
    parameter, the stored argument is mutable and the call supplies a mutable
    qualifier for that parameter, then the overridden receiver constrains the
    same stored argument: under the same qualifier parameter, or with a
    written qualifier that is mutable on this object. *)
Lemma recv_poly_source : forall qr n n1 Vs args1 args' ca ka j m Cj aj R1 R',
  targs R1 = args1 -> targs R' = args' ->
  recv_args n1 args1 -> recv_args n args' ->
  length Vs = n1 -> length ca = n ->
  (forall ka0 ca0, length ka0 = length ka -> length ca0 = n ->
     radmit qr (map (dyn qr ca0 [] []) Vs) ka0 R1 -> radmit qr ca0 ka0 R') ->
  radmit qr (map (dyn qr ca [] []) Vs) ka R1 ->
  nth_error args' j = Some (TVar (TVPoly m) ClassVar j) ->
  nth_error ca j = Some (RClass Mut Cj aj) ->
  qnth ka m = Mut ->
  (exists i, nth_error Vs i = Some (TVar TVSub ClassVar j) /\
             nth_error args1 i = Some (TVar (TVPoly m) ClassVar i)) \/
  (exists i u, nth_error Vs i = Some (TVar TVSub ClassVar j) /\
               nth_error args1 i = Some (TVar (TVQual u) ClassVar i) /\
               dynq qr u = Mut).
Proof.
  intros qr n n1 Vs args1 args' ca ka j m Cj aj R1 R' Hta1 Hta' [Hl1 Hsh1] [Hl' Hsh']
    HlV Hlca Hadm Hact Hj Hcaj Hkm.
  destruct (find_pair (is_psrc m j) Vs args1) as [(i & V & a & HV & Ha & Hs) | Hnp].
  { left. destruct (is_psrc_true _ _ _ _ Hs) as [-> (o & i' & ->)].
    destruct (Hsh1 i _ Ha) as [u E]. inversion E; subst. eauto. }
  destruct (find_pair (is_qsrc qr j) Vs args1) as [(i & V & a & HV & Ha & Hs) | Hnq].
  { right. destruct (is_qsrc_true _ _ _ _ Hs) as [-> (u0 & o & i' & -> & Hd)].
    destruct (Hsh1 i _ Ha) as [u E]. inversion E; subst. eauto. }
  exfalso.
  set (ca0 := update j (RClass Imm Cj aj) ca).
  set (ka0 := update m Mut (map unmq ka)).
  assert (Hjlt : j < length ca).
  { apply nth_error_Some. rewrite Hcaj. discriminate. }
  assert (Hca0j : nth_error ca0 j = Some (RClass Imm Cj aj)).
  { unfold ca0. apply update_same. exact Hjlt. }
  assert (Hca0k : forall k, k <> j -> nth_error ca0 k = nth_error ca k).
  { intros k Hk. unfold ca0. apply update_diff. auto. }
  assert (Hmlt : m < length (map unmq ka)).
  { rewrite length_map. apply qnth_lt. rewrite Hkm. discriminate. }
  assert (Hk0m : qnth ka0 m = Mut).
  { unfold ka0. apply qnth_update_same. exact Hmlt. }
  assert (Hk0k : forall k, k <> m -> qnth ka0 k = unmq (qnth ka k)).
  { intros k Hk. unfold ka0. rewrite qnth_update_diff; auto. apply qnth_map_unmq. }
  assert (H0 : radmit qr (map (dyn qr ca0 [] []) Vs) ka0 R1).
  { intros ma. rewrite Hta1. specialize (Hact ma). rewrite Hta1 in Hact.
    eapply Forall2_map2_nth; [exact Hact|].
    intros i V a HV Ha Hrel.
    destruct (Hsh1 i a Ha) as [u ->].
    destruct u as [|u|mu].
    - simpl. rewrite nth_error_map. rewrite HV. simpl. apply rarg_sub_refl.
    - simpl in Hrel. rewrite nth_error_map in Hrel. rewrite HV in Hrel.
      simpl in Hrel. apply rarg_sub_requalify_iff in Hrel.
      simpl. rewrite nth_error_map. rewrite HV. simpl.
      apply rarg_sub_requalify_iff.
      destruct (plain_dec V j) as [-> | Hne].
      + pose proof (Hnq i _ _ HV Ha) as Hf. simpl in Hf.
        destruct (q_eq_dec (dynq qr u) Mut) as [E | Hnm].
        { rewrite Nat.eqb_refl in Hf. discriminate. }
        simpl. rewrite Hca0j. simpl.
        simpl in Hrel. rewrite Hcaj in Hrel. simpl in Hrel.
        destruct Hrel as [Hx | [Hx _]]; [congruence|].
        rewrite Hx. right. split; auto.
      + rewrite (dyn_head_other qr ca ca0 [] [] j V Hca0k Hne). exact Hrel.
    - simpl in Hrel. rewrite nth_error_map in Hrel. rewrite HV in Hrel.
      simpl in Hrel. apply rarg_sub_requalify_iff in Hrel.
      simpl. rewrite nth_error_map. rewrite HV. simpl.
      apply rarg_sub_requalify_iff.
      destruct (Nat.eq_dec mu m) as [-> | Hmu].
      + rewrite Hk0m. rewrite Hkm in Hrel.
        destruct (plain_dec V j) as [-> | Hne].
        * pose proof (Hnp i _ _ HV Ha) as Hf. simpl in Hf.
          rewrite !Nat.eqb_refl in Hf. discriminate.
        * rewrite (dyn_head_other qr ca ca0 [] [] j V Hca0k Hne). exact Hrel.
      + rewrite (Hk0k mu Hmu).
        destruct (plain_dec V j) as [-> | Hne].
        * simpl. rewrite Hca0j. simpl.
          simpl in Hrel. rewrite Hcaj in Hrel. simpl in Hrel.
          apply arg_q_sub_unmq_imm. exact Hrel.
        * rewrite (dyn_head_other qr ca ca0 [] [] j V Hca0k Hne).
          apply arg_q_sub_unmq. exact Hrel. }
  assert (Hl0 : length ca0 = n).
  { unfold ca0. rewrite update_length. exact Hlca. }
  assert (Hlk0 : length ka0 = length ka).
  { unfold ka0. rewrite update_length. apply length_map. }
  pose proof (Hadm ka0 ca0 Hlk0 Hl0 H0 []) as H'. rewrite Hta' in H'.
  assert (Hy : nth_error (map (dyn qr ca0 [] ka0) args') j =
               Some (RClass (qnth ka0 m) Cj aj)).
  { rewrite nth_error_map. rewrite Hj. simpl. rewrite Hca0j. reflexivity. }
  pose proof (Forall2_nth _ _ _ _ _ H' j _ _ Hca0j Hy) as Hr.
  rewrite Hk0m in Hr.
  inversion Hr; subst. destruct Hq as [Hq | [Hq _]]; discriminate.
Qed.

Lemma existsb_combine_nth : forall (A B : Type) (f : A -> B -> bool) l l',
  existsb (fun p => f (fst p) (snd p)) (combine l l') = true <->
  exists i x y, nth_error l i = Some x /\ nth_error l' i = Some y /\ f x y = true.
Proof.
  intros A B f l. induction l as [|x l IH]; intros l'; simpl.
  - split; [discriminate | intros ([|i] & a & b & H & _); discriminate].
  - destruct l' as [|y l']; simpl.
    + split; [discriminate | intros ([|i] & a & b & _ & H & _); discriminate].
    + rewrite orb_true_iff. rewrite IH. split.
      * intros [H | (i & a & b & H1 & H2 & H3)].
        -- exists 0, x, y. repeat split; auto.
        -- exists (S i), a, b. repeat split; auto.
      * intros ([|i] & a & b & H1 & H2 & H3); simpl in *.
        -- inversion H1; inversion H2; subst. left. exact H3.
        -- right. exists i, a, b. repeat split; auto.
Qed.

(** Replace by [Imm] the head of every argument selected by [F]. *)
Fixpoint flip_from (F : nat -> bool) (k : nat) (ca : list rtype) : list rtype :=
  match ca with
  | [] => []
  | r :: ca' => (if F k then rrequalify Imm r else r) :: flip_from F (S k) ca'
  end.

Lemma nth_error_flip_from : forall F ca k i,
  nth_error (flip_from F k ca) i =
  option_map (fun r => if F (k + i) then rrequalify Imm r else r) (nth_error ca i).
Proof.
  intros F ca. induction ca as [|r ca IH]; intros k [|i]; simpl; auto.
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IH. rewrite Nat.add_succ_r. reflexivity.
Qed.

Lemma length_flip_from : forall F ca k, length (flip_from F k ca) = length ca.
Proof. intros F ca. induction ca; intros k; simpl; auto. Qed.

Lemma plainvar_dec : forall T : qualified_type,
  {k | T = TVar TVSub ClassVar k} + {forall k, T <> TVar TVSub ClassVar k}.
Proof.
  intros [q0 C a | [|q0|mp] [|] n | n C a]; try (right; intros k; discriminate).
  left. exists n. reflexivity.
Qed.

(** The head of a resolved type that is not a plain use of a class parameter
    does not depend on the heads of the class arguments. *)
Lemma dyn_head_nonplain : forall qctx F ca ma ka T,
  (forall k, T <> TVar TVSub ClassVar k) ->
  rhead (dyn qctx (flip_from F 0 ca) ma ka T) = rhead (dyn qctx ca ma ka T).
Proof.
  intros qctx F ca ma ka T HT.
  destruct T as [q0 C a | u o n | n C a]; simpl; try reflexivity.
  destruct u as [|q0|mp].
  - destruct o; simpl; [|reflexivity]. exfalso. exact (HT n eq_refl).
  - rewrite !rhead_rrequalify. reflexivity.
  - rewrite !rhead_rrequalify. reflexivity.
Qed.

(** The same situation when the overridden receiver has no such argument
    under the same qualifier parameter.  Then it puts, under that parameter,
    an argument whose head is fixed as mutable: one that is not a plain
    parameter of the overriding class, or a parameter that it also writes
    with a qualifier that is mutable on this object. *)
Lemma recv_poly_pinned : forall qr n n1 Vs args1 args' ca ka j m Cj aj R1 R',
  targs R1 = args1 -> targs R' = args' ->
  recv_args n1 args1 -> recv_args n args' ->
  length Vs = n1 -> length ca = n ->
  (forall ka0 ca0, length ka0 = length ka -> length ca0 = n ->
     radmit qr (map (dyn qr ca0 [] []) Vs) ka0 R1 -> radmit qr ca0 ka0 R') ->
  radmit qr (map (dyn qr ca [] []) Vs) ka R1 ->
  nth_error args' j = Some (TVar (TVPoly m) ClassVar j) ->
  nth_error ca j = Some (RClass Mut Cj aj) ->
  qnth ka m = Mut ->
  (forall i, nth_error Vs i = Some (TVar TVSub ClassVar j) ->
             nth_error args1 i <> Some (TVar (TVPoly m) ClassVar i)) ->
  exists i V, nth_error args1 i = Some (TVar (TVPoly m) ClassVar i) /\
    nth_error Vs i = Some V /\
    (((forall k, V <> TVar TVSub ClassVar k) /\ rhead (dyn qr ca [] [] V) = Mut) \/
     (exists j2 i2 u, V = TVar TVSub ClassVar j2 /\
        nth_error Vs i2 = Some (TVar TVSub ClassVar j2) /\
        nth_error args1 i2 = Some (TVar (TVQual u) ClassVar i2) /\
        dynq qr u = Mut)).
Proof.
  intros qr n n1 Vs args1 args' ca ka j m Cj aj R1 R' Hta1 Hta' [Hl1 Hsh1] [Hl' Hsh']
    HlV Hlca Hadm Hact Hj Hcaj Hkm Hnosrc.
  set (qsrcb := fun j2 =>
         existsb (fun p => is_qsrc qr j2 (fst p) (snd p)) (combine Vs args1)).
  set (bad := fun V a =>
         match a with
         | TVar (TVPoly m') _ _ =>
             Nat.eqb m' m &&
             match plainvar_dec V with
             | inleft (exist _ j2 _) => qsrcb j2
             | inright _ =>
                 if q_eq_dec (rhead (dyn qr ca [] [] V)) Mut then true else false
             end
         | _ => false
         end).
  destruct (find_pair bad Vs args1) as [(i & V & a & HV & Ha & Hb) | Hnone].
  { destruct (Hsh1 i a Ha) as [u ->].
    destruct u as [|u|mu]; unfold bad in Hb; simpl in Hb; try discriminate.
    apply andb_true_iff in Hb. destruct Hb as [Hm Hb].
    apply Nat.eqb_eq in Hm. subst mu.
    exists i, V. split; [exact Ha|]. split; [exact HV|].
    destruct (plainvar_dec V) as [[j2 ->] | Hnp].
    - right. unfold qsrcb in Hb. apply existsb_combine_nth in Hb.
      destruct Hb as (i2 & V2 & a2 & H1 & H2 & H3).
      destruct (is_qsrc_true _ _ _ _ H3) as [-> (u0 & o & i' & -> & Hd)].
      destruct (Hsh1 i2 _ H2) as [u E]. inversion E; subst.
      exists j2, i2, u0. auto.
    - left. split; [exact Hnp|].
      destruct (q_eq_dec (rhead (dyn qr ca [] [] V)) Mut); [assumption | discriminate]. }
  exfalso.
  set (F := fun j2 =>
         existsb (fun p => is_psrc m j2 (fst p) (snd p)) (combine Vs args1)).
  set (ca0 := flip_from F 0 ca).
  set (ka0 := update m Imm (map unmq ka)).
  assert (HFsrc : forall j2, F j2 = true ->
            exists i', nth_error Vs i' = Some (TVar TVSub ClassVar j2) /\
                       nth_error args1 i' = Some (TVar (TVPoly m) ClassVar i')).
  { intros j2 HF. unfold F in HF. apply existsb_combine_nth in HF.
    destruct HF as (i' & V' & a' & H1 & H2 & H3).
    destruct (is_psrc_true _ _ _ _ H3) as [-> (o & k & ->)].
    destruct (Hsh1 i' _ H2) as [u E]. inversion E; subst. eauto. }
  assert (HFmut : forall j2, F j2 = true ->
            rhead (dyn qr ca [] [] (TVar TVSub ClassVar j2)) = Mut).
  { intros j2 HF. destruct (HFsrc j2 HF) as (i' & HV' & Ha').
    pose proof (Hact []) as Ha0. rewrite Hta1 in Ha0.
    assert (Hx : nth_error (map (dyn qr ca [] []) Vs) i' =
                 Some (dyn qr ca [] [] (TVar TVSub ClassVar j2))).
    { rewrite nth_error_map. rewrite HV'. reflexivity. }
    assert (Hy : nth_error (map (dyn qr (map (dyn qr ca [] []) Vs) [] ka) args1) i' =
                 Some (rrequalify (qnth ka m)
                         (dyn qr ca [] [] (TVar TVSub ClassVar j2)))).
    { rewrite nth_error_map. rewrite Ha'. simpl. rewrite nth_error_map.
      rewrite HV'. reflexivity. }
    pose proof (Forall2_nth _ _ _ _ _ Ha0 i' _ _ Hx Hy) as Hr.
    apply rarg_sub_requalify_iff in Hr. rewrite Hkm in Hr.
    destruct Hr as [Hr | [Hr _]]; [symmetry; exact Hr | discriminate]. }
  assert (HnF : F j = false).
  { destruct (F j) eqn:E; auto. destruct (HFsrc j E) as (i' & H1 & H2).
    exfalso. exact (Hnosrc i' H1 H2). }
  assert (Hca0 : forall k, nth_error ca0 k =
            option_map (fun r => if F k then rrequalify Imm r else r) (nth_error ca k)).
  { intros k. unfold ca0. rewrite nth_error_flip_from. reflexivity. }
  assert (Hflip : forall j2, F j2 = true ->
            rhead (dyn qr ca0 [] [] (TVar TVSub ClassVar j2)) = Imm).
  { intros j2 HF. pose proof (HFmut j2 HF) as Hm. simpl in Hm. simpl.
    rewrite (Hca0 j2). destruct (nth_error ca j2) as [r|]; simpl.
    - rewrite HF. apply rhead_rrequalify.
    - simpl in Hm. discriminate. }
  assert (Hkeep : forall j2, F j2 = false ->
            rhead (dyn qr ca0 [] [] (TVar TVSub ClassVar j2)) =
            rhead (dyn qr ca [] [] (TVar TVSub ClassVar j2))).
  { intros j2 HF. simpl. rewrite (Hca0 j2).
    destruct (nth_error ca j2) as [r|]; simpl; [rewrite HF|]; reflexivity. }
  assert (Hmlt : m < length (map unmq ka)).
  { rewrite length_map. apply qnth_lt. rewrite Hkm. discriminate. }
  assert (Hk0m : qnth ka0 m = Imm).
  { unfold ka0. apply qnth_update_same. exact Hmlt. }
  assert (Hk0k : forall k, k <> m -> qnth ka0 k = unmq (qnth ka k)).
  { intros k Hk. unfold ka0. rewrite qnth_update_diff; auto. apply qnth_map_unmq. }
  assert (H0 : radmit qr (map (dyn qr ca0 [] []) Vs) ka0 R1).
  { intros ma. rewrite Hta1. specialize (Hact ma). rewrite Hta1 in Hact.
    eapply Forall2_map2_nth; [exact Hact|].
    intros i V a HV Ha Hrel.
    destruct (Hsh1 i a Ha) as [u ->].
    destruct u as [|u|mu].
    - simpl. rewrite nth_error_map. rewrite HV. simpl. apply rarg_sub_refl.
    - simpl in Hrel. rewrite nth_error_map in Hrel. rewrite HV in Hrel.
      simpl in Hrel. apply rarg_sub_requalify_iff in Hrel.
      simpl. rewrite nth_error_map. rewrite HV. simpl.
      apply rarg_sub_requalify_iff.
      destruct (plainvar_dec V) as [[j2 ->] | Hnp].
      + destruct (F j2) eqn:EF.
        * rewrite (Hflip j2 EF). rewrite (HFmut j2 EF) in Hrel.
          destruct Hrel as [Hx | [Hx _]].
          -- exfalso. destruct (HFsrc j2 EF) as (i' & HV' & Ha').
             pose proof (Hnone i' _ _ HV' Ha') as Hb. unfold bad in Hb. simpl in Hb.
             rewrite Nat.eqb_refl in Hb. simpl in Hb.
             destruct (plainvar_dec (TVar TVSub ClassVar j2)) as [[k E] | Hn];
               [|exact (Hn j2 eq_refl)].
             inversion E; subst k.
             assert (Hq : qsrcb j2 = true).
             { unfold qsrcb. apply existsb_combine_nth.
               exists i, (TVar TVSub ClassVar j2), (TVar (TVQual u) ClassVar i).
               repeat split; auto. simpl.
               destruct (q_eq_dec (dynq qr u) Mut); [apply Nat.eqb_refl | congruence]. }
             congruence.
          -- rewrite Hx. right. split; auto.
        * rewrite (Hkeep j2 EF). exact Hrel.
      + unfold ca0. rewrite dyn_head_nonplain; auto.
    - simpl in Hrel. rewrite nth_error_map in Hrel. rewrite HV in Hrel.
      simpl in Hrel. apply rarg_sub_requalify_iff in Hrel.
      simpl. rewrite nth_error_map. rewrite HV. simpl.
      apply rarg_sub_requalify_iff.
      destruct (Nat.eq_dec mu m) as [-> | Hmu].
      + rewrite Hk0m. rewrite Hkm in Hrel.
        destruct (plainvar_dec V) as [[j2 ->] | Hnp].
        * assert (EF : F j2 = true).
          { unfold F. apply existsb_combine_nth.
            exists i, (TVar TVSub ClassVar j2), (TVar (TVPoly m) ClassVar i).
            repeat split; auto. simpl. rewrite !Nat.eqb_refl. reflexivity. }
          rewrite (Hflip j2 EF). left. reflexivity.
        * exfalso. pose proof (Hnone i _ _ HV Ha) as Hb. unfold bad in Hb. simpl in Hb.
          rewrite Nat.eqb_refl in Hb. simpl in Hb.
          destruct (plainvar_dec V) as [[k E] | _]; [exact (Hnp k E)|].
          destruct (q_eq_dec (rhead (dyn qr ca [] [] V)) Mut) as [|Hne];
            [discriminate|].
          apply Hne. destruct Hrel as [Hx | [Hx _]]; [symmetry; exact Hx | discriminate].
      + rewrite (Hk0k mu Hmu).
        destruct (plainvar_dec V) as [[j2 ->] | Hnp].
        * destruct (F j2) eqn:EF.
          -- rewrite (Hflip j2 EF). rewrite (HFmut j2 EF) in Hrel.
             apply arg_q_sub_unmq_imm. exact Hrel.
          -- rewrite (Hkeep j2 EF). apply arg_q_sub_unmq. exact Hrel.
        * unfold ca0. rewrite dyn_head_nonplain; auto.
          apply arg_q_sub_unmq. exact Hrel. }
  assert (Hl0 : length ca0 = n).
  { unfold ca0. rewrite length_flip_from. exact Hlca. }
  assert (Hlk0 : length ka0 = length ka).
  { unfold ka0. rewrite update_length. apply length_map. }
  pose proof (Hadm ka0 ca0 Hlk0 Hl0 H0 []) as H'. rewrite Hta' in H'.
  assert (Hca0j : nth_error ca0 j = Some (RClass Mut Cj aj)).
  { rewrite Hca0. rewrite Hcaj. simpl. rewrite HnF. reflexivity. }
  assert (Hy : nth_error (map (dyn qr ca0 [] ka0) args') j =
               Some (RClass (qnth ka0 m) Cj aj)).
  { rewrite nth_error_map. rewrite Hj. simpl. rewrite Hca0j. reflexivity. }
  pose proof (Forall2_nth _ _ _ _ _ H' j _ _ Hca0j Hy) as Hr.
  rewrite Hk0m in Hr.
  inversion Hr; subst. destruct Hq as [Hq | [Hq _]]; discriminate.
Qed.

(* ------------------THE VIEW OF A PLAIN PARAMETER------------------*)

Lemma subst_adapt_plain : forall mt qh Ts S j,
  subst Ts [] [] (adapt mt qh S) = TVar TVSub ClassVar j ->
  exists m, S = TVar TVSub ClassVar m /\
            nth_error Ts m = Some (TVar TVSub ClassVar j).
Proof.
  intros mt qh Ts S j H.
  destruct S as [q0 C a | u o n | n C a]; unfold adapt in H; simpl in H;
    try discriminate.
  - destruct u as [|q0|mp]; simpl in H.
    + destruct o; simpl in H.
      * destruct (nth_error Ts n) as [U|] eqn:E; [|discriminate].
        subst U. eauto.
      * destruct n; discriminate.
    + destruct (match tv_lookup o Ts [] n with
                | Some U => U | None => default_type end); discriminate.
    + replace (nth_error (@nil qarg) mp) with (@None qarg) in H
        by (destruct mp; reflexivity).
      simpl in H.
      destruct (match tv_lookup o Ts [] n with
                | Some U => U | None => default_type end); discriminate.
  - destruct n; discriminate.
Qed.

(** A superclass parameter that receives a parameter of the subclass
    unchanged has, in every labelled view, that parameter's argument. *)
Lemma view_plain_var : forall CT mt qh C Ts D Vs,
  wf_class_table CT ->
  super_inst CT mt qh C Ts D Vs ->
  forall k hq g d As A0 lcD,
    view CT k hq g d C As D lcD ->
    (forall i j, nth_error Ts i = Some (TVar TVSub ClassVar j) ->
       exists A, nth_error As i = Some A /\ nth_error A0 j = Some A) ->
    forall i j, nth_error Vs i = Some (TVar TVSub ClassVar j) ->
      exists A, nth_error lcD i = Some A /\ nth_error A0 j = Some A.
Proof.
  intros CT mt qh C Ts D Vs Hct H.
  induction H as [C Ts | C Ts P Ss D Vs Hparent Hrest IH];
    intros k hq g d As A0 lcD Hv Hinv i j Hi.
  - assert (lcD = As).
    { symmetry. eapply view_deterministic; [exact Hct | apply v_refl | exact Hv]. }
    subst. auto.
  - inversion Hv as [| ? ? P0 Ss0 ? ? Hparent0 Hrest0]; subst.
    + exfalso.
      pose proof Hparent as Hp. unfold parent_lookup in Hp.
      destruct (find_class CT D) as [def|] eqn:Hfind; [|discriminate].
      destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hp) as (sd & Hsd & Hlt & _).
      assert (Hle : D <= P).
      { eapply base_subtype_le; [exact Hct|].
        eapply super_inst_base; [| |exact Hrest].
        - intros C0 P0 Ss0 Hp0. unfold parent_lookup in Hp0.
          destruct (find_class CT C0) as [d0|] eqn:Hf0; [|discriminate].
          destruct (wf_class_super_inv _ _ _ _ _ Hct Hf0 Hp0) as (sd0 & Hsd0 & _).
          eapply find_class_dom; eauto.
        - eapply find_class_dom; eauto. }
      simpl in Hlt. lia.
    + assert (HE : (P0, Ss0) = (P, Ss)) by congruence.
      inversion HE; subst P0 Ss0. clear HE.
      eapply IH; [exact Hrest0 | | exact Hi].
      intros i0 j0 Hi0.
      rewrite nth_error_map in Hi0. rewrite nth_error_map in Hi0.
      destruct (nth_error Ss i0) as [S|] eqn:ES; [|discriminate].
      simpl in Hi0. inversion Hi0 as [Hi1].
      destruct (subst_adapt_plain _ _ _ _ _ Hi1) as (m & -> & Hm).
      destruct (Hinv m j0 Hm) as (A & HA & HA0).
      exists A. split; [|exact HA0].
      unfold hstep. rewrite nth_error_map. rewrite ES. simpl.
      rewrite HA. reflexivity.
Qed.

(* ------------------THE VIEW OF AN ARGUMENT THAT IS NOT A PLAIN PARAMETER------------------*)

(** A labelled argument whose head, when mutable, carries the label [l]. *)
Definition ownhead (L : list nat) (l : lab) (A : ltype) : Prop :=
  match A with
  | LT q0 l0 _ _ => q0 = Mut -> norm L l0 = norm L l
  end.

(** From a class whose payloads are of the object's own label upwards, a
    superclass argument that is not one of the class's own parameters, passed
    on unchanged, is headed by the object's own label when it is mutable: its
    head was written in a class header, and the object reads every header
    through its own label. *)
Lemma oview_nonplain_own : forall CT L mt qh qo l C Ts D Vs,
  wf_class_table CT ->
  super_inst CT mt qh C Ts D Vs ->
  forall As lcD,
    oview CT qo l C As D lcD ->
    hinv CT L qo l C As -> pown CT L l C As ->
    (forall i A, nth_error As i = Some A ->
       (exists j, nth_error Ts i = Some (TVar TVSub ClassVar j)) \/ ownhead L l A) ->
    forall i A, nth_error lcD i = Some A ->
      (exists j, nth_error Vs i = Some (TVar TVSub ClassVar j)) \/ ownhead L l A.
Proof.
  intros CT L mt qh qo l C Ts D Vs Hct H.
  induction H as [C Ts | C Ts P Ss D Vs Hparent Hrest IH];
    intros As lcD Hv Hi Hk Hinv i A HA.
  - assert (lcD = As).
    { symmetry. eapply view_deterministic; [exact Hct | apply v_refl | exact Hv]. }
    subst. auto.
  - unfold oview in Hv.
    inversion Hv as [| ? ? P0 Ss0 ? ? Hparent0 Hrest0]; subst.
    + exfalso.
      pose proof Hparent as Hp. unfold parent_lookup in Hp.
      destruct (find_class CT D) as [def|] eqn:Hfind; [|discriminate].
      destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hp) as (sd & Hsd & Hlt & _).
      assert (Hle : D <= P).
      { eapply base_subtype_le; [exact Hct|].
        eapply super_inst_base; [| |exact Hrest].
        - intros C0 P0 Ss0 Hp0. unfold parent_lookup in Hp0.
          destruct (find_class CT C0) as [d0|] eqn:Hf0; [|discriminate].
          destruct (wf_class_super_inv _ _ _ _ _ Hct Hf0 Hp0) as (sd0 & Hsd0 & _).
          eapply find_class_dom; eauto.
        - eapply find_class_dom; eauto. }
      simpl in Hlt. lia.
    + assert (HE : (P0, Ss0) = (P, Ss)) by congruence.
      inversion HE; subst P0 Ss0. clear HE.
      rewrite hstep_obj in Hrest0.
      change (hframe (qr2q qo) l (pclassf CT C As) As) with (hfr CT qo l C As) in Hrest0.
      destruct (hinv_step CT L qo l C As P Ss Hct Hi Hparent) as [HiP HkP].
      pose proof (pown_hdr CT L qo l C As Hk) as Hmutl.
      eapply (IH _ lcD Hrest0 HiP (HkP Hk)); [|exact HA].
      intros i0 A0 HA0.
      rewrite nth_error_map in HA0.
      destruct (nth_error Ss i0) as [S|] eqn:ES; [|discriminate].
      simpl in HA0. inversion HA0; subst A0. clear HA0.
      rewrite !nth_error_map. rewrite ES. simpl.
      destruct S as [q0 C0 a0 | u o k | n0 C0 a0].
      * right. simpl. intros Hq.
        destruct q0; simpl in Hq; try discriminate.
        -- exact Hmutl.
        -- reflexivity.
      * destruct u as [|q0|mp].
        -- destruct o.
           ++ simpl. destruct (nth_error As k) as [A'|] eqn:EA.
              ** destruct (Hinv k A' EA) as [[j Hj] | Ho].
                 --- left. exists j. unfold adapt. simpl. rewrite Hj. reflexivity.
                 --- right. exact Ho.
              ** right. simpl. intros Hx. discriminate.
           ++ right. simpl. destruct k; simpl; intros Hx; discriminate.
        -- right. simpl.
           destruct (match tv_lookup o As [] k with Some A0 => A0 | None => ldefault end)
             as [qa la Ca Aa].
           simpl. intros Hq.
           destruct q0; simpl in Hq; try discriminate.
           ++ exact Hmutl.
           ++ reflexivity.
        -- right. simpl.
           destruct (match tv_lookup o As [] k with Some A0 => A0 | None => ldefault end)
             as [qa la Ca Aa].
           unfold lqnth. destruct mp; simpl; intros Hx; discriminate.
      * right. simpl. unfold lqnth. destruct n0; simpl; intros Hx; discriminate.
Qed.

(* ------------------ALONG THE LOOKUP CHAIN------------------*)

(** On a mutable receiver, every argument that the declared receiver [R]
    requalifies as receiver-dependent carries the receiver's own label. *)
Definition lrecv_ok (L : list nat) (qr : q_r) (c : option nat)
    (lc : list ltype) (R : qualified_type) : Prop :=
  qr = Mut_r ->
  forall j l1 C As,
    nth_error (targs R) j = Some (TVar (TVQual RDM) ClassVar j) ->
    nth_error lc j = Some (LT Mut l1 C As) ->
    norm L l1 = norm L (olab c).

Lemma nth_class_var_types : forall n i T,
  nth_error (class_var_types n) i = Some T -> T = TVar TVSub ClassVar i /\ i < n.
Proof.
  intros n i T H. unfold class_var_types in H. rewrite nth_error_map in H.
  destruct (nth_error (seq 0 n) i) as [k|] eqn:Hk; [|discriminate].
  assert (Hlt : i < length (seq 0 n)) by (apply nth_error_Some; congruence).
  rewrite length_seq in Hlt.
  apply (nth_error_nth _ _ 0) in Hk.
  assert (Hs : nth i (seq 0 n) 0 = 0 + i) by (apply seq_nth; exact Hlt).
  rewrite Hs in Hk. simpl in Hk. subst k. simpl in H. inversion H. auto.
Qed.

(** The arguments of a receiver type that has no mutable position are not
    requalified as mutable. *)
Lemma no_mut_recv_args : forall Δ R i u o n,
  no_mut Δ R ->
  nth_error (targs R) i = Some (TVar (TVQual u) o n) -> u <> Mut.
Proof.
  intros Δ R i u o n Hnm Hi.
  assert (Hall : Forall (no_mut Δ) (targs R)).
  { inversion Hnm; subst; simpl; auto; simpl in Hi; destruct i; discriminate. }
  rewrite Forall_forall in Hall.
  pose proof (Hall _ (nth_error_In _ _ Hi)) as Hx. inversion Hx; subst. assumption.
Qed.

Lemma lookup_lref_recvp : forall CT qr c Co Ro C Rs1,
  wf_class_table CT ->
  rsuper_inst CT (qr2q qr) Co Ro C Rs1 ->
  wf_rtypeuse CT (mkruntime_type qr Co Ro) ->
  forall Ao, erases Ao Ro ->
  forall mth D' mdef' D mdef ca' ca lc' lc,
    FindMethodWithName CT Co mth D' mdef' ->
    FindMethodWithName CT C mth D mdef ->
    rsuper_inst CT (qr2q qr) Co Ro D' ca' ->
    rsuper_inst CT (qr2q qr) Co Ro D ca ->
    oview CT qr (olab c) Co Ao D' lc' ->
    oview CT qr (olab c) Co Ao D lc ->
    readonly_state_method_scope (mscope (msignature mdef')) ->
    forall L ka,
      length ka = mqparams (msignature mdef) ->
      radmit (qr2q qr) ca ka (mreceiver (msignature mdef)) ->
      lrecv_ok L qr c lc (mreceiver (msignature mdef)) ->
      lrecv_ok L qr c lc' (mreceiver (msignature mdef')).
Proof.
  intros CT qr c Co Ro C Rs1 Hct H.
  remember (qr2q qr) as qo eqn:Hqo.
  induction H as [C Rs | C Rs P Ss D0 Vs Hparent Hrest IH];
    intros Hrt Ao HeA mth D' mdef' D mdef ca' ca lc' lc Hf' Hf Hs' Hs Hl' Hl
      Hrsc L ka Hk Hadm Hok.
  - destruct (find_method_with_name_deterministic _ _ _ _ _ _ _ Hf' Hf) as [-> ->].
    assert (lc' = lc) by (eapply oview_deterministic; eauto). subst lc'.
    exact Hok.
  - subst qo.
    pose proof (rsuper_inst_le _ _ _ _ _ _ Hct Hrest) as HleC.
    pose proof Hparent as Hparent'. unfold parent_lookup in Hparent'.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
    destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hparent') as (sd & _ & HltP & _).
    pose proof (base_subtype_le _ _ _ Hct (find_method_with_name_base _ _ _ _ _ Hf))
      as HleD.
    assert (HsD : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs [] []) Ss) D ca).
    { inversion Hs; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    assert (HrtP : wf_rtypeuse CT
                     (mkruntime_type qr P (map (dyn (qr2q qr) Rs [] []) Ss))).
    { eapply rsuper_wf; [exact Hct | | exact Hrt].
      eapply rsi_step; eauto. apply rsi_refl. }
    assert (HeAP : erases (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss)
                     (map (dyn (qr2q qr) Rs [] []) Ss)).
    { unfold erases. rewrite map_erase_hstep_obj. unfold erases in HeA.
      rewrite HeA. reflexivity. }
    assert (HlD : oview CT qr (olab c) P
                       (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss) D lc).
    { inversion Hl; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    inversion Hf'; subst.
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      assert (ca' = Rs).
      { eapply rsuper_inst_deterministic; [exact Hct | exact Hs' | apply rsi_refl]. }
      subst ca'.
      assert (lc' = Ao).
      { eapply oview_deterministic; [exact Hct | exact Hl' | apply v_refl]. }
      subst lc'.
      destruct (find_from_subclass _ _ _ _ _ _ Hrest _ _ _ Hf) as (D1 & mdef1 & HfP).
      destruct (find_rsuper_exists _ _ _ _ _ HfP (qr2q qr)
                  (map (dyn (qr2q qr) Rs [] []) Ss)) as [ca1 Hs1].
      destruct (oview_exists _ _ _ _ _ _ Hs1 qr (olab c) _ eq_refl HeAP)
        as (lc1 & Hl1 & He1).
      pose proof (find_method_wf _ _ _ _ _ Hct Hf') as Hwm.
      assert (HfP' : FindMethodWithName CT P (mname (msignature mdef')) D1 mdef1).
      { rewrite (gget_method_name_consistent _ _ _ Hget_method). exact HfP. }
      assert (Hs1' : rsuper_inst CT (qr2q qr) D' Rs D1 ca1)
        by (eapply rsi_step; eauto).
      destruct (override_data CT qr D' Rs def mdef' P Ss D1 mdef1 ca1
                  Hct Hrt Hfind Hparent' Hwm HfP' Hs1')
        as (Vs0 & Hag & Hsi & Hcompat & Hca1 & _).
      pose proof (lookup_refines _ _ _ _ _ _ Hct Hrest HrtP _ _ _ _ _ _ _
                    HfP Hf Hs1 HsD) as (_ & ([_ Hadmr] & _ & Hmq1) & _).
      assert (Hrsc1 : readonly_state_method_scope (mscope (msignature mdef1))).
      { destruct Hcompat as (_ & Hscope & _). rewrite <- Hscope. exact Hrsc. }
      pose proof (IH HrtP _ HeAP _ _ _ _ _ _ _ lc1 lc HfP Hf Hs1 HsD Hl1 HlD
                    Hrsc1 L ka Hk Hadm Hok) as Htop.
      pose proof (find_method_wf _ _ _ _ _ Hct HfP) as Hwm1.
      intros Hqr j l1 Cj Asj Hj HAj. subst qr.
      (* shapes and lengths *)
      destruct Hwm as ((Hsh' & _) & _).
      destruct Hsh' as (args' & Hra' & Hcase').
      assert (Hta' : targs (mreceiver (msignature mdef')) = args').
      { destruct Hcase' as [[qx Hx] | [nx Hx]]; rewrite Hx; reflexivity. }
      pose proof Hwm1 as ((Hsh1 & _) & _ & _ & _ & _ & Hroots1).
      destruct Hsh1 as (args1 & Hra1 & Hcase1).
      assert (Hta1 : targs (mreceiver (msignature mdef1)) = args1).
      { destruct Hcase1 as [[qx Hx] | [nx Hx]]; rewrite Hx; reflexivity. }
      assert (HlenRs : length Rs = length (class_tparams CT D')).
      { unfold wf_rtypeuse in Hrt. simpl in Hrt. rewrite Hfind in Hrt.
        destruct Hrt as (_ & _ & Hbnd). unfold class_tparams. rewrite Hfind.
        apply (Forall2_length Hbnd). }
      assert (HlenVs : length Vs0 = length (class_tparams CT D1)).
      { pose proof (rsuper_wf _ _ _ _ _ _ Hct Hs1' Hrt) as Hw1.
        unfold wf_rtypeuse in Hw1. simpl in Hw1. unfold class_tparams.
        destruct (find_class CT D1) as [d1|]; [|contradiction].
        destruct Hw1 as (_ & _ & Hbnd1).
        rewrite <- (Forall2_length Hbnd1). rewrite (Hca1 [] []).
        rewrite length_map. reflexivity. }
      assert (HAoj : nth_error Rs j = Some (RClass Mut Cj (map erase Asj))).
      { unfold erases in HeA. rewrite <- HeA. rewrite nth_error_map. rewrite HAj.
        reflexivity. }
      assert (Hnomut1 : forall i u,
                nth_error args1 i = Some (TVar (TVQual u) ClassVar i) -> u <> Mut).
      { intros i u Hi.
        destruct (Hroots1 Hrsc1) as [Hnm1 _].
        eapply no_mut_recv_args; [exact Hnm1|]. rewrite Hta1. exact Hi. }
      assert (Hadm1 : forall ka0 ca0, length ka0 = length ka ->
                length ca0 = length (class_tparams CT D') ->
                radmit Mut (map (dyn Mut ca0 [] []) Vs0) ka0 (mreceiver (msignature mdef1)) ->
                radmit Mut ca0 ka0 (mreceiver (msignature mdef'))).
      { intros ka0 ca0 Hlk0 Hl0 Hadm0.
        destruct Hcompat as (_ & _ & _ & _ & _ & Hrcv & Hpass).
        refine (recv_up_radmit CT _ _ Vs0 _ _ _ _ Mut_r ca0 ka0 Hct
                  _ _ _ _ _ _ _ Hrcv Hpass Hadm0).
        - rewrite Hta1. rewrite HlenVs. exact Hra1.
        - rewrite Hta'. rewrite Hl0. exact Hra'.
        - destruct Hcase1 as [[qx Hx] | [nx Hx]]; rewrite Hx; discriminate.
        - destruct Hcase' as [[qx Hx] | [nx Hx]]; rewrite Hx; discriminate.
        - rewrite Hlk0. rewrite Hk. symmetry. exact Hmq1.
        - reflexivity.
        - intros Hq. rewrite Hq in Hag. simpl in Hag. discriminate. }
      assert (Hact1 : radmit Mut (map (dyn Mut Rs [] []) Vs0) ka
                        (mreceiver (msignature mdef1))).
      { pose proof (Hadmr ka Hk Hadm) as Hx. rewrite (Hca1 [] []) in Hx. exact Hx. }
      assert (Hj' : nth_error args' j = Some (TVar (TVQual RDM) ClassVar j)).
      { rewrite <- Hta'. exact Hj. }
      destruct (recv_rdm_source (length (class_tparams CT D'))
                  (length (class_tparams CT D1)) Vs0 args1 args' Rs ka j Cj
                  (map erase Asj) _ _ Hta1 Hta' Hra1 Hra' HlenVs HlenRs
                  Hnomut1 Hadm1 Hact1 Hj' HAoj)
        as (i & HVi & Hai).
      (* the labelled argument is the same at the overridden class *)
      assert (Hbase : forall i0 j0,
                nth_error (class_var_types (length Rs)) i0 = Some (TVar TVSub ClassVar j0) ->
                exists A, nth_error Ao i0 = Some A /\ nth_error Ao j0 = Some A).
      { intros i0 j0 Hi0.
        destruct (nth_class_var_types _ _ _ Hi0) as [E Hlt]. inversion E; subst j0.
        assert (Hlt' : i0 < length Ao).
        { unfold erases in HeA. rewrite <- HeA in Hlt. rewrite length_map in Hlt.
          exact Hlt. }
        destruct (nth_error Ao i0) as [A|] eqn:EA.
        - exists A. auto.
        - apply nth_error_None in EA. lia. }
      destruct (view_plain_var _ _ _ _ _ _ _ Hct Hsi false Mut (fun q0 => q0)
                  (olab c) Ao Ao lc1
                  (v_step CT false Mut (fun q0 => q0) (olab c) D' Ao P Ss D1 lc1
                     Hparent Hl1) Hbase i j HVi) as (A & HA1 & HA0).
      rewrite HAj in HA0. inversion HA0; subst A.
      eapply (Htop eq_refl i); [rewrite Hta1; exact Hai | exact HA1].
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      rewrite Hsuper in Hparent'. inversion Hparent'; subst.
      pose proof (base_subtype_le _ _ _ Hct
                    (find_method_with_name_base _ _ _ _ _ Hparent_fmn)) as HleD'.
      assert (HsD' : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs [] []) Ss) D' ca').
      { inversion Hs'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      assert (HlD' : oview CT qr (olab c) P
                       (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss) D' lc').
      { inversion Hl'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      exact (IH HrtP _ HeAP _ _ _ _ _ _ _ lc' lc Hparent_fmn Hf HsD' HsD HlD' HlD
               Hrsc L ka Hk Hadm Hok).
Qed.

(* ------------------AT THE CALL------------------*)

Lemma ldyn_member_recv_args : forall F qy Vs Us Qs R,
  (exists q1 C1 a1, R = TClass q1 C1 a1) \/ (exists n1 C1 a1, R = THead n1 C1 a1) ->
  exists q2 l2 C0,
    ((exists q0, R = TClass q0 C0 (targs R)) \/ (exists n, R = THead n C0 (targs R))) /\
    ldyn F (member_recv qy Vs Us Qs R) =
    LT q2 l2 C0
      (map (fun T => ldyn F (subst Vs Us Qs (map_qual (vpa_recv qy) T))) (targs R)).
Proof.
  intros F qy Vs Us Qs R [(q1 & C1 & a1 & ->) | (n1 & C1 & a1 & ->)].
  - unfold member_recv. cbn [map_qual subst ldyn targs].
    do 3 eexists. split; [left; eexists; reflexivity|].
    rewrite !map_map. reflexivity.
  - unfold member_recv. cbn [map_qual subst targs].
    destruct (nth_error Qs n1) as [[ql | m]|]; unfold qhead; cbn [ldyn];
      do 3 eexists; (split; [right; eexists; reflexivity|]);
      rewrite !map_map; reflexivity.
Qed.

Lemma ldyn_requalify_head : forall F q0 U,
  exists C a, ldyn F (requalify q0 U) = LT (dynq (lf_q F) q0) (lab_of F q0) C a.
Proof.
  intros F q0 [q1 C a | u o n | n C a]; simpl.
  - eauto.
  - destruct (match tv_lookup o (lf_cargs F) (lf_margs F) n with
              | Some A => A | None => ldefault end) as [qa la Ca aa].
    simpl. eauto.
  - eauto.
Qed.

Lemma norm_some : forall L l w, norm L l = Some w -> l = LIn w /\ List.In w L.
Proof.
  intros L [w0|] w H; simpl in H; [|discriminate].
  destruct (in_dec Nat.eq_dec w0 L); inversion H; subst. auto.
Qed.

(** A mutable head label is the label of the object. *)
Lemma headL_norm : forall L c l,
  headL L c Mut l -> norm L l = norm L (olab c).
Proof.
  intros L c l H. specialize (H eq_refl).
  destruct (norm L l) as [w|] eqn:E.
  - subst c. destruct (norm_some _ _ _ E) as [_ Hin]. simpl.
    symmetry. apply norm_live. exact Hin.
  - destruct c as [w|]; simpl; [|reflexivity].
    symmetry. apply norm_dead. apply H. reflexivity.
Qed.

Print Assumptions lookup_lref_recvp.

(** On a receiver of either mutability, every mutable argument that the
    declared receiver [R] writes under a qualifier parameter carries the
    label of the qualifier argument, when that argument is mutable. *)
Definition lrecv_okp (L : list nat) (lk : list (q * lab)) (lc : list ltype)
    (R : qualified_type) : Prop :=
  forall j m l1 C As,
    nth_error (targs R) j = Some (TVar (TVPoly m) ClassVar j) ->
    nth_error lc j = Some (LT Mut l1 C As) ->
    fst (lqnth lk m) = Mut ->
    norm L l1 = norm L (snd (lqnth lk m)).

Lemma class_var_types_nth : forall n i,
  i < n -> nth_error (class_var_types n) i = Some (TVar TVSub ClassVar i).
Proof.
  intros n i H. unfold class_var_types. rewrite nth_error_map.
  assert (Hlt : i < length (seq 0 n)) by (rewrite length_seq; exact H).
  rewrite (nth_error_nth' (seq 0 n) 0 Hlt). rewrite seq_nth; try exact H. reflexivity.
Qed.

Lemma radmit_qual_head : forall qr ca ka R i u r,
  radmit qr ca ka R ->
  nth_error (targs R) i = Some (TVar (TVQual u) ClassVar i) ->
  nth_error ca i = Some r ->
  arg_q_sub (rhead r) (dynq qr u).
Proof.
  intros qr ca ka R i u r H HT Hr.
  assert (Hy : nth_error (map (dyn qr ca [] ka) (targs R)) i =
               Some (rrequalify (dynq qr u) r)).
  { rewrite nth_error_map. rewrite HT. simpl. rewrite Hr. reflexivity. }
  pose proof (Forall2_nth _ _ _ _ _ (H []) i _ _ Hr Hy) as Hx.
  apply rarg_sub_requalify_iff in Hx. exact Hx.
Qed.

(** The same along the lookup chain: the fact for the declaration the caller
    sees carries to the declaration that runs. *)
Lemma lookup_lref_recvq : forall CT qr c Co Ro C Rs1,
  wf_class_table CT ->
  clean_bounds_ct CT ->
  rsuper_inst CT (qr2q qr) Co Ro C Rs1 ->
  wf_rtypeuse CT (mkruntime_type qr Co Ro) ->
  forall Ao, erases Ao Ro ->
  forall mth D' mdef' D mdef ca' ca lc' lc,
    FindMethodWithName CT Co mth D' mdef' ->
    FindMethodWithName CT C mth D mdef ->
    rsuper_inst CT (qr2q qr) Co Ro D' ca' ->
    rsuper_inst CT (qr2q qr) Co Ro D ca ->
    oview CT qr (olab c) Co Ao D' lc' ->
    oview CT qr (olab c) Co Ao D lc ->
    readonly_state_method_scope (mscope (msignature mdef')) ->
    forall L lk,
      hinv CT L qr (olab c) Co Ao ->
      length lk = mqparams (msignature mdef) ->
      radmit (qr2q qr) ca (map fst lk) (mreceiver (msignature mdef)) ->
      lrecv_ok L qr c lc (mreceiver (msignature mdef)) ->
      lrecv_okp L lk lc (mreceiver (msignature mdef)) ->
      lrecv_okp L lk lc' (mreceiver (msignature mdef')).
Proof.
  intros CT qr c Co Ro C Rs1 Hct Hclean H.
  remember (qr2q qr) as qo eqn:Hqo.
  induction H as [C Rs | C Rs P Ss D0 Vs Hparent Hrest IH];
    intros Hrt Ao HeA mth D' mdef' D mdef ca' ca lc' lc Hf' Hf Hs' Hs Hl' Hl
      Hrsc L lk Hinv0 Hlk Hadm Hok Hokp.
  - destruct (find_method_with_name_deterministic _ _ _ _ _ _ _ Hf' Hf) as [-> ->].
    assert (lc' = lc) by (eapply oview_deterministic; eauto). subst lc'.
    exact Hokp.
  - subst qo.
    pose proof (rsuper_inst_le _ _ _ _ _ _ Hct Hrest) as HleC.
    pose proof Hparent as Hparent'. unfold parent_lookup in Hparent'.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
    destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hparent') as (sd & _ & HltP & _).
    pose proof (base_subtype_le _ _ _ Hct (find_method_with_name_base _ _ _ _ _ Hf))
      as HleD.
    assert (HsD : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs [] []) Ss) D ca).
    { inversion Hs; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    assert (HrtP : wf_rtypeuse CT
                     (mkruntime_type qr P (map (dyn (qr2q qr) Rs [] []) Ss))).
    { eapply rsuper_wf; [exact Hct | | exact Hrt].
      eapply rsi_step; eauto. apply rsi_refl. }
    assert (HeAP : erases (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss)
                     (map (dyn (qr2q qr) Rs [] []) Ss)).
    { unfold erases. rewrite map_erase_hstep_obj. unfold erases in HeA.
      rewrite HeA. reflexivity. }
    assert (HlD : oview CT qr (olab c) P
                       (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss) D lc).
    { inversion Hl; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    assert (Hk : length (map fst lk) = mqparams (msignature mdef)).
    { rewrite length_map. exact Hlk. }
    assert (HinvP : hinv CT L qr (olab c) P
                      (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss)).
    { rewrite hstep_obj.
      exact (proj1 (hinv_step CT L qr (olab c) C Ao P Ss Hct Hinv0 Hparent)). }
    inversion Hf'; subst.
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      assert (ca' = Rs).
      { eapply rsuper_inst_deterministic; [exact Hct | exact Hs' | apply rsi_refl]. }
      subst ca'.
      assert (lc' = Ao).
      { eapply oview_deterministic; [exact Hct | exact Hl' | apply v_refl]. }
      subst lc'.
      destruct (find_from_subclass _ _ _ _ _ _ Hrest _ _ _ Hf) as (D1 & mdef1 & HfP).
      destruct (find_rsuper_exists _ _ _ _ _ HfP (qr2q qr)
                  (map (dyn (qr2q qr) Rs [] []) Ss)) as [ca1 Hs1].
      destruct (oview_exists _ _ _ _ _ _ Hs1 qr (olab c) _ eq_refl HeAP)
        as (lc1 & Hl1 & He1).
      pose proof (find_method_wf _ _ _ _ _ Hct Hf') as Hwm.
      assert (HfP' : FindMethodWithName CT P (mname (msignature mdef')) D1 mdef1).
      { rewrite (gget_method_name_consistent _ _ _ Hget_method). exact HfP. }
      assert (Hs1' : rsuper_inst CT (qr2q qr) D' Rs D1 ca1)
        by (eapply rsi_step; eauto).
      destruct (override_data CT qr D' Rs def mdef' P Ss D1 mdef1 ca1
                  Hct Hrt Hfind Hparent' Hwm HfP' Hs1')
        as (Vs0 & Hag & Hsi & Hcompat & Hca1 & _).
      pose proof (lookup_refines _ _ _ _ _ _ Hct Hrest HrtP _ _ _ _ _ _ _
                    HfP Hf Hs1 HsD) as (_ & ([_ Hadmr] & _ & Hmq1) & _).
      assert (Hrsc1 : readonly_state_method_scope (mscope (msignature mdef1))).
      { destruct Hcompat as (_ & Hscope & _). rewrite <- Hscope. exact Hrsc. }
      pose proof (IH HrtP _ HeAP _ _ _ _ _ _ _ lc1 lc HfP Hf Hs1 HsD Hl1 HlD
                    Hrsc1 L lk HinvP Hlk Hadm Hok Hokp) as Htop.
      pose proof (lookup_lref_recvp CT qr c P _ D0 Vs Hct Hrest HrtP _ HeAP
                    _ _ _ _ _ _ _ lc1 lc HfP Hf Hs1 HsD Hl1 HlD
                    Hrsc1 L (map fst lk) Hk Hadm Hok) as Htop_r.
      pose proof (find_method_wf _ _ _ _ _ Hct HfP) as Hwm1.
      (* the class that declares the method that runs has no mutable
         position in its bounds, so the object reads every class header from
         there upwards through its own label *)
      assert (Hin' : List.In mdef' (methods (body def))).
      { eapply gget_method_In; eauto. }
      pose proof (Hclean D' def mdef' Hfind Hin' Hrsc) as Hnb.
      assert (Hpn : pclassf CT D' Ao = None).
      { apply pclassf_clean. intros d Hd. rewrite Hfind in Hd. inversion Hd; subst d.
        eapply nomut_bounds_clean; eauto. }
      assert (Hown : pown CT L (olab c) D' Ao).
      { intros q' l' Hx. rewrite Hpn in Hx. discriminate. }
      intros j m l1 Cj Asj Hj HAj Hkq.
      (* shapes and lengths *)
      destruct Hwm as ((Hsh' & _) & _).
      destruct Hsh' as (args' & Hra' & Hcase').
      assert (Hta' : targs (mreceiver (msignature mdef')) = args').
      { destruct Hcase' as [[qx Hx] | [nx Hx]]; rewrite Hx; reflexivity. }
      pose proof Hwm1 as ((Hsh1 & _) & _ & _ & _ & _ & Hroots1).
      destruct Hsh1 as (args1 & Hra1 & Hcase1).
      assert (Hta1 : targs (mreceiver (msignature mdef1)) = args1).
      { destruct Hcase1 as [[qx Hx] | [nx Hx]]; rewrite Hx; reflexivity. }
      assert (HlenRs : length Rs = length (class_tparams CT D')).
      { unfold wf_rtypeuse in Hrt. simpl in Hrt. rewrite Hfind in Hrt.
        destruct Hrt as (_ & _ & Hbnd). unfold class_tparams. rewrite Hfind.
        apply (Forall2_length Hbnd). }
      assert (HlenVs : length Vs0 = length (class_tparams CT D1)).
      { pose proof (rsuper_wf _ _ _ _ _ _ Hct Hs1' Hrt) as Hw1.
        unfold wf_rtypeuse in Hw1. simpl in Hw1. unfold class_tparams.
        destruct (find_class CT D1) as [d1|]; [|contradiction].
        destruct Hw1 as (_ & _ & Hbnd1).
        rewrite <- (Forall2_length Hbnd1). rewrite (Hca1 [] []).
        rewrite length_map. reflexivity. }
      assert (HAoj : nth_error Rs j = Some (RClass Mut Cj (map erase Asj))).
      { unfold erases in HeA. rewrite <- HeA. rewrite nth_error_map. rewrite HAj.
        reflexivity. }
      assert (Hnomut1 : forall i u,
                nth_error args1 i = Some (TVar (TVQual u) ClassVar i) -> u <> Mut).
      { intros i u Hi.
        destruct (Hroots1 Hrsc1) as [Hnm1 _].
        eapply no_mut_recv_args; [exact Hnm1|]. rewrite Hta1. exact Hi. }
      assert (Hadm1 : forall ka0 ca0, length ka0 = length (map fst lk) ->
                length ca0 = length (class_tparams CT D') ->
                radmit (qr2q qr) (map (dyn (qr2q qr) ca0 [] []) Vs0) ka0
                  (mreceiver (msignature mdef1)) ->
                radmit (qr2q qr) ca0 ka0 (mreceiver (msignature mdef'))).
      { intros ka0 ca0 Hlk0 Hl0 Hadm0.
        destruct Hcompat as (_ & _ & _ & _ & _ & Hrcv & Hpass).
        refine (recv_up_radmit CT _ _ Vs0 _ _ _ _ qr ca0 ka0 Hct
                  _ _ _ _ _ _ _ Hrcv Hpass Hadm0).
        - rewrite Hta1. rewrite HlenVs. exact Hra1.
        - rewrite Hta'. rewrite Hl0. exact Hra'.
        - destruct Hcase1 as [[qx Hx] | [nx Hx]]; rewrite Hx; discriminate.
        - destruct Hcase' as [[qx Hx] | [nx Hx]]; rewrite Hx; discriminate.
        - rewrite Hlk0. rewrite Hk. symmetry. exact Hmq1.
        - intros Hq. rewrite Hq in Hag.
          destruct qr; simpl in Hag; [reflexivity | discriminate].
        - intros Hq. rewrite Hq in Hag.
          destruct qr; simpl in Hag; [discriminate | reflexivity]. }
      assert (Hact1' : radmit (qr2q qr) ca1 (map fst lk) (mreceiver (msignature mdef1))).
      { exact (Hadmr (map fst lk) Hk Hadm). }
      assert (Hact1 : radmit (qr2q qr) (map (dyn (qr2q qr) Rs [] []) Vs0) (map fst lk)
                        (mreceiver (msignature mdef1))).
      { pose proof Hact1' as Hx. rewrite (Hca1 [] []) in Hx. exact Hx. }
      assert (Hj' : nth_error args' j = Some (TVar (TVPoly m) ClassVar j)).
      { rewrite <- Hta'. exact Hj. }
      assert (Hkm : qnth (map fst lk) m = Mut).
      { rewrite qnth_map_fst. exact Hkq. }
      assert (Hbase : forall i0 j0,
                nth_error (class_var_types (length Rs)) i0 = Some (TVar TVSub ClassVar j0) ->
                exists A, nth_error Ao i0 = Some A /\ nth_error Ao j0 = Some A).
      { intros i0 j0 Hi0.
        destruct (nth_class_var_types _ _ _ Hi0) as [E Hlt]. inversion E; subst j0.
        assert (Hlt' : i0 < length Ao).
        { unfold erases in HeA. rewrite <- HeA in Hlt. rewrite length_map in Hlt.
          exact Hlt. }
        destruct (nth_error Ao i0) as [A|] eqn:EA.
        - exists A. auto.
        - apply nth_error_None in EA. lia. }
      assert (Hview1 : view CT false (qr2q qr) (fun q0 => q0) (olab c) D' Ao D1 lc1).
      { eapply v_step; [exact Hparent | exact Hl1]. }
      pose proof Hra1 as [_ Hshp1].
      destruct (find_pair (is_psrc m j) Vs0 args1) as [(i & V & a & HV & Ha & Hsb) | Hnp].
      { (* the overridden receiver writes the same stored argument under the
           same qualifier parameter *)
        destruct (is_psrc_true _ _ _ _ Hsb) as [-> (o & i' & ->)].
        destruct (Hshp1 i _ Ha) as [u E]. injection E as Eu Eo Ei. subst u o i'.
        destruct (view_plain_var _ _ _ _ _ _ _ Hct Hsi false (qr2q qr) (fun q0 => q0)
                    (olab c) Ao Ao lc1 Hview1 Hbase i j HV) as (A & HA1 & HA0).
        rewrite HAj in HA0. inversion HA0; subst A.
        eapply (Htop i m l1); [rewrite Hta1; exact Ha | exact HA1 | exact Hkq]. }
      assert (Hnosrc : forall i, nth_error Vs0 i = Some (TVar TVSub ClassVar j) ->
                nth_error args1 i <> Some (TVar (TVPoly m) ClassVar i)).
      { intros i HV Ha. pose proof (Hnp i _ _ HV Ha) as Hfx. simpl in Hfx.
        rewrite !Nat.eqb_refl in Hfx. discriminate. }
      destruct (recv_poly_source (qr2q qr) (length (class_tparams CT D'))
                  (length (class_tparams CT D1)) Vs0 args1 args' Rs (map fst lk) j m Cj
                  (map erase Asj) _ _ Hta1 Hta' Hra1 Hra' HlenVs HlenRs
                  Hadm1 Hact1 Hj' HAoj Hkm)
        as [(i & HVi & Hai) | (i & u & HVi & Hai & Hdu)].
      { exfalso. exact (Hnosrc i HVi Hai). }
      (* the stored argument is written receiver-dependent by the overridden
         receiver, on a mutable object: it carries the object's own label *)
      assert (Hu : u = RDM /\ qr = Mut_r).
      { pose proof (Hnomut1 i u Hai) as Hne.
        destruct u; simpl in Hdu; try discriminate; try congruence.
        destruct qr; simpl in Hdu; try discriminate. auto. }
      destruct Hu as [-> Hqr].
      assert (Hl1c : norm L l1 = norm L (olab c)).
      { destruct (view_plain_var _ _ _ _ _ _ _ Hct Hsi false (qr2q qr) (fun q0 => q0)
                    (olab c) Ao Ao lc1 Hview1 Hbase i j HVi) as (A & HA1 & HA0).
        rewrite HAj in HA0. inversion HA0; subst A.
        eapply (Htop_r Hqr i); [rewrite Hta1; exact Hai | exact HA1]. }
      destruct (recv_poly_pinned (qr2q qr) (length (class_tparams CT D'))
                  (length (class_tparams CT D1)) Vs0 args1 args' Rs (map fst lk) j m Cj
                  (map erase Asj) _ _ Hta1 Hta' Hra1 Hra' HlenVs HlenRs
                  Hadm1 Hact1 Hj' HAoj Hkm Hnosrc)
        as (i3 & V3 & Ha3 & HV3 &
            [[Hnp3 Hh3] | (j2 & i2 & u2 & -> & HV2 & Ha2 & Hd2)]).
      * (* under the same parameter the overridden receiver has an argument
           that is not a plain parameter of this class and is mutable: its
           label is the object's own, and the label of the qualifier
           argument *)
        assert (HA3 : exists A3, nth_error lc1 i3 = Some A3 /\
                                 erase A3 = dyn (qr2q qr) Rs [] [] V3).
        { assert (Hc1 : nth_error ca1 i3 = Some (dyn (qr2q qr) Rs [] [] V3)).
          { rewrite (Hca1 [] []). rewrite nth_error_map. rewrite HV3. reflexivity. }
          rewrite <- He1 in Hc1. rewrite nth_error_map in Hc1.
          destruct (nth_error lc1 i3) as [A3|]; [|discriminate].
          inversion Hc1. eauto. }
        destruct HA3 as (A3 & HA3 & HeA3).
        destruct A3 as [q3 l3 C3 As3]. simpl in HeA3. rewrite <- HeA3 in Hh3.
        simpl in Hh3. subst q3.
        assert (Hl3k : norm L l3 = norm L (snd (lqnth lk m))).
        { eapply (Htop i3 m l3); [rewrite Hta1; exact Ha3 | exact HA3 | exact Hkq]. }
        assert (Hl3c : norm L l3 = norm L (olab c)).
        { assert (HbaseN : forall i0 A, nth_error Ao i0 = Some A ->
                    (exists j0, nth_error (class_var_types (length Rs)) i0 =
                                Some (TVar TVSub ClassVar j0)) \/
                    ownhead L (olab c) A).
          { intros i0 A HA. left. exists i0. apply class_var_types_nth.
            unfold erases in HeA. rewrite <- HeA. rewrite length_map.
            apply nth_error_Some. congruence. }
          destruct (oview_nonplain_own CT L AbstractState _ qr (olab c) D' _ D1 Vs0
                      Hct Hsi Ao lc1 Hview1 Hinv0 Hown HbaseN i3 _ HA3)
            as [[j3 Hj3] | Ho].
          - exfalso. rewrite HV3 in Hj3. inversion Hj3 as [E3]. exact (Hnp3 j3 E3).
          - simpl in Ho. exact (Ho eq_refl). }
        rewrite Hl1c. rewrite <- Hl3c. exact Hl3k.
      * (* under the same parameter the overridden receiver has a parameter
           of this class that it also writes receiver-dependent *)
        destruct (view_plain_var _ _ _ _ _ _ _ Hct Hsi false (qr2q qr) (fun q0 => q0)
                    (olab c) Ao Ao lc1 Hview1 Hbase i3 j2 HV3) as (A & HA1 & HA0).
        destruct (view_plain_var _ _ _ _ _ _ _ Hct Hsi false (qr2q qr) (fun q0 => q0)
                    (olab c) Ao Ao lc1 Hview1 Hbase i2 j2 HV2) as (A' & HA1' & HA0').
        rewrite HA0 in HA0'. inversion HA0'; subst A'.
        destruct A as [qA lA CA AsA].
        assert (Hu2 : u2 = RDM).
        { pose proof (Hnomut1 i2 u2 Ha2) as Hne. subst qr.
          destruct u2; simpl in Hd2; try discriminate; try congruence. }
        subst u2.
        assert (HqA : qA = Mut).
        { assert (Hc : nth_error ca1 i2 = Some (erase (LT qA lA CA AsA))).
          { rewrite <- He1. rewrite nth_error_map. rewrite HA1'. reflexivity. }
          assert (HT2 : nth_error (targs (mreceiver (msignature mdef1))) i2 =
                        Some (TVar (TVQual RDM) ClassVar i2)).
          { rewrite Hta1. exact Ha2. }
          pose proof (radmit_qual_head _ _ _ _ _ _ _ Hact1' HT2 Hc) as Hx.
          rewrite Hqr in Hx. simpl in Hx.
          destruct Hx as [Hx | [Hx _]]; [symmetry; exact Hx | discriminate]. }
        subst qA.
        assert (HlAk : norm L lA = norm L (snd (lqnth lk m))).
        { eapply (Htop i3 m lA); [rewrite Hta1; exact Ha3 | exact HA1 | exact Hkq]. }
        assert (HlAc : norm L lA = norm L (olab c)).
        { eapply (Htop_r Hqr i2); [rewrite Hta1; exact Ha2 | exact HA1']. }
        rewrite Hl1c. rewrite <- HlAc. exact HlAk.
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      rewrite Hsuper in Hparent'. inversion Hparent'; subst.
      pose proof (base_subtype_le _ _ _ Hct
                    (find_method_with_name_base _ _ _ _ _ Hparent_fmn)) as HleD'.
      assert (HsD' : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs [] []) Ss) D' ca').
      { inversion Hs'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      assert (HlD' : oview CT qr (olab c) P
                       (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss) D' lc').
      { inversion Hl'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      exact (IH HrtP _ HeAP _ _ _ _ _ _ _ lc' lc Hparent_fmn Hf HsD' HsD HlD' HlD
               Hrsc L lk HinvP Hlk Hadm Hok Hokp).
Qed.

Print Assumptions lookup_lref_recvq.
