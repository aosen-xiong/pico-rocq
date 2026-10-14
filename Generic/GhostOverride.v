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
Lemma ldyn_no_method_vars : forall CT Δ top T,
  wf_stype CT Δ top T ->
  (method_bounds Δ, qparams Δ) = ([], 0) ->
  forall F ms ks, ldyn (lf_with_args F (lf_cargs F) ms ks) T = ldyn F T.
Proof.
  intros CT Δ top T H. induction H using wf_stype_ind'; intros Hmq F ms ks;
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
    rewrite <- (ldyn_no_method_vars _ _ _ _ HwB eq_refl (obj_frame qr b c lca) lm lk).
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
    rewrite (dyn_no_method_vars _ _ _ _ HB eq_refl). exact HR.
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
