From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases.

(** Method-call support for type preservation. *)

(* ------------------CLASS TABLE INVERSION------------------*)

Lemma wf_class_super_inv : forall CT C def P Ss,
  wf_class_table CT ->
  find_class CT C = Some def ->
  super (signature def) = Some (P, Ss) ->
  exists super_def,
    find_class CT P = Some super_def /\
    P < C /\
    Forall lost_free Ss /\
    Forall2
      (fun T B =>
         lost_free (member_type AbstractState
                      (qc2q (class_qualifier (signature def))) Ss [] [] B) /\
         qualified_type_subtype CT
           (mk_tv_env (ctparams (signature def)) [] AbstractState 0) T
           (member_type AbstractState
              (qc2q (class_qualifier (signature def))) Ss [] [] B))
      Ss (ctparams (signature super_def)) /\
    (class_qualifier (signature def) = class_qualifier (signature super_def) \/
     class_qualifier (signature super_def) = RDM_c) /\
    Forall (wf_method CT C) (methods (body def)).
Proof.
  intros CT C def P Ss Hwf Hfind Hsuper.
  pose proof (wf_class_table_class _ _ _ Hwf Hfind) as Hcls.
  assert (Hname : cname (signature def) = C).
  { destruct Hwf as (_ & _ & _ & Hn). apply Hn; auto. }
  inversion Hcls; subst.
  - congruence.
  - rewrite Hsuper in Hsuper0. inversion Hsuper0; subst.
    exists super_def. repeat split; auto.
    eapply Forall2_impl; [|eassumption].
    intros a b0 [Ha Hb]. split; auto using bound_sub_self.
Qed.

Lemma rsuper_inst_le : forall CT qh C Rs D Vs,
  wf_class_table CT -> rsuper_inst CT qh C Rs D Vs -> D <= C.
Proof.
  intros CT qh C Rs D Vs Hwf H. induction H; auto.
  unfold parent_lookup in Hparent.
  destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
  destruct (wf_class_super_inv _ _ _ _ _ Hwf Hfind Hparent) as (sd & _ & Hlt & _).
  lia.
Qed.

Lemma rsuper_inst_deterministic : forall CT qh C Rs D Vs1,
  wf_class_table CT ->
  rsuper_inst CT qh C Rs D Vs1 ->
  forall Vs2, rsuper_inst CT qh C Rs D Vs2 -> Vs1 = Vs2.
Proof.
  intros CT qh C Rs D Vs1 Hwf H. induction H; intros Vs2 H2.
  - inversion H2; subst; auto.
    exfalso.
    pose proof (rsuper_inst_le _ _ _ _ _ _ Hwf Hrest) as Hle.
    unfold parent_lookup in Hparent.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
    destruct (wf_class_super_inv _ _ _ _ _ Hwf Hfind Hparent) as (sd & _ & Hlt & _).
    lia.
  - inversion H2; subst.
    + exfalso.
      pose proof (rsuper_inst_le _ _ _ _ _ _ Hwf H) as Hle.
      unfold parent_lookup in Hparent.
      destruct (find_class CT D) as [def|] eqn:Hfind; [|discriminate].
      destruct (wf_class_super_inv _ _ _ _ _ Hwf Hfind Hparent) as (sd & _ & Hlt & _).
      lia.
    + rewrite Hparent in Hparent0. inversion Hparent0; subst.
      apply IHrsuper_inst; auto.
Qed.

Lemma bound_agree_head_ok : forall qr qc,
  vpa_mutability_runtime_bound_agree qr qc = true ->
  head_ok qr (dynq (qr2q qr) (qc2q qc)).
Proof.
  intros [] []; simpl; intros H; try discriminate; unfold head_ok; simpl; auto.
Qed.

Lemma bound_agree_super : forall qr qc qs,
  vpa_mutability_runtime_bound_agree qr qc = true ->
  qc = qs \/ qs = RDM_c ->
  vpa_mutability_runtime_bound_agree qr qs = true.
Proof.
  intros [] [] [] H [Heq | Heq]; simpl in *; try reflexivity; try discriminate.
Qed.

(** An object's runtime type stays well formed when viewed at a superclass. *)
Lemma rsuper_wf : forall CT qr C Rs D Vs,
  wf_class_table CT ->
  rsuper_inst CT (qr2q qr) C Rs D Vs ->
  wf_rtypeuse CT (mkruntime_type qr C Rs) ->
  wf_rtypeuse CT (mkruntime_type qr D Vs).
Proof.
  intros CT qr C Rs D Vs Hwf H.
  remember (qr2q qr) as qo eqn:Hqo.
  induction H; intros Hrt; auto.
  apply IHrsuper_inst; auto. clear IHrsuper_inst. subst qo.
  unfold wf_rtypeuse in *. simpl in *.
  unfold parent_lookup in Hparent.
  destruct (find_class CT C) as [def|] eqn:Hfind; [|contradiction].
  destruct Hrt as (Hagree & Hlf & Hbnd).
  destruct (wf_class_super_inv _ _ _ _ _ Hwf Hfind Hparent)
    as (sd & Hsd & _ & HlfS & HbS & Hpin & _).
  rewrite Hsd.
  assert (Hfb : frame_bounds_ok CT
                  (mk_tv_env (ctparams (signature def)) [] AbstractState 0)
                  (qr2q qr) Rs [] []).
  { apply frame_bounds_ok_of_rbounds; simpl; auto. constructor. }
  assert (Hc : concrete_q (qr2q qr)) by apply qr2q_concrete.
  refine (conj _ (conj _ _)).
  - eapply bound_agree_super; eauto.
  - apply map_dyn_lost_free; auto.
  - unfold rbounds_ok. eapply Forall2_map_left; [exact HbS|].
    intros T B [HlfB Hsub]. simpl in HlfB, Hsub.
    pose proof (subtype_dyn _ _ _ _ _ _ _ _ Hc Hfb Hsub) as Hrs.
    unfold member_type in Hrs. rewrite dyn_subst in Hrs. simpl map in Hrs.
    rewrite (dyn_adapt_exact AbstractState qr qr
               (qc2q (class_qualifier (signature def)))
               (map (dyn (qr2q qr) Rs [] []) Ss) (map (dyn (qr2q qr) Rs [] []) Ss)
               [] [] [] B); auto using Forall2_rarg_sub_refl, bound_agree_head_ok.
    rewrite <- (dyn_subst (qr2q qr) Rs [] [] Ss [] []).
    apply dyn_lost_free; auto.
Qed.

(* ------------------METHOD LOOKUP------------------*)

Lemma gget_method_In : forall ms m mdef,
  gget_method ms m = Some mdef -> List.In mdef ms.
Proof.
  intros ms m mdef H. unfold gget_method in H.
  apply find_some in H. tauto.
Qed.

Lemma find_method_wf : forall CT C m D mdef,
  wf_class_table CT ->
  FindMethodWithName CT C m D mdef ->
  wf_method CT D mdef.
Proof.
  intros CT C m D mdef Hwf H. induction H; auto.
  subst own_methods. apply gget_method_In in Hget_method.
  pose proof (wf_class_table_class _ _ _ Hwf Hfind) as Hcls.
  destruct (super (signature def)) as [[P Ss]|] eqn:Hsuper.
  - destruct (wf_class_super_inv _ _ _ _ _ Hwf Hfind Hsuper)
      as (_ & _ & _ & _ & _ & _ & Hmeths).
    rewrite Forall_forall in Hmeths. auto.
  - inversion Hcls; subst.
    + rewrite Hno_methods in Hget_method. contradiction.
    + congruence.
Qed.

(* ------------------IDENTITY INSTANTIATION------------------*)

Lemma map_nth_default_seq : forall {A : Type} (d : A) (l : list A),
  map (fun i => match nth_error l i with Some x => x | None => d end)
    (seq 0 (length l)) = l.
Proof.
  intros A d l. induction l as [|a l IH]; simpl; auto.
  f_equal. rewrite <- seq_shift. rewrite map_map. simpl. exact IH.
Qed.

Lemma dyn_class_var_types : forall qctx ca ma ka,
  map (dyn qctx ca ma ka) (class_var_types (length ca)) = ca.
Proof.
  intros. unfold class_var_types. rewrite map_map. simpl.
  apply map_nth_default_seq.
Qed.

(* ------------------EVALUATION FACTS------------------*)

Lemma eval_stmt_heap_ext : forall CT rΓ h s res rΓ' h',
  eval_stmt CT rΓ h s res rΓ' h' -> heap_ext h h'.
Proof.
  intros CT rΓ h s res rΓ' h' H.
  induction H; subst; auto using heap_ext_refl, update_field_heap_ext,
    heap_ext_app; eauto using heap_ext_trans.
Qed.

Lemma callee_env_targs : forall CT rΓ h ly D Us Qs vals rΓ',
  callee_env CT rΓ h ly D Us Qs vals rΓ' ->
  vars rΓ' = Iot ly :: vals.
Proof.
  intros CT rΓ h ly D Us Qs vals rΓ' (lt & qt & oy & ca & _ & _ & _ & _ & ->).
  reflexivity.
Qed.

(** A successful, well-typed evaluation keeps the activation's receiver and
    runtime type arguments. *)
Lemma eval_stmt_frame : forall CT rΓ h s rΓ' h',
  eval_stmt CT rΓ h s OK rΓ' h' ->
  forall Δ sΓ mt sΓ',
    stmt_typing CT Δ sΓ mt s sΓ' ->
    get_this_var_mapping (vars rΓ') = get_this_var_mapping (vars rΓ) /\
    cargs rΓ' = cargs rΓ /\ margs rΓ' = margs rΓ.
Proof.
  intros CT rΓ h s rΓ' h' H.
  remember OK as res eqn:Hres.
  induction H; intros Δ sΓ mt0 sΓ' Htype; try discriminate;
    inversion Htype; subst; simpl; auto.
  - split; auto. apply get_this_var_mapping_app_null_last.
  - split; auto. apply get_this_var_mapping_update; auto.
  - split; auto. apply get_this_var_mapping_update; auto.
  - split; auto. apply get_this_var_mapping_update; auto.
  - split; auto. apply get_this_var_mapping_update; auto.
  - destruct (IHeval_stmt1 eq_refl _ _ _ _ Htype1) as (H1 & H2 & H3).
    destruct (IHeval_stmt2 eq_refl _ _ _ _ Htype2) as (H4 & H5 & H6).
    repeat split; congruence.
Qed.

(** A successful evaluation keeps the activation's qualifier arguments. *)
Lemma eval_stmt_qargs : forall CT rΓ h s res rΓ' h',
  eval_stmt CT rΓ h s res rΓ' h' -> res = OK -> qargs rΓ' = qargs rΓ.
Proof.
  intros CT rΓ h s res rΓ' h' H.
  induction H; intros Hr; try discriminate; subst; simpl; try reflexivity.
  rewrite IHeval_stmt2; auto.
Qed.

(* ------------------TYPES WITHOUT METHOD VARIABLES------------------*)

Section wf_stype_ind'.
  Variable CT : class_table.
  Variable Δ : tv_env.
  Variable P : bool -> qualified_type -> Prop.
  Hypothesis Hclass : forall top q0 C Ts def,
    find_class CT C = Some def ->
    Forall (wf_stype CT Δ false) Ts ->
    Forall (P false) Ts ->
    P top (TClass q0 C Ts).
  Hypothesis Hvar : forall top u o n B,
    tv_bound Δ o n = Some B -> tv_use_ok Δ top u -> P top (TVar u o n).
  Hypothesis Hhead : forall top n C Ts,
    n < qparams Δ ->
    wf_stype CT Δ top (TClass RO C Ts) ->
    P top (TClass RO C Ts) ->
    P top (THead n C Ts).

  Fixpoint wf_stype_ind' top T (H : wf_stype CT Δ top T) : P top T :=
    match H with
    | wfs_class _ _ top q0 C Ts def Hfind _ _ Hargs _ =>
        Hclass top q0 C Ts def Hfind Hargs
          ((fix go l (Hl : Forall (wf_stype CT Δ false) l) : Forall (P false) l :=
              match Hl with
              | Forall_nil _ => Forall_nil _
              | @Forall_cons _ _ x l' Hx Hr =>
                  Forall_cons x (wf_stype_ind' false x Hx) (go l' Hr)
              end) Ts Hargs)
    | wfs_var _ _ top u o n B Hb Hu => Hvar top u o n B Hb Hu
    | wfs_head _ _ top n C Ts Hb Hv =>
        Hhead top n C Ts Hb Hv (wf_stype_ind' top _ Hv)
    end.
End wf_stype_ind'.

(** A type that is well formed where no method type variable is declared does
    not depend on the method type arguments. *)
Lemma dyn_no_method_vars : forall CT Δ top T,
  wf_stype CT Δ top T ->
  (method_bounds Δ, qparams Δ) = ([], 0) ->
  forall qctx ca ma ka, dyn qctx ca ma ka T = dyn qctx ca [] [] T.
Proof.
  intros CT Δ top T H. induction H using wf_stype_ind'; intros Hmq qctx ca ma ka;
    pose proof Hmq as Hmq'; injection Hmq' as Hm Hq0.
  - simpl. f_equal. induction H1; simpl; auto.
    inversion H0; subst. f_equal; auto.
  - destruct u as [| |m];
      [| |exfalso; simpl in H0; rewrite Hq0 in H0; inversion H0];
      (unfold tv_bound in H; destruct o; simpl in *;
       [reflexivity | rewrite Hm in H; destruct n; discriminate]).
  - exfalso. rewrite Hq0 in H. inversion H.
Qed.

Lemma class_bounds_wf : forall CT D defD,
  wf_class_table CT ->
  find_class CT D = Some defD ->
  Forall (wf_stypeuse CT (mk_tv_env (ctparams (signature defD)) [] AbstractState 0))
    (ctparams (signature defD)).
Proof.
  intros CT D defD Hwf Hfind.
  pose proof (wf_class_table_class _ _ _ Hwf Hfind) as Hcls.
  inversion Hcls; subst.
  - rewrite Hno_tparams. constructor.
  - eapply Forall_impl; [|exact H]. intros B [_ HB]. exact HB.
Qed.

Lemma Forall2_Forall_r_impl : forall {A B : Type} (P R : A -> B -> Prop)
    (Q : B -> Prop) l1 l2,
  Forall2 P l1 l2 -> Forall Q l2 ->
  (forall a b, P a b -> Q b -> R a b) ->
  Forall2 R l1 l2.
Proof.
  intros A B P R Q l1 l2 H. induction H; intros HQ Himp; constructor;
    inversion HQ; subst; auto.
Qed.

Lemma Forall2_Forall_l : forall {A B : Type} (P : A -> B -> Prop)
    (Q : A -> Prop) l1 l2,
  Forall2 P l1 l2 -> (forall a b, P a b -> Q a) -> Forall Q l1.
Proof.
  intros A B P Q l1 l2 H Himp. induction H; constructor; eauto.
Qed.

(* ------------------OVERRIDING------------------*)

Lemma Forall2_map_right : forall {A B B' : Type} (P : A -> B -> Prop)
    (Q : A -> B' -> Prop) (f : B -> B') l1 l2,
  Forall2 P l1 l2 ->
  (forall a b, P a b -> Q a (f b)) ->
  Forall2 Q l1 (map f l2).
Proof.
  intros. induction H; simpl; constructor; auto.
Qed.

Lemma dyn_map_qual_eq : forall f qa qb ca ma ka T,
  (forall q0, dynq qb (f q0) = dynq qa q0) ->
  dyn qb ca ma ka (map_qual f T) = dyn qa ca ma ka T.
Proof.
  intros f qa qb ca ma ka T Hq.
  induction T using qualified_type_ind'; simpl.
  - rewrite Hq. f_equal. rewrite map_map.
    induction H; simpl; auto. f_equal; auto.
  - destruct u; simpl; auto. rewrite Hq. reflexivity.
  - f_equal. rewrite map_map.
    induction H; simpl; auto. f_equal; auto.
Qed.

Lemma dynq_class_adapt : forall qr qc q0,
  vpa_mutability_runtime_bound_agree qr qc = true ->
  dynq (qr2q qr) (vpa_q AbstractState (qc2q qc) q0) = dynq (qr2q qr) q0.
Proof.
  intros [] [] []; simpl; intros H; try reflexivity; discriminate.
Qed.

(** Adapting through the class's own declared mutability changes nothing for
    an object of that class. *)
Lemma dyn_class_adapt : forall qr qc ca ma ka T,
  vpa_mutability_runtime_bound_agree qr qc = true ->
  dyn (qr2q qr) ca ma ka (adapt AbstractState (qc2q qc) T) = dyn (qr2q qr) ca ma ka T.
Proof.
  intros. unfold adapt. apply dyn_map_qual_eq.
  intros q0. apply dynq_class_adapt; auto.
Qed.

Lemma dyn_method_var_types : forall qctx ca ma ka,
  map (dyn qctx ca ma ka) (method_var_types (length ma)) = ma.
Proof.
  intros. unfold method_var_types. rewrite map_map. simpl.
  apply map_nth_default_seq.
Qed.

Lemma map_qnth_seq : forall ka, map (qnth ka) (seq 0 (length ka)) = ka.
Proof.
  unfold qnth. induction ka as [|a ka IH]; simpl; auto.
  f_equal. rewrite <- seq_shift. rewrite map_map. exact IH.
Qed.

(** The identity qualifier arguments read as the activation's own. *)
Lemma rqarg_qvar_args : forall qctx ka,
  map (rqarg qctx ka) (qvar_args (length ka)) = ka.
Proof.
  intros. unfold qvar_args. rewrite map_map. simpl. apply map_qnth_seq.
Qed.

Lemma super_inst_exists : forall CT qh C Rs D Vs,
  rsuper_inst CT qh C Rs D Vs ->
  forall mt q0 Ts, exists Ws, super_inst CT mt q0 C Ts D Ws.
Proof.
  intros CT qh C Rs D Vs H. induction H; intros mt q0 Ts.
  - exists Ts. apply si_refl.
  - destruct (IHrsuper_inst mt q0
                (map (subst Ts [] []) (map (adapt mt q0) Ss))) as [Ws HW].
    exists Ws. eapply si_step; eauto.
Qed.

(** A static superclass view read through a qualifier that the object reads
    exactly is matched exactly at runtime. *)
Lemma super_inst_dyn_exact : forall CT mt qx C Ts D Vs,
  super_inst CT mt qx C Ts D Vs ->
  forall qo ca ma ka,
    (forall q0, dynq qo (vpa_q mt qx q0) = dynq qo q0) ->
    rsuper_inst CT qo C (map (dyn qo ca ma ka) Ts) D (map (dyn qo ca ma ka) Vs).
Proof.
  intros CT mt qx C Ts D Vs H. induction H; intros qo ca ma ka Hq.
  - apply rsi_refl.
  - eapply rsi_step; eauto.
    assert (Heq : map (dyn qo ca ma ka)
                    (map (subst Ts [] []) (map (adapt mt qx) Ss)) =
                  map (dyn qo (map (dyn qo ca ma ka) Ts) [] []) Ss).
    { rewrite map_dyn_subst. simpl. rewrite map_map. apply map_ext.
      intros T. unfold adapt. apply dyn_map_qual_eq; auto. }
    rewrite <- Heq. apply IHsuper_inst; auto.
Qed.

(** What static subtyping says about the head of a class type and of a class
    type under a qualifier parameter. *)
Lemma sub_head_inv : forall CT Δ T U,
  qualified_type_subtype CT Δ T U ->
  (forall q1 C Ts, T = TClass q1 C Ts ->
     (exists q2 D Us, U = TClass q2 D Us /\ (q1 = q2 \/ q2 = RO \/ q1 = Bot)) \/
     (q1 = Bot /\ exists n D Us, U = THead n D Us)) /\
  (forall n C Ts, T = THead n C Ts ->
     (exists D Us, U = THead n D Us) \/ (exists D Us, U = TClass RO D Us)).
Proof.
  intros CT Δ T U H. induction H; split;
    try (intros ? ? ? E; discriminate E).
  - intros qa Ca Tsa E. inversion E; subst. left.
    eexists _, _, _. split; [reflexivity|]. inversion Hqsub; subst; auto.
  - intros qa Ca Tsa E. inversion E; subst. left. eauto 8.
  - intros n0 C0 Ts0 E. inversion E; subst. right. eauto.
  - intros n0 C0 Ts0 E. inversion E; subst. left. eauto.
  - intros n0 C0 Ts0 E. inversion E; subst. left. eauto.
  - intros qa Ca Tsa E. inversion E; subst. right. split; eauto 6.
  - intros qa Ca Tsa E.
    destruct IHqualified_type_subtype1 as [IH1 _].
    destruct IHqualified_type_subtype2 as [IH2c IH2h].
    destruct (IH1 _ _ _ E) as [(q2 & D & Us & -> & Hq) | (-> & n & D & Us & ->)].
    + destruct (IH2c _ _ _ eq_refl)
        as [(q3 & E3 & Ws & -> & Hq3) | (-> & n & E3 & Ws & ->)].
      * left. eexists _, _, _. split; [reflexivity|].
        destruct Hq as [-> | [-> | ->]]; auto.
        destruct Hq3 as [<- | [-> | Hx]]; auto. discriminate.
      * right. split; eauto 6.
        destruct Hq as [-> | [Hx | ->]]; auto. discriminate.
    + destruct (IH2h _ _ _ eq_refl) as [(E3 & Ws & ->) | (E3 & Ws & ->)].
      * right. split; eauto 6.
      * left. eexists _, _, _. split; [reflexivity|]. auto.
  - intros n0 C0 Ts0 E.
    destruct IHqualified_type_subtype1 as [_ IH1].
    destruct IHqualified_type_subtype2 as [IH2c IH2h].
    destruct (IH1 _ _ _ E) as [(D & Us & ->) | (D & Us & ->)].
    + exact (IH2h _ _ _ eq_refl).
    + right.
      destruct (IH2c _ _ _ eq_refl)
        as [(q3 & E3 & Ws & -> & Hq3) | (Hx & _)]; [|discriminate].
      destruct Hq3 as [<- | [-> | Hx]]; eauto. discriminate.
Qed.

(** The receiver of a declaration is under the qualifier parameter [n], or is
    one that no object inhabits. *)
Definition recv_slot (n : nat) (R : qualified_type) : Prop :=
  (exists C a, R = THead n C a) \/ (exists C a, R = TClass Bot C a).

Lemma nth_error_qvar_args : forall k n a,
  nth_error (qvar_args k) n = Some a -> a = QVar n.
Proof.
  intros k n a H. unfold qvar_args in H. rewrite nth_error_map in H.
  destruct (nth_error (seq 0 k) n) as [i|] eqn:Hi; [|discriminate].
  inversion H; subst.
  assert (Hlt : n < length (seq 0 k)) by (apply nth_error_Some; congruence).
  rewrite length_seq in Hlt.
  apply (nth_error_nth _ _ 0) in Hi.
  rewrite seq_nth in Hi; try exact Hlt.
  simpl in Hi. subst. reflexivity.
Qed.

Lemma vpa_as_bot : forall qc q1,
  vpa_q AbstractState (qc2q qc) q1 = Bot -> q1 = Bot.
Proof. intros [] []; simpl; congruence. Qed.

(** What the override check on receivers gives. *)
Lemma recv_override_facts : forall CT Δ qc Vs k kq R R',
  ((exists q1 C1 a1, R = TClass q1 C1 a1) \/
   (exists n1 C1 a1, R = THead n1 C1 a1)) ->
  ((exists q2 C2 a2, R' = TClass q2 C2 a2) \/
   (exists n2 C2 a2, R' = THead n2 C2 a2)) ->
  qualified_type_subtype CT Δ
    (rebase (member_type AbstractState (qc2q qc) Vs (method_var_types k)
               (qvar_args kq) R) R') R' ->
  (forall q1 C1 a1 q2 C2 a2, R = TClass q1 C1 a1 -> R' = TClass q2 C2 a2 ->
     vpa_q AbstractState (qc2q qc) q1 = q2 \/ q2 = RO \/
     vpa_q AbstractState (qc2q qc) q1 = Bot) /\
  (forall n1 C1 a1 q2 C2 a2, R = THead n1 C1 a1 ->
     R' = TClass q2 C2 a2 -> q2 = RO) /\
  (forall n, recv_slot n R' -> recv_slot n R).
Proof.
  intros CT Δ qc Vs k kq R R' HR HR' Hsub.
  assert (Hview : forall n1 C1 a1,
            (exists a, member_type AbstractState (qc2q qc) Vs (method_var_types k)
                         (qvar_args kq) (THead n1 C1 a1) = THead n1 C1 a) \/
            (exists a, member_type AbstractState (qc2q qc) Vs (method_var_types k)
                         (qvar_args kq) (THead n1 C1 a1) = TClass RO C1 a)).
  { intros n1 C1 a1. unfold member_type, adapt. cbn [map_qual subst].
    destruct (nth_error (qvar_args kq) n1) as [a|] eqn:Hn.
    - rewrite (nth_error_qvar_args _ _ _ Hn). left. eexists. reflexivity.
    - right. eexists. reflexivity. }
  refine (conj _ (conj _ _)).
  - intros q1 C1 a1 q2 C2 a2 -> ->.
    unfold member_type, adapt in Hsub. cbn [map_qual subst rebase rehead] in Hsub.
    destruct (proj1 (sub_head_inv _ _ _ _ Hsub) _ _ _ eq_refl)
      as [(q3 & D & Us & E & Hq) | (_ & n & D & Us & E)]; [|discriminate].
    inversion E; subst. exact Hq.
  - intros n1 C1 a1 q2 C2 a2 -> ->.
    destruct (Hview n1 C1 a1) as [[a Ha] | [a Ha]]; rewrite Ha in Hsub;
      cbn [rebase rehead] in Hsub.
    + destruct (proj2 (sub_head_inv _ _ _ _ Hsub) _ _ _ eq_refl)
        as [(D & Us & E) | (D & Us & E)]; [discriminate|].
      inversion E; reflexivity.
    + destruct (proj1 (sub_head_inv _ _ _ _ Hsub) _ _ _ eq_refl)
        as [(q3 & D & Us & E & Hq) | (Hx & _)]; [|discriminate].
      inversion E; subst. destruct Hq as [<- | [-> | Hx]]; auto. discriminate.
  - intros n Hslot.
    assert (Hsub' : exists C a,
              (R' = THead n C a \/ R' = TClass Bot C a) /\
              forall T, rebase T R' = rehead T C a).
    { destruct Hslot as [(C & a & ->) | (C & a & ->)]; exists C, a; split; auto. }
    destruct Hsub' as (C & a & HR'eq & Hreb). rewrite Hreb in Hsub.
    destruct HR as [(q1 & C1 & a1 & ->) | (n1 & C1 & a1 & ->)].
    + unfold member_type, adapt in Hsub. cbn [map_qual subst rehead] in Hsub.
      right. exists C1, a1. f_equal.
      destruct (proj1 (sub_head_inv _ _ _ _ Hsub) _ _ _ eq_refl)
        as [(q3 & D & Us & E & Hq) | (Hb & _)].
      * destruct HR'eq as [-> | ->]; [discriminate|]. inversion E; subst.
        destruct Hq as [Hq | [Hq | Hq]]; try discriminate;
          exact (vpa_as_bot _ _ Hq).
      * exact (vpa_as_bot _ _ Hb).
    + destruct (Hview n1 C1 a1) as [[a0 Ha] | [a0 Ha]]; rewrite Ha in Hsub;
        cbn [rehead] in Hsub.
      * destruct (proj2 (sub_head_inv _ _ _ _ Hsub) _ _ _ eq_refl)
          as [(D & Us & E) | (D & Us & E)].
        -- destruct HR'eq as [-> | ->]; [|discriminate]. inversion E; subst.
           left. eauto.
        -- destruct HR'eq as [-> | ->]; discriminate.
      * destruct (proj1 (sub_head_inv _ _ _ _ Hsub) _ _ _ eq_refl)
          as [(q3 & D & Us & E & Hq) | (Hx & _)]; [|discriminate].
        destruct HR'eq as [-> | ->]; [discriminate|]. inversion E; subst.
        destruct Hq as [Hq | [Hq | Hq]]; discriminate.
Qed.

Lemma receiver_shape_cases : forall CT C T,
  receiver_shape CT C T ->
  (exists q1 C1 a1, T = TClass q1 C1 a1) \/
  (exists n1 C1 a1, T = THead n1 C1 a1).
Proof. intros CT C T (args & _ & [[q0 ->] | [n ->]]); [left | right]; eauto. Qed.

Lemma Forall2_map_r_nth : forall (A B C : Type) (P : A -> C -> Prop)
    (f g : B -> C) l a,
  Forall2 P l (map f a) ->
  (forall i x T, nth_error l i = Some x -> nth_error a i = Some T ->
     P x (f T) -> P x (g T)) ->
  Forall2 P l (map g a).
Proof.
  intros A B C P f g l. induction l as [|x l IH]; intros [|T a] H Hp;
    inversion H; subst; constructor.
  - apply (Hp 0); auto.
  - apply IH; auto. intros i. apply (Hp (S i)).
Qed.

Lemma Forall2_map_map_nth : forall (A A' B C C' : Type)
    (P : A -> C -> Prop) (Q : A' -> C' -> Prop)
    (e : A' -> A) (f : B -> C) (g : B -> C') l a,
  Forall2 P (map e l) (map f a) ->
  (forall i x T, nth_error l i = Some x -> nth_error a i = Some T ->
     P (e x) (f T) -> Q x (g T)) ->
  Forall2 Q l (map g a).
Proof.
  intros A A' B C C' P Q e f g l. induction l as [|x l IH]; intros [|T a] H Hp;
    simpl in H; inversion H; subst; constructor.
  - apply (Hp 0); auto.
  - apply IH; auto. intros i. apply (Hp (S i)).
Qed.

(** A written qualifier on a receiver argument that the caller knows means
    the same for the caller and for the receiver object. *)
Lemma recv_arg_q : forall mt (qr qctx : q_r) qy u,
  head_ok qr (dynq (qr2q qctx) qy) ->
  vpa_q mt qy u <> Lost ->
  dynq (qr2q qctx) (vpa_recv qy u) = dynq (qr2q qr) u /\
  dynq (qr2q qr) u <> Lost.
Proof.
  intros mt qr qctx qy u Hh Hn.
  destruct mt, qr, qctx, qy, u; simpl in *; unfold head_ok in Hh; simpl in Hh;
    try (exfalso; apply Hn; reflexivity);
    try (destruct Hh as [Hh | [Hh | Hh]]; discriminate);
    split; try reflexivity; discriminate.
Qed.

(** The arguments of a class type or of a class type under a qualifier
    parameter survive receiver adaptation, substitution and resolution. *)
Lemma dyn_member_recv_args : forall qctx ca ma ka qy Vs Us Qs R,
  (exists q1 C1 a1, R = TClass q1 C1 a1) \/ (exists n1 C1 a1, R = THead n1 C1 a1) ->
  exists q0 C0,
    (exists a1, targs R = a1 /\ (R = TClass q0 C0 a1 \/ exists n, R = THead n C0 a1)) /\
    exists q2,
    dyn qctx ca ma ka (member_recv qy Vs Us Qs R) =
    RClass q2 C0
      (map (fun T => dyn qctx ca ma ka
                       (subst Vs Us Qs (map_qual (vpa_recv qy) T))) (targs R)).
Proof.
  intros qctx ca ma ka qy Vs Us Qs R [(q1 & C1 & a1 & ->) | (n1 & C1 & a1 & ->)].
  - exists q1, C1. split; [exists a1; auto|].
    unfold member_recv. cbn [map_qual subst dyn targs]. eexists.
    rewrite !map_map. reflexivity.
  - exists RO, C1. split; [exists a1; split; eauto|].
    unfold member_recv. cbn [map_qual subst targs].
    destruct (nth_error Qs n1) as [[ql | m]|]; unfold qhead; cbn [dyn]; eexists;
      rewrite !map_map; reflexivity.
Qed.

(** The receiver object satisfies what the declared receiver of the
    statically selected method asks of its type arguments. *)
Lemma static_radmit : forall CT Δ h mt (qr qctx : q_r) ca0 ma0 ka0 Ty qy Vs Us Qs R
    ly Co Ro fso D caD,
  wf_class_table CT ->
  frame_bounds_ok CT Δ (qr2q qctx) ca0 ma0 ka0 ->
  qualified_type_subtype CT Δ Ty (member_recv qy Vs Us Qs R) ->
  recv_args_known mt qy R ->
  receiver_shape CT D R ->
  loc_has_rtype CT h ly (dyn (qr2q qctx) ca0 ma0 ka0 Ty) ->
  runtime_getObj h ly = Some (mkObj (mkruntime_type qr Co Ro) fso) ->
  head_ok qr (dynq (qr2q qctx) qy) ->
  rsuper_inst CT (qr2q qr) Co Ro D caD ->
  radmit (qr2q qr) caD (map (rqarg (qr2q qctx) ka0) Qs) R.
Proof.
  intros CT Δ h mt qr qctx ca0 ma0 ka0 Ty qy Vs Us Qs R ly Co Ro fso D caD
    Hct Hfb Hsub Hrcv_args Hrecv Hyty Hoy Hhead HsupD.
  intros ma1.
  pose proof (loc_has_rtype_sub _ _ _ _ _ Hyty
                (subtype_dyn _ _ _ _ _ _ _ _ (qr2q_concrete _) Hfb Hsub)) as Hrt.
  destruct (dyn_member_recv_args (qr2q qctx) ca0 ma0 ka0
              qy Vs Us Qs _ (receiver_shape_cases _ _ _ Hrecv))
    as (q0 & C0 & (a1 & Ha1 & HR) & q2 & Hdyn).
  rewrite Hdyn in Hrt. unfold loc_has_rtype in Hrt. rewrite Hoy in Hrt.
  simpl in Hrt. destruct Hrt as (_ & Vs0 & Hsup0 & Hle0).
  destruct Hrecv as (args1 & [Hlen1 Hsh1] & Hcase).
  assert (HC0 : C0 = D /\ targs R = args1).
  { destruct Hcase as [[qx Hx] | [nx Hx]]; rewrite Hx in HR; rewrite Hx;
      destruct HR as [HR | [nn HR]]; inversion HR; subst; auto. }
  destruct HC0 as [HC0 Hta]. subst C0. rewrite Hta in Hle0. rewrite Hta.
  assert (Vs0 = caD) by (eapply rsuper_inst_deterministic; eauto). subst Vs0.
  eapply Forall2_map_r_nth; [exact Hle0|].
  intros i rx T Hrx HT Hrel.
  destruct (Hsh1 i T HT) as [u0 ->].
  destruct u0 as [|u0|mu0].
  - simpl. rewrite Hrx. apply rarg_sub_refl.
  - assert (Hin : List.In (TVar (TVQual u0) ClassVar i) (targs R)).
    { rewrite Hta. eapply nth_error_In; eauto. }
    destruct (recv_arg_q mt qr qctx qy u0 Hhead (Hrcv_args _ _ _ Hin))
      as [Heq Hnl].
    cbn [map_qual] in Hrel. rewrite dyn_subst in Hrel. simpl in Hrel.
    rewrite Heq in Hrel.
    simpl. rewrite Hrx. destruct rx as [q1 Cx ax].
    destruct (match nth_error (map (dyn (qr2q qctx) ca0 ma0 ka0) Vs) i
              with Some R0 => R0 | None => default_rtype end) as [qw Cw aw].
    simpl in Hrel. inversion Hrel; subst.
    simpl. apply ras_class; [|apply Forall2_rarg_sub_refl].
    destruct Hq as [Hq | [Hq _]]; [left; exact Hq | contradiction].
  - (* under a qualifier parameter: the caller checked the stored argument
       against the qualifier it supplies for that parameter *)
    cbn [map_qual] in Hrel. rewrite dyn_subst in Hrel. simpl in Hrel.
    simpl. rewrite Hrx. destruct rx as [q1 Cx ax].
    destruct (match nth_error (map (dyn (qr2q qctx) ca0 ma0 ka0) Vs) i
              with Some R0 => R0 | None => default_rtype end) as [qw Cw aw].
    simpl in Hrel. inversion Hrel; subst.
    simpl. apply ras_class; [exact Hq | apply Forall2_rarg_sub_refl].
Qed.

Definition recv_head (T : qualified_type) : q :=
  match T with
  | TClass q0 _ _ => q0
  | TVar _ _ _ => RO
  | THead _ _ _ => RO
  end.

(** The declaration selected at run time, with signature [sig'] and the
    receiver's class arguments [ca'] at its declaring class, can stand in for
    the declaration the caller saw, with signature [sig] and class arguments
    [ca].  Stated on runtime types for one receiver mutability: method type
    arguments that fit the caller's declaration fit the selected one, values
    that inhabit the caller's parameter types inhabit the selected ones, and
    a result of the selected return type inhabits the caller's return type. *)
Definition sem_ref (CT : class_table) (qr : q_r)
    (ca' : list rtype) (sig' : method_sig)
    (ca : list rtype) (sig : method_sig) : Prop :=
  mscope sig' = mscope sig /\
  (((head_ok qr (dynq (qr2q qr) (recv_head (mreceiver sig))) ->
     head_ok qr (dynq (qr2q qr) (recv_head (mreceiver sig')))) /\
    (forall ka, length ka = mqparams sig ->
       radmit (qr2q qr) ca ka (mreceiver sig) ->
       radmit (qr2q qr) ca' ka (mreceiver sig'))) /\
   (forall n, recv_slot n (mreceiver sig') -> recv_slot n (mreceiver sig)) /\
   mqparams sig' = mqparams sig) /\
  forall ma ka,
    length ka = mqparams sig ->
    rbounds_ok CT (qr2q qr) ca ma ka ma (mtparams sig) ->
    rbounds_ok CT (qr2q qr) ca' ma ka ma (mtparams sig') /\
    Forall2
      (fun P P' => forall h loc,
         loc_has_rtype CT h loc (dyn (qr2q qr) ca ma ka P) ->
         loc_has_rtype CT h loc (dyn (qr2q qr) ca' ma ka P'))
      (mparams sig) (mparams sig') /\
    (forall h loc,
       loc_has_rtype CT h loc (dyn (qr2q qr) ca' ma ka (mret sig')) ->
       loc_has_rtype CT h loc (dyn (qr2q qr) ca ma ka (mret sig))).

Lemma sem_ref_refl : forall CT qr ca sig, sem_ref CT qr ca sig ca sig.
Proof.
  intros. refine (conj eq_refl
                    (conj (conj (conj (fun H => H) (fun ka _ H => H))
                             (conj (fun n H => H) eq_refl)) _)).
  intros ma ka Hk Hb. refine (conj Hb (conj _ (fun h loc H => H))).
  induction (mparams sig); constructor; auto.
Qed.

Lemma sem_ref_trans : forall CT qr ca1 s1 ca2 s2 ca3 s3,
  sem_ref CT qr ca1 s1 ca2 s2 -> sem_ref CT qr ca2 s2 ca3 s3 ->
  sem_ref CT qr ca1 s1 ca3 s3.
Proof.
  intros CT qr ca1 s1 ca2 s2 ca3 s3 (Hs12 & ([Hh12 Ha12] & Hsl12 & Hq12) & H12)
    (Hs23 & ([Hh23 Ha23] & Hsl23 & Hq23) & H23).
  refine (conj _ (conj _ _)).
  - congruence.
  - split; [split; [auto|]|].
    + intros ka Hk Ha. apply (Ha12 ka); [congruence | exact (Ha23 ka Hk Ha)].
    + split; [auto | congruence].
  - intros ma ka Hk Hb3.
    destruct (H23 ma ka Hk Hb3) as (Hb2 & Hp23 & Hr23).
    assert (Hk2 : length ka = mqparams s2) by congruence.
    destruct (H12 ma ka Hk2 Hb2) as (Hb1 & Hp12 & Hr12).
    refine (conj Hb1 (conj _ _)).
    + eapply Forall2_compose; [exact Hp23 | exact Hp12 |].
      intros P3 P2 P1 Ha Hb h loc Hl. auto.
    + intros h loc Hl. auto.
Qed.

(** One override step, from the declared override check of the overriding
    method. *)
Lemma override_step : forall CT qr D' ca' def' mdef' P Ss D1 mdef1 ca1,
  wf_class_table CT ->
  wf_rtypeuse CT (mkruntime_type qr D' ca') ->
  find_class CT D' = Some def' ->
  super (signature def') = Some (P, Ss) ->
  wf_method CT D' mdef' ->
  FindMethodWithName CT P (mname (msignature mdef')) D1 mdef1 ->
  rsuper_inst CT (qr2q qr) D' ca' D1 ca1 ->
  sem_ref CT qr ca' (msignature mdef') ca1 (msignature mdef1).
Proof.
  intros CT qr D' ca' def' mdef' P Ss D1 mdef1 ca1
    Hct Hrt Hfind Hsuper Hwm Hfm Hrs.
  unfold wf_rtypeuse in Hrt. simpl in Hrt. rewrite Hfind in Hrt.
  destruct Hrt as (Hagree & Hlf & Hbnd).
  set (qC := class_qualifier (signature def')) in *.
  destruct (super_inst_exists _ _ _ _ _ _ Hrs AbstractState (qc2q qC)
              (class_var_types (length (ctparams (signature def')))))
    as [Vs Hsi].
  pose proof Hwm as (_ & _ & _ & _ & Hovr & _).
  pose proof (Hovr def' P Ss D1 mdef1 Vs Hfind Hsuper Hfm Hsi) as Hcompat.
  assert (Hlen_ca : length (ctparams (signature def')) = length ca').
  { symmetry. apply (Forall2_length Hbnd). }
  assert (Hca1 : forall ma ka, ca1 = map (dyn (qr2q qr) ca' ma ka) Vs).
  { intros ma ka.
    pose proof (super_inst_dyn_exact _ _ _ _ _ _ _ Hsi (qr2q qr) ca' ma ka
                  (fun q0 => dynq_class_adapt qr qC q0 Hagree)) as Hex.
    rewrite Hlen_ca in Hex. rewrite dyn_class_var_types in Hex.
    eapply rsuper_inst_deterministic; eauto. }
  set (sig1 := msignature mdef1) in *.
  set (sig' := msignature mdef') in *.
  assert (Hview : forall ma ka T,
            length ma = length (mtparams sig1) ->
            length ka = mqparams sig1 ->
            dyn (qr2q qr) ca' ma ka
              (member_type AbstractState (qc2q qC) Vs
                 (method_var_types (length (mtparams sig1)))
                 (qvar_args (mqparams sig1)) T) =
            dyn (qr2q qr) ca1 ma ka T).
  { intros ma ka T Hlen Hlenk. unfold member_type. rewrite dyn_subst.
    rewrite <- Hlen. rewrite dyn_method_var_types.
    rewrite <- Hlenk. rewrite rqarg_qvar_args. rewrite <- (Hca1 ma ka).
    apply dyn_class_adapt; auto. }
  destruct Hcompat as (_ & Hscope & [Hmtp Hmqp] & Hret & Hpar & Hrcv & Hadm).
  pose proof Hwm as ((Hshape' & _) & _).
  pose proof (find_method_wf _ _ _ _ _ Hct Hfm) as ((Hshape1 & _) & _).
  destruct (recv_override_facts _ _ _ _ _ _ _
              _ (receiver_shape_cases _ _ _ Hshape1)
              (receiver_shape_cases _ _ _ Hshape') Hrcv)
    as (Hcc & Hhc & Hslot).
  refine (conj Hscope (conj (conj (conj _ _) (conj Hslot Hmqp)) _)).
  2:{ fold sig1 sig'. intros ka Hk Ha1.
      apply (Hadm qr ca' ka).
      - intros Hq. fold qC in Hq. rewrite Hq in Hagree.
        destruct qr; simpl in Hagree; [reflexivity | discriminate].
      - intros Hq. fold qC in Hq. rewrite Hq in Hagree.
        destruct qr; simpl in Hagree; [discriminate | reflexivity].
      - simpl. unfold class_tparams. rewrite Hfind. symmetry. exact Hlen_ca.
      - exact Hk.
      - rewrite <- (Hca1 [] []). exact Ha1. }
  - fold sig1 sig'.
    destruct (receiver_shape_cases _ _ _ Hshape') as
      [(q2 & C2 & a2 & Hr2) | (n2 & C2 & a2 & Hr2)];
      fold sig' in Hr2; rewrite Hr2;
      [|intros _; simpl; unfold head_ok; auto].
    destruct (receiver_shape_cases _ _ _ Hshape1) as
      [(q1 & C1 & a1 & Hr1) | (n1 & C1 & a1 & Hr1)];
      fold sig1 in Hr1; rewrite Hr1.
    + simpl. intros Hh.
      rewrite <- (dynq_class_adapt qr qC q1 Hagree) in Hh.
      destruct (Hcc _ _ _ _ _ _ Hr1 Hr2) as [Hq | [-> | Hq]].
      * rewrite <- Hq. exact Hh.
      * unfold head_ok. auto.
      * exfalso. fold qC in Hq. rewrite Hq in Hh. simpl in Hh.
        eapply head_ok_not_bot; eauto.
    + intros _. rewrite (Hhc _ _ _ _ _ _ Hr1 Hr2). simpl. unfold head_ok. auto.
  - intros ma ka Hk Hb1.
    assert (Hlen : length ma = length (mtparams sig1))
      by apply (Forall2_length Hb1).
    assert (Hb' : rbounds_ok CT (qr2q qr) ca' ma ka ma (mtparams sig')).
    { rewrite Hmtp. unfold rbounds_ok in *.
      eapply Forall2_map_right; [exact Hb1|].
      intros R B HR. simpl in *. rewrite Hview; auto. }
    assert (Hfb : frame_bounds_ok CT (method_tv_env CT D' sig') (qr2q qr) ca' ma ka).
    { apply frame_bounds_ok_of_rbounds; simpl; auto.
      unfold class_tparams. rewrite Hfind. unfold rbounds_ok in *.
      eapply Forall2_Forall_r_impl;
        [exact Hbnd | exact (class_bounds_wf _ _ _ Hct Hfind) |].
      intros R B HR HB. simpl in HR.
      rewrite (dyn_no_method_vars _ _ _ _ HB eq_refl). exact HR. }
    refine (conj Hb' (conj _ _)).
    + eapply Forall2_impl; [|exact Hpar].
      intros P1 P' Hsub h loc Hl. simpl in Hsub.
      eapply loc_has_rtype_sub;
        [|eapply subtype_dyn; eauto using qr2q_concrete].
      rewrite Hview; auto.
    + intros h loc Hl.
      pose proof (loc_has_rtype_sub _ _ _ _ _ Hl
                    (subtype_dyn _ _ _ _ _ _ _ _ (qr2q_concrete _) Hfb Hret)) as Hl'.
      rewrite Hview in Hl'; auto.
Qed.

Lemma base_subtype_le : forall CT C D,
  wf_class_table CT -> base_subtype CT C D -> D <= C.
Proof.
  intros CT C D Hwf H. induction H; auto.
  - specialize (IHbase_subtype1 Hwf). specialize (IHbase_subtype2 Hwf). lia.
  - unfold parent_lookup in Hparent.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
    destruct (wf_class_super_inv _ _ _ _ _ Hwf Hfind Hparent) as (sd & _ & Hlt & _).
    lia.
Qed.

Lemma find_rsuper_exists : forall CT C m D mdef,
  FindMethodWithName CT C m D mdef ->
  forall qh Rs, exists Vs, rsuper_inst CT qh C Rs D Vs.
Proof.
  intros CT C m D mdef H. induction H; intros qh Rs.
  - exists Rs. apply rsi_refl.
  - destruct (IHFindMethodWithName qh (map (dyn qh Rs [] []) Ss)) as [Vs HV].
    exists Vs. eapply rsi_step; eauto.
    unfold parent_lookup. rewrite Hfind. exact Hsuper.
Qed.

Lemma find_from_subclass : forall CT qh P Rs C Vs,
  rsuper_inst CT qh P Rs C Vs ->
  forall m D mdef,
    FindMethodWithName CT C m D mdef ->
    exists D1 mdef1, FindMethodWithName CT P m D1 mdef1.
Proof.
  intros CT qh P Rs C Vs H. induction H; intros m D0 mdef Hf.
  - eauto.
  - destruct (IHrsuper_inst m D0 mdef Hf) as (D1 & mdef1 & H1).
    unfold parent_lookup in Hparent.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
    destruct (gget_method (methods (body def)) m) as [md|] eqn:Hg.
    + exists C, md. eapply FOM_Here; eauto.
    + exists D1, mdef1. eapply FOM_Super; eauto.
Qed.

(** The declaration found from the receiver's class can stand in for the one
    found from any superclass of it. *)
Lemma lookup_refines : forall CT qr Co Ro C Rs1,
  wf_class_table CT ->
  rsuper_inst CT (qr2q qr) Co Ro C Rs1 ->
  wf_rtypeuse CT (mkruntime_type qr Co Ro) ->
  forall m D' mdef' D mdef ca' ca,
    FindMethodWithName CT Co m D' mdef' ->
    FindMethodWithName CT C m D mdef ->
    rsuper_inst CT (qr2q qr) Co Ro D' ca' ->
    rsuper_inst CT (qr2q qr) Co Ro D ca ->
    sem_ref CT qr ca' (msignature mdef') ca (msignature mdef).
Proof.
  intros CT qr Co Ro C Rs1 Hct H.
  remember (qr2q qr) as qo eqn:Hqo.
  induction H as [C Rs | C Rs P Ss D0 Vs Hparent Hrest IH];
    intros Hrt m D' mdef' D mdef ca' ca Hf' Hf Hs' Hs.
  - destruct (find_method_with_name_deterministic _ _ _ _ _ _ _ Hf' Hf) as [-> ->].
    assert (ca' = ca) by (eapply rsuper_inst_deterministic; eauto). subst.
    apply sem_ref_refl.
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
    + (* declared in the receiver's class: one override step, then recurse *)
      rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      assert (ca' = Rs).
      { eapply rsuper_inst_deterministic; [exact Hct | exact Hs' | apply rsi_refl]. }
      subst ca'.
      destruct (find_from_subclass _ _ _ _ _ _ Hrest _ _ _ Hf) as (D1 & mdef1 & HfP).
      destruct (find_rsuper_exists _ _ _ _ _ HfP (qr2q qr)
                  (map (dyn (qr2q qr) Rs [] []) Ss)) as [ca1 Hs1].
      eapply sem_ref_trans; [|eapply (IH HrtP); eauto].
      eapply override_step; eauto.
      * eapply find_method_wf; eauto.
      * rewrite (gget_method_name_consistent _ _ _ Hget_method). exact HfP.
      * eapply rsi_step; eauto.
    + (* inherited: recurse *)
      rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      rewrite Hsuper in Hparent'. inversion Hparent'; subst.
      pose proof (base_subtype_le _ _ _ Hct
                    (find_method_with_name_base _ _ _ _ _ Hparent_fmn)) as HleD'.
      assert (HsD' : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs [] []) Ss) D' ca').
      { inversion Hs'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      eapply (IH HrtP); eauto.
Qed.

(** A qualifier argument accepted by the checker is never unknown at run
    time. *)
Lemma rqarg_not_lost : forall Δ qctx ka a,
  concrete_q qctx ->
  Forall (fun q0 => q0 <> Lost) ka ->
  qarg_ok Δ a -> rqarg qctx ka a <> Lost.
Proof.
  intros Δ qctx ka [q0|m] Hc Hka Hok; simpl in *.
  - destruct Hc as [-> | ->]; destruct q0; simpl; congruence.
  - apply qnth_not_lost. exact Hka.
Qed.

Lemma map_rqarg_not_lost : forall Δ qctx ka Qs,
  concrete_q qctx ->
  Forall (fun q0 => q0 <> Lost) ka ->
  Forall (qarg_ok Δ) Qs ->
  Forall (fun q0 => q0 <> Lost) (map (rqarg qctx ka) Qs).
Proof.
  intros Δ qctx ka Qs Hc Hka H. induction H; simpl; constructor;
    eauto using rqarg_not_lost.
Qed.

(* ------------------CALL ENTRY------------------*)

(** Entering a well-typed call from a well-formed configuration yields a
    well-formed configuration for the body of the method selected at run
    time, and a result of that method's return type is a value of the call's
    destination type. *)
(** What the receiver check of a call says about the receiver object: its
    mutability may be seen through the declared receiver's qualifier, unless
    that is [RDM]; for a receiver under a qualifier parameter, through the
    qualifier supplied for it. *)
Lemma recv_head_typable : forall CT Δ h ly Ty qy Vs Us Qs R qctx ca ma ka o,
  frame_bounds_ok CT Δ (qr2q qctx) ca ma ka ->
  qualified_type_subtype CT Δ Ty (member_recv qy Vs Us Qs R) ->
  wf_r_typable CT h ly Ty qctx ca ma ka ->
  runtime_getObj h ly = Some o ->
  match R with
  | TClass q1 _ _ => q1 = RDM \/ head_ok (rqtype (rt_type o)) q1
  | THead n _ _ =>
      head_ok (rqtype (rt_type o)) (qnth (map (rqarg (qr2q qctx) ka) Qs) n)
  | TVar _ _ _ => True
  end.
Proof.
  intros CT Δ h ly Ty qy Vs Us Qs R qctx ca ma ka o Hfb Hsub Hty Ho.
  pose proof (wf_r_typable_subtype _ _ _ _ _ _ _ _ _ _ Hfb Hsub Hty) as Hbt.
  unfold wf_r_typable, member_recv in Hbt. rewrite dyn_subst in Hbt.
  destruct R as [q1 C args | u ow n | n C args]; [| exact I |].
  - simpl in Hbt. unfold loc_has_rtype in Hbt. rewrite Ho in Hbt.
    destruct Hbt as [Hh _].
    destruct q1; simpl in Hh; auto.
  - simpl in Hbt. unfold loc_has_rtype in Hbt. rewrite Ho in Hbt.
    exact (proj1 Hbt).
Qed.

Lemma call_entry : forall CT Δ sΓ rΓ h mt x m y Us Qs zs sΓ' ly cy D' mdef' vals rΓ',
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
  runtime_getVal rΓ y = Some (Iot ly) ->
  r_basetype h ly = Some cy ->
  FindMethodWithName CT cy m D' mdef' ->
  runtime_lookup_list rΓ zs = Some vals ->
  callee_env CT rΓ h ly D' Us Qs vals rΓ' ->
  exists ι o oy Tx,
    get_this_var_mapping (vars rΓ) = Some ι /\
    runtime_getObj h ι = Some o /\
    runtime_getObj h ly = Some oy /\
    static_getType sΓ x = Some Tx /\
    x <> 0 /\ sΓ' = sΓ /\
    frame_bounds_ok CT Δ (qr2q (rqtype (rt_type o))) (cargs rΓ) (margs rΓ) (qargs rΓ) /\
    wf_method CT D' mdef' /\
    wf_r_config CT (method_tv_env CT D' (msignature mdef'))
      (mreceiver (msignature mdef') :: mparams (msignature mdef')) rΓ' h /\
    get_this_var_mapping (vars rΓ') = Some ly /\
    (forall h' v,
       val_typable CT h' v (mret (msignature mdef'))
         (rqtype (rt_type oy)) (cargs rΓ') (margs rΓ') (qargs rΓ') ->
       val_typable CT h' v Tx (rqtype (rt_type o)) (cargs rΓ) (margs rΓ) (qargs rΓ)) /\
    method_scope_subtype (mscope (msignature mdef')) mt.
Proof.
  intros CT Δ sΓ rΓ h mt x m y Us Qs zs sΓ' ly cy D' mdef' vals rΓ'
    Hwf Htype Hvy Hbase Hfind Hvals Henv.
  inversion Htype; subst.
  pose proof (wf_r_config_qargs _ _ _ _ _ Hwf) as Hka.
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
  (* the receiver's class arguments at the statically selected declaration *)
  destruct (super_inst_dyn _ _ _ _ _ _ _ Hsuper (qr2q qr) (qr2q qctx)
              (cargs rΓ) (margs rΓ) (qargs rΓ) Rs1) as (caD & HsupX & HleX); auto.
  { intros q0. apply dynq_vpa_q_agree; auto using qr2q_concrete. }
  pose proof (rsuper_inst_trans _ _ _ _ _ _ Hsup1 _ _ HsupX) as HsupD.
  (* the declaration selected at run time refines the static one *)
  destruct (lookup_refines _ _ _ _ _ _ Hct Hsup1 Hrt_oy _ _ _ _ _ _ _
              Hfind Hfind_m Hsupc HsupD) as (Hsc & [Hhd Hslot] & Hma).
  pose proof (rsuper_wf _ _ _ _ _ _ Hct Hsupc Hrt_oy) as Hview.
  unfold wf_rtypeuse in Hview. simpl in Hview.
  destruct (find_class CT D') as [defD|] eqn:HfD; [|contradiction].
  destruct Hview as (_ & Hlf_ca & Hb_ca).
  pose proof (find_method_wf _ _ _ _ _ Hct Hfind) as Hwm'.
  pose proof (find_method_wf _ _ _ _ _ Hct Hfind_m) as Hwm.
  pose proof Hwm' as ((Hrecv' & _) & _ & _ & (sΓb & Tb & Hbody & _ & _) & _ & _).
  pose proof Hwm as ((Hrecv & _) & _).
  assert (Hlm' : Forall rlost_free margs').
  { apply map_dyn_lost_free; auto using qr2q_concrete. }
  assert (Hka' : Forall (fun q0 => q0 <> Lost) kargs').
  { eapply map_rqarg_not_lost; eauto using qr2q_concrete. }
  assert (Hklen : length kargs' = mqparams (msignature mdef)).
  { unfold kargs'. rewrite length_map. exact Hqargs_len. }
  assert (Hmrefl : Forall2 rarg_sub margs' margs') by apply Forall2_rarg_sub_refl.
  assert (Hctp : class_tparams CT D' = ctparams (signature defD)).
  { unfold class_tparams. rewrite HfD. reflexivity. }
  (* method type arguments fit the static declaration, hence the selected one *)
  assert (HbD : rbounds_ok CT (qr2q qr) caD margs' kargs' margs'
                  (mtparams (msignature mdef))).
  { unfold rbounds_ok. unfold margs' at 2.
    eapply Forall2_map_left; [exact Htargs_bnd|].
    intros U B [HlfB Hsub]. apply bound_sub_self in Hsub. simpl in HlfB, Hsub.
    pose proof (subtype_dyn _ _ _ _ _ _ _ _ (qr2q_concrete _) Hfb Hsub) as Hrs.
    unfold member_type in Hrs. rewrite dyn_subst in Hrs.
    rewrite (dyn_adapt_exact mt qr qctx qy caD
               (map (dyn (qr2q qctx) (cargs rΓ) (margs rΓ) (qargs rΓ)) Vs)
               margs' margs' kargs' B); auto.
    unfold margs', kargs'. rewrite <- dyn_subst.
    apply dyn_lost_free; auto using qr2q_concrete. }
  destruct (Hma margs' kargs' Hklen HbD) as (Hb' & Hpar_ref & Hret_ref).
  (* arguments and receiver in the callee's activation *)
  pose proof (lookup_list_typable _ _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_args Hvals)
    as Hvals_ty.
  assert (Hparams :
    Forall2 (fun v P =>
               match v with
               | Null_a => True
               | Iot loc => loc_has_rtype CT h loc (dyn (qr2q qr) caD margs' kargs' P)
               end) vals (mparams (msignature mdef))).
  { eapply Forall2_compose; [exact Hvals_ty | exact Harg_sub |].
    intros v A P Hv Hassign. simpl in Hv, Hassign.
    exact (assignable_to_member _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             qr caD margs' Hfb Hlc Hlm Hka Hassign Hv Hhead HleX Hmrefl). }
  assert (Hparams' :
    Forall2 (fun v P =>
               match v with
               | Null_a => True
               | Iot loc => loc_has_rtype CT h loc (dyn (qr2q qr) ca' margs' kargs' P)
               end) vals (mparams (msignature mdef'))).
  { eapply Forall2_compose; [exact Hparams | exact Hpar_ref |].
    intros v P P' Hv Hf. destruct v as [|loc]; auto. }
  assert (Hhead_static :
    head_ok qr (dynq (qr2q qr) (recv_head (mreceiver (msignature mdef))))).
  { destruct Hrecv as (args1 & _ & [[qr1 Hreq1] | [n1 Hreq1]]);
      [|rewrite Hreq1; simpl; unfold head_ok; auto].
    pose proof (recv_head_typable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hfb
                  Hrcv_sub Hyty Hoy) as Hrt.
    rewrite Hreq1 in Hrt. rewrite Hreq1. simpl in Hrt. simpl.
    destruct Hrt as [-> | Hh].
    - unfold head_ok. right. right. destruct qr; reflexivity.
    - destruct qr1; simpl; auto.
      unfold head_ok. right. right. destruct qr; reflexivity. }
  pose proof (proj1 Hhd Hhead_static) as Hhead_sel.
  (* the receiver object satisfies what the static declaration asks of its
     type arguments, hence what the selected one asks *)
  assert (Hadm_static : radmit (qr2q qr) caD kargs' (mreceiver (msignature mdef))).
  { exact (static_radmit CT Δ h mt qr qctx _ _ _ Ty qy Vs Us Qs _ ly Co Ro fso D caD
             Hct Hfb Hrcv_sub Hrcv_args Hrecv Hyty Hoy Hhead HsupD). }
  pose proof (proj2 Hhd kargs' Hklen Hadm_static) as Hadm_sel.
  assert (Hrecv_ty :
    loc_has_rtype CT h ly
      (dyn (qr2q qr) ca' margs' kargs' (mreceiver (msignature mdef')))).
  { destruct Hrecv' as (args2 & _ & [[qr2 Hreq2] | [n2 Hreq2]]).
    - rewrite Hreq2 in Hhead_sel. rewrite Hreq2. simpl in Hhead_sel.
      pose proof (Hadm_sel margs') as Hadm2. rewrite Hreq2 in Hadm2.
      simpl in Hadm2. simpl dyn.
      unfold loc_has_rtype. rewrite Hoy. simpl. split; [exact Hhead_sel|].
      exists ca'. split; [exact Hsupc | exact Hadm2].
    - (* the receiver takes its qualifier from a method type variable: the
         caller supplied it, and checked the receiver against it *)
      assert (Hs : recv_slot n2 (mreceiver (msignature mdef))).
      { apply Hslot. rewrite Hreq2. left. eauto. }
      assert (Hh : head_ok qr (qnth kargs' n2)).
      { pose proof (recv_head_typable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hfb
                      Hrcv_sub Hyty Hoy) as Hrt.
        destruct Hs as [(C0 & a0 & E) | (C0 & a0 & E)]; rewrite E in Hrt;
          simpl in Hrt.
        - exact Hrt.
        - exfalso. destruct Hrt as [Hb | Hb]; [discriminate|].
          eapply head_ok_not_bot; eauto. }
      pose proof (Hadm_sel margs') as Hadm2. rewrite Hreq2 in Hadm2.
      simpl in Hadm2.
      rewrite Hreq2. simpl dyn.
      unfold loc_has_rtype. rewrite Hoy. simpl. split; [exact Hh|].
      exists ca'. split; [exact Hsupc | exact Hadm2]. }
  exists ι, o, (mkObj (mkruntime_type qr Co Ro) fso), Tx.
  refine (conj Hthis (conj Hobj (conj Hoy (conj Hget_x (conj Hnot_rcv
           (conj eq_refl (conj Hfb (conj Hwm' (conj _ (conj eq_refl
           (conj _ _))))))))))).
  - (* the callee configuration *)
    refine (conj Hct (conj Hheap (conj _ (conj _ (conj _ (conj _ _)))))).
    + refine (conj _ (conj _ _)); simpl.
      * lia.
      * exists ly. split; auto. eapply runtime_getObj_dom; eauto.
      * constructor.
        -- rewrite Hoy. exact I.
        -- eapply Forall2_Forall_l; [exact Hvals_ty|].
           intros [|loc] A Hv; auto. simpl in Hv. unfold wf_r_typable in Hv.
           destruct (loc_has_rtype_getObj _ _ _ _ Hv) as [o' Ho'].
           rewrite Ho'. exact I.
    + eapply stmt_typing_wf_env; eauto.
    + exists ly, (mkObj (mkruntime_type qr Co Ro) fso), D'. simpl.
      refine (conj eq_refl (conj Hoy (conj eq_refl (conj Hsupc
               (conj Hlf_ca (conj (conj Hlm' Hka') (conj _ Hb'))))))).
      rewrite Hctp. unfold rbounds_ok in *.
      eapply Forall2_Forall_r_impl;
        [exact Hb_ca | exact (class_bounds_wf _ _ _ Hct HfD) |].
      intros R B HR HB. simpl in HR.
      rewrite (dyn_no_method_vars _ _ _ _ HB eq_refl). exact HR.
    + simpl. f_equal. symmetry. apply (Forall2_length Hparams').
    + intros ι' qc' Hth Hm i Hi sqt Hnth.
      simpl in Hth. inversion Hth; subst ι'.
      unfold r_muttype in Hm. rewrite Hoy in Hm. inversion Hm; subst qc'.
      unfold runtime_getVal. simpl.
      destruct i as [|i]; simpl in *.
      * inversion Hnth; subst. exact Hrecv_ty.
      * pose proof (Forall2_nth_error_rel _ _ _ i Hparams') as Hrel.
        rewrite Hnth in Hrel.
        destruct (nth_error vals i) as [[|loc]|]; auto.
  - (* the result *)
    intros h' v Hv. simpl in Hv.
    eapply val_typable_subtype; [exact Hfb | exact Hret_sub |].
    destruct v as [|loc]; [exact I|]. simpl in *.
    unfold wf_r_typable in *. apply Hret_ref in Hv.
    unfold member_type. rewrite dyn_subst.
    eapply loc_has_rtype_adapt; eauto.
  - rewrite Hsc. exact Hscope.
Qed.
