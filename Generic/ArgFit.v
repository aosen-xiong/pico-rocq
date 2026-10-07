From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels ArgViews GhostTyping
  GhostFit ArgTyping GhostInvariant.

(** Fits in the header frame, and their step to the parent class.

    The arguments of a reader at a class fit that class's bounds, each bound
    read the way the reader reads the class's header: written mutable
    positions through the payload.  The fit is the head-view fit of the
    earlier layer; it is what locates payloads. *)

Definition hfr (CT : class_table) (qo : q_r) (l : lab) (C : class_name)
    (As : list ltype) : lframe :=
  hframe (qr2q qo) l (pclassf CT C As) As.

Definition hfit (CT : class_table) (L : list nat) (qo : q_r) (l : lab)
    (C : class_name) (As : list ltype) : Prop :=
  forall def, find_class CT C = Some def ->
    frame_fits CT L (class_env def) (hfr CT qo l C As).

Lemma hstep_obj : forall hq l pn As Ss,
  hstep false hq (fun q0 => q0) l pn As Ss = map (ldyn (hframe hq l pn As)) Ss.
Proof.
  intros. unfold hstep. rewrite rd_map_obj. apply map_ext. intros S.
  rewrite map_qual_id. reflexivity.
Qed.

Ltac hdr_solve H1 H2 :=
  (split;
   [ solve [left; reflexivity] || solve [right; split; auto]
   | solve [left; reflexivity] || solve [right; left; discriminate]
     || solve [right; right; reflexivity]
     || solve [right; right; exact H1]
     || solve [right; right; symmetry; apply H2; reflexivity] ]).

(** A parent's bound, read in the parent's header frame and read through
    the child's class qualifier in the child's. *)
Lemma hdr_cond : forall L qo cq lmP lmC l cs,
  vpa_mutability_runtime_bound_agree qo cq = true ->
  norm L lmP = norm L lmC ->
  (cq = Mut_c -> norm L lmC = norm L l) ->
  label_cond L (vpa_q AbstractState (qc2q cq))
    (mk_lframe (qr2q qo) lmP l cs []) (mk_lframe (qr2q qo) lmC l cs []).
Proof.
  intros L qo cq lmP lmC l cs Hag H1 H2 q0.
  destruct qo, cq; try discriminate Hag; destruct q0;
    cbv [vpa_q vpa_mutability_qq_abstract_state qc2q qr2q dynq lf_q lab_of
         lf_mut lf_rdm arg_q_sub];
    hdr_solve H1 H2.
Qed.

Lemma hdr_cond_unm : forall L qo cq lmP lmC l cs,
  vpa_mutability_runtime_bound_agree qo cq = true ->
  (cq = Mut_c -> norm L lmC = norm L l) ->
  label_cond L (unm (vpa_q AbstractState (qc2q cq)))
    (mk_lframe (qr2q qo) lmP l cs []) (mk_lframe (qr2q qo) lmC l cs []).
Proof.
  intros L qo cq lmP lmC l cs Hag H2 q0.
  assert (H1 : LOut = LOut) by reflexivity.
  destruct qo, cq; try discriminate Hag; destruct q0;
    cbv [unm vpa_q vpa_mutability_qq_abstract_state qc2q qr2q dynq lf_q lab_of
         lf_mut lf_rdm arg_q_sub];
    hdr_solve H1 H2.
Qed.

Lemma pfindsf_nth : forall CT Bs As n B A,
  nth_error Bs n = Some B -> nth_error As n = Some A ->
  pfindf CT B A <> None -> pfindsf CT Bs As <> None.
Proof.
  intros CT Bs. induction Bs as [|B0 Bs IH]; intros As n B A HB HA Hp.
  - destruct n; discriminate.
  - destruct As as [|A0 As]; [destruct n; discriminate|].
    simpl. destruct n as [|n]; simpl in HB, HA.
    + inversion HB; inversion HA; subst.
      destruct (pfindf CT B A); [discriminate | congruence].
    + destruct (pfindf CT B0 A0); [discriminate|]. eapply IH; eauto.
Qed.

(* ------------------FROM FITS IN ANY READING TO THE HEADER FRAME------------------*)

(** Arguments that fit a class's bounds, each bound read through a class
    qualifier in a frame with a given mutable label, fit them in the header
    frame; and the payload, when there is one, is a mutable node of that
    label. *)
Lemma hfit_of_fits : forall CT L qo cq l lm0 C def As,
  wf_class_table CT ->
  find_class CT C = Some def ->
  vpa_mutability_runtime_bound_agree qo cq = true ->
  (cq = Mut_c -> norm L lm0 = norm L l) ->
  Forall2
    (fun A B =>
       lsubt CT L A
         (ldyn (mk_lframe (qr2q qo) lm0 l As [])
            (map_qual (vpa_q AbstractState (qc2q cq)) B)) /\
       rlost_free (erase
         (ldyn (mk_lframe (qr2q qo) lm0 l As [])
            (map_qual (vpa_q AbstractState (qc2q cq)) B))))
    As (ctparams (signature def)) ->
  hfit CT L qo l C As /\
  (forall q' l', pclassf CT C As = Some (q', l') ->
     q' = Mut /\ norm L l' = norm L lm0).
Proof.
  intros CT L qo cq l lm0 C def As Hwf Hfind Hag Hmc Hall.
  remember (vpa_q AbstractState (qc2q cq)) as f eqn:Hf.
  remember (mk_lframe (qr2q qo) lm0 l As []) as Fa eqn:HFa.
  assert (HfM : f Mut = Mut) by (rewrite Hf; destruct cq; reflexivity).
  assert (Hpay : forall q' l', pclassf CT C As = Some (q', l') ->
            q' = Mut /\ norm L l' = norm L lm0).
  { intros q' l' Hp.
    assert (HmF : lf_mut Fa = lm0) by (rewrite HFa; reflexivity).
    rewrite <- HmF.
    eapply (pclassf_fit CT L Fa f C def As q' l' Hwf HfM Hfind); eauto.
    - exact (class_bounds_class _ _ _ Hwf Hfind).
    - eapply Forall2_impl; [|exact Hall]. intros a b [Ha _]. exact Ha. }
  split; [|exact Hpay].
  intros def' Hfd' o n B Hb. rewrite Hfind in Hfd'. inversion Hfd'; subst def'.
  destruct (tv_bound_class_env _ _ _ _ Hb) as [-> Hnb].
  pose proof (Forall2_nth_error_rel _ _ _ n Hall) as Hrel. rewrite Hnb in Hrel.
  destruct (nth_error As n) as [A|] eqn:HA; [|contradiction].
  destruct Hrel as [Hs Hrl].
  assert (HX : ldyn (hfr CT qo l C As) (TVar TVSub ClassVar n) = A).
  { unfold hfr, hframe. cbn [ldyn lf_cargs lf_margs tv_lookup]. rewrite HA.
    reflexivity. }
  rewrite HX.
  pose proof (class_bounds_class _ _ _ Hwf Hfind) as Hcls.
  rewrite Forall_forall in Hcls.
  pose proof (Hcls _ (nth_error_In _ _ Hnb)) as HBc.
  destruct B as [qb D Bs|u o0 n0|? ? ? ?]; [|contradiction..].
  destruct A as [q1 l1 C1 As1].
  destruct (q_eq_dec q1 Bot) as [-> | Hq1].
  - (* an argument no value has: only shapes matter *)
    cbn [ldyn map_qual] in Hs |- *. unfold lsubt in Hs |- *. left.
    split; [reflexivity|].
    destruct Hs as [(_ & Vs & Hv & Hlen) | (_ & _ & Vs & Hv & Hle)].
    + exists Vs. split; auto. rewrite Hlen. rewrite !length_map. reflexivity.
    + exists Vs. split; auto. rewrite (Forall2_length Hle).
      rewrite !length_map. reflexivity.
  - eapply lsubt_agree_r; [exact Hs|]. apply lagree_sym; [|exact Hrl].
    destruct (has_mut (TClass qb D Bs)) eqn:Hm.
    + (* the bound writes a mutable position: there is a payload *)
      assert (Hne : pclassf CT C As <> None).
      { unfold pclassf. rewrite Hfind. eapply pfindsf_nth; eauto.
        eapply (fit_ex CT L Fa f qb D Bs (LT q1 l1 C1 As1) Hwf Hs); auto. }
      destruct (pclassf CT C As) as [[q' l']|] eqn:Hpn; [|congruence].
      destruct (Hpay q' l' eq_refl) as [-> Hl'].
      apply ldyn_map_qual_agree.
      * unfold hfr, hframe. rewrite Hpn. simpl rd_lab. rewrite HFa. rewrite Hf.
        apply hdr_cond; auto.
      * rewrite HFa. simpl. apply Forall2_lagree_refl.
      * rewrite HFa. simpl. constructor.
    + (* the bound writes none *)
      rewrite (no_mut_lit_unm f _ Hm). apply ldyn_map_qual_agree.
      * unfold hfr, hframe. rewrite HFa. rewrite Hf.
        apply hdr_cond_unm; auto.
      * rewrite HFa. simpl. apply Forall2_lagree_refl.
      * rewrite HFa. simpl. constructor.
Qed.

(* ------------------THE STEP TO THE PARENT CLASS------------------*)

(** A reader whose arguments fit its class's bounds in the header frame has,
    at the parent class, arguments that fit the parent's bounds in the
    parent's header frame; and the parent's payload, when there is one, is a
    mutable node of the label the child reads its own header with. *)
Lemma hfit_step : forall CT L qo l C As def P Ss sd,
  wf_class_table CT ->
  find_class CT C = Some def ->
  super (signature def) = Some (P, Ss) ->
  find_class CT P = Some sd ->
  vpa_mutability_runtime_bound_agree qo (class_qualifier (signature def)) = true ->
  Forall rlost_free (map erase As) ->
  (class_qualifier (signature def) = Mut_c ->
   norm L (lf_mut (hfr CT qo l C As)) = norm L l) ->
  hfit CT L qo l C As ->
  hfit CT L qo l P (map (ldyn (hfr CT qo l C As)) Ss) /\
  (forall q' l',
     pclassf CT P (map (ldyn (hfr CT qo l C As)) Ss) = Some (q', l') ->
     q' = Mut /\ norm L l' = norm L (lf_mut (hfr CT qo l C As))).
Proof.
  intros CT L qo l C As def P Ss sd Hwf Hfind Hsuper Hsd Hag Hlfa Hmc Hfit.
  remember (hfr CT qo l C As) as Fh eqn:HFh.
  destruct (wf_class_super_bsub _ _ _ _ _ Hwf Hfind Hsuper)
    as (sd' & Hsd' & Hbnds).
  rewrite Hsd in Hsd'. inversion Hsd'; subst sd'. clear Hsd'.
  assert (Hconc : lf_q Fh = Mut \/ lf_q Fh = Imm).
  { rewrite HFh. unfold hfr. simpl. destruct qo; auto. }
  assert (Hfit' : frame_fits CT L (class_env def) Fh).
  { rewrite HFh. exact (Hfit def Hfind). }
  assert (HFa : lf_with_args Fh (map (ldyn Fh) Ss) [] =
                mk_lframe (qr2q qo) (lf_mut Fh) l (map (ldyn Fh) Ss) []).
  { rewrite HFh. reflexivity. }
  eapply (hfit_of_fits CT L qo (class_qualifier (signature def)) l (lf_mut Fh)
            P sd (map (ldyn Fh) Ss) Hwf Hsd Hag Hmc).
  rewrite <- HFa.
  assert (Hgen : forall Xs Bs,
            Forall2
              (fun T B =>
                 lost_free (member_type AbstractState
                              (qc2q (class_qualifier (signature def))) Ss [] B) /\
                 bound_sub CT (class_env def) T
                   (member_type AbstractState
                      (qc2q (class_qualifier (signature def))) Ss [] B))
              Xs Bs ->
            Forall2
              (fun A B =>
                 lsubt CT L A
                   (ldyn (lf_with_args Fh (map (ldyn Fh) Ss) [])
                      (map_qual (vpa_q AbstractState
                                   (qc2q (class_qualifier (signature def)))) B)) /\
                 rlost_free (erase
                   (ldyn (lf_with_args Fh (map (ldyn Fh) Ss) [])
                      (map_qual (vpa_q AbstractState
                                   (qc2q (class_qualifier (signature def)))) B))))
              (map (ldyn Fh) Xs) Bs).
  { intros Xs Bs HF. induction HF as [|T B Xs Bs [Hlf Hbs] HF IH]; simpl;
      constructor; auto.
    pose proof (sub_lsubt CT (with_mode (class_env def) ReadonlyState) L Fh
                  (or_introl eq_refl) Hconc
                  (fun o0 n0 B0 Hb0 => Hfit' o0 n0 B0 Hb0)
                  _ _ (Hbs ReadonlyState)) as Hs.
    assert (Hrl : rlost_free (erase (ldyn Fh
              (member_type AbstractState
                 (qc2q (class_qualifier (signature def))) Ss [] B)))).
    { rewrite erase_ldyn. rewrite HFh. unfold hfr. simpl.
      apply dyn_lost_free; auto; try apply qr2q_concrete; try constructor. }
    unfold member_type, adapt in Hs, Hrl. rewrite ldyn_subst in Hs, Hrl.
    simpl map in Hs, Hrl. split; assumption. }
  exact (Hgen _ _ Hbnds).
Qed.

(* ------------------ALONG A WHOLE VIEW------------------*)

(** What is kept from a class to each of its superclasses: the header fit,
    arguments with nothing left open, a mutability that the class allows,
    and, for a class declared mutable, a header read through the reader's
    own label. *)
Definition hinv (CT : class_table) (L : list nat) (qo : q_r) (l : lab)
    (C : class_name) (As : list ltype) : Prop :=
  hfit CT L qo l C As /\
  Forall rlost_free (map erase As) /\
  forall def, find_class CT C = Some def ->
    vpa_mutability_runtime_bound_agree qo (class_qualifier (signature def)) = true /\
    (class_qualifier (signature def) = Mut_c ->
     norm L (lf_mut (hfr CT qo l C As)) = norm L l).

(** The payload, when there is one, is a mutable node of the reader's own
    label. *)
Definition pown (CT : class_table) (L : list nat) (l : lab)
    (C : class_name) (As : list ltype) : Prop :=
  forall q' l', pclassf CT C As = Some (q', l') ->
    q' = Mut /\ norm L l' = norm L l.

Lemma pown_hdr : forall CT L qo l C As,
  pown CT L l C As -> norm L (lf_mut (hfr CT qo l C As)) = norm L l.
Proof.
  intros CT L qo l C As Hk. unfold hfr, hframe. cbn [lf_mut].
  destruct (pclassf CT C As) as [[q' l']|] eqn:Hp; [|reflexivity].
  destruct (Hk q' l' Hp) as [-> Hl]. simpl. exact Hl.
Qed.

Lemma bound_agree_super : forall qo cq cqP,
  vpa_mutability_runtime_bound_agree qo cq = true ->
  cq = cqP \/ cqP = RDM_c ->
  vpa_mutability_runtime_bound_agree qo cqP = true.
Proof.
  intros qo cq cqP H [-> | ->]; auto. destruct qo; reflexivity.
Qed.

Lemma hinv_step : forall CT L qo l C As P Ss,
  wf_class_table CT ->
  hinv CT L qo l C As ->
  parent_lookup CT C = Some (P, Ss) ->
  hinv CT L qo l P (map (ldyn (hfr CT qo l C As)) Ss) /\
  (pown CT L l C As -> pown CT L l P (map (ldyn (hfr CT qo l C As)) Ss)).
Proof.
  intros CT L qo l C As P Ss Hwf (Hfit & Hlf & Hcls) Hparent.
  unfold parent_lookup in Hparent.
  destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
  destruct (Hcls def eq_refl) as [Hag Hmc].
  destruct (wf_class_super_inv _ _ _ _ _ Hwf Hfind Hparent)
    as (sd & Hsd & _ & HlfS & _ & Hqq & _).
  destruct (hfit_step CT L qo l C As def P Ss sd Hwf Hfind Hparent Hsd Hag Hlf
              Hmc Hfit) as [HfitP HpayP].
  assert (HpownP : pown CT L l C As ->
                   pown CT L l P (map (ldyn (hfr CT qo l C As)) Ss)).
  { intros Hk q' l' Hp. destruct (HpayP q' l' Hp) as [-> Hl].
    split; auto. rewrite Hl. apply pown_hdr. exact Hk. }
  split; [|exact HpownP].
  refine (conj HfitP (conj _ _)).
  - rewrite map_erase_ldyn. unfold hfr. simpl.
    apply map_dyn_lost_free; auto; try apply qr2q_concrete; try constructor.
  - intros sd' Hsd'. rewrite Hsd in Hsd'. inversion Hsd'; subst sd'.
    split; [eapply bound_agree_super; eauto|].
    intros HmP.
    assert (HmC : class_qualifier (signature def) = Mut_c).
    { destruct Hqq as [Hx | Hx]; congruence. }
    specialize (Hmc HmC).
    destruct (pclassf CT P (map (ldyn (hfr CT qo l C As)) Ss))
      as [[q' l']|] eqn:Hp.
    + destruct (HpayP q' l' eq_refl) as [-> Hl].
      unfold hfr at 1. unfold hframe. cbn [lf_mut]. rewrite Hp. simpl.
      rewrite Hl. exact Hmc.
    + unfold hfr at 1. unfold hframe. cbn [lf_mut]. rewrite Hp. reflexivity.
Qed.

(** Along an object's view. *)
Lemma hinv_oview : forall CT L qo l C As D Vs,
  wf_class_table CT ->
  oview CT qo l C As D Vs ->
  hinv CT L qo l C As ->
  hinv CT L qo l D Vs /\ (pown CT L l C As -> pown CT L l D Vs).
Proof.
  intros CT L qo l C As D Vs Hwf H. unfold oview in H.
  induction H; intros Hi; [split; auto|].
  rewrite hstep_obj in H, IHview.
  destruct (hinv_step CT L qo l C As P Ss Hwf Hi Hparent) as [HiP HkP].
  destruct (IHview HiP) as [HiD HkD]. split; auto.
Qed.

(* ------------------A TYPE WRITTEN MUTABLE------------------*)

Lemma tg_mut_id : forall q0, ArgViews.tg Mut q0 = q0.
Proof. intros []; reflexivity. Qed.

Lemma map_qual_tg_mut : forall T, map_qual (ArgViews.tg Mut) T = T.
Proof.
  induction T using qualified_type_ind'.
  - simpl. rewrite tg_mut_id. f_equal. induction H; simpl; auto. f_equal; auto.
  - destruct u; simpl; auto. rewrite tg_mut_id. reflexivity.
  - simpl. f_equal. induction H; simpl; auto. f_equal; auto.
Qed.

(** When its payload is not left open, a labelled type headed mutable steps
    to its parent exactly as an object does. *)
Lemma hstep_mut_obj : forall l pn As Ss,
  (forall lp, pn <> Some (Lost, lp)) ->
  hstep true Mut (ArgViews.tg Mut) l pn As Ss =
  map (ldyn (hframe Mut l pn As)) Ss.
Proof.
  intros l pn As Ss Hn. unfold hstep.
  assert (Hrd : rd_map true (ArgViews.tg Mut) pn = ArgViews.tg Mut).
  { destruct pn as [[qp lp]|]; auto. destruct qp; auto.
    exfalso. exact (Hn lp eq_refl). }
  rewrite Hrd. apply map_ext. intros S. rewrite map_qual_tg_mut. reflexivity.
Qed.

(** A labelled type headed mutable whose arguments fit in the header frame
    and whose payload is of its own label has payloads of that label along
    every view. *)
Lemma pcoh_of_hinv : forall CT L l C As,
  wf_class_table CT ->
  hinv CT L Mut_r l C As ->
  pown CT L l C As ->
  pcoh CT L Mut l C As l.
Proof.
  intros CT L l C As Hwf Hi Hk C' As' Hv. unfold tview in Hv.
  assert (Hgen : hinv CT L Mut_r l C' As' /\ pown CT L l C' As').
  { revert Hi Hk.
    induction Hv; intros Hi Hk; [split; auto|].
    assert (Hn : forall lp, pclassf CT C As <> Some (Lost, lp)).
    { intros lp Hp. destruct (Hk _ _ Hp) as [Hx _]. discriminate. }
    rewrite (hstep_mut_obj l (pclassf CT C As) As Ss Hn) in Hv, IHHv.
    destruct (hinv_step CT L Mut_r l C As P Ss Hwf Hi Hparent) as [HiP HkP].
    apply IHHv; auto. }
  destruct Hgen as [_ Hk'].
  destruct (pclassf CT C' As') as [[q' l']|] eqn:Hp; auto.
  destruct (Hk' q' l' Hp) as [-> Hl]. exact Hl.
Qed.

(* ------------------STARTING FACTS: ALLOCATION------------------*)

Lemma lagree_erase_eq : forall L A B,
  lagree L A B -> rlost_free (erase B) -> erase A = erase B.
Proof.
  intros L A B H. induction H using lagree_ind'. intros Hlf.
  change (erase (LT q2 l2 C Bs)) with (RClass q2 C (map erase Bs)) in Hlf.
  apply rlost_free_class in Hlf. destruct Hlf as [Hq2 Hargs].
  assert (q2 = q1).
  { unfold arg_q_sub in H. destruct H as [-> | [-> _]]; congruence. }
  subst q2. simpl. f_equal.
  clear H H0 Hq2 H1.
  induction H2 as [|a b As' Bs' Hab Hrest IH]; simpl; auto.
  simpl in Hargs. inversion Hargs; subst. f_equal; auto.
Qed.

Ltac rd_solve :=
  (split;
   [ solve [left; reflexivity] || solve [right; split; auto]
   | solve [left; reflexivity] || solve [right; left; discriminate]
     || solve [right; right; reflexivity] ]).

(** A bound adapted through the allocation qualifier reads the same in the
    allocating frame and in a frame with the new object's mutability, the
    allocating world for written mutable positions and the new object's
    colour for receiver-dependent ones. *)
Lemma alloc_read_cond : forall L qthis qc wf mode cs cs' ms',
  label_cond2 L (vpa_q AbstractState (qc2q qc)) (vpa_q AbstractState (qc2q qc))
    (lf_with_args (act_frame qthis wf mode cs' ms') cs [])
    (mk_lframe (qr2q (vpa_mutability_object_creation qthis qc)) (LIn wf)
       (olab (new_color qc wf mode)) cs []).
Proof.
  intros L qthis qc wf mode cs cs' ms' q0.
  destruct q0, qc, qthis, mode;
    cbv [act_frame lf_with_args lf_q lab_of lf_mut lf_rdm vpa_q
         vpa_mutability_qq_abstract_state qc2q qr2q dynq olab
         vpa_mutability_object_creation new_color arg_q_sub];
    rd_solve.
Qed.

Lemma alloc_read_cond_rev : forall L qthis qc wf mode cs cs' ms',
  label_cond2 L (vpa_q AbstractState (qc2q qc)) (vpa_q AbstractState (qc2q qc))
    (mk_lframe (qr2q (vpa_mutability_object_creation qthis qc)) (LIn wf)
       (olab (new_color qc wf mode)) cs [])
    (lf_with_args (act_frame qthis wf mode cs' ms') cs []).
Proof.
  intros L qthis qc wf mode cs cs' ms' q0.
  destruct q0, qc, qthis, mode;
    cbv [act_frame lf_with_args lf_q lab_of lf_mut lf_rdm vpa_q
         vpa_mutability_qq_abstract_state qc2q qr2q dynq olab
         vpa_mutability_object_creation new_color arg_q_sub];
    rd_solve.
Qed.

(** At an allocation: the new object's arguments fit its class's bounds in
    the header frame, whatever its mutability and colour, and its payload,
    when there is one, is a mutable node of the allocating world. *)
Lemma alloc_hfit : forall CT L Δ qthis wf mode lc lm qc C def Ts,
  wf_class_table CT ->
  readonly_state_method_scope (tv_mode Δ) ->
  frame_fits CT L Δ (act_frame qthis wf mode lc lm) ->
  Forall rlost_free (map erase lc) -> Forall rlost_free (map erase lm) ->
  find_class CT C = Some def ->
  Forall lost_free Ts ->
  Forall2
    (fun T B =>
       lost_free (member_type AbstractState (qc2q qc) Ts [] B) /\
       bound_sub CT Δ T (member_type AbstractState (qc2q qc) Ts [] B))
    Ts (ctparams (signature def)) ->
  hfit CT L (vpa_mutability_object_creation qthis qc)
    (olab (new_color qc wf mode)) C
    (map (ldyn (act_frame qthis wf mode lc lm)) Ts) /\
  (forall q' l',
     pclassf CT C (map (ldyn (act_frame qthis wf mode lc lm)) Ts) = Some (q', l') ->
     q' = Mut /\ norm L l' = norm L (LIn wf)).
Proof.
  intros CT L Δ qthis wf mode lc lm qc C def Ts Hwf Hrs Hfits Hlc Hlm Hfind
    HlfT Hbounds.
  remember (act_frame qthis wf mode lc lm) as Fc eqn:HFc.
  assert (Hconc : lf_q Fc = Mut \/ lf_q Fc = Imm).
  { rewrite HFc. simpl. destruct qthis; auto. }
  assert (HlfA : Forall rlost_free (map erase (map (ldyn Fc) Ts))).
  { rewrite map_erase_ldyn. rewrite HFc. simpl.
    apply map_dyn_lost_free; auto. apply qr2q_concrete. }
  eapply (hfit_of_fits CT L (vpa_mutability_object_creation qthis qc) qc
            (olab (new_color qc wf mode)) (LIn wf) C def
            (map (ldyn Fc) Ts) Hwf Hfind).
  - destruct qthis, qc; reflexivity.
  - intros ->. reflexivity.
  - assert (Hgen : forall Xs Bs,
              Forall2
                (fun T B =>
                   lost_free (member_type AbstractState (qc2q qc) Ts [] B) /\
                   bound_sub CT Δ T (member_type AbstractState (qc2q qc) Ts [] B))
                Xs Bs ->
              Forall2
                (fun A B =>
                   lsubt CT L A
                     (ldyn (mk_lframe
                              (qr2q (vpa_mutability_object_creation qthis qc))
                              (LIn wf) (olab (new_color qc wf mode))
                              (map (ldyn Fc) Ts) [])
                        (map_qual (vpa_q AbstractState (qc2q qc)) B)) /\
                   rlost_free (erase
                     (ldyn (mk_lframe
                              (qr2q (vpa_mutability_object_creation qthis qc))
                              (LIn wf) (olab (new_color qc wf mode))
                              (map (ldyn Fc) Ts) [])
                        (map_qual (vpa_q AbstractState (qc2q qc)) B))))
                (map (ldyn Fc) Xs) Bs).
    { intros Xs Bs HF. induction HF as [|T B Xs Bs [Hlf Hbs] HF IH]; simpl;
        constructor; auto.
      pose proof (sub_lsubt CT Δ L Fc Hrs Hconc Hfits _ _
                    (bound_sub_self _ _ _ _ Hbs)) as Hs.
      assert (Hrl : rlost_free (erase (ldyn Fc
                (member_type AbstractState (qc2q qc) Ts [] B)))).
      { rewrite erase_ldyn. rewrite HFc. simpl.
        apply dyn_lost_free; auto. apply qr2q_concrete. }
      unfold member_type, adapt in Hs, Hrl. rewrite ldyn_subst in Hs, Hrl.
      simpl map in Hs, Hrl.
      assert (Hfwd : lagree L
                (ldyn (lf_with_args Fc (map (ldyn Fc) Ts) [])
                   (map_qual (vpa_q AbstractState (qc2q qc)) B))
                (ldyn (mk_lframe
                         (qr2q (vpa_mutability_object_creation qthis qc))
                         (LIn wf) (olab (new_color qc wf mode))
                         (map (ldyn Fc) Ts) [])
                   (map_qual (vpa_q AbstractState (qc2q qc)) B))).
      { apply ldyn_map_qual_agree2.
        - rewrite HFc. apply alloc_read_cond.
        - simpl. apply Forall2_lagree_refl.
        - simpl. constructor. }
      assert (Hbwd : lagree L
                (ldyn (mk_lframe
                         (qr2q (vpa_mutability_object_creation qthis qc))
                         (LIn wf) (olab (new_color qc wf mode))
                         (map (ldyn Fc) Ts) [])
                   (map_qual (vpa_q AbstractState (qc2q qc)) B))
                (ldyn (lf_with_args Fc (map (ldyn Fc) Ts) [])
                   (map_qual (vpa_q AbstractState (qc2q qc)) B))).
      { apply ldyn_map_qual_agree2.
        - rewrite HFc. apply alloc_read_cond_rev.
        - simpl. apply Forall2_lagree_refl.
        - simpl. constructor. }
      split.
      - eapply lsubt_agree_r; eauto.
      - rewrite (lagree_erase_eq L _ _ Hbwd Hrl). exact Hrl. }
    exact (Hgen _ _ Hbounds).
Qed.

(** The whole bundle for a new object; and when the object is in the
    allocating world, its payload is of its own label. *)
Lemma alloc_hinv : forall CT L Δ qthis wf mode lc lm qc C def Ts,
  wf_class_table CT ->
  readonly_state_method_scope (tv_mode Δ) ->
  frame_fits CT L Δ (act_frame qthis wf mode lc lm) ->
  Forall rlost_free (map erase lc) -> Forall rlost_free (map erase lm) ->
  find_class CT C = Some def ->
  vpa_mutability_bound (qc2q qc) (class_qualifier (signature def)) = qc2q qc ->
  Forall lost_free Ts ->
  Forall2
    (fun T B =>
       lost_free (member_type AbstractState (qc2q qc) Ts [] B) /\
       bound_sub CT Δ T (member_type AbstractState (qc2q qc) Ts [] B))
    Ts (ctparams (signature def)) ->
  hinv CT L (vpa_mutability_object_creation qthis qc)
    (olab (new_color qc wf mode)) C
    (map (ldyn (act_frame qthis wf mode lc lm)) Ts) /\
  (new_color qc wf mode = Some wf ->
   pown CT L (LIn wf) C (map (ldyn (act_frame qthis wf mode lc lm)) Ts)).
Proof.
  intros CT L Δ qthis wf mode lc lm qc C def Ts Hwf Hrs Hfits Hlc Hlm Hfind
    Hqc HlfT Hbounds.
  destruct (alloc_hfit CT L Δ qthis wf mode lc lm qc C def Ts Hwf Hrs Hfits
              Hlc Hlm Hfind HlfT Hbounds) as [Hfit Hpay].
  split.
  - refine (conj Hfit (conj _ _)).
    + rewrite map_erase_ldyn. simpl.
      apply map_dyn_lost_free; auto. apply qr2q_concrete.
    + intros def' Hfd'. rewrite Hfind in Hfd'. inversion Hfd'; subst def'.
      split.
      * destruct qthis, qc, (class_qualifier (signature def));
          simpl in Hqc; try discriminate; reflexivity.
      * intros Hm. rewrite Hm in Hqc.
        assert (qc = Mut_c) by (destruct qc; simpl in Hqc; congruence).
        subst qc. unfold hfr, hframe. cbn [lf_mut].
        destruct (pclassf CT C (map (ldyn (act_frame qthis wf mode lc lm)) Ts))
          as [[q' l']|] eqn:Hp; [|reflexivity].
        destruct (Hpay q' l' eq_refl) as [-> Hl]. simpl. exact Hl.
  - intros Hc q' l' Hp. exact (Hpay q' l' Hp).
Qed.

(* ------------------STARTING FACTS: A TYPE WRITTEN MUTABLE------------------*)

Lemma static_read_cond : forall L F cs,
  label_cond2 L (vpa_q AbstractState Mut) (vpa_q AbstractState Mut)
    (lf_with_args F cs [])
    (mk_lframe Mut (lf_mut F) (lf_mut F) cs []).
Proof.
  intros L [qF lm lr c0 m0] cs q0.
  destruct q0;
    cbv [lf_with_args lf_q lab_of lf_mut lf_rdm vpa_q
         vpa_mutability_qq_abstract_state dynq arg_q_sub];
    rd_solve.
Qed.

Lemma static_read_cond_rev : forall L F cs,
  label_cond2 L (vpa_q AbstractState Mut) (vpa_q AbstractState Mut)
    (mk_lframe Mut (lf_mut F) (lf_mut F) cs [])
    (lf_with_args F cs []).
Proof.
  intros L [qF lm lr c0 m0] cs q0.
  destruct q0;
    cbv [lf_with_args lf_q lab_of lf_mut lf_rdm vpa_q
         vpa_mutability_qq_abstract_state dynq arg_q_sub];
    rd_solve.
Qed.

(** A well-formed type written mutable, read in a frame whose own type
    variables fit: its arguments fit its class's bounds in the header frame
    and its payloads, along every view, are of the frame's mutable label. *)
Lemma static_mut_pcoh : forall CT L Δ F C Ts def,
  wf_class_table CT ->
  readonly_state_method_scope (tv_mode Δ) ->
  (lf_q F = Mut \/ lf_q F = Imm) ->
  frame_fits CT L Δ F ->
  Forall rlost_free (map erase (lf_cargs F)) ->
  Forall rlost_free (map erase (lf_margs F)) ->
  find_class CT C = Some def ->
  class_qualifier (signature def) <> Imm_c ->
  Forall2
    (fun T B =>
       lost_free (subst Ts [] (adapt AbstractState Mut B)) ->
       bound_sub CT Δ T (subst Ts [] (adapt AbstractState Mut B)))
    Ts (ctparams (signature def)) ->
  Forall lost_free Ts ->
  Forall (fun B => lost_free (subst Ts [] (adapt AbstractState Mut B)))
    (ctparams (signature def)) ->
  hinv CT L Mut_r (lf_mut F) C (map (ldyn F) Ts) /\
  pown CT L (lf_mut F) C (map (ldyn F) Ts) /\
  pcoh CT L Mut (lf_mut F) C (map (ldyn F) Ts) (lf_mut F).
Proof.
  intros CT L Δ F C Ts def Hwf Hrs Hconc Hfits Hlc Hlm Hfind Hhead Hbounds HlfT HlfB.
  assert (HlfA : Forall rlost_free (map erase (map (ldyn F) Ts))).
  { rewrite map_erase_ldyn. apply map_dyn_lost_free; auto. }
  assert (Hmain :
    hfit CT L Mut_r (lf_mut F) C (map (ldyn F) Ts) /\
    (forall q' l', pclassf CT C (map (ldyn F) Ts) = Some (q', l') ->
       q' = Mut /\ norm L l' = norm L (lf_mut F))).
  { eapply (hfit_of_fits CT L Mut_r Mut_c (lf_mut F) (lf_mut F) C def
              (map (ldyn F) Ts) Hwf Hfind); auto.
    assert (Hgen : forall Xs Bs,
              Forall2
                (fun T B =>
                   lost_free (subst Ts [] (adapt AbstractState Mut B)) ->
                   bound_sub CT Δ T (subst Ts [] (adapt AbstractState Mut B)))
                Xs Bs ->
              Forall (fun B => lost_free (subst Ts [] (adapt AbstractState Mut B)))
                Bs ->
              Forall2
                (fun A B =>
                   lsubt CT L A
                     (ldyn (mk_lframe (qr2q Mut_r) (lf_mut F) (lf_mut F)
                              (map (ldyn F) Ts) [])
                        (map_qual (vpa_q AbstractState (qc2q Mut_c)) B)) /\
                   rlost_free (erase
                     (ldyn (mk_lframe (qr2q Mut_r) (lf_mut F) (lf_mut F)
                              (map (ldyn F) Ts) [])
                        (map_qual (vpa_q AbstractState (qc2q Mut_c)) B))))
                (map (ldyn F) Xs) Bs).
    { intros Xs Bs HF. induction HF as [|T B Xs Bs Hb HF IH]; intros HlB; simpl;
        constructor; inversion HlB as [|? ? Hlf HlB']; subst; auto.
      pose proof (sub_lsubt CT Δ L F Hrs Hconc Hfits _ _
                    (bound_sub_self _ _ _ _ (Hb Hlf))) as Hs.
      assert (Hrl : rlost_free (erase (ldyn F
                (subst Ts [] (adapt AbstractState Mut B))))).
      { rewrite erase_ldyn. apply dyn_lost_free; auto. }
      unfold adapt in Hs, Hrl. rewrite ldyn_subst in Hs, Hrl.
      simpl map in Hs, Hrl.
      assert (Hfwd : lagree L
                (ldyn (lf_with_args F (map (ldyn F) Ts) [])
                   (map_qual (vpa_q AbstractState Mut) B))
                (ldyn (mk_lframe Mut (lf_mut F) (lf_mut F) (map (ldyn F) Ts) [])
                   (map_qual (vpa_q AbstractState Mut) B))).
      { apply ldyn_map_qual_agree2.
        - apply static_read_cond.
        - simpl. apply Forall2_lagree_refl.
        - simpl. constructor. }
      assert (Hbwd : lagree L
                (ldyn (mk_lframe Mut (lf_mut F) (lf_mut F) (map (ldyn F) Ts) [])
                   (map_qual (vpa_q AbstractState Mut) B))
                (ldyn (lf_with_args F (map (ldyn F) Ts) [])
                   (map_qual (vpa_q AbstractState Mut) B))).
      { apply ldyn_map_qual_agree2.
        - apply static_read_cond_rev.
        - simpl. apply Forall2_lagree_refl.
        - simpl. constructor. }
      split.
      - eapply lsubt_agree_r; eauto.
      - rewrite (lagree_erase_eq L _ _ Hbwd Hrl). exact Hrl. }
    exact (Hgen _ _ Hbounds HlfB). }
  destruct Hmain as [Hfit Hpay].
  assert (Hk : pown CT L (lf_mut F) C (map (ldyn F) Ts)) by exact Hpay.
  assert (Hi : hinv CT L Mut_r (lf_mut F) C (map (ldyn F) Ts)).
  { refine (conj Hfit (conj HlfA _)).
    intros def' Hfd'. rewrite Hfind in Hfd'. inversion Hfd'; subst def'.
    split.
    - destruct (class_qualifier (signature def)); simpl; auto; congruence.
    - intros _. apply pown_hdr. exact Hk. }
  refine (conj Hi (conj Hk _)).
  apply pcoh_of_hinv; auto.
Qed.

Print Assumptions hfit_of_fits.
Print Assumptions hinv_oview.
Print Assumptions alloc_hinv.
Print Assumptions static_mut_pcoh.

(* ------------------PAYLOAD-AWARE FITS------------------*)

(** A class without parameters that is not declared immutable: read by a
    mutable reader, every payload above it is of the reader's label. *)
Lemma pcoh_argfree : forall CT L l C,
  wf_class_table CT ->
  (forall def, find_class CT C = Some def ->
     ctparams (signature def) = [] /\
     class_qualifier (signature def) <> Imm_c) ->
  pcoh CT L Mut l C [] l.
Proof.
  intros CT L l C Hwf Hc.
  assert (Hpn : pclassf CT C [] = None).
  { unfold pclassf. destruct (find_class CT C) as [def|] eqn:Hf; auto.
    destruct (Hc def eq_refl) as [Hp _]. rewrite Hp. reflexivity. }
  apply pcoh_of_hinv; auto.
  - refine (conj _ (conj _ _)).
    + intros def Hf o n B Hb. destruct (Hc def Hf) as [Hp _].
      destruct (tv_bound_class_env _ _ _ _ Hb) as [_ Hnb]. rewrite Hp in Hnb.
      destruct n; discriminate.
    + constructor.
    + intros def Hf. destruct (Hc def Hf) as [_ Hq]. split.
      * destruct (class_qualifier (signature def)); auto; congruence.
      * intros _. unfold hfr, hframe. cbn [lf_mut]. rewrite Hpn. reflexivity.
  - intros q' l' Hp. rewrite Hpn in Hp. discriminate.
Qed.

(** What is used of a static type's well-formedness: when it is a class
    type written mutable, its arguments satisfy its class's bounds. *)
Definition sbnd (CT : class_table) (Δ : tv_env) (T : qualified_type) : Prop :=
  match T with
  | TClass q0 C Ts =>
      q0 = Mut -> exists def, find_class CT C = Some def /\
        Forall2
          (fun T B =>
             lost_free (subst Ts [] (adapt AbstractState Mut B)) ->
             bound_sub CT Δ T (subst Ts [] (adapt AbstractState Mut B)))
          Ts (ctparams (signature def))
  | TVar _ _ _ => True
  | THead _ _ _ _ => True
  end.

Lemma sbnd_of_wf : forall CT Δ top T, wf_stype CT Δ top T -> sbnd CT Δ T.
Proof.
  intros CT Δ top T H. inversion H; subst; simpl; auto.
  intros Hq. subst. exists def. split; [assumption|].
  eapply Forall2_impl; [|eassumption]. intros a b Hab _. exact Hab.
Qed.

Lemma sbnd_mode : forall CT Δ m T, sbnd CT Δ T -> sbnd CT (with_mode Δ m) T.
Proof.
  intros CT Δ m [q0 C Ts|u o n|? ? ? ?]; simpl; auto.
Qed.

Lemma wf_class_super_sbnd : forall CT C def P Ss,
  wf_class_table CT ->
  find_class CT C = Some def ->
  super (signature def) = Some (P, Ss) ->
  Forall (sbnd CT (class_env def)) Ss.
Proof.
  intros CT C def P Ss Hwf Hfind Hsuper.
  pose proof (wf_class_table_class _ _ _ Hwf Hfind) as Hcls.
  inversion Hcls; subst.
  - congruence.
  - rewrite Hsuper in Hsuper0. inversion Hsuper0; subst.
    match goal with
    | Hw : wf_stypeuse _ _ (TClass _ _ _) |- _ =>
        inversion Hw as [? ? ? ? ? ? ? ? Hargs ?| |]; subst
    end.
    eapply Forall_impl; [|exact Hargs]. intros a Ha.
    exact (sbnd_of_wf _ _ _ _ Ha).
Qed.

(** A static type, read in a frame, is coherent as far as it is written
    mutable. *)
Lemma cohT_static : forall CT L Δ F T,
  wf_class_table CT -> readonly_state_method_scope (tv_mode Δ) ->
  (lf_q F = Mut \/ lf_q F = Imm) ->
  (forall o n B, tv_bound Δ o n = Some B -> is_class_type B) ->
  frame_fits CT L Δ F -> frame_fitsp CT L Δ F -> fcoh CT L Δ F ->
  Forall rlost_free (map erase (lf_cargs F)) ->
  Forall rlost_free (map erase (lf_margs F)) ->
  sbnd CT Δ T -> lost_free T ->
  ~ deadA CT (ldyn F T) -> ~ insaneA CT (ldyn F T) ->
  reachm Δ T -> cohT CT L F (ldyn F T) T.
Proof.
  intros CT L Δ F T Hwf Hrs Hconc Hbc Hfits Hfitp Hcoh Hlc Hlm Hsb Hlf Hnd Hsn Hr.
  destruct T as [q0 C Ts|u o n|? ? ? ?].
  - cbn [ldyn] in Hnd, Hsn |- *. simpl. intros Hq Hl Va Hva.
    simpl in Hr. destruct Hr as [-> | ->]; [|simpl in Hq; discriminate].
    destruct (Hsb eq_refl) as (def & Hfind & Hb).
    apply lost_free_class in Hlf. destruct Hlf as [_ HlfT].
    assert (HlfB : Forall (fun B => lost_free (subst Ts [] (adapt AbstractState Mut B)))
                     (ctparams (signature def))).
    { simpl in Hnd.
      destruct (clsok_dec CT C (length (map (ldyn F) Ts))) as [Hok | Hno];
        [|exfalso; exact (Hnd Hno)].
      destruct Hok as [Hlv _]. specialize (Hlv def Hfind).
      eapply Forall_impl; [|exact Hlv]. intros B HB. unfold adapt.
      apply lost_free_inst; auto. intros q1 Hq1. destruct q1; simpl; congruence. }
    assert (Hni : class_qualifier (signature def) <> Imm_c).
    { intros Hi. apply Hsn. simpl. split; [exact Hq | eauto]. }
    destruct (static_mut_pcoh CT L Δ F C Ts def Hwf Hrs Hconc Hfits Hlc Hlm Hfind
                Hni Hb HlfT HlfB) as (_ & _ & Hp).
    assert (Va = map (ldyn F) Ts).
    { unfold tview in Hva. simpl in Hva.
      exact (view_deterministic _ _ _ _ _ _ _ _ _ Hwf Hva _ (v_refl _ _ _ _ _ _ _)). }
    subst Va. exact Hp.
  - destruct u as [|qv].
    + destruct (ldyn F (TVar TVSub o n)); simpl; auto.
    + cbn [ldyn] in Hnd, Hsn |- *.
      destruct (match tv_lookup o (lf_cargs F) (lf_margs F) n with
                | Some A0 => A0 | None => ldefault end) as [qa la Ca Aa].
      simpl lrehead in Hnd, Hsn |- *. simpl. intros Hq Hl C0 Hv.
      apply (pcoh_lm _ _ _ _ _ _ (lab_of F qv)); [exact Hl|].
      apply pcoh_argfree; auto. intros d0 Hd0. split.
      * simpl in Hnd.
        destruct (clsok_dec CT Ca (length Aa)) as [Hok | Hno];
          [|exfalso; exact (Hnd Hno)].
        destruct Hok as [_ Har].
        pose proof (view_arity _ _ _ _ _ _ _ _ _ Hwf Hv Har d0 Hd0) as Hlen.
        destruct (ctparams (signature d0)); [reflexivity | discriminate].
      * intros Hi. apply Hsn. simpl. split; [exact Hq|].
        exact (view_imm _ _ _ _ _ _ _ _ _ Hwf Hv d0 Hd0 Hi).
  - simpl in Hr. contradiction.
Qed.

(** One static subtyping fact about a well-formed type, read in a frame. *)
Lemma fit3 : forall CT L Δ F,
  wf_class_table CT -> readonly_state_method_scope (tv_mode Δ) ->
  (lf_q F = Mut \/ lf_q F = Imm) ->
  (forall o n B, tv_bound Δ o n = Some B -> is_class_type B) ->
  frame_fits CT L Δ F -> frame_fitsp CT L Δ F -> fcoh CT L Δ F ->
  Forall rlost_free (map erase (lf_cargs F)) ->
  Forall rlost_free (map erase (lf_margs F)) ->
  forall T U, sbnd CT Δ T -> lost_free T -> qualified_type_subtype CT Δ T U ->
    fit3p CT L (ldyn F T) (ldyn F U) /\
    (forall q0 K Xs, U = TClass q0 K Xs -> q0 = Mut ->
       ~ deadA CT (ldyn F T) -> ~ insaneA CT (ldyn F T) ->
       scoh CT L (ldyn F T) K).
Proof.
  intros CT L Δ F Hwf Hrs Hconc Hbc Hfits Hfitp Hcoh Hlc Hlm T U Hsb Hlf Hsub.
  pose proof (hvb_of_coh CT L Δ F Hwf Hbc Hfitp Hcoh) as Hvb.
  destruct (deadA_dec CT (ldyn F T)) as [Hd | Hnd].
  { split; [right; left; exact Hd|]. intros; contradiction. }
  destruct (insaneA_dec CT (ldyn F T)) as [Hi | Hsn].
  { split; [|intros; contradiction]. right. right. split; auto.
    refine (proj1 (sub_lsubtp CT Δ L F Hwf Hrs Hconc Hbc Hfitp Hvb T U Hsub
                     (lbot (ldyn F T)) _ (insaneA_lbot _ _)
                     (fun _ => cohT_lbot _ _ _ _ _) _)).
    - intros Hd. exact (Hnd (deadA_lbot _ _ Hd)).
    - apply lsubtp_lbot. apply lsubtp_refl. }
  destruct (sub_lsubtp CT Δ L F Hwf Hrs Hconc Hbc Hfitp Hvb T U Hsub (ldyn F T)
              Hnd Hsn
              (fun Hr => cohT_static CT L Δ F T Hwf Hrs Hconc Hbc Hfits Hfitp
                           Hcoh Hlc Hlm Hsb Hlf Hnd Hsn Hr)
              (lsubtp_refl _ _ _)) as [Hs Hc].
  split; [left; exact Hs|].
  intros q0 K Xs -> -> _ _.
  specialize (Hc (or_introl eq_refl)).
  cbn [ldyn] in Hs. revert Hs Hc.
  destruct (ldyn F T) as [qA lA CA AsA]. intros Hs Hc. simpl in Hc |- *.
  intros -> Va Hva.
  destruct Hs as [(Hx & _) | (_ & Hl & _)]; [discriminate|].
  assert (Hl' : norm L lA = norm L (lf_mut F)) by (apply Hl; reflexivity).
  apply (pcoh_lm _ _ _ _ _ _ (lf_mut F)); [symmetry; exact Hl'|].
  exact (Hc eq_refl Hl' Va Hva).
Qed.

(** The payload-aware counterpart of [hfit_of_fits]: fits and coherence of
    the arguments, each bound read with a given label for written mutable
    positions, give the fits and the coherence in the header frame. *)
Lemma pfit_of_fits : forall CT L qo cq l lm0 C def As,
  wf_class_table CT ->
  find_class CT C = Some def ->
  vpa_mutability_runtime_bound_agree qo cq = true ->
  (cq = Mut_c -> norm L lm0 = norm L l) ->
  Forall2
    (fun A B =>
       (lsubt CT L A
          (ldyn (mk_lframe (qr2q qo) lm0 l As [])
             (map_qual (vpa_q AbstractState (qc2q cq)) B)) /\
        rlost_free (erase
          (ldyn (mk_lframe (qr2q qo) lm0 l As [])
             (map_qual (vpa_q AbstractState (qc2q cq)) B)))) /\
       fit3p CT L A
         (ldyn (mk_lframe (qr2q qo) lm0 l As [])
            (map_qual (vpa_q AbstractState (qc2q cq)) B)) /\
       (forall q0 K Xs, B = TClass q0 K Xs -> q0 = Mut ->
          ~ deadA CT A -> ~ insaneA CT A -> scoh CT L A K))
    As (ctparams (signature def)) ->
  frame_fitsp CT L (class_env def) (hfr CT qo l C As) /\
  fcoh CT L (class_env def) (hfr CT qo l C As).
Proof.
  intros CT L qo cq l lm0 C def As Hwf Hfind Hag Hmc Hall.
  assert (Hold : Forall2
            (fun A B =>
               lsubt CT L A
                 (ldyn (mk_lframe (qr2q qo) lm0 l As [])
                    (map_qual (vpa_q AbstractState (qc2q cq)) B)) /\
               rlost_free (erase
                 (ldyn (mk_lframe (qr2q qo) lm0 l As [])
                    (map_qual (vpa_q AbstractState (qc2q cq)) B))))
            As (ctparams (signature def))).
  { eapply Forall2_impl; [|exact Hall]. intros a b [Ha _]. exact Ha. }
  destruct (hfit_of_fits CT L qo cq l lm0 C def As Hwf Hfind Hag Hmc Hold)
    as [_ Hpay].
  remember (vpa_q AbstractState (qc2q cq)) as f eqn:Hf.
  remember (mk_lframe (qr2q qo) lm0 l As []) as Fa eqn:HFa.
  assert (HfM : f Mut = Mut) by (rewrite Hf; destruct cq; reflexivity).
  assert (HXg : forall n A, nth_error As n = Some A ->
            ldyn (hfr CT qo l C As) (TVar TVSub ClassVar n) = A).
  { intros n A HA. unfold hfr, hframe. cbn [ldyn lf_cargs lf_margs tv_lookup].
    rewrite HA. reflexivity. }
  split.
  - intros o n B Hb.
    destruct (tv_bound_class_env _ _ _ _ Hb) as [-> Hnb].
    pose proof (Forall2_nth_error_rel _ _ _ n Hall) as Hrel. rewrite Hnb in Hrel.
    destruct (nth_error As n) as [A|] eqn:HA; [|contradiction].
    destruct Hrel as [[Hs Hrl] [Hp _]].
    rewrite (HXg n A HA).
    pose proof (class_bounds_class _ _ _ Hwf Hfind) as Hcls.
    rewrite Forall_forall in Hcls.
    pose proof (Hcls _ (nth_error_In _ _ Hnb)) as HBc.
    destruct B as [qb D Bs|u o0 n0|? ? ? ?]; [|contradiction..].
    destruct A as [q1 l1 C1 As1].
    assert (Hagr : q1 <> Bot ->
              lagree L (ldyn Fa (map_qual f (TClass qb D Bs)))
                (ldyn (hfr CT qo l C As) (TClass qb D Bs))).
    { intros Hq1. apply lagree_sym; [|exact Hrl].
      destruct (has_mut (TClass qb D Bs)) eqn:Hm.
      + assert (Hne : pclassf CT C As <> None).
        { unfold pclassf. rewrite Hfind. eapply pfindsf_nth; eauto.
          eapply (fit_ex CT L Fa f qb D Bs (LT q1 l1 C1 As1) Hwf Hs); auto. }
        destruct (pclassf CT C As) as [[q' l']|] eqn:Hpn; [|congruence].
        destruct (Hpay q' l' eq_refl) as [-> Hl'].
        apply ldyn_map_qual_agree.
        * unfold hfr, hframe. rewrite Hpn. simpl rd_lab. rewrite HFa. rewrite Hf.
          apply hdr_cond; auto.
        * rewrite HFa. simpl. apply Forall2_lagree_refl.
        * rewrite HFa. simpl. constructor.
      + rewrite (no_mut_lit_unm f _ Hm). apply ldyn_map_qual_agree.
        * unfold hfr, hframe. rewrite HFa. rewrite Hf.
          apply hdr_cond_unm; auto.
        * rewrite HFa. simpl. apply Forall2_lagree_refl.
        * rewrite HFa. simpl. constructor. }
    destruct Hp as [Hp | [Hp | [Hi Hp]]]; [ | right; left; exact Hp | ].
    + left. destruct (q_eq_dec q1 Bot) as [-> | Hq1].
      * cbn [ldyn map_qual] in Hp |- *. left. split; [reflexivity|].
        destruct Hp as [(_ & Vs & Hv & Hlen) | (_ & _ & Vs & Hv & Hle)].
        -- exists Vs. split; auto. rewrite Hlen. rewrite !length_map. reflexivity.
        -- exists Vs. split; auto. rewrite (Forall2_length Hle).
           rewrite !length_map. reflexivity.
      * eapply lsubtp_agree_r; [exact Hp|]. exact (Hagr Hq1).
    + right. right. split; [exact Hi|].
      eapply lsubtp_agree_r; [exact Hp|]. apply Hagr.
      destruct Hi as [-> _]. discriminate.
  - intros o n K Bs Hb Hnd Hsn.
    destruct (tv_bound_class_env _ _ _ _ Hb) as [-> Hnb].
    pose proof (Forall2_nth_error_rel _ _ _ n Hall) as Hrel. rewrite Hnb in Hrel.
    destruct (nth_error As n) as [A|] eqn:HA; [|contradiction].
    destruct Hrel as [_ [_ Hc]].
    rewrite (HXg n A HA) in Hnd, Hsn |- *.
    exact (Hc Mut K Bs eq_refl eq_refl Hnd Hsn).
Qed.

(** The arguments of a new object, each read against its class's bound. *)
Lemma alloc_fits2 : forall CT L Δ qthis wf mode lc lm qc Ts,
  wf_class_table CT ->
  readonly_state_method_scope (tv_mode Δ) ->
  (forall o n B, tv_bound Δ o n = Some B -> is_class_type B) ->
  frame_fits CT L Δ (act_frame qthis wf mode lc lm) ->
  frame_fitsp CT L Δ (act_frame qthis wf mode lc lm) ->
  fcoh CT L Δ (act_frame qthis wf mode lc lm) ->
  Forall rlost_free (map erase lc) -> Forall rlost_free (map erase lm) ->
  Forall lost_free Ts ->
  forall Xs Bs,
    Forall (sbnd CT Δ) Xs -> Forall lost_free Xs ->
    Forall2
      (fun T B =>
         lost_free (member_type AbstractState (qc2q qc) Ts [] B) /\
         bound_sub CT Δ T (member_type AbstractState (qc2q qc) Ts [] B))
      Xs Bs ->
    Forall2
      (fun A B =>
         (lsubt CT L A
            (ldyn (mk_lframe (qr2q (vpa_mutability_object_creation qthis qc))
                     (LIn wf) (olab (new_color qc wf mode))
                     (map (ldyn (act_frame qthis wf mode lc lm)) Ts) [])
               (map_qual (vpa_q AbstractState (qc2q qc)) B)) /\
          rlost_free (erase
            (ldyn (mk_lframe (qr2q (vpa_mutability_object_creation qthis qc))
                     (LIn wf) (olab (new_color qc wf mode))
                     (map (ldyn (act_frame qthis wf mode lc lm)) Ts) [])
               (map_qual (vpa_q AbstractState (qc2q qc)) B)))) /\
         fit3p CT L A
           (ldyn (mk_lframe (qr2q (vpa_mutability_object_creation qthis qc))
                    (LIn wf) (olab (new_color qc wf mode))
                    (map (ldyn (act_frame qthis wf mode lc lm)) Ts) [])
              (map_qual (vpa_q AbstractState (qc2q qc)) B)) /\
         (forall q0 K Xs', B = TClass q0 K Xs' -> q0 = Mut ->
            ~ deadA CT A -> ~ insaneA CT A -> scoh CT L A K))
      (map (ldyn (act_frame qthis wf mode lc lm)) Xs) Bs.
Proof.
  intros CT L Δ qthis wf mode lc lm qc Ts Hwf Hrs Hbc Hfits Hfitp Hcoh Hlc Hlm
    HlfT Xs Bs HsbX HlfX HF.
  remember (act_frame qthis wf mode lc lm) as Fc eqn:HFc.
  assert (Hconc : lf_q Fc = Mut \/ lf_q Fc = Imm).
  { rewrite HFc. simpl. destruct qthis; auto. }
  assert (Hlc' : Forall rlost_free (map erase (lf_cargs Fc))).
  { rewrite HFc. exact Hlc. }
  assert (Hlm' : Forall rlost_free (map erase (lf_margs Fc))).
  { rewrite HFc. exact Hlm. }
  revert HsbX HlfX.
  induction HF as [|T B Xs Bs [Hlf Hbs] HF IH]; intros HsbX HlfX; simpl;
    constructor.
  2: { apply IH; [exact (Forall_inv_tail HsbX) | exact (Forall_inv_tail HlfX)]. }
  pose proof (Forall_inv HsbX) as HsbT. pose proof (Forall_inv HlfX) as HlfT0.
  pose proof (sub_lsubt CT Δ L Fc Hrs Hconc Hfits _ _
                (bound_sub_self _ _ _ _ Hbs)) as Hs.
  assert (Hrl : rlost_free (erase (ldyn Fc
            (member_type AbstractState (qc2q qc) Ts [] B)))).
  { rewrite erase_ldyn. rewrite HFc. simpl.
    apply dyn_lost_free; auto. apply qr2q_concrete. }
  destruct (fit3 CT L Δ Fc Hwf Hrs Hconc Hbc Hfits Hfitp Hcoh Hlc' Hlm' T
              (member_type AbstractState (qc2q qc) Ts [] B) HsbT HlfT0
              (bound_sub_self _ _ _ _ Hbs)) as [H3 Hc3].
  unfold member_type, adapt in Hs, Hrl, H3. rewrite ldyn_subst in Hs, Hrl, H3.
  simpl map in Hs, Hrl, H3.
  assert (Hfwd : lagree L
            (ldyn (lf_with_args Fc (map (ldyn Fc) Ts) [])
               (map_qual (vpa_q AbstractState (qc2q qc)) B))
            (ldyn (mk_lframe
                     (qr2q (vpa_mutability_object_creation qthis qc))
                     (LIn wf) (olab (new_color qc wf mode))
                     (map (ldyn Fc) Ts) [])
               (map_qual (vpa_q AbstractState (qc2q qc)) B))).
  { apply ldyn_map_qual_agree2.
    - rewrite HFc. apply alloc_read_cond.
    - simpl. apply Forall2_lagree_refl.
    - simpl. constructor. }
  assert (Hbwd : lagree L
            (ldyn (mk_lframe
                     (qr2q (vpa_mutability_object_creation qthis qc))
                     (LIn wf) (olab (new_color qc wf mode))
                     (map (ldyn Fc) Ts) [])
               (map_qual (vpa_q AbstractState (qc2q qc)) B))
            (ldyn (lf_with_args Fc (map (ldyn Fc) Ts) [])
               (map_qual (vpa_q AbstractState (qc2q qc)) B))).
  { apply ldyn_map_qual_agree2.
    - rewrite HFc. apply alloc_read_cond_rev.
    - simpl. apply Forall2_lagree_refl.
    - simpl. constructor. }
  refine (conj (conj _ _) (conj _ _)).
  - eapply lsubt_agree_r; eauto.
  - rewrite (lagree_erase_eq L _ _ Hbwd Hrl). exact Hrl.
  - eapply fit3p_agree; eauto.
  - intros q0 K Xs' -> -> Hnd Hsn.
    eapply Hc3; [| | exact Hnd | exact Hsn].
    + unfold member_type, adapt. cbn [map_qual subst]. reflexivity.
    + destruct qc; reflexivity.
Qed.

Lemma alloc_fitsp : forall CT L Δ qthis wf mode lc lm qc C def Ts,
  wf_class_table CT ->
  readonly_state_method_scope (tv_mode Δ) ->
  (forall o n B, tv_bound Δ o n = Some B -> is_class_type B) ->
  frame_fits CT L Δ (act_frame qthis wf mode lc lm) ->
  frame_fitsp CT L Δ (act_frame qthis wf mode lc lm) ->
  fcoh CT L Δ (act_frame qthis wf mode lc lm) ->
  Forall rlost_free (map erase lc) -> Forall rlost_free (map erase lm) ->
  find_class CT C = Some def ->
  Forall lost_free Ts -> Forall (sbnd CT Δ) Ts ->
  Forall2
    (fun T B =>
       lost_free (member_type AbstractState (qc2q qc) Ts [] B) /\
       bound_sub CT Δ T (member_type AbstractState (qc2q qc) Ts [] B))
    Ts (ctparams (signature def)) ->
  frame_fitsp CT L (class_env def)
    (hfr CT (vpa_mutability_object_creation qthis qc)
       (olab (new_color qc wf mode)) C
       (map (ldyn (act_frame qthis wf mode lc lm)) Ts)) /\
  fcoh CT L (class_env def)
    (hfr CT (vpa_mutability_object_creation qthis qc)
       (olab (new_color qc wf mode)) C
       (map (ldyn (act_frame qthis wf mode lc lm)) Ts)).
Proof.
  intros CT L Δ qthis wf mode lc lm qc C def Ts Hwf Hrs Hbc Hfits Hfitp Hcoh
    Hlc Hlm Hfind HlfT HsbT Hbounds.
  eapply (pfit_of_fits CT L (vpa_mutability_object_creation qthis qc) qc
            (olab (new_color qc wf mode)) (LIn wf) C def _ Hwf Hfind).
  - destruct qthis, qc; reflexivity.
  - intros ->. reflexivity.
  - eapply alloc_fits2; eauto.
Qed.

(** From a class to its parent. *)
Lemma step_fitsp : forall CT L qo l C As def P Ss sd,
  wf_class_table CT ->
  find_class CT C = Some def ->
  super (signature def) = Some (P, Ss) ->
  find_class CT P = Some sd ->
  vpa_mutability_runtime_bound_agree qo (class_qualifier (signature def)) = true ->
  Forall rlost_free (map erase As) ->
  (class_qualifier (signature def) = Mut_c ->
   norm L (lf_mut (hfr CT qo l C As)) = norm L l) ->
  hfit CT L qo l C As ->
  frame_fitsp CT L (class_env def) (hfr CT qo l C As) ->
  fcoh CT L (class_env def) (hfr CT qo l C As) ->
  frame_fitsp CT L (class_env sd)
    (hfr CT qo l P (map (ldyn (hfr CT qo l C As)) Ss)) /\
  fcoh CT L (class_env sd)
    (hfr CT qo l P (map (ldyn (hfr CT qo l C As)) Ss)).
Proof.
  intros CT L qo l C As def P Ss sd Hwf Hfind Hsuper Hsd Hag Hlf Hmc Hfit
    Hfitp Hcoh.
  remember (hfr CT qo l C As) as Fh eqn:HFh.
  destruct (wf_class_super_bsub _ _ _ _ _ Hwf Hfind Hsuper)
    as (sd' & Hsd' & Hbnds).
  rewrite Hsd in Hsd'. inversion Hsd'; subst sd'. clear Hsd'.
  destruct (wf_class_super_inv _ _ _ _ _ Hwf Hfind Hsuper)
    as (sd' & Hsd' & _ & HlfS & _).
  clear sd' Hsd'.
  pose proof (wf_class_super_sbnd _ _ _ _ _ Hwf Hfind Hsuper) as HsbS.
  assert (Hconc : lf_q Fh = Mut \/ lf_q Fh = Imm).
  { rewrite HFh. unfold hfr. simpl. destruct qo; auto. }
  assert (Hfit' : frame_fits CT L (class_env def) Fh).
  { rewrite HFh. exact (Hfit def Hfind). }
  assert (Hbc : forall o n B, tv_bound (class_env def) o n = Some B ->
                              is_class_type B).
  { intros o n B Hb. destruct (tv_bound_class_env _ _ _ _ Hb) as [_ Hnb].
    pose proof (class_bounds_class _ _ _ Hwf Hfind) as Hcls.
    rewrite Forall_forall in Hcls. exact (Hcls _ (nth_error_In _ _ Hnb)). }
  assert (Hlc' : Forall rlost_free (map erase (lf_cargs Fh))).
  { rewrite HFh. exact Hlf. }
  assert (Hlm' : Forall rlost_free (map erase (lf_margs Fh))).
  { rewrite HFh. constructor. }
  assert (HFa : lf_with_args Fh (map (ldyn Fh) Ss) [] =
                mk_lframe (qr2q qo) (lf_mut Fh) l (map (ldyn Fh) Ss) []).
  { rewrite HFh. reflexivity. }
  eapply (pfit_of_fits CT L qo (class_qualifier (signature def)) l (lf_mut Fh)
            P sd (map (ldyn Fh) Ss) Hwf Hsd Hag Hmc).
  rewrite <- HFa.
  assert (Hgen : forall Xs Bs,
            Forall (sbnd CT (class_env def)) Xs -> Forall lost_free Xs ->
            Forall2
              (fun T B =>
                 lost_free (member_type AbstractState
                              (qc2q (class_qualifier (signature def))) Ss [] B) /\
                 bound_sub CT (class_env def) T
                   (member_type AbstractState
                      (qc2q (class_qualifier (signature def))) Ss [] B))
              Xs Bs ->
            Forall2
              (fun A B =>
                 (lsubt CT L A
                    (ldyn (lf_with_args Fh (map (ldyn Fh) Ss) [])
                       (map_qual (vpa_q AbstractState
                                    (qc2q (class_qualifier (signature def)))) B)) /\
                  rlost_free (erase
                    (ldyn (lf_with_args Fh (map (ldyn Fh) Ss) [])
                       (map_qual (vpa_q AbstractState
                                    (qc2q (class_qualifier (signature def)))) B)))) /\
                 fit3p CT L A
                   (ldyn (lf_with_args Fh (map (ldyn Fh) Ss) [])
                      (map_qual (vpa_q AbstractState
                                   (qc2q (class_qualifier (signature def)))) B)) /\
                 (forall q0 K Xs', B = TClass q0 K Xs' -> q0 = Mut ->
                    ~ deadA CT A -> ~ insaneA CT A -> scoh CT L A K))
              (map (ldyn Fh) Xs) Bs).
  { intros Xs Bs HsbX HlfX HF. revert HsbX HlfX.
    induction HF as [|T B Xs Bs [Hlfb Hbs] HF IH]; intros HsbX HlfX; simpl;
      constructor.
    2: { apply IH; [exact (Forall_inv_tail HsbX) | exact (Forall_inv_tail HlfX)]. }
    pose proof (Forall_inv HsbX) as HsbT. pose proof (Forall_inv HlfX) as HlfT0.
    pose proof (sub_lsubt CT (with_mode (class_env def) ReadonlyState) L Fh
                  (or_introl eq_refl) Hconc
                  (fun o0 n0 B0 Hb0 => Hfit' o0 n0 B0 Hb0)
                  _ _ (Hbs ReadonlyState)) as Hs.
    assert (Hrl : rlost_free (erase (ldyn Fh
              (member_type AbstractState
                 (qc2q (class_qualifier (signature def))) Ss [] B)))).
    { rewrite erase_ldyn. rewrite HFh. unfold hfr. simpl.
      apply dyn_lost_free; auto; try apply qr2q_concrete; try constructor. }
    destruct (fit3 CT L (with_mode (class_env def) ReadonlyState) Fh Hwf
                (or_introl eq_refl) Hconc
                (fun o0 n0 B0 Hb0 => Hbc o0 n0 B0 Hb0)
                (fun o0 n0 B0 Hb0 => Hfit' o0 n0 B0 Hb0)
                (fun o0 n0 B0 Hb0 => Hfitp o0 n0 B0 Hb0)
                (fun o0 n0 K0 Bs0 Hb0 => Hcoh o0 n0 K0 Bs0 Hb0)
                Hlc' Hlm' T
                (member_type AbstractState
                   (qc2q (class_qualifier (signature def))) Ss [] B)
                (sbnd_mode _ _ _ _ HsbT) HlfT0 (Hbs ReadonlyState))
      as [H3 Hc3].
    unfold member_type, adapt in Hs, Hrl, H3. rewrite ldyn_subst in Hs, Hrl, H3.
    simpl map in Hs, Hrl, H3.
    refine (conj (conj Hs Hrl) (conj H3 _)).
    intros q0 K Xs' -> -> Hnd Hsn.
    eapply Hc3; [| | exact Hnd | exact Hsn].
    + unfold member_type, adapt. cbn [map_qual subst]. reflexivity.
    + destruct (class_qualifier (signature def)); reflexivity. }
  exact (Hgen _ _ HsbS HlfS Hbnds).
Qed.

(** Along an object's view. *)
Lemma fitsp_oview : forall CT L qo l C As D Vs,
  wf_class_table CT ->
  oview CT qo l C As D Vs ->
  hinv CT L qo l C As ->
  (forall def, find_class CT C = Some def ->
     frame_fitsp CT L (class_env def) (hfr CT qo l C As) /\
     fcoh CT L (class_env def) (hfr CT qo l C As)) ->
  forall def, find_class CT D = Some def ->
    frame_fitsp CT L (class_env def) (hfr CT qo l D Vs) /\
    fcoh CT L (class_env def) (hfr CT qo l D Vs).
Proof.
  intros CT L qo l C As D Vs Hwf H. unfold oview in H.
  induction H; intros Hi Hc; [exact Hc|].
  rewrite hstep_obj in H, IHview.
  destruct (hinv_step CT L qo l C As P Ss Hwf Hi Hparent) as [HiP _].
  apply IHview; auto.
  intros sd Hsd.
  destruct Hi as (Hfit & Hlf & Hcls).
  unfold parent_lookup in Hparent.
  destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
  destruct (Hcls def eq_refl) as [Hag Hmc].
  destruct (Hc def eq_refl) as [Hfp Hco].
  exact (step_fitsp CT L qo l C As def P Ss sd Hwf Hfind Hparent Hsd Hag Hlf Hmc
           Hfit Hfp Hco).
Qed.

Print Assumptions fit3.
Print Assumptions alloc_fitsp.
Print Assumptions fitsp_oview.
