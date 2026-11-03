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
    (mk_lframe (qr2q qo) lmP l cs [] []) (mk_lframe (qr2q qo) lmC l cs [] []).
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
    (mk_lframe (qr2q qo) lmP l cs [] []) (mk_lframe (qr2q qo) lmC l cs [] []).

(** Place in the proof: fits in the header frame and their step to the parent
    class; a type written mutable; static bounds; payload-view fits from
    head-view fits; well-formed bounds in scope.  The bridge between the ghost
    fit and the payload-view fit.
    Counterpart in the non-generic proof (ReadonlyWorlds.v): none. *)
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

Lemma norm_nil : forall l, norm [] l = None.
Proof. intros [w|]; reflexivity. Qed.

(** The payload view takes no payload either: every head-view fit is a
    payload-view fit. *)
Lemma frame_fitsp_of_fits : forall CT L Δ F,
  frame_fits CT L Δ F -> frame_fitsp CT L Δ F.
Proof. intros CT L Δ F H o n B Hb. left. apply lsubtp_of_lsubt. exact (H o n B Hb). Qed.

(** In an abstract-state class qualifier that is not mutable, only a written
    [Mut] reads as [Mut]. *)
Lemma vpa_as_mut_only : forall cq q0,
  cq <> Mut_c -> vpa_q AbstractState (qc2q cq) q0 = Mut -> q0 = Mut.
Proof. intros [] q0 Hne H; [congruence | destruct q0; cbv in H; congruence..]. Qed.

(** A node in which the search finds nothing has bottom nodes at every
    position where the bound writes a mutable qualifier, so it agrees with the
    bound read under any label of such positions. *)
Lemma bwalk_relabel : forall CT L f hq lm lm' lr As B V,
  (forall q0, f q0 = Mut -> q0 = Mut) -> f Mut = Mut ->
  pwalk CT B V = None ->
  bagree L V (ldyn (mk_lframe hq lm lr As [] []) (map_qual f B)) ->
  bagree L V (ldyn (mk_lframe hq lm' lr As [] []) (map_qual f B)).
Proof.
  intros CT L f hq lm lm' lr As B. induction B using qualified_type_ind';
    intros V Hfm Hf Hp Hle.
  - destruct V as [q1 l1 C0 As0]. cbn [ldyn map_qual] in Hle |- *.
    inversion Hle as [? ? ? ? ? ? ? Hq Hlab Hargs]; subst.
    assert (Hdesc : pwalks CT args As0 = None ->
              Forall2 (bagree L) As0
                (map (ldyn (mk_lframe hq lm' lr As [] [])) (map (map_qual f) args))).
    { intros Hpw. clear Hq Hlab Hle Hp. revert As0 Hargs Hpw.
      induction H as [|B Bs HB HBs IH]; intros As0 Hargs Hpw; simpl in Hargs;
        inversion Hargs as [|A0 ? As0' ? HA Hrest]; subst; simpl; constructor.
      - simpl in Hpw. destruct (pwalk CT B A0) eqn:Hx; [discriminate|]. eapply HB; eauto.
      - apply IH; auto. simpl in Hpw. destruct (pwalk CT B A0); [discriminate | exact Hpw]. }
    destruct (q_eq_dec (f qual) Mut) as [Hfq | Hfq].
    + pose proof (Hfm qual Hfq) as Hqm. subst qual.
      destruct (q_eq_dec q1 Bot) as [-> | Hb1].
      * rewrite (pwalk_class CT Mut C args Bot l1 C As0 (or_intror eq_refl)) in Hp.
        simpl in Hp. rewrite Nat.eqb_refl in Hp.
        constructor.
        -- rewrite Hf. left. split; [reflexivity | simpl; discriminate].
        -- right. left. discriminate.
        -- exact (Hdesc Hp).
      * exfalso. rewrite (pwalk_mut CT C args q1 l1 C As0 Hb1) in Hp.
        rewrite (pnode_nb q1 l1 Hb1) in Hp. discriminate.
    + assert (Hlabeq : lab_of (mk_lframe hq lm lr As [] []) (f qual) =
                       lab_of (mk_lframe hq lm' lr As [] []) (f qual)).
      { destruct (f qual); simpl; congruence. }
      rewrite <- Hlabeq. constructor; auto.
      destruct (q_eq_dec qual Mut) as [-> | Hqm]; [congruence|].
      rewrite (pwalk_class CT qual C args q1 l1 C As0 (or_introl Hqm)) in Hp.
      simpl in Hp. rewrite Nat.eqb_refl in Hp. exact (Hdesc Hp).
  - destruct V as [q1 l1 C0 As0].
    destruct u as [|qv|m]; cbn [ldyn map_qual lf_cargs lf_margs lf_qargs lf_q] in Hle |- *.
    + exact Hle.
    + destruct (q_eq_dec (f qv) Mut) as [Hfq | Hfq].
      * pose proof (Hfm qv Hfq) as Hqm. subst qv. cbn [pwalk] in Hp.
        destruct (q_eq_dec q1 Bot) as [-> | Hb1];
          [| rewrite (pnode_nb q1 l1 Hb1) in Hp; discriminate].
        destruct (match tv_lookup o As [] n with Some A => A | None => ldefault end)
          as [qa la Ca Aa].
        simpl lrehead in Hle |- *. inversion Hle; subst.
        constructor.
        -- rewrite Hf. left. split; [reflexivity | simpl; discriminate].
        -- right. left. discriminate.
        -- assumption.
      * assert (Hlabeq : lab_of (mk_lframe hq lm lr As [] []) (f qv) =
                         lab_of (mk_lframe hq lm' lr As [] []) (f qv)).
        { destruct (f qv); simpl; congruence. }
        rewrite <- Hlabeq. exact Hle.
    + exact Hle.
  - destruct V as [q1 l1 C0 As0]. cbn [ldyn map_qual lf_qargs] in Hle |- *.
    inversion Hle as [? ? ? ? ? ? ? Hq Hlab Hargs]; subst.
    constructor; auto.
    rewrite (pwalk_head CT n C args q1 l1 C As0) in Hp.
    simpl in Hp. rewrite Nat.eqb_refl in Hp.
    clear Hq Hlab Hle. revert As0 Hargs Hp.
    induction H as [|B Bs HB HBs IH]; intros As0 Hargs Hpw; simpl in Hargs;
      inversion Hargs as [|A0 ? As0' ? HA Hrest]; subst; simpl; constructor.
    + simpl in Hpw. destruct (pwalk CT B A0) eqn:Hx; [discriminate|]. eapply HB; eauto.
    + apply IH; auto. simpl in Hpw. destruct (pwalk CT B A0); [discriminate | exact Hpw].
Qed.

Lemma bwalks_relabel : forall CT L f hq lm lm' lr As Bs Vs,
  (forall q0, f q0 = Mut -> q0 = Mut) -> f Mut = Mut ->
  pwalks CT Bs Vs = None ->
  Forall2 (bagree L) Vs (map (ldyn (mk_lframe hq lm lr As [] [])) (map (map_qual f) Bs)) ->
  Forall2 (bagree L) Vs (map (ldyn (mk_lframe hq lm' lr As [] [])) (map (map_qual f) Bs)).
Proof.
  intros CT L f hq lm lm' lr As Bs. induction Bs as [|B Bs IH]; intros Vs Hfm Hf Hp Hle;
    inversion Hle; subst; simpl; constructor.
  - simpl in Hp. destruct (pwalk CT B x) eqn:Hx; [discriminate|].
    eapply bwalk_relabel; eauto.
  - apply IH; auto. simpl in Hp. destruct (pwalk CT B x); [discriminate | exact Hp].
Qed.

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
         (ldyn (mk_lframe (qr2q qo) lm0 l As [] [])
            (map_qual (vpa_q AbstractState (qc2q cq)) B)) /\
       rlost_free (erase
         (ldyn (mk_lframe (qr2q qo) lm0 l As [] [])
            (map_qual (vpa_q AbstractState (qc2q cq)) B))))
    As (ctparams (signature def)) ->
  Forall rlost_free (map erase As) ->
  hfit CT L qo l C As /\
  (forall q' l', pclassf CT C As = Some (q', l') ->
     q' = Mut /\ norm L l' = norm L lm0).
Proof.
  intros CT L qo cq l lm0 C def As Hwf Hfind Hag Hmc Hall HlfA.
  remember (vpa_q AbstractState (qc2q cq)) as f eqn:Hf.
  remember (mk_lframe (qr2q qo) lm0 l As [] []) as Fa eqn:HFa.
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
  destruct B as [qb D Bs|u o0 n0| ? ? ?]; [|contradiction..].
  destruct A as [q1 l1 C1 As1].
  destruct (q_eq_dec q1 Bot) as [-> | Hq1].
  - (* an argument no value has: the bottom reader's view, with the escape *)
    destruct (lsubt_lb _ _ _ _ _ _ _ _ _ _ Hs) as (Vs & Hv & Hle).
    cbn [ldyn map_qual] in Hle.
    cbn [ldyn]. left. split; [reflexivity|]. exists Vs. split; [exact Hv|].
    (* the bound read under two labels of its written mutable positions *)
    assert (Hrd2 : forall lmP lmC,
              norm L lmP = norm L lmC -> (cq = Mut_c -> norm L lmC = norm L l) ->
              Forall2 (lagree L)
                (map (ldyn (mk_lframe (qr2q qo) lmC l As [] [])) (map (map_qual f) Bs))
                (map (ldyn (mk_lframe (qr2q qo) lmP l As [] [])) Bs)).
    { intros lmP lmC H1 H2. rewrite map_map.
      assert (Hid : map (ldyn (mk_lframe (qr2q qo) lmP l As [] [])) Bs =
                    map (fun S => ldyn (mk_lframe (qr2q qo) lmP l As [] [])
                                    (map_qual (fun q0 => q0) S)) Bs).
      { apply map_ext. intros S. rewrite map_qual_id. reflexivity. }
      rewrite Hid. apply map_ldyn_map_qual_agree2; [| simpl; apply Forall2_lagree_refl
                                                     | simpl; constructor | reflexivity].
      intros q0. rewrite Hf.
      destruct qo, cq; try discriminate Hag; destruct q0;
        cbv [vpa_q vpa_mutability_qq_abstract_state qc2q qr2q dynq lf_q lab_of
             lf_mut lf_rdm arg_q_sub];
        (split;
         [ solve [left; reflexivity] || solve [right; split; auto]
         | solve [left; reflexivity] || solve [right; left; discriminate]
           || solve [right; right; reflexivity]
           || solve [right; right; exact (eq_sym H1)]
           || solve [right; right; apply H2; reflexivity] ]). }
    unfold hfr, hframe.
    destruct (pclassf CT C As) as [[q' l']|] eqn:Hpn.
    + (* a payload: its label is the fitting frame's *)
      destruct (Hpay q' l' eq_refl) as [-> Hl']. cbn [rd_lab].
      eapply Forall2_bagree_trans_l; [|apply (Hrd2 l' lm0); auto].
      rewrite HFa in Hle. exact Hle.
    + cbn [rd_lab].
      assert (Hdec : cq = Mut_c \/ cq <> Mut_c)
        by (destruct cq; [left; reflexivity | right; discriminate | right; discriminate]).
      destruct Hdec as [-> | Hcq].
      * (* a mutable class: the own label is the fitting frame's *)
        eapply Forall2_bagree_trans_l; [|apply (Hrd2 l lm0); [symmetry; exact (Hmc eq_refl) | exact Hmc]].
        rewrite HFa in Hle. exact Hle.
      * (* nothing found: the argument is bottom at every written mutable position *)
        assert (Hnone : pwalk CT (TClass qb D Bs) (LT Bot l1 C1 As1) = None).
        { destruct (pwalk CT (TClass qb D Bs) (LT Bot l1 C1 As1)) as [x|] eqn:Hx; [|reflexivity].
          exfalso. revert Hpn. unfold pclassf. rewrite Hfind.
          apply (pfindsf_nth CT _ _ n _ _ Hnb HA). cbn [pfindf popen]. rewrite Hx. discriminate. }
        assert (Hle' : Forall2 (bagree L) Vs
                  (map (ldyn (mk_lframe (qr2q qo) l l As [] [])) (map (map_qual f) Bs))).
        { pose proof (fun q0 => vpa_as_mut_only cq q0 Hcq) as Hfm. rewrite <- Hf in Hfm.
          rewrite (pwalk_class CT qb D Bs Bot l1 C1 As1 (or_intror eq_refl)) in Hnone.
          change (prd Bot) with ArgViews.tgb in Hnone.
          rewrite (tviewg_of_lbsuper _ _ _ _ _ Hwf Hv l1) in Hnone.
          rewrite HFa in Hle.
          exact (bwalks_relabel CT L f (qr2q qo) lm0 l l As Bs Vs Hfm HfM Hnone Hle). }
        eapply Forall2_bagree_trans_l; [exact Hle' | apply (Hrd2 l l); auto].
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
      * rewrite HFa. reflexivity.
    + (* the bound writes none *)
      rewrite (no_mut_lit_unm f _ Hm). apply ldyn_map_qual_agree.
      * unfold hfr, hframe. rewrite HFa. rewrite Hf.
        apply hdr_cond_unm; auto.
      * rewrite HFa. simpl. apply Forall2_lagree_refl.
      * rewrite HFa. simpl. constructor.
      * rewrite HFa. reflexivity.
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
  assert (HFa : lf_with_args Fh (map (ldyn Fh) Ss) [] [] =
                mk_lframe (qr2q qo) (lf_mut Fh) l (map (ldyn Fh) Ss) [] []).
  { rewrite HFh. reflexivity. }
  eapply (hfit_of_fits CT L qo (class_qualifier (signature def)) l (lf_mut Fh)
            P sd (map (ldyn Fh) Ss) Hwf Hsd Hag Hmc).
  rewrite <- HFa.
  assert (Hgen : forall Xs Bs,
            Forall2
              (fun T B =>
                 lost_free (member_type AbstractState
                              (qc2q (class_qualifier (signature def))) Ss [] [] B) /\
                 bound_sub CT (class_env def) T
                   (member_type AbstractState
                      (qc2q (class_qualifier (signature def))) Ss [] [] B))
              Xs Bs ->
            Forall2
              (fun A B =>
                 lsubt CT L A
                   (ldyn (lf_with_args Fh (map (ldyn Fh) Ss) [] [])
                      (map_qual (vpa_q AbstractState
                                   (qc2q (class_qualifier (signature def)))) B)) /\
                 rlost_free (erase
                   (ldyn (lf_with_args Fh (map (ldyn Fh) Ss) [] [])
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
                 (qc2q (class_qualifier (signature def))) Ss [] [] B)))).
    { rewrite erase_ldyn. rewrite HFh. unfold hfr. simpl.
      apply dyn_lost_free; auto; try apply qr2q_concrete; try constructor. }
    unfold member_type, adapt in Hs, Hrl. rewrite ldyn_subst in Hs, Hrl.
    simpl map in Hs, Hrl. split; assumption. }
  exact (Hgen _ _ Hbnds).
  destruct (wf_class_super_inv _ _ _ _ _ Hwf Hfind Hsuper) as (sd'' & _ & _ & HlfS & _).
  rewrite map_erase_ldyn. rewrite HFh. unfold hfr. simpl.
  apply map_dyn_lost_free; auto; try apply qr2q_concrete; try constructor.
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
Lemma alloc_read_cond : forall L qthis qc wf mode cs cs' ms' ks',
  label_cond2 L (vpa_q AbstractState (qc2q qc)) (vpa_q AbstractState (qc2q qc))
    (lf_with_args (act_frame qthis wf mode cs' ms' ks') cs [] [])
    (mk_lframe (qr2q (vpa_mutability_object_creation qthis qc)) (LIn wf)
       (olab (new_color qc wf mode)) cs [] []).
Proof.
  intros L qthis qc wf mode cs cs' ms' ks' q0.
  destruct q0, qc, qthis, mode;
    cbv [act_frame lf_with_args lf_q lab_of lf_mut lf_rdm vpa_q
         vpa_mutability_qq_abstract_state qc2q qr2q dynq olab
         vpa_mutability_object_creation new_color arg_q_sub];
    rd_solve.
Qed.

Lemma alloc_read_cond_rev : forall L qthis qc wf mode cs cs' ms' ks',
  label_cond2 L (vpa_q AbstractState (qc2q qc)) (vpa_q AbstractState (qc2q qc))
    (mk_lframe (qr2q (vpa_mutability_object_creation qthis qc)) (LIn wf)
       (olab (new_color qc wf mode)) cs [] [])
    (lf_with_args (act_frame qthis wf mode cs' ms' ks') cs [] []).
Proof.
  intros L qthis qc wf mode cs cs' ms' ks' q0.
  destruct q0, qc, qthis, mode;
    cbv [act_frame lf_with_args lf_q lab_of lf_mut lf_rdm vpa_q
         vpa_mutability_qq_abstract_state qc2q qr2q dynq olab
         vpa_mutability_object_creation new_color arg_q_sub];
    rd_solve.
Qed.

(** At an allocation: the new object's arguments fit its class's bounds in
    the header frame, whatever its mutability and colour, and its payload,
    when there is one, is a mutable node of the allocating world. *)
Lemma alloc_hfit : forall CT L Δ qthis wf mode lc lm lk qc C def Ts,
  wf_class_table CT ->
  readonly_state_method_scope (tv_mode Δ) ->
  frame_fits CT L Δ (act_frame qthis wf mode lc lm lk) ->
  Forall rlost_free (map erase lc) -> Forall rlost_free (map erase lm) ->
  Forall (fun q0 => q0 <> Lost) (map fst lk) ->
  find_class CT C = Some def ->
  Forall lost_free Ts ->
  Forall2
    (fun T B =>
       lost_free (member_type AbstractState (qc2q qc) Ts [] [] B) /\
       bound_sub CT Δ T (member_type AbstractState (qc2q qc) Ts [] [] B))
    Ts (ctparams (signature def)) ->
  hfit CT L (vpa_mutability_object_creation qthis qc)
    (olab (new_color qc wf mode)) C
    (map (ldyn (act_frame qthis wf mode lc lm lk)) Ts) /\
  (forall q' l',
     pclassf CT C (map (ldyn (act_frame qthis wf mode lc lm lk)) Ts) = Some (q', l') ->
     q' = Mut /\ norm L l' = norm L (LIn wf)).
Proof.
  intros CT L Δ qthis wf mode lc lm lk qc C def Ts Hwf Hrs Hfits Hlc Hlm Hlk Hfind
    HlfT Hbounds.
  remember (act_frame qthis wf mode lc lm lk) as Fc eqn:HFc.
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
                   lost_free (member_type AbstractState (qc2q qc) Ts [] [] B) /\
                   bound_sub CT Δ T (member_type AbstractState (qc2q qc) Ts [] [] B))
                Xs Bs ->
              Forall2
                (fun A B =>
                   lsubt CT L A
                     (ldyn (mk_lframe
                              (qr2q (vpa_mutability_object_creation qthis qc))
                              (LIn wf) (olab (new_color qc wf mode))
                              (map (ldyn Fc) Ts) [] [])
                        (map_qual (vpa_q AbstractState (qc2q qc)) B)) /\
                   rlost_free (erase
                     (ldyn (mk_lframe
                              (qr2q (vpa_mutability_object_creation qthis qc))
                              (LIn wf) (olab (new_color qc wf mode))
                              (map (ldyn Fc) Ts) [] [])
                        (map_qual (vpa_q AbstractState (qc2q qc)) B))))
                (map (ldyn Fc) Xs) Bs).
    { intros Xs Bs HF. induction HF as [|T B Xs Bs [Hlf Hbs] HF IH]; simpl;
        constructor; auto.
      pose proof (sub_lsubt CT Δ L Fc Hrs Hconc Hfits _ _
                    (bound_sub_self _ _ _ _ Hbs)) as Hs.
      assert (Hrl : rlost_free (erase (ldyn Fc
                (member_type AbstractState (qc2q qc) Ts [] [] B)))).
      { rewrite erase_ldyn. rewrite HFc. simpl.
        apply dyn_lost_free; auto. apply qr2q_concrete. }
      unfold member_type, adapt in Hs, Hrl. rewrite ldyn_subst in Hs, Hrl.
      simpl map in Hs, Hrl.
      assert (Hfwd : lagree L
                (ldyn (lf_with_args Fc (map (ldyn Fc) Ts) [] [])
                   (map_qual (vpa_q AbstractState (qc2q qc)) B))
                (ldyn (mk_lframe
                         (qr2q (vpa_mutability_object_creation qthis qc))
                         (LIn wf) (olab (new_color qc wf mode))
                         (map (ldyn Fc) Ts) [] [])
                   (map_qual (vpa_q AbstractState (qc2q qc)) B))).
      { apply ldyn_map_qual_agree2.
        - rewrite HFc. apply alloc_read_cond.
        - simpl. apply Forall2_lagree_refl.
        - simpl. constructor.
        - reflexivity. }
      assert (Hbwd : lagree L
                (ldyn (mk_lframe
                         (qr2q (vpa_mutability_object_creation qthis qc))
                         (LIn wf) (olab (new_color qc wf mode))
                         (map (ldyn Fc) Ts) [] [])
                   (map_qual (vpa_q AbstractState (qc2q qc)) B))
                (ldyn (lf_with_args Fc (map (ldyn Fc) Ts) [] [])
                   (map_qual (vpa_q AbstractState (qc2q qc)) B))).
      { apply ldyn_map_qual_agree2.
        - rewrite HFc. apply alloc_read_cond_rev.
        - simpl. apply Forall2_lagree_refl.
        - simpl. constructor.
        - reflexivity. }
      split.
      - eapply lsubt_agree_r; eauto.
      - rewrite (lagree_erase_eq L _ _ Hbwd Hrl). exact Hrl. }
    exact (Hgen _ _ Hbounds).
  - exact HlfA.
Qed.

(** The whole bundle for a new object; and when the object is in the
    allocating world, its payload is of its own label. *)
Lemma alloc_hinv : forall CT L Δ qthis wf mode lc lm lk qc C def Ts,
  wf_class_table CT ->
  readonly_state_method_scope (tv_mode Δ) ->
  frame_fits CT L Δ (act_frame qthis wf mode lc lm lk) ->
  Forall rlost_free (map erase lc) -> Forall rlost_free (map erase lm) ->
  Forall (fun q0 => q0 <> Lost) (map fst lk) ->
  find_class CT C = Some def ->
  vpa_mutability_bound (qc2q qc) (class_qualifier (signature def)) = qc2q qc ->
  Forall lost_free Ts ->
  Forall2
    (fun T B =>
       lost_free (member_type AbstractState (qc2q qc) Ts [] [] B) /\
       bound_sub CT Δ T (member_type AbstractState (qc2q qc) Ts [] [] B))
    Ts (ctparams (signature def)) ->
  hinv CT L (vpa_mutability_object_creation qthis qc)
    (olab (new_color qc wf mode)) C
    (map (ldyn (act_frame qthis wf mode lc lm lk)) Ts) /\
  (new_color qc wf mode = Some wf ->
   pown CT L (LIn wf) C (map (ldyn (act_frame qthis wf mode lc lm lk)) Ts)).
Proof.
  intros CT L Δ qthis wf mode lc lm lk qc C def Ts Hwf Hrs Hfits Hlc Hlm Hlk Hfind
    Hqc HlfT Hbounds.
  destruct (alloc_hfit CT L Δ qthis wf mode lc lm lk qc C def Ts Hwf Hrs Hfits
              Hlc Hlm Hlk Hfind HlfT Hbounds) as [Hfit Hpay].
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
        destruct (pclassf CT C (map (ldyn (act_frame qthis wf mode lc lm lk)) Ts))
          as [[q' l']|] eqn:Hp; [|reflexivity].
        destruct (Hpay q' l' eq_refl) as [-> Hl]. simpl. exact Hl.
  - intros Hc q' l' Hp. exact (Hpay q' l' Hp).
Qed.

(* ------------------STARTING FACTS: A TYPE WRITTEN MUTABLE------------------*)

Lemma static_read_cond : forall L F cs,
  label_cond2 L (vpa_q AbstractState Mut) (vpa_q AbstractState Mut)
    (lf_with_args F cs [] [])
    (mk_lframe Mut (lf_mut F) (lf_mut F) cs [] []).
Proof.
  intros L [qF lm lr c0 m0 k0] cs q0.
  destruct q0;
    cbv [lf_with_args lf_q lab_of lf_mut lf_rdm vpa_q
         vpa_mutability_qq_abstract_state dynq arg_q_sub];
    rd_solve.
Qed.

Lemma static_read_cond_rev : forall L F cs,
  label_cond2 L (vpa_q AbstractState Mut) (vpa_q AbstractState Mut)
    (mk_lframe Mut (lf_mut F) (lf_mut F) cs [] [])
    (lf_with_args F cs [] []).
Proof.
  intros L [qF lm lr c0 m0 k0] cs q0.
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
  Forall (fun q0 => q0 <> Lost) (map fst (lf_qargs F)) ->
  find_class CT C = Some def ->
  class_qualifier (signature def) <> Imm_c ->
  Forall2
    (fun T B =>
       lost_free (subst Ts [] [] (adapt AbstractState Mut B)) ->
       bound_sub CT Δ T (subst Ts [] [] (adapt AbstractState Mut B)))
    Ts (ctparams (signature def)) ->
  Forall lost_free Ts ->
  Forall (fun B => lost_free (subst Ts [] [] (adapt AbstractState Mut B)))
    (ctparams (signature def)) ->
  hinv CT L Mut_r (lf_mut F) C (map (ldyn F) Ts) /\
  pown CT L (lf_mut F) C (map (ldyn F) Ts).
Proof.
  intros CT L Δ F C Ts def Hwf Hrs Hconc Hfits Hlc Hlm Hlk Hfind Hhead Hbounds HlfT HlfB.
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
                   lost_free (subst Ts [] [] (adapt AbstractState Mut B)) ->
                   bound_sub CT Δ T (subst Ts [] [] (adapt AbstractState Mut B)))
                Xs Bs ->
              Forall (fun B => lost_free (subst Ts [] [] (adapt AbstractState Mut B)))
                Bs ->
              Forall2
                (fun A B =>
                   lsubt CT L A
                     (ldyn (mk_lframe (qr2q Mut_r) (lf_mut F) (lf_mut F)
                              (map (ldyn F) Ts) [] [])
                        (map_qual (vpa_q AbstractState (qc2q Mut_c)) B)) /\
                   rlost_free (erase
                     (ldyn (mk_lframe (qr2q Mut_r) (lf_mut F) (lf_mut F)
                              (map (ldyn F) Ts) [] [])
                        (map_qual (vpa_q AbstractState (qc2q Mut_c)) B))))
                (map (ldyn F) Xs) Bs).
    { intros Xs Bs HF. induction HF as [|T B Xs Bs Hb HF IH]; intros HlB; simpl;
        constructor; inversion HlB as [|? ? Hlf HlB']; subst; auto.
      pose proof (sub_lsubt CT Δ L F Hrs Hconc Hfits _ _
                    (bound_sub_self _ _ _ _ (Hb Hlf))) as Hs.
      assert (Hrl : rlost_free (erase (ldyn F
                (subst Ts [] [] (adapt AbstractState Mut B))))).
      { rewrite erase_ldyn. apply dyn_lost_free; auto. }
      unfold adapt in Hs, Hrl. rewrite ldyn_subst in Hs, Hrl.
      simpl map in Hs, Hrl.
      assert (Hfwd : lagree L
                (ldyn (lf_with_args F (map (ldyn F) Ts) [] [])
                   (map_qual (vpa_q AbstractState Mut) B))
                (ldyn (mk_lframe Mut (lf_mut F) (lf_mut F) (map (ldyn F) Ts) [] [])
                   (map_qual (vpa_q AbstractState Mut) B))).
      { apply ldyn_map_qual_agree2.
        - apply static_read_cond.
        - simpl. apply Forall2_lagree_refl.
        - simpl. constructor.
        - reflexivity. }
      assert (Hbwd : lagree L
                (ldyn (mk_lframe Mut (lf_mut F) (lf_mut F) (map (ldyn F) Ts) [] [])
                   (map_qual (vpa_q AbstractState Mut) B))
                (ldyn (lf_with_args F (map (ldyn F) Ts) [] [])
                   (map_qual (vpa_q AbstractState Mut) B))).
      { apply ldyn_map_qual_agree2.
        - apply static_read_cond_rev.
        - simpl. apply Forall2_lagree_refl.
        - simpl. constructor.
        - reflexivity. }
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
  exact (conj Hi Hk).
Qed.

Print Assumptions hfit_of_fits.
Print Assumptions hinv_oview.
Print Assumptions alloc_hinv.
Print Assumptions static_mut_pcoh.

(* ------------------STATIC BOUNDS------------------*)

Definition sbnd (CT : class_table) (Δ : tv_env) (T : qualified_type) : Prop :=
  match T with
  | TClass q0 C Ts =>
      q0 = Mut -> exists def, find_class CT C = Some def /\
        Forall2
          (fun T B =>
             lost_free (subst Ts [] [] (adapt AbstractState Mut B)) ->
             bound_sub CT Δ T (subst Ts [] [] (adapt AbstractState Mut B)))
          Ts (ctparams (signature def))
  | TVar _ _ _ => True
  | THead _ _ _ => True
  end.

Lemma sbnd_of_wf : forall CT Δ T, wf_stype CT Δ T -> sbnd CT Δ T.
Proof.
  intros CT Δ T H. inversion H; subst; simpl; auto.
  intros Hq. subst. exists def. split; [assumption|].
  eapply Forall2_impl; [|eassumption]. intros a b Hab _. exact Hab.
Qed.

Lemma sbnd_mode : forall CT Δ m T, sbnd CT Δ T -> sbnd CT (with_mode Δ m) T.
Proof.
  intros CT Δ m [q0 C Ts|u o n| ? ? ?]; simpl; auto.
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
        inversion Hw as [? ? ? ? ? ? ? Hargs ?| |]; subst
    end.
    eapply Forall_impl; [|exact Hargs]. intros a Ha.
    exact (sbnd_of_wf _ _ _ Ha).
Qed.

(** A static type, read in a frame, is coherent as far as it is written
    mutable. *)
(* ------------------PAYLOAD-VIEW FITS FROM HEAD-VIEW FITS------------------*)

(** The payload view takes no payload either, so the head-view fit of a
    static subtyping gives the payload-view fit directly. *)
Lemma fit3 : forall CT L Δ F,
  readonly_state_method_scope (tv_mode Δ) ->
  (lf_q F = Mut \/ lf_q F = Imm) ->
  frame_fits CT L Δ F ->
  forall T U, qualified_type_subtype CT Δ T U ->
    fit3p CT L (ldyn F T) (ldyn F U).
Proof.
  intros CT L Δ F Hrs Hq Hfit T U Hsub. left. apply lsubtp_of_lsubt.
  eapply sub_lsubt; eauto.
Qed.

Lemma alloc_fitsp : forall CT L Δ qthis wf mode lc lm lk qc C def Ts,
  wf_class_table CT ->
  readonly_state_method_scope (tv_mode Δ) ->
  frame_fits CT L Δ (act_frame qthis wf mode lc lm lk) ->
  Forall rlost_free (map erase lc) -> Forall rlost_free (map erase lm) ->
  Forall (fun q0 => q0 <> Lost) (map fst lk) ->
  find_class CT C = Some def ->
  Forall lost_free Ts ->
  Forall2
    (fun T B =>
       lost_free (member_type AbstractState (qc2q qc) Ts [] [] B) /\
       bound_sub CT Δ T (member_type AbstractState (qc2q qc) Ts [] [] B))
    Ts (ctparams (signature def)) ->
  frame_fitsp CT L (class_env def)
    (hfr CT (vpa_mutability_object_creation qthis qc)
       (olab (new_color qc wf mode)) C
       (map (ldyn (act_frame qthis wf mode lc lm lk)) Ts)).
Proof.
  intros CT L Δ qthis wf mode lc lm lk qc C def Ts Hwf Hrs Hfit Hlc Hlm Hlk Hfind HlfT Hb.
  apply frame_fitsp_of_fits.
  destruct (alloc_hfit CT L Δ qthis wf mode lc lm lk qc C def Ts Hwf Hrs Hfit Hlc Hlm Hlk
              Hfind HlfT Hb) as [Hh _].
  exact (Hh def Hfind).
Qed.

(** Along an object's view. *)
Lemma fitsp_oview : forall CT L qo l C As D Vs,
  wf_class_table CT ->
  oview CT qo l C As D Vs ->
  hinv CT L qo l C As ->
  forall def, find_class CT D = Some def ->
    frame_fitsp CT L (class_env def) (hfr CT qo l D Vs).
Proof.
  intros CT L qo l C As D Vs Hwf Hv Hi def Hfd.
  destruct (hinv_oview _ _ _ _ _ _ _ _ Hwf Hv Hi) as [(Hfit & _ & _) _].
  apply frame_fitsp_of_fits. exact (Hfit def Hfd).
Qed.

Print Assumptions fit3.
Print Assumptions alloc_fitsp.
Print Assumptions fitsp_oview.

(* ------------------WELL-FORMED BOUNDS IN SCOPE------------------*)

(** The arguments of every class-type bound in scope fit their class. *)
Definition bwf (CT : class_table) (Δ : tv_env) : Prop :=
  forall o n qb0 C0 Ts0, tv_bound Δ o n = Some (TClass qb0 C0 Ts0) ->
    exists def0, find_class CT C0 = Some def0 /\
      Forall2 (fun T B => bound_sub CT Δ T (subst Ts0 [] [] (adapt AbstractState qb0 B)))
        Ts0 (ctparams (signature def0)).

Lemma bwf_of_wf : forall CT Δ,
  (forall o n B, tv_bound Δ o n = Some B -> wf_stype CT Δ B) -> bwf CT Δ.
Proof.
  intros CT Δ H o n qb0 C0 Ts0 Hb. pose proof (H _ _ _ Hb) as Hw.
  inversion Hw; subst. eauto.
Qed.

(** Subtyping survives adding type variables. *)
Lemma subtype_env_ext : forall CT Δ1 Δ2 T U,
  qualified_type_subtype CT Δ1 T U ->
  tv_mode Δ1 = tv_mode Δ2 -> qparams Δ1 <= qparams Δ2 ->
  (forall o n B, tv_bound Δ1 o n = Some B -> tv_bound Δ2 o n = Some B) ->
  qualified_type_subtype CT Δ2 T U.
Proof.
  intros CT Δ1 Δ2 T U H Hm Hk Hb.
  induction H; try (econstructor; eauto; fail);
    econstructor; try rewrite <- Hm; eauto; lia.
Qed.

Lemma bound_sub_env_ext : forall CT Δ1 Δ2 T U,
  bound_sub CT Δ1 T U ->
  qparams Δ1 <= qparams Δ2 ->
  (forall o n B, tv_bound Δ1 o n = Some B -> tv_bound Δ2 o n = Some B) ->
  bound_sub CT Δ2 T U.
Proof.
  intros CT Δ1 Δ2 T U H Hk Hb m.
  eapply subtype_env_ext; [exact (H m) | reflexivity | exact Hk |].
  intros o n B HB. exact (Hb o n B HB).
Qed.

Lemma bwf_mode : forall CT Δ m, bwf CT Δ -> bwf CT (with_mode Δ m).
Proof.
  intros CT Δ m H o n qb0 C0 Ts0 Hb. destruct (H o n qb0 C0 Ts0 Hb) as (d & Hd & Hf).
  exists d. split; auto.
Qed.

Lemma bwf_class_env : forall CT C def,
  wf_class_table CT -> find_class CT C = Some def -> bwf CT (class_env def).
Proof.
  intros CT C def Hwf Hfind. apply bwf_of_wf. intros o n B Hb.
  destruct (tv_bound_class_env _ _ _ _ Hb) as [-> HnB].
  pose proof (class_bounds_wf _ _ _ Hwf Hfind) as Hw. rewrite Forall_forall in Hw.
  exact (Hw _ (nth_error_In _ _ HnB)).
Qed.

Lemma bwf_method_env : forall CT C md,
  wf_class_table CT -> wf_method CT C md ->
  bwf CT (method_tv_env CT C (msignature md)).
Proof.
  intros CT C md Hwf Hm o n qb0 C0 Ts0 Hb.
  destruct o.
  - unfold tv_bound, method_tv_env, class_tparams in Hb. simpl in Hb.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|destruct n; discriminate].
    pose proof (class_bounds_wf _ _ _ Hwf Hfind) as Hw. rewrite Forall_forall in Hw.
    pose proof (Hw _ (nth_error_In _ _ Hb)) as HwB.
    inversion HwB; subst. exists def0. split; auto.
    eapply Forall2_impl; [|exact Hbounds]. intros T B HTB.
    eapply bound_sub_env_ext; [exact HTB | simpl; lia |].
    intros o' n' B' HB'. destruct o'; simpl in HB' |- *.
    + unfold class_tparams. rewrite Hfind. exact HB'.
    + destruct n'; discriminate.
  - unfold wf_method in Hm. destruct Hm as (_ & Hmt & _).
    rewrite Forall_forall in Hmt.
    unfold tv_bound, method_tv_env in Hb. simpl in Hb.
    destruct (Hmt _ (nth_error_In _ _ Hb)) as (_ & HwB & _).
    inversion HwB; subst. eauto.
Qed.
