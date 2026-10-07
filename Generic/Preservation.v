From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall.

(** Type preservation for generic PICO with casts.

    A successful big-step evaluation of a well-typed statement from a
    well-formed configuration ends in a well-formed configuration.  Calls
    dispatch on the receiver's runtime class, so the method that runs may
    override the one the caller's typing saw. *)
Theorem preservation_pico : forall CT rΓ h s res rΓ' h',
    eval_stmt CT rΓ h s res rΓ' h' ->
    res = OK ->
    forall Δ sΓ mt sΓ',
      wf_r_config CT Δ sΓ rΓ h ->
      stmt_typing CT Δ sΓ mt s sΓ' ->
      wf_r_config CT Δ sΓ' rΓ' h'.
Proof.
  intros CT rΓ h s res rΓ' h' Heval.
  induction Heval; intros Hres Δ sΓ mt0 sΓ' Hwf Htype; try discriminate.
  - (* skip *)
    inversion Htype; subst. exact Hwf.
  - (* local *)
    inversion Htype; subst. apply preservation_local; auto.
  - (* assignment *)
    eapply preservation_varass; eauto.
  - (* field write *)
    subst. eapply preservation_fldwrite; eauto.
  - (* object creation *)
    subst. eapply preservation_new; eauto.
  - (* call *)
    subst.
    destruct (call_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                Hwf Htype Hval_y Hbase Hfind Hargs Hframe)
      as (ι & o & oy & Tx & Hthis & Hobj & Hoy & Hget_x & Hx & -> &
          Hfb & Hwm & Hcfg & Hthis' & Hret & _).
    pose proof Hwm as
      (_ & _ & _ & (sΓb & Tb & Hbody & Hnthb & Hsubb) & _ & _).
    pose proof (IHHeval eq_refl _ _ _ _ Hcfg Hbody) as Hcfg''.
    destruct (eval_stmt_frame _ _ _ _ _ _ Heval _ _ _ _ Hbody)
      as (Hth_eq & Hca_eq & Hma_eq).
    pose proof (eval_stmt_heap_ext _ _ _ _ _ _ _ Heval) as Hext.
    destruct (heap_ext_getObj _ _ _ _ Hext Hoy) as (oy' & Hoy' & Hrt_oy).
    destruct (heap_ext_getObj _ _ _ _ Hext Hobj) as (o' & Hobj' & Hrt_o).
    destruct (wf_r_config_this _ _ _ _ _ Hcfg'')
      as (ι2 & o2 & Hth2 & Hobj2 & _ & _ & _ & Hfb2).
    rewrite Hth_eq in Hth2. rewrite Hthis' in Hth2. inversion Hth2; subst ι2.
    rewrite Hoy' in Hobj2. inversion Hobj2; subst o2. clear Hth2 Hobj2.
    assert (Hth'' : get_this_var_mapping (vars rΓ'') = Some ly) by congruence.
    pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hcfg'' Hth'' Hoy' Hnthb) as Hrv.
    rewrite Hretval in Hrv.
    assert (Hrv' : val_typable CT h' retval
                     (mret (msignature mdef)) (rqtype (rt_type oy'))
                     (cargs rΓ'') (margs rΓ'')).
    { eapply val_typable_subtype; eauto. }
    rewrite Hca_eq in Hrv'. rewrite Hma_eq in Hrv'. rewrite Hrt_oy in Hrv'.
    apply Hret in Hrv'.
    pose proof Hcfg'' as (_ & Hheap' & _).
    pose proof (wf_r_config_heap_ext _ _ _ _ _ _ Hwf Hext Hheap') as Hwf'.
    eapply wf_r_config_update_var; eauto.
    rewrite Hrt_o. exact Hrv'.
  - (* cast *)
    eapply preservation_cast; eauto.
  - (* sequence *)
    inversion Htype; subst. eauto.
Qed.

Print Assumptions preservation_pico.
