From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation.

(** Field writes through a receiver whose static view is not mutable.

    This is the local fact behind readonly-state and transitive-state
    preservation: such a write can only store into a slot declared
    assignable, and is not typable at all in the modes with strict
    assignability. *)

Lemma non_mut_receiver_write_assignable : forall mt qx a0,
  qx <> Mut ->
  vpa_a mt qx a0 = Assignable ->
  a0 = Assignable /\ ~ strict_assignability_method_scope mt.
Proof.
  intros mt qx a0 Hq H.
  destruct mt, qx, a0; simpl in H; try discriminate; try congruence;
    (split; [reflexivity|]); intros [Hs | Hs]; discriminate.
Qed.

Theorem non_mut_receiver_write_preservation :
  forall CT Δ sΓ mt rΓ h x f0 y sΓ' rΓ' h' Tx qx C Ts l qr Co Ro vals f,
    wf_r_config CT Δ sΓ rΓ h ->
    stmt_typing CT Δ sΓ mt (SFldWrite x f0 y) sΓ' ->
    static_getType sΓ x = Some Tx ->
    ubound Δ Tx = Some (TClass qx C Ts) ->
    qx <> Mut ->
    eval_stmt CT rΓ h (SFldWrite x f0 y) OK rΓ' h' ->
    runtime_getObj h l = Some (mkObj (mkruntime_type qr Co Ro) vals) ->
    (sf_assignability_rel CT Co f Final \/
     sf_assignability_rel CT Co f RDA \/
     strict_assignability_method_scope mt) ->
    exists vals',
      runtime_getObj h' l = Some (mkObj (mkruntime_type qr Co Ro) vals') /\
      nth_error vals f = nth_error vals' f.
Proof.
  intros CT Δ sΓ mt rΓ h x f0 y sΓ' rΓ' h' Tx qx C Ts l qr Co Ro vals f
    Hwf Htype HTx Hub Hq Heval Hl Hprot.
  inversion Htype; subst.
  rewrite HTx in Hget_x. inversion Hget_x; subst Tx0. clear Hget_x.
  rewrite Hub in Hub0. inversion Hub0; subst. clear Hub0.
  destruct (non_mut_receiver_write_assignable _ _ _ Hq Hassignable)
    as [Hdecl Hnonstrict].
  inversion Heval; subst.
  destruct (Nat.eq_dec loc_x l) as [-> | Hne].
  - rewrite Hl in Hobj. inversion Hobj; subst o. clear Hobj. simpl in *.
    rewrite (update_field_getObj_same _ _ _ _ _ Hl). simpl.
    eexists. split; [reflexivity|].
    destruct (Nat.eq_dec f0 f) as [-> | Hnf].
    + exfalso.
      destruct (wf_r_config_this _ _ _ _ _ Hwf)
        as (ι & othis & Hthis & Hobjt & _ & _ & _ & Hfb).
      pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobjt HTx) as Hxty.
      rewrite Hval_x in Hxty.
      pose proof (wf_r_typable_ubound _ _ _ _ _ _ _ _ _ Hfb Hub Hxty) as Hxty'.
      destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ Hxty')
        as (ox & Vs & Hox & _ & Hsup & _).
      rewrite Hl in Hox. inversion Hox; subst ox. simpl in Hsup.
      destruct Hassign as (fdO & HlookO & Ha).
      inversion HlookO as [? ? fsO ? ? HcfO HgetO]; subst.
      inversion Hfld_def as [? ? fsC ? ? HcfC HgetC]; subst.
      destruct (field_inherit _ _ _ _ _ _ Hsup _ _ _ _ HcfC HcfO HgetC)
        as (fd' & Hnth' & Hassign_eq & _).
      unfold gget in HgetO. rewrite HgetO in Hnth'. inversion Hnth'; subst fd'.
      assert (Hrt : sf_assignability_rel CT Co f Assignable).
      { exists fdO. split; [exact HlookO | congruence]. }
      destruct Hprot as [Hp | [Hp | Hstrict]].
      * pose proof (sf_assignability_deterministic_rel _ _ _ _ _ Hrt Hp).
        discriminate.
      * pose proof (sf_assignability_deterministic_rel _ _ _ _ _ Hrt Hp).
        discriminate.
      * exact (Hnonstrict Hstrict).
    + symmetry. apply update_diff; auto.
  - rewrite update_field_getObj_diff; auto.
    exists vals. split; auto.
Qed.

Print Assumptions non_mut_receiver_write_preservation.
