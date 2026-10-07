From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases
  PreservationCall ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels
  GhostTyping.

(** Forgetting the mutable positions of a type: a written [Mut] becomes
    [Lost].  Subtyping in readonly-state and transitive-state code keeps
    labels on the forgotten types even when the labels at the forgotten
    positions are not known. *)

Definition fl (q0 : q) : q := match q0 with Mut => Lost | _ => q0 end.
Notation fT := (map_qual fl).

Lemma fl_ne : forall q0, q0 <> Mut -> fl q0 = q0.
Proof. intros q0 H. destruct q0; simpl; congruence. Qed.

Lemma map_qual_comp : forall f g T,
  map_qual f (map_qual g T) = map_qual (fun q0 => f (g q0)) T.
Proof.
  intros f g T. induction T using qualified_type_ind'.
  - simpl. f_equal. rewrite map_map. induction H; simpl; auto. f_equal; auto.
  - destruct u; reflexivity.
  - simpl. f_equal. rewrite map_map. induction H; simpl; auto. f_equal; auto.
Qed.

Lemma fT_requalify : forall q0 U, fT (requalify q0 U) = requalify (fl q0) (fT U).
Proof. intros q0 [q1 C a | [|q1] o n | o n C a]; reflexivity. Qed.

Lemma fT_headby : forall U C args,
  fT (headby U C args) = headby (fT U) C (map fT args).
Proof. intros [q1 C1 a | [|q1] o n | o n C1 a] C args; reflexivity. Qed.

Lemma fT_subst : forall Ts Us T,
  fT (subst Ts Us T) = subst (map fT Ts) (map fT Us) (fT T).
Proof.
  intros Ts Us T. induction T using qualified_type_ind'.
  - simpl. f_equal. rewrite map_map. rewrite map_map.
    induction H; simpl; auto. f_equal; auto.
  - assert (Hl : match tv_lookup o (map fT Ts) (map fT Us) n with
                 | Some U => U | None => default_type end =
                 fT (match tv_lookup o Ts Us n with
                     | Some U => U | None => default_type end)).
    { destruct o; simpl; rewrite nth_error_map;
        destruct (nth_error _ n); reflexivity. }
    destruct u as [|qv].
    + change (fT (match tv_lookup o Ts Us n with
                  | Some U => U | None => default_type end) =
              match tv_lookup o (map fT Ts) (map fT Us) n with
              | Some U => U | None => default_type end).
      symmetry. exact Hl.
    + change (fT (requalify qv
                    (match tv_lookup o Ts Us n with
                     | Some U => U | None => default_type end)) =
              requalify (fl qv)
                (match tv_lookup o (map fT Ts) (map fT Us) n with
                 | Some U => U | None => default_type end)).
      rewrite Hl. apply fT_requalify.
  - assert (Hl : match tv_lookup o (map fT Ts) (map fT Us) n with
                 | Some U => U | None => default_type end =
                 fT (match tv_lookup o Ts Us n with
                     | Some U => U | None => default_type end)).
    { destruct o; simpl; rewrite nth_error_map;
        destruct (nth_error _ n); reflexivity. }
    change (fT (headby (match tv_lookup o Ts Us n with
                        | Some U => U | None => default_type end)
                  C (map (subst Ts Us) args)) =
            headby (match tv_lookup o (map fT Ts) (map fT Us) n with
                    | Some U => U | None => default_type end)
              C (map (subst (map fT Ts) (map fT Us)) (map fT args))).
    rewrite Hl. rewrite fT_headby. f_equal.
    rewrite !map_map. induction H; simpl; auto. f_equal; auto.
Qed.

Lemma targ_sub_fl : forall T U, targ_sub T U -> targ_sub (fT T) (fT U).
Proof.
  intros T U H. induction H using targ_sub_ind'.
  - destruct u; constructor.
  - simpl. constructor.
    + destruct H as [-> | [-> [-> | ->]]]; unfold arg_q_sub; simpl; auto.
    + clear H H0. induction H1; simpl; constructor; auto.
  - simpl. constructor.
    clear H. induction H0; simpl; constructor; auto.
Qed.

Lemma fl_closed_clean : forall T, closed_clean T -> fT T = T.
Proof.
  induction T using qualified_type_ind'; simpl; intros Hc; [|contradiction..].
  destruct Hc as [Hq Hgo]. f_equal.
  - destruct Hq as (H1 & _). apply fl_ne. exact H1.
  - induction H; simpl in *; auto. destruct Hgo. f_equal; auto.
Qed.

Lemma no_mut_fT : forall Δ T, no_mut Δ T -> fT T = T.
Proof.
  intros Δ T. induction T using qualified_type_ind'; intros Hnm.
  - inversion Hnm; subst. simpl. f_equal; [apply fl_ne; auto|].
    clear Hnm Hq. induction H; simpl; auto.
    inversion Hargs; subst. f_equal; auto.
  - inversion Hnm; subst; simpl; auto. rewrite fl_ne; auto.
  - inversion Hnm; subst. simpl. f_equal.
    clear Hnm Hbound. induction H; simpl; auto.
    inversion Hargs; subst. f_equal; auto.
Qed.

(* ------------------LABEL CONDITIONS UNDER FORGETTING------------------*)

Lemma label_cond_fl : forall L f Fo Fc,
  label_cond L f Fo Fc -> label_cond L (fun q0 => fl (f q0)) Fo Fc.
Proof.
  intros L f Fo Fc H q0. destruct (H q0) as [Ha Hb].
  destruct (q_eq_dec (f q0) Mut) as [E | E].
  - rewrite E in Ha. rewrite E. simpl in Ha. simpl.
    split; [|left; reflexivity].
    destruct Ha as [Ha | [Ha _]]; [|discriminate].
    rewrite <- Ha. right. split; auto.
  - rewrite (fl_ne _ E). split; auto.
Qed.

Lemma fl_label_cond_mut : forall L mt qo b c As qthis wf mode lc lm,
  readonly_state_method_scope mt ->
  label_cond L (fun q0 => fl (vpa_q mt Mut q0)) (obj_frame qo b c As)
    (act_frame qthis wf mode lc lm).
Proof.
  intros L mt qo b c As qthis wf mode lc lm Hrs q0.
  destruct Hrs as [-> | ->]; destruct q0, qo, qthis; simpl; unfold arg_q_sub;
    (split; [ solve [left; reflexivity] || solve [right; split; auto]
            | solve [left; reflexivity] || solve [right; left; discriminate] ]).
Qed.

Lemma super_inst_ldyn_fl : forall CT mt qh C Ts D Vs,
  super_inst CT mt qh C Ts D Vs ->
  forall L qo b c Fc As,
    label_cond L (fun q0 => fl (vpa_q mt qh q0)) (obj_frame qo b c []) Fc ->
    Forall2 (lagree L) As (map (ldyn Fc) (map fT Ts)) ->
    exists Vs0, lsuper_inst CT qo b c C As D Vs0 /\
                Forall2 (lagree L) Vs0 (map (ldyn Fc) (map fT Vs)).
Proof.
  intros CT mt qh C Ts D Vs H.
  induction H; intros L qo b c Fc As Hcond Hargs.
  - exists As. split; [apply lsi_refl | exact Hargs].
  - destruct (IHsuper_inst L qo b c Fc (map (ldyn (obj_frame qo b c As)) Ss) Hcond)
      as [Vs0 [Hs Hle]].
    { assert (Heq : map (ldyn Fc)
                      (map fT (map (subst Ts []) (map (adapt mt qh) Ss))) =
                    map (ldyn (lf_with_args Fc (map (ldyn Fc) (map fT Ts)) []))
                      (map (map_qual (fun q0 => fl (vpa_q mt qh q0))) Ss)).
      { clear. induction Ss as [|S Ss IH]; simpl; auto.
        f_equal; auto. rewrite fT_subst. unfold adapt. rewrite map_qual_comp.
        rewrite ldyn_subst. reflexivity. }
      rewrite Heq.
      apply map_ldyn_map_qual_agree.
      - apply (label_cond_args L _ _ _ As [] (map (ldyn Fc) (map fT Ts)) [] Hcond).
      - exact Hargs.
      - constructor. }
    exists Vs0. split; auto. eapply lsi_step; eauto.
Qed.

(* ------------------SUBTYPING ON FORGOTTEN TYPES------------------*)

Lemma lhas_subtype_fl : forall P CT Δ h G L next mt qthis wf mode lc lm ca ma,
  heapL P CT h G L next ->
  List.In wf L ->
  readonly_state_method_scope mt ->
  tv_mode Δ = mt ->
  (forall o n B v,
     tv_bound Δ o n = Some B ->
     wf_r_typable CT h v (TVar TVSub o n) qthis ca ma ->
     lhas CT h G L v (ldyn (act_frame qthis wf mode lc lm) (TVar TVSub o n)) ->
     lhas CT h G L v (ldyn (act_frame qthis wf mode lc lm) B)) ->
  (forall o n B, tv_bound Δ o n = Some B -> fT B = B) ->
  frame_bounds_ok CT Δ (qr2q qthis) ca ma ->
  map erase lc = ca -> map erase lm = ma ->
  forall T U,
    qualified_type_subtype CT Δ T U ->
    forall v,
      wf_r_typable CT h v T qthis ca ma ->
      lhas CT h G L v (ldyn (act_frame qthis wf mode lc lm) (fT T)) ->
      lhas CT h G L v (ldyn (act_frame qthis wf mode lc lm) (fT U)).
Proof.
  intros P CT Δ h G L next mt qthis wf mode lc lm ca ma
    HG HwfL Hrs Hmode Hcb Hfl Hfb Hec Hem T U Hsub.
  set (Fc := act_frame qthis wf mode lc lm).
  induction Hsub; intros v Hty Hl.
  - (* same class, widen the qualifier *)
    destruct Hl as (o & Ho & Hh & Vs & Hs & Hle).
    exists o. split; auto. simpl. split.
    + unfold headL. intros Hm. inversion Hqsub; subst.
      * apply Hh. exact Hm.
      * simpl in Hm. discriminate.
      * exfalso. exact (typable_head_not_bot _ _ _ _ _ _ _ Hty eq_refl).
    + exists Vs. split; auto.
      eapply Forall2_lagree_trans; [exact Hle|].
      apply map_ldyn_targ_sub.
      clear - Hargs. induction Hargs; simpl; constructor; auto using targ_sub_fl.
  - (* up the hierarchy *)
    pose proof Hl as (o & Ho & Hh & As & Hs & Hle).
    rewrite Hmode in Hsuper.
    assert (Hcond : label_cond L (fun q0 => fl (vpa_q mt q1 q0))
                      (obj_frame (rqtype (rt_type o)) (g_birth G v) (g_col G v) [])
                      Fc).
    { destruct (q_eq_dec q1 Mut) as [-> | Hne].
      - apply fl_label_cond_mut. exact Hrs.
      - apply label_cond_fl.
        destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ Hty)
          as (o' & Vs' & Ho' & Hhead & _).
        rewrite Ho in Ho'. inversion Ho'; subst o'. clear Ho'.
        assert (Hnb : q1 <> Bot).
        { intros ->. exact (typable_head_not_bot _ _ _ _ _ _ _ Hty eq_refl). }
        change (headL L (g_col G v) (dynq (qr2q qthis) (fl q1))
                  (lab_of Fc (fl q1))) in Hh.
        rewrite (fl_ne _ Hne) in Hh. unfold headL in Hh.
        apply rs_label_cond; auto.
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
    destruct (super_inst_ldyn_fl _ _ _ _ _ _ _ Hsuper L _ _ _ Fc As Hcond Hle)
      as (Vs0 & Hs0 & Hle0).
    exists o. split; auto. simpl. split; [exact Hh|].
    exists Vs0. split; auto. eapply lsuper_inst_trans; eauto.
  - exact Hl.
  - (* a type variable at its bound *)
    rewrite (Hfl _ _ _ Hbound).
    eapply Hcb; eauto.
  - (* widen the written qualifier of a variable use *)
    destruct Hl as (ob & Hob & Hl). exists ob. split; auto.
    simpl in *.
    destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
      as [qa la Ca Aa].
    simpl in *. destruct Hl as (Hh & Vs & Hs & Hle).
    split; [|eauto].
    unfold headL. intros Hm. inversion Hqsub; subst.
    + apply Hh. exact Hm.
    + simpl in Hm. discriminate.
    + exfalso. eapply (typable_whead_not_bot _ _ _ _ _ _ _ Hty). reflexivity.
  - (* view the supplied type as readonly *)
    destruct Hl as (ob & Hob & Hl). exists ob. split; auto.
    simpl in *.
    destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
      as [qa la Ca Aa].
    simpl in *. destruct Hl as (Hh & Vs & Hs & Hle).
    split; [|eauto]. unfold headL. intros Hm. discriminate.
  - (* a qualified variable use at an argument-free bound *)
    pose proof (wf_r_typable_subtype _ _ _ _ _ _ _ _ _ Hfb
                  (qtype_qvar_bound CT Δ q1 o n qb C Hsub) Hty) as Hty'.
    destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ Hty')
      as (ob & Rs' & Hob & _ & Hrs' & Hle').
    simpl in Hle'. inversion Hle'; subst.
    destruct (lsuper_inst_exists _ _ _ _ _ _ Hrs' (rqtype (rt_type ob))
                (g_birth G v) (g_col G v) (g_args G v) eq_refl
                (hl_erase _ _ _ _ _ _ HG _ _ Hob)) as (Vs & Hs & He).
    apply map_eq_nil in He. subst Vs.
    destruct Hl as (ob' & Hob' & Hl).
    exists ob. split; auto. simpl. split.
    + simpl in Hl.
      destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
        as [qa la Ca Aa].
      simpl in Hl. tauto.
    + exists (@nil ltype). split; [exact Hs | constructor].
  - (* a variable-headed class type viewed as readonly *)
    destruct Hl as (ob & Hob & Hl). exists ob. split; auto.
    simpl in *.
    destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
      as [qa la Ca Aa].
    simpl in *. destruct Hl as (Hh & Vs & Hs & Hle).
    split; [unfold headL; intros Hm; discriminate|].
    exists Vs. split; auto.
    eapply Forall2_lagree_trans; [exact Hle|].
    apply map_ldyn_targ_sub.
    clear - Hargs. induction Hargs; simpl; constructor; auto using targ_sub_fl.
  - (* compatible arguments under the same variable head *)
    destruct Hl as (ob & Hob & Hl). exists ob. split; auto.
    simpl in *.
    destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
      as [qa la Ca Aa].
    simpl in *. destruct Hl as (Hh & Vs & Hs & Hle).
    split; [exact Hh|].
    exists Vs. split; auto.
    eapply Forall2_lagree_trans; [exact Hle|].
    apply map_ldyn_targ_sub.
    clear - Hargs. induction Hargs; simpl; constructor; auto using targ_sub_fl.
  - (* up the hierarchy under the same variable head *)
    rewrite Hmode in Hsuper.
    destruct Hl as (ob & Hob & Hl).
    assert (Hcond : label_cond L (fun q0 => fl (vpa_q mt RO q0))
                      (obj_frame (rqtype (rt_type ob)) (g_birth G v) (g_col G v) [])
                      Fc).
    { apply label_cond_fl. apply rs_label_cond; auto; try discriminate.
      unfold head_ok. left. reflexivity. }
    exists ob. split; auto.
    change (ldyn Fc (fT (THead o n C Ts))) with
      (lheadby (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
         C (map (ldyn Fc) (map fT Ts))) in Hl.
    change (ldyn Fc (fT (THead o n D Vs))) with
      (lheadby (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
         D (map (ldyn Fc) (map fT Vs))).
    destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
      as [qa la Ca Aa].
    simpl lheadby in *. destruct Hl as (Hh & As & Hs & Hle).
    destruct (super_inst_ldyn_fl _ _ _ _ _ _ _ Hsuper L _ _ _ Fc As Hcond Hle)
      as (Vs0 & Hs0 & Hle0).
    split; [exact Hh|].
    exists Vs0. split; auto. eapply lsuper_inst_trans; eauto.
  - (* the bottom-qualified type of the class *)
    exfalso. exact (typable_head_not_bot _ _ _ _ _ _ _ Hty eq_refl).
  - (* transitivity *)
    apply IHHsub2.
    + eapply wf_r_typable_subtype; eauto.
    + apply IHHsub1; auto.
Qed.
