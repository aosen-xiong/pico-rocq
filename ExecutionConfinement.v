Require Import Syntax Notations Helpers Typing Subtyping Bigstep Reachability Properties Preservation.
From Stdlib Require Import List Lia Sets.Ensembles.
Import ListNotations.

Definition confined_loc (Q : Ensemble Loc) (cutoff l : Loc) : Prop :=
  In Loc Q l \/ cutoff <= l.

Definition raw_heap_edge (h : heap) (l l' : Loc) : Prop :=
  exists o f,
    runtime_getObj h l = Some o /\
    getVal o.(fields_map) f = Some (Iot l').

Definition env_is_confined (Q : Ensemble Loc) (cutoff : Loc) (rGamma : r_env) : Prop :=
  forall x l, runtime_getVal rGamma x = Some (Iot l) -> confined_loc Q cutoff l.

Definition heap_is_confined (Q : Ensemble Loc) (cutoff : Loc) (h : heap) : Prop :=
  forall l l', confined_loc Q cutoff l -> raw_heap_edge h l l' -> confined_loc Q cutoff l'.

Definition state_is_confined (Q : Ensemble Loc) (cutoff : Loc) (rGamma : r_env) (h : heap) : Prop :=
  env_is_confined Q cutoff rGamma /\ heap_is_confined Q cutoff h.

Lemma wf_config_value_dom : forall CT sGamma rGamma h x l,
  wf_r_config CT sGamma rGamma h ->
  runtime_getVal rGamma x = Some (Iot l) -> l < dom h.
Proof.
  intros CT sGamma rGamma h x l Hwf Hval.
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [[_ [_ Hvals]] _]]].
  apply runtime_getVal_dom in Hval as Hxdom. unfold runtime_getVal in Hval.
  pose proof (Forall_nth_error _ _ _ _ Hvals Hval) as Hvalwf.
  destruct (runtime_getObj h l) eqn:Hobj.
  - apply runtime_getObj_dom in Hobj. exact Hobj.
  - simpl in Hvalwf. rewrite Hobj in Hvalwf. contradiction.
Qed.

Lemma wf_raw_edge_target_dom : forall CT h l l',
  wf_heap CT h -> raw_heap_edge h l l' -> l' < dom h.
Proof.
  intros CT h l l' Hwf [o [f [Hobj Hfield]]].
  specialize (Hwf l). apply runtime_getObj_dom in Hobj as Hldom.
  specialize (Hwf Hldom). unfold wf_obj in Hwf. rewrite Hobj in Hwf.
  destruct Hwf as [_ [fds [Hcollect [Hlen Hvals]]]].
  assert (Hfdom : f < dom (fields_map o)) by (apply getVal_dom in Hfield; exact Hfield).
  assert (Hfd : exists fd, nth_error fds f = Some fd).
  { apply nth_error_Some_exists. rewrite <- Hlen. exact Hfdom. }
  destruct Hfd as [fd Hfd]. unfold getVal in Hfield.
  eapply Forall2_nth_error_prop in Hvals; eauto. simpl in Hvals.
  destruct (runtime_getObj h l') eqn:Htarget; try contradiction.
  apply runtime_getObj_dom in Htarget. exact Htarget.
Qed.

Lemma initial_state_is_confined : forall CT sGamma rGamma h,
  wf_r_config CT sGamma rGamma h ->
  state_is_confined (reachable_locations_from_initial_env CT h rGamma) (dom h) rGamma h.
Proof.
  intros CT sGamma rGamma h Hwf. split.
  - intros x l Hval. left. unfold reachable_locations_from_initial_env.
    exists x, l. split; [exact Hval|]. apply rch_heap.
    eapply wf_config_value_dom; eauto.
  - intros l l' [Hin|Hfresh] [o [f [Hobj Hfield]]].
    + left. unfold reachable_locations_from_initial_env in *.
      destruct Hin as [x [root [Hroot Hreach]]]. exists x, root. split; [exact Hroot|].
      eapply rch_trans; [exact Hreach|]. eapply rch_step; eauto.
      unfold wf_r_config in Hwf. destruct Hwf as [_ [Hheap _]].
      eapply wf_raw_edge_target_dom.
      * exact Hheap.
      * exists o, f. split; [exact Hobj|exact Hfield].
    + apply runtime_getObj_dom in Hobj. lia.
Qed.

Lemma eval_expr_preserves_confinement :
  forall CT rGamma h e l Q cutoff,
    state_is_confined Q cutoff rGamma h ->
    eval_expr OK CT rGamma h e (Iot l) OK rGamma h ->
    confined_loc Q cutoff l.
Proof.
  intros CT rGamma h e l Q cutoff [Henv Hheap] Heval.
  inversion Heval; subst.
  - eapply Henv; eauto.
  - eapply Hheap.
    + eapply Henv; eauto.
    + exists o, f. auto.
Qed.

Lemma raw_edge_after_update : forall h lx old fnew value l l',
  runtime_getObj h lx = Some old ->
  raw_heap_edge (update_field h lx fnew value) l l' ->
  raw_heap_edge h l l' \/ (l = lx /\ value = Iot l').
Proof.
  intros h lx old fnew value l l' Hold [o [f [Hobj Hfield]]].
  destruct (Nat.eq_dec l lx) as [->|Hneq].
  - unfold update_field in Hobj. rewrite Hold in Hobj.
    have Hdom := Hold. apply runtime_getObj_dom in Hdom.
    rewrite runtime_getObj_update_same in Hobj; auto. injection Hobj as <-. simpl in Hfield.
    destruct (Nat.eq_dec f fnew) as [->|Hfdiff].
    + unfold getVal in Hfield.
      assert (Hfdom : fnew < dom (update fnew value (fields_map old))).
      { apply nth_error_Some. rewrite Hfield. discriminate. }
      rewrite update_length in Hfdom.
      pose proof (@update_same Syntax.value fnew value (fields_map old) Hfdom) as Hsame.
      rewrite Hsame in Hfield. injection Hfield as <-. right. auto.
    + left. exists old, f. split; [exact Hold|].
      unfold getVal in *. rewrite update_diff in Hfield; auto.
  - left. unfold update_field in Hobj. rewrite Hold in Hobj.
    rewrite runtime_getObj_update_diff in Hobj; auto. exists o, f. auto.
Qed.

Lemma raw_edge_after_append : forall h o l l',
  raw_heap_edge (h ++ [o]) l l' ->
  raw_heap_edge h l l' \/
  (l = dom h /\ exists f, getVal o.(fields_map) f = Some (Iot l')).
Proof.
  intros h [rt fields] l l' [obj [f [Hobj Hfield]]].
  have Hldom := Hobj. apply runtime_getObj_dom in Hldom.
  rewrite length_app in Hldom. simpl in Hldom.
  destruct (Nat.eq_dec l (dom h)) as [->|Hneq].
  - right. split; [reflexivity|]. rewrite runtime_getObj_last in Hobj.
    injection Hobj as <-. exists f. exact Hfield.
  - left. assert (l < dom h) by lia. rewrite runtime_getObj_last2 in Hobj; auto.
    exists obj, f. auto.
Qed.

Lemma env_confined_lookup_list : forall Q cutoff rGamma xs vals,
  env_is_confined Q cutoff rGamma ->
  runtime_lookup_list rGamma xs = Some vals ->
  forall i l, nth_error vals i = Some (Iot l) -> confined_loc Q cutoff l.
Proof.
  intros Q cutoff rGamma xs vals Henv Hlookup i l Hnth.
  destruct (runtime_lookup_list_nth_zs rGamma xs vals i (Iot l) Hlookup Hnth)
    as [x [_ Hval]]. eapply Henv; eauto.
Qed.

Lemma env_confined_update : forall Q cutoff rGamma x v,
  env_is_confined Q cutoff rGamma ->
  (match v with
   | Null_a => True
   | Iot l => confined_loc Q cutoff l
   | Int _ => True
   end) ->
  env_is_confined Q cutoff (update_r_env_value rGamma x v).
Proof.
  intros Q cutoff rGamma x v Henv Hv y l Hval.
  destruct (Nat.eq_dec y x) as [->|Hneq].
  - apply runtime_getVal_dom in Hval as Hdom.
    destruct v as [|lv|n].
    + assert (Hsame : runtime_getVal (update_r_env_value rGamma x Null_a) x = Some Null_a).
      { apply runtime_getVal_update_same. unfold update_r_env_value in Hdom.
        destruct rGamma; simpl in *; rewrite update_length in Hdom; exact Hdom. }
      rewrite Hval in Hsame. discriminate.
    + assert (Hsame : runtime_getVal (update_r_env_value rGamma x (Iot lv)) x = Some (Iot lv)).
      { apply runtime_getVal_update_same. unfold update_r_env_value in Hdom.
        destruct rGamma; simpl in *; rewrite update_length in Hdom; exact Hdom. }
      rewrite Hval in Hsame. injection Hsame as ->. exact Hv.
    + assert (Hsame : runtime_getVal (update_r_env_value rGamma x (Int n)) x = Some (Int n)).
      { apply runtime_getVal_update_same. unfold update_r_env_value in Hdom.
        destruct rGamma; simpl in *; rewrite update_length in Hdom; exact Hdom. }
      rewrite Hval in Hsame. discriminate.
  - rewrite runtime_getVal_update_diff in Hval; auto. eapply Henv; eauto.
Qed.

Lemma eval_stmt_preserves_confinement :
  forall CT rGamma h stmt result rGamma' h' Q cutoff,
    cutoff <= dom h ->
    state_is_confined Q cutoff rGamma h ->
    eval_stmt OK CT rGamma h stmt result rGamma' h' ->
    state_is_confined Q cutoff rGamma' h'.
Proof.
  intros CT rGamma h stmt result rGamma' h' Q cutoff Hcutoff Hstate Heval.
  remember OK as ok. induction Heval; subst; try discriminate.
  - exact Hstate.
  - destruct Hstate as [Henv Hheap]. split; [|exact Hheap].
    intros y l Hval.
    destruct (Nat.eq_dec y (dom (vars rΓ))) as [->|Hneq].
    + rewrite runtime_getVal_last in Hval.
      destruct T as [q [|C]]; simpl in Hval; discriminate.
    + assert (y < dom (vars rΓ)).
      { apply runtime_getVal_dom in Hval. simpl in Hval. rewrite length_app in Hval. simpl in Hval. lia. }
      rewrite runtime_getVal_last2 in Hval; auto.
      eapply Henv; eauto.
  - destruct Hstate as [Henv Hheap]. split; [|exact Hheap].
    replace (set_vars rΓ (update x v2 (vars rΓ))) with
      (update_r_env_value rΓ x v2) by (destruct rΓ; reflexivity).
    apply env_confined_update; [exact Henv|].
    destruct v2; [trivial| |trivial].
    eapply eval_expr_preserves_confinement; eauto. split; assumption.
  - exact Hstate.
  - destruct Hstate as [Henv Hheap]. split; [exact Henv|].
    intros l l' Hconf Hedge.
    destruct (raw_edge_after_update h loc_x o f val_y l l' Hobj Hedge)
      as [Hold|[-> Hvalue]].
    + eapply Hheap; eauto.
    + destruct val_y; try discriminate. injection Hvalue as <-. eapply Henv; eauto.
  - exact Hstate.
  - exact Hstate.
  - destruct Hstate as [Henv Hheap]. split.
    + replace (set_vars rΓ (update x (Iot (dom h)) (vars rΓ))) with
        (update_r_env_value rΓ x (Iot (dom h))) by (destruct rΓ; reflexivity).
      apply env_confined_update; [exact Henv|]. right. exact Hcutoff.
    + intros l l' Hconf Hedge.
      destruct (raw_edge_after_append h
        _ l l' Hedge)
        as [Hold|[-> [f Hfield]]].
      * eapply Hheap; eauto.
      * eapply env_confined_lookup_list; eauto.
  - assert (Hframeconf : state_is_confined Q cutoff (mkr_env (Iot ly :: vals)) h).
    {
      destruct Hstate as [Henv Hheap]. split; [|exact Hheap].
      intros i l Hval. destruct i as [|i].
      - simpl in Hval. injection Hval as <-. eapply Henv; eauto.
      - simpl in Hval. exact (env_confined_lookup_list Q cutoff rΓ zs vals
          Henv Hargs i l Hval).
    }
    have Hbody := IHHeval Hcutoff Hframeconf eq_refl.
    destruct Hbody as [Henvbody Hheapbody]. split; [|exact Hheapbody].
    replace (set_vars rΓ (update x retval (vars rΓ))) with
      (update_r_env_value rΓ x retval) by (destruct rΓ; reflexivity).
    apply env_confined_update.
    + destruct Hstate; assumption.
    + destruct retval; [trivial| |trivial]. eapply Henvbody; eauto.
  - exact Hstate.
  - eapply IHHeval; eauto.
    destruct Hstate as [Henv Hheap]. split; [|exact Hheap].
    intros i l Hval. destruct i as [|i].
    + simpl in Hval. injection Hval as <-. eapply Henv; eauto.
    + simpl in Hval. exact (env_confined_lookup_list Q cutoff rΓ zs vals
        Henv Hargs i l Hval).
  - eapply IHHeval; eauto.
    destruct Hstate as [Henv Hheap]. split; [|exact Hheap].
    intros i l Hval. destruct i as [|i].
    + simpl in Hval. injection Hval as <-. eapply Henv; eauto.
    + simpl in Hval. exact (env_confined_lookup_list Q cutoff rΓ zs vals
        Henv Hargs i l Hval).
  - have Hmid := IHHeval1 Hcutoff Hstate eq_refl.
    have Hgrow := eval_stmt_preserves_heap_domain_simple CT rΓ h s1 rΓ' h' Heval1.
    exact (IHHeval2 (ltac:(lia)) Hmid eq_refl).
  - eapply IHHeval; eauto.
  - have Hmid := IHHeval1 Hcutoff Hstate eq_refl.
    have Hgrow := eval_stmt_preserves_heap_domain_simple CT rΓ h s1 rΓ' h' Heval1.
    exact (IHHeval2 (ltac:(lia)) Hmid eq_refl).
  - eapply IHHeval; eauto.
  - have Hmid := IHHeval1 Hcutoff Hstate eq_refl.
    have Hgrow := eval_stmt_preserves_heap_domain_simple CT rΓ h s1 rΓ' h' Heval1.
    exact (IHHeval2 (ltac:(lia)) Hmid eq_refl).
  - eapply IHHeval; eauto.
  - eapply IHHeval; eauto.
  - exact Hstate.
Qed.

Lemma confined_eval_preserves_old_object :
  forall CT rGamma h stmt rGamma' h' Q cutoff l C qr vals vals',
    cutoff <= dom h ->
    state_is_confined Q cutoff rGamma h ->
    eval_stmt OK CT rGamma h stmt OK rGamma' h' ->
    runtime_getObj h l = Some (mkObj (mkruntime_type qr C) vals) ->
    runtime_getObj h' l = Some (mkObj (mkruntime_type qr C) vals') ->
    l < cutoff -> ~ In Loc Q l -> vals = vals'.
Proof.
  intros CT rGamma h stmt rGamma' h' Q cutoff l C qr vals vals'
    Hcutoff Hstate Heval Hbefore Hafter Hlt Hnot.
  remember OK as ok. generalize dependent vals. generalize dependent vals'.
  induction Heval; intros; subst; try discriminate.
  - rewrite Hbefore in Hafter. congruence.
  - rewrite Hbefore in Hafter. congruence.
  - rewrite Hbefore in Hafter. congruence.
  - destruct Hstate as [Henv Hheap].
    destruct (Nat.eq_dec loc_x l) as [->|Hneq].
    + have Hconf := Henv x l Hval_x. destruct Hconf; [contradiction|lia].
    + unfold update_field in Hafter. rewrite Hobj in Hafter.
      rewrite runtime_getObj_update_diff in Hafter; auto.
  - apply runtime_getObj_dom in Hbefore as Hdom.
    rewrite runtime_getObj_last2 in Hafter; auto.
  - assert (Hframe : state_is_confined Q cutoff (mkr_env (Iot ly :: vals)) h).
    {
      destruct Hstate as [Henv Hheap]. split; [|exact Hheap].
      intros i loc Hval. destruct i as [|i].
      + simpl in Hval. injection Hval as <-. eapply Henv; eauto.
      + simpl in Hval. exact (env_confined_lookup_list Q cutoff rΓ zs vals
          Henv Hargs i loc Hval).
    }
    eapply IHHeval; eauto.
  - destruct (runtime_preserves_r_type_heap CT rΓ h l
      (mkruntime_type qr C) h' vals s1 rΓ' Hbefore Heval1) as [mid Hmid].
    have Hmidstate := eval_stmt_preserves_confinement CT rΓ h s1 OK rΓ' h'
      Q cutoff Hcutoff Hstate Heval1.
    have Hgrow := eval_stmt_preserves_heap_domain_simple CT rΓ h s1 rΓ' h' Heval1.
    assert (Hfirst : vals = mid) by (eapply IHHeval1; eauto).
    assert (Hsecond : mid = vals') by (eapply IHHeval2; eauto; lia).
    congruence.
  - eapply IHHeval; eauto.
  - eapply IHHeval; eauto.
Qed.

Theorem eval_preserves_old_unreachable_object :
  forall CT sGamma rGamma h stmt rGamma' h' l C qr vals vals',
    wf_r_config CT sGamma rGamma h ->
    eval_stmt OK CT rGamma h stmt OK rGamma' h' ->
    runtime_getObj h l = Some (mkObj (mkruntime_type qr C) vals) ->
    runtime_getObj h' l = Some (mkObj (mkruntime_type qr C) vals') ->
    ~ In Loc (reachable_locations_from_initial_env CT h rGamma) l ->
    vals = vals'.
Proof.
  intros CT sGamma rGamma h stmt rGamma' h' l C qr vals vals'
    Hwf Heval Hbefore Hafter Hnotin.
  eapply (@confined_eval_preserves_old_object
    CT rGamma h stmt rGamma' h'
    (reachable_locations_from_initial_env CT h rGamma)
    (dom h) l C qr vals vals').
  - apply Nat.le_refl.
  - eapply initial_state_is_confined; eauto.
  - exact Heval.
  - exact Hbefore.
  - exact Hafter.
  - apply runtime_getObj_dom in Hbefore. exact Hbefore.
  - exact Hnotin.
Qed.
