From Stdlib Require Import List Lia Bool.

Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels GhostTyping
  GhostForget GhostFit.

(** No qualifier argument of a well-formed activation is unknown; let [auto]
    use this. *)
Global Hint Extern 1 (Forall (fun q0 : q => q0 <> Lost) (qargs _)) =>
  (eapply wf_r_config_qargs; eassumption) : core.

(** The label invariant: transport along heap growth, world opening and
    closing, and variable updates. *)

(** [G'] agrees with [G] on the objects of [h]. *)
Definition gext (h : heap) (G G' : ghost) : Prop :=
  forall l, l < dom h ->
    g_col G' l = g_col G l /\ g_birth G' l = g_birth G l /\
    g_args G' l = g_args G l.

Lemma gext_refl : forall h G, gext h G G.
Proof. intros h G l Hl. auto. Qed.

Lemma gext_trans : forall h h' G1 G2 G3,
  gext h G1 G2 -> gext h' G2 G3 -> dom h <= dom h' -> gext h G1 G3.
Proof.
  intros h h' G1 G2 G3 H12 H23 Hd l Hl.
  destruct (H12 l Hl) as (A1 & A2 & A3).
  destruct (H23 l) as (B1 & B2 & B3); [lia|].
  repeat split; congruence.
Qed.

Lemma lhas_ext : forall CT h h' G G' L v A,
  heap_ext h h' -> gext h G G' ->
  lhas CT h G L v A -> lhas CT h' G' L v A.
Proof.
  intros CT h h' G G' L v A Hext Hg (o & Ho & HA).
  destruct (heap_ext_getObj _ _ _ _ Hext Ho) as (o' & Ho' & Hrt).
  destruct (Hg v (runtime_getObj_dom _ _ _ Ho)) as (E1 & E2 & E3).
  exists o'. split; auto. destruct A as [q0 l D Us].
  rewrite E1. rewrite E2. rewrite E3. rewrite Hrt. exact HA.
Qed.

Lemma norm_cons_cases : forall L w0 l,
  norm L l = norm (w0 :: L) l \/
  (norm L l = None /\ norm (w0 :: L) l = Some w0 /\ ~ List.In w0 L).
Proof.
  intros L w0 [w|]; [|left; reflexivity]. unfold norm.
  destruct (in_dec Nat.eq_dec w L) as [i|n];
    destruct (in_dec Nat.eq_dec w (w0 :: L)) as [i'|n']; auto.
  - exfalso. apply n'. right. exact i.
  - destruct i' as [-> | i']; [auto | contradiction].
Qed.

Lemma headL_pop : forall L w0 c q0 l,
  headL (w0 :: L) c q0 l -> headL L c q0 l.
Proof.
  intros L w0 c q0 l H Hq. specialize (H Hq).
  destruct (norm_cons_cases L w0 l) as [He | (He & He' & Hn)].
  - rewrite He. destruct (norm (w0 :: L) l); auto.
    intros w Hc Hin. apply (H w Hc). right. exact Hin.
  - rewrite He. rewrite He' in H. intros w Hc Hin.
    assert (w = w0) by congruence. subst. contradiction.
Qed.

Lemma lhas_pop : forall CT h G L w0 v A,
  lhas CT h G (w0 :: L) v A -> lhas CT h G L v A.
Proof.
  intros CT h G L w0 v A (o & Ho & HA). exists o. split; auto.
  destruct A as [q0 l D Us]. destruct HA as (Hh & Vs & Hs & Hle).
  split; [eapply headL_pop; eauto|].
  exists Vs. split; auto. eapply Forall2_lagree_pop; eauto.
Qed.

Lemma headL_push : forall L n c q0 l,
  headL L c q0 l -> lab_bound n l -> (forall w, c = Some w -> w < n) ->
  headL (n :: L) c q0 l.
Proof.
  intros L n c q0 l H Hb Hc Hq. specialize (H Hq).
  rewrite (norm_push _ _ _ Hb). destruct (norm L l); auto.
  intros w Hcw [Heq | Hin].
  - specialize (Hc w Hcw). lia.
  - exact (H w Hcw Hin).
Qed.

Lemma lhas_push : forall P CT h G L next v A,
  heapL P CT h G L next ->
  lhas CT h G L v A -> lbound next A ->
  lhas CT h G (next :: L) v A.
Proof.
  intros P CT h G L next v A HG (o & Ho & HA) Hb. exists o. split; auto.
  destruct A as [q0 l D Us]. destruct HA as (Hh & Vs & Hs & Hle).
  apply lbound_node in Hb. destruct Hb as [Hl HUs].
  assert (Hc : forall w, g_col G v = Some w -> w < next).
  { intros w Hw. destruct (hl_col _ _ _ _ _ _ HG _ _ Hw) as (_ & _ & _ & Hlt & _).
    exact Hlt. }
  destruct (hl_bound _ _ _ _ _ _ HG v) as [Hargs Hbirth].
  split; [apply headL_push; auto|].
  exists Vs. split; auto.
  apply Forall2_lagree_push; auto.
  eapply lsuper_inst_lbound; eauto.
Qed.

(* ------------------THE ACTIVATION PART OF THE INVARIANT------------------*)

Record frameL (CT : class_table) (sΓ : s_env) (rΓ : r_env) (h : heap)
    (G : ghost) (L : list nat) (next wf : nat) (mode : bool) (qthis : q_r)
    (lc lm : list ltype) (lk : list (q * lab)) : Prop := {
  fl_live : List.In wf L;
  fl_this : exists ι o,
    get_this_var_mapping (vars rΓ) = Some ι /\
    runtime_getObj h ι = Some o /\
    rqtype (rt_type o) = qthis /\
    (mode = true -> g_col G ι = Some wf);
  fl_ec : map erase lc = cargs rΓ;
  fl_em : map erase lm = margs rΓ;
  fl_ek : map fst lk = qargs rΓ;
  fl_bound : Forall (lbound next) lc /\ Forall (lbound next) lm;
  fl_kbound : Forall (fun p => lab_bound next (snd p)) lk;
  fl_vars : forall x T v,
    static_getType sΓ x = Some T ->
    runtime_getVal rΓ x = Some (Iot v) ->
    lhas CT h G L v (ldyn (act_frame qthis wf mode lc lm lk) T);
}.

Lemma frameL_update : forall CT sΓ rΓ h G L next wf mode qthis lc lm lk x v Tx,
  frameL CT sΓ rΓ h G L next wf mode qthis lc lm lk ->
  x <> 0 ->
  static_getType sΓ x = Some Tx ->
  (forall w, v = Iot w ->
     lhas CT h G L w (ldyn (act_frame qthis wf mode lc lm lk) Tx)) ->
  frameL CT sΓ (set_vars rΓ (update x v (vars rΓ))) h G L next wf mode qthis lc lm lk.
Proof.
  intros CT sΓ rΓ h G L next wf mode qthis lc lm lk x v Tx HF Hx HTx Hnew.
  constructor.
  - exact (fl_live _ _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - destruct (fl_this _ _ _ _ _ _ _ _ _ _ _ _ _ HF) as (ι & o & Hth & Hrest).
    exists ι, o. simpl. rewrite get_this_var_mapping_update; auto.
  - exact (fl_ec _ _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - exact (fl_em _ _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - exact (fl_ek _ _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - exact (fl_bound _ _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - exact (fl_kbound _ _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - intros y T w HT Hv. unfold runtime_getVal in Hv. simpl in Hv.
    destruct (Nat.eq_dec x y) as [-> | Hne].
    + apply nth_error_update_same_inv in Hv. subst v.
      assert (T = Tx) by (unfold static_getType in *; congruence). subst T.
      apply Hnew. reflexivity.
    + rewrite update_diff in Hv; auto.
      eapply (fl_vars _ _ _ _ _ _ _ _ _ _ _ _ _ HF); eauto.
Qed.

Lemma frameL_local : forall CT sΓ rΓ h G L next wf mode qthis lc lm lk T,
  dom sΓ = dom (vars rΓ) ->
  frameL CT sΓ rΓ h G L next wf mode qthis lc lm lk ->
  frameL CT (sΓ ++ [T]) (set_vars rΓ (vars rΓ ++ [Null_a])) h G L next wf mode
    qthis lc lm lk.
Proof.
  intros CT sΓ rΓ h G L next wf mode qthis lc lm lk T Hlen HF.
  constructor.
  - exact (fl_live _ _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - destruct (fl_this _ _ _ _ _ _ _ _ _ _ _ _ _ HF) as (ι & o & Hth & Hrest).
    exists ι, o. simpl. rewrite get_this_var_mapping_app_null_last. auto.
  - exact (fl_ec _ _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - exact (fl_em _ _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - exact (fl_ek _ _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - exact (fl_bound _ _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - exact (fl_kbound _ _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - intros x T0 v HT Hv. unfold static_getType in HT.
    unfold runtime_getVal in Hv. simpl in Hv.
    destruct (Nat.lt_ge_cases x (dom sΓ)) as [Hlt | Hge].
    + rewrite nth_error_app1 in HT; auto.
      rewrite nth_error_app1 in Hv; [lia|].
      eapply (fl_vars _ _ _ _ _ _ _ _ _ _ _ _ _ HF); eauto.
    + rewrite nth_error_app2 in Hv; [lia|].
      destruct (x - dom (vars rΓ)) as [|k]; simpl in Hv; [discriminate|].
      destruct k; discriminate.
Qed.

Lemma frameL_ext : forall CT sΓ rΓ h h' G G' L next next' wf mode qthis lc lm lk,
  frameL CT sΓ rΓ h G L next wf mode qthis lc lm lk ->
  heap_ext h h' -> gext h G G' -> next <= next' ->
  frameL CT sΓ rΓ h' G' L next' wf mode qthis lc lm lk.
Proof.
  intros CT sΓ rΓ h h' G G' L next next' wf mode qthis lc lm lk HF Hext Hg Hle.
  constructor.
  - exact (fl_live _ _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - destruct (fl_this _ _ _ _ _ _ _ _ _ _ _ _ _ HF) as (ι & o & Hth & Ho & Hq & Hm).
    destruct (heap_ext_getObj _ _ _ _ Hext Ho) as (o' & Ho' & Hrt).
    exists ι, o'. rewrite Hrt. repeat split; auto.
    intros Hmode. destruct (Hg ι (runtime_getObj_dom _ _ _ Ho)) as (E1 & _).
    rewrite E1. auto.
  - exact (fl_ec _ _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - exact (fl_em _ _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - exact (fl_ek _ _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - destruct (fl_bound _ _ _ _ _ _ _ _ _ _ _ _ _ HF) as [H1 H2].
    split; eapply Forall_lbound_mono; eauto.
  - eapply Forall_impl; [|exact (fl_kbound _ _ _ _ _ _ _ _ _ _ _ _ _ HF)].
    intros p Hp. eapply lab_bound_mono; eauto.
  - intros x T v HT Hv.
    eapply lhas_ext; eauto.
    eapply (fl_vars _ _ _ _ _ _ _ _ _ _ _ _ _ HF); eauto.
Qed.

(* ------------------THE HEAP PART: TRANSPORT------------------*)

Lemma heapL_bound_frame : forall P CT h G L next l o,
  heapL P CT h G L next ->
  runtime_getObj h l = Some o ->
  frame_bound next
    (obj_frame (rqtype (rt_type o)) (g_birth G l) (g_col G l) (g_args G l)).
Proof.
  intros P CT h G L next l o HG Ho.
  destruct (hl_bound _ _ _ _ _ _ HG l) as [Hargs Hbirth].
  apply obj_frame_bound; auto.
  intros w Hw. destruct (hl_col _ _ _ _ _ _ HG _ _ Hw) as (_ & _ & _ & Hlt & _).
  exact Hlt.
Qed.

(** Opening a fresh world keeps the heap part of the invariant. *)
Lemma heapL_push : forall P CT h G L next,
  heapL P CT h G L next -> heapL P CT h G (next :: L) (S next).
Proof.
  intros P CT h G L next HG. constructor.
  - intros l w Hc. destruct (hl_col _ _ _ _ _ _ HG _ _ Hc) as (H1 & H2 & H3 & H4 & H5).
    repeat split; auto.
  - exact (hl_erase _ _ _ _ _ _ HG).
  - intros l o fs f fd v Ho Hcf Hn Hv.
    eapply lhas_push; eauto.
    + eapply (hl_fields _ _ _ _ _ _ HG); eauto.
    + apply ldyn_lbound. eapply heapL_bound_frame; eauto.
  - intros w [<- | Hin]; [lia|].
    pose proof (hl_live _ _ _ _ _ _ HG _ Hin). lia.
  - intros l. destruct (hl_bound _ _ _ _ _ _ HG l) as [H1 H2]. split.
    + eapply Forall_lbound_mono; [|exact H1]. lia.
    + intros w Hw. specialize (H2 w Hw). lia.
Qed.

(** Closing a world keeps the heap part of the invariant. *)
Lemma heapL_pop : forall P CT h G L w0 next,
  heapL P CT h G (w0 :: L) next -> heapL P CT h G L next.
Proof.
  intros P CT h G L w0 next HG. constructor.
  - exact (hl_col _ _ _ _ _ _ HG).
  - exact (hl_erase _ _ _ _ _ _ HG).
  - intros l o fs f fd v Ho Hcf Hn Hv.
    eapply lhas_pop. eapply (hl_fields _ _ _ _ _ _ HG); eauto.
  - intros w Hin. apply (hl_live _ _ _ _ _ _ HG). right. exact Hin.
  - exact (hl_bound _ _ _ _ _ _ HG).
Qed.

(** A field write keeps the heap part, provided the stored value inhabits the
    field's declared type as the receiver object reads it. *)
Lemma heapL_update : forall P CT h G L next lx ox f0 vy,
  heapL P CT h G L next ->
  runtime_getObj h lx = Some ox ->
  (forall fs fd wv,
     CollectFields CT (rctype (rt_type ox)) fs ->
     nth_error fs f0 = Some fd -> vy = Iot wv ->
     lhas CT h G L wv
       (ldyn (obj_frame (rqtype (rt_type ox)) (g_birth G lx) (g_col G lx)
                (g_args G lx)) (ftype fd))) ->
  heapL P CT (update_field h lx f0 vy) G L next.
Proof.
  intros P CT h G L next lx ox f0 vy HG Hox Hnew.
  pose proof (update_field_heap_ext h lx f0 vy) as Hext.
  constructor.
  - intros l w Hc.
    destruct (hl_col _ _ _ _ _ _ HG _ _ Hc) as (H1 & H2 & H3 & H4 & H5).
    rewrite update_field_length. rewrite update_field_r_muttype. auto.
  - intros l o Ho.
    destruct (Nat.eq_dec lx l) as [-> | Hne].
    + rewrite (update_field_getObj_same _ _ _ _ _ Hox) in Ho.
      inversion Ho; subst o. simpl. exact (hl_erase _ _ _ _ _ _ HG _ _ Hox).
    + rewrite update_field_getObj_diff in Ho; auto.
      exact (hl_erase _ _ _ _ _ _ HG _ _ Ho).
  - intros l o fs f fd v Ho Hcf Hn Hv.
    eapply lhas_ext; [exact Hext | apply gext_refl |].
    destruct (Nat.eq_dec lx l) as [-> | Hne].
    + rewrite (update_field_getObj_same _ _ _ _ _ Hox) in Ho.
      inversion Ho; subst o. simpl in *.
      destruct (Nat.eq_dec f0 f) as [-> | Hnf].
      * apply nth_error_update_same_inv in Hv. subst vy.
        eapply Hnew; eauto.
      * rewrite update_diff in Hv; auto.
        eapply (hl_fields _ _ _ _ _ _ HG); eauto.
    + rewrite update_field_getObj_diff in Ho; auto.
      eapply (hl_fields _ _ _ _ _ _ HG); eauto.
  - exact (hl_live _ _ _ _ _ _ HG).
  - exact (hl_bound _ _ _ _ _ _ HG).
Qed.

(* ------------------STATEMENT CASES------------------*)

(** The data every case starts from. *)
Lemma frame_ctx : forall CT Δ sΓ rΓ h G L next wf mode qthis lc lm lk,
  wf_r_config CT Δ sΓ rΓ h ->
  frameL CT sΓ rΓ h G L next wf mode qthis lc lm lk ->
  exists ι o,
    get_this_var_mapping (vars rΓ) = Some ι /\
    runtime_getObj h ι = Some o /\
    rqtype (rt_type o) = qthis /\
    Forall rlost_free (cargs rΓ) /\ Forall rlost_free (margs rΓ) /\
    frame_bounds_ok CT Δ (qr2q qthis) (cargs rΓ) (margs rΓ) (qargs rΓ).
Proof.
  intros CT Δ sΓ rΓ h G L next wf mode qthis lc lm lk Hwf HF.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & _ & Hlc & Hlm & Hfb).
  destruct (fl_this _ _ _ _ _ _ _ _ _ _ _ _ _ HF) as (ι' & o' & Hth' & Ho' & Hq & _).
  assert (ι' = ι) by congruence. subst ι'.
  rewrite Hobj in Ho'. inversion Ho'; subst o'.
  exists ι, o. rewrite <- Hq. auto 10.
Qed.

(* ------------------ALLOCATION: GHOST DATA------------------*)

(** The ghost state extended at one location. *)
Definition g_new (G : ghost) (n : Loc) (c b : option nat) (a : list ltype)
    : ghost :=
  mk_ghost (fun l => if Nat.eqb l n then c else g_col G l)
           (fun l => if Nat.eqb l n then b else g_birth G l)
           (fun l => if Nat.eqb l n then a else g_args G l).

Lemma g_new_col_same : forall G n c b a, g_col (g_new G n c b a) n = c.
Proof. intros. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.
Lemma g_new_birth_same : forall G n c b a, g_birth (g_new G n c b a) n = b.
Proof. intros. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.
Lemma g_new_args_same : forall G n c b a, g_args (g_new G n c b a) n = a.
Proof. intros. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma g_new_other : forall G n c b a l, l <> n ->
  g_col (g_new G n c b a) l = g_col G l /\
  g_birth (g_new G n c b a) l = g_birth G l /\
  g_args (g_new G n c b a) l = g_args G l.
Proof.
  intros G n c b a l Hne. simpl.
  destruct (Nat.eqb l n) eqn:E; auto.
  apply Nat.eqb_eq in E. contradiction.
Qed.

Lemma gext_new : forall h G c b a, gext h G (g_new G (dom h) c b a).
Proof. intros h G c b a l Hl. apply g_new_other. lia. Qed.

Lemma act_frame_bound : forall n qthis wf mode lc lm lk,
  wf < n -> Forall (lbound n) lc -> Forall (lbound n) lm ->
  Forall (fun p => lab_bound n (snd p)) lk ->
  frame_bound n (act_frame qthis wf mode lc lm lk).
Proof.
  intros n qthis wf mode lc lm lk Hw Hc Hm Hk. unfold frame_bound, act_frame. simpl.
  refine (conj Hw (conj _ (conj Hc (conj Hm Hk)))). destruct mode; simpl; auto.
Qed.

(** The new object reads its own class's member types the way the allocating
    activation reads them through the allocation qualifier. *)
(** The birth world of a new object.  A mutable object is born in the world it
    is in, if any.  An immutable object is in no world; it is born in the
    world of the call that creates it, and that is how a mutable position
    written in its class's declarations is read. *)
Definition new_birth (qn : q_r) (qc : q_c) (wf : nat) (mode : bool) : option nat :=
  match qn with
  | Imm_r => Some wf
  | Mut_r => new_color qc wf mode
  end.

Lemma new_birth_of_color : forall qn qc wf mode w,
  new_color qc wf mode = Some w -> new_birth qn qc wf mode = Some w.
Proof.
  intros [] qc wf mode w H; simpl; auto.
  destruct qc, mode; simpl in H; congruence.
Qed.

Lemma new_birth_is : forall qn qc wf mode w,
  new_birth qn qc wf mode = Some w -> w = wf.
Proof.
  intros [] [] wf [] w H; simpl in H; congruence.
Qed.

Lemma qc_rdm_dec : forall qc : q_c, {qc = RDM_c} + {qc <> RDM_c}.
Proof. intros []; auto; right; discriminate. Qed.

Lemma new_label_cond : forall L mt qthis qc wf mode As lc lm lk cs ms ks,
  readonly_state_method_scope mt ->
  label_cond L (vpa_q mt (qc2q qc))
    (obj_frame (vpa_mutability_object_creation qthis qc)
       (new_birth (vpa_mutability_object_creation qthis qc) qc wf mode)
       (new_color qc wf mode) As)
    (lf_with_args (act_frame qthis wf mode lc lm lk) cs ms ks).
Proof.
  intros L mt qthis qc wf mode As lc lm lk cs ms ks Hrs q0.
  destruct Hrs as [-> | ->]; destruct q0, qc, qthis, mode;
    cbv [obj_frame act_frame lf_with_args lf_q
    lab_of lf_mut lf_rdm vpa_q vpa_mutability_qq_abstract_state
    vpa_mutability_qq_readonly_state qc2q qr2q dynq
    vpa_mutability_object_creation new_birth new_color arg_q_sub];
    (split; [solve [auto] || solve [right; split; auto]
            | solve [right; right; reflexivity]
              || solve [right; left; discriminate]
              || solve [left; reflexivity]]).
Qed.

(* ------------------OBJECTS FIT THEIR CLASS BOUNDS------------------*)

Definition class_env (def : class_def) : tv_env :=
  mk_tv_env (ctparams (signature def)) [] AbstractState 0.

Lemma tv_bound_class_env : forall def o n B,
  tv_bound (class_env def) o n = Some B ->
  o = ClassVar /\ nth_error (ctparams (signature def)) n = Some B.
Proof.
  intros def o n B H. destruct o; simpl in H; auto. destruct n; discriminate.
Qed.

Lemma class_bounds_class : forall CT C def,
  wf_class_table CT -> find_class CT C = Some def ->
  Forall is_class_type (ctparams (signature def)).
Proof.
  intros CT C def Hct Hfind.
  pose proof (wf_class_table_class _ _ _ Hct Hfind) as Hc.
  inversion Hc; subst.
  - rewrite Hno_tparams. constructor.
  - match goal with
    | HH : Forall (fun B => is_class_type B /\ _) _ |- _ =>
        eapply Forall_impl; [|exact HH]; intros a [Ha _]; exact Ha
    end.
Qed.

Lemma class_env_class : forall CT C def,
  wf_class_table CT -> find_class CT C = Some def ->
  forall o n B, tv_bound (class_env def) o n = Some B -> is_class_type B.
Proof.
  intros CT C def Hct Hfind o n B Hb.
  destruct (tv_bound_class_env _ _ _ _ Hb) as [_ Hn].
  pose proof (class_bounds_class _ _ _ Hct Hfind) as Hall.
  rewrite Forall_forall in Hall. apply Hall. eapply nth_error_In; eauto.
Qed.

(** No class type-parameter bound mentions [Mut]. *)
Definition class_bounds_nm (CT : class_table) : Prop :=
  forall C def n B,
    find_class CT C = Some def ->
    nth_error (ctparams (signature def)) n = Some B ->
    is_class_type B /\ no_mut (class_env def) B.

(** Every object's labelled type arguments fit its class's bounds as the
    object itself reads them. *)
Definition obF (CT : class_table) (h : heap) (G : ghost) (L : list nat) : Prop :=
  forall l o def,
    runtime_getObj h l = Some o ->
    find_class CT (rctype (rt_type o)) = Some def ->
    frame_fits CT L (class_env def)
      (obj_frame (rqtype (rt_type o)) (g_birth G l) (g_col G l) (g_args G l)).

Lemma obF_push : forall P CT h G L next,
  heapL P CT h G L next -> obF CT h G L -> obF CT h G (next :: L).
Proof.
  intros P CT h G L next HG Hob l o def Ho Hfc o0 n B Hb.
  pose proof (heapL_bound_frame _ _ _ _ _ _ _ _ HG Ho) as HFb.
  apply lsubt_push.
  - exact (Hob l o def Ho Hfc o0 n B Hb).
  - apply ldyn_lbound. exact HFb.
  - apply ldyn_lbound. exact HFb.
Qed.

Lemma obF_pop : forall CT h G L w0, obF CT h G (w0 :: L) -> obF CT h G L.
Proof.
  intros CT h G L w0 Hob l o def Ho Hfc o0 n B Hb.
  eapply lsubt_pop. eapply Hob; eauto.
Qed.

Lemma obF_update : forall CT h G L lx ox f0 vy,
  obF CT h G L -> runtime_getObj h lx = Some ox ->
  obF CT (update_field h lx f0 vy) G L.
Proof.
  intros CT h G L lx ox f0 vy Hob Hox l o def Ho Hfc.
  destruct (Nat.eq_dec lx l) as [-> | Hne].
  - rewrite (update_field_getObj_same _ _ _ _ _ Hox) in Ho.
    inversion Ho; subst o. simpl in Hfc. simpl.
    exact (Hob _ _ _ Hox Hfc).
  - rewrite update_field_getObj_diff in Ho; auto; try exact (Hob _ _ _ Ho Hfc).
Qed.

Ltac lc_fit_solve Hbc :=
  (split;
   [ solve [left; reflexivity] || solve [right; split; auto]
   | solve [left; reflexivity] || solve [right; left; discriminate]
     || solve [right; right; reflexivity]
     || solve [right; right; rewrite Hbc; reflexivity]
     || solve [right; right; rewrite <- Hbc; reflexivity] ]).

(** A bound of the allocated class, read by the new object and by the
    allocating activation through the allocation qualifier. *)
Lemma new_label_cond_as : forall L qthis qc wf mode As lc lm lk cs ms ks,
  label_cond L (unm (vpa_q AbstractState (qc2q qc)))
    (obj_frame (vpa_mutability_object_creation qthis qc)
       (new_birth (vpa_mutability_object_creation qthis qc) qc wf mode)
       (new_color qc wf mode) As)
    (lf_with_args (act_frame qthis wf mode lc lm lk) cs ms ks).
Proof.
  intros L qthis qc wf mode As lc lm lk cs ms ks q0.
  assert (Hbc : LOut = LOut) by reflexivity.
  destruct q0, qc, qthis, mode;
    cbv [unm obj_frame act_frame lf_with_args lf_q lab_of lf_mut lf_rdm vpa_q
         vpa_mutability_qq_abstract_state qc2q qr2q dynq
         vpa_mutability_object_creation new_birth new_color arg_q_sub];
    lc_fit_solve Hbc.
Qed.

(** The same without forgetting written mutable positions, for an allocation
    at a fixed mutability. *)
Lemma new_label_cond_as_full : forall L qthis qc wf mode As lc lm lk cs ms ks,
  qc <> RDM_c ->
  label_cond L (vpa_q AbstractState (qc2q qc))
    (obj_frame (vpa_mutability_object_creation qthis qc)
       (new_birth (vpa_mutability_object_creation qthis qc) qc wf mode)
       (new_color qc wf mode) As)
    (lf_with_args (act_frame qthis wf mode lc lm lk) cs ms ks).
Proof.
  intros L qthis qc wf mode As lc lm lk cs ms ks Hne q0.
  assert (Hbc : LOut = LOut) by reflexivity.
  destruct qc; [| |congruence]; destruct q0, qthis, mode;
    cbv [obj_frame act_frame lf_with_args lf_q lab_of lf_mut lf_rdm vpa_q
         vpa_mutability_qq_abstract_state qc2q qr2q dynq
         vpa_mutability_object_creation new_birth new_color arg_q_sub];
    lc_fit_solve Hbc.
Qed.

(** A bound of the superclass, read by an object directly and through its
    class's view. *)
Lemma obj_adapt_cond : forall L qr qC b c As Bs cs,
  vpa_mutability_runtime_bound_agree qr qC = true ->
  (qr = Mut_r -> olab b = olab c) ->
  label_cond L (vpa_q AbstractState (qc2q qC))
    (obj_frame qr b c As) (lf_with_args (obj_frame qr b c Bs) cs [] []).
Proof.
  intros L qr qC b c As Bs cs Hag Hbc q0.
  destruct qr.
  - pose proof (Hbc eq_refl) as He. unfold olab in He.
    destruct qC; try discriminate Hag; destruct q0;
      cbv [obj_frame lf_with_args lf_q lab_of lf_mut lf_rdm vpa_q
           vpa_mutability_qq_abstract_state qc2q qr2q dynq arg_q_sub];
      lc_fit_solve He.
  - assert (He : LOut = LOut) by reflexivity.
    destruct qC; try discriminate Hag; destruct q0;
      cbv [obj_frame lf_with_args lf_q lab_of lf_mut lf_rdm vpa_q
           vpa_mutability_qq_abstract_state qc2q qr2q dynq arg_q_sub];
      lc_fit_solve He.
Qed.

Lemma wf_class_super_bsub : forall CT C def P Ss,
  wf_class_table CT ->
  find_class CT C = Some def ->
  super (signature def) = Some (P, Ss) ->
  exists sd,
    find_class CT P = Some sd /\
    Forall2
      (fun T B =>
         lost_free (member_type AbstractState
                      (qc2q (class_qualifier (signature def))) Ss [] [] B) /\
         bound_sub CT (class_env def) T
           (member_type AbstractState
              (qc2q (class_qualifier (signature def))) Ss [] [] B))
      Ss (ctparams (signature sd)).
Proof.
  intros CT C def P Ss Hwf Hfind Hsuper.
  pose proof (wf_class_table_class _ _ _ Hwf Hfind) as Hcls.
  inversion Hcls; subst.
  - congruence.
  - rewrite Hsuper in Hsuper0. inversion Hsuper0; subst.
    exists super_def. split; auto.
Qed.

(** From a class to its superclass. *)
Lemma obF_step : forall CT L qr b c C As def P Ss sd,
  wf_class_table CT ->
  find_class CT C = Some def ->
  super (signature def) = Some (P, Ss) ->
  find_class CT P = Some sd ->
  wf_rtypeuse CT (mkruntime_type qr C (map erase As)) ->
  (qr = Mut_r -> olab b = olab c) ->
  frame_fits CT L (class_env def) (obj_frame qr b c As) ->
  frame_fits CT L (class_env sd)
    (obj_frame qr b c (map (ldyn (obj_frame qr b c As)) Ss)).
Proof.
  intros CT L qr b c C As def P Ss sd Hct Hfind Hsuper Hsd Hrt Hbc Hfit
    o n B Hb.
  set (Fo := obj_frame qr b c As) in *.
  destruct (tv_bound_class_env _ _ _ _ Hb) as [-> Hnb].
  destruct (wf_class_super_bsub _ _ _ _ _ Hct Hfind Hsuper)
    as (sd' & Hsd' & Hbnds).
  rewrite Hsd in Hsd'. inversion Hsd'; subst sd'. clear Hsd'.
  pose proof (Forall2_nth_error_rel _ _ _ n Hbnds) as Hrel. rewrite Hnb in Hrel.
  destruct (nth_error Ss n) as [S|] eqn:HS; [|contradiction].
  destruct Hrel as [Hlf Hbs].
  assert (HX : ldyn (obj_frame qr b c (map (ldyn Fo) Ss)) (TVar TVSub ClassVar n)
               = ldyn Fo S).
  { cbn [ldyn obj_frame lf_cargs lf_margs tv_lookup].
    rewrite nth_error_map. rewrite HS. reflexivity. }
  rewrite HX.
  unfold wf_rtypeuse in Hrt. simpl in Hrt. rewrite Hfind in Hrt.
  destruct Hrt as (Hag & Hlfa & _).
  assert (Hconc : lf_q Fo = Mut \/ lf_q Fo = Imm)
    by (unfold Fo; simpl; destruct qr; auto).
  pose proof (sub_lsubt CT (with_mode (class_env def) ReadonlyState) L Fo
                (or_introl eq_refl) Hconc (fun o0 n0 B0 Hb0 => Hfit o0 n0 B0 Hb0)
                _ _ (Hbs ReadonlyState)) as Hs.
  eapply lsubt_agree_r; [exact Hs|].
  assert (Hrl : rlost_free (erase (ldyn Fo
            (member_type AbstractState (qc2q (class_qualifier (signature def)))
               Ss [] [] B)))).
  { rewrite erase_ldyn. apply dyn_lost_free; auto;
      try apply qr2q_concrete; try constructor. }
  apply lagree_sym; [|exact Hrl].
  unfold member_type, adapt. rewrite ldyn_subst.
  apply ldyn_map_qual_agree.
  - apply obj_adapt_cond; auto.
  - simpl. apply Forall2_lagree_refl.
  - simpl. constructor.
  - reflexivity.
Qed.

Section Cases.
  Variables (P : Loc -> Prop) (CT : class_table) (Δ : tv_env).
  Variables (sΓ : s_env) (rΓ : r_env) (h : heap) (G : ghost).
  Variables (L : list nat) (next wf : nat) (mode : bool).
  Variables (lc lm : list ltype) (lk : list (q * lab)).
  Variables (ι : Loc) (o : Obj).
  Local Notation mt := (tv_mode Δ).
  Local Notation qthis := (rqtype (rt_type o)).
  Hypothesis Hrs : readonly_state_method_scope mt.
  Hypothesis Hnb : nomut_bounds Δ.
  Hypothesis Hwf : wf_r_config CT Δ sΓ rΓ h.
  Hypothesis HG : heapL P CT h G L next.
  Hypothesis HMc : mutcL CT h G.
  Hypothesis HF : frameL CT sΓ rΓ h G L next wf mode qthis lc lm lk.
  Hypothesis Hthis : get_this_var_mapping (vars rΓ) = Some ι.
  Hypothesis Hobj : runtime_getObj h ι = Some o.
  Hypothesis Hfb : frame_bounds_ok CT Δ (qr2q qthis) (cargs rΓ) (margs rΓ) (qargs rΓ).
  Hypothesis Hlfc : Forall rlost_free (cargs rΓ).
  Hypothesis Hlfm : Forall rlost_free (margs rΓ).
  Hypothesis Hfit : frame_fits CT L Δ (act_frame qthis wf mode lc lm lk).

  Let Fc := act_frame qthis wf mode lc lm lk.

  Lemma var_typed : forall x T v,
    static_getType sΓ x = Some T ->
    runtime_getVal rΓ x = Some (Iot v) ->
    wf_r_typable CT h v T qthis (cargs rΓ) (margs rΓ) (qargs rΓ) /\
    lhas CT h G L v (ldyn Fc T).
  Proof.
    intros x T v HT Hv. split.
    - pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj HT) as Hty.
      rewrite Hv in Hty. exact Hty.
    - exact (fl_vars _ _ _ _ _ _ _ _ _ _ _ _ _ HF _ _ _ HT Hv).
  Qed.

  Lemma lsub : forall T U v,
    qualified_type_subtype CT Δ T U ->
    wf_r_typable CT h v T qthis (cargs rΓ) (margs rΓ) (qargs rΓ) ->
    lhas CT h G L v (ldyn Fc T) ->
    lhas CT h G L v (ldyn Fc U).
  Proof.
    intros T U v Hsub Hty Hl.
    exact (lhas_subtype P CT Δ h G L next mt qthis wf mode lc lm lk _ _
             _ HG (fl_live _ _ _ _ _ _ _ _ _ _ _ _ _ HF) Hrs eq_refl
             (vb_of_fits P CT Δ h G L next (act_frame qthis wf mode lc lm lk) _ _ _ qthis
                HG HMc Hfit eq_refl
                (fl_ec _ _ _ _ _ _ _ _ _ _ _ _ _ HF) (fl_em _ _ _ _ _ _ _ _ _ _ _ _ _ HF) (fl_ek _ _ _ _ _ _ _ _ _ _ _ _ _ HF))
             (fun o0 n0 B0 Hb0 => nomut_bounds_head Δ o0 n0 B0 Hnb Hb0) Hfb
             (fl_ec _ _ _ _ _ _ _ _ _ _ _ _ _ HF) (fl_em _ _ _ _ _ _ _ _ _ _ _ _ _ HF) (fl_ek _ _ _ _ _ _ _ _ _ _ _ _ _ HF)
             T U Hsub v Hty Hl).
  Qed.

  (** A receiver seen at the class type through which a member is looked
      up: its object, the object's labelled view at that class, and the
      agreement between the object's reading of a declared member type and
      the activation's reading of the adapted one. *)
  Lemma recv_view : forall T v qx C Ts,
    ubound Δ T = Some (TClass qx C Ts) ->
    wf_r_typable CT h v T qthis (cargs rΓ) (margs rΓ) (qargs rΓ) ->
    lhas CT h G L v (ldyn Fc T) ->
    exists ov As,
      runtime_getObj h v = Some ov /\
      wf_r_typable CT h v (TClass qx C Ts) qthis (cargs rΓ) (margs rΓ) (qargs rΓ) /\
      headL L (g_col G v) (dynq (qr2q qthis) qx) (lab_of Fc qx) /\
      lsuper_inst CT (rqtype (rt_type ov)) (g_birth G v) (g_col G v)
        (rctype (rt_type ov)) (g_args G v) C As /\
      (forall F,
         lagree L
           (ldyn (obj_frame (rqtype (rt_type ov)) (g_birth G v) (g_col G v) As) F)
           (ldyn Fc (member_type mt qx Ts [] [] F))).
  Proof.
    intros T v qx C Ts Hub Hty Hl.
    assert (Hty' : wf_r_typable CT h v (TClass qx C Ts) qthis
                     (cargs rΓ) (margs rΓ) (qargs rΓ)).
    { eapply wf_r_typable_ubound; eauto. }
    assert (Hl' : lhas CT h G L v (ldyn Fc (TClass qx C Ts))).
    { destruct (ubound_subtype CT _ _ _ Hub) as [-> | Hsub]; auto.
      eapply lsub; eauto. }
    pose proof Hl' as (ov & Hov & Hh & As & Hs & Hle).
    pose proof (recv_label_cond _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  _ _ HG (fl_live _ _ _ _ _ _ _ _ _ _ _ _ _ HF) Hrs Hov Hty' Hl')
      as Hcond.
    exists ov, As. refine (conj Hov (conj Hty' (conj Hh (conj Hs _)))).
    intros F. unfold member_type, adapt. rewrite ldyn_subst.
    apply ldyn_map_qual_agree.
    - exact (label_cond_args L _ _ _ As [] (map (ldyn Fc) Ts)
               (map (ldyn Fc) []) _ _ Hcond).
    - exact Hle.
    - constructor.
    - reflexivity.
  Qed.

  Lemma expr_lhas : forall e Te w,
    expr_has_type CT Δ sΓ mt e Te ->
    eval_expr CT rΓ h e (Iot w) OK rΓ h ->
    lhas CT h G L w (ldyn Fc Te).
  Proof.
    intros e Te w Htype Heval.
    inversion Htype; subst; inversion Heval; subst.
    - destruct (var_typed _ _ _ Hget Hval) as [_ Hl]. exact Hl.
    - destruct (var_typed _ _ _ Hget_x Hval) as [Hty Hl].
      destruct (recv_view _ _ _ _ _ Hub Hty Hl)
        as (ov & As & Hov & _ & _ & Hs & Hag).
      rewrite Hobj0 in Hov. inversion Hov; subst ov. clear Hov.
      pose proof Hwf as (Hct & Hheap & _).
      pose proof (Hheap v (runtime_getObj_dom _ _ _ Hobj0)) as Hwfo.
      unfold wf_obj in Hwfo. rewrite Hobj0 in Hwfo.
      destruct Hwfo as (_ & fsO & HcfO & _).
      inversion Hfld_def as [? ? fsC ? ? HcfC HgetC]; subst.
      destruct (lfield_inherit _ _ _ _ _ _ _ _ Hs _ _ _ _ HcfC HcfO HgetC)
        as (fd' & Hnth' & _ & Hdyn).
      pose proof (hl_fields _ _ _ _ _ _ HG _ _ _ _ _ _ Hobj0 HcfO Hnth' Hfield)
        as Hfv.
      rewrite Hdyn in Hfv.
      eapply lhas_agree; [exact Hfv | apply Hag].
  Qed.

  Lemma lcase_assign : forall x e v,
    stmt_typing CT Δ sΓ mt (SVarAss x e) sΓ ->
    eval_expr CT rΓ h e v OK rΓ h ->
    frameL CT sΓ (set_vars rΓ (update x v (vars rΓ))) h G L next wf mode
      qthis lc lm lk.
  Proof.
    intros x e v Htype Heval. inversion Htype; subst.
    eapply frameL_update; eauto.
    intros w ->.
    pose proof (expr_eval_typable _ _ _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hfb
                  Htype_e Heval) as Hty. simpl in Hty.
    eapply lsub; eauto. eapply expr_lhas; eauto.
  Qed.

  Lemma lcase_cast : forall x T y v,
    stmt_typing CT Δ sΓ mt (SCast x T y) sΓ ->
    runtime_getVal rΓ y = Some v ->
    frameL CT sΓ (set_vars rΓ (update x v (vars rΓ))) h G L next wf mode
      qthis lc lm lk.
  Proof.
    intros x T y v Htype Hval. inversion Htype; subst.
    eapply frameL_update; eauto.
    intros w ->.
    assert (Hsub' : qualified_type_subtype CT Δ Ty Tx).
    { destruct Hsource as [Hs | Hnarrow].
      - eapply qtype_trans; eauto.
      - exfalso. destruct Hrs as [Hr | Hr]; rewrite Hr in Hscope;
          simpl in Hscope; auto. }
    destruct (var_typed _ _ _ Hget_y Hval) as [Hty Hl].
    eapply lsub; eauto.
  Qed.

  Lemma lcase_fldwrite : forall x f0 y lx ox a0 vf vy,
    stmt_typing CT Δ sΓ mt (SFldWrite x f0 y) sΓ ->
    runtime_getVal rΓ x = Some (Iot lx) ->
    runtime_getObj h lx = Some ox ->
    getVal (fields_map ox) f0 = Some vf ->
    sf_assignability_rel CT (rctype (rt_type ox)) f0 a0 ->
    runtime_getVal rΓ y = Some vy ->
    heapL P CT (update_field h lx f0 vy) G L next /\
    prot_preserved P CT mt h (update_field h lx f0 vy).
  Proof.
    intros x f0 y lx ox a0 vf vy Htype Hvx Hox Hvf Hassign Hvy.
    inversion Htype; subst.
    destruct (var_typed _ _ _ Hget_x Hvx) as [Hxty Hxl].
    destruct (recv_view _ _ _ _ _ Hub Hxty Hxl)
      as (ov & As & Hov & Hxty' & Hhead & Hs & Hag).
    rewrite Hox in Hov. inversion Hov; subst ov. clear Hov.
    pose proof Hwf as (Hct & Hheap & _).
    pose proof (Hheap lx (runtime_getObj_dom _ _ _ Hox)) as Hwfo.
    unfold wf_obj in Hwfo. rewrite Hox in Hwfo.
    destruct Hwfo as (_ & fsO & HcfO & _).
    inversion Hfld_def as [? ? fsC ? ? HcfC HgetC]; subst.
    destruct (lfield_inherit _ _ _ _ _ _ _ _ Hs _ _ _ _ HcfC HcfO HgetC)
      as (fd' & HnO & Hassign_eq & Hdyn).
    destruct Hsub as [Hsub Hok].
    split.
    - apply (heapL_update P CT h G L next lx ox f0 vy HG Hox).
      intros fs fd wv Hcf Hn ->.
      assert (fs = fsO) by eauto using collect_fields_deterministic_rel.
      subst fs. rewrite HnO in Hn. inversion Hn; subst fd.
      rewrite Hdyn.
      destruct (var_typed _ _ _ Hget_y Hvy) as [Hyty Hyl].
      pose proof (lsub _ _ _ Hsub Hyty Hyl) as Hm.
      eapply lhas_agree; [exact Hm|]. apply lagree_sym; [apply Hag|].
      rewrite erase_ldyn. simpl.
      rewrite (fl_ec _ _ _ _ _ _ _ _ _ _ _ _ _ HF).
      rewrite (fl_em _ _ _ _ _ _ _ _ _ _ _ _ _ HF). try rewrite (fl_ek _ _ _ _ _ _ _ _ _ _ _ _ _ HF).
      pose proof Hok as Hlf.
        apply dyn_lost_free; auto. apply qr2q_concrete.
    - intros l qr C0 Rs0 vals f HP Hl Hprot.
      destruct (Nat.eq_dec lx l) as [-> | Hne].
      + rewrite Hl in Hox. inversion Hox; subst ox. simpl in *.
        rewrite (update_field_getObj_same _ _ _ _ _ Hl). simpl.
        eexists. split; [reflexivity|].
        destruct (Nat.eq_dec f0 f) as [-> | Hnf].
        * exfalso.
          assert (Ha0 : a0 = assignability fieldT).
          { destruct Hassign as (fdO & HlookO & Ha).
            inversion HlookO as [? ? fs2 ? ? Hcf2 Hget2]; subst.
            assert (fs2 = fsO) by eauto using collect_fields_deterministic_rel.
            subst fs2. unfold gget in Hget2. congruence. }
          assert (Hqx : qx = Mut).
          { destruct Hprot as [Hp | [Hp | Hstrict]].
            - pose proof (sf_assignability_deterministic_rel _ _ _ _ _ Hassign Hp)
                as Heq.
              rewrite Ha0 in Heq. rewrite Heq in Hassignable.
              destruct (tv_mode Δ), qx; simpl in Hassignable; discriminate.
            - pose proof (sf_assignability_deterministic_rel _ _ _ _ _ Hassign Hp)
                as Heq.
              rewrite Ha0 in Heq. rewrite Heq in Hassignable.
              destruct (tv_mode Δ), qx; simpl in Hassignable;
                try discriminate; reflexivity.
            - destruct Hstrict as [Hst | Hst]; rewrite Hst in Hassignable;
                destruct qx, (assignability fieldT); simpl in Hassignable;
                try discriminate; reflexivity. }
          subst qx.
          unfold headL in Hhead. specialize (Hhead eq_refl).
          change (lab_of Fc Mut) with (LIn wf) in Hhead.
          rewrite (norm_live _ _ (fl_live _ _ _ _ _ _ _ _ _ _ _ _ _ HF)) in Hhead.
          destruct (hl_col _ _ _ _ _ _ HG _ _ Hhead) as (_ & HnP & _). auto.
        * symmetry. apply update_diff; auto.
      + rewrite update_field_getObj_diff; auto. exists vals. split; auto.
  Qed.

  Lemma lcase_new : forall x qc C Ts ys l1 qthisr vals,
    stmt_typing CT Δ sΓ mt (SNew x qc C Ts ys) sΓ ->
    runtime_getVal rΓ 0 = Some (Iot l1) ->
    runtime_lookup_list rΓ ys = Some vals ->
    r_muttype h l1 = Some qthisr ->
    (forall l, P l -> l < dom h) ->
    obF CT h G L ->
    (qc = RDM_c -> forall def n B,
       find_class CT C = Some def ->
       nth_error (ctparams (signature def)) n = Some B ->
       no_mut (class_env def) B) ->
    let onew := mkObj
                  (mkruntime_type (vpa_mutability_object_creation qthisr qc) C
                     (map (dyn (qr2q qthisr) (cargs rΓ) (margs rΓ) (qargs rΓ)) Ts)) vals in
    let G' := g_new G (dom h) (new_color qc wf mode)
                (new_birth (vpa_mutability_object_creation qthisr qc) qc wf mode)
                (map (ldyn Fc) Ts) in
    heapL P CT (h ++ [onew]) G' L next /\
    frameL CT sΓ (set_vars rΓ (update x (Iot (dom h)) (vars rΓ))) (h ++ [onew])
      G' L next wf mode qthis lc lm lk /\
    gext h G G' /\ mutcL CT (h ++ [onew]) G' /\ obF CT (h ++ [onew]) G' L.
  Proof.
    intros x qc C Ts ys l1 qthisr vals Htype Hthis0 Hvals Hmut HPdom Hob
      Hnm onew G'.
    inversion Htype; subst.
    apply get_this_runtime_getVal in Hthis0.
    assert (l1 = ι) by congruence. subst l1.
    assert (Hq : qthisr = rqtype (rt_type o)).
    { unfold r_muttype in Hmut. rewrite Hobj in Hmut. congruence. }
    subst qthisr.
    pose proof (heap_ext_app h onew) as Hext.
    pose proof (gext_new h G (new_color qc wf mode)
                  (new_birth (vpa_mutability_object_creation qthis qc) qc wf mode)
                  (map (ldyn Fc) Ts))
      as Hgx. fold G' in Hgx.
    pose proof (fl_live _ _ _ _ _ _ _ _ _ _ _ _ _ HF) as HwfL.
    pose proof (hl_live _ _ _ _ _ _ HG _ HwfL) as Hwn.
    destruct (fl_bound _ _ _ _ _ _ _ _ _ _ _ _ _ HF) as [Hblc Hblm].
    pose proof (fl_kbound _ _ _ _ _ _ _ _ _ _ _ _ _ HF) as Hblk.
    pose proof (act_frame_bound next qthis wf mode lc lm lk Hwn Hblc Hblm Hblk) as HFb.
    pose proof (fl_ec _ _ _ _ _ _ _ _ _ _ _ _ _ HF) as Hec.
    pose proof (fl_em _ _ _ _ _ _ _ _ _ _ _ _ _ HF) as Hem.
    pose proof (fl_ek _ _ _ _ _ _ _ _ _ _ _ _ _ HF) as Hek.
    pose proof Hwf as (Hct & Hheap & Hrenv & _).
    set (qn := vpa_mutability_object_creation qthis qc) in *.
    assert (Harg : forall f fd v,
              nth_error fds f = Some fd ->
              nth_error vals f = Some (Iot v) ->
              lhas CT h G L v
                (ldyn (obj_frame qn (new_birth qn qc wf mode) (new_color qc wf mode)
                         (map (ldyn Fc) Ts)) (ftype fd))).
    { intros f fd v Hfd Hv.
      destruct (lookup_lists_nth _ _ _ _ _ _ _ Hget_args Hvals Hv)
        as (y & A & HyA & Hyv & HnA).
      pose proof (Forall2_nth_error_rel _ _ _ f Harg_sub) as Hrel.
      rewrite HnA in Hrel. rewrite Hfd in Hrel. destruct Hrel as [Hsub Hok].
      destruct (var_typed _ _ _ HyA Hyv) as [Hty Hl].
      pose proof (lsub _ _ _ Hsub Hty Hl) as Hm.
      eapply lhas_agree; [exact Hm|]. apply lagree_sym.
      - unfold member_type, adapt. rewrite ldyn_subst.
        apply ldyn_map_qual_agree.
        + apply new_label_cond. exact Hrs.
        + simpl. apply Forall2_lagree_refl.
        + simpl. constructor.
        + reflexivity.
      - rewrite erase_ldyn. simpl. rewrite Hec. rewrite Hem. try rewrite Hek.
        pose proof Hok as Hlf.
          apply dyn_lost_free; auto. apply qr2q_concrete. }
    assert (Hold : forall l, l < dom h ->
              g_col G' l = g_col G l /\ g_birth G' l = g_birth G l /\
              g_args G' l = g_args G l) by exact Hgx.
    assert (Hlt : forall l o0, runtime_getObj (h ++ [onew]) l = Some o0 ->
              l <> dom h -> l < dom h).
    { intros l o0 Ho Hne. apply runtime_getObj_dom in Ho.
      rewrite length_app in Ho. simpl in Ho. lia. }
    assert (HG' : heapL P CT (h ++ [onew]) G' L next).
    { constructor.
      - intros l w Hc.
        destruct (Nat.eq_dec l (dom h)) as [-> | Hne].
        + unfold G' in Hc. rewrite g_new_col_same in Hc.
          assert (Hw : w = wf).
          { destruct qc, mode; simpl in Hc; congruence. }
          subst w. refine (conj _ (conj _ (conj _ (conj Hwn _)))).
          * rewrite length_app. simpl. lia.
          * intros HP. apply HPdom in HP. lia.
          * unfold r_muttype, onew. rewrite runtime_getObj_last. simpl. f_equal.
            apply creation_mut.
            destruct qc, mode; simpl in Hc; try discriminate; auto.
            right. split; auto.
            destruct (fl_this _ _ _ _ _ _ _ _ _ _ _ _ _ HF)
              as (ι0 & o0 & Hth0 & Ho0 & _ & Hc0).
            assert (ι0 = ι) by congruence. subst ι0.
            destruct (hl_col _ _ _ _ _ _ HG _ _ (Hc0 eq_refl))
              as (_ & _ & Hm & _).
            unfold r_muttype in Hm. rewrite Hobj in Hm. congruence.
          * unfold G'. rewrite g_new_birth_same.
            apply new_birth_of_color. exact Hc.
        + destruct (g_new_other G (dom h) (new_color qc wf mode) (new_birth qn qc wf mode)
                      (map (ldyn Fc) Ts) l Hne) as (Hc1 & Hc2 & _).
          fold G' in Hc1, Hc2. rewrite Hc1 in Hc. rewrite Hc2.
          destruct (hl_col _ _ _ _ _ _ HG _ _ Hc) as (Ka & Kb & Kc & Kd & Ke).
          refine (conj _ (conj Kb (conj _ (conj Kd Ke)))).
          * rewrite length_app. lia.
          * unfold r_muttype in *. unfold onew. rewrite runtime_getObj_last2; auto.
      - intros l o0 Ho.
        destruct (Nat.eq_dec l (dom h)) as [-> | Hne].
        + unfold onew in Ho. rewrite runtime_getObj_last in Ho.
          inversion Ho; subst o0.
          unfold G'. rewrite g_new_args_same. rewrite map_erase_ldyn. simpl.
          rewrite Hec. rewrite Hem. try rewrite Hek. reflexivity.
        + pose proof (Hlt _ _ Ho Hne) as Hl.
          unfold onew in Ho. rewrite runtime_getObj_last2 in Ho; auto.
          destruct (Hold _ Hl) as (_ & _ & Ha). rewrite Ha.
          exact (hl_erase _ _ _ _ _ _ HG _ _ Ho).
      - intros l o0 fs f fd v Ho Hcf Hn Hval.
        eapply lhas_ext; [exact Hext | exact Hgx |].
        destruct (Nat.eq_dec l (dom h)) as [-> | Hne].
        + unfold onew in Ho. rewrite runtime_getObj_last in Ho.
          inversion Ho; subst o0. simpl in Hcf, Hval.
          assert (fs = fds) by eauto using collect_fields_deterministic_rel.
          subst fs.
          unfold G'. rewrite g_new_col_same. rewrite g_new_birth_same.
          rewrite g_new_args_same. eapply Harg; eauto.
        + pose proof (Hlt _ _ Ho Hne) as Hl.
          unfold onew in Ho. rewrite runtime_getObj_last2 in Ho; auto.
          destruct (Hold _ Hl) as (Hc1 & Hc2 & Hc3).
          rewrite Hc1. rewrite Hc2. rewrite Hc3.
          eapply (hl_fields _ _ _ _ _ _ HG); eauto.
      - exact (hl_live _ _ _ _ _ _ HG).
      - intros l.
        destruct (Nat.eq_dec l (dom h)) as [-> | Hne].
        + unfold G'. rewrite g_new_args_same. rewrite g_new_birth_same. split.
          * apply map_ldyn_lbound. exact HFb.
          * intros w Hw. rewrite (new_birth_is _ _ _ _ _ Hw). exact Hwn.
        + destruct (g_new_other G (dom h) (new_color qc wf mode) (new_birth qn qc wf mode)
                      (map (ldyn Fc) Ts) l Hne) as (_ & Hc2 & Hc3).
          fold G' in Hc2, Hc3. rewrite Hc2. rewrite Hc3.
          exact (hl_bound _ _ _ _ _ _ HG l). }
    assert (HM' : mutcL CT (h ++ [onew]) G').
    { intros l w o0 Hb Ho0 Hq0.
      destruct (Nat.eq_dec l (dom h)) as [-> | Hne].
      + unfold onew in Ho0. rewrite runtime_getObj_last in Ho0.
        inversion Ho0; subst o0. cbn [rt_type rqtype] in Hq0.
        unfold G' in Hb. rewrite g_new_birth_same in Hb.
        unfold G'. rewrite g_new_col_same.
        rewrite Hq0 in Hb. exact Hb.
      + destruct (g_new_other G (dom h) (new_color qc wf mode)
                    (new_birth qn qc wf mode) (map (ldyn Fc) Ts) l Hne)
          as (Hc1 & Hc2 & _).
        fold G' in Hc1, Hc2. rewrite Hc1. rewrite Hc2 in Hb.
        pose proof (Hlt _ _ Ho0 Hne) as Hl0.
        unfold onew in Ho0. rewrite runtime_getObj_last2 in Ho0; auto.
        exact (HMc _ _ _ Hb Ho0 Hq0). }
    refine (conj HG' (conj _ (conj Hgx (conj HM' _)))).
    - assert (HF0 : frameL CT sΓ rΓ (h ++ [onew]) G' L next wf mode qthis lc lm lk).
      { eapply frameL_ext; eauto. }
      eapply frameL_update; eauto.
      intros w Hw. inversion Hw; subst w.
      apply (lhas_subtype P CT Δ (h ++ [onew]) G' L next mt qthis wf mode lc lm lk
               _ _ _ HG' HwfL Hrs eq_refl
               (vb_of_fits P CT Δ (h ++ [onew]) G' L next Fc _ _ _ qthis
                  HG' HM' Hfit eq_refl Hec Hem Hek)
               (fun o0 n0 B0 Hb0 => nomut_bounds_head Δ o0 n0 B0 Hnb Hb0)
               Hfb Hec Hem Hek _ _ Hresult_sub).
      + unfold wf_r_typable, loc_has_rtype. simpl.
        unfold onew. rewrite runtime_getObj_last. simpl.
        split.
        * rewrite creation_dynq. unfold head_ok. auto.
        * eexists. split; [apply rsi_refl | apply Forall2_rarg_sub_refl].
      + exists onew. split; [apply runtime_getObj_last|].
        change (ldyn Fc (TClass (qc2q qc) C Ts))
          with (LT (dynq (qr2q qthis) (qc2q qc)) (lab_of Fc (qc2q qc)) C
                  (map (ldyn Fc) Ts)).
        split.
        * unfold headL. intros Hm. unfold G'. rewrite g_new_col_same.
          destruct qc; cbn [qc2q dynq] in Hm; try discriminate;
            unfold Fc; cbn [qc2q lab_of act_frame lf_mut lf_rdm new_color];
            try (rewrite (norm_live _ _ HwfL); reflexivity).
          destruct mode; [rewrite (norm_live _ _ HwfL); reflexivity|].
          simpl. intros w Hc. discriminate.
        * exists (map (ldyn Fc) Ts). split.
          -- unfold G'. rewrite g_new_args_same. apply lsi_refl.
          -- apply Forall2_lagree_refl.
    - intros l o0 def0 Ho Hfc.
      destruct (Nat.eq_dec l (dom h)) as [-> | Hne].
      + unfold onew in Ho. rewrite runtime_getObj_last in Ho.
        inversion Ho; subst o0. cbn [rt_type rqtype rctype] in *.
        rewrite Hfind in Hfc. inversion Hfc; subst def0.
        unfold G'. rewrite g_new_col_same. rewrite g_new_birth_same.
        rewrite g_new_args_same.
        intros o1 n B Hb.
        destruct (tv_bound_class_env _ _ _ _ Hb) as [-> Hnbd].
        pose proof (Forall2_nth_error_rel _ _ _ n Hbounds) as Hrel.
        rewrite Hnbd in Hrel.
        destruct (nth_error Ts n) as [T|] eqn:HT; [|contradiction].
        destruct Hrel as [HlfB HbsB].
        assert (HX : ldyn (obj_frame qn (new_birth qn qc wf mode)
                             (new_color qc wf mode) (map (ldyn Fc) Ts))
                       (TVar TVSub ClassVar n) = ldyn Fc T).
        { cbn [ldyn obj_frame lf_cargs lf_margs tv_lookup].
          rewrite nth_error_map. rewrite HT. reflexivity. }
        rewrite HX.
        assert (Hconc : lf_q Fc = Mut \/ lf_q Fc = Imm).
        { unfold Fc. simpl. destruct (rqtype (rt_type o)); auto. }
        pose proof (sub_lsubt CT Δ L Fc Hrs Hconc Hfit _ _
                      (bound_sub_self _ _ _ _ HbsB)) as Hs.
        eapply lsubt_agree_r; [exact Hs|].
        assert (Hrl : rlost_free (erase (ldyn Fc
                  (member_type AbstractState (qc2q qc) Ts [] [] B)))).
        { rewrite erase_ldyn. simpl. rewrite Hec. rewrite Hem. try rewrite Hek.
          apply dyn_lost_free; auto; try apply qr2q_concrete. }
        apply lagree_sym; [|exact Hrl].
        unfold member_type, adapt. rewrite ldyn_subst.
        destruct (qc_rdm_dec qc) as [Hrdm | Hnrdm].
        * (* a receiver-dependent allocation: the class's bounds have no
             mutable position *)
          pose proof (Hnm Hrdm _ _ _ Hfind Hnbd) as HnmB.
          rewrite (no_mut_unm _ _ (vpa_q AbstractState (qc2q qc)) HnmB).
          apply ldyn_map_qual_agree.
          -- apply new_label_cond_as.
          -- simpl. apply Forall2_lagree_refl.
          -- simpl. constructor.
          -- reflexivity.
        * apply ldyn_map_qual_agree.
          -- apply new_label_cond_as_full. exact Hnrdm.
          -- simpl. apply Forall2_lagree_refl.
          -- simpl. constructor.
          -- reflexivity.
      + pose proof (Hlt _ _ Ho Hne) as Hl.
        unfold onew in Ho. rewrite runtime_getObj_last2 in Ho; auto.
        destruct (Hold _ Hl) as (Hc1 & Hc2 & Hc3).
        rewrite Hc1. rewrite Hc2. rewrite Hc3. exact (Hob _ _ _ Ho Hfc).
  Qed.
End Cases.
