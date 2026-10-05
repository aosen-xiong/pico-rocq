From Stdlib Require Import List Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping Bigstep Properties Preservation.
Require Import Reachability AbstractStatePreservation.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoCacheTyping.

(** * Abstract Noninterference for Derivation Methods

    A cache field is filled with the result of a derivation method.  For the
    racy cache write to be benign, that result must be a function of the
    receiver's abstract state alone: two runs of the derivation in heaps that
    agree on the abstract state must return the same value.

    This file states that property as a noninterference theorem.  The public
    part of the heap is a set [P] of locations closed under abstract-field
    edges (the same edges as [reachable_abs]); the abstract fields of every
    location in [P] hold equal values in both heaps.  Everything else, in
    particular cache fields and [@Assign] fields, may differ arbitrarily.

    Derivation statements are checked syntactically by [deriv_stmt]: they read
    only locals, literals and abstract fields ([ts_expr_reads_only_stable]),
    branch with [SIfZero], and call only methods from a set [D] of derivation
    methods, closed under dynamic dispatch.  They never write fields or
    allocate.  Recursion through [D] replaces loops. *)

(** ** Public locations and heap agreement *)

Definition value_in (P : Loc -> Prop) (v : value) : Prop :=
  forall l, v = Iot l -> P l.

Definition env_in (P : Loc -> Prop) (rΓ : r_env) : Prop :=
  forall x l, runtime_getVal rΓ x = Some (Iot l) -> P l.

(** Two heaps agree on [P] when every public location holds an object of the
    same runtime type in both heaps, and the two objects' abstract fields are
    equal and point only to public locations. *)
Definition abs_agree (CT : class_table) (P : Loc -> Prop) (h1 h2 : heap) : Prop :=
  forall l, P l ->
    exists rt fs1 fs2,
      runtime_getObj h1 l = Some (mkObj rt fs1) /\
      runtime_getObj h2 l = Some (mkObj rt fs2) /\
      forall f, abstract_field CT (rctype rt) f ->
        getVal fs1 f = getVal fs2 f /\
        (forall l', getVal fs1 f = Some (Iot l') -> P l').

(** ** Derivation-safe statements and methods *)

Inductive deriv_stmt (CT : class_table) (D : method_def -> Prop) :
    s_env -> stmt -> s_env -> Prop :=
  | DS_Skip : forall sΓ,
      deriv_stmt CT D sΓ SSkip sΓ
  | DS_Local : forall sΓ T x,
      deriv_stmt CT D sΓ (SLocal T x) (sΓ ++ [T])
  | DS_VarAss : forall sΓ x e
      (Hexpr : ts_expr_reads_only_stable CT sΓ e),
      deriv_stmt CT D sΓ (SVarAss x e) sΓ
  | DS_Seq : forall sΓ s1 sΓ' s2 sΓ''
      (Hderiv1 : deriv_stmt CT D sΓ s1 sΓ')
      (Hderiv2 : deriv_stmt CT D sΓ' s2 sΓ''),
      deriv_stmt CT D sΓ (SSeq s1 s2) sΓ''
  | DS_IfZero : forall sΓ x s_zero s_nonzero sΓ'
      (Hzero : deriv_stmt CT D sΓ s_zero sΓ')
      (Hnonzero : deriv_stmt CT D sΓ s_nonzero sΓ'),
      deriv_stmt CT D sΓ (SIfZero x s_zero s_nonzero) sΓ'
  (** Every implementation that dynamic dispatch can select must be a
      derivation method. *)
  | DS_Call : forall sΓ x m y args Ty Cy
      (Hget_y : static_getType sΓ y = Some Ty)
      (Href : sbase Ty = TRef Cy)
      (Hdispatch : forall R mdef,
        class_subtype CT R Cy ->
        FindMethodWithName CT R m mdef ->
        D mdef),
      deriv_stmt CT D sΓ (SCall x m y args) sΓ.

(** [D] is a table of derivation methods when each body is derivation-safe
    in its own signature environment, assuming the whole table.  The check is
    modular, so derivation methods may be mutually recursive. *)
Definition derivation_table (CT : class_table) (D : method_def -> Prop) : Prop :=
  forall mdef, D mdef ->
    exists sΓ',
      deriv_stmt CT D
        (mreceiver (msignature mdef) :: mparams (msignature mdef))
        (mbody_stmt (mbody mdef)) sΓ'.

(** ** Auxiliary facts *)

Lemma deriv_stmt_typing_env :
  forall CT D sΓ s sΓd mt sΓt,
    deriv_stmt CT D sΓ s sΓd ->
    stmt_typing CT sΓ mt s sΓt ->
    sΓd = sΓt.
Proof.
  intros CT D sΓ s sΓd mt sΓt Hderiv.
  revert sΓt.
  induction Hderiv; intros sΓt Htyping; inversion Htyping; subst; auto.
  - have Hmid := IHHderiv1 _ Htype1. subst.
    exact (IHHderiv2 _ Htype2).
Qed.

Lemma nth_error_update_cases :
  forall {X : Type} (l : list X) p v i w,
    nth_error (update p v l) i = Some w ->
    w = v \/ nth_error l i = Some w.
Proof.
  intros X l.
  induction l as [|a l IH]; intros p v i w Hnth.
  - destruct p; simpl in Hnth; destruct i; discriminate.
  - destruct p as [|p]; destruct i as [|i]; simpl in Hnth.
    + injection Hnth as ->. left. reflexivity.
    + right. exact Hnth.
    + right. exact Hnth.
    + exact (IH p v i w Hnth).
Qed.

Lemma env_in_update :
  forall P rΓ x v,
    env_in P rΓ ->
    value_in P v ->
    env_in P (set_vars rΓ (update x v (vars rΓ))).
Proof.
  intros P rΓ x v Henv Hv y l Hy.
  unfold runtime_getVal in Hy. simpl in Hy.
  destruct (nth_error_update_cases (vars rΓ) x v y (Iot l) Hy) as [Heq | Hold].
  - exact (Hv l (eq_sym Heq)).
  - exact (Henv y l Hold).
Qed.

Lemma env_in_append_default :
  forall P rΓ T,
    env_in P rΓ ->
    env_in P (set_vars rΓ (vars rΓ ++ [default_value T])).
Proof.
  intros P rΓ T Henv y l Hy.
  unfold runtime_getVal in Hy. simpl in Hy.
  destruct (Nat.lt_ge_cases y (length (vars rΓ))) as [Hlt | Hge].
  - rewrite (nth_error_app1 _ _ Hlt) in Hy.
    exact (Henv y l Hy).
  - rewrite (nth_error_app2 _ _ Hge) in Hy.
    destruct (y - length (vars rΓ)) as [|k]; simpl in Hy.
    + injection Hy as Hy.
      exfalso. exact (default_value_not_location T l Hy).
    + destruct k; discriminate.
Qed.

Lemma env_in_call_frame :
  forall P rΓ zs vals ly,
    env_in P rΓ ->
    P ly ->
    runtime_lookup_list rΓ zs = Some vals ->
    env_in P (mkr_env (Iot ly :: vals)).
Proof.
  intros P rΓ zs vals ly Henv Hly Hargs y l Hy.
  unfold runtime_getVal in Hy. simpl in Hy.
  destruct y as [|i].
  - simpl in Hy. injection Hy as <-. exact Hly.
  - simpl in Hy.
    destruct (runtime_lookup_list_nth_zs rΓ zs vals i (Iot l) Hargs Hy)
      as [j [_ Hj]].
    exact (Henv j l Hj).
Qed.

Lemma abs_agree_basetype :
  forall CT P h1 h2 l,
    abs_agree CT P h1 h2 ->
    P l ->
    r_basetype h2 l = r_basetype h1 l.
Proof.
  intros CT P h1 h2 l Hagree Hl.
  destruct (Hagree l Hl) as (rt & fs1 & fs2 & Hobj1 & Hobj2 & _).
  unfold r_basetype. rewrite Hobj1; rewrite Hobj2. reflexivity.
Qed.

(** A field that is abstract in a class stays abstract in every subclass,
    because subclasses inherit field declarations unchanged. *)
Lemma abstract_field_subtype :
  forall CT R C f,
    class_subtype CT R C ->
    abstract_field CT C f ->
    abstract_field CT R f.
Proof.
  intros CT R C f Hsub [Hmut Hassign].
  split.
  - destruct Hmut as [[fdef [Hlookup Hq]] | [fdef [Hlookup Hq]]].
    + left. exists fdef. split; [|exact Hq].
      eapply field_inheritance_subtyping; eauto.
    + right. exists fdef. split; [|exact Hq].
      eapply field_inheritance_subtyping; eauto.
  - destruct Hassign as [[fdef [Hlookup Ha]] | [fdef [Hlookup Ha]]].
    + left. exists fdef. split; [|exact Ha].
      eapply field_inheritance_subtyping; eauto.
    + right. exists fdef. split; [|exact Ha].
      eapply field_inheritance_subtyping; eauto.
Qed.

(** ** Expressions *)

Lemma deriv_expr_noninterference :
  forall CT sΓ rΓ h1 h2 P e v1 r1 rΓ1 h1' v2 r2 rΓ2 h2',
    ts_expr_reads_only_stable CT sΓ e ->
    wf_r_config CT sΓ rΓ h1 ->
    abs_agree CT P h1 h2 ->
    env_in P rΓ ->
    eval_expr CT rΓ h1 e v1 r1 rΓ1 h1' ->
    eval_expr CT rΓ h2 e v2 r2 rΓ2 h2' ->
    v1 = v2 /\ r1 = r2 /\ value_in P v1.
Proof.
  intros CT sΓ rΓ h1 h2 P e v1 r1 rΓ1 h1' v2 r2 rΓ2 h2'
    Hexpr Hwf Hagree Henv Heval1 Heval2.
  destruct Hexpr.
  - inversion Heval1; subst. inversion Heval2; subst.
    repeat split; intros l Hl; discriminate.
  - inversion Heval1; subst. inversion Heval2; subst.
    repeat split; [congruence |].
    intros l ->. exact (Henv x l Hval).
  - inversion Heval1; subst. inversion Heval2; subst.
    repeat split; intros l Hl; discriminate.
  - inversion Heval1; subst; inversion Heval2; subst; try congruence.
    + (* both runs read the field of the same public object *)
      assert (v0 = v) by congruence. subst v0.
      have Hv := Henv x v Hval.
      destruct (Hagree v Hv) as (rt & fs1 & fs2 & Hobj1 & Hobj2 & Hfields).
      rewrite Hobj1 in Hobj. injection Hobj as <-.
      rewrite Hobj2 in Hobj0. injection Hobj0 as <-.
      simpl in Hfield, Hfield0.
      have Hsub : class_subtype CT (rctype rt) C.
      { eapply runtime_value_class_subtype;
          [exact Hwf | exact Hget_x | exact Href | exact Hval |].
        unfold r_basetype. rewrite Hobj1. reflexivity. }
      destruct (Hfields f (abstract_field_subtype CT (rctype rt) C f Hsub
        Hstable)) as [Heq Hclosed].
      repeat split.
      * congruence.
      * intros l ->. exact (Hclosed l Hfield).
    + repeat split; intros l Hl; discriminate.
Qed.

(** ** Statements *)

(** Align the two evaluations of a stable expression. *)
Ltac expr_align :=
  match goal with
  | Hx : ts_expr_reads_only_stable _ _ ?e,
    Hw : wf_r_config _ _ ?G ?H1,
    Ha : abs_agree _ ?P ?H1 ?H2,
    Hp : env_in ?P ?G,
    E1 : eval_expr _ ?G ?H1 ?e _ _ _ _,
    E2 : eval_expr _ ?G ?H2 ?e _ _ _ _ |- _ =>
      let Hv := fresh "Hv" in
      let Hr := fresh "Hr" in
      let Hin := fresh "Hin" in
      destruct (deriv_expr_noninterference _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        Hx Hw Ha Hp E1 E2) as (Hv & Hr & Hin)
  end.

(** Two runs of a derivation-safe, well-typed statement from the same
    environment, in heaps that agree on the public locations, have the same
    outcome and final environment, leave both heaps unchanged, and keep every
    location in the environment public. *)
Theorem derivation_noninterference :
  forall CT D,
    derivation_table CT D ->
    forall rΓ h1 s r1 rΓ1 h1',
      eval_stmt CT rΓ h1 s r1 rΓ1 h1' ->
      forall sΓ mt sΓ' h2 P r2 rΓ2 h2',
        deriv_stmt CT D sΓ s sΓ' ->
        stmt_typing CT sΓ mt s sΓ' ->
        wf_r_config CT sΓ rΓ h1 ->
        abs_agree CT P h1 h2 ->
        env_in P rΓ ->
        eval_stmt CT rΓ h2 s r2 rΓ2 h2' ->
        r1 = r2 /\ rΓ1 = rΓ2 /\ h1' = h1 /\ h2' = h2 /\ env_in P rΓ1.
Proof.
  intros CT D Htable rΓ h1 s r1 rΓ1 h1' Hrun.
  induction Hrun;
    intros sΓ mt sΓ_out h2 P r2 rΓ2 h2' Xderiv Xtyp Xwf Xagree Xpub Xrun2;
    inversion Xderiv; subst.
  - (* skip *)
    inversion Xrun2; subst.
    repeat split; auto.
  - (* local declaration *)
    inversion Xrun2; subst.
    repeat split; auto.
    apply env_in_append_default. assumption.
  - (* assignment *)
    inversion Xrun2; subst; expr_align; try discriminate; subst;
      repeat split; auto.
    apply env_in_update; assumption.
  - (* assignment raising NPE *)
    inversion Xrun2; subst; expr_align; try discriminate; subst;
      repeat split; auto.
  (* The call cases share one alignment argument: both runs resolve the same
     public receiver, hence the same runtime class and method, and the callee
     body is itself a derivation. *)
  - (* call returning normally *)
    destruct Hfind as [Hfind_m Hbody_eq]. subst.
    have Hly : P ly := Xpub y ly Hval_y.
    have Hsub : class_subtype CT cy Cy :=
      runtime_value_class_subtype CT _ rΓ h y Ty Cy ly cy
        Xwf Hget_y Href Hval_y Hbase.
    destruct (Htable mdef (Hdispatch cy mdef Hsub Hfind_m))
      as [sΓd Hbody_deriv].
    destruct (typed_call_has_wf_callee_frame CT _ _ rΓ h x m y zs _
      vals ly cy mdef Xwf Xtyp Hval_y Hbase Hfind_m Hargs)
      as [sΓt [Hbody_typ Hframe_wf]].
    have Hsame := deriv_stmt_typing_env CT D _ _ _ _ _ Hbody_deriv Hbody_typ.
    subst sΓd.
    have Hframe_pub := env_in_call_frame P rΓ zs vals ly Xpub Hly Hargs.
    inversion Xrun2; subst; try congruence;
      match goal with
      | Hy : runtime_getVal _ y = Some (Iot ?ly2) |- _ =>
          tryif constr_eq Hy Hval_y then fail else
          (assert (ly2 = ly) by congruence; subst ly2)
      end;
      match goal with
      | Hb : r_basetype _ ly = Some ?cy2 |- _ =>
          tryif constr_eq Hb Hbase then fail else
          (rewrite (abs_agree_basetype _ _ _ _ ly Xagree Hly) in Hb;
           assert (cy2 = cy) by congruence; subst cy2)
      end;
      match goal with
      | Hf : FindMethodWithName CT cy m ?mdef2 /\ _ = _ |- _ =>
          let Hf_m := fresh "Hf_m" in
          let Hf_b := fresh "Hf_b" in
          destruct Hf as [Hf_m Hf_b];
          have Hmdef_eq := find_method_with_name_deterministic
            CT cy m mdef mdef2 Hfind_m Hf_m;
          subst mdef2
      end;
      match goal with
      | Ha : runtime_lookup_list _ zs = Some ?vals2 |- _ =>
          tryif constr_eq Ha Hargs then fail else
          (assert (vals2 = vals) by congruence; subst vals2)
      end;
      subst.
    + 
      edestruct (IHHrun Htable) as (_ & Henv_eq & Hh1 & Hh2 & Hpub_body);
        [exact Hbody_deriv | exact Hbody_typ | exact Hframe_wf |
         exact Xagree | exact Hframe_pub | eassumption |];
      subst.
      assert (retval0 = retval) by congruence. subst retval0.
      repeat split; auto.
      apply env_in_update; [assumption |].
      intros l ->. exact (Hpub_body _ l Hretval).
    + 
      edestruct (IHHrun Htable) as (Hr & _);
        [exact Hbody_deriv | exact Hbody_typ | exact Hframe_wf |
         exact Xagree | exact Hframe_pub | eassumption |];
      discriminate.
    + 
      edestruct (IHHrun Htable) as (Hr & _);
        [exact Hbody_deriv | exact Hbody_typ | exact Hframe_wf |
         exact Xagree | exact Hframe_pub | eassumption |];
      discriminate.
  - (* call on a null receiver *)
    inversion Xrun2; subst; try congruence.
    repeat split; auto.
  - (* call whose body raises NPE *)
    destruct Hfind as [Hfind_m Hbody_eq]. subst.
    have Hly : P ly := Xpub y ly Hval_y.
    have Hsub : class_subtype CT cy Cy :=
      runtime_value_class_subtype CT _ rΓ h y Ty Cy ly cy
        Xwf Hget_y Href Hval_y Hbase.
    destruct (Htable mdef (Hdispatch cy mdef Hsub Hfind_m))
      as [sΓd Hbody_deriv].
    destruct (typed_call_has_wf_callee_frame CT _ _ rΓ h x m y zs _
      vals ly cy mdef Xwf Xtyp Hval_y Hbase Hfind_m Hargs)
      as [sΓt [Hbody_typ Hframe_wf]].
    have Hsame := deriv_stmt_typing_env CT D _ _ _ _ _ Hbody_deriv Hbody_typ.
    subst sΓd.
    have Hframe_pub := env_in_call_frame P rΓ zs vals ly Xpub Hly Hargs.
    inversion Xrun2; subst; try congruence;
      match goal with
      | Hy : runtime_getVal _ y = Some (Iot ?ly2) |- _ =>
          tryif constr_eq Hy Hval_y then fail else
          (assert (ly2 = ly) by congruence; subst ly2)
      end;
      match goal with
      | Hb : r_basetype _ ly = Some ?cy2 |- _ =>
          tryif constr_eq Hb Hbase then fail else
          (rewrite (abs_agree_basetype _ _ _ _ ly Xagree Hly) in Hb;
           assert (cy2 = cy) by congruence; subst cy2)
      end;
      match goal with
      | Hf : FindMethodWithName CT cy m ?mdef2 /\ _ = _ |- _ =>
          let Hf_m := fresh "Hf_m" in
          let Hf_b := fresh "Hf_b" in
          destruct Hf as [Hf_m Hf_b];
          have Hmdef_eq := find_method_with_name_deterministic
            CT cy m mdef mdef2 Hfind_m Hf_m;
          subst mdef2
      end;
      match goal with
      | Ha : runtime_lookup_list _ zs = Some ?vals2 |- _ =>
          tryif constr_eq Ha Hargs then fail else
          (assert (vals2 = vals) by congruence; subst vals2)
      end;
      subst.
    + 
      edestruct (IHHrun Htable) as (Hr & _);
        [exact Hbody_deriv | exact Hbody_typ | exact Hframe_wf |
         exact Xagree | exact Hframe_pub | eassumption |];
      discriminate.
    + 
      edestruct (IHHrun Htable) as (_ & Henv_eq & Hh1 & Hh2 & Hpub_body);
        [exact Hbody_deriv | exact Hbody_typ | exact Hframe_wf |
         exact Xagree | exact Hframe_pub | eassumption |];
      subst.
      repeat split; auto.
    + 
      edestruct (IHHrun Htable) as (Hr & _);
        [exact Hbody_deriv | exact Hbody_typ | exact Hframe_wf |
         exact Xagree | exact Hframe_pub | eassumption |];
      discriminate.
  - (* call whose body raises a mutation exception *)
    destruct Hfind as [Hfind_m Hbody_eq]. subst.
    have Hly : P ly := Xpub y ly Hval_y.
    have Hsub : class_subtype CT cy Cy :=
      runtime_value_class_subtype CT _ rΓ h y Ty Cy ly cy
        Xwf Hget_y Href Hval_y Hbase.
    destruct (Htable mdef (Hdispatch cy mdef Hsub Hfind_m))
      as [sΓd Hbody_deriv].
    destruct (typed_call_has_wf_callee_frame CT _ _ rΓ h x m y zs _
      vals ly cy mdef Xwf Xtyp Hval_y Hbase Hfind_m Hargs)
      as [sΓt [Hbody_typ Hframe_wf]].
    have Hsame := deriv_stmt_typing_env CT D _ _ _ _ _ Hbody_deriv Hbody_typ.
    subst sΓd.
    have Hframe_pub := env_in_call_frame P rΓ zs vals ly Xpub Hly Hargs.
    inversion Xrun2; subst; try congruence;
      match goal with
      | Hy : runtime_getVal _ y = Some (Iot ?ly2) |- _ =>
          tryif constr_eq Hy Hval_y then fail else
          (assert (ly2 = ly) by congruence; subst ly2)
      end;
      match goal with
      | Hb : r_basetype _ ly = Some ?cy2 |- _ =>
          tryif constr_eq Hb Hbase then fail else
          (rewrite (abs_agree_basetype _ _ _ _ ly Xagree Hly) in Hb;
           assert (cy2 = cy) by congruence; subst cy2)
      end;
      match goal with
      | Hf : FindMethodWithName CT cy m ?mdef2 /\ _ = _ |- _ =>
          let Hf_m := fresh "Hf_m" in
          let Hf_b := fresh "Hf_b" in
          destruct Hf as [Hf_m Hf_b];
          have Hmdef_eq := find_method_with_name_deterministic
            CT cy m mdef mdef2 Hfind_m Hf_m;
          subst mdef2
      end;
      match goal with
      | Ha : runtime_lookup_list _ zs = Some ?vals2 |- _ =>
          tryif constr_eq Ha Hargs then fail else
          (assert (vals2 = vals) by congruence; subst vals2)
      end;
      subst.
    + 
      edestruct (IHHrun Htable) as (Hr & _);
        [exact Hbody_deriv | exact Hbody_typ | exact Hframe_wf |
         exact Xagree | exact Hframe_pub | eassumption |];
      discriminate.
    + 
      edestruct (IHHrun Htable) as (Hr & _);
        [exact Hbody_deriv | exact Hbody_typ | exact Hframe_wf |
         exact Xagree | exact Hframe_pub | eassumption |];
      discriminate.
    + 
      edestruct (IHHrun Htable) as (_ & Henv_eq & Hh1 & Hh2 & Hpub_body);
        [exact Hbody_deriv | exact Hbody_typ | exact Hframe_wf |
         exact Xagree | exact Hframe_pub | eassumption |];
      subst.
      repeat split; auto.
  (* Sequences: align the first statement; when it completes normally in
     both runs, continue from the common intermediate environment. *)
  - (* s1 and s2 complete normally *)
    inversion Xtyp; subst.
    have Hmid := deriv_stmt_typing_env CT D _ _ _ _ _ Hderiv1 Htype1. subst.
    inversion Xrun2; subst;
    (edestruct (IHHrun1 Htable) as (Hr1 & Henv1 & Hh1 & Hh1' & Hpub1);
      [exact Hderiv1 | exact Htype1 | exact Xwf | exact Xagree | exact Xpub |
       eassumption |]);
    subst; try discriminate.
    
    all: match goal with
         | Xw : wf_r_config _ _ _ ?H1,
           E : eval_stmt _ _ ?H1 ?s OK _ _ |- _ =>
             match type of Htype1 with
             | stmt_typing _ _ _ s _ =>
                 have Hmid_wf := preservation_pico CT _ _ _ _ _ _ _ _ Xw Htype1 E
             end
         end;
      (edestruct (IHHrun2 Htable) as (Hr2 & Henv2 & Hh2 & Hh2' & Hpub2);
        [exact Hderiv2 | exact Htype2 | exact Hmid_wf | exact Xagree |
         exact Hpub1 | eassumption |]);
      subst; try discriminate.
    all: repeat split; auto.
  - (* s1 raises NPE *)
    inversion Xtyp; subst.
    have Hmid := deriv_stmt_typing_env CT D _ _ _ _ _ Hderiv1 Htype1. subst.
    inversion Xrun2; subst;
    (edestruct (IHHrun Htable) as (Hr1 & Henv1 & Hh1 & Hh1' & Hpub1);
      [exact Hderiv1 | exact Htype1 | exact Xwf | exact Xagree | exact Xpub |
       eassumption |]);
    subst; try discriminate.
    all: repeat split; auto.
  - (* s2 raises NPE *)
    inversion Xtyp; subst.
    have Hmid := deriv_stmt_typing_env CT D _ _ _ _ _ Hderiv1 Htype1. subst.
    inversion Xrun2; subst;
    (edestruct (IHHrun1 Htable) as (Hr1 & Henv1 & Hh1 & Hh1' & Hpub1);
      [exact Hderiv1 | exact Htype1 | exact Xwf | exact Xagree | exact Xpub |
       eassumption |]);
    subst; try discriminate.
    
    all: match goal with
         | Xw : wf_r_config _ _ _ ?H1,
           E : eval_stmt _ _ ?H1 ?s OK _ _ |- _ =>
             match type of Htype1 with
             | stmt_typing _ _ _ s _ =>
                 have Hmid_wf := preservation_pico CT _ _ _ _ _ _ _ _ Xw Htype1 E
             end
         end;
      (edestruct (IHHrun2 Htable) as (Hr2 & Henv2 & Hh2 & Hh2' & Hpub2);
        [exact Hderiv2 | exact Htype2 | exact Hmid_wf | exact Xagree |
         exact Hpub1 | eassumption |]);
      subst; try discriminate.
    all: repeat split; auto.
  - (* s1 raises a mutation exception *)
    inversion Xtyp; subst.
    have Hmid := deriv_stmt_typing_env CT D _ _ _ _ _ Hderiv1 Htype1. subst.
    inversion Xrun2; subst;
    (edestruct (IHHrun Htable) as (Hr1 & Henv1 & Hh1 & Hh1' & Hpub1);
      [exact Hderiv1 | exact Htype1 | exact Xwf | exact Xagree | exact Xpub |
       eassumption |]);
    subst; try discriminate.
    all: repeat split; auto.
  - (* s2 raises a mutation exception *)
    inversion Xtyp; subst.
    have Hmid := deriv_stmt_typing_env CT D _ _ _ _ _ Hderiv1 Htype1. subst.
    inversion Xrun2; subst;
    (edestruct (IHHrun1 Htable) as (Hr1 & Henv1 & Hh1 & Hh1' & Hpub1);
      [exact Hderiv1 | exact Htype1 | exact Xwf | exact Xagree | exact Xpub |
       eassumption |]);
    subst; try discriminate.
    
    all: match goal with
         | Xw : wf_r_config _ _ _ ?H1,
           E : eval_stmt _ _ ?H1 ?s OK _ _ |- _ =>
             match type of Htype1 with
             | stmt_typing _ _ _ s _ =>
                 have Hmid_wf := preservation_pico CT _ _ _ _ _ _ _ _ Xw Htype1 E
             end
         end;
      (edestruct (IHHrun2 Htable) as (Hr2 & Henv2 & Hh2 & Hh2' & Hpub2);
        [exact Hderiv2 | exact Htype2 | exact Hmid_wf | exact Xagree |
         exact Hpub1 | eassumption |]);
      subst; try discriminate.
    all: repeat split; auto.
  (* Zero tests: the guard is read from the shared environment, so both runs
     take the same branch. *)
  - (* zero branch *)
    inversion Xrun2; subst; try congruence.
    edestruct (IHHrun Htable) as (Hr & Henv' & Hh & Hh' & Hpub');
      [exact Hzero | inversion Xtyp; eassumption | exact Xwf | exact Xagree |
       exact Xpub | eassumption |].
    subst. repeat split; auto.
  - (* nonzero branch *)
    inversion Xrun2; subst; try congruence.
    edestruct (IHHrun Htable) as (Hr & Henv' & Hh & Hh' & Hpub');
      [exact Hnonzero | inversion Xtyp; eassumption | exact Xwf |
       exact Xagree | exact Xpub | eassumption |].
    subst. repeat split; auto.
  - (* null guard: zero branch *)
    inversion Xrun2; subst; try congruence.
    edestruct (IHHrun Htable) as (Hr & Henv' & Hh & Hh' & Hpub');
      [exact Hzero | inversion Xtyp; eassumption | exact Xwf | exact Xagree |
       exact Xpub | eassumption |].
    subst. repeat split; auto.
  - (* reference guard: nonzero branch *)
    inversion Xrun2; subst; try congruence.
    edestruct (IHHrun Htable) as (Hr & Henv' & Hh & Hh' & Hpub');
      [exact Hnonzero | inversion Xtyp; eassumption | exact Xwf |
       exact Xagree | exact Xpub | eassumption |].
    subst. repeat split; auto.
Qed.

(** ** Replaying a derivation in an agreeing heap

    Noninterference compares two runs that both exist.  Stability also needs
    the converse direction: a derivation run in one heap can be replayed, with
    the same outcome and environment, in any heap that agrees on the public
    abstract state. *)

Lemma deriv_expr_simulation :
  forall CT sΓ rΓ h1 h2 P e v r rΓ1 h1',
    ts_expr_reads_only_stable CT sΓ e ->
    wf_r_config CT sΓ rΓ h1 ->
    abs_agree CT P h1 h2 ->
    env_in P rΓ ->
    eval_expr CT rΓ h1 e v r rΓ1 h1' ->
    eval_expr CT rΓ h2 e v r rΓ h2.
Proof.
  intros CT sΓ rΓ h1 h2 P e v r rΓ1 h1' Hexpr Hwf Hagree Hpub Heval.
  destruct Hexpr; inversion Heval; subst.
  - constructor.
  - constructor. assumption.
  - constructor.
  - have Hv := Hpub x v0 Hval.
    destruct (Hagree v0 Hv) as (rt & fs1 & fs2 & Hobj1 & Hobj2 & Hfields).
    rewrite Hobj1 in Hobj. injection Hobj as <-.
    have Hsub : class_subtype CT (rctype rt) C.
    { eapply runtime_value_class_subtype;
        [exact Hwf | exact Hget_x | exact Href | exact Hval |].
      unfold r_basetype. rewrite Hobj1. reflexivity. }
    destruct (Hfields f (abstract_field_subtype CT (rctype rt) C f Hsub
      Hstable)) as [Heq _].
    eapply EBS_Field; [exact Hval | exact Hobj2 |].
    simpl in Hfield |- *. rewrite <- Heq. exact Hfield.
  - apply EBS_Field_NPE. assumption.
Qed.

Theorem derivation_simulation :
  forall CT D,
    derivation_table CT D ->
    forall rΓ h1 s r rΓ1 h1',
      eval_stmt CT rΓ h1 s r rΓ1 h1' ->
      forall sΓ mt sΓ' h2 P,
        deriv_stmt CT D sΓ s sΓ' ->
        stmt_typing CT sΓ mt s sΓ' ->
        wf_r_config CT sΓ rΓ h1 ->
        abs_agree CT P h1 h2 ->
        env_in P rΓ ->
        h1' = h1 /\ eval_stmt CT rΓ h2 s r rΓ1 h2 /\ env_in P rΓ1.
Proof.
  intros CT D Htable rΓ h1 s r rΓ1 h1' Hrun.
  induction Hrun;
    intros sΓ mt sΓ_out h2 P Xderiv Xtyp Xwf Xagree Xpub;
    inversion Xderiv; subst.
  - (* skip *)
    repeat split; [constructor | assumption].
  - (* local declaration *)
    repeat split.
    + constructor. assumption.
    + apply env_in_append_default. assumption.
  - (* assignment *)
    have Hsim : eval_expr CT rΓ h2 e v2 OK rΓ h2.
    { eapply deriv_expr_simulation; eauto. }
    edestruct deriv_expr_noninterference as (_ & _ & Hin);
      [exact Hexpr | exact Xwf | exact Xagree | exact Xpub | exact Heval |
       exact Hsim |].
    repeat split.
    + eapply SBS_Assign; eassumption.
    + apply env_in_update; assumption.
  - (* assignment raising NPE *)
    repeat split; [| assumption].
    eapply SBS_Assign_NPE; [eassumption |].
    eapply deriv_expr_simulation; eauto.
  (* Calls: the receiver is public, so the second heap dispatches to the same
     method, whose body is replayed by induction. *)
  - destruct Hfind as [Hfind_m Hbody_eq]. subst.
    have Hly : P ly := Xpub y ly Hval_y.
    have Hsub : class_subtype CT cy Cy :=
      runtime_value_class_subtype CT _ rΓ h y Ty Cy ly cy
        Xwf Hget_y Href Hval_y Hbase.
    destruct (Htable mdef (Hdispatch cy mdef Hsub Hfind_m))
      as [sΓd Hbody_deriv].
    destruct (typed_call_has_wf_callee_frame CT _ _ rΓ h x m y zs _
      vals ly cy mdef Xwf Xtyp Hval_y Hbase Hfind_m Hargs)
      as [sΓt [Hbody_typ Hframe_wf]].
    have Hsame := deriv_stmt_typing_env CT D _ _ _ _ _ Hbody_deriv Hbody_typ.
    subst sΓd.
    have Hframe_pub := env_in_call_frame P rΓ zs vals ly Xpub Hly Hargs.
    destruct (IHHrun Htable _ _ _ h2 P Hbody_deriv Hbody_typ Hframe_wf Xagree
      Hframe_pub) as (Hh & Hbody2 & Hpub_body).
    subst.
    repeat split.
    + eapply SBS_Call; eauto.
      rewrite (abs_agree_basetype _ _ _ _ ly Xagree Hly). exact Hbase.
    + apply env_in_update; [assumption |].
      intros l ->. exact (Hpub_body _ l Hretval).
  - repeat split; [| assumption].
    apply SBS_Call_NPE. assumption.
  - destruct Hfind as [Hfind_m Hbody_eq]. subst.
    have Hly : P ly := Xpub y ly Hval_y.
    have Hsub : class_subtype CT cy Cy :=
      runtime_value_class_subtype CT _ rΓ h y Ty Cy ly cy
        Xwf Hget_y Href Hval_y Hbase.
    destruct (Htable mdef (Hdispatch cy mdef Hsub Hfind_m))
      as [sΓd Hbody_deriv].
    destruct (typed_call_has_wf_callee_frame CT _ _ rΓ h x m y zs _
      vals ly cy mdef Xwf Xtyp Hval_y Hbase Hfind_m Hargs)
      as [sΓt [Hbody_typ Hframe_wf]].
    have Hsame := deriv_stmt_typing_env CT D _ _ _ _ _ Hbody_deriv Hbody_typ.
    subst sΓd.
    have Hframe_pub := env_in_call_frame P rΓ zs vals ly Xpub Hly Hargs.
    destruct (IHHrun Htable _ _ _ h2 P Hbody_deriv Hbody_typ Hframe_wf Xagree
      Hframe_pub) as (Hh & Hbody2 & Hpub_body).
    subst.
    repeat split; [| assumption].
    eapply SBS_Call_NPE_Body; eauto.
    rewrite (abs_agree_basetype _ _ _ _ ly Xagree Hly). exact Hbase.
  - destruct Hfind as [Hfind_m Hbody_eq]. subst.
    have Hly : P ly := Xpub y ly Hval_y.
    have Hsub : class_subtype CT cy Cy :=
      runtime_value_class_subtype CT _ rΓ h y Ty Cy ly cy
        Xwf Hget_y Href Hval_y Hbase.
    destruct (Htable mdef (Hdispatch cy mdef Hsub Hfind_m))
      as [sΓd Hbody_deriv].
    destruct (typed_call_has_wf_callee_frame CT _ _ rΓ h x m y zs _
      vals ly cy mdef Xwf Xtyp Hval_y Hbase Hfind_m Hargs)
      as [sΓt [Hbody_typ Hframe_wf]].
    have Hsame := deriv_stmt_typing_env CT D _ _ _ _ _ Hbody_deriv Hbody_typ.
    subst sΓd.
    have Hframe_pub := env_in_call_frame P rΓ zs vals ly Xpub Hly Hargs.
    destruct (IHHrun Htable _ _ _ h2 P Hbody_deriv Hbody_typ Hframe_wf Xagree
      Hframe_pub) as (Hh & Hbody2 & Hpub_body).
    subst.
    repeat split; [| assumption].
    eapply SBS_Call_MUTATIONEXP_Body; eauto.
    rewrite (abs_agree_basetype _ _ _ _ ly Xagree Hly). exact Hbase.
  (* Sequences *)
  - inversion Xtyp; subst.
    have Hmid := deriv_stmt_typing_env CT D _ _ _ _ _ Hderiv1 Htype1. subst.
    destruct (IHHrun1 Htable _ _ _ h2 P Hderiv1 Htype1 Xwf Xagree Xpub)
      as (Hh1 & Hrun1' & Hpub1).
    subst.
    have Hmid_wf := preservation_pico CT _ _ _ _ _ _ _ _ Xwf Htype1 Hrun1.
    destruct (IHHrun2 Htable _ _ _ h2 P Hderiv2 Htype2 Hmid_wf Xagree Hpub1)
      as (Hh2 & Hrun2' & Hpub2).
    subst.
    repeat split; [| assumption].
    eapply SBS_Seq; eassumption.
  - inversion Xtyp; subst.
    have Hmid := deriv_stmt_typing_env CT D _ _ _ _ _ Hderiv1 Htype1. subst.
    destruct (IHHrun Htable _ _ _ h2 P Hderiv1 Htype1 Xwf Xagree Xpub)
      as (Hh1 & Hrun1' & Hpub1).
    subst.
    repeat split; [| assumption].
    apply SBS_Seq_NPE_first. assumption.
  - inversion Xtyp; subst.
    have Hmid := deriv_stmt_typing_env CT D _ _ _ _ _ Hderiv1 Htype1. subst.
    destruct (IHHrun1 Htable _ _ _ h2 P Hderiv1 Htype1 Xwf Xagree Xpub)
      as (Hh1 & Hrun1' & Hpub1).
    subst.
    have Hmid_wf := preservation_pico CT _ _ _ _ _ _ _ _ Xwf Htype1 Hrun1.
    destruct (IHHrun2 Htable _ _ _ h2 P Hderiv2 Htype2 Hmid_wf Xagree Hpub1)
      as (Hh2 & Hrun2' & Hpub2).
    subst.
    repeat split; [| assumption].
    eapply SBS_Seq_NPE_second; eassumption.
  - inversion Xtyp; subst.
    have Hmid := deriv_stmt_typing_env CT D _ _ _ _ _ Hderiv1 Htype1. subst.
    destruct (IHHrun Htable _ _ _ h2 P Hderiv1 Htype1 Xwf Xagree Xpub)
      as (Hh1 & Hrun1' & Hpub1).
    subst.
    repeat split; [| assumption].
    apply SBS_Seq_MUTATIONEXP_first. assumption.
  - inversion Xtyp; subst.
    have Hmid := deriv_stmt_typing_env CT D _ _ _ _ _ Hderiv1 Htype1. subst.
    destruct (IHHrun1 Htable _ _ _ h2 P Hderiv1 Htype1 Xwf Xagree Xpub)
      as (Hh1 & Hrun1' & Hpub1).
    subst.
    have Hmid_wf := preservation_pico CT _ _ _ _ _ _ _ _ Xwf Htype1 Hrun1.
    destruct (IHHrun2 Htable _ _ _ h2 P Hderiv2 Htype2 Hmid_wf Xagree Hpub1)
      as (Hh2 & Hrun2' & Hpub2).
    subst.
    repeat split; [| assumption].
    eapply SBS_Seq_MUTATIONEXP_second; eassumption.
  (* Zero tests *)
  - inversion Xtyp; subst.
    edestruct (IHHrun Htable) as (Hh & Hrun' & Hpub');
      [exact Hzero | eassumption | exact Xwf | exact Xagree | exact Xpub |].
    subst.
    repeat split; [| assumption].
    eapply SBS_IfZero; eassumption.
  - inversion Xtyp; subst.
    edestruct (IHHrun Htable) as (Hh & Hrun' & Hpub');
      [exact Hnonzero | eassumption | exact Xwf | exact Xagree | exact Xpub |].
    subst.
    repeat split; [| assumption].
    eapply SBS_IfNonzero; eassumption.
  - inversion Xtyp; subst.
    edestruct (IHHrun Htable) as (Hh & Hrun' & Hpub');
      [exact Hzero | eassumption | exact Xwf | exact Xagree | exact Xpub |].
    subst.
    repeat split; [| assumption].
    eapply SBS_IfNull; eassumption.
  - inversion Xtyp; subst.
    edestruct (IHHrun Htable) as (Hh & Hrun' & Hpub');
      [exact Hnonzero | eassumption | exact Xwf | exact Xagree | exact Xpub |].
    subst.
    repeat split; [| assumption].
    eapply SBS_IfRef; eassumption.
Qed.

(** ** Stability of the abstract state

    PICO's abstract-state preservation theorem says a well-typed statement
    never changes the non-[Assign] fields of objects reachable through
    abstract state from an immutable root.  In the vocabulary of this file:
    the heap before and after the statement agree on that reachable set. *)

Lemma wf_heap_field_location_dom :
  forall CT h l o f l',
    wf_heap CT h ->
    runtime_getObj h l = Some o ->
    nth_error (fields_map o) f = Some (Iot l') ->
    l' < dom h.
Proof.
  intros CT h l o f l' Hheap Hobj Hfield.
  have Hdom := runtime_getObj_dom l o h Hobj.
  have Hwf := Hheap l Hdom.
  unfold wf_obj in Hwf. rewrite Hobj in Hwf.
  destruct Hwf as [_ [field_defs [_ [Hlen Hfields]]]].
  assert (Hf : f < length field_defs).
  { rewrite <- Hlen. apply nth_error_Some. rewrite Hfield. discriminate. }
  destruct (nth_error_Some_exists field_defs f Hf) as [fdef Hfdef].
  have Hentry := Forall2_nth_error _ _ _ _ _ _ Hfields Hfield Hfdef.
  simpl in Hentry.
  destruct (runtime_getObj h l') as [o'|] eqn:Hl'; [|contradiction].
  exact (runtime_getObj_dom l' o' h Hl').
Qed.

Lemma reachable_abs_target_dom :
  forall CT h l0 l1,
    reachable_abs CT h l0 l1 ->
    l1 < dom h.
Proof.
  intros CT h l0 l1 Hreach.
  induction Hreach; assumption.
Qed.

Theorem abstract_state_agreement_preserved :
  forall CT sΓ mt rΓ h s rΓ' h' sΓ' root C0 vals0,
    runtime_getObj h root = Some (mkObj (mkruntime_type Imm_r C0) vals0) ->
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ mt s sΓ' ->
    eval_stmt CT rΓ h s OK rΓ' h' ->
    abs_agree CT (reachable_abs CT h root) h h'.
Proof.
  intros CT sΓ mt rΓ h s rΓ' h' sΓ' root C0 vals0 Hroot Hwf Htyping Heval
    l Hreach.
  have Hdom := reachable_abs_target_dom CT h root l Hreach.
  destruct (runtime_getObj_Some h l Hdom) as [rt [fs1 Hobj1]].
  destruct rt as [qr C].
  destruct (runtime_preserves_r_type_heap CT rΓ h l (mkruntime_type qr C) h'
    fs1 s rΓ' Hobj1 Heval) as [fs2 Hobj2].
  exists (mkruntime_type qr C), fs1, fs2.
  split; [exact Hobj1 |].
  split; [exact Hobj2 |].
  intros f [Hmut Hassign].
  simpl in Hmut, Hassign.
  split.
  - unfold getVal.
    eapply abstract_state_preservation_with_end;
      [exact Hroot | exact Hreach | exact Hwf | exact Htyping | exact Heval |
       exact Hobj1 | exact Hobj2 |].
    destruct Hassign as [Hrda | Hfinal]; [right | left]; assumption.
  - intros l' Hl'.
    have Hheap : wf_heap CT h by (destruct Hwf as [_ [Hheap _]]; exact Hheap).
    eapply reachable_abs_trans; [exact Hreach |].
    eapply reachable_abs_step;
      [| exact Hobj1 | exact Hl' | exact Hmut | exact Hassign].
    eapply wf_heap_field_location_dom; [exact Hheap | exact Hobj1 | exact Hl'].
Qed.

(** ** Stability of derived values

    A derivation that reads only the abstract state reachable from an
    immutable root gives the same result after any well-typed statement as it
    did before: it can be replayed in the later heap, and every run there
    agrees with the earlier one.  So the set of valid cache values, which is
    defined by the derivation's result, never changes. *)
Corollary derivation_result_stable :
  forall CT D sΓ mt rΓ h s rΓ' h' sΓ' root C0 vals0,
    derivation_table CT D ->
    runtime_getObj h root = Some (mkObj (mkruntime_type Imm_r C0) vals0) ->
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ mt s sΓ' ->
    eval_stmt CT rΓ h s OK rΓ' h' ->
    forall sΓd mtd sΓd' d rΓd rd rΓd' hd,
      deriv_stmt CT D sΓd d sΓd' ->
      stmt_typing CT sΓd mtd d sΓd' ->
      wf_r_config CT sΓd rΓd h ->
      env_in (reachable_abs CT h root) rΓd ->
      eval_stmt CT rΓd h d rd rΓd' hd ->
      eval_stmt CT rΓd h' d rd rΓd' h' /\
      (forall rd2 rΓd2 hd2,
        eval_stmt CT rΓd h' d rd2 rΓd2 hd2 ->
        rd2 = rd /\ rΓd2 = rΓd').
Proof.
  intros CT D sΓ mt rΓ h s rΓ' h' sΓ' root C0 vals0 Htable Hroot Hwf Htyping
    Heval sΓd mtd sΓd' d rΓd rd rΓd' hd Hderiv Hdtyp Hdwf Hpub Hrun.
  have Hagree := abstract_state_agreement_preserved CT sΓ mt rΓ h s rΓ' h' sΓ'
    root C0 vals0 Hroot Hwf Htyping Heval.
  destruct (derivation_simulation CT D Htable rΓd h d rd rΓd' hd Hrun
    sΓd mtd sΓd' h' _ Hderiv Hdtyp Hdwf Hagree Hpub) as (_ & Hrun' & _).
  split; [exact Hrun' |].
  intros rd2 rΓd2 hd2 Hrun2.
  destruct (derivation_noninterference CT D Htable rΓd h d rd rΓd' hd Hrun
    sΓd mtd sΓd' h' _ rd2 rΓd2 hd2 Hderiv Hdtyp Hdwf Hagree Hpub Hrun2)
    as (Hr & Henv & _).
  split; symmetry; assumption.
Qed.
