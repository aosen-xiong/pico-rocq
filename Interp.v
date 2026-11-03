From Stdlib Require Import List Lia PeanoNat Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation MutationSafety Progress.

(** A fuel-based definitional interpreter.

    [run CT n rΓ h s] computes the outcome of evaluating [s] with budget [n]:
    a result with the final environment and heap, or [None] when evaluation
    is stuck.  As in [eval_fuel], only a method call spends budget.

    The interpreter is sound for the evaluation with a budget, and complete
    for it over a well-formed class table, so the two define the same
    semantics, the outcome of an evaluation with a budget is unique, and the
    progress theorem holds for the interpreter: on a well-typed statement in
    a well-formed state it returns a normal finish, a null dereference, or a
    timeout. *)

(* ------------------COMPUTABLE LOOKUPS------------------*)

(** The lookups of the semantics walk up the superclass chain.  Each function
    takes a bound on the length of the walk; in a well-formed class table a
    superclass has a smaller index, so the index of the starting class plus
    one is enough. *)

Fixpoint collect_fields_f (k : nat) (CT : class_table) (C : class_name)
    : option (list field_def) :=
  match k with
  | 0 => None
  | S k' =>
      match find_class CT C with
      | None => Some []
      | Some def =>
          match super (signature def) with
          | None => Some []
          | Some (P, Ss) =>
              match collect_fields_f k' CT P with
              | Some pf => Some (map (subst_field Ss) pf ++ Syntax.fields (body def))
              | None => None
              end
          end
      end
  end.

Lemma collect_fields_f_sound : forall k CT C fs,
  collect_fields_f k CT C = Some fs -> CollectFields CT C fs.
Proof.
  induction k as [|k IH]; intros CT C fs H; simpl in H; [discriminate|].
  destruct (find_class CT C) as [def|] eqn:Hf.
  - destruct (super (signature def)) as [[P Ss]|] eqn:Hs.
    + destruct (collect_fields_f k CT P) as [pf|] eqn:Hp; [|discriminate].
      inversion H; subst. eapply CF_Inherit; eauto.
    + inversion H; subst. eapply CF_Object; eauto.
  - inversion H; subst. apply CF_NotFound. exact Hf.
Qed.

Lemma collect_fields_f_complete : forall CT C fs,
  wf_class_table CT -> CollectFields CT C fs ->
  forall k, C < k -> collect_fields_f k CT C = Some fs.
Proof.
  intros CT C fs Hct H. induction H; intros k Hk; destruct k as [|k]; try lia; simpl.
  - rewrite Hnone. reflexivity.
  - rewrite Hfind. rewrite Hsuper. reflexivity.
  - rewrite Hfind. rewrite Hsuper.
    destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hsuper) as (sd & _ & Hlt & _).
    rewrite (IHCollectFields Hct k ltac:(lia)). subst own_fields. reflexivity.
Qed.

Definition assign_f (CT : class_table) (C : class_name) (f : var) : option a :=
  match collect_fields_f (S C) CT C with
  | Some fs => option_map assignability (gget fs f)
  | None => None
  end.

Lemma assign_f_sound : forall CT C f a0,
  assign_f CT C f = Some a0 -> sf_assignability_rel CT C f a0.
Proof.
  intros CT C f a0 H. unfold assign_f in H.
  destruct (collect_fields_f (S C) CT C) as [fs|] eqn:Hc; [|discriminate].
  destruct (gget fs f) as [fd|] eqn:Hg; [|discriminate].
  simpl in H. inversion H; subst. exists fd. split; [|reflexivity].
  eapply FL_Found; [eapply collect_fields_f_sound; eauto | exact Hg].
Qed.

Lemma assign_f_complete : forall CT C f a0,
  wf_class_table CT -> sf_assignability_rel CT C f a0 -> assign_f CT C f = Some a0.
Proof.
  intros CT C f a0 Hct (fd & Hfl & Ha). inversion Hfl; subst.
  unfold assign_f.
  rewrite (collect_fields_f_complete _ _ _ Hct Hcf (S C) ltac:(lia)).
  rewrite Hget. reflexivity.
Qed.

Fixpoint find_method_f (k : nat) (CT : class_table) (C : class_name)
    (m : method_name) : option (class_name * method_def) :=
  match k with
  | 0 => None
  | S k' =>
      match find_class CT C with
      | None => None
      | Some def =>
          match gget_method (methods (body def)) m with
          | Some mdef => Some (C, mdef)
          | None =>
              match super (signature def) with
              | Some (P, _) => find_method_f k' CT P m
              | None => None
              end
          end
      end
  end.

Lemma find_method_f_sound : forall k CT C m D mdef,
  find_method_f k CT C m = Some (D, mdef) -> FindMethodWithName CT C m D mdef.
Proof.
  induction k as [|k IH]; intros CT C m D mdef H; simpl in H; [discriminate|].
  destruct (find_class CT C) as [def|] eqn:Hf; [|discriminate].
  destruct (gget_method (methods (body def)) m) as [md|] eqn:Hg.
  - inversion H; subst. eapply FOM_Here; eauto.
  - destruct (super (signature def)) as [[P Ss]|] eqn:Hs; [|discriminate].
    eapply FOM_Super; eauto.
Qed.

Lemma find_method_f_complete : forall CT C m D mdef,
  wf_class_table CT -> FindMethodWithName CT C m D mdef ->
  forall k, C < k -> find_method_f k CT C m = Some (D, mdef).
Proof.
  intros CT C m D mdef Hct H. induction H; intros k Hk; destruct k as [|k]; try lia;
    simpl; rewrite Hfind; subst own_methods.
  - rewrite Hget_method. reflexivity.
  - rewrite Hnot_here. rewrite Hsuper.
    destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hsuper) as (sd & _ & Hlt & _).
    apply IHFindMethodWithName; [exact Hct | lia].
Qed.

Fixpoint rsuper_f (k : nat) (CT : class_table) (qh : q) (C : class_name)
    (Rs : list rtype) (D : class_name) : option (list rtype) :=
  match k with
  | 0 => None
  | S k' =>
      if Nat.eqb C D then Some Rs
      else match parent_lookup CT C with
           | Some (P, Ss) => rsuper_f k' CT qh P (map (dyn qh Rs [] []) Ss) D
           | None => None
           end
  end.

Lemma rsuper_f_sound : forall k CT qh C Rs D Vs,
  rsuper_f k CT qh C Rs D = Some Vs -> rsuper_inst CT qh C Rs D Vs.
Proof.
  induction k as [|k IH]; intros CT qh C Rs D Vs H; simpl in H; [discriminate|].
  destruct (Nat.eqb C D) eqn:E.
  - apply Nat.eqb_eq in E. inversion H; subst. apply rsi_refl.
  - destruct (parent_lookup CT C) as [[P Ss]|] eqn:Hp; [|discriminate].
    eapply rsi_step; eauto.
Qed.

Lemma rsuper_f_complete : forall CT qh C Rs D Vs,
  wf_class_table CT -> rsuper_inst CT qh C Rs D Vs ->
  forall k, C < k -> rsuper_f k CT qh C Rs D = Some Vs.
Proof.
  intros CT qh C Rs D Vs Hct H. induction H; intros k Hk; destruct k as [|k];
    try lia; simpl.
  - rewrite Nat.eqb_refl. reflexivity.
  - pose proof (rsuper_inst_le _ _ _ _ _ _ Hct H) as Hle.
    pose proof Hparent as Hp. unfold parent_lookup in Hp.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
    destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hp) as (sd & _ & Hlt & _).
    assert (E : Nat.eqb C D = false) by (apply Nat.eqb_neq; lia).
    rewrite E. rewrite Hparent. apply IHrsuper_inst. lia.
Qed.

Definition callee_env_f (CT : class_table) (rΓ : r_env) (h : heap) (ly : Loc)
    (D : class_name) (Us : list qualified_type) (Qs : list qarg)
    (vals : list value) : option r_env :=
  match runtime_getVal rΓ 0 with
  | Some (Iot lthis) =>
      match r_muttype h lthis with
      | Some qthis =>
          match runtime_getObj h ly with
          | Some oy =>
              match rsuper_f (S (rctype (rt_type oy))) CT (qr2q (rqtype (rt_type oy)))
                      (rctype (rt_type oy)) (rtargs (rt_type oy)) D with
              | Some cargs' =>
                  Some (mkr_env (Iot ly :: vals) cargs'
                          (map (dyn (qr2q qthis) (cargs rΓ) (margs rΓ) (qargs rΓ)) Us)
                          (map (rqarg (qr2q qthis) (qargs rΓ)) Qs))
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

Lemma callee_env_f_sound : forall CT rΓ h ly D Us Qs vals rΓc,
  callee_env_f CT rΓ h ly D Us Qs vals = Some rΓc ->
  callee_env CT rΓ h ly D Us Qs vals rΓc.
Proof.
  intros CT rΓ h ly D Us Qs vals rΓc H. unfold callee_env_f in H.
  destruct (runtime_getVal rΓ 0) as [[|lthis]|] eqn:H0; try discriminate.
  destruct (r_muttype h lthis) as [qthis|] eqn:Hm; [|discriminate].
  destruct (runtime_getObj h ly) as [oy|] eqn:Ho; [|discriminate].
  destruct (rsuper_f _ CT _ _ _ D) as [cargs'|] eqn:Hr; [|discriminate].
  inversion H; subst. exists lthis, qthis, oy, cargs'.
  repeat split; auto. eapply rsuper_f_sound; eauto.
Qed.

Lemma callee_env_f_complete : forall CT rΓ h ly D Us Qs vals rΓc,
  wf_class_table CT ->
  callee_env CT rΓ h ly D Us Qs vals rΓc ->
  callee_env_f CT rΓ h ly D Us Qs vals = Some rΓc.
Proof.
  intros CT rΓ h ly D Us Qs vals rΓc Hct
    (lthis & qthis & oy & cargs' & H0 & Hm & Ho & Hr & ->).
  unfold callee_env_f. rewrite H0. rewrite Hm. rewrite Ho.
  rewrite (rsuper_f_complete _ _ _ _ _ _ Hct Hr (S (rctype (rt_type oy)))
             (Nat.lt_succ_diag_r _)). reflexivity.
Qed.

(* ------------------THE INTERPRETER------------------*)

Definition eval_expr_f (rΓ : r_env) (h : heap) (e : expr)
    : option (value * eval_result) :=
  match e with
  | ENull => Some (Null_a, OK)
  | EVar x =>
      match runtime_getVal rΓ x with
      | Some v => Some (v, OK)
      | None => None
      end
  | EField x f =>
      match runtime_getVal rΓ x with
      | Some (Iot l) =>
          match runtime_getObj h l with
          | Some o =>
              match getVal (fields_map o) f with
              | Some v1 => Some (v1, OK)
              | None => None
              end
          | None => None
          end
      | Some Null_a => Some (Null_a, NPE)
      | None => None
      end
  end.

(** One statement that is neither a sequence nor a call. *)
Definition step_atomic (CT : class_table) (rΓ : r_env) (h : heap) (s : stmt)
    : option (eval_result * r_env * heap) :=
  match s with
  | SSkip => Some (OK, rΓ, h)
  | SLocal T x =>
      match runtime_getVal rΓ x with
      | None => Some (OK, set_vars rΓ (vars rΓ ++ [Null_a]), h)
      | Some _ => None
      end
  | SVarAss x e =>
      match runtime_getVal rΓ x with
      | Some _ =>
          match eval_expr_f rΓ h e with
          | Some (v, OK) => Some (OK, set_vars rΓ (update x v (vars rΓ)), h)
          | Some (_, NPE) => Some (NPE, rΓ, h)
          | _ => None
          end
      | None => None
      end
  | SFldWrite x f y =>
      match runtime_getVal rΓ x with
      | Some Null_a => Some (NPE, rΓ, h)
      | Some (Iot l) =>
          match runtime_getObj h l with
          | Some o =>
              match getVal (fields_map o) f with
              | Some _ =>
                  match assign_f CT (rctype (rt_type o)) f with
                  | Some a0 =>
                      match runtime_getVal rΓ y with
                      | Some vy =>
                          match runtime_vpa_assignability (rqtype (rt_type o)) a0 with
                          | Assignable => Some (OK, rΓ, update_field h l f vy)
                          | Final => Some (MUTATIONEXP, rΓ, h)
                          | RDA => None
                          end
                      | None => None
                      end
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | SNew x qc C Ts ys =>
      match runtime_getVal rΓ 0 with
      | Some (Iot l1) =>
          match runtime_lookup_list rΓ ys with
          | Some vals =>
              match r_muttype h l1 with
              | Some qthis =>
                  Some (OK,
                        set_vars rΓ (update x (Iot (dom h)) (vars rΓ)),
                        h ++ [mkObj
                                (mkruntime_type (vpa_mutability_object_creation qthis qc) C
                                   (map (dyn (qr2q qthis) (cargs rΓ) (margs rΓ) (qargs rΓ)) Ts))
                                vals])
              | None => None
              end
          | None => None
          end
      | _ => None
      end
  | SCast x T y =>
      match runtime_getVal rΓ x with
      | Some _ =>
          match runtime_getVal rΓ y with
          | Some v2 => Some (OK, set_vars rΓ (update x v2 (vars rΓ)), h)
          | None => None
          end
      | None => None
      end
  | SCall _ _ _ _ _ _ => None
  | SSeq _ _ => None
  end.

Definition run_call_body (CT : class_table) (rΓ : r_env) (x : var)
    (mdef : method_def) (r : option (fres * r_env * heap))
    : option (fres * r_env * heap) :=
  match r with
  | Some (FDone OK, rΓb, hb) =>
      match runtime_getVal rΓb (mreturn (mbody mdef)) with
      | Some retval => Some (FDone OK, set_vars rΓ (update x retval (vars rΓ)), hb)
      | None => None
      end
  | other => other
  end.

Fixpoint run (CT : class_table) (n : nat) (rΓ : r_env) (h : heap) (s : stmt)
    {struct n} : option (fres * r_env * heap) :=
  (fix go (s : stmt) (rΓ : r_env) (h : heap) {struct s}
       : option (fres * r_env * heap) :=
     match s with
     | SSeq s1 s2 =>
         match go s1 rΓ h with
         | Some (FDone OK, rΓ1, h1) => go s2 rΓ1 h1
         | other => other
         end
     | SCall x m y Us Qs zs =>
         match runtime_getVal rΓ y with
         | Some Null_a => Some (FDone NPE, rΓ, h)
         | Some (Iot ly) =>
             match r_basetype h ly with
             | Some cy =>
                 match find_method_f (S cy) CT cy m with
                 | Some (D, mdef) =>
                     match runtime_lookup_list rΓ zs with
                     | Some vals =>
                         match callee_env_f CT rΓ h ly D Us Qs vals with
                         | Some rΓc =>
                             match n with
                             | 0 => Some (FTimeout, rΓ, h)
                             | S k =>
                                 run_call_body CT rΓ x mdef
                                   (run CT k rΓc h (mbody_stmt (mbody mdef)))
                             end
                         | None => None
                         end
                     | None => None
                     end
                 | None => None
                 end
             | None => None
             end
         | None => None
         end
     | _ =>
         match step_atomic CT rΓ h s with
         | Some (r, rΓ', h') => Some (FDone r, rΓ', h')
         | None => None
         end
     end) s rΓ h.

(** The interpreter, one statement form at a time. *)
Lemma run_seq : forall CT n rΓ h s1 s2,
  run CT n rΓ h (SSeq s1 s2) =
  match run CT n rΓ h s1 with
  | Some (FDone OK, rΓ1, h1) => run CT n rΓ1 h1 s2
  | other => other
  end.
Proof. intros. destruct n; reflexivity. Qed.

Lemma run_atomic : forall CT n rΓ h s,
  atomic s ->
  run CT n rΓ h s =
  match step_atomic CT rΓ h s with
  | Some (r, rΓ', h') => Some (FDone r, rΓ', h')
  | None => None
  end.
Proof. intros CT n rΓ h s Ha. destruct n; destruct s; simpl in Ha; try contradiction; reflexivity. Qed.

Lemma run_call : forall CT n rΓ h x m y Us Qs zs,
  run CT n rΓ h (SCall x m y Us Qs zs) =
  match runtime_getVal rΓ y with
  | Some Null_a => Some (FDone NPE, rΓ, h)
  | Some (Iot ly) =>
      match r_basetype h ly with
      | Some cy =>
          match find_method_f (S cy) CT cy m with
          | Some (D, mdef) =>
              match runtime_lookup_list rΓ zs with
              | Some vals =>
                  match callee_env_f CT rΓ h ly D Us Qs vals with
                  | Some rΓc =>
                      match n with
                      | 0 => Some (FTimeout, rΓ, h)
                      | S k => run_call_body CT rΓ x mdef
                                 (run CT k rΓc h (mbody_stmt (mbody mdef)))
                      end
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.
Proof. intros. destruct n; reflexivity. Qed.

(* ------------------SOUNDNESS------------------*)

Lemma eval_expr_f_sound : forall CT rΓ h e v r,
  eval_expr_f rΓ h e = Some (v, r) -> eval_expr CT rΓ h e v r rΓ h.
Proof.
  intros CT rΓ h e v r H. destruct e as [|x|x f]; simpl in H.
  - inversion H; subst. apply EBS_Null.
  - destruct (runtime_getVal rΓ x) as [v0|] eqn:Hx; [|discriminate].
    inversion H; subst. apply EBS_Val. exact Hx.
  - destruct (runtime_getVal rΓ x) as [[|l]|] eqn:Hx; try discriminate.
    + inversion H; subst. apply EBS_Field_NPE. exact Hx.
    + destruct (runtime_getObj h l) as [o|] eqn:Ho; [|discriminate].
      destruct (getVal (fields_map o) f) as [v1|] eqn:Hf; [|discriminate].
      inversion H; subst. eapply EBS_Field; eauto.
Qed.

Lemma step_atomic_sound : forall CT rΓ h s r rΓ' h',
  step_atomic CT rΓ h s = Some (r, rΓ', h') -> eval_stmt CT rΓ h s r rΓ' h'.
Proof.
  intros CT rΓ h s r rΓ' h' H. destruct s; simpl in H; try discriminate.
  - inversion H; subst. apply SBS_Skip.
  - destruct (runtime_getVal rΓ v) eqn:Hx; [discriminate|].
    inversion H; subst. apply SBS_Local. exact Hx.
  - destruct (runtime_getVal rΓ v) as [v1|] eqn:Hx; [|discriminate].
    destruct (eval_expr_f rΓ h e) as [[v2 r2]|] eqn:He; [|discriminate].
    destruct r2; inversion H; subst.
    + eapply SBS_Assign; eauto using eval_expr_f_sound.
    + eapply SBS_Assign_NPE; eauto using eval_expr_f_sound.
  - destruct (runtime_getVal rΓ v) as [[|l]|] eqn:Hx; try discriminate.
    + inversion H; subst. apply SBS_FldWrite_NPE. exact Hx.
    + destruct (runtime_getObj h l) as [o|] eqn:Ho; [|discriminate].
      destruct (getVal (fields_map o) v0) as [vf|] eqn:Hf; [|discriminate].
      destruct (assign_f CT (rctype (rt_type o)) v0) as [a0|] eqn:Ha; [|discriminate].
      destruct (runtime_getVal rΓ v1) as [vy|] eqn:Hy; [|discriminate].
      destruct (runtime_vpa_assignability (rqtype (rt_type o)) a0) eqn:Hr;
        inversion H; subst.
      * eapply SBS_FldWrite; eauto using assign_f_sound.
      * eapply SBS_FldWrite_MUTATIONEXP; eauto using assign_f_sound.
  - destruct (runtime_getVal rΓ 0) as [[|l1]|] eqn:H0; try discriminate.
    destruct (runtime_lookup_list rΓ l0) as [vals|] eqn:Hl; [|discriminate].
    destruct (r_muttype h l1) as [qthis|] eqn:Hm; [|discriminate].
    inversion H; subst. eapply SBS_New; eauto.
  - destruct (runtime_getVal rΓ v) as [v1|] eqn:Hx; [|discriminate].
    destruct (runtime_getVal rΓ v0) as [v2|] eqn:Hy; [|discriminate].
    inversion H; subst. eapply SBS_Cast; eauto.
Qed.

Lemma step_atomic_atomic : forall CT rΓ h s x,
  step_atomic CT rΓ h s = Some x -> atomic s.
Proof. intros CT rΓ h s x H. destruct s; simpl in *; try exact I; discriminate. Qed.

Theorem run_sound : forall CT n s rΓ h r rΓ' h',
  run CT n rΓ h s = Some (r, rΓ', h') -> eval_fuel CT n rΓ h s r rΓ' h'.
Proof.
  intros CT n. induction n as [n IHn] using lt_wf_ind.
  assert (Hatom : forall s rΓ h r rΓ' h', atomic s ->
            run CT n rΓ h s = Some (r, rΓ', h') -> eval_fuel CT n rΓ h s r rΓ' h').
  { intros s rΓ h r rΓ' h' Ha H. rewrite (run_atomic _ _ _ _ _ Ha) in H.
    destruct (step_atomic CT rΓ h s) as [[[r1 rΓ1] h1]|] eqn:Hs; [|discriminate].
    inversion H; subst. apply EF_Atom; [exact Ha | apply step_atomic_sound; exact Hs]. }
  induction s; intros rΓ h r rΓ' h' H; try (apply Hatom; [exact I | exact H]).
  - (* call *)
    rewrite run_call in H.
    destruct (runtime_getVal rΓ v0) as [[|ly]|] eqn:Hy; try discriminate.
    { inversion H; subst. apply EF_Call_NPE. exact Hy. }
    destruct (r_basetype h ly) as [cy|] eqn:Hb; [|discriminate].
    destruct (find_method_f (S cy) CT cy m) as [[D mdef]|] eqn:Hf; [|discriminate].
    destruct (runtime_lookup_list rΓ l1) as [vals|] eqn:Hl; [|discriminate].
    destruct (callee_env_f CT rΓ h ly D l l0 vals) as [rΓc|] eqn:Hc; [|discriminate].
    apply find_method_f_sound in Hf. apply callee_env_f_sound in Hc.
    destruct n as [|k].
    { inversion H; subst. eapply EF_Call_Timeout; eauto. }
    unfold run_call_body in H.
    destruct (run CT k rΓc h (mbody_stmt (mbody mdef))) as [[[rb rΓb] hb]|] eqn:Hr;
      [|discriminate].
    pose proof (IHn k (Nat.lt_succ_diag_r k) _ _ _ _ _ _ Hr) as Hbody.
    destruct rb as [[| |]|].
    + destruct (runtime_getVal rΓb (mreturn (mbody mdef))) as [retval|] eqn:Hret;
        [|discriminate].
      inversion H; subst. eapply EF_Call; eauto.
    + inversion H; subst. eapply EF_Call_Fail; eauto. discriminate.
    + inversion H; subst. eapply EF_Call_Fail; eauto. discriminate.
    + inversion H; subst. eapply EF_Call_Fail; eauto. discriminate.
  - (* sequence *)
    rewrite run_seq in H.
    destruct (run CT n rΓ h s1) as [[[r1 rΓ1] h1]|] eqn:H1; [|discriminate].
    destruct r1 as [[| |]|].
    + eapply EF_Seq; [apply IHs1; exact H1 | apply IHs2; exact H].
    + inversion H; subst. eapply EF_Seq_Fail; [apply IHs1; exact H1 | discriminate].
    + inversion H; subst. eapply EF_Seq_Fail; [apply IHs1; exact H1 | discriminate].
    + inversion H; subst. eapply EF_Seq_Fail; [apply IHs1; exact H1 | discriminate].
Qed.

(* ------------------COMPLETENESS------------------*)

Lemma eval_expr_f_complete : forall CT rΓ h e v r rΓ' h',
  eval_expr CT rΓ h e v r rΓ' h' ->
  eval_expr_f rΓ h e = Some (v, r) /\ rΓ' = rΓ /\ h' = h.
Proof.
  intros CT rΓ h e v r rΓ' h' H. inversion H; subst; simpl.
  - auto.
  - rewrite Hval. auto.
  - rewrite Hval. rewrite Hobj. rewrite Hfield. auto.
  - rewrite Hnull. auto.
Qed.

Lemma step_atomic_complete : forall CT rΓ h s r rΓ' h',
  wf_class_table CT -> atomic s ->
  eval_stmt CT rΓ h s r rΓ' h' ->
  step_atomic CT rΓ h s = Some (r, rΓ', h').
Proof.
  intros CT rΓ h s r rΓ' h' Hct Ha H.
  inversion H; subst; simpl in Ha; try contradiction; simpl.
  - reflexivity.
  - rewrite Hnone. reflexivity.
  - rewrite Hval.
    destruct (eval_expr_f_complete _ _ _ _ _ _ _ _ Heval) as (He & _ & _).
    rewrite He. reflexivity.
  - rewrite Hval.
    destruct (eval_expr_f_complete _ _ _ _ _ _ _ _ Heval) as (He & _ & _).
    rewrite He. reflexivity.
  - rewrite Hval_x. rewrite Hobj. rewrite Hfield.
    rewrite (assign_f_complete _ _ _ _ Hct Hassign). rewrite Hval_y.
    rewrite Hruntime_assignable. reflexivity.
  - rewrite Hnull. reflexivity.
  - rewrite Hval_x. rewrite Hobj. rewrite Hfield.
    rewrite (assign_f_complete _ _ _ _ Hct Hassign). rewrite Hval_y.
    rewrite Hfinal. reflexivity.
  - rewrite Hthis. rewrite Hargs. rewrite Hmut. reflexivity.
  - rewrite Hval_x. rewrite Hval_y. reflexivity.
Qed.

Theorem run_complete : forall CT n rΓ h s r rΓ' h',
  wf_class_table CT ->
  eval_fuel CT n rΓ h s r rΓ' h' ->
  run CT n rΓ h s = Some (r, rΓ', h').
Proof.
  intros CT n rΓ h s r rΓ' h' Hct H. induction H.
  - rewrite (run_atomic _ _ _ _ _ Hatom).
    rewrite (step_atomic_complete _ _ _ _ _ _ _ Hct Hatom Heval). reflexivity.
  - rewrite run_call. rewrite Hnull. reflexivity.
  - rewrite run_call. rewrite Hval_y. rewrite Hbase.
    rewrite (find_method_f_complete _ _ _ _ _ Hct Hfind (S cy) (Nat.lt_succ_diag_r _)).
    rewrite Hargs. rewrite (callee_env_f_complete _ _ _ _ _ _ _ _ _ Hct Hframe).
    reflexivity.
  - rewrite run_call. rewrite Hval_y. rewrite Hbase.
    rewrite (find_method_f_complete _ _ _ _ _ Hct Hfind (S cy) (Nat.lt_succ_diag_r _)).
    rewrite Hargs. rewrite (callee_env_f_complete _ _ _ _ _ _ _ _ _ Hct Hframe).
    unfold run_call_body. rewrite (IHeval_fuel Hct). rewrite Hretval. reflexivity.
  - rewrite run_call. rewrite Hval_y. rewrite Hbase.
    rewrite (find_method_f_complete _ _ _ _ _ Hct Hfind (S cy) (Nat.lt_succ_diag_r _)).
    rewrite Hargs. rewrite (callee_env_f_complete _ _ _ _ _ _ _ _ _ Hct Hframe).
    unfold run_call_body. rewrite (IHeval_fuel Hct).
    destruct r as [[| |]|]; try reflexivity. contradiction Hfail. reflexivity.
  - rewrite run_seq. rewrite (IHeval_fuel1 Hct). exact (IHeval_fuel2 Hct).
  - rewrite run_seq. rewrite (IHeval_fuel Hct).
    destruct r as [[| |]|]; try reflexivity. contradiction Hfail. reflexivity.
Qed.

(* ------------------THE THEOREMS------------------*)

(** The interpreter and the evaluation with a budget define the same
    semantics. *)
Theorem run_agrees : forall CT n rΓ h s r rΓ' h',
  wf_class_table CT ->
  (run CT n rΓ h s = Some (r, rΓ', h') <-> eval_fuel CT n rΓ h s r rΓ' h').
Proof.
  intros. split; [apply run_sound | apply run_complete; assumption].
Qed.

(** The outcome of an evaluation with a budget is unique. *)
Corollary eval_fuel_deterministic : forall CT n rΓ h s r1 rΓ1 h1 r2 rΓ2 h2,
  wf_class_table CT ->
  eval_fuel CT n rΓ h s r1 rΓ1 h1 ->
  eval_fuel CT n rΓ h s r2 rΓ2 h2 ->
  r1 = r2 /\ rΓ1 = rΓ2 /\ h1 = h2.
Proof.
  intros CT n rΓ h s r1 rΓ1 h1 r2 rΓ2 h2 Hct H1 H2.
  apply (run_complete _ _ _ _ _ _ _ _ Hct) in H1.
  apply (run_complete _ _ _ _ _ _ _ _ Hct) in H2.
  rewrite H1 in H2. inversion H2. auto.
Qed.

(** PROGRESS for the interpreter.  On a well-typed statement in a well-formed
    state, with any budget, the interpreter returns an outcome, and the
    outcome is a normal finish, a null dereference, or a timeout.  It is
    never stuck and never returns a rejected write. *)
Theorem run_progress : forall n CT Δ sΓ mt rΓ h s sΓ',
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt s sΓ' ->
  exists r rΓ' h',
    run CT n rΓ h s = Some (r, rΓ', h') /\
    (r = FDone OK \/ r = FDone NPE \/ r = FTimeout).
Proof.
  intros n CT Δ sΓ mt rΓ h s sΓ' Hwf Htype.
  destruct (progress n CT Δ sΓ mt rΓ h s sΓ' Hwf Htype) as (r & rΓ' & h' & Hev & Hr).
  exists r, rΓ', h'. split; [|exact Hr].
  apply run_complete; [exact (proj1 Hwf) | exact Hev].
Qed.

(** A normal finish of the interpreter leaves a well-formed state. *)
Corollary run_preservation : forall CT Δ sΓ mt rΓ h s sΓ' n rΓ' h',
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt s sΓ' ->
  run CT n rΓ h s = Some (FDone OK, rΓ', h') ->
  wf_r_config CT Δ sΓ' rΓ' h'.
Proof.
  intros CT Δ sΓ mt rΓ h s sΓ' n rΓ' h' Hwf Htype H.
  eapply fuel_preservation; eauto. apply run_sound. exact H.
Qed.

Print Assumptions run_agrees.
Print Assumptions run_progress.
Print Assumptions eval_fuel_deterministic.
