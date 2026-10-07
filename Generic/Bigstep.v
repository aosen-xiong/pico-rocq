From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require String.
Require Import Stdlib.Classes.RelationClasses.
Import ListNotations.

Require Import Syntax Typing Subtyping ViewpointAdaptation Helpers.

(* ------------------RUNTIME HELPER FUNCTIONS------------------*)
(* The first element should also be a Loc because that is the receiver type*)
Definition get_this_var_mapping (vm : var_mapping) : option Loc :=
  match vm with
  | [] => None
  | ι :: _ =>
    match ι with
    | Null_a => None
    | Iot loc => Some loc
    end
  end.

(* Get the runtime mutability type of a Loc *)
Definition r_muttype (h: heap) (ι: Loc) : option q_r :=
  match runtime_getObj h ι with
  | None => None
  | Some o => Some (rqtype (rt_type o))
  end.

(* Get the runtime class name of a Loc *)
Definition r_basetype (h: heap) (ι: Loc) : option class_name :=
  match runtime_getObj h ι with
  | None => None
  | Some o => Some (rctype (rt_type o))
  end.

(* Get the runtime type of a Loc *)
Definition r_type (h: heap) (ι: Loc) : option runtime_type :=
  match runtime_getObj h ι with
  | None => None
  | Some o => Some (rt_type o)
  end.

Definition update_field (h: heap) (ι: Loc) (f: var) (v: value) : heap :=
  match runtime_getObj h ι with
  | None => h
  | Some o =>
      let new_fields := update f v o.(fields_map) in
      let new_obj := (set_fields_map o (new_fields))
      in update ι new_obj h
  end.

Lemma update_field_length : forall h ι f v,
  dom (update_field h ι f v) = dom h.
Proof.
  intros.
  unfold update_field.
  destruct (runtime_getObj h ι); [apply update_length | reflexivity].
Qed.

Definition vpa_mutability_runtime_bound_agree (q1: q_r)(q2 : q_c) : bool :=
  match (q1, q2) with
    | (Imm_r, RDM_c) => true
    | (Mut_r, RDM_c) => true
    | (Imm_r, Imm_c) => true
    | (Mut_r, Mut_c) => true
    | (_, _) => false
    end.

(* ------------------RUNTIME WELLFORMEDNESS RULES------------------*)

(** Runtime type arguments [Rs] satisfy the declared bounds [Bs], with the
    bounds resolved through [qctx] and the arguments [ca], [ma]. *)
Definition rbounds_ok (CT : class_table) (qctx : q) (ca ma : list rtype)
    (Rs : list rtype) (Bs : list qualified_type) : Prop :=
  Forall2 (fun R B => rtype_subtype CT R (dyn qctx ca ma B)) Rs Bs.

(** Well-formed runtime object type: the mutability agrees with the class
    declaration, and the stored type arguments are fully known and satisfy
    the class's bounds. *)
Definition wf_rtypeuse (CT: class_table) (rt : runtime_type) : Prop :=
  match find_class CT (rctype rt) with
  | None => False
  | Some def =>
      vpa_mutability_runtime_bound_agree (rqtype rt)
        (class_qualifier (signature def)) /\
      Forall rlost_free (rtargs rt) /\
      rbounds_ok CT (qr2q (rqtype rt)) (rtargs rt) [] (rtargs rt)
        (ctparams (signature def))
  end.

(** An object's concrete mutability may be seen through this runtime head. *)
Definition head_ok (qo : q_r) (rq : q) : Prop :=
  rq = RO \/ rq = Lost \/ rq = qr2q qo.

(** The object at [ι] inhabits runtime type [R]: its mutability may be seen
    through [R]'s head, and its own type arguments, viewed at [R]'s class,
    agree with [R]'s arguments up to forgotten positions. *)
Definition loc_has_rtype (CT : class_table) (h : heap) (ι : Loc) (R : rtype) : Prop :=
  match runtime_getObj h ι, R with
  | Some o, RClass rq D Us =>
      head_ok (rqtype (rt_type o)) rq /\
      exists Vs,
        rsuper_inst CT (qr2q (rqtype (rt_type o)))
          (rctype (rt_type o)) (rtargs (rt_type o)) D Vs /\
        Forall2 rarg_sub Vs Us
  | None, _ => False
  end.

(** The object at [ι] inhabits static type [T], read in an activation whose
    receiver has mutability [qcontext] and whose runtime class and method type
    arguments are [ca] and [ma]. *)
Definition wf_r_typable (CT: class_table) (h: heap) (ι: Loc)
    (T: qualified_type) (qcontext: q_r) (ca ma : list rtype) : Prop :=
  loc_has_rtype CT h ι (dyn (qr2q qcontext) ca ma T).

(* Wellformed Runtime Object: an object is well-formed if itself and its fields' type are well formed *)
Definition wf_obj (CT: class_table) (h: heap) (ι: Loc) : Prop :=
  match runtime_getObj h ι with
  | None => False
  | Some o =>
      (* The runtime type of the object is well-formed *)
      wf_rtypeuse CT (rt_type o) /\
      (* All field values are well-formed and have correct types *)
      exists field_defs, CollectFields CT (rt_type o).(rctype) field_defs /\
      List.length (fields_map o) = List.length field_defs /\
      Forall2 (fun v fdef =>
        match v with
        | Null_a => True
        | Iot loc =>
            wf_r_typable CT h loc (ftype fdef)
              (rqtype (rt_type o)) (rtargs (rt_type o)) []
        end) (fields_map o) field_defs
  end.

Definition wf_renv (CT: class_table) (rΓ: r_env) (h: heap) : Prop :=
  (* The first variable is the receiver and should always be present as non-null value *)
  dom rΓ.(vars) > 0 /\
  (exists iot, get_this_var_mapping rΓ.(vars) = Some iot /\ iot < dom h) /\
  Forall (fun value =>
    match value with
    | Null_a => True
    | Iot loc =>
        match runtime_getObj h loc with
        | None => False
        | Some _ => True
        end
    end) rΓ.(vars).

(* Wellformed Runtime Heap: a heap is well-formed if all objects in it are well-formed *)
Definition wf_heap (CT: class_table) (h: heap) : Prop :=
    forall (ι : Loc),
    ι < (List.length h) ->
    wf_obj CT h ι.

(** The activation's runtime type arguments fit the static bound environment
    [Δ] of the code it runs.  [Cthis] is the class whose type parameters [Δ]
    lists: the receiver object, viewed at [Cthis], has exactly the class
    arguments recorded in the environment, and both argument lists are fully
    known and satisfy their bounds. *)
Definition wf_frame_targs (CT : class_table) (Δ : tv_env) (rΓ : r_env) (h : heap)
    : Prop :=
  exists ι o Cthis,
    get_this_var_mapping (vars rΓ) = Some ι /\
    runtime_getObj h ι = Some o /\
    class_bounds Δ = class_tparams CT Cthis /\
    rsuper_inst CT (qr2q (rqtype (rt_type o)))
      (rctype (rt_type o)) (rtargs (rt_type o)) Cthis (cargs rΓ) /\
    Forall rlost_free (cargs rΓ) /\
    Forall rlost_free (margs rΓ) /\
    rbounds_ok CT (qr2q (rqtype (rt_type o))) (cargs rΓ) (margs rΓ)
      (cargs rΓ) (class_bounds Δ) /\
    rbounds_ok CT (qr2q (rqtype (rt_type o))) (cargs rΓ) (margs rΓ)
      (margs rΓ) (method_bounds Δ).

(** A runtime configuration is well formed when its class table, heap, and
    environments are well formed and the static and runtime environments
    correspond pointwise. *)
Definition wf_r_config (CT: class_table) (Δ : tv_env) (sΓ: s_env) (rΓ: r_env) (h: heap) : Prop :=
  (* CT is well-formed *)
  wf_class_table CT /\
  (* Heap is well-formed *)
  wf_heap CT h /\
  (* Runtime environment is well-formed *)
  wf_renv CT rΓ h /\
  (* Static environment is well-formed *)
  wf_senv CT Δ sΓ /\
  (* The activation's runtime type arguments fit the bound environment *)
  wf_frame_targs CT Δ rΓ h /\
  (* Static and runtime environment correspond *)
  List.length sΓ = List.length rΓ.(vars) /\
  forall ι qcontext,
  get_this_var_mapping (vars rΓ) = Some ι ->
  (r_muttype h ι) = Some qcontext ->
  forall i, i < List.length sΓ ->
  forall sqt,
    nth_error sΓ i = Some sqt ->
    match runtime_getVal rΓ i with
    | Some (Iot loc) =>
        wf_r_typable CT h loc sqt qcontext (cargs rΓ) (margs rΓ)
    | Some Null_a => True
    | None => False
    end.

(* ------------------EVALUATION RULES------------------*)

(* Evaluation resulting state *)
Inductive eval_result :=
| OK : eval_result
| MUTATIONEXP: eval_result
| NPE : eval_result.

Definition runtime_vpa_assignability (q1: q_r) (a1: a) : a :=
  match q1, a1 with
    | _, Assignable => Assignable
    | Mut_r, RDA => Assignable
    | _, _ => Final
  end.

(* PICO expression evaluation *)
Inductive eval_expr : class_table -> r_env -> heap -> expr -> value -> eval_result -> r_env -> heap -> Prop :=
  (* evalutate null expression  *)
  | EBS_Null : forall CT rΓ h,
      eval_expr CT rΓ h ENull Null_a OK rΓ h

  (* evaluate value expression *)
  | EBS_Val : forall CT rΓ h x v
      (Hval : runtime_getVal rΓ x = Some v),
      eval_expr CT rΓ h (EVar x) v OK rΓ h

  (* evaluate field access expression *)
  | EBS_Field : forall CT rΓ h x f v o v1
      (Hval   : runtime_getVal rΓ x = Some (Iot v))
      (Hobj   : runtime_getObj h v = Some o)
      (Hfield : getVal o.(fields_map) f = Some v1),
      eval_expr CT rΓ h (EField x f) v1 OK rΓ h

  (* evaluate field access expression yields NPE *)
  | EBS_Field_NPE : forall CT rΓ h x f
      (Hnull : runtime_getVal rΓ x = Some (Null_a)),
      eval_expr CT rΓ h (EField x f) Null_a NPE rΓ h
  .

Lemma eval_expr_deterministic :
  forall CT rΓ h e v1 r1 rΓ1' h1' v2 r2 rΓ2' h2',
    eval_expr CT rΓ h e v1 r1 rΓ1' h1' ->
    eval_expr CT rΓ h e v2 r2 rΓ2' h2' ->
    v1 = v2 /\ r1 = r2 /\ rΓ1' = rΓ2' /\ h1' = h2'.
Proof.
  intros CT rΓ h e v1 r1 rΓ1' h1' v2 r2 rΓ2' h2' H1 H2.
  inversion H1; subst; inversion H2; subst.
  - repeat split; reflexivity.
  - rewrite Hval0 in Hval; injection Hval as ?; subst.
    repeat split; reflexivity.
  - rewrite Hval0 in Hval; injection Hval as ?; subst.
    rewrite Hobj0 in Hobj; injection Hobj as ?; subst.
    rewrite Hfield0 in Hfield; injection Hfield as ?; subst.
    repeat split; reflexivity.
  - rewrite Hnull in Hval; discriminate.
  - rewrite Hnull in Hval; discriminate.
  - repeat split; reflexivity.
Qed.

(** The environment of a callee activation.  [ly] is the receiver object, [D]
    the class declaring the selected method.  The class arguments are the
    receiver's own arguments viewed at [D]; the method arguments are the
    written ones, resolved in the caller's activation. *)
Definition callee_env (CT : class_table) (rΓ : r_env) (h : heap)
    (ly : Loc) (D : class_name) (Us : list qualified_type) (vals : list value)
    (rΓ' : r_env) : Prop :=
  exists lthis qthis oy cargs',
    runtime_getVal rΓ 0 = Some (Iot lthis) /\
    r_muttype h lthis = Some qthis /\
    runtime_getObj h ly = Some oy /\
    rsuper_inst CT (qr2q (rqtype (rt_type oy)))
      (rctype (rt_type oy)) (rtargs (rt_type oy)) D cargs' /\
    rΓ' = mkr_env (Iot ly :: vals) cargs'
            (map (dyn (qr2q qthis) (cargs rΓ) (margs rΓ)) Us).

(* PICO Statement evaluation *)
Inductive eval_stmt : class_table -> r_env -> heap -> stmt -> eval_result -> r_env -> heap -> Prop :=
  (* evaluate skip statement *)
  | SBS_Skip : forall CT rΓ h,
      eval_stmt CT rΓ h SSkip OK rΓ h

  (* evaluate local variable declaration statement *)
  | SBS_Local : forall CT rΓ h T x
      (Hnone : runtime_getVal rΓ x = None),
      eval_stmt CT rΓ h (SLocal T x) OK
      (set_vars rΓ (rΓ.(vars)++[Null_a]) )
      h

  (* evaluate variable assignment statement *)
  | SBS_Assign : forall CT rΓ h x e v1 v2
      (Hval   : runtime_getVal rΓ x = Some v1)
      (Heval  : eval_expr CT rΓ h e v2 OK rΓ h),
      eval_stmt CT rΓ h (SVarAss x e) OK
      (set_vars rΓ (update x v2 rΓ.(vars)))
      h

  | SBS_Assign_NPE : forall CT rΓ h x e v1 v2
      (Hval   : runtime_getVal rΓ x = Some v1)
      (Heval  : eval_expr CT rΓ h e v2 NPE rΓ h),
      eval_stmt CT rΓ h (SVarAss x e) NPE
      rΓ
      h

  (* evaluate field write statement *)
  | SBS_FldWrite : forall CT rΓ h x f y loc_x o a vf val_y h'
      (Hval_x  : runtime_getVal rΓ x = Some (Iot loc_x))
      (Hobj    : runtime_getObj h loc_x = Some o)
      (Hfield  : getVal o.(fields_map) f = Some vf)
      (Hassign : sf_assignability_rel CT (rctype (rt_type o)) f a)
      (Hval_y  : runtime_getVal rΓ y = Some val_y)
      (Hruntime_assignable : runtime_vpa_assignability (rqtype (rt_type o)) a = Assignable)
      (Hupdate : h' = update_field h loc_x f val_y),
      eval_stmt CT rΓ h (SFldWrite x f y) OK rΓ h'

  (* evaluate field write statement NPE *)
  | SBS_FldWrite_NPE : forall CT rΓ h x f y
      (Hnull : runtime_getVal rΓ x = Some (Null_a)),
      eval_stmt CT rΓ h (SFldWrite x f y) NPE rΓ h

  | SBS_FldWrite_MUTATIONEXP : forall CT rΓ h x f y loc_x o a vf val_y
      (Hval_x  : runtime_getVal rΓ x = Some (Iot loc_x))
      (Hobj    : runtime_getObj h loc_x = Some o)
      (Hfield  : getVal o.(fields_map) f = Some vf)
      (Hassign : sf_assignability_rel CT (rctype (rt_type o)) f a)
      (Hval_y  : runtime_getVal rΓ y = Some val_y)
      (Hfinal  : runtime_vpa_assignability (rqtype (rt_type o)) a = Final),
      eval_stmt CT rΓ h (SFldWrite x f y) MUTATIONEXP rΓ h

  (* evaluate object creation statement: the written type arguments are
     resolved in the current activation and stored in the new object *)
  | SBS_New : forall CT rΓ h x (q_c:q_c) c Ts ys l1 qthisr vals o qadapted rΓ' h'
      (Hthis    : runtime_getVal rΓ 0 = Some (Iot l1))
      (Hargs    : runtime_lookup_list rΓ ys = Some vals)
      (Hmut     : r_muttype h l1 = Some qthisr)
      (Hadapt   : vpa_mutability_object_creation qthisr q_c = qadapted)
      (Hobj     : o = mkObj
                        (mkruntime_type qadapted c
                           (map (dyn (qr2q qthisr) (cargs rΓ) (margs rΓ)) Ts))
                        vals)
      (Hheap    : h' = h++[o])
      (Henv     : rΓ' = (set_vars rΓ (update x (Iot (dom h)) rΓ.(vars)))),
      eval_stmt CT rΓ h (SNew x q_c c Ts ys) OK rΓ' h'

  (* evaluate method call statement *)
  | SBS_Call : forall CT rΓ h x y m Us zs vals ly cy D mdef mstmt mret retval h' rΓ' rΓ'' rΓ'''
      (Hval_y      : runtime_getVal rΓ y = Some (Iot ly))
      (Hbase       : r_basetype h ly = Some cy)
      (Hfind       : FindMethodWithName CT cy m D mdef)
      (Hstmt       : mstmt = (mbody mdef).(mbody_stmt))
      (Hret        : mret = (mbody mdef).(mreturn))
      (Hargs       : runtime_lookup_list rΓ zs = Some vals)
      (Hframe      : callee_env CT rΓ h ly D Us vals rΓ')
      (Heval_body  : eval_stmt CT rΓ' h mstmt OK rΓ'' h')
      (Hretval     : runtime_getVal rΓ'' mret = Some retval)
      (Henv        : rΓ''' = (set_vars rΓ (update x retval rΓ.(vars)))),
      eval_stmt CT rΓ h (SCall x m y Us zs) OK rΓ''' h'

  (* evaluate method call statement NPE *)
  | SBS_Call_NPE : forall CT rΓ h x y m Us zs
      (Hnull : runtime_getVal rΓ y = Some (Null_a)),
      eval_stmt CT rΓ h (SCall x m y Us zs) NPE rΓ h

  | SBS_Call_NPE_Body : forall CT rΓ h x y m Us zs vals ly cy D mdef mstmt h' rΓ' rΓ''
      (Hval_y     : runtime_getVal rΓ y = Some (Iot ly))
      (Hbase      : r_basetype h ly = Some cy)
      (Hfind      : FindMethodWithName CT cy m D mdef)
      (Hstmt      : mstmt = (mbody mdef).(mbody_stmt))
      (Hargs      : runtime_lookup_list rΓ zs = Some vals)
      (Hframe     : callee_env CT rΓ h ly D Us vals rΓ')
      (Heval_body : eval_stmt CT rΓ' h mstmt NPE rΓ'' h'),
      eval_stmt CT rΓ h (SCall x m y Us zs) NPE rΓ'' h'

  | SBS_Call_MUTATIONEXP_Body : forall CT rΓ h x y m Us zs vals ly cy D mdef mstmt h' rΓ' rΓ''
      (Hval_y     : runtime_getVal rΓ y = Some (Iot ly))
      (Hbase      : r_basetype h ly = Some cy)
      (Hfind      : FindMethodWithName CT cy m D mdef)
      (Hstmt      : mstmt = (mbody mdef).(mbody_stmt))
      (Hargs      : runtime_lookup_list rΓ zs = Some vals)
      (Hframe     : callee_env CT rΓ h ly D Us vals rΓ')
      (Heval_body : eval_stmt CT rΓ' h mstmt MUTATIONEXP rΓ'' h'),
      eval_stmt CT rΓ h (SCall x m y Us zs) MUTATIONEXP rΓ'' h'

  (* evaluate cast statement: the value is copied unchanged and the cast
     never fails; the type system admits only casts for which this is right *)
  | SBS_Cast : forall CT rΓ h x T y v1 v2
      (Hval_x : runtime_getVal rΓ x = Some v1)
      (Hval_y : runtime_getVal rΓ y = Some v2),
      eval_stmt CT rΓ h (SCast x T y) OK
      (set_vars rΓ (update x v2 rΓ.(vars)))
      h

  (* evaluate sequence of statements *)
  | SBS_Seq : forall CT rΓ h s1 s2 rΓ' h' rΓ'' h''
      (Heval1 : eval_stmt CT rΓ h s1 OK rΓ' h')
      (Heval2 : eval_stmt CT rΓ' h' s2 OK rΓ'' h''),
      eval_stmt CT rΓ h (SSeq s1 s2) OK rΓ'' h''

  | SBS_Seq_NPE_first : forall CT rΓ h s1 s2 rΓ' h'
      (Heval1 : eval_stmt CT rΓ h s1 NPE rΓ' h'),
      eval_stmt CT rΓ h (SSeq s1 s2) NPE rΓ' h'

  | SBS_Seq_NPE_second : forall CT rΓ h s1 s2 rΓ' h' rΓ'' h''
      (Heval1 : eval_stmt CT rΓ h s1 OK rΓ' h')
      (Heval2 : eval_stmt CT rΓ' h' s2 NPE rΓ'' h''),
      eval_stmt CT rΓ h (SSeq s1 s2) NPE rΓ'' h''

  | SBS_Seq_MUTATIONEXP_first : forall CT rΓ h s1 s2 rΓ' h'
      (Heval1 : eval_stmt CT rΓ h s1 MUTATIONEXP rΓ' h'),
      eval_stmt CT rΓ h (SSeq s1 s2) MUTATIONEXP rΓ' h'

  | SBS_Seq_MUTATIONEXP_second : forall CT rΓ h s1 s2 rΓ' h' rΓ'' h''
      (Heval1 : eval_stmt CT rΓ h s1 OK rΓ' h')
      (Heval2 : eval_stmt CT rΓ' h' s2 MUTATIONEXP rΓ'' h''),
      eval_stmt CT rΓ h (SSeq s1 s2) MUTATIONEXP rΓ'' h''
  .
