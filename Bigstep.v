From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require String.
From RecordUpdate Require Import RecordUpdate.
Require Import Stdlib.Sets.Ensembles.
Require Import Stdlib.Logic.Classical_Prop.
Require Import Stdlib.Classes.RelationClasses.
Import ListNotations.

Require Import Syntax Typing Subtyping ViewpointAdaptation Helpers Reachability.

(* ------------------RUNTIME H ELPER FUNCTION------------------*)
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

Lemma get_this_var_mapping_app_null_last : forall vs,
  get_this_var_mapping (vs ++ [Null_a]) = get_this_var_mapping vs.
Proof.
  intros vs. destruct vs; reflexivity.
Qed.

Lemma get_this_var_mapping_update_vars_app_null : forall rΓ,
  get_this_var_mapping (vars (rΓ <| vars := vars rΓ ++ [Null_a] |>))
  = get_this_var_mapping (vars rΓ).
Proof.
  intro rΓ. simpl. apply get_this_var_mapping_app_null_last.
Qed.

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
      let new_obj := o <| fields_map := new_fields |>
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
(* Wellformed Runtime Type use  *)
Definition wf_rtypeuse (CT: class_table) (q: q_r) (c: class_name) : Prop :=
  match (bound CT c) with
  | None => False
  | Some q' => c < dom CT /\ vpa_mutability_runtime_bound_agree q q'
  end.

Definition qualifier_typable_context (qr: q_r) (qs: q) (qcontext: q_r): Prop :=
  match qr with
  | Imm_r =>
    match vpa_mutability_rs qcontext qs with
    | Imm => True
    | RO => True
    | Lost => True
    | _ => False
    end
  | Mut_r =>
    match vpa_mutability_rs qcontext qs with
    | Mut => True
    | RO => True
    | Lost => True
    | _ => False
    end
  end.

(* heap typable is different than environment typable; I sepearate it in the proof but uses the same in the written up *)
Definition qualifier_typable_heap (qr: q_r) (qs: q): Prop :=
  match qr with
  | Imm_r =>
    match qs with 
    | Imm => True
    | RO => True
    | _ => False
    end
  | Mut_r =>
    match qs with
    | Mut => True
    | RO => True
    | _ => False
    end
  end.

(* Wellformed Runtime Object: an object is well-formed if itself and its fields' type are well formed *)
Definition wf_obj (CT: class_table) (h: heap) (ι: Loc) : Prop :=
  match runtime_getObj h ι with
  | None => False
  | Some o =>
      (* The runtime type of the object is well-formed *)
      wf_rtypeuse CT (rt_type o).(rqtype) (rt_type o).(rctype) /\
      (* All field values are well-formed and have correct types *)
      exists field_defs, CollectFields CT (rt_type o).(rctype) field_defs /\
      List.length (fields_map o) = List.length field_defs /\
      Forall2 (fun v fdef => 
        match v with
        | Null_a => True
        | Iot loc => 
          match runtime_getObj h loc with
          | Some _ => 
            (* Field value exists and has correct type *)
            exists rqt, r_type h loc = Some rqt /\
            base_subtype CT (rctype rqt) (f_base_type (ftype fdef)) /\
            qualifier_typable_heap (rqtype rqt) (vpa_mutability_rec_fld (rqtype (rt_type o)) (mutability (ftype fdef)))
          | None => False
          end
        end) (fields_map o) field_defs
  end.

(* Wellformed Runtime environment: a rΓ is well formed if for all variable in its domain, it maps to null_a or a value in the domin of heap *)
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

Definition wf_r_typable (CT: class_table) (rΓ: r_env) (h: heap) (ι: Loc) (sqt: qualified_type) (qcontext: q_r) : Prop :=
  match r_type h ι with
  | Some rqt =>
      base_subtype CT (rctype rqt) (sctype sqt) /\ 
      qualifier_typable_context (rqtype rqt) (sqtype sqt) qcontext
  | _ => False
  end.

Lemma wf_r_typable_env_independent_simple : forall CT rΓ1 rΓ2 h loc sqt qcontext
  (Hwf : wf_r_typable CT rΓ1 h loc sqt qcontext),
  wf_r_typable CT rΓ2 h loc sqt qcontext.
Proof.
  intros CT rΓ1 rΓ2 h loc sqt qcontext Hwf.
  exact Hwf.
Qed.

(* Wellformed Runtime Config: if (1) heap is well formed (2) static env is well formed (3) runtime env is well formed (4) the static env and run time env corresponds  *)
Definition wf_r_config (CT: class_table) (sΓ: s_env) (rΓ: r_env) (h: heap) : Prop :=
  (* CT is well-formed *)
  wf_class_table CT /\
  (* Heap is well-formed *)
  wf_heap CT h /\
  (* Runtime environment is well-formed *)
  wf_renv CT rΓ h /\
  (* Static environment is well-formed *)
  wf_senv CT sΓ /\
  (* Static and runtime environment correspond *)
  List.length sΓ = List.length rΓ.(vars) /\
  forall ι qcontext,
  get_this_var_mapping (vars rΓ) = Some ι ->
  (r_muttype h ι) = Some qcontext ->
  forall i, i < List.length sΓ ->
  forall sqt,
    (* TODO: unify the method used to static_get_type *)
    nth_error sΓ i = Some sqt ->
    match runtime_getVal rΓ i with
    | Some (Iot loc) => wf_r_typable CT rΓ h loc sqt qcontext
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

Definition reachable_locations_from_initial_env
  (CT : class_table) (h : heap) (rΓ : r_env) : Ensembles.Ensemble Loc :=
  fun l_target => 
    exists x l_root ,
      runtime_getVal rΓ x = Some (Iot l_root) /\
      reachable h l_root l_target.

(* PICO expression evaluation *)
Inductive eval_expr : eval_result -> (Loc -> Prop) -> class_table -> r_env -> heap -> expr -> value -> eval_result -> (Loc -> Prop)  -> r_env -> heap -> Prop :=
  (* evalutate null expression  *)
  | EBS_Null : forall CT rΓ h,
      eval_expr OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h ENull Null_a OK (reachable_locations_from_initial_env CT h rΓ) rΓ h

  (* evaluate value expression *)
  | EBS_Val : forall CT rΓ h x v
      (Hval : runtime_getVal rΓ x = Some v),
      eval_expr OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h (EVar x) v OK (reachable_locations_from_initial_env CT h rΓ) rΓ h

  (* evaluate field access expression *)
  | EBS_Field : forall CT rΓ h x f v o v1
      (Hval   : runtime_getVal rΓ x = Some (Iot v))
      (Hobj   : runtime_getObj h v = Some o)
      (Hfield : getVal o.(fields_map) f = Some v1),
      eval_expr OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h (EField x f) v1 OK (reachable_locations_from_initial_env CT h rΓ) rΓ h

  (* evaluate field access expression yields NPE *)
  | EBS_Field_NPE : forall CT rΓ h x f
      (Hnull : runtime_getVal rΓ x = Some (Null_a)),
      eval_expr OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h (EField x f) Null_a NPE (reachable_locations_from_initial_env CT h rΓ) rΓ h
  .
Notation "rΓ ',' h '⟦' e '⟧' '-->' v ',' rΓ' ',' h'" := (eval_expr OK rΓ h e v OK rΓ' h') (at level 200).

(* Determinism of eval_expr.

   Every well-formed expression evaluation from a given starting state
   produces the same result value, outcome tag, reach set, environment,
   and heap. *)
Lemma eval_expr_deterministic :
  forall CT rΓ h e v1 r1 reach1' rΓ1' h1' v2 r2 reach2' rΓ2' h2',
    eval_expr OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h e v1
              r1 reach1' rΓ1' h1' ->
    eval_expr OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h e v2
              r2 reach2' rΓ2' h2' ->
    v1 = v2 /\ r1 = r2 /\ reach1' = reach2' /\ rΓ1' = rΓ2' /\ h1' = h2'.
Proof.
  intros CT rΓ h e v1 r1 reach1' rΓ1' h1' v2 r2 reach2' rΓ2' h2' H1 H2.
  inversion H1; subst; inversion H2; subst.
  - (* EBS_Null vs EBS_Null *)
    repeat split; reflexivity.
  - (* EBS_Val vs EBS_Val *)
    rewrite Hval0 in Hval; injection Hval as ?; subst.
    repeat split; reflexivity.
  - (* EBS_Field vs EBS_Field *)
    rewrite Hval0 in Hval; injection Hval as ?; subst.
    rewrite Hobj0 in Hobj; injection Hobj as ?; subst.
    rewrite Hfield0 in Hfield; injection Hfield as ?; subst.
    repeat split; reflexivity.
  - (* EBS_Field vs EBS_Field_NPE: Iot vs Null contradiction *)
    rewrite Hnull in Hval; discriminate.
  - (* EBS_Field_NPE vs EBS_Field: Null vs Iot contradiction *)
    rewrite Hnull in Hval; discriminate.
  - (* EBS_Field_NPE vs EBS_Field_NPE *)
    repeat split; reflexivity.
Qed.

(* PICO Statement evaluation *)
Inductive eval_stmt : eval_result -> (Loc -> Prop)  -> class_table -> r_env -> heap -> stmt -> eval_result -> (Loc -> Prop)  -> r_env -> heap -> Prop :=
  (* evaluate skip statement *)
  | SBS_Skip : forall CT rΓ h,
      eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h SSkip OK (reachable_locations_from_initial_env CT h rΓ) rΓ h

  (* evaluate local variable declaration statement *)
  | SBS_Local : forall CT rΓ h T x
      (Hnone : runtime_getVal rΓ x = None),
      eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h (SLocal T x) OK (reachable_locations_from_initial_env CT h rΓ)
      (rΓ <|vars := rΓ.(vars)++[Null_a] |> )
      h

  (* evaluate variable assignment statement *)
  | SBS_Assign : forall CT rΓ h x e v1 v2
      (Hval   : runtime_getVal rΓ x = Some v1)
      (Heval  : eval_expr OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h e v2 OK (reachable_locations_from_initial_env CT h rΓ) rΓ h),
      eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h (SVarAss x e) OK (reachable_locations_from_initial_env CT h rΓ)
      (rΓ <|vars := update x v2 rΓ.(vars)|>)
      h

  | SBS_Assign_NPE : forall CT rΓ h x e v1 v2
      (Hval   : runtime_getVal rΓ x = Some v1)
      (Heval  : eval_expr OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h e v2 NPE (reachable_locations_from_initial_env CT h rΓ) rΓ h),
      eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h (SVarAss x e) NPE (reachable_locations_from_initial_env CT h rΓ)
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
      eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h (SFldWrite x f y) OK (reachable_locations_from_initial_env CT h rΓ) rΓ h'

  (* evaluate field write statement NPE *)
  | SBS_FldWrite_NPE : forall CT rΓ h x f y
      (Hnull : runtime_getVal rΓ x = Some (Null_a)),
      eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h (SFldWrite x f y) NPE (reachable_locations_from_initial_env CT h rΓ) rΓ h

  | SBS_FldWrite_MUTATIONEXP : forall CT rΓ h x f y loc_x o a vf val_y
      (Hval_x  : runtime_getVal rΓ x = Some (Iot loc_x))
      (Hobj    : runtime_getObj h loc_x = Some o)
      (Hfield  : getVal o.(fields_map) f = Some vf)
      (Hassign : sf_assignability_rel CT (rctype (rt_type o)) f a)
      (Hval_y  : runtime_getVal rΓ y = Some val_y)
      (Hfinal  : runtime_vpa_assignability (rqtype (rt_type o)) a = Final),
      eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h (SFldWrite x f y) MUTATIONEXP (reachable_locations_from_initial_env CT h rΓ) rΓ h

  (* evaluate object creation statement *)
  | SBS_New : forall CT rΓ h x (q_c:q_c) c ys l1 qthisr vals o qadapted rΓ' h'
      (Hthis    : runtime_getVal rΓ 0 = Some (Iot l1))
      (Hargs    : runtime_lookup_list rΓ ys = Some vals)
      (Hmut     : r_muttype h l1 = Some qthisr)
      (Hadapt   : vpa_mutability_object_creation qthisr q_c = qadapted)
      (Hobj     : o = mkObj (mkruntime_type qadapted c) (vals))
      (Hheap    : h' = h++[o])
      (Henv     : rΓ' = rΓ <| vars := update x (Iot (dom h)) rΓ.(vars) |>),
      eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h (SNew x q_c c ys) OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h'

  (* evaluate method call statement *)
  | SBS_Call : forall CT rΓ h x y m zs vals ly cy mdef mbody mstmt mret retval h' rΓ' rΓ'' rΓ'''
      (Hval_y      : runtime_getVal rΓ y = Some (Iot ly))
      (Hbase       : r_basetype h ly = Some cy)
      (Hfind       : FindMethodWithName CT cy m mdef /\ mbody = Syntax.mbody mdef)
      (Hstmt       : mstmt = mbody.(mbody_stmt))
      (Hret        : mret = mbody.(mreturn))
      (Hargs       : runtime_lookup_list rΓ zs = Some vals)
      (Hframe      : rΓ' = mkr_env (Iot ly :: vals))
      (Heval_body  : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ') CT rΓ' h mstmt OK (reachable_locations_from_initial_env CT h rΓ') rΓ'' h')
      (Hretval     : runtime_getVal rΓ'' mret = Some retval)
      (Henv        : rΓ''' = rΓ <| vars := update x retval rΓ.(vars) |>),
      eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h (SCall x m y zs) OK (reachable_locations_from_initial_env CT h rΓ) rΓ''' h'

  (* evaluate method call statement NPE *)
  | SBS_Call_NPE : forall CT rΓ h x y m zs
      (Hnull : runtime_getVal rΓ y = Some (Null_a)),
      eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h (SCall x m y zs) NPE (reachable_locations_from_initial_env CT h rΓ) rΓ h

  | SBS_Call_NPE_Body : forall CT rΓ h x y m zs vals ly cy mdef mbody mstmt mret h' rΓ' rΓ''
      (Hval_y     : runtime_getVal rΓ y = Some (Iot ly))
      (Hbase      : r_basetype h ly = Some cy)
      (Hfind      : FindMethodWithName CT cy m mdef /\ mbody = Syntax.mbody mdef)
      (Hstmt      : mstmt = mbody.(mbody_stmt))
      (Hret       : mret = mbody.(mreturn))
      (Hargs      : runtime_lookup_list rΓ zs = Some vals)
      (Hframe     : rΓ' = mkr_env (Iot ly :: vals))
      (Heval_body : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ') CT rΓ' h mstmt NPE (reachable_locations_from_initial_env CT h rΓ') rΓ'' h'),
      eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h (SCall x m y zs) NPE (reachable_locations_from_initial_env CT h rΓ) rΓ'' h'
  (* evaluate sequence of statements *)
  | SBS_Seq : forall CT rΓ h s1 s2 rΓ' h' rΓ'' h''
      (Heval1 : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h s1 OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h')
      (Heval2 : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ' h' s2 OK (reachable_locations_from_initial_env CT h rΓ) rΓ'' h''),
      eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h (SSeq s1 s2) OK (reachable_locations_from_initial_env CT h rΓ) rΓ'' h''

  | SBS_Seq_NPE_first : forall CT rΓ h s1 s2 rΓ' h'
      (Heval1 : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h s1 NPE (reachable_locations_from_initial_env CT h rΓ) rΓ' h'),
      eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h (SSeq s1 s2) NPE (reachable_locations_from_initial_env CT h rΓ) rΓ' h'

  | SBS_Seq_NPE_second : forall CT rΓ h s1 s2 rΓ' h' rΓ'' h''
      (Heval1 : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h s1 OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h')
      (Heval2 : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ' h' s2 NPE (reachable_locations_from_initial_env CT h rΓ) rΓ'' h''),
      eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h (SSeq s1 s2) NPE (reachable_locations_from_initial_env CT h rΓ) rΓ'' h''
.

(* Determinism of eval_stmt.

   Every well-formed statement evaluation from a given starting state
   produces the same outcome tag, reach set, environment, and heap. *)
Lemma eval_stmt_deterministic :
  forall CT rΓ h s reach res1 reach1' rΓ1' h1' res2 reach2' rΓ2' h2',
    eval_stmt OK reach CT rΓ h s res1 reach1' rΓ1' h1' ->
    eval_stmt OK reach CT rΓ h s res2 reach2' rΓ2' h2' ->
    res1 = res2 /\ reach1' = reach2' /\ rΓ1' = rΓ2' /\ h1' = h2'.
Proof.
  intros CT rΓ h s reach res1 reach1' rΓ1' h1' res2 reach2' rΓ2' h2' H1.
  generalize dependent h2'.
  generalize dependent rΓ2'.
  generalize dependent reach2'.
  generalize dependent res2.
  induction H1; intros res2 reach2' rΓ2' h2' H2.
  - (* SBS_Skip *)
    inversion H2; subst.
    repeat split; reflexivity.
  - (* SBS_Local *)
    inversion H2; subst.
    repeat split; reflexivity.
  - (* SBS_Assign *)
    inversion H2; subst.
    + (* H2 : SBS_Assign *)
      pose proof (eval_expr_deterministic _ _ _ _ _ _ _ _ _ _ _ _ _ _ Heval Heval0)
        as Hdet.
      destruct Hdet as [Hveq _].
      subst.
      repeat split; reflexivity.
    + (* H2 : SBS_Assign_NPE — eval_expr OK vs NPE *)
      pose proof (eval_expr_deterministic _ _ _ _ _ _ _ _ _ _ _ _ _ _ Heval Heval0)
        as Hdet.
      destruct Hdet as [_ [Hreq _]].
      discriminate.
  - (* SBS_Assign_NPE *)
    inversion H2; subst.
    + (* H2 : SBS_Assign — eval_expr NPE vs OK *)
      pose proof (eval_expr_deterministic _ _ _ _ _ _ _ _ _ _ _ _ _ _ Heval Heval0)
        as Hdet.
      destruct Hdet as [_ [Hreq _]].
      discriminate.
    + (* H2 : SBS_Assign_NPE *)
      repeat split; reflexivity.
  - (* SBS_FldWrite *)
    inversion H2; subst.
    + (* H2 : SBS_FldWrite *)
      rewrite Hval_x0 in Hval_x; injection Hval_x as Hloc_eq; subst loc_x0.
      rewrite Hobj0 in Hobj; injection Hobj as Ho_eq; subst o0.
      rewrite Hval_y0 in Hval_y; injection Hval_y as Hval_y_eq; subst val_y0.
      pose proof (sf_assignability_deterministic_rel _ _ _ _ _ Hassign Hassign0) as Haeq.
      subst a0.
      repeat split; reflexivity.
    + (* H2 : SBS_FldWrite_NPE — Iot vs Null *)
      rewrite Hnull in Hval_x; discriminate.
    + (* H2 : SBS_FldWrite_MUTATIONEXP — same field, Assignable vs Final *)
      rewrite Hval_x0 in Hval_x; injection Hval_x as Hloc_eq; subst loc_x0.
      rewrite Hobj0 in Hobj; injection Hobj as Ho_eq; subst o0.
      pose proof (sf_assignability_deterministic_rel _ _ _ _ _ Hassign Hassign0) as Haeq.
      subst a0.
      rewrite Hruntime_assignable in Hfinal; discriminate.
  - (* SBS_FldWrite_NPE *)
    inversion H2; subst.
    + (* H2 : SBS_FldWrite — Null vs Iot *)
      rewrite Hval_x in Hnull; discriminate.
    + (* H2 : SBS_FldWrite_NPE *)
      repeat split; reflexivity.
    + (* H2 : SBS_FldWrite_MUTATIONEXP — Null vs Iot *)
      rewrite Hval_x in Hnull; discriminate.
  - (* SBS_FldWrite_MUTATIONEXP *)
    inversion H2; subst.
    + (* H2 : SBS_FldWrite — Final vs Assignable *)
      rewrite Hval_x0 in Hval_x; injection Hval_x as Hloc_eq; subst loc_x0.
      rewrite Hobj0 in Hobj; injection Hobj as Ho_eq; subst o0.
      pose proof (sf_assignability_deterministic_rel _ _ _ _ _ Hassign Hassign0) as Haeq.
      subst a0.
      rewrite Hfinal in Hruntime_assignable; discriminate.
    + (* H2 : SBS_FldWrite_NPE — Iot vs Null *)
      rewrite Hnull in Hval_x; discriminate.
    + (* H2 : SBS_FldWrite_MUTATIONEXP *)
      repeat split; reflexivity.
  - (* SBS_New *)
    inversion H2; subst.
    rewrite Hthis0 in Hthis; injection Hthis as Hl_eq; subst l0.
    rewrite Hargs0 in Hargs; injection Hargs as Hvals_eq; subst vals0.
    rewrite Hmut0 in Hmut; injection Hmut as Hqthisr_eq; subst qthisr0.
    repeat split; reflexivity.
  - (* SBS_Call *)
    inversion H2; subst.
    + (* H2 : SBS_Call *)
      rewrite Hval_y0 in Hval_y; injection Hval_y as Hly_eq; subst.
      rewrite Hbase0 in Hbase; injection Hbase as Hcy_eq; subst.
      destruct Hfind as [Hfmn1 Hmbody1].
      destruct Hfind0 as [Hfmn2 Hmbody2].
      pose proof (find_method_with_name_deterministic _ _ _ _ _ Hfmn1 Hfmn2) as Hmdef_eq.
      subst.
      rewrite Hargs0 in Hargs; injection Hargs as Hvals_eq; subst.
      destruct (IHeval_stmt _ _ _ _ Heval_body) as [_ [_ [Henv_eq Hheap_eq]]].
      subst.
      rewrite Hretval0 in Hretval; injection Hretval as Hretval_eq; subst.
      repeat split; reflexivity.
    + (* H2 : SBS_Call_NPE — Iot vs Null *)
      rewrite Hnull in Hval_y; discriminate.
    + (* H2 : SBS_Call_NPE_Body — IH: OK = NPE *)
      rewrite Hval_y0 in Hval_y; injection Hval_y as Hly_eq; subst.
      rewrite Hbase0 in Hbase; injection Hbase as Hcy_eq; subst.
      destruct Hfind as [Hfmn1 Hmbody1].
      destruct Hfind0 as [Hfmn2 Hmbody2].
      pose proof (find_method_with_name_deterministic _ _ _ _ _ Hfmn1 Hfmn2) as Hmdef_eq.
      subst.
      rewrite Hargs0 in Hargs; injection Hargs as Hvals_eq; subst.
      destruct (IHeval_stmt _ _ _ _ Heval_body) as [Hres_eq _].
      discriminate.
  - (* SBS_Call_NPE *)
    inversion H2; subst.
    + (* H2 : SBS_Call — Null vs Iot *)
      rewrite Hval_y in Hnull; discriminate.
    + (* H2 : SBS_Call_NPE *)
      repeat split; reflexivity.
    + (* H2 : SBS_Call_NPE_Body — Null vs Iot *)
      rewrite Hval_y in Hnull; discriminate.
  - (* SBS_Call_NPE_Body *)
    inversion H2; subst.
    + (* H2 : SBS_Call — IH: NPE = OK *)
      rewrite Hval_y0 in Hval_y; injection Hval_y as Hly_eq; subst.
      rewrite Hbase0 in Hbase; injection Hbase as Hcy_eq; subst.
      destruct Hfind as [Hfmn1 Hmbody1].
      destruct Hfind0 as [Hfmn2 Hmbody2].
      pose proof (find_method_with_name_deterministic _ _ _ _ _ Hfmn1 Hfmn2) as Hmdef_eq.
      subst.
      rewrite Hargs0 in Hargs; injection Hargs as Hvals_eq; subst.
      destruct (IHeval_stmt _ _ _ _ Heval_body) as [Hres_eq _].
      discriminate.
    + (* H2 : SBS_Call_NPE — Iot vs Null *)
      rewrite Hnull in Hval_y; discriminate.
    + (* H2 : SBS_Call_NPE_Body *)
      rewrite Hval_y0 in Hval_y; injection Hval_y as Hly_eq; subst.
      rewrite Hbase0 in Hbase; injection Hbase as Hcy_eq; subst.
      destruct Hfind as [Hfmn1 Hmbody1].
      destruct Hfind0 as [Hfmn2 Hmbody2].
      pose proof (find_method_with_name_deterministic _ _ _ _ _ Hfmn1 Hfmn2) as Hmdef_eq.
      subst.
      rewrite Hargs0 in Hargs; injection Hargs as Hvals_eq; subst.
      destruct (IHeval_stmt _ _ _ _ Heval_body) as [_ [_ [Henv_eq Hheap_eq]]].
      subst.
      repeat split; reflexivity.
  - (* SBS_Seq *)
    inversion H2; subst.
    + (* H2 : SBS_Seq *)
      destruct (IHeval_stmt1 _ _ _ _ Heval1) as [_ [_ [Hrenv1 Hh1]]].
      subst.
      exact (IHeval_stmt2 _ _ _ _ Heval2).
    + (* H2 : SBS_Seq_NPE_first — IH on s1: OK = NPE *)
      destruct (IHeval_stmt1 _ _ _ _ Heval1) as [Hres_eq _].
      discriminate.
    + (* H2 : SBS_Seq_NPE_second — IH on s2: OK = NPE *)
      destruct (IHeval_stmt1 _ _ _ _ Heval1) as [_ [_ [Hrenv1 Hh1]]].
      subst.
      destruct (IHeval_stmt2 _ _ _ _ Heval2) as [Hres_eq _].
      discriminate.
  - (* SBS_Seq_NPE_first *)
    inversion H2; subst.
    + (* H2 : SBS_Seq — IH on s1: NPE = OK *)
      destruct (IHeval_stmt _ _ _ _ Heval1) as [Hres_eq _].
      discriminate.
    + (* H2 : SBS_Seq_NPE_first *)
      exact (IHeval_stmt _ _ _ _ Heval1).
    + (* H2 : SBS_Seq_NPE_second — IH on s1: NPE = OK *)
      destruct (IHeval_stmt _ _ _ _ Heval1) as [Hres_eq _].
      discriminate.
  - (* SBS_Seq_NPE_second *)
    inversion H2; subst.
    + (* H2 : SBS_Seq — IH on s2: NPE = OK *)
      destruct (IHeval_stmt1 _ _ _ _ Heval1) as [_ [_ [Hrenv1 Hh1]]].
      subst.
      destruct (IHeval_stmt2 _ _ _ _ Heval2) as [Hres_eq _].
      discriminate.
    + (* H2 : SBS_Seq_NPE_first — IH on s1: OK = NPE *)
      destruct (IHeval_stmt1 _ _ _ _ Heval1) as [Hres_eq _].
      discriminate.
    + (* H2 : SBS_Seq_NPE_second *)
      destruct (IHeval_stmt1 _ _ _ _ Heval1) as [_ [_ [Hrenv1 Hh1]]].
      subst.
      exact (IHeval_stmt2 _ _ _ _ Heval2).
Qed.

Lemma r_type_dom : forall h loc rqt
  (Hrtype : r_type h loc = Some rqt),
  loc < dom h.
Proof.
  intros h loc rqt H.
  unfold r_type in H.
  destruct (runtime_getObj h loc) as [o|] eqn:Hobj.
  - (* Some case *)
    unfold runtime_getObj in Hobj.
    apply nth_error_Some.
    rewrite Hobj.
    discriminate.
  - (* None case *)
    simpl in H.
    discriminate H.
Qed.

Lemma qualifier_typable_subtype : forall CT qr T1 T2 qcontext
  (Hsub   : qualified_type_subtype CT T1 T2)
  (Hqual1 : qualifier_typable_context qr (sqtype T1) qcontext),
  qualifier_typable_context qr (sqtype T2) qcontext.
Proof.
  intros CT qr T1 T2 qcontext Hsub Hqual1.
  apply qualified_type_subtype_q_subtype in Hsub.
  unfold qualifier_typable_context in *.
  destruct qr as [|].
  - (* Goal 1: Mut_r case *)
  destruct T1 as [q1 c1], T2 as [q2 c2].
  simpl in *.
  destruct q1, q2, qcontext; simpl in *; auto;
  try (inversion Hsub; subst; simpl in *; auto).

  - (* Goal 2: Imm_r case *)  
    destruct T1 as [q1 c1], T2 as [q2 c2].
    simpl in *.
    destruct q1, q2, qcontext; simpl in *; auto;
    try (inversion Hsub; subst; simpl in *; auto).
Qed.

(* Subtyping Preservation for wf_r_typable *)
Lemma wf_r_typable_subtype : forall CT rΓ h loc T1 T2 qcontext
  (Hwfheap : wf_heap CT h)
  (Hwf     : wf_r_typable CT rΓ h loc T1 qcontext)
  (Hsub    : qualified_type_subtype CT T1 T2),
  wf_r_typable CT rΓ h loc T2 qcontext.
Proof.
  intros CT rΓ h loc T1 T2 qcontext hwfheap Hwf Hsub.
  unfold wf_r_typable in *.
  destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
  split.
- (* Base type equality *)
  destruct Hwf as [Hbase _].
  apply qualified_type_subtype_base_subtype in Hsub.
  inversion Hsub; subst.
  exact Hbase.
  eapply base_trans; eauto.
  eapply base_trans; eauto.
  - destruct Hwf as [_ Hqualifier]. 
  eapply qualifier_typable_subtype; [ exact Hsub | exact Hqualifier].
Qed.

Lemma get_this_qualified_type_nth_error : forall sΓ Tthis
  (Hthis : get_this_qualified_type sΓ = Some Tthis),
  nth_error sΓ 0 = Some Tthis.
Proof.
  intros sΓ Tthis H.
  unfold get_this_qualified_type in H.
  destruct sΓ as [|T sΓ']; [discriminate|].
  injection H as H. subst. reflexivity.
Qed.

Lemma get_this_var_mapping_runtime_getVal : forall rΓ loc
  (Hthis : get_this_var_mapping (vars rΓ) = Some loc),
  runtime_getVal rΓ 0 = Some (Iot loc).
Proof.
  intros rΓ loc H.
  unfold get_this_var_mapping in H.
  unfold runtime_getVal.
  destruct (vars rΓ) as [|v vs] eqn:Hvars.
  - discriminate H.
  - destruct v as [|l].
    + discriminate H.
    + injection H as Heq. subst l.
      reflexivity.
Qed.

Lemma r_muttype_of_r_type : forall h loc rqt
  (Hr : r_type h loc = Some rqt),
  r_muttype h loc = Some (rqtype rqt).
Proof.
  intros h loc rqt Hr.
  unfold r_type in Hr. unfold r_muttype.
  destruct (runtime_getObj h loc) as [o|] eqn:Hobj; [|discriminate Hr].
  inversion Hr; subst. reflexivity.
Qed.

Lemma vpa_mutability_tt_sctype_abs_imm : forall Tthis T,
  sctype (vpa_mutability_tt_abs_imm Tthis T) = sctype T.
Proof.
  intros Tthis T.
  unfold vpa_mutability_tt_abs_imm.
  destruct T as [q c]. simpl.
  destruct (sqtype Tthis); destruct q; simpl; reflexivity.
Qed.

Lemma vpa_preserve_basetype_subtype_abs_imm : forall CT Tthis T1 T2
  (Hsub : base_subtype CT (sctype (vpa_mutability_tt_abs_imm Tthis T1)) (sctype (vpa_mutability_tt_abs_imm Tthis T2))),
  base_subtype CT (sctype T1) (sctype T2).
Proof.
  intros CT Tthis T1 T2 Hsub.
  rewrite !vpa_mutability_tt_sctype_abs_imm in Hsub.
  exact Hsub.
Qed.

Lemma vpa_mutability_tt_sctype_safe_ro : forall Tthis T,
  sctype (vpa_mutability_tt_safe_ro Tthis T) = sctype T.
Proof.
  intros Tthis T.
  unfold vpa_mutability_tt_safe_ro.
  destruct T as [q c]. simpl.
  destruct (sqtype Tthis); destruct q; simpl; reflexivity.
Qed.

Lemma vpa_preserve_basetype_subtype_safe_ro : forall CT Tthis T1 T2
  (Hsub : base_subtype CT (sctype (vpa_mutability_tt_safe_ro Tthis T1)) (sctype (vpa_mutability_tt_safe_ro Tthis T2))),
  base_subtype CT (sctype T1) (sctype T2).
Proof.
  intros CT Tthis T1 T2 Hsub.
  (* apply qualified_type_subtype_base_subtype in Hsub. *)
  rewrite !vpa_mutability_tt_sctype_safe_ro in Hsub.
  exact Hsub.
Qed.

(* Both directions cannot be proved here. *)
(* q_subtype (sqtype (vpa_mutability_tt Tthis T1)) (sqtype (vpa_mutability_tt Tthis T2)) <->
q_subtype (sqtype T1) (sqtype T2). *)

Lemma wf_r_typable_adapted_subtype_abs_imm : forall CT sΓ rΓ h Tthis locthis loc T1 T2 qcontext
  (HwfConfig        : wf_heap CT h)
  (HThisType        : get_this_qualified_type sΓ = Some Tthis)
  (HThisVal         : get_this_var_mapping (vars rΓ) = Some locthis)
  (HthisMutability  : r_muttype h locthis = Some qcontext)
  (* wf_r_typable CT rΓ h locthis Tthis qcontext -> *)
  (Hthistypablity   : qualifier_typable_context qcontext (sqtype Tthis) qcontext)
  (Hwf              : wf_r_typable CT rΓ h loc T1 qcontext)
  (Hsub             : qualified_type_subtype CT (vpa_mutability_tt_abs_imm Tthis T1) (vpa_mutability_tt_abs_imm Tthis T2)),
  wf_r_typable CT rΓ h loc T2 qcontext.
Proof.
  intros CT sΓ rΓ h Tthis locthis loc T1 T2 qcontext HwfConfig HThisType HThisVal HthisMutability Hthistypablity Hwf Hsub.
  unfold wf_r_typable in *.
  destruct (r_type h loc) as [rt|] eqn:Hrtype; [|contradiction].
  split.
- (* Base type equality *)
  destruct Hwf as [Hbase _].
  apply qualified_type_subtype_base_subtype in Hsub.
  assert (base_subtype CT (sctype T1) (sctype T2)).
  {
    eapply vpa_preserve_basetype_subtype_abs_imm; eauto.
  }
  inversion Hsub; subst.
  eapply base_trans; eauto.
  eapply base_trans; eauto.
  eapply base_trans; eauto.
- destruct Hwf as [_ Hqualifier].
  unfold wf_r_config in HwfConfig.
  apply qualified_type_subtype_q_subtype in Hsub.
  assert (exists Tthis, r_type h locthis = Some Tthis).
  {
    unfold r_muttype in HthisMutability.
    destruct (runtime_getObj h locthis) eqn: save; [|easy].
    unfold r_type.
    rewrite save.
    eauto.
  }
  destruct H as [Tthistype HThisRuntimeType].
  assert(qcontext = rqtype Tthistype).
  {
    unfold r_muttype in HthisMutability.
    unfold r_type in HThisRuntimeType.
    destruct (runtime_getObj h locthis) eqn: save; [|easy].
    inversion HThisRuntimeType; subst.
    inversion HthisMutability; reflexivity.
  }
  unfold qualifier_typable_context in *; unfold vpa_mutability_rs in *; unfold vpa_mutability_tt_abs_imm in *.
  destruct (rqtype rt) eqn: qt; destruct qcontext eqn: qrthis; destruct (sqtype Tthis) eqn: qsthis; destruct (sqtype T1) eqn: qt1; destruct (sqtype T2) eqn: qt2; simpl in *; try easy.
  all: try rewrite qt1 in Hsub; try rewrite qt2 in Hsub; try constructor; try easy.
  all: inversion Hsub; easy.
Qed.

Lemma wf_r_typable_adapted_subtype_safe_ro : forall CT sΓ rΓ h Tthis locthis loc T1 T2 qcontext
  (HwfConfig        : wf_heap CT h)
  (HThisType        : get_this_qualified_type sΓ = Some Tthis)
  (HThisVal         : get_this_var_mapping (vars rΓ) = Some locthis)
  (HthisMutability  : r_muttype h locthis = Some qcontext)
  (* wf_r_typable CT rΓ h locthis Tthis qcontext -> *)
  (Hthistypablity   : qualifier_typable_context qcontext (sqtype Tthis) qcontext)
  (Hwf              : wf_r_typable CT rΓ h loc T1 qcontext)
  (Hsub             : qualified_type_subtype CT (vpa_mutability_tt_safe_ro Tthis T1) (vpa_mutability_tt_safe_ro Tthis T2)),
  wf_r_typable CT rΓ h loc T2 qcontext.
Proof.
  intros CT sΓ rΓ h Tthis locthis loc T1 T2 qcontext HwfConfig HThisType HThisVal HthisMutability Hthistypablity Hwf Hsub.
  unfold wf_r_typable in *.
  destruct (r_type h loc) as [rt|] eqn:Hrtype; [|contradiction].
  split.
- (* Base type equality *)
  destruct Hwf as [Hbase _].
  apply qualified_type_subtype_base_subtype in Hsub.
  assert (base_subtype CT (sctype T1) (sctype T2)).
  {
    eapply vpa_preserve_basetype_subtype_safe_ro; eauto.
  }
  inversion Hsub; subst.
  eapply base_trans; eauto.
  eapply base_trans; eauto.
  eapply base_trans; eauto.
- destruct Hwf as [_ Hqualifier].
  unfold wf_r_config in HwfConfig.
  apply qualified_type_subtype_q_subtype in Hsub.
  assert (exists Tthis, r_type h locthis = Some Tthis).
  {
    unfold r_muttype in HthisMutability.
    destruct (runtime_getObj h locthis) eqn: save; [|easy].
    unfold r_type.
    rewrite save.
    eauto.
  }
  destruct H as [Tthistype HThisRuntimeType].
  assert(qcontext = rqtype Tthistype).
  {
    unfold r_muttype in HthisMutability.
    unfold r_type in HThisRuntimeType.
    destruct (runtime_getObj h locthis) eqn: save; [|easy].
    inversion HThisRuntimeType; subst.
    inversion HthisMutability; reflexivity.
  }
  unfold qualifier_typable_context in *; unfold vpa_mutability_rs in *; unfold vpa_mutability_tt_safe_ro in *.
  destruct (rqtype rt) eqn: qt; destruct qcontext eqn: qrthis; destruct (sqtype Tthis) eqn: qsthis; destruct (sqtype T1) eqn: qt1; destruct (sqtype T2) eqn: qt2; simpl in *; try easy.
  all: try rewrite qt1 in Hsub; try rewrite qt2 in Hsub; try constructor; try easy.
  all: inversion Hsub; easy.
Qed.

Lemma Forall2_nth_error_prop : forall {A B : Type} (P : A -> B -> Prop) (l1 : list A) (l2 : list B) (n : nat) (a : A) (b : B)
  (Hforall2 : Forall2 P l1 l2)
  (Hnth1    : nth_error l1 n = Some a)
  (Hnth2    : nth_error l2 n = Some b),
  P a b.
Proof.
  intros A B P l1 l2 n a b Hforall2 Hnth1 Hnth2.
  revert l1 l2 Hforall2 Hnth1 Hnth2.
  induction n; intros l1 l2 Hforall2 Hnth1 Hnth2.
  - (* n = 0 *)
    destruct l1 as [|a1 l1']; [discriminate|].
    destruct l2 as [|b1 l2']; [discriminate|].
    inversion Hforall2; subst.
    simpl in Hnth1, Hnth2.
    injection Hnth1 as Ha_eq.
    injection Hnth2 as Hb_eq.
    subst. exact H2.
  - (* n = S n' *)
    destruct l1 as [|a1 l1']; [discriminate|].
    destruct l2 as [|b1 l2']; [discriminate|].
    inversion Hforall2; subst.
    simpl in Hnth1, Hnth2.
    apply IHn with l1' l2'; assumption.
Qed.

Lemma nth_error_update_neq : forall {A : Type} (l : list A) (i j : nat) (v : A)
  (Hneq : i <> j),
  nth_error (update i v l) j = nth_error l j.
Proof.
  intros A l i j v Hneq.
  apply update_diff.
  exact Hneq.
Qed.

(* 1. Static-Runtime Correspondence Lemmas *)
Lemma runtime_lookup_list_preserves_length : forall rΓ args vals
  (Hlookup : runtime_lookup_list rΓ args = Some vals),
  List.length vals = List.length args.
Proof.
  intros rΓ args vals H.
  unfold runtime_lookup_list in H.
  generalize dependent vals.
  induction args as [|a args' IH]; intros vals H.
  - simpl in H. injection H as H. subst. reflexivity.
  - simpl in H.
    destruct (runtime_getVal rΓ a) as [v|] eqn:Hval; [|discriminate].
    destruct (mapM (fun x => runtime_getVal rΓ x) args') as [vs|] eqn:Hmap; [|discriminate].
    injection H as H. subst.
    simpl. f_equal. apply IH. reflexivity.
Qed.

Lemma runtime_lookup_list_preserves_typing : forall CT sΓ rΓ h args vals argtypes ι qcontext
  (Hreceiveraddr  : get_this_var_mapping (vars rΓ) = Some ι)
  (Hreceiverrmut  : (r_muttype h ι) = Some qcontext)
  (Hwf            : wf_r_config CT sΓ rΓ h)
  (Hstatic        : static_getType_list sΓ args = Some argtypes)
  (Hruntime       : runtime_lookup_list rΓ args = Some vals),
  Forall2 (fun v T => match v with
    | Null_a => True
    | Iot loc => wf_r_typable CT rΓ h loc T qcontext
    end) vals argtypes.
Proof.
  intros CT sΓ rΓ h args vals argtypes ι qcontext Hreceiveraddr Hreceiverrmut Hwf Hstatic Hruntime.
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [_ [_ [Hlen Hcorr]]]]].
  generalize dependent vals. generalize dependent argtypes.
  induction args as [|a args' IH]; intros argtypes Hstatic vals Hruntime.
  - (* Base case: empty list *)
    unfold static_getType_list, runtime_lookup_list in *.
    simpl in Hstatic, Hruntime.
    injection Hstatic as Hstatic. injection Hruntime as Hruntime.
    subst. constructor.
  - (* Inductive case: a :: args' *)
    unfold static_getType_list, runtime_lookup_list in *.
    simpl in Hstatic, Hruntime.
    destruct (static_getType sΓ a) as [T|] eqn:HstaticT; [|discriminate].
    destruct (mapM (static_getType sΓ) args') as [Ts|] eqn:HstaticTs; [|discriminate].
    destruct (runtime_getVal rΓ a) as [v|] eqn:HruntimeV; [|discriminate].
    destruct (mapM (runtime_getVal rΓ) args') as [vs|] eqn:HruntimeVs; [|discriminate].
    injection Hstatic as Hstatic. injection Hruntime as Hruntime.
    subst. constructor.
    + (* Show v is well-typed with T *)
      assert (Ha_bound : a < List.length sΓ) by (apply static_getType_dom in HstaticT; exact HstaticT).
      specialize (Hcorr ι qcontext Hreceiveraddr Hreceiverrmut a Ha_bound T HstaticT).
      rewrite HruntimeV in Hcorr.
      destruct v as [|loc]; [trivial | exact Hcorr].
    + (* Apply IH to the tail *)
      apply IH.
      * unfold static_getType_list. reflexivity.
      * unfold runtime_lookup_list. reflexivity.
Qed.

(* 2. Heap Extension Preservation *)
Lemma heap_extension_preserves_objects : forall h obj loc
  (Hloc : loc < dom h),
  runtime_getObj (h ++ [obj]) loc = runtime_getObj h loc.
Proof.
  intros h obj loc Hloc.
  unfold runtime_getObj.
  apply nth_error_app1. exact Hloc.
Qed.

Lemma heap_extension_preserves_wf_r_typable : forall CT rΓ h obj loc T qcontext
  (Hwf : wf_r_typable CT rΓ h loc T qcontext),
  wf_r_typable CT rΓ (h ++ [obj]) loc T qcontext.
Proof.
  intros CT rΓ h obj loc T qcontext Hwf.
  unfold wf_r_typable in *.
  destruct (r_type h loc) as [rqt|] eqn:Hrtype; [|contradiction].
  (* destruct (get_this_var_mapping (vars rΓ)) as [ι'|] eqn:Hthis; [|contradiction]. *)
  (* destruct (r_muttype h ι') as [q|] eqn:Hmut; [|contradiction]. *)
  
  assert (Hrtype_ext : r_type (h ++ [obj]) loc = Some rqt).
  {
    unfold r_type in *.
    assert (Hloc_dom : loc < dom h).
    {
      unfold r_type in Hrtype.
      destruct (runtime_getObj h loc) as [o|] eqn:Hobj; [|discriminate].
      apply runtime_getObj_dom in Hobj. exact Hobj.
    }
    rewrite heap_extension_preserves_objects; assumption.
  }
  rewrite Hrtype_ext.
  exact Hwf.
Qed.

(* 3. Subtyping Properties *)
Lemma q_subtype_refl : forall q
  (Hneq : q <> Lost),
  q_subtype q q.
Proof.
  intros q Hneq.
  apply q_refl. exact Hneq.
Qed.

(* 4. Forall2 Manipulation Lemmas *)
Lemma Forall2_trans {A B C : Type} (P : A -> B -> Prop) (Q : B -> C -> Prop) (R : A -> C -> Prop) :
  forall l1 l2 l3
  (Htrans : forall a b c, P a b -> Q b c -> R a c)
  (HP     : Forall2 P l1 l2)
  (HQ     : Forall2 Q l2 l3),
  Forall2 R l1 l3.
Proof.
  intros l1 l2 l3 Htrans HP HQ.
  generalize dependent l3. generalize dependent l1.
  induction l2 as [|b l2' IH]; intros l1 HP l3 HQ.
  - inversion HP; subst. inversion HQ; subst. constructor.
  - inversion HP; subst. inversion HQ; subst.
    constructor.
    + apply Htrans with b; assumption.
    + apply IH; assumption.
Qed.

Lemma Forall2_map : forall {A B C} (f : B -> C) (P : A -> C -> Prop) l1 l2
  (H : Forall2 (fun a b => P a (f b)) l1 l2),
  Forall2 P l1 (map f l2).
Proof.
  intros A B C f P l1 l2 H.
  induction H.
  - constructor.
  - simpl. constructor; assumption.
Qed.

(* 5. Field Access and Update Lemmas *)
Lemma field_update_preserves_other_fields : forall (fields : list value) f v f'
  (Hneq : f <> f'),
  getVal (update f v fields) f' = getVal fields f'.
Proof.
  intros fields f v f' Hneq.
  unfold getVal.
  apply update_diff. exact Hneq.
Qed.

Lemma field_update_preserves_length : forall (fields : list value) f v
  (Hbound : f < List.length fields),
  List.length (update f v fields) = List.length fields.
Proof.
  intros fields f v Hbound.
  apply update_length.
Qed.

(* evaluation preserves runtime type on heap. *)
Lemma runtime_preserves_r_type_heap : forall CT rΓ h loc C h' vals s rΓ'
  (Hobj  : runtime_getObj h loc = Some {| rt_type := C; fields_map := vals |})
  (Heval : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h s OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h'),
  exists vals', runtime_getObj h' loc = Some {| rt_type := C; fields_map := vals' |}.
Proof.
  intros. remember OK as ok. generalize dependent vals. 
  induction Heval; intros; subst; try discriminate.
  1-3: exists vals; assumption.
  - (* SBS_FldWrite *)
    destruct (Nat.eq_dec loc loc_x).
    + subst loc_x. rewrite Hobj in Hobj0. inversion Hobj0; subst.
      exists (update f val_y vals). unfold runtime_getObj.
      unfold update_field. rewrite Hobj. simpl.
      rewrite update_same; auto. apply runtime_getObj_dom in Hobj; auto.
    + exists vals. unfold runtime_getObj. unfold update_field. rewrite Hobj.
      rewrite update_diff; auto.
  - (* SBS_New *)
    exists vals0.
    apply runtime_getObj_dom in Hobj0 as Hloc_dom.
    rewrite runtime_getObj_last2; auto.
  - (* SBS_Call *)
    eapply IHHeval; eauto.
  - (* SBS_Seq *)
    destruct (IHHeval1 Heqok vals Hobj) as [vals' Hobj'].
    destruct (IHHeval2 Heqok vals' Hobj') as [vals'' Hobj''].
    exists vals''. exact Hobj''.
Qed.

Lemma Forall2_length : forall {A B} (P : A -> B -> Prop) l1 l2
  (H : Forall2 P l1 l2),
  List.length l1 = List.length l2.
Proof.
  intros A B P l1 l2 H.
  induction H; [reflexivity | simpl; f_equal; assumption].
Qed.

Lemma Forall_nth_error_wf_class : forall CT CT' C def
  (Hforall : Forall (wf_class CT) CT')
  (Hfind   : find_class CT' C = Some def),
  wf_class CT def.
Proof.
  intros CT CT' C def Hforall Hfind.
  generalize dependent C.
  induction CT' as [|cdef CT'' IH]; intros C Hfind.
  - simpl in Hfind.   exfalso.
  destruct C; simpl in Hfind; discriminate.
  - simpl in Hfind.
    destruct C as [|C'].
    + injection Hfind as Heq. subst def.
      inversion Hforall; subst.
      exact H1.
    + inversion Hforall; subst.
    apply IH with (C := C').
    * exact H2.
    * exact Hfind.
Qed.

Lemma find_class_wf_class : forall CT C def
  (Hwf_ct : wf_class_table CT)
  (Hfind  : find_class CT C = Some def),
  wf_class CT def.
Proof.
  intros CT C def Hwf_ct Hfind.
  unfold wf_class_table in Hwf_ct.
  (* Use induction on CT to find the class at position C *)
  generalize dependent C.
  induction CT as [|cdef CT' IH]; intros C Hfind.
  - (* Empty CT case *)
  exfalso.
  destruct C; simpl in Hfind; discriminate.

  - (* Non-empty CT case *)
    simpl in Hfind.
    destruct C as [|C'].
    + (* C = 0, so def = cdef *)
      injection Hfind as Heq. subst def.
      inversion Hwf_ct; subst.
      inversion H; subst.
      exact H3.
    + (* C = S C', recurse *)
      inversion Hwf_ct; subst.
      assert (Hfind_CT' : find_class CT' C' = Some def).
      {
        simpl in Hfind.
        exact Hfind.
      }

      apply (Forall_nth_error_wf_class (cdef :: CT') CT' C' def).
      * inversion H; subst.
      exact H4.
      * exact Hfind_CT'.
Qed.

Lemma vpa_assingability_assign_cases : forall q a
  (Hvpa : vpa_assignability q a = Assignable),
  (a = Assignable) \/
  (q = Mut /\ a = RDA).
Proof.
  intros q a Hvpa.
  unfold vpa_assignability in Hvpa.
  destruct q, a; simpl in Hvpa; try discriminate; auto.
Qed.

(* Expression Evaluation Preservation *)
(* TODO: This could be refactored to remove the first two premises. *)
Lemma expr_eval_preservation : forall P CT sΓ mt rΓ h e v rΓ' h' T ι qcontext
  (Hreceiveraddr : get_this_var_mapping (vars rΓ) = Some ι)
  (Hreceiverrmut : (r_muttype h ι) = Some qcontext)
  (Hwf           : wf_r_config CT sΓ rΓ h)
  (Htype         : expr_has_type CT sΓ mt e T)
  (Heval         : eval_expr OK P CT rΓ h e v OK P rΓ' h'),
  match v with
  | Null_a => True
  | Iot loc => wf_r_typable CT rΓ h loc T qcontext
  end.
Proof.
  intros P CT sΓ mt rΓ h e v rΓ' h' T ι qcontext Hreceiveraddr Hreceiverrmut Hwf Htype Heval.
  have Hevalcopy := Heval.
  remember OK as ok. 
  induction Heval; inversion Htype; subst; try discriminate.
  - (* EBS_Null *) trivial.
  - (* EBS_Val *) 
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [_ [_ [Hlen Hcorr]]]]].
    assert (Hx_bound : x < List.length sΓ) by (apply static_getType_dom in Hget; exact Hget).
    specialize (Hcorr ι qcontext Hreceiveraddr Hreceiverrmut x Hx_bound T Hget).
    rewrite Hval in Hcorr.
    destruct v as [|loc]; [trivial | exact Hcorr].
  - (* EBS_Field *)
  destruct v1 as [|loc]; [trivial|].
  (* Need to show: wf_r_typable CT rΓ h loc (vpa_type_to_type T0 ...) *)
  unfold wf_r_config in Hwf.
  destruct Hwf as [Hwfclass [Hwf_heap [Hwf_renv [Hwf_senv [_ Hcorr]]]]].
  (* Use heap well-formedness to get field typing *)
  assert (Hobj_wf : wf_obj CT h v).
  {
    apply Hwf_heap.
    apply runtime_getObj_dom in Hobj.
    exact Hobj.
  }
  unfold wf_obj in Hobj_wf.
  rewrite Hobj in Hobj_wf.
  destruct Hobj_wf as [_ Hfields_wf].
  destruct Hfields_wf as [Hdom_eq Hforall2].
  destruct Hforall2 as [Hcollect [Hdom_eq_test Hforall2]].

  assert (Hfield_lookup : exists fdef, 
    nth_error Hdom_eq f = Some fdef /\
    nth_error (fields_map o) f = Some (Iot loc)).
  {
    (* Use H1 and Hdom_eq to establish this *)
    (* Convert getVal to nth_error using domain equality *)
    assert (Hf_in_dom : f < dom (fields_map o)).
    {
      apply getVal_dom in Hfield.
      exact Hfield.
    }
    (* Use domain equality to get f in collect_fields domain *)
    rewrite Hdom_eq_test in Hf_in_dom.
    assert (Hfdef_exists : exists fdef, nth_error Hdom_eq f = Some fdef).
    {
      destruct (nth_error Hdom_eq f) as [fdef|] eqn:Hfdef_lookup.
      - exists fdef. reflexivity.
      - exfalso.
        apply nth_error_None in Hfdef_lookup.
        lia.
    }
    destruct Hfdef_exists as [fdef Hfdef_lookup].
    (* Convert H1 from getVal to nth_error *)
    assert (Hfield_nth : nth_error (fields_map o) f = Some (Iot loc)).
    {
      unfold getVal in Hfield.
      exact Hfield.
    }
    exists fdef.
    split; [exact Hfdef_lookup | exact Hfield_nth].
  }
  destruct Hfield_lookup as [fdef [Hfdef_lookup Hfield_nth]].
  (* Apply Forall2 property *)
  eapply Forall2_nth_error_prop in Hforall2; eauto.
  simpl in Hforall2.
  (* Now check if loc exists in heap *)
  destruct (runtime_getObj h loc) as [o_loc|] eqn:Hloc_obj.
  * (* loc exists in heap *)
    destruct Hforall2 as [rqt [Hrtype_loc Hsubtype]].
    (* Now you have the typing for loc *)
    unfold wf_r_typable.
    rewrite Hrtype_loc.
    (* Get this variable mapping *)
    destruct (get_this_var_mapping (vars rΓ)) as [ι'|] eqn:Hthis.
    2:{
      (* Use wf_r_config to show that this variable mapping must exist *)
      destruct Hwf_renv as [Hwf_this [Hwf_this_addr Hwf_renv]].
      (* Hwf_this should guarantee that get_this_var_mapping succeeds *)
      unfold get_this_var_mapping in Hthis.
      (* get_this_var_mapping typically looks at vars[0] *)
      assert (H0_bound : 0 < dom (vars rΓ)) by exact Hwf_this.
      (* unfold dom in H0_bound. *)
      (* Since length > 0, nth_error 0 must succeed *)
      destruct (nth_error (vars rΓ) 0) as [v0|] eqn:Hv0.
      - (* vars[0] exists, so get_this_var_mapping should succeed *)
        simpl in Hthis.
        destruct (vars rΓ) as [|v1 rest] eqn:Hvars.
        simpl in Hv0.
        discriminate.
        simpl in Hv0.
        injection Hv0 as Hv0_eq.
        subst v0.
        (* So v1 = v0, and from Hthis we know v1 = Null_a *)
        destruct v1 as [|loc'].
        + (* v1 = Null_a, consistent with Hthis *)
          (* But this contradicts well-formedness - need stronger condition *)
          (* For now, this might be an allowed case *)
          destruct Hwf_this_addr as [iot Hiot].
          (* gget (Null_a :: rest) 0 should return Null_a, not Iot iot *)
          simpl in Hiot.
          destruct Hiot as [Hiot Hthisdom].
          (* gget is likely nth_error or similar, so gget (Null_a :: rest) 0 = Some Null_a *)
          discriminate Hiot.
        + (* v1 = Iot loc', should make get_this_var_mapping return Some loc' *)
          simpl in Hthis.
          discriminate Hthis.
      - (* vars[0] doesn't exist, contradicts length > 0 *)
        apply nth_error_None in Hv0.
        simpl in H0_bound.
        lia.
    }
    destruct (r_muttype h ι') as [q|] eqn:Hmut.
    2:{
      assert (Hι'_in_heap : ι' < dom h).
      {
        (* ι' comes from get_this_var_mapping, so it must be in heap *)
        (* Use the third component of Hwf_renv *)
        destruct Hwf_renv as [Hwf_this [Hwf_this_addr Hwf_renv]].
        destruct Hwf_this_addr as [iot Hiot].
        destruct Hiot as [Hiot Hthisdom].
        unfold get_this_var_mapping in Hthis.
        assert (Hconnect : ι' = iot).
        {
          unfold get_this_var_mapping in Hthis.
          destruct (vars rΓ) as [|vtest rest] eqn:Hvars.
          - (* Empty list case *)
            discriminate Hthis.
          - (* Non-empty list case *)
            destruct vtest as [|loctest] eqn:Hv.
            + (* Null_a case *)
              discriminate Hthis.
            + (* Iot loc case *)
              injection Hthis as Heq.
              subst ι'.
              simpl in Hiot.
              injection Hiot as Heq2.
              exact Heq2.
        }
        rewrite Hconnect. exact Hthisdom.
      }
      (* Now use heap well-formedness *)
      apply Hwf_heap in Hι'_in_heap.
      unfold wf_obj in Hι'_in_heap.
        destruct Hwf_renv as [Hwf_this [Hwf_this_addr Hwf_renv]].
        destruct Hwf_this_addr as [iot Hiot].
        destruct Hiot as [Hiot Hthisdom].
      assert (Hconnect : ι' = iot).
      {
        unfold get_this_var_mapping in Hthis.
        destruct (vars rΓ) as [|vtest rest] eqn:Hvars.
        - discriminate Hthis.
        - destruct vtest as [|loctest] eqn:Hv.
          + discriminate Hthis.
          + injection Hthis as Heq.
            subst ι'.
            simpl in Hiot.
            injection Hiot as Heq2.
            exact Heq2.
      }
      rewrite Hconnect in Hmut.
      unfold r_muttype in Hmut.
      apply runtime_getObj_Some in Hthisdom.
      destruct Hthisdom as [C [ω Ho']].
      rewrite Ho' in Hmut.
      discriminate Hmut.
    }
  assert (Hfdef_eq : fdef = fDef).
  {
    unfold sf_def_rel in Hfld_def.
    
    assert (Hfield_lookup_o : FieldLookup CT (rctype (rt_type o)) f fdef).
    {
      apply FL_Found with Hdom_eq.
      - exact Hcollect.
      - exact Hfdef_lookup.
    }

    (* Use wf_r_typable for x *)
    assert (Hx_wf : wf_r_typable CT rΓ h v T0 qcontext).
    {
      assert (Hx_bound : x < dom sΓ) by (apply static_getType_dom in Hget_x; exact Hget_x).
      specialize (Hcorr ι qcontext Hreceiveraddr Hreceiverrmut x Hx_bound T0 Hget_x).
      rewrite Hval in Hcorr.
      exact Hcorr.
    }
    
    (* Extract base subtyping from wf_r_typable *)
    unfold wf_r_typable in Hx_wf.
    unfold r_type in Hx_wf.
    rewrite Hobj in Hx_wf.
    simpl in Hx_wf.
    eapply field_lookup_deterministic_rel.
    - exact Hfield_lookup_o.
    - destruct Hx_wf as [Hbase _].
      eapply field_inheritance_subtyping; eauto.
  }
  subst fdef.
  split.
  -- (* Base subtyping *)
    simpl.
    destruct Hsubtype as [Hbasesubtyp _].
    exact Hbasesubtyp.
  -- (* Qualifier typability *)
    destruct Hsubtype as [Hbasesubtyp Hqualifiertypable].
    unfold qualifier_typable_context.
    inversion Hreceiveraddr; subst ι'.
    rewrite Hmut in Hreceiverrmut.
    inversion Hreceiverrmut; subst q.
    unfold vpa_mutability_rs; unfold vpa_mutability_stype_fld_abs_imm in *; unfold vpa_mutability_rec_fld in Hqualifiertypable;
    destruct (rqtype rqt) eqn: Hrqttype;
    destruct (sqtype T0) eqn: HsqtypeT0;
    destruct (mutability (ftype fDef)) eqn: Hfieldqualifier;
    destruct qcontext eqn: Hqcontext;
    simpl;
    try (inversion Hsubtype; auto);
    destruct T0 as [q0 c0] eqn: HT0type;
    try discriminate;
    try trivial.
    all:
    try destruct (rqtype (rt_type o)) eqn: HreceiverRuntimeQualifier;
    unfold qualifier_typable_heap in Hqualifiertypable;
    try easy.
    all: try simpl in HsqtypeT0; subst q0.
    all: try have H7copy := Hget_x; try apply static_getType_dom in Hget_x.
    all: try unfold static_getType in H7copy.
    all: try specialize (Hcorr ι Mut_r Hreceiveraddr Hmut x Hget_x {|
    sqtype := Imm; sctype :=
    c0
    |} H7copy).
    all: try specialize (Hcorr ι Imm_r Hreceiveraddr Hmut x Hget_x {|
    sqtype := Imm; sctype :=
    c0
    |} H7copy).
    all: try specialize (Hcorr ι Mut_r Hreceiveraddr Hmut x Hget_x {|
    sqtype := RDM; sctype :=
    c0
    |} H7copy).
    all: try specialize (Hcorr ι Imm_r Hreceiveraddr Hmut x Hget_x {|
    sqtype := RDM; sctype :=
    c0
    |} H7copy).
    all: try specialize (Hcorr ι Mut_r Hreceiveraddr Hmut x Hget_x {|
    sqtype := Bot; sctype :=
    c0
    |} H7copy).
    all: try specialize (Hcorr ι Imm_r Hreceiveraddr Hmut x Hget_x {|
    sqtype := Bot; sctype :=
    c0
    |} H7copy).
    all: try specialize (Hcorr ι Mut_r Hreceiveraddr Hmut x Hget_x {|
    sqtype := Mut; sctype :=
    c0
    |} H7copy).
    all: try specialize (Hcorr ι Imm_r Hreceiveraddr Hmut x Hget_x {|
    sqtype := Mut; sctype :=
    c0
    |} H7copy).
    all: try rewrite Hval in Hcorr.
    all: try unfold wf_r_typable in Hcorr.
    all: try unfold r_type in Hcorr.
    all: try rewrite Hobj in Hcorr.
    all: try destruct Hcorr as [Hobasetype Hoqualifier].
    all: try simpl in Hoqualifier.
    all: try rewrite HreceiverRuntimeQualifier in Hoqualifier.
    all: try unfold qualifier_typable in Hoqualifier.
    all: try unfold vpa_mutability_rs; try unfold vpa_mutability_stype_fld in *; try unfold vpa_mutability_rec_fld in Hqualifiertypable; try easy.
  *  exfalso. exact Hforall2.
  -
  destruct v1 as [|loc]; [trivial|].
  (* Need to show: wf_r_typable CT rΓ h loc (vpa_type_to_type T0 ...) *)
  unfold wf_r_config in Hwf.
  destruct Hwf as [Hwfclass [Hwf_heap [Hwf_renv [Hwf_senv [_ Hcorr]]]]].
  (* Use heap well-formedness to get field typing *)
  assert (Hobj_wf : wf_obj CT h v).
  {
    apply Hwf_heap.
    apply runtime_getObj_dom in Hobj.
    exact Hobj.
  }
  unfold wf_obj in Hobj_wf.
  rewrite Hobj in Hobj_wf.
  destruct Hobj_wf as [_ Hfields_wf].
  destruct Hfields_wf as [Hdom_eq Hforall2].
  destruct Hforall2 as [Hcollect [Hdom_eq_test Hforall2]].

  assert (Hfield_lookup : exists fdef, 
    nth_error Hdom_eq f = Some fdef /\
    nth_error (fields_map o) f = Some (Iot loc)).
  {
    (* Use H1 and Hdom_eq to establish this *)
    (* Convert getVal to nth_error using domain equality *)
    assert (Hf_in_dom : f < dom (fields_map o)).
    {
      apply getVal_dom in Hfield.
      exact Hfield.
    }
    (* Use domain equality to get f in collect_fields domain *)
    rewrite Hdom_eq_test in Hf_in_dom.
    assert (Hfdef_exists : exists fdef, nth_error Hdom_eq f = Some fdef).
    {
      destruct (nth_error Hdom_eq f) as [fdef|] eqn:Hfdef_lookup.
      - exists fdef. reflexivity.
      - exfalso.
        apply nth_error_None in Hfdef_lookup.
        lia.
    }
    destruct Hfdef_exists as [fdef Hfdef_lookup].
    (* Convert H1 from getVal to nth_error *)
    assert (Hfield_nth : nth_error (fields_map o) f = Some (Iot loc)).
    {
      unfold getVal in Hfield.
      exact Hfield.
    }
    exists fdef.
    split; [exact Hfdef_lookup | exact Hfield_nth].
  }
  destruct Hfield_lookup as [fdef [Hfdef_lookup Hfield_nth]].
  (* Apply Forall2 property *)
  eapply Forall2_nth_error_prop in Hforall2; eauto.
  simpl in Hforall2.
  (* Now check if loc exists in heap *)
  destruct (runtime_getObj h loc) as [o_loc|] eqn:Hloc_obj.
  * (* loc exists in heap *)
    destruct Hforall2 as [rqt [Hrtype_loc Hsubtype]].
    (* Now you have the typing for loc *)
    unfold wf_r_typable.
    rewrite Hrtype_loc.
    (* Get this variable mapping *)
    destruct (get_this_var_mapping (vars rΓ)) as [ι'|] eqn:Hthis.
    2:{
      (* Use wf_r_config to show that this variable mapping must exist *)
      destruct Hwf_renv as [Hwf_this [Hwf_this_addr Hwf_renv]].
      (* Hwf_this should guarantee that get_this_var_mapping succeeds *)
      unfold get_this_var_mapping in Hthis.
      (* get_this_var_mapping typically looks at vars[0] *)
      assert (H0_bound : 0 < dom (vars rΓ)) by exact Hwf_this.
      (* unfold dom in H0_bound. *)
      (* Since length > 0, nth_error 0 must succeed *)
      destruct (nth_error (vars rΓ) 0) as [v0|] eqn:Hv0.
      - (* vars[0] exists, so get_this_var_mapping should succeed *)
        simpl in Hthis.
        destruct (vars rΓ) as [|v1 rest] eqn:Hvars.
        simpl in Hv0.
        discriminate.
        simpl in Hv0.
        injection Hv0 as Hv0_eq.
        subst v0.
        (* So v1 = v0, and from Hthis we know v1 = Null_a *)
        destruct v1 as [|loc'].
        + (* v1 = Null_a, consistent with Hthis *)
          (* But this contradicts well-formedness - need stronger condition *)
          (* For now, this might be an allowed case *)
          destruct Hwf_this_addr as [iot Hiot].
          (* gget (Null_a :: rest) 0 should return Null_a, not Iot iot *)
          simpl in Hiot.
          destruct Hiot as [Hiot Hthisdom].
          (* gget is likely nth_error or similar, so gget (Null_a :: rest) 0 = Some Null_a *)
          discriminate Hiot.
        + (* v1 = Iot loc', should make get_this_var_mapping return Some loc' *)
          simpl in Hthis.
          discriminate Hthis.
      - (* vars[0] doesn't exist, contradicts length > 0 *)
        apply nth_error_None in Hv0.
        simpl in H0_bound.
        lia.
    }
    destruct (r_muttype h ι') as [q|] eqn:Hmut.
    2:{
      assert (Hι'_in_heap : ι' < dom h).
      {
        (* ι' comes from get_this_var_mapping, so it must be in heap *)
        (* Use the third component of Hwf_renv *)
        destruct Hwf_renv as [Hwf_this [Hwf_this_addr Hwf_renv]].
        destruct Hwf_this_addr as [iot Hiot].
        destruct Hiot as [Hiot Hthisdom].
        unfold get_this_var_mapping in Hthis.
        assert (Hconnect : ι' = iot).
        {
          unfold get_this_var_mapping in Hthis.
          destruct (vars rΓ) as [|vtest rest] eqn:Hvars.
          - (* Empty list case *)
            discriminate Hthis.
          - (* Non-empty list case *)
            destruct vtest as [|loctest] eqn:Hv.
            + (* Null_a case *)
              discriminate Hthis.
            + (* Iot loc case *)
              injection Hthis as Heq.
              subst ι'.
              simpl in Hiot.
              injection Hiot as Heq2.
              exact Heq2.
        }
        rewrite Hconnect. exact Hthisdom.
      }
      (* Now use heap well-formedness *)
      apply Hwf_heap in Hι'_in_heap.
      unfold wf_obj in Hι'_in_heap.
      destruct Hwf_renv as [Hwf_this [Hwf_this_addr Hwf_renv]].
      destruct Hwf_this_addr as [iot Hiot].
      destruct Hiot as [Hiot Hthisdom].
      assert (Hconnect : ι' = iot).
      {
        unfold get_this_var_mapping in Hthis.
        destruct (vars rΓ) as [|vtest rest] eqn:Hvars.
        - discriminate Hthis.
        - destruct vtest as [|loctest] eqn:Hv.
          + discriminate Hthis.
          + injection Hthis as Heq.
            subst ι'.
            simpl in Hiot.
            injection Hiot as Heq2.
            exact Heq2.
      }
      rewrite Hconnect in Hmut.
      unfold r_muttype in Hmut.
      apply runtime_getObj_Some in Hthisdom.
      destruct Hthisdom as [C [ω Ho']].
      rewrite Ho' in Hmut.
      discriminate Hmut.
    }
    assert (Hfdef_eq : fdef = fDef).
    {
      unfold sf_def_rel in Hfld_def.
      
      (* Next, get FieldLookup from CollectFields *)
      assert (Hfield_lookup_o : FieldLookup CT (rctype (rt_type o)) f fdef).
      {
        apply FL_Found with Hdom_eq.
        - exact Hcollect.
        - exact Hfdef_lookup.
      }

      (* Use wf_r_typable for x *)
      assert (Hx_wf : wf_r_typable CT rΓ h v T0 qcontext).
      {
        assert (Hx_bound : x < dom sΓ) by (apply static_getType_dom in Hget_x; exact Hget_x).
        specialize (Hcorr ι qcontext Hreceiveraddr Hreceiverrmut x Hx_bound T0 Hget_x).
        rewrite Hval in Hcorr.
        exact Hcorr.
      }
      
      (* Extract base subtyping from wf_r_typable *)
      unfold wf_r_typable in Hx_wf.
      unfold r_type in Hx_wf.
      rewrite Hobj in Hx_wf.
      simpl in Hx_wf.
      eapply field_lookup_deterministic_rel.
      - exact Hfield_lookup_o.
      - destruct Hx_wf as [Hbase _].
        eapply field_inheritance_subtyping; eauto.
    }
    subst fdef.
    split.
  -- (* Base subtyping *)
    simpl.
    destruct Hsubtype as [Hbasesubtyp _].
    exact Hbasesubtyp.
  -- (* Qualifier typability *)
    destruct Hsubtype as [Hbasesubtyp Hqualifiertypable].
    unfold qualifier_typable_context.
    inversion Hreceiveraddr; subst ι'.
    rewrite Hmut in Hreceiverrmut.
    inversion Hreceiverrmut; subst q.
    unfold vpa_mutability_rs; unfold vpa_mutability_stype_fld_abs_imm in *; unfold vpa_mutability_rec_fld in Hqualifiertypable;
    destruct (rqtype rqt) eqn: Hrqttype;
    destruct (sqtype T0) eqn: HsqtypeT0;
    destruct (mutability (ftype fDef)) eqn: Hfieldqualifier;
    destruct qcontext eqn: Hqcontext;
    simpl;
    try (inversion Hsubtype; auto);
    destruct T0 as [q0 c0] eqn: HT0type;
    try discriminate;
    try trivial.
    all: 
    try destruct (rqtype (rt_type o)) eqn: HreceiverRuntimeQualifier;
    unfold qualifier_typable_heap in Hqualifiertypable;
    try easy.
    all: try simpl in HsqtypeT0; subst q0.
    all: try have H7copy := Hget_x; try apply static_getType_dom in Hget_x.
    all: try unfold static_getType in H7copy.
    all: try specialize (Hcorr ι Mut_r Hreceiveraddr Hmut x Hget_x {|
    sqtype := Imm; sctype :=
    c0
    |} H7copy).
    all: try specialize (Hcorr ι Imm_r Hreceiveraddr Hmut x Hget_x {|
    sqtype := Imm; sctype :=
    c0
    |} H7copy).
    all: try specialize (Hcorr ι Mut_r Hreceiveraddr Hmut x Hget_x {|
    sqtype := RDM; sctype :=
    c0
    |} H7copy).
    all: try specialize (Hcorr ι Imm_r Hreceiveraddr Hmut x Hget_x {|
    sqtype := RDM; sctype :=
    c0
    |} H7copy).
    all: try specialize (Hcorr ι Mut_r Hreceiveraddr Hmut x Hget_x {|
    sqtype := Bot; sctype :=
    c0
    |} H7copy).
    all: try specialize (Hcorr ι Imm_r Hreceiveraddr Hmut x Hget_x {|
    sqtype := Bot; sctype :=
    c0
    |} H7copy).
    all: try specialize (Hcorr ι Mut_r Hreceiveraddr Hmut x Hget_x {|
    sqtype := Mut; sctype :=
    c0
    |} H7copy).
    all: try specialize (Hcorr ι Imm_r Hreceiveraddr Hmut x Hget_x {|
    sqtype := Mut; sctype :=
    c0
    |} H7copy).
    all: try rewrite Hval in Hcorr.
    all: try unfold wf_r_typable in Hcorr.
    all: try unfold r_type in Hcorr.
    all: try rewrite Hobj in Hcorr.
    all: try destruct Hcorr as [Hobasetype Hoqualifier].
    all: try simpl in Hoqualifier.
    all: try rewrite HreceiverRuntimeQualifier in Hoqualifier.
    all: try unfold qualifier_typable in Hoqualifier.
    all: try unfold vpa_mutability_rs; try unfold vpa_mutability_stype_fld in *; try unfold vpa_mutability_rec_fld in Hqualifiertypable; try easy.
  *  exfalso. exact Hforall2.
Qed.

Lemma runtime_lookup_list_preserves_wf_values : forall CT rΓ h zs vals0
  (Hwf_renv : wf_renv CT rΓ h)
  (Hlookup  : runtime_lookup_list rΓ zs = Some vals0),
  Forall (fun v => match v with
    | Null_a => True
    | Iot loc => match runtime_getObj h loc with Some _ => True | None => False end
    end) vals0.
Proof.
  intros CT rΓ h zs vals0 Hwf_renv Hlookup.
  unfold runtime_lookup_list in Hlookup.
  unfold wf_renv in Hwf_renv.
  destruct Hwf_renv as [_ [_ Hallvals]].
  (* Prove by induction on zs and vals0 simultaneously *)
  generalize dependent vals0.
  induction zs as [|z zs' IH]; intros vals0 Hlookup.
  - (* Base case: zs = [] *)
    simpl in Hlookup.
    injection Hlookup as Hlookup.
    subst vals0.
    constructor.
  - (* Inductive case: zs = z :: zs' *)
    simpl in Hlookup.
    destruct (runtime_getVal rΓ z) as [v|] eqn:Hv; [|discriminate].
    destruct (mapM (runtime_getVal rΓ) zs') as [vs|] eqn:Hvs; [|discriminate].
    injection Hlookup as Hlookup.
    subst vals0.
    constructor.
    + (* Show v is well-formed *)
      destruct v as [|loc].
      * (* Case: Null_a *)
        trivial.
      * (* Case: Iot loc *)
        assert (Hloc_bound : z < dom (vars rΓ)).
        {
          apply runtime_getVal_dom in Hv.
          exact Hv.
        }
        assert (Hloc_wf := Forall_nth_error _ _ _ _ Hallvals Hv).
        simpl in Hloc_wf.
        exact Hloc_wf.
    + (* Show vs is well-formed *)
      apply IH.
      reflexivity.
Qed.

Lemma method_frame_vals_wf : forall CT rΓ h ly vals0 zs cy
  (Hwf_renv : wf_renv CT rΓ h)
  (Hly_base : r_basetype h ly = Some cy)
  (Hlookup  : runtime_lookup_list rΓ zs = Some vals0),
  Forall (fun value => match value with
    | Null_a => True
    | Iot loc => match runtime_getObj h loc with Some _ => True | None => False end
    end) (Iot ly :: vals0).
Proof.
  intros CT rΓ h ly vals0 zs cy Hwf_renv Hly_base Hlookup.
  constructor.
  - (* First element: Iot ly *)
    simpl.
    unfold r_basetype in Hly_base.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobj; [trivial | discriminate Hly_base].
  - (* Rest of the list: vals0 *)
    eapply runtime_lookup_list_preserves_wf_values; eauto.
Qed.

Lemma wf_class_in_table : forall CT C
  (Hwf_ct    : wf_class_table CT)
  (Hwf_class : wf_class CT C)
  (Hdom      : cname (signature C) < dom CT),
  find_class CT (cname (signature C)) = Some C.
Proof.
  intros CT C Hwf_ct Hwf_class Hdom.
  unfold wf_class_table in Hwf_ct.
  destruct Hwf_ct as [Hforall Hcname_consistent].
  (* Use the bidirectional consistency directly *)
  apply Hcname_consistent.
  reflexivity.
Qed.
