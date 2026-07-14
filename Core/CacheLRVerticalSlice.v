From Stdlib Require Import List.
Import ListNotations.

Require Import Syntax Core.GenericCacheProtocol.

(** * Cache Logical-Relation Vertical Slice

    This file is a deliberately small vertical slice for the paper story.  The
    generic theorem in [GenericCacheProtocol] already proves that
    [CacheSafeMethod] preserves semantic immutability.  This file shows how
    that semantic method premise can be discharged for a representative
    local-copy cache idiom, rejected for a double-read idiom, and exposed
    through a tiny type-indexed semantic interpretation.

    The definitions here are intentionally flat: cache fields and cache values
    are ordinary types, and histories are functions from fields to lists of
    values.  This avoids dependent finite-map proof overhead in the vertical
    slice while preserving the theorem shape used by the main development. *)

Record FlatCacheProtocol (AbsVal Field Val : Type) : Type := {
  flat_valid_cache : AbsVal -> Field -> Val -> Prop;
  flat_default_val : Field -> Val;
  flat_default_valid :
    forall a k, flat_valid_cache a k (flat_default_val k)
}.

Arguments flat_valid_cache {_ _ _} _ _ _ _.
Arguments flat_default_val {_ _ _} _ _.
Arguments flat_default_valid {_ _ _} _ _ _.

Definition flat_history (Field Val : Type) : Type := Field -> list Val.

Definition FlatCacheHistOK {AbsVal Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val)
    (hist : flat_history Field Val) (a : AbsVal) : Prop :=
  forall k v,
    In v (hist k) ->
    flat_valid_cache P a k v.

Definition flat_default_history {AbsVal Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val) : flat_history Field Val :=
  fun k => [flat_default_val P k].

Lemma cache_hist_ok_default :
  forall {AbsVal Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val) a,
    FlatCacheHistOK P (flat_default_history P) a.
Proof.
  intros AbsVal Field Val P a k v Hin.
  unfold flat_default_history in Hin.
  simpl in Hin.
  destruct Hin as [Hv | Hin].
  - subst v.
    apply flat_default_valid.
  - contradiction.
Qed.

Lemma cache_hist_ok_read_valid :
  forall {AbsVal Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val) hist a k v
    (Hhist : FlatCacheHistOK P hist a)
    (Hin : In v (hist k)),
    flat_valid_cache P a k v.
Proof.
  intros AbsVal Field Val P hist a k v Hhist Hin.
  eapply Hhist.
  exact Hin.
Qed.

Definition append_hist {Field Val : Type}
    (field_eq_dec : forall x y : Field, {x = y} + {x <> y})
    (hist : flat_history Field Val) (k : Field) (v : Val) :
    flat_history Field Val :=
  fun k' =>
    if field_eq_dec k' k then hist k' ++ [v] else hist k'.

Lemma cache_write_preserves_hist_ok :
  forall {AbsVal Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val)
    (field_eq_dec : forall x y : Field, {x = y} + {x <> y})
    hist a k v
    (Hhist : FlatCacheHistOK P hist a)
    (Hvalid : flat_valid_cache P a k v),
    FlatCacheHistOK P (append_hist field_eq_dec hist k v) a.
Proof.
  intros AbsVal Field Val P field_eq_dec hist a k v Hhist Hvalid k' v' Hin.
  unfold append_hist in Hin.
  destruct (field_eq_dec k' k) as [Heq | Hneq].
  - subst k'.
    apply in_app_or in Hin.
    destruct Hin as [Hold | Hnew].
    + eapply Hhist.
      exact Hold.
    + simpl in Hnew.
      destruct Hnew as [Hv | Hnil].
      * subst v'.
        exact Hvalid.
      * contradiction.
  - eapply Hhist.
    exact Hin.
Qed.

Inductive flat_cache_event (Field Val : Type) : Type :=
  | FlatERead : Field -> Val -> flat_cache_event Field Val
  | FlatEWrite : Field -> Val -> flat_cache_event Field Val.

Arguments FlatERead {_ _} _ _.
Arguments FlatEWrite {_ _} _ _.

Definition FlatValidEvent {AbsVal Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val) (a : AbsVal)
    (ev : flat_cache_event Field Val) : Prop :=
  match ev with
  | FlatERead k v => flat_valid_cache P a k v
  | FlatEWrite k v => flat_valid_cache P a k v
  end.

Fixpoint FlatValidTrace {AbsVal Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val) (a : AbsVal)
    (tr : list (flat_cache_event Field Val)) : Prop :=
  match tr with
  | [] => True
  | ev :: tr' => FlatValidEvent P a ev /\ FlatValidTrace P a tr'
  end.

Lemma valid_trace_cons_inv :
  forall {AbsVal Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val) a ev tr,
    FlatValidTrace P a (ev :: tr) ->
    FlatValidEvent P a ev /\ FlatValidTrace P a tr.
Proof.
  intros AbsVal Field Val P a ev tr Htrace.
  exact Htrace.
Qed.

Lemma valid_trace_app :
  forall {AbsVal Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val) a
    (tr1 tr2 : list (flat_cache_event Field Val)),
    FlatValidTrace P a (tr1 ++ tr2) <->
    FlatValidTrace P a tr1 /\ FlatValidTrace P a tr2.
Proof.
  intros AbsVal Field Val P a tr1.
  induction tr1 as [|ev tr1 IH]; intros tr2; simpl.
  - split.
    + intro Htrace.
      split; [exact I | exact Htrace].
    + intros [_ Htrace].
      exact Htrace.
  - rewrite IH.
    split.
    + intros [Hev [Htr1 Htr2]].
      split; [split; assumption | exact Htr2].
    + intros [[Hev Htr1] Htr2].
      split; [exact Hev | split; assumption].
Qed.

Lemma valid_trace_read_valid :
  forall {AbsVal Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val) a tr k v
    (Htrace : FlatValidTrace P a tr)
    (Hin : In (FlatERead k v) tr),
    flat_valid_cache P a k v.
Proof.
  intros AbsVal Field Val P a tr.
  induction tr as [|ev tr IH]; intros k v Htrace Hin.
  - contradiction.
  - simpl in Htrace.
    destruct Htrace as [Hev Htr].
    simpl in Hin.
    destruct Hin as [Heq | Hin].
    + subst ev.
      exact Hev.
    + eapply IH; eauto.
Qed.

Lemma valid_trace_write_valid :
  forall {AbsVal Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val) a tr k v
    (Htrace : FlatValidTrace P a tr)
    (Hin : In (FlatEWrite k v) tr),
    flat_valid_cache P a k v.
Proof.
  intros AbsVal Field Val P a tr.
  induction tr as [|ev tr IH]; intros k v Htrace Hin.
  - contradiction.
  - simpl in Htrace.
    destruct Htrace as [Hev Htr].
    simpl in Hin.
    destruct Hin as [Heq | Hin].
    + subst ev.
      exact Hev.
    + eapply IH; eauto.
Qed.

Fixpoint apply_writes {Field Val : Type}
    (field_eq_dec : forall x y : Field, {x = y} + {x <> y})
    (hist : flat_history Field Val)
    (writes : list (flat_cache_event Field Val)) : flat_history Field Val :=
  match writes with
  | [] => hist
  | FlatERead _ _ :: writes' =>
      apply_writes field_eq_dec hist writes'
  | FlatEWrite k v :: writes' =>
      apply_writes field_eq_dec (append_hist field_eq_dec hist k v) writes'
  end.

Lemma apply_valid_writes_preserves_hist_ok :
  forall {AbsVal Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val)
    (field_eq_dec : forall x y : Field, {x = y} + {x <> y})
    hist a writes
    (Hhist : FlatCacheHistOK P hist a)
    (Hwrites : FlatValidTrace P a writes),
    FlatCacheHistOK P (apply_writes field_eq_dec hist writes) a.
Proof.
  intros AbsVal Field Val P field_eq_dec hist a writes.
  revert hist.
  induction writes as [|ev writes IH]; intros hist Hhist Hwrites; simpl.
  - exact Hhist.
  - destruct Hwrites as [Hev Hwrites].
    destruct ev as [k v | k v].
    + apply IH; assumption.
    + apply IH.
      * eapply cache_write_preserves_hist_ok; eauto.
      * exact Hwrites.
Qed.

Definition FlatCacheMethod
    (AbsVal Args Ret Field Val : Type) : Type :=
  AbsVal -> Args -> list (flat_cache_event Field Val) ->
  Ret -> list (flat_cache_event Field Val) -> Prop.

Definition FlatCacheSafeMethod {AbsVal Args Ret Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val)
    (F : AbsVal -> Args -> Ret)
    (m : FlatCacheMethod AbsVal Args Ret Field Val) : Prop :=
  forall a args tr r writes,
    FlatValidTrace P a tr ->
    m a args tr r writes ->
    r = F a args /\ FlatValidTrace P a writes.

Definition FlatSemImm {Obj AbsVal Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val)
    (StableAbs : Obj -> AbsVal -> Prop)
    (o : Obj) (a : AbsVal) (hist : flat_history Field Val) : Prop :=
  StableAbs o a /\ FlatCacheHistOK P hist a.

Theorem cache_safe_preserves_semimm :
  forall {Obj AbsVal Args Ret Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val)
    (field_eq_dec : forall x y : Field, {x = y} + {x <> y})
    (StableAbs : Obj -> AbsVal -> Prop)
    (F : AbsVal -> Args -> Ret)
    (m : FlatCacheMethod AbsVal Args Ret Field Val)
    o a hist args tr r writes
    (Hsem : FlatSemImm P StableAbs o a hist)
    (Hsafe : FlatCacheSafeMethod P F m)
    (Hrun : m a args tr r writes)
    (Htrace : FlatValidTrace P a tr),
    r = F a args /\
    FlatSemImm P StableAbs o a (apply_writes field_eq_dec hist writes).
Proof.
  intros Obj AbsVal Args Ret Field Val P field_eq_dec StableAbs F m
         o a hist args tr r writes Hsem Hsafe Hrun Htrace.
  destruct Hsem as [Hstable Hhist].
  destruct (Hsafe a args tr r writes Htrace Hrun) as [Hresult Hwrites].
  split.
  - exact Hresult.
  - split.
    + exact Hstable.
    + eapply apply_valid_writes_preserves_hist_ok; eauto.
Qed.

Theorem derived_cache_method_sound :
  forall {Obj AbsVal Args Ret Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val)
    (field_eq_dec : forall x y : Field, {x = y} + {x <> y})
    (StableAbs : Obj -> AbsVal -> Prop)
    (F : AbsVal -> Args -> Ret)
    (m : FlatCacheMethod AbsVal Args Ret Field Val)
    o a hist args tr r writes
    (Hsem : FlatSemImm P StableAbs o a hist)
    (Hsafe : FlatCacheSafeMethod P F m)
    (Hrun : m a args tr r writes)
    (Htrace : FlatValidTrace P a tr),
    r = F a args /\
    FlatSemImm P StableAbs o a (apply_writes field_eq_dec hist writes).
Proof.
  intros.
  eapply cache_safe_preserves_semimm; eauto.
Qed.

(** ** Local-Copy Cache Rule *)

Definition local_copy_method {AbsVal Args Ret Field Val : Type}
    (k : Field) (is_hit : Val -> bool) (decode : Val -> Ret)
    (encode : Ret -> Val) (F : AbsVal -> Args -> Ret) :
    FlatCacheMethod AbsVal Args Ret Field Val :=
  fun a args tr r writes =>
    match tr with
    | [] =>
        r = F a args /\
        writes = [FlatEWrite k (encode (F a args))]
    | FlatERead k' v :: _ =>
        k' = k /\
        if is_hit v then
          r = decode v /\ writes = []
        else
          r = F a args /\
          writes = [FlatEWrite k (encode (F a args))]
    | FlatEWrite _ _ :: _ => False
    end.

Record local_copy_conditions {AbsVal Args Ret Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val)
    (F : AbsVal -> Args -> Ret)
    (k : Field) (is_hit : Val -> bool) (decode : Val -> Ret)
    (encode : Ret -> Val) : Prop := {
  lcc_hit_sound :
    forall a args v,
      flat_valid_cache P a k v ->
      is_hit v = true ->
      decode v = F a args;
  lcc_encode_valid :
    forall a args,
      flat_valid_cache P a k (encode (F a args))
}.

Theorem local_copy_cache_safe :
  forall {AbsVal Args Ret Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val)
    (F : AbsVal -> Args -> Ret)
    k is_hit decode encode
    (Hconditions :
      local_copy_conditions P F k is_hit decode encode),
    FlatCacheSafeMethod
      P
      F
      (local_copy_method k is_hit decode encode F).
Proof.
  intros AbsVal Args Ret Field Val P F k is_hit decode encode Hconditions
         a args tr r writes Htrace Hrun.
  destruct Hconditions as [Hhit_sound Hencode_valid].
  destruct tr as [|ev tr'].
  - simpl in Hrun.
    destruct Hrun as [Hr Hwrites].
    subst r writes.
    split; [reflexivity |].
    simpl.
    split.
    + apply Hencode_valid.
    + exact I.
  - destruct ev as [k' v | k' v]; simpl in Hrun; try contradiction.
    simpl in Htrace.
    destruct Htrace as [Hread _].
    destruct Hrun as [Hfield Hbranch].
    subst k'.
    destruct (is_hit v) eqn:Hhit.
    + destruct Hbranch as [Hr Hwrites].
      subst r writes.
      split.
      * apply Hhit_sound; assumption.
      * exact I.
    + destruct Hbranch as [Hr Hwrites].
      subst r writes.
      split; [reflexivity |].
      simpl.
      split.
      * apply Hencode_valid.
      * exact I.
Qed.

(** ** Source-Level Cache Initializers *)

Inductive cache_initializer_event (Field : Type) : Type :=
  | InitReadAbstract : cache_initializer_event Field
  | InitReadArgument : cache_initializer_event Field
  | InitReadCache : Field -> cache_initializer_event Field.

Arguments InitReadAbstract {_}.
Arguments InitReadArgument {_}.
Arguments InitReadCache {_} _.

Definition CacheInitializer
    (AbsVal Args Ret Field : Type) : Type :=
  AbsVal -> Args -> Ret -> list (cache_initializer_event Field) -> Prop.

Definition InitReadsOnlyAbstract {Field : Type}
    (deps : list (cache_initializer_event Field)) : Prop :=
  forall k, ~ In (InitReadCache k) deps.

Record cache_initializer_safe {AbsVal Args Ret Field : Type}
    (init : CacheInitializer AbsVal Args Ret Field)
    (F : AbsVal -> Args -> Ret) : Prop := {
  cis_result_deterministic :
    forall a args r deps,
      init a args r deps ->
      r = F a args;
  cis_reads_only_abstract :
    forall a args r deps,
      init a args r deps ->
      InitReadsOnlyAbstract deps
}.

Definition source_local_copy_method {AbsVal Args Ret Field Val : Type}
    (k : Field) (is_hit : Val -> bool) (decode : Val -> Ret)
    (encode : Ret -> Val)
    (init : CacheInitializer AbsVal Args Ret Field) :
    FlatCacheMethod AbsVal Args Ret Field Val :=
  fun a args tr r writes =>
    match tr with
    | [] =>
        exists deps,
          init a args r deps /\
          writes = [FlatEWrite k (encode r)]
    | FlatERead k' v :: _ =>
        k' = k /\
        if is_hit v then
          r = decode v /\ writes = []
        else
          exists deps,
            init a args r deps /\
            writes = [FlatEWrite k (encode r)]
    | FlatEWrite _ _ :: _ => False
    end.

Record source_local_copy_conditions {AbsVal Args Ret Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val)
    (F : AbsVal -> Args -> Ret)
    (k : Field) (is_hit : Val -> bool) (decode : Val -> Ret)
    (encode : Ret -> Val)
    (init : CacheInitializer AbsVal Args Ret Field) : Prop := {
  slcc_initializer_safe :
    cache_initializer_safe init F;
  slcc_hit_sound :
    forall a args v,
      flat_valid_cache P a k v ->
      is_hit v = true ->
      decode v = F a args;
  slcc_encode_valid :
    forall a args,
      flat_valid_cache P a k (encode (F a args))
}.

Theorem source_local_copy_cache_safe :
  forall {AbsVal Args Ret Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val)
    (F : AbsVal -> Args -> Ret)
    k is_hit decode encode init
    (Hconditions :
      source_local_copy_conditions P F k is_hit decode encode init),
    FlatCacheSafeMethod
      P
      F
      (source_local_copy_method k is_hit decode encode init).
Proof.
  intros AbsVal Args Ret Field Val P F k is_hit decode encode init
         Hconditions a args tr r writes Htrace Hrun.
  destruct Hconditions as [Hinit_safe Hhit_sound Hencode_valid].
  destruct Hinit_safe as [Hinit_result Hinit_abstract].
  destruct tr as [|ev tr'].
  - simpl in Hrun.
    destruct Hrun as [deps [Hinit Hwrites]].
    pose proof (Hinit_abstract a args r deps Hinit) as Hdeps.
    subst writes.
    pose proof (Hinit_result a args r deps Hinit) as Hr.
    subst r.
    split; [reflexivity |].
    simpl.
    split.
    + apply Hencode_valid.
    + exact I.
  - destruct ev as [k' v | k' v]; simpl in Hrun; try contradiction.
    simpl in Htrace.
    destruct Htrace as [Hread _].
    destruct Hrun as [Hfield Hbranch].
    subst k'.
    destruct (is_hit v) eqn:Hhit.
    + destruct Hbranch as [Hr Hwrites].
      subst r writes.
      split.
      * apply Hhit_sound; assumption.
      * exact I.
    + destruct Hbranch as [deps [Hinit Hwrites]].
      pose proof (Hinit_abstract a args r deps Hinit) as Hdeps.
      subst writes.
      pose proof (Hinit_result a args r deps Hinit) as Hr.
      subst r.
      split; [reflexivity |].
      simpl.
      split.
      * apply Hencode_valid.
      * exact I.
Qed.

(** ** Bad Double-Read Counterexample *)

Inductive symbolic_hash_field : Type :=
  | SymbolicHash.

Inductive symbolic_hash_val : Type :=
  | VDefault
  | VDerived.

Definition symbolic_hash_valid
    (_ : unit) (_ : symbolic_hash_field) (v : symbolic_hash_val) : Prop :=
  v = VDefault \/ v = VDerived.

Definition symbolic_hash_protocol :
    FlatCacheProtocol unit symbolic_hash_field symbolic_hash_val.
Proof.
  refine {|
    flat_valid_cache := symbolic_hash_valid;
    flat_default_val := fun _ => VDefault;
    flat_default_valid := _
  |}.
  intros [] [].
  left.
  reflexivity.
Defined.

Definition symbolic_hash_pure (_ : unit) (_ : unit) : symbolic_hash_val :=
  VDerived.

Definition bad_double_read_trace : list (flat_cache_event symbolic_hash_field symbolic_hash_val) :=
  [FlatERead SymbolicHash VDerived; FlatERead SymbolicHash VDefault].

Definition bad_double_read_method :
    FlatCacheMethod unit unit symbolic_hash_val symbolic_hash_field symbolic_hash_val :=
  fun _ _ tr r writes =>
    tr = bad_double_read_trace /\
    r = VDefault /\
    writes = [].

Theorem bad_double_read_counterexample :
  exists a args tr r writes,
    FlatValidTrace symbolic_hash_protocol a tr /\
    bad_double_read_method a args tr r writes /\
    r <> symbolic_hash_pure a args.
Proof.
  exists tt, tt, bad_double_read_trace, VDefault, [].
  split.
  - unfold bad_double_read_trace.
    simpl.
    repeat split; unfold symbolic_hash_valid; auto.
  - split.
    + unfold bad_double_read_method.
      repeat split; reflexivity.
    + unfold symbolic_hash_pure.
      discriminate.
Qed.

Theorem bad_double_read_not_cache_safe :
  ~ FlatCacheSafeMethod
      symbolic_hash_protocol
      symbolic_hash_pure
      bad_double_read_method.
Proof.
  intros Hsafe.
  destruct bad_double_read_counterexample as
    [a [args [tr [r [writes [Htrace [Hrun Hwrong]]]]]]].
  destruct (Hsafe a args tr r writes Htrace Hrun) as [Hresult _].
  apply Hwrong.
  exact Hresult.
Qed.

(** ** Minimal Type-Indexed Semantic Interpretation *)

Inductive core_ty : Type :=
  | CoreTInt
  | CoreTBool
  | CoreTImmObj : class_name -> core_ty.

Inductive core_val : Type :=
  | CoreVInt : nat -> core_val
  | CoreVBool : bool -> core_val
  | CoreVObj : Loc -> core_val.

Definition core_val_interp (T : core_ty) (v : core_val) : Prop :=
  match T, v with
  | CoreTInt, CoreVInt _ => True
  | CoreTBool, CoreVBool _ => True
  | CoreTImmObj _, CoreVObj _ => True
  | _, _ => False
  end.

Definition core_env_interp (Γ : list core_ty) (ρ : list core_val) : Prop :=
  Forall2 core_val_interp Γ ρ.

Record cache_method_spec (AbsVal Args Field Val : Type) : Type := {
  cms_field : Field;
  cms_ret_ty : core_ty;
  cms_is_hit : Val -> bool;
  cms_decode : Val -> core_val;
  cms_encode : core_val -> Val;
  cms_pure : AbsVal -> Args -> core_val
}.

Arguments cms_field {_ _ _ _} _.
Arguments cms_ret_ty {_ _ _ _} _.
Arguments cms_is_hit {_ _ _ _} _ _.
Arguments cms_decode {_ _ _ _} _ _.
Arguments cms_encode {_ _ _ _} _ _.
Arguments cms_pure {_ _ _ _} _ _ _.

Definition cache_method_of_spec {AbsVal Args Field Val : Type}
    (spec : cache_method_spec AbsVal Args Field Val) :
    FlatCacheMethod AbsVal Args core_val Field Val :=
  local_copy_method
    (cms_field spec)
    (cms_is_hit spec)
    (cms_decode spec)
    (cms_encode spec)
    (cms_pure spec).

Record cache_method_typing {AbsVal Args Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val)
    (spec : cache_method_spec AbsVal Args Field Val) : Prop := {
  cmt_pure_typed :
    forall a args, core_val_interp (cms_ret_ty spec) (cms_pure spec a args);
  cmt_decode_typed :
    forall v,
      cms_is_hit spec v = true ->
      core_val_interp (cms_ret_ty spec) (cms_decode spec v);
  cmt_hit_sound :
    forall a args v,
      flat_valid_cache P a (cms_field spec) v ->
      cms_is_hit spec v = true ->
      cms_decode spec v = cms_pure spec a args;
  cmt_encode_valid :
    forall a args,
      flat_valid_cache P a (cms_field spec) (cms_encode spec (cms_pure spec a args))
}.

Definition cache_stmt_typing {AbsVal Args Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val)
    (spec : cache_method_spec AbsVal Args Field Val)
    (m : FlatCacheMethod AbsVal Args core_val Field Val) : Prop :=
  m = cache_method_of_spec spec /\ cache_method_typing P spec.

Definition source_cache_method_of_spec {AbsVal Args Field Val : Type}
    (spec : cache_method_spec AbsVal Args Field Val)
    (init : CacheInitializer AbsVal Args core_val Field) :
    FlatCacheMethod AbsVal Args core_val Field Val :=
  source_local_copy_method
    (cms_field spec)
    (cms_is_hit spec)
    (cms_decode spec)
    (cms_encode spec)
    init.

Record source_cache_method_typing {AbsVal Args Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val)
    (spec : cache_method_spec AbsVal Args Field Val)
    (init : CacheInitializer AbsVal Args core_val Field)
    (m : FlatCacheMethod AbsVal Args core_val Field Val) : Prop := {
  scmt_method_shape :
    m = source_cache_method_of_spec spec init;
  scmt_initializer_safe :
    cache_initializer_safe init (cms_pure spec);
  scmt_pure_typed :
    forall a args, core_val_interp (cms_ret_ty spec) (cms_pure spec a args);
  scmt_decode_typed :
    forall v,
      cms_is_hit spec v = true ->
      core_val_interp (cms_ret_ty spec) (cms_decode spec v);
  scmt_hit_sound :
    forall a args v,
      flat_valid_cache P a (cms_field spec) v ->
      cms_is_hit spec v = true ->
      cms_decode spec v = cms_pure spec a args;
  scmt_encode_valid :
    forall a args,
      flat_valid_cache P a (cms_field spec) (cms_encode spec (cms_pure spec a args))
}.

Definition semantic_cache_stmt {AbsVal Args Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val)
    (spec : cache_method_spec AbsVal Args Field Val)
    (m : FlatCacheMethod AbsVal Args core_val Field Val) : Prop :=
  FlatCacheSafeMethod P (cms_pure spec) m.

Theorem cache_stmt_fundamental :
  forall {AbsVal Args Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val)
    (spec : cache_method_spec AbsVal Args Field Val)
    (m : FlatCacheMethod AbsVal Args core_val Field Val)
    (Htyping : cache_stmt_typing P spec m),
    semantic_cache_stmt P spec m.
Proof.
  intros AbsVal Args Field Val P spec m [Hm Htyped].
  subst m.
  destruct Htyped as [_ _ Hhit_sound Hencode_valid].
  unfold semantic_cache_stmt, cache_method_of_spec.
  apply local_copy_cache_safe.
  constructor.
  - intros a args v Hvalid Hhit.
    eapply Hhit_sound; eauto.
  - intros a args.
    apply Hencode_valid.
Qed.

Theorem source_cache_stmt_fundamental :
  forall {AbsVal Args Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val)
    (spec : cache_method_spec AbsVal Args Field Val)
    (init : CacheInitializer AbsVal Args core_val Field)
    (m : FlatCacheMethod AbsVal Args core_val Field Val)
    (Htyping : source_cache_method_typing P spec init m),
    semantic_cache_stmt P spec m.
Proof.
  intros AbsVal Args Field Val P spec init m Htyping.
  destruct Htyping as
    [Hshape Hinit_safe _ _ Hhit_sound Hencode_valid].
  subst m.
  unfold semantic_cache_stmt, source_cache_method_of_spec.
  apply source_local_copy_cache_safe.
  constructor.
  - exact Hinit_safe.
  - intros a args v Hvalid Hhit.
    eapply Hhit_sound; eauto.
  - intros a args.
    apply Hencode_valid.
Qed.

Corollary typed_cache_method_implies_cache_safe :
  forall {AbsVal Args Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val)
    (spec : cache_method_spec AbsVal Args Field Val)
    (m : FlatCacheMethod AbsVal Args core_val Field Val)
    (Htyping : cache_stmt_typing P spec m),
    FlatCacheSafeMethod P (cms_pure spec) m.
Proof.
  intros.
  eapply cache_stmt_fundamental; eauto.
Qed.

Corollary source_typed_cache_method_implies_cache_safe :
  forall {AbsVal Args Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val)
    (spec : cache_method_spec AbsVal Args Field Val)
    (init : CacheInitializer AbsVal Args core_val Field)
    (m : FlatCacheMethod AbsVal Args core_val Field Val)
    (Htyping : source_cache_method_typing P spec init m),
    FlatCacheSafeMethod P (cms_pure spec) m.
Proof.
  intros.
  eapply source_cache_stmt_fundamental; eauto.
Qed.

Theorem typed_cache_method_semantic_immutability :
  forall {Obj AbsVal Args Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val)
    (field_eq_dec : forall x y : Field, {x = y} + {x <> y})
    (StableAbs : Obj -> AbsVal -> Prop)
    (spec : cache_method_spec AbsVal Args Field Val)
    (m : FlatCacheMethod AbsVal Args core_val Field Val)
    o a hist args tr r writes
    (Htyping : cache_stmt_typing P spec m)
    (Hsem : FlatSemImm P StableAbs o a hist)
    (Hrun : m a args tr r writes)
    (Htrace : FlatValidTrace P a tr),
    r = cms_pure spec a args /\
    FlatSemImm P StableAbs o a (apply_writes field_eq_dec hist writes).
Proof.
  intros Obj AbsVal Args Field Val P field_eq_dec StableAbs spec m
         o a hist args tr r writes Htyping Hsem Hrun Htrace.
  eapply cache_safe_preserves_semimm; eauto.
  eapply typed_cache_method_implies_cache_safe.
  exact Htyping.
Qed.

Theorem source_typed_cache_method_semantic_immutability :
  forall {Obj AbsVal Args Field Val : Type}
    (P : FlatCacheProtocol AbsVal Field Val)
    (field_eq_dec : forall x y : Field, {x = y} + {x <> y})
    (StableAbs : Obj -> AbsVal -> Prop)
    (spec : cache_method_spec AbsVal Args Field Val)
    (init : CacheInitializer AbsVal Args core_val Field)
    (m : FlatCacheMethod AbsVal Args core_val Field Val)
    o a hist args tr r writes
    (Htyping : source_cache_method_typing P spec init m)
    (Hsem : FlatSemImm P StableAbs o a hist)
    (Hrun : m a args tr r writes)
    (Htrace : FlatValidTrace P a tr),
    r = cms_pure spec a args /\
    FlatSemImm P StableAbs o a (apply_writes field_eq_dec hist writes).
Proof.
  intros Obj AbsVal Args Field Val P field_eq_dec StableAbs spec init m
         o a hist args tr r writes Htyping Hsem Hrun Htrace.
  eapply cache_safe_preserves_semimm; eauto.
  eapply source_typed_cache_method_implies_cache_safe.
  exact Htyping.
Qed.
