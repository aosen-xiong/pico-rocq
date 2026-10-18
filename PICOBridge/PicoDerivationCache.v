From Stdlib Require Import List Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping Bigstep Properties Preservation.
Require Import Reachability LiveCapabilityStack DerivedCache.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoCacheTyping
  PICOBridge.PicoDerivationNoninterference.

(** * Cache Protocols Defined by Derivation Methods

    [DerivedCache] parameterizes its protocol by a Rocq function
    [derived : list value -> nat] and asks every cache write to prove
    [n = derived abs_vals].  Here the protocol is instead defined by a PICO
    derivation method: a cache value is valid when it is empty ([Int 0]) or
    is what the derivation method returns on the receiver.  Noninterference
    and stability ([PicoDerivationNoninterference]) show that this set of
    valid values is well defined and never changes, so writing the
    derivation's own result needs no separate correctness premise. *)

(** ** Derived values and the protocol *)

(** Invoking method [m] on receiver [o] in heap [h] returns [v].  The method
    is the one dynamic dispatch selects for [o]'s runtime class, run with no
    arguments; a derivation leaves the heap unchanged. *)
Definition derived_by (CT : class_table) (m : method_name) (h : heap)
    (o : Loc) (v : value) : Prop :=
  exists cy mdef rΓ',
    r_basetype h o = Some cy /\
    FindMethodWithName CT cy m mdef /\
    eval_stmt CT (mkr_env [Iot o]) h (mbody_stmt (mbody mdef)) OK rΓ' h /\
    runtime_getVal rΓ' (mreturn (mbody mdef)) = Some v.

Definition derivation_cache_value (CT : class_table) (m : method_name)
    (h : heap) (o : Loc) (v : value) : Prop :=
  v = Int 0 \/ derived_by CT m h o v.

Definition derivation_cache_protocol (CT : class_table) (m : method_name)
    (h : heap) (o : Loc) (cache_f : var) : Prop :=
  exists v,
    field_read h o cache_f v /\
    derivation_cache_value CT m h o v.

(** The derivation of [m] on [o] is well behaved in [h]: dispatch selects a
    parameterless method from the derivation table [D], and the method's
    entry frame is well formed. *)
Definition derivation_ready (CT : class_table) (D : method_def -> Prop)
    (m : method_name) (h : heap) (o : Loc) : Prop :=
  exists cy mdef,
    r_basetype h o = Some cy /\
    FindMethodWithName CT cy m mdef /\
    D mdef /\
    mparams (msignature mdef) = [] /\
    wf_r_config CT [mreceiver (msignature mdef)] (mkr_env [Iot o]) h.

(** ** Auxiliary facts *)

Lemma derivation_ready_body :
  forall CT D m h o cy mdef,
    derivation_table CT D ->
    derivation_ready CT D m h o ->
    r_basetype h o = Some cy ->
    FindMethodWithName CT cy m mdef ->
    exists sΓd',
      deriv_stmt CT D [mreceiver (msignature mdef)]
        (mbody_stmt (mbody mdef)) sΓd' /\
      stmt_typing CT [mreceiver (msignature mdef)]
        (mscope (msignature mdef)) (mbody_stmt (mbody mdef)) sΓd' /\
      wf_r_config CT [mreceiver (msignature mdef)] (mkr_env [Iot o]) h.
Proof.
  intros CT D m h o cy mdef Htable
    [cy' [mdef' [Hbase' [Hfind' [HD [Hparams Hwf]]]]]] Hbase Hfind.
  assert (cy' = cy) by congruence. subst cy'.
  have Hmdef := find_method_with_name_deterministic CT cy m mdef' mdef
    Hfind' Hfind.
  subst mdef'.
  destruct (Htable mdef HD) as [sΓd Hderiv].
  rewrite Hparams in Hderiv.
  have Hwf_copy := Hwf.
  destruct Hwf_copy as [Hct [Hheap _]].
  have Hdom := r_basetype_in_dom CT h o cy Hheap Hbase.
  destruct (method_body_well_typed_by_find CT cy m mdef Hct Hdom Hfind)
    as [sΓt Htyping].
  rewrite Hparams in Htyping.
  have Hsame := deriv_stmt_typing_env CT D _ _ _ _ _ Hderiv Htyping.
  subst sΓd.
  exists sΓt. split; [exact Hderiv | split; [exact Htyping | exact Hwf]].
Qed.

Lemma receiver_frame_public :
  forall CT h o,
    o < dom h ->
    env_in (reachable_abs CT h o) (mkr_env [Iot o]).
Proof.
  intros CT h o Hdom x l Hx.
  destruct x as [| x]; simpl in Hx.
  - injection Hx as <-. apply reachable_abs_heap. exact Hdom.
  - destruct x; discriminate.
Qed.

Lemma r_basetype_dom :
  forall h o cy,
    r_basetype h o = Some cy ->
    o < dom h.
Proof.
  intros h o cy Hbase.
  unfold r_basetype in Hbase.
  destruct (runtime_getObj h o) as [obj |] eqn:Hobj; [| discriminate].
  exact (runtime_getObj_dom o obj h Hobj).
Qed.

(** Abstract-state reachability is closed under abstract-field edges. *)
Lemma reachable_abs_abstract_field_closed :
  forall CT h root l rt fs f l',
    wf_heap CT h ->
    reachable_abs CT h root l ->
    runtime_getObj h l = Some (mkObj rt fs) ->
    abstract_field CT (rctype rt) f ->
    getVal fs f = Some (Iot l') ->
    reachable_abs CT h root l'.
Proof.
  intros CT h root l rt fs f l' Hheap Hreach Hobj [Hmut Hassign] Hfield.
  destruct rt as [q C]. simpl in Hmut, Hassign.
  eapply reachable_abs_trans; [exact Hreach |].
  eapply reachable_abs_step;
    [| exact Hobj | exact Hfield | exact Hmut | exact Hassign].
  eapply wf_heap_field_location_dom; [exact Hheap | exact Hobj | exact Hfield].
Qed.

(** ** Transport of derived values

    A derived value survives any heap change that preserves the abstract
    state reachable from the receiver and its runtime class, and it is the
    only value the derivation can return afterwards. *)
Lemma derived_by_transport :
  forall CT D m h h' o w,
    derivation_table CT D ->
    derivation_ready CT D m h o ->
    abs_agree CT (reachable_abs CT h o) h h' ->
    r_basetype h' o = r_basetype h o ->
    derived_by CT m h o w ->
    derived_by CT m h' o w /\
    (forall w', derived_by CT m h' o w' -> w' = w).
Proof.
  intros CT D m h h' o w Htable Hready Hagree Hbase_eq
    [cy [mdef [rΓd [Hbase [Hfind [Hrun Hret]]]]]].
  destruct (derivation_ready_body CT D m h o cy mdef Htable Hready Hbase Hfind)
    as [sΓd [Hderiv [Htyping Hwf]]].
  have Hpub := receiver_frame_public CT h o (r_basetype_dom h o cy Hbase).
  destruct (derivation_simulation CT D Htable (mkr_env [Iot o]) h _ OK rΓd h
    Hrun _ _ _ h' _ Hderiv Htyping Hwf Hagree Hpub) as (_ & Hrun' & _).
  split.
  - exists cy, mdef, rΓd.
    repeat split; [congruence | exact Hfind | exact Hrun' | exact Hret].
  - intros w' [cy2 [mdef2 [rΓ2 [Hbase2 [Hfind2 [Hrun2 Hret2]]]]]].
    assert (cy2 = cy) by congruence. subst cy2.
    have Hmdef := find_method_with_name_deterministic CT cy m mdef2 mdef
      Hfind2 Hfind.
    subst mdef2.
    destruct (derivation_noninterference CT D Htable (mkr_env [Iot o]) h _ OK
      rΓd h Hrun _ _ _ h' _ OK rΓ2 h' Hderiv Htyping Hwf Hagree Hpub Hrun2)
      as (_ & Henv & _).
    subst rΓ2. congruence.
Qed.

(** ** Stability under PICO execution

    For an immutable receiver, every value that is valid before a
    well-typed statement is still valid afterwards, the derivation can only
    return the same value afterwards, and the derivation stays well behaved.
    So the set of valid cache values never changes. *)
Theorem derivation_cache_value_stable :
  forall CT D m sΓ mt rΓ h s rΓ' h' sΓ' o C0 vals0,
    derivation_table CT D ->
    runtime_getObj h o = Some (mkObj (mkruntime_type Imm_r C0) vals0) ->
    derivation_ready CT D m h o ->
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ mt s sΓ' ->
    eval_stmt CT rΓ h s OK rΓ' h' ->
    derivation_ready CT D m h' o /\
    (forall v, derivation_cache_value CT m h o v ->
               derivation_cache_value CT m h' o v) /\
    (forall v v', derived_by CT m h o v -> derived_by CT m h' o v' -> v' = v).
Proof.
  intros CT D m sΓ mt rΓ h s rΓ' h' sΓ' o C0 vals0 Htable Hroot Hready
    Hwf Htyping Heval.
  have Hagree := abstract_state_agreement_preserved CT sΓ mt rΓ h s rΓ' h' sΓ'
    o C0 vals0 Hroot Hwf Htyping Heval.
  destruct (runtime_preserves_r_type_heap CT rΓ h o (mkruntime_type Imm_r C0)
    h' vals0 s rΓ' Hroot Heval) as [vals0' Hroot'].
  have Hbase_eq : r_basetype h' o = r_basetype h o.
  { unfold r_basetype. rewrite Hroot. rewrite Hroot'. reflexivity. }
  split; [| split].
  - (* the entry frame stays well formed in the later heap *)
    destruct Hready as [cy [mdef [Hbase [Hfind [HD [Hparams Hfwf]]]]]].
    exists cy, mdef.
    split; [congruence |].
    split; [assumption |].
    split; [assumption |].
    split; [assumption |].
    have Hpost := preservation_pico CT sΓ mt rΓ h s rΓ' h' sΓ' Hwf Htyping
      Heval.
    destruct Hpost as [_ [Hheap' _]].
    eapply wf_r_config_preserved_by_runtime_types; [exact Hfwf | exact Hheap' |].
    split.
    + exact (eval_stmt_preserves_heap_domain_simple CT rΓ h s rΓ' h' Heval).
    + intros l Hl.
      destruct (runtime_getObj_Some h l Hl) as [rt [fs Hobj]].
      destruct (runtime_preserves_r_type_heap CT rΓ h l rt h' fs s rΓ' Hobj
        Heval) as [fs' Hobj'].
      unfold r_type. rewrite Hobj. rewrite Hobj'. reflexivity.
  - intros v [Hempty | Hderived].
    + left. exact Hempty.
    + right.
      exact (proj1 (derived_by_transport CT D m h h' o v Htable Hready Hagree
        Hbase_eq Hderived)).
  - intros v v' Hderived Hderived'.
    exact (proj2 (derived_by_transport CT D m h h' o v Htable Hready Hagree
      Hbase_eq Hderived) v' Hderived').
Qed.

(** ** Writing the derived value

    Cache fields are [Assignable], so they are never abstract fields.  A cache
    write therefore leaves the abstract state reachable from the receiver
    unchanged, and writing the derivation's own result keeps the protocol
    with no premise about which value was computed. *)

Lemma cache_field_not_abstract :
  forall CT C f,
    cache_field CT C f ->
    ~ abstract_field CT C f.
Proof.
  intros CT C f Hcache [_ Hassign].
  unfold cache_field in Hcache.
  destruct Hassign as [Hrda | Hfinal].
  - have Heq := sf_assignability_deterministic_rel CT C f _ _ Hcache Hrda.
    discriminate.
  - have Heq := sf_assignability_deterministic_rel CT C f _ _ Hcache Hfinal.
    discriminate.
Qed.

Lemma abs_agree_cache_write :
  forall CT h o rt0 fs0 cache_f v,
    wf_heap CT h ->
    runtime_getObj h o = Some (mkObj rt0 fs0) ->
    cache_field CT (rctype rt0) cache_f ->
    abs_agree CT (reachable_abs CT h o) h (update_field h o cache_f v).
Proof.
  intros CT h o rt0 fs0 cache_f v Hheap Hobj0 Hcache l Hreach.
  have Hdom := reachable_abs_target_dom CT h o l Hreach.
  destruct (runtime_getObj_Some h l Hdom) as [rt [fs Hobj]].
  have Ho_dom := runtime_getObj_dom o (mkObj rt0 fs0) h Hobj0.
  destruct (Nat.eq_dec l o) as [-> | Hneq].
  - rewrite Hobj0 in Hobj. injection Hobj as <- <-.
    exists rt0, fs0, (update cache_f v fs0).
    split; [exact Hobj0 |].
    split.
    + unfold update_field. rewrite Hobj0.
      apply runtime_getObj_update_same. exact Ho_dom.
    + intros f Habs.
      split.
      * have Hneq_f : cache_f <> f.
        { intros ->. exact (cache_field_not_abstract CT _ f Hcache Habs). }
        unfold getVal. symmetry. apply update_diff. exact Hneq_f.
      * intros l' Hl'.
        exact (reachable_abs_abstract_field_closed CT h o o rt0 fs0 f l'
          Hheap Hreach Hobj0 Habs Hl').
  - exists rt, fs, fs.
    split; [exact Hobj |].
    split.
    + unfold update_field. rewrite Hobj0.
      rewrite runtime_getObj_update_diff.
      * intros Heq. apply Hneq. symmetry. exact Heq.
      * exact Hobj.
    + intros f Habs.
      split; [reflexivity |].
      intros l' Hl'.
      exact (reachable_abs_abstract_field_closed CT h o l rt fs f l'
        Hheap Hreach Hobj Habs Hl').
Qed.

Theorem derived_cache_write_sound :
  forall CT D m h o C0 vals0 cache_f v_old v,
    derivation_table CT D ->
    runtime_getObj h o = Some (mkObj (mkruntime_type Imm_r C0) vals0) ->
    derivation_ready CT D m h o ->
    cache_field CT C0 cache_f ->
    field_read h o cache_f v_old ->
    derived_by CT m h o v ->
    derivation_cache_protocol CT m (update_field h o cache_f v) o cache_f /\
    (forall w, derivation_cache_value CT m h o w ->
               derivation_cache_value CT m (update_field h o cache_f v) o w) /\
    (forall w w', derived_by CT m h o w ->
                  derived_by CT m (update_field h o cache_f v) o w' -> w' = w).
Proof.
  intros CT D m h o C0 vals0 cache_f v_old v Htable Hroot Hready Hcache
    [obj [Hobj Hold]] Hderived.
  rewrite Hroot in Hobj. injection Hobj as <-.
  simpl in Hold.
  have Hheap : wf_heap CT h.
  { destruct Hready as [cy [mdef [_ [_ [_ [_ Hfwf]]]]]].
    destruct Hfwf as [_ [Hheap _]]. exact Hheap. }
  have Hagree := abs_agree_cache_write CT h o (mkruntime_type Imm_r C0) vals0
    cache_f v Hheap Hroot Hcache.
  have Ho_dom := runtime_getObj_dom o _ h Hroot.
  have Hobj' : runtime_getObj (update_field h o cache_f v) o =
    Some (mkObj (mkruntime_type Imm_r C0) (update cache_f v vals0)).
  { unfold update_field. rewrite Hroot.
    apply runtime_getObj_update_same. exact Ho_dom. }
  have Hbase_eq :
    r_basetype (update_field h o cache_f v) o = r_basetype h o.
  { unfold r_basetype. rewrite Hobj'. rewrite Hroot. reflexivity. }
  split; [| split].
  - exists v. split.
    + exists (mkObj (mkruntime_type Imm_r C0) (update cache_f v vals0)).
      split; [exact Hobj' |].
      simpl. unfold getVal. apply update_same.
      eapply getVal_dom. exact Hold.
    + right.
      exact (proj1 (derived_by_transport CT D m h _ o v Htable Hready Hagree
        Hbase_eq Hderived)).
  - intros w [Hempty | Hw].
    + left. exact Hempty.
    + right.
      exact (proj1 (derived_by_transport CT D m h _ o w Htable Hready Hagree
        Hbase_eq Hw)).
  - intros w w' Hw Hw'.
    exact (proj2 (derived_by_transport CT D m h _ o w Htable Hready Hagree
      Hbase_eq Hw) w' Hw').
Qed.

(** ** The cache update, without a correctness premise

    Operational counterpart of [DerivedCache.derived_cache_update_sequence_sound]:
    the update calls the derivation method and stores its result,
    [tmp = recv.m(); recv.cache_f = tmp].  Unlike the original theorem, there
    is no premise [n = derived abs_vals]: the stored value is valid because it
    is what the derivation returned. *)
Theorem derived_cache_update_sequence_sound_by_derivation :
  forall CT D m rΓ h h' recv tmp cache_f o C0 vals0 rΓ_out,
    derivation_table CT D ->
    runtime_getVal rΓ recv = Some (Iot o) ->
    recv <> tmp ->
    runtime_getObj h o = Some (mkObj (mkruntime_type Imm_r C0) vals0) ->
    derivation_ready CT D m h o ->
    cache_field CT C0 cache_f ->
    eval_stmt CT rΓ h
      (SSeq (SCall tmp m recv []) (SFldWrite recv cache_f tmp))
      OK rΓ_out h' ->
    derivation_cache_protocol CT m h' o cache_f /\
    (forall w, derivation_cache_value CT m h o w ->
               derivation_cache_value CT m h' o w) /\
    (forall w w', derived_by CT m h o w -> derived_by CT m h' o w' -> w' = w).
Proof.
  intros CT D m rΓ h h' recv tmp cache_f o C0 vals0 rΓ_out Htable Hrecv
    Hneq Hroot Hready Hcache Hrun.
  inversion Hrun; subst; try discriminate.
  (* the call *)
  inversion Heval1; subst; try discriminate.
  destruct Hfind as [Hfind_m Hbody_eq]. subst.
  assert (ly = o) by congruence. subst ly.
  simpl in Hargs. injection Hargs as <-.
  (* the derivation body leaves the heap unchanged *)
  destruct (derivation_ready_body CT D m h o cy mdef Htable Hready Hbase
    Hfind_m) as [sΓd [Hderiv [Htyping Hfwf]]].
  have Hheap : wf_heap CT h by (destruct Hfwf as [_ [Hheap _]]; exact Hheap).
  have Hrefl : abs_agree CT (reachable_abs CT h o) h h.
  { intros l Hreach.
    have Hdom := reachable_abs_target_dom CT h o l Hreach.
    destruct (runtime_getObj_Some h l Hdom) as [rt [fs Hobj]].
    exists rt, fs, fs.
    repeat split; try assumption.
    intros l' Hl'.
    eapply reachable_abs_abstract_field_closed; eassumption. }
  have Hpub := receiver_frame_public CT h o (r_basetype_dom h o cy Hbase).
  destruct (derivation_simulation CT D Htable (mkr_env [Iot o]) h _ OK rΓ'' h'0
    Heval_body _ _ _ h _ Hderiv Htyping Hfwf Hrefl Hpub) as (Hh & _ & _).
  subst h'0.
  have Hderived : derived_by CT m h o retval.
  { exists cy, mdef, rΓ''. repeat split; assumption. }
  (* the write stores the returned value into the receiver's cache field *)
  have Hrecv_after :
    runtime_getVal (set_vars rΓ (update tmp retval (vars rΓ))) recv =
    Some (Iot o).
  { unfold runtime_getVal in *. simpl.
    rewrite update_diff;
      [intros Heq; apply Hneq; symmetry; exact Heq | exact Hrecv]. }
  have Htmp_after :
    forall w,
      runtime_getVal (set_vars rΓ (update tmp retval (vars rΓ))) tmp = Some w ->
      w = retval.
  { intros w Hw. unfold runtime_getVal in Hw. simpl in Hw.
    destruct (Nat.lt_ge_cases tmp (length (vars rΓ))) as [Hlt | Hge].
    - rewrite (update_same _ tmp retval (vars rΓ) Hlt) in Hw. congruence.
    - exfalso.
      assert (Hnone : nth_error (update tmp retval (vars rΓ)) tmp = None).
      { apply nth_error_None. rewrite update_length. exact Hge. }
      rewrite Hnone in Hw. discriminate. }
  inversion Heval2; subst.
  match goal with
  | Hx : runtime_getVal (set_vars rΓ _) recv = Some (Iot ?lx) |- _ =>
      rewrite Hrecv_after in Hx; injection Hx as <-
  end.
  match goal with
  | Hy : runtime_getVal (set_vars rΓ _) tmp = Some ?vy |- _ =>
      have Hvy := Htmp_after vy Hy; subst vy
  end.
  match goal with
  | Ho : runtime_getObj h o = Some ?obj,
    Hf : getVal (fields_map ?obj) cache_f = Some ?vf |- _ =>
      rewrite Hroot in Ho; injection Ho as <-;
      exact (derived_cache_write_sound CT D m h o C0 vals0 cache_f vf retval
        Htable Hroot Hready Hcache
        (ex_intro _ (mkObj (mkruntime_type Imm_r C0) vals0) (conj Hroot Hf))
        Hderived)
  end.
Qed.
