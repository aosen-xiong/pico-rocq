From Stdlib Require Import List Lia PeanoNat FunctionalExtensionality.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import ownp.
Import ListNotations.

Require Import Syntax Helpers Subtyping Typing Bigstep Core.GenericCacheProtocol
  Core.GenericDerivedCache Examples.PicoIfZeroCacheExamples.
Require Import Iris.GenericCacheGhostState.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage
  PICOBridge.PicoIrisCoreInvariant PICOBridge.PicoIrisSemImmOperations
  PICOBridge.PicoIrisSemImmLogicalRelation PICOBridge.PicoIrisSemanticAPI
  PICOBridge.PicoCacheTyping.
Require Import Reachability PICOBridge.PicoDerivationNoninterference
  PICOBridge.PicoDerivationCache.
Require DerivedCache.
Require Import Examples.PicoSemanticCacheAPIExamples.

(** * A Concrete Non-Vacuous Hash-Cache Provider *)

Definition pico_hash_cache_addr (receiver : Loc) : FieldAddr :=
  (receiver, hash_cache_field).

Definition pico_hash_cache_adapter
    (receiver : Loc) : PicoCoreCacheAdapter hash_cache_protocol.
Proof.
  refine (@Build_PicoCoreCacheAdapter nat hash_cache_protocol
    (fun addr =>
      if field_addr_eqb addr (pico_hash_cache_addr receiver)
      then Some HashField else None)
    (fun _ v => Some v)).
Defined.

Lemma field_addr_eqb_eq : forall a b,
  field_addr_eqb a b = true <-> a = b.
Proof.
  intros [l f] [l' f']. unfold field_addr_eqb; simpl.
  split.
  - intros H. apply Bool.andb_true_iff in H. destruct H as [Hl Hf].
    apply Nat.eqb_eq in Hl. apply Nat.eqb_eq in Hf. subst. reflexivity.
  - intros H. inversion H; subst. rewrite !Nat.eqb_refl. reflexivity.
Qed.

Lemma pico_hash_cache_adapter_some : forall receiver addr k,
  pico_core_cache_field hash_cache_protocol
    (pico_hash_cache_adapter receiver) addr = Some k ->
  addr = pico_hash_cache_addr receiver /\ k = HashField.
Proof.
  intros receiver addr k Hfield.
  unfold pico_hash_cache_adapter in Hfield; simpl in Hfield.
  destruct (field_addr_eqb addr (pico_hash_cache_addr receiver)) eqn:Heq;
    [|discriminate].
  apply field_addr_eqb_eq in Heq. split; [exact Heq | congruence].
Qed.

Lemma pico_concrete_hash_adapter_at : forall receiver,
  pico_core_cache_field hash_cache_protocol
    (pico_hash_cache_adapter receiver) (receiver, hash_cache_field) =
  Some HashField.
Proof.
  intros receiver. unfold pico_hash_cache_adapter; simpl.
  assert (Heq : field_addr_eqb (receiver, hash_cache_field)
      (pico_hash_cache_addr receiver) = true).
  { apply (proj2 (field_addr_eqb_eq _ _)). reflexivity. }
  rewrite Heq. reflexivity.
Qed.

Lemma pico_concrete_hash_value_adapter : forall receiver v,
  pico_core_cache_value hash_cache_protocol
    (pico_hash_cache_adapter receiver) HashField v = Some v.
Proof. reflexivity. Qed.

Theorem pico_concrete_hash_value_adapter_api : forall receiver,
  PicoHashCacheValueAdapter (pico_hash_cache_adapter receiver).
Proof. intros receiver v. apply pico_concrete_hash_value_adapter. Qed.


(** The provider's abstract hash is defined by a PICO derivation method [m],
    not by a Rocq function on field values.  The provider fixes a reference
    heap [h0] in which [m] returns [Int hash_value] on [receiver].  Every
    later state agrees with [h0] on the receiver's abstract footprint, the
    abstract fields of objects reachable from [receiver] along abstract
    fields.  Noninterference ([derived_by_transport]) then shows that [m]
    still returns exactly [Int hash_value] in every such state. *)

Definition pico_hash_snapshot (receiver : Loc) (state : pico_core_state) :
    CacheHistorySnapshot hash_cache_protocol :=
  fun _ => values_written_to (pcs_weak state) (pico_hash_cache_addr receiver).

Definition pico_hash_abstract_field
    (CT : class_table) (h0 : heap) (receiver : Loc) (addr : FieldAddr) : Prop :=
  reachable_abs CT h0 receiver (fst addr) /\
  exists rt fs,
    runtime_getObj h0 (fst addr) = Some (mkObj rt fs) /\
    abstract_field CT (rctype rt) (snd addr).

(** The abstract hash the provider exposes.  Its connection to the heap is
    [pico_concrete_hash_provider_represents_heap]. *)
Definition pico_hash_object (hash_value : nat) (_ : pico_core_state) : nat :=
  hash_value.

(** Every weak history in the footprint holds only the reference heap's
    value, and is nonempty.  Field reads of the footprint therefore return
    the reference value. *)
Definition pico_hash_footprint_histories
    (CT : class_table) (h0 : heap) (receiver : Loc) (sigma : wm_state) : Prop :=
  forall l f v0,
    pico_hash_abstract_field CT h0 receiver (l, f) ->
    DerivedCache.field_read h0 l f v0 ->
    values_written_to sigma (l, f) <> @nil value /\
    forall v, List.In v (values_written_to sigma (l, f)) -> v = v0.

Definition pico_hash_provider_inv
    (CT : class_table) (receiver : Loc) (m : method_name) (h0 : heap)
    (hash_value : nat) (state : pico_core_state) : Prop :=
  heap_wm_type_agree (pcs_heap state) (pcs_weak state) /\
  ((exists D, derivation_table CT D /\ derivation_ready CT D m h0 receiver) /\
   derived_by CT m h0 receiver (Int hash_value) /\
   abs_agree CT (reachable_abs CT h0 receiver) h0 (pcs_heap state) /\
   pico_hash_footprint_histories CT h0 receiver (pcs_weak state) /\
   (exists rt0 fs0,
     runtime_getObj h0 receiver = Some (mkObj rt0 fs0) /\
     derived_cache_field CT (rctype rt0) hash_cache_field)) /\
  CacheHistSnapshotOK hash_cache_protocol
    (pico_hash_snapshot receiver state) hash_value.

Lemma pico_hash_snapshot_valid_append : forall receiver hash_value state v,
  CacheHistSnapshotOK hash_cache_protocol
    (pico_hash_snapshot receiver state) hash_value ->
  hash_cache_valid hash_value HashField v ->
  CacheHistSnapshotOK hash_cache_protocol
    (fun _ => pico_hash_snapshot receiver state HashField ++ [v]) hash_value.
Proof.
  intros receiver hash_value state v Hok Hvalid [] value Hin.
  apply in_app_or in Hin. destruct Hin as [Hin | [<- | []]].
  - exact (Hok HashField value Hin).
  - exact Hvalid.
Qed.

Lemma runtime_getObj_update_field_other_general : forall h loc f v receiver,
  loc <> receiver ->
  runtime_getObj (update_field h loc f v) receiver = runtime_getObj h receiver.
Proof.
  intros h loc f v receiver Hneq. unfold update_field.
  destruct (runtime_getObj h loc) as [o |] eqn:Hloc; [|reflexivity].
  unfold runtime_getObj. apply update_diff. exact Hneq.
Qed.

(** ** Agreement with the reference heap *)

(** A write outside the footprint keeps agreement with the reference heap. *)
Lemma abs_agree_update_field_outside :
  forall CT P h0 h loc f v,
    abs_agree CT P h0 h ->
    ~ (P loc /\
       exists rt fs,
         runtime_getObj h0 loc = Some (mkObj rt fs) /\
         abstract_field CT (rctype rt) f) ->
    abs_agree CT P h0 (update_field h loc f v).
Proof.
  intros CT P h0 h loc f v Hagree Hout l Hl.
  destruct (Hagree l Hl) as (rt & fs0 & fs & Hobj0 & Hobj & Hfields).
  exists rt, fs0.
  destruct (Nat.eq_dec l loc) as [-> | Hneq].
  - exists (update f v fs).
    split; [exact Hobj0 |].
    split.
    + unfold update_field. rewrite Hobj.
      apply runtime_getObj_update_same.
      exact (runtime_getObj_dom loc _ h Hobj).
    + intros g Habs.
      have Hneq_f : f <> g.
      { intros <-. apply Hout. split; [exact Hl |].
        exists rt, fs0. split; assumption. }
      destruct (Hfields g Habs) as [Heq Hclosed].
      split; [| exact Hclosed].
      rewrite Heq. unfold getVal. symmetry. apply update_diff. exact Hneq_f.
  - exists fs.
    split; [exact Hobj0 |].
    split; [| exact Hfields].
    rewrite runtime_getObj_update_field_other_general; [exact Hobj |].
    intros Heq. apply Hneq. symmetry. exact Heq.
Qed.

Lemma abs_agree_alloc :
  forall CT P h0 h o,
    abs_agree CT P h0 h ->
    abs_agree CT P h0 (h ++ [o]).
Proof.
  intros CT P h0 h o Hagree l Hl.
  destruct (Hagree l Hl) as (rt & fs0 & fs & Hobj0 & Hobj & Hfields).
  exists rt, fs0, fs.
  split; [exact Hobj0 |].
  split; [| exact Hfields].
  have Hdom := runtime_getObj_dom l _ h Hobj.
  unfold runtime_getObj in *. rewrite nth_error_app1; [exact Hobj | exact Hdom].
Qed.

Lemma abs_agree_reachable_refl :
  forall CT h root,
    wf_heap CT h ->
    abs_agree CT (reachable_abs CT h root) h h.
Proof.
  intros CT h root Hheap l Hreach.
  have Hdom := reachable_abs_target_dom CT h root l Hreach.
  destruct (runtime_getObj_Some h l Hdom) as [rt [fs Hobj]].
  exists rt, fs, fs.
  split; [exact Hobj |].
  split; [exact Hobj |].
  intros f Habs.
  split; [reflexivity |].
  intros l' Hl'.
  exact (reachable_abs_abstract_field_closed CT h root l rt fs f l'
    Hheap Hreach Hobj Habs Hl').
Qed.

(** The cache address of the receiver is outside its abstract footprint. *)
Lemma pico_hash_cache_addr_not_footprint :
  forall CT h0 receiver,
    (exists rt0 fs0,
      runtime_getObj h0 receiver = Some (mkObj rt0 fs0) /\
      derived_cache_field CT (rctype rt0) hash_cache_field) ->
    ~ pico_hash_abstract_field CT h0 receiver (receiver, hash_cache_field).
Proof.
  intros CT h0 receiver (rt0 & fs0 & Hobj0' & Hcache_field)
    (_ & rt & fs & Hobj0 & Habs_field).
  simpl in Hobj0, Habs_field.
  rewrite Hobj0 in Hobj0'. injection Hobj0' as <- <-.
  exact (derived_cache_field_not_abstract CT (rctype rt)
    hash_cache_field Hcache_field Habs_field).
Qed.

Lemma pico_hash_footprint_histories_write_outside :
  forall CT h0 receiver sigma sigma' V V' loc f v,
    pico_hash_footprint_histories CT h0 receiver sigma ->
    wm_write sigma sigma' V V' (loc, f) v ->
    ~ pico_hash_abstract_field CT h0 receiver (loc, f) ->
    pico_hash_footprint_histories CT h0 receiver sigma'.
Proof.
  intros CT h0 receiver sigma sigma' V V' loc f v Hhist [-> _] Hout
    l g v0 Hfoot Hread.
  assert (Hneq : (l, g) <> (loc, f)).
  { intros Heq. rewrite Heq in Hfoot. exact (Hout Hfoot). }
  unfold values_written_to.
  rewrite history_of_append_write_other; [| exact Hneq].
  exact (Hhist l g v0 Hfoot Hread).
Qed.

Lemma pico_hash_footprint_histories_alloc :
  forall CT h0 receiver h sigma o V,
    pico_hash_footprint_histories CT h0 receiver sigma ->
    abs_agree CT (reachable_abs CT h0 receiver) h0 h ->
    length h = length (wm_objs sigma) ->
    pico_hash_footprint_histories CT h0 receiver
      (pico_core_alloc_weak sigma o V).
Proof.
  intros CT h0 receiver h sigma o V Hhist Habs Hlength l g v0 Hfoot Hread.
  destruct (Habs l (proj1 Hfoot)) as (rt & fs0 & fs & _ & Hobj & _).
  have Hdom := runtime_getObj_dom l _ h Hobj.
  assert (Hneq : l <> length (wm_objs sigma)) by lia.
  unfold values_written_to, history_of, pico_core_alloc_weak; simpl.
  apply Nat.eqb_neq in Hneq. rewrite Hneq.
  exact (Hhist l g v0 Hfoot Hread).
Qed.

(** Weak histories created by allocating the heap [h] hold exactly the
    allocated field values. *)
Definition pico_hash_allocated_histories (h : heap) (sigma : wm_state) : Prop :=
  forall l f v0, DerivedCache.field_read h l f v0 -> values_written_to sigma (l, f) = [v0].

Lemma pico_hash_allocated_histories_empty :
  pico_hash_allocated_histories [] (mkWMState [] (fun _ => [])).
Proof.
  intros l f v0 (o & Hobj & _).
  unfold runtime_getObj in Hobj. destruct l; discriminate.
Qed.

Lemma pico_hash_allocated_histories_alloc :
  forall h sigma o V,
    length h = length (wm_objs sigma) ->
    pico_hash_allocated_histories h sigma ->
    pico_hash_allocated_histories (h ++ [o]) (pico_core_alloc_weak sigma o V).
Proof.
  intros h sigma o V Hlength Hhist l f v0 (obj & Hobj & Hget).
  unfold values_written_to, history_of, pico_core_alloc_weak; simpl.
  destruct (Nat.lt_ge_cases l (length h)) as [Hlt | Hge].
  - assert (Hneq : l <> length (wm_objs sigma)) by lia.
    apply Nat.eqb_neq in Hneq. rewrite Hneq.
    apply (Hhist l f v0). exists obj. split; [| exact Hget].
    unfold runtime_getObj in *. rewrite nth_error_app1 in Hobj; assumption.
  - unfold runtime_getObj in Hobj.
    rewrite nth_error_app2 in Hobj; [| exact Hge].
    destruct (l - length h) as [| k] eqn:Hk.
    + simpl in Hobj. injection Hobj as <-.
      assert (Heq : l = length (wm_objs sigma)) by lia.
      apply Nat.eqb_eq in Heq. rewrite Heq.
      unfold getVal in Hget. rewrite Hget. reflexivity.
    + simpl in Hobj. destruct k; discriminate.
Qed.

Lemma pico_hash_allocated_footprint_histories :
  forall CT h0 receiver sigma,
    pico_hash_allocated_histories h0 sigma ->
    pico_hash_footprint_histories CT h0 receiver sigma.
Proof.
  intros CT h0 receiver sigma Halloc l f v0 _ Hread.
  rewrite (Halloc l f v0 Hread).
  split; [discriminate |].
  intros v [-> | []]. reflexivity.
Qed.

(** ** The provider *)

Definition pico_concrete_hash_semimm
    (CT : class_table) (receiver : Loc) (m : method_name) (h0 : heap)
    (hash_value : nat) :
    PicoCoreSemImmInstantiation hash_cache_protocol
      pico_hash_stable_abs hash_value (pico_hash_cache_adapter receiver).
Proof.
  refine {|
    pcsi_state_inv := pico_hash_provider_inv CT receiver m h0 hash_value;
    pcsi_object := pico_hash_object hash_value;
    pcsi_snapshot := pico_hash_snapshot receiver;
    pcsi_abstract_field := pico_hash_abstract_field CT h0 receiver
  |}.
  - intros state _. reflexivity.
  - intros state addr k v _ Hfield Hin.
    destruct (pico_hash_cache_adapter_some receiver addr k Hfield)
      as [-> ->].
    exists v. split; [reflexivity | exact Hin].
  - intros h h' sigma sigma' V V' loc f v
      (Hagree & (Hready & Hderived & Habs & Hhist & Hcache) & Hvalid)
      Hheap Hwrite Hnoncache Hunrelated.
    assert (Haddr : (loc, f) <> pico_hash_cache_addr receiver).
    { intros Heq. rewrite Heq in Hnoncache.
      unfold pico_hash_cache_adapter in Hnoncache; simpl in Hnoncache.
      rewrite (proj2 (field_addr_eqb_eq _ _) eq_refl) in Hnoncache.
      discriminate. }
    assert (Hhistory : history_of sigma' (pico_hash_cache_addr receiver) =
        history_of sigma (pico_hash_cache_addr receiver)).
    { destruct Hwrite as [-> _]. apply history_of_append_write_other.
      congruence. }
    simpl. split; [reflexivity |].
    split.
    + apply functional_extensionality_dep. intros [].
      unfold pico_hash_snapshot; simpl.
      unfold values_written_to. rewrite Hhistory. reflexivity.
    + split.
      * subst h'. eapply heap_wm_type_agree_write_update_field; eauto.
      * split.
        -- split; [exact Hready |].
           split; [exact Hderived |].
           split; [subst h'; apply abs_agree_update_field_outside;
             [exact Habs | exact Hunrelated] |].
           split; [| exact Hcache].
           eapply pico_hash_footprint_histories_write_outside;
             [exact Hhist | exact Hwrite | exact Hunrelated].
        -- intros [] value Hin. apply Hvalid with (k := HashField).
           unfold pico_hash_snapshot, values_written_to in *; simpl in *.
           rewrite Hhistory in Hin. exact Hin.
  - intros h h' sigma sigma' V V' loc f v k cv
      (Hagree & (Hready & Hderived & Habs & Hhist & Hcache) & Hvalid)
      Hheap Hwrite Hfield Hvalue Hcvvalid.
    destruct (pico_hash_cache_adapter_some receiver (loc, f) k Hfield)
      as [Haddr ->]. simpl in Hvalue. inversion Hvalue; subst cv.
    assert (Hhistory : history_of sigma' (pico_hash_cache_addr receiver) =
      history_of sigma (pico_hash_cache_addr receiver) ++
        [mkWriteMsg v (length (history_of sigma
          (pico_hash_cache_addr receiver))) V]).
    { rewrite <- Haddr. eapply wm_write_history_same; eauto. }
    assert (Hloc : loc = receiver /\ f = hash_cache_field).
    { inversion Haddr. auto. }
    destruct Hloc as [-> ->].
    simpl. split.
    + exists HashField, v. split; [exact Hfield |].
      split; [reflexivity |]. split; [exact Hcvvalid |].
      intros []. exists [v]. split.
      * unfold pico_hash_snapshot, values_written_to; simpl.
        rewrite Hhistory. rewrite map_app. reflexivity.
      * constructor; [exact Hcvvalid | constructor].
    + split.
      * subst h'. eapply heap_wm_type_agree_write_update_field; eauto.
      * split.
        -- split; [exact Hready |].
           split; [exact Hderived |].
           have Hout := pico_hash_cache_addr_not_footprint CT h0 receiver
             Hcache.
           split; [subst h'; apply abs_agree_update_field_outside;
             [exact Habs | exact Hout] |].
           split; [| exact Hcache].
           eapply pico_hash_footprint_histories_write_outside;
             [exact Hhist | exact Hwrite | exact Hout].
        -- intros [] value Hin.
           unfold pico_hash_snapshot, values_written_to in Hin; simpl in Hin.
           rewrite Hhistory in Hin. rewrite map_app in Hin. simpl in Hin.
           apply in_app_or in Hin. destruct Hin as [Hin | [<- | []]].
           ++ exact (Hvalid HashField value Hin).
           ++ exact Hcvvalid.
  - intros h sigma new_object V
      (Hagree & (Hready & Hderived & Habs & Hhist & Hcache) & Hvalid).
    pose proof (proj1 Hagree) as Hlength.
    change (length h = length (wm_objs sigma)) in Hlength.
    assert (Hreceiver : receiver < length h).
    { destruct Hcache as (rt0 & fs0 & Hobj0 & _).
      have Hdom0 := runtime_getObj_dom receiver _ h0 Hobj0.
      destruct (Habs receiver (reachable_abs_heap CT h0 receiver Hdom0))
        as (rt & fs0' & fs & _ & Hobj & _).
      exact (runtime_getObj_dom receiver _ h Hobj). }
    assert (Hneq : receiver <> length (wm_objs sigma)) by lia.
    simpl. split; [reflexivity |].
    split.
    + apply functional_extensionality_dep. intros [].
      unfold pico_hash_snapshot, values_written_to, history_of,
        pico_core_alloc_weak; simpl.
      apply Nat.eqb_neq in Hneq. rewrite Hneq. reflexivity.
    + split.
      * apply heap_wm_type_agree_alloc. exact Hagree.
      * split.
        -- split; [exact Hready |].
           split; [exact Hderived |].
           split; [apply abs_agree_alloc; exact Habs |].
           split; [| exact Hcache].
           eapply pico_hash_footprint_histories_alloc;
             [exact Hhist | exact Habs | exact Hlength].
        -- intros [] value Hin.
           unfold pico_hash_snapshot, values_written_to, history_of,
             pico_core_alloc_weak in Hin; simpl in Hin.
           apply Nat.eqb_neq in Hneq. rewrite Hneq in Hin.
           exact (Hvalid HashField value Hin).
Defined.

Section concrete_hash_api.
  Context `{Hmem : CacheMemoryModel}.
  Context `{Hprogress : @CacheMemoryModelProgress Hmem}.
  Context (CT : class_table).
  Context `{!ownPGS (pico_core_language CT) Sigma}.
  Context `{!genericCacheG hash_cache_protocol Sigma}.

  Theorem pico_heap_hash_callable_api_wfI
      receiver m h0 hash_value C receiver_type method compute
      (Htyping : stmt_typing CT [receiver_type] AbstractState
        (pico_hash_method_stmt_with compute)
        [receiver_type; int_type; int_type])
      (Hreceiver : sbase receiver_type = TRef C)
      (Hoverride : forall parent_def parent mdef_parent qc,
        find_class CT C = Some parent_def ->
        super (signature parent_def) = Some parent ->
        bound CT C = Some qc ->
        FindMethodWithName CT parent method mdef_parent ->
        method_override_compatible CT qc
          (pico_hash_method_signature receiver_type method)
          (msignature mdef_parent))
      (Hcache_runtime : PicoHashCacheRuntimeAssignable CT receiver_type) :
    pico_ts_derived_computationI CT
      (pico_core_semimm_worldI hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver m h0 hash_value))
      ts_no_calls [receiver_type; int_type; int_type]
      [receiver_type; int_type; int_type]
      compute cache_tmp (Int hash_value) -∗
    pico_callable_method_wfI CT
      (pico_core_semimm_worldI hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver m h0 hash_value))
      C (pico_hash_method_def_with receiver_type method compute)
      (pico_hash_method_contract_at receiver hash_value) ∗
    pico_exported_methodI CT
      (pico_core_semimm_worldI hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver m h0 hash_value))
      (pico_hash_method_contract_at receiver hash_value)
      (pico_hash_method_def_with receiver_type method compute).
  Proof.
    iIntros "#Hcompute".
    assert (Hfield_at : forall rGamma h loc,
      pico_core_typed_env CT [receiver_type; int_type; int_type] rGamma h ->
      runtime_getVal rGamma cache_receiver = Some (Iot loc) ->
      loc = receiver ->
      pico_core_cache_field hash_cache_protocol
        (pico_hash_cache_adapter receiver) (loc, hash_cache_field) =
        Some HashField).
    { intros rGamma h loc Henv Hentry ->. apply pico_concrete_hash_adapter_at. }
    iPoseProof (@pico_hash_method_callable_for_with_computationI
      Hmem Hprogress CT Sigma ownPGS0 genericCacheG0
      (pico_hash_cache_adapter receiver) hash_value (fun loc => loc = receiver)
      (pico_concrete_hash_semimm CT receiver m h0 hash_value)
      receiver_type method compute Htyping Hfield_at
      (pico_concrete_hash_value_adapter_api receiver) Hcache_runtime
      with "Hcompute") as "#Hcallable".
    iSplit.
    - iSplit; [iPureIntro | iExact "Hcallable"].
      eapply pico_hash_method_def_with_wf; eauto.
    - iApply pico_callable_method_exportI. iExact "Hcallable".
  Qed.

  (** A concrete client call consumes the installed hash API and resumes with
      both its functional contract and PICO's typed caller environment.  The
      closed-dispatch premise states that this singleton environment covers
      every dynamic subtype admitted at this call site. *)
  Theorem pico_heap_hash_api_call_wpI
      receiver m h0 hash_value C receiver_type method compute
      sGamma sGamma' mt caller x y args vals h sigma V K E Phi
      (Hmethod_typing : stmt_typing CT [receiver_type] AbstractState
        (pico_hash_method_stmt_with compute)
        [receiver_type; int_type; int_type])
      (Hoverride : forall parent_def parent mdef_parent qc,
        find_class CT C = Some parent_def ->
        super (signature parent_def) = Some parent ->
        bound CT C = Some qc ->
        FindMethodWithName CT parent method mdef_parent ->
        method_override_compatible CT qc
          (pico_hash_method_signature receiver_type method)
          (msignature mdef_parent))
      (Hcache_runtime : PicoHashCacheRuntimeAssignable CT receiver_type)
      (Hcall_typing : stmt_typing CT sGamma mt
        (SCall x method y args) sGamma')
      (Hstatic_receiver : static_getType sGamma y = Some receiver_type)
      (Hreceiver_base : sbase receiver_type = TRef C)
      (Hclosed_dispatch : forall D mdef,
        class_subtype CT D C ->
        FindMethodWithName CT D method mdef -> D = C)
      (Henv : pico_core_typed_env CT sGamma caller h)
      (Hreceiver : runtime_getVal caller y = Some (Iot receiver))
      (Hbase : r_basetype h receiver = Some C)
      (Hfind : FindMethodWithName CT C method
        (pico_hash_method_def_with receiver_type method compute))
      (Hargs : runtime_lookup_list caller args = Some vals)
      (Hstate : pico_core_lr_state CT (mkPicoCoreState h sigma)) :
    pico_ts_derived_computationI CT
      (pico_core_semimm_worldI hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver m h0 hash_value))
      ts_no_calls [receiver_type; int_type; int_type]
      [receiver_type; int_type; int_type]
      compute cache_tmp (Int hash_value) -∗
    pico_core_semimm_worldI hash_cache_protocol pico_hash_stable_abs
      hash_value (pico_hash_cache_adapter receiver)
      (pico_concrete_hash_semimm CT receiver m h0 hash_value)
      (mkPicoCoreState h sigma) -∗
    ownP (mkPicoCoreState h sigma) -∗
    (▷ ∀ callee_done final_state V' returned,
      ⌜pico_core_typed_env CT sGamma'
        (set_vars caller (update x returned (vars caller)))
        (pcs_heap final_state)⌝ -∗
      ⌜pico_core_lr_state CT final_state⌝ -∗
      ⌜pico_core_heap_types_extend h (pcs_heap final_state)⌝ -∗
      ⌜psmc_post (pico_hash_method_contract_at receiver hash_value)
        (mkr_env (Iot receiver :: vals))
        (mkPicoCoreVal OK callee_done V')⌝ -∗
      pico_core_semimm_worldI hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver m h0 hash_value) final_state -∗
      ownP final_state -∗
      WP CoreRun
        (set_vars caller (update x returned (vars caller)))
        SSkip V' K @ NotStuck; E {{ Phi }}) -∗
    WP CoreRun caller (SCall x method y args) V K
      @ NotStuck; E {{ Phi }}.
  Proof.
    iIntros "#Hcompute HR Hown Hcontinue".
    iPoseProof (pico_heap_hash_callable_api_wfI receiver m h0 hash_value C
      receiver_type method compute Hmethod_typing Hreceiver_base Hoverride
      Hcache_runtime
      with "Hcompute") as "[#Hapi _]".
    set (contract := pico_hash_method_contract_at receiver hash_value).
    set (Psi := pico_singleton_semantic_method_env C method contract).
    iPoseProof (pico_singleton_semantic_method_env_wfI CT
      (pico_core_semimm_worldI hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver m h0 hash_value))
      C method contract
      (pico_hash_method_def_with receiver_type method compute) Hfind
      with "Hapi") as "#Hsemantic".
    assert (Hsummary : pico_ts_call_summary CT Psi sGamma x y method args).
    {
      exists receiver_type, C, contract. repeat split; try assumption.
      - unfold Psi, pico_singleton_semantic_method_env.
        rewrite !Nat.eqb_refl. reflexivity.
      - intros D mdef Hsub HfindD.
        assert (D = C) by (eapply Hclosed_dispatch; eauto). subst D.
        unfold Psi, pico_singleton_semantic_method_env.
        rewrite !Nat.eqb_refl. reflexivity.
    }
    iApply (pico_semantic_typed_call_wpI CT
      (pico_core_semimm_worldI hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver m h0 hash_value))
      Psi sGamma sGamma' mt caller x y method args receiver C
      (pico_hash_method_def_with receiver_type method compute) vals
      h sigma V K E Phi Hcall_typing Hsummary Henv Hreceiver Hbase Hfind
      Hargs Hstate with "Hsemantic HR Hown [Hcontinue]").
    - intros advertised Hspec.
      unfold Psi, pico_singleton_semantic_method_env in Hspec.
      rewrite !Nat.eqb_refl in Hspec. inversion Hspec; subst advertised.
      exists receiver. split; [reflexivity | reflexivity].
    - iNext. iIntros (advertised callee_done final_state V' returned)
        "%Hspec %Hcaller_typed %Hstate_final %Hextend %Hpost HR Hown".
      unfold Psi, pico_singleton_semantic_method_env in Hspec.
      rewrite !Nat.eqb_refl in Hspec. inversion Hspec; subst advertised.
      iApply ("Hcontinue" with "[] [] [] [] HR Hown").
      + iPureIntro. exact Hcaller_typed.
      + iPureIntro. exact Hstate_final.
      + iPureIntro. exact Hextend.
      + iPureIntro. unfold contract in Hpost. exact Hpost.
  Qed.
End concrete_hash_api.

Theorem pico_concrete_hash_semimm_nonempty :
  forall CT receiver m h0 hash_value state,
    pico_hash_provider_inv CT receiver m h0 hash_value state ->
    pcsi_state_inv hash_cache_protocol pico_hash_stable_abs hash_value
      (pico_hash_cache_adapter receiver)
      (pico_concrete_hash_semimm CT receiver m h0 hash_value) state.
Proof. intros; exact H. Qed.

(** In every provider state, running the derivation method on the receiver
    returns the provider's hash, and nothing else. *)
Theorem pico_concrete_hash_provider_represents_heap :
  forall CT receiver m h0 hash_value state,
    pico_hash_provider_inv CT receiver m h0 hash_value state ->
    derived_by CT m (pcs_heap state) receiver (Int hash_value) /\
    (forall w, derived_by CT m (pcs_heap state) receiver w ->
               w = Int hash_value).
Proof.
  intros CT receiver m h0 hash_value state
    (_ & ((D & Htable & Hready) & Hderived & Habs & _) & _).
  apply (derived_by_transport CT D m h0 (pcs_heap state) receiver
    (Int hash_value) Htable Hready Habs); [| exact Hderived].
  destruct Hderived as [cy [mdef [rΓ' [Hbase _]]]].
  have Hdom := r_basetype_dom h0 receiver cy Hbase.
  destruct (Habs receiver (reachable_abs_heap CT h0 receiver Hdom))
    as (rt & fs0 & fs & Hobj0 & Hobj & _).
  unfold r_basetype. rewrite Hobj0. rewrite Hobj. reflexivity.
Qed.

(** The Iris hash protocol is the derivation-defined protocol: a cache value
    is valid for the provider exactly when it is empty or is what the
    derivation method returns in the current heap. *)
Theorem pico_concrete_hash_cache_valid_is_derivation_value :
  forall CT receiver m h0 hash_value state v,
    pico_hash_provider_inv CT receiver m h0 hash_value state ->
    hash_cache_valid hash_value HashField v <->
    derivation_cache_value CT m (pcs_heap state) receiver v.
Proof.
  intros CT receiver m h0 hash_value state v Hinv.
  destruct (pico_concrete_hash_provider_represents_heap
    CT receiver m h0 hash_value state Hinv) as [Hderived Hunique].
  unfold hash_cache_valid, derivation_cache_value.
  split.
  - intros [Hzero | [-> _]].
    + left. exact Hzero.
    + right. exact Hderived.
  - intros [Hzero | Hby].
    + left. exact Hzero.
    + have -> := Hunique v Hby.
      destruct hash_value as [| n].
      * left. reflexivity.
      * right. split; [reflexivity | discriminate].
Qed.

(** A provider state can be installed at its own reference heap. *)
Lemma pico_hash_provider_inv_at_reference :
  forall CT D receiver m h0 hash_value sigma,
    derivation_table CT D ->
    derivation_ready CT D m h0 receiver ->
    derived_by CT m h0 receiver (Int hash_value) ->
    (exists rt0 fs0,
      runtime_getObj h0 receiver = Some (mkObj rt0 fs0) /\
      derived_cache_field CT (rctype rt0) hash_cache_field) ->
    heap_wm_type_agree h0 sigma ->
    pico_hash_allocated_histories h0 sigma ->
    CacheHistSnapshotOK hash_cache_protocol
      (pico_hash_snapshot receiver (mkPicoCoreState h0 sigma)) hash_value ->
    pico_hash_provider_inv CT receiver m h0 hash_value
      (mkPicoCoreState h0 sigma).
Proof.
  intros CT D receiver m h0 hash_value sigma Htable Hready Hderived Hcache
    Hagree Halloc Hsnapshot.
  split; [exact Hagree |].
  split; [| exact Hsnapshot].
  split; [exists D; split; assumption |].
  split; [exact Hderived |].
  split; [| split; [apply pico_hash_allocated_footprint_histories;
    exact Halloc | exact Hcache]].
  destruct Hready as (cy & mdef & _ & _ & _ & _ & _ & Hheap & _).
  exact (abs_agree_reachable_refl CT h0 receiver Hheap).
Qed.

Definition empty_wm_state : wm_state := mkWMState [] (fun _ => []).

Theorem pico_concrete_hash_initial_state :
  forall CT D m o initial abstract_values hash_value,
    derivation_table CT D ->
    derivation_ready CT D m [o] 0 ->
    derived_by CT m [o] 0 (Int hash_value) ->
    fields_map o = initial :: abstract_values ->
    derived_cache_field CT (rctype (rt_type o)) hash_cache_field ->
    hash_cache_valid hash_value HashField initial ->
    pico_hash_provider_inv CT 0 m [o] hash_value
      (mkPicoCoreState [o] (pico_core_alloc_weak empty_wm_state o 0)).
Proof.
  intros CT D m o initial abstract_values hash_value Htable Hready Hderived
    Hfields Hdecl Hvalid.
  apply (pico_hash_provider_inv_at_reference CT D); try assumption.
  - exists (rt_type o), (fields_map o).
    split; [destruct o; reflexivity | exact Hdecl].
  - change (heap_wm_type_agree ([] ++ [o])
      (pico_core_alloc_weak empty_wm_state o 0)).
    apply heap_wm_type_agree_alloc.
    split; [reflexivity |]. intros loc obj Hobj.
    unfold runtime_getObj in Hobj. destruct loc; discriminate.
  - change (pico_hash_allocated_histories ([] ++ [o])
      (pico_core_alloc_weak empty_wm_state o 0)).
    apply pico_hash_allocated_histories_alloc; [reflexivity |].
    exact pico_hash_allocated_histories_empty.
  - intros [] value Hin.
    unfold pico_hash_snapshot, values_written_to, history_of,
      pico_hash_cache_addr, pico_core_alloc_weak, empty_wm_state in Hin.
    rewrite Hfields in Hin. simpl in Hin.
    destruct Hin as [<- | []]. exact Hvalid.
Qed.

(** ** A Derivation Method for the Witness Hash

    The witness hash is the object's final [Int] payload.  PICO computes it
    with a parameterless method that reads that field. *)

Definition pico_hash_witness_root : class_name := 0.
Definition pico_hash_witness_class : class_name := 1.

Definition pico_hash_witness_cache_def : field_def :=
  {| ftype :=
       {| assignability := Assignable;
          mutability := Imm_f;
          f_base_type := TInt |};
     fname := hash_cache_field |}.

Definition pico_hash_witness_payload_def : field_def :=
  {| ftype :=
       {| assignability := Final;
          mutability := Imm_f;
          f_base_type := TInt |};
     fname := 1 |}.

Definition pico_hash_witness_receiver_type : qualified_type :=
  Build_qualified_type Imm (TRef pico_hash_witness_class).

Definition pico_hash_derive_method : method_name := 1.
Definition pico_hash_derive_result : var := 1.

Definition pico_hash_derive_stmt : stmt :=
  SSeq (SLocal int_type pico_hash_derive_result)
    (SVarAss pico_hash_derive_result (EField cache_receiver 1)).

Definition pico_hash_derive_method_def : method_def :=
  {| msignature :=
       pico_hash_method_signature pico_hash_witness_receiver_type
         pico_hash_derive_method;
     mbody := {| mbody_stmt := pico_hash_derive_stmt;
                 mreturn := pico_hash_derive_result |} |}.

(** The derivation table containing only the hash derivation. *)
Definition pico_hash_derivations (mdef : method_def) : Prop :=
  mdef = pico_hash_derive_method_def.

Lemma pico_hash_payload_abstract : forall CT,
  sf_def_rel CT pico_hash_witness_class 1 pico_hash_witness_payload_def ->
  abstract_field CT pico_hash_witness_class 1.
Proof.
  intros CT Hdef. split.
  - right. exists pico_hash_witness_payload_def. split; [exact Hdef | reflexivity].
  - right. exists pico_hash_witness_payload_def. split; [exact Hdef | reflexivity].
Qed.

Lemma pico_hash_derivation_table : forall CT,
  sf_def_rel CT pico_hash_witness_class 1 pico_hash_witness_payload_def ->
  derivation_table CT pico_hash_derivations.
Proof.
  intros CT Hdef mdef Hmdef.
  unfold pico_hash_derivations in Hmdef. subst mdef. simpl.
  eexists.
  eapply DS_Seq.
  - apply DS_Local.
  - apply DS_VarAss.
    eapply TSERO_Field with
      (T := pico_hash_witness_receiver_type) (C := pico_hash_witness_class).
    + reflexivity.
    + reflexivity.
    + exact (pico_hash_payload_abstract CT Hdef).
Qed.

Lemma pico_hash_derive_method_typing : forall CT,
  wf_senv CT [pico_hash_witness_receiver_type] ->
  wf_senv CT [pico_hash_witness_receiver_type; int_type] ->
  sf_def_rel CT pico_hash_witness_class 1 pico_hash_witness_payload_def ->
  stmt_typing CT [pico_hash_witness_receiver_type] AbstractState
    pico_hash_derive_stmt [pico_hash_witness_receiver_type; int_type].
Proof.
  intros CT Hwf1 Hwf2 Hdef.
  eapply ST_Seq with (sΓ' := [pico_hash_witness_receiver_type; int_type]).
  - exact Hwf1.
  - eapply ST_Local with (T := int_type) (x := pico_hash_derive_result).
    + exact Hwf1.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - eapply ST_VarAss with (Te := int_type)
      (Tthis := pico_hash_witness_receiver_type) (Tx := int_type).
    + exact Hwf2.
    + change (expr_has_type CT [pico_hash_witness_receiver_type; int_type]
        AbstractState (EField 0 1) (Build_qualified_type Imm TInt)).
      eapply ET_Field_abstract_state with
        (T := pico_hash_witness_receiver_type)
        (C := pico_hash_witness_class)
        (fDef := pico_hash_witness_payload_def).
      * exact Hwf2.
      * reflexivity.
      * reflexivity.
      * exact Hdef.
      * left. reflexivity.
    + reflexivity.
    + unfold pico_hash_derive_result. discriminate.
    + reflexivity.
    + apply qtype_refl; simpl; [reflexivity | discriminate].
Qed.

Lemma pico_hash_derive_method_wf : forall CT
    (Htyping : stmt_typing CT [pico_hash_witness_receiver_type] AbstractState
      pico_hash_derive_stmt [pico_hash_witness_receiver_type; int_type])
    (Hoverride : forall parent_def parent mdef_parent qc,
      find_class CT pico_hash_witness_class = Some parent_def ->
      super (signature parent_def) = Some parent ->
      bound CT pico_hash_witness_class = Some qc ->
      FindMethodWithName CT parent pico_hash_derive_method mdef_parent ->
      method_override_compatible CT qc
        (pico_hash_method_signature pico_hash_witness_receiver_type
          pico_hash_derive_method)
        (msignature mdef_parent)),
    wf_method CT pico_hash_witness_class pico_hash_derive_method_def.
Proof.
  intros CT Htyping Hoverride.
  unfold wf_method; simpl.
  split; [reflexivity |].
  exists [pico_hash_witness_receiver_type; int_type], int_type.
  split; [exact Htyping |].
  split; [unfold pico_hash_derive_result; simpl; lia |].
  split; [unfold pico_hash_derive_result; reflexivity |].
  split.
  - apply qtype_sub; simpl.
    + reflexivity.
    + reflexivity.
    + constructor; discriminate.
    + constructor.
  - split.
    + intros parent_def parent mdef_parent qc Hclass Hsuper Hbound Hfind.
      eapply Hoverride; eauto.
    + split; [reflexivity |].
      intros [Hscope | Hscope]; discriminate.
Qed.

(** Running the derivation on an object whose payload is [Int n] returns
    [Int n]. *)
Lemma pico_hash_derive_by : forall CT h o rt c n,
  runtime_getObj h o = Some (mkObj rt [c; Int n]) ->
  FindMethodWithName CT (rctype rt) pico_hash_derive_method
    pico_hash_derive_method_def ->
  derived_by CT pico_hash_derive_method h o (Int n).
Proof.
  intros CT h o rt c n Hobj Hfind.
  exists (rctype rt), pico_hash_derive_method_def.
  eexists.
  split; [unfold r_basetype; rewrite Hobj; reflexivity |].
  split; [exact Hfind |].
  split.
  - simpl. unfold pico_hash_derive_stmt.
    eapply SBS_Seq.
    + apply SBS_Local. reflexivity.
    + eapply SBS_Assign.
      * reflexivity.
      * eapply EBS_Field; [reflexivity | exact Hobj | reflexivity].
  - reflexivity.
Qed.

(** ** Closed Non-Vacuity Witness *)

Definition pico_hash_witness_root_constructor : constructor_def :=
  {| csignature := {| cqualifier := RDM_c; cparams := [] |} |}.

Definition pico_hash_witness_constructor : constructor_def :=
  {| csignature :=
       {| cqualifier := Imm_c; cparams := [int_type; int_type] |} |}.

Definition pico_hash_witness_root_def : class_def :=
  {| signature :=
       {| class_qualifier := RDM_c;
          cname := pico_hash_witness_root;
          super := None |};
     body :=
       {| fields := [];
          constructor := pico_hash_witness_root_constructor;
          methods := [] |} |}.

Definition pico_hash_witness_class_def : class_def :=
  {| signature :=
       {| class_qualifier := Imm_c;
          cname := pico_hash_witness_class;
          super := Some pico_hash_witness_root |};
     body :=
       {| fields :=
            [pico_hash_witness_cache_def; pico_hash_witness_payload_def];
          constructor := pico_hash_witness_constructor;
          methods := [pico_hash_derive_method_def] |} |}.

Definition pico_hash_witness_CT : class_table :=
  [pico_hash_witness_root_def; pico_hash_witness_class_def].

Lemma pico_hash_witness_collect_fields :
  CollectFields pico_hash_witness_CT pico_hash_witness_class
    [pico_hash_witness_cache_def; pico_hash_witness_payload_def].
Proof.
  eapply CF_Inherit with
    (def := pico_hash_witness_class_def)
    (parent := pico_hash_witness_root)
    (parent_fields := [])
    (own_fields :=
      [pico_hash_witness_cache_def; pico_hash_witness_payload_def]).
  - reflexivity.
  - reflexivity.
  - eapply CF_Object with (def := pico_hash_witness_root_def); reflexivity.
  - reflexivity.
Qed.

Lemma pico_hash_witness_payload_field_def :
  sf_def_rel pico_hash_witness_CT pico_hash_witness_class 1
    pico_hash_witness_payload_def.
Proof.
  unfold sf_def_rel.
  eapply FL_Found with
    (fields := [pico_hash_witness_cache_def; pico_hash_witness_payload_def]).
  - exact pico_hash_witness_collect_fields.
  - reflexivity.
Qed.

Lemma pico_hash_witness_wf_env1 :
  wf_senv pico_hash_witness_CT [pico_hash_witness_receiver_type].
Proof.
  unfold wf_senv, wf_stypeuse, pico_hash_witness_receiver_type,
    pico_hash_witness_CT, pico_hash_witness_class_def,
    pico_hash_witness_class, bound, find_class, gget.
  simpl. split; [lia |].
  constructor.
  - unfold gget. simpl. split; [constructor; discriminate | lia].
  - constructor.
Qed.

Lemma pico_hash_witness_wf_env2 :
  wf_senv pico_hash_witness_CT [pico_hash_witness_receiver_type; int_type].
Proof.
  unfold wf_senv, wf_stypeuse, pico_hash_witness_receiver_type,
    pico_hash_witness_CT, pico_hash_witness_class_def,
    pico_hash_witness_class, bound, find_class, gget, int_type.
  simpl. split; [lia |].
  constructor.
  - unfold gget. simpl. split; [constructor; discriminate | lia].
  - constructor; [reflexivity | constructor].
Qed.

Lemma pico_hash_witness_derive_wf :
  wf_method pico_hash_witness_CT pico_hash_witness_class
    pico_hash_derive_method_def.
Proof.
  apply pico_hash_derive_method_wf.
  - apply pico_hash_derive_method_typing.
    + exact pico_hash_witness_wf_env1.
    + exact pico_hash_witness_wf_env2.
    + exact pico_hash_witness_payload_field_def.
  - intros parent_def parent mdef_parent qc Hclass Hsuper Hbound Hfind.
    simpl in Hclass. inversion Hclass; subst parent_def.
    simpl in Hsuper. inversion Hsuper; subst parent.
    inversion Hfind; subst.
    + simpl in Hfind0. inversion Hfind0; subst def.
      unfold pico_hash_witness_root_def in Hget_method.
      simpl in Hget_method. discriminate.
    + simpl in Hfind0. inversion Hfind0; subst def.
      unfold pico_hash_witness_root_def in Hsuper0.
      simpl in Hsuper0. discriminate.
Qed.

Lemma pico_hash_witness_class_table_wf :
  wf_class_table pico_hash_witness_CT.
Proof.
  unfold wf_class_table.
  repeat split.
  - constructor.
    + eapply WFObjectDef with (class_name := pico_hash_witness_root);
        simpl; try reflexivity.
      * unfold wf_constructor_object. simpl.
        repeat split; try reflexivity.
        eapply CF_Object with (def := pico_hash_witness_root_def); reflexivity.
      * constructor.
      * constructor.
    + constructor.
      * eapply WFOtherDef with
          (superC := pico_hash_witness_root)
          (thisC := pico_hash_witness_class);
          simpl; try reflexivity.
        -- unfold pico_hash_witness_class, pico_hash_witness_root. lia.
        -- split.
           ++ unfold wf_constructor. simpl.
           split; [reflexivity |].
           split.
           ** repeat constructor; reflexivity.
           **
           exists [pico_hash_witness_cache_def; pico_hash_witness_payload_def].
           repeat split; try reflexivity.
           --- exact pico_hash_witness_collect_fields.
           --- constructor.
              ++++ apply qtype_refl; simpl; [reflexivity | discriminate].
              ++++ constructor.
                   **** apply qtype_refl; simpl; [reflexivity | discriminate].
                   **** constructor.
           ++ split.
              ** constructor; [exact pico_hash_witness_derive_wf | constructor].
              ** split.
                 --- constructor; [simpl; tauto | constructor].
                 --- exists [pico_hash_witness_cache_def; pico_hash_witness_payload_def].
           repeat split; try reflexivity.
           ++++ exact pico_hash_witness_collect_fields.
           ++++ right. reflexivity.
           ++++ repeat constructor; simpl; trivial.
      * constructor.
  - exists pico_hash_witness_root_def. split; reflexivity.
  - intros i def Hi Hfind.
    destruct i as [|[|i]].
    + lia.
    + simpl in Hfind. inversion Hfind; subst. discriminate.
    + unfold find_class, gget in Hfind. simpl in Hfind.
      rewrite nth_error_nil in Hfind. discriminate.
  - intros i def Hfind.
    destruct i as [|[|i]].
    + simpl in Hfind. inversion Hfind. reflexivity.
    + simpl in Hfind. inversion Hfind. reflexivity.
    + unfold find_class, gget in Hfind. simpl in Hfind.
      rewrite nth_error_nil in Hfind. discriminate.
Qed.

Lemma pico_hash_witness_find_derive :
  FindMethodWithName pico_hash_witness_CT pico_hash_witness_class
    pico_hash_derive_method pico_hash_derive_method_def.
Proof.
  eapply FOM_Here with
    (def := pico_hash_witness_class_def)
    (own_methods := [pico_hash_derive_method_def]).
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma pico_hash_witness_derivation_table :
  derivation_table pico_hash_witness_CT pico_hash_derivations.
Proof.
  exact (pico_hash_derivation_table pico_hash_witness_CT
    pico_hash_witness_payload_field_def).
Qed.

(** One-object witness heaps: cache [Int c], payload [Int n]. *)
Definition pico_hash_witness_heap (c n : nat) : heap :=
  [mkObj (mkruntime_type Imm_r pico_hash_witness_class) [Int c; Int n]].

Lemma pico_hash_witness_heap_wf : forall c n,
  wf_heap pico_hash_witness_CT (pico_hash_witness_heap c n).
Proof.
  intros c n. unfold wf_heap. intros loc Hloc.
  unfold pico_hash_witness_heap in *. simpl in Hloc.
  assert (loc = 0) by lia. subst loc.
  unfold wf_obj, runtime_getObj. simpl.
  split.
  - unfold wf_rtypeuse, bound. simpl. split.
    + unfold pico_hash_witness_class. lia.
    + trivial.
  - exists [pico_hash_witness_cache_def; pico_hash_witness_payload_def].
    split; [exact pico_hash_witness_collect_fields |].
    split; [reflexivity |].
    repeat constructor; reflexivity.
Qed.

Lemma pico_hash_witness_config_wf : forall c n,
  wf_r_config pico_hash_witness_CT [pico_hash_witness_receiver_type]
    (mkr_env [Iot 0]) (pico_hash_witness_heap c n).
Proof.
  intros c n.
  unfold wf_r_config.
  split; [exact pico_hash_witness_class_table_wf |].
  split.
  - exact (pico_hash_witness_heap_wf c n).
  - split.
    + unfold wf_renv, pico_hash_witness_heap. simpl.
      split; [lia |]. split.
      * exists 0. split; reflexivity || lia.
      * constructor; [simpl; trivial | constructor].
    + split.
      * exact pico_hash_witness_wf_env1.
      * split; [reflexivity |].
        intros receiver qcontext Hreceiver Hmut i Hi T Htype.
        simpl in Hreceiver. inversion Hreceiver; subst receiver.
        unfold pico_hash_witness_heap, r_muttype, runtime_getObj in Hmut.
        simpl in Hmut.
        inversion Hmut; subst qcontext.
        destruct i; [|simpl in Hi; lia].
        simpl in Htype. inversion Htype; subst T. simpl.
        unfold wf_r_typable, r_type, pico_hash_witness_heap, runtime_getObj.
        simpl.
        split.
        -- apply base_ref. apply class_refl.
           unfold pico_hash_witness_class. simpl. lia.
        -- trivial.
Qed.

Lemma pico_hash_witness_derived : forall c n,
  derived_by pico_hash_witness_CT pico_hash_derive_method
    (pico_hash_witness_heap c n) 0 (Int n).
Proof.
  intros c n.
  eapply pico_hash_derive_by with
    (rt := mkruntime_type Imm_r pico_hash_witness_class) (c := Int c).
  - reflexivity.
  - exact pico_hash_witness_find_derive.
Qed.

Lemma pico_hash_witness_ready : forall c n,
  derivation_ready pico_hash_witness_CT pico_hash_derivations
    pico_hash_derive_method (pico_hash_witness_heap c n) 0.
Proof.
  intros c n.
  exists pico_hash_witness_class, pico_hash_derive_method_def.
  split; [reflexivity |].
  split; [exact pico_hash_witness_find_derive |].
  split; [reflexivity |].
  split; [reflexivity |].
  exact (pico_hash_witness_config_wf c n).
Qed.

Definition pico_hash_witness_object : Obj :=
  mkObj (mkruntime_type Imm_r pico_hash_witness_class) [Int 0; Int 7].

Definition pico_hash_witness_initial_heap : heap :=
  [pico_hash_witness_object].

Lemma pico_hash_witness_cache_declared :
  derived_cache_field pico_hash_witness_CT pico_hash_witness_class
    hash_cache_field.
Proof.
  unfold derived_cache_field, cache_field, sf_assignability_rel.
  exists pico_hash_witness_cache_def. split; [|reflexivity].
  eapply FL_Found with
    (fields := [pico_hash_witness_cache_def; pico_hash_witness_payload_def]).
  - exact pico_hash_witness_collect_fields.
  - reflexivity.
Qed.

Theorem pico_concrete_hash_provider_inhabited :
  pico_hash_provider_inv pico_hash_witness_CT 0 pico_hash_derive_method
    pico_hash_witness_initial_heap 7
    (mkPicoCoreState [pico_hash_witness_object]
      (pico_core_alloc_weak empty_wm_state pico_hash_witness_object 0)).
Proof.
  eapply pico_concrete_hash_initial_state with
    (D := pico_hash_derivations)
    (initial := Int 0) (abstract_values := [Int 7]).
  - exact pico_hash_witness_derivation_table.
  - exact (pico_hash_witness_ready 0 7).
  - exact (pico_hash_witness_derived 0 7).
  - reflexivity.
  - exact pico_hash_witness_cache_declared.
  - unfold hash_cache_valid. left. reflexivity.
Qed.

(** ** Closed Post-Write Counterexample State *)

Definition pico_hash_witness_initial_weak : wm_state :=
  pico_core_alloc_weak empty_wm_state pico_hash_witness_object 0.

Definition pico_hash_witness_bad_heap : heap :=
  update_field pico_hash_witness_initial_heap 0 hash_cache_field (Int 7).

Definition pico_hash_witness_bad_weak : wm_state :=
  append_write_msg pico_hash_witness_initial_weak (0, hash_cache_field)
    (mkWriteMsg (Int 7) 1 0).

Definition pico_hash_witness_bad_state : pico_core_state :=
  mkPicoCoreState pico_hash_witness_bad_heap pico_hash_witness_bad_weak.

Lemma pico_hash_witness_valid_write :
  wm_write pico_hash_witness_initial_weak pico_hash_witness_bad_weak
    0 0 (0, hash_cache_field) (Int 7).
Proof. split; reflexivity. Qed.

Lemma pico_hash_witness_bad_provider_inv :
  pico_hash_provider_inv pico_hash_witness_CT 0 pico_hash_derive_method
    pico_hash_witness_initial_heap 7 pico_hash_witness_bad_state.
Proof.
  pose proof (pcsi_valid_cache_write_effect
    hash_cache_protocol pico_hash_stable_abs 7
    (pico_hash_cache_adapter 0)
    (pico_concrete_hash_semimm pico_hash_witness_CT 0
      pico_hash_derive_method pico_hash_witness_initial_heap 7)
    pico_hash_witness_initial_heap pico_hash_witness_bad_heap
    pico_hash_witness_initial_weak pico_hash_witness_bad_weak
    0 0 0 hash_cache_field (Int 7) HashField (Int 7)
    pico_concrete_hash_provider_inhabited eq_refl
    pico_hash_witness_valid_write
    (pico_concrete_hash_adapter_at 0)
    (pico_concrete_hash_value_adapter 0 (Int 7))) as Heffect.
  assert (Hvalid : hash_cache_valid 7 HashField (Int 7)).
  { right. split; reflexivity || discriminate. }
  specialize (Heffect Hvalid).
  exact (proj2 Heffect).
Qed.

Lemma pico_hash_witness_bad_state_wf :
  pico_core_state_wf pico_hash_witness_bad_state.
Proof.
  assert (Hempty : pico_core_state_wf
    (mkPicoCoreState [] empty_wm_state)).
  {
    split.
    - split; [reflexivity |]. intros loc o Hobj.
      unfold runtime_getObj in Hobj. destruct loc; discriminate.
    - intros loc o f current Hobj.
      unfold runtime_getObj in Hobj. destruct loc; discriminate.
  }
  assert (Hinitial : pico_core_state_wf
    (mkPicoCoreState pico_hash_witness_initial_heap
      pico_hash_witness_initial_weak)).
  {
    change (pico_core_state_wf
      (mkPicoCoreState ([] ++ [pico_hash_witness_object])
        (pico_core_alloc_weak empty_wm_state pico_hash_witness_object 0))).
    apply pico_core_state_wf_alloc. exact Hempty.
  }
  unfold pico_hash_witness_bad_state.
  eapply pico_core_state_wf_write with (o := pico_hash_witness_object).
  - exact Hinitial.
  - reflexivity.
  - exact pico_hash_witness_valid_write.
Qed.

Lemma pico_hash_witness_bad_heap_wf :
  wf_heap pico_hash_witness_CT pico_hash_witness_bad_heap.
Proof. exact (pico_hash_witness_heap_wf 7 7). Qed.

Lemma pico_hash_witness_bad_config_wf :
  wf_r_config pico_hash_witness_CT [pico_hash_witness_receiver_type]
    (mkr_env [Iot 0]) pico_hash_witness_bad_heap.
Proof. exact (pico_hash_witness_config_wf 7 7). Qed.

Lemma pico_hash_witness_bad_typed_env :
  pico_core_typed_env pico_hash_witness_CT
    [pico_hash_witness_receiver_type] (mkr_env [Iot 0])
    pico_hash_witness_bad_heap.
Proof.
  exists Imm_r, 0.
  split; [exact pico_hash_witness_bad_config_wf |].
  split; [reflexivity |].
  split.
  - unfold pico_hash_witness_bad_heap, pico_hash_witness_initial_heap,
      update_field, r_muttype, runtime_getObj. reflexivity.
  - intros x T Htype.
    destruct x.
    + simpl in Htype. inversion Htype; subst T.
      exists (Iot 0). split; [reflexivity |].
      unfold pico_core_typed_value, wf_r_typable, r_type,
        pico_hash_witness_bad_heap, pico_hash_witness_initial_heap,
        update_field, runtime_getObj. simpl.
      split.
      * apply base_ref. apply class_refl.
        unfold pico_hash_witness_class. simpl. lia.
      * trivial.
    + unfold static_getType in Htype. simpl in Htype.
      rewrite nth_error_nil in Htype. discriminate.
Qed.

(** After the valid write, the cache holds [Int 7] and the derivation still
    returns [Int 7] in the current heap. *)
Theorem pico_hash_witness_bad_state_cache_is_derived :
  derivation_cache_protocol pico_hash_witness_CT pico_hash_derive_method
    pico_hash_witness_bad_heap 0 hash_cache_field.
Proof.
  exists (Int 7). split.
  - exists (mkObj (mkruntime_type Imm_r pico_hash_witness_class)
      [Int 7; Int 7]).
    split; reflexivity.
  - right.
    exact (proj1 (pico_concrete_hash_provider_represents_heap
      pico_hash_witness_CT 0 pico_hash_derive_method
      pico_hash_witness_initial_heap 7 pico_hash_witness_bad_state
      pico_hash_witness_bad_provider_inv)).
Qed.
