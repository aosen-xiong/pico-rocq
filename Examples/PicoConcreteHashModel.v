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

Definition pico_hash_snapshot (receiver : Loc) (state : pico_core_state) :
    CacheHistorySnapshot hash_cache_protocol :=
  fun _ => values_written_to (pcs_weak state) (pico_hash_cache_addr receiver).

Definition pico_hash_abstract_field (receiver : Loc) (addr : FieldAddr) : Prop :=
  fst addr = receiver /\ addr <> pico_hash_cache_addr receiver.

Definition pico_hash_abstract_values
    (receiver : Loc) (state : pico_core_state) : list value :=
  match runtime_getObj (pcs_heap state) receiver with
  | Some o => tl (fields_map o)
  | None => []
  end.

Definition pico_hash_object
    (hash : list value -> nat) (receiver : Loc) (state : pico_core_state) : nat :=
  hash (pico_hash_abstract_values receiver state).

Definition pico_hash_provider_inv
    (CT : class_table) (receiver : Loc) (hash : list value -> nat)
    (hash_value : nat) (state : pico_core_state) : Prop :=
  heap_wm_type_agree (pcs_heap state) (pcs_weak state) /\
  (exists o cache_value abstract_values rt,
    runtime_getObj (pcs_heap state) receiver = Some o /\
    fields_map o = cache_value :: abstract_values /\
    hash abstract_values = hash_value /\
    wm_get_type (pcs_weak state) receiver = Some rt /\
    derived_cache_field CT (rctype rt) hash_cache_field) /\
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

Definition pico_concrete_hash_semimm
    (CT : class_table) (receiver : Loc) (hash : list value -> nat)
    (hash_value : nat) :
    PicoCoreSemImmInstantiation CT hash_cache_protocol
      pico_hash_stable_abs hash_value (pico_hash_cache_adapter receiver).
Proof.
  refine {|
    pcsi_state_inv := pico_hash_provider_inv CT receiver hash hash_value;
    pcsi_object := pico_hash_object hash receiver;
    pcsi_snapshot := pico_hash_snapshot receiver;
    pcsi_abstract_field := pico_hash_abstract_field receiver
  |}.
  - intros addr k Habstract Hcache.
    destruct (pico_hash_cache_adapter_some receiver addr k Hcache) as [-> _].
    exact (proj2 Habstract eq_refl).
  - intros state loc f k Hinv Hfield.
    destruct Hinv as (_ & (o & cache_value & abstract_values & rt & Hobj &
      Hfields & Hhash & Htype & Hdecl) & _).
    destruct (pico_hash_cache_adapter_some receiver (loc, f) k Hfield)
      as [Haddr _]. inversion Haddr; subst. exists rt. auto.
  - intros state Hinv. destruct Hinv as (_ & (o & cache_value &
      abstract_values & rt & Hobj & Hfields & Hhash & Htype & Hdecl) & _).
    unfold pico_hash_stable_abs, pico_hash_object, pico_hash_abstract_values.
    rewrite Hobj. rewrite Hfields. exact Hhash.
  - intros state addr k v _ Hfield Hin.
    destruct (pico_hash_cache_adapter_some receiver addr k Hfield)
      as [-> ->].
    exists v. split; [reflexivity | exact Hin].
  - intros h h' sigma sigma' V V' loc f v
      (Hagree & Hrepresentation & Hvalid) Hheap Hwrite Hnoncache Hunrelated.
    destruct Hrepresentation as (o & cache_value & abstract_values & rt &
      Hobj & Hfields & Hhash & Htype & Hdecl).
    assert (Haddr : (loc, f) <> pico_hash_cache_addr receiver).
    { intros Heq. rewrite Heq in Hnoncache.
      unfold pico_hash_cache_adapter in Hnoncache; simpl in Hnoncache.
      rewrite (proj2 (field_addr_eqb_eq _ _) eq_refl) in Hnoncache.
      discriminate. }
    assert (Hhistory : history_of sigma' (pico_hash_cache_addr receiver) =
        history_of sigma (pico_hash_cache_addr receiver)).
    { destruct Hwrite as [-> _]. apply history_of_append_write_other.
      congruence. }
    assert (Hloc_other : loc <> receiver).
    { intros ->. apply Hunrelated. split; [reflexivity | exact Haddr]. }
    assert (Hobj_after : runtime_getObj h' receiver = Some o).
    { subst h'. rewrite runtime_getObj_update_field_other_general;
        assumption. }
    simpl. split.
    + unfold pico_hash_object, pico_hash_abstract_values.
      rewrite Hobj_after. rewrite Hobj.
      reflexivity.
    + split.
      * apply functional_extensionality_dep. intros [].
      unfold pico_hash_snapshot; simpl.
      unfold values_written_to. rewrite Hhistory. reflexivity.
      * split.
        -- subst h'. eapply heap_wm_type_agree_write_update_field; eauto.
        -- split.
           ++ exists o, cache_value, abstract_values, rt. repeat split; try assumption.
              rewrite (wm_write_get_type sigma sigma' V V' (loc, f) v
                receiver Hwrite). exact Htype.
           ++ intros [] value Hin. apply Hvalid with (k := HashField).
           unfold pico_hash_snapshot, values_written_to in *; simpl in *.
           rewrite Hhistory in Hin. exact Hin.
  - intros h h' sigma sigma' V V' loc f v k cv
      (Hagree & Hrepresentation & Hvalid) Hheap Hwrite Hfield Hvalue Hcvvalid.
    destruct Hrepresentation as (o & old_cache & abstract_values & rt &
      Hobj & Hfields & Hhash & Htype & Hdecl).
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
    assert (Hobj_after : runtime_getObj h' receiver =
      Some (set_fields_map o (v :: abstract_values))).
    { subst h'. pose proof (runtime_getObj_update_field_same_value
        h receiver hash_cache_field v o Hobj) as Hsame.
      unfold hash_cache_field in *. rewrite Hfields in Hsame. exact Hsame. }
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
        -- exists (set_fields_map o (v :: abstract_values)), v,
             abstract_values, rt. split; [exact Hobj_after |].
           split; [reflexivity |]. split; [exact Hhash |]. split.
           ++ rewrite (wm_write_get_type sigma sigma' V V'
                (receiver, hash_cache_field) v receiver Hwrite). exact Htype.
           ++ exact Hdecl.
        -- intros [] value Hin.
           unfold pico_hash_snapshot, values_written_to in Hin; simpl in Hin.
           rewrite Hhistory in Hin. rewrite map_app in Hin. simpl in Hin.
           apply in_app_or in Hin. destruct Hin as [Hin | [<- | []]].
           ++ exact (Hvalid HashField value Hin).
           ++ exact Hcvvalid.
  - intros h sigma new_object V (Hagree & Hrepresentation & Hvalid).
    destruct Hrepresentation as (o & cache_value & abstract_values & rt &
      Hobj & Hfields & Hhash & Htype & Hdecl).
    pose proof (proj1 Hagree) as Hlength.
    pose proof (runtime_getObj_dom receiver o h Hobj) as Hreceiver.
    change (length h = length (wm_objs sigma)) in Hlength.
    assert (Hneq : receiver <> length (wm_objs sigma)) by lia.
    assert (Hobj_after : runtime_getObj (h ++ [new_object]) receiver = Some o).
    { unfold runtime_getObj. rewrite nth_error_app1; assumption. }
    simpl. split.
    + unfold pico_hash_object, pico_hash_abstract_values.
      rewrite Hobj_after. rewrite Hobj.
      reflexivity.
    + split.
      * apply functional_extensionality_dep. intros [].
      unfold pico_hash_snapshot, values_written_to, history_of,
        pico_core_alloc_weak; simpl.
      apply Nat.eqb_neq in Hneq. rewrite Hneq. reflexivity.
      * split.
        -- apply heap_wm_type_agree_alloc. exact Hagree.
        -- split.
           ++ exists o, cache_value, abstract_values, rt. repeat split; try assumption.
              unfold wm_get_type, pico_core_alloc_weak; simpl.
              rewrite nth_error_app1; [exact Htype | lia].
           ++ intros [] value Hin.
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
      receiver hash hash_value C receiver_type method compute
      (Htyping : stmt_typing CT [receiver_type] AbstractImm
        (pico_hash_method_stmt_with compute)
        [receiver_type; int_type; int_type])
      (Hoverride : forall parent_def parent mdef_parent,
        find_class CT C = Some parent_def ->
        super (signature parent_def) = Some parent ->
        FindMethodWithName CT parent method mdef_parent ->
        msignature mdef_parent =
          pico_hash_method_signature receiver_type method)
      (Hcache_runtime : PicoHashCacheRuntimeAssignable CT receiver_type) :
    pico_ts_derived_computationI CT
      (pico_core_semimm_worldI CT hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver hash hash_value))
      ts_no_calls [receiver_type; int_type; int_type]
      [receiver_type; int_type; int_type]
      compute cache_tmp (Int hash_value) -∗
    pico_callable_method_wfI CT
      (pico_core_semimm_worldI CT hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver hash hash_value))
      C (pico_hash_method_def_with receiver_type method compute)
      (pico_hash_method_contract_at receiver hash_value) ∗
    pico_exported_methodI CT
      (pico_core_semimm_worldI CT hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver hash hash_value))
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
      (pico_concrete_hash_semimm CT receiver hash hash_value)
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
      receiver hash hash_value C receiver_type method compute
      sGamma sGamma' mt caller x y args vals h sigma V K E Phi
      (Hmethod_typing : stmt_typing CT [receiver_type] AbstractImm
        (pico_hash_method_stmt_with compute)
        [receiver_type; int_type; int_type])
      (Hoverride : forall parent_def parent mdef_parent,
        find_class CT C = Some parent_def ->
        super (signature parent_def) = Some parent ->
        FindMethodWithName CT parent method mdef_parent ->
        msignature mdef_parent =
          pico_hash_method_signature receiver_type method)
      (Hcache_runtime : PicoHashCacheRuntimeAssignable CT receiver_type)
      (Hcall_typing : stmt_typing CT sGamma mt
        (SCall x y method args) sGamma')
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
      (pico_core_semimm_worldI CT hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver hash hash_value))
      ts_no_calls [receiver_type; int_type; int_type]
      [receiver_type; int_type; int_type]
      compute cache_tmp (Int hash_value) -∗
    pico_core_semimm_worldI CT hash_cache_protocol pico_hash_stable_abs
      hash_value (pico_hash_cache_adapter receiver)
      (pico_concrete_hash_semimm CT receiver hash hash_value)
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
      pico_core_semimm_worldI CT hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver hash hash_value) final_state -∗
      ownP final_state -∗
      WP CoreRun
        (set_vars caller (update x returned (vars caller)))
        SSkip V' K @ NotStuck; E {{ Phi }}) -∗
    WP CoreRun caller (SCall x y method args) V K
      @ NotStuck; E {{ Phi }}.
  Proof.
    iIntros "#Hcompute HR Hown Hcontinue".
    iPoseProof (pico_heap_hash_callable_api_wfI receiver hash hash_value C
      receiver_type method compute Hmethod_typing Hoverride Hcache_runtime
      with "Hcompute") as "[#Hapi _]".
    set (contract := pico_hash_method_contract_at receiver hash_value).
    set (Psi := pico_singleton_semantic_method_env C method contract).
    iPoseProof (pico_singleton_semantic_method_env_wfI CT
      (pico_core_semimm_worldI CT hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver hash hash_value))
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
      (pico_core_semimm_worldI CT hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver hash hash_value))
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

Theorem pico_concrete_hash_semimm_nonempty : forall CT receiver hash hash_value state,
  pico_hash_provider_inv CT receiver hash hash_value state ->
  pcsi_state_inv CT hash_cache_protocol pico_hash_stable_abs hash_value
    (pico_hash_cache_adapter receiver)
    (pico_concrete_hash_semimm CT receiver hash hash_value) state.
Proof. intros; exact H. Qed.

Theorem pico_concrete_hash_provider_represents_heap :
  forall CT receiver hash hash_value state
    (Hinv : pico_hash_provider_inv CT receiver hash hash_value state),
    pico_hash_object hash receiver state = hash_value.
Proof.
  intros CT receiver hash hash_value state
    (_ & (o & cache_value & abstract_values & rt & Hobj & Hfields & Hhash &
      Htype & Hdecl) & _).
  unfold pico_hash_object, pico_hash_abstract_values.
  rewrite Hobj. rewrite Hfields. exact Hhash.
Qed.

Definition empty_wm_state : wm_state := mkWMState [] (fun _ => []).

Theorem pico_concrete_hash_initial_state : forall CT hash hash_value o initial
    abstract_values,
  fields_map o = initial :: abstract_values ->
  hash abstract_values = hash_value ->
  derived_cache_field CT (rctype (rt_type o)) hash_cache_field ->
  nth_error (fields_map o) hash_cache_field = Some initial ->
  hash_cache_valid hash_value HashField initial ->
  pico_hash_provider_inv CT 0 hash hash_value
    (mkPicoCoreState [o] (pico_core_alloc_weak empty_wm_state o 0)).
Proof.
  intros CT hash hash_value o initial abstract_values Hfields Hhash Hdecl
    Hfield Hvalid.
  split.
  - change (heap_wm_type_agree ([] ++ [o])
      (pico_core_alloc_weak empty_wm_state o 0)).
    apply heap_wm_type_agree_alloc.
    split; [reflexivity |]. intros loc obj Hobj.
    unfold runtime_getObj in Hobj. destruct loc; discriminate.
  - split.
    + exists o, initial, abstract_values, (rt_type o). repeat split; try assumption;
        simpl; try reflexivity.
    + intros [] value Hin.
    unfold pico_hash_snapshot, values_written_to, history_of,
      pico_hash_cache_addr, pico_core_alloc_weak, empty_wm_state in Hin.
    unfold hash_cache_field in Hfield.
    rewrite Hfields in Hin. simpl in Hin.
    destruct Hin as [<- | []]. exact Hvalid.
Qed.

(** ** Closed Non-Vacuity Witness *)

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
          methods := [] |} |}.

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
              ** constructor.
              ** split.
                 --- constructor.
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

Definition pico_hash_witness_function (values : list value) : nat :=
  match values with
  | Int n :: _ => n
  | _ => 0
  end.

Definition pico_hash_witness_object : Obj :=
  mkObj (mkruntime_type Imm_r pico_hash_witness_class) [Int 0; Int 7].

Lemma pico_hash_witness_cache_declared :
  derived_cache_field pico_hash_witness_CT pico_hash_witness_class
    hash_cache_field.
Proof.
  unfold derived_cache_field, cache_field, sf_assignability_rel.
  exists pico_hash_witness_cache_def. split; [|reflexivity].
  eapply FL_Found with
    (fields := [pico_hash_witness_cache_def; pico_hash_witness_payload_def]).
  - eapply CF_Inherit with
      (def := pico_hash_witness_class_def)
      (parent := pico_hash_witness_root)
      (parent_fields := [])
      (own_fields :=
        [pico_hash_witness_cache_def; pico_hash_witness_payload_def]).
    + reflexivity.
    + reflexivity.
    + eapply CF_Object with (def := pico_hash_witness_root_def);
        reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Theorem pico_concrete_hash_provider_inhabited :
  pico_hash_provider_inv pico_hash_witness_CT 0
    pico_hash_witness_function 7
    (mkPicoCoreState [pico_hash_witness_object]
      (pico_core_alloc_weak empty_wm_state pico_hash_witness_object 0)).
Proof.
  eapply pico_concrete_hash_initial_state with
    (initial := Int 0) (abstract_values := [Int 7]).
  - reflexivity.
  - reflexivity.
  - exact pico_hash_witness_cache_declared.
  - reflexivity.
  - unfold hash_cache_valid. left. reflexivity.
Qed.

(** ** Closed Post-Write Counterexample State *)

Definition pico_hash_witness_receiver_type : qualified_type :=
  Build_qualified_type Imm (TRef pico_hash_witness_class).

Definition pico_hash_witness_initial_heap : heap :=
  [pico_hash_witness_object].

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
  pico_hash_provider_inv pico_hash_witness_CT 0
    pico_hash_witness_function 7 pico_hash_witness_bad_state.
Proof.
  pose proof (pcsi_valid_cache_write_effect
    pico_hash_witness_CT hash_cache_protocol pico_hash_stable_abs 7
    (pico_hash_cache_adapter 0)
    (pico_concrete_hash_semimm pico_hash_witness_CT 0
      pico_hash_witness_function 7)
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
Proof.
  unfold wf_heap. intros loc Hloc.
  unfold pico_hash_witness_bad_heap, pico_hash_witness_initial_heap in *.
  assert (loc = 0) by (rewrite update_field_length in Hloc; simpl in Hloc; lia).
  subst loc.
  unfold wf_obj, update_field, runtime_getObj. simpl.
  split.
  - unfold wf_rtypeuse, bound. simpl. split.
    + unfold pico_hash_witness_class. lia.
    + trivial.
  - exists [pico_hash_witness_cache_def; pico_hash_witness_payload_def].
    split; [exact pico_hash_witness_collect_fields |].
    split; [reflexivity |].
    repeat constructor; reflexivity.
Qed.

Lemma pico_hash_witness_bad_config_wf :
  wf_r_config pico_hash_witness_CT [pico_hash_witness_receiver_type]
    (mkr_env [Iot 0]) pico_hash_witness_bad_heap.
Proof.
  unfold wf_r_config.
  split; [exact pico_hash_witness_class_table_wf |].
  split.
  - exact pico_hash_witness_bad_heap_wf.
  - split.
    + unfold wf_renv, pico_hash_witness_bad_heap,
      pico_hash_witness_initial_heap. simpl.
      split; [lia |]. split.
      * exists 0. split; reflexivity || lia.
      * constructor; [simpl; trivial | constructor].
    + split.
      * unfold wf_senv. split; [simpl; lia |].
        constructor; [|constructor].
        unfold pico_hash_witness_receiver_type, wf_stypeuse, bound. simpl.
        split; [apply q_refl; discriminate |].
        unfold pico_hash_witness_class. lia.
      * split; [reflexivity |].
        intros receiver qcontext Hreceiver Hmut i Hi T Htype.
        simpl in Hreceiver. inversion Hreceiver; subst receiver.
        unfold pico_hash_witness_bad_heap, pico_hash_witness_initial_heap,
          update_field, r_muttype, runtime_getObj in Hmut. simpl in Hmut.
        inversion Hmut; subst qcontext.
        destruct i; [|simpl in Hi; lia].
        simpl in Htype. inversion Htype; subst T. simpl.
        unfold wf_r_typable, r_type, pico_hash_witness_bad_heap,
          pico_hash_witness_initial_heap, update_field, runtime_getObj. simpl.
        split.
        -- apply base_ref. apply class_refl.
           unfold pico_hash_witness_class. simpl. lia.
        -- trivial.
Qed.

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
