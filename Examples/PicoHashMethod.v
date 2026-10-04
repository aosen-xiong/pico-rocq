From Stdlib Require Import List Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping Bigstep.
Require Import Core.GenericCacheProtocol Core.GenericDerivedCache.
Require Import Examples.PicoIfZeroCache.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoCoreLanguage
  PICOBridge.PicoCoreInvariant PICOBridge.PicoCoreSemImm
  PICOBridge.PicoCacheTyping.

(** * Hash Cache as a Bespoke Semantic API

    The local-copy trace proof supplies the functional half of the API
    boundary.  A concrete source method is exported only after its body has
    also been proved to inhabit the Iris method contract below. *)

Definition pico_hash_decode_args (_ : r_env) : option unit := Some tt.

Definition pico_hash_decode_result (v : value) : option value := Some v.

Definition pico_hash_method_contract_for
    (receiver_ok : Loc -> Prop) (H : nat) :
    PicoSemanticMethodContract :=
  {| psmc_pre := fun entry _ =>
       exists receiver,
         runtime_getVal entry cache_receiver = Some (Iot receiver) /\
         receiver_ok receiver;
     psmc_post := fun _ result =>
       pcv_result result = OK /\
       exists returned,
         runtime_getVal (pcv_env result) cache_result = Some returned /\
         pico_hash_decode_result returned = Some (hash_pure_result H tt) |}.

Definition pico_hash_method_contract (H : nat) : PicoSemanticMethodContract :=
  pico_hash_method_contract_for (fun _ => True) H.

Definition pico_hash_method_contract_at (receiver : Loc) (H : nat) :
    PicoSemanticMethodContract :=
  pico_hash_method_contract_for (fun loc => loc = receiver) H.

Definition pico_hash_compute_stmt (H : nat) : stmt :=
  SVarAss cache_tmp (EInt H).

Definition pico_hash_method_core_stmt_with (compute : stmt) : stmt :=
  pico_local_copy_cache_stmt compute.

Definition pico_hash_method_core_stmt (H : nat) : stmt :=
  pico_hash_method_core_stmt_with (pico_hash_compute_stmt H).

Definition pico_hash_method_stmt_with (compute : stmt) : stmt :=
  SSeq (SLocal int_type cache_tmp)
    (SSeq (SLocal int_type cache_result)
      (pico_hash_method_core_stmt_with compute)).

Definition pico_hash_method_stmt (H : nat) : stmt :=
  pico_hash_method_stmt_with (pico_hash_compute_stmt H).

Definition pico_hash_method_signature
    (receiver_type : qualified_type) (method : method_name) : method_sig :=
  {| mscope := AbstractState;
     mret := int_type;
     mname := method;
     mreceiver := receiver_type;
     mparams := [] |}.

Definition pico_hash_method_def_with
    (receiver_type : qualified_type) (method : method_name) (compute : stmt) :
    method_def :=
  {| msignature := pico_hash_method_signature receiver_type method;
     mbody := {| mbody_stmt := pico_hash_method_stmt_with compute;
                 mreturn := cache_result |} |}.

Definition pico_hash_method_def
    (receiver_type : qualified_type) (method : method_name) (H : nat) :
    method_def :=
  pico_hash_method_def_with receiver_type method (pico_hash_compute_stmt H).

Definition pico_double_read_hash_method_stmt (H : nat) : stmt :=
  SSeq (SLocal int_type cache_tmp)
    (SSeq (SLocal int_type cache_result)
      (pico_double_read_cache_stmt (pico_hash_compute_stmt H))).

Definition pico_double_read_hash_method_def
    (receiver_type : qualified_type) (method : method_name) (H : nat) :
    method_def :=
  {| msignature := pico_hash_method_signature receiver_type method;
     mbody := {| mbody_stmt := pico_double_read_hash_method_stmt H;
                 mreturn := cache_result |} |}.

Lemma pico_double_read_hash_method_def_wf : forall
    CT C receiver_type method H
    (Htyping : stmt_typing CT [receiver_type] AbstractState
      (pico_double_read_hash_method_stmt H)
      [receiver_type; int_type; int_type])
    (Hreceiver : sbase receiver_type = TRef C)
    (Hoverride : forall parent_def parent mdef_parent qc,
      find_class CT C = Some parent_def ->
      super (signature parent_def) = Some parent ->
      bound CT C = Some qc ->
      FindMethodWithName CT parent method mdef_parent ->
      method_override_compatible CT qc
        (pico_hash_method_signature receiver_type method)
        (msignature mdef_parent)),
    wf_method CT C (pico_double_read_hash_method_def receiver_type method H).
Proof.
  intros CT C receiver_type method H Htyping Hreceiver Hoverride.
  unfold wf_method; simpl.
  split; [reflexivity |].
  exists [receiver_type; int_type; int_type], int_type.
  split; [exact Htyping |].
  split; [unfold cache_result; simpl; lia |].
  split; [unfold cache_result; reflexivity |].
  split.
  - apply qtype_sub; simpl.
    + reflexivity.
    + reflexivity.
    + constructor; discriminate.
    + constructor.
  - split.
    + intros parent_def parent mdef_parent qc Hclass Hsuper Hbound Hfind.
      eapply Hoverride; eauto.
    + split; [exact Hreceiver |].
      intros [Hscope | Hscope]; discriminate.
Qed.

Lemma pico_hash_method_typing_parts_with : forall CT receiver_type compute,
  stmt_typing CT [receiver_type] AbstractState
    (pico_hash_method_stmt_with compute)
    [receiver_type; int_type; int_type] ->
  stmt_typing CT [receiver_type] AbstractState
      (SLocal int_type cache_tmp) [receiver_type; int_type] /\
  stmt_typing CT [receiver_type; int_type] AbstractState
      (SLocal int_type cache_result)
      [receiver_type; int_type; int_type] /\
  stmt_typing CT [receiver_type; int_type; int_type] AbstractState
      (pico_hash_method_core_stmt_with compute)
      [receiver_type; int_type; int_type].
Proof.
  intros CT receiver_type compute Htyping.
  unfold pico_hash_method_stmt_with in Htyping.
  inversion Htyping; subst.
  inversion Htype1; subst.
  inversion Htype2; subst.
  inversion Htype0; subst.
  split; [econstructor; eauto |].
  split; [econstructor; eauto | assumption].
Qed.

Lemma pico_hash_method_final_assign_typing : forall CT receiver_type compute,
  stmt_typing CT [receiver_type] AbstractState
    (pico_hash_method_stmt_with compute)
    [receiver_type; int_type; int_type] ->
  stmt_typing CT [receiver_type; int_type; int_type] AbstractState
    (SVarAss cache_result (EVar cache_tmp))
    [receiver_type; int_type; int_type].
Proof.
  intros CT receiver_type compute Htyping.
  destruct (pico_hash_method_typing_parts_with CT receiver_type compute Htyping)
    as (_ & _ & Hcore).
  unfold pico_hash_method_core_stmt_with, pico_local_copy_cache_stmt in Hcore.
  inversion Hcore; subst.
  inversion Htype1; subst.
  inversion Htype2; subst.
  unfold pico_local_copy_cache_branch in Htype0.
  inversion Htype0; subst.
  inversion H10; subst.
  exact Htype3.
Qed.

Lemma pico_hash_method_cache_write_typing : forall CT receiver_type compute,
  stmt_typing CT [receiver_type] AbstractState
    (pico_hash_method_stmt_with compute)
    [receiver_type; int_type; int_type] ->
  stmt_typing CT [receiver_type; int_type; int_type] AbstractState
    (SFldWrite cache_receiver hash_cache_field cache_tmp)
    [receiver_type; int_type; int_type].
Proof.
  intros CT receiver_type compute Htyping.
  destruct (pico_hash_method_typing_parts_with CT receiver_type compute Htyping)
    as (_ & _ & Hcore).
  unfold pico_hash_method_core_stmt_with, pico_local_copy_cache_stmt in Hcore.
  inversion Hcore; subst.
  inversion Htype1; subst.
  inversion Htype2; subst.
  unfold pico_local_copy_cache_branch in Htype0.
  inversion Htype0; subst.
  inversion H10; subst.
  inversion H9; subst.
  inversion Htype5; subst.
  exact Htype5.
Qed.

Lemma pico_hash_method_def_with_wf : forall
    CT C receiver_type method compute
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
        (msignature mdef_parent)),
    wf_method CT C (pico_hash_method_def_with receiver_type method compute).
Proof.
  intros CT C receiver_type method compute Htyping Hreceiver Hoverride.
  unfold wf_method; simpl.
  split; [reflexivity |].
  exists [receiver_type; int_type; int_type], int_type.
  split; [exact Htyping |].
  split; [unfold cache_result; simpl; lia |].
  split; [unfold cache_result; reflexivity |].
  split.
  - apply qtype_sub; simpl.
    + reflexivity.
    + reflexivity.
    + constructor; discriminate.
    + constructor.
  - split.
    + intros parent_def parent mdef_parent qc Hclass Hsuper Hbound Hfind.
      eapply Hoverride; eauto.
    + split; [exact Hreceiver |].
      intros [Hscope | Hscope]; discriminate.
Qed.

(** The receivers whose hash-cache field the adapter maps. *)
Definition pico_hash_cache_receiver
    (A : PicoCoreCacheAdapter hash_cache_protocol) (loc : Loc) : Prop :=
  pico_core_cache_field hash_cache_protocol A (loc, hash_cache_field) =
    Some HashField.
