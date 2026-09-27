From Stdlib Require Import List.
Import ListNotations.

Require Import Core.GenericCacheProtocol.

(** * Semantic Immutability as a Rely-Guarantee Condition

    The interference an immutable object tolerates preserves its stable
    abstraction and extends its cache histories only by protocol-valid
    values.  This one relation is both the rely and the guarantee of every
    thread that uses the object.  Semantic immutability is stable under it,
    and a trace-robust method meets its rely-guarantee specification when its
    reads and writes are interleaved with arbitrary rely steps.

    A method execution is modelled as the trace interpreter [CacheRun] sees
    it: a read phase followed by a write phase.  Environment steps may occur
    anywhere in either phase. *)

Section rely_guarantee.
  Context {Obj AbsVal : Type}.
  Context (P : CacheProtocol AbsVal).
  Context (Stable : StableAbs Obj AbsVal).

  (** A state is the object representation together with the cache
      histories. *)
  Record CacheState : Type := mkCacheState {
    cs_obj : Obj;
    cs_hist : @CacheHistory Obj AbsVal P
  }.

  Definition SemImmAt (a : AbsVal) (s : CacheState) : Prop :=
    SemImm P (cs_hist s) Stable (cs_obj s) a.

  (** The interference relation: the stable abstraction is preserved, and
      every cache history of the object grows only by appending valid
      values.  Nothing else in the state is constrained. *)
  Definition CacheInterference (a : AbsVal) (s s' : CacheState) : Prop :=
    (Stable (cs_obj s) a -> Stable (cs_obj s') a) /\
    CacheHistValidExtension P (cs_hist s) (cs_hist s') (cs_obj s) (cs_obj s') a.

  Definition CacheRely (a : AbsVal) : CacheState -> CacheState -> Prop :=
    CacheInterference a.

  Definition CacheGuar (a : AbsVal) : CacheState -> CacheState -> Prop :=
    CacheInterference a.

  Lemma cache_interference_refl : forall a s,
    CacheInterference a s s.
  Proof.
    intros a s. split; [intros H; exact H |].
    apply cache_hist_valid_extension_refl.
  Qed.

  Lemma cache_interference_trans : forall a s1 s2 s3,
    CacheInterference a s1 s2 ->
    CacheInterference a s2 s3 ->
    CacheInterference a s1 s3.
  Proof.
    intros a s1 s2 s3 [Hstable12 Hext12] [Hstable23 Hext23].
    split.
    - intros H. exact (Hstable23 (Hstable12 H)).
    - eapply cache_hist_valid_extension_trans; eassumption.
  Qed.

  (** Every thread's guarantee is included in every other thread's rely. *)
  Lemma cache_guar_in_rely : forall a s s',
    CacheGuar a s s' -> CacheRely a s s'.
  Proof. intros a s s' H. exact H. Qed.

  (** Semantic immutability is stable under the rely. *)
  Theorem semimm_stable_under_rely : forall a s s',
    SemImmAt a s ->
    CacheRely a s s' ->
    SemImmAt a s'.
  Proof.
    intros a s s' [Hstable Hhist] [Hstable_step Hext].
    split.
    - exact (Hstable_step Hstable).
    - eapply cache_hist_ok_valid_extension; eassumption.
  Qed.

  (** A read observes some whole value already in the field's history. *)
  Definition CacheReadAt (s : CacheState) (obs : CacheObs P) : Prop :=
    In (obs_value obs) (cs_hist s (cs_obj s) (obs_field obs)).

  (** An own write appends exactly one value to one cache field.  Its effect
      on the stable abstraction is the abstract-state half of the guarantee,
      which a type system supplies; it is a premise of the step, not derived
      from the written value. *)
  Definition CacheOwnWrite (a : AbsVal)
      (s : CacheState) (w : CacheObs P) (s' : CacheState) : Prop :=
    (Stable (cs_obj s) a -> Stable (cs_obj s') a) /\
    CacheHistExtendsByTrace P (cs_hist s) (cs_hist s') (cs_obj s) (cs_obj s') [w].

  (** The read phase: reads of the current histories interleaved with
      environment steps that satisfy the rely. *)
  Inductive rg_read_phase (a : AbsVal) :
      CacheState -> CacheTrace P -> CacheState -> Prop :=
    | RGReadDone : forall s,
        rg_read_phase a s [] s
    | RGReadEnv : forall s s1 tr s2,
        CacheRely a s s1 ->
        rg_read_phase a s1 tr s2 ->
        rg_read_phase a s tr s2
    | RGRead : forall s obs tr s2,
        CacheReadAt s obs ->
        rg_read_phase a s tr s2 ->
        rg_read_phase a s (obs :: tr) s2.

  (** The write phase: own writes interleaved with environment steps. *)
  Inductive rg_write_phase (a : AbsVal) :
      CacheState -> CacheTrace P -> CacheState -> Prop :=
    | RGWriteDone : forall s,
        rg_write_phase a s [] s
    | RGWriteEnv : forall s s1 ws s2,
        CacheRely a s s1 ->
        rg_write_phase a s1 ws s2 ->
        rg_write_phase a s ws s2
    | RGWrite : forall s w s1 ws s2,
        CacheOwnWrite a s w s1 ->
        rg_write_phase a s1 ws s2 ->
        rg_write_phase a s (w :: ws) s2.

  (** Every own step allowed by the write phase with a valid value is a
      guarantee step. *)
  Lemma cache_own_valid_write_guar : forall a s w s',
    CacheOwnWrite a s w s' ->
    ValidObs P a w ->
    CacheGuar a s s'.
  Proof.
    intros a s w s' [Hstable Hext] Hvalid.
    split; [exact Hstable |].
    eapply cache_hist_extends_by_valid_trace; [| exact Hext].
    constructor; [exact Hvalid | constructor].
  Qed.

  (** Every guarantee step of the write phase: the own writes, when valid,
      and the environment steps are all interference steps, so the whole
      phase is one interference step. *)
  Lemma rg_write_phase_interference : forall a s ws s',
    rg_write_phase a s ws s' ->
    ValidTrace P a ws ->
    CacheInterference a s s'.
  Proof.
    intros a s ws s' Hphase.
    induction Hphase as [s | s s1 ws s2 Hrely Htail IH
      | s w s1 ws s2 Hwrite Htail IH]; intros Hvalid.
    - apply cache_interference_refl.
    - eapply cache_interference_trans; [exact Hrely | exact (IH Hvalid)].
    - inversion Hvalid as [| w0 ws0 Hw Hws]; subst.
      eapply cache_interference_trans.
      + exact (cache_own_valid_write_guar a s w s1 Hwrite Hw).
      + exact (IH Hws).
  Qed.

  (** Reads interleaved with rely steps observe valid values and preserve
      semantic immutability. *)
  Lemma rg_read_phase_valid : forall a s tr s',
    rg_read_phase a s tr s' ->
    SemImmAt a s ->
    ValidTrace P a tr /\ SemImmAt a s'.
  Proof.
    intros a s tr s' Hphase.
    induction Hphase as [s | s s1 tr s2 Hrely Htail IH
      | s obs tr s2 Hread Htail IH]; intros Hsem.
    - split; [constructor | exact Hsem].
    - apply IH. eapply semimm_stable_under_rely; eassumption.
    - destruct (IH Hsem) as [Htr Hsem'].
      split; [| exact Hsem'].
      constructor; [| exact Htr].
      destruct Hsem as [_ Hhist].
      exact (Hhist (obs_field obs) (obs_value obs) Hread).
  Qed.

  (** Rely-guarantee specification of a trace-robust method.  From a state
      satisfying semantic immutability, a method whose reads and writes are
      interleaved with arbitrary rely steps returns the pure result, emits
      only valid writes, performs only guarantee steps, and ends in a state
      satisfying semantic immutability. *)
  Theorem cache_method_rely_guarantee :
    forall {Args Result : Type}
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      a args s0 s1 s2 tr,
      CacheSafeMethod P F run_with_cache_trace ->
      SemImmAt a s0 ->
      rg_read_phase a s0 tr s1 ->
      rg_write_phase a s1 (run_writes (run_with_cache_trace a args tr)) s2 ->
      run_result (run_with_cache_trace a args tr) = F a args /\
      ValidTrace P a (run_writes (run_with_cache_trace a args tr)) /\
      CacheGuar a s1 s2 /\
      SemImmAt a s2.
  Proof.
    intros Args Result F run a args s0 s1 s2 tr Hsafe Hsem0 Hreads Hwrites.
    destruct (rg_read_phase_valid a s0 tr s1 Hreads Hsem0) as [Htr Hsem1].
    destruct (Hsafe a args tr Htr) as [Hresult Hvalid_writes].
    pose proof (rg_write_phase_interference a s1 _ s2 Hwrites Hvalid_writes) as Hinterf.
    split; [exact Hresult |].
    split; [exact Hvalid_writes |].
    split; [exact Hinterf |].
    eapply semimm_stable_under_rely; eassumption.
  Qed.
End rely_guarantee.
