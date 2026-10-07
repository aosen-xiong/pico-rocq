From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping Bigstep Properties Reachability
  Preservation.
Require Import Core.GenericCacheProtocol Core.GenericDerivedCache.
Require Import Examples.PicoIfZeroCache Examples.PicoHashMethod
  Examples.PicoConcreteHashProvider Examples.PicoCacheMethodJudgment.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoCacheTyping
  PICOBridge.PicoDerivationCache PICOBridge.PicoCoreLanguage
  PICOBridge.PicoCoreSemImm PICOBridge.PicoDerivationNoninterference
  PICOBridge.PicoDerivationSmallStep PICOBridge.PicoDerivationPrefix
  PICOBridge.PicoCoreTraceRobust PICOBridge.PicoCoreFrame.

(** * A Flow Judgment for Cache Methods

    The cache-method judgment of [PicoCacheMethodJudgment] accepts one shape
    of method body.  This file states the rules as a flow judgment over
    arbitrary statements and proves the judgment sound.

    The judgment tracks, for each local variable, where its value comes
    from: the receiver, an unchecked read of the cache field, the cache
    field's sentinel, the derived value, or anything else.  A read of the
    cache field yields an unchecked value.  Testing an unchecked value
    against the sentinel refines it: to the sentinel on one branch and to
    the derived value on the other.  A write to the cache field must store
    the derived value, and the method must return the derived value.  All
    other code is derivation code, whose effect on the abstract store is
    given by its sequential evaluation in the reference heap.

    A method accepted by the judgment is trace robust on the core machine:
    under every interleaving and every valid cache read, each write it
    performs stores a valid value, and if it returns normally it returns the
    protocol's value.  The proof does not use that the cache field is read
    only once.  A value that is read is unchecked until it is tested, so a
    second read cannot be returned or written without its own test. *)

(** ** Origins *)

Inductive origin : Type :=
  | OThis
  | OUnchecked
  | OSentinel
  | ODerived
  | OOther.

Definition origin_le (o o' : origin) : Prop :=
  o = o' \/ o' = OOther \/
  (o' = OUnchecked /\ (o = OSentinel \/ o = ODerived)).

Lemma origin_le_refl : forall o, origin_le o o.
Proof. intros o. left. reflexivity. Qed.

Lemma origin_le_trans :
  forall o1 o2 o3, origin_le o1 o2 -> origin_le o2 o3 -> origin_le o1 o3.
Proof.
  intros o1 o2 o3 H12 H23.
  destruct o1, o2, o3;
    unfold origin_le in *;
    repeat match goal with
           | H : _ \/ _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           end;
    try discriminate; auto.
Qed.

Lemma origin_le_derived : forall o, origin_le o ODerived -> o = ODerived.
Proof.
  intros o [H | [H | [H _]]]; [exact H | discriminate | discriminate].
Qed.

(** ** Lists *)

Lemma Forall2_refl_le : forall G, Forall2 origin_le G G.
Proof. induction G; constructor; [apply origin_le_refl | assumption]. Qed.

Lemma Forall2_trans_le :
  forall G1 G2 G3,
    Forall2 origin_le G1 G2 -> Forall2 origin_le G2 G3 ->
    Forall2 origin_le G1 G3.
Proof.
  intros G1 G2 G3 H12. revert G3.
  induction H12; intros G3 H23; inversion H23; subst; constructor.
  - eapply origin_le_trans; eassumption.
  - apply IHForall2. assumption.
Qed.

Lemma Forall2_nth_left :
  forall {A B : Type} (R : A -> B -> Prop) l1 l2 i a,
    Forall2 R l1 l2 -> nth_error l1 i = Some a ->
    exists b, nth_error l2 i = Some b /\ R a b.
Proof.
  intros A B R l1 l2 i a Hall. revert i.
  induction Hall; intros i Hnth.
  - destruct i; discriminate.
  - destruct i as [| i]; simpl in *.
    + injection Hnth as <-. eauto.
    + apply IHHall. exact Hnth.
Qed.

Lemma Forall2_nth_right :
  forall {A B : Type} (R : A -> B -> Prop) l1 l2 i b,
    Forall2 R l1 l2 -> nth_error l2 i = Some b ->
    exists a, nth_error l1 i = Some a /\ R a b.
Proof.
  intros A B R l1 l2 i b Hall. revert i.
  induction Hall; intros i Hnth.
  - destruct i; discriminate.
  - destruct i as [| i]; simpl in *.
    + injection Hnth as <-. eauto.
    + apply IHHall. exact Hnth.
Qed.

Lemma Forall2_update_both :
  forall {A B : Type} (R : A -> B -> Prop) l1 l2 i a b,
    Forall2 R l1 l2 -> R a b ->
    Forall2 R (update i a l1) (update i b l2).
Proof.
  intros A B R l1 l2 i a b Hall Hab. revert i.
  induction Hall; intros i.
  - destruct i; constructor.
  - destruct i as [| i]; simpl; constructor; auto.
Qed.

Lemma Forall2_le_derived :
  forall G G' i,
    Forall2 origin_le G G' -> nth_error G' i = Some ODerived ->
    nth_error G i = Some ODerived.
Proof.
  intros G G' i Hle Hnth.
  destruct (Forall2_nth_right _ _ _ _ _ Hle Hnth) as (o & Ho & Hl).
  apply origin_le_derived in Hl. subst o. exact Ho.
Qed.

(** ** Two facts about steps *)

(** Only a finished control steps to a normal result. *)
Lemma step_done_ok_inv :
  forall `{Hmem : CacheMemoryModel} CT rGamma s V K S rGamma' V' S',
    pico_core_step CT (CoreRun rGamma s V K) S (CoreDone OK rGamma' V') S' ->
    s = SSkip /\ K = [].
Proof.
  intros Hmem CT rGamma s V K S rGamma' V' S' Hstep.
  inversion Hstep; subst; auto.
Qed.

Section flow_judgment.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table) (D : method_def -> Prop).
  Context (receiver : Loc) (m : method_name) (h0 : heap) (H : nat).
  Context (mc : method_name) (mdef : method_def).
  Context (Trecv : qualified_type) (mt : method_scope).
  Context (rt0 : runtime_type) (fs0 : fields_mapping).
  Context (caller : r_env) (x y : var).

  Let footprint := reachable_abs CT h0 receiver.
  Let rho1 := mkr_env [Iot receiver].
  Let body := mbody_stmt (mbody mdef).
  Let ret := mreturn (mbody mdef).
  Let Kc : pico_core_cont := [KCall caller x ret].
  Let caller_done : r_env := set_vars caller (update x (Int H) (vars caller)).

  (** ** What an origin says about a value *)

  Definition flow_valid_read (v : value) : Prop :=
    v = Int 0 \/ (v = Int H /\ H <> 0).

  Definition sem_origin (o : origin) (v : value) : Prop :=
    match o with
    | OThis => v = Iot receiver
    | OUnchecked => flow_valid_read v
    | OSentinel => v = Int 0
    | ODerived => v = Int H
    | OOther => True
    end.

  Definition sem (G : list origin) (rho : r_env) : Prop :=
    Forall2 sem_origin G (vars rho).

  Lemma sem_origin_le :
    forall o o' v, origin_le o o' -> sem_origin o v -> sem_origin o' v.
  Proof.
    intros o o' v [-> | [-> | [-> [-> | ->]]]] Hs; simpl in *; auto.
    - left. exact Hs.
    - destruct (Nat.eq_dec H 0) as [Hz | Hnz].
      + left. rewrite Hs Hz. reflexivity.
      + right. split; assumption.
  Qed.

  Lemma sem_le :
    forall G G' rho, Forall2 origin_le G G' -> sem G rho -> sem G' rho.
  Proof.
    unfold sem. intros G G' rho Hle. generalize (vars rho).
    induction Hle; intros vs Hs; inversion Hs; subst; constructor.
    - eapply sem_origin_le; eassumption.
    - apply IHHle. assumption.
  Qed.

  Lemma sem_get :
    forall G rho i o,
      sem G rho -> nth_error G i = Some o ->
      exists v, runtime_getVal rho i = Some v /\ sem_origin o v.
  Proof.
    intros G rho i o Hs Hnth.
    exact (Forall2_nth_left _ _ _ _ _ Hs Hnth).
  Qed.

  Lemma sem_update :
    forall G rho i o v,
      sem G rho -> sem_origin o v ->
      sem (update i o G) (set_vars rho (update i v (vars rho))).
  Proof.
    intros G rho i o v Hs Hv. unfold sem. simpl.
    apply Forall2_update_both; assumption.
  Qed.

  (** ** Refinement at the default test *)

  Definition refine_zero (G : list origin) (t : var) : list origin :=
    match nth_error G t with
    | Some OUnchecked => update t OSentinel G
    | _ => G
    end.

  Definition refine_nonzero (G : list origin) (t : var) : list origin :=
    match nth_error G t with
    | Some OUnchecked => update t ODerived G
    | _ => G
    end.

  Lemma set_vars_same :
    forall rho, set_vars rho (vars rho) = rho.
  Proof. intros [vs]. reflexivity. Qed.

  Lemma update_self :
    forall {A : Type} (l : list A) i a,
      nth_error l i = Some a -> update i a l = l.
  Proof.
    intros A l. induction l as [| b l IH]; intros i a Hnth.
    - destruct i; reflexivity.
    - destruct i as [| i]; simpl in *.
      + injection Hnth as ->. reflexivity.
      + f_equal. apply IH. exact Hnth.
  Qed.

  Lemma sem_refine_zero :
    forall G rho t v,
      sem G rho -> runtime_getVal rho t = Some v ->
      (v = Int 0 \/ v = Null_a) ->
      sem (refine_zero G t) rho.
  Proof.
    intros G rho t v Hs Hv Hzero. unfold refine_zero.
    destruct (nth_error G t) as [[| | | |] |] eqn:Hnth; try exact Hs.
    destruct (sem_get _ _ _ _ Hs Hnth) as (v' & Hv' & Hvalid).
    rewrite Hv in Hv'. injection Hv' as <-.
    assert (Hv0 : v = Int 0).
    { destruct Hzero as [-> | ->]; [reflexivity |].
      destruct Hvalid as [Hn | [Hn _]]; discriminate. }
    subst v.
    have Hupd := sem_update G rho t OSentinel (Int 0) Hs eq_refl.
    unfold runtime_getVal in Hv.
    rewrite (update_self _ _ _ Hv) in Hupd.
    rewrite set_vars_same in Hupd. exact Hupd.
  Qed.

  Lemma sem_refine_nonzero :
    forall G rho t v,
      sem G rho -> runtime_getVal rho t = Some v ->
      ((exists n, v = Int (S n)) \/ (exists l, v = Iot l)) ->
      sem (refine_nonzero G t) rho.
  Proof.
    intros G rho t v Hs Hv Hnz. unfold refine_nonzero.
    destruct (nth_error G t) as [[| | | |] |] eqn:Hnth; try exact Hs.
    destruct (sem_get _ _ _ _ Hs Hnth) as (v' & Hv' & Hvalid).
    rewrite Hv in Hv'. injection Hv' as <-.
    assert (HvH : v = Int H).
    { destruct Hvalid as [-> | [-> _]]; [| reflexivity].
      destruct Hnz as [(n & Hn) | (l & Hl)]; discriminate. }
    have Hupd := sem_update G rho t ODerived v Hs HvH.
    unfold runtime_getVal in Hv.
    rewrite (update_self _ _ _ Hv) in Hupd.
    rewrite set_vars_same in Hupd. exact Hupd.
  Qed.

  (** ** The judgment *)

  (** [flow sG G s sG' G'] says that statement [s] takes the abstract store
      [G] to [G'], in the static environment [sG], which it extends to
      [sG'].  Derivation code is a leaf: its effect is whatever its
      sequential evaluation in the reference heap establishes. *)
  Inductive flow :
      s_env -> list origin -> stmt -> s_env -> list origin -> Prop :=
    | F_Skip : forall sG G,
        flow sG G SSkip sG G
    | F_Seq : forall sG G s1 sG1 G1 G1' s2 sG2 G2,
        flow sG G s1 sG1 G1 ->
        Forall2 origin_le G1 G1' ->
        flow sG1 G1' s2 sG2 G2 ->
        flow sG G (SSeq s1 s2) sG2 G2
    | F_If : forall sG G t s0 s1 sG' G0 G1 G',
        flow sG (refine_zero G t) s0 sG' G0 ->
        flow sG (refine_nonzero G t) s1 sG' G1 ->
        Forall2 origin_le G0 G' ->
        Forall2 origin_le G1 G' ->
        flow sG G (SIfZero t s0 s1) sG' G'
    | F_Read : forall sG G t yv,
        nth_error G yv = Some OThis ->
        (* [t] is an integer local.  The premise is stated as a typing fact
           because the proof uses it to keep the frame well formed after
           the read. *)
        (forall n, stmt_typing CT sG mt (SVarAss t (EInt n)) sG) ->
        flow sG G (SVarAss t (EField yv hash_cache_field)) sG
          (update t OUnchecked G)
    | F_Write : forall sG G yv z,
        nth_error G yv = Some OThis ->
        nth_error G z = Some ODerived ->
        flow sG G (SFldWrite yv hash_cache_field z) sG G
    | F_Deriv : forall sG G d sG' G',
        d <> SSkip ->
        deriv_stmt CT D sG d sG' ->
        stmt_typing CT sG mt d sG' ->
        (forall rho rho1,
           sem G rho ->
           eval_stmt CT rho h0 d OK rho1 h0 ->
           sem G' rho1) ->
        flow sG G d sG' G'.

  (** The rest of the method body, as a stack of pending statements, ends
      with the returned variable holding the derived value. *)
  Inductive cont_flow : s_env -> list origin -> pico_core_cont -> Prop :=
    | CF_Nil : forall sG G,
        nth_error G ret = Some ODerived ->
        cont_flow sG G []
    | CF_Seq : forall sG G s sG' G' G'' K,
        flow sG G s sG' G' ->
        Forall2 origin_le G' G'' ->
        cont_flow sG' G'' K ->
        cont_flow sG G (KSeq s :: K).

  (** ** Rules for leaf statements

      The leaf rule for derivation code is semantic.  The usual leaves
      follow from it. *)

  Lemma flow_local :
    forall sG G T t,
      stmt_typing CT sG mt (SLocal T t) (sG ++ [T]) ->
      flow sG G (SLocal T t) (sG ++ [T]) (G ++ [OOther]).
  Proof.
    intros sG G T t Htyped. apply F_Deriv.
    - discriminate.
    - apply DS_Local.
    - exact Htyped.
    - intros rho rhob Hs Heval. inversion Heval; subst.
      unfold sem. simpl. apply Forall2_app; [exact Hs |].
      constructor; [exact I | constructor].
  Qed.

  (** A fresh integer local holds the sentinel. *)
  Lemma flow_local_int :
    forall sG G t,
      stmt_typing CT sG mt (SLocal int_type t) (sG ++ [int_type]) ->
      flow sG G (SLocal int_type t) (sG ++ [int_type]) (G ++ [OSentinel]).
  Proof.
    intros sG G t Htyped. apply F_Deriv.
    - discriminate.
    - apply DS_Local.
    - exact Htyped.
    - intros rho rhob Hs Heval. inversion Heval; subst.
      unfold sem. simpl. apply Forall2_app; [exact Hs |].
      constructor; [reflexivity | constructor].
  Qed.

  (** An assignment of an expression that reads only locals, literals and
      abstract fields. *)
  Lemma flow_assign :
    forall sG G t e,
      ts_expr_reads_only_stable CT sG e ->
      stmt_typing CT sG mt (SVarAss t e) sG ->
      flow sG G (SVarAss t e) sG (update t OOther G).
  Proof.
    intros sG G t e Hexpr Htyped. apply F_Deriv.
    - discriminate.
    - apply DS_VarAss. exact Hexpr.
    - exact Htyped.
    - intros rho rhob Hs Heval. inversion Heval; subst.
      apply sem_update; [exact Hs | exact I].
  Qed.

  (** A copy keeps the origin. *)
  Lemma flow_copy :
    forall sG G t z o,
      stmt_typing CT sG mt (SVarAss t (EVar z)) sG ->
      nth_error G z = Some o ->
      flow sG G (SVarAss t (EVar z)) sG (update t o G).
  Proof.
    intros sG G t z o Htyped Hz. apply F_Deriv.
    - discriminate.
    - apply DS_VarAss. apply TSERO_Var.
    - exact Htyped.
    - intros rho rhob Hs Heval. inversion Heval; subst.
      destruct (sem_get _ _ _ _ Hs Hz) as (v & Hv & Hov).
      match goal with
      | He : eval_expr _ _ _ (EVar z) _ _ _ _ |- _ => inversion He; subst
      end.
      match goal with
      | Hval : runtime_getVal rho z = Some ?w |- _ =>
          rewrite Hv in Hval; injection Hval as <-
      end.
      apply sem_update; assumption.
  Qed.

  (** A call of the protocol's derivation method on the receiver yields
      the derived value. *)
  Lemma derivation_call_sem :
    forall G t yv rho rhob,
      derived_by CT m h0 receiver (Int H) ->
      nth_error G yv = Some OThis ->
      sem G rho ->
      eval_stmt CT rho h0 (SCall t m yv []) OK rhob h0 ->
      sem (update t ODerived G) rhob.
  Proof.
    intros G t yv rho rhob
      (cy0 & mdef0 & rG0 & Hbase0 & Hfind0 & Heval0 & Hret0) Hthis Hs Heval.
    destruct (sem_get _ _ _ _ Hs Hthis) as (v & Hv & Hrecv).
    simpl in Hrecv. subst v.
    inversion Heval; subst.
    match goal with
    | Hvy : runtime_getVal rho yv = Some (Iot ?l) |- _ =>
        rewrite Hv in Hvy; injection Hvy as <-
    end.
    match goal with
    | Hb : r_basetype h0 receiver = Some ?c,
      Hf : FindMethodWithName CT ?c m ?md /\ _,
      Ha : runtime_lookup_list _ [] = Some ?vs,
      Hbody : eval_stmt CT _ h0 _ OK ?rG h0,
      Hr : runtime_getVal ?rG _ = Some ?rv |- _ =>
        rewrite Hbase0 in Hb; injection Hb as <-;
        destruct Hf as [Hf ->];
        have Hmd := find_method_with_name_deterministic CT _ _ _ _ Hf Hfind0;
        subst md; simpl in Ha; injection Ha as <-;
        destruct (eval_stmt_deterministic _ _ _ _ _ _ _ _ _ _ Hbody Heval0)
          as (_ & HrG & _);
        subst rG; rewrite Hret0 in Hr; injection Hr as <-
    end.
    apply sem_update; [exact Hs | reflexivity].
  Qed.

  Lemma flow_derivation_call :
    forall sG G t yv sG',
      derived_by CT m h0 receiver (Int H) ->
      deriv_stmt CT D sG (SCall t m yv []) sG' ->
      stmt_typing CT sG mt (SCall t m yv []) sG' ->
      nth_error G yv = Some OThis ->
      flow sG G (SCall t m yv []) sG' (update t ODerived G).
  Proof.
    intros sG G t yv sG' Hderived Hderiv Htyped Hthis. apply F_Deriv.
    - discriminate.
    - exact Hderiv.
    - exact Htyped.
    - intros rho rhob Hs Heval.
      eapply derivation_call_sem; eassumption.
  Qed.

  (** ** The local-copy method is accepted

      The method reads the cache field into a local, tests the local,
      computes and writes on a miss, and returns the local. *)
  Lemma local_copy_flow :
    forall compute,
      let sG3 := [Trecv; int_type; int_type] in
      stmt_typing CT [Trecv] mt (SLocal int_type cache_tmp)
        [Trecv; int_type] ->
      stmt_typing CT [Trecv; int_type] mt (SLocal int_type cache_result)
        sG3 ->
      (forall n, stmt_typing CT sG3 mt (SVarAss cache_tmp (EInt n)) sG3) ->
      stmt_typing CT sG3 mt (SVarAss cache_result (EVar cache_tmp)) sG3 ->
      compute <> SSkip ->
      deriv_stmt CT D sG3 compute sG3 ->
      stmt_typing CT sG3 mt compute sG3 ->
      (forall rho rhob,
         sem [OThis; OSentinel; OSentinel] rho ->
         eval_stmt CT rho h0 compute OK rhob h0 ->
         sem [OThis; ODerived; OOther] rhob) ->
      flow [Trecv] [OThis] (pico_hash_method_stmt_with compute) sG3
        [OThis; ODerived; ODerived].
  Proof.
    intros compute sG3 Hl1 Hl2 Hint Hcopy Hns Hderiv Htyped Hcompute.
    unfold pico_hash_method_stmt_with, pico_hash_method_core_stmt_with,
      pico_local_copy_cache_stmt, pico_local_copy_cache_branch.
    eapply F_Seq.
    { exact (flow_local_int [Trecv] [OThis] cache_tmp Hl1). }
    { apply Forall2_refl_le. }
    eapply F_Seq.
    { exact (flow_local_int [Trecv; int_type] [OThis; OSentinel]
               cache_result Hl2). }
    { apply Forall2_refl_le. }
    eapply F_Seq.
    { apply (F_Read sG3 [OThis; OSentinel; OSentinel] cache_tmp
               cache_receiver); [reflexivity | exact Hint]. }
    { apply Forall2_refl_le. }
    eapply F_Seq.
    { apply (F_If sG3 [OThis; OUnchecked; OSentinel] cache_tmp _ _ sG3
               [OThis; ODerived; OOther] [OThis; ODerived; OSentinel]
               [OThis; ODerived; OOther]).
      - eapply F_Seq.
        + apply (F_Deriv sG3 [OThis; OSentinel; OSentinel] compute sG3
                   [OThis; ODerived; OOther]); assumption.
        + apply Forall2_refl_le.
        + apply F_Write; reflexivity.
      - apply F_Skip.
      - apply Forall2_refl_le.
      - constructor; [apply origin_le_refl |].
        constructor; [apply origin_le_refl |].
        constructor; [right; left; reflexivity | constructor]. }
    { apply Forall2_refl_le. }
    exact (flow_copy sG3 [OThis; ODerived; OOther] cache_result cache_tmp
             ODerived Hcopy eq_refl).
  Qed.

  (** ** The double read is rejected

      The method that reads the cache field again for its result is not
      accepted: the second read is unchecked, and derivation code cannot
      read a field that is not abstract. *)

  Lemma deriv_stmt_keeps_receiver :
    forall sG d sG' T,
      deriv_stmt CT D sG d sG' ->
      static_getType sG cache_receiver = Some T ->
      static_getType sG' cache_receiver = Some T.
  Proof.
    intros sG d sG' T Hd. induction Hd; intros Hg; auto.
    match goal with
    | |- static_getType (?l ++ _) _ = _ =>
        destruct l; [discriminate | exact Hg]
    end.
  Qed.

  Lemma flow_keeps_receiver :
    forall sG G s sG' G' T,
      flow sG G s sG' G' ->
      static_getType sG cache_receiver = Some T ->
      static_getType sG' cache_receiver = Some T.
  Proof.
    intros sG G s sG' G' T Hfl. induction Hfl; intros Hg; auto.
    eapply deriv_stmt_keeps_receiver; eassumption.
  Qed.

  Lemma cache_read_not_deriv :
    forall sG t sG' T C,
      static_getType sG cache_receiver = Some T ->
      sbase T = TRef C ->
      ~ abstract_field CT C hash_cache_field ->
      deriv_stmt CT D sG
        (SVarAss t (EField cache_receiver hash_cache_field)) sG' ->
      False.
  Proof.
    intros sG t sG' T C Hg Hb Hna Hd. inversion Hd; subst.
    match goal with
    | He : ts_expr_reads_only_stable _ _ (EField _ _) |- _ =>
        inversion He; subst
    end.
    match goal with
    | Hg' : static_getType _ cache_receiver = Some ?T',
      Hb' : sbase ?T' = TRef ?C',
      Ha : abstract_field CT ?C' hash_cache_field |- _ =>
        rewrite Hg' in Hg; injection Hg as <-;
        rewrite Hb' in Hb; injection Hb as <-;
        exact (Hna Ha)
    end.
  Qed.

  Lemma double_read_not_flow :
    forall compute sG G sG' G' T C,
      static_getType sG cache_receiver = Some T ->
      sbase T = TRef C ->
      ~ abstract_field CT C hash_cache_field ->
      flow sG G (pico_double_read_cache_stmt compute) sG' G' ->
      nth_error G' cache_result = Some ODerived ->
      False.
  Proof.
    intros compute sG G sG' G' T C Hg Hb Hna Hfl Hres.
    unfold pico_double_read_cache_stmt in Hfl.
    inversion Hfl as
      [ | ? ? ? sGa ? Ga' ? ? ? Hfl1 _ Hfl2 | | | | ? ? ? ? ? _ Hd _ _ ]; subst.
    - have Hga := flow_keeps_receiver _ _ _ _ _ T Hfl1 Hg.
      inversion Hfl2 as
        [ | ? ? ? sGb ? Gb' ? ? ? Hfl3 _ Hfl4 | | | | ? ? ? ? ? _ Hd _ _ ];
        subst.
      + have Hgb := flow_keeps_receiver _ _ _ _ _ T Hfl3 Hga.
        inversion Hfl4 as [ | | | | | ? ? ? ? ? _ Hd _ _ ]; subst.
        * destruct (Nat.lt_ge_cases cache_result (length Gb')) as [Hlt | Hge].
          -- rewrite (update_same _ _ _ _ Hlt) in Hres. discriminate.
          -- assert (Hnone :
               nth_error (update cache_result OUnchecked Gb') cache_result
                 = None).
             { apply nth_error_None. rewrite update_length. exact Hge. }
             rewrite Hnone in Hres. discriminate.
        * exact (cache_read_not_deriv _ _ _ _ _ Hgb Hb Hna Hd).
      + inversion Hd; subst.
        match goal with
        | Hd1 : deriv_stmt _ _ sGa (pico_local_copy_cache_branch _) ?sGm,
          Hd2 : deriv_stmt _ _ ?sGm (SVarAss _ _) _ |- _ =>
            exact (cache_read_not_deriv _ _ _ _ _
                     (deriv_stmt_keeps_receiver _ _ _ T Hd1 Hga) Hb Hna Hd2)
        end.
    - inversion Hd; subst.
      match goal with
      | Hd1 : deriv_stmt _ _ sG (SVarAss _ (EField _ _)) _ |- _ =>
          exact (cache_read_not_deriv _ _ _ _ _ Hg Hb Hna Hd1)
      end.
  Qed.

  (** ** Assumptions about the method and the receiver *)

  Hypothesis Htable : derivation_table CT D.
  Hypothesis Hwf1 : wf_r_config CT [Trecv] rho1 h0.
  Hypothesis Hobj0 : runtime_getObj h0 receiver = Some (mkObj rt0 fs0).
  Hypothesis Hcachefield :
    derived_cache_field CT (rctype rt0) hash_cache_field.
  Hypothesis Hfind : FindMethodWithName CT (rctype rt0) mc mdef.
  Hypothesis Hy : runtime_getVal caller y = Some (Iot receiver).

  (** The body is accepted, and returns the derived value. *)
  Variables (sGbody : s_env) (Gbody : list origin).
  Hypothesis Hflow : flow [Trecv] [OThis] body sGbody Gbody.
  Hypothesis Hreturn : nth_error Gbody ret = Some ODerived.

  Notation hash_machine := (pico_concrete_hash_semimm CT receiver m h0 H).
  Notation hash_inv :=
    (machine_inv hash_cache_protocol pico_hash_stable_abs H
       (pico_hash_cache_adapter receiver) hash_machine).
  Notation hash_run :=
    (thread_run CT hash_cache_protocol pico_hash_stable_abs H
       (pico_hash_cache_adapter receiver) hash_machine).

  Lemma flow_receiver_in_footprint : footprint receiver.
  Proof.
    apply reachable_abs_heap. eapply runtime_getObj_dom. exact Hobj0.
  Qed.

  Lemma flow_footprint_dom :
    forall l, footprint l ->
      exists rt fs, runtime_getObj h0 l = Some (mkObj rt fs).
  Proof.
    intros l Hl.
    have Hdom := reachable_abs_target_dom CT h0 receiver l Hl.
    unfold runtime_getObj.
    destruct (nth_error h0 l) as [[rt fs] |] eqn:Hnth.
    - eauto.
    - apply nth_error_None in Hnth. lia.
  Qed.

  Lemma rho1_in_footprint : env_in footprint rho1.
  Proof.
    intros z l Hz. destruct z as [| z]; simpl in Hz.
    - injection Hz as <-. exact flow_receiver_in_footprint.
    - destruct z; discriminate.
  Qed.

  Lemma env_in_update_int :
    forall rho t n,
      env_in footprint rho ->
      env_in footprint (set_vars rho (update t (Int n) (vars rho))).
  Proof.
    intros rho t n Hin z l Hz.
    unfold runtime_getVal in Hz. simpl in Hz.
    destruct (Nat.eq_dec t z) as [-> | Hne].
    - destruct (Nat.lt_ge_cases z (length (vars rho))) as [Hlt | Hge].
      + rewrite (update_same _ _ _ _ Hlt) in Hz. discriminate.
      + assert (Hlt : z < length (update z (Int n) (vars rho))).
        { apply nth_error_Some. rewrite Hz. discriminate. }
        rewrite update_length in Hlt. lia.
    - rewrite (update_diff _ _ _ _ _ Hne) in Hz. exact (Hin z l Hz).
  Qed.

  (** ** The phases of a call *)

  Inductive flow_phase : pico_core_expr -> Prop :=
    | FP_Call : forall V,
        flow_phase (CoreRun caller (SCall x mc y []) V [])
    | FP_Body : forall sG G rho s V sG1 G1 G1' Kb,
        flow sG G s sG1 G1 ->
        Forall2 origin_le G1 G1' ->
        cont_flow sG1 G1' Kb ->
        sem G rho ->
        wf_r_config CT sG rho h0 ->
        env_in footprint rho ->
        flow_phase (CoreRun rho s V (Kb ++ Kc))
    | FP_Deriv : forall sG G rho d V0 sG1 G1 G1' Kb n r s V K1,
        deriv_stmt CT D sG d sG1 ->
        stmt_typing CT sG mt d sG1 ->
        (forall rhoa rhob,
           sem G rhoa ->
           eval_stmt CT rhoa h0 d OK rhob h0 ->
           sem G1 rhob) ->
        Forall2 origin_le G1 G1' ->
        cont_flow sG1 G1' Kb ->
        sem G rho ->
        wf_r_config CT sG rho h0 ->
        env_in footprint rho ->
        footprint_steps CT footprint h0 n (CoreRun rho d V0 [])
          (CoreRun r s V K1) ->
        ~ (s = SSkip /\ K1 = []) ->
        flow_phase (CoreRun r s V (K1 ++ Kb ++ Kc))
    | FP_Resume : forall V,
        flow_phase (CoreRun caller_done SSkip V [])
    | FP_Done : forall V,
        flow_phase (CoreDone OK caller_done V)
    | FP_Failed : forall r rho V,
        r <> OK ->
        flow_phase (CoreDone r rho V).

  (** A control inside derivation code is running derivation code. *)
  Lemma deriv_phase_running :
    forall sG rho d V0 sG1 n r s V K1,
      deriv_stmt CT D sG d sG1 ->
      stmt_typing CT sG mt d sG1 ->
      wf_r_config CT sG rho h0 ->
      env_in footprint rho ->
      footprint_steps CT footprint h0 n (CoreRun rho d V0 [])
        (CoreRun r s V K1) ->
      ~ (s = SSkip /\ K1 = []) ->
      deriv_running CT footprint h0 [] (CoreRun r s V K1).
  Proof.
    intros sG rho d V0 sG1 n r s V K1 Hderiv Htyped Hwf Hin Hsteps Hnf.
    destruct (deriv_prefix CT D footprint h0 Htable flow_footprint_dom n n rho
      d V0 [] _ sG1 mt _ (le_n n) Hsteps Hderiv Htyped Hwf Hin)
      as [Hrun | [(rho1' & V1 & k & _ & _ & _ & Htail) | Hfail]].
    - exact Hrun.
    - exfalso. inversion Htail; subst.
      + apply Hnf. split; reflexivity.
      + match goal with
        | Hst : pico_core_step _ (CoreRun _ SSkip _ []) _ _ _ |- _ =>
            destruct (pico_core_skip_done_unique _ _ _ _ _ _ Hst) as [-> _]
        end.
        match goal with
        | Hrest : footprint_steps _ _ _ _ (CoreDone _ _ _) _ |- _ =>
            destruct (footprint_steps_done_inv _ _ _ _ _ _ _ _ Hrest)
              as [_ Heq]; discriminate
        end.
    - destruct Hfail as (r' & rG & V' & Heq & _). discriminate.
  Qed.

  Lemma cache_field_not_abstract_read :
    forall r s V K1 x' y',
      deriv_running CT footprint h0 [] (CoreRun r s V K1) ->
      s = SVarAss x' (EField y' hash_cache_field) ->
      runtime_getVal r y' = Some (Iot receiver) ->
      False.
  Proof.
    intros r s V K1 x' y' (rG & s' & V' & K' & Heq & _ & _ & _ & Hread)
      Hs Hy'.
    injection Heq as <- <- <- <-. subst s.
    destruct (Hread x' y' hash_cache_field receiver eq_refl Hy')
      as (_ & rt & fs & Hobj & Habs).
    rewrite Hobj0 in Hobj. injection Hobj as <- <-.
    exact (derived_cache_field_not_abstract CT _ _ Hcachefield Habs).
  Qed.

  (** A step of a control inside derivation code. *)
  Lemma deriv_phase_step :
    forall sG G rho d V0 sG1 G1 G1' Kb n r s V K1 S e' S',
      deriv_stmt CT D sG d sG1 ->
      stmt_typing CT sG mt d sG1 ->
      (forall rhoa rhob,
         sem G rhoa ->
         eval_stmt CT rhoa h0 d OK rhob h0 ->
         sem G1 rhob) ->
      Forall2 origin_le G1 G1' ->
      cont_flow sG1 G1' Kb ->
      sem G rho ->
      wf_r_config CT sG rho h0 ->
      env_in footprint rho ->
      footprint_steps CT footprint h0 n (CoreRun rho d V0 [])
        (CoreRun r s V K1) ->
      ~ (s = SSkip /\ K1 = []) ->
      hash_inv S ->
      pico_core_step CT (CoreRun r s V (K1 ++ Kb ++ Kc)) S e' S' ->
      flow_phase e'.
  Proof.
    intros sG G rho d V0 sG1 G1 G1' Kb n r s V K1 S e' S'
      Hderiv Htyped Hsem1 Hle Hcont Hsem Hwf Hin Hsteps Hnf Hinv Hstep.
    destruct (step_under_cont CT (Kb ++ Kc) r s V K1 S e' S' Hstep Hnf)
      as (e1' & Hstep1 & ->).
    have Hsteps' := footprint_steps_snoc CT footprint h0 _ _ _ _ _ _ Hsteps
      (hash_inv_footprint_state CT receiver m h0 H _ Hinv) Hstep1.
    destruct (deriv_prefix CT D footprint h0 Htable flow_footprint_dom _ _ rho
      d V0 [] _ sG1 mt _ (le_n _) Hsteps' Hderiv Htyped Hwf Hin)
      as [Hrun | [(rhof & V1 & k & _ & Heval & Hinf & Htail) | Hfail]].
    - destruct Hrun as (rG & s' & V' & K' & Heq & (Kabove & HK & Hnf') & _).
      subst e1'. rewrite app_nil_r in HK. subst K'. simpl.
      eapply FP_Deriv; eauto.
    - inversion Htail; subst.
      + simpl.
        change (CoreRun rhof SSkip V1 (Kb ++ Kc))
          with (CoreRun rhof SSkip V1 (Kb ++ Kc)).
        eapply FP_Body.
        * apply F_Skip.
        * exact Hle.
        * exact Hcont.
        * exact (Hsem1 _ _ Hsem Heval).
        * exact (preservation_pico CT _ mt _ _ _ _ _ _ Hwf Htyped Heval).
        * exact Hinf.
      + exfalso.
        match goal with
        | Hst : pico_core_step _ (CoreRun _ SSkip _ []) _ _ _ |- _ =>
            destruct (pico_core_skip_done_unique _ _ _ _ _ _ Hst) as [-> _]
        end.
        match goal with
        | Hrest : footprint_steps _ _ _ _ (CoreDone _ _ _) _ |- _ =>
            destruct (footprint_steps_done_inv _ _ _ _ _ _ _ _ Hrest)
              as [_ Heq]
        end.
        subst e1'.
        destruct (step_done_ok_inv CT _ _ _ _ _ _ _ _ Hstep1) as [Hs HK].
        apply Hnf. split; assumption.
    - destruct Hfail as (r' & rG & V' & -> & Hr). simpl.
      apply FP_Failed. exact Hr.
  Qed.

  Lemma flow_read_is_cache_read :
    forall G rho t yv V K,
      sem G rho ->
      nth_error G yv = Some OThis ->
      cache_read_control hash_cache_protocol (pico_hash_cache_adapter receiver)
        (CoreRun rho (SVarAss t (EField yv hash_cache_field)) V K).
  Proof.
    intros G rho t yv V K Hsem Hthis.
    destruct (sem_get _ _ _ _ Hsem Hthis) as (v & Hv & Hrecv).
    simpl in Hrecv. subst v.
    exists rho; exists t; exists yv; exists hash_cache_field; exists V;
      exists K; exists receiver; exists HashField.
    split; [reflexivity |]. split; [exact Hv |].
    apply pico_concrete_hash_adapter_at.
  Qed.

  (** Every step that is not a cache read preserves the phases. *)
  Lemma flow_phase_step :
    forall e S e' S',
      flow_phase e ->
      ~ cache_read_control hash_cache_protocol
          (pico_hash_cache_adapter receiver) e ->
      hash_inv S ->
      pico_core_step CT e S e' S' ->
      flow_phase e'.
  Proof.
    intros e S e' S' Hphase Hnoread Hinv Hstep.
    destruct Hphase as
      [ V
      | sG G rho s V sG1 G1 G1' Kb Hfl Hle Hcont Hsem Hwf Hin
      | sG G rho d V0 sG1 G1 G1' Kb n r s V K1 Hderiv Htyped Hsem1 Hle Hcont
          Hsem Hwf Hin Hsteps Hnf
      | V | V | r rho V Hr ].
    - (* the call *)
      inversion Hstep; subst.
      + match goal with
        | Hyl : runtime_getVal caller y = Some (Iot ?l),
          Hb : r_basetype _ ?l = Some ?C,
          Hf : FindMethodWithName CT ?C mc ?md,
          Ha : runtime_lookup_list caller [] = Some ?vs |- _ =>
            rewrite Hy in Hyl; injection Hyl as <-;
            have Hcls := hash_inv_receiver_class CT receiver m h0 H rt0 fs0
              Hobj0 _ Hinv;
            simpl in Hcls; rewrite Hcls in Hb; injection Hb as <-;
            have Hmd := find_method_with_name_deterministic CT _ _ _ _ Hf Hfind;
            subst md; simpl in Ha; injection Ha as <-
        end.
        change (CoreRun (mkr_env [Iot receiver]) (mbody_stmt (mbody mdef)) V
                  [KCall caller x (mreturn (mbody mdef))])
          with (CoreRun rho1 body V ([] ++ Kc)).
        eapply FP_Body.
        * exact Hflow.
        * apply Forall2_refl_le.
        * apply CF_Nil. exact Hreturn.
        * unfold sem. simpl. constructor; [reflexivity | constructor].
        * exact Hwf1.
        * exact rho1_in_footprint.
      + congruence.
    - (* the body *)
      inversion Hfl; subst.
      + (* skip *)
        destruct Kb as [| fr Kb'].
        * inversion Hcont; subst.
          have Hret := Forall2_le_derived _ _ _ Hle H0.
          destruct (sem_get _ _ _ _ Hsem Hret) as (v & Hv & Hd).
          simpl in Hd. subst v.
          simpl in Hstep. inversion Hstep; subst.
          match goal with
          | Hr : runtime_getVal rho ret = Some ?rv |- _ =>
              rewrite Hv in Hr; injection Hr as <-
          end.
          apply FP_Resume.
        * inversion Hcont; subst.
          simpl in Hstep. inversion Hstep; subst.
          eapply FP_Body; eauto.
          eapply sem_le; eassumption.
      + (* sequence *)
        inversion Hstep; subst.
        change (CoreRun rho s1 V (KSeq s2 :: Kb ++ Kc))
          with (CoreRun rho s1 V ((KSeq s2 :: Kb) ++ Kc)).
        eapply FP_Body; eauto.
        eapply CF_Seq; eauto.
      + (* default test *)
        inversion Hstep; subst;
          match goal with
          | Hf : flow sG ?Gr ?sb sG1 ?Ga,
            Hl : Forall2 origin_le ?Ga G1
            |- flow_phase (CoreRun rho ?sb V _) =>
              apply (FP_Body sG Gr rho sb V sG1 Ga G1' Kb Hf
                       (Forall2_trans_le _ _ _ Hl Hle) Hcont);
                [| exact Hwf | exact Hin]
          end.
        * eapply sem_refine_zero; eauto.
        * eapply sem_refine_nonzero; eauto.
        * eapply sem_refine_zero; eauto.
        * eapply sem_refine_nonzero; eauto.
      + (* the read is a cache read *)
        exfalso. apply Hnoread.
        eapply flow_read_is_cache_read; eassumption.
      + (* the write *)
        inversion Hstep; subst.
        * eapply FP_Body; eauto. apply F_Skip.
        * apply FP_Failed. discriminate.
        * apply FP_Failed. discriminate.
      + (* derivation code *)
        change (CoreRun rho s V (Kb ++ Kc))
          with (CoreRun rho s V ([] ++ Kb ++ Kc)) in Hstep.
        eapply deriv_phase_step; eauto.
        * apply FootprintStepsRefl.
        * intros [Hs _]. contradiction.
    - eapply deriv_phase_step; eauto.
    - inversion Hstep; subst. apply FP_Done.
    - exfalso. eapply core_done_no_step. exact Hstep.
    - exfalso. eapply core_done_no_step. exact Hstep.
  Qed.

  (** Every control reached by a run of the call is in one of the phases. *)
  Lemma flow_run_phase :
    forall V0 tr e,
      hash_run (CoreRun caller (SCall x mc y []) V0 []) tr e ->
      ValidTrace hash_cache_protocol H tr ->
      flow_phase e.
  Proof.
    intros V0 tr e Hrun.
    induction Hrun as
      [| tr rGamma x' y' f V V' K old loc k v cv sigma Hrun IH Hxo Hyo Hread
           Hfield Hvalue
       | tr e S e' S' Hrun IH Hnoread Hinv Hstep];
      intros Hvalid.
    - apply FP_Call.
    - apply Forall_app in Hvalid. destruct Hvalid as [Hvalid Hobs].
      have Hphase := IH Hvalid.
      destruct (pico_hash_cache_adapter_some _ _ _ Hfield) as [Haddr ->].
      injection Haddr as -> ->.
      simpl in Hvalue. injection Hvalue as <-.
      inversion Hobs as [| ? ? Hcv _]; subst.
      unfold ValidObs in Hcv. simpl in Hcv. unfold hash_cache_valid in Hcv.
      inversion Hphase as
        [ V1
        | sG G rho s V1 sG1 G1 G1' Kb Hfl Hle Hcont Hsem Hwf Hin
        | sG G rho d V1 sG1 G1 G1' Kb n r s V2 K1 Hderiv Htyped Hsem1 Hle
            Hcont Hsem Hwf Hin Hsteps Hnf
        | V1 | V1 | r rho V1 Hr ]; subst.
      + (* the body *)
        inversion Hfl; subst.
        * (* the read *)
          eapply FP_Body.
          -- apply F_Skip.
          -- exact Hle.
          -- exact Hcont.
          -- apply sem_update; [exact Hsem | exact Hcv].
          -- destruct Hcv as [-> | [-> _]].
             ++ eapply preservation_pico; [exact Hwf | match goal with Ht : forall n, stmt_typing _ _ _ _ _ |- _ => apply Ht end |].
                eapply SBS_Assign; [exact Hxo | apply EBS_Int].
             ++ eapply preservation_pico; [exact Hwf | match goal with Ht : forall n, stmt_typing _ _ _ _ _ |- _ => apply Ht end |].
                eapply SBS_Assign; [exact Hxo | apply EBS_Int].
          -- destruct Hcv as [-> | [-> _]]; apply env_in_update_int; exact Hin.
        * (* derivation code does not read the cache field *)
          exfalso.
          eapply cache_field_not_abstract_read; [| reflexivity | exact Hyo].
          eapply deriv_phase_running with (n := 0) (K1 := []); eauto.
          -- apply FootprintStepsRefl.
          -- intros [Hs _]. discriminate.
      + exfalso.
        eapply cache_field_not_abstract_read; [| reflexivity | exact Hyo].
        eapply deriv_phase_running; eauto.
    - exact (flow_phase_step e S e' S' (IH Hvalid) Hnoread Hinv Hstep).
  Unshelve. all: assumption. Qed.

  (** ** Soundness *)

  (** The caller has a slot for the result. *)
  Hypothesis Hx : x < dom (vars caller).

  Theorem flow_cache_method_trace_robust :
    forall V0,
      machine_cache_safe CT hash_cache_protocol pico_hash_stable_abs H
        (pico_hash_cache_adapter receiver) hash_machine
        (cache_call_result_ok H x)
        (CoreRun caller (SCall x mc y []) V0 []).
  Proof.
    intros V0 tr e Hrun Hvalid.
    have Hphase := flow_run_phase V0 tr e Hrun Hvalid.
    split.
    - intros rGamma x' f y' V K loc v -> Hx' Hy'.
      inversion Hphase as
        [ V1
        | sG G rho s V1 sG1 G1 G1' Kb Hfl Hle Hcont Hsem Hwf Hin
        | sG G rho d V1 sG1 G1 G1' Kb n r s V2 K1 Hderiv Htyped Hsem1 Hle
            Hcont Hsem Hwf Hin Hsteps Hnf
        | V1 | V1 | r rho V1 Hr ]; subst.
      + inversion Hfl; subst.
        * match goal with
          | Hthis : nth_error _ _ = Some OThis,
            Hval : nth_error _ _ = Some ODerived |- _ =>
              destruct (sem_get _ _ _ _ Hsem Hthis) as (vr & Hvr & Hrecv);
              destruct (sem_get _ _ _ _ Hsem Hval) as (vd & Hvd & Hder)
          end.
          simpl in Hrecv, Hder. subst vr vd.
          rewrite Hvr in Hx'. injection Hx' as <-.
          rewrite Hvd in Hy'. injection Hy' as <-.
          right. exists HashField, (Int H).
          split; [apply pico_concrete_hash_adapter_at |].
          split; [reflexivity |].
          simpl. unfold hash_cache_valid.
          destruct (Nat.eq_dec H 0) as [Hz | Hnz].
          -- left. rewrite Hz. reflexivity.
          -- right. split; [reflexivity | exact Hnz].
        * match goal with
          | Hd : deriv_stmt _ _ _ (SFldWrite _ _ _) _ |- _ => inversion Hd
          end.
      + exfalso.
        have Hrunning := deriv_phase_running _ _ _ _ _ _ _ _ _ _ Hderiv Htyped
          Hwf Hin Hsteps Hnf.
        destruct Hrunning as (rG & s' & V' & K' & Heq & _ & Hnowrite & _).
        injection Heq as <- <- <- <-.
        eapply Hnowrite. reflexivity.
    - intros r rGamma V ->.
      inversion Hphase; subst.
      + intros _. simpl. unfold caller_done, runtime_getVal, set_vars.
        cbn [vars]. apply update_same. exact Hx.
      + intros Hok. simpl in Hok. contradiction.
  Qed.

  (** The local-copy method whose initializer calls the derivation method
      is accepted. *)
  Lemma local_copy_derivation_call_flow :
    let sG3 := [Trecv; int_type; int_type] in
    let compute := SCall cache_tmp m cache_receiver [] in
    derived_by CT m h0 receiver (Int H) ->
    stmt_typing CT [Trecv] mt (SLocal int_type cache_tmp)
      [Trecv; int_type] ->
    stmt_typing CT [Trecv; int_type] mt (SLocal int_type cache_result) sG3 ->
    (forall n, stmt_typing CT sG3 mt (SVarAss cache_tmp (EInt n)) sG3) ->
    stmt_typing CT sG3 mt (SVarAss cache_result (EVar cache_tmp)) sG3 ->
    deriv_stmt CT D sG3 compute sG3 ->
    stmt_typing CT sG3 mt compute sG3 ->
    flow [Trecv] [OThis] (pico_hash_method_stmt_with compute) sG3
      [OThis; ODerived; ODerived].
  Proof.
    intros sG3 compute Hderived Hl1 Hl2 Hint Hcopy Hderiv Htyped.
    apply local_copy_flow; try assumption.
    - discriminate.
    - intros rho rhob Hs Heval.
      have Hd := derivation_call_sem [OThis; OSentinel; OSentinel] cache_tmp
        cache_receiver rho rhob Hderived eq_refl Hs Heval.
      eapply sem_le; [| exact Hd].
      constructor; [apply origin_le_refl |].
        constructor; [apply origin_le_refl |].
        constructor; [right; left; reflexivity | constructor].
  Qed.
End flow_judgment.
