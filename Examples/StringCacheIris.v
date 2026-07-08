From Stdlib Require Import ZArith.

From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import spawn.
From iris.base_logic.lib Require Import invariants.

Open Scope Z_scope.

(** * Iris heap_lang String-Cache Example

    This file is an ordinary Iris/heap_lang wrapper for the cache idea.  It is
    intentionally sequentially consistent: heap_lang gives interleaving
    concurrency with atomic heap operations, not Java weak-memory races. *)

(** Deterministic hash used by the example object. *)
Definition deterministic_hash (v c : Z) : Z :=
  v + 31 * c.

(** Cache invariant for a String-like hash and hash-is-zero cache pair. *)
Definition CacheOK (H h : Z) (hashIsZero : bool) : Prop :=
  (h = 0 \/ h = H) /\
  (H = 0 \/ hashIsZero = false).

(** Heap-lang allocation of the String-like object representation. *)
Definition mk_string_obj : val :=
  λ: "value" "coder",
    let: "hash" := ref #0 in
    let: "hashIsZero" := ref #false in
    ("value", "coder", "hash", "hashIsZero").

Definition hashCode_store_nonzero : val :=
  λ: "o",
    let: "value" := Fst (Fst (Fst "o")) in
    let: "coder" := Snd (Fst (Fst "o")) in
    let: "hash" := Snd (Fst "o") in
    let: "computed" := "value" + (#31 * "coder") in
    "hash" <- "computed";;
    "computed".

Definition hashCode_local_copy_nonzero : val :=
  λ: "o",
    let: "value" := Fst (Fst (Fst "o")) in
    let: "coder" := Snd (Fst (Fst "o")) in
    let: "hash" := Snd (Fst "o") in
    let: "h" := !"hash" in
    if: "h" = #0 then
      let: "computed" := "value" + (#31 * "coder") in
      "hash" <- "computed";;
      "computed"
    else
      "h".

Definition hashCode_local_copy_zero : val :=
  λ: "o",
    let: "value" := Fst (Fst (Fst "o")) in
    let: "coder" := Snd (Fst (Fst "o")) in
    let: "hash" := Snd (Fst "o") in
    let: "hashIsZero" := Snd "o" in
    let: "h" := !"hash" in
    if: "h" = #0 then
      let: "computed" := "value" + (#31 * "coder") in
      if: "computed" = #0 then
        "hashIsZero" <- #true;;
        "computed"
      else
        "hash" <- "computed";;
        "computed"
    else
      "h".

Definition hashCode_local_copy : val := hashCode_local_copy_zero.

(** Two concurrent calls to the local-copy cache method. *)
Definition hashCode_fork2 : val :=
  λ: "o",
    Fork (hashCode_local_copy "o");;
    Fork (hashCode_local_copy "o");;
    #().

Definition hashCode_spawn2_join : val :=
  λ: "o",
    let: "h1" := spawn.spawn (λ: <>, hashCode_local_copy "o") in
    let: "h2" := spawn.spawn (λ: <>, hashCode_local_copy "o") in
    let: "r1" := spawn.join "h1" in
    let: "r2" := spawn.join "h2" in
    ("r1", "r2").

Section proofs.
  Context `{!heapGS Σ}.

  Definition ImmString (N : namespace) (o : val) (v c : Z) : iProp Σ :=
    ∃ (hash hashIsZero : loc),
      ⌜o = (#v, #c, #hash, #hashIsZero)%V⌝ ∗
      inv N (∃ (h : Z) (z : bool),
        hash ↦ #h ∗
        hashIsZero ↦ #z ∗
        ⌜CacheOK (deterministic_hash v c) h z⌝).

  Global Instance ImmString_persistent N o v c :
    Persistent (ImmString N o v c).
  Proof. apply _. Qed.

  Lemma mk_string_obj_spec N v c :
    {{{ True }}}
      mk_string_obj #v #c
    {{{ o, RET o; ImmString N o v c }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /mk_string_obj.
    wp_pures.
    wp_alloc hash as "Hhash".
    wp_pures.
    wp_alloc hashIsZero as "HhashIsZero".
    wp_pures.
    iMod (inv_alloc N _ (∃ (h : Z) (z : bool),
            hash ↦ #h ∗
            hashIsZero ↦ #z ∗
            ⌜CacheOK (deterministic_hash v c) h z⌝)%I
          with "[Hhash HhashIsZero]") as "#Hinv".
    {
      iNext.
      iExists 0, false.
      iFrame.
      iPureIntro.
      split; [left | right]; reflexivity.
    }
    iModIntro.
    iApply "HΦ".
    iExists hash, hashIsZero.
    iSplit; [done | iExact "Hinv"].
  Qed.

  Lemma hashCode_store_nonzero_spec N o v c :
    deterministic_hash v c ≠ 0 ->
    {{{ ImmString N o v c }}}
      hashCode_store_nonzero o
    {{{ RET #(deterministic_hash v c); ImmString N o v c }}}.
  Proof.
    iIntros (Hnz Φ) "Himm HΦ".
    iDestruct "Himm" as (hash hashIsZero ->) "#Hinv".
    rewrite /hashCode_store_nonzero /deterministic_hash.
    wp_pures.
    wp_bind (#hash <- #(v + 31 * c))%E.
    iInv N as (h z) "(>Hhash & >HhashIsZero & >%Hok)" "Hclose".
    wp_store.
    iMod ("Hclose" with "[Hhash HhashIsZero]") as "_".
    {
      iNext.
      iExists (v + 31 * c), z.
      iFrame.
      iPureIntro.
      destruct Hok as [_ Hz].
      split.
      - right. reflexivity.
      - destruct Hz as [Hzero | Hzfalse]; [contradiction | right; exact Hzfalse].
    }
    iModIntro.
    wp_pures.
    iApply "HΦ".
    iModIntro.
    iExists hash, hashIsZero.
    iSplit; [done | iExact "Hinv"].
  Qed.

  Lemma hashCode_local_copy_nonzero_spec N o v c :
    deterministic_hash v c ≠ 0 ->
    {{{ ImmString N o v c }}}
      hashCode_local_copy_nonzero o
    {{{ RET #(deterministic_hash v c); ImmString N o v c }}}.
  Proof.
    iIntros (Hnz Φ) "Himm HΦ".
    unfold deterministic_hash in Hnz.
    iDestruct "Himm" as (hash hashIsZero ->) "#Hinv".
    rewrite /hashCode_local_copy_nonzero /deterministic_hash.
    wp_pures.
    wp_bind (! #hash)%E.
    iInv N as (h z) "(>Hhash & >HhashIsZero & >%Hok)" "Hclose".
    wp_load.
    iMod ("Hclose" with "[Hhash HhashIsZero]") as "_".
    {
      iNext.
      iExists h, z.
      iFrame.
      done.
    }
    iModIntro.
    destruct Hok as [[Hh_zero | Hh_hash] Hz].
    - subst h.
      wp_pures.
      wp_bind (#hash <- #(v + 31 * c))%E.
      iInv N as (h2 z2) "(>Hhash & >HhashIsZero & >%Hok)" "Hclose".
      wp_store.
      iMod ("Hclose" with "[Hhash HhashIsZero]") as "_".
      {
        iNext.
        iExists (v + 31 * c), z2.
        iFrame.
        iPureIntro.
        destruct Hok as [_ Hz2].
        split.
        + right. reflexivity.
        + destruct Hz2 as [Hzero | Hzfalse];
            [contradiction | right; exact Hzfalse].
      }
      iModIntro.
      wp_pures.
      iApply "HΦ".
      iModIntro.
      iExists hash, hashIsZero.
      iSplit; [done | iExact "Hinv"].
    - subst h.
      wp_pures.
      rewrite bool_decide_false.
      2: { intros Heq. inversion Heq. apply Hnz. exact H0. }
      wp_pures.
      iApply "HΦ".
      iModIntro.
      iExists hash, hashIsZero.
      iSplit; [done | iExact "Hinv"].
  Qed.

  Lemma hashCode_local_copy_zero_spec N o v c :
    deterministic_hash v c = 0 ->
    {{{ ImmString N o v c }}}
      hashCode_local_copy_zero o
    {{{ RET #0; ImmString N o v c }}}.
  Proof.
    iIntros (Hzero Φ) "Himm HΦ".
    unfold deterministic_hash in Hzero.
    iDestruct "Himm" as (hash hashIsZero ->) "#Hinv".
    rewrite /hashCode_local_copy_zero /deterministic_hash.
    wp_pures.
    wp_bind (! #hash)%E.
    iInv N as (h z) "(>Hhash & >HhashIsZero & >%Hok)" "Hclose".
    wp_load.
    iMod ("Hclose" with "[Hhash HhashIsZero]") as "_".
    {
      iNext.
      iExists h, z.
      iFrame.
      done.
    }
    iModIntro.
    destruct Hok as [[Hh_zero | Hh_hash] _].
    - subst h.
      wp_pures.
      rewrite bool_decide_true; last (rewrite Hzero; reflexivity).
      wp_pures.
      wp_bind (#hashIsZero <- #true)%E.
      iInv N as (h2 z2) "(>Hhash & >HhashIsZero & >%Hok)" "Hclose".
      wp_store.
      iMod ("Hclose" with "[Hhash HhashIsZero]") as "_".
      {
        iNext.
        iExists h2, true.
        iFrame.
        iPureIntro.
        destruct Hok as [Hh_ok _].
        split; [exact Hh_ok | left; exact Hzero].
      }
      iModIntro.
      wp_pures.
      replace (#(v + 31 * c))%V with (#0)%V
        by (rewrite Hzero; reflexivity).
      iApply "HΦ".
      iModIntro.
      iExists hash, hashIsZero.
      iSplit; [done | rewrite /deterministic_hash Hzero; iExact "Hinv"].
    - rewrite Hzero in Hh_hash.
      subst h.
      wp_pures.
      rewrite bool_decide_true; last (rewrite Hzero; reflexivity).
      wp_pures.
      wp_bind (#hashIsZero <- #true)%E.
      iInv N as (h2 z2) "(>Hhash & >HhashIsZero & >%Hok)" "Hclose".
      wp_store.
      iMod ("Hclose" with "[Hhash HhashIsZero]") as "_".
      {
        iNext.
        iExists h2, true.
        iFrame.
        iPureIntro.
        destruct Hok as [Hh_ok _].
        split; [exact Hh_ok | left; exact Hzero].
      }
      iModIntro.
      wp_pures.
      replace (#(v + 31 * c))%V with (#0)%V
        by (rewrite Hzero; reflexivity).
      iApply "HΦ".
      iModIntro.
      iExists hash, hashIsZero.
      iSplit; [done | rewrite /deterministic_hash Hzero; iExact "Hinv"].
  Qed.

  Lemma hashCode_local_copy_nonzero_full_spec N o v c :
    deterministic_hash v c ≠ 0 ->
    {{{ ImmString N o v c }}}
      hashCode_local_copy o
    {{{ RET #(deterministic_hash v c); ImmString N o v c }}}.
  Proof.
    iIntros (Hnz Φ) "Himm HΦ".
    unfold deterministic_hash in Hnz.
    iDestruct "Himm" as (hash hashIsZero ->) "#Hinv".
    rewrite /hashCode_local_copy /hashCode_local_copy_zero /deterministic_hash.
    wp_pures.
    wp_bind (! #hash)%E.
    iInv N as (h z) "(>Hhash & >HhashIsZero & >%Hok)" "Hclose".
    wp_load.
    iMod ("Hclose" with "[Hhash HhashIsZero]") as "_".
    {
      iNext.
      iExists h, z.
      iFrame.
      done.
    }
    iModIntro.
    destruct Hok as [[Hh_zero | Hh_hash] Hz].
    - subst h.
      wp_pures.
      rewrite bool_decide_false.
      2: { intros Heq. inversion Heq. apply Hnz. exact H0. }
      wp_pures.
      wp_bind (#hash <- #(v + 31 * c))%E.
      iInv N as (h2 z2) "(>Hhash & >HhashIsZero & >%Hok)" "Hclose".
      wp_store.
      iMod ("Hclose" with "[Hhash HhashIsZero]") as "_".
      {
        iNext.
        iExists (v + 31 * c), z2.
        iFrame.
        iPureIntro.
        destruct Hok as [_ Hz2].
        split.
        + right. reflexivity.
        + destruct Hz2 as [Hzero | Hzfalse];
            [contradiction | right; exact Hzfalse].
      }
      iModIntro.
      wp_pures.
      iApply "HΦ".
      iModIntro.
      iExists hash, hashIsZero.
      iSplit; [done | iExact "Hinv"].
    - subst h.
      wp_pures.
      rewrite bool_decide_false.
      2: { intros Heq. inversion Heq. apply Hnz. exact H0. }
      wp_pures.
      iApply "HΦ".
      iModIntro.
      iExists hash, hashIsZero.
      iSplit; [done | iExact "Hinv"].
  Qed.

  Lemma hashCode_local_copy_spec N o v c :
    {{{ ImmString N o v c }}}
      hashCode_local_copy o
    {{{ RET #(deterministic_hash v c); ImmString N o v c }}}.
  Proof.
    destruct (Z.eq_dec (deterministic_hash v c) 0) as [Hzero | Hnz].
    - rewrite /hashCode_local_copy.
      replace (#(deterministic_hash v c))%V with #0%V
        by (rewrite Hzero; reflexivity).
      apply hashCode_local_copy_zero_spec.
      exact Hzero.
    - apply hashCode_local_copy_nonzero_full_spec.
      exact Hnz.
  Qed.

  Lemma hashCode_fork2_spec N o v c :
    {{{ ImmString N o v c }}}
      hashCode_fork2 o
    {{{ RET #(); ImmString N o v c }}}.
  Proof.
    iIntros (Φ) "#Himm HΦ".
    rewrite /hashCode_fork2.
    wp_pures.
    wp_apply wp_fork.
    - wp_apply (hashCode_local_copy_spec with "Himm").
      iIntros "_".
      done.
    - wp_seq.
      wp_apply wp_fork.
      + wp_apply (hashCode_local_copy_spec with "Himm").
        iIntros "_".
        done.
      + wp_seq.
        iApply "HΦ".
        iExact "Himm".
  Qed.

  Lemma hashCode_spawn2_join_spec `{!spawnG Σ} N (Nspawn : namespace) o v c :
    {{{ ImmString N o v c }}}
      hashCode_spawn2_join o
    {{{ RET (#(deterministic_hash v c), #(deterministic_hash v c))%V;
        ImmString N o v c }}}.
  Proof.
    iIntros (Φ) "#Himm HΦ".
    rewrite /hashCode_spawn2_join.
    wp_pures.
    wp_apply (spawn_spec Nspawn
      (fun r => ⌜r = #(deterministic_hash v c)⌝%I) with "[Himm]").
    - wp_pures.
      wp_apply (hashCode_local_copy_spec with "Himm").
      iIntros "_".
      done.
    - iIntros (h1) "Hh1".
      wp_pures.
      wp_apply (spawn_spec Nspawn
        (fun r => ⌜r = #(deterministic_hash v c)⌝%I) with "[Himm]").
      + wp_pures.
        wp_apply (hashCode_local_copy_spec with "Himm").
        iIntros "_".
        done.
      + iIntros (h2) "Hh2".
        wp_pures.
        wp_apply (join_spec with "Hh1").
        iIntros (r1) "%Hr1".
        subst r1.
        wp_pures.
        wp_apply (join_spec with "Hh2").
        iIntros (r2) "%Hr2".
        subst r2.
        wp_pures.
        iApply "HΦ".
        iExact "Himm".
  Qed.
End proofs.
