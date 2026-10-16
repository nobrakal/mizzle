From iris.proofmode Require Import base proofmode.

From mizzle.lang Require Export semantics.

From mizzle.logic Require Import interp goal goal_proof goal_tactics.
From mizzle.stdlib Require Import atomic_loc.
From mizzle.lang Require Import options.

(** Mutexes, after Zoo's [zoo_std/mutex__code.v], restricted to the
    operations Mizzle uses, plus their callees. A mutex is a single boolean
    cell, [false] when unlocked and [true] when locked. [lock]'s CAS goes
    through the split-argument wrapper [atomic_loc٠cas] rather than Zoo's
    descriptor form, as generated code does. The goal-mode specs follow. *)

Definition mutex٠create : val :=
  vfun: <> =>
    ref false.

Definition mutex٠lock : val :=
  vrec: "lock" "t" =>
    if: ~ atomic_loc٠cas "t" ⟨contents⟩ false true then (
      "lock" "t"
    ).

(* [Atomic.set t false] in the OCaml source, hence the atomic write: marking
   it non-atomic would report a data race against [lock]'s [CAS]. *)
Definition mutex٠unlock : val :=
  vfun: "t" =>
    "t" <-ᵃᵗ false.

Definition mutex٠synchronize : val :=
  vfun: "t" =>
    mutex٠lock "t" ;;
    mutex٠unlock "t".

Definition mutex٠protect : val :=
  vfun: "t" "fn" =>
    mutex٠lock "t" ;;
    let: "res" := "fn" () in
    mutex٠unlock "t" ;;
    "res".

(** Goal-mode specs. *)

Section mutex.
Context `{seqlogGS Σ}.

Notation focused p ks e := (running p (fill ks e)).

(** [mutex٠create ()] allocates a fresh, unlocked mutex. *)
Lemma focused_mutex_create E p ks :
  focused p ks (App (Val mutex٠create) (Val ValUnit)) -∗
  (∀ lm:location,
     lm ↦∗ [ValBool false] -∗
     focused p ks (Val (ValLoc lm)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hf Hcont". rewrite /mutex٠create. g_call "Hf".
  iApply (goal_ref with "Hf").
  iIntros (lm) "Hl Hf".
  iApply ("Hcont" with "Hl Hf").
Qed.

(** [mutex٠lock #lm] on an unlocked mutex: the CAS succeeds at once. *)
Lemma focused_mutex_lock E p ks (lm:location) :
  lm ↦∗ [ValBool false] -∗
  focused p ks (App (Val mutex٠lock) (Val (ValLoc lm))) -∗
  (lm ↦∗ [ValBool true] -∗ focused p ks (Val ValUnit) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hl Hf Hcont". rewrite /mutex٠lock. g_call "Hf".
  g_cas_succ "Hf" "Hl".
  g_unop "Hf". g_if_false "Hf".
  iApply ("Hcont" with "Hl Hf").
Qed.

(** [mutex٠unlock #lm] stores [false], whatever the previous state. *)
Lemma focused_mutex_unlock E p ks (lm:location) (b:val) :
  lm ↦∗ [b] -∗
  focused p ks (App (Val mutex٠unlock) (Val (ValLoc lm))) -∗
  (lm ↦∗ [ValBool false] -∗ focused p ks (Val ValUnit) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hl Hf Hcont". rewrite /mutex٠unlock. g_call "Hf".
  g_set_field "Hf" "Hl".
  iApply ("Hcont" with "Hl Hf").
Qed.

(** [mutex٠synchronize #lm] = lock; unlock. *)
Lemma focused_mutex_synchronize E p ks (lm:location) :
  lm ↦∗ [ValBool false] -∗
  focused p ks (App (Val mutex٠synchronize) (Val (ValLoc lm))) -∗
  (lm ↦∗ [ValBool false] -∗ focused p ks (Val ValUnit) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hl Hf Hcont". rewrite /mutex٠synchronize. g_call "Hf".
  g_focus (App (Val mutex٠lock) (Val _)) "Hf".
  iApply (focused_mutex_lock with "Hl Hf").
  iIntros "Hl Hf". iEval (simpl) in "Hf". g_let "Hf".
  iApply (focused_mutex_unlock with "Hl Hf").
  iIntros "Hl Hf". iApply ("Hcont" with "Hl Hf").
Qed.

(** [mutex٠protect #lm fn]: lock; run [fn ()]; unlock; return [fn]'s
    result. Stated in resumption style: the continuation receives the
    critical section [fn ()] focused under some context [ks'], plus a
    resume wand to fire once it has reduced to a value [w]; resuming
    performs the unlock and hands back the released mutex together with
    [w] as the result of the whole [protect] call. *)
Lemma focused_mutex_protect E p ks (lm:location) (fn:val) :
  lm ↦∗ [ValBool false] -∗
  focused p ks (App (App (Val mutex٠protect) (Val (ValLoc lm))) (Val fn)) -∗
  (∀ ks',
     focused p ks' (App (Val fn) (Val ValUnit)) -∗
     (∀ w, focused p ks' (Val w) -∗
           (lm ↦∗ [ValBool false] -∗ focused p ks (Val w) -∗ goal E) -∗
           goal E) -∗
     goal E) -∗
  goal E.
Proof.
  iIntros "Hl Hf Hcont". rewrite /mutex٠protect. g_call2 "Hf".
  g_focus (App (Val mutex٠lock) (Val _)) "Hf".
  iApply (focused_mutex_lock with "Hl Hf").
  iIntros "Hl Hf". iEval (simpl) in "Hf". g_let "Hf".
  g_focus (App (Val fn) (Val _)) "Hf".
  iApply ("Hcont" with "Hf [Hl]").
  iIntros (w) "Hf Hcont2". iEval (simpl) in "Hf". g_let "Hf".
  g_focus (App (Val mutex٠unlock) (Val _)) "Hf".
  iApply (focused_mutex_unlock with "Hl Hf").
  iIntros "Hl Hf". iEval (simpl) in "Hf". g_let "Hf".
  iApply ("Hcont2" with "Hl Hf").
Qed.

End mutex.

(** Sealed for clients, now that the proofs above are done. *)
#[global] Opaque mutex٠create mutex٠lock mutex٠unlock mutex٠synchronize mutex٠protect.
