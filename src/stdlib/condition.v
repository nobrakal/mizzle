From iris.proofmode Require Import base proofmode.

From mizzle.lang Require Export semantics.

From mizzle.logic Require Import interp goal goal_proof goal_tactics.
From mizzle.lang Require Import options.

(** Condition variables, copied from Zoo's [zoo_std/condition__code.v] and
    restricted to the operations Mizzle uses, plus their callees. In Zoo these
    are no-ops on a unit value; see the specs below. *)

Definition condition٠create : val :=
  vfun: <> =>
    ().

Definition condition٠notify : val :=
  vfun: "_t" =>
    ().

Definition condition٠notify_all : val :=
  vfun: "_t" =>
    ().

Definition condition٠wait : val :=
  vfun: "_t" "_mtx" =>
    ().

Definition condition٠wait_until : val :=
  vrec: "wait_until" "t" "mtx" "pred" =>
    if: ~ "pred" () then (
      condition٠wait "t" "mtx" ;;
      "wait_until" "t" "mtx" "pred"
    ).

Definition condition٠wait_while : val :=
  vfun: "t" "mtx" "pred" =>
    condition٠wait_until "t" "mtx" (fun: <> => ~ "pred" ()).

(** Goal-mode specs for the condition variables above. As in Zoo their
    runtime content is trivial: a condition is [()] and notification is a
    no-op (waiting is busy-waiting). *)

Section condition.
Context `{seqlogGS Σ}.

(** [condition٠create ()] returns [()]. *)
Lemma focused_condition_create E p ks :
  focused p ks (App (Val condition٠create) (Val ValUnit)) -∗
  (focused p ks (Val ValUnit) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hf Hcont". rewrite /condition٠create. g_call "Hf".
  iApply ("Hcont" with "Hf").
Qed.

(** [condition٠notify_all c] is a no-op. *)
Lemma focused_condition_notify_all E p ks (c:val) :
  focused p ks (App (Val condition٠notify_all) (Val c)) -∗
  (focused p ks (Val ValUnit) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hf Hcont". rewrite /condition٠notify_all. g_call "Hf".
  iApply ("Hcont" with "Hf").
Qed.

End condition.

(** Sealed for clients, now that the proofs above are done. *)
#[global] Opaque condition٠create condition٠notify condition٠notify_all condition٠wait condition٠wait_until condition٠wait_while.
