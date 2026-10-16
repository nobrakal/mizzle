From iris.proofmode Require Import base proofmode.
From stdpp Require Import hlist.

From mizzle.lang Require Import instances.
From mizzle.lang Require Export semantics.

From mizzle.logic Require Import interp goal goal_proof goal_tactics.

(** [diverge] and [assume], copied from Zoo's [zoo_std/diverge.v] and
    [zoo_std/assume.v]. Only the program text is reproduced: Zoo's WP specs
    are replaced by the goal-mode spec in the specs below. Both are sealed
    [Opaque] at the end of this file, as in Zoo. *)

Definition diverge : val :=
  vrec: "diverge" <> =>
    "diverge" ().

Definition assume : val :=
  vfun: "b" =>
    if: ~ "b" then
      diverge ().

(** Goal-mode spec for [assume] (program text above):
      [assume ≜ vfun: "b" => if: ~"b" then diverge ()].
    Running it on [true] takes the (implicit) else-branch and reduces to [()];
    on [false] it diverges, so there is nothing to say. We therefore only
    spec the [true] case. [assume] is sealed [Opaque] at the end of the file,
    as in Zoo. *)

Section assume.
Context `{seqlogGS Σ}.

Lemma goal_assume E p ks :
  focused p ks (assume (Val (ValBool true))) -∗
  (focused p ks () -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hp Hcont". rewrite /assume.
  g_call "Hp". g_unop "Hp". g_if_false "Hp".
  all: iApply ("Hcont" with "Hp").
Qed.

Lemma goal_assume_at E K p ks :
  focused p ks (fill K (assume (Val (ValBool true)))) -∗
  (focused p ks (fill K ()) -∗ goal E) -∗
  goal E.
Proof. rewrite -!fill_app. iApply goal_assume. Qed.

End assume.

Tactic Notation "g_assume" constr(Hp) :=
  iStartProof;
  g_locate Hp
    ltac:(fun e' => lazymatch e' with App (Val assume) _ => idtac end)
    ltac:(fun e => fail 1 "g_assume: no [assume #true] redex in" e);
  let spec := mk_spec_1 Hp in
  with_focused_ks_e Hp ltac:(fun ks _ => iApply (ITrm (goal_assume _ _ ks) hnil spec));
  iIntros Hp;
  iEval (simpl) in Hp.

(** Sealed for clients, now that the proofs above are done. *)
#[global] Opaque diverge assume.
