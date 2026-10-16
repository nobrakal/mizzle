From iris.proofmode Require Import base proofmode.

From mizzle.lang Require Import instances.
From mizzle.lang Require Export semantics.
From mizzle.stdlib Require Import structural_equality.

From mizzle.logic Require Import interp goal stuck goal_proof goal_tactics.

Section structeq.
Context `{seqlogGS Σ}.

#[local] Transparent structeq.

(** [structeq] decides equality on integers: a focused [structeq #z1 #z2]
    reduces to the boolean [bool_decide (z1 = z2)]. [[card]] *)
Lemma focused_structeq_int E p ks (z1 z2 : Z) :
  focused p ks (App (App (Val structeq) (Val (ValInt z1))) (Val (ValInt z2))) -∗
  (focused p ks (Val (ValBool (bool_decide (z1 = z2)))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hp Hcont". rewrite /structeq.
  g_call "Hp". g_rec "Hp". g_call "Hp".
  g_unop "Hp". g_if_true "Hp".
  g_unop "Hp". g_if_true "Hp".
  g_equal "Hp".
Qed.

End structeq.
