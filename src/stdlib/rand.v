From iris.proofmode Require Import base proofmode.

From mizzle.lang Require Export semantics.

From mizzle.logic Require Import interp goal goal_proof goal_tactics.

Definition nondet_bool : val :=
  vfun: <> =>
    let: "l" := ref true in
    Fork ("l" <- false) ;;
    !"l".

Section rand.
Context `{seqlogGS Σ}.

(** Choose the outcome [b] of a [nondet_bool ()] coin flip. [[card]] *)
Lemma goal_rand E p ks (b:bool) :
  focused p ks (nondet_bool (Val ValUnit)) -∗
  (focused p ks (Val (ValBool b)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hp Hcont".
  rewrite /nondet_bool.
  g_call "Hp".
  g_alloc "Hp" "Hl". g_let "Hp".
  g_fork "Hp" "Ht" "Hloc". g_let "Hp".
  destruct b.
  { g_get_field "Hp" "Hl".
    iApply ("Hcont" with "Hp"). }
  { g_set_field "Ht" "Hl".
    g_get_field "Hp" "Hl".
    iApply ("Hcont" with "Hp"). }
Qed.

End rand.
