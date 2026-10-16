From mizzle.test Require Import test_prelude.

From mizzle.stdlib Require Import assert.

Definition lazy_init : expr :=
  let: "c" := ref 0 in
  let: "n" := ref 0 in
  Fork (if: !"c" == 0 then "n" <- !"n" + 1 ;; "c" <- 1 else ()) ;;
  (if: !"c" == 0 then "n" <- !"n" + 1 ;; "c" <- 1 else ()) ;;
  assert: !"n" == 1.

Section bugs.
Context `{seqlogGS Σ}.

Lemma lazy_init_buggy p ks :
  remaining is_stuck' -∗
  focused p ks lazy_init -∗
  goal ⊤.
Proof.
  iIntros "Hrem Hp". rewrite /lazy_init.
  (* Setup: alloc c, n. *)
  g_alloc "Hp" "Hc". g_let "Hp".
  g_alloc "Hp" "Hn". g_let "Hp".
  (* Fork. Hp = main, Hf = forked. *)
  g_fork "Hp" "Hf" "Hfloc". g_let "Hp".
  (* Drive forked: c=0, then-branch, n := !n+1 = 1.
     Stop before [c <- 1] so c stays 0 for main. *)
  g_get_field "Hf" "Hc". g_equal "Hf". g_if_true "Hf".
  g_get_field "Hf" "Hn". g_binop "Hf". g_set_field "Hf" "Hn".
  g_let "Hf".
  (* Hf parked at [#c_loc <- 1]. Switch to main. *)
  g_get_field "Hp" "Hc". g_equal "Hp". g_if_true "Hp".
  g_get_field "Hp" "Hn". g_binop "Hp". g_set_field "Hp" "Hn".
  g_let "Hp".
  g_set_field "Hp" "Hc".
  g_let "Hp".
  g_get_field "Hp" "Hn". g_equal "Hp". g_assert_stuck "Hp".
Qed.

End bugs.
