From mizzle.test Require Import test_prelude.

From mizzle.stdlib Require Import assert.

Definition transfer : expr :=
  let: "a" := ref 100 in
  let: "b" := ref 0 in
  Fork ("a" <- !"a" - 10 ;; "b" <- !"b" + 10) ;;
  "a" <- !"a" - 20 ;;
  "b" <- !"b" + 20 ;;
  assert: (!"a" + !"b") == 100.

Section bugs.
Context `{seqlogGS Σ}.

Lemma transfer_buggy p ks :
  remaining is_stuck' -∗
  focused p ks transfer -∗
  goal ⊤.
Proof.
  iIntros "Hrem Hp". rewrite /transfer.
  g_alloc "Hp" "Ha". g_let "Hp".
  g_alloc "Hp" "Hb". g_let "Hp".
  g_fork "Hp" "Hf" "Hfloc". g_let "Hp".
  (* Main reads a=100; expression now holds [a <- 100 - 20 ;; ...]. *)
  g_get_field "Hp" "Ha".
  (* Run forked to completion: a := 90, b := 10. *)
  g_get_field "Hf" "Ha". g_binop "Hf". g_set_field "Hf" "Ha". g_let "Hf".
  g_get_field "Hf" "Hb". g_binop "Hf". g_set_field "Hf" "Hb".
  (* Main computes 80 and writes a=80, overwriting forked's 90. *)
  g_binop "Hp". g_set_field "Hp" "Ha". g_let "Hp".
  replace (0 + 10)%Z with 10%Z by lia.
  g_get_field "Hp" "Hb". g_binop "Hp". g_set_field "Hp" "Hb". g_let "Hp".
  (* Final state: a=80, b=30, sum=110 ≠ 100; assert: false. *)
  replace (100 - 20)%Z with 80%Z by lia.
  replace (10 + 20)%Z with 30%Z by lia.
  g_get_field "Hp" "Hb". g_get_field "Hp" "Ha".
  g_binop "Hp". g_equal "Hp".
  g_assert_stuck "Hp".
Qed.

End bugs.
