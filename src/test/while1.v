From mizzle.test Require Import test_prelude.

From mizzle.stdlib Require Import assert.

(* Count a reference up to 3 with a [while:] loop, then assert (wrongly)
   that it holds 2. *)
Definition count_to_three : expr :=
  let: "r" := ref 0 in
  while: !"r" < 3 begin
    "r" <- !"r" + 1
  end ;;
  assert: !"r" == 2.

Section bugs.
Context `{seqlogGS Σ}.

(** Unfolding the loop by hand, one [g_while] per iteration. *)
Lemma count_to_three_buggy p ks :
  remaining is_stuck' -∗
  focused p ks count_to_three -∗
  goal ⊤.
Proof.
  iIntros "Hrem Hp". rewrite /count_to_three.
  g_alloc "Hp" "Hr". g_let "Hp".
  g_while "Hp".
  g_get_field "Hp" "Hr". g_binop "Hp". g_if_true "Hp".
  g_get_field "Hp" "Hr". g_binop "Hp". g_set_field "Hp" "Hr". g_seq "Hp".
  iSimpl in "Hr".
  do 2 (g_while "Hp";
        g_get_field "Hp" "Hr"; g_binop "Hp"; g_if_true "Hp";
        g_get_field "Hp" "Hr"; g_binop "Hp"; g_set_field "Hp" "Hr"; g_seq "Hp";
        iSimpl in "Hr").
  g_while "Hp".
  g_get_field "Hp" "Hr". g_binop "Hp". g_if_false "Hp".
  g_seq "Hp".
  g_get_field "Hp" "Hr". g_equal "Hp".
  g_assert_stuck "Hp".
Qed.

End bugs.
