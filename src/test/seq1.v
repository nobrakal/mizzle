From mizzle.test Require Import test_prelude.

From mizzle.stdlib Require Import assert.

Notation "'OSome'" := (in_type "test.seq1.opt" 0)(in custom mizzle_tag).
Notation "'ONone'" := (in_type "test.seq1.opt" 1)(in custom mizzle_tag).

(* [safe_sq] returns ‘OSome(x*x) for non-zero x and §ONone otherwise.
   The caller squares 5, expects 25, but the assertion is off by one. *)
Definition opt_square : expr :=
  let: "safe_sq" := fun: "x" =>
    if: "x" == 0 then §ONone else ‘OSome( "x" * "x" ) in
  match: "safe_sq" 5 with
  | ONone => assert: false
  | OSome "v" => assert: "v" == 24
  end.

Section bugs.
Context `{seqlogGS Σ}.

Lemma opt_square_buggy p ks :
  remaining is_stuck' -∗
  focused p ks opt_square -∗
  goal ⊤.
Proof.
  iIntros "Hrem Hp". rewrite /opt_square.
  g_rec "Hp". g_let "Hp".
  g_call "Hp".
  g_equal "Hp". g_if_false "Hp".
  g_binop "Hp".
  replace (5 * 5)%Z with 25%Z by lia.
  g_block "Hp".
  g_match "Hp".
  g_equal "Hp".
  g_assert_stuck "Hp".
Qed.

End bugs.
