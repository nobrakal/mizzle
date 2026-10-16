From mizzle.test Require Import test_prelude.

From mizzle.stdlib Require Import assert.

Notation "'LNil'"  := (in_type "test.seq2.list" 0)(in custom mizzle_tag).
Notation "'LCons'" := (in_type "test.seq2.list" 1)(in custom mizzle_tag).

(* Recursive sum over a tagged-list ADT. The Cons branch forgets to
   add the head, so [sum [1;2;3]] returns 0 rather than 6. *)
Definition list_sum : expr :=
  let: "sum" := rec: "f" "l" =>
    match: "l" with
    | LNil => 0
    | LCons "h" "t" => "f" "t"
    end in
  let: "xs" := ‘LCons( 1, ‘LCons( 2, ‘LCons( 3, §LNil ) ) ) in
  assert: "sum" "xs" == 6.

Section bugs.
Context `{seqlogGS Σ}.

Lemma list_sum_buggy p ks :
  remaining is_stuck' -∗
  focused p ks list_sum -∗
  goal ⊤.
Proof.
  iIntros "Hrem Hp". rewrite /list_sum.
  g_rec "Hp". g_let "Hp".
  g_block "Hp".
  g_let "Hp".
  g_call "Hp". g_match "Hp".
  g_call "Hp". g_match "Hp".
  g_call "Hp". g_match "Hp".
  g_call "Hp". g_match "Hp".
  g_equal "Hp".
  g_assert_stuck "Hp".
Qed.

End bugs.
