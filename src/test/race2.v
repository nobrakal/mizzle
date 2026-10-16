From mizzle.test Require Import test_prelude.

From mizzle.stdlib Require Import assert.

Definition try_deposit : val :=
  vfun: "balance" "deposits" "fee" "ledger" =>
    if: !"deposits" == 0 then
      (let: "amt" := 50 - !"fee" in
       "balance" <- !"balance" + "amt" ;;
       "ledger" <- !"ledger" + "amt" ;;
       "deposits" <- 1)
    else ().

Definition bank : expr :=
  let: "balance" := ref 100 in
  let: "deposits" := ref 0 in
  let: "fee" := ref 5 in
  let: "ledger" := ref 0 in
  Fork (try_deposit "balance" "deposits" "fee" "ledger") ;;
  try_deposit "balance" "deposits" "fee" "ledger" ;;
  assert: !"deposits" == 1 ;;
  assert: !"balance" == 145 ;;
  assert: !"ledger" == 45.

Section bugs.
Context `{seqlogGS Σ}.

Lemma bank_buggy p ks :
  remaining is_stuck' -∗
  focused p ks bank -∗
  goal ⊤.
Proof.
  iIntros "Hrem Hp". rewrite /bank /try_deposit.
  (* Setup: alloc balance, deposits, fee, ledger. *)
  g_alloc "Hp" "Hb". g_let "Hp".
  g_alloc "Hp" "Hd". g_let "Hp".
  g_alloc "Hp" "Hfe". g_let "Hp".
  g_alloc "Hp" "Hl". g_let "Hp".
  (* Fork. Hp = main, Ht = forked thread. *)
  g_fork "Hp" "Ht" "Htloc". g_let "Hp".
  (* Drive forked thread: 4-arg call expansion, then read deposits=0,
     take true branch, compute amt = 50 - 5 = 45. Park before the
     writes. *)
  g_call4 "Ht".
  g_get_field "Ht" "Hd". g_equal "Ht". g_if_true "Ht".
  g_get_field "Ht" "Hfe". g_binop "Ht". g_let "Ht".
  (* Ht parked at: balance <- !balance + 45 ;; ledger <- !ledger + 45 ;;
     deposits <- 1.  Switch to main and drive its full try_deposit body. *)
  g_call4 "Hp".
  g_get_field "Hp" "Hd". g_equal "Hp". g_if_true "Hp".
  g_get_field "Hp" "Hfe". g_binop "Hp". g_let "Hp".
  g_get_field "Hp" "Hb". g_binop "Hp". g_set_field "Hp" "Hb". g_let "Hp".
  g_get_field "Hp" "Hl". g_binop "Hp". g_set_field "Hp" "Hl". g_let "Hp".
  g_set_field "Hp" "Hd".
  (* Main's body returned (); now Hp at [() ;; assert1 ;; assert2 ;; assert3]. *)
  g_let "Hp".
  (* Resume forked thread: it reads balance=145, writes 145+45=190. *)
  g_get_field "Ht" "Hb". g_binop "Ht". g_set_field "Ht" "Hb".
  g_get_field "Hp" "Hd". g_equal "Hp".

  g_assert "Hp". g_let "Hp".

  g_get_field "Hp" "Hb". g_equal "Hp".
  g_assert_stuck "Hp".
Qed.

End bugs.
