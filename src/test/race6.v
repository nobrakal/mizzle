From mizzle.test Require Import test_prelude.

From mizzle.stdlib Require Import assert.

Definition memo_once : expr :=
  let: "make_once" := (fun: "f" =>
    let: "called" := ref false in
    let: "cache"  := ref 0 in
    fun: <> =>
      if: !"called" then
        !"cache"
      else
        let: "v" := "f" () in
        "cache"  <- "v" ;;
        "called" <- true ;;
        "v") in
  let: "counter" := ref 0 in
  let: "tick" := (fun: <> => "counter" <- !"counter" + 1 ;; !"counter") in
  let: "f" := "make_once" "tick" in
  Fork ("f" ()) ;;
  "f" () ;;
  assert: !"counter" == 1.

Section bugs.
Context `{seqlogGS Σ}.

Lemma memo_once_buggy p ks :
  remaining is_stuck' -∗
  focused p ks memo_once -∗
  goal ⊤.
Proof.
  iIntros "Hrem Hp". rewrite /memo_once.
  (* Setup: bind make_once, alloc counter, bind tick. *)
  g_rec "Hp". g_let "Hp".
  g_alloc "Hp" "Hcounter". g_let "Hp".
  g_rec "Hp". g_let "Hp".
  (* Run [make_once tick]: alloc called, cache; bind f. *)
  g_call "Hp".
  g_alloc "Hp" "Hcalled". g_let "Hp".
  g_alloc "Hp" "Hcache". g_let "Hp".
  g_rec "Hp". g_let "Hp".
  (* Fork. *)
  g_fork "Hp" "Hf" "Hfloc". g_let "Hp".
  (* Drive forked: sees called=false, runs tick fully (counter -> 1),
     stores cache, but stops before [called <- true]. *)
  g_call "Hf". g_get_field "Hf" "Hcalled". g_if_false "Hf".
  g_call "Hf".
  g_get_field "Hf" "Hcounter". g_binop "Hf". g_set_field "Hf" "Hcounter".
  replace ((0 + 1)%Z) with 1%Z by lia.
  g_let "Hf". g_get_field "Hf" "Hcounter". g_let "Hf".
  g_set_field "Hf" "Hcache". g_let "Hf".
  (* Switch to main: still sees called=false, runs tick again
     (counter -> 2), then [assert: !counter == 1] is stuck. *)
  g_call "Hp". g_get_field "Hp" "Hcalled". g_if_false "Hp".
  g_call "Hp".
  g_get_field "Hp" "Hcounter". g_binop "Hp". g_set_field "Hp" "Hcounter".
  replace ((1 + 1)%Z) with 2%Z by lia.
  g_let "Hp". g_get_field "Hp" "Hcounter". g_let "Hp".
  g_set_field "Hp" "Hcache". g_let "Hp".
  g_set_field "Hp" "Hcalled". g_let "Hp".
  g_let "Hp".
  g_get_field "Hp" "Hcounter". g_equal "Hp".
  g_assert_stuck "Hp".
Qed.

End bugs.
