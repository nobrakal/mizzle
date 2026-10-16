From mizzle.test Require Import test_prelude.

From mizzle.stdlib Require Import assert.

Definition pipeline : expr :=
  let: "stages" := ref (fun: "x" => "x") in
  let: "stage" := ref 0 in
  let: "log" := ref 0 in
  let: "result" := ref 0 in
  Fork (
    "log" <- !"log" + 1 ;;
    if: !"stage" == 0 then
      (let: "old" := !"stages" in
       "stages" <- (fun: "x" => "old" "x" + 10) ;;
       "stage" <- 1)
    else ()
  ) ;;
  ("log" <- !"log" + 1 ;;
   (if: !"stage" == 0 then
      (let: "old" := !"stages" in
       "stages" <- (fun: "x" => "old" "x" * 2) ;;
       "stage" <- 1)
    else ())) ;;
  "result" <- (!"stages") 5 ;;
  assert: !"stage" == 1 ;;
  assert: (!"result" == 15) or (!"result" == 10).

Section bugs.
Context `{seqlogGS Σ}.

Lemma pipeline_buggy p ks :
  remaining is_stuck' -∗
  focused p ks pipeline -∗
  goal ⊤.
Proof.
  iIntros "Hrem Hp". rewrite /pipeline.
  (* Setup: alloc stages (closure value), stage, log, result. *)
  g_rec "Hp". g_alloc "Hp" "Hstages". g_let "Hp".
  g_alloc "Hp" "Hstage". g_let "Hp".
  g_alloc "Hp" "Hlog". g_let "Hp".
  g_alloc "Hp" "Hresult". g_let "Hp".
  (* Fork: Hp = main, Hpnew = forked. *)
  g_fork "Hp" "Hpnew" "Hpnewloc". g_let "Hp".
  (* Drive forked thread: log inc; stage=0 → if-true; wrap stages.
     Stop before [stage <- 1] so stage stays 0 for main. *)
  g_get_field "Hpnew" "Hlog". g_binop "Hpnew". g_set_field "Hpnew" "Hlog". g_let "Hpnew".
  g_get_field "Hpnew" "Hstage". g_equal "Hpnew". g_if_true "Hpnew".
  g_get_field "Hpnew" "Hstages". g_let "Hpnew".
  g_rec "Hpnew". g_set_field "Hpnew" "Hstages".
  (* Forked is parked at [stage <- 1]; switch to main. *)
  replace ((0 + 1)%Z) with 1%Z by lia.
  g_get_field "Hp" "Hlog". g_binop "Hp". g_set_field "Hp" "Hlog". g_let "Hp".
  (* Main's stage check: still 0! Both threads enter the if-true branch. *)
  g_get_field "Hp" "Hstage". g_equal "Hp". g_if_true "Hp".
  g_get_field "Hp" "Hstages". g_let "Hp".
  g_rec "Hp". g_set_field "Hp" "Hstages". g_let "Hp".
  g_set_field "Hp" "Hstage". g_let "Hp".
  (* result := (stages 5) = (5 + 10) * 2 = 30 — neither 15 nor 10. *)
  g_get_field "Hp" "Hstages".
  g_call "Hp". g_call "Hp". g_call "Hp".
  g_binop "Hp". g_binop "Hp".
  g_set_field "Hp" "Hresult". g_let "Hp".
  replace (((5 + 10) * 2)%Z) with 30%Z by lia.
  (* assert stage = 1: passes. *)
  g_get_field "Hp" "Hstage". g_equal "Hp". g_assert "Hp". g_let "Hp".
  (* assert (result = 15) or (result = 10): both fail, get stuck. *)
  g_get_field "Hp" "Hresult". g_equal "Hp". g_if_false "Hp".
  g_get_field "Hp" "Hresult". g_equal "Hp". g_assert_stuck "Hp".
Qed.

End bugs.
