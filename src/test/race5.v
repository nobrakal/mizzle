From mizzle.test Require Import test_prelude.

From mizzle.stdlib Require Import assert.

Definition double_init : expr :=
  let: "init" := ref false in
  let: "x"    := ref 0 in
  let: "y"    := ref 0 in
  let: "z"    := ref 0 in
  let: "log"  := ref 0 in
  let: "bump" := (fun: "loc" "n" => "loc" <- !"loc" + "n") in
  let: "init_once" := (fun: <> =>
    "bump" "log" 1 ;;
    if: !"init" == false then
      "bump" "x" 10 ;;
      "bump" "y" 20 ;;
      "bump" "z" 30 ;;
      "init" <- true
    else ()) in
  Fork ("init_once" ()) ;;
  Fork ("init_once" ()) ;;
  Fork ("init_once" ()) ;;
  "init_once" () ;;
  let: "sum" := !"x" + !"y" + !"z" in
  assert: !"init" == true ;;
  assert: "sum" == 60.

Section bugs.
Context `{seqlogGS Σ}.

Lemma goal_bump p ks (lc : location) (n m : Z) :
  lc ↦∗ [ValInt n] -∗
  focused p ks ((vfun: "loc" "n" => "loc" <- !"loc" + "n")%V (Val (ValLoc lc)) (Val (ValInt m))) -∗
  (lc ↦∗ [ValInt (n + m)] -∗ focused p ks (Val ValUnit) -∗ goal ⊤) -∗
  goal ⊤.
Proof.
  iIntros "Hl Hp Hk".
  g_call2 "Hp".
  g_get_field "Hp" "Hl". g_binop "Hp". g_set_field "Hp" "Hl".
  iApply ("Hk" with "Hl Hp").
Qed.

Lemma double_init_buggy p ks :
  remaining is_stuck' -∗
  focused p ks double_init -∗
  goal ⊤.
Proof.
  iIntros "Hrem Hp". rewrite /double_init.
  (* Setup: alloc init, x, y, z, log; bind bump and init_once. *)
  g_alloc "Hp" "Hinit". g_let "Hp".
  g_alloc "Hp" "Hx". g_let "Hp".
  g_alloc "Hp" "Hy". g_let "Hp".
  g_alloc "Hp" "Hz". g_let "Hp".
  g_alloc "Hp" "Hlog". g_let "Hp".
  g_rec "Hp". g_let "Hp".
  g_rec "Hp". g_let "Hp".
  (* Spawn three forks; we only need Hf1 to misbehave. *)
  g_fork "Hp" "Hf1" "Hf1loc". g_let "Hp".
  g_fork "Hp" "Hf2" "Hf2loc". g_let "Hp".
  g_fork "Hp" "Hf3" "Hf3loc". g_let "Hp".
  (* Hf1: enter init_once, bump log, read init=false, take then-branch,
     bump x to 10. Park before the y/z/init writes. *)
  g_call "Hf1".
  g_focus (App (App (Val _) (Val _)) (Val _)) "Hf1".
  iApply (goal_bump with "Hlog Hf1"). iIntros "Hlog Hf1". iSimpl in "Hf1".
  g_let "Hf1".
  g_get_field "Hf1" "Hinit". g_equal "Hf1". g_if_true "Hf1".
  g_focus (App (App (Val _) (Val _)) (Val _)) "Hf1".
  iApply (goal_bump with "Hx Hf1"). iIntros "Hx Hf1". iSimpl in "Hf1".
  replace ((0 + 10)%Z) with 10%Z by lia.
  (* Main: init still false, runs the full body, bumping x to 20. *)
  g_call "Hp".
  g_focus (App (App (Val _) (Val _)) (Val _)) "Hp".
  iApply (goal_bump with "Hlog Hp"). iIntros "Hlog Hp". iSimpl in "Hp".
  g_let "Hp".
  g_get_field "Hp" "Hinit". g_equal "Hp". g_if_true "Hp".
  g_focus (App (App (Val _) (Val _)) (Val _)) "Hp".
  iApply (goal_bump with "Hx Hp"). iIntros "Hx Hp". iSimpl in "Hp".
  replace ((10 + 10)%Z) with 20%Z by lia.
  g_let "Hp".
  g_focus (App (App (Val _) (Val _)) (Val _)) "Hp".
  iApply (goal_bump with "Hy Hp"). iIntros "Hy Hp". iSimpl in "Hp".
  replace ((0 + 20)%Z) with 20%Z by lia.
  g_let "Hp".
  g_focus (App (App (Val _) (Val _)) (Val _)) "Hp".
  iApply (goal_bump with "Hz Hp"). iIntros "Hz Hp". iSimpl in "Hp".
  replace ((0 + 30)%Z) with 30%Z by lia.
  g_let "Hp".
  g_set_field "Hp" "Hinit".
  g_let "Hp".
  (* Compute sum = 20 + 20 + 30 = 70; first assert (init=true) passes, the
     second one (sum=60) is stuck. *)
  g_get_field "Hp" "Hz". g_get_field "Hp" "Hy". g_get_field "Hp" "Hx".
  g_binop "Hp". g_binop "Hp".
  g_let "Hp".
  g_get_field "Hp" "Hinit". g_equal "Hp".
  g_assert "Hp". g_let "Hp".
  replace ((20 + 20 + 30)%Z) with 70%Z by lia.
  g_equal "Hp".
  g_assert_stuck "Hp".
Qed.

End bugs.
