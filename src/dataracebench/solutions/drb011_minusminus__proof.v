From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.dataracebench.cases Require Import drb011_minusminus__code.

Section proof.
Context `{seqlogGS Σ}.

(** [x[i] := 5] for even [i], [-5] for odd [i], then [parallel_for 100 (fun i =>
    if x[i] <= 0 then num_nodes2 <- !num_nodes2 - 1)]. Threads 1 and 3 both see
    [-5]: thread 1 reads [num_nodes2] and parks at the non-atomic write, thread
    3 parks at the non-atomic read of [num_nodes2]. The first four init
    iterations are stepped by hand to keep the values of [x[1]] and [x[3]]. *)
Lemma drb011_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drb011_minusminus٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drb011_minusminus٠main.
g_call "Hrun". g_let "Hrun". g_let "Hrun". g_alloc "Hrun" "Hn". g_let "Hrun".
g_array_make "Hrun" a "Hhdr_a" "Hcells_a". g_let "Hrun".
iDestruct (zcells_of_replicate with "Hcells_a") as "Hza".
iDestruct (zcells_split a 0 _ 4 with "Hza") as "[Hz4 Hzr]"; first lia.
iDestruct (zcells_split a 0 4 1 with "Hz4") as "[Hz0 Hz4]"; first lia.
iDestruct (zcells_split a _ _ 1 with "Hz4") as "[Hz1 Hz4]"; first lia.
iDestruct (zcells_split a _ _ 1 with "Hz4") as "[Hz2 Hz3]"; first lia.
iDestruct (zcells_acc a _ _ 0 with "Hz0") as "[[%z0 Hc0] _]"; first lia.
iDestruct (zcells_acc a _ _ 1 with "Hz1") as "[[%z1 Hc1] _]"; first lia.
iDestruct (zcells_acc a _ _ 2 with "Hz2") as "[[%z2 Hc2] _]"; first lia.
iDestruct (zcells_acc a _ _ 3 with "Hz3") as "[[%z3 Hc3] _]"; first (simpl; lia).
g_focus (For _ _ _) "Hrun".
(* iterations 0..3 by hand *)
g_for "Hrun". g_rec "Hrun". g_call "Hrun". g_args "Hrun".
g_focus (App (App (Val structural_equality.structeq) _) _) "Hrun".
iApply (focused_structeq_int with "Hrun"). iIntros "Hrun". iEval (simpl) in "Hrun".
g_if_true "Hrun". g_array_set "Hrun" "Hhdr_a" "Hc0". g_seq "Hrun".
g_for "Hrun". g_rec "Hrun". g_call "Hrun". g_args "Hrun".
g_focus (App (App (Val structural_equality.structeq) _) _) "Hrun".
iApply (focused_structeq_int with "Hrun"). iIntros "Hrun". iEval (simpl) in "Hrun".
g_if_false "Hrun". g_args "Hrun". g_array_set "Hrun" "Hhdr_a" "Hc1". g_seq "Hrun".
g_for "Hrun". g_rec "Hrun". g_call "Hrun". g_args "Hrun".
g_focus (App (App (Val structural_equality.structeq) _) _) "Hrun".
iApply (focused_structeq_int with "Hrun"). iIntros "Hrun". iEval (simpl) in "Hrun".
g_if_true "Hrun". g_array_set "Hrun" "Hhdr_a" "Hc2". g_seq "Hrun".
g_for "Hrun". g_rec "Hrun". g_call "Hrun". g_args "Hrun".
g_focus (App (App (Val structural_equality.structeq) _) _) "Hrun".
iApply (focused_structeq_int with "Hrun"). iIntros "Hrun". iEval (simpl) in "Hrun".
g_if_false "Hrun". g_args "Hrun". g_array_set "Hrun" "Hhdr_a" "Hc3". g_seq "Hrun".
(* the rest of the init loop, generically *)
g_focus (For _ _ _) "Hrun".
iApply (focused_loop_inv ⊤ p (fun _ => zcells a (0 + 4%nat) (Z.to_nat 100 - 4))%I 4 100 _ _
          with "[] [Hzr] Hrun"); first lia.
{ iModIntro. iIntros (i ks' Hi) "Hz Hf Hcont".
  g_rec "Hf". g_call "Hf". g_args "Hf".
  iDestruct (zcells_acc a _ _ i with "Hz") as "[[%z Hc] Hz']"; first lia.
  g_focus (App (App (Val structural_equality.structeq) _) _) "Hf".
  iApply (focused_structeq_int with "Hf"). iIntros "Hf".
  destruct (bool_decide _); iEval (simpl) in "Hf".
  - g_if_true "Hf". g_array_set "Hf" "Hhdr_a" "Hc".
    iApply ("Hcont" with "[Hz' Hc] Hf"). iApply "Hz'". by iFrame.
  - g_if_false "Hf". g_args "Hf". g_array_set "Hf" "Hhdr_a" "Hc".
    iApply ("Hcont" with "[Hz' Hc] Hf"). iApply "Hz'". by iFrame. }
{ iFrame. }
iIntros "_ Hrun". iEval (simpl) in "Hrun". g_seq "Hrun".
g_rec "Hrun".
iEval (rewrite (val_int_of_nat 100 ltac:(lia))) in "Hrun".
iApply (drb٠parallel_for_spec with "Hrun").
iIntros (qs kss Hlen Hlen') "Hthreads _".
destruct qs as [|q0 [|q1 [|q2 [|q3 qs]]]]; try (simpl in Hlen; lia).
destruct kss as [|k0 [|k1 [|k2 [|k3 kss]]]]; try (simpl in Hlen'; lia).
iDestruct "Hthreads" as "(_ & Hq1 & _ & Hq3 & _)".
(* thread 1: x[1] = -5, read num_nodes2, park at the write *)
g_call "Hq1". g_array_get "Hq1" "Hhdr_a" "Hc1". g_args "Hq1". g_if_true "Hq1".
g_get_field "Hq1" "Hn". g_args "Hq1".
(* thread 3: x[3] = -5, park at the read of num_nodes2 *)
g_call "Hq3". g_array_get "Hq3" "Hhdr_a" "Hc3". g_args "Hq3". g_if_true "Hq3".
iApply (goal_race_close q1 q3 with "Hrem Hq1 Hq3"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drb011_minusminus_racy v0 :
  exists c, rtc silent_step ([(drb011_minusminus٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drb011_racy_goal. Qed.
