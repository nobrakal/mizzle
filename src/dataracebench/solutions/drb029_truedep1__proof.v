From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.dataracebench.cases Require Import drb029_truedep1__code.

Section proof.
Context `{seqlogGS Σ}.

(** [a[i] := i] for [i] in [0,100), then [parallel_for 99 (fun i => a[i+1] :=
    a[i] + 1)]. Thread 0 writes [a[1]], thread 1 reads [a[1]]: same address,
    one write, both non-atomic. Thread 0 first reads [a[0]], then parks at the
    raw [SetField] of [a[1]]; thread 1 parks at the raw [GetField] of [a[1]]. *)
Lemma drb029_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drb029_truedep1٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drb029_truedep1٠main.
g_call "Hrun". g_let "Hrun".
g_array_make "Hrun" a "Hhdr_a" "Hcells_a".
g_let "Hrun".
iDestruct (zcells_of_replicate with "Hcells_a") as "Hza".
g_focus (For _ _ _) "Hrun".
iApply (focused_loop_inv ⊤ p (fun _ => zcells a 0 (Z.to_nat 100))%I 0 100 _ _
          with "[] [Hza] Hrun"); first lia.
{ iModIntro. iIntros (i ks' Hi) "Hz Hf Hcont".
  g_rec "Hf". g_call "Hf".
  iDestruct (zcells_acc a 0 (Z.to_nat 100) i with "Hz") as "[Hc Hz']"; first lia.
  iDestruct "Hc" as (z) "Hc".
  g_array_set "Hf" "Hhdr_a" "Hc".
  iApply ("Hcont" with "[Hz' Hc] Hf"). iApply "Hz'". by iFrame. }
{ iFrame. }
iIntros "Hza Hrun". iEval (simpl) in "Hrun".
g_let "Hrun". g_rec "Hrun".
g_args "Hrun".
iEval (rewrite (val_int_of_nat 99 ltac:(lia))) in "Hrun".
iApply (drb٠parallel_for_spec with "Hrun").
iIntros (qs kss Hlen Hlen') "Hthreads _".
destruct qs as [|q0 [|q1 qs]]; try (simpl in Hlen; lia).
destruct kss as [|ks0 [|ks1 kss]]; try (simpl in Hlen'; lia).
iDestruct "Hthreads" as "(Hq0 & Hq1 & _)".
iDestruct (zcells_acc a 0 (Z.to_nat 100) 0 with "Hza") as "[Hc0 _]"; first lia.
iDestruct "Hc0" as (z0) "Hc0".
(* thread q0 (i = 0): read a[0], then park at the raw SetField of a[1] *)
g_call "Hq0". g_args "Hq0".
g_array_get "Hq0" "Hhdr_a" "Hc0".
g_args "Hq0".
g_array_set_to_set_field "Hq0" "Hhdr_a".
(* thread q1 (i = 1): park at the raw GetField of a[1] *)
g_call "Hq1". g_args "Hq1".
g_array_get_to_get_field "Hq1" "Hhdr_a".
iApply (goal_race_close q0 q1 with "Hrem Hq0 Hq1"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drb029_truedep1_racy v0 :
  exists c, rtc silent_step ([(drb029_truedep1٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drb029_racy_goal. Qed.
