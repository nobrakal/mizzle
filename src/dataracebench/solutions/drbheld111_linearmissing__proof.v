From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.dataracebench.cases Require Import drbheld111_linearmissing__code.

Section proof.
Context `{seqlogGS Σ}.

(** Shared counter [j] is read and written by every iteration with no
    synchronisation. Thread 0 (i = 0) runs its whole body and parks at the
    raw [SetField] of [j]; thread 1 (i = 1) reads [b[1]], [a[1]] and parks
    at the raw [GetField] of [j]: same address, one write, both non-atomic. *)
Lemma drbheld111_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drbheld111_linearmissing٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drbheld111_linearmissing٠main.
g_call "Hrun". g_let "Hrun".
g_array_make "Hrun" a "Hhdr_a" "Hcells_a". g_let "Hrun".
g_array_make "Hrun" b "Hhdr_b" "Hcells_b". g_let "Hrun".
g_array_make "Hrun" c "Hhdr_c" "Hcells_c". g_let "Hrun".
g_alloc "Hrun" "Hj". g_let "Hrun".
iDestruct (zcells_of_replicate with "Hcells_a") as "Hza".
iDestruct (zcells_of_replicate with "Hcells_b") as "Hzb".
iDestruct (zcells_of_replicate with "Hcells_c") as "Hzc".
g_focus (For _ _ _) "Hrun".
iApply (focused_loop_inv ⊤ p (fun _ => zcells a 0 (Z.to_nat 100) ∗
          zcells b 0 (Z.to_nat 100) ∗ zcells c 0 (Z.to_nat 100))%I 0 100 _ _
          with "[] [Hza Hzb Hzc] Hrun"); first lia.
{ iModIntro. iIntros (i ks' Hi) "(Ha & Hb & Hc) Hf Hcont".
  g_rec "Hf". g_call "Hf".
  iDestruct (zcells_acc a 0 _ i with "Ha") as "[Hca Ha']"; first lia.
  iDestruct (zcells_acc b 0 _ i with "Hb") as "[Hcb Hb']"; first lia.
  iDestruct (zcells_acc c 0 _ i with "Hc") as "[Hcc Hc']"; first lia.
  iDestruct "Hca" as (za) "Hca". iDestruct "Hcb" as (zb) "Hcb".
  iDestruct "Hcc" as (zc) "Hcc".
  g_array_set "Hf" "Hhdr_a" "Hca". g_seq "Hf".
  g_array_set "Hf" "Hhdr_b" "Hcb". g_seq "Hf".
  g_array_set "Hf" "Hhdr_c" "Hcc".
  iApply ("Hcont" with "[Ha' Hb' Hc' Hca Hcb Hcc] Hf").
  iSplitL "Ha' Hca"; [iApply "Ha'"; by iFrame|].
  iSplitL "Hb' Hcb"; [iApply "Hb'"; by iFrame|].
  iApply "Hc'"; by iFrame. }
{ iFrame. }
iIntros "(Hza & Hzb & Hzc) Hrun". iEval (simpl) in "Hrun".
g_let "Hrun". g_rec "Hrun".
iEval (rewrite (val_int_of_nat 100 ltac:(lia))) in "Hrun".
iApply (drb٠parallel_for_spec with "Hrun").
iIntros (qs kss Hlen Hlen') "Hthreads _".
destruct qs as [|q0 [|q1 qs]]; try (simpl in Hlen; lia).
destruct kss as [|ks0 [|ks1 kss]]; try (simpl in Hlen'; lia).
iDestruct "Hthreads" as "(Hq0 & Hq1 & _)".
iDestruct (zcells_split a 0 _ 1 with "Hza") as "[Ha0 Ha1]"; first lia.
iDestruct (zcells_split b 0 _ 1 with "Hzb") as "[Hb0 Hb1]"; first lia.
iDestruct (zcells_acc a 0 1 0 with "Ha0") as "[Ha0 _]"; first lia.
iDestruct (zcells_acc b 0 1 0 with "Hb0") as "[Hb0 _]"; first lia.
iDestruct (zcells_acc a _ _ 1 with "Ha1") as "[Ha1 _]"; first lia.
iDestruct (zcells_acc b _ _ 1 with "Hb1") as "[Hb1 _]"; first lia.
iDestruct (zcells_acc c 0 _ 0 with "Hzc") as "[Hc0 _]"; first lia.
iDestruct "Ha0" as (a0) "Ha0". iDestruct "Hb0" as (b0) "Hb0".
iDestruct "Hc0" as (c0) "Hc0".
iDestruct "Ha1" as (a1) "Ha1". iDestruct "Hb1" as (b1) "Hb1".
(* thread q0 (i = 0): full iteration, park at the write [j <- !j + 1] *)
g_call "Hq0".
g_array_get "Hq0" "Hhdr_b" "Hb0".
g_array_get "Hq0" "Hhdr_a" "Ha0".
g_binop "Hq0".
g_get_field "Hq0" "Hj".
g_array_get "Hq0" "Hhdr_c" "Hc0".
g_args "Hq0".
g_get_field "Hq0" "Hj".
g_array_set "Hq0" "Hhdr_c" "Hc0".
g_seq "Hq0".
g_get_field "Hq0" "Hj".
g_args "Hq0".
(* thread q1 (i = 1): read b[1], a[1], park at the read [!j] *)
g_call "Hq1".
g_array_get "Hq1" "Hhdr_b" "Hb1".
g_array_get "Hq1" "Hhdr_a" "Ha1".
g_binop "Hq1".
iApply (goal_race_close q0 q1 with "Hrem Hq0 Hq1"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drbheld111_linearmissing_racy v0 :
  exists c, rtc silent_step ([(drbheld111_linearmissing٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drbheld111_racy_goal. Qed.
