From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.dataracebench.cases Require Import drbheld206_simdscatter__code.

Section proof.
Context `{seqlogGS Σ}.

(** Iteration [i] writes [a[2i]] and reads [a[i+64]] and [b[i]]. Thread 0
    reads [a[64]]; thread 32 writes [a[64]]: same address, one write, both
    non-atomic. Park thread 0 at the raw [GetField] of [a[64]] and thread 32
    at the raw [SetField] of [a[64]]. *)
Lemma drbheld206_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drbheld206_simdscatter٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drbheld206_simdscatter٠main.
g_call "Hrun". g_let "Hrun". g_args "Hrun".
g_array_make "Hrun" a "Hhdr_a" "Hcells_a".
g_let "Hrun".
g_array_make "Hrun" b "Hhdr_b" "Hcells_b".
g_let "Hrun".
iDestruct (zcells_of_replicate with "Hcells_a") as "Hza".
iDestruct (zcells_of_replicate with "Hcells_b") as "Hzb".
g_args "Hrun".
g_focus (For _ _ _) "Hrun".
iApply (focused_loop_inv ⊤ p (fun _ => zcells a 0 (Z.to_nat 40000))%I 0 40000 _ _
          with "[] [Hza] Hrun"); first lia.
{ iModIntro. iIntros (i ks' Hi) "Hz Hf Hcont".
  g_rec "Hf". g_call "Hf".
  iDestruct (zcells_acc a 0 (Z.to_nat 40000) i with "Hz") as "[Hc Hz']"; first lia.
  iDestruct "Hc" as (z) "Hc".
  g_array_set "Hf" "Hhdr_a" "Hc".
  iApply ("Hcont" with "[Hz' Hc] Hf"). iApply "Hz'". by iFrame. }
{ iFrame. }
iIntros "Hza Hrun". iEval (simpl) in "Hrun".
g_seq "Hrun".
g_focus (For _ _ _) "Hrun".
iApply (focused_loop_inv ⊤ p (fun _ => zcells b 0 (Z.to_nat 20000))%I 0 20000 _ _
          with "[] [Hzb] Hrun"); first lia.
{ iModIntro. iIntros (i ks' Hi) "Hz Hf Hcont".
  g_rec "Hf". g_call "Hf". g_args "Hf".
  iDestruct (zcells_acc b 0 (Z.to_nat 20000) i with "Hz") as "[Hc Hz']"; first lia.
  iDestruct "Hc" as (z) "Hc".
  g_array_set "Hf" "Hhdr_b" "Hc".
  iApply ("Hcont" with "[Hz' Hc] Hf"). iApply "Hz'". by iFrame. }
{ iFrame. }
iIntros "Hzb Hrun". iEval (simpl) in "Hrun".
g_seq "Hrun". g_rec "Hrun".
iEval (rewrite (val_int_of_nat 20000 ltac:(lia))) in "Hrun".
iApply (drb٠parallel_for_spec with "Hrun").
iIntros (qs kss Hlen Hlen') "Hthreads _".
destruct (lookup_lt_is_Some_2 qs 0) as [q0 Hq0]; first lia.
destruct (lookup_lt_is_Some_2 kss 0) as [ks0 Hks0]; first lia.
destruct (lookup_lt_is_Some_2 qs 32) as [q1 Hq1]; first lia.
destruct (lookup_lt_is_Some_2 kss 32) as [ks1 Hks1]; first lia.
iDestruct (big_sepL2_delete _ _ _ 0 with "Hthreads") as "[T0 Rest]"; [done..|].
iDestruct (big_sepL2_lookup _ _ _ 32 with "Rest") as "T1"; [done..|].
iEval (simpl) in "T1".
(* carve the needed cells: a[64], a[96], b[0], b[32] *)
iDestruct (zcells_split a 0 _ 65 with "Hza") as "[Ha1 Ha2]"; first lia.
iDestruct (zcells_split b 0 _ 1 with "Hzb") as "[Hb1 Hb2]"; first lia.
iDestruct (zcells_acc a 0 _ 64 with "Ha1") as "[Hc64 _]"; first lia.
iDestruct (zcells_acc a _ _ 96 with "Ha2") as "[Hc96 _]"; first lia.
iDestruct (zcells_acc b 0 _ 0 with "Hb1") as "[Hb0 _]"; first lia.
iDestruct (zcells_acc b _ _ 32 with "Hb2") as "[Hb32 _]"; first lia.
iDestruct "Hc64" as (z1) "Hc64". iDestruct "Hc96" as (z2) "Hc96".
iDestruct "Hb0" as (z3) "Hb0". iDestruct "Hb32" as (z4) "Hb32".
(* thread 0: read b[0], park at the raw GetField of a[64] *)
g_call "T0". g_args "T0".
g_array_get "T0" "Hhdr_b" "Hb0".
g_args "T0".
g_array_get_to_get_field "T0" "Hhdr_a".
(* thread 32: read b[32] and a[96], park at the raw SetField of a[64] *)
g_call "T1". g_args "T1".
g_array_get "T1" "Hhdr_b" "Hb32".
g_args "T1".
g_array_get "T1" "Hhdr_a" "Hc96".
g_args "T1".
g_array_set_to_set_field "T1" "Hhdr_a".
iApply (goal_race_close q0 q1 with "Hrem T0 T1"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drbheld206_simdscatter_racy v0 :
  exists c, rtc silent_step ([(drbheld206_simdscatter٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drbheld206_racy_goal. Qed.
