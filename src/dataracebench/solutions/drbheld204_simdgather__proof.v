From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.dataracebench.cases Require Import drbheld204_simdgather__code.

Section proof.
Context `{seqlogGS Σ}.

(** [parallel_for 20000 (fun i => a[i+64] := a[2i] + b[i])]. Thread 0 writes
    [a[64]], thread 32 reads [a[64]]: same address, one write, both
    non-atomic. Park thread 0 at the raw [SetField] of [a[64]] and thread 32
    at the raw [GetField] of [a[64]]. *)
Lemma drbheld204_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drbheld204_simdgather٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drbheld204_simdgather٠main.
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
g_let "Hrun".
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
g_let "Hrun". g_rec "Hrun".
iEval (rewrite (val_int_of_nat 20000 ltac:(lia))) in "Hrun".
iApply (drb٠parallel_for_spec with "Hrun").
iIntros (qs kss Hlen Hlen') "Hthreads _".
(* thread 0 and thread 32 *)
destruct qs as [|q0 qs]; [simpl in Hlen; lia|].
destruct kss as [|ks0 kss]; [simpl in Hlen'; lia|].
iDestruct "Hthreads" as "[Hq0 Hthreads]".
do 31 (destruct qs as [|? qs]; [simpl in Hlen; lia|];
       destruct kss as [|? kss]; [simpl in Hlen'; lia|];
       iDestruct "Hthreads" as "[_ Hthreads]").
destruct qs as [|q1 qs]; [simpl in Hlen; lia|].
destruct kss as [|ks1 kss]; [simpl in Hlen'; lia|].
iDestruct "Hthreads" as "[Hq1 _]".
iEval (simpl) in "Hq1".
iDestruct (zcells_split a 0 _ 64 with "Hza") as "[Ha0 _]"; first lia.
iDestruct (zcells_acc a 0 _ 0 with "Ha0") as "[Hca0 _]"; first lia.
iDestruct "Hca0" as (za) "Hca0".
iDestruct (zcells_split b 0 _ 32 with "Hzb") as "[Hb0 Hb32]"; first lia.
iDestruct (zcells_acc b 0 _ 0 with "Hb0") as "[Hcb0 _]"; first lia.
iDestruct (zcells_acc b _ _ 32 with "Hb32") as "[Hcb32 _]"; first lia.
iDestruct "Hcb0" as (z0) "Hcb0". iDestruct "Hcb32" as (z32) "Hcb32".
(* thread 0: read b[0], a[0], park at the raw SetField of a[64] *)
g_call "Hq0". g_args "Hq0".
g_array_get "Hq0" "Hhdr_b" "Hcb0".
g_args "Hq0".
g_array_get "Hq0" "Hhdr_a" "Hca0".
g_args "Hq0".
g_array_set_to_set_field "Hq0" "Hhdr_a".
(* thread 32: read b[32], park at the raw GetField of a[64] *)
g_call "Hq1". g_args "Hq1".
g_array_get "Hq1" "Hhdr_b" "Hcb32".
g_args "Hq1".
g_array_get_to_get_field "Hq1" "Hhdr_a".
iApply (goal_race_close q0 q1 with "Hrem Hq0 Hq1"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drbheld204_simdgather_racy v0 :
  exists c, rtc silent_step ([(drbheld204_simdgather٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drbheld204_racy_goal. Qed.
