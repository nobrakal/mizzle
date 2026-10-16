
From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.dataracebench.cases Require Import drb024_simdtruedep__code.

Section proof.
Context `{seqlogGS Σ}.

(** Init [a[i] := i], [b[i] := i+1], then [parallel_for 99 (fun i => a[i+1]
    := a[i] + b[i])]. Thread 0 writes [a[1]], thread 1 reads [a[1]]: same
    address, one write, both non-atomic. Evaluation is right-to-left, so each
    thread reads [b[i]] before [a[i]]. Park thread 0 at the raw [SetField] of
    [a[1]] and thread 1 at the raw [GetField] of [a[1]]. *)
Lemma drb024_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drb024_simdtruedep٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drb024_simdtruedep٠main.
g_call "Hrun". g_let "Hrun".
g_array_make "Hrun" a "Hhdr_a" "Hcells_a". g_let "Hrun".
g_array_make "Hrun" b "Hhdr_b" "Hcells_b". g_let "Hrun".
iDestruct (zcells_of_replicate with "Hcells_a") as "Hza".
iDestruct (zcells_of_replicate with "Hcells_b") as "Hzb".
g_focus (For _ _ _) "Hrun".
iApply (focused_loop_inv ⊤ p
          (fun _ => zcells a 0 (Z.to_nat 100) ∗ zcells b 0 (Z.to_nat 100))%I 0 100 _ _
          with "[] [Hza Hzb] Hrun"); first lia.
{ iModIntro. iIntros (i ks' Hi) "[Hza Hzb] Hf Hcont".
  g_rec "Hf". g_call "Hf".
  iDestruct (zcells_acc a 0 (Z.to_nat 100) i with "Hza") as "[Hc Hza']"; first lia.
  iDestruct "Hc" as (z) "Hc".
  g_array_set "Hf" "Hhdr_a" "Hc".
  g_seq "Hf". g_args "Hf".
  iDestruct (zcells_acc b 0 (Z.to_nat 100) i with "Hzb") as "[Hd Hzb']"; first lia.
  iDestruct "Hd" as (z') "Hd".
  g_array_set "Hf" "Hhdr_b" "Hd".
  iApply ("Hcont" with "[Hza' Hzb' Hc Hd] Hf").
  iSplitL "Hza' Hc"; [iApply "Hza'"|iApply "Hzb'"]; by iFrame. }
{ iFrame. }
iIntros "[Hza Hzb] Hrun". iEval (simpl) in "Hrun".
g_let "Hrun". g_rec "Hrun".
g_args "Hrun".
iEval (rewrite (val_int_of_nat 99 ltac:(lia))) in "Hrun".
iApply (drb٠parallel_for_spec with "Hrun").
iIntros (qs kss Hlen Hlen') "Hthreads _".
destruct qs as [|q0 [|q1 qs]]; try (simpl in Hlen; lia).
destruct kss as [|ks0 [|ks1 kss]]; try (simpl in Hlen'; lia).
iDestruct "Hthreads" as "(Hq0 & Hq1 & _)".
(* carve a[0], b[0], b[1] out of the generic blocks *)
iDestruct (zcells_split a 0 (Z.to_nat 100) 2 with "Hza") as "[Ha01 _]"; first lia.
iDestruct (zcells_acc a 0 2 0 with "Ha01") as "[Ha0 _]"; first lia.
iDestruct "Ha0" as (w0) "Ha0".
iDestruct (zcells_split b 0 (Z.to_nat 100) 2 with "Hzb") as "[Hb01 _]"; first lia.
iDestruct (zcells_split b 0 2 1 with "Hb01") as "[Hbl Hbr]"; first lia.
iDestruct (zcells_acc b 0 1 0 with "Hbl") as "[Hb0 _]"; first lia.
iDestruct (zcells_acc b (0 + Z.of_nat 1) _ 1 with "Hbr") as "[Hb1 _]"; first lia.
iDestruct "Hb0" as (y0) "Hb0". iDestruct "Hb1" as (y1) "Hb1".
(* thread q0 (i = 0): read b[0], a[0], park at the raw SetField of a[1] *)
g_call "Hq0". g_args "Hq0".
g_array_get "Hq0" "Hhdr_b" "Hb0".
g_array_get "Hq0" "Hhdr_a" "Ha0".
g_args "Hq0".
g_array_set_to_set_field "Hq0" "Hhdr_a".
(* thread q1 (i = 1): read b[1], park at the raw GetField of a[1] *)
g_call "Hq1". g_args "Hq1".
g_array_get "Hq1" "Hhdr_b" "Hb1".
g_array_get_to_get_field "Hq1" "Hhdr_a".
iApply (goal_race_close q0 q1 with "Hrem Hq0 Hq1"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drb024_simdtruedep_racy v0 :
  exists c, rtc silent_step ([(drb024_simdtruedep٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drb024_racy_goal. Qed.
