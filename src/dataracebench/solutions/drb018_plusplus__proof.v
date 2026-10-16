From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.dataracebench.cases Require Import drb018_plusplus__code.

Section proof.
Context `{seqlogGS Σ}.

(** Every iteration does [idx := !out_len; out_len <- idx + 1]: the shared
    counter is read and written non-atomically by all threads. Thread 0 reads
    [out_len] and is parked at the raw [SetField] of [out_len]; thread 1 is
    parked at its raw [GetField] of [out_len]. *)
Lemma drb018_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drb018_plusplus٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drb018_plusplus٠main.
g_call "Hrun". g_let "Hrun".
g_alloc "Hrun" "Hl". g_let "Hrun".
g_array_make "Hrun" a "Hhdr_a" "Hcells_a". g_let "Hrun".
g_array_make "Hrun" b "Hhdr_b" "Hcells_b". g_let "Hrun".
iDestruct (zcells_of_replicate with "Hcells_a") as "Hza".
g_focus (For _ _ _) "Hrun".
iApply (focused_loop_inv ⊤ p (fun _ => zcells a 0 (Z.to_nat 1000))%I 0 1000 _ _
          with "[] [Hza] Hrun"); first lia.
{ iModIntro. iIntros (i ks' Hi) "Hz Hf Hcont".
  g_rec "Hf". g_call "Hf".
  iDestruct (zcells_acc a 0 (Z.to_nat 1000) i with "Hz") as "[Hc Hz']"; first lia.
  iDestruct "Hc" as (z) "Hc".
  g_array_set "Hf" "Hhdr_a" "Hc".
  iApply ("Hcont" with "[Hz' Hc] Hf"). iApply "Hz'". by iFrame. }
{ iFrame. }
iIntros "Hza Hrun". iEval (simpl) in "Hrun".
g_seq "Hrun". g_rec "Hrun".
iEval (rewrite (val_int_of_nat 1000 ltac:(lia))) in "Hrun".
iApply (drb٠parallel_for_spec with "Hrun").
iIntros (qs kss Hlen Hlen') "Hthreads _".
destruct qs as [|q0 [|q1 qs]]; try (simpl in Hlen; lia).
destruct kss as [|ks0 [|ks1 kss]]; try (simpl in Hlen'; lia).
iDestruct "Hthreads" as "(Hq0 & Hq1 & _)".
(* thread q0: read out_len, park at the write out_len <- 1 *)
g_call "Hq0". g_get_field "Hq0" "Hl". g_let "Hq0". g_args "Hq0".
(* thread q1: park at the read !out_len *)
g_call "Hq1".
iApply (goal_race_close q0 q1 with "Hrem Hq0 Hq1"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drb018_plusplus_racy v0 :
  exists c, rtc silent_step ([(drb018_plusplus٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drb018_racy_goal. Qed.
