From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.dataracebench.cases Require Import drb014_outofbounds__code.

Section proof.
Context `{seqlogGS Σ}.

(** [b] has 100*100 cells; [parallel_for 99 (fun k => i := k+1; for j in
    [0,100]: b[i*100+j] := b[i*100+j-1])]. Thread 0 (i = 1) at j = 99 writes
    [b[199]]; thread 1 (i = 2) at j = 0 reads [b[199]]: same address, one
    write, both non-atomic. *)
Lemma drb014_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drb014_outofbounds٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drb014_outofbounds٠main.
g_call "Hrun". g_let "Hrun". g_let "Hrun". g_args "Hrun".
g_array_make "Hrun" b "Hhdr" "Hcells".
g_let "Hrun".
iDestruct (zcells_of_replicate with "Hcells") as "Hz".
g_rec "Hrun". g_args "Hrun".
iEval (rewrite (val_int_of_nat 99 ltac:(lia))) in "Hrun".
iApply (drb٠parallel_for_spec with "Hrun").
iIntros (qs kss Hlen Hlen') "Hthreads _".
destruct qs as [|q0 [|q1 qs]]; try (simpl in Hlen; lia).
destruct kss as [|ks0 [|ks1 kss]]; try (simpl in Hlen'; lia).
iDestruct "Hthreads" as "(Hq0 & Hq1 & _)".
(* thread q0 (i = 1): run j = 0..98, then park at the write of b[199] *)
g_call "Hq0". g_args "Hq0". g_let "Hq0". iEval (simpl) in "Hq0".
g_focus (For _ _ _) "Hq0".
iApply (focused_loop_prefix ⊤ q0 (fun _ => zcells b 0 (Z.to_nat 10000))%I 0 99 100 _ _
          with "[] [Hz] Hq0"); first lia.
{ iModIntro. iIntros (i ks' Hi) "Hz Hf Hcont".
  g_rec "Hf". g_call "Hf". g_args "Hf".
  iDestruct (zcells_acc b 0 _ (100 + i - 1) with "Hz") as "[Hc Hz']"; first lia.
  iDestruct "Hc" as (z) "Hc".
  g_array_get "Hf" "Hhdr" "Hc".
  iDestruct ("Hz'" with "[Hc]") as "Hz"; first by iFrame.
  iDestruct (zcells_acc b 0 _ (100 + i) with "Hz") as "[Hc Hz']"; first lia.
  iDestruct "Hc" as (z') "Hc".
  g_args "Hf".
  g_array_set "Hf" "Hhdr" "Hc".
  iApply ("Hcont" with "[Hz' Hc] Hf"). iApply "Hz'". by iFrame. }
{ iFrame. }
iIntros "Hz Hq0".
g_for "Hq0".
g_rec "Hq0". g_call "Hq0". g_args "Hq0".
iDestruct (zcells_split b 0 _ 199 with "Hz") as "[Hza Hzb]"; first lia.
iDestruct (zcells_acc b 0 199 198 with "Hza") as "[Hc198 _]"; first lia.
iDestruct (zcells_acc b (0 + Z.of_nat 199) _ 199 with "Hzb") as "[Hc199 _]"; first lia.
iDestruct "Hc198" as (z1) "Hc198". iDestruct "Hc199" as (z2) "Hc199".
g_array_get "Hq0" "Hhdr" "Hc198".
g_args "Hq0".
g_array_set_to_set_field "Hq0" "Hhdr".
(* thread q1 (i = 2): j = 0, park at the read of b[199] *)
g_call "Hq1". g_args "Hq1". g_let "Hq1". iEval (simpl) in "Hq1".
g_for "Hq1". g_rec "Hq1". g_call "Hq1". g_args "Hq1".
g_array_get_to_get_field "Hq1" "Hhdr".
iApply (goal_race_close q0 q1 with "Hrem Hq0 Hq1"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drb014_outofbounds_racy v0 :
  exists c, rtc silent_step ([(drb014_outofbounds٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drb014_racy_goal. Qed.
