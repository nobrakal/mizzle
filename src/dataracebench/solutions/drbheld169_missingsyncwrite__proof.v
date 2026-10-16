From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.dataracebench.cases Require Import drbheld169_missingsyncwrite__code.

Section proof.
Context `{seqlogGS Σ}.

(** Read [r[n]] through the generic block, then restore it. *)
Local Ltac rd R H n := iDestruct (zcells_acc R 0 _ n with "Hz") as "[Hc Hz]"; [lia|];
  iDestruct "Hc" as (?) "Hc"; g_array_get H "Hhdr" "Hc";
  iDestruct ("Hz" with "[Hc]") as "Hz"; [by iFrame|]; g_args H.

(** Every parallel iteration writes [r1[k]] for all [k], unsynchronized.
    Thread 0 (i = 1) and thread 1 (i = 2) both reach [r1[0] := ...] at
    [j = 1, k = 0]: same address, two non-atomic writes. Park both at the
    raw [SetField] of [r1[0]]. *)
Lemma drbheld169_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drbheld169_missingsyncwrite٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drbheld169_missingsyncwrite٠main.
g_call "Hrun". g_let "Hrun".
g_array_make "Hrun" r1 "Hhdr1" "Hc1".
g_let "Hrun".
g_args "Hrun".
g_array_make "Hrun" r "Hhdr" "Hcr".
g_let "Hrun".
iDestruct (zcells_of_replicate with "Hcr") as "Hz".
g_focus (For _ _ _) "Hrun".
(* triple-nested init loop *)
iApply (focused_loop_inv ⊤ p (fun _ => zcells r 0 (Z.to_nat 512))%I 0 8 _ _ with "[] [Hz] Hrun"); first lia.
{ iModIntro. iIntros (i ks' Hi) "Hz Hf Hcont".
  g_rec "Hf". g_call "Hf".
  iApply (focused_loop_inv ⊤ p (fun _ => zcells r 0 (Z.to_nat 512))%I 0 8 _ _ with "[] [Hz] Hf"); first lia.
  { iModIntro. iIntros (j ks'' Hj) "Hz Hf Hcont".
    g_rec "Hf". g_call "Hf".
    iApply (focused_loop_inv ⊤ p (fun _ => zcells r 0 (Z.to_nat 512))%I 0 8 _ _ with "[] [Hz] Hf"); first lia.
    { iModIntro. iIntros (k ks3 Hk) "Hz Hf Hcont".
      g_rec "Hf". g_call "Hf".
      iDestruct (zcells_acc r 0 (Z.to_nat 512) ((i * 8 + j) * 8 + k) with "Hz") as "[Hc Hz']"; first lia.
      iDestruct "Hc" as (z) "Hc".
      g_args "Hf".
      g_array_set "Hf" "Hhdr" "Hc".
      iApply ("Hcont" with "[Hz' Hc] Hf"). iApply "Hz'". by iFrame. }
    { iFrame. }
    iIntros "Hz Hf". iApply ("Hcont" with "Hz Hf"). }
  { iFrame. }
  iIntros "Hz Hf". iApply ("Hcont" with "Hz Hf"). }
{ iFrame. }
iIntros "Hz Hrun". iEval (simpl) in "Hrun".
g_let "Hrun". g_rec "Hrun". g_args "Hrun".
iEval (rewrite (val_int_of_nat 6 ltac:(lia))) in "Hrun".
iApply (drb٠parallel_for_spec with "Hrun").
iIntros (qs kss Hlen Hlen') "Hthreads _".
destruct qs as [|q0 [|q1 qs]]; try (simpl in Hlen; lia).
destruct kss as [|ks0 [|ks1 kss]]; try (simpl in Hlen'; lia).
iDestruct "Hthreads" as "(Hq0 & Hq1 & _)".
(* thread q0 (i = 1, j = 1, k = 0): reads r[136], r[8], r[80], r[64] *)
g_call "Hq0". g_args "Hq0". g_let "Hq0". g_args "Hq0". g_for "Hq0".
g_rec "Hq0". g_call "Hq0". g_for "Hq0". g_rec "Hq0". g_call "Hq0". g_args "Hq0".
rd r "Hq0" 136. rd r "Hq0" 8. rd r "Hq0" 80. rd r "Hq0" 64.
g_array_set_to_set_field "Hq0" "Hhdr1".
(* thread q1 (i = 2, j = 1, k = 0): reads r[200], r[72], r[144], r[128] *)
g_call "Hq1". g_args "Hq1". g_let "Hq1". g_args "Hq1". g_for "Hq1".
g_rec "Hq1". g_call "Hq1". g_for "Hq1". g_rec "Hq1". g_call "Hq1". g_args "Hq1".
rd r "Hq1" 200. rd r "Hq1" 72. rd r "Hq1" 144. rd r "Hq1" 128.
g_array_set_to_set_field "Hq1" "Hhdr1".
iApply (goal_race_close q0 q1 with "Hrem Hq0 Hq1"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drbheld169_missingsyncwrite_racy v0 :
  exists c, rtc silent_step ([(drbheld169_missingsyncwrite٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drbheld169_racy_goal. Qed.
