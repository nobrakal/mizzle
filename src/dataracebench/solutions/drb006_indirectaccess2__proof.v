From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.dataracebench.cases Require Import drb006_indirectaccess2__code.

Section proof.
Context `{seqlogGS Σ}.

(** [index_set[0] = 521] and, after the overwrite, [index_set[5] = 533].
    Thread 0 writes [base[521+12] = base[533]] (second update); thread 5
    reads [base[533]] (first update). Same address, one write, both
    non-atomic. *)
Lemma drb006_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drb006_indirectaccess2٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drb006_indirectaccess2٠main.
g_call "Hrun".
iEval (rewrite /drb006_indirectaccess2٠n) in "Hrun".
g_array_make "Hrun" a "Hhdr_a" "Hcells_a".
g_let "Hrun".
iDestruct (zcells_of_replicate with "Hcells_a") as "Hza".
g_args "Hrun".
(* outer iteration g = 0, by hand, to learn index_set[0] = 521 *)
g_focus (For _ _ _) "Hrun".
g_for "Hrun".
g_rec "Hrun". g_call "Hrun". g_args "Hrun". g_let "Hrun". g_args "Hrun".
iDestruct (zcells_split a 0 (Z.to_nat 180) 1 with "Hza") as "[Hz0 Hz1]"; first lia.
iDestruct (zcells_acc a 0 1 0 with "Hz0") as "[Hc0 _]"; first lia.
iDestruct "Hc0" as (z0) "Hc0".
g_focus (For _ _ _) "Hrun".
g_for "Hrun".
g_rec "Hrun". g_call "Hrun". g_args "Hrun".
g_array_set "Hrun" "Hhdr_a" "Hc0".
g_seq "Hrun". g_args "Hrun".
g_focus (For _ _ _) "Hrun".
iApply (focused_loop_inv ⊤ p (fun _ => zcells a (0 + 1%nat) (Z.to_nat 180 - 1))%I 1 6 _ _
          with "[] [Hz1] Hrun"); first lia.
{ iModIntro. iIntros (i ks' Hi) "Hz Hf Hcont".
  g_rec "Hf". g_call "Hf". g_args "Hf".
  iDestruct (zcells_acc a _ _ i with "Hz") as "[Hc Hz']"; first lia.
  iDestruct "Hc" as (z) "Hc".
  g_array_set "Hf" "Hhdr_a" "Hc".
  iApply ("Hcont" with "[Hz' Hc] Hf"). iApply "Hz'". by iFrame. }
{ iFrame. }
iIntros "Hz1 Hrun". iEval (simpl) in "Hrun".
g_seq "Hrun".
(* outer iterations g = 1..29 only touch indices >= 6 *)
g_focus (For _ _ _) "Hrun".
iApply (focused_loop_inv ⊤ p (fun _ => zcells a (0 + 1%nat) (Z.to_nat 180 - 1))%I 1 30 _ _
          with "[] [Hz1] Hrun"); first lia.
{ iModIntro. iIntros (g ks' Hg) "Hz Hf Hcont".
  g_rec "Hf". g_call "Hf". g_args "Hf". g_let "Hf". g_args "Hf".
  g_focus (For _ _ _) "Hf".
  iApply (focused_loop_inv ⊤ p (fun _ => zcells a (0 + 1%nat) (Z.to_nat 180 - 1))%I 0 6 _ _
          with "[] [Hz] Hf"); first lia.
  { iModIntro. iIntros (k ks'' Hk) "Hz Hf Hcont".
    g_rec "Hf". g_call "Hf". g_args "Hf".
    iDestruct (zcells_acc a _ _ (6 * g + k) with "Hz") as "[Hc Hz']"; first lia.
    iDestruct "Hc" as (z) "Hc".
    g_array_set "Hf" "Hhdr_a" "Hc".
    iApply ("Hcont" with "[Hz' Hc] Hf"). iApply "Hz'". by iFrame. }
  { iFrame. }
  iIntros "Hz Hf". iEval (simpl) in "Hf".
  iApply ("Hcont" with "Hz Hf"). }
{ iFrame. }
iIntros "Hz1 Hrun". iEval (simpl) in "Hrun".
g_seq "Hrun".
(* index_set[5] := 533 *)
iDestruct (zcells_split a (0 + 1%nat) (Z.to_nat 180 - 1) 4 with "Hz1") as "[Hz14 Hz5]"; first lia.
iDestruct (zcells_acc a _ _ 5 with "Hz5") as "[Hc5 _]"; first lia.
iDestruct "Hc5" as (z5) "Hc5".
g_array_set "Hrun" "Hhdr_a" "Hc5".
g_seq "Hrun". g_args "Hrun".
g_array_make "Hrun" b "Hhdr_b" "Hcells_b".
g_let "Hrun".
iDestruct (zcells_of_replicate with "Hcells_b") as "Hzb".
g_args "Hrun".
g_focus (For _ _ _) "Hrun".
iApply (focused_loop_inv ⊤ p (fun _ => zcells b 0 (Z.to_nat 2026))%I 521 2026 _ _
          with "[] [Hzb] Hrun"); first lia.
{ iModIntro. iIntros (i ks' Hi) "Hz Hf Hcont".
  g_rec "Hf". g_call "Hf".
  iDestruct (zcells_acc b 0 _ i with "Hz") as "[Hc Hz']"; first lia.
  iDestruct "Hc" as (z) "Hc".
  g_array_set "Hf" "Hhdr_b" "Hc".
  iApply ("Hcont" with "[Hz' Hc] Hf"). iApply "Hz'". by iFrame. }
{ iFrame. }
iIntros "Hzb Hrun". iEval (simpl) in "Hrun".
g_seq "Hrun". g_rec "Hrun". g_args "Hrun".
iEval (rewrite (val_int_of_nat 180 ltac:(lia))) in "Hrun".
iApply (drb٠parallel_for_spec with "Hrun").
iIntros (qs kss Hlen Hlen') "Hthreads _".
do 6 (destruct qs as [|? qs]; try (simpl in Hlen; lia)).
do 6 (destruct kss as [|? kss]; try (simpl in Hlen'; lia)).
iDestruct "Hthreads" as "(Hq0 & _ & _ & _ & _ & Hq5 & _)".
iDestruct (zcells_split b 0 (Z.to_nat 2026) 533 with "Hzb") as "[Hb1 Hb2]"; first lia.
iDestruct (zcells_acc b 0 533 521 with "Hb1") as "[Hc521 _]"; first lia.
iDestruct (zcells_acc b (0 + Z.of_nat 533) _ 533 with "Hb2") as "[Hc533 _]"; first lia.
iDestruct "Hc521" as (y1) "Hc521". iDestruct "Hc533" as (y2) "Hc533".
(* thread 0: idx = 521; update base[521], read base[533], park at its write *)
g_call "Hq0".
g_array_get "Hq0" "Hhdr_a" "Hc0". g_let "Hq0".
g_array_get "Hq0" "Hhdr_b" "Hc521". g_args "Hq0".
g_array_set "Hq0" "Hhdr_b" "Hc521". g_seq "Hq0". g_args "Hq0".
g_array_get "Hq0" "Hhdr_b" "Hc533". g_args "Hq0".
g_array_set_to_set_field "Hq0" "Hhdr_b".
(* thread 5: idx = 533; park at the read of base[533] *)
g_call "Hq5".
g_array_get "Hq5" "Hhdr_a" "Hc5". g_let "Hq5".
g_array_get_to_get_field "Hq5" "Hhdr_b".
iApply (goal_race_close n n4 with "Hrem Hq0 Hq5"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drb006_indirectaccess2_racy v0 :
  exists c, rtc silent_step ([(drb006_indirectaccess2٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drb006_racy_goal. Qed.
