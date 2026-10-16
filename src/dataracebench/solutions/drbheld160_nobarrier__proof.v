From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.dataracebench.cases Require Import drbheld160_nobarrier__code.

Section proof.
Context `{seqlogGS Σ}.

(** Two teams run [team 0 7] (thread q) and [team 8 15] (thread p) with no
    barrier between the two inner loops. Team p fills [temp[8..15]], then its
    second loop (k = 8) reads [temp[15-8] = temp[7]]; team q, still in its
    first loop at i = 7, writes [temp[7]]. Same address, one write, both
    non-atomic. *)
Lemma drbheld160_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drbheld160_nobarrier٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drbheld160_nobarrier٠main.
g_call "Hrun". g_let "Hrun". g_let "Hrun". g_let "Hrun".
g_array_make "Hrun" b "Hhdr_b" "Hcb". g_let "Hrun".
g_array_make "Hrun" c "Hhdr_c" "Hcc". g_let "Hrun".
g_array_make "Hrun" t "Hhdr_t" "Hct". g_let "Hrun".
iDestruct (zcells_of_replicate with "Hcb") as "Hzb".
iDestruct (zcells_of_replicate with "Hcc") as "Hzc".
iDestruct (zcells_of_replicate with "Hct") as "Hzt".
g_rec "Hrun". g_let "Hrun". g_rec "Hrun". g_rec "Hrun".
iApply (drb_par_spec with "Hrun").
iIntros (q ksq ksp) "Hq Hp _".
g_call "Hq". g_call2 "Hq". g_for "Hq".
g_call "Hp". g_call2 "Hp". g_for "Hp".
(* team p: whole first inner loop over [8,16) *)
g_rec "Hp". g_call "Hp". g_args "Hp".
g_focus (For _ _ _) "Hp".
iApply (focused_loop_inv ⊤ p (fun _ => zcells b 0 (Z.to_nat 16) ∗ zcells c 0 (Z.to_nat 16) ∗ zcells t 0 (Z.to_nat 16))%I 8 16 _ _
          with "[] [Hzb Hzc Hzt] Hp"); first lia.
{ iModIntro. iIntros (i ks' Hi) "(Hb & Hc & Ht) Hf Hcont".
  g_rec "Hf". g_call "Hf".
  iDestruct (zcells_acc c 0 _ i with "Hc") as "[Hci Hc']"; first lia.
  iDestruct (zcells_acc b 0 _ i with "Hb") as "[Hbi Hb']"; first lia.
  iDestruct (zcells_acc t 0 _ i with "Ht") as "[Hti Ht']"; first lia.
  iDestruct "Hci" as (z1) "Hci". iDestruct "Hbi" as (z2) "Hbi". iDestruct "Hti" as (z3) "Hti".
  g_array_get "Hf" "Hhdr_c" "Hci".
  g_array_get "Hf" "Hhdr_b" "Hbi".
  g_args "Hf".
  g_array_set "Hf" "Hhdr_t" "Hti".
  iApply ("Hcont" with "[Hb' Hc' Ht' Hbi Hci Hti] Hf").
  iSplitL "Hb' Hbi"; [iApply "Hb'"; by iFrame|].
  iSplitL "Hc' Hci"; [iApply "Hc'"; by iFrame|].
  iApply "Ht'"; by iFrame. }
{ iFrame. }
iIntros "(Hzb & Hzc & Hzt) Hp". iEval (simpl) in "Hp".
g_seq "Hp".
(* team p, second loop, k = 8: park at the raw read of temp[7] *)
g_args "Hp". g_for "Hp". g_rec "Hp". g_call "Hp". g_args "Hp". g_let "Hp".
g_array_get_to_get_field "Hp" "Hhdr_t".
(* team q: iterations [0,7) of the first loop, then i = 7 up to the write *)
g_rec "Hq". g_call "Hq". g_args "Hq".
g_focus (For _ _ _) "Hq".
iApply (focused_loop_prefix ⊤ q (fun _ => zcells b 0 (Z.to_nat 16) ∗ zcells c 0 (Z.to_nat 16) ∗ zcells t 0 (Z.to_nat 16))%I 0 7 8 _ _
          with "[] [Hzb Hzc Hzt] Hq"); first lia.
{ iModIntro. iIntros (i ks' Hi) "(Hb & Hc & Ht) Hf Hcont".
  g_rec "Hf". g_call "Hf".
  iDestruct (zcells_acc c 0 _ i with "Hc") as "[Hci Hc']"; first lia.
  iDestruct (zcells_acc b 0 _ i with "Hb") as "[Hbi Hb']"; first lia.
  iDestruct (zcells_acc t 0 _ i with "Ht") as "[Hti Ht']"; first lia.
  iDestruct "Hci" as (z1) "Hci". iDestruct "Hbi" as (z2) "Hbi". iDestruct "Hti" as (z3) "Hti".
  g_array_get "Hf" "Hhdr_c" "Hci".
  g_array_get "Hf" "Hhdr_b" "Hbi".
  g_args "Hf".
  g_array_set "Hf" "Hhdr_t" "Hti".
  iApply ("Hcont" with "[Hb' Hc' Ht' Hbi Hci Hti] Hf").
  iSplitL "Hb' Hbi"; [iApply "Hb'"; by iFrame|].
  iSplitL "Hc' Hci"; [iApply "Hc'"; by iFrame|].
  iApply "Ht'"; by iFrame. }
{ iFrame. }
iIntros "(Hb & Hc & _) Hq".
g_for "Hq". g_rec "Hq". g_call "Hq".
iDestruct (zcells_acc c 0 _ 7 with "Hc") as "[Hci _]"; first lia.
iDestruct (zcells_acc b 0 _ 7 with "Hb") as "[Hbi _]"; first lia.
iDestruct "Hci" as (z1) "Hci". iDestruct "Hbi" as (z2) "Hbi".
g_array_get "Hq" "Hhdr_c" "Hci".
g_array_get "Hq" "Hhdr_b" "Hbi".
g_args "Hq".
g_array_set_to_set_field "Hq" "Hhdr_t".
iApply (goal_race_close q p with "Hrem Hq Hp"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drbheld160_nobarrier_racy v0 :
  exists c, rtc silent_step ([(drbheld160_nobarrier٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drbheld160_racy_goal. Qed.
