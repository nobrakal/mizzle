From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.dataracebench.cases Require Import drb005_indirectaccess1__code.

Section proof.
Context `{seqlogGS Σ}.

(** [index_set[6g+k] := 521 + 338(g/6) + 26(g%6) + 2k], then
    [index_set[53] := 923]. So [index_set[48] = 911] and [index_set[53] = 923].
    Thread 48 writes [base[911+12] = base[923]]; thread 53 reads [base[923]].
    Park thread 48 at the raw [SetField] of [base[923]] and thread 53 at the
    raw [GetField] of [base[923]]. *)
Lemma drb005_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drb005_indirectaccess1٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drb005_indirectaccess1٠main.
g_call "Hrun". iEval (rewrite /drb005_indirectaccess1٠n) in "Hrun".
g_array_make "Hrun" a "Hhdr_a" "Hcells_a".
g_let "Hrun".
iDestruct (zcells_of_replicate with "Hcells_a") as "Hza".
g_args "Hrun".
(* invariant at position [q = 6g+k]: cell 48 holds 911 once written *)
pose (K := fun (q:Z) => (zcells a 0 48 ∗
  (if decide (q ≤ 48)%Z then ∃ z:Z, (a +ₗ 48) ↦ ValInt z else (a +ₗ 48) ↦ ValInt 911) ∗
  zcells a 49 131)%I).
iAssert (K 0) with "[Hza]" as "HK".
{ iDestruct (zcells_split a 0 (Z.to_nat 180) 48 with "Hza") as "[$ Hr]"; first lia.
  iDestruct (zcells_split _ _ _ 1 with "Hr") as "[H1 Hr]"; first lia.
  iSplitL "H1".
  { destruct decide; [|lia].
    iDestruct (zcells_acc _ _ _ 48 with "H1") as "[$ _]". simpl; lia. }
  have -> : (0 + 48%nat + 1%nat)%Z = 49%Z by lia.
  have -> : (Z.to_nat 180 - 48 - 1)%nat = 131%nat by lia. done. }
g_focus (For _ _ _) "Hrun".
iApply (focused_loop_inv ⊤ p (fun g:Z => K (6*g)%Z) 0 30 _ _ with "[] [HK] Hrun"); first lia.
2:{ done. }
{ iModIntro. iIntros (i ks' Hi) "HK Hf Hcont".
  g_rec "Hf". g_call "Hf". g_args "Hf". g_let "Hf". g_args "Hf".
  iApply (focused_loop_inv ⊤ p (fun k:Z => K (6*i+k)%Z) 0 6 _ _ with "[] [HK] Hf"); first lia.
  2:{ have -> : (6*i+0 = 6*i)%Z by lia. done. }
  { iModIntro. iIntros (k ks'' Hk) "HK Hf Hcont".
    g_rec "Hf". g_call "Hf". g_args "Hf". iDestruct "HK" as "(HL & HM & HR)".
    destruct (Z.lt_trichotomy (6*i+k) 48) as [Hlt|[Heq|Hgt]].
    - iDestruct (zcells_acc a 0 48 (6*i+k) with "HL") as "[Hc HL]"; first lia.
      iDestruct "Hc" as (z) "Hc".
      g_array_set "Hf" "Hhdr_a" "Hc".
      iApply ("Hcont" with "[-Hf] Hf"). iSplitL "HL Hc". { iApply "HL". by iFrame. }
      destruct (decide (6 * i + k ≤ 48)%Z); [|lia].
      destruct (decide (6 * i + (k+1) ≤ 48)%Z); [|lia]. iFrame.
    - assert (i = 8 /\ k = 0) as [-> ->] by lia.
      destruct (decide (6 * 8 + 0 ≤ 48)%Z); [|lia]. iDestruct "HM" as (z) "Hc".
      g_array_set "Hf" "Hhdr_a" "Hc".
      iApply ("Hcont" with "[-Hf] Hf"). simpl. iFrame.
    - iDestruct (zcells_acc a 49 131 (6*i+k) with "HR") as "[Hc HR]"; first lia.
      iDestruct "Hc" as (z) "Hc".
      g_array_set "Hf" "Hhdr_a" "Hc".
      iApply ("Hcont" with "[-Hf] Hf"). iSplitL "HL"; first done. iSplitL "HM".
      { destruct (decide (6 * i + k ≤ 48)%Z); [lia|].
        destruct (decide (6 * i + (k+1) ≤ 48)%Z); [lia|]. done. }
      iApply "HR". by iFrame. }
  iIntros "HK Hf". iApply ("Hcont" with "[HK] Hf").
  have -> : (6*(i+1) = 6*i+6)%Z by lia. done. }
iIntros "HK Hrun". iEval (simpl) in "Hrun".
iDestruct "HK" as "(_ & HM & HR)". destruct (decide (6 * 30 ≤ 48)%Z); [lia|].
g_seq "Hrun".
iDestruct (zcells_acc a 49 131 53 with "HR") as "[Hc _]"; first lia.
iDestruct "Hc" as (z) "Hc".
g_array_set "Hrun" "Hhdr_a" "Hc".
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
  iDestruct (zcells_acc b 0 (Z.to_nat 2026) i with "Hz") as "[Hc Hz']"; first lia.
  iDestruct "Hc" as (z') "Hc".
  g_array_set "Hf" "Hhdr_b" "Hc".
  iApply ("Hcont" with "[Hz' Hc] Hf"). iApply "Hz'". by iFrame. }
{ iFrame. }
iIntros "Hzb Hrun". iEval (simpl) in "Hrun".
g_seq "Hrun". g_rec "Hrun".
clear K n.
iEval (rewrite (val_int_of_nat 1 ltac:(lia)) (val_int_of_nat 180 ltac:(lia))) in "Hrun".
iApply (drb٠parallel_for_chunked_spec with "Hrun"); first lia.
iIntros (qs kss Hlen Hlen') "Hthreads _".
assert (length qs = 180) as Hq by lia.
destruct (lookup_lt_is_Some_2 qs 48) as [q48 Hq48]; first lia.
destruct (lookup_lt_is_Some_2 qs 53) as [q53 Hq53]; first lia.
destruct (lookup_lt_is_Some_2 kss 48) as [k48 Hk48]; first lia.
destruct (lookup_lt_is_Some_2 kss 53) as [k53 Hk53]; first lia.
iDestruct (big_sepL2_delete _ qs kss 48 with "Hthreads") as "[H48 Hrest]"; [done..|].
iDestruct (big_sepL2_lookup _ qs kss 53 with "Hrest") as "H53"; [done..|].
simpl.
rewrite one_chunk_spec_equation_1. destruct decide; [lia|].
iDestruct "H48" as (ks48) "[H48 _]".
rewrite one_chunk_spec_equation_1. destruct decide; [lia|].
iDestruct "H53" as (ks53) "[H53 _]".
iDestruct (zcells_split b 0 (Z.to_nat 2026) 912 with "Hzb") as "[Hb1 Hb2]"; first lia.
iDestruct (zcells_acc b 0 912 911 with "Hb1") as "[Hc911 _]"; first lia.
iDestruct (zcells_acc b _ _ 923 with "Hb2") as "[Hc923 _]"; first lia.
iDestruct "Hc911" as (w1) "Hc911". iDestruct "Hc923" as (w2) "Hc923".
(* thread 48: idx = 911; update base[911], read base[923], park at its write *)
g_call "H48". g_args "H48".
g_array_get "H48" "Hhdr_a" "HM".
g_let "H48". g_args "H48".
g_array_get "H48" "Hhdr_b" "Hc911". g_args "H48".
g_array_set "H48" "Hhdr_b" "Hc911". g_seq "H48". g_args "H48".
g_array_get "H48" "Hhdr_b" "Hc923". g_args "H48".
g_array_set_to_set_field "H48" "Hhdr_b".
(* thread 53: idx = 923; park at the read of base[923] *)
g_call "H53". g_args "H53".
g_array_get "H53" "Hhdr_a" "Hc".
g_let "H53". g_args "H53".
g_array_get_to_get_field "H53" "Hhdr_b".
iApply (goal_race_close q48 q53 with "Hrem H48 H53"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drb005_indirectaccess1_racy v0 :
  exists c, rtc silent_step ([(drb005_indirectaccess1٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drb005_racy_goal. Qed.
