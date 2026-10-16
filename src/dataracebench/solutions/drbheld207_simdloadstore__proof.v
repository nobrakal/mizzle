From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.dataracebench.cases Require Import drbheld207_simdloadstore__code.

Section proof.
Context `{seqlogGS Σ}.

(** [a[i] := i; b[i] := i+1] for [i] in [0,20000), then
    [parallel_for 19936 (fun i => a[i+64] := a[i] + b[i])]. Thread 0 writes
    [a[64]], thread 64 reads [a[64]]: same address, one write, both
    non-atomic. *)
Lemma drbheld207_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drbheld207_simdloadstore٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drbheld207_simdloadstore٠main.
g_call "Hrun". g_let "Hrun".
g_array_make "Hrun" a "Hhdr_a" "Hcells_a". g_let "Hrun".
g_array_make "Hrun" b "Hhdr_b" "Hcells_b". g_let "Hrun".
iDestruct (zcells_of_replicate with "Hcells_a") as "Hza".
iDestruct (zcells_of_replicate with "Hcells_b") as "Hzb".
g_focus (For _ _ _) "Hrun".
iApply (focused_loop_inv ⊤ p (fun _ => zcells a 0 (Z.to_nat 20000) ∗ zcells b 0 (Z.to_nat 20000))%I 0 20000 _ _
          with "[] [Hza Hzb] Hrun"); first lia.
{ iModIntro. iIntros (i ks' Hi) "[Hza Hzb] Hf Hcont".
  g_rec "Hf". g_call "Hf".
  iDestruct (zcells_acc a 0 (Z.to_nat 20000) i with "Hza") as "[Hc Hza']"; first lia.
  iDestruct "Hc" as (z) "Hc".
  g_array_set "Hf" "Hhdr_a" "Hc". g_seq "Hf".
  iDestruct (zcells_acc b 0 (Z.to_nat 20000) i with "Hzb") as "[Hd Hzb']"; first lia.
  iDestruct "Hd" as (z') "Hd".
  g_args "Hf".
  g_array_set "Hf" "Hhdr_b" "Hd".
  iApply ("Hcont" with "[Hza' Hzb' Hc Hd] Hf").
  iSplitL "Hza' Hc"; [iApply "Hza'"|iApply "Hzb'"]; by iFrame. }
{ iSplitL "Hza"; [iExact "Hza"|iExact "Hzb"]. }
iIntros "[Hza Hzb] Hrun". iEval (simpl) in "Hrun".
g_seq "Hrun". g_args "Hrun".
g_rec "Hrun". g_args "Hrun".
iEval (rewrite (val_int_of_nat 19936 ltac:(lia))) in "Hrun".
iApply (drb٠parallel_for_spec with "Hrun").
iIntros (qs kss Hlen Hlen') "Hthreads _".
destruct qs as [|q0 qs]; try (simpl in Hlen; lia).
destruct kss as [|ks0 kss]; try (simpl in Hlen'; lia).
iDestruct "Hthreads" as "[Hq0 Hrest]".
destruct (lookup_lt_is_Some_2 qs 63) as [q64 Hq]; first (simpl in Hlen; lia).
destruct (lookup_lt_is_Some_2 kss 63) as [ks64 Hk]; first (simpl in Hlen'; lia).
iDestruct (big_sepL2_lookup with "Hrest") as "Hq64"; [exact Hq|exact Hk|].
iEval (simpl) in "Hq64".
iDestruct (zcells_acc a 0 _ 0 with "Hza") as "[Ha0 _]"; first lia.
iDestruct (zcells_acc b 0 _ 0 with "Hzb") as "[Hb0 Hzb']"; first lia.
iDestruct "Ha0" as (x0) "Ha0". iDestruct "Hb0" as (y0) "Hb0".
(* thread q0 (i = 0): read b[0], a[0], park at the raw SetField of a[64] *)
g_call "Hq0". g_args "Hq0".
g_array_get "Hq0" "Hhdr_b" "Hb0".
g_array_get "Hq0" "Hhdr_a" "Ha0".
g_args "Hq0".
g_array_set_to_set_field "Hq0" "Hhdr_a".
(* thread q64 (i = 64): read b[64], park at the raw GetField of a[64] *)
iDestruct ("Hzb'" with "[Hb0]") as "Hzb"; first by iExists _.
iDestruct (zcells_acc b 0 _ 64 with "Hzb") as "[Hb64 _]"; first lia.
iDestruct "Hb64" as (y) "Hb64".
g_call "Hq64". g_args "Hq64".
g_array_get "Hq64" "Hhdr_b" "Hb64".
g_array_get_to_get_field "Hq64" "Hhdr_a".
iApply (goal_race_close q0 q64 with "Hrem Hq0 Hq64"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drbheld207_simdloadstore_racy v0 :
  exists c, rtc silent_step ([(drbheld207_simdloadstore٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drbheld207_racy_goal. Qed.
