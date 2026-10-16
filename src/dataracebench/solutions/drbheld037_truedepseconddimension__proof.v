From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.dataracebench.cases Require Import drbheld037_truedepseconddimension__code.

Section proof.
Context `{seqlogGS Σ}.

(** [b] is a 1000x1000 matrix; for [i = 0], [parallel_for 999 (fun k =>
    b[i][k+1] := b[i][k])]. Thread 0 ([j = 1]) writes [b[0][1]], thread 1
    ([j = 2]) reads [b[0][1]]: same address, one write, both non-atomic.
    Park thread 0 at the raw [SetField] and thread 1 at the raw [GetField]. *)
Lemma drbheld037_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drbheld037_truedepseconddimension٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drbheld037_truedepseconddimension٠main.
g_call "Hrun". g_let "Hrun". g_let "Hrun".
g_focus (array٠make_matrix _ _ _) "Hrun".
iApply (array٠make_matrix_spec with "Hrun"); [lia|lia|].
iIntros (l rows Hlen) "#Hhdr Hrows Hcells Hrun". iSimpl in "Hrun".
g_let "Hrun".
destruct rows as [|r0 rows]; first (simpl in Hlen; lia).
iDestruct "Hrows" as "[Hr0 _]".
iDestruct "Hcells" as "[[#Hhr0 Hc0] _]".
iDestruct (zcells_of_replicate with "Hc0") as "Hz".
iDestruct (zcells_split r0 0 _ 1 with "Hz") as "[Hz0 Hz1]"; first lia.
iDestruct (zcells_acc r0 0 1 0 with "Hz0") as "[Hc00 _]"; first lia.
iDestruct "Hc00" as (z0) "Hc00".
iDestruct (zcells_acc r0 _ _ 1 with "Hz1") as "[Hc01 _]"; first lia.
iDestruct "Hc01" as (z1) "Hc01".
(* first outer iteration, i = 0 *)
g_for "Hrun". iSimpl in "Hrun".
g_rec "Hrun". g_call "Hrun". g_rec "Hrun". g_args "Hrun".
g_focus (App (App (Val drb٠parallel_for) _) _) "Hrun".
iApply (drb٠parallel_for_spec _ _ _ 999 with "Hrun").
iIntros (qs kss Hl1 Hl2) "Hthreads _".
destruct qs as [|q0 [|q1 qs]]; try (simpl in Hl1; lia).
destruct kss as [|ks0 [|ks1 kss]]; try (simpl in Hl2; lia).
iDestruct "Hthreads" as "(Hq0 & Hq1 & _)".
(* thread q0 (k = 0, j = 1): read b[0][0], park at the write of b[0][1] *)
g_call "Hq0". g_args "Hq0". g_let "Hq0". g_args "Hq0".
g_array_get "Hq0" "Hhdr" "Hr0".
g_array_get "Hq0" "Hhr0" "Hc00".
g_array_get "Hq0" "Hhdr" "Hr0".
g_array_set_to_set_field "Hq0" "Hhr0".
(* thread q1 (k = 1, j = 2): park at the read of b[0][1] *)
g_call "Hq1". g_args "Hq1". g_let "Hq1". g_args "Hq1".
g_array_get "Hq1" "Hhdr" "Hr0".
g_array_get_to_get_field "Hq1" "Hhr0".
iApply (goal_race_close q0 q1 with "Hrem Hq0 Hq1"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drbheld037_truedepseconddimension_racy v0 :
  exists c, rtc silent_step ([(drbheld037_truedepseconddimension٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drbheld037_racy_goal. Qed.
