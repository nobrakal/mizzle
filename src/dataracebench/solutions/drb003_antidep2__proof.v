From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.dataracebench.cases Require Import drb003_antidep2__code.

Section proof.
Context `{seqlogGS Σ}.

(** [a] is a 20x20 matrix; [parallel_for 19 (fun i => for j: a[i][j] :=
    a[i][j] + a[i+1][j])]. Thread 0 reads [a[1][0]], thread 1 writes
    [a[1][0]]: same address, one write, both non-atomic. *)
Lemma drb003_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drb003_antidep2٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drb003_antidep2٠main.
g_call "Hrun". g_let "Hrun".
g_focus (array٠make_matrix _ _ _) "Hrun".
iApply (array٠make_matrix_spec with "Hrun"); [lia..|].
iIntros (l rows Hlen) "#Hhdr Hrows Hcells Hrun". iSimpl in "Hrun".
g_let "Hrun". g_rec "Hrun". g_args "Hrun".
iApply (drb٠parallel_for_spec _ _ _ 19 with "Hrun").
iIntros (qs kss Hl1 Hl2) "Hthreads _".
destruct qs as [|q0 [|q1 qs]]; try (simpl in Hl1; lia).
destruct kss as [|ks0 [|ks1 kss]]; try (simpl in Hl2; lia).
iDestruct "Hthreads" as "(Hq0 & Hq1 & _)".
destruct rows as [|r0 [|r1 [|r2 rows]]]; try (simpl in Hlen; lia).
iDestruct "Hrows" as "(Hp0 & Hp1 & Hp2 & _)".
iDestruct "Hcells" as "((#Hh0 & Hc0) & (#Hh1 & Hc1) & (#Hh2 & Hc2) & _)".
g_call "Hq0".
iDestruct (zcells_of_replicate with "Hc1") as "Hz1".
iDestruct (zcells_of_replicate with "Hc2") as "Hz2".
iDestruct (zcells_acc r1 0 _ 0 with "Hz1") as "[Hd1 _]"; first lia.
iDestruct (zcells_acc r2 0 _ 0 with "Hz2") as "[Hd2 _]"; first lia.
iDestruct "Hd1" as (z1) "Hd1". iDestruct "Hd2" as (z2) "Hd2".
(* thread q0 (i = 0, j = 0): park at the raw GetField of a[1][0] *)
g_for "Hq0". g_args "Hq0".
g_rec "Hq0". g_call "Hq0". g_args "Hq0".
g_array_get "Hq0" "Hhdr" "Hp1".
g_array_get_to_get_field "Hq0" "Hh1".
(* thread q1 (i = 1, j = 0): read a[2][0], a[1][0], park at SetField a[1][0] *)
g_call "Hq1". g_for "Hq1". g_rec "Hq1". g_call "Hq1". g_args "Hq1".
g_array_get "Hq1" "Hhdr" "Hp2".
g_array_get "Hq1" "Hh2" "Hd2".
g_array_get "Hq1" "Hhdr" "Hp1".
g_array_get "Hq1" "Hh1" "Hd1".
g_args "Hq1".
g_array_get "Hq1" "Hhdr" "Hp1".
g_array_set_to_set_field "Hq1" "Hh1".
iApply (goal_race_close q0 q1 with "Hrem Hq0 Hq1"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drb003_antidep2_racy v0 :
  exists c, rtc silent_step ([(drb003_antidep2٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drb003_racy_goal. Qed.
