
From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.dataracebench.cases Require Import drbheld179_threadsensitivity__code.

Section proof.
Context `{seqlogGS Σ}.

(** [a := make 100 0], then [parallel_for 100 (fun i => a[i] := i; if i = 1
    then a[0] := 1)]. Thread 0 writes [a[0]] (its own cell), thread 1 also
    writes [a[0]] in its [i = 1] branch: same address, both writes, both
    non-atomic. Park both at the raw [SetField] of [a[0]]. *)
Lemma drbheld179_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drbheld179_threadsensitivity٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drbheld179_threadsensitivity٠main.
g_call "Hrun". g_let "Hrun".
g_array_make "Hrun" a "Hhdr_a" "Hcells_a".
g_let "Hrun".
iDestruct (zcells_of_replicate with "Hcells_a") as "Hza".
g_rec "Hrun".
iEval (rewrite (val_int_of_nat 100 ltac:(lia))) in "Hrun".
iApply (drb٠parallel_for_spec with "Hrun").
iIntros (qs kss Hlen Hlen') "Hthreads _".
destruct qs as [|q0 [|q1 qs]]; try (simpl in Hlen; lia).
destruct kss as [|ks0 [|ks1 kss]]; try (simpl in Hlen'; lia).
iDestruct "Hthreads" as "(Hq0 & Hq1 & _)".
iDestruct (zcells_acc a 0 _ 1 with "Hza") as "[Hc1 _]"; first lia.
iDestruct "Hc1" as (z1) "Hc1".
(* thread q0 (i = 0): park at the raw SetField of a[0] *)
g_call "Hq0". g_args "Hq0".
g_array_set_to_set_field "Hq0" "Hhdr_a".
(* thread q1 (i = 1): write a[1], take the branch, park at SetField of a[0] *)
g_call "Hq1". g_args "Hq1".
g_array_set "Hq1" "Hhdr_a" "Hc1".
g_seq "Hq1".
g_focus (App (App _ _) _) "Hq1".
iApply (focused_structeq_int with "Hq1"). iIntros "Hq1".
iEval (simpl) in "Hq1".
g_if_true "Hq1".
g_array_set_to_set_field "Hq1" "Hhdr_a".
iApply (goal_race_close q0 q1 with "Hrem Hq0 Hq1"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drbheld179_threadsensitivity_racy v0 :
  exists c, rtc silent_step ([(drbheld179_threadsensitivity٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drbheld179_racy_goal. Qed.
