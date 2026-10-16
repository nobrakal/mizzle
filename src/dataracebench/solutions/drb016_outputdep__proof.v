From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.dataracebench.cases Require Import drb016_outputdep__code.

Section proof.
Context `{seqlogGS Σ}.

(** [x := 10], then [parallel_for 100 (fun i => a[i] := !x; x := i)].
    Every iteration writes the shared [x] non-atomically: thread 0 and
    thread 1 both park at the raw [SetField] of [x] (write/write race). *)
Lemma drb016_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drb016_outputdep٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drb016_outputdep٠main.
g_call "Hrun". g_let "Hrun".
g_array_make "Hrun" a "Hhdr_a" "Hcells_a".
g_let "Hrun".
iDestruct (zcells_of_replicate with "Hcells_a") as "Hza".
g_alloc "Hrun" "Hx".
g_let "Hrun". g_rec "Hrun".
iEval (rewrite (val_int_of_nat 100 ltac:(lia))) in "Hrun".
iApply (drb٠parallel_for_spec with "Hrun").
iIntros (qs kss Hlen Hlen') "Hthreads _".
destruct qs as [|q0 [|q1 qs]]; try (simpl in Hlen; lia).
destruct kss as [|ks0 [|ks1 kss]]; try (simpl in Hlen'; lia).
iDestruct "Hthreads" as "(Hq0 & Hq1 & _)".
iDestruct (zcells_split a 0 (Z.to_nat 100) 2 with "Hza") as "[Hz01 _]"; first lia.
iDestruct (zcells_acc a 0 2 0 with "Hz01") as "[Hc0 Hz01]"; first lia.
iDestruct "Hc0" as (z0) "Hc0".
(* thread q0 (i = 0): read x, write a[0], park at the write of x *)
g_call "Hq0".
g_get_field "Hq0" "Hx".
g_array_set "Hq0" "Hhdr_a" "Hc0".
g_seq "Hq0".
(* thread q1 (i = 1): read x, write a[1], park at the write of x *)
g_call "Hq1".
g_get_field "Hq1" "Hx".
iDestruct ("Hz01" with "[Hc0]") as "Hz01"; first by iExists _.
iDestruct (zcells_acc a 0 2 1 with "Hz01") as "[Hc1 _]"; first lia.
iDestruct "Hc1" as (z1) "Hc1".
g_array_set "Hq1" "Hhdr_a" "Hc1".
g_seq "Hq1".
iApply (goal_race_close q0 q1 with "Hrem Hq0 Hq1"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drb016_outputdep_racy v0 :
  exists c, rtc silent_step ([(drb016_outputdep٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drb016_racy_goal. Qed.
