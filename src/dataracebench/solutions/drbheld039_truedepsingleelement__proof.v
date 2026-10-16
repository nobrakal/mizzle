From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.dataracebench.cases Require Import drbheld039_truedepsingleelement__code.

Section proof.
Context `{seqlogGS Σ}.

(** [a[0] := 2], then [parallel_for 1000 (fun i => a[i] := a[i] + a[0])].
    Thread 0 writes [a[0]]; thread 1 reads [a[0]] (its first redex, by
    right-to-left evaluation): same address, one write, both non-atomic. *)
Lemma drbheld039_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drbheld039_truedepsingleelement٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drbheld039_truedepsingleelement٠main.
g_call "Hrun". g_let "Hrun".
g_array_make "Hrun" a "Hhdr_a" "Hcells_a".
g_let "Hrun".
iDestruct (zcells_of_replicate with "Hcells_a") as "Hza".
iDestruct (zcells_acc a 0 (Z.to_nat 1000) 0 with "Hza") as "[Hc0 Hza']"; first lia.
iDestruct "Hc0" as (z0) "Hc0".
g_array_set "Hrun" "Hhdr_a" "Hc0".
g_seq "Hrun". g_rec "Hrun".
iEval (rewrite (val_int_of_nat 1000 ltac:(lia))) in "Hrun".
iApply (drb٠parallel_for_spec with "Hrun").
iIntros (qs kss Hlen Hlen') "Hthreads _".
destruct qs as [|q0 [|q1 qs]]; try (simpl in Hlen; lia).
destruct kss as [|ks0 [|ks1 kss]]; try (simpl in Hlen'; lia).
iDestruct "Hthreads" as "(Hq0 & Hq1 & _)".
(* thread q0 (i = 0): read a[0] twice, park at the raw SetField of a[0] *)
g_call "Hq0". g_args "Hq0".
g_array_get "Hq0" "Hhdr_a" "Hc0".
g_array_get "Hq0" "Hhdr_a" "Hc0".
g_args "Hq0".
g_array_set_to_set_field "Hq0" "Hhdr_a".
(* thread q1 (i = 1): park at the raw GetField of a[0] *)
g_call "Hq1". g_args "Hq1".
g_array_get_to_get_field "Hq1" "Hhdr_a".
iApply (goal_race_close q0 q1 with "Hrem Hq0 Hq1"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drbheld039_truedepsingleelement_racy v0 :
  exists c, rtc silent_step ([(drbheld039_truedepsingleelement٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drbheld039_racy_goal. Qed.
