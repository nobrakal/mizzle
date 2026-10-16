From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.dataracebench.cases Require Import drb009_lastprivatemissing__code.

Section proof.
Context `{seqlogGS Σ}.

(** [x := ref 0], then [parallel_for 10000 (fun i => x <- i)]. Threads 0 and 1
    both write [x] non-atomically: park each at its raw [SetField]. *)
Lemma drb009_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drb009_lastprivatemissing٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drb009_lastprivatemissing٠main.
g_call "Hrun". g_let "Hrun".
g_alloc "Hrun" "Hx". g_let "Hrun". g_rec "Hrun".
iEval (rewrite (val_int_of_nat 10000 ltac:(lia))) in "Hrun".
iApply (drb٠parallel_for_spec with "Hrun").
iIntros (qs kss Hlen Hlen') "Hthreads _".
destruct qs as [|q0 [|q1 qs]]; try (simpl in Hlen; lia).
destruct kss as [|ks0 [|ks1 kss]]; try (simpl in Hlen'; lia).
iDestruct "Hthreads" as "(Hq0 & Hq1 & _)".
g_call "Hq0". g_call "Hq1".
iApply (goal_race_close q0 q1 with "Hrem Hq0 Hq1"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drb009_lastprivatemissing_racy v0 :
  exists c, rtc silent_step ([(drb009_lastprivatemissing٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drb009_racy_goal. Qed.
