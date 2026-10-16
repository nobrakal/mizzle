From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.stdlib Require Import mutex.
From mizzle.dataracebench.cases Require Import drbheld119_nestlock__code.

Section proof.
Context `{seqlogGS Σ}.

(** Thread 1 takes the lock and increments [b]; thread 2 increments [b]
    without the lock. Both park at the non-atomic write [b <- !b + 1]:
    same address, two writes, both non-atomic. *)
Lemma drbheld119_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drbheld119_nestlock٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drbheld119_nestlock٠main.
g_call "Hrun".
g_alloc "Hrun" "Ha". g_let "Hrun".
g_alloc "Hrun" "Hb". g_let "Hrun".
g_focus (mutex٠create _) "Hrun".
iApply (focused_mutex_create with "Hrun"). iIntros (lm) "Hlm Hrun". iSimpl in "Hrun".
g_let "Hrun". g_rec "Hrun". g_rec "Hrun".
g_focus (drb٠par _ _) "Hrun".
iApply (drb_par_spec with "Hrun").
iIntros (q ksq ksp) "Hq Hp _".
(* thread q: lock, then park at the write of b *)
g_call "Hq".
g_focus (mutex٠lock _) "Hq".
iApply (focused_mutex_lock with "Hlm Hq"). iIntros "Hlm Hq". iSimpl in "Hq".
g_seq "Hq".
iEval (rewrite /drbheld119_nestlock٠incr_b) in "Hq".
g_call "Hq". g_get_field "Hq" "Hb". g_args "Hq".
(* thread p: no lock, park at the write of b *)
g_call "Hp". iEval (rewrite /drbheld119_nestlock٠incr_b) in "Hp".
g_call "Hp". g_get_field "Hp" "Hb". g_args "Hp".
iApply (goal_race_close q p with "Hrem Hq Hp"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drbheld119_nestlock_racy v0 :
  exists c, rtc silent_step ([(drbheld119_nestlock٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drbheld119_racy_goal. Qed.
