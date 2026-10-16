From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.stdlib Require Import mutex.
From mizzle.dataracebench.cases Require Import drbheld074_flush__code.

Section proof.
Context `{seqlogGS Σ}.

(** Both branches write [i <- 1] under the lock, but read [!i] after
    releasing it. Thread q runs [f1] to completion and parks at the
    unprotected read of [i]; thread p takes the lock and parks at its
    write of [i]: same address, one write, both non-atomic. *)
Lemma drbheld074_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drbheld074_flush٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drbheld074_flush٠main.
g_call "Hrun". g_alloc "Hrun" "Hi". g_let "Hrun".
g_focus (mutex٠create _) "Hrun".
iApply (focused_mutex_create with "Hrun"). iIntros (lm) "Hlm Hrun". iSimpl in "Hrun".
g_let "Hrun". g_alloc "Hrun" "Hs1". g_let "Hrun". g_alloc "Hrun" "Hs2". g_let "Hrun".
g_rec "Hrun". g_rec "Hrun".
g_focus (drb٠par _ _) "Hrun".
iApply (drb_par_spec with "Hrun").
iIntros (q ksq ksp) "Hq Hp _".
(* thread q: lock; i <- 1; unlock; park at the read of i *)
g_call "Hq". iEval (rewrite /drbheld074_flush٠f1) in "Hq". g_call2 "Hq".
g_focus (mutex٠lock _) "Hq".
iApply (focused_mutex_lock with "Hlm Hq"). iIntros "Hlm Hq". iSimpl in "Hq".
g_seq "Hq". g_set_field "Hq" "Hi". g_seq "Hq".
g_focus (mutex٠unlock _) "Hq".
iApply (focused_mutex_unlock with "Hlm Hq"). iIntros "Hlm Hq". iSimpl in "Hq".
g_seq "Hq".
(* thread p: lock; park at the write i <- 1 *)
g_call "Hp". iEval (rewrite /drbheld074_flush٠f1) in "Hp". g_call2 "Hp".
g_focus (mutex٠lock _) "Hp".
iApply (focused_mutex_lock with "Hlm Hp"). iIntros "Hlm Hp". iSimpl in "Hp".
g_seq "Hp".
iApply (goal_race_close q p with "Hrem Hq Hp"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drbheld074_flush_racy v0 :
  exists c, rtc silent_step ([(drbheld074_flush٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drbheld074_racy_goal. Qed.
