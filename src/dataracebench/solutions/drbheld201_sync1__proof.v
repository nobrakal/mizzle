From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.stdlib Require Import mutex.
From mizzle.dataracebench.cases Require Import drbheld201_sync1__code.

Section proof.
Context `{seqlogGS Σ}.

(** [x := ref 1], mutex [l], then [par f g]: [f] writes [x <- 0] inside the
    critical section, [g] writes [x <- 1] *after* unlocking. Schedule: [g]
    locks, unlocks and parks at its write; [f] then locks and parks at its
    write. Two non-atomic writes to [x]: a race. *)
Lemma drbheld201_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drbheld201_sync1٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drbheld201_sync1٠main.
g_call "Hrun". g_alloc "Hrun" "Hx". g_let "Hrun".
g_focus (mutex٠create _) "Hrun".
iApply (focused_mutex_create with "Hrun"). iIntros (lm) "Hm Hrun". iSimpl in "Hrun".
g_let "Hrun". g_rec "Hrun". g_rec "Hrun".
g_focus (drb٠par _ _) "Hrun".
iApply (drb_par_spec with "Hrun"). iIntros (q ksq ksp) "Hq Hp _".
(* thread p (g): lock; unlock; park at [x <- 1] *)
g_call "Hp". g_focus (mutex٠lock _) "Hp".
iApply (focused_mutex_lock with "Hm Hp"). iIntros "Hm Hp". iSimpl in "Hp".
g_seq "Hp". g_focus (mutex٠unlock _) "Hp".
iApply (focused_mutex_unlock with "Hm Hp"). iIntros "Hm Hp". iSimpl in "Hp".
g_seq "Hp".
(* thread q (f): lock; park at [x <- 0] *)
g_call "Hq". g_focus (mutex٠lock _) "Hq".
iApply (focused_mutex_lock with "Hm Hq"). iIntros "Hm Hq". iSimpl in "Hq".
g_seq "Hq".
iApply (goal_race_close q p with "Hrem Hq Hp"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drbheld201_sync1_racy v0 :
  exists c, rtc silent_step ([(drbheld201_sync1٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drbheld201_racy_goal. Qed.
