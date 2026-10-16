From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.stdlib Require Import mutex.
From mizzle.dataracebench.cases Require Import drbheld187_barrier2__code.

Section proof.
Context `{seqlogGS Σ}.

(** The first [par] makes each thread take one lock ([l0] / [l1]). In the
    second [par], the forked thread writes [x <- 0] immediately, while the
    main thread unlocks and relocks [l1] (which does not order it with the
    other thread) and then writes [x <- 1]: two non-atomic writes to [x].
    Park both threads at their [SetField] of [x]. *)
Lemma drbheld187_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drbheld187_barrier2٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drbheld187_barrier2٠main.
g_call "Hrun".
g_alloc "Hrun" "Hx". g_let "Hrun".
g_focus (mutex٠create _) "Hrun".
iApply (focused_mutex_create with "Hrun"). iIntros (l0) "Hl0 Hrun". iSimpl in "Hrun".
g_let "Hrun".
g_focus (mutex٠create _) "Hrun".
iApply (focused_mutex_create with "Hrun"). iIntros (l1) "Hl1 Hrun". iSimpl in "Hrun".
g_let "Hrun".
(* first par: each thread takes its lock *)
g_rec "Hrun". g_rec "Hrun".
g_focus (drb٠par _ _) "Hrun".
iApply (drb_par_spec with "Hrun").
iIntros (q ksq ksp) "Hq Hp Hk".
g_call "Hq". g_call "Hp".
g_focus (mutex٠lock _) "Hq".
iApply (focused_mutex_lock with "Hl0 Hq"). iIntros "Hl0 Hq". iSimpl in "Hq".
g_focus (mutex٠lock _) "Hp".
iApply (focused_mutex_lock with "Hl1 Hp"). iIntros "Hl1 Hp". iSimpl in "Hp".
iApply ("Hk" with "Hq Hp"). iIntros "Hrun". iEval (simpl) in "Hrun".
g_seq "Hrun".
(* second par: race on the two writes to x *)
g_rec "Hrun". g_rec "Hrun".
g_focus (drb٠par _ _) "Hrun".
iApply (drb_par_spec with "Hrun").
iIntros (q' ksq' ksp') "Hq Hp _".
g_call "Hq". g_call "Hp".
g_focus (mutex٠unlock _) "Hp".
iApply (focused_mutex_unlock with "Hl1 Hp"). iIntros "Hl1 Hp". iEval (simpl) in "Hp".
g_seq "Hp".
g_focus (mutex٠lock _) "Hp".
iApply (focused_mutex_lock with "Hl1 Hp"). iIntros "Hl1 Hp". iEval (simpl) in "Hp".
g_seq "Hp".
iApply (goal_race_close q' p with "Hrem Hq Hp"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drbheld187_barrier2_racy v0 :
  exists c, rtc silent_step ([(drbheld187_barrier2٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drbheld187_racy_goal. Qed.
