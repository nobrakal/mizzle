From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.stdlib Require Import mutex.
From mizzle.dataracebench.cases Require Import drbheld193_criticalsection3__code.

Section proof.
Context `{seqlogGS Σ}.

(** The writer guards [s <- 1] with mutex [a], the reader guards [!s] with
    mutex [b]: distinct locks, so no exclusion. Park the writer at the
    non-atomic [SetField] of [s] (holding [a]) and the reader at the
    non-atomic [GetField] of [s] (holding [b]). *)
Lemma drbheld193_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drbheld193_criticalsection3٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drbheld193_criticalsection3٠main.
g_call "Hrun". g_alloc "Hrun" "Hx". g_let "Hrun".
g_alloc "Hrun" "Hs". g_let "Hrun".
g_focus (mutex٠create _) "Hrun".
iApply (focused_mutex_create with "Hrun"). iIntros (la) "Ha Hrun". iSimpl in "Hrun".
g_let "Hrun".
g_focus (mutex٠create _) "Hrun".
iApply (focused_mutex_create with "Hrun"). iIntros (lb) "Hb Hrun". iSimpl in "Hrun".
g_let "Hrun". g_rec "Hrun". g_rec "Hrun".
iApply (drb_par_spec with "Hrun"). iIntros (q ksq ksp) "Hq Hp _".
(* writer: x <- 1; lock a; park at s <- 1 *)
g_call "Hq". g_set_field "Hq" "Hx". g_seq "Hq".
g_focus (mutex٠lock _) "Hq".
iApply (focused_mutex_lock with "Ha Hq"). iIntros "Ha Hq". iSimpl in "Hq". g_seq "Hq".
(* reader: first loop iteration, lock b; park at !s *)
g_call "Hp". g_alloc "Hp" "Hf". g_let "Hp".
g_while "Hp". g_get_field "Hp" "Hf". g_unop "Hp". g_if_true "Hp".
g_focus (mutex٠lock _) "Hp".
iApply (focused_mutex_lock with "Hb Hp"). iIntros "Hb Hp". iSimpl in "Hp". g_seq "Hp".
iApply (goal_race_close q p with "Hrem Hq Hp"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drbheld193_criticalsection3_racy v0 :
  exists c, rtc silent_step ([(drbheld193_criticalsection3٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drbheld193_racy_goal. Qed.
