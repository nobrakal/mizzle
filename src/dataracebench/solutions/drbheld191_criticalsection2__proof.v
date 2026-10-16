From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.stdlib Require Import mutex.
From mizzle.dataracebench.cases Require Import drbheld191_criticalsection2__code.

Section proof.
Context `{seqlogGS Σ}.

(** The two threads guard [size] with *different* mutexes [a] and [b], so the
    locks exclude nothing. Thread 1 takes [a], reads [size] twice and parks at
    the raw write [size <- 1]; thread 2 takes [b] and parks at the raw read
    [!size]. Same address, one write, both non-atomic. *)
Lemma drbheld191_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drbheld191_criticalsection2٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drbheld191_criticalsection2٠main.
g_call "Hrun". g_let "Hrun".
g_alloc "Hrun" "Hs". g_let "Hrun".
g_focus (mutex٠create ()%E) "Hrun".
iApply (focused_mutex_create with "Hrun"). iIntros (la) "Ha Hrun". iSimpl in "Hrun".
g_let "Hrun".
g_focus (mutex٠create ()%E) "Hrun".
iApply (focused_mutex_create with "Hrun"). iIntros (lb) "Hb Hrun". iSimpl in "Hrun".
g_let "Hrun".
g_rec "Hrun". g_rec "Hrun".
g_focus (drb٠par _ _) "Hrun".
iApply (drb_par_spec with "Hrun").
iIntros (q ksq ksp) "Hq Hp _".
(* thread q: lock a, test size < 10, park at the write to size *)
g_call "Hq". g_alloc "Hq" "Hr1". g_let "Hq". g_while "Hq". g_if_true "Hq".
g_focus (mutex٠lock _) "Hq".
iApply (focused_mutex_lock with "Ha Hq"). iIntros "Ha Hq". iSimpl in "Hq".
g_seq "Hq". g_get_field "Hq" "Hs". g_args "Hq". g_if_true "Hq".
g_get_field "Hq" "Hs". g_args "Hq".
(* thread p: lock b, park at the read of size *)
g_call "Hp". g_alloc "Hp" "Hr2". g_let "Hp". g_while "Hp". g_if_true "Hp".
g_focus (mutex٠lock _) "Hp".
iApply (focused_mutex_lock with "Hb Hp"). iIntros "Hb Hp". iSimpl in "Hp".
g_seq "Hp".
iApply (goal_race_close q p with "Hrem Hq Hp"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drbheld191_criticalsection2_racy v0 :
  exists c, rtc silent_step ([(drbheld191_criticalsection2٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drbheld191_racy_goal. Qed.
