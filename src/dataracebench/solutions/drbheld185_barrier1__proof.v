From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.stdlib Require Import mutex.
From mizzle.stdlib Require Import assert.
From mizzle.dataracebench.cases Require Import drbheld185_barrier1__code.

Section proof.
Context `{seqlogGS Σ}.

(** [raise c f ;; lower c f] with the mutex and flag both free: the thread
    raises its own flag and immediately consumes it in [lower], so it never
    waits for the other thread. *)
Lemma raise_lower_spec p ks (lm lf : location) :
  lm ↦∗ [false%V] -∗ lf ↦∗ [false%V] -∗
  focused p ks (drbheld185_barrier1٠raise #lm #lf ;; drbheld185_barrier1٠lower #lm #lf)%E -∗
  (lm ↦∗ [false%V] -∗ lf ↦∗ [false%V] -∗ focused p ks (Val ValUnit) -∗ goal ⊤) -∗ goal ⊤.
Proof.
iIntros "Hm Hf Hq HK".
rewrite /drbheld185_barrier1٠raise /drbheld185_barrier1٠lower.
g_call2 "Hq".
g_focus (mutex٠lock _) "Hq". iApply (focused_mutex_lock with "Hm Hq"). iIntros "Hm Hq". iSimpl in "Hq".
g_seq "Hq". g_get_field "Hq" "Hf". g_unop "Hq".
g_focus (assert _) "Hq". iApply (goal_assert with "Hq"). iIntros "Hq". iSimpl in "Hq".
g_seq "Hq". g_set_field "Hq" "Hf". g_seq "Hq".
g_focus (mutex٠unlock _) "Hq". iApply (focused_mutex_unlock with "Hm Hq"). iIntros "Hm Hq". iSimpl in "Hq".
g_seq "Hq". g_call2 "Hq". g_alloc "Hq" "Hfin". g_let "Hq".
g_while "Hq". g_get_field "Hq" "Hfin". g_unop "Hq". g_if_true "Hq".
g_focus (mutex٠lock _) "Hq". iApply (focused_mutex_lock with "Hm Hq"). iIntros "Hm Hq". iSimpl in "Hq".
g_seq "Hq". g_get_field "Hq" "Hf". g_if_true "Hq". g_set_field "Hq" "Hf". g_seq "Hq".
g_set_field "Hq" "Hfin". g_seq "Hq".
g_focus (mutex٠unlock _) "Hq". iApply (focused_mutex_unlock with "Hm Hq"). iIntros "Hm Hq". iSimpl in "Hq".
g_seq "Hq". g_while "Hq". g_get_field "Hq" "Hfin". g_unop "Hq". g_if_false "Hq".
iSimpl in "Hq". iApply ("HK" with "Hm [Hf] Hq"). done.
Qed.

Lemma mybarrier0_spec p ks (lm l0 l1 : location) :
  lm ↦∗ [false%V] -∗ l0 ↦∗ [false%V] -∗
  focused p ks (drbheld185_barrier1٠mybarrier #lm #l0 #l1 #0)%E -∗
  (lm ↦∗ [false%V] -∗ l0 ↦∗ [false%V] -∗ focused p ks (Val ValUnit) -∗ goal ⊤) -∗ goal ⊤.
Proof.
iIntros "Hm Hf Hq HK". rewrite {1}/drbheld185_barrier1٠mybarrier. g_call4 "Hq".
g_focus (structural_equality.structeq _ _) "Hq".
iApply (focused_structeq_int with "Hq"). iIntros "Hq". iSimpl in "Hq". g_if_true "Hq".
iApply (raise_lower_spec with "Hm Hf Hq HK").
Qed.

Lemma mybarrier1_spec p ks (lm l0 l1 : location) :
  lm ↦∗ [false%V] -∗ l1 ↦∗ [false%V] -∗
  focused p ks (drbheld185_barrier1٠mybarrier #lm #l0 #l1 #1)%E -∗
  (lm ↦∗ [false%V] -∗ l1 ↦∗ [false%V] -∗ focused p ks (Val ValUnit) -∗ goal ⊤) -∗ goal ⊤.
Proof.
iIntros "Hm Hf Hq HK". rewrite {1}/drbheld185_barrier1٠mybarrier. g_call4 "Hq".
g_focus (structural_equality.structeq _ _) "Hq".
iApply (focused_structeq_int with "Hq"). iIntros "Hq". iSimpl in "Hq". g_if_false "Hq".
g_focus (structural_equality.structeq _ _) "Hq".
iApply (focused_structeq_int with "Hq"). iIntros "Hq". iSimpl in "Hq". g_if_true "Hq".
iApply (raise_lower_spec with "Hm Hf Hq HK").
Qed.

(** The "barrier" never synchronizes: each thread only waits on its own flag.
    Thread 0 passes one barrier and parks at the non-atomic [x <- 0]; thread 1
    passes three barriers and parks at the non-atomic [x <- 1]. *)
Lemma drbheld185_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drbheld185_barrier1٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drbheld185_barrier1٠main.
g_call "Hrun". g_let "Hrun".
g_alloc "Hrun" "Hx". g_let "Hrun".
g_alloc "Hrun" "Hf0". g_let "Hrun".
g_alloc "Hrun" "Hf1". g_let "Hrun".
g_focus (mutex٠create _) "Hrun".
iApply (focused_mutex_create with "Hrun"). iIntros (lm) "Hm Hrun". iSimpl in "Hrun".
g_let "Hrun". g_rec "Hrun". g_let "Hrun". g_rec "Hrun". g_rec "Hrun".
iApply (drb_par_spec with "Hrun"). iIntros (q ksq ksp) "Hq Hp _".
(* thread q (tid 0): one barrier, park at x <- 0 *)
g_call "Hq". g_call "Hq". g_for "Hq". g_rec "Hq". g_call "Hq".
g_focus (drbheld185_barrier1٠mybarrier _ _ _ _)%E "Hq".
iApply (mybarrier0_spec with "Hm Hf0 Hq"). iIntros "Hm Hf0 Hq". iSimpl in "Hq".
g_seq "Hq".
g_focus (structural_equality.structeq _ _) "Hq".
iApply (focused_structeq_int with "Hq"). iIntros "Hq". iSimpl in "Hq". g_if_true "Hq".
(* thread p (tid 1): three barriers, park at x <- 1 *)
g_call "Hp". g_call "Hp". g_for "Hp". g_rec "Hp". g_call "Hp".
g_focus (drbheld185_barrier1٠mybarrier _ _ _ _)%E "Hp".
iApply (mybarrier1_spec with "Hm Hf1 Hp"). iIntros "Hm Hf1 Hp". iSimpl in "Hp".
g_seq "Hp".
g_focus (structural_equality.structeq _ _) "Hp".
iApply (focused_structeq_int with "Hp"). iIntros "Hp". iSimpl in "Hp". g_if_false "Hp". g_seq "Hp".
g_focus (drbheld185_barrier1٠mybarrier _ _ _ _)%E "Hp".
iApply (mybarrier1_spec with "Hm Hf1 Hp"). iIntros "Hm Hf1 Hp". iSimpl in "Hp".
g_seq "Hp".
g_focus (drbheld185_barrier1٠mybarrier _ _ _ _)%E "Hp".
iApply (mybarrier1_spec with "Hm Hf1 Hp"). iIntros "Hm Hf1 Hp". iSimpl in "Hp".
g_seq "Hp".
g_focus (structural_equality.structeq _ _) "Hp".
iApply (focused_structeq_int with "Hp"). iIntros "Hp". iSimpl in "Hp". g_if_true "Hp".
iApply (goal_race_close q p with "Hrem Hq Hp"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drbheld185_barrier1_racy v0 :
  exists c, rtc silent_step ([(drbheld185_barrier1٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drbheld185_racy_goal. Qed.
