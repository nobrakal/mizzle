From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.stdlib Require Import mutex.
From mizzle.dataracebench.cases Require Import drbheld189_barrier3__code.

Section proof.
Context `{seqlogGS Σ}.

(** Enter [barrier_wait] for each tid, stated over an abstract [ks] so the
    unfolding does not blow up the large loop context. *)
Lemma wait0 E q ks (l0 l1 : location) :
  focused q ks (drbheld189_barrier3٠barrier_wait #l0 #l1 #0) -∗
  (focused q ks (mutex٠unlock #l0 ;; mutex٠lock #l1 ;; mutex٠lock #l0 ;; mutex٠unlock #l1)%E -∗ goal E) -∗ goal E.
Proof.
iIntros "Hq Hk". rewrite /drbheld189_barrier3٠barrier_wait.
g_call3 "Hq".
g_focus (structural_equality.structeq _ _) "Hq".
iApply (focused_structeq_int with "Hq"). iIntros "Hq". iSimpl in "Hq". g_if_true "Hq".
all: try iApply ("Hk" with "Hq").
Qed.

Lemma wait1 E q ks (l0 l1 : location) :
  focused q ks (drbheld189_barrier3٠barrier_wait #l0 #l1 #1) -∗
  (focused q ks (mutex٠lock #l0 ;; mutex٠unlock #l1 ;; mutex٠unlock #l0 ;; mutex٠lock #l1)%E -∗ goal E) -∗ goal E.
Proof.
iIntros "Hq Hk". rewrite /drbheld189_barrier3٠barrier_wait.
g_call3 "Hq".
g_focus (structural_equality.structeq _ _) "Hq".
iApply (focused_structeq_int with "Hq"). iIntros "Hq". iSimpl in "Hq". g_if_false "Hq".
g_focus (structural_equality.structeq _ _) "Hq".
iApply (focused_structeq_int with "Hq"). iIntros "Hq". iSimpl in "Hq". g_if_true "Hq".
all: try iApply ("Hk" with "Hq").
Qed.

(** The two-lock barrier does not separate phases: thread 1 can run three
    waits while thread 0 is still inside its first one. Schedule:
    T0 unlock l0; T1 waits #1, #2 and half of #3 (lock l0, unlock l1);
    T0 lock l1; T1 unlock l0; T0 lock l0, unlock l1 -> T0 at [x <- 0];
    T1 lock l1 -> T1 at [x <- 1]. Two non-atomic writes to [x]. *)
Lemma drbheld189_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drbheld189_barrier3٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drbheld189_barrier3٠main.
g_call "Hrun". g_let "Hrun". g_alloc "Hrun" "Hx". g_let "Hrun".
g_focus (mutex٠create _) "Hrun".
iApply (focused_mutex_create with "Hrun"). iIntros (l0) "H0 Hrun". iSimpl in "Hrun". g_let "Hrun".
g_focus (mutex٠create _) "Hrun".
iApply (focused_mutex_create with "Hrun"). iIntros (l1) "H1 Hrun". iSimpl in "Hrun". g_let "Hrun".
g_focus (mutex٠create _) "Hrun".
iApply (focused_mutex_create with "Hrun"). iIntros (l2) "H2 Hrun". iSimpl in "Hrun". g_let "Hrun".
g_rec "Hrun". g_rec "Hrun".
(* barrier_start *)
g_focus (drb٠par _ _) "Hrun".
iApply (drb_par_spec with "Hrun"). iIntros (q ksq ksp) "Hq Hp Hk".
g_call "Hq". rewrite /drbheld189_barrier3٠barrier_start. g_call4 "Hq".
g_focus (structural_equality.structeq _ _) "Hq".
iApply (focused_structeq_int with "Hq"). iIntros "Hq". iSimpl in "Hq".
g_if_true "Hq".
g_focus (mutex٠lock _) "Hq". iApply (focused_mutex_lock with "H0 Hq"). iIntros "H0 Hq". iSimpl in "Hq". g_seq "Hq".
iApply (focused_mutex_lock with "H2 Hq"). iIntros "H2 Hq".
g_call "Hp". g_call4 "Hp".
g_focus (structural_equality.structeq _ _) "Hp".
iApply (focused_structeq_int with "Hp"). iIntros "Hp". iSimpl in "Hp". g_if_false "Hp".
g_focus (structural_equality.structeq _ _) "Hp".
iApply (focused_structeq_int with "Hp"). iIntros "Hp". iSimpl in "Hp". g_if_true "Hp".
iApply (focused_mutex_lock with "H1 Hp"). iIntros "H1 Hp".
iApply ("Hk" with "Hq Hp"). iIntros "Hrun". iSimpl in "Hrun". g_seq "Hrun".
(* the body threads *)
g_rec "Hrun". g_let "Hrun". g_rec "Hrun". g_rec "Hrun".
g_focus (drb٠par _ _) "Hrun".
iApply (drb_par_spec with "Hrun"). iIntros (q0 ks0 ks1) "Hq Hp _".
g_call "Hq". g_call "Hq". g_for "Hq".
g_call "Hp". g_call "Hp". g_for "Hp".
g_rec "Hq". g_call "Hq". g_rec "Hp". g_call "Hp".
(* T0: wait #1, unlock l0 *)
g_focus (App (App (App (Val drbheld189_barrier3٠barrier_wait) _) _) _) "Hq".
iApply (wait0 with "Hq"). iIntros "Hq".
g_focus (mutex٠unlock _) "Hq". iApply (focused_mutex_unlock with "H0 Hq"). iIntros "H0 Hq". iSimpl in "Hq". g_seq "Hq".
(* T1: wait #1 *)
g_focus (App (App (App (Val drbheld189_barrier3٠barrier_wait) _) _) _) "Hp".
iApply (wait1 with "Hp"). iIntros "Hp".
g_focus (mutex٠lock _) "Hp". iApply (focused_mutex_lock with "H0 Hp"). iIntros "H0 Hp". iSimpl in "Hp". g_seq "Hp".
g_focus (mutex٠unlock _) "Hp". iApply (focused_mutex_unlock with "H1 Hp"). iIntros "H1 Hp". iSimpl in "Hp". g_seq "Hp".
g_focus (mutex٠unlock _) "Hp". iApply (focused_mutex_unlock with "H0 Hp"). iIntros "H0 Hp". iSimpl in "Hp". g_seq "Hp".
g_focus (mutex٠lock _) "Hp". iApply (focused_mutex_lock with "H1 Hp"). iIntros "H1 Hp". iSimpl in "Hp". g_seq "Hp".
g_focus (structural_equality.structeq _ _) "Hp".
iApply (focused_structeq_int with "Hp"). iIntros "Hp". iSimpl in "Hp". g_if_false "Hp". g_seq "Hp".
(* T1: wait #2 *)
g_focus (App (App (App (Val drbheld189_barrier3٠barrier_wait) _) _) _) "Hp".
iApply (wait1 with "Hp"). iIntros "Hp".
g_focus (mutex٠lock _) "Hp". iApply (focused_mutex_lock with "H0 Hp"). iIntros "H0 Hp". iSimpl in "Hp". g_seq "Hp".
g_focus (mutex٠unlock _) "Hp". iApply (focused_mutex_unlock with "H1 Hp"). iIntros "H1 Hp". iSimpl in "Hp". g_seq "Hp".
g_focus (mutex٠unlock _) "Hp". iApply (focused_mutex_unlock with "H0 Hp"). iIntros "H0 Hp". iSimpl in "Hp". g_seq "Hp".
g_focus (mutex٠lock _) "Hp". iApply (focused_mutex_lock with "H1 Hp"). iIntros "H1 Hp". iSimpl in "Hp". g_seq "Hp".
(* T1: wait #3, interleaved with the rest of T0's wait #1 *)
g_focus (App (App (App (Val drbheld189_barrier3٠barrier_wait) _) _) _) "Hp".
iApply (wait1 with "Hp"). iIntros "Hp".
g_focus (mutex٠lock _) "Hp". iApply (focused_mutex_lock with "H0 Hp"). iIntros "H0 Hp". iSimpl in "Hp". g_seq "Hp".
g_focus (mutex٠unlock _) "Hp". iApply (focused_mutex_unlock with "H1 Hp"). iIntros "H1 Hp". iSimpl in "Hp". g_seq "Hp".
g_focus (mutex٠lock _) "Hq". iApply (focused_mutex_lock with "H1 Hq"). iIntros "H1 Hq". iSimpl in "Hq". g_seq "Hq".
g_focus (mutex٠unlock _) "Hp". iApply (focused_mutex_unlock with "H0 Hp"). iIntros "H0 Hp". iSimpl in "Hp". g_seq "Hp".
g_focus (mutex٠lock _) "Hq". iApply (focused_mutex_lock with "H0 Hq"). iIntros "H0 Hq". iSimpl in "Hq". g_seq "Hq".
g_focus (mutex٠unlock _) "Hq". iApply (focused_mutex_unlock with "H1 Hq"). iIntros "H1 Hq". iSimpl in "Hq". g_seq "Hq".
(* T0 parks at [x <- 0] *)
g_focus (structural_equality.structeq _ _) "Hq".
iApply (focused_structeq_int with "Hq"). iIntros "Hq". iSimpl in "Hq". g_if_true "Hq".
(* T1 finishes wait #3 and parks at [x <- 1] *)
g_focus (mutex٠lock _) "Hp". iApply (focused_mutex_lock with "H1 Hp"). iIntros "H1 Hp". iSimpl in "Hp". g_seq "Hp".
g_focus (structural_equality.structeq _ _) "Hp".
iApply (focused_structeq_int with "Hp"). iIntros "Hp". iSimpl in "Hp". g_if_true "Hp".
iApply (goal_race_close q0 p with "Hrem Hq Hp"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drbheld189_barrier3_racy v0 :
  exists c, rtc silent_step ([(drbheld189_barrier3٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drbheld189_racy_goal. Qed.
