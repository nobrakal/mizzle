From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.dataracebench.cases Require Import drbheld124_master__code.

Section proof.
Context `{seqlogGS Σ}.

(** [init := ref 0], then [par (fun () -> !init) (fun () -> init := 10; !init)].
    The first branch reads [init], the second writes it, both non-atomic and
    unsynchronized. Park the reader at its [GetField] and the writer at its
    [SetField]. *)
Lemma drbheld124_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drbheld124_master٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun". rewrite /drbheld124_master٠main.
g_call "Hrun". g_alloc "Hrun" "Hl". g_let "Hrun".
g_rec "Hrun". g_rec "Hrun".
iApply (drb_par_spec with "Hrun").
iIntros (q ksq ksp) "Hq Hp _".
g_call "Hq". g_call "Hp".
iApply (goal_race_close q p with "Hrem Hq Hp"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drbheld124_master_racy v0 :
  exists c, rtc silent_step ([(drbheld124_master٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drbheld124_racy_goal. Qed.
