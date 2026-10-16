
From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.dataracebench.cases Require Import drbheld197_diffusion2__code.

Section proof.
Context `{seqlogGS Σ}.

(** [u = [0; 18]], [p = 0] in the first time step. Thread k writes
    [b[u[1-p] + k+1] = b[19+k]] and reads [b[k]], [b[k+1]], [b[k+2]].
    Thread 0 writes [b[19]]; thread 17 reads [b[19]] ([u[p] + 18 + 1]).
    Park thread 17 at the raw [GetField] of [b[19]] and thread 0 at the
    raw [SetField] of [b[19]]. *)
Lemma drbheld197_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drbheld197_diffusion2٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drbheld197_diffusion2٠main.
g_call "Hrun". g_let "Hrun". g_let "Hrun". g_let "Hrun".
g_args "Hrun".
g_array_make "Hrun" b "Hhdr_b" "Hcells_b".
g_let "Hrun".
g_array_make "Hrun" u "Hhdr_u" "Hcells_u".
g_let "Hrun".
iDestruct "Hcells_u" as "[Hu0 [Hu1 _]]".
g_args "Hrun".
g_array_set "Hrun" "Hhdr_u" "Hu1".
g_seq "Hrun".
iDestruct (zcells_of_replicate with "Hcells_b") as "Hzb".
g_args "Hrun".
g_focus (For _ _ _) "Hrun".
iApply (focused_loop_inv ⊤ p (fun _ => u.[0] ↦ 0 ∗ u.[1] ↦ 18 ∗ zcells b 0 (Z.to_nat 40))%I 1 19 _ _
          with "[] [Hu0 Hu1 Hzb] Hrun"); first lia.
{ iModIntro. iIntros (i ks' Hi) "(Hu0 & Hu1 & Hz) Hf Hcont".
  g_rec "Hf". g_call "Hf".
  g_array_get "Hf" "Hhdr_u" "Hu1". g_args "Hf".
  iDestruct (zcells_acc b 0 (Z.to_nat 40) (18 + i) with "Hz") as "[Hc Hz]"; first lia.
  iDestruct "Hc" as (z) "Hc".
  g_array_set "Hf" "Hhdr_b" "Hc". iSpecialize ("Hz" with "[Hc]"); first by iExists _.
  g_seq "Hf".
  g_array_get "Hf" "Hhdr_u" "Hu0". g_args "Hf".
  iDestruct (zcells_acc b 0 (Z.to_nat 40) (0 + i) with "Hz") as "[Hc Hz]"; first lia.
  iDestruct "Hc" as (z') "Hc".
  g_array_set "Hf" "Hhdr_b" "Hc". iSpecialize ("Hz" with "[Hc]"); first by iExists _.
  iApply ("Hcont" with "[$Hu0 $Hu1 $Hz] Hf"). }
{ iFrame. }
iIntros "(Hu0 & Hu1 & Hzb) Hrun". iEval (simpl) in "Hrun".
g_seq "Hrun".
(* the four boundary writes b[0], b[19], b[18], b[37] *)
g_array_get "Hrun" "Hhdr_u" "Hu0"; g_args "Hrun".
iDestruct (zcells_acc b 0 (Z.to_nat 40) 0 with "Hzb") as "[[% Hc] Hzb]"; first lia.
g_array_set "Hrun" "Hhdr_b" "Hc". iSpecialize ("Hzb" with "[Hc]"); first by iExists _. g_seq "Hrun".
g_array_get "Hrun" "Hhdr_u" "Hu0"; g_args "Hrun".
iDestruct (zcells_acc b 0 (Z.to_nat 40) 19 with "Hzb") as "[[% Hc] Hzb]"; first lia.
g_array_set "Hrun" "Hhdr_b" "Hc". iSpecialize ("Hzb" with "[Hc]"); first by iExists _. g_seq "Hrun".
g_array_get "Hrun" "Hhdr_u" "Hu1"; g_args "Hrun".
iDestruct (zcells_acc b 0 (Z.to_nat 40) 18 with "Hzb") as "[[% Hc] Hzb]"; first lia.
g_array_set "Hrun" "Hhdr_b" "Hc". iSpecialize ("Hzb" with "[Hc]"); first by iExists _. g_seq "Hrun".
g_array_get "Hrun" "Hhdr_u" "Hu1"; g_args "Hrun".
iDestruct (zcells_acc b 0 (Z.to_nat 40) 37 with "Hzb") as "[[% Hc] Hzb]"; first lia.
g_array_set "Hrun" "Hhdr_b" "Hc". iSpecialize ("Hzb" with "[Hc]"); first by iExists _. g_seq "Hrun".
g_alloc "Hrun" "Hp". g_let "Hrun".
(* first time step *)
g_for "Hrun".
g_rec "Hrun". g_call "Hrun". g_rec "Hrun". g_args "Hrun".
iEval (rewrite (val_int_of_nat 18 ltac:(lia))) in "Hrun".
g_focus (App (App (Val drb٠parallel_for) _) _) "Hrun".
iApply (drb٠parallel_for_spec with "Hrun").
iIntros (qs kss Hlen Hlen') "Hthreads _".
do 18 (destruct qs as [|? qs]; [simpl in Hlen; lia|]).
do 18 (destruct kss as [|? kss]; [simpl in Hlen'; lia|]).
iDestruct "Hthreads" as "(Hq0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hq17 & _)".
g_call "Hq0". g_args "Hq0". g_let "Hq0".
g_call "Hq17". g_args "Hq17". g_let "Hq17".
(* thread 17: read b[18], then park at the read of b[19] *)
g_get_field "Hq17" "Hp". g_array_get "Hq17" "Hhdr_u" "Hu0". g_args "Hq17".
iDestruct (zcells_acc b 0 (Z.to_nat 40) 18 with "Hzb") as "[[% Hc] Hzb]"; first lia.
g_array_get "Hq17" "Hhdr_b" "Hc". iSpecialize ("Hzb" with "[Hc]"); first by iExists _. g_args "Hq17".
g_get_field "Hq17" "Hp". g_array_get "Hq17" "Hhdr_u" "Hu0". g_args "Hq17".
g_array_get_to_get_field "Hq17" "Hhdr_b".
(* thread 0: read b[1], b[2], b[0], b[1], then park at the write of b[19] *)
g_get_field "Hq0" "Hp". g_array_get "Hq0" "Hhdr_u" "Hu0". g_args "Hq0".
iDestruct (zcells_acc b 0 (Z.to_nat 40) 1 with "Hzb") as "[[% Hc] Hzb]"; first lia.
g_array_get "Hq0" "Hhdr_b" "Hc". iSpecialize ("Hzb" with "[Hc]"); first by iExists _. g_args "Hq0".
g_get_field "Hq0" "Hp". g_array_get "Hq0" "Hhdr_u" "Hu0". g_args "Hq0".
iDestruct (zcells_acc b 0 (Z.to_nat 40) 2 with "Hzb") as "[[% Hc] Hzb]"; first lia.
g_array_get "Hq0" "Hhdr_b" "Hc". iSpecialize ("Hzb" with "[Hc]"); first by iExists _. g_args "Hq0".
g_get_field "Hq0" "Hp". g_array_get "Hq0" "Hhdr_u" "Hu0". g_args "Hq0".
iDestruct (zcells_acc b 0 (Z.to_nat 40) 0 with "Hzb") as "[[% Hc] Hzb]"; first lia.
g_array_get "Hq0" "Hhdr_b" "Hc". iSpecialize ("Hzb" with "[Hc]"); first by iExists _. g_args "Hq0".
g_get_field "Hq0" "Hp". g_array_get "Hq0" "Hhdr_u" "Hu0". g_args "Hq0".
iDestruct (zcells_acc b 0 (Z.to_nat 40) 1 with "Hzb") as "[[% Hc] Hzb]"; first lia.
g_array_get "Hq0" "Hhdr_b" "Hc". iSpecialize ("Hzb" with "[Hc]"); first by iExists _. g_args "Hq0".
g_get_field "Hq0" "Hp". g_args "Hq0". g_array_get "Hq0" "Hhdr_u" "Hu1". g_args "Hq0".
g_array_set_to_set_field "Hq0" "Hhdr_b".
iApply (goal_race_close _ _ with "Hrem Hq0 Hq17"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drbheld197_diffusion2_racy v0 :
  exists c, rtc silent_step ([(drbheld197_diffusion2٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drbheld197_racy_goal. Qed.
