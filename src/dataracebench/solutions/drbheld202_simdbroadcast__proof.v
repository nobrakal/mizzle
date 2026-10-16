From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.dataracebench.cases Require Import drbheld202_simdbroadcast__code.

Section proof.
Context `{seqlogGS Σ}.

(** [a[i] := i] for [i] in [0,20000), then [parallel_for 20000 (fun i =>
    a[i] := a[i] + a[64])]. Thread 0 reads [a[64]], thread 64 writes [a[64]]:
    same address, one write, both non-atomic. *)
Lemma drbheld202_racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drbheld202_simdbroadcast٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drbheld202_simdbroadcast٠main.
g_call "Hrun". g_let "Hrun".
g_array_make "Hrun" a "Hhdr_a" "Hcells_a".
g_let "Hrun".
iDestruct (zcells_of_replicate with "Hcells_a") as "Hza".
g_focus (For _ _ _) "Hrun".
iApply (focused_loop_inv ⊤ p (fun _ => zcells a 0 (Z.to_nat 20000))%I 0 20000 _ _
          with "[] [Hza] Hrun"); first lia.
{ iModIntro. iIntros (i ks' Hi) "Hz Hf Hcont".
  g_rec "Hf". g_call "Hf".
  iDestruct (zcells_acc a 0 (Z.to_nat 20000) i with "Hz") as "[Hc Hz']"; first lia.
  iDestruct "Hc" as (z) "Hc".
  g_array_set "Hf" "Hhdr_a" "Hc".
  iApply ("Hcont" with "[Hz' Hc] Hf"). iApply "Hz'". by iFrame. }
{ iFrame. }
iIntros "Hza Hrun". iEval (simpl) in "Hrun".
g_seq "Hrun". g_rec "Hrun".
iEval (rewrite (val_int_of_nat 20000 ltac:(lia))) in "Hrun".
iApply (drb٠parallel_for_spec with "Hrun").
iIntros (qs kss Hlen Hlen') "Hthreads _".
destruct qs as [|q0 qs]; [simpl in Hlen; lia|].
destruct kss as [|ks0 kss]; [simpl in Hlen'; lia|].
iDestruct "Hthreads" as "[Hq0 Hth]".
(* skip threads 1..63 *)
do 63 (destruct qs as [|? qs]; [simpl in Hlen; lia|];
       destruct kss as [|? kss]; [simpl in Hlen'; lia|];
       iDestruct "Hth" as "[_ Hth]").
destruct qs as [|q64 qs]; [simpl in Hlen; lia|].
destruct kss as [|ks64 kss]; [simpl in Hlen'; lia|].
iDestruct "Hth" as "[Hq64 _]".
iEval (simpl) in "Hq64".
iDestruct (zcells_acc a 0 (Z.to_nat 20000) 64 with "Hza") as "[Hc _]"; first lia.
iDestruct "Hc" as (z) "Hc".
(* thread 0: park at the raw GetField of a[64] (rightmost operand first) *)
g_call "Hq0". g_args "Hq0".
g_array_get_to_get_field "Hq0" "Hhdr_a".
(* thread 64: read a[64] twice, then park at the raw SetField of a[64] *)
g_call "Hq64". g_args "Hq64".
g_array_get "Hq64" "Hhdr_a" "Hc".
g_args "Hq64".
g_array_get "Hq64" "Hhdr_a" "Hc".
g_args "Hq64".
g_array_set_to_set_field "Hq64" "Hhdr_a".
iApply (goal_race_close q0 q64 with "Hrem Hq0 Hq64"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drbheld202_simdbroadcast_racy v0 :
  exists c, rtc silent_step ([(drbheld202_simdbroadcast٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply drbheld202_racy_goal. Qed.
