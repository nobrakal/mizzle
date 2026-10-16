
From mizzle.dataracebench.support Require Import drb_prelude.
From mizzle.stdlib Require Import array.
From mizzle.dataracebench.cases Require Import drbheld195_diffusion1__code.

Section proof.
Context `{seqlogGS Σ}.

Lemma zcells_uncons l (base : Z) (n : nat) :
  zcells l base (S n) -∗ (∃ z:Z, (l +ₗ base) ↦ ValInt z) ∗ zcells l (base + 1) n.
Proof.
iIntros "Hz".
iDestruct (zcells_split l base (S n) 1 with "Hz") as "[H1 H2]"; first lia.
iDestruct (zcells_acc l base 1 base with "H1") as "[Hc _]"; first lia.
iFrame. replace (S n - 1)%nat with n by lia. done.
Qed.

(** [u1 := a], [u2 := b]. Time step 0 runs [parallel_for] fully (reads [a],
    writes [b]: no race), then [u1 <- !u2] makes [u1] and [u2] both point to
    [b]. In time step 1, thread k=0 writes [b[1]] while thread k=1 reads
    [b[1]] (as [u1[i-1]] with i=2): same address, one write, non-atomic. *)
Lemma racy_goal p ks :
  remaining is_racy' -∗
  focused p ks (App (Val drbheld195_diffusion1٠main) (Val ValUnit)) -∗
  goal ⊤.
Proof.
iIntros "Hrem Hrun".
rewrite /drbheld195_diffusion1٠main.
g_call "Hrun". g_let "Hrun". g_let "Hrun". g_let "Hrun".
g_array_make "Hrun" a "Hhdr_a" "Hcells_a".
g_alloc "Hrun" "Hu1".
g_let "Hrun".
g_array_make "Hrun" b "Hhdr_b" "Hcells_b".
g_alloc "Hrun" "Hu2".
g_let "Hrun".
iDestruct (zcells_of_replicate with "Hcells_a") as "Hza".
iDestruct (zcells_of_replicate with "Hcells_b") as "Hzb".
g_args "Hrun".
g_focus (For _ _ _) "Hrun".
iApply (focused_loop_inv ⊤ p (fun _ => zcells a 0 (Z.to_nat 10) ∗ zcells b 0 (Z.to_nat 10) ∗ l ↦∗ [ValLoc a] ∗ l0 ↦∗ [ValLoc b])%I 1 9 _ _
          with "[] [Hza Hzb Hu1 Hu2] Hrun"); first lia.
{ iModIntro. iIntros (i ks' Hi) "(Hza & Hzb & Hu1 & Hu2) Hf Hcont".
  g_rec "Hf". g_call "Hf".
  iDestruct (zcells_acc a 0 (Z.to_nat 10) i with "Hza") as "[Hc Hza]"; first lia.
  iDestruct "Hc" as (z) "Hc".
  iDestruct (zcells_acc b 0 (Z.to_nat 10) i with "Hzb") as "[Hd Hzb]"; first lia.
  iDestruct "Hd" as (z') "Hd".
  g_get_field "Hf" "Hu1".
  g_array_set "Hf" "Hhdr_a" "Hc".
  g_seq "Hf".
  g_get_field "Hf" "Hu1".
  g_array_get "Hf" "Hhdr_a" "Hc".
  g_get_field "Hf" "Hu2".
  g_array_set "Hf" "Hhdr_b" "Hd".
  iApply ("Hcont" with "[-Hf] Hf"). iFrame. iSplitL "Hza Hc"; [iApply "Hza"|iApply "Hzb"]; by iFrame. }
{ iFrame. }
iIntros "(Hza & Hzb & Hu1 & Hu2) Hrun". iEval (simpl) in "Hrun".
g_let "Hrun".
iDestruct (zcells_acc a 0 (Z.to_nat 10) 0 with "Hza") as "[Hc Hza]"; first lia.
iDestruct "Hc" as (?) "Hc".
g_get_field "Hrun" "Hu1". g_array_set "Hrun" "Hhdr_a" "Hc". g_seq "Hrun".
iDestruct ("Hza" with "[Hc]") as "Hza"; first by iFrame.
g_args "Hrun".
iDestruct (zcells_acc a 0 (Z.to_nat 10) 9 with "Hza") as "[Hc Hza]"; first lia.
iDestruct "Hc" as (?) "Hc".
g_get_field "Hrun" "Hu1". g_array_set "Hrun" "Hhdr_a" "Hc". g_seq "Hrun".
iDestruct ("Hza" with "[Hc]") as "Hza"; first by iFrame.
iDestruct (zcells_acc b 0 (Z.to_nat 10) 0 with "Hzb") as "[Hc Hzb]"; first lia.
iDestruct "Hc" as (?) "Hc".
g_get_field "Hrun" "Hu2". g_array_set "Hrun" "Hhdr_b" "Hc". g_seq "Hrun".
iDestruct ("Hzb" with "[Hc]") as "Hzb"; first by iFrame.
g_args "Hrun".
iDestruct (zcells_acc b 0 (Z.to_nat 10) 9 with "Hzb") as "[Hc Hzb]"; first lia.
iDestruct "Hc" as (?) "Hc".
g_get_field "Hrun" "Hu2". g_array_set "Hrun" "Hhdr_b" "Hc". g_seq "Hrun".
iDestruct ("Hzb" with "[Hc]") as "Hzb"; first by iFrame.
(* time step 0 *)
g_for "Hrun".
g_rec "Hrun". g_call "Hrun". g_rec "Hrun". g_args "Hrun".
iEval (rewrite (val_int_of_nat 8 ltac:(lia))) in "Hrun".
g_focus (App (App _ _) _) "Hrun".
iApply (drb٠parallel_for_spec with "Hrun").
iIntros (qs kss Hlen Hlen') "Hthreads Hjoin".
do 9 (destruct qs as [|? qs]; try (simpl in Hlen; lia)).
do 9 (destruct kss as [|? kss]; try (simpl in Hlen'; lia)).
iDestruct "Hthreads" as "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & _)".
replace (Z.to_nat 10) with 10%nat by lia.
iDestruct (zcells_uncons with "Hza") as "[[% Ha0] Hza]".
iDestruct (zcells_uncons with "Hza") as "[[% Ha1] Hza]".
iDestruct (zcells_uncons with "Hza") as "[[% Ha2] Hza]".
iDestruct (zcells_uncons with "Hza") as "[[% Ha3] Hza]".
iDestruct (zcells_uncons with "Hza") as "[[% Ha4] Hza]".
iDestruct (zcells_uncons with "Hza") as "[[% Ha5] Hza]".
iDestruct (zcells_uncons with "Hza") as "[[% Ha6] Hza]".
iDestruct (zcells_uncons with "Hza") as "[[% Ha7] Hza]".
iDestruct (zcells_uncons with "Hza") as "[[% Ha8] Hza]".
iDestruct (zcells_uncons with "Hza") as "[[% Ha9] Hza]".
iDestruct (zcells_uncons with "Hzb") as "[[% Hb0] Hzb]".
iDestruct (zcells_uncons with "Hzb") as "[[% Hb1] Hzb]".
iDestruct (zcells_uncons with "Hzb") as "[[% Hb2] Hzb]".
iDestruct (zcells_uncons with "Hzb") as "[[% Hb3] Hzb]".
iDestruct (zcells_uncons with "Hzb") as "[[% Hb4] Hzb]".
iDestruct (zcells_uncons with "Hzb") as "[[% Hb5] Hzb]".
iDestruct (zcells_uncons with "Hzb") as "[[% Hb6] Hzb]".
iDestruct (zcells_uncons with "Hzb") as "[[% Hb7] Hzb]".
iDestruct (zcells_uncons with "Hzb") as "[[% Hb8] Hzb]".
iDestruct (zcells_uncons with "Hzb") as "[[% Hb9] Hzb]".
g_call "H0". g_args "H0". g_let "H0".
g_get_field "H0" "Hu1". g_array_get "H0" "Hhdr_a" "Ha1".
g_args "H0". g_get_field "H0" "Hu1". g_array_get "H0" "Hhdr_a" "Ha2".
g_args "H0". g_get_field "H0" "Hu1". g_array_get "H0" "Hhdr_a" "Ha0".
g_args "H0". g_get_field "H0" "Hu1". g_array_get "H0" "Hhdr_a" "Ha1".
g_args "H0". g_get_field "H0" "Hu2". g_array_set "H0" "Hhdr_b" "Hb1".
g_call "H1". g_args "H1". g_let "H1".
g_get_field "H1" "Hu1". g_array_get "H1" "Hhdr_a" "Ha2".
g_args "H1". g_get_field "H1" "Hu1". g_array_get "H1" "Hhdr_a" "Ha3".
g_args "H1". g_get_field "H1" "Hu1". g_array_get "H1" "Hhdr_a" "Ha1".
g_args "H1". g_get_field "H1" "Hu1". g_array_get "H1" "Hhdr_a" "Ha2".
g_args "H1". g_get_field "H1" "Hu2". g_array_set "H1" "Hhdr_b" "Hb2".
g_call "H2". g_args "H2". g_let "H2".
g_get_field "H2" "Hu1". g_array_get "H2" "Hhdr_a" "Ha3".
g_args "H2". g_get_field "H2" "Hu1". g_array_get "H2" "Hhdr_a" "Ha4".
g_args "H2". g_get_field "H2" "Hu1". g_array_get "H2" "Hhdr_a" "Ha2".
g_args "H2". g_get_field "H2" "Hu1". g_array_get "H2" "Hhdr_a" "Ha3".
g_args "H2". g_get_field "H2" "Hu2". g_array_set "H2" "Hhdr_b" "Hb3".
g_call "H3". g_args "H3". g_let "H3".
g_get_field "H3" "Hu1". g_array_get "H3" "Hhdr_a" "Ha4".
g_args "H3". g_get_field "H3" "Hu1". g_array_get "H3" "Hhdr_a" "Ha5".
g_args "H3". g_get_field "H3" "Hu1". g_array_get "H3" "Hhdr_a" "Ha3".
g_args "H3". g_get_field "H3" "Hu1". g_array_get "H3" "Hhdr_a" "Ha4".
g_args "H3". g_get_field "H3" "Hu2". g_array_set "H3" "Hhdr_b" "Hb4".
g_call "H4". g_args "H4". g_let "H4".
g_get_field "H4" "Hu1". g_array_get "H4" "Hhdr_a" "Ha5".
g_args "H4". g_get_field "H4" "Hu1". g_array_get "H4" "Hhdr_a" "Ha6".
g_args "H4". g_get_field "H4" "Hu1". g_array_get "H4" "Hhdr_a" "Ha4".
g_args "H4". g_get_field "H4" "Hu1". g_array_get "H4" "Hhdr_a" "Ha5".
g_args "H4". g_get_field "H4" "Hu2". g_array_set "H4" "Hhdr_b" "Hb5".
g_call "H5". g_args "H5". g_let "H5".
g_get_field "H5" "Hu1". g_array_get "H5" "Hhdr_a" "Ha6".
g_args "H5". g_get_field "H5" "Hu1". g_array_get "H5" "Hhdr_a" "Ha7".
g_args "H5". g_get_field "H5" "Hu1". g_array_get "H5" "Hhdr_a" "Ha5".
g_args "H5". g_get_field "H5" "Hu1". g_array_get "H5" "Hhdr_a" "Ha6".
g_args "H5". g_get_field "H5" "Hu2". g_array_set "H5" "Hhdr_b" "Hb6".
g_call "H6". g_args "H6". g_let "H6".
g_get_field "H6" "Hu1". g_array_get "H6" "Hhdr_a" "Ha7".
g_args "H6". g_get_field "H6" "Hu1". g_array_get "H6" "Hhdr_a" "Ha8".
g_args "H6". g_get_field "H6" "Hu1". g_array_get "H6" "Hhdr_a" "Ha6".
g_args "H6". g_get_field "H6" "Hu1". g_array_get "H6" "Hhdr_a" "Ha7".
g_args "H6". g_get_field "H6" "Hu2". g_array_set "H6" "Hhdr_b" "Hb7".
g_call "H7". g_args "H7". g_let "H7".
g_get_field "H7" "Hu1". g_array_get "H7" "Hhdr_a" "Ha8".
g_args "H7". g_get_field "H7" "Hu1". g_array_get "H7" "Hhdr_a" "Ha9".
g_args "H7". g_get_field "H7" "Hu1". g_array_get "H7" "Hhdr_a" "Ha7".
g_args "H7". g_get_field "H7" "Hu1". g_array_get "H7" "Hhdr_a" "Ha8".
g_args "H7". g_get_field "H7" "Hu2". g_array_set "H7" "Hhdr_b" "Hb8".
iApply ("Hjoin" with "[H0 H1 H2 H3 H4 H5 H6 H7]"); first by iFrame.
iIntros "Hrun". iEval (simpl) in "Hrun".
(* [u1 <- !u2]: now both refs point to [b] *)
g_seq "Hrun". g_get_field "Hrun" "Hu1". g_let "Hrun".
g_get_field "Hrun" "Hu2". g_set_field "Hrun" "Hu1".
g_seq "Hrun".
(* time step 1 *)
g_for "Hrun".
g_rec "Hrun". g_call "Hrun". g_rec "Hrun". g_args "Hrun".
iEval (simpl) in "Hu1".
g_focus (App (App _ _) _) "Hrun".
iApply (drb٠parallel_for_spec _ _ _ 8%nat with "Hrun").
iIntros (qs' kss' Hl1 Hl2) "Hthreads _".
destruct qs' as [|q0 [|q1 qs']]; try (simpl in Hl1; lia).
destruct kss' as [|ks0 [|ks1 kss']]; try (simpl in Hl2; lia).
iDestruct "Hthreads" as "(Hq0 & Hq1 & _)".
(* thread k=0: park at the raw SetField of b[1] *)
g_call "Hq0". g_args "Hq0". g_let "Hq0".
g_get_field "Hq0" "Hu1". g_array_get "Hq0" "Hhdr_b" "Hb1".
g_args "Hq0". g_get_field "Hq0" "Hu1". g_array_get "Hq0" "Hhdr_b" "Hb2".
g_args "Hq0". g_get_field "Hq0" "Hu1". g_array_get "Hq0" "Hhdr_b" "Hb0".
g_args "Hq0". g_get_field "Hq0" "Hu1". g_array_get "Hq0" "Hhdr_b" "Hb1".
g_args "Hq0". g_get_field "Hq0" "Hu2". g_array_set_to_set_field "Hq0" "Hhdr_b".
(* thread k=1: park at the raw GetField of b[1] *)
g_call "Hq1". g_args "Hq1". g_let "Hq1".
g_get_field "Hq1" "Hu1". g_array_get "Hq1" "Hhdr_b" "Hb2".
g_args "Hq1". g_get_field "Hq1" "Hu1". g_array_get "Hq1" "Hhdr_b" "Hb3".
g_args "Hq1". g_get_field "Hq1" "Hu1". g_array_get_to_get_field "Hq1" "Hhdr_b".
iApply (goal_race_close q0 q1 with "Hrem Hq0 Hq1"); [solve_access..| solve_races].
Qed.

End proof.

Theorem drbheld195_diffusion1_racy v0 :
  exists c, rtc silent_step ([(drbheld195_diffusion1٠main ())%E], initial_state v0) c /\ racy c.
Proof. apply goal_race_adequacy. intros. apply racy_goal. Qed.
