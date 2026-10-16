From stdpp Require Import relations.
From iris.proofmode Require Import base proofmode.
From iris.bi.lib Require Import fixpoint_mono.

From mizzle.lang Require Export instances.

From mizzle.logic Require Import interp goal wp.

Section wp_run.
Context `{seqlogGS Σ}.

Existing Instance wp_pre_mono'.

(* Lift a primitive step through an evaluation context. *)
Lemma fill_prim_step K p e σ κ e' σ' efs :
  prim_step p e σ κ e' σ' efs →
  prim_step p (fill K e) σ κ (fill K e') σ' efs.
Proof.
  intros [K0 e1 e2 -> -> Hb].
  apply (base_step_fill_prim_step' (K0 ++ K) e1 e2);
    [ rewrite fill_app // | rewrite fill_app // | done].
Qed.

(* The induction predicate quantifies over an arbitrary evaluation context
   [K]: the [running] assertion is about [fill K e], while the WP-driven step
   still concerns the redex [e]. Instantiating [K := []] recovers the plain
   single-thread rule. *)
Definition wp_run_pred (x : wp_arg Σ) : iProp Σ :=
  ∀ K,
  running x.1.1 (fill K x.1.2) -∗
  (∀ v:val, running x.1.1 (fill K (Val v)) ∗ x.2 v -∗ goal ⊤) -∗
  goal ⊤.

Local Instance wp_run_pred_ne : NonExpansive wp_run_pred.
Proof.
  intros n [[a b] c] [[a' b'] d] [[Ha Hb] Hc].
  rewrite /wp_run_pred /=. solve_proper.
Qed.

(* [wp_run_pred] specialized to the single thread [p], with the redex [e] plugged into
   an arbitrary evaluation context [K]. The WP is kept on [e]. *)
Lemma wp_run_at p e Q K :
  wp p e Q -∗
  (running p (fill K e) -∗
  (∀ (v:val), running p (fill K (Val v)) ∗ Q v -∗ goal ⊤) -∗
  goal ⊤).
Proof.
  iIntros "Hwp".
  iAssert (wp_run_pred (p, e, Q)) with "[Hwp]" as "H"; last by iApply ("H" $! K).
  rewrite wp_unseal /wp_def.
  iApply (least_fixpoint_ind wp_pre wp_run_pred with "[] Hwp").
  iModIntro. iIntros ([[p' e'] Q']) "IH". simpl.
  rewrite /wp_run_pred /wp_pre /=.
  destruct (to_val e') as [v|] eqn:He.
  - iIntros (K') "Hrun Hpost".
    apply of_to_val in He. subst e'.
    iApply fupd_goal. iMod "IH" as "HQ". iModIntro.
    iApply "Hpost". iFrame.
  - iIntros (K') "Hrun Hpost".
    iApply goal_unfold. iLeft.
    iIntros (es σ ts) "Hi".
    iDestruct (interp_running_exploit with "Hrun Hi") as %Hlook.
    iMod ("IH" $! K' with "Hrun Hi") as "(%Hred & %Hwf & Hcont)".
    destruct Hred as (κ & enew & σ' & efs & Hstep).
    iMod ("Hcont" $! κ enew σ' efs Hstep) as "(Hi & Hrun & Hwp & _)".
    iModIntro. iRight.
    iExists (<[p':=fill K' enew]> es ++ efs), σ', (κ).
    iFrame "Hi".
    iSplitR.
    { iPureIntro. exists κ, p', (fill K' e'), (fill K' enew), σ', efs.
      split_and!; try done. by apply fill_prim_step. }
    iDestruct "Hwp" as "[Hwp _]".
    iApply ("Hwp" $! K' with "Hrun Hpost").
Qed.

End wp_run.
