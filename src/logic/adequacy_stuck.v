From stdpp Require Import relations.
From iris.proofmode Require Import base proofmode.

From mizzle.lang Require Export semantics.

From mizzle.logic Require Import interp goal adequacy stuck wf_access.

(** Adequacy specialized for stuckness, obtained by instantiating Mizzle's
    generic [goal_adequacy] with the remaining resource [is_stuck'] and the
    operational stuckness predicate [Stuck]. *)
Lemma adequacy_stuck e v0 :
  (∀ `{hG:!seqlogGS Σ},
     remaining is_stuck' ∗ running 0 e ∗ local 0 v0 ⊢ goal ⊤) →
  ∃ es σ', rtc silent_step ([e], initial_state v0) (es, σ') ∧ Stuck es σ'.
Proof.
  intros Hwp.
  destruct (goal_adequacy (λ Σ _, is_stuck') e v0
    (λ c, Stuck c.1 c.2)) as ([es σ'] & Hrtc & Hstuck).
  2:{ exists es, σ'. done. }
  intros Σ hG. iIntros "(Hrem & Hrun & Hlocal)".
  iSplitL.
  { iApply (Hwp with "[$Hrem $Hrun $Hlocal]"). }
  iIntros (es σ' ts) "(Hi & Hstuck)".
  iDestruct "Hstuck" as (p) "Hstuck".
  iDestruct ("Hstuck" with "Hi") as %(e' & Hlk & Hnv & Hir).
  iPureIntro. by exists p, e'.
Qed.
