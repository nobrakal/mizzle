From stdpp Require Import relations.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi.lib Require Import fixpoint_mono.
From iris.algebra Require Import coPset.

From mizzle.lang Require Export semantics.

From mizzle.logic Require Import interp goal wf_access.

Section adequacy_pre.

Context `{seqlogGS Σ}.

Local Instance sound_Φ_ne (P : iProp Σ) :
  NonExpansive (λ E : coPsetO, (∀ c ts, interp c.1 c.2 ts ={E, ⊤}=∗
      ∃ c' κ, ⌜traced_steps c κ c'⌝ ∗ interp c'.1 c'.2 (ts ++ κ) ∗ ▷ P)%I).
Proof. intros n E1 E2 HE. assert (E1 = E2) as -> by (apply leibniz_equiv, HE). done. Qed.

(** Trace-aware soundness: extracting the [goal] fixpoint yields a full
    reduction together with the observation trace [κ] it produces. The
    trace is also recorded in [interp]'s ghost state: the final
    interpretation holds the accumulated trace [ts ++ κ]. *)
Lemma goal_sound_tr c ts P :
  interp (fst c) (snd c) ts ∗ γinit ↪PROP□ P ∗ goal ⊤ ={⊤}=∗
  ∃ c' κ, ⌜traced_steps c κ c'⌝ ∗ interp (fst c') (snd c') (ts ++ κ) ∗ ▷ P.
Proof.
  iIntros "(Hi & #Hsaved & Hwp)".
  iRevert (c ts) "Hi".
  iApply (least_fixpoint_iter goal_pre
    (λ E, ∀ c ts, interp c.1 c.2 ts ={E, ⊤}=∗
      ∃ c' κ, ⌜traced_steps c κ c'⌝ ∗ interp c'.1 c'.2 (ts ++ κ) ∗ ▷ P)%I
    with "[] Hwp").
  iModIntro. iIntros (E) "[Hstep|(%E' & Hshift)]".
  - iIntros (c0 ts) "Hi".
    iMod ("Hstep" $! c0.1 c0.2 ts with "Hi")
      as "[(Hi & Hrem & Hcl)|(%es' & %σ' & %κ & %Hstep & Hi & IH)]".
    + iMod "Hcl" as "_".
      iDestruct "Hrem" as (Q) "[#Hsavedrem HQ]".
      iSpecialize ("HQ" with "[//]").
      iDestruct (saved_prop_agree with "Hsaved Hsavedrem") as "#Hr".
      iModIntro. iExists c0, []. rewrite app_nil_r. iFrame.
      iSplitR; first (iPureIntro; constructor).
      iNext. iRewrite "Hr". iFrame.
    + iMod ("IH" $! (es', σ') (ts ++ κ) with "Hi") as (c'' κs) "(%Hts & Hi & HP)".
      iModIntro. iExists c'', (κ ++ κs). rewrite -app_assoc. iFrame. iPureIntro.
      by eapply traced_steps_l.
  - iIntros (c0 ts) "Hi". iMod "Hshift". iApply ("Hshift" $! c0 ts with "Hi").
Qed.

Lemma goal_sound c ts P :
  interp (fst c) (snd c) ts ∗ γinit ↪PROP□ P ∗ goal ⊤ ={⊤}=∗
  ∃ c' ts', ⌜rtc silent_step c c'⌝ ∗ interp (fst c') (snd c') ts' ∗ ▷ P.
Proof.
  iIntros "H". iMod (goal_sound_tr with "H") as (c' κ) "(%Hts & Hi & HP)".
  iModIntro. iExists c', (ts ++ κ). iFrame. iPureIntro.
  by eapply traced_steps_rtc_silent_step.
Qed.

End adequacy_pre.

Import Initialization.

(** Trace-aware adequacy: the extracted reduction is reported together with
    the observation trace [κ] it produces, and the closing predicate [Q']
    may talk about that trace. The final [interp es σ κ] is exposed to the
    closing arm, so a trace fragment held in [Q] can be related to [κ]. *)
Lemma goal_adequacy_open_tr Q `{seqlogPreG Σ} e v0
    (Q' : list observation → list expr * state → Prop) :
  (∀ `{hG:!seqlogGS Σ},
     remaining (Q Σ hG) ∗ running 0 e ∗ local 0 v0 ⊢
     goal ⊤ ∗ (∀ es σ ts, (interp es σ ts ∗ Q Σ hG) -∗ ⌜Q' ts (es,σ)⌝)) ->
  exists c κ, traced_steps ([e], initial_state v0) κ c /\ Q' κ c.
Proof.
  intros Hwp.
  eapply pure_soundness.
  apply (@step_fupdN_soundness_lc Σ _ _ _ 1 0).

  iIntros. simpl.
  iMod (seqlog_init e (initial_state v0) v0 eq_refl)
    as "[%hi (%Xeq&Hrun&Hloc&_&Hi)]".
  iMod ("Hi" $! (Q _ hi)) as "(Hi&#HP)".

  iDestruct (Hwp with "[Hrun Hloc]") as "(Hgoal&Hend)".
  { iFrame. iExists _. iFrame "HP". auto. }

  rewrite -Xeq.

  iMod (goal_sound_tr (_,_) [] (Q _ hi) with "[-Hend]") as (c κ) "(%&Hi&HQ)".
  { iFrame "∗#". }

  iApply @fupd_mask_intro. done. iIntros.
  do 3 iModIntro.
  iDestruct ("Hend" with "[$]") as %Hpure.
  iPureIntro. exists c, ([] ++ κ). split_and !; try done.
  destruct c; done.
  Unshelve. exact _.
Qed.

Lemma goal_adequacy_tr Q e v0
    (Q' : list observation → list expr * state → Prop) :
  (∀ `{hG:!seqlogGS Σ},
     remaining (Q Σ hG) ∗ running 0 e ∗ local 0 v0 ⊢
     goal ⊤ ∗ (∀ es σ ts, (interp es σ ts ∗ Q Σ hG) -∗ ⌜Q' ts (es,σ)⌝)) ->
  exists c κ, traced_steps ([e], initial_state v0) κ c /\ Q' κ c.
Proof.
  intros Hwp.
  eapply goal_adequacy_open_tr; eauto with typeclass_instances.
Qed.

(** Trace-aware adequacy: the initial trace is handed to the driver as the
    empty-trace fragment [trace_model []], so the program need not allocate
    anything to start emitting. *)
Lemma goal_adequacy_trace_open_tr Q `{seqlogPreG Σ} e v0
    (Q' : list observation → list expr * state → Prop) :
  (∀ `{hG:!seqlogGS Σ},
     remaining (Q Σ hG) ∗ running 0 e ∗ local 0 v0 ∗
     trace_model [] ⊢
     goal ⊤ ∗ (∀ es σ ts, (interp es σ ts ∗ Q Σ hG) -∗ ⌜Q' ts (es,σ)⌝)) ->
  exists c κ, traced_steps ([e], initial_state v0) κ c /\ Q' κ c.
Proof.
  intros Hwp.
  eapply pure_soundness.
  apply (@step_fupdN_soundness_lc Σ _ _ _ 1 0).

  iIntros. simpl.
  iMod (seqlog_init e (initial_state v0) v0 eq_refl)
    as "[%hi (%Xeq&Hrun&Hloc&Htm&Hi)]".
  iMod ("Hi" $! (Q _ hi)) as "(Hi&#HP)".

  iDestruct (Hwp with "[Hrun Hloc Htm]") as "(Hgoal&Hend)".
  { iFrame. iExists _. iFrame "HP". auto. }

  rewrite -Xeq.

  iMod (goal_sound_tr (_,_) [] (Q _ hi) with "[-Hend]") as (c κ) "(%&Hi&HQ)".
  { iFrame "∗#". }

  iApply @fupd_mask_intro. done. iIntros.
  do 3 iModIntro.
  iDestruct ("Hend" with "[$]") as %Hpure.
  iPureIntro. exists c, ([] ++ κ). split_and !; try done.
  destruct c; done.
  Unshelve. exact _.
Qed.

Lemma goal_adequacy_trace_tr Q e v0
    (Q' : list observation → list expr * state → Prop) :
  (∀ `{hG:!seqlogGS Σ},
     remaining (Q Σ hG) ∗ running 0 e ∗ local 0 v0 ∗
     trace_model [] ⊢
     goal ⊤ ∗ (∀ es σ ts, (interp es σ ts ∗ Q Σ hG) -∗ ⌜Q' ts (es,σ)⌝)) ->
  exists c κ, traced_steps ([e], initial_state v0) κ c /\ Q' κ c.
Proof.
  intros Hwp.
  eapply goal_adequacy_trace_open_tr; eauto with typeclass_instances.
Qed.

Lemma goal_adequacy_open Q `{seqlogPreG Σ} e v0 Q' :
  (∀ `{hG:!seqlogGS Σ},
     remaining (Q Σ hG) ∗ running 0 e ∗ local 0 v0 ⊢
     goal ⊤ ∗ (∀ es σ ts, (interp es σ ts ∗ Q Σ hG) -∗ ⌜Q' (es,σ)⌝)) ->
  exists c, rtc silent_step ([e], initial_state v0) c /\ Q' c.
Proof.
  intros Hwp.
  destruct (goal_adequacy_open_tr Q e v0 (λ _ c, Q' c) Hwp)
    as (c & κ & Hts & HQ).
  exists c. split; [by eapply traced_steps_rtc_silent_step|done].
Qed.

Lemma goal_adequacy Q e v0 Q' :
  (∀ `{hG:!seqlogGS Σ},
     remaining (Q Σ hG) ∗ running 0 e ∗ local 0 v0 ⊢
     goal ⊤ ∗ (∀ es σ ts, (interp es σ ts ∗ Q Σ hG) -∗ ⌜Q' (es,σ)⌝)) ->
  exists c, rtc silent_step ([e], initial_state v0) c /\ Q' c.
Proof.
  intros Hwp.
  eapply goal_adequacy_open; eauto with typeclass_instances.
Qed.
