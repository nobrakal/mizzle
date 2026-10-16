From mizzle.test Require Import test_prelude.

From mizzle.logic Require Import negation.

Definition incr : val :=
  vfun: "r" => "r" <- !"r" + 1.

Section go.
Context `{seqlogGS Σ}.

Lemma goal_incr_neg p ks (l : location) (n : Z) :
  l ↦∗ [ #n ] -∗
  focused p ks (incr #l) -∗
  remaining (focused p ks (Val ValUnit) ∗ neg ((l +ₗ 0) ↦ #n)) -∗
  goal ⊤.
Proof.
  iIntros "Hblk Hp Hrem". rewrite /incr.
  g_call "Hp".
  g_get_field "Hp" "Hblk". g_binop "Hp". g_set_field "Hp" "Hblk".
  iEval (rewrite mz_block_unfold; simpl) in "Hblk".
  iDestruct "Hblk" as (tag) "(_ & Hl & _)".
  iApply (fulfill with "[Hp Hl Hrem]"); last by iModIntro.
  iApply (update_remaining with "[Hp Hl] Hrem").
  iIntros "_". iFrame "Hp". rewrite /neg.
  iApply (bi.impl_intro_r with "Hl").
  iIntros "H".
  iDestruct (mz_pointsto_and_agree with "H") as %Heq.
  exfalso. inversion Heq. lia.
Qed.

End go.

From mizzle.stdlib Require Import rand.

Definition incr_rand : val :=
  vfun: "r" =>
    if: nondet_bool ()
    then "r" <- !"r" + 1
    else ().

Section go2.
Context `{seqlogGS Σ}.

Lemma goal_incr_rand_neg p ks (l : location) (n : Z) :
  (l +ₗ 0) ↦ #n -∗
  focused p ks (incr_rand #l) -∗
  remaining (focused p ks (Val ValUnit) ∗ neg ((l +ₗ 0) ↦ #(n+1))) -∗
  goal ⊤.
Proof.
  iIntros "Hl Hp Hrem". rewrite /incr_rand.
  g_call "Hp".
  g_focus (nondet_bool _) "Hp".
  iApply (goal_rand _ _ _ false with "Hp"). iIntros "Hp". iSimpl in "Hp".
  g_if_false "Hp".
  iApply (fulfill with "[Hp Hl Hrem]"); last by iModIntro.
  iApply (update_remaining with "[Hp Hl] Hrem").
  iIntros "_". iFrame "Hp". rewrite /neg.
  iApply (bi.impl_intro_r with "Hl").
  iIntros "H".
  iDestruct (mz_pointsto_and_agree with "H") as %Heq.
  exfalso. inversion Heq. lia.
Qed.

End go2.
