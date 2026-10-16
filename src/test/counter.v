From mizzle.test Require Import test_prelude.

From mizzle.logic Require Import negation.

Definition mk_counter : val :=
  vfun: <> => ref #0.

Definition incr_atomic : val :=
  vrec: "self" "c" =>
    let: "n" := !"c" in
    if: CAS ("c", #0) "n" ("n" + #1) then ()
    else ("self" "c").

Definition get_counter : val :=
  vfun: "c" => !"c".

From iris.base_logic.lib Require Import invariants mono_nat.

Section counter_spec.
Context `{seqlogGS Σ, !mono_natG Σ}.

Definition counterN : namespace := nroot .@ "counter".

Definition counter_inv (γ : gname) (c : location) : iProp Σ :=
  ∃ n : nat, c ↦∗ [ #n ] ∗ mono_nat_auth_own γ 1 n.

Definition is_counter (γ : gname) (c : location) : iProp Σ :=
  inv counterN (counter_inv γ c).

Definition counter_lb (γ : gname) (n : nat) : iProp Σ :=
  mono_nat_lb_own γ n.

Global Instance is_counter_persistent γ c : Persistent (is_counter γ c) := _.
Global Instance counter_lb_persistent γ n : Persistent (counter_lb γ n) := _.

Lemma goal_mk_counter p ks :
  focused p ks (mk_counter (Val ValUnit)) -∗
  (∀ (c : location) γ,
     is_counter γ c -∗ counter_lb γ 0 -∗
     focused p ks (Val (ValLoc c)) -∗ goal ⊤) -∗
  goal ⊤.
Proof.
  iIntros "Hp Hcont". rewrite /mk_counter.
  g_call "Hp". g_alloc "Hp" "Hc".
  iApply fupd_goal.
  iMod (mono_nat_own_alloc 0) as (γ) "[Hauth #Hlb]".
  iMod (inv_alloc counterN _ (counter_inv γ l) with "[Hc Hauth]") as "#Hinv".
  { iNext. iExists 0%nat. iFrame. }
  iModIntro. iApply ("Hcont" with "Hinv Hlb Hp").
Qed.

Lemma goal_incr_atomic p ks γ c :
  is_counter γ c -∗
  focused p ks (incr_atomic (Val (ValLoc c))) -∗
  (∀ n : nat, counter_lb γ (S n) -∗ focused p ks (Val ValUnit) -∗ goal ⊤) -∗
  goal ⊤.
Proof.
  iIntros "#Hinv Hp Hcont". rewrite /incr_atomic. g_call "Hp".
  iApply (goal_inv_acc with "Hinv"); first done.
  iIntros "HP Hclose".
  iDestruct "HP" as (n) "[Hc Hauth]".
  iApply fupd_goal. iMod "Hc". iMod "Hauth". iModIntro.
  g_get_field "Hp" "Hc". g_let "Hp". g_binop "Hp".
  g_focus (CAS _ _ _) "Hp". g_tuple "Hp".
  g_cas_prim_succ "Hp" "Hc".
  simpl.
  g_if_true "Hp".
  iApply fupd_goal.
  iMod (mono_nat_own_update (S n) with "Hauth") as "[Hauth #Hlb]"; first lia.
  replace #(n + 1)%Z with #(S n) by (do 2 f_equal; lia).
  iModIntro.
  iApply (goal_inv_close with "[Hc Hauth] Hclose"); first done.
  { iNext. iExists (S n). iFrame. }
  iApply ("Hcont" with "Hlb Hp").
Qed.

Lemma goal_get_counter p ks γ c n :
  is_counter γ c -∗
  counter_lb γ n -∗
  focused p ks (get_counter (Val (ValLoc c))) -∗
  (∀ m : nat, ⌜n ≤ m⌝%nat -∗ counter_lb γ m -∗
     focused p ks (Val (ValInt (Z.of_nat m))) -∗ goal ⊤) -∗
  goal ⊤.
Proof.
  iIntros "#Hinv #Hlb Hp Hcont". rewrite /get_counter. g_call "Hp".
  iApply (goal_inv_acc with "Hinv"); first done.
  iIntros "HP Hclose".
  iDestruct "HP" as (m) "[Hc Hauth]".
  iApply fupd_goal. iMod "Hc". iMod "Hauth".
  iDestruct (mono_nat_lb_own_valid with "Hauth Hlb") as %[_ Hle].
  iDestruct (mono_nat_lb_own_get with "Hauth") as "#Hlb'".
  iModIntro.
  g_get_field "Hp" "Hc".
  iApply (goal_inv_close with "[Hc Hauth] Hclose"); first done.
  { iNext. iExists m. iFrame. }
  iApply ("Hcont" $! m with "[%] Hlb' Hp"); lia.
Qed.

End counter_spec.
