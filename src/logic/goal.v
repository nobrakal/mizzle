From iris.proofmode Require Import base proofmode.
From iris.bi.lib Require Import fixpoint_mono.
From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import coPset.

From mizzle.lang Require Export semantics.

From mizzle.logic Require Import interp wf_access decompose.

Definition terminated es := Forall (fun x => is_Some (to_val x)) es.

(** Discharge [wf_access σ (fill ks e)] for a concrete non-field-access redex
    [e]: rewrite to the bare redex and compute the vacuous [_ => True] arm. *)
Ltac wf_vacuous :=
  match goal with
  | |- wf_access ?σ (fill ?ks ?e) =>
      unfold wf_access;
      rewrite (decompose_fill_redex ks e
                ltac:(reflexivity)
                ltac:(reflexivity || (simpl; rewrite split_block_of_vals; reflexivity)));
      exact I
  end.

(** Discharge the [wf_access σ (fill ks <field-redex>)] obligation from the
    in-bounds witness [Hwf] extracted from the block. *)
Ltac wf_from_block σ ks redex Hwf :=
  rewrite (wf_access_fill_eq σ ks redex eq_refl eq_refl); exact Hwf.

Definition goal_pre `{seqlogGS Σ} (goal: coPsetO -d> iPropO Σ) : coPsetO -d> iPropO Σ :=
  λ E,
  ((∀ (es:list expr) (σ:state) (ts : list observation),
      interp es σ ts ={E}=∗
      (interp es σ ts ∗ remaining True%I ∗ |={E,⊤}=> True) ∨
      ∃ es' σ' κ,
      ⌜step (es,σ) κ (es',σ')⌝ ∗ interp es' σ' (ts ++ κ) ∗ goal E)
   ∨
   (∃ E', |={E,E'}=> goal E'))%I.

Section goal.
Context `{seqlogGS Σ}.

Lemma goal_pre_mono (wp1 wp2 : coPsetO -d> iPropO Σ) :
  □ (∀ E, wp1 E -∗ wp2 E) -∗ ∀ E, goal_pre wp1 E -∗ goal_pre wp2 E.
Proof.
  iIntros "#HX" (E) "[H|(%E' & H)]".
  - iLeft. iIntros (es σ ts) "Hi".
    iMod ("H" with "Hi") as "[Hl|(%&%&%&%&Hi&Hg)]".
    + iModIntro. by iLeft.
    + iModIntro. iRight. iExists _, _, _. iFrame "% Hi". by iApply "HX".
  - iRight. iExists E'. iMod "H" as "H". iModIntro. by iApply "HX".
Qed.

Global Instance goal_pre_mono' : BiMonoPred goal_pre.
Proof.
  constructor.
  - intros wp1 wp2 Hne1 Hne2.
    iIntros "#H" (E) "Hg".
    iApply (goal_pre_mono with "[] Hg").
    iIntros "!>" (E') "?". by iApply "H".
  - intros wp Hwp n E1 E2 HE.
    assert (E1 = E2) as -> by (apply leibniz_equiv, HE). done.
Qed.

Definition goal E : iProp Σ := bi_least_fixpoint goal_pre E.

Lemma goal_unfold E :
  goal E ⊣⊢ goal_pre goal E.
Proof. rewrite {1}/goal least_fixpoint_unfold //. Qed.

Lemma fulfill E :
  remaining True%I -∗ (|={E,⊤}=> True) -∗ goal E.
Proof.
  iIntros "Hr ?". iApply goal_unfold. iLeft. iIntros (es σ ts) "Hi".
  iModIntro. iLeft. iFrame.
Qed.

Lemma goal_mask_intro E E' :
  (|={E,E'}=> goal E') -∗ goal E.
Proof.
  iIntros "H". iApply goal_unfold. iRight. iExists E'. iExact "H".
Qed.

Lemma fupd_goal E : (|={E}=> goal E) -∗ goal E.
Proof.
  iIntros "H". iApply (goal_mask_intro _ E). iExact "H".
Qed.

Lemma bupd_goal E : (|==> goal E) -∗ goal E.
Proof.
  iIntros "H".
  iApply fupd_goal.
  iMod "H". by iFrame.
Qed.

Lemma construct_silent_step_fill es σ p ks e e' σ' :
  es !! p = Some (fill ks e) →
  base_step p e σ [] e' σ' [] →
  silent_step (es, σ) (<[p:=fill ks e']> es, σ').
Proof.
  intros Hlook Hstep.
  exists [].
  exists p, (fill ks e), (fill ks e'), σ', [].
  rewrite app_nil_r. split_and!; try done.
  econstructor; [reflexivity|reflexivity|exact Hstep].
Qed.

Local Lemma goal_base_step E p ks e (Φ : expr → iProp Σ) :
  running p (fill ks e) -∗
  (∀ es σ ts, interp es σ ts ={E}=∗
      ∃ e' σ', ⌜base_step p e σ [] e' σ' []⌝ ∗ ⌜wf_access σ (fill ks e)⌝ ∗
               interp es σ' ts ∗ Φ e') -∗
  (∀ e', Φ e' -∗ running p (fill ks e') -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hrun Hstep Hgoal".
  iApply goal_unfold.
  iLeft.
  iIntros (es σ ts) "Hi". simpl.
  iDestruct (interp_running_exploit with "Hrun Hi") as %Hlook.
  iMod ("Hstep" with "Hi") as (e' σ' Hstep Hwf) "[Hi HQ]".
  iMod (interp_run (fill ks e') with "Hrun Hi") as "[Hrun Hi]".
  iSpecialize ("Hgoal" with "HQ Hrun").
  iModIntro. iRight.
  iExists (<[p:=fill ks e']> es), σ', [].
  rewrite app_nil_r. iFrame.
  iPureIntro.
  by eapply construct_step_fill.
Qed.

Lemma goal_inv_acc N E P :
  ↑N ⊆ E ->
  inv N P -∗
  (▷ P -∗ (▷ P ={E ∖ ↑N, E}=∗ True) -∗ goal (E ∖ ↑N)) -∗
  goal E.
Proof.
  iIntros (HN) "#Hinv Hgoal".
  iApply (goal_mask_intro _ (E ∖ ↑N)).
  iMod (inv_acc with "Hinv") as "[HP Hclose]"; first done.
  iModIntro.
  iApply ("Hgoal" with "HP Hclose").
Qed.

Lemma goal_inv_close N E P :
  ↑N ⊆ E ->
  ▷ P -∗ (▷ P ={E ∖ ↑N, E}=∗ True) -∗
  goal E -∗
  goal (E ∖ ↑N).
Proof.
  iIntros (HN) "HP Hclose Hgoal".
  iApply (goal_mask_intro _ E).
  iMod ("Hclose" with "HP") as "_".
  iModIntro. iExact "Hgoal".
Qed.

(* This encompasses if, calls, etc *)
Lemma goal_pure_step E p ks e e' φ n :
  PureExec φ n e e' →
  φ →
  running p (fill ks e) -∗
  (running p (fill ks e') -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hexec Hφ) "Hrun Hgoal". specialize (Hexec Hφ).
  iInduction Hexec as [e0|n e0 em ef Hps Hrest IH].
  { by iApply "Hgoal". }
  pose proof (pure_step_context (fill ks) e0 em Hps) as [Hsafe Hdet].
  iApply goal_unfold. iLeft.
  iIntros (es σ ts) "Hi".
  iDestruct (interp_running_exploit with "Hrun Hi") as %Hlook.
  destruct (Hsafe p σ) as (enew & σnew & efs & Hstep).
  destruct (Hdet _ _ _ _ _ _ Hstep) as (_ & -> & -> & ->).
  iMod (interp_run (fill ks em) with "Hrun Hi") as "[Hrun Hi]".
  iModIntro. iRight.
  iExists (<[p:=fill ks em]> es), σ, [].
  rewrite app_nil_r. iFrame. iSplitR.
  { iPureIntro.
    exists [], p, (fill ks e0), (fill ks em), σ, [].
    rewrite app_nil_r. split_and!; try done.
    by eapply pure_step_wf_access. }
  iApply ("IH" with "Hrun Hgoal").
Qed.

Lemma goal_app E p ks i recs rec v :
  recs !! i = Some rec →
  running p (fill ks (App (Val (ValRecs i recs)) (Val v))) -∗
  (running p (fill ks (eval_app recs rec.1.2 v rec.2)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hrec) "Hrun Hgoal".
  iApply (goal_base_step _ _ _ _
    (λ e, ⌜e = eval_app recs rec.1.2 v rec.2⌝)%I
    with "Hrun [] [Hgoal]").
  { iIntros (es σ ts) "Hi". iModIntro.
    iExists (eval_app recs rec.1.2 v rec.2), σ. iFrame.
    iPureIntro. split_and!; [by apply base_step_app | wf_vacuous | done]. }
  { iIntros (e') "-> Hrun". by iApply "Hgoal". }
Qed.

(* The bid for a strong-generative block is chosen non-deterministically by
   the step rule, so we can pick any [bid] when consuming this expression. *)
Lemma goal_block_immutable_generative_strong E p ks tag (vs : list val) (bid : block_id) :
  running p (fill ks (Block ImmutableGenerativeStrong tag (of_vals vs))) -∗
  (running p (fill ks (Val (ValBlock (Generative (Some bid)) tag vs))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hrun Hgoal".
  iApply (goal_base_step _ _ _ _
    (λ e, ⌜e = Val (ValBlock (Generative (Some bid)) tag vs)⌝)%I
    with "Hrun [] [Hgoal]").
  { iIntros (es σ ts) "Hi". iModIntro.
    iExists (Val (ValBlock (Generative (Some bid)) tag vs)), σ. iFrame.
    iPureIntro. split_and!; [|wf_vacuous|done]. by apply base_step_block_immutable_generative_strong. }
  { iIntros (e') "-> Hrun". by iApply "Hgoal". }
Qed.

Lemma goal_block_mutable E p ks tag (vs:list val) :
  0 < length vs →
  running p (fill ks (Block Mutable tag (of_vals vs))) -∗
  (∀ l:location,
    l ↦ₕ□ Header tag (length vs) -∗
    ([∗ list] i ↦ v ∈ vs, (l +ₗ Z.of_nat i) ↦ v) -∗
    running p (fill ks (Val (ValLoc l))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hsz) "Hrun Hgoal".
  iApply (goal_base_step _ _ _ _
    (λ e, ∃ l:location, ⌜e = Val (ValLoc l)⌝ ∗
      l ↦ₕ□ Header tag (length vs) ∗
      [∗ list] i ↦ v ∈ vs, (l +ₗ Z.of_nat i) ↦ v)%I
    with "Hrun [] [Hgoal]").
  { iIntros (es σ ts) "Hi".
    set (l := location_fresh (dom σ.(state_headers) ∪ dom σ.(state_heap))).
    pose proof (location_fresh_fresh (dom σ.(state_headers) ∪ dom σ.(state_heap))) as Hfresh.
    setoid_rewrite not_elem_of_union in Hfresh.
    assert (σ.(state_headers) !! l = None) as Hhdr.
    { apply not_elem_of_dom. rewrite -(location_add_0 l).
      apply Hfresh. lia. }
    assert (∀ i:nat, i < length vs →
              σ.(state_headers) !! (l +ₗ i) = None ∧
              σ.(state_heap) !! (l +ₗ i) = None) as Hfree.
    { intros i Hi. split; apply not_elem_of_dom; apply Hfresh; lia. }
    iMod (interp_block_mutable l _ _ _ tag vs with "Hi") as "(Hi & Hl & Hcells & _)".
    { done. }
    { apply not_elem_of_dom. rewrite -(location_add_0 l). apply Hfresh. lia. }
    { intros i Hi. apply Hfree, Hi. }
    { intros i Hi. apply Hfree, Hi. }
    iModIntro. iExists (Val (ValLoc l)), (state_alloc l (Header tag (length vs)) vs σ).
    iFrame "Hi".
    iSplit.
    { iPureIntro.
      replace (length vs) with (length (of_vals vs)) by apply length_of_vals.
      apply base_step_block_mutable; try done.
      - rewrite length_of_vals //.
      - split_and!.
        + done.
        + apply not_elem_of_dom. rewrite -(location_add_0 l). apply Hfresh. lia.
        + intros i Hi. apply Hfree. rewrite length_of_vals // in Hi. }
    iSplit.
    { iPureIntro. wf_vacuous. }
    { iExists l. by iFrame. } }
  { iIntros (e') "[%l (-> & Hl & Hcells)] Hrun". iApply ("Hgoal" with "Hl Hcells Hrun"). }
Qed.

Lemma goal_alloc E p ks tag (n:Z) :
  (0 ≤ n)%Z →
  running p (fill ks (Alloc (Val (ValNat tag)) (Val (ValInt n)))) -∗
  (∀ l:location,
    l ↦ₕ□ Header tag (Z.to_nat n) -∗
    ([∗ list] i ↦ v ∈ replicate (Z.to_nat n) ValUnit, (l +ₗ Z.of_nat i) ↦ v) -∗
    (* Orphan live-location token: only meaningful when [n = 0], since
       for [n > 0] the cell at offset 0 already carries [loc_tok1 l]. *)
    (⌜n = 0%Z⌝ -∗ loc_tok1 l) -∗
    running p (fill ks (Val (ValLoc l))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hn) "Hrun Hgoal".
  iApply (goal_base_step _ _ _ _
    (λ e, ∃ l:location, ⌜e = Val (ValLoc l)⌝ ∗
      l ↦ₕ□ Header tag (Z.to_nat n) ∗
      ([∗ list] i ↦ v ∈ replicate (Z.to_nat n) ValUnit, (l +ₗ Z.of_nat i) ↦ v) ∗
      (⌜n = 0%Z⌝ -∗ loc_tok1 l))%I
    with "Hrun [] [Hgoal]").
  { iIntros (es σ ts) "Hi".
    set (l := location_fresh (dom σ.(state_headers) ∪ dom σ.(state_heap))).
    pose proof (location_fresh_fresh (dom σ.(state_headers) ∪ dom σ.(state_heap))) as Hfresh.
    setoid_rewrite not_elem_of_union in Hfresh.
    assert (σ.(state_headers) !! l = None) as Hhdr.
    { apply not_elem_of_dom. rewrite -(location_add_0 l).
      apply Hfresh. lia. }
    assert (∀ i, i < length (replicate (Z.to_nat n) ValUnit) → σ.(state_heap) !! (l +ₗ i) = None) as Hheap.
    { intros i Hi. apply not_elem_of_dom. apply Hfresh. lia. }
    assert (∀ i:nat, i < Z.to_nat n →
              σ.(state_headers) !! (l +ₗ i) = None ∧
              σ.(state_heap) !! (l +ₗ i) = None) as Hfree.
    { intros i Hi. split; apply not_elem_of_dom; apply Hfresh; lia. }
    iMod (interp_block_mutable l _ _ _ tag (replicate (Z.to_nat n) ValUnit) with "Hi")
      as "(Hi & Hl & Hcells & Horph)".
    { done. }
    { apply not_elem_of_dom. rewrite -(location_add_0 l). apply Hfresh. lia. }
    { exact Hheap. }
    { intros i Hi. apply Hfree. rewrite length_replicate in Hi. done. }
    iEval (rewrite length_replicate) in "Hi".
    iEval (rewrite length_replicate) in "Hl".
    iModIntro.
    iExists (Val (ValLoc l)), (state_alloc l (Header tag (Z.to_nat n)) (replicate (Z.to_nat n) ValUnit) σ).
    iFrame "Hi".
    iSplit.
    { iPureIntro. apply base_step_alloc; first done.
      split_and!.
      - done.
      - apply not_elem_of_dom. rewrite -(location_add_0 l). apply Hfresh. lia.
      - intros i Hi. split; apply not_elem_of_dom; apply Hfresh; lia. }
    iSplit.
    { iPureIntro. wf_vacuous. }
    iExists l. iFrame "Hl Hcells".
    iSplit; first done.
    destruct (Z.to_nat n) as [|n'] eqn:Hzn; simpl.
    - (* n = 0: provide the orphan token. *)
      iIntros (_). iFrame.
    - (* n > 0: vacuous wand; the premise [n = 0] contradicts [Z.to_nat n = S n']. *)
      iIntros (->). simpl in Hzn. lia. }
  { iIntros (e') "[%l (-> & Hl & Hcells & Horph)] Hrun".
    iApply ("Hgoal" with "Hl Hcells Horph Hrun"). }
Qed.

Lemma goal_ref E p ks v :
  running p (fill ks (ref (Val v))) -∗
  (∀ l:location, l ↦∗ [v] -∗ running p (fill ks (Val (ValLoc l))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hrun Hgoal".
  iApply (goal_block_mutable _ _ _ _ [v] with "Hrun"); first (simpl; lia).
  iIntros (l) "Hhdr Hcells Hrun". simpl.
  iApply ("Hgoal" with "[Hhdr Hcells] Hrun").
  iExists _. iFrame.
Qed.

Lemma goal_get_field E atm p ks (l:location) (fld:Z) dq vs v :
  (0 ≤ fld)%Z →
  vs !! Z.to_nat fld = Some v →
  running p (fill ks (GetField atm (Val (ValLoc l)) (Val (ValInt fld)))) -∗
  l ↦∗{dq} vs -∗
  (l ↦∗{dq} vs -∗ running p (fill ks (Val v)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hfld Hidx) "Hrun Hblk Hgoal".
  iApply (goal_base_step _ _ _ _
    (λ e, ⌜e = Val v⌝ ∗ l ↦∗{dq} vs)%I
    with "Hrun [Hblk] [Hgoal]").
  { iIntros (es σ ts) "Hi".
    iDestruct (interp_block_wf_access l _ _ _ _ _ fld with "Hi Hblk") as %Hwf.
    { apply lookup_lt_Some in Hidx. lia. }
    iDestruct (mz_block_cell_acc_Z _ _ _ _ _ Hfld Hidx with "Hblk") as "[Hc Hclose]".
    iDestruct (interp_get_field with "Hi Hc") as %Hlook.
    iDestruct ("Hclose" $! v with "Hc") as "Hblk".
    rewrite list_insert_id; last exact Hidx.
    iModIntro. iExists (Val v), σ. iFrame "Hi Hblk".
    iPureIntro. split_and!.
    - by eapply base_step_get_field_mutable.
    - wf_from_block σ ks (GetField atm (Val (ValLoc l)) (Val (ValInt fld))) Hwf.
    - done. }
  { iIntros (e') "[-> Hblk] Hrun". iApply ("Hgoal" with "Hblk Hrun"). }
Qed.

Lemma goal_set_field E atm p ks (l:location) (fld:Z) v w vs :
  (0 ≤ fld)%Z →
  vs !! Z.to_nat fld = Some v →
  running p (fill ks (SetField atm (Val (ValLoc l)) (Val (ValInt fld)) (Val w))) -∗
  l ↦∗ vs -∗
  (l ↦∗ <[Z.to_nat fld := w]> vs -∗ running p (fill ks (Val ValUnit)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hfld Hidx) "Hrun Hblk Hgoal".
  iApply (goal_base_step _ _ _ _
    (λ e, ⌜e = Val ValUnit⌝ ∗ l ↦∗ <[Z.to_nat fld := w]> vs)%I
    with "Hrun [Hblk] [Hgoal]").
  { iIntros (es σ ts) "Hi".
    iDestruct (interp_block_wf_access l _ _ _ _ _ fld with "Hi Hblk") as %Hwf.
    { apply lookup_lt_Some in Hidx. lia. }
    iDestruct (mz_block_cell_acc_Z _ _ _ _ _ Hfld Hidx with "Hblk") as "[Hc Hclose]".
    iMod (interp_set_field _ _ _ _ _ w with "Hi Hc") as "(%Hlook & Hi & Hc)".
    iDestruct ("Hclose" $! w with "Hc") as "Hblk".
    iModIntro. iExists (Val ValUnit), _. iFrame "Hi Hblk".
    iPureIntro. split_and!.
    - apply base_step_set_field. by eexists.
    - wf_from_block σ ks (SetField atm (Val (ValLoc l)) (Val (ValInt fld)) (Val w)) Hwf.
    - done. }
  { iIntros (e') "[-> Hblk] Hrun". iApply ("Hgoal" with "Hblk Hrun"). }
Qed.

Lemma goal_cas_succ E p ks (l:location) (fld:Z) v1 v2 vl vs :
  vl ≈ v1 →
  (0 ≤ fld)%Z →
  vs !! Z.to_nat fld = Some vl →
  running p (fill ks (CAS (Val (ValTuple [ValLoc l; ValInt fld])) (Val v1) (Val v2))) -∗
  l ↦∗ vs -∗
  (l ↦∗ <[Z.to_nat fld := v2]> vs -∗ running p (fill ks (Val (ValBool true))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hsim Hfld Hidx) "Hrun Hblk Hgoal".
  iApply (goal_base_step _ _ _ _
    (λ e, ⌜e = Val (ValBool true)⌝ ∗ l ↦∗ <[Z.to_nat fld := v2]> vs)%I
    with "Hrun [Hblk] [Hgoal]").
  { iIntros (es σ ts) "Hi".
    iDestruct (interp_block_wf_access l _ _ _ _ _ fld with "Hi Hblk") as %Hwf.
    { apply lookup_lt_Some in Hidx. lia. }
    iDestruct (mz_block_cell_acc_Z _ _ _ _ _ Hfld Hidx with "Hblk") as "[Hc Hclose]".
    iMod (interp_set_field _ _ _ _ _ v2 with "Hi Hc") as "(%Hlook & Hi & Hc)".
    iDestruct ("Hclose" $! v2 with "Hc") as "Hblk".
    iModIntro. iExists (Val (ValBool true)), _. iFrame "Hi Hblk".
    iPureIntro. split_and!.
    - eapply base_step_cas_success; done.
    - wf_from_block σ ks (CAS (Val (ValTuple [ValLoc l; ValInt fld])) (Val v1) (Val v2)) Hwf.
    - done. }
  { iIntros (e') "[-> Hblk] Hrun". iApply ("Hgoal" with "Hblk Hrun"). }
Qed.

Lemma goal_cas_fail E p ks (l:location) (fld:Z) dq v1 v2 vl vs :
  vl ≉ v1 →
  (0 ≤ fld)%Z →
  vs !! Z.to_nat fld = Some vl →
  running p (fill ks (CAS (Val (ValTuple [ValLoc l; ValInt fld])) (Val v1) (Val v2))) -∗
  l ↦∗{dq} vs -∗
  (l ↦∗{dq} vs -∗ running p (fill ks (Val (ValBool false))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hnsim Hfld Hidx) "Hrun Hblk Hgoal".
  iApply (goal_base_step _ _ _ _
    (λ e, ⌜e = Val (ValBool false)⌝ ∗ l ↦∗{dq} vs)%I
    with "Hrun [Hblk] [Hgoal]").
  { iIntros (es σ ts) "Hi".
    iDestruct (interp_block_wf_access l _ _ _ _ _ fld with "Hi Hblk") as %Hwf.
    { apply lookup_lt_Some in Hidx. lia. }
    iDestruct (mz_block_cell_acc_Z _ _ _ _ _ Hfld Hidx with "Hblk") as "[Hc Hclose]".
    iDestruct (interp_get_field with "Hi Hc") as %Hlook.
    iDestruct ("Hclose" $! vl with "Hc") as "Hblk".
    rewrite list_insert_id; last exact Hidx.
    iModIntro. iExists (Val (ValBool false)), σ. iFrame "Hi Hblk".
    iPureIntro. split_and!.
    - eapply base_step_cas_fail; done.
    - wf_from_block σ ks (CAS (Val (ValTuple [ValLoc l; ValInt fld])) (Val v1) (Val v2)) Hwf.
    - done. }
  { iIntros (e') "[-> Hblk] Hrun". iApply ("Hgoal" with "Hblk Hrun"). }
Qed.

Lemma goal_equal_fail E p ks v1 v2 :
  v1 ≉ v2 →
  running p (fill ks (Equal (Val v1) (Val v2))) -∗
  (running p (fill ks (Val (ValBool false))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hnsim) "Hrun Hgoal".
  iApply (goal_base_step _ _ _ _
    (λ e, ⌜e = Val (ValBool false)⌝)%I
    with "Hrun [] [Hgoal]").
  { iIntros (es σ ts) "Hi".
    iModIntro. iExists (Val (ValBool false)), σ. iFrame.
    iPureIntro. split_and!; [|wf_vacuous|done].
    by apply base_step_equal_fail. }
  { iIntros (e') "-> Hrun". iApply ("Hgoal" with "Hrun"). }
Qed.

Lemma goal_equal_succ E p ks v1 v2 :
  v1 ≈ v2 →
  running p (fill ks (Equal (Val v1) (Val v2))) -∗
  (running p (fill ks (Val (ValBool true))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hsim) "Hrun Hgoal".
  iApply (goal_base_step _ _ _ _
    (λ e, ⌜e = Val (ValBool true)⌝)%I
    with "Hrun [] [Hgoal]").
  { iIntros (es σ ts) "Hi".
    iModIntro. iExists (Val (ValBool true)), σ. iFrame.
    iPureIntro. split_and!; [|wf_vacuous|done].
    by apply base_step_equal_success. }
  { iIntros (e') "-> Hrun". iApply ("Hgoal" with "Hrun"). }
Qed.

Lemma goal_fork E p ks e v :
  val_immediate v →
  running p (fill ks (Fork e)) -∗
  (∀ p', local p' v -∗ running p' e -∗ running p (fill ks (Val ValUnit)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hv) "Hrun Hgoal".
  iApply goal_unfold. iLeft.
  iIntros (es σ ts) "Hi".
  iDestruct (interp_running_exploit with "Hrun Hi") as %Hlook.
  iMod (interp_fork v _ _ (fill ks Unit) e with "Hrun Hi")
    as "(Hrun & Hrun' & Hloc & Hi)".
  iModIntro. iRight.
  iExists (<[p:=fill ks Unit]> es ++ [e]), (state_add_local v σ), [].
  rewrite app_nil_r.
  iFrame.
  iSplitR "Hrun Hrun' Hloc Hgoal".
  - iPureIntro.
    exists [], p, (fill ks (Fork e)), (fill ks Unit), (state_add_local v σ), [e].
    split_and!; try done.
    { econstructor; [reflexivity|reflexivity|]. by apply base_step_fork. }
    { wf_vacuous. }
  - iApply ("Hgoal" with "Hloc Hrun' Hrun").
Qed.

Lemma goal_get_local E p ks v :
  running p (fill ks GetLocal) -∗
  local p v -∗
  (local p v -∗ running p (fill ks (Val v)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hrun Hloc Hgoal".
  iApply (goal_base_step _ _ _ _
    (λ e, ⌜e = Val v⌝ ∗ local p v)%I
    with "Hrun [Hloc] [Hgoal]").
  { iIntros (es σ ts) "Hi".
    iDestruct (interp_local_exploit with "Hloc Hi") as %Hlook.
    iModIntro. iExists (Val v), σ. iFrame.
    iPureIntro. split_and!; [|wf_vacuous|done].
    by apply base_step_get_local. }
  { iIntros (e') "[-> Hloc] Hrun". iApply ("Hgoal" with "Hloc Hrun"). }
Qed.

Lemma goal_set_local E p ks v w :
  running p (fill ks (SetLocal (Val w))) -∗
  local p v -∗
  (local p w -∗ running p (fill ks (Val ValUnit)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hrun Hloc Hgoal".
  iApply (goal_base_step _ _ _ _
    (λ e, ⌜e = Val ValUnit⌝ ∗ local p w)%I
    with "Hrun [Hloc] [Hgoal]").
  { iIntros (es σ ts) "Hi".
    iDestruct (interp_local_exploit with "Hloc Hi") as %Hlook.
    iMod (interp_set_local _ _ w with "Hloc Hi") as "[Hloc Hi]".
    iModIntro. iExists (Val ValUnit), _. iFrame.
    iPureIntro. split_and!; [|wf_vacuous|done].
    apply base_step_set_local. by eexists. }
  { iIntros (e') "[-> Hloc] Hrun". iApply ("Hgoal" with "Hloc Hrun"). }
Qed.

Lemma goal_match_mutable E p ks (l:location) hdr x e0 brs e' dq :
  eval_match hdr.(header_tag) hdr.(header_size) (SubjectLoc l) x e0 brs = Some e' →
  running p (fill ks (Match (Val (ValLoc l)) x e0 brs)) -∗
  l ↦ₕ{dq} hdr -∗
  (l ↦ₕ{dq} hdr -∗ running p (fill ks e') -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hev) "Hrun Hl Hgoal".
  iApply (goal_base_step _ _ _ _
    (λ e, ⌜e = e'⌝ ∗ l ↦ₕ{dq} hdr)%I
    with "Hrun [Hl] [Hgoal]").
  { iIntros (es σ ts) "Hi".
    iDestruct (interp_get_field_header with "Hi Hl") as %Hlook.
    iModIntro. iExists e', σ. iFrame.
    iPureIntro. split_and!; [|wf_vacuous|done].
    by eapply base_step_match_mutable. }
  { iIntros (e'') "[-> Hl] Hrun". iApply ("Hgoal" with "Hl Hrun"). }
Qed.

Lemma goal_get_tag_mutable E p ks (l:location) hdr dq :
  running p (fill ks (GetTag (Val (ValLoc l)))) -∗
  l ↦ₕ{dq} hdr -∗
  (l ↦ₕ{dq} hdr -∗ running p (fill ks (Val (ValNat hdr.(header_tag)))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hrun Hl Hgoal".
  iApply (goal_base_step _ _ _ _
    (λ e, ⌜e = Val (ValNat hdr.(header_tag))⌝ ∗ l ↦ₕ{dq} hdr)%I
    with "Hrun [Hl] [Hgoal]").
  { iIntros (es σ ts) "Hi".
    iDestruct (interp_get_field_header with "Hi Hl") as %Hlook.
    iModIntro. iExists _, σ. iFrame.
    iPureIntro. split_and!; [|wf_vacuous|done].
    by apply base_step_get_tag_mutable. }
  { iIntros (e') "[-> Hl] Hrun". iApply ("Hgoal" with "Hl Hrun"). }
Qed.

Lemma goal_get_size_mutable E p ks (l:location) hdr dq :
  running p (fill ks (GetSize (Val (ValLoc l)))) -∗
  l ↦ₕ{dq} hdr -∗
  (l ↦ₕ{dq} hdr -∗ running p (fill ks (Val (ValNat hdr.(header_size)))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hrun Hl Hgoal".
  iApply (goal_base_step _ _ _ _
    (λ e, ⌜e = Val (ValNat hdr.(header_size))⌝ ∗ l ↦ₕ{dq} hdr)%I
    with "Hrun [Hl] [Hgoal]").
  { iIntros (es σ ts) "Hi".
    iDestruct (interp_get_field_header with "Hi Hl") as %Hlook.
    iModIntro. iExists _, σ. iFrame.
    iPureIntro. split_and!; [|wf_vacuous|done].
    by apply base_step_get_size_mutable. }
  { iIntros (e') "[-> Hl] Hrun". iApply ("Hgoal" with "Hl Hrun"). }
Qed.

Lemma goal_xchg E p ks (l:location) (fld:Z) v w vs :
  (0 ≤ fld)%Z →
  vs !! Z.to_nat fld = Some v →
  running p (fill ks (Xchg (Val (ValTuple [ValLoc l; ValInt fld])) (Val w))) -∗
  l ↦∗ vs -∗
  (l ↦∗ <[Z.to_nat fld := w]> vs -∗ running p (fill ks (Val v)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hfld Hidx) "Hrun Hblk Hgoal".
  iApply (goal_base_step _ _ _ _
    (λ e, ⌜e = Val v⌝ ∗ l ↦∗ <[Z.to_nat fld := w]> vs)%I
    with "Hrun [Hblk] [Hgoal]").
  { iIntros (es σ ts) "Hi".
    iDestruct (interp_block_wf_access l _ _ _ _ _ fld with "Hi Hblk") as %Hwf.
    { apply lookup_lt_Some in Hidx. lia. }
    iDestruct (mz_block_cell_acc_Z _ _ _ _ _ Hfld Hidx with "Hblk") as "[Hc Hclose]".
    iMod (interp_set_field _ _ _ _ _ w with "Hi Hc") as "(%Hlook & Hi & Hc)".
    iDestruct ("Hclose" $! w with "Hc") as "Hblk".
    iModIntro. iExists (Val v), _. iFrame "Hi Hblk".
    iPureIntro. split_and!.
    - by eapply base_step_xchg.
    - wf_from_block σ ks (Xchg (Val (ValTuple [ValLoc l; ValInt fld])) (Val w)) Hwf.
    - done. }
  { iIntros (e') "[-> Hblk] Hrun". iApply ("Hgoal" with "Hblk Hrun"). }
Qed.

Lemma goal_faa E p ks (l:location) (fld:Z) (i1 i2:Z) vs :
  (0 ≤ fld)%Z →
  vs !! Z.to_nat fld = Some (ValInt i1) →
  running p (fill ks (FAA (Val (ValTuple [ValLoc l; ValInt fld])) (Val (ValInt i2)))) -∗
  l ↦∗ vs -∗
  (l ↦∗ <[Z.to_nat fld := ValInt (i1 + i2)]> vs -∗ running p (fill ks (Val (ValInt i1))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hfld Hidx) "Hrun Hblk Hgoal".
  iApply (goal_base_step _ _ _ _
    (λ e, ⌜e = Val (ValInt i1)⌝ ∗ l ↦∗ <[Z.to_nat fld := ValInt (i1 + i2)]> vs)%I
    with "Hrun [Hblk] [Hgoal]").
  { iIntros (es σ ts) "Hi".
    iDestruct (interp_block_wf_access l _ _ _ _ _ fld with "Hi Hblk") as %Hwf.
    { apply lookup_lt_Some in Hidx. lia. }
    iDestruct (mz_block_cell_acc_Z _ _ _ _ _ Hfld Hidx with "Hblk") as "[Hc Hclose]".
    iMod (interp_set_field _ _ _ _ _ (ValInt (i1 + i2)) with "Hi Hc") as "(%Hlook & Hi & Hc)".
    iDestruct ("Hclose" $! (ValInt (i1 + i2)) with "Hc") as "Hblk".
    iModIntro. iExists (Val (ValInt i1)), _. iFrame "Hi Hblk".
    iPureIntro. split_and!.
    - by eapply base_step_faa.
    - wf_from_block σ ks (FAA (Val (ValTuple [ValLoc l; ValInt fld])) (Val (ValInt i2))) Hwf.
    - done. }
  { iIntros (e') "[-> Hblk] Hrun". iApply ("Hgoal" with "Hblk Hrun"). }
Qed.

(** ** Header-aware single-cell field rules

    These take the persistent header [l ↦ₕ{dqh} hdr] plus a single cell
    [(l +ₗ fld) ↦ v] and an in-range offset, certifying [wf_access] from the
    header rather than from a whole block. They fit the array specs,
    which keep the header separate from individual cells. *)

Lemma goal_get_field_cell E atm p ks (l:location) (fld:Z) dqh hdr dq v :
  (0 ≤ fld < Z.of_nat (header_size hdr))%Z →
  running p (fill ks (GetField atm (Val (ValLoc l)) (Val (ValInt fld)))) -∗
  l ↦ₕ{dqh} hdr -∗
  (l +ₗ fld) ↦{dq} v -∗
  (l ↦ₕ{dqh} hdr -∗ (l +ₗ fld) ↦{dq} v -∗ running p (fill ks (Val v)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hfld) "Hrun Hh Hc Hgoal".
  iApply (goal_base_step _ _ _ _
    (λ e, ⌜e = Val v⌝ ∗ l ↦ₕ{dqh} hdr ∗ (l +ₗ fld) ↦{dq} v)%I
    with "Hrun [Hh Hc] [Hgoal]").
  { iIntros (es σ ts) "Hi".
    iDestruct (interp_header_wf_access l _ _ _ _ _ fld Hfld with "Hi Hh") as %Hwf.
    iDestruct (interp_get_field with "Hi Hc") as %Hlook.
    iModIntro. iExists (Val v), σ. iFrame "Hi Hh Hc".
    iPureIntro. split_and!.
    - by eapply base_step_get_field_mutable.
    - wf_from_block σ ks (GetField atm (Val (ValLoc l)) (Val (ValInt fld))) Hwf.
    - done. }
  { iIntros (e') "(-> & Hh & Hc) Hrun". iApply ("Hgoal" with "Hh Hc Hrun"). }
Qed.

Lemma goal_set_field_cell E atm p ks (l:location) (fld:Z) dqh hdr v w :
  (0 ≤ fld < Z.of_nat (header_size hdr))%Z →
  running p (fill ks (SetField atm (Val (ValLoc l)) (Val (ValInt fld)) (Val w))) -∗
  l ↦ₕ{dqh} hdr -∗
  (l +ₗ fld) ↦ v -∗
  (l ↦ₕ{dqh} hdr -∗ (l +ₗ fld) ↦ w -∗ running p (fill ks (Val ValUnit)) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hfld) "Hrun Hh Hc Hgoal".
  iApply (goal_base_step _ _ _ _
    (λ e, ⌜e = Val ValUnit⌝ ∗ l ↦ₕ{dqh} hdr ∗ (l +ₗ fld) ↦ w)%I
    with "Hrun [Hh Hc] [Hgoal]").
  { iIntros (es σ ts) "Hi".
    iDestruct (interp_header_wf_access l _ _ _ _ _ fld Hfld with "Hi Hh") as %Hwf.
    iMod (interp_set_field _ _ _ _ _ w with "Hi Hc") as "(%Hlook & Hi & Hc)".
    iModIntro. iExists (Val ValUnit), _. iFrame "Hi Hh Hc".
    iPureIntro. split_and!.
    - apply base_step_set_field. by eexists.
    - wf_from_block σ ks (SetField atm (Val (ValLoc l)) (Val (ValInt fld)) (Val w)) Hwf.
    - done. }
  { iIntros (e') "(-> & Hh & Hc) Hrun". iApply ("Hgoal" with "Hh Hc Hrun"). }
Qed.

Lemma goal_cas_succ_cell E p ks (l:location) (fld:Z) dqh hdr v1 v2 vl :
  vl ≈ v1 →
  (0 ≤ fld < Z.of_nat (header_size hdr))%Z →
  running p (fill ks (CAS (Val (ValTuple [ValLoc l; ValInt fld])) (Val v1) (Val v2))) -∗
  l ↦ₕ{dqh} hdr -∗
  (l +ₗ fld) ↦ vl -∗
  (l ↦ₕ{dqh} hdr -∗ (l +ₗ fld) ↦ v2 -∗ running p (fill ks (Val (ValBool true))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hsim Hfld) "Hrun Hh Hc Hgoal".
  iApply (goal_base_step _ _ _ _
    (λ e, ⌜e = Val (ValBool true)⌝ ∗ l ↦ₕ{dqh} hdr ∗ (l +ₗ fld) ↦ v2)%I
    with "Hrun [Hh Hc] [Hgoal]").
  { iIntros (es σ ts) "Hi".
    iDestruct (interp_header_wf_access l _ _ _ _ _ fld Hfld with "Hi Hh") as %Hwf.
    iMod (interp_set_field _ _ _ _ _ v2 with "Hi Hc") as "(%Hlook & Hi & Hc)".
    iModIntro. iExists (Val (ValBool true)), _. iFrame "Hi Hh Hc".
    iPureIntro. split_and!.
    - eapply base_step_cas_success; done.
    - wf_from_block σ ks (CAS (Val (ValTuple [ValLoc l; ValInt fld])) (Val v1) (Val v2)) Hwf.
    - done. }
  { iIntros (e') "(-> & Hh & Hc) Hrun". iApply ("Hgoal" with "Hh Hc Hrun"). }
Qed.

Lemma goal_cas_fail_cell E p ks (l:location) (fld:Z) dqh hdr dq v1 v2 vl :
  vl ≉ v1 →
  (0 ≤ fld < Z.of_nat (header_size hdr))%Z →
  running p (fill ks (CAS (Val (ValTuple [ValLoc l; ValInt fld])) (Val v1) (Val v2))) -∗
  l ↦ₕ{dqh} hdr -∗
  (l +ₗ fld) ↦{dq} vl -∗
  (l ↦ₕ{dqh} hdr -∗ (l +ₗ fld) ↦{dq} vl -∗ running p (fill ks (Val (ValBool false))) -∗ goal E) -∗
  goal E.
Proof.
  iIntros (Hnsim Hfld) "Hrun Hh Hc Hgoal".
  iApply (goal_base_step _ _ _ _
    (λ e, ⌜e = Val (ValBool false)⌝ ∗ l ↦ₕ{dqh} hdr ∗ (l +ₗ fld) ↦{dq} vl)%I
    with "Hrun [Hh Hc] [Hgoal]").
  { iIntros (es σ ts) "Hi".
    iDestruct (interp_header_wf_access l _ _ _ _ _ fld Hfld with "Hi Hh") as %Hwf.
    iDestruct (interp_get_field with "Hi Hc") as %Hlook.
    iModIntro. iExists (Val (ValBool false)), σ. iFrame "Hi Hh Hc".
    iPureIntro. split_and!.
    - eapply base_step_cas_fail; done.
    - wf_from_block σ ks (CAS (Val (ValTuple [ValLoc l; ValInt fld])) (Val v1) (Val v2)) Hwf.
    - done. }
  { iIntros (e') "(-> & Hh & Hc) Hrun". iApply ("Hgoal" with "Hh Hc Hrun"). }
Qed.

(** ** The [Emit] trace primitive

    [Emit #v] appends the observation [v] to the global trace. The trace is
    ghost: it never constrains control flow or the heap, and no program can
    read it back. *)

(** [Emit #v] is a leaf redex, and not a field access, so [wf_access] holds
    vacuously. Like [goal_pure_step], [interp] is kept internal. *)
Lemma goal_emit E p ks (v : val) tr :
  running p (fill ks (Emit (Val v))) -∗
  trace_model tr -∗
  (running p (fill ks Unit) -∗ trace_model (tr ++ [v]) -∗ goal E) -∗
  goal E.
Proof.
  iIntros "Hrun Htr Hgoal".
  iApply goal_unfold. iLeft. iIntros (es σ ts) "Hi".
  iDestruct (interp_running_exploit with "Hrun Hi") as %Hlook.
  iMod (interp_emit v with "Hi Htr") as "[Hi Htr]".
  iMod (interp_run (fill ks Unit) with "Hrun Hi") as "[Hrun Hi]".
  iSpecialize ("Hgoal" with "Hrun Htr").
  iModIntro. iRight.
  iExists (<[p := fill ks Unit]> es), σ, [v].
  iFrame "Hi Hgoal".
  iPureIntro.
  exists [v], p, (fill ks (Emit (Val v))), (fill ks Unit), σ, [].
  split_and!; try done.
  - simpl. econstructor; [reflexivity|reflexivity|]. by apply base_step_emit.
  - by rewrite app_nil_r.
  - simpl. wf_vacuous.
Qed.

End goal.
