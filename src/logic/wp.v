From stdpp Require Import relations.
From iris.proofmode Require Import base proofmode.
From iris.bi.lib Require Import fixpoint_mono.
From iris.base_logic.lib Require Import fancy_updates invariants.

From mizzle.lang Require Export instances.

From mizzle.logic Require Import interp wf_access decompose goal.

Definition wp_arg Σ : Type := nat * expr * (val -d> iPropO Σ).

(* To support [wp_bind], the non-value case quantifies over an arbitrary
  evaluation context [K]: the [running] assertion (and the resulting thread
  expression) is about [fill K e] rather than [e] alone, while the step itself
  concerns the redex [e]. Instantiating [K := []] recovers the plain rule.

  Note: if I want to derive something showing neg (wp p e Q),
  I'll have to write this WP only in terms of ghost_heap
  (ie, remove the running assertions).
   *)
Definition wp_pre `{seqlogGS Σ}
  (wp : wp_arg Σ -d> iPropO Σ) : wp_arg Σ -d> iPropO Σ :=
  λ x,
    let p := x.1.1 in
    let e := x.1.2 in
    let Φ := x.2 in
    match to_val e with
    | Some v => |={⊤}=> Φ v
    | None =>
        ∀ K, running p (fill K e) -∗
        ∀ es σ ts, interp es σ ts ={⊤}=∗
          ⌜reducible p e σ⌝ ∗ ⌜wf_access σ (fill K e)⌝ ∗
          (∀ κ e' σ' efs,
             ⌜prim_step p e σ κ e' σ' efs⌝ ={⊤}=∗
             interp (<[p:= fill K e']> es ++ efs) σ' (ts ++ κ) ∗
             running p (fill K e') ∗ wp (p, e', Φ) ∗
             ([∗ list] k ↦ ef ∈ efs,
                running (length es + k) ef ∗
                wp (length es + k, ef, (λ _, True%I))))
    end%I.

Section wp.
Context `{seqlogGS Σ}.

Lemma wp_pre_mono (wp1 wp2 : wp_arg Σ -d> iPropO Σ) :
  □ (∀ x, wp1 x -∗ wp2 x) -∗
    ∀ x, wp_pre wp1 x -∗ wp_pre wp2 x.
Proof.
  iIntros "#HX" (x). rewrite /wp_pre.
  destruct x as [[p e] Φ]. simpl.
  destruct (to_val e) as [v|] eqn:He; first by auto.
  iIntros "Hwp" (K) "Hrun". iIntros (es σ ts) "Hi".
  iMod ("Hwp" $! K with "Hrun Hi") as "($ & $ & Hcont)".
  iModIntro. iIntros (κ e' σ' efs Hstep).
  iMod ("Hcont" $! κ e' σ' efs Hstep) as "($ & $ & Hrec & Hfs)".
  iModIntro. iSplitL "Hrec".
  { by iApply "HX". }
  iApply (big_sepL_impl with "Hfs").
  iIntros "!>" (k ef _) "[$ Hk]". by iApply "HX".
Qed.

Instance wp_pre_mono' : BiMonoPred wp_pre.
Proof.
  constructor.
  { iIntros (wp1 wp2 ??) "#H". iIntros (x).
    iApply (wp_pre_mono with "[H]").
    iModIntro. iIntros (?). iApply "H". }
  intros wp Hwp n [[p e] Φ] [[p' e'] Φ'] [[Hp He] HΦ]. simpl in *.
  assert (p = p') by (apply leibniz_equiv; done).
  assert (e = e') by (apply leibniz_equiv; done).
  subst.
  rewrite /wp_pre /=.
  destruct (to_val e').
  - rewrite /bi_wand /=. f_equiv. apply HΦ.
  - solve_proper.
Qed.

Definition wp_def (p:nat) (e:expr) (Φ:val → iProp Σ) : iProp Σ :=
  bi_least_fixpoint wp_pre (p, e, Φ).

Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp := wp_aux.(unseal).
Lemma wp_unseal : wp = wp_def.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Lemma wp_unfold p e Φ :
  wp p e Φ ⊣⊢ wp_pre (λ x, wp x.1.1 x.1.2 x.2) (p, e, Φ).
Proof.
  rewrite wp_unseal /wp_def.
  rewrite {1}least_fixpoint_unfold //.
Qed.

Lemma wp_value p v Φ :
  Φ v -∗ wp p (Val v) Φ.
Proof.
  iIntros "HΦ". rewrite wp_unfold /wp_pre /=. by iFrame.
Qed.

Lemma fupd_wp p e Φ :
  (|={⊤}=> wp p e Φ) -∗ wp p e Φ.
Proof.
  iIntros "H".
  destruct (to_val e) as [v|] eqn:He.
  - rewrite !wp_unfold /wp_pre He. by iMod "H".
  - rewrite !wp_unfold /wp_pre He.
    iIntros (K). iIntros "Hrun" (es σ ts) "Hi".
    iMod "H". by iApply ("H" $! K with "Hrun Hi").
Qed.

Definition wp_bind_pred (x : wp_arg Σ) : iProp Σ :=
  ∀ K Φ,
    (∀ v, x.2 v -∗ wp x.1.1 (fill K (Val v)) Φ) -∗
    wp x.1.1 (fill K x.1.2) Φ.

Local Instance wp_bind_pred_ne : NonExpansive wp_bind_pred.
Proof.
  intros n [[p e] Φ] [[p' e'] Φ'] [[Hp He] HΦ].
  assert (p = p') by (apply leibniz_equiv; done).
  assert (e = e') by (apply leibniz_equiv; done). subst.
  rewrite /wp_bind_pred /=. solve_proper.
Qed.

Lemma wp_bind K p e Φ :
  wp p e (λ v, wp p (fill K (Val v)) Φ) -∗ wp p (fill K e) Φ.
Proof.
  iIntros "Hwp".
  iAssert (wp_bind_pred (p, e, (λ v, wp p (fill K (Val v)) Φ)%I)) with "[Hwp]" as "Hbind".
  { rewrite wp_unseal /wp_def.
    iApply (least_fixpoint_ind wp_pre wp_bind_pred with "[] Hwp").
    iModIntro. clear. iIntros ([[p e] Ψ]) "Hbody".
    rewrite {2}/wp_bind_pred /=.
    iIntros (K Φ) "HΦ".
    rewrite /wp_pre /=.
    destruct (to_val e) as [v|] eqn:He.
    - apply of_to_val in He. subst e.
      iApply fupd_wp. iMod "Hbody" as "HΨ". iModIntro.
      by iApply "HΦ".
    - rewrite wp_unfold /wp_pre.
      assert (to_val (fill K e) = None) as Hnv by (apply fill_not_val; done).
      rewrite Hnv.
      iIntros (K0). iIntros "Hrun" (es σ ts) "Hi".
      rewrite -fill_app.
      iMod ("Hbody" $! (K ++ K0) with "Hrun Hi") as "(%Hred & %Hwf & Hcont)".
      iModIntro. iSplit.
      { iPureIntro. by apply (reducible_context (fill K)). }
      iSplit.
      { iPureIntro. exact Hwf. }
      iIntros (κ e'' σ' efs Hstep). simpl in Hstep.
      destruct (@context_fill_step_inv (fill K) (context_fill K) p e σ κ e'' σ' efs He Hstep)
        as (e' & -> & Hstep').
      iMod ("Hcont" $! κ e' σ' efs Hstep') as "(Hi & Hrun & Hwp & Hfs)".
      iModIntro. rewrite -!fill_app. iFrame "Hi Hrun".
      iSplitL "Hwp HΦ".
      { iDestruct "Hwp" as "[Hbp _]".
        iApply ("Hbp" $! K Φ with "HΦ"). }
      iApply (big_sepL_impl with "Hfs").
      iIntros "!>" (k ef _) "[$ Hk]". iDestruct "Hk" as "[_ Hk]".
      rewrite wp_unseal /wp_def. iExact "Hk". }
  rewrite /wp_bind_pred /=. iApply ("Hbind" $! K Φ).
  iIntros (v) "$".
Qed.

End wp.

Notation "'WP' e ∷ p {{ Φ } }" := (wp p e Φ)
  (at level 20, e, p, Φ at level 200,
   format "'[hv' 'WP'  e  '∷'  p  '/' {{  Φ  } } ']'") : bi_scope.

Notation "'WP' e ∷ p {{ v , Q } }" := (wp p e (λ v, Q))
  (at level 20, e, p, Q at level 200,
   format "'[hv' 'WP'  e  '∷'  p  '/' {{  v ,  Q  } } ']'") : bi_scope.

Section wp_rules.
Context `{seqlogGS Σ}.

Lemma wp_get_field p (l:location) (fld:Z) dq vs v Φ (atm : atomicity) :
  (0 ≤ fld)%Z →
  vs !! Z.to_nat fld = Some v →
  l ↦∗{dq} vs -∗
  (l ↦∗{dq} vs -∗ Φ v) -∗
  WP GetField atm (Val (ValLoc l)) (Val (ValInt fld)) ∷ p {{ Φ }}.
Proof.
  iIntros (Hfld Hidx) "Hblk HΦ". rewrite wp_unfold /wp_pre /=.
  iIntros (K). iIntros "Hrun" (es σ ts) "Hi".
  iDestruct (interp_block_wf_access l _ _ _ _ _ fld with "Hi Hblk") as %Hwf.
  { apply lookup_lt_Some in Hidx. lia. }
  iDestruct (mz_block_cell_acc_Z _ _ _ _ _ Hfld Hidx with "Hblk") as "[Hc Hclose]".
  iDestruct (interp_get_field with "Hi Hc") as %Hlook.
  iModIntro. iSplit.
  { iPureIntro. eexists _,_,_,_. apply base_step_prim_step.
    by eapply base_step_get_field_mutable. }
  iSplit.
  { iPureIntro. wf_from_block σ K (GetField atm (Val (ValLoc l)) (Val (ValInt fld))) Hwf. }
  iIntros (κ e' σ' efs Hstep).
  apply base_reducible_prim_step in Hstep; last first.
  { eexists _,_,_,_. by eapply base_step_get_field_mutable. }
  invert_base_step.
  iDestruct ("Hclose" $! v with "Hc") as "Hblk".
  rewrite list_insert_id; last exact Hidx.
  iMod (interp_run (fill K (Val v)) with "Hrun Hi") as "[Hrun Hi]".
  iModIntro. rewrite !app_nil_r. iFrame.
  iSplitL "HΦ Hblk".
  { iApply wp_value. by iApply "HΦ". }
  done.
Qed.

Lemma wp_set_field p (l:location) (fld:Z) v w vs Φ (atm : atomicity) :
  (0 ≤ fld)%Z →
  vs !! Z.to_nat fld = Some v →
  l ↦∗ vs -∗
  (l ↦∗ <[Z.to_nat fld := w]> vs -∗ Φ ValUnit) -∗
  WP SetField atm (Val (ValLoc l)) (Val (ValInt fld)) (Val w) ∷ p {{ Φ }}.
Proof.
  iIntros (Hfld Hidx) "Hblk HΦ". rewrite wp_unfold /wp_pre /=.
  iIntros (K). iIntros "Hrun" (es σ ts) "Hi".
  iDestruct (interp_block_wf_access l _ _ _ _ _ fld with "Hi Hblk") as %Hwf.
  { apply lookup_lt_Some in Hidx. lia. }
  iDestruct (mz_block_cell_acc_Z _ _ _ _ _ Hfld Hidx with "Hblk") as "[Hc Hclose]".
  iMod (interp_set_field _ _ _ _ _ w with "Hi Hc") as "(%Hlook & Hi & Hc)".
  iModIntro. iSplit.
  { iPureIntro. eexists _,_,_,_. apply base_step_prim_step.
    apply base_step_set_field. by eexists. }
  iSplit.
  { iPureIntro. wf_from_block σ K (SetField atm (Val (ValLoc l)) (Val (ValInt fld)) (Val w)) Hwf. }
  iIntros (κ e' σ' efs Hstep).
  apply base_reducible_prim_step in Hstep; last first.
  { eexists _,_,_,_. apply base_step_set_field. by eexists. }
  invert_base_step.
  iDestruct ("Hclose" $! w with "Hc") as "Hblk".
  iMod (interp_run (fill K Unit) with "Hrun Hi") as "[Hrun Hi]".
  iModIntro. rewrite !app_nil_r. iFrame.
  iSplitL "HΦ Hblk".
  { iApply wp_value. by iApply "HΦ". }
  done.
Qed.

Lemma wp_alloc p tag (n:Z) Φ :
  (0 ≤ n)%Z →
  (∀ l:location,
    l ↦ₕ□ Header tag (Z.to_nat n) -∗
    ([∗ list] i ↦ v ∈ replicate (Z.to_nat n) ValUnit, (l +ₗ Z.of_nat i) ↦ v) -∗
    Φ (ValLoc l)) -∗
  WP Alloc (Val (ValNat tag)) (Val (ValInt n)) ∷ p {{ Φ }}.
Proof.
  iIntros (Hn) "HΦ". rewrite wp_unfold /wp_pre /=.
  iIntros (K). iIntros "Hrun" (es σ ts) "Hi".
  set (l := location_fresh (dom σ.(state_headers) ∪ dom σ.(state_heap))).
  pose proof (location_fresh_fresh (dom σ.(state_headers) ∪ dom σ.(state_heap))) as Hfresh.
  setoid_rewrite not_elem_of_union in Hfresh.
  assert (σ.(state_headers) !! l = None) as Hhdr.
  { apply not_elem_of_dom. rewrite -(location_add_0 l). apply Hfresh. lia. }
  assert (∀ i:nat, i < Z.to_nat n →
            σ.(state_headers) !! (l +ₗ i) = None ∧
            σ.(state_heap) !! (l +ₗ i) = None) as Hfree.
  { intros i Hi. split; apply not_elem_of_dom; apply Hfresh; lia. }
  iModIntro. iSplit.
  { iPureIntro. eexists _,_,_,_. apply base_step_prim_step.
    apply base_step_alloc; first done. split_and!.
    - done.
    - apply not_elem_of_dom. rewrite -(location_add_0 l). apply Hfresh. lia.
    - intros i Hi. split; apply not_elem_of_dom; apply Hfresh; lia. }
  iSplit.
  { iPureIntro. wf_vacuous. }
  iIntros (κ e' σ' efs Hstep).
  apply base_reducible_prim_step in Hstep; last first.
  { eexists _,_,_,_. apply base_step_alloc; first done. split_and!.
    - done.
    - apply not_elem_of_dom. rewrite -(location_add_0 l). apply Hfresh. lia.
    - intros i Hi. split; apply not_elem_of_dom; apply Hfresh; lia. }
  invert_base_step.
  rename l0 into l'.
  match goal with H : state_alloc_condition _ _ _ |- _ =>
    destruct H as [Hhdr' [Hheap_l' Hboth']] end.
  iMod (interp_block_mutable l' _ _ _ tag (replicate (Z.to_nat n) ValUnit) with "Hi")
    as "(Hi & #Hhdr & Hcells & _)".
  { apply Hhdr'. }
  { apply Hheap_l'. }
  { intros i Hi. apply Hboth'. rewrite length_replicate in Hi. done. }
  { intros i Hi. apply Hboth'. rewrite length_replicate in Hi. done. }
  rewrite length_replicate.
  iMod (interp_run (fill K (Val (ValLoc l'))) with "Hrun Hi") as "[Hrun Hi]".
  iModIntro. rewrite !app_nil_r. iFrame.
  iSplitR "".
  { iApply wp_value. iApply ("HΦ" with "Hhdr Hcells"). }
  done.
Qed.

Lemma wp_fork p e Φ :
  (∀ p' v, ⌜val_immediate v⌝ -∗ local p' v -∗ WP e ∷ p' {{ _, True }}) -∗
  Φ ValUnit -∗
  WP Fork e ∷ p {{ Φ }}.
Proof.
  iIntros "He HΦ". rewrite wp_unfold /wp_pre /=.
  iIntros (K). iIntros "Hrun" (es σ ts) "Hi".
  iModIntro. iSplit.
  { iPureIntro. eexists _,_,_,_. apply base_step_prim_step. apply base_step_fork'. }
  iSplit.
  { iPureIntro. wf_vacuous. }
  iIntros (κ e' σ' efs Hstep).
  apply base_reducible_prim_step in Hstep; last first.
  { eexists _,_,_,_. apply base_step_fork'. }
  invert_base_step.
  iMod (interp_fork v p _ (fill K ()) e with "Hrun Hi") as "(Hrun & Hrunf & Hlocal & Hi)".
  iModIntro. rewrite Nat.add_0_r.
  replace ([]) with (@nil (val*val)) by reflexivity.
  rewrite (app_nil_r ts).
  iFrame "Hi Hrun Hrunf".
  iSplitL "HΦ".
  { iApply wp_value. done. }
  iApply ("He" with "[//] Hlocal").
Qed.

Lemma wp_pure_step p e e' Φ :
  pure_step e e' →
  WP e' ∷ p {{ Φ }} -∗
  WP e ∷ p {{ Φ }}.
Proof.
  iIntros (Hps) "Hwp".
  assert (to_val e = None) as He.
  { eapply (reducible_not_val p e inhabitant), reducible_no_obs_reducible,
      (pure_step_safe _ _ Hps). }
  rewrite (wp_unfold p e) /wp_pre /= He.
  iIntros (K). iIntros "Hrun" (es σ ts) "Hi".
  iModIntro. iSplit.
  { iPureIntro. apply reducible_no_obs_reducible, (pure_step_safe _ _ Hps). }
  iSplit.
  { iPureIntro. by apply (pure_step_wf_access σ K e e' Hps). }
  iIntros (κ e2 σ' efs Hstep).
  destruct (pure_step_det _ _ Hps _ _ _ _ _ _ Hstep) as (-> & -> & -> & ->).
  iMod (interp_run (fill K e') with "Hrun Hi") as "[Hrun Hi]".
  iModIntro. rewrite !app_nil_r. iFrame "Hi Hrun Hwp". done.
Qed.

Lemma wp_pure p e e' φ n Φ :
  PureExec φ n e e' →
  φ →
  WP e' ∷ p {{ Φ }} -∗
  WP e ∷ p {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [|n x y z Hstep Hsteps] "IH".
  - done.
  - iApply (wp_pure_step with "[Hwp]"); first exact Hstep. by iApply "IH".
Qed.

End wp_rules.

Section wp_adequacy.
Context `{seqlogGS Σ}.

Definition wptp (Φ0 : val → iProp Σ) (es : list expr) : iProp Σ :=
  [∗ list] q ↦ e ∈ es,
    running q e ∗ wp q e (if Nat.eqb q 0 then Φ0 else (λ _, True%I)).

Lemma wptp_lookup Φ0 es q e :
  es !! q = Some e →
  wptp Φ0 es -∗
    (running q e ∗ wp q e (if Nat.eqb q 0 then Φ0 else (λ _, True%I))) ∗
    (∀ e',
      running q e' ∗ wp q e' (if Nat.eqb q 0 then Φ0 else (λ _, True%I)) -∗
      wptp Φ0 (<[q:=e']> es)).
Proof.
  iIntros (Hlook) "Hwptp". rewrite /wptp.
  iDestruct (big_sepL_insert_acc with "Hwptp") as "[$ Hclose]"; first done.
  iIntros (e') "He'". by iApply "Hclose".
Qed.

Lemma wptp_app Φ0 es efs :
  length es ≠ 0 →
  wptp Φ0 es ∗
  ([∗ list] k ↦ ef ∈ efs,
    running (length es + k) ef ∗ wp (length es + k) ef (λ _, True%I)) -∗
  wptp Φ0 (es ++ efs).
Proof.
  iIntros (Hne) "[Hes Hefs]". rewrite /wptp.
  rewrite big_sepL_app. iFrame "Hes".
  iApply (big_sepL_mono with "Hefs"). iIntros (k ef _) "[$ Hk]".
  destruct (Nat.eqb (length es + k) 0) eqn:Heq; last done.
  apply Nat.eqb_eq in Heq. lia.
Qed.

Lemma wptp_step Φ0 es σ ts es' σ' :
  silent_step (es, σ) (es', σ') →
  interp es σ ts ∗ wptp Φ0 es ={⊤}=∗
  ∃ ts', interp es' σ' ts' ∗ wptp Φ0 es'.
Proof.
  iIntros ((κ & tid & e1 & e2 & σ2 & efs & Hstep & Hlook & Heq)) "[Hi Hwptp]".
  simpl in *. injection Heq as -> ->.
  iDestruct (wptp_lookup with "Hwptp") as "[[Hrun Hwp] Hclose]"; first exact Hlook.
  rewrite wp_unfold /wp_pre /=.
  destruct (to_val e1) as [v|] eqn:He1.
  { exfalso. eapply prim_step_not_val in Hstep. congruence. }
  iMod ("Hwp" $! [] with "Hrun Hi") as "(_ & _ & Hcont)".
  iMod ("Hcont" $! κ e2 σ2 efs Hstep) as "(Hi & Hrun & Hwp & Hefs)".
  iModIntro. iExists (ts ++ κ). iFrame "Hi".
  pose proof (lookup_lt_Some _ _ _ Hlook) as Hlt.
  assert (length (<[tid:=e2]> es) ≠ 0) as Hne.
  { rewrite length_insert. lia. }
  iPoseProof (wptp_app Φ0 (<[tid:=e2]> es) efs Hne) as "Happ".
  rewrite length_insert.
  iApply "Happ". iFrame "Hefs". iApply "Hclose". iFrame.
Qed.

Lemma wptp_safe Φ0 es σ ts q e :
  to_val e = None →
  es !! q = Some e →
  interp es σ ts ∗ wptp Φ0 es ={⊤}=∗ ⌜reducible q e σ⌝.
Proof.
  iIntros (He Hlook) "[Hi Hwptp]".
  iDestruct (wptp_lookup with "Hwptp") as "[[Hrun Hwp] _]"; first exact Hlook.
  rewrite wp_unfold /wp_pre He.
  iMod ("Hwp" $! [] with "Hrun Hi") as "(%Hred & _ & _)".
  by iModIntro.
Qed.

Lemma wptp_value Φ0 es σ ts v :
  es !! 0 = Some (Val v) →
  interp es σ ts ∗ wptp Φ0 es ={⊤}=∗ Φ0 v.
Proof.
  iIntros (Hlook) "[Hi Hwptp]".
  iDestruct (wptp_lookup with "Hwptp") as "[[Hrun Hwp] _]"; first exact Hlook.
  simpl. rewrite wp_unfold /wp_pre /=.
  by iMod "Hwp".
Qed.

Lemma wptp_steps n Φ0 es σ ts es' σ' :
  relations.nsteps silent_step n (es, σ) (es', σ') →
  interp es σ ts ∗ wptp Φ0 es ={⊤}=∗ ∃ ts', interp es' σ' ts' ∗ wptp Φ0 es'.
Proof.
  iInduction n as [|n] "IH" forall (es σ ts).
  - iIntros (Hn) "[Hi Hwptp]". inversion Hn; subst. iExists ts. by iFrame.
  - iIntros (Hn) "[Hi Hwptp]". inversion Hn; subst.
    destruct y as [es1 σ1].
    iMod (wptp_step with "[$Hi $Hwptp]") as (ts1) "[Hi Hwptp]"; first eassumption.
    iApply ("IH" with "[//] [$Hi $Hwptp]").
Qed.

End wp_adequacy.

Import Initialization.

Lemma wp_adequacy `{seqlogPreG Σ} e σ v0 (φ : val → Prop) :
  σ.(state_locals) = [v0] →
  (∀ `{hG : !seqlogGS Σ},
     local 0 v0 -∗ WP e ∷ 0 {{ v, ⌜φ v⌝ }}) →
  ∀ es' σ', rtc silent_step ([e], σ) (es', σ') →
    (∀ q e0, es' !! q = Some e0 → to_val e0 = None → reducible q e0 σ') ∧
    (∀ v, es' !! 0 = Some (Val v) → φ v).
Proof.
  intros Hloc Hwp es' σ' Hrtc.
  apply rtc_nsteps_1 in Hrtc as [n Hn].
  assert (∀ (P : Prop),
    (∀ (Hlc : invGS_gen HasLc Σ),
       £ 0 ⊢@{iPropI Σ} |={⊤}=> ⌜P⌝) → P) as Hsound.
  { intros P HP. eapply pure_soundness.
    eapply (step_fupdN_soundness_lc _ 0 0).
    iIntros (Hlc) "Hlc". iMod (HP with "Hlc") as "%HP'".
    iApply fupd_mask_intro; first set_solver. iIntros "_". by iPureIntro.
    Unshelve. all: apply _. }
  split.
  - intros q e0 Hlook He0.
    apply Hsound. iIntros (Hlc) "_".
    iMod (seqlog_init e σ v0 Hloc) as "[%hi (%Xeq & Hrun & Hlocal & _ & Hi)]".
    rewrite -Xeq.
    iMod ("Hi" $! True%I) as "(Hi & _)".
    iDestruct (Hwp with "Hlocal") as "Hwp".
    iAssert (wptp (λ v, ⌜φ v⌝)%I [e]) with "[Hwp Hrun]" as "Hwptp".
    { rewrite /wptp /=. iSplitL; [iFrame|done]. }
    iPoseProof (@wptp_steps _ hi n _ _ _ _ _ _ Hn with "[$Hi $Hwptp]") as "Hupd".
    iMod "Hupd" as (ts') "[Hi Hwptp]".
    by iMod (wptp_safe with "[$Hi $Hwptp]") as "%".
  - intros v Hlook.
    apply Hsound. iIntros (Hlc) "_".
    iMod (seqlog_init e σ v0 Hloc) as "[%hi (%Xeq & Hrun & Hlocal & _ & Hi)]".
    rewrite -Xeq.
    iMod ("Hi" $! True%I) as "(Hi & _)".
    iDestruct (Hwp with "Hlocal") as "Hwp".
    iAssert (wptp (λ v, ⌜φ v⌝)%I [e]) with "[Hwp Hrun]" as "Hwptp".
    { rewrite /wptp /=. iSplitL; [iFrame|done]. }
    iMod (@wptp_steps _ hi n _ _ _ _ _ _ Hn with "[$Hi $Hwptp]") as (ts') "[Hi Hwptp]".
    by iMod (wptp_value with "[$Hi $Hwptp]") as "%Hphi".
Qed.
