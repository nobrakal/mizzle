From stdpp Require Import relations.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi.lib Require Import fixpoint_mono.

From mizzle.lang Require Import instances.

From mizzle.logic Require Import interp goal adequacy translate decompose
  wf_access completeness stuck base_stuck.
From mizzle.lang Require Import locs_in_headers block_heap_complete_preserved.

Lemma irreducible_no_oob_form p e σ :
  to_val e = None →
  irreducible_no_oob p e σ →
  ∃ K r,
    e = fill K r ∧
    to_val r = None ∧
    sub_redexes_are_values r ∧
    ∀ κ r' σ' es, base_step p r σ κ r' σ' es → wf_access σ r → False.
Proof.
  intros Hv Hir.
  exists (decompose e).1, (decompose e).2.
  split; [|split; [|split]].
  - symmetry. exact (decompose_sound e).
  - exact (decompose_redex_not_val e Hv).
  - exact (decompose_step_none_sub_redexes _ (decompose_redex_no_step e)).
  - intros κ r' σ' es Hbase Hwa.
    have Heq : fill (decompose e).1 (decompose e).2 = e := decompose_sound e.
    have Hrno : decompose_step (decompose e).2 = None := decompose_redex_no_step e.
    have Hrnv : to_val (decompose e).2 = None := decompose_redex_not_val e Hv.
    rewrite -(wf_access_fill_eq σ (decompose e).1 (decompose e).2 Hrnv Hrno) Heq in Hwa.
    eapply Hir; [|exact Hwa].
    exact (base_step_fill_prim_step' (decompose e).1 (decompose e).2 r' (eq_sym Heq) eq_refl Hbase).
Qed.

Section go.
Context `{seqlogGS Σ}.

Lemma is_stuck_complete es p e σ κ :
  Forall (wf_header σ) es ->
  block_heap_complete σ ->
  es !! p = Some e ->
  to_val e = None ->
  irreducible_no_oob p e σ ->
  mirror es σ κ -∗ is_stuck'.
Proof.
  intros Hwfh Hbhc Hlook Hnv Hir. iIntros "Hext".
  iEval (rewrite mirror_unfold) in "Hext".
  iDestruct "Hext" as (φ ψ Hok) "(Hruns & Hloc & Hheap & Hhdrs & Horph & Hpm)".
  pose proof (proj1 Hok) as Hinvs.
  iDestruct (big_sepL2_length with "Hruns") as %Hlen.
  assert (is_Some (φ !! p)) as [tid' Hφp].
  { apply lookup_lt_is_Some. rewrite Hlen. by eapply lookup_lt_Some. }
  iDestruct (big_sepL2_lookup_acc _ _ _ _ _ _ Hφp Hlook with "Hruns") as "[Hrun _]".
  apply irreducible_no_oob_form in Hir as (K & r & -> & Hrv & Hsub & Hstep); last done.

  iEval (rewrite tr_fill /=) in "Hrun". rewrite /is_stuck'. iExists tid'.

  apply deduce_base_stuck in Hstep; [|done|done].
  destruct Hstep as
    [ v w Hr Hbad
    | i recs v Hr Hi
    | op v Hr Hev
    | op v1 v2 Hr Hev
    | v e1 e2 Hr Hbad
    | v1 v2 e' Hr Hbad
    | v1 v2 Hr Hbad
    | z n Hr Hneg
    | tag Hr
    | v x e' brs Hr Hbad
    | l x e' brs Hr Hhdr
    | l hdr x e' brs Hr Hhdr Hem
    | gen tag vs x e' brs Hr Hem
    | v Hr Hbad
    | l Hr Hhdr
    | gen tag Hr
    | v Hr Hbad
    | l Hr Hhdr
    | gen tag Hr
    | atm v1 v2 Hr Hbad
    | atm l fld Hr Hhdr
    | atm l fld hdr Hr Hhdr Hbd
    | atm l fld hdr Hr Hhdr Hbd Hcell
    | atm gen tag vs fld Hr Hrange
    | atm v1 v2 v3 Hr Hbad
    | atm l fld v Hr Hhdr
    | atm l fld v hdr Hr Hhdr Hbd
    | atm l fld v hdr Hr Hhdr Hbd Hcell
    | v1 v2 Hr Hbad
    | l fld v Hr Hhdr
    | l fld v hdr Hr Hhdr Hbd
    | l fld v hdr Hr Hhdr Hbd Hcell
    | v0 v1 v2 Hr Hbad
    | l fld v1 v2 Hr Hhdr
    | l fld v1 v2 hdr Hr Hhdr Hbd
    | l fld v1 v2 hdr Hr Hhdr Hbd Hcell
    | v1 v2 Hr Hbad
    | l fld n Hr Hhdr
    | l fld n hdr Hr Hhdr Hbd
    | l fld n hdr Hr Hhdr Hbd Hcell
    | l fld n v hdr Hr Hhdr Hbd Hcell Hni
    | Hr Hloc
    | v Hr Hloc
    | x Hr ];
  subst r.
  - (* App (Val v) (Val w), v not ValRecs *)
    iApply (stuck_call tid' (tr_ectx ψ K) (tr_val ψ v) (tr_val ψ w) with "Hrun").
    by destruct v.
  - (* App (ValRecs i recs) v, index missing *)
    iApply (stuck_app tid' (tr_ectx ψ K) i _ (tr_val ψ v) with "Hrun").
    by rewrite list_lookup_fmap Hi.
  - (* Unop *)
    iApply (stuck_unop tid' (tr_ectx ψ K) op (tr_val ψ v) with "Hrun").
    by apply tr_eval_unop_none.
  - (* Binop *)
    iApply (stuck_binop tid' (tr_ectx ψ K) op (tr_val ψ v1) (tr_val ψ v2) with "Hrun").
    by apply tr_eval_binop_none.
  - (* If, not bool *)
    iApply (stuck_if tid' (tr_ectx ψ K) (tr_val ψ v) (tr_expr ψ e1) (tr_expr ψ e2) with "Hrun").
    by destruct v as [[b1|n1|l1|]|i1 recs1|gen1 tag1 vs1].
  - (* For, not both int *)
    iApply (stuck_for tid' (tr_ectx ψ K) (tr_val ψ v1) (tr_val ψ v2) (tr_expr ψ e') with "Hrun").
    by destruct v1 as [[b1|n1|l1|]|i1 recs1|gen1 tag1 vs1], v2 as [[b2|n2|l2|]|i2 recs2|gen2 tag2 vs2].
  - (* Alloc, wrong types *)
    iApply (stuck_alloc tid' (tr_ectx ψ K) (tr_val ψ v1) (tr_val ψ v2) with "Hrun").
    by destruct v1 as [[b1|n1|l1|]|i1 recs1|gen1 tag1 vs1], v2 as [[b2|n2|l2|]|i2 recs2|gen2 tag2 vs2].
  - (* Alloc, negative *)
    iApply (stuck_alloc_neg tid' (tr_ectx ψ K) z n with "Hrun"). exact Hneg.
  - (* Block Mutable [] *)
    iApply (stuck_block_mutable_empty tid' (tr_ectx ψ K) tag with "Hrun").
  - (* Match, not loc or block *)
    iApply (stuck_match tid' (tr_ectx ψ K) (tr_val ψ v) x (tr_expr ψ e') _ with "Hrun").
    by destruct v as [[b1|n1|l1|]|i1 recs1|gen1 tag1 vs1].
  - (* Match mutable, no header *)
    assert (Hwf : wf_header σ (Match (Val (ValLoc l)) x e' brs)).
    { eapply wf_header_at_redex; [exact Hlook|exact Hwfh|done|done]. }
    rewrite /wf_header /= Hhdr in Hwf. by destruct Hwf.
  - (* Match mutable, no branch *)
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hhdr with "Hhdrs") as "[#Hh _]".
    iApply (stuck_match_mutable_no_branch tid' (tr_ectx ψ K) (tr_loc ψ l) hdr x (tr_expr ψ e') _ with "Hh Hrun").
    by apply tr_eval_match_loc_none.
  - (* Match immutable, no branch *)
    iApply (stuck_match_immutable_no_branch tid' (tr_ectx ψ K) gen tag (tr_val ψ <$> vs) x (tr_expr ψ e') _ with "Hrun").
    by apply tr_eval_match_block_none.
  - (* GetTag, not loc or block *)
    iApply (stuck_gettag tid' (tr_ectx ψ K) (tr_val ψ v) with "Hrun").
    by destruct v as [[b1|n1|l1|]|i1 recs1|gen1 tag1 vs1].
  - (* GetTag mutable, no header *)
    assert (Hwf : wf_header σ (GetTag (Val (ValLoc l)))).
    { eapply wf_header_at_redex; [exact Hlook|exact Hwfh|done|done]. }
    rewrite /wf_header /= Hhdr in Hwf. by destruct Hwf.
  - (* GetTag immutable, empty block *)
    iApply (stuck_gettag_immutable_empty tid' (tr_ectx ψ K) gen tag with "Hrun").
  - (* GetSize, not loc or block *)
    iApply (stuck_getsize tid' (tr_ectx ψ K) (tr_val ψ v) with "Hrun").
    by destruct v as [[b1|n1|l1|]|i1 recs1|gen1 tag1 vs1].
  - (* GetSize mutable, no header *)
    assert (Hwf : wf_header σ (GetSize (Val (ValLoc l)))).
    { eapply wf_header_at_redex; [exact Hlook|exact Hwfh|done|done]. }
    rewrite /wf_header /= Hhdr in Hwf. by destruct Hwf.
  - (* GetSize immutable, empty block *)
    iApply (stuck_getsize_immutable_empty tid' (tr_ectx ψ K) gen tag with "Hrun").
  - (* GetField, wrong types *)
    iApply (stuck_get_field tid' (tr_ectx ψ K) (tr_val ψ v1) (tr_val ψ v2) with "Hrun").
    by destruct v1 as [[b1|n1|l1|]|i1 recs1|gen1 tag1 vs1], v2 as [[b2|n2|l2|]|i2 recs2|gen2 tag2 vs2].
  - (* GetField mutable, no header *)
    pose proof (wf_header_at_redex σ es p K _ Hlook Hwfh Hrv ltac:(done)) as Hwf.
    rewrite /wf_header /= Hhdr in Hwf. by destruct Hwf.
  - (* GetField mutable, out of bounds *)
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hhdr with "Hhdrs") as "[#Hh _]".
    iApply (stuck_get_field_oob tid' (tr_ectx ψ K) (tr_loc ψ l) fld hdr with "Hh Hrun"). exact Hbd.
  - (* GetField mutable, cell absent: refuted by block_heap_complete *)
    exfalso.
    destruct (Hbhc l hdr Hhdr (Z.to_nat fld) ltac:(lia)) as [w Hw].
    rewrite Z2Nat.id in Hw; [|lia]. rewrite Hw in Hcell. discriminate.
  - (* GetField immutable, out of range *)
    iApply (stuck_get_field_block tid' (tr_ectx ψ K) gen tag (tr_val ψ <$> vs) fld with "Hrun").
    intros nn Hnn. rewrite list_lookup_fmap (Hrange nn Hnn) //.
  - (* SetField, wrong types *)
    iApply (stuck_set_field tid' (tr_ectx ψ K) (tr_val ψ v1) (tr_val ψ v2) (tr_val ψ v3) with "Hrun").
    by destruct v1 as [[b1|n1|l1|]|i1 recs1|gen1 tag1 vs1], v2 as [[b2|n2|l2|]|i2 recs2|gen2 tag2 vs2].
  - (* SetField mutable, no header *)
    pose proof (wf_header_at_redex σ es p K _ Hlook Hwfh Hrv ltac:(done)) as Hwf.
    rewrite /wf_header /= Hhdr in Hwf. by destruct Hwf.
  - (* SetField mutable, out of bounds *)
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hhdr with "Hhdrs") as "[#Hh _]".
    iApply (stuck_set_field_oob tid' (tr_ectx ψ K) (tr_loc ψ l) fld (tr_val ψ v) hdr with "Hh Hrun"). exact Hbd.
  - (* SetField mutable, cell absent: refuted by block_heap_complete *)
    exfalso.
    destruct (Hbhc l hdr Hhdr (Z.to_nat fld) ltac:(lia)) as [w Hw].
    rewrite Z2Nat.id in Hw; [|lia]. rewrite Hw in Hcell. discriminate.
  - (* Xchg, wrong type *)
    iApply (stuck_xchg tid' (tr_ectx ψ K) (tr_val ψ v1) (tr_val ψ v2) with "Hrun").
    destruct v1 as [lit|i recs|gen tag vs]; try done.
    destruct gen as [bid|]; try done.
    destruct tag as [|tag']; try done.
    destruct vs as [| [[ba|na|la|]|ia ra|ga ta vsa] [| [[bb|fldb|lb|]|ib rb|gb tb vsb] [|c vs']]];
    done.
  - (* Xchg, no header *)
    pose proof (wf_header_at_redex σ es p K _ Hlook Hwfh Hrv ltac:(done)) as Hwf.
    rewrite /wf_header /= Hhdr in Hwf. by destruct Hwf.
  - (* Xchg, out of bounds *)
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hhdr with "Hhdrs") as "[#Hh _]".
    iApply (stuck_xchg_oob tid' (tr_ectx ψ K) (tr_loc ψ l) fld (tr_val ψ v) hdr with "Hh Hrun"). exact Hbd.
  - (* Xchg, cell absent: refuted by block_heap_complete *)
    exfalso.
    destruct (Hbhc l hdr Hhdr (Z.to_nat fld) ltac:(lia)) as [w Hw].
    rewrite Z2Nat.id in Hw; [|lia]. rewrite Hw in Hcell. discriminate.
  - (* CAS, wrong type *)
    iApply (stuck_cas tid' (tr_ectx ψ K) (tr_val ψ v0) (tr_val ψ v1) (tr_val ψ v2) with "Hrun").
    destruct v0 as [lit|i recs|gen tag vs]; try done.
    destruct gen as [bid|]; try done.
    destruct tag as [|tag']; try done.
    destruct vs as [| [[ba|na|la|]|ia ra|ga ta vsa] [| [[bb|fldb|lb|]|ib rb|gb tb vsb] [|c vs']]];
    done.
  - (* CAS, no header *)
    pose proof (wf_header_at_redex σ es p K _ Hlook Hwfh Hrv ltac:(done)) as Hwf.
    rewrite /wf_header /= Hhdr in Hwf. by destruct Hwf.
  - (* CAS, out of bounds *)
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hhdr with "Hhdrs") as "[#Hh _]".
    iApply (stuck_cas_oob tid' (tr_ectx ψ K) (tr_loc ψ l) fld (tr_val ψ v1) (tr_val ψ v2) hdr with "Hh Hrun"). exact Hbd.
  - (* CAS, cell absent: refuted by block_heap_complete *)
    exfalso. destruct (Hbhc l hdr Hhdr (Z.to_nat fld) ltac:(lia)) as [w Hw].
    rewrite Z2Nat.id in Hw; [|lia]. rewrite Hw in Hcell. discriminate.
  - (* FAA, wrong types *)
    iApply (stuck_faa tid' (tr_ectx ψ K) (tr_val ψ v1) (tr_val ψ v2) with "Hrun").
    destruct v1 as [lit|i recs|gen tag vs]; try done.
    destruct gen as [bid|]; try done.
    destruct tag as [|tag']; try done.
    destruct vs as [| [[ba|na|la|]|ia ra|ga ta vsa] [| [[bb|fldb|lb|]|ib rb|gb tb vsb] [|c vs']]]; try done.
    destruct v2 as [[b2|n2|l2|]|i2 recs2|gen2 tag2 vs2]; done.
  - (* FAA, no header *)
    pose proof (wf_header_at_redex σ es p K _ Hlook Hwfh Hrv ltac:(done)) as Hwf.
    rewrite /wf_header /= Hhdr in Hwf. by destruct Hwf.
  - (* FAA, out of bounds *)
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hhdr with "Hhdrs") as "[#Hh _]".
    iApply (stuck_faa_oob tid' (tr_ectx ψ K) (tr_loc ψ l) fld n hdr with "Hh Hrun"). exact Hbd.
  - (* FAA, cell absent: refuted by block_heap_complete *)
    exfalso. destruct (Hbhc l hdr Hhdr (Z.to_nat fld) ltac:(lia)) as [w Hw].
    rewrite Z2Nat.id in Hw; [|lia]. rewrite Hw in Hcell. discriminate.
  - (* FAA, cell present but not an integer *)
    destruct (ei_block _ _ _ _ Hinvs l hdr Hhdr (Z.to_nat fld) ltac:(lia)) as (l' & Hψl & Hψlf).
    rewrite Z2Nat.id in Hψlf; [|lia].
    assert (Htrl : tr_loc ψ l = l') by (rewrite /tr_loc Hψl //).
    assert (Htrlf : tr_loc ψ (l +ₗ fld) = l' +ₗ fld) by (rewrite /tr_loc Hψlf //).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hcell with "Hheap") as "[Hc _]".
    iEval (rewrite Htrlf -Htrl) in "Hc".
    iApply (stuck_faa_not_int tid' (tr_ectx ψ K) (tr_loc ψ l) fld n (tr_val ψ v) with "Hc Hrun").
    intros m Heq. apply tr_val_inv_litint in Heq. exact (Hni m Heq).
  - (* GetLocal, no local *)
    exfalso.
    pose proof (ei_len _ _ _ _ Hinvs) as Hl2.
    apply lookup_lt_Some in Hlook. rewrite Hl2 in Hlook.
    apply lookup_lt_is_Some in Hlook as [w Hw]. rewrite Hw in Hloc. discriminate.
  - (* SetLocal, no local *)
    exfalso.
    pose proof (ei_len _ _ _ _ Hinvs) as Hl2.
    apply lookup_lt_Some in Hlook. rewrite Hl2 in Hlook.
    apply lookup_lt_is_Some in Hlook as [w Hw]. rewrite Hw in Hloc. discriminate.
  - (* Var *)
    iApply (stuck_var tid' (tr_ectx ψ K) x with "Hrun").
Qed.

End go.

Lemma completeness_stuck e v0 es σ κ :
  traced_steps ([e], initial_state v0) κ (es,σ) ->
  Stuck es σ ->
  locs_expr e = ∅ -> locs_val v0 = ∅ ->
  (∀ `{hG:!seqlogGS Σ},
    remaining is_stuck' ∗ running 0 e ∗ local 0 v0 ∗ trace_model [] -∗
    goal ⊤).
Proof.
  intros Hsteps (p & e' & Hepp & Hnv & Hir) Hloe Hlov0.
  iIntros (??) "(Hrem&Hrun&Hlocal&Hpm)".
  iApply (completeness e v0 es σ κ Hsteps Hloe Hlov0).
  iFrame "Hrun Hlocal Hpm".
  iApply (update_remaining with "[] Hrem").
  { iApply is_stuck_complete; [..|exact Hepp|exact Hnv|exact Hir].
    - (* Forall (wf_header σ) es — derived from the
         [locs_state_in_headers] preservation lemma. *)
      apply Forall_locs_expr_in_headers_wf_header.
      eapply traced_steps_locs_in_headers; first exact Hsteps.
      + apply Forall_singleton. rewrite /locs_expr_in_headers Hloe. set_solver.
      + split.
        * constructor; [|by constructor]. rewrite Hlov0. set_solver.
        * by apply map_Forall_empty.
    - (* block_heap_complete σ — by step preservation; initial heap is
         empty so the invariant is vacuous at the start. *)
      eapply traced_steps_block_heap_complete; first exact Hsteps.
      intros l hdr Hl. by rewrite /initial_state /= lookup_empty in Hl. }
Qed.
