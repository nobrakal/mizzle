From stdpp Require Import relations.
From iris.proofmode Require Import base proofmode.
From iris.base_logic.lib Require Import fancy_updates.
From iris.bi.lib Require Import fixpoint_mono.

From mizzle.lang Require Import instances.

From mizzle.logic Require Import interp goal adequacy translate decompose
  wf_access completeness race.
From mizzle.lang Require Import locs_in_headers block_heap_complete_preserved.

(** Source-level accesses translate to target-level accesses on the
    [tr_expr]-translated expression. Because [running] holds the *translated*
    expression, two threads racing on the same source address [l] must be
    shown to race on the same *target* address. The shared target address is
    [tr_loc ψ l]: a source access at [base +ₗ fld] translates to a target
    access at [tr_loc ψ base +ₗ fld], and block-alignment together with the
    in-bounds witness ([wf_access]) gives
    [tr_loc ψ base +ₗ fld = tr_loc ψ (base +ₗ fld) = tr_loc ψ l]. *)
Lemma access_tr ψ σ e l b :
  block_aligned ψ σ →
  wf_access σ e →
  access e l b →
  access (tr_expr ψ e) (tr_loc ψ l) b.
Proof.
  intros Hba Hwf (ks & e' & -> & Hla).
  exists (tr_ectx ψ ks), (tr_expr ψ e').
  split; [apply tr_fill|].
  assert (Hv : to_val e' = None) by (inversion Hla; subst; reflexivity).
  assert (Hd : decompose_step e' = None) by (inversion Hla; subst; reflexivity).
  unfold wf_access in Hwf. rewrite (decompose_fill_redex ks e' Hv Hd) in Hwf.
  inversion Hla; subst; simpl in Hwf |- *;
    destruct Hwf as (hdr & Hhdr & Hbd);
    destruct (block_witness σ ψ _ _ Hba (ex_intro _ hdr (conj Hhdr Hbd)))
      as (li & Hb1 & Hb2);
    erewrite tr_loc_offset by eassumption;
    constructor.
Qed.

Section go.
Context `{seqlogGS Σ}.

(** Completeness core: from [mirror es σ κ] (which carries the block-alignment
    invariant), a well-formed racy configuration yields the logical race
    predicate [is_racy']. Mirrors [is_stuck_complete]. *)
Lemma is_racy_complete es σ κ p1 p2 e1 e2 l k1 k2 :
  p1 ≠ p2 →
  es !! p1 = Some e1 →
  es !! p2 = Some e2 →
  access e1 l k1 →
  access e2 l k2 →
  races k1 k2 →
  wf_access σ e1 →
  wf_access σ e2 →
  mirror es σ κ -∗ is_racy'.
Proof.
  intros Hne Hl1 Hl2 Ha1 Ha2 Hw Hwf1 Hwf2. iIntros "Hext".
  iEval (rewrite mirror_unfold) in "Hext".
  iDestruct "Hext" as (φ ψ Hok) "(Hruns & Hloc & Hheap & Hhdrs & Horph & Hpm)".
  pose proof (proj1 Hok) as Hinvs.
  iDestruct (big_sepL2_length with "Hruns") as %Hlen.
  assert (is_Some (φ !! p1)) as [tid1 Hφ1].
  { apply lookup_lt_is_Some. rewrite Hlen. by eapply lookup_lt_Some. }
  assert (is_Some (φ !! p2)) as [tid2 Hφ2].
  { apply lookup_lt_is_Some. rewrite Hlen. by eapply lookup_lt_Some. }
  rewrite (big_sepL2_delete' _ φ es p1 tid1 e1 Hφ1 Hl1).
  iDestruct "Hruns" as "[Hr1 Hrest]".
  iDestruct (big_sepL2_lookup_acc _ _ _ p2 tid2 e2 Hφ2 Hl2 with "Hrest")
    as "[Hr2imp _]".
  iDestruct ("Hr2imp" with "[%]") as "Hr2"; first done.
  assert (Hba : block_aligned ψ σ) by exact (ei_block _ _ _ _ Hinvs).
  rewrite /is_racy'. iExists tid1, tid2.
  iApply (is_racy_intro tid1 tid2 _ _ (tr_loc ψ l) k1 k2 with "Hr1 Hr2").
  - apply (access_tr ψ σ); [exact Hba | exact Hwf1 | exact Ha1].
  - apply (access_tr ψ σ); [exact Hba | exact Hwf2 | exact Ha2].
  - exact Hw.
Qed.

End go.

(** A well-formed (in-bounds) racy configuration: two distinct threads each
    have an in-bounds racing access to the same location. *)
Definition wf_racy (es : list expr) (σ : state) :=
  ∃ p1 p2 e1 e2 l k1 k2,
    p1 ≠ p2 ∧
    es !! p1 = Some e1 ∧ es !! p2 = Some e2 ∧
    access e1 l k1 ∧ access e2 l k2 ∧
    races k1 k2 ∧
    wf_access σ e1 ∧ wf_access σ e2.

Lemma completeness_race e v0 es σ κ :
  traced_steps ([e], initial_state v0) κ (es,σ) ->
  wf_racy es σ ->
  locs_expr e = ∅ -> locs_val v0 = ∅ ->
  (∀ `{hG:!seqlogGS Σ},
    remaining is_racy' ∗ running 0 e ∗ local 0 v0 ∗ trace_model [] -∗
    goal ⊤).
Proof.
  intros Hsteps (p1&p2&e1&e2&l&k1&k2&Hne&Hl1&Hl2&Ha1&Ha2&Hw&Hwf1&Hwf2)
    Hloe Hlov0.
  iIntros (??) "(Hrem&Hrun&Hlocal&Hpm)".
  iApply (completeness e v0 es σ κ Hsteps Hloe Hlov0).
  iFrame "Hrun Hlocal Hpm".
  iApply (update_remaining with "[] Hrem").
  iApply (is_racy_complete es σ κ p1 p2 e1 e2 l k1 k2); eauto.
Qed.
